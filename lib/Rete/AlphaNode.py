# -*- coding: utf-8 -*-
"""
===========================================================================================
"""
from rdflib.graph import Graph
from rdflib import (
    BNode,
    Namespace,
    RDF,
    RDFS,
    URIRef,
    Variable,
    )
from rdflib import py3compat

from .Node import Node
try:
    from functools import reduce
except ImportError:
    pass


OWL_NS = Namespace("http://www.w3.org/2002/07/owl#")

SUBJECT = 0
PREDICATE = 1
OBJECT = 2

VARIABLE = 0
VALUE = 1

TERMS = [SUBJECT, PREDICATE, OBJECT]


def normalizeTerm(term):
    """
    Graph Identifiers are used
    """
    if isinstance(term, Graph):
        return term.identifier
    else:
        return term

from pickle import dumps, PicklingError  # for memoize


class memoize(object):
    """Decorator that caches a function's return value each time it is called.
    If called later with the same arguments, the cached value is returned, and
    not re-evaluated. Slow for mutable types."""
    # Ideas from MemoizeMutable class of Recipe 52201 by Paul Moore and
    # from memoized decorator of
    # http://wiki.python.org/moin/PythonDecoratorLibrary
    # For a version with timeout see Recipe 325905
    # For a self cleaning version see Recipe 440678
    # Weak references (a dict with weak values) can be used, like this:
    #   self._cache = weakref.WeakValueDictionary()
    #   but the keys of such dict can't be int
    def __init__(self, func):
        self.func = func
        self._cache = {}

    def __call__(self, *args, **kwds):
        key = args
        if kwds:
            items = list(kwds.items())
            items.sort()
            key = key + tuple(items)
        try:
            if key in self._cache:
                return self._cache[key]
            self._cache[key] = result = self.func(*args, **kwds)
            return result
        except TypeError:
            try:
                dump = dumps(key)
            except PicklingError:
                return self.func(*args, **kwds)
            else:
                if dump in self._cache:
                    return self._cache[dump]
                self._cache[dump] = result = self.func(*args, **kwds)
                return result


class ReteToken:
    """
    A ReteToken, an RDF triple in a Rete network.  Once it passes an alpha
    node test, if will have unification substitutions per variable
    """
    def __init__(self, triple, debug=False):
        (subject, predicate, object) = triple
        self.debug = debug
        self.subject = (None, normalizeTerm(subject))
        self.predicate = (None, normalizeTerm(predicate))
        self.object_ = (None, normalizeTerm(object))
        self.bindingDict = {}
        self._termConcat = self.concatenateTerms(
                [self.subject, self.predicate, self.object_])
        self.hash = hash(self._termConcat)
        self.inferred = False

    def __hash__(self):
        """

        >>> token1 = ReteToken((RDFS.domain, RDFS.domain, RDFS.Class))
        >>> token2 = ReteToken((RDFS.domain, RDFS.domain, RDFS.Class))
        >>> token1 == token2
        True
        >>> token1 in set([token2])
        True
        """
        return self.hash

    @memoize
    def concatenateTerms(terms):
        return reduce(lambda x, y: unicode(x) + unicode(y), [term[VALUE] for term in terms])

    def __eq__(self, other):
        return hash(self) == hash(other)

    @py3compat.format_doctest_out
    def alphaNetworkHash(self, termHash):
        """
        We store pointers to all the system's alpha memories in a hash table, indexed
        according to the particular values being tested. Executing the alpha network then becomes a
        simple matter of doing eight hash table lookups:

        >>> aNode1 = AlphaNode((Variable('Z'), RDF.type, Variable('A')))
        >>> aNode2 = AlphaNode((Variable('X'), RDF.type, Variable('C')))
        >>> token = ReteToken((URIRef('urn:uuid:Boo'), RDF.type, URIRef('urn:uuid:Foo')))
        >>> token.alphaNetworkHash(aNode1.alphaNetworkHash())
        %(u)s'http://www.w3.org/1999/02/22-rdf-syntax-ns#type'

        """
        triple = list(self.asTuple())
        termHash = list(termHash)
        return ''.join([triple[idx] for idx in TERMS if termHash[idx] == '1'])

    def unboundCopy(self, noSubsequentDebug=False):
        if noSubsequentDebug:
            return ReteToken((self.subject[VALUE], self.predicate[VALUE], self.object_[VALUE]))
        else:
            return ReteToken(
                (self.subject[VALUE],
                 self.predicate[VALUE],
                 self.object_[VALUE]), self.debug)

    def __repr__(self):
        return "<ReteToken: %s>" % (
            ', '.join(["%s->%s" % (var, val) for var, val in self.getVarBindings(False)])
        )

    def getVarBindings(self, asDict=True):
        _vars = []
        for var, val in [self.subject, self.predicate, self.object_]:
            if isinstance(var, (Variable)):
                _vars.append((var, val))
        return dict(_vars) if asDict else _vars

    def getUniterm(self):
        from FuXi.Horn.PositiveConditions import BuildUnitermFromTuple
        return BuildUnitermFromTuple(tuple(
                [val for var, val in [self.subject, self.predicate, self.object_]]))

    def asTuple(self):
        return (self.subject[VALUE], self.predicate[VALUE], self.object_[VALUE])

    def bindVariables(self, thing):
        """
        This function, called when a token passes a node test, associates
        token terms with variables in the node test
        """
        if isinstance(thing, BuiltInAlphaNode):
            self.pattern = list(thing.n3builtin)
            self.subject = (thing.n3builtin.argument, self.subject[VALUE])
            self.predicate = (thing.n3builtin.uri, self.predicate[VALUE])
            self.object_ = (thing.n3builtin.result, self.object_[VALUE])
            assert not self.bindingDict, self.bindingDict
            bindHashItems = []
            for var, val in [self.subject, self.predicate, self.object_]:
                if var and isinstance(var, (Variable, BNode)) and var not in self.bindingDict:
                    self.bindingDict[var] = val
                    bindHashItems.append(var + val)
                else:
                    bindHashItems.append(val)
            #self.bindingDict := { var1 -> val1, var2 -> val2, ..  }
            self.hash = hash(reduce(lambda x, y: x + y, bindHashItems))
            return self
        elif isinstance(thing, AlphaNode):
            self.pattern = thing.triplePattern
            self.subject = (thing.triplePattern[SUBJECT], self.subject[VALUE])
            self.predicate = (thing.triplePattern[PREDICATE], self.predicate[VALUE])
            self.object_ = (thing.triplePattern[OBJECT], self.object_[VALUE])
            assert not self.bindingDict, self.bindingDict
            bindHashItems = []
            for var, val in [self.subject, self.predicate, self.object_]:
                if var and isinstance(var, (Variable, BNode)) and var not in self.bindingDict:
                    self.bindingDict[var] = val
                    bindHashItems.append(var + val)
                else:
                    bindHashItems.append(val)
            #self.bindingDict := { var1 -> val1, var2 -> val2, ..  }
            self.hash = hash(reduce(lambda x, y: x + y, bindHashItems))
            return self
        elif isinstance(thing, dict):
            revDict = dict([(v, k) for k, v in list(thing.items())])
            # create mapping from variable to value if in range of mapping
            self.subject = (revDict.get(self.subject[VALUE], self.subject[VALUE]), self.subject[VALUE])
            self.predicate = (revDict.get(self.predicate[VALUE], self.predicate[VALUE]), self.predicate[VALUE])
            self.object_ = (revDict.get(self.object_[VALUE], self.object_[VALUE]), self.object_[VALUE])


def defaultIntraElementTest(aReteToken, triplePattern):
    """
    'Standard' Charles Forgy intra element token pattern test.
    """
    tokenTerms = [aReteToken.subject[VALUE], aReteToken.predicate[VALUE], aReteToken.object_[VALUE]]
    varBindings = {}
    for idx in [SUBJECT, PREDICATE, OBJECT]:
        tokenTerm = tokenTerms[idx]
        patternTerm = triplePattern[idx]
        if not isinstance(patternTerm, (Variable, BNode)) and tokenTerm != patternTerm:
            return False
        elif patternTerm in varBindings and varBindings[patternTerm] != tokenTerm:
            return False
        elif patternTerm not in varBindings:
            varBindings[patternTerm] = tokenTerm
    return True


class AlphaNode(Node):
    """
    Basic Triple Pattern Pattern check
    """
    def __init__(self, triplePatternOrFunc, filters=None):
        filters = filters and filters or {}
        self.relinked = False
        self.name = BNode()
        self.triplePattern = triplePatternOrFunc
        self.descendentMemory = []
        self.descendentBetaNodes = set()
        self.builtin = bool(filters.get(self.triplePattern[PREDICATE]))
        self.universalTruths = []

    @py3compat.format_doctest_out
    def alphaNetworkHash(self, groundTermHash=False, skolemTerms=[]):
        """
        Thus, given a WME w, to determine which alpha memories w should be added to, we need only check whether
        any of these eight possibilities is actually present in the system.  (Some might not be present, since
        there might not be any alpha memory corresponding to that particular combination of tests and 's.)

        0 - Variable
        1 - Ground term

        >>> aNode1 = AlphaNode((Variable('P'), RDF.type, OWL_NS.InverseFunctionalProperty))
        >>> aNode2 = AlphaNode((Variable('X'), Variable('P'), Variable('Z')))
        >>> aNode1.alphaNetworkHash()
        ('0', '1', '1')
        >>> aNode2.alphaNetworkHash()
        ('0', '0', '0')
        >>> aNode1.alphaNetworkHash(groundTermHash=True)
        %(u)s'http://www.w3.org/1999/02/22-rdf-syntax-ns#typehttp://www.w3.org/2002/07/owl#InverseFunctionalProperty'
        """
        if groundTermHash:
            return ''.join([term for term in self.triplePattern
                            if not isinstance(term, (BNode, Variable)) or \
                               isinstance(term, BNode) and term in skolemTerms])
        else:
            return tuple([isinstance(term, (BNode, Variable)) and '0' or '1' for term in self.triplePattern])

    def checkDefaultRule(self, defaultRules):
        """
        Check to see if the inter element test associated with this Alpha node may match
        the given 'default' conflict set.  If so, update universalTruths with the
        default conflict set token list which if matched, means the intra element test automatically
        passes
        """
        pass

    def __repr__(self):
        return "<AlphaNode: %s. Feeds %s beta nodes>" % (
            repr(self.triplePattern), len(self.descendentBetaNodes))

    def activate(self, aReteToken):
        from .BetaNode import PartialInstantiation, LEFT_MEMORY, RIGHT_MEMORY, LEFT_UNLINKING
        # print(aReteToken.asTuple())
        # aReteToken.debug = True
        aReteToken.bindVariables(self)
        for memory in self.descendentMemory:
            singleToken = PartialInstantiation([aReteToken], consistentBindings=aReteToken.bindingDict.copy())
            # print(memory)
            # print(self)
            # print(self.descendentMemory)
            if memory.position == LEFT_MEMORY:
                memory.addToken(singleToken)
            else:
                memory.addToken(aReteToken)
            if memory.successor.leftUnlinkedNodes and len(memory) == 1 and LEFT_UNLINKING:
                # Relink left memory of successor
                # from Util import renderNetwork
                # from md5 import md5
                # from datetime import datetime
                # import os
                # print("Re-linking %s" % (memory.successor))
                # print("Re-linking triggered from %s" % (repr(self)))
                for node in memory.successor.leftUnlinkedNodes:
                    # print("\trelinking to ", node, " from ", memory.position)
                    # aReteToken.debug = True
                    if node.unlinkedMemory is None:
                        assert len(node.descendentMemory) == 1, "%s %s %s" % (
                                node, node.descendentMemory, memory.successor)
                        disconnectedMemory = list(node.descendentMemory)[0]

                    else:
                        disconnectedMemory = node.unlinkedMemory
                        node.descendentMemory.append(disconnectedMemory)
                        node.unlinkedMemory = None
                    # if aReteToken.debug:
                    #     print("\t reattached memory ", str(disconnectedMemory))
                    memory.successor.memories[LEFT_MEMORY] = disconnectedMemory
                    node.descendentBetaNodes.add(memory.successor)
                    # print(memory.successor.memories[LEFT_MEMORY])
                    memory.successor.propagate(RIGHT_MEMORY, aReteToken.debug, wme=aReteToken)

                    # node._activate(singleToken, aReteToken.debug)
                    # print("Activating re-linked node", node)
                    # node.propagate(None, aReteToken.debug)

                    # if memory.position == LEFT_MEMORY:
                    #     node.propagate(memory.position, aReteToken.debug, singleToken)
                    # else:
                    #     node.propagate(memory.position, aReteToken.debug, wme=aReteToken)

                # if memory.successor.network:
                #     dtNow = datetime.now().isoformat()
                #     fName = dtNow.replace(':', '-').replace('.', '-')
                #     renderNetwork(memory.successor.network).write_graphviz(fName+'.dot')
                #     os.popen ('dot -Tsvg -o %s %s'%(fName+'.svg', fName+'.dot'), 'r')
                #     os.remove(fName+'.dot')
                #     print(fName)

                # self.relinked = True
                memory.successor.leftUnlinkedNodes = set()

            if aReteToken.debug:
                print("Added %s to %s" % (aReteToken, memory.successor))

            if memory.successor.aPassThru or not memory.successor.checkNullActivation(memory.position):
                if aReteToken.debug:
                    print("Propagated from %s" % (self))
                    print(aReteToken.asTuple())
                if memory.position == LEFT_MEMORY:
                    memory.successor.propagate(memory.position, aReteToken.debug, singleToken)
                else:
                    memory.successor.propagate(memory.position, aReteToken.debug, wme=aReteToken)
            else:
                if aReteToken.debug:
                    print("skipped null right activation of %s from %s" % (
                            memory.successor, self))


class BuiltInAlphaNode(AlphaNode):
    """
    An Alpha Node for Builtins which doesn't participate in intraElement tests
    """
    def __init__(self, n3builtin):
        self.name = BNode()
        self.n3builtin = n3builtin
        self.descendentMemory = []
        self.descendentBetaNodes = set()
        self.universalTruths = []

    def __iter__(self):
        yield self.n3builtin.argument
        yield self.n3builtin.result

    def alphaNetworkHash(self, groundTermHash=False):
        if groundTermHash:
            return ''.join([term for term in self.n3builtin if not isinstance(term, (BNode, Variable))])
        else:
            return tuple([isinstance(term, (BNode, Variable)) and '0' or '1' for term in self.n3builtin])

    def __repr__(self):
        return "<BuiltInAlphaNode %s(%s), %s : Feeds %s beta nodes>" % (
                    self.n3builtin.func, self.n3builtin.argument,
                    self.n3builtin.result, len(self.descendentBetaNodes))

    def intraElementTest(self, aReteToken):
        pass


def test():
    import doctest
    doctest.testmod()


if __name__ == '__main__':
    test()

# from FuXi.Rete.AlphaNode import SUBJECT
# from FuXi.Rete.AlphaNode import PREDICATE
# from FuXi.Rete.AlphaNode import OBJECT
# from FuXi.Rete.AlphaNode import VARIABLE
# from FuXi.Rete.AlphaNode import VALUE
# from FuXi.Rete.AlphaNode import TERMS

# from FuXi.Rete.AlphaNode import AlphaNode
# from FuXi.Rete.AlphaNode import BuiltInAlphaNode
# from FuXi.Rete.AlphaNode import normalizeTerm
# from FuXi.Rete.AlphaNode import memoize
