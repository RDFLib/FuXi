"""
RIF Core parser for FuXi.

Parses RIF Core XML (and RIF In RDF) syntaxes into FuXi (converts the former
into the latter).

Supports Frames and atoms with only two positional arguments.  Follows import
trail.
"""

import os
import urllib2
import logging
from lxml import etree
from rdflib.graph import Graph
from rdflib import Namespace, RDF, Variable, URIRef
from rdflib.util import first
from rdflib.collection import Collection
from FuXi.Horn.PositiveConditions import And, ExternalFunction, Uniterm
from FuXi.Horn.HornRules import Rule, Clause


def _debug(*args, **kw):
    logging.basicConfig(level=logging.DEBUG, format="%(message)s")
    logger = logging.getLogger(__name__)
    logger.debug(*args, **kw)


__all__ = [
    'RIFCoreParser',
    'SmartRedirectHandler',
    'RIF_NS',
    'XSD_NS',
    'mimetypes',
    ]


class SmartRedirectHandler(urllib2.HTTPRedirectHandler):
    def http_error_301(self, req, fp, code, msg, headers):
        result = urllib2.HTTPRedirectHandler.http_error_301(
            self, req, fp, code, msg, headers)
        result.status = code
        return result

    def http_error_302(self, req, fp, code, msg, headers):
        result = urllib2.HTTPRedirectHandler.http_error_302(
            self, req, fp, code, msg, headers)
        result.status = code
        return result

RIF_NS = Namespace('http://www.w3.org/2007/rif#')
XSD_NS = Namespace('http://www.w3.org/2001/XMLSchema#')

mimetypes = {
    'application/rdf+xml': 'xml',
    'text/n3': 'n3',
    'text/turtle': 'turtle',
}

# TRANSFORM_URI = iri.absolutize(
#        'rif-core-rdf.xsl',iri.os_path_to_uri(__file__))

__fpath__ = os.path.split(__file__)[0]

if 'build/src/' in __fpath__:
    __fpath__ = ''.join(__fpath__.split('build/src/'))

TRANSFORM_URI = 'file://' + os.path.join(__fpath__, 'rif-core-rdf.xsl')


IMPLIES_PARTS = \
"""
SELECT DISTINCT ?impl ?body ?bodyType ?head ?headType {
    ?impl a             rif:Implies;
          rif:if        ?body;
          rif:then      ?head .
    ?body a             ?bodyType .
    ?head a             ?headType .
}
"""

RULE_PARTS = \
"""
SELECT DISTINCT ?rule ?vars ?impl {
    ?rule a             rif:Forall;
          rif:formula   ?impl;
          rif:vars      ?vars
}
"""

FRAME_PARTS = \
"""
SELECT ?frame ?object ?slots {
    ?frame  a           rif:Frame;
            rif:object  ?object;
            rif:slots   ?slots
}
"""

EXTERNAL_PARTS = \
"""
SELECT ?external ?args ?op {
    ?external   a           rif:External;
                rif:content [ a rif:Atom; rif:args ?args; rif:op ?op ]
}
"""

ATOM_PARTS = \
"""
SELECT ?atom ?args ?op {
    ?atom   a        rif:Atom;
            rif:args ?args;
            rif:op ?op
}
"""

rif_namespaces = {u'rif': RIF_NS}


class RIFCoreParser(object):
    def __init__(self, location=None, graph=None, debug=False):
        self.location = location
        self.rules = {}
        if graph:
            assert location is None, "Must supply one of graph or location"
            self.graph = graph
            if debug:
                _debug("RIF in RDF graph was provided")
        else:
            assert graph is None, "Must supply one of graph or location"
            if debug:
                _debug("RIF document URL provided %s" % location)
            if self.location.find('http:') + 1:
                req = urllib2.Request(self.location)

                #From:
                #http://www.diveintopython.org/http_web_services/redirects.html
                # points an 'opener' to the address to 'sniff' out final
                # Location header
                opener = urllib2.build_opener(SmartRedirectHandler())
                f = opener.open(req)
                self.content = f.read()
            else:
                self.content = urllib2.urlopen(self.location).read()
                # self.content = open(self.location).read()
            try:
                transform = etree.XSLT(etree.parse(TRANSFORM_URI))
                self.graph = Graph().parse(
                    data=etree.tostring(
                        transform(etree.fromstring(self.content))))
                if debug:
                    _debug("Extracted rules from RIF XML format")
            except ValueError:
                try:
                    self.graph = Graph().parse(data=self.content, format='xml')
                except:
                    self.graph = Graph().parse(data=self.content, format='n3')
                if debug:
                    _debug("Extracted rules from RIF in RDF document")

    def getRuleset(self):
        """
        >>> parser = RIFCoreParser('http://www.w3.org/2005/rules/test/repository/tc/Frames/Frames-premise.rif')
        >>> for rule in parser.getRuleset(): print(rule)
        Forall ?Customer ( ns1:discount(?Customer 10) :- ns1:status(?Customer "gold"^^<http://www.w3.org/2001/XMLSchema#string>) )
        Forall ?Customer ( ns1:discount(?Customer 5) :- ns1:status(?Customer "silver"^^<http://www.w3.org/2001/XMLSchema#string>) )
        >>> parser = RIFCoreParser('http://www.w3.org/2005/rules/test/repository/tc/Guards_and_subtypes/Guards_and_subtypes-premise.rif')
        >>> for rule in parser.getRuleset(): print(rule)
        """
        self.implications = dict([(impl, (body, bodyType, head, headType))
                                    for impl, body, bodyType, head, headType in
                                        self.graph.query(IMPLIES_PARTS, initNs=rif_namespaces)])
        self.rules = dict([(rule, (vars, impl))
                                for rule, vars, impl
                                    in self.graph.query(RULE_PARTS,
                                                        initNs=rif_namespaces)])
        self.frames = dict([(frame, (obj, slots))
            for frame, obj, slots in self.graph.query(FRAME_PARTS,
                                                    initNs=rif_namespaces)])

        self.atoms = dict([(atom, (args, op))
                                for atom, args, op in self.graph.query(
                                        ATOM_PARTS,
                                        initNs=rif_namespaces)])

        self.externals = dict([(external, (args, op))
                               for external, args, op in self.graph.query(
                                    EXTERNAL_PARTS,
                                    initNs=rif_namespaces)])
        rt = []
        for sentenceCollection in self.graph.objects(predicate=RIF_NS.sentences):
            col = Collection(self.graph, sentenceCollection)
            for sentence in col:
                if RIF_NS.Implies in self.graph.objects(sentence, RDF.type):
                    rt.append(self.extractImp(sentence))
                elif RIF_NS.Forall in self.graph.objects(sentence, RDF.type):
                    rt.append(self.extractRule(sentence))
        return rt

    def extractImp(self, impl):
        body, bodyType, head, headType = self.implications[impl]
        head = first(self.extractPredication(head, headType))
        if bodyType == RIF_NS.And:
            raise
        else:
            body = self.extractPredication(body, bodyType)

        body = And([first(body)]) if len(body) == 1 else And(body)
        return Rule(Clause(body, head), declare=[])

    def extractRule(self, rule):
        vars, impl = self.rules[rule]
        body, bodyType, head, headType = self.implications[impl]
        allVars = map(self.extractTerm, Collection(self.graph, vars))
        head = first(self.extractPredication(head, headType))
        if bodyType == RIF_NS.And:
            body = [first(self.extractPredication(
                       i,
                       first(self.graph.objects(i, RDF.type)))
                   ) for i in Collection(self.graph,
                        first(self.graph.objects(body, RIF_NS.formulas)))]

        else:
            body = self.extractPredication(body, bodyType)

        body = And([first(body)]) if len(body) == 1 else And(body)
        return Rule(
            Clause(body, head),
            declare=allVars,
            nsMapping=dict(self.graph.namespaces())
        )

    def extractPredication(self, predication, predType):
        if predType == RIF_NS.Frame:
            return self.extractFrame(predication)
        elif predType == RIF_NS.Atom:
            return [self.extractAtom(predication)]
        else:
            assert predType == RIF_NS.External
            # from FuXi.Rete.RuleStore import N3Builtin
            # N3Builtin(self, uri, func, argument, result)
            args, op = self.externals[predication]
            args = list(map(self.extractTerm, Collection(self.graph, args)))
            op = self.extractTerm(op)
            return [ExternalFunction(Uniterm(op, args))]

    def extractAtom(self, atom):
        args, op = self.atoms[atom]
        op = self.extractTerm(op)
        args = list(map(self.extractTerm, Collection(self.graph, args)))
        if len(args) > 2:
            raise NotImplementedError(
                "FuXi RIF Core parsing only supports subset involving binary/unary Atoms"
            )
        return Uniterm(op, args)

    def extractFrame(self, frame):
        obj, slots = self.frames[frame]
        rt = []
        for slot in Collection(self.graph, slots):
            k = self.extractTerm(first(self.graph.objects(slot, RIF_NS.slotkey)))
            v = self.extractTerm(first(self.graph.objects(slot, RIF_NS.slotvalue)))
            rt.append(
                Uniterm(k, [self.extractTerm(obj), v])
            )
        return rt

    def extractTerm(self, term):
        if (term, RDF.type, RIF_NS.Var) in self.graph:
            return Variable(first(self.graph.objects(term, RIF_NS.varname)))
        elif (term, RIF_NS.constIRI, None) in self.graph:
            iriLit = first(self.graph.objects(term, RIF_NS.constIRI))
            assert iriLit.datatype == XSD_NS.anyURI
            return URIRef(iriLit)
        else:
            return first(self.graph.objects(term, RIF_NS.value))


def test():
    import doctest
    doctest.testmod()

if __name__ == '__main__':
    # test()
    parser = RIFCoreParser('http://www.w3.org/2005/rules/test/repository/tc/Guards_and_subtypes/Guards_and_subtypes-premise.rif')
    for rule in parser.getRuleset():
        _debug(rule)

# from FuXi.Horn.RIFCore import RIFCoreParser
# from FuXi.Horn.RIFCore import SmartRedirectHandler
# from FuXi.Horn.RIFCore import RIF_NS
# from FuXi.Horn.RIFCore import XSD_NS
# from FuXi.Horn.RIFCore import mimetypes
