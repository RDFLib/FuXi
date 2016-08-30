# -*- coding: utf-8 -*-
"""
"""
import unittest
from rdflib import Graph
from rdflib import Literal
from FuXi.Syntax.InfixOWL import (
    Class,
    EnumeratedClass,
    OWL_NS,
    Property,
    Restriction,
)
from FuXi.Syntax.InfixOWL import some
from FuXi.Syntax.InfixOWL import max
from rdflib.namespace import (Namespace, NamespaceManager)
from pprint import pformat

exNs = Namespace('http://example.com/')

a = b = c = None


class TestUnitTestAction(unittest.TestCase):

    def setUp(self):
        self.nsm = NamespaceManager(Graph())
        self.nsm.bind('ex', exNs, override=False)
        self.nsm.bind('owl', OWL_NS, override=False)
        self.graph = Graph()
        self.graph.namespace_manager = self.nsm

    def test_owlpyclasses(self):
        # Now we have an empty Graph, we can construct OWL classes in it using the
        # Python classes defined in this module

        a = Class(exNs.Opera, graph=self.graph)

        # Now we can assert rdfs:subClassOf and owl:equivalentClass relationships
        # (in the underlying graph) with other classes using the subClassOf and
        # equivalentClass descriptors which can be set to a list of objects for
        # the corresponding predicates.

        a.subClassOf = [exNs.MusicalWork]

        # We can then access the rdfs:subClassOf relationships

        assert pformat(list(a.subClassOf)) == '[Class: ex:MusicalWork ]', pformat(list(a.subClassOf))

        # This can also be used against already populated graphs:

        owlGraph = Graph().parse(str(OWL_NS))
        nsm = self.graph.namespace_manager
        nsm.bind('owl', OWL_NS, override=False)
        owlGraph.namespace_manager = nsm

        assert pformat(
            list(Class(OWL_NS.Class, graph=owlGraph).subClassOf)) == \
            '[Class: rdfs:Class ]'

    def test_subclass(self):
        # Operators are also available. For instance we can add ex:Opera to the
        # extension of the ex:CreativeWork class via the '+=' operator

        a = Class(exNs.Opera, graph=self.graph)
        a.subClassOf = [exNs.MusicalWork]
        # assert str(a) == 'Class: ex:Opera SubClassOf: ex:MusicalWork'
        assert str(a) == "Class: ex:Opera SubClassOf: b'ex:MusicalWork'", str(a)

        b = Class(exNs.CreativeWork, graph=self.graph)
        b += a

        assert pformat(list(a.subClassOf)) == \
            '[Class: ex:CreativeWork , Class: ex:MusicalWork ]' or \
            '[Class: ex:MusicalWork , Class: ex:CreativeWork ]'

        # And we can then remove it from the extension as well

        b -= a
        a

        # assert pformat(a) == 'Class: ex:Opera SubClassOf: ex:MusicalWork'
        assert pformat(a) == "Class: ex:Opera SubClassOf: b'ex:MusicalWork'", pformat(a)

    def test_booleans(self):
        # Boolean class constructions can also be created with Python operators
        # For example, The | operator can be used to construct a class consisting
        # of a owl:unionOf the operands:

        a = Class(exNs.Opera, graph=self.graph)
        a.subClassOf = [exNs.MusicalWork]
        b = Class(exNs.CreativeWork, graph=self.graph)
        c = a | b | Class(exNs.Work, graph=self.graph)

        # assert(pformat(c)) == '( ex:Opera OR ex:CreativeWork OR ex:Work )'
        assert(pformat(c)) == "( b'ex:Opera' OR b'ex:CreativeWork' OR b'ex:Work' )", pformat(c)

        # Boolean class expressions can also be operated as lists (natively in python)

        del c[c.index(Class(exNs.Work, graph=self.graph))]

        # assert pformat(c) == '( ex:Opera OR ex:CreativeWork )'
        assert pformat(c) == "( b'ex:Opera' OR b'ex:CreativeWork' )", pformat(c)

    def test_ampersand_logical_operator(self):
        # The '&' operator can be used to construct class intersection:

        woman = Class(exNs.Female, graph=self.graph) & Class(exNs.Human, graph=self.graph)
        woman.identifier = exNs.Woman

        assert pformat(woman) == '( ex:Female AND ex:Human )', pformat(woman)

    def test_owl_enumerated_classes(self):
        # Enumerated classes can also be manipulated

        contList = [
            Class(exNs.Africa, graph=self.graph),
            Class(exNs.NorthAmerica, graph=self.graph)
        ]

        # assert pformat(EnumeratedClass(members=contList, graph=self.graph)) == \
        #     '{ ex:Africa ex:NorthAmerica }'
        assert pformat(EnumeratedClass(members=contList, graph=self.graph)) == \
            "{ b'ex:Africa' b'ex:NorthAmerica' }", pformat(EnumeratedClass(members=contList, graph=self.graph))

    def test_owl_restrictions(self):
        # owl:Restrictions can also be instantiated:

        # assert pformat(Restriction(exNs.hasParent, graph=self.graph, allValuesFrom=exNs.Human)) == \
        #     '( ex:hasParent ONLY ex:Human )'
        assert pformat(Restriction(exNs.hasParent, graph=self.graph, allValuesFrom=exNs.Human)) == \
            "( ex:hasParent ONLY b'ex:Human' )", pformat(Restriction(exNs.hasParent, graph=self.graph, allValuesFrom=exNs.Human))

    def test_manchester_owl_restrictions(self):
        # Restrictions can also be created using Manchester OWL syntax in
        # 'colloquial' Python. A Python infix operator recipe was used for
        # this purpose. See below

        assert pformat(
            exNs.hasParent | some | Class(exNs.Physician, graph=self.graph)) == \
            '( ex:hasParent SOME ex:Physician )', pformat(exNs.hasParent | some | Class(exNs.Physician, graph=self.graph))

        assert pformat(
            Property(exNs.hasParent, graph=self.graph) | max | Literal(1)) == \
            '( ex:hasParent MAX 1 )', pformat(Property(exNs.hasParent, graph=self.graph) | max | Literal(1))


if __name__ == '__main__':
    suite = unittest.makeSuite(TestUnitTestAction)
    unittest.TextTestRunner(verbosity=5).run(suite)


