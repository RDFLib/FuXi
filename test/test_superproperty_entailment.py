#!/usr/bin/env python
# encoding: utf-8

import unittest
from pprint import pformat
from rdflib import Graph, Namespace
from FuXi.Rete.RuleStore import SetupRuleStore
from FuXi.Rete.Util import generateTokenSet
from FuXi.DLP.DLNormalization import NormalFormReduction
import logging

logging.basicConfig(level=logging.DEBUG, format="%(message)s")


def _debug(*args, **kw):
    _logger = logging.getLogger(__name__)
    _logger.setLevel(logging.DEBUG)
    _logger.debug(*args, **kw)

EX = Namespace('http://example.org/')
EX_TERMS = Namespace('http://example.org/terms/')

expected_triples = [
    (EX.john, EX_TERMS.has_sibling, EX.jack),
    (EX.john, EX_TERMS.brother, EX.jack),
    (EX.jack, EX_TERMS.has_brother, EX.john),
]

ABOX = \
"""
@prefix exterms: <http://example.org/terms/> .
@prefix : <http://example.org/> .

:john exterms:has_brother :jack .
:jack exterms:brother     :john .
"""

TBOX = \
"""
@prefix exterms: <http://example.org/terms/> .
@prefix rdf: <http://www.w3.org/1999/02/22-rdf-syntax-ns#> .
@prefix rdfs: <http://www.w3.org/2000/01/rdf-schema#> .
@prefix owl: <http://www.w3.org/2002/07/owl#>.

exterms:Agent
    a rdfs:Class .

exterms:Person
    a rdfs:Class ;
    rdfs:subClassOf exterms:Agent .

exterms:has_sibling
    a rdf:Property .

exterms:has_brother
    a rdf:Property ;
    rdfs:subPropertyOf exterms:has_sibling ;
    rdfs:domain exterms:Person ;
    rdfs:range exterms:Person .

exterms:brother
    a rdf:Property ;
    owl:equivalentProperty exterms:has_brother ;
    rdfs:domain exterms:Person ;
    rdfs:range exterms:Person .

"""


class test_superproperty_entailment(unittest.TestCase):
    def setUp(self):
        self.rule_store, self.rule_graph, self.network = \
                            SetupRuleStore(makeNetwork=True)
        self.tBoxGraph = Graph().parse(data=TBOX, format='n3')

        self.aBoxGraph = Graph().parse(data=ABOX, format='n3')
        NormalFormReduction(self.tBoxGraph)

    def testReasoning(self):
        _debug('setting up DLP...')
        self.network.setupDescriptionLogicProgramming(self.tBoxGraph)
        _debug("Rules:\n %s" % pformat(list(self.network.rules)))
        _debug(self.network)

        _debug('feeding TBox... ')
        self.network.feedFactsToAdd(generateTokenSet(self.tBoxGraph))
        _debug('feeding ABox...')
        self.network.feedFactsToAdd(generateTokenSet(self.aBoxGraph))

        self.network.inferredFacts.bind('ex', EX)
        self.network.inferredFacts.bind('exterms', EX_TERMS)
        _debug("Facts:\n%s" % (
            self.network.inferredFacts.serialize(format='n3')))

        for triple in expected_triples:
            self.failUnless(
                triple in self.network.inferredFacts, \
                    "Missing %s" % (repr(triple)))

        self.failUnless(3 == 2)

if __name__ == '__main__':
    unittest.main()
