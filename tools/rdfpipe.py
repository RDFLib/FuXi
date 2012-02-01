#!/usr/bin/env python
import sys
from pprint import pprint

try:
    from rdflib.graph import Graph, ConjunctiveGraph
    from rdflib.namespace import NamespaceManager
except ImportError:
    from rdflib.Graph import Graph, ConjunctiveGraph
    from rdflib.syntax.NamespaceManager import NamespaceManager
from rdflib import Namespace, plugin, RDF, RDFS, URIRef
from rdflib.store import Store

from FuXi.Rete import ReteNetwork
from FuXi.Rete.RuleStore import N3RuleStore
from FuXi.Rete.Util import generateTokenSet

from Ft.Lib import Uri

RDFLIB_CONNECTION=''
RDFLIB_STORE='IOMemory'

def main():
  from optparse import OptionParser

  parser = OptionParser()
  parser.add_option('--stdin', type="choice",
    choices = ['xml', 'trix', 'n3', 'nt', 'rdfa'],
    help = 'Parse RDF from STDIN (useful for piping) with given format')
  parser.add_option('-x', '--xml', action='append',
    help = 'Append to the list of RDF/XML documents to parse')
  parser.add_option('-t', '--trix', action='append',
    help = 'Append to the list of TriX documents to parse')
  parser.add_option('-n', '--n3', action='append',
    help = 'Append to the list of N3 documents to parse')
  parser.add_option('--nt', action='append',
    help = 'Append to the list of NT documents to parse')
  parser.add_option('-a', '--rdfa', action='append',
    help = 'Append to the list of RDFa documents to parse')

  parser.add_option('-o', '--output', type="choice",
    choices = ['n3', 'xml', 'pretty-xml', 'TriX', 'turtle', 'nt'],
    help = 'Format of the final serialized RDF graph')

  parser.add_option('-m', '--ns', action='append',
    help = 'Register a namespace binding (QName prefix to a base URI)')

  parser.add_option('-r', '--rules', action='append',
    help = 'Append to the list of fact files to use to perform reasoning')
  parser.add_option('-i', '--inferred',
    help = 'URI to use for the graph containing any inferred triples')

  parser.set_defaults(
      xml=[], trix=[], n3=[], nt=[], rdfa=[], ns=[],
      output='n3'
    )

  (options, args) = parser.parse_args()

  store = plugin.get(RDFLIB_STORE,Store)()        
  store.open(RDFLIB_CONNECTION)

  namespace_manager = NamespaceManager(Graph())
  for prefixDef in options.ns:
    prefix, uri = prefixDef.split('=')
    namespace_manager.bind(prefix, uri, override=False)    

  factGraph = ConjunctiveGraph(store) 
  for graphRef in options.xml:
    factGraph.parse(graphRef, publicID=Uri.OsPathToUri(graphRef),
                    format='xml')
  for graphRef in options.trix:
    factGraph.parse(graphRef, publicID=Uri.OsPathToUri(graphRef),
                    format='trix')
  for graphRef in options.n3:
    factGraph.parse(graphRef, publicID=Uri.OsPathToUri(graphRef),
                    format='n3')
  for graphRef in options.nt:
    factGraph.parse(graphRef, publicID=Uri.OsPathToUri(graphRef),
                    format='nt')
  for graphRef in options.rdfa:
    factGraph.parse(graphRef, publicID=Uri.OsPathToUri(graphRef),
                    format='rdfa')
  if options.stdin:
    factGraph.parse(sys.stdin, format=options.stdin)

  if options.inferred and len(options.rules) > 0:
    inferredURI = URIRef(options.inferred)
    ruleStore = N3RuleStore()
    ruleGraph = Graph(ruleStore)
    for ruleFile in options.rules:
      ruleGraph.parse(ruleFile, format='n3')
    tokenSet = generateTokenSet(factGraph)
    deltaGraph = Graph(store=factGraph.store,
                       identifier=inferredURI)
    network = ReteNetwork(ruleStore,
                          inferredTarget=deltaGraph)
    network.feedFactsToAdd(tokenSet)

  print factGraph.serialize(destination=None, format=options.output,
                            base=None)
  store.rollback()

if __name__ == "__main__":
    main()
