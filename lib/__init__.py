import rdflib
if rdflib.__version__.startswith('3'):
    rdflib.plugin.register('sparql', rdflib.query.Processor,
                          'rdfextras.sparql.processor', 'Processor')
    rdflib.plugin.register('sparql', rdflib.query.Result,
                          'rdfextras.sparql.query', 'SPARQLQueryResult')
