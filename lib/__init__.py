import rdflib
rdflib.plugin.register('sparql', rdflib.query.Processor,
                      'rdfextras.sparql.processor', 'Processor')
rdflib.plugin.register('sparql', rdflib.query.Result,
                      'rdfextras.sparql.query', 'SPARQLQueryResult')
