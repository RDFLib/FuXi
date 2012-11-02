import rdflib
rdflib.plugin.register('sparql', rdflib.query.Processor,
                      'rdfextras.sparql.processor', 'Processor')
rdflib.plugin.register('sparql', rdflib.query.Result,
                      'rdfextras.sparql.query', 'SPARQLQueryResult')


def _debug(*args, **kw):
    import logging
    logging.basicConfig(level=logging.ERROR, format="%(message)s")
    logger = logging.getLogger(__name__)
    logger.debug(*args, **kw)
