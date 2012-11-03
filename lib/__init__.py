import logging
import rdflib
rdflib.plugin.register('sparql', rdflib.query.Processor,
                      'rdfextras.sparql.processor', 'Processor')
rdflib.plugin.register('sparql', rdflib.query.Result,
                      'rdfextras.sparql.query', 'SPARQLQueryResult')
rdflib.plugin.register('text/xml', rdflib.parser.Parser,
                'rdflib.plugins.parsers.rdfxml', 'RDFXMLParser')


def debug(*args, **kw):
    logging.basicConfig(level=logging.ERROR, format="%(message)s")
    logger = logging.getLogger(__name__)
    logger.debug(*args, **kw)
