import logging

def debug(*args, **kw):
    logging.basicConfig(level=logging.ERROR, format="%(message)s")
    logger = logging.getLogger(__name__)
    logger.debug(*args, **kw)
