import unittest
import logging
logging.basicConfig(level=logging.DEBUG)

from FuXi.Rete.Network import HashablePatternList
from rdflib import URIRef, Literal
# import rdflib.term


class TestHashablePatternList(unittest.TestCase):
    def setUp(self):
        super(TestHashablePatternList, self).setUp()

        # self.oldWarning = rdflib.term._LOGGER.warning
        # def stopOnWarning(msg):
        #     raise ValueError("this warning was logged: %s" % msg)
        # rdflib.term._LOGGER.warning = stopOnWarning

    def tearDown(self):
        super(TestHashablePatternList, self).tearDown()
        # rdflib.term._LOGGER.warning = self.oldWarning

    def testCombineUriAndLiteral(self):
        # This is a simplified version of input that happens in real usage with a rule like this:
        # { ?c :p1 ?uri . } => { ?c :p2 (" " ?uri) . } .
        hpl = HashablePatternList(items=[(URIRef('http://example.com/'),),
                                         (Literal(' '),)])
        hash(hpl)

if __name__ == '__main__':
    unittest.main()
