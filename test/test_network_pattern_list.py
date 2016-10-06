import unittest
import logging
logging.basicConfig(level=logging.DEBUG)

from FuXi.Rete.Network import HashablePatternList
from rdflib import URIRef, Literal
<<<<<<< HEAD
import rdflib.term
=======
# import rdflib.term

>>>>>>> 29b6d7bff057aed20dd8d8880c839a484a3acd7f

class TestHashablePatternList(unittest.TestCase):
    def setUp(self):
        super(TestHashablePatternList, self).setUp()
<<<<<<< HEAD
        
        self.oldWarning = rdflib.term._LOGGER.warning
        def stopOnWarning(msg):
            raise ValueError("this warning was logged: %s" % msg)
        rdflib.term._LOGGER.warning = stopOnWarning
        
    def tearDown(self):
        super(TestHashablePatternList, self).tearDown()
        rdflib.term._LOGGER.warning = self.oldWarning
        
=======

        # self.oldWarning = rdflib.term._LOGGER.warning
        # def stopOnWarning(msg):
        #     raise ValueError("this warning was logged: %s" % msg)
        # rdflib.term._LOGGER.warning = stopOnWarning

    def tearDown(self):
        super(TestHashablePatternList, self).tearDown()
        # rdflib.term._LOGGER.warning = self.oldWarning

>>>>>>> 29b6d7bff057aed20dd8d8880c839a484a3acd7f
    def testCombineUriAndLiteral(self):
        # This is a simplified version of input that happens in real usage with a rule like this:
        # { ?c :p1 ?uri . } => { ?c :p2 (" " ?uri) . } .
        hpl = HashablePatternList(items=[(URIRef('http://example.com/'),),
                                         (Literal(' '),)])
        hash(hpl)

if __name__ == '__main__':
    unittest.main()
