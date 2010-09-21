'''
Created on Sep 16, 2010

@author: onewnan

A single command that runs all FuXi unit tests.  If option --variants is set 
then testOWLis run all three ways --'gms','sld' and 'bfp' -- to maximize coverage.

If a coverage tool is installed this module can help generate coverage statistics, e.g.,

    coverage run suite.py --variants
    coverage report
'''
import unittest
import additionalDLPTests
import test_builtin_ordering
import test_network_reset
import test_superproperty_entailment
import testExistentialInHead
import testOWL
import testSkolemization


def suite():
    suite = unittest.TestSuite()
    suite.addTest(unittest.makeSuite(additionalDLPTests.AdditionalDescriptionLogicTests,'test'))
    suite.addTest(unittest.makeSuite(test_builtin_ordering.URIRefStringStartsWith,'test'))
    suite.addTest(unittest.makeSuite(test_network_reset.NetworkReset,'test'))
    suite.addTest(unittest.makeSuite(test_superproperty_entailment.test_superproperty_entailment,'test'))
    suite.addTest(unittest.makeSuite(testExistentialInHead.ExistentialInHeadTest,'test'))
    suite.addTest(unittest.makeSuite(testSkolemization.UnionSkolemizedTest,'test'))
    return suite

def splash(txt):
    print "running " + txt + " ===================================="
    
if __name__ == "__main__":
    #import sys;sys.argv = ['', 'Test.testName']
    from optparse import OptionParser
    op = OptionParser('usage: %prog [options]')
    op.add_option('--variants', 
                  action='store_true',
                  default=False,
      help = 'Whether to run testOwl all three ways or just bottom up ')    
    (options, facts) = op.parse_args()
    suite = suite()
    splash("non-OWL suite")
    unittest.TextTestRunner(verbosity=2).run(suite)
    testOWLoptions = testOWL.defaultOptions()
    splash("testOWL " + testOWLoptions.strategy)
    testOWL.runTests(testOWLoptions)
    if options.variants:
        testOWLoptions.strategy = "sld"
        splash("testOWL " + testOWLoptions.strategy)
        testOWL.runTests(testOWLoptions)
        testOWLoptions.strategy = "bfp"
        splash("testOWL " + testOWLoptions.strategy)
        testOWL.runTests(testOWLoptions)
