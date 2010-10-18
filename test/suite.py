'''
Created on Sep 16, 2010

@author: onewnan

Run all FuXi tests.  

If option --variants is set then testOWLis run all three ways,
'gms','sld' and 'bfp', to maximize coverage.

If a coverage tool is installed this module can help generate coverage statistics, e.g.,

    coverage run --branch suite.py 
    coverage report
    coverage html
'''
import doctest
import unittest
import additionalDLPTests
import imp
import FuXi
import os
import sys
import test_builtin_ordering
import test_network_reset
import test_superproperty_entailment
import testExistentialInHead
import testOWL
import testSkolemization
import traceback
from unittest import TestResult

FILES_TO_IGNORE = ('suite.py', 'CommandLine.py')
VISUAL_SEPARATOR = "===================================="
modsWithLoadErrors = []

def moduleIterator(name):
    '''
    Successively return all modules in all package 'name'.
    '''
    OTHER_EXTENSIONS = ('.pyo','.pyc' )
    stack = []
    try:
        file, packageRoute, description = imp.find_module(name)
        package = imp.load_module(name, file, packageRoute, description)
    except ImportError, err:
        print 'ImportError:', err
        return
    if file:
        raise ImportError('Not a package: %r', name)
        file.close()
        return
    else:
        stack.append((name, packageRoute, package))
    while stack:
        name, packageRoute, package = stack.pop()
        packagePath = package.__path__
        for entry in os.listdir(packageRoute):
            if not entry:
                continue
            if entry in FILES_TO_IGNORE:
                pass
            elif entry.endswith('.py'):
                modName = entry[:-3]
                try:
                    file, pathName, description = imp.find_module(modName, packagePath)
                    qualName = name + '.' + modName
                    mod = imp.load_module(qualName, file, pathName, description)
                    yield (entry, mod)
                except:
                    fullPath = packageRoute + os.sep + modName
                    modsWithLoadErrors.append(modName)
                    print "ERROR -- exception loading " + fullPath
                    if traceback:
                        traceback.print_exc()
                finally:
                    file.close()
            elif entry.find('.') != -1:
                pass
            else:
                newRoute = packageRoute + os.sep + entry
                file, newPath, description = imp.find_module(entry, packagePath)
                #mod = imp.load_module("__main__", file, pathName, description)
                qualName = name + "." + entry
                mod = imp.load_module(qualName, file, newPath, description)
                stack.append((qualName, newRoute, mod))
def addTestsToSuite(mod, suite):
    '''
    Examine the dictionary of mod and add its test cases to suite.
    
    '''
    for entry in mod.__dict__:
        if isinstance(mod.__dict__[entry], unittest.TestCase):
            tests = unittest.TestLoader().loadTestsFromTestCase(entry)
            suite.add(tests)
def runSuite(title, suite, summary):
    '''
    Run the TestSuite, appending results including 'title' to list of strings 'results'.
    '''
    splash("Running " + title)
    sys.argv = [""]
    results = TestResult()
    suite.run(results)
    summary.append(("Summary of %s " % (title)) + VISUAL_SEPARATOR)
    summary.append("* Ran %i tests with %i failures and %i errors." \
        % (results.testsRun, results.failures.__len__(), results.errors.__len__()))
    if results.failures.__len__():
        summary.append("* Failed tests were:")
        for test, trace in results.failures:
            print "FAILURE with unit test: ", test
            print trace
            summary.append(repr(test))
    if results.errors.__len__():
        summary.append("* Tests in error were:")
        for test, trace in results.errors:
            print "ERROR with unit test: ", test
            print trace
            summary.append(repr(test))
    return summary
def runEmbeddedTests(summary):
    '''
    For each module in FuXi, run its test routine--if any--and any doctests.
    '''
    print "Disregard reports of the form 'running xx test function ... \\n*** DocTestRunner.merge: yy in both testers; summing outcomes."
    print "Refer instead to the testmod execution of these tests."
    sys.argv = [""]
    modsWithLoadErrors = []
    modsWithDoctestFailures = []
    modsWithDoctestErrors = []
    modsWithUnitTestErrors = []
    totalDoctests = 0
    totalDoctestFailures = 0
    totalUnitTestMods = 0
    suite = unittest.TestSuite()
    for entry, mod in moduleIterator("FuXi"):
        if not entry in FILES_TO_IGNORE:   
            # addTestsToSuite(mod, suite)
            totalUnitTestMods += 1
            if "test" in mod.__dict__:
                try:
                    print "running %s test function" % (entry)
                    mod.__dict__["test"]()
                except:               
                    modsWithUnitTestErrors.append(mod)
                    print "ERROR--exception running unittest " + entry
                    if traceback:
                        traceback.print_exc()
            sys.__stderr__.flush()
            sys.__stdout__.flush()
            tests = 0
            try:
                print "running %s under doctest.testmod" % (entry)
                failures, tests = doctest.testmod(mod)
            except:
                modsWithDoctestErrors.append(mod)
                print "ERROR--exception running doctest " + entry
                traceback.print_exc()
                sys.__stderr__.flush()
            if tests > 0:
                totalDoctests += tests
                totalDoctestFailures += failures 
                if failures > 0:
                    modsWithDoctestFailures.append(entry)
    for line in summary:
        print line
    summary.append("Summary of Embedded Tests " + VISUAL_SEPARATOR)
    summary.append("* %i mods with load errors:" % (modsWithLoadErrors.__len__()))
    summary.append(modsWithLoadErrors)
    summary.append("* %i mods with doctest failures:" % (modsWithDoctestFailures.__len__()) )
    summary.append(modsWithDoctestFailures)
    summary.append("* %i mods with doctest errors: " % (modsWithDoctestErrors.__len__())) 
    summary.append(modsWithDoctestErrors)
    summary.append("* Total doctests run %i: " % (totalDoctests))
    summary.append("* Total doctest failures encountered:  %i" % (totalDoctestFailures))
    summary.append("* Total attempted unit test modules: %i" % (totalUnitTestMods))
    summary.append("* %i mods with unit test errors: " % (modsWithUnitTestErrors.__len__()))
    summary.append(modsWithUnitTestErrors)
    return summary

def suite():
    
    '''
    Return a TestSuite of tests in the test directory.
    '''
    suite = unittest.TestSuite()
    suite.addTest(unittest.makeSuite(additionalDLPTests.AdditionalDescriptionLogicTests,'test'))
    suite.addTest(unittest.makeSuite(test_builtin_ordering.URIRefStringStartsWith,'test'))
    suite.addTest(unittest.makeSuite(test_network_reset.NetworkReset,'test'))
    suite.addTest(unittest.makeSuite(test_superproperty_entailment.test_superproperty_entailment,'test'))
    suite.addTest(unittest.makeSuite(testExistentialInHead.ExistentialInHeadTest,'test'))
    suite.addTest(unittest.makeSuite(testSkolemization.UnionSkolemizedTest,'test'))
    return suite
def splash(txt):
    print "running " + txt + " " + VISUAL_SEPARATOR
    
if __name__ == "__main__":
    #import sys;sys.argv = ['', 'Test.testName']
    from optparse import OptionParser
    op = OptionParser('usage: %prog [options]')
    op.add_option('--variants', 
                  action='store_true',
                  default=False,
      help = 'Whether to run testOwl three ways or just bottom up ')    
    op.add_option('--testFunctions', 
                  action='store_true',
                  default=True,
      help = 'Whether to test modules via their test functions rather than as a unittest suite.')  
    (options, facts) = op.parse_args()

    testOWLoptions = testOWL.defaultOptions()
    splash("Running testOWL with " + testOWLoptions.strategy)
    testOWL.runTests(testOWLoptions)
    if options.variants:
        testOWLoptions.strategy = "sld"
        splash("Running testOWL with " + testOWLoptions.strategy)
        testOWL.runTests(testOWLoptions)
        testOWLoptions.strategy = "bfp"
        splash("Running testOWL with "  + testOWLoptions.strategy)
        testOWL.runTests(testOWLoptions)
    sys.__stderr__.flush()

    summary = []
    # Caution: for some reason external unit tests run properly only if run before embedded tests.
    #runStandaloneUnitTests()
    runSuite("External Unit Tests (other than testOWL)", suite(), summary)
    runEmbeddedTests(summary)
    for line in summary:
        print line 
    print "\nNote summary statistics are not available for testOWL runs."
