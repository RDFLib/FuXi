'''
Created on Sep 16, 2010

@author: onewnan

Run all FuXi tests.  

Note the discovery mechanisms require sources on the python path.

If a coverage tool is installed this module can help generate coverage statistics, e.g.,

    coverage erase
    coverage run --branch --source="FuXi" suite.py --variants --unittest2 
    coverage report
'''
import doctest
import unittest
import additionalDLPTests
import imp
import FuXi
import os
import rdflib
import sys
import test_builtin_ordering
import test_network_reset
import test_superproperty_entailment
import testExistentialInHead
import testOWL
import testReteAction
import testSkolemization
import traceback
import types
from unittest import TestResult

FILES_TO_IGNORE = ('suite.py', 'CommandLine.py')
VISUAL_SEPARATOR = " ===================================="
modsWithLoadErrors = []

def moduleIterator(root):
    '''
    Successively return all modules in all packages beneath root.
    
    The parameter 'root' may be either a module or a module's path name.
    '''
    OTHER_EXTENSIONS = ('.pyo','.pyc' )
    stack = []
    if isinstance(root,types.ModuleType):
        packageRoute = root.__path__
        file = False
        name = root.__name__
    else: # string
        try:
            name = root
            file, packageRoute, description = imp.find_module(name)
            package = imp.load_module(root, file, packageRoute, description)
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
def runSuite(title, suite, summary):
    '''
    Run the indicated test suite, accumulating statistics and the title in the summary.
    
    The summary is a list of strings.
    '''
    splash(title)
    sys.argv = [""]
    results = TestResult()
    suite.run(results)
    summary.append(("Summary of %s " % (title)) + VISUAL_SEPARATOR)
    summary.append("* Ran %i tests with %i failures and %i errors." \
        % (results.testsRun, results.failures.__len__(), results.errors.__len__()))
    if results.failures.__len__():
        summary.append("* Failed tests were:")
        for test, trace in results.failures:
            print "FAIL: ", test, "(unit test)"
            print trace
            summary.append(repr(test))
    if results.errors.__len__():
        summary.append("* Tests in error were:")
        for test, trace in results.errors:
            print "ERROR: ", test, "(unit test)"
            print trace
            summary.append(repr(test))
    return summary
def extractEmbeddedSuite(root):
    '''
    Use unittest2 to extract a suite of embedded unit tests from root.
    
    The parameter 'root' can be either a module or the path name of a module.
    '''
    if isinstance(root,types.ModuleType):
        packageRoute = root.__path__[0]
        file = False
        packageName = root.__name__
    else:
        packageName = root
        file, packageRoute, description = imp.find_module(packageName)
    top_level_dir = os.path.abspath(packageRoute + "/..")
    loader = unittest2.TestLoader()
    suite = loader.discover(packageRoute,top_level_dir=top_level_dir,pattern="*.py")
    return suite
def runEmbeddedTests(root, summary, usingUnittest2):
    '''
    For each module nested under root, run its unit- and doc-tests.
    
    The root parameter may be a module or a module name.
    '''
    if isinstance(root,types.ModuleType):
        packageRoute = root.__path__[0]
        file = False
        packageName = root.__name__
    else:
        packageName = root
        file, packageRoute, description = imp.find_module(packageName)
    if not usingUnittest2:
        if options.verbose:
            print "Running test functions rather than directly running unit tests."
            print "For better test results, install unittest2 and execute with flag --unittest2."
            print "Please disregard warnings of the form 'running xx test function ... \\n*** DocTestRunner.merge: yy in both testers; summing outcomes."
            print "Refer instead to the testmod results for these tests."
    else:
        if options.verbose:
            print "Running unit tests directly rather than invoking test functions."
        embeddedSuite = extractEmbeddedSuite(root)
        title = "Embedded " + packageName + " Unit Tests "
        runSuite(title, embeddedSuite, summary)
    sys.argv = [""]
        
    modsWithLoadErrors = []
    modsWithDoctestFailures = []
    modsWithDoctestErrors = []
    modsWithTestFunctionFailures = []
    totalDoctests = 0
    totalDoctestFailures = 0
    totalTestFunctionsRun = 0
    for entry, mod in moduleIterator(packageName):
        if not entry in FILES_TO_IGNORE:   
            if not usingUnittest2 and "test" in mod.__dict__:
                try:
                    totalTestFunctionsRun += 1
                    if options.verbose:
                        print "running %s's test function" % (entry)
                    mod.__dict__["test"]()
                except:               
                    modsWithTestFunctionFailures.append(mod)
                    print "ERROR--exception running unittest " + entry
                    if traceback:
                        traceback.print_exc()
                sys.__stderr__.flush()
                sys.__stdout__.flush()
            tests = 0
            try:
                if options.verbose:
                    print "running %s using doctest.testmod" % (entry)
                failures, tests = doctest.testmod(mod)
            except:
                modsWithDoctestErrors.append(mod)
                print "ERROR--exception running doctest for", entry
                traceback.print_exc()
                sys.__stderr__.flush()
            if tests > 0:
                totalDoctests += tests
                totalDoctestFailures += failures 
                if failures > 0:
                    modsWithDoctestFailures.append(entry)
    if usingUnittest2:
        title = "Summary of " + packageName + " Doctests" 
    else:
        title = "Summary of Embedded " + packageName + " Tests " 
    summary.append(title + VISUAL_SEPARATOR)
#    summary.append("* %i mods with load errors:" % (modsWithLoadErrors.__len__()))
#    summary.append(modsWithLoadErrors)
    summary.append("* %i mods with doctest failures:" % (modsWithDoctestFailures.__len__()) )
    summary.append(modsWithDoctestFailures)
    summary.append("* %i mods with doctest errors: " % (modsWithDoctestErrors.__len__())) 
    summary.append(modsWithDoctestErrors)
    summary.append("* Total doctests run %i: " % (totalDoctests))
    if not usingUnittest2:
        summary.append("* Total attempted test functions: %i" % (totalTestFunctionsRun))
        summary.append("* %i mods with test function failures: " % (modsWithTestFunctionFailures.__len__()))
        summary.append(modsWithTestFunctionFailures)
    return summary

def suite():
    
    '''
    Return a TestSuite containing all tests from the test directory.
    '''
    suite = unittest.TestSuite()
    suite.addTest(unittest.makeSuite(additionalDLPTests.AdditionalDescriptionLogicTests,'test'))
    suite.addTest(unittest.makeSuite(test_builtin_ordering.URIRefStringStartsWith,'test'))
    suite.addTest(unittest.makeSuite(test_network_reset.NetworkReset,'test'))
    suite.addTest(unittest.makeSuite(test_superproperty_entailment.test_superproperty_entailment,'test'))
    suite.addTest(unittest.makeSuite(testExistentialInHead.ExistentialInHeadTest,'test'))
    suite.addTest(unittest.makeSuite(testReteAction.ReteActionTest,'test'))
    suite.addTest(unittest.makeSuite(testSkolemization.UnionSkolemizedTest,'test'))
    return suite
def splash(txt):
    '''
    Print a separator line indicating what part of the suite is running.
    '''
    print "\nRunning " + txt + VISUAL_SEPARATOR
if __name__ == "__main__":
    from optparse import OptionParser
    op = OptionParser('usage: %prog [options]')
    op.add_option('--variants', 
                  action='store_true',
                  default=False,
      help = 'Whether to run testOwl three ways or just bottom up ')    
    op.add_option('--unittest2', 
                  action='store_true',
                  default=False,
      help = 'Whether to use unittest2 discovery. ')   
    op.add_option('--rdftests', 
                  action='store_true',
                  default=False,
      help = "Whether to run rdflib's (in addition to FuXi's) embedded tests. ")   
    op.add_option('--verbose', 
                  action='store_true',
                  default=False,
      help = "Whether to include informational messages besides summaries. ")   
    (options, facts) = op.parse_args()
    summary = []
    flagCount = 0
    if options.variants:
        flagCount = 1
        flags = "--variants"
    else:
        flagCount = 0
        flags = ""
    usingUnittest2 = False
    if options.unittest2:
        try:
            import unittest2
            usingUnittest2 = True
            flagCount+=1
            flags = flags + " --unittest2"
        except:
            print "Unittest2 libraries not found, --unittest2 flag ignored."
            pass
    rdftests = False
    if options.rdftests:
        rdfpath = rdflib.__path__[0]
        if os.path.isdir(rdfpath):
            rdftests = True
            flagCount+=1
            flags = flags + " --rdftests"
        else:
            print "--rdftests flag is ignored since", rdfpath, "is not a directory.",
    if options.verbose:
        print "Running suite.py with %i flags set: %s" % (flagCount, flags)
    if usingUnittest2 and options.verbose:
        print "Using unittest2 libraries.  CAUTION: these may not be compatible with your debugger.  See"
        print "\thttp://pydev.blogspot.com/2007/06/why-cant-pydev-debugger-work-with.html"
    testOWLoptions = testOWL.defaultOptions()
    splash("testOWL with " + testOWLoptions.strategy)
    testOWL.runTests(testOWLoptions)
    if options.variants:
        testOWLoptions.strategy = "sld"
        splash("testOWL with " + testOWLoptions.strategy)
        testOWL.runTests(testOWLoptions)
        testOWLoptions.strategy = "bfp"
        splash("testOWL with "  + testOWLoptions.strategy)
        testOWL.runTests(testOWLoptions)
    sys.__stderr__.flush()

    # Caution: for some reason external unit tests run properly only if run before embedded tests.
    #runStandaloneUnitTests()
    runSuite("FuXi External Unit Tests (other than testOWL)", suite(), summary)
    runEmbeddedTests("FuXi",summary,usingUnittest2)
    if rdftests:
        runEmbeddedTests(rdflib,summary,usingUnittest2)
    for line in summary:
        print line 
    print "\nNote summary statistics are not available for the testOWL runs."

