import unittest, os, time, sys
from FuXi.Syntax.InfixOWL import *
try:
    from rdflib.graph import Graph, ReadOnlyGraphAggregate, ConjunctiveGraph
    from rdflib.namespace import NamespaceManager
except ImportError:
    from rdflib.Graph import Graph,ReadOnlyGraphAggregate,ConjunctiveGraph
    from rdflib.syntax.NamespaceManager import NamespaceManager
from rdflib import RDF, RDFS, Literal, Variable, URIRef
from rdflib import plugin
from rdflib.util import first
from rdflib.store import Store
from cStringIO import StringIO

DATALOG_SAFETY_NONE   = 0
DATALOG_SAFETY_STRICT = 1  
DATALOG_SAFETY_LOOSE  = 2

safetyNameMap = {
  'none'   : DATALOG_SAFETY_NONE,
  'strict' : DATALOG_SAFETY_STRICT,
  'loose'  : DATALOG_SAFETY_LOOSE
}

def SubSumptionExpansion(owlClass):
    owlClass = CastClass(owlClass) 
    if isinstance(owlClass,BooleanClass) and owlClass._operator == OWL_NS.unionOf:
        for member in owlClass:
            expanded = False
            for innerMember in SubSumptionExpansion(Class(member)):
                expanded = True
                yield innerMember
            if not expanded:
                yield member
    else:
        for member in owlClass.subSumpteeIds():
            expanded = False
            for innerMember in SubSumptionExpansion(Class(member)):
                expanded = True
                yield innerMember
            if not expanded:
                yield member

def ComplementExpansion(owlClass,debug=False):
    """
    For binary conjunctions of a positive conjunction concept and a negative atomic concept  
    """
    owlClass=CastClass(owlClass.identifier,owlClass.graph)
    if isinstance(owlClass,BooleanClass) and \
       len(owlClass) == 2 and owlClass._operator == OWL_NS.intersectionOf:
        oldRepr = owlClass.__repr__()
        #A boolean-constructed class
        negativeClasses = set()
        otherClasses = set()
        for member in owlClass:
            member = Class(member)
            if member.complementOf:
                #A negative class, expand it and add to bucket of classes to 'remove'
                for expandedClass in SubSumptionExpansion(member.complementOf):
                    negativeClasses.add(expandedClass)
            else:
                #A positive class, expand it and add to bucket of base classes
                expanded = False
                for expandedClass in SubSumptionExpansion(member):
                    expanded = True
                    otherClasses.add(expandedClass)
                if not expanded:
                    otherClasses.add(member.identifier)

        if negativeClasses:
            #Delete the old list of operands for the boolean class
            oldList = owlClass._rdfList
            oldList.clear()
                        
            #Recreate the list of operands, exluding the expanded negative classes
            for allowedClasses in otherClasses.difference(negativeClasses) :
                oldList.append(classOrIdentifier(allowedClasses))
            owlClass.changeOperator(OWL_NS.unionOf)        
            if debug:
                print "Incoming boolean class: ", oldRepr             
                print "Expanded boolean class: ", owlClass.__repr__()
            return owlClass
        else:
            if debug:
                print "There were no negative classes!"
            
class ComplementExpansionTestSuite(unittest.TestCase):
    def setUp(self):
        self.testGraph = Graph()
        Individual.factoryGraph = self.testGraph         
    
    def testExpand(self):
        EX = Namespace("http://example.com/")
        namespace_manager = NamespaceManager(Graph())
        namespace_manager.bind('ex', EX, override=False)
        self.testGraph.namespace_manager = namespace_manager    
        
        man   = Class(EX.Man)
        boy   = Class(EX.Boy)
        woman = Class(EX.Woman)
        girl  = Class(EX.Girl)
        male  = Class(EX.Male)
        female= Class(EX.Female)
        human = Class(EX.Human)        
        animal = Class(EX.Animal)
        cat = Class(EX.Cat)
        dog = Class(EX.Dog)
        animal = Class(EX.Animal)
        
        animal = cat | dog | human
        human += man
        human += boy
        human += woman
        human += girl
        male   += man
        male   += boy
        female += woman
        female += girl
        
        testClass = human & ~ female
        self.assertEquals(repr(testClass),'( ex:Human and ( not ex:Female ) )')
        newtestClass = ComplementExpansion(testClass,debug=True)      
        self.assertTrue(repr(newtestClass) in ['( ex:Boy or ex:Man )','( ex:Man or ex:Boy )'],repr(newtestClass))

        testClass2 = animal & ~ (male | female)
        self.assertEquals(repr(testClass2),
                          '( ( ex:Cat or ex:Dog or ex:Human ) and ( not ( ex:Male or ex:Female ) ) )')
        newtestClass2 = ComplementExpansion(testClass2,debug=True)  
        testClass2Repr = repr(newtestClass2)
        self.assertTrue(testClass2Repr in ['( ex:Cat or ex:Dog )','( ex:Dog or ex:Cat )'],testClass2Repr)

if __name__ == '__main__':
    unittest.main()    
    sys.exit(1)
    from optparse import OptionParser
    parser = OptionParser()

    parser.add_option('--verbose',action="store_true",default=False,
        help='Output debug print statements or not')    
    parser.add_option('--format',default="xml",
        help='The RDF serialization syntax to parse with')

    (options, args) = parser.parse_args()

    owlGraph = Graph()
    for input in args[0:]:
        if options.verbose:
            print "Parsing ", input, " as ", options.format
        owlGraph.parse(input,format=options.format)

    Individual.factoryGraph = owlGraph
    
    def topList(node,g):
        for s in g.subjects(RDF.rest,node):
            yield s

    for negativeClass in owlGraph.subjects(predicate=OWL_NS.complementOf):
        containingList = first(owlGraph.subjects(RDF.first,negativeClass))
        prevLink = None
        while containingList:
            prevLink = containingList
            containingList = first(owlGraph.subjects(RDF.rest,containingList))
        for s,p,o in owlGraph.triples_choices((None,
                                            [OWL_NS.intersectionOf,
                                             OWL_NS.unionOf],
                                             prevLink)):
            _class = Class(s)
#            print _class.__repr__(True,True)            
            ComplementExpansion(_class,debug=options.verbose)
