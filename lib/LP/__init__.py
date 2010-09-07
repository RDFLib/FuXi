import doctest
from rdflib.Graph import Graph
from rdflib import RDF, URIRef, Namespace, Literal, BNode

def IdentifyHybridPredicates(graph,derivedPredicates):
    """
    Takes an RDF graph and a list of derived predicates and return
    those predicates that are both EDB (extensional) and IDB (intensional) predicates.
    i.e., derived predicates that appear in the graph
    
    >>> g=Graph()
    >>> EX= Namespace('http://example.com/')
    >>> g.add((BNode(),EX.predicate1,Literal(1)))
    >>> g.add((BNode(),RDF.type,EX.Class1))
    >>> g.add((BNode(),RDF.type,EX.Class2))
    >>> rt=IdentifyHybridPredicates(g,[EX.predicate1,EX.Class1,EX.Class3])
    >>> sorted(rt)
    [rdflib.URIRef('http://example.com/Class1'), rdflib.URIRef('http://example.com/predicate1')]
    """
    derivedPredicates = derivedPredicates if isinstance(derivedPredicates,
                                                        set) else \
                        set(derivedPredicates)
    return derivedPredicates.intersection(                    
                    [ o if p == RDF.type else p 
                        for s,p,o in graph ])    
    
if __name__ == '__main__':
    import doctest
    doctest.testmod()