from rdflib import (
    Graph,
    Literal,
    )
from FuXi.Syntax.InfixOWL import (
    Class,
    EnumeratedClass,
    OWL_NS,
    Property,
    Restriction,
    )
from FuXi.Syntax.InfixOWL import some
from FuXi.Syntax.InfixOWL import max

from rdflib.namespace import (
    Namespace,
    NamespaceManager,
    )
from pprint import pformat

exNs = Namespace('http://example.com/')
namespace_manager = NamespaceManager(Graph())
namespace_manager.bind('ex', exNs, override=False)
namespace_manager.bind('owl', OWL_NS, override=False)
g = Graph()
g.namespace_manager = namespace_manager

# Now we have an empty Graph, we can construct OWL classes in it using the
# Python classes defined in this module

a = Class(exNs.Opera, graph=g)

# Now we can assert rdfs:subClassOf and owl:equivalentClass relationships
# (in the underlying graph) with other classes using the subClassOf and
# equivalentClass descriptors which can be set to a list of objects for
# the corresponding predicates.

a.subClassOf = [exNs.MusicalWork]

# We can then access the rdfs:subClassOf relationships

assert pformat(list(a.subClassOf)) == '[Class: ex:MusicalWork ]'

# This can also be used against already populated graphs:

owlGraph = Graph().parse(OWL_NS)
namespace_manager.bind('owl', OWL_NS, override=False)
owlGraph.namespace_manager = namespace_manager

assert pformat(
    list(Class(OWL_NS.Class, graph=owlGraph).subClassOf)) == \
    '[Class: rdfs:Class ]'

# Operators are also available. For instance we can add ex:Opera to the
# extension of the ex:CreativeWork class via the '+=' operator

assert str(a) == 'Class: ex:Opera SubClassOf: ex:MusicalWork'

b = Class(exNs.CreativeWork, graph=g)
b += a

assert pformat(list(a.subClassOf)) == \
    '[Class: ex:CreativeWork , Class: ex:MusicalWork ]' or \
    '[Class: ex:MusicalWork , Class: ex:CreativeWork ]'

# And we can then remove it from the extension as well

b -= a
a

assert pformat(a) == 'Class: ex:Opera SubClassOf: ex:MusicalWork'

# Boolean class constructions can also be created with Python operators
# For example, The | operator can be used to construct a class consisting
# of a owl:unionOf the operands:

c = a | b | Class(exNs.Work, graph=g)

assert(pformat(c)) == '( ex:Opera OR ex:CreativeWork OR ex:Work )'

# Boolean class expressions can also be operated as lists (natively in python)

del c[c.index(Class(exNs.Work, graph=g))]

assert pformat(c) == '( ex:Opera OR ex:CreativeWork )'

# The '&' operator can be used to construct class intersection:

woman = Class(exNs.Female, graph=g) & Class(exNs.Human, graph=g)
woman.identifier = exNs.Woman

assert pformat(woman) == '( ex:Female AND ex:Human )'

# Enumerated classes can also be manipulated

contList = [
    Class(exNs.Africa, graph=g),
    Class(exNs.NorthAmerica, graph=g)
]

assert pformat(
    EnumeratedClass(members=contList, graph=g)) == \
    '{ ex:Africa ex:NorthAmerica }'

# owl:Restrictions can also be instanciated:

assert pformat(Restriction(
    exNs.hasParent, graph=g, allValuesFrom=exNs.Human)) == \
    '( ex:hasParent ONLY ex:Human )'

# Restrictions can also be created using Manchester OWL syntax in
# 'colloquial' Python. A Python infix operator recipe was used for
# this purpose. See below

assert pformat(
    exNs.hasParent | some | Class(exNs.Physician, graph=g)) == \
    '( ex:hasParent SOME ex:Physician )'

assert pformat(
    Property(exNs.hasParent, graph=g) | max | Literal(1)) == \
    '( ex:hasParent MAX 1 )'

print("Completed")
