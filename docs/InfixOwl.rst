==============================================================================
InfixOwl
==============================================================================

Introduction
===============================

An infix syntax for Python, `Manchester
OWL <http://owl-workshop.man.ac.uk/acceptedLong/submission_9.pdf>`_, OWL
Abstract `Syntax <http://www.w3.org/TR/owl-semantics/syntax.html>`_, and
RDF (via RDFLib).

Computer-based Patient Record Ontology
===================================================================================

An `example <http://python-dlp.googlecode.com/files/pomr.py>`_ of
building a OWL ontology programmatically via
`FuXi </p/fuxi/wiki/FuXi>`_.Syntax.InfixOWL

GALEN Extract
=================================

As an example, a large
`extract <http://python-dlp.googlecode.com/files/GALEN-CABG-Segment.txt>`_
of GALEN was generated using `InfixOwl </p/fuxi/wiki/InfixOwl>`_:

::

        from FuXi.Syntax.InfixOWL import *
        galenGraph = Graph().parse(os.path.join(os.path.dirname(__file__), 'GALEN-CABG-Segment.owl'))
        graph=galenGraph
        for c in graph.subjects(predicate=RDF.type,object=OWL_NS.Class):
            if isinstance(c,URIRef):
                print Class(c,graph=graph).__repr__(True),"\n"

Doctest Example
=====================================

Uses Manchester Syntax for
`\_\_repr\_\_ <http://docs.python.org/ref/customization.html>`_

::

    >>> exNs = Namespace('http://example.com/')        
    >>> namespace_manager = NamespaceManager(Graph())
    >>> namespace_manager.bind('ex', exNs, override=False)
    >>> namespace_manager.bind('owl', OWL_NS, override=False)
    >>> g = Graph()    
    >>> g.namespace_manager = namespace_manager

Now we have an empty
`Graph <http://rdflib.net/rdflib-2.4.0/html/public/rdflib.Graph.Graph-class.html>`_,
we can construct OWL classes in it using the Python classes defined in
this module

::

    >>> a = Class(exNs.Opera,graph=g)

Now we can assert
`rdfs:subClassOf <http://www.w3.org/TR/rdf-schema/#ch_subclassof>`_ and
`owl:equivalentClass <http://www.w3.org/TR/owl-ref/#equivalentClass-def>`_
relationships (in the underlying graph) with other classes using the
*subClassOf* and *equivalentClass*
`descriptors <http://users.rcn.com/python/download/Descriptor.htm>`_
which can be set to a list of objects for the corresponding predicates.

::

    >>> a.subClassOf = [exNs.MusicalWork]

We can then access the rdfs:subClassOf relationships

::

    >>> print list(a.subClassOf)
    [Class: ex:MusicalWork ]

This can also be used against already populated graphs:

::

    >>> owlGraph = Graph().parse(OWL_NS)
    >>> namespace_manager.bind('owl', OWL_NS, override=False)
    >>> owlGraph.namespace_manager = namespace_manager
    >>> list(Class(OWL_NS.Class,graph=owlGraph).subClassOf)
    [Class: rdfs:Class ]

Operators are also available. For instance we can add ex:Opera to the
extension of the ex:CreativeWork`? </p/fuxi/w/edit/CreativeWork>`_ class
via the '+=' operator

::

    >>> a
    Class: ex:Opera SubClassOf: ex:MusicalWork
    >>> b = Class(exNs.CreativeWork,graph=g)
    >>> b += a
    >>> print list(a.subClassOf)
    [Class: ex:CreativeWork , Class: ex:MusicalWork ]

And we can then remove it from the extension as well

::

    >>> b -= a
    >>> a
    Class: ex:Opera SubClassOf: ex:MusicalWork

`Boolean <http://www.w3.org/TR/owl-ref/#Boolean>`_ class constructions
can also be created with Python operators For example, The \| operator
can be used to construct a class consisting of a owl:unionOf the
operands:

::

    >>> c =  a | b | Class(exNs.Work,graph=g)
    >>> c
    ( ex:Opera or ex:CreativeWork or ex:Work )

Boolean class expressions can also be operated as lists (natively in
python)

::

    >>> del c[c.index(Class(exNs.Work,graph=g))]
    >>> c
    ( ex:Opera or ex:CreativeWork )

The '&' operator can be used to construct class intersection:

::

    >>> woman = Class(exNs.Female,graph=g) & Class(exNs.Human,graph=g)
    >>> woman.identifier = exNs.Woman
    >>> woman
    ( ex:Female and ex:Human )

`Enumerated <http://www.w3.org/TR/owl-ref/#EnumeratedClass>`_ classes
can also be manipulated

::

    >>> contList = [Class(exNs.Africa,graph=g),Class(exNs.NorthAmerica,graph=g)]
    >>> EnumeratedClass(members=contList,graph=g)
    { ex:Africa ex:NorthAmerica }

`owl:Restrictions <http://www.w3.org/TR/owl-ref/#Restriction>`_ can also
be instanciated:

::

    >>> Restriction(exNs.hasParent,graph=g,allValuesFrom=exNs.Human)
    ( ex:hasParent only ex:Human )

Restrictions can also be created using Manchester OWL syntax in
'colloquial' Python. A Python infix operator
`recipe <http://aspn.activestate.com/ASPN/Cookbook/Python/Recipe/384122>`_
was used for this purpose. See below

::

    >>> exNs.hasParent |some| Class(exNs.Physician,graph=g)
    ( ex:hasParent some ex:Physician )
    >>> Property(exNs.hasParent,graph=g) |max| Literal(1)
    ( ex:hasParent max 1 )

Then we can serialize the live RDFLib graph as uniform RDF/XML.

::

    >>> print g.serialize(format='pretty-xml')
    <?xml version="1.0" encoding="utf-8"?>
    <rdf:RDF
      xmlns:owl='http://www.w3.org/2002/07/owl#'
      xmlns:rdf='http://www.w3.org/1999/02/22-rdf-syntax-ns#'
      xmlns:rdfs='http://www.w3.org/2000/01/rdf-schema#'
    >
      <owl:Class rdf:about="http://example.com/Work"/>
      <owl:Restriction>
        <owl:someValuesFrom>
          <owl:Class rdf:about="http://example.com/Physician"/>
        </owl:someValuesFrom>
        <owl:onProperty rdf:resource="http://example.com/hasParent"/>
      </owl:Restriction>
      <owl:Class>
        <owl:oneOf rdf:parseType="Collection">
          <owl:Class rdf:about="http://example.com/Africa"/>
          <owl:Class rdf:about="http://example.com/NorthAmerica"/>
        </owl:oneOf>
      </owl:Class>
      <owl:Restriction>
        <owl:maxCardinality rdf:datatype="http://www.w3.org/2001/XMLSchema#int">1</owl:maxCardinality>
        <owl:onProperty rdf:resource="http://example.com/hasParent"/>
      </owl:Restriction>
      <owl:Restriction>
        <owl:allValuesFrom>
          <owl:Class rdf:about="http://example.com/Human"/>
        </owl:allValuesFrom>
        <owl:onProperty rdf:resource="http://example.com/hasParent"/>
      </owl:Restriction>
      <owl:Class rdf:about="http://example.com/Woman">
        <owl:intersectionOf rdf:parseType="Collection">
          <owl:Class rdf:about="http://example.com/Female"/>
        </owl:intersectionOf>
        <owl:unionOf rdf:parseType="Collection">
          <owl:Class rdf:about="http://example.com/Opera">
            <rdfs:subClassOf>
              <owl:Class rdf:about="http://example.com/MusicalWork"/>
            </rdfs:subClassOf>
          </owl:Class>
          <owl:Class rdf:about="http://example.com/CreativeWork"/>
        </owl:unionOf>
      </owl:Class>
    </rdf:RDF>

First Class Infix Operators
=============================================================

Other Python equivalents of Manchester OWL:

-  \|only\|
-  \|max\|
-  \|min\|
-  \|exactly\|
-  \|value\|

