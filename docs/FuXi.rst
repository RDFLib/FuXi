=========
FuXi 1.2
=========

Introduction
================================

`FuXi </p/fuxi/wiki/FuXi>`_ (pronounced foo-shee) is a forward-chaining
production system for Notation 3 Description Logic Programming. It is
implemented as a companion to RDFLib – which it requires for its various
RDF processing.

What is with the Name?
======================

    In the beginning there was as yet no moral or social order. Men knew
    their mothers only, not their fathers. When hungry, they searched
    for food; when satisfied, they threw away the remnants. They
    devoured their food hide and hair, drank the blood, and clad
    themselves in skins and rushes. Then came Fu Hsi and looked upward
    and contemplated the images in the heavens, and looked downward and
    contemplated the occurrences on earth. He united man and wife,
    regulated the five stages of change, and laid down the laws of
    humanity. He devised the eight trigrams, in order to gain mastery
    over the world.

Originally, it was an idea to express the underlying constructs of the
Yi Jing / I Ching in Description & First Order Logic in order to reason
over them.

** `Why FuXi? <http://copia.posterous.com/why-fuxi>`_ **


Background of RETE and RETE/UL Algorithms
=========================================

It relies on Charles Forgy's `Rete algorithm <https://en.wikipedia.org/wiki/Rete_algorithm>`_ for
the many pattern/many object match problem. It also implements
algorithms outlined in the PhD thesis (1995) of Robert Doorenbos:

    Production Matching for Large Learning Systems.

Robert's thesis describes a modification of the original Rete algorithm
that (amongst other things) limits the fact syntax (referred to as
Working Memory Elements) to 3-item tuples (which corresponds quite
nicely with the RDF abstract syntax). The thesis also describes methods
for using hash tables to improve efficiency of alpha nodes and beta
nodes.

An introductory description from the above:

    Rete (usually pronounced either "REET" or "REE-tee", from the Latin
    word for "network") deals with a production memory (PM) and a
    working memory (WM). Each of these may change gradually over time.
    The working memory is a set of items which (in most systems)
    represent facts about the system's current situation - the state of
    the external world and/or the internal problem-solving state of the
    system itself. Each item in `WM` is called a working memory element,or
    a WME.

The production memory is a set of productions (i.e., rules). A
production is specified as a set of conditions, collectively called the
left-hand side (LHS), and a set of actions, collectively called the
right-hand side (RHS).



Python Idioms (hashing efficiently)
===================================

-  compiles an RDFLib N3 rule graph into
   :ref:`FuXi.Rete.AlphaNode` and :ref:`FuXi.Rete.BetaNode` instances
-  takes a fact (or the removal of a fact, perhaps?) and propagates
   down, starting from it's alpha nodes
-  stores inferred triples in provided triple source (an RDFLib graph)
   or a temporary IOMemory Graph by default

Like RDFLib, `FuXi` is very idiomatic and uses Python hash / set / list
mechanism to maximize the matching efficiency of the network (see
:mod:`Fuxi.Rete.Network`_). The extent of the efficiency has not been
fully explored and there is much more that can be done to improve the
already impressive performance.

Network
=======

Rete "Legend"
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. figure:: _static/rete-network.jpg
   :align: center
   :alt: 

An OWL/RDFS Example
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. figure:: _static/fuxi.png
   :align: center
   :alt: 

`FuXi </p/fuxi/wiki/FuXi>`_'s Network intances can be exported to a
`Graphviz <http://www.graphviz.org/>`_ **DOT** file and rendered to any
image format. `Boost Graph Library - Python
Bindings <http://www.generic-programming.org/~dgregor/bgl-python/>`_ is
used for this. This provides a nice visual feedback to the
discrimination network built to a ruleset.

Beta (Join) Nodes
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

::

    (<x> ^self <y>) /* C1 */
    (<x> ^color red) /* C2 */
    (<y> ^color red) /* C3 */
    ... /* other conditions */

.. figure:: http://python-dlp.googlecode.com/files/rete-ul-join-node.png
   :align: center
   :alt: 


Roadmap & Limitations
=====================

The full unlinking algorithm has the following FSM:

.. figure:: _static/rete-ul-unlinking-FSM.png
   :align: center
   :alt: 

`FuXi </p/fuxi/wiki/FuXi>`_ currently implements production capabilities
for a limited subset of Notation 3. In particular built-ins are not
implemented as they have a significant impact on the efficiency of a
RETE network (which was really only intended for pattern matching).
Robert's thesis includes algorithms / heuristics for implementing
support for:

-  Negation `? </p/fuxi/w/edit/NegatedConditions>`_
-  Non-equality tests (read: built-in support)
-  Live addition/removal of rules
-  Support for removal of triples / WMEs

Proof Generation
================

See: `Proof generation /
visualization <http://groups.google.com/group/fuxi-discussion/browse_thread/thread/4f612c91e585f552>`_

Installation
============

Fuxi is now setuptools integrated and can be installed via:

::

    wget http://peak.telecommunity.com/dist/ez_setup.py
    python ez_setup.py
    easy_install fuxi
    Fuxi

Command-line Program
====================

Command-line help:

::

    Usage: FuXi [options] factFile1 factFile2 ... factFileN

    Options:
      -h, --help            show this help message and exit
      --why=WHY             Used with --filter to solve queries (the heads of
                            filter-rules) in a top-down fashion using the adorned
                            program and sip for each rule In this way OWL-DLP,
                            OWL2-RL, N3, (and RIF) theories can be solved /
                            queried
      --closure             Whether or not to serialize the inferred triples along
                            with the original triples.  Otherwise (the default
                            behavior), serialize only the inferred triples
      --output=RDF_FORMAT   Serialize the inferred triples and/or original RDF
                            triples to STDOUT using the specified RDF syntax ('xml
                            ','pretty-xml','nt','turtle', or 'n3') or to print a
                            summary of the conflict set (from the RETE network) if
                            the value of this option is 'conflict'.  If the the
                            value is 'rif' or 'rif-xml', Then the rules used for
                            inference will be serialized as RIF.  If the value is
                            'pml' and --why is used,  then the PML RDF statements
                            are serialized.  If output is 'proof-graph then a
                            graphviz .dot file of the proof graph is printed.
                            Finally if the value is 'man-owl', then the RDF facts
                            are assumed to be OWL/RDF and serialized via
                            Manchester OWL syntax. The default is n3
      --class=QNAME         Used with --output=man-owl to determine which classes
                            within the entire OWL/RDF are targetted for
                            serialization.  Can be used more than once
      --property=QNAME      Used with --output=man-owl or --extract to determine
                            which properties are serialized / extracted.  Can be
                            used more than once
      --normalize           Used with --output=man-owl to attempt to determine if
                            the ontology is 'normalized' [Rector, A. 2003]The
                            default is False
      --input-format=RDF_FORMAT
                            The format of the RDF document(s) which serve as the
                            initial facts  for the RETE network. One of
                            'xml','n3','trix', 'nt', or 'rdfa'.  The default is
                            xml
      --pDSemantics         Used with --dlp to add pD semantics ruleset for
                            semantics not covered by DLP but can be expressed in
                            definite Datalog Logic Programming The default is
                            False
      --stdin               Parse STDIN as an RDF graph to contribute to the
                            initial facts. The default is False
      --ns=PREFIX=URI       Register a namespace binding (QName prefix to a base
                            URI).  This can be used more than once
      --rules=PATH_OR_URI   The Notation 3 documents to use as rulesets for the
                            RETE network.  Can be specified more than once
      --filter=PATH_OR_URI  The Notation 3 documents to use as a filter
                            (entailments do not particpate in network)
      --ruleFacts           Determines whether or not to attempt to parse initial
                            facts from the rule graph.  The default is False
      --dlp                 Use Description Logic Programming (DLP) to extract
                            rules from OWL/RDF.  The default is False
      --negation            Extract negative rules?
      --normalForm          Whether or not to reduce DL axioms & LP rules to a
                            normal form


