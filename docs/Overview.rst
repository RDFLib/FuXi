==============================================================================
Overview: components and architecture
==============================================================================

Introduction
============

This page gives an overview of what FuXi is, i.e. its components and the
underlying architectural principles that motivated its development.

Contents
========

.. contents::
   :depth: 2


Architectural Motivation
=======================================================

Briefly, `FuXi </p/fuxi/wiki/FuXi>`_ aims to be the engine for
contemporary expert systems based on the Semantic Web technologies.
Traditionally, expert systems are an application of computing and
artificial intelligence with the aim of supporting software that
attempts to reproduce the deterministic behavior of one or more human
experts in a specific problem domain.

Typically, the term loosely refers to systems built using two separate
(and often competing) architectural approaches to the same general
problem: `Logic
programming <http://en.wikipedia.org/wiki/Logic_Programming>`_ and
`Production systems <http://en.wikipedia.org/wiki/Production_system>`_.
The former is the basis for modern (deductive) database theory and the
latter is the family of systems that underly business rule processing
implementations.

One of the more important findings in deductive database literature and
a key architectural constraint of python-dlp is the fact that for
certain classes of formal rule languages (Datalog), the semantics of
both systems coincide ***(1)***. We believe the combination of this
important characteristic along with its proven, robust scalability
suggests that this language be used as the basis for an expert system
for the Semantic Web.

This particular framework is often placed in contrast to more
traditional, logic-based approaches to knowledge representation that are
the basis for OWL and emphasize an 'open-world' view of data. We believe
this argument is a red herring and easily addressed by the fact that
Datalog (or Horn logic) - the most common of all rule language syntax -
has a semantics that does not violate the open world assumption when you
remove negation from the language.

The question of whether such a restricted language is able to meet
knowledge representation requirements should be answered for each
relevant domain (rather than in general) as each brings their own set of
needs. The development of Python-dlp was motivated by problems in the
domain of medical terminology and the knowledge representation
requirements have been well met there.

At least for this restricted language, we have a versatility that spans
both traditional approaches to expert systems as well as that of
database theory and does not violate the open-world assumption. For
these reasons, python-dlp is able to be a framework for the next
generation of Semantic Web applications that emphasizes provable
scalability, expressive versatility, and a rule-based knowledge
representation.

Knowledge Representation Languages
===========================================================================

FuXi uses `RDF`_ for its core knowledge representation of facts in a
particular domain. It relies on `RDFS`_ and a fragment of `OWL`_/`OWL2`_
(specifically the fragment of Description Logic that intersects with
`Datalog`_) for a model-theoretic knowledge representation of restrictions
on `how the RDF is interpreted`_.

Finally, `RIF-Core`_ is adopted for capturing rule-based::

    *IF* ... *THEN* ..

logic for the RDF.

.. _RDF: http://www.w3.org/RDF/
.. _RDFS: http://www.w3.org/RDF/
.. _OWL: http://www.w3.org/RDF/
.. _OWL2: http://www.w3.org/RDF/
.. _Datalog: http://www.w3.org/RDF/
.. _how the RDF is interpreted: http://www.w3.org/TR/rdf-mt/#interp
.. _RIF-Core: http://www.w3.org/TR/rif-core/

Components
===========================

RETE-UL Network
-----------------------------------------------------------------

At the heart of the python-dlp framework is an implementation of most of
the RETE-UL algorithms outlined in the PhD thesis (1995) of Robert
Doorenbos:

    Production Matching for Large Learning Systems.

Robert's thesis describes a modification of the original
`Rete <http://en.wikipedia.org/wiki/Rete_algorithm>`_ algorithm that
(amongst other things) limits the fact syntax (referred to as Working
Memory Elements) to 3-item tuples (which corresponds quite nicely with
the RDF abstract syntax). The thesis also describes methods for using
hash tables to improve efficiency of alpha nodes and beta nodes.

Sideways Information Passing
-------------------------------------------------------------------------------------------

`FuXi </p/fuxi/wiki/FuXi>`_ has full support for Sideways Information
Passing, a general optimization technique originally based on one of the
more important algorithms in database theory called the Generalized
Magic Set (GMS) transformation. Originally, the GMS transformation is
used to efficiently evaluate a query against a (possibly recursive)
datalog program and database. It is the theoretical basis of relational
algebra implementations which include (possibly recursive)
`views <http://en.wikipedia.org/wiki/Database_view>`_.

Base and Derived Predicates
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

An important distinction needed for `FuXi </p/fuxi/wiki/FuXi>`_'s SIP
capabilities is between **derived** predicates and **base** predicates,
the former comprises the Intensional Database (**IDB**) and the latter
the Extensional Database (**EDB**). Derived predicates are those that
(as the name suggests) are derived via rules and base predicates are (in
the traditional sense) the stated *facts* (also known as *the
database*).

Backward Chaining / Top Down Evaluation
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

`FuXi </p/fuxi/wiki/FuXi>`_ comes with two top-down (backward chaining)
algorithms for SPARQL RIF-Core and OWL 2 RL entailment. The first is a
native Prolog-like Python implementation that can take a triple (as a
goal) and generate a series of SPARQL queries against the given
factGraph, combining the results as answers to the goal. ** This has
been deprecated** by an extension of the `Backwards Fixpoint
Procedure <http://dx.doi.org/10.1016/0169-023X(90)90017-8>`_, a
'meta-interpretation' method that creates a program or ruleset that
captures (or encodes) a top-down procedure for answering the original
question such that it can be evaluated via a forward-chaining /
bottom-up algorithm.

Both of these methods can be used to answer queries that involve derived
predicates whose semantics are defined either in a set of OWL2 RL
`axioms <http://www.w3.org/TR/owl2-profiles/#Profile_Specification_3>`_
or RIF Core
`formulas <http://www.w3.org/TR/rif-core/#Formulas_of_RIF-Core>`_. These
answers are computed via a series of coordinated SPARQL queries
dispatched against the user-specified RDF graph (which can be connected
to a large, remote SQL backend).

Reason for Deprecation
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

The
`FuXi </p/fuxi/wiki/FuXi>`_.Rete.TopDown`? </p/fuxi/w/edit/TopDown>`_
module is essentially a refutation (proof)-based implementation of a
top-down strategy. Adding tabling / memoization to this strategy became
quite complicated and the BFP is meant to address (and replace) this
complexity:

    One conclusion that can be drawn fromthe BFP is that it does not
    make sense to hierarchically structure queries according to their
    generation. In contrast it makes sense to rely on a static rewriting
    such as the Alexander or Magic Set rewriting and process the
    resulting rules with a semi-naive bottom-up rule engine. --
    `Foundations of Rule-Based Query
    Answering <http://www.comlab.ox.ac.uk/files/3094/fulltext.pdf>`_

    BFP collects generated queries and proven facts in (n-ary) relations
    [...] In contrast SLD-Resolution relies on hierarchical data
    structure that relate proven facts and generated queries to the
    queries they come from. -- `Backwards Fixpoint
    Procedure <http://dx.doi.org/10.1016/0169-023X(90)90017-8>`_

It is this hierarchical data structure (still a work in progress at the
time the TopDown`? </p/fuxi/w/edit/TopDown>`_ method was deprecated)
that is `most <http://code.google.com/p/fuxi/issues/detail?id=28>`_
problematic.

The use of the RETE-UL network to
`implement <http://code.google.com/p/fuxi/wiki/FuXiUserManual#FuXi_.LP>`_
a BFP ruleset results in a much smaller and manageable code base, so
this is now the preferred means for top-down SPARQL query mediation /
entailment (see:
`TopDownSW <http://code.google.com/p/fuxi/wiki/TopDownSW>`_)

Builtin Infrastructure
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

There is a dual framework for handling managing user-defined built-in
predicates. They can be implemented as Python functions that are the
values of a mapping from URI references of he builtin predicates. These
are then used during forward chained evaluation via the RETE-UL network
or during backward chaining. In the latter case, the functions are
invoked the same as they would during forward chaining (one at a time)
or can be converted into FILTER expressions and combined with the
literals that precede it in the body (or antecedent) of a RIF rule into
one of the intermediate SPARQL queries that are dispatched against the
fact graph.

In converting builtins into SPARQL FILTERs, a user-specified template
can be provided for this purpose. An example of how this can be done is
below. The format for this SPARQL FILER template specification is in
RDF:

::

    @prefix templ:  <http://code.google.com/p/fuxi/wiki/BuiltinSPARQLTemplates#>.
    @prefix owl:    <http://www.w3.org/2002/07/owl#>.
    @prefix owl:    <http://www.w3.org/2002/07/owl#>.
    @prefix rdfs:   <http://www.w3.org/2000/01/rdf-schema#>.
    @prefix rdf:    <http://www.w3.org/1999/02/22-rdf-syntax-ns#>.
    @prefix str:    <http://www.w3.org/2000/10/swap/string#>.
    @prefix log:    <http://www.w3.org/2000/10/swap/log#>.
    @prefix math:   <http://www.w3.org/2000/10/swap/math#>.

    str:greaterThan          templ:filterTemplate "STR(%s) > STR(%s)" .
    log:notEqualTo           templ:filterTemplate "%s != %s" .
    str:startsWith           templ:filterTemplate "REGEX(%s,'$%s')" .
    str:greaterThanOrEqualTo templ:filterTemplate "STR(%s) >= STR(%s)" .
    str:lessThanOrEqualTo    templ:filterTemplate "STR(%s) <= STR(%s)" .

FuXi and Description Logic Programming
-----------------------------------------------------------------------------------------------------

`FuXi </p/fuxi/wiki/FuXi>`_ includes an implementation of the
Description Logic Programming language. Specifically, for certain
restricted classes of OWL-DL and OWL2 (OWL2 RL in particular), axioms
expressed in this language can be converted into a set of rules that
exactly capture the semantics for efficient evaluation via the RETE-UL
network .

Non-Monotonic Negation
---------------------------------------------------

`FuXi </p/fuxi/wiki/FuXi>`_ has support for non-monotonic negation:
default negation and negation as failure. There is a very long history
of non-monotonic reasoning. The reader is directed to `Logic Programming
and Negation: A
Survery <http://citeseerx.ist.psu.edu/viewdoc/summary?doi=10.1.1.20.7217>`_
for more details on the subject.

`FuXi </p/fuxi/wiki/FuXi>`_ can perform reasoning over rules with
negated literals in the body / consequent. When calculating an RDF
closure graph via forward chaining, the rules are separated into two
sets: those without negation and those without. The first group is used
to create an initial RDF closure (i.e., just those conclusions that
follow from a positive theory. Then the remaining rules are converted
into a SPARQL query against this closure graph and fill out the
consequent using the resulting bindings (this is quite similar to the
way the SPIN framework `uses <http://spinrdf.org/spin.html#spin-rules>`_
SPARQL constructs to implement rules).

The conversion to and from SPARQL (for the most part) follows the
conventions described in `The Expressive Power of
SPARQL <http://www.dcc.uchile.cl/~cgutierr/papers/expPowSPARQL.pdf>`_.
Historically, it has been shown that for theories that are stratified
(i.e., where there aren't any circular references between conclusion
that follow from *negative* consequences), there will always be a unique
set of answers even in the face of rules that use negation.

This essentially coincides with the `stable model
semantics <http://en.wikipedia.org/wiki/Stable_model_semantics>`_.

When `FuXi </p/fuxi/wiki/FuXi>`_ is solving a query via backward
chaining, however, the rulesets are considered a complete set (including
both those that involve negated consequences and those that dont). When
the top-down solver comes across a negated literal in the body, it will
attempt to *solve* the positive literal (as a subgoal) and will continue
processing the rule only if the attempt fails, thus it is more inline
with negation as failure. However, again, historically, for stratified
(datalog) theories, negation as failure, stable model semantics have the
same semantics and are just as computationally tractable as those
without negation (they scale with the data via a polynomial curve).

So, using the RIF-Core safety checking capabilities, a user can perform
non-monotonic queries in a manner that is guaranteed to scale.

Unfortunately, the only way that negated literals can be introduced into
a RIF ruleset (this will change in the future) is via the use of
owl:complementOf in an OWL graph that is converted into a RIF ruleset.
For more on the nature of this conversion, see: `Using OWL and Default
Negation to Reason about Patient
Records <http://chimezie.posterous.com/using-owl-and-default-negation-to-reason-abou>`_

OWL and Rule APIs
-----------------------------------------

`FuXi </p/fuxi/wiki/FuXi>`_ includes two Python APIs that seek to
leverage the versatility and expressiveness of the host language for
managing rulesets and OWL axioms. The former API is described in more
detail in the `user manual </p/fuxi/wiki/FuXiUserManual>`_ and the
latter (InfixOWL) is the subject of the 2008 OWLED paper `InfixOWL: An
Idiomatic Interface for
OWL <http://ftp.informatik.rwth-aachen.de/Publications/CEUR-WS/Vol-432/owled2008eu_submission_19.pdf>`_

Additional Capabilities
-----------------------------------------------------

In addition, `FuXi </p/fuxi/wiki/FuXi>`_ includes libraries for

-  Reducing DL and Horn clauses into *normal* forms
-  (Limited) support for default negation (different from the
   interpretation of negation associated with OWL, but using OWL as a
   surface syntax for this purpose)
-  Proof generation
-  Visualization libraries for the corresponding RETE networks built
   from the rulesets and of proof trees.

Usage
-----------------

The typical usage of python-dlp (or `FuXi </p/fuxi/wiki/FuXi>`_ more
specifically) is to either programatically compose a set of OWL
descriptions using the Infix OWL interface or to parse them from an
existing OWL/RDF document. Then, the DLP APIs can be used to construct a
RETE network from a ruleset that corresponds with the OWL descriptions.
Finally, the GMS transformation can be used (in an intermediate step) to
re-write the resulting rules into a more optimal form for evaluation
against a corresponding RETE network.

*(1)* Vianu, V.: Rule-based languages, Annals of Mathematics and
Artificial Intelligence, Springer 1997.

