==============================================================================
FuXi Semantics 
==============================================================================

A sketch of a semantics for FuXi based on Classic Logic Programming formalisms.

-  *This page may later be superseded by or become aligned with *
   `N3Logic: A Logical Framework For the World Wide
   Web <http://arxiv.org/abs/0711.1533>`_

Introduction
===============================

`FuXi </p/fuxi/wiki/FuXi>`_ adopts the semantics of Description Logic
Programs *`#1 <#1>`_*. This combined KR is a unidirectional mapping from
a restricted `subset <http://www.w3.org/Submission/owl11-tractable/#4>`_
of Description Logic to a corresponding Horn ruleset (*def-Horn*) and a
Logic Program (*def-LP*). `FuXi </p/fuxi/wiki/FuXi>`_ uses Logic
Programs *`#2 <#2>`_* as its operation semantics due to its superior
lineage *`#4 <#4>`_* and time *`#2 <#2>`_* & space *`#3 <#3>`_*
complexity. The restrictions adopted are those outlined in the
Description Logic Programming Paper and listed below (known as
*f-weakenings*):

-  *Definite*: i.e., no negation operators (either classic or NAF)
-  *Equality-free*: no equals operator (owl:sameAs, or fully
   communicative owl:equivalentClass)
-  *Datalog*: no function symbols (but 'external' predicates are
   allowed)

The mapping between def-Horn and def-LP is sound and complete (for rules
with only ground terms in the head/conclusion). *need explanation of
semantics of BNodes in the head* In particular, LP's cannot express
existentially quantified variables in the head of a rule (or a fact).
Also, universally quantified variables that appear in the head of a
rule, must appear somewhere in the body of the same rule.

Semantics
=========================

`FuXi </p/fuxi/wiki/FuXi>`_'s semantics are comprised of a set of
Description Logic Programs.

The combined semantics include f-weakenings *`#1 <#1>`_* of Description
Horn Logic rulesets (generated from DL expressions via the algorithm
presented by Grosof, B. et.al.). Description Horn Logic rulesets
generated from DL expressions can be used in conjunction with rules
expressed in their native dialect, as long as they adhere to *DL-safety
restrictions* (see:
`http://code.google.com/p/owl1-1/wiki/SafeRules <http://code.google.com/p/owl1-1/wiki/SafeRules>`_).

The semantics of a generated DLP, additional DL-safe def-LP rules, an
initial, ground (possibly by
`skolemization <http://www.w3.org/TR/rdf-mt/#defskolem>`_ *`#4 <#4>`_*)
set of facts is a conclusion set, where each conclusion is a ground
atom, i.e., fact, entailed by the LP. Formally, the semantics of the
corresponding def-LP R is defined as follows. Let HB stand for the
Herbrand base of R. The conclusion set C is the smallest (w.r.t. set
inclusion) subset S of HB such that for any rule in the DLP, the
conclusion set is a Herbrand Model *`#2 <#2>`_*

Details
=====================

Implementations` <#Implementations>`_
-------------------------------------

In `FuXi </p/fuxi/wiki/FuXi>`_'s implementation, the conclusion set is
calculated using a RETE-UL network. Other evaluation mechanism can be
adopted for an operational semantics, including:

-  FOL Resolution principle
-  General modus ponen
-  Euler, cycle-detected backwards (top-down) unification
-  Datalog reduction to relation algebra and evaluation against RDBMS

The Abstract Syntax and Mappings to
SWRL/RIF/N3` <#The_Abstract_Syntax_and_Mappings_to_SWRL/RIF/N3>`_
-----------------------------------------------------------------------------------------------------

The DLP abstract syntax is very expressive and can be serialized as any
of:

-  SWRL (DL-Safe subset)
-  RIF Basic Logic Dialect `BLD Last Call
   Draft <http://www.w3.org/2005/rules/wg/wiki/FrontPage?action=AttachFile&do=get&target=ED-rif-bld-20070914.html>`_
-  *"N3-Datalog"* (a syntactic subset of full N3 - a sibling of Turtle
   and SPARQL triple patterns)

RIF BLD: DLP
-------------------------------

Concrete syntax

::

      CONDITION   ::= CONJUNCTION | DISJUNCTION | EXISTENTIAL | ATOMIC
      CONJUNCTION ::= 'And' '(' CONDITION* ')'
      DISJUNCTION ::= 'Or' '(' CONDITION* ')'
      EXISTENTIAL ::= 'Exists' Var+ '(' CONDITION ')'
      ATOMIC      ::= Uniterm
      Uniterm     ::= Const '(' TERM* ')'
      TERM        ::= Const | Var | Uniterm
      Const       ::= CONSTNAME | '"'CONSTNAME'"''^^'TYPENAME
      Var         ::= '?'VARNAME

      Ruleset  ::= RULE*
      RULE     ::= 'Forall' Var* CLAUSE
      CLAUSE   ::= Implies | ATOMIC
      Implies  ::= ATOMIC ':-' CONDITION
      CONSTNAME ::= CURIE | '<' IRI '>' | RDFLiteral

N3-Datalog
~~~~~~~~~~~~~~~~~~~~~~~~~~~

Start with
`"n3rules" <http://www.w3.org/2000/10/swap/grammar/n3rules-report.html>`_
and remove:
`existential <http://www.w3.org/2000/10/swap/grammar/n3rules-report.html#existential>`_
and
`existential_s <http://www.w3.org/2000/10/swap/grammar/n3rules-report.html#existential_s>`_

Mapping def-LP to RETE-UL
---------------------------------------------------------

A syntactic function is outlined which has a domain of a def-LP
expression and a range of a corresponding RETE-UL *`#3 <#3>`_* network.
See `"Mapping Rete algorithm to FOL and then to
RDF/N3" <http://copia.ogbuji.net/blog/2006-07-14/fuxi-mapping-from-rete-to-n3>`_
for a high-level overview.

Operational Semantics for Default Negation
-------------------------------------------------------------------------------------------

See: NegatedConditions`? </p/fuxi/w/edit/NegatedConditions>`_ for
RETE-UL support for (**NAF**)

Efficient Proof Generation
-----------------------------------------------------------

Use *Magic sets* *`#5 <#5>`_* for efficient forward-chained theorem
proof generation

Correspondence with Full Notation 3
-----------------------------------------------------------------------------

See: `Notation 3 Logic <http://www.w3.org/DesignIssues/N3Logic>`_. This
would require extending the data log restriction with support for
function symbols (thus making it no longer decidable *`#2 <#2>`_* - with
the exception of if the functions are non-recursive), and negation as
failure (making it only polynomial space complexity *`#2 <#2>`_* ).

Formulae & Named Graphs
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Formal N3 Formulae are epistemological operators and thus not in the
Herbrand universe of any Logic Program. However, they can be used to
denote head and body atoms in a Horn clause. Kyle, G.
`introduces <http://ninebynine.org/RDFNotes/UsingContextsWithRDF.html#xtocid-6303976>`_
a notion of formula nodes into the RDF model theory with a partitions of
formulaic (hypothetical) statements. This logic is outside the bounds of
FOL with the possible exception of introducing non-deterministic
function symbols (builtins) for scoped inference mechanics
(log:includes, log:semantics, etc..).

Time Complexity: Polynomial
-------------------------------------------------------------

Space Complexity: Polynomial
---------------------------------------------------------------

Appendix
=======================

KR expressive classes / restrictions diagram:

`|image2| <http://www.cs.man.ac.uk/~horrocks/Publications/download/2003/p117-grosof.pdf>`_

References
===========================

#. `Description Logic Programs: Combining Logic Programs with
   Description
   Logic <http://www.cs.man.ac.uk/~horrocks/Publications/download/2003/p117-grosof.pdf>`_
#. `Complexity and expressive power of logic
   programming <http://doi.acm.org/10.1145/502807.502810>`_
#. `Production Matching for Large Learning
   Systems <http://reports-archive.adm.cs.cmu.edu/anon/1995/CMU-CS-95-113.pdf>`_
#. `A Realistic Architecture for the Semantic
   Web <http://www.inf.unibz.it/~jdebruijn/publications/msa-ruleml05.pdf>`_
#. `Magic sets and other strange ways to implement logic programs
   (extended abstract) <http://doi.acm.org/10.1145/6012.15399>`_

.. |image2| image:: http://python-dlp.googlecode.com/files/MT-KR-Geneology.png
