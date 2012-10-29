.. FuXi documentation master file

============
Introduction
============

FuXi (pronounced foo-shee - 伏羲) is a bi-directional logical reasoning system for the Semantic Web. It is implemented as a companion to `RDFLib <https://github.com/RDFLib>`_ – which it requires for its various RDF processing. FuXi aims to be the engine for contemporary expert systems based on the Semantic Web technologies.

FuXi is named after the `first <http://en.wikipedia.org/wiki/Fu_Hsi>`_ of the Three Sovereigns
of ancient China.  It originally formed from an idea to express the underlying symbols (and
their relationships) in the Yi Jing or Zhou Yi ("The Book of Changes") in OWL and RDF in order
to reason over their structural relationships.

For an overview of the architecture, please read `FuXi Overview <http://code.google.com/p/fuxi/wiki/Overview>`_ and 
`FuXi User Manual <http://code.google.com/p/fuxi/wiki/FuXiUserManual>`_ for more information.

* `fuxi <https://fuxi.googlecode.com/hg/>`_ *

`DOAP <http://usefulinc.com/doap/>`_ file:
* `/trunk/fuxi/FuXi.rdf <http://python-dlp.googlecode.com/svn/trunk/fuxi/FuXi.rdf>`_ *


Contents:

.. toctree::
   :maxdepth: 1

   Overview
   FuXi
   FuXiUserManual
   Installation_Testing
   Tutorial
   FuXiSemantics
   InfixOwl
   builtin_SPARQL_templates
   data_description_language
   ReteActions
   TopDownSW







Modules
=======

Packages
-----------------------

-  Rete.Network: Rete network
-  Rete.Proof: Proof generation / serialization
-  Rete.DLP: Description Logic Programming core
-  Horn: RIF Horn rules core API
-  Syntax.InfixOWL: InfixOWL API


FuXi.Rete
=========

An implementation of most of the RETE-UL algorithms outlined in the PhD thesis (1995) of Robert Doorenbos: *Production Matching for Large Learning Systems*.  See
`FuXi.Rete <http://code.google.com/p/fuxi/wiki/FuXiUserManual#FuXi_.Rete>`_ in manual for how to use SetupRuleStore to create an ReteNetwork.

.. autofunction:: FuXi.Rete.RuleStore.SetupRuleStore
.. autoclass:: FuXi.Rete.Network.ReteNetwork
    :members:
    :undoc-members:

FuXi.Horn
=========

FuXi includes an API that was originally implemented as a reference implementation of the W3C's Rule Interchange Format Basic Logic Dialect but eventually evolved into a
Pythonic API for managing an abstract Logic Programming syntax. It includes functions used for creating rulesets converted from OWL RDF expressions and creating
a Horn ruleset from a parsed Notation 3 graph:

.. autofunction:: FuXi.Horn.HornRules.HornFromN3
.. autofunction:: FuXi.Horn.HornRules.HornFromDL
.. autofunction:: FuXi.Horn.HornRules.NetworkFromN3

Below are the various classes and functions that comprise this API

.. automodule:: FuXi.Horn.PositiveConditions
  :members:
  :undoc-members:


FuXi.Rete.Magic
===============

This module is where the `Sideways Information Passing <http://code.google.com/p/fuxi/wiki/Overview#Sideways_Information_Passing>`_ 
reasoning capabilities are implemented. 

.. autofunction:: FuXi.Rete.Magic.MagicSetTransformation

FuXi.SPARQL
===========

Backward chaining algorithms for SPARQL RIF-Core and OWL 2 RL entailment. The Backwards Fixpoint Procedure (BFP) implementation uses 
RETE-UL as the RIF PRD implementation of a meta-interpreter of a ruleset that evaluates conjunctive (BGPs) SPARQL queries using a 
SPARQL 1.1 RIF Entailment Regime. 

See: `Overview <http://code.google.com/p/fuxi/wiki/Overview#Backward_Chaining_/_Top_Down_Evaluation>`_ and 
`User Manual <http://code.google.com/p/fuxi/wiki/FuXiUserManual#FuXi_.SPARQL>`_

.. autoclass:: FuXi.SPARQL.BackwardChainingStore.TopDownSPARQLEntailingStore
    :members:
    :undoc-members:

FuXi.Syntax
===========

Includes the InfixOwl library (see the linked Wiki for more information).  A Python binding for OWL Abstract Syntax that incorporates the 
Manchester OWL Syntax.  See the `Wiki <http://code.google.com/p/fuxi/wiki/InfixOwl>`_ and `OWLED paper <http://python-dlp.googlecode.com/files/infixOwl.pdf>`_

.. automodule:: FuXi.Syntax.InfixOWL
   :members:
   :undoc-members:

Indices and tables
==================

* :ref:`genindex`
* :ref:`modindex`
* :ref:`search`

