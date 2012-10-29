==============================================================================
Rete Actions
==============================================================================

Description of the Action mechanisms in the RETE implementation.

The `FuXi </p/fuxi/wiki/FuXi>`_.Rete.Network.Network class supports
`externally defined actions <http://www.w3.org/TR/rif-prd/#Execute>`_.
In particular, for each terminal BetaNode`? </p/fuxi/w/edit/BetaNode>`_
(the beta node associated with the firing of a particular rule) in a
Network instance, there is an
`executeAction <http://code.google.com/p/fuxi/source/browse/lib/Rete/BetaNode.py#535>`_
attribute that is a mapping from a (ground) RDF triple to a tuple of
(**override**,**executeAction**) where **executeAction** is a function
with the following signature:

def someExecuteAction(*tNode*, *inferredTriple*, *token*, *binding*,
debug = False)

and **override** is a boolean value
`indicating <http://code.google.com/p/fuxi/source/browse/lib/Rete/Network.py#527>`_
whether the custom action will perform *all* of the production duties
(bypassing the inference of triples, etc.). The first parameter passed
in is the terminal node, the second is None if **override** is True or
the inferred triple otherwise, token is the fully instantiated
`token <http://code.google.com/p/fuxi/source/browse/lib/Rete/BetaNode.py#146>`_,
and binding is the `solution
mapping <http://www.w3.org/TR/rdf-sparql-query/#defn_sparqlSolutionMapping>`_
associated with the fully instantiated token as a dictionary of rdflib
terms (or None if **override** is True). The custom action can then use
these parameters to implement its behavior.

Externally defined actions can be registered via the
`FuXi.Rete.Network.Network.registerReteAction <http://code.google.com/p/fuxi/source/browse/lib/Rete/Network.py#643>`_
method.

