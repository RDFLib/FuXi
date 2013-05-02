from FuXi.Rete.Network import ReteNetwork, InferredGoal
from FuXi.Rete.BetaNode import BetaNode
from FuXi.Rete.AlphaNode import AlphaNode, ReteToken, BuiltInAlphaNode
from FuXi.Rete.ReteVocabulary import RETE_NS


PROGRAM2 = \
u"""
@prefix ex: <http://doi.acm.org/10.1145/28659.28689#>.
{ ?X ex:flat ?Y } => { ?X ex:sg ?Y }.
{ ?X ex:up ?Z1 .
  ?Z1 ex:sg ?Z2.
  ?Z2 ex:flat ?Z3.
  ?Z3 ex:sg ?Z4.
  ?Z4 ex:down ?Y
  } => {
  ?X ex:sg ?Y }.
"""

PROGRAM1 = \
"""
@prefix : <http://example.com#>.
{ ?X par ?Y } => { ?X anc ?Y }
{ ?X par ?Z . ?Z  anc ?Y } => { ?X anc ?Y }
"""

PARTITION_LP_DB_PREDICATES = \
"""
@prefix ex: <http://doi.acm.org/10.1145/16856.16859#>.
ex:a ex:father ex:b.
ex:b ex:parent ex:c.
ex:b ex:grandfather ex:d.
{ ?X ex:father ?Z. ?X ex:parent ?Y } => { ?X ex:grandfather ?Y }.
"""
