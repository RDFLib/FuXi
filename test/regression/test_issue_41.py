"""
http://code.google.com/p/fuxi/issues/detail?id=41

the network.registerAction method must check that the RHS
is a Uniterm and not a compound term (e.g. And, Empty, etc)
before trying to call rule.formula.head.toRDFTuple().
"""
import unittest
from rdflib import Variable
from FuXi.Rete.RuleStore import SetupRuleStore
from FuXi.Horn.HornRules import HornFromN3
from StringIO import StringIO

rule_fixture = """\
@prefix test: <http://example.org/>.

{ ?x a ?y } => { 
 ?x test:value "hello" .
 ?x test:value "world" 
}.
"""

class TestUnitermAction(unittest.TestCase):
    def setUp(self):
        self.rules = HornFromN3(StringIO(rule_fixture))

    def test_issue_41(self):
        ruleStore, ruleGraph, network = SetupRuleStore(makeNetwork=True)
        for rule in self.rules:
            network.buildNetworkFromClause(rule)
        def dummy(*av, **kw):
            pass
        head = (Variable("x"), Variable("y"), Variable("z"))
        network.registerReteAction(head, False, dummy)

if __name__ == '__main__':
    suite = unittest.makeSuite(TestUnitermAction)
    unittest.TextTestRunner(verbosity=5).run(suite)
