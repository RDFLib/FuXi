"""
"""

class Node(object):
    """
    A node in a Rete network.  Behavior between Alpha and Beta (Join) nodes
    """
    def connectToBetaNode(self,betaNode,position):
        from BetaNode import BetaNode, LEFT_MEMORY, RIGHT_MEMORY, PartialInstanciation
        self.descendentMemory.append(betaNode.memories[position])
        self.descendentBetaNodes.add(betaNode)        