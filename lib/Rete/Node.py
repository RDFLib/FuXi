"""
"""

class Node(object):
    """
    A node in a Rete network.  Behavior between Alpha and Beta (Join) nodes
    """
    def updateDescendentMemory(self,memory):
        if memory.successor not in [mem.successor for mem in self.descendentMemory]:
            self.descendentMemory.append(memory)
        
    def connectToBetaNode(self,betaNode,position):
        # from BetaNode import BetaNode, LEFT_MEMORY, RIGHT_MEMORY, PartialInstantiation
        self.updateDescendentMemory(betaNode.memories[position])
        self.descendentBetaNodes.add(betaNode)        