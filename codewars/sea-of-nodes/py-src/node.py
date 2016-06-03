class Node(object):
    def __init__(self, inputs=[], ctrl_deps=[]):
        self.inputs = []
        self.uses = []
        self.ctrl_deps = []
        self.ctrl_uses = []

        for input_node in inputs:
            self._adapt_input(input_node)

        for ctrl_dep in ctrl_deps:
            self._adapt_ctrl(ctrl_dep)

    def dfs(self):
        visited = set()
        stack = [self]
        while stack:
            n = stack.pop()
            yield n
            for i in n.inputs + n.ctrl_deps:
                if i not in visited:
                    visited.add(i)
                    stack.append(i)

    def _adapt_input(self, input_node):
        if input_node._add_use(self):
            self.inputs.append(input_node)

    def _adapt_ctrl(self, ctrl_dep):
        if ctrl_dep._add_ctrl_use(self):
            self.ctrl_deps.append(ctrl_dep)

    # def _remove_child(self, child):
    #     assert child.use is self
    #     child.use = None
    #     self.inputs.remove(child)

    def _add_use(self, user):
        if user in self.uses:
            # Already used
            return False
        else:
            self.uses.append(user)
            return True

    def _add_ctrl_use(self, user):
        if user in self.ctrl_uses:
            # Already used
            return False
        else:
            self.ctrl_uses.append(user)
            return True

    def replace(self, node):
        pass

class ValueNode(Node):
    pass

class ControlNode(Node):
    pass

class AddNode(ValueNode):
    def __init__(self, lhs, rhs):
        super().__init__([lhs, rhs])

    def __repr__(self):
        return '(+ %s %s)' % tuple(self.inputs)

    def eval(self):
        lhs, rhs = self.inputs
        return lhs.eval() + rhs.eval()

class LitNode(ValueNode):
    def __init__(self, i64):
        super().__init__([])
        self.i64 = i64

    def __repr__(self):
        return '(lit %d)' % self.i64

    def eval(self):
        return self.i64

class SelectNode(ControlNode):
    def __init__(self, value, block):
        super().__init__([value], [block])

class StartNode(ControlNode):
    def exec(self):
        self.ctrl_deps[0].exec()

class ComposeNode(ValueNode):
    def __init__(self, selections):
        super().__init__(selections)

class RetNode(ControlNode):
    def __init__(self, n):
        super().__init__([n])

    def __repr__(self):
        return '(ret %s)' % self.value

    @property
    def value(self):
        return self.inputs[0]

    def exec(self):
        raise Return(self.value.eval())

class ExitNode(ControlNode):
    def __init__(self, c):
        super().__init__([], [c])

    def __repr__(self):
        return '(exit %s)' % self.ctrl

    @property
    def ctrl(self):
        return self.ctrl_deps[0]

    def exec(self):
        return self.ctrl.exec()

class Return(Exception):
    def __init__(self, value):
        self.value = value

class RegionNode(ControlNode):
    pass

class IfNode(ControlNode):
    def __init__(self, cond):
        super().__init__([cond])

    def exec(self):
        res = self.inputs[0].eval()
        t, f = self.ctrl_uses
        if res == 0:
            f.exec()
        else:
            t.exec()

n = ExitNode(RetNode(AddNode(LitNode(1), LitNode(2))))
n2 = RegionNode()
for ch in list(n.dfs()):
    ch._adapt_ctrl(n2)
print(n2.ctrl_uses)
n.exec()
