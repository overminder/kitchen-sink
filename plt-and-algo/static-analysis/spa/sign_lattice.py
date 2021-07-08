""" Exercise 6.5 in the lecture notes:

    checking monotonicity of an operator given by an n × n table.
"""

from enum import IntEnum, auto
import random

class Sign(IntEnum):
    TOP = 0
    NEG = 1
    ZERO = 2
    POS = 3
    BOT = 4

    @staticmethod
    def lt(x, y):
        if y == Sign.TOP:
            return True
        if x == Sign.BOT:
            return True
        return False

    @staticmethod
    def leq(x, y):
        return x == y or Sign.lt(x, y)

    @staticmethod
    def lub(x, y):
        if x == y:
            return x
        if x == Sign.BOT:
            return y
        if y == Sign.BOT:
            return x
        if x == Sign.TOP:
            return x
        if y == Sign.TOP:
            return y
        return Sign.TOP

    @staticmethod
    def glb(x, y):
        if x == y:
            return x
        if x == Sign.BOT:
            return x
        if y == Sign.BOT:
            return y
        if x == Sign.TOP:
            return y
        if y == Sign.TOP:
            return x
        return Sign.BOT

    @staticmethod
    def read(name):
        return SYMBOLS.index(name)

    @staticmethod
    def show(value):
        return SYMBOLS[value]

    @staticmethod
    def run(lhs, op, rhs):
        result = getattr(Sign, op)(lhs, rhs)
        if isinstance(result, bool):
            result_repr = str(result)
        elif isinstance(result, Sign):
            result_repr = Sign.show(result)
        else:
            raise ValueError(result)
        print(' '.join([Sign.show(lhs), op, Sign.show(rhs), '=',
            result_repr]))

# (Sign, Sign)
class Sign2:
    @staticmethod
    def lt(p1, p2):
        x1, y1 = p1
        x2, y2 = p2
        return Sign.lt(x1, x2) and Sign.lt(y1, y2)

    @staticmethod
    def leq(p1, p2):
        return p1 == p2 or Sign2.lt(p1, p2)

    @staticmethod
    def lub(p1, p2):
        x1, y1 = p1
        x2, y2 = p2
        return Sign.lub(x1, x2), Sign.lub(y1, y2)

    @staticmethod
    def show(p):
        return '(' + ', '.join(Sign.show(s) for s in p) + ')'

    @staticmethod
    def run(lhs, op, rhs):
        result = getattr(Sign2, op)(lhs, rhs)
        if isinstance(result, bool):
            result_repr = str(result)
        elif isinstance(result, tuple):
            result_repr = Sign2.show(result)
        else:
            raise ValueError(result)
        print(' '.join([Sign2.show(lhs), op, Sign2.show(rhs), '=',
            result_repr]))

SYMBOLS = '?-0+⊥'

def parse_table(table):
    (name, *header), *rests = [line.split(' ') for line in table.strip().split('\n')]
    out = []
    for rest in rests:
        lhs, *results = rest
        assert len(results) == len(header)
        for rhs, result in zip(header, results):
            args = Sign.read(lhs), Sign.read(rhs)
            out.append((args, Sign.read(result)))
    return name, out

TABLE_GT = """
> ⊥ 0 - + ?
⊥ ⊥ ⊥ ⊥ ⊥ ⊥
0 ⊥ 0 + 0 ?
- ⊥ 0 ? 0 ?
+ ⊥ + + ? ?
? ⊥ ? ? ? ?
"""

def gen_table(n):
    signs = list(Sign)
    c = lambda: random.choice(signs)
    table = [((c(), c()), c()) for _ in range(n)]
    return table

def main():
    _, table = parse_table(TABLE_GT)
    # table = gen_table(100)
    # Hmm this is n^4 rather than n^3...
    for i, entry in enumerate(table):
        for j, entry2 in enumerate(table):
            if i == j:
                continue
            args1, res1 = entry
            args2, res2 = entry2
            if Sign2.leq(args1, args2):
                assert Sign.leq(res1, res2)
            if Sign2.leq(args2, args1):
                assert Sign.leq(res2, res1)
    # Sign2.run((Sign.BOT, Sign.BOT), 'lub', (Sign.TOP, Sign.ZERO))

if __name__ == '__main__':
    main()

