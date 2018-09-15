from enum import Enum

class Race(Enum):
    WOREWOLF = 1
    HUMAN = 2

# Optimize: This is sparse so we just need a two field class.
def gen_players(n, k):
    res = []
    def go(i, ww_left):
        if i >= n:
            if ww_left == 0:
                k(res)
            return
        if ww_left > 0:
            res.append(Race.WOREWOLF)
            go(i + 1, ww_left - 1)
            res.pop()
        res.append(Race.HUMAN)
        go(i + 1, ww_left)
        res.pop()
    go(0, 2)

# gen_players(3, print)

# Optimize: This is tail recursive.
def check_assertion(xs, players, k):
    def go(i, lies_left, ww_lies_left):
        if i >= len(xs):
            if lies_left == 0 and ww_lies_left == 0:
                k(players)
            return
        (nth, player) = xs[i]
        if player == players[nth]:
            go(i + 1, lies_left, ww_lies_left)
        else:
            # Lie.
            if lies_left <= 0:
                # Cut
                return
            if players[i] == Race.WOREWOLF:
                if ww_lies_left <= 0:
                    # Cut
                    return
                go(i + 1, lies_left - 1, ww_lies_left - 1)
            else:
                go(i + 1, lies_left - 1, ww_lies_left)
    go(0, 2, 1)

SAMPLE_INPUT_1 = '''
5
-2
+3
-4
+5
+4
'''

def parse_input(lines):
    ns = [int(x.strip()) for x in lines.split() if x.strip()]
    n = ns[0]
    rs = [(abs(r) - 1, Race.HUMAN if r > 0 else Race.WOREWOLF) for r in ns[1:]]
    return (n, rs)


def solve(args):
    class Done(Exception):
        pass

    def done(ps):
        raise Done(ps)

    n, rs = parse_input(args)

    def check_player(ps):
        check_assertion(rs, ps, done)

    try:
        gen_players(n, check_player)
    except Done as d:
        return d.args[0]

def print_solution(sol):
    if sol:
        ww_ixs = [i + 1 for (i, p) in enumerate(sol) if p == Race.WOREWOLF]
        print(' '.join(str(i) for i in ww_ixs))
    else:
        print('No Solution')

print_solution(solve(SAMPLE_INPUT_1))
