import csv
import re
from datetime import datetime

def unparen(x):
    if x is None:
        return 1
    else:
        x = x.strip()
        assert x.startswith('(')
        assert x.endswith(')')
        return int(x[1:-1])

# Sample events: "Receiver gains buff (stack) from Source"
# "Receiver's buff (stack) fades from Source"
def parse_event(e):
    if 'gains' in e:
        stk = re.search('\d+', e)
        if stk:
            stk = int(stk.group(0))
        else:
            stk = 1
        return '+', stk
    else:
        assert 'fades' in e
        return '-', 0 # <- unused

def parse_time(t):
    return datetime.strptime(t, '%H:%M:%S.%f')

def do_avg(rs):
    prev_t = parse_time('00:00:00.000')
    prev_stk = 0
    total_stk = 0

    def add_prev_to_total(t):
        nonlocal total_stk

        dt = (t - prev_t).total_seconds() * 1000
        print(t, prev_t, prev_stk, dt)
        total_stk += dt * prev_stk

    for i, r in enumerate(rs):
        t = parse_time(r['Time'])
        try:
            ty, stk = parse_event(r['Event'])
        except AssertionError:
            print(f'Error at {t} {i}')
            raise

        # Stack change: save the prev one.
        add_prev_to_total(t)

        # And record this event to be processed later
        prev_t = t
        if ty == '+':
            # Adding a new stack.
            prev_stk = stk
        else:
            assert ty == '-'
            # Removing one stack
            prev_stk -= 1

    # end = parse_time('00:05:06.000')
    # add_prev_to_total(end)
    end = prev_t

    start = parse_time('00:00:00.000')

    return total_stk / ((end - start).total_seconds() * 1000)

def main():
    # WCL CSV export
    with open('wv-h-nzoth.csv', newline='') as f:
        rs = list(csv.DictReader(f, delimiter=',', quotechar='"'))

    avg = do_avg(rs)
    print(avg)

main()
