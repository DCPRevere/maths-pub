#!/usr/bin/env python3
"""Sweep e = 13, 14 and produce the TARGET LIST: for every uncertified class,
which min-degree-3 core does it reduce to, and does that core carry a weight?

No Moebius mass above e = 10: the partition-pair loop is Theta(A_e^2) and
A_13 = 3 508 421, A_14 = 22 566 340, so 1.2e13 / 5.1e14 ordered pairs.  The
class counts and the core tally are what the target list needs.
"""
import sys
import time
import collections

import u5_canon as K
import u5_reduce as R
import u5_core3 as CO
from graded_verify_u5core3 import reduce_core


def core_of(key):
    c = [list(r) for r in key]
    U, V = len(c), len(c[0])
    es = []
    for u in range(U):
        for v in range(V):
            es += [(u, U + v)] * c[u][v]
    return reduce_core(U + V, es)


def classify(rv, res):
    simple = len(set(res)) == len(res) and all(a != b for a, b in res)
    if not simple or rv == 0:
        return ('not-simple', rv, len(res))
    deg = CO.degrees(rv, res)
    if min(deg) < 3:
        return ('has-leaf', rv, len(res), tuple(sorted(deg)))
    return ('core', rv, len(res), CO.canon(rv, tuple(sorted(set(res)))))


def main():
    for e in [int(x) for x in sys.argv[1:]] or [13, 14]:
        t = time.time()
        cd = K.classes_direct(e)
        te = time.time() - t
        t = time.time()
        bad = [k for k in cd
               if R.certify(*R.pattern_state([list(r) for r in k])) is None]
        tc = time.time() - t
        print(f'e={e}: {len(cd)} classes (enum {te:.0f}s, certify {tc:.0f}s), '
              f'{len(bad)} NOT certified', flush=True)
        tally = collections.Counter()
        for k in bad:
            rv, res = core_of(k)
            tally[classify(rv, res)] += 1
        for kk, n in tally.most_common():
            print(f'    x{n:5d}  {kk}', flush=True)
        # is K_5 among them?
        K5 = (5, tuple((a, b) for a in range(5) for b in range(a + 1, 5)))
        ck5 = CO.canon(*K5)
        hits = sum(n for kk, n in tally.items()
                   if kk[0] == 'core' and kk[3] == ck5)
        print(f'    K_5 core: {hits} classes', flush=True)


if __name__ == '__main__':
    main()
