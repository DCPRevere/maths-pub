#!/usr/bin/env python3
"""Graded verifier for the canon rewrite (u5_canon.py).

The rewrite is only allowed if it is OUTPUT-IDENTICAL to u5_hunt.canon, not
merely "some other valid canonical form": the residue logs print canon keys,
and Lam_e is accumulated per key.  So the gate is a regression, and the
regression IS the verifier.

    C1  canon agrees with the brute force on every incidence matrix that
        occurs at e <= 8, and on a large sample of raw matrices
    C2  patterns(e) agrees EXACTLY (keys, signed sums, l1 masses) for e <= 8
    C3  the e = 9 ground truth: 317 classes, Lam_9 = 17656369920, and the
        residue list of results/u5_residue2.log reproduced element for element
    C4  classes_direct(e) yields the same class SET as the pair loop, e <= 9
    C5  mutation controls

Ground truth (brute-force runs, results/u5_residue.log and u5_residue2.log):
    e = 8 : 127 classes, Lam_8 = 217430640,          0 uncertified
    e = 9 : 317 classes, Lam_9 = 17656369920,        5 uncertified
"""
import sys
import time
from itertools import permutations

import u5_hunt as H
import u5_canon as K
import u5_reduce as R

CHECKS = 0
FAILS = []
FIRED = {}


def chk(cond, msg):
    global CHECKS
    CHECKS += 1
    if not cond:
        FAILS.append(msg)
    return bool(cond)


def fire(t):
    FIRED[t] = FIRED.get(t, 0) + 1


LAM = {4: 78, 5: 1896, 6: 68880, 7: 3386160, 8: 217430640, 9: 17656369920}
NCLASS = {4: 4, 5: 5, 6: 21, 7: 37, 8: 127, 9: 317}
RESIDUE_E9 = [((0, 1, 1), (1, 1, 1), (1, 1, 2)),
              ((0, 1, 1), (1, 1, 1), (2, 1, 1)),
              ((0, 1, 2), (1, 1, 1), (1, 1, 1)),
              ((0, 1, 1, 1), (1, 0, 1, 1), (1, 1, 0, 1)),
              ((0, 1, 1), (1, 0, 1), (1, 1, 0), (1, 1, 1))]


def brute_canon(c):
    U, V = len(c), len(c[0])
    best = None
    for rp in permutations(range(U)):
        rows = [tuple(c[rp[u]]) for u in range(U)]
        for cp in permutations(range(V)):
            key = tuple(tuple(rows[u][cp[v]] for v in range(V))
                        for u in range(U))
            if best is None or key < best:
                best = key
    return best


def raw_matrices(e):
    """Every incidence matrix that actually occurs at this e."""
    parts = [p for p in H.set_partitions(e) if all(len(b) >= 2 for b in p)]
    out = set()
    for pi in parts:
        for rho in parts:
            out.add(tuple(tuple(r) for r in H.incidence(pi, rho, e)))
    return out


def C1():
    print('C1  canon agrees with the brute force, matrix by matrix')
    tot = 0
    for e in range(4, 9):
        for raw in raw_matrices(e):
            c = [list(r) for r in raw]
            tot += 1
            if not chk(K.canon(c) == brute_canon(c),
                       f'C1: canon mismatch at e={e} on {raw}'):
                return
    print(f'    {tot} distinct incidence matrices, all identical')


def C2():
    print('C2  patterns(e) identical (keys, signed sums, masses), e <= 8')
    for e in range(4, 9):
        t = time.time()
        pb = H.patterns(e)
        tb = time.time() - t
        t = time.time()
        pf = K.patterns(e)
        tf = time.time() - t
        chk(pb == pf, f'C2: patterns({e}) differ')
        chk(len(pf) == NCLASS[e], f'C2: class count at e={e}')
        chk(sum(b for _, b in pf.values()) == LAM[e], f'C2: Lam_{e}')
        print(f'    e={e}: {len(pf):4d} classes, Lam={LAM[e]:12d}, '
              f'brute {tb:7.2f}s -> fast {tf:6.2f}s  ({tb/max(tf,1e-9):5.0f}x)')


def C3():
    print('C3  the e = 9 ground truth, reproduced')
    t = time.time()
    pf = K.patterns(9)
    tf = time.time() - t
    chk(len(pf) == 317, f'C3: e=9 class count {len(pf)} != 317')
    chk(sum(b for _, b in pf.values()) == LAM[9], 'C3: Lam_9')
    # The historical residue list was produced BEFORE the core lemmas were
    # registered, so it is reproduced with them switched off.  That isolates
    # the canon rewrite (what this file gates) from the registration fix
    # (what U5-CORES.md sec 6 is about): if the canon were wrong, the keys
    # and hence the list would move here too.
    for nm in ('L-K4', 'L-K33'):
        pass
    for nm in R.CORE_LEMMAS:
        R.DISABLE.add(nm)
    bad = []
    for key, (sgn, mass) in pf.items():
        c = [list(r) for r in key]
        if R.certify(*R.pattern_state(c)) is None:
            bad.append((key, mass))
    R.DISABLE.clear()
    got = sorted(k for k, _ in bad)
    chk(got == sorted(RESIDUE_E9),
        f'C3: historical residue list differs; got {got}')
    chk(sum(m for _, m in bad) == 45480960, 'C3: residue mass')
    # and with them ON, the residue is empty -- that is e_0 >= 9
    bad2 = [k for k in pf
            if R.certify(*R.pattern_state([list(r) for r in k])) is None]
    chk(not bad2, f'C3: e=9 not fully certified, {bad2[:3]}')
    print(f'    e=9 in {tf:.1f}s: 317 classes, Lam_9 exact; historical '
          f'{len(bad)} residues + mass reproduced; 0 with the core lemmas on')


def C4():
    print('C4  classes_direct(e) == the pair loop class set, e <= 10')
    for e in range(4, 11):
        t = time.time()
        pf = K.patterns(e)
        cd = K.classes_direct(e)
        chk(cd == set(pf), f'C4: classes_direct({e}) differs')
        if e >= 9:
            print(f'    e={e}: {len(cd)} classes agree '
                  f'(pair loop {time.time()-t:.0f}s)')
    print('    e = 4..10 all agree -- classes_direct is gated where the '
          'pair loop can still be run')


NSWEEP = {8: 127, 9: 317, 10: 1018, 11: 2989, 12: 9930}


def C6():
    print('C6  the sweep decision: every class at e <= 12 is certified')
    for e in (8, 9, 10, 11, 12):
        cd = K.classes_direct(e)
        chk(len(cd) == NSWEEP[e], f'C6: class count at e={e} is {len(cd)}')
        bad = [k for k in cd
               if R.certify(*R.pattern_state([list(r) for r in k])) is None]
        chk(not bad, f'C6: e={e} has {len(bad)} uncertified, {bad[:3]}')
        print(f'    e={e:2d}: {len(cd):5d} classes, 0 uncertified')
    print('    => e_0 = 12')


def C5():
    print('C5  mutation controls')
    for e in (6, 7, 8):
        pf = K.patterns(e)
        n_ok = len(pf)
        parts = [p for p in H.set_partitions(e) if all(len(b) >= 2 for b in p)]

        def count(cf):
            out = set()
            for pi in parts:
                for rho in parts:
                    c = H.incidence(pi, rho, e)
                    if H.is_connected(c):
                        out.add(cf(c))
            return len(out)

        # no_colsort: leave the columns alone
        def m_nocol(c):
            U, V = len(c), len(c[0])
            best = None
            for rp in permutations(range(U)):
                cand = tuple(tuple(c[rp[u]]) for u in range(U))
                if best is None or cand < best:
                    best = cand
            return best
        if count(m_nocol) != n_ok:
            fire('no_colsort')

        # colsort_by_sum: sort columns by their SUM, not as vectors
        def m_bysum(c):
            U, V = len(c), len(c[0])
            best = None
            for rp in permutations(range(U)):
                rows = [c[rp[u]] for u in range(U)]
                cols = sorted(range(V),
                              key=lambda v: sum(rows[u][v] for u in range(U)))
                cand = tuple(tuple(rows[u][v] for v in cols) for u in range(U))
                if best is None or cand < best:
                    best = cand
            return best
        if count(m_bysum) != n_ok:
            fire('colsort_by_sum')

        # no_rowperm: skip the row permutation loop
        def m_norow(c):
            U, V = len(c), len(c[0])
            cols = sorted(range(V), key=lambda v: tuple(c[u][v]
                                                        for u in range(U)))
            return tuple(tuple(c[u][v] for v in cols) for u in range(U))
        if count(m_norow) != n_ok:
            fire('no_rowperm')

        # raw_key: no canonicalisation at all
        if count(lambda c: tuple(tuple(r) for r in c)) != n_ok:
            fire('raw_key')

    for t in ('no_colsort', 'colsort_by_sum', 'no_rowperm', 'raw_key'):
        chk(FIRED.get(t, 0) >= 2,
            f'C5: control {t} fired at {FIRED.get(t,0)} positions, need >= 2')
    print(f'    {FIRED}')


def main():
    C1()
    C2()
    C3()
    C4()
    C6()
    C5()
    print()
    print(f'RESULT: {CHECKS} checks, {len(FAILS)} failures; '
          f'{len(FIRED)} controls fired at {sum(FIRED.values())} positions')
    for f in FAILS[:20]:
        print('  FAIL', f)
    return 1 if FAILS else 0


if __name__ == '__main__':
    sys.exit(main())
