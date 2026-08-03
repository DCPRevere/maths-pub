#!/usr/bin/env python3
"""Exact probe of the two predicted core bounds (NOTES sec 39 P1-P4)."""
from fractions import Fraction as F
from itertools import permutations
import random
import u5_core3 as C

# --------------------------------------------------------------- witnesses


def perm_matrix(p, n):
    return [[F(1) if p[i] == j else F(0) for j in range(n)] for i in range(n)]


def random_ds(n, k, rng):
    """Exact doubly stochastic: rational convex combination of permutations."""
    perms = [tuple(rng.sample(range(n), n)) for _ in range(k)]
    w = [F(rng.randint(1, 9)) for _ in range(k)]
    s = sum(w)
    w = [x / s for x in w]
    A = [[F(0)] * n for _ in range(n)]
    for wt, p in zip(w, perms):
        for i in range(n):
            A[i][p[i]] += wt
    return A


def in_omega(A, n):
    if any(A[i][j] < 0 for i in range(n) for j in range(n)):
        return False
    if any(sum(A[i]) != 1 for i in range(n)):
        return False
    if any(sum(A[i][j] for i in range(n)) != 1 for j in range(n)):
        return False
    return True


# ----------------------------------------------------------------- patterns

# subdivided prism, e = 11: the FIRST 3-connected core (P5)
PRISM_PAT = (8, [(0, 1), (1, 2), (0, 6), (6, 2), (3, 4), (4, 5), (3, 7),
                 (7, 5), (0, 3), (1, 4), (2, 5)])
PRISM_CORE = (6, [(0, 1), (1, 2), (0, 2), (3, 4), (4, 5), (3, 5),
                  (0, 3), (1, 4), (2, 5)])
Q3 = (8, [(i, 4 + j) for i in range(4) for j in range(4) if i != j])
K34 = (7, [(i, 3 + j) for i in range(3) for j in range(4)])
K33 = (6, [(i, 3 + j) for i in range(3) for j in range(3)])
C6 = (6, [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 0)])

PATS = {'prism-pattern(e=11)': (PRISM_PAT, 3),
        'Q3(e=12)': (Q3, 4),
        'K34(e=12)': (K34, 5),
        'K33(e=9)': (K33, 2),
        'C6(cycle,e=6)': (C6, 0)}


def report(n, A, tag):
    B = C.bmat(A, n)
    Q = C.frob2(B, n)
    beta = F(n - 1, n)
    out = []
    for name, ((v, es), c) in PATS.items():
        S = C.invariant(v, es, [B] * len(es), n)
        ok = abs(S) <= beta ** c * Q
        okQ = abs(S) <= Q
        out.append((name, S, Q, c, ok, okQ, F(abs(S), 1) / Q if Q else 0))
    print(f'--- {tag}  n={n}  Q={Q} ({float(Q):.4f})')
    for (name, S, Q, c, ok, okQ, r) in out:
        print(f'  {name:22s} S={float(S):+12.6f}  |S|/Q={float(r):.6f}  '
              f'<=beta^{c}Q: {ok}   <=Q: {okQ}')
    return out


if __name__ == '__main__':
    import sys
    rng = random.Random(20260803)
    n = 5
    # the permutation-matrix vertex
    idp = list(range(n))
    report(n, perm_matrix(idp, n), 'B = P - J/n (identity)')
    for t in range(3):
        A = random_ds(n, 4, rng)
        assert in_omega(A, n)
        report(n, A, f'random DS #{t}')
    # P4: the asymptotic ratio at the permutation matrix
    print('\nP4: |S_G|/Q at B = P - J/n, P = I, as n grows')
    print('%-4s %-14s %-14s %-14s %-14s' % ('n', 'C6', 'K33', 'Q3', 'prism-pat'))
    for n in (5, 6, 7, 8, 10, 12):
        B = C.bmat(perm_matrix(list(range(n)), n), n)
        Q = C.frob2(B, n)
        row = []
        for key in ('C6(cycle,e=6)', 'K33(e=9)', 'Q3(e=12)',
                    'prism-pattern(e=11)'):
            (v, es), c = PATS[key]
            S = C.invariant(v, es, [B] * len(es), n)
            row.append(float(F(abs(S)) / Q))
        print('%-4d %-14.9f %-14.9f %-14.9f %-14.9f' % (n, *row))
