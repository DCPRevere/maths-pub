#!/usr/bin/env python3
"""
Independent re-verification of a single point, straight from the definition.

Shares NO code with falsify_rankone.py: standard library only, sigma_k by naive
enumeration of (row set, column set, bijection), e_k by naive enumeration of
k-subsets, everything in exact rationals.  Slow on purpose.

Usage:
    python3 falsify_rankone_check.py n k "u1,u2,..." "v1,v2,..."
        checks A = u v^T / n   (u, v given as comma-separated rationals)
    python3 falsify_rankone_check.py --selftest
        runs the built-in spot checks
"""

import itertools
import sys
from fractions import Fraction as F


def sigma_k(A, n, k):
    """sum over all k-row-sets, all k-column-sets, all bijections."""
    t = F(0)
    for R in itertools.combinations(range(n), k):
        for Cc in itertools.combinations(range(n), k):
            for s in itertools.permutations(Cc):
                p = F(1)
                for i in range(k):
                    p *= A[R[i]][s[i]]
                t += p
    return t


def e_k(z, k):
    t = F(0)
    for S in itertools.combinations(range(len(z)), k):
        p = F(1)
        for i in S:
            p *= z[i]
        t += p
    return t


def C(n, k):
    t = 1
    for i in range(k):
        t = t * (n - i) // (i + 1)
    return t


def fac(k):
    t = 1
    for i in range(2, k + 1):
        t *= i
    return t


def check(n, k, u, v, verbose=True):
    A = [[u[i] * v[j] / n for j in range(n)] for i in range(n)]
    tot = sum(A[i][j] for i in range(n) for j in range(n))
    r = [sum(A[i][j] for j in range(n)) for i in range(n)]
    c = [sum(A[i][j] for i in range(n)) for j in range(n)]
    neg = [(i, j) for i in range(n) for j in range(n) if A[i][j] < 0]
    phi = (F(e_k(r, k), C(n, k)) + F(e_k(c, k), C(n, k))
           - F(sigma_k(A, n, k), C(n, k) ** 2))
    bound = F(2) - F(fac(k), n ** k)
    if verbose:
        print(f"n={n} k={k}")
        print(f"  sum of entries = {tot}  (must be {n}): "
              f"{'OK' if tot == n else 'NOT IN K_n'}")
        print(f"  negative entries: {len(neg)} "
              f"{'OK' if not neg else '-- NOT IN K_n'}")
        print(f"  Phi_k   = {phi}   = {float(phi):.15f}")
        print(f"  bound   = {bound} = {float(bound):.15f}")
        print(f"  ratio   = {phi / bound} = {float(phi / bound):.15f}")
        print(f"  VERDICT: {'*** EXCEEDS THE BOUND ***' if phi > bound else 'within the bound'}")
    return phi, bound


def parse(s):
    return [F(t) for t in s.split(",")]


def selftest():
    """Spot checks against values the scan reports."""
    print("--- barycentre must give exactly the bound ---")
    for n, k in [(6, 5), (7, 5), (9, 8)]:
        u = [F(1)] * n
        phi, bd = check(n, k, u, u)
        assert phi == bd, "barycentre is not tight"
        print()
    print("--- a two-value point ---")
    n, k = 8, 5
    u = [F(3, 2)] * 3 + [F(7, 10)] * 5
    assert sum(u) == n
    v = [F(1)] * n
    check(n, k, u, v)
    print()
    print("--- a boundary point with zeros ---")
    n, k = 7, 5
    u = [F(7, 3)] * 3 + [F(0)] * 4
    v = [F(1)] * n
    check(n, k, u, v)
    print()
    print("SELFTEST DONE")


if __name__ == "__main__":
    if len(sys.argv) == 2 and sys.argv[1] == "--selftest":
        selftest()
    elif len(sys.argv) == 5:
        n, k = int(sys.argv[1]), int(sys.argv[2])
        check(n, k, parse(sys.argv[3]), parse(sys.argv[4]))
    else:
        print(__doc__)
        sys.exit(2)
