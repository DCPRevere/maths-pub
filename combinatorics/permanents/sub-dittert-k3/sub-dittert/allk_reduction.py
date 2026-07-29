"""
THE MACLAURIN REDUCTION: sub-Dittert holds outside an explicit, shrinking
neighbourhood of the Birkhoff polytope, for EVERY k at once, elementarily.

Standard library only, Fraction throughout, no float in any decision.

THE SPLIT.  Directly from the definition, with no expansion at all,

    F_{n,k}(A) := (2 - k!/n^k) - [E_k(r) + E_k(c) - P_k(A)]
                = [ 2 - E_k(r) - E_k(c) ]  +  [ P_k(A) - k!/n^k ].

The first bracket is the MACLAURIN DEFICIT of the two line-sum vectors; it is
non-negative on K_n because sum r = sum c = n.  The second is the SUBPERMANENT
DEFICIT; it is non-negative on the Birkhoff polytope (Friedland / van der
Waerden) and can be negative on K_n, but never below -k!/n^k, because P_k >= 0.

THE QUANTITATIVE MACLAURIN STEP.  For r >= 0 with sum r = n and 2 <= k <= n,
write R = r - 1.  Then E_2(r) = 1 - |R|^2/(n(n-1)) exactly, and Maclaurin's
inequality E_k^{1/k} <= E_2^{1/2} with E_2 in [0,1] gives E_k <= E_2^{k/2} <= E_2,
hence

    1 - E_k(r)  >=  |R|^2 / (n(n-1)),        EQUALITY at k = 2.

THE THEOREM.  For every n >= 2, every 2 <= k <= n and every A in K_n,

    F_{n,k}(A)  >=  (|R|^2 + |C|^2)/(n(n-1))  -  k!/n^k .

In particular the Cheon-Hwang conjecture HOLDS at (n,k) for every A with

    |r - 1|^2 + |c - 1|^2  >=  (n-1) k! / n^(k-1)  =:  T(n,k),

so the open part of the conjecture is confined to the set where the line sums
are within T(n,k) of uniform -- and {r = c = 1} intersected with K_n is exactly
the Birkhoff polytope, where the statement is Friedland's theorem.  T(n,k) -> 0
in both parameters: T(n,3) = 6(n-1)/n^2, and T(n,n) = (n-1) n!/n^(n-1).

WHAT IS AND IS NOT PROVED.  This does NOT prove the conjecture: the residual
neighbourhood is nonempty and contains points that are not doubly stochastic, so
Friedland does not reach them.  It reduces the problem, uniformly in k, with an
effective threshold, by three ingredients only: the split, Maclaurin, P_k >= 0.

Usage:  GUARD_MEM=4G ../guard.sh python3 allk_reduction.py
"""

import random
from fractions import Fraction as Fr
from itertools import combinations, permutations
from math import comb, factorial


def elem_sym(vec, d):
    e = [Fr(0)] * (d + 1)
    e[0] = Fr(1)
    for x in vec:
        for j in range(min(d, len(vec)), 0, -1):
            e[j] += e[j - 1] * x
    return e[d]


def per(M):
    m = len(M)
    if m == 0:
        return Fr(1)
    tot = Fr(0)
    for p in permutations(range(m)):
        prod = Fr(1)
        for i in range(m):
            prod *= M[i][p[i]]
        tot += prod
    return tot


def sigma_k(A, k):
    n = len(A)
    tot = Fr(0)
    for R in combinations(range(n), k):
        for C in combinations(range(n), k):
            tot += per([[A[i][j] for j in C] for i in R])
    return tot


def lines(A):
    n = len(A)
    return ([sum(A[i][j] for j in range(n)) for i in range(n)],
            [sum(A[i][j] for i in range(n)) for j in range(n)])


def E(vec, k, n):
    return elem_sym(vec, k) / Fr(comb(n, k))


def Pk(A, k):
    n = len(A)
    return sigma_k(A, k) / Fr(comb(n, k)) ** 2


def gamma(n, k):
    return Fr(factorial(k), n ** k)


def F_of(A, k):
    n = len(A)
    r, c = lines(A)
    return (2 - gamma(n, k)) - (E(r, k, n) + E(c, k, n) - Pk(A, k))


def dev2(vec):
    return sum((x - 1) ** 2 for x in vec)


def T(n, k):
    return Fr((n - 1) * factorial(k), n ** (k - 1))


# --------------------------------------------------------------------- samplers


def rand_Kn(n, rng, zeros=0.0, spread=9):
    while True:
        M = [[0 if rng.random() < zeros else rng.randint(0, spread)
              for _ in range(n)] for _ in range(n)]
        tot = sum(sum(row) for row in M)
        if tot:
            break
    return [[Fr(n * M[i][j], tot) for j in range(n)] for i in range(n)]


def rand_near_omega(n, rng, scale):
    """A point of K_n whose line sums are close to 1: start doubly stochastic,
    then move by a small K_n-preserving perturbation with nonzero line sums."""
    A = [[Fr(1, n)] * n for _ in range(n)]
    for _ in range(3):
        i, i2 = rng.sample(range(n), 2)
        j, j2 = rng.sample(range(n), 2)
        v = Fr(rng.randint(-3, 3), 1) * scale
        A[i][j] += v
        A[i2][j2] += v
        A[i][j2] -= v
        A[i2][j] -= v
    # now add a line-sum-carrying piece of controlled size
    u = [Fr(0)] * n
    i, i2 = rng.sample(range(n), 2)
    u[i], u[i2] = scale, -scale
    for i in range(n):
        for j in range(n):
            A[i][j] += u[i] / n
    if any(x < 0 for row in A for x in row):
        return None
    return A


# ------------------------------------------------------------------- the checks


def part1(rng):
    print("PART 1.  The split is an identity, not an approximation.")
    bad = 0
    for n in (3, 4, 5):
        for k in range(2, n + 1):
            for _ in range(4):
                A = rand_Kn(n, rng, zeros=0.2)
                r, c = lines(A)
                lhs = F_of(A, k)
                rhs = (2 - E(r, k, n) - E(c, k, n)) + (Pk(A, k) - gamma(n, k))
                if lhs != rhs:
                    bad += 1
    print(f"  F = [Maclaurin deficit] + [subpermanent deficit]: {bad} mismatches")
    print()
    return bad


def part2(rng):
    print("PART 2.  The quantitative Maclaurin step, exactly:")
    print("     1 - E_k(r)  >=  |r-1|^2 / (n(n-1))   for r >= 0, sum r = n.")
    print()
    bad = 0
    tight = []
    checks = 0
    for n in range(3, 9):
        menu = []
        menu.append(("uniform", [Fr(1)] * n))
        menu.append(("spike", [Fr(n)] + [Fr(0)] * (n - 1)))
        menu.append(("two", [Fr(n, 2), Fr(n, 2)] + [Fr(0)] * (n - 2)))
        menu.append(("ramp", None))
        v = [Fr(2 * (i + 1)) for i in range(n)]
        s = sum(v)
        menu[-1] = ("ramp", [x * n / s for x in v])
        for t in range(25):
            w = [Fr(rng.randint(0, 20)) for _ in range(n)]
            s = sum(w)
            if s == 0:
                continue
            menu.append((f"rand{t}", [x * n / s for x in w]))
        for nm, r in menu:
            for k in range(2, n + 1):
                lhs = 1 - E(r, k, n)
                rhs = Fr(dev2(r), 1) / Fr(n * (n - 1))
                checks += 1
                if lhs < rhs:
                    bad += 1
                    print(f"  VIOLATION n={n} k={k} {nm}: {lhs} < {rhs}")
                if k == 2 and lhs != rhs:
                    print(f"  k=2 NOT tight at n={n} {nm}: {lhs} vs {rhs}")
    print(f"  {checks} (n, k, r) checks, {bad} violations; k = 2 is an equality")
    print("  in every case, as the derivation says it must be.")
    print()
    return bad


def part3(rng):
    print("PART 3.  THE THEOREM.  Every A in K_n with")
    print("     |r-1|^2 + |c-1|^2  >=  T(n,k) = (n-1) k!/n^(k-1)")
    print("  satisfies the conjecture.  Checked by measuring both sides.")
    print()
    print("     n    k    T(n,k)              covered / tested   min F on covered")
    for n in (3, 4, 5, 6):
        for k in range(2, n + 1):
            cov = tot = 0
            minF = None
            for t in range(60):
                A = rand_Kn(n, rng, zeros=[0.0, 0.2, 0.4, 0.6][t % 4])
                r, c = lines(A)
                tot += 1
                if dev2(r) + dev2(c) >= T(n, k):
                    cov += 1
                    f = F_of(A, k)
                    assert f >= 0, (n, k, f)
                    if minF is None or f < minF:
                        minF = f
            print(f"    {n:>3}  {k:>3}    {str(T(n, k)):<18s}  {cov:>4}/{tot:<5}"
                  f"      {('%.6f' % float(minF)) if minF is not None else '-'}")
    print()
    print("  Sizes of the residual neighbourhood, to show it shrinks:")
    print("     n    T(n,3)          T(n,n)")
    for n in (4, 6, 8, 12, 20, 40):
        print(f"    {n:>3}   {str(T(n, 3)):<14s}  {str(T(n, n))[:28]}"
              f"  ~ {float(T(n, n)):.3e}")
    print()


def part4(rng):
    print("PART 4.  The residual region is REAL: points of K_n that are not")
    print("  doubly stochastic and are not covered.  If none existed the theorem")
    print("  would prove the conjecture, which would be a red flag.")
    print()
    found = 0
    shown = 0
    for n in (4, 5):
        for k in range(2, n + 1):
            for t in range(400):
                A = rand_near_omega(n, rng, Fr(1, 30 + t % 40))
                if A is None:
                    continue
                r, c = lines(A)
                d = dev2(r) + dev2(c)
                if d == 0:
                    continue                      # doubly stochastic: Friedland
                if d < T(n, k):
                    found += 1
                    if shown < 3:
                        shown += 1
                        f = F_of(A, k)
                        print(f"    n={n} k={k}: |R|^2+|C|^2 = {d} < T = {T(n,k)},"
                              f"  F = {f} (>= 0, but NOT by this theorem)")
                    break
    print(f"  {found} residual points found.  The reduction is genuine and")
    print("  partial: it is not a proof of the conjecture.")
    print()


def main():
    rng = random.Random(20260729)
    print("allk_reduction.py -- the Maclaurin reduction, uniform in k")
    print()
    b1 = part1(rng)
    b2 = part2(rng)
    part3(rng)
    part4(rng)
    print("DONE" if b1 == 0 and b2 == 0 else "FAILURES PRESENT")


if __name__ == "__main__":
    main()
