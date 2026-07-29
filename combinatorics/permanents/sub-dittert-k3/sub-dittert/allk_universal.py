"""
THE UNIVERSAL FORM of the sub-Dittert objective, and what it forces.

Standard library only, Fraction throughout, no float in any decision.  Nothing
here is fitted: every claim is derived first and then checked exactly.

THE CLAIM.  Write A = J_n/n + b, R_i = sum_j b_ij, C_j = sum_i b_ij, and

    s_d(n,k) = [k]_d / [n]_d                    (falling factorials)
    t_d(n,k) = s_d(n,k)^2 * (k-d)! / n^(k-d)

Then, IDENTICALLY as polynomials in b, for every 1 <= k <= n,

    F_{n,k}(b) := (2 - k!/n^k) - [E_k(r) + E_k(c) - P_k(A)]
                = sum_{d=1}^{k} [ t_d sigma_d(b) - s_d (e_d(R) + e_d(C)) ].

This is one identity from which the four scattered "already-uniform" facts all
drop out, and it is the reason a uniform-in-(n,k) certificate structure can be
written down at all:

  * the coefficient of a degree-d monomial is  -s_d  (distinct rows XOR distinct
    columns),  -2 s_d + t_d  (a partial permutation),  0 otherwise -- three
    numbers per degree, whatever k is;
  * d = 1 gives grad F(0) = (-2k/n + k*k!/n^(k+1)) * 1, the criticality fact;
  * d = 2 gives the tangent Hessian with alpha = s_2 = k(k-1)/(n(n-1)) and
    beta = t_2 = alpha^2 (k-2)!/n^(k-2), i.e. allk_hessian.py's two eigenvalues;
  * the constant term cancels EXACTLY, which is L1(e) of paper_l: the degree-0
    row of the certificate system is consistent iff F(centre) = 0.

PART 3 then settles the shape of the certificate programme.  With a common Gram
basis of degree e, deg(b_p sigma_p) = 2e+1, so 2e+1 >= k forces

    e(k) = ceil((k-1)/2),      D(k) = 2e+1,

and MIXED degrees (sigma_0 at k/2, multipliers at k/2 - 1) are impossible for
even k because the top form of F would have to be a sum of squares on the
hyperplane and it is not -- witness produced, not asserted.  Since the
programme's row and column counts depend on (e, D) alone and not on k, the
programme SHAPE is constant on the bands {2,3}, {4,5}, {6,7}, ...

Usage:  GUARD_MEM=4G ../guard.sh python3 allk_universal.py
"""

import random
from fractions import Fraction as Fr
from itertools import combinations, permutations
from math import comb, factorial

# ----------------------------------------------------------------- primitives


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


def sigma_d(A, d):
    """Sum of all d x d subpermanents.  sigma_0 = 1."""
    n = len(A)
    if d == 0:
        return Fr(1)
    if d > n:
        return Fr(0)
    tot = Fr(0)
    for R in combinations(range(n), d):
        for C in combinations(range(n), d):
            tot += per([[A[i][j] for j in C] for i in R])
    return tot


def lines(M):
    n = len(M)
    return ([sum(M[i][j] for j in range(n)) for i in range(n)],
            [sum(M[i][j] for i in range(n)) for j in range(n)])


def Phi(A, k):
    n = len(A)
    N = Fr(comb(n, k))
    r, c = lines(A)
    return elem_sym(r, k) / N + elem_sym(c, k) / N - sigma_d(A, k) / (N * N)


def gamma(n, k):
    return Fr(factorial(k), n ** k)


def F_direct(b, k):
    """F by its definition, from the 1992 functional."""
    n = len(b)
    A = [[Fr(1, n) + b[i][j] for j in range(n)] for i in range(n)]
    return (2 - gamma(n, k)) - Phi(A, k)


# ------------------------------------------------------------ the universal law


def falling(x, d):
    out = Fr(1)
    for i in range(d):
        out *= (x - i)
    return out


def s_coef(n, k, d):
    return falling(Fr(k), d) / falling(Fr(n), d)


def t_coef(n, k, d):
    if d > k:
        return Fr(0)
    return s_coef(n, k, d) ** 2 * Fr(factorial(k - d), n ** (k - d))


def F_universal(b, k):
    """F by the claimed universal form."""
    n = len(b)
    R, C = lines(b)
    tot = Fr(0)
    for d in range(1, k + 1):
        tot += t_coef(n, k, d) * sigma_d(b, d)
        tot -= s_coef(n, k, d) * (elem_sym(R, d) + elem_sym(C, d))
    return tot


def coef_rule(n, k, cells):
    """The claimed coefficient of the monomial prod_{cells} b, cells a multiset."""
    d = len(cells)
    if d == 0 or d > k:
        return Fr(0)
    dr = len({r for r, _ in cells}) == d
    dc = len({c for _, c in cells}) == d
    out = Fr(0)
    if dr:
        out -= s_coef(n, k, d)
    if dc:
        out -= s_coef(n, k, d)
    if dr and dc:
        out += t_coef(n, k, d)
    return out


# ------------------------------------------------------------------- test data


def rand_b(n, rng, spread=7, denom=5):
    return [[Fr(rng.randint(-spread, spread), rng.randint(1, denom))
             for _ in range(n)] for _ in range(n)]


def doubly_centred(n, rng, spread=4):
    """A random integer matrix with every row and column sum zero."""
    M = [[Fr(0)] * n for _ in range(n)]
    for _ in range(3 * n):
        i, i2 = rng.sample(range(n), 2)
        j, j2 = rng.sample(range(n), 2)
        v = Fr(rng.randint(-spread, spread))
        M[i][j] += v
        M[i2][j2] += v
        M[i][j2] -= v
        M[i2][j] -= v
    return M


# -------------------------------------------------------------------- PART 1


def part1(rng):
    print("PART 1.  F by definition  ==  the universal form,  identically in b.")
    print("  Random rational b, NOT restricted to the hyperplane sum b = 0, so")
    print("  this tests the polynomial identity and not merely its restriction.")
    print()
    bad = 0
    checks = 0
    for n in range(3, 7):
        for k in range(1, n + 1):
            if n == 6 and k >= 5:
                continue
            for _ in range(3):
                b = rand_b(n, rng)
                a = F_direct(b, k)
                u = F_universal(b, k)
                checks += 1
                if a != u:
                    bad += 1
                    print(f"  n={n} k={k} MISMATCH  direct {a}  universal {u}")
    print(f"  {checks} (n, k, b) checks, {bad} mismatches.")
    print()

    print("  and the three-class coefficient rule, monomial by monomial:")
    bad2 = 0
    checks2 = 0
    for n in (4, 5):
        for k in range(2, n + 1):
            # extract the coefficient of a monomial by finite differences on a
            # basis-free route: evaluate F on a formal grid is expensive, so
            # instead compare F_universal's expansion against coef_rule using
            # the multilinear part -- for squarefree monomials the coefficient is
            # recovered by inclusion-exclusion over the chosen cells.
            cellset = [(0, 0), (0, 1), (1, 0), (1, 1), (2, 2), (1, 2)]
            for d in range(1, min(k, 4) + 1):
                for cells in combinations(cellset, d):
                    got = _multilinear_coef(n, k, cells)
                    want = coef_rule(n, k, cells)
                    checks2 += 1
                    if got != want:
                        bad2 += 1
                        if bad2 <= 4:
                            print(f"  n={n} k={k} cells={cells}: "
                                  f"direct {got} rule {want}")
    print(f"  {checks2} squarefree monomial coefficients, {bad2} mismatches.")
    print()
    return bad + bad2


def _multilinear_coef(n, k, cells):
    """Coefficient of the squarefree monomial prod_{cells} b, by inclusion-
    exclusion on F_direct: sum over subsets S of cells of (-1)^{|cells|-|S|}
    F(indicator of S)."""
    d = len(cells)
    tot = Fr(0)
    for r in range(d + 1):
        for S in combinations(range(d), r):
            b = [[Fr(0)] * n for _ in range(n)]
            for idx in S:
                i, j = cells[idx]
                b[i][j] = Fr(1)
            tot += Fr((-1) ** (d - r)) * F_direct(b, k)
    return tot


# -------------------------------------------------------------------- PART 2


def part2():
    print("PART 2.  The four already-uniform facts, as corollaries of PART 1.")
    print()
    print("  (a) grad F(0) = (-2 s_1 + t_1) * 1  =  (-2k/n + k*k!/n^(k+1)) * 1.")
    for n, k in ((4, 3), (5, 3), (5, 4), (6, 4)):
        g = -2 * s_coef(n, k, 1) + t_coef(n, k, 1)
        alt = Fr(-2 * k, n) + Fr(k * factorial(k), n ** (k + 1))
        assert g == alt
        print(f"      n={n} k={k}:  {g}")
    assert -2 * s_coef(4, 3, 1) + t_coef(4, 3, 1) == Fr(-183, 128)
    print("      (4,3) gives -183/128, the recorded gradient of NOTES section 4. [V]")
    print()

    print("  (b) the tangent Hessian: alpha = s_2 = k(k-1)/(n(n-1)),")
    print("      beta = t_2 = alpha^2 (k-2)!/n^(k-2)  -- allk_hessian.py's two")
    print("      eigenvalues, now DERIVED rather than separately verified.")
    for n in range(3, 9):
        for k in range(2, n + 1):
            assert s_coef(n, k, 2) == Fr(k * (k - 1), n * (n - 1))
            assert t_coef(n, k, 2) == (Fr(k * (k - 1), n * (n - 1)) ** 2
                                       * Fr(factorial(k - 2), n ** (k - 2)))
    print("      identity checked for 3 <= n <= 8, 2 <= k <= n.  [V]")
    print()

    print("  (c) the constant term cancels: no d = 0 term appears, which is")
    print("      L1(e) of paper_l -- the degree-0 row of the certificate system")
    print("      is identically zero and consistent iff F(centre) = 0.")
    for n in range(3, 8):
        for k in range(1, n + 1):
            z = [[Fr(0)] * n for _ in range(n)]
            assert F_direct(z, k) == 0 and F_universal(z, k) == 0
    print("      F(0) = 0 by both routes, 3 <= n <= 7, all k.  [V]")
    print()

    print("  (d) s_d = [k]_d/[n]_d vanishes for d > k, so ONE formula covers")
    print("      every k and truncates itself; and 0 < s_d <= 1, 0 < t_d for")
    print("      1 <= d <= k <= n.")
    for n in range(3, 12):
        for k in range(2, n + 1):
            for d in range(1, k + 1):
                assert 0 < s_coef(n, k, d) <= 1
                assert t_coef(n, k, d) > 0
            if k < n:                       # [n]_d itself vanishes once d > n
                assert s_coef(n, k, k + 1) == 0
    print("      checked for 3 <= n <= 11; the truncation s_{k+1} = 0 is checked")
    print("      for k < n, the only range where [n]_{k+1} is nonzero.  [V]")
    print()


# -------------------------------------------------------------------- PART 3


def part3(rng):
    print("PART 3.  The Gram degree is FORCED, and the programme shape depends")
    print("  on k only through e = ceil((k-1)/2).")
    print()
    print("  (i) A common Gram basis of degree e gives deg(b_p sigma_p) = 2e+1,")
    print("      so 2e+1 >= deg F = k.  Hence e >= (k-1)/2.")
    print()
    print("  (ii) MIXED degrees are ruled out for even k.  If sigma_0 had basis")
    print("      degree k/2 and the multipliers k/2 - 1, the degree-k part of the")
    print("      identity would read  F_k = (sigma_0)_k + lambda_{k-1} * h,  so on")
    print("      the hyperplane h = 0 the top form F_k would be a sum of squares,")
    print("      hence >= 0.  It is not.  F_k(b) = s_k [ s_k sigma_k(b) - e_k(R)")
    print("      - e_k(C) ], so a doubly centred b with sigma_k(b) < 0 kills it.")
    print()
    found = {}
    for n in (4, 5, 6):
        for k in (4, 6):
            if k > n:
                continue
            for _ in range(4000):
                b = doubly_centred(n, rng)
                R, C = lines(b)
                assert all(x == 0 for x in R) and all(x == 0 for x in C)
                sk = sigma_d(b, k)
                if sk < 0:
                    top = s_coef(n, k, k) * (s_coef(n, k, k) * sk
                                             - elem_sym(R, k) - elem_sym(C, k))
                    assert top < 0
                    found[(n, k)] = (b, sk, top)
                    break
    for (n, k), (b, sk, top) in sorted(found.items()):
        print(f"      n={n} k={k}:  sigma_{k}(b) = {sk},  F_{k}(b) = {top} < 0")
        print("        b =")
        for row in b:
            print("          " + " ".join(f"{str(x):>5s}" for x in row))
    if not found:
        print("      NO WITNESS FOUND -- the forcing argument is NOT established.")
    print()
    print("  (iii) Consequently  e(k) = ceil((k-1)/2)  and  D(k) = 2e+1, and the")
    print("      programme's row/column counts -- rows = orbits of monomials of")
    print("      degree <= D, lambda = orbits of degree <= D-1, sigma_0 and")
    print("      sigma_11 = orbits of pairs of basis monomials of degree <= e --")
    print("      mention k NOWHERE.  So the shape is constant on the BANDS:")
    print()
    print("        k    e   D    band")
    for k in range(2, 12):
        e = (k - 1 + 1) // 2 if k % 2 == 0 else (k - 1) // 2
        e = -(-(k - 1) // 2)
        D = 2 * e + 1
        band = "{%d,%d}" % (2 * e, 2 * e + 1)
        print(f"        {k:<4} {e}   {D}    {band}")
    print()
    print("  RECORDED SHAPES, to be reproduced exactly:")
    print("      k = 3 (e=1, D=3):  rows 12, sigma_0 3, sigma_11 11, lambda 5,")
    print("                         unknowns 19          [NOTES 6a.4]")
    print("      k = 4 (e=2, D=5):  rows 87, sigma_0 51, sigma_11 356, lambda 33,")
    print("                         unknowns 440         [NOTES 6b.2]")
    print("  PREDICTION, before any k = 5 measurement exists:")
    print("      k = 5 (e=2, D=5):  rows 87, sigma_0 51, sigma_11 356, lambda 33,")
    print("                         unknowns 440 -- IDENTICAL to k = 4, and the")
    print("      eleven sigma_11 blocks are the same eleven, multiplicities")
    print("      16,14,10,7,4,4,3,2,1,1,1.  Only the right-hand side moves.")
    print()


def main():
    rng = random.Random(20260729)
    print("allk_universal.py -- the universal form of F, and what it forces")
    print()
    bad = part1(rng)
    part2()
    part3(rng)
    print("DONE" if bad == 0 else "PART 1 FAILURES PRESENT -- everything below is void")


if __name__ == "__main__":
    main()
