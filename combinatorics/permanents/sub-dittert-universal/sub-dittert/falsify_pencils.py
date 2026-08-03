#!/usr/bin/env python3
"""
Falsification scan for the Cheon-Hwang sub-Dittert conjecture on

    K_n = { A >= 0 entrywise, sum_ij A_ij = n },

    Phi_k(A) = E_k(r) + E_k(c) - P_k(A)  <=  2 - k!/n^k =: M(n,k),

    E_k(v) = e_k(v)/C(n,k),   P_k(A) = sigma_k(A)/C(n,k)^2,
    sigma_k(A) = sum over k-subsets alpha, beta of per(A[alpha,beta]).

Scope of this scan: 5 <= k < n, n <= 12.  Two searches.

  (1) PENCILS.  A(t) = J_n/n + t (B - J_n/n) for B in K_n.  Both J_n/n and B
      have entry sum n, so every A(t) has entry sum n: no rescaling is needed,
      the pencil is affine inside the sum-n hyperplane.  Nonnegativity is the
      only constraint, giving the admissible interval

        t in [ t-, t+ ],  t- = max over d_ij>0 of -1/(n d_ij),
                          t+ = min over d_ij<0 of  1/(n |d_ij|),
        d = B - J_n/n.

      For B a permutation matrix this is t in [-1/(n-1), 1].  Phi_k(A(t)) - M
      is a polynomial in t of degree <= k, obtained here EXACTLY by evaluating
      at t = 0,1,...,k over Q and Lagrange-interpolating.

  (2) NAMED STRUCTURED MATRICES.  These appear as the endpoint t=1 of their
      own pencil, so one pencil computation gives both.

Everything is exact.  Matrices are carried as (integer numerator matrix,
positive integer denominator); sigma_k comes from Ryser inclusion-exclusion
applied to per(M + xJ) = sum_j (n-j)! sigma_j(M) x^{n-j}, in pure integer
arithmetic, which yields ALL k at once.
"""

import itertools
import os
import sys
import time
from fractions import Fraction as Q
from math import comb, factorial

# ------------------------------------------------------------------ exact core


def sigma_all_int(M, n):
    """[sigma_0(M), ..., sigma_n(M)] for an INTEGER matrix M.

    per(M + xJ) = sum_{j} (n-j)! sigma_j(M) x^{n-j}, and the order-n permanent
    is expanded by Ryser inclusion-exclusion over column subsets S:
        per(X) = sum_S (-1)^{n-|S|} prod_i ( sum_{j in S} X_ij ).
    With X = M + xJ the inner sum is (rowsum_S(i)) + |S| x, a linear factor.
    """
    tot = [0] * (n + 1)
    for r in range(1, n + 1):
        for S in itertools.combinations(range(n), r):
            prod = [1]
            for i in range(n):
                Mi = M[i]
                s0 = 0
                for j in S:
                    s0 += Mi[j]
                new = [0] * (len(prod) + 1)
                for idx, c in enumerate(prod):
                    if c:
                        new[idx] += c * s0
                        new[idx + 1] += c * r
                prod = new
            if (n - r) & 1:
                for idx, c in enumerate(prod):
                    tot[idx] -= c
            else:
                for idx, c in enumerate(prod):
                    tot[idx] += c
    out = []
    for k in range(n + 1):
        num, f = tot[n - k], factorial(n - k)
        assert num % f == 0, "non-integral sigma"
        out.append(num // f)
    return out


def esym_all(v, n):
    """[e_0(v), ..., e_n(v)] for a list of n numbers."""
    e = [1] + [0] * n
    for x in v:
        for j in range(n, 0, -1):
            e[j] += e[j - 1] * x
    return e


def bound(n, k):
    return Q(2) - Q(factorial(k), n ** k)


def phi_all_k(M, D, n):
    """A = M/D with M integer, D > 0, sum(M) = n*D.  Returns {k: Phi_k(A)}."""
    R = [sum(row) for row in M]
    C = [sum(M[i][j] for i in range(n)) for j in range(n)]
    sig = sigma_all_int(M, n)
    eR, eC = esym_all(R, n), esym_all(C, n)
    out = {}
    for k in range(1, n + 1):
        cnk = comb(n, k)
        out[k] = (Q(eR[k] + eC[k], cnk) - Q(sig[k], cnk * cnk)) / Q(D) ** k
    return out


# ------------------------------------------------------------------- pencils


def pencil_point(Bnum, Bden, n, t_int):
    """Integer-numerator form of A(t) = J/n + t(B - J/n) at integer t."""
    D = n * Bden
    M = [[Bden + t_int * (n * Bnum[i][j] - Bden) for j in range(n)]
         for i in range(n)]
    return M, D


def admissible_interval(Bnum, Bden, n):
    """[t-, t+] such that A(t) >= 0 entrywise."""
    lo, hi = None, None
    for i in range(n):
        for j in range(n):
            d = Q(Bnum[i][j], Bden) - Q(1, n)          # d_ij
            if d > 0:
                v = -Q(1, n) / d
                lo = v if lo is None else max(lo, v)
            elif d < 0:
                v = -Q(1, n) / d
                hi = v if hi is None else min(hi, v)
    return (lo if lo is not None else Q(-10 ** 9),
            hi if hi is not None else Q(10 ** 9))


def lagrange(points):
    """Exact interpolation of a polynomial through [(x_i, y_i)]; returns the
    coefficient list [c_0, c_1, ...]."""
    m = len(points)
    coeffs = [Q(0)] * m
    for i, (xi, yi) in enumerate(points):
        # basis_i(x) = prod_{j != i} (x - x_j)/(x_i - x_j)
        basis = [Q(1)]
        denom = Q(1)
        for j, (xj, _) in enumerate(points):
            if j == i:
                continue
            denom *= (xi - xj)
            new = [Q(0)] * (len(basis) + 1)
            for a, c in enumerate(basis):
                new[a] -= c * xj
                new[a + 1] += c
            basis = new
        f = yi / denom
        for a, c in enumerate(basis):
            coeffs[a] += c * f
    while len(coeffs) > 1 and coeffs[-1] == 0:
        coeffs.pop()
    return coeffs


def pev(coeffs, t):
    v = Q(0)
    for c in reversed(coeffs):
        v = v * t + c
    return v


def pderiv(coeffs):
    return [coeffs[i] * i for i in range(1, len(coeffs))] or [Q(0)]


def pencil_polys(Bnum, Bden, n, ks):
    """{k: coefficient list of p_k(t) = Phi_k(A(t)) - M(n,k)} for k in ks.

    p_k has degree <= k, so k+1 sample points determine it exactly."""
    kmax = max(ks)
    samples = {}
    for t in range(kmax + 1):
        M, D = pencil_point(Bnum, Bden, n, t)
        samples[t] = phi_all_k(M, D, n)
    out = {}
    for k in ks:
        pts = [(Q(t), samples[t][k] - bound(n, k)) for t in range(k + 1)]
        out[k] = lagrange(pts)
    return out


def scan_interval(coeffs, lo, hi, steps=240):
    """Exact evaluation of p on a rational grid over [lo,hi]; then, around the
    best grid cell, an exact bisection on p' to pin the local maximum."""
    best = (pev(coeffs, lo), lo)
    grid = []
    for s in range(steps + 1):
        t = lo + (hi - lo) * Q(s, steps)
        v = pev(coeffs, t)
        grid.append((t, v))
        if v > best[0]:
            best = (v, t)
    # refine on the two cells adjacent to the best grid point
    d = pderiv(coeffs)
    idx = max(range(len(grid)), key=lambda s: grid[s][1])
    for a, b in ((max(idx - 1, 0), idx), (idx, min(idx + 1, steps))):
        ta, tb = grid[a][0], grid[b][0]
        fa, fb = pev(d, ta), pev(d, tb)
        if fa == 0 or fb == 0 or (fa > 0) == (fb > 0):
            continue
        for _ in range(60):
            tm = (ta + tb) / 2
            fm = pev(d, tm)
            if fm == 0:
                ta = tb = tm
                break
            if (fm > 0) == (fa > 0):
                ta, fa = tm, fm
            else:
                tb, fb = tm, fm
        v = pev(coeffs, (ta + tb) / 2)
        if v > best[0]:
            best = (v, (ta + tb) / 2)
    return best  # (max value of p found, argmax)


def low_order(coeffs):
    """(order, coefficient) of the lowest-degree nonzero term above t^0."""
    for i in range(1, len(coeffs)):
        if coeffs[i] != 0:
            return i, coeffs[i]
    return None, Q(0)


# --------------------------------------------------------- matrix generators


def perm_matrix(p, n):
    M = [[0] * n for _ in range(n)]
    for i, j in enumerate(p):
        M[i][j] = 1
    return M, 1


def circulant(S, n):
    """(1/|S|) sum_{s in S} C^s : |S|-regular circulant, doubly stochastic."""
    m = len(S)
    M = [[0] * n for _ in range(n)]
    for i in range(n):
        for s in S:
            M[i][(i + s) % n] = 1
    return M, m


def weighted_circulant(w, n):
    """sum_s w_s C^s with rational weights w = {s: Q}, sum w_s = 1."""
    den = 1
    for v in w.values():
        den = den * v.denominator // __import__("math").gcd(den, v.denominator)
    M = [[0] * n for _ in range(n)]
    for i in range(n):
        for s, v in w.items():
            M[i][(i + s) % n] += int(v * den)
    return M, den


def from_01(M01, n):
    """Scale a nonnegative integer matrix into K_n: B = M * n / sum(M)."""
    tot = sum(sum(r) for r in M01)
    g = __import__("math").gcd(tot, n)
    return [[x * (n // g) for x in row] for row in M01], tot // g


def group_regular(elts, group_table, n):
    """Union of the permutations P_g, g in elts, of a group's Cayley table
    (a Latin square): an |elts|-regular 0/1 matrix, scaled to K_n."""
    M = [[0] * n for _ in range(n)]
    for i in range(n):
        for g in elts:
            M[i][group_table[g][i]] = 1
    return from_01(M, n)


def block_diag_J(parts, n):
    """Block diagonal of J_b/b over block sizes `parts` (sum = n)."""
    M = [[0] * n for _ in range(n)]
    off = 0
    dens = []
    for b in parts:
        for i in range(off, off + b):
            for j in range(off, off + b):
                M[i][j] = 1
        dens.append(b)
        off += b
    # common denominator = lcm of block sizes
    import math
    L = 1
    for b in dens:
        L = L * b // math.gcd(L, b)
    off = 0
    for b in parts:
        for i in range(off, off + b):
            for j in range(off, off + b):
                M[i][j] = L // b
        off += b
    return M, L


def rank_one(u, v, n):
    """B = u v^T scaled into K_n."""
    M = [[u[i] * v[j] for j in range(n)] for i in range(n)]
    return from_01(M, n)


def fano_incidence():
    """Point-line incidence of the Fano plane (7x7, 3-regular)."""
    lines = [(0, 1, 3), (1, 2, 4), (2, 3, 5), (3, 4, 6),
             (4, 5, 0), (5, 6, 1), (6, 0, 2)]
    M = [[0] * 7 for _ in range(7)]
    for li, L in enumerate(lines):
        for p in L:
            M[li][p] = 1
    return M


def biplane_11():
    """Symmetric 2-(11,5,2) design: rows are QR(11) = {1,3,4,5,9} translates."""
    QR = {1, 3, 4, 5, 9}
    M = [[1 if ((j - i) % 11) in QR else 0 for j in range(11)]
         for i in range(11)]
    return M


def complement01(M, n):
    return [[1 - M[i][j] for j in range(n)] for i in range(n)]


def cyclic_group_table(n):
    return [[(g + i) % n for i in range(n)] for g in range(n)]


def product_group_table(mods):
    """Cayley table of Z_{m1} x Z_{m2} x ..., indices = mixed-radix."""
    n = 1
    for m in mods:
        n *= m
    def dec(x):
        out = []
        for m in reversed(mods):
            out.append(x % m)
            x //= m
        return list(reversed(out))
    def enc(v):
        x = 0
        for m, a in zip(mods, v):
            x = x * m + a
        return x
    tab = []
    for g in range(n):
        gv = dec(g)
        tab.append([enc([(a + b) % m for a, b, m in zip(gv, dec(i), mods)])
                    for i in range(n)])
    return tab


def s3_table():
    """Cayley table of S_3 as a 6x6 Latin square (non-abelian)."""
    perms = list(itertools.permutations(range(3)))
    idx = {p: i for i, p in enumerate(perms)}
    def comp(a, b):
        return tuple(a[b[t]] for t in range(3))
    return [[idx[comp(perms[g], perms[i])] for i in range(6)] for g in range(6)]


def q8_table():
    """Cayley table of the quaternion group Q_8 (8x8 Latin square)."""
    names = ["1", "-1", "i", "-i", "j", "-j", "k", "-k"]
    idx = {s: t for t, s in enumerate(names)}
    def neg(s):
        return s[1:] if s.startswith("-") else "-" + s
    base = {("i", "j"): "k", ("j", "k"): "i", ("k", "i"): "j",
            ("j", "i"): "-k", ("k", "j"): "-i", ("i", "k"): "-j",
            ("i", "i"): "-1", ("j", "j"): "-1", ("k", "k"): "-1"}
    def mul(a, b):
        sa = a.startswith("-")
        sb = b.startswith("-")
        a2, b2 = a.lstrip("-"), b.lstrip("-")
        if a2 == "1":
            r = b2
        elif b2 == "1":
            r = a2
        else:
            r = base[(a2, b2)]
        s = sa ^ sb ^ r.startswith("-")
        r = r.lstrip("-")
        return ("-" + r) if s else r
    return [[idx[mul(names[g], names[i])] for i in range(8)] for g in range(8)]


def prolongation_latin(n):
    """A non-group Latin square: the 'turn-square'/intercalate-swapped cyclic
    square (swap the 2x2 intercalate in rows 0,1 x cols 0,1 when it exists)."""
    L = [[(i + j) % n for j in range(n)] for i in range(n)]
    # swap a 2x2 intercalate if one exists: rows 0,1 columns c,d with
    # L[0][c]=L[1][d] and L[0][d]=L[1][c]
    for c in range(n):
        for d in range(c + 1, n):
            if L[0][c] == L[1][d] and L[0][d] == L[1][c]:
                L[0][c], L[0][d] = L[0][d], L[0][c]
                L[1][c], L[1][d] = L[1][d], L[1][c]
                return L
    return L


def latin_symbol_union(L, syms, n):
    M = [[0] * n for _ in range(n)]
    for i in range(n):
        for j in range(n):
            if L[i][j] in syms:
                M[i][j] = 1
    return from_01(M, n)


def triangular(n):
    return from_01([[1 if j >= i else 0 for j in range(n)] for i in range(n)], n)


def arrow(n):
    M = [[0] * n for _ in range(n)]
    for i in range(n):
        M[0][i] = 1
        M[i][0] = 1
        M[i][i] = 1
    return from_01(M, n)


def petersen_like(n, degs):
    """Circulant graph adjacency, degree |degs| symmetric set, scaled."""
    S = set()
    for d in degs:
        S.add(d % n)
        S.add((-d) % n)
    return circulant(sorted(S), n)


# ------------------------------------------------- direction-form of a pencil
# Only the DIRECTION d = B - J/n matters: rescaling d just reparametrises t.
# Working with d directly also admits directions that are not of the form
# B - J/n for a "named" B (e.g. a single intercalate).


def dir_from_B(Bnum, Bden, n):
    """d = B - J_n/n as (integer numerator matrix, denominator)."""
    return [[n * Bnum[i][j] - Bden for j in range(n)] for i in range(n)], n * Bden


def dir_point(dnum, dden, n, t_int):
    """A(t) = J/n + t d, as (integer numerator, denominator)."""
    return ([[dden + t_int * n * dnum[i][j] for j in range(n)]
             for i in range(n)], n * dden)


def dir_admissible(dnum, dden, n):
    lo, hi = None, None
    for i in range(n):
        for j in range(n):
            d = Q(dnum[i][j], dden)
            if d > 0:
                v = -Q(1, n) / d
                lo = v if lo is None else max(lo, v)
            elif d < 0:
                v = -Q(1, n) / d
                hi = v if hi is None else min(hi, v)
    return (lo if lo is not None else Q(-10 ** 6),
            hi if hi is not None else Q(10 ** 6))


def dir_polys(dnum, dden, n, ks):
    """{k: coefficients of p_k(t) = Phi_k(J/n + t d) - M(n,k)}, exact."""
    assert sum(sum(r) for r in dnum) == 0, "direction must have zero entry sum"
    kmax = max(ks)
    samples = {}
    for t in range(kmax + 1):
        M, D = dir_point(dnum, dden, n, t)
        samples[t] = phi_all_k(M, D, n)
    return {k: lagrange([(Q(t), samples[t][k] - bound(n, k))
                         for t in range(k + 1)]) for k in ks}


def dir_norm2(dnum, dden, n):
    s = sum(x * x for row in dnum for x in row)
    return Q(s, dden * dden)


def intercalate_dir(n):
    """The sparsest zero-row-sum zero-column-sum direction: +1 -1 / -1 +1."""
    d = [[0] * n for _ in range(n)]
    d[0][0] = d[1][1] = 1
    d[0][1] = d[1][0] = -1
    return d, 1


def row_effect_dir(n, w):
    """d_ij = w_i / n with sum w = 0: pure row-sum perturbation."""
    return [[w[i] for _ in range(n)] for i in range(n)], n


def col_effect_dir(n, w):
    return [[w[j] for j in range(n)] for _ in range(n)], n
