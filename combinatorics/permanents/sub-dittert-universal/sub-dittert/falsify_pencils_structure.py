#!/usr/bin/env python3
"""Structure probe + exact one-step ascent.

(A) PERMUTATION INVARIANCE.  Phi_k is invariant under A -> QAR for permutation
    matrices Q,R (row sums permute, column sums permute, sigma_k is unchanged).
    Since QJR = J, the pencil J/n + t(P - J/n) is carried to J/n + t(QPR - J/n),
    and every permutation matrix is QPR for P = I.  So ALL permutation pencils
    are the same pencil.  Checked here by comparing exact coefficient lists.

(B) HESSIAN ISOTYPIC STRUCTURE.  The quadratic coefficient c_2 of
    p_k(t) = Phi_k(J/n + t d) - M is (1/2) d^T H d.  H commutes with the row and
    column permutation actions and with transposition, so it acts as a scalar on
    each isotypic piece of {sum d = 0}: row-effect, column-effect, interaction
    (zero row AND column sums).  Confirmed here by exhibiting equal Rayleigh
    quotients across many directions in the same piece.

(C) EXACT ASCENT.  Gradient of Phi_k in closed form:
      d e_k(r)/d a_ij  = e_{k-1}(r with r_i deleted)
      d e_k(c)/d a_ij  = e_{k-1}(c with c_j deleted)
      d sigma_k/d a_ij = sigma_{k-1}(A with row i and column j deleted)
    (expand per(A[alpha,beta]) along the entry (i,j)).  We project the gradient
    onto {sum b = 0}, the tangent space of K_n, and do one exact line search.
"""
import itertools
import json
import os
import sys
import time
from fractions import Fraction as Q
from math import comb, factorial

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import falsify_pencils as fp  # noqa: E402


# --------------------------------------------------------------- (A) and (B)
def probe(nmax=10):
    print("== (A) permutation pencils are all the same pencil ==")
    for n in range(6, nmax + 1):
        ks = list(range(5, n))
        ident = list(range(n))
        cyc = [(i + 1) % n for i in range(n)]
        inv = list(range(n))
        for i in range(0, n - 1, 2):
            inv[i], inv[i + 1] = inv[i + 1], inv[i]
        mix = list(range(n))
        mix[0], mix[1] = mix[1], mix[0]
        tail = list(range(2, n))
        for a, i in enumerate(tail):
            mix[i] = tail[(a + 1) % len(tail)]
        polys = []
        for p in (ident, cyc, inv, mix):
            d = fp.dir_from_B(*fp.perm_matrix(p, n), n)
            polys.append(fp.dir_polys(*d, n, ks))
        same = all(polys[i][k] == polys[0][k] for i in range(1, 4) for k in ks)
        print(f"  n={n}: identity / n-cycle / 2-cycle-product / mixed "
              f"pencils identical: {same}")
        for k in ks:
            c = polys[0][k]
            print(f"    n={n} k={k}: p_k(t) = " +
                  " + ".join(f"({c[i]}) t^{i}" for i in range(1, len(c))
                             if c[i] != 0))
            print(f"        p_k on [-1/{n - 1}, 1]: "
                  f"p(1) = {fp.pev(c, Q(1))}, "
                  f"p(-1/{n-1}) = {fp.pev(c, Q(-1, n - 1))}")

    print("\n== (B) Hessian is a scalar on each isotypic piece ==")
    for n in range(6, nmax + 1):
        for k in range(5, n):
            vals = {}
            probes = []
            # interaction directions (zero row AND column sums)
            probes.append(("interaction:intercalate", ) + fp.intercalate_dir(n))
            probes.append(("interaction:I-J/n", )
                          + fp.dir_from_B(*fp.perm_matrix(list(range(n)), n), n))
            probes.append(("interaction:circ01", )
                          + fp.dir_from_B(*fp.circulant([0, 1], n), n))
            w = [0] * n
            w[0], w[1] = 1, -1
            probes.append(("row-effect:pair", ) + fp.row_effect_dir(n, w))
            w2 = [n - 1] + [-1] * (n - 1)
            probes.append(("row-effect:spike", ) + fp.row_effect_dir(n, w2))
            probes.append(("col-effect:pair", ) + fp.col_effect_dir(n, w))
            probes.append(("col-effect:spike", ) + fp.col_effect_dir(n, w2))
            for lab, dn, dd in probes:
                p = fp.dir_polys(dn, dd, n, [k])[k]
                r = p[2] / fp.dir_norm2(dn, dd, n)
                vals.setdefault(lab.split(":")[0], []).append((lab, r))
            print(f"  n={n} k={k}")
            for piece, lst in vals.items():
                uniq = {str(r) for _, r in lst}
                print(f"    {piece:12s} c_2/||d||^2 = {lst[0][1]} "
                      f"(constant across probes: {len(uniq) == 1})")


# ------------------------------------------------------------------- (C)
def sigma_km1_minor(M, n, i, j, k):
    sub = [[M[a][b] for b in range(n) if b != j] for a in range(n) if a != i]
    return fp.sigma_all_int(sub, n - 1)[k - 1]


def gradient(M, D, n, k):
    """Exact grad of Phi_k at A = M/D, as a matrix of Fractions."""
    R = [sum(r) for r in M]
    C = [sum(M[a][j] for a in range(n)) for j in range(n)]
    cnk = comb(n, k)
    eR_del = [fp.esym_all([R[a] for a in range(n) if a != i], n - 1)[k - 1]
              for i in range(n)]
    eC_del = [fp.esym_all([C[b] for b in range(n) if b != j], n - 1)[k - 1]
              for j in range(n)]
    g = [[Q(0)] * n for _ in range(n)]
    for i in range(n):
        for j in range(n):
            s = sigma_km1_minor(M, n, i, j, k)
            g[i][j] = (Q(eR_del[i] + eC_del[j], cnk)
                       - Q(s, cnk * cnk)) / Q(D) ** (k - 1)
    return g


def ascend(M, D, n, k, label):
    """One exact line search along the K_n-tangential gradient at A = M/D."""
    g = gradient(M, D, n, k)
    mean = sum(g[i][j] for i in range(n) for j in range(n)) / (n * n)
    b = [[g[i][j] - mean for j in range(n)] for i in range(n)]
    den = 1
    for row in b:
        for x in row:
            den = den * x.denominator // __import__("math").gcd(
                den, x.denominator)
    bn = [[int(x * den) for x in row] for row in b]
    if all(x == 0 for row in bn for x in row):
        return None
    # A(s) = A + s*b ; keep integer arithmetic: numerator D*den*A + s*D*bn ...
    # A(s)_ij = (M_ij*den + s*bn_ij) / (D*den) for integer s
    Dn = D * den
    Mn = [[M[i][j] * den for j in range(n)] for i in range(n)]
    lo, hi = None, None
    for i in range(n):
        for j in range(n):
            if bn[i][j] > 0:
                v = -Q(Mn[i][j], bn[i][j])
                lo = v if lo is None else max(lo, v)
            elif bn[i][j] < 0:
                v = -Q(Mn[i][j], bn[i][j])
                hi = v if hi is None else min(hi, v)
    if lo is None:
        lo = Q(-1)
    if hi is None:
        hi = Q(1)
    pts = []
    for s in range(k + 1):
        Ms = [[Mn[i][j] + s * bn[i][j] for j in range(n)] for i in range(n)]
        pts.append((Q(s), fp.phi_all_k(Ms, Dn, n)[k] - fp.bound(n, k)))
    p = fp.lagrange(pts)
    vmax, sarg = fp.scan_interval(p, lo, hi)
    Mb = fp.bound(n, k)
    return dict(family=label, n=n, k=k, s_lo=str(lo), s_hi=str(hi),
                p_at_start=str(fp.pev(p, Q(0))), p_max=str(vmax),
                s_argmax=str(sarg), ratio_max=str(1 + vmax / Mb))


def ascent_run():
    print("\n== (C) one exact gradient ascent step from named structured "
          "points ==")
    cases = []
    for n, k in ((7, 5), (7, 6), (8, 5), (8, 7), (9, 5), (9, 8)):
        seeds = [("perm:identity", ) + fp.perm_matrix(list(range(n)), n),
                 ("circ-reg:all-but-0", ) + fp.circulant(list(range(1, n)), n),
                 ("circ-reg:0.1", ) + fp.circulant([0, 1], n),
                 ("blockJ:2+rest", ) + fp.block_diag_J([2, n - 2], n),
                 ("triangular", ) + fp.triangular(n)]
        if n == 7:
            seeds.append(("design:Fano", ) + fp.from_01(fp.fano_incidence(), 7))
        for lab, Bn, Bd in seeds:
            cases.append((lab, Bn, Bd, n, k))
    hits = []
    for lab, Bn, Bd, n, k in cases:
        r = ascend(Bn, Bd, n, k, lab)
        if r is None:
            print(f"  n={n} k={k} {lab}: gradient is constant, no tangential "
                  f"direction")
            continue
        print(f"  n={n} k={k} {lab}: p at start = {r['p_at_start']}, "
              f"p_max along ascent = {r['p_max']} at s={r['s_argmax']}, "
              f"ratio = {float(Q(r['ratio_max'])):.9f}")
        if Q(r["p_max"]) > 0:
            hits.append(r)
    print("  ascent hits (p > 0):", len(hits))
    return hits


if __name__ == "__main__":
    nmax = int(sys.argv[1]) if len(sys.argv) > 1 else 10
    probe(nmax)
    ascent_run()
