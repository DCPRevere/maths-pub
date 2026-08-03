"""
Exact rational rounding for the sub-Dittert certificate.

The semidefinite program is solved in floating point; NOTHING about that solve is
trusted.  This module

  1. rebuilds the constraint system over Q with integer accumulators, so A0 and
     A2 are integer matrices and A1 = A1c/n + A1l with both parts integer;
  2. rounds the numerical solution to rationals and then applies an EXACT
     rational correction, chosen on a pivot set of the row-reduced system, so the
     linear identity holds IDENTICALLY over Q rather than approximately;
  3. provides exact rational LDL^T so positive definiteness is decided over Q.

The module name is `exactsd` rather than `exact` on purpose: dittert/ has its own
`exact.py`, and both directories end up on sys.path.  A silent name collision
would make the pipeline verify the wrong problem, which is exactly the class of
error this project keeps paying for.
"""

import itertools
import os
import sys
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "dittert"))
sys.path.insert(0, HERE)  # HERE must win the name `expand` (see sos.py)
from symmetry import act, monomials                              # noqa: E402


def exact_system(d):
    """Rebuild A0, A1 (= A1c/n + A1l), A2, rhs exactly from the orbit data."""
    from sos import transporters
    n, B = d["n"], d["B"]
    N = n * n
    basis, orbit_of = d["basis"], d["orbit_of"]
    rows = d["n_rows"]
    trans = transporters(n, (0, 0))

    def mm(u, v):
        return tuple(sorted(u + v))

    A0 = [[0] * len(d["g_orbits"]) for _ in range(rows)]
    for vi, orb in enumerate(d["g_orbits"]):
        for code in orb:
            u, v = divmod(code, B)
            A0[orbit_of[mm(basis[u], basis[v])]][vi] += 1

    A1c = [[0] * len(d["s_orbits"]) for _ in range(rows)]
    A1l = [[0] * len(d["s_orbits"]) for _ in range(rows)]
    for vi, orb in enumerate(d["s_orbits"]):
        for code in orb:
            u, v = divmod(code, B)
            bu, bv = basis[u], basis[v]
            for pk in range(N):
                g = trans[pk]
                prod = mm(act(g, bu), act(g, bv))
                A1c[orbit_of[prod]][vi] += 1
                A1l[orbit_of[mm(prod, (pk,))]][vi] += 1

    lam_mons = monomials(N, d["TOPDEG"] - 1)
    A2 = [[0] * len(d["lam_orbit_reps"]) for _ in range(rows)]
    for vi, members in enumerate(d["lam_orbit_reps"]):
        for t in members:
            mu = lam_mons[t]
            for pk in range(N):
                A2[orbit_of[mm(mu, (pk,))]][vi] += 1

    rhs = [F(0)] * rows
    for e, c in d["Fpoly"].items():
        mono = tuple(sorted(itertools.chain.from_iterable(
            [t] * et for t, et in enumerate(e) if et)))
        rhs[orbit_of[mono]] += c
    return A0, A1c, A1l, A2, rhs


def full_matrix(A0, A1c, A1l, A2, n):
    out = []
    for r in range(len(A0)):
        row = [F(v) for v in A0[r]]
        row += [F(A1c[r][t], n) + F(A1l[r][t]) for t in range(len(A1c[r]))]
        row += [F(v) for v in A2[r]]
        out.append(row)
    return out


def rref_pivots(M, rhs):
    A = [row[:] for row in M]
    b = list(rhs)
    R, C = len(A), len(A[0])
    piv, r = [], 0
    for c in range(C):
        k = next((i for i in range(r, R) if A[i][c] != 0), None)
        if k is None:
            continue
        A[r], A[k] = A[k], A[r]
        b[r], b[k] = b[k], b[r]
        pv = A[r][c]
        A[r] = [v / pv for v in A[r]]
        b[r] = b[r] / pv
        for i in range(R):
            if i != r and A[i][c] != 0:
                f = A[i][c]
                A[i] = [x - f * y for x, y in zip(A[i], A[r])]
                b[i] = b[i] - f * b[r]
        piv.append(c)
        r += 1
        if r == R:
            break
    return piv, A, b, r


def independent_rows(M, rhs):
    """Exact row reduction over Q -> (kept, redundant, consistent)."""
    R, C = len(M), len(M[0])
    A = [row[:] for row in M]
    b = list(rhs)
    order = list(range(R))
    kept, r = [], 0
    for c in range(C):
        k = next((i for i in range(r, R) if A[i][c] != 0), None)
        if k is None:
            continue
        A[r], A[k] = A[k], A[r]
        b[r], b[k] = b[k], b[r]
        order[r], order[k] = order[k], order[r]
        pv = A[r][c]
        A[r] = [v / pv for v in A[r]]
        b[r] = b[r] / pv
        for i in range(r + 1, R):
            if A[i][c] != 0:
                f = A[i][c]
                A[i] = [x - f * y for x, y in zip(A[i], A[r])]
                b[i] = b[i] - f * b[r]
        kept.append(order[r])
        r += 1
        if r == R:
            break
    redundant = [order[i] for i in range(r, R)]
    consistent = all(b[i] == 0 for i in range(r, R))
    return sorted(kept), sorted(redundant), consistent


def round_and_correct(d, xnum, ynum, znum, denom=10 ** 7):
    """Round the numerical solution, then correct it exactly onto the identity."""
    n = d["n"]
    A0, A1c, A1l, A2, rhs = exact_system(d)
    Mfull = full_matrix(A0, A1c, A1l, A2, n)
    nx, ny = len(xnum), len(ynum)

    v = [F(round(float(t) * denom), denom)
         for t in list(xnum) + list(ynum) + list(znum)]
    resid = []
    for r in range(len(Mfull)):
        s = sum(Mfull[r][t] * v[t] for t in range(len(v)))
        resid.append(rhs[r] - s)

    piv, A, b, rank = rref_pivots(Mfull, resid)
    delta = [F(0)] * len(v)
    for i, c in enumerate(piv):
        delta[c] = b[i]
    vstar = [v[t] + delta[t] for t in range(len(v))]

    ok = all(sum(Mfull[r][t] * vstar[t] for t in range(len(vstar))) == rhs[r]
             for r in range(len(Mfull)))
    maxd = max((abs(x) for x in delta), default=F(0))
    return vstar[:nx], vstar[nx:nx + ny], vstar[nx + ny:], ok, maxd


def assemble(B, orbs, coeffs):
    G = [[F(0)] * B for _ in range(B)]
    for vi, orb in enumerate(orbs):
        c = coeffs[vi]
        if c == 0:
            continue
        for code in orb:
            u, v = divmod(code, B)
            G[u][v] += c
    return G


def ldl_pivots(G):
    """Exact rational LDL^T.  (pivots, None) if positive definite, else
    (None, index of the first non-positive pivot)."""
    B = len(G)
    a = [row[:] for row in G]
    piv = []
    for k in range(B):
        dk = a[k][k]
        if dk <= 0:
            return None, k
        piv.append(dk)
        for i in range(k + 1, B):
            if a[i][k] == 0:
                continue
            f = a[i][k] / dk
            for j in range(k, B):
                a[i][j] -= f * a[k][j]
            for j in range(k, B):
                a[j][i] = a[i][j]
    return piv, None


def is_symmetric(G):
    B = len(G)
    return all(G[i][j] == G[j][i] for i in range(B) for j in range(i + 1, B))
