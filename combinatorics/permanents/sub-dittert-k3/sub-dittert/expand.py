"""
Cheon-Hwang sub-Dittert conjecture: exact expansion of the objective in centred
coordinates.

Source of the statement: G.-S. Cheon and S.-G. Hwang, "Maximization of a matrix
function related to the Dittert conjecture", Linear Algebra Appl. 165 (1992)
153-165, doi:10.1016/0024-3795(92)90234-2.

For A in K_n = { A >= 0 : sum_ij a_ij = n }, with row sums r and column sums c,

    E_k(r)      = e_k(r) / C(n,k)
    P_k(A)      = sigma_k(A) / C(n,k)^2
    gamma(n,k)  = k! / n^k

where e_k is the k-th elementary symmetric polynomial and sigma_k(A) is the sum
of the permanents of all k x k submatrices of A.  The conjecture is

    E_k(r) + E_k(c) - P_k(A)  <=  2 - gamma(n,k),      1 <= k <= n,

with equality only at A = J_n/n.

Two sanity anchors, both checked in validate.py:

  * k = n gives E_n(r) = prod r_i, P_n(A) = per(A), gamma = n!/n^n, so the
    statement is EXACTLY Dittert's conjecture.  At n = 4 this must reproduce
    dittert/expand.py term for term.
  * At A = J_n/n every row and column sum is 1, so e_k = C(n,k) and E_k = 1;
    every k x k submatrix is J_k/n with permanent k!/n^k, and there are
    C(n,k)^2 of them, so P_k = gamma(n,k).  The bound is attained.

TRAP.  At n = 4 the right-hand side is 61/32 for BOTH k = 3 and k = 4, because
3!/4^3 = 24/256 = 4!/4^4.  Seeing 61/32 is therefore NOT evidence that the k = 3
code is right.  validate.py separates the two by comparing whole polynomials.

Centred coordinates: A = J_n/n + b, so sum_ij b_ij = 0 and a_ij >= 0 reads
b_ij >= -1/n.  This module builds

    F(b) := (2 - gamma(n,k)) - [ E_k(r) + E_k(c) - P_k(J_n/n + b) ]

exactly over Q, so the conjecture is F >= 0 on K_n with equality only at b = 0.
deg F = k.  At (n,k) = (4,3) that is degree 3, one lower than Dittert at n = 4.
"""

import itertools
from fractions import Fraction as F
from math import comb, factorial


def zero_exp(N):
    return (0,) * N


def poly_add(p, q):
    out = dict(p)
    for e, c in q.items():
        v = out.get(e, F(0)) + c
        if v:
            out[e] = v
        else:
            out.pop(e, None)
    return out


def poly_mul(p, q):
    out = {}
    for e1, c1 in p.items():
        for e2, c2 in q.items():
            e = tuple(x + y for x, y in zip(e1, e2))
            v = out.get(e, F(0)) + c1 * c2
            if v:
                out[e] = v
            else:
                out.pop(e, None)
    return out


def poly_scale(p, s):
    if s == 0:
        return {}
    return {e: c * s for e, c in p.items()}


def poly_sub(p, q):
    return poly_add(p, poly_scale(q, F(-1)))


def elem_sym(polys, k):
    """e_k of a list of polynomials, by the standard O(nk) recurrence."""
    N = len(next(iter(polys[0]))) if polys else 0
    e = [{zero_exp(N): F(1)}] + [{} for _ in range(k)]
    for p in polys:
        for j in range(min(k, len(e) - 1), 0, -1):
            e[j] = poly_add(e[j], poly_mul(e[j - 1], p))
    return e[k]


def permanent_poly(rows):
    """Permanent of a square matrix of polynomials, by the permutation sum."""
    m = len(rows)
    N = len(next(iter(rows[0][0])))
    total = {}
    for sigma in itertools.permutations(range(m)):
        term = {zero_exp(N): F(1)}
        for i in range(m):
            term = poly_mul(term, rows[i][sigma[i]])
        total = poly_add(total, term)
    return total


def build(n, k):
    """Return a dict with F(b), the entries, and the pieces, all exact over Q."""
    N = n * n
    idx = {(i, j): i * n + j for i in range(n) for j in range(n)}

    def var(i, j):
        e = [0] * N
        e[idx[(i, j)]] = 1
        return {tuple(e): F(1)}

    def const(c):
        c = F(c)
        return {zero_exp(N): c} if c else {}

    inv_n = F(1, n)
    entry = {(i, j): poly_add(const(inv_n), var(i, j))
             for i in range(n) for j in range(n)}

    rows = [poly_add(const(0), {}) for _ in range(n)]
    rows = []
    for i in range(n):
        s = {}
        for j in range(n):
            s = poly_add(s, entry[(i, j)])
        rows.append(s)
    cols = []
    for j in range(n):
        s = {}
        for i in range(n):
            s = poly_add(s, entry[(i, j)])
        cols.append(s)

    Ek_r = poly_scale(elem_sym(rows, k), F(1, comb(n, k)))
    Ek_c = poly_scale(elem_sym(cols, k), F(1, comb(n, k)))

    sigma = {}
    for alpha in itertools.combinations(range(n), k):
        for beta in itertools.combinations(range(n), k):
            sub = [[entry[(a, b)] for b in beta] for a in alpha]
            sigma = poly_add(sigma, permanent_poly(sub))
    Pk = poly_scale(sigma, F(1, comb(n, k) ** 2))

    gamma = F(factorial(k), n ** k)
    M = F(2) - gamma
    obj = poly_sub(poly_add(Ek_r, Ek_c), Pk)          # the quantity bounded
    Fpoly = poly_sub(const(M), obj)

    return dict(n=n, k=k, N=N, idx=idx, F=Fpoly, M=M, gamma=gamma,
                obj=obj, Ek_r=Ek_r, Ek_c=Ek_c, Pk=Pk, sigma=sigma,
                entry=entry, rows=rows, cols=cols)


def evaluate(p, point):
    tot = F(0)
    for e, c in p.items():
        v = c
        for t, et in enumerate(e):
            if et:
                v *= point[t] ** et
        tot += v
    return tot


def gradient(p, N):
    out = []
    for t in range(N):
        d = {}
        for e, c in p.items():
            if e[t]:
                e2 = list(e)
                e2[t] -= 1
                e2 = tuple(e2)
                d[e2] = d.get(e2, F(0)) + c * e[t]
        out.append(d)
    return out


def hessian(p, N):
    """Exact Hessian matrix of p at b = 0, as a list of lists of Fractions."""
    H = [[F(0)] * N for _ in range(N)]
    for e, c in p.items():
        if sum(e) != 2:
            continue
        nz = [t for t, et in enumerate(e) if et]
        if len(nz) == 1:
            t = nz[0]
            H[t][t] = 2 * c
        else:
            s, t = nz
            H[s][t] = c
            H[t][s] = c
    return H


if __name__ == "__main__":
    for (n, k) in [(3, 2), (3, 3), (4, 2), (4, 3), (4, 4), (5, 3), (5, 4)]:
        d = build(n, k)
        N = d["N"]
        zero = [F(0)] * N
        Fp = d["F"]
        degs = sorted({sum(e) for e in Fp})
        val = evaluate(Fp, zero)
        grad = [evaluate(g, zero) for g in gradient(Fp, N)]
        gset = sorted(set(grad))
        print(f"(n,k)=({n},{k}): gamma={d['gamma']}  M=2-gamma={d['M']}"
              f" = {float(d['M']):.10f}")
        print(f"   monomials in F: {len(Fp)}, degrees {degs}")
        print(f"   F(0) = {val}  (must be 0)")
        print(f"   distinct grad F(0) values: {gset}"
              f"  -> {'CRITICAL on K_n' if len(gset) == 1 else 'NOT constant'}")
        print()
