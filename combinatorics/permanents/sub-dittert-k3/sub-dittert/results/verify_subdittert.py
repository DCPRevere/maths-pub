#!/usr/bin/env python3
"""
STANDALONE verifier for the Cheon-Hwang sub-Dittert certificate.

This file shares NO code with the pipeline that produced the certificate.  It
imports only the Python standard library: no numpy, no scipy, no cvxpy, and
nothing from the sub-dittert or dittert packages.  It re-derives the objective
from the definition in the 1992 paper, reads only the JSON certificate, and
decides everything in exact rational arithmetic.  No floating-point number is
used in any decision.

WHAT IS BEING PROVED.  For A in K_n = { A >= 0 : sum a_ij = n }, with row sums r
and column sums c,

    E_k(r) = e_k(r)/C(n,k),  P_k(A) = sigma_k(A)/C(n,k)^2,  gamma = k!/n^k,

    E_k(r) + E_k(c) - P_k(A) <= 2 - gamma,   with equality only at J_n/n.

HOW.  Write A = J_n/n + b, so sum b = 0 and a_p = 1/n + b_p >= 0.  Put
F(b) = (2 - gamma) - [E_k(r) + E_k(c) - P_k(A)].  The certificate exhibits

    F(b) = sigma_0(b) + sum_p (1/n + b_p) sigma_p(b) + lambda(b) * (sum_q b_q)

with sigma_0(b) = b^T G0 b and sigma_p(b) = b^T G[p] b.  On K_n the last term
vanishes (sum b = 0) and every 1/n + b_p is >= 0, so if G0 and all G[p] are
positive SEMIdefinite then F >= 0 on K_n: the inequality.

UNIQUENESS comes free from POSITIVE DEFINITENESS.  If F(b) = 0 for some b in K_n
then every term above is zero; in particular b^T G0 b = 0, and G0 positive
definite forces b = 0.  So J_n/n is the ONLY point of equality.  This is why the
script insists on definiteness, not merely semidefiniteness.

CHECKS PERFORMED
  1. sigma_k by two structurally different algorithms (direct subpermanent
     enumeration, and Ryser inclusion-exclusion applied to per(A + xJ)).
  2. the bound M read from the file equals 2 - k!/n^k.
  3. the identity, by FULL coefficient comparison over Q -- every monomial, never
     sampling.
  4. G0 and all n^2 multiplier Grams positive definite, by exact rational LDL^T.
  5. mutation tests: perturbations of the certificate that MUST be rejected.  A
     verifier that never rejects proves nothing.

Usage:  python3 verify_subdittert.py [certificate.json]
"""

import itertools
import json
import os
import sys
from fractions import Fraction as Q


# ----------------------------------------------------------- polynomial algebra
# A polynomial is a dict from a sorted tuple of variable indices (with
# repetition) to a rational coefficient.  () is the constant monomial.
def padd(p, q):
    out = dict(p)
    for m, c in q.items():
        v = out.get(m, Q(0)) + c
        if v:
            out[m] = v
        else:
            out.pop(m, None)
    return out


def pmul(p, q):
    out = {}
    for m1, c1 in p.items():
        for m2, c2 in q.items():
            m = tuple(sorted(m1 + m2))
            v = out.get(m, Q(0)) + c1 * c2
            if v:
                out[m] = v
            else:
                out.pop(m, None)
    return out


def pscale(p, s):
    return {} if s == 0 else {m: c * s for m, c in p.items()}


def psub(p, q):
    return padd(p, pscale(q, Q(-1)))


def pconst(c):
    c = Q(c)
    return {(): c} if c else {}


def pvar(i):
    return {(i,): Q(1)}


# ------------------------------------------------------------- the objective F
def elementary(polys, k):
    """e_k of a list of polynomials."""
    e = [pconst(1)] + [{} for _ in range(k)]
    for p in polys:
        for j in range(k, 0, -1):
            e[j] = padd(e[j], pmul(e[j - 1], p))
    return e[k]


def permanent(rows):
    """Permanent by the permutation sum (definition)."""
    m = len(rows)
    tot = {}
    for s in itertools.permutations(range(m)):
        t = pconst(1)
        for i in range(m):
            t = pmul(t, rows[i][s[i]])
        tot = padd(tot, t)
    return tot


def binom(n, k):
    r = 1
    for i in range(k):
        r = r * (n - i) // (i + 1)
    return r


def factorial(k):
    r = 1
    for i in range(2, k + 1):
        r *= i
    return r


def build_F(n, k):
    """F(b) = (2 - k!/n^k) - [E_k(r) + E_k(c) - P_k(J/n + b)], exactly over Q."""
    N = n * n
    entry = {(i, j): padd(pconst(Q(1, n)), pvar(i * n + j))
             for i in range(n) for j in range(n)}
    rows, cols = [], []
    for i in range(n):
        s = {}
        for j in range(n):
            s = padd(s, entry[(i, j)])
        rows.append(s)
    for j in range(n):
        s = {}
        for i in range(n):
            s = padd(s, entry[(i, j)])
        cols.append(s)

    sig = {}
    for al in itertools.combinations(range(n), k):
        for be in itertools.combinations(range(n), k):
            sig = padd(sig, permanent([[entry[(a, b)] for b in be]
                                       for a in al]))

    obj = psub(padd(pscale(elementary(rows, k), Q(1, binom(n, k))),
                    pscale(elementary(cols, k), Q(1, binom(n, k)))),
               pscale(sig, Q(1, binom(n, k) ** 2)))
    M = Q(2) - Q(factorial(k), n ** k)
    return psub(pconst(M), obj), M, sig


# --------------------------------- sigma_k by a second, structurally different route
def ryser_sigma_k(A, n, k):
    """sigma_k(A) from per(A + xJ) = sum_j x^{n-j} (n-j)! sigma_j(A), with the
    order-n permanent computed by Ryser inclusion-exclusion over column subsets.
    Univariate polynomials in x are plain coefficient lists."""
    def umul(p, q):
        o = [Q(0)] * (len(p) + len(q) - 1)
        for i, a in enumerate(p):
            if a:
                for j, b in enumerate(q):
                    if b:
                        o[i + j] += a * b
        return o

    def uadd(p, q):
        m = max(len(p), len(q))
        return [(p[i] if i < len(p) else Q(0)) + (q[i] if i < len(q) else Q(0))
                for i in range(m)]

    tot = [Q(0)]
    for r in range(1, n + 1):
        for S in itertools.combinations(range(n), r):
            prod = [Q(1)]
            for i in range(n):
                s = [Q(0), Q(0)]
                for j in S:
                    s = uadd(s, [A[i][j], Q(1)])
                prod = umul(prod, s)
            sgn = Q((-1) ** (n - r))
            tot = uadd(tot, [sgn * c for c in prod])
    while len(tot) < n + 1:
        tot.append(Q(0))
    return tot[n - k] / factorial(n - k)


def direct_sigma_k(A, n, k):
    tot = Q(0)
    for al in itertools.combinations(range(n), k):
        for be in itertools.combinations(range(n), k):
            for s in itertools.permutations(range(k)):
                p = Q(1)
                for t in range(k):
                    p *= A[al[t]][be[s[t]]]
                tot += p
    return tot


# ------------------------------------------------------------- exact linear algebra
def ldl_positive_definite(G):
    """Exact rational LDL^T without pivoting.  Returns (True, min_pivot) if G is
    positive definite, else (False, index of the first non-positive pivot)."""
    B = len(G)
    a = [row[:] for row in G]
    pivots = []
    for kk in range(B):
        d = a[kk][kk]
        if d <= 0:
            return False, kk
        pivots.append(d)
        for i in range(kk + 1, B):
            if a[i][kk] == 0:
                continue
            f = a[i][kk] / d
            for j in range(kk, B):
                a[i][j] -= f * a[kk][j]
            for j in range(kk, B):
                a[j][i] = a[i][j]
    return True, min(pivots)


def symmetric(G):
    B = len(G)
    return all(G[i][j] == G[j][i] for i in range(B) for j in range(i + 1, B))


# ------------------------------------------------------------------- the checks
def certificate_polynomial(cert):
    """Multiply out the right-hand side of the certificate identity.

    basis[u] is a MONOMIAL (a sorted tuple of variable indices), so the product
    m_u * m_v is the concatenation, re-sorted.  With a degree-1 basis this
    reduces to the pair (u,v), but the code does not assume that."""
    n, N = cert["n"], cert["N"]
    G0 = cert["G0"]
    Gp = cert["Gp"]
    lam = cert["lam"]
    basis = cert["basis"]
    B = len(G0)
    assert len(basis) == B, "basis length does not match the Gram size"

    rhs = {}

    def add(m, c):
        if c:
            v = rhs.get(m, Q(0)) + c
            if v:
                rhs[m] = v
            else:
                rhs.pop(m, None)

    prod = [[tuple(sorted(basis[u] + basis[v])) for v in range(B)]
            for u in range(B)]

    for u in range(B):
        for v in range(B):
            c = G0[u][v]
            if c:
                add(prod[u][v], c)

    inv = Q(1, n)
    for p in range(N):
        M = Gp[p]
        for u in range(B):
            for v in range(B):
                c = M[u][v]
                if not c:
                    continue
                base = prod[u][v]
                add(base, c * inv)
                add(tuple(sorted(base + (p,))), c)

    for mono, c in lam.items():
        if not c:
            continue
        for q in range(N):
            add(tuple(sorted(mono + (q,))), c)
    return rhs


def load(path):
    with open(path) as fh:
        raw = json.load(fh)
    cert = dict(n=raw["n"], k=raw["k"], N=raw["N"], M=Q(raw["bound_M"]))
    cert["basis"] = [tuple(m) for m in raw["basis"]]
    cert["G0"] = [[Q(x) for x in row] for row in raw["G0"]]
    cert["Gp"] = [[[Q(x) for x in row] for row in Mx] for Mx in raw["Gp"]]
    lam = {}
    for key, val in raw["lam"].items():
        mono = tuple(int(t) for t in key.split(",")) if key else ()
        lam[mono] = Q(val)
    cert["lam"] = lam
    return cert


def main(path):
    print("=" * 74)
    print("STANDALONE verification of the sub-Dittert certificate")
    print("(standard library only; shares no code with the pipeline)")
    print("=" * 74)
    cert = load(path)
    n, k, N = cert["n"], cert["k"], cert["N"]
    print(f"certificate: (n,k) = ({n},{k}), {N} variables, "
          f"Gram size {len(cert['G0'])}")

    passed = []

    # ---- 1. sigma_k by two structurally different algorithms
    trials = [
        [[Q(i * 3 + j * 5 + 1, 7) for j in range(n)] for i in range(n)],
        [[Q(1, n) for _ in range(n)] for _ in range(n)],
        [[Q((i + 1) * (j + 2), 11) for j in range(n)] for i in range(n)],
        [[Q(1 if i == j else 0) for j in range(n)] for i in range(n)],
    ]
    ok = all(direct_sigma_k(A, n, k) == ryser_sigma_k(A, n, k) for A in trials)
    print(f"[1] sigma_k: direct subpermanent enumeration vs Ryser on "
          f"per(A+xJ), {len(trials)} matrices: {'AGREE' if ok else 'DISAGREE'}")
    passed.append(("sigma_k two algorithms", ok))

    # ---- 2. the bound
    Mexp = Q(2) - Q(factorial(k), n ** k)
    ok = (cert["M"] == Mexp)
    print(f"[2] bound M in the file = {cert['M']}, "
          f"2 - {k}!/{n}^{k} = {Mexp}: {'MATCH' if ok else 'MISMATCH'}")
    passed.append(("bound value", ok))

    # ---- 3. the identity, full coefficient comparison
    Fpoly, M2, sig = build_F(n, k)
    assert M2 == Mexp
    rhs = certificate_polynomial(cert)
    Fclean = {m: c for m, c in Fpoly.items() if c}
    ok = (rhs == Fclean)
    if not ok:
        keys = set(rhs) | set(Fclean)
        bad = [m for m in keys if rhs.get(m, Q(0)) != Fclean.get(m, Q(0))]
        print(f"    {len(bad)} differing monomials, e.g. {bad[:3]}")
    print(f"[3] identity by FULL coefficient comparison over Q: "
          f"certificate {len(rhs)} monomials, F {len(Fclean)} monomials -> "
          f"{'IDENTICAL' if ok else '*** MISMATCH ***'}")
    passed.append(("polynomial identity", ok))

    # ---- 4. positive definiteness by exact rational LDL^T
    allsym = symmetric(cert["G0"]) and all(symmetric(M) for M in cert["Gp"])
    pd0, info0 = ldl_positive_definite(cert["G0"])
    pdp = []
    for p in range(N):
        pdp.append(ldl_positive_definite(cert["Gp"][p]))
    ok = allsym and pd0 and all(a for a, _ in pdp)
    print(f"[4] exact rational LDL^T:")
    print(f"    all {1 + N} Gram matrices symmetric: {allsym}")
    print(f"    G0 positive definite: {pd0}, min pivot "
          f"{float(info0):.6e}" if pd0 else f"    G0 FAILED at pivot {info0}")
    minp = min(v for a, v in pdp if a) if all(a for a, _ in pdp) else None
    print(f"    all {N} multiplier Grams positive definite: "
          f"{all(a for a, _ in pdp)}"
          + (f", min pivot {float(minp):.6e}" if minp is not None else ""))
    passed.append(("positive definiteness", ok))

    # ---- 5. mutation tests
    print(f"[5] mutation tests (each MUST be rejected)")
    muts = []

    c2 = dict(cert)
    G = [row[:] for row in cert["G0"]]
    G[0][0] = G[0][0] + Q(1, 10 ** 20)
    c2["G0"] = G
    muts.append(("G0[0][0] += 1e-20", certificate_polynomial(c2) == Fclean))

    c3 = dict(cert)
    Gps = [[row[:] for row in Mx] for Mx in cert["Gp"]]
    Gps[0][1][1] = Gps[0][1][1] + Q(1, 10 ** 20)
    c3["Gp"] = Gps
    muts.append(("Gp[0][1][1] += 1e-20", certificate_polynomial(c3) == Fclean))

    c4 = dict(cert)
    lam2 = dict(cert["lam"])
    kk = next(iter(lam2))
    lam2[kk] = lam2[kk] + Q(1, 10 ** 20)
    c4["lam"] = lam2
    muts.append(("one lambda coefficient += 1e-20",
                 certificate_polynomial(c4) == Fclean))

    # a mutation that must also break DEFINITENESS, not just the identity
    Gneg = [row[:] for row in cert["G0"]]
    Gneg[0][0] = Q(-1)
    okneg, _ = ldl_positive_definite(Gneg)
    muts.append(("G0[0][0] := -1 must lose definiteness", okneg))

    for name, accepted in muts:
        print(f"    {name}: "
              f"{'REJECTED (good)' if not accepted else '*** ACCEPTED (BAD)'}")
    ok = not any(a for _, a in muts)
    passed.append(("mutation tests reject", ok))

    # ---- 6. the equality point
    zero = {(): Q(0)}
    val = sum(c for m, c in Fpoly.items() if not m)
    ok = (val == 0)
    print(f"[6] F(0) = {val} (equality is attained at J_n/n): "
          f"{'OK' if ok else 'BAD'}")
    passed.append(("equality at the barycentre", ok))

    print()
    allok = all(o for _, o in passed)
    for name, o in passed:
        print(f"  {'PASS' if o else 'FAIL'}  {name}")
    print()
    if allok:
        print("=" * 74)
        print(f"VERIFIED.  For every A in K_{n}:")
        print(f"    E_{k}(r) + E_{k}(c) - P_{k}(A)  <=  {cert['M']}"
              f"  = 2 - {k}!/{n}^{k}")
        print(f"with equality if and only if A = J_{n}/{n}.")
        print("=" * 74)
    else:
        print("*** VERIFICATION FAILED ***")
    return 0 if allok else 1


if __name__ == "__main__":
    here = os.path.dirname(os.path.abspath(__file__))
    default = os.path.join(here, "subdittert_n4k3d1_certificate.json")
    sys.exit(main(sys.argv[1] if len(sys.argv) > 1 else default))
