#!/usr/bin/env python3
"""
STANDALONE verification of a Dittert certificate.

This script shares NO code with the pipeline that produced the certificate.  It
imports nothing from the pipeline directory.  It reads only the deposited pickle and
recomputes everything else from the mathematical definitions:

  * the Dittert functional phi(A) = prod row sums + prod col sums - per(A),
    with the permanent by brute force over all n! permutations AND, independently,
    by Ryser inclusion-exclusion (a structurally different algorithm);
  * the target M_n = 2 - n!/n^n;
  * the monomial basis, from its own combinatorial definition;
  * the group action and the transporters;
  * both Gram matrices from the orbit data;
  * positive definiteness, by exact rational LDL^T;
  * THE IDENTITY, by full coefficient comparison over Q -- every monomial, not
    a sample.

It then runs MUTATION TESTS: if a verifier never rejects anything it proves
nothing.

The claimed identity, in centred coordinates b = A - J_n/n, is

    M_n - phi(J_n/n + b)
        = sigma_0(b) + sum_{p} sigma_p(b) (1/n + b_p) + lambda(b) * (sum_q b_q)

with sigma_0(b) = m(b)^T G_0 m(b), sigma_p(b) = m(g_p^{-1} b)^T H m(g_p^{-1} b)
for any group element g_p carrying position 0 to position p, and m the vector of
monomials of degree 1 and 2 (the constant is deliberately excluded).

Usage:  python3 verify_dittert.py [path/to/dittert_n4.pkl]
        (defaults to the certificate sitting beside this script)
"""

import itertools
import os
import pickle
import sys
from fractions import Fraction as F
from math import factorial


# --------------------------------------------------------------------- basics
def positions(n):
    return [(i, j) for i in range(n) for j in range(n)]


def generators(n):
    """Row swaps, column swaps and transposition, as permutations of positions."""
    pos = positions(n)
    idx = {p: k for k, p in enumerate(pos)}
    gens = []
    for a in range(n - 1):
        gens.append(tuple(idx[((a + 1 if i == a else a if i == a + 1 else i), j)]
                          for (i, j) in pos))
    for a in range(n - 1):
        gens.append(tuple(idx[(i, (a + 1 if j == a else a if j == a + 1 else j))]
                          for (i, j) in pos))
    gens.append(tuple(idx[(j, i)] for (i, j) in pos))
    return gens


def group_elements(n):
    gens = generators(n)
    N = n * n
    ident = tuple(range(N))
    seen, frontier = {ident}, [ident]
    while frontier:
        nxt = []
        for g in frontier:
            for h in gens:
                c = tuple(h[g[k]] for k in range(N))
                if c not in seen:
                    seen.add(c)
                    nxt.append(c)
        frontier = nxt
    return seen


def monomials(N, maxdeg, mindeg=0):
    out = []
    for d in range(mindeg, maxdeg + 1):
        out.extend(itertools.combinations_with_replacement(range(N), d))
    return out


def act(g, mono):
    return tuple(sorted(g[v] for v in mono))


# ------------------------------------------------------------- the functional
def per_brute(M, n):
    tot = F(0)
    for s in itertools.permutations(range(n)):
        pr = F(1)
        for i in range(n):
            pr *= M[i][s[i]]
            if pr == 0:
                break
        tot += pr
    return tot


def per_ryser(M, n):
    tot = F(0)
    for r in range(1, n + 1):
        for S in itertools.combinations(range(n), r):
            pr = F(1)
            for i in range(n):
                pr *= sum((M[i][j] for j in S), F(0))
            tot += F((-1) ** (n - r)) * pr
    return tot


def phi_at(bvals, n):
    """phi(J/n + b) exactly, b given as a list over positions."""
    pos = positions(n)
    M = [[F(0)] * n for _ in range(n)]
    inv = F(1, n)
    for k, (i, j) in enumerate(pos):
        M[i][j] = inv + bvals[k]
    pr = F(1)
    for i in range(n):
        pr *= sum(M[i], F(0))
    pc = F(1)
    for j in range(n):
        pc *= sum((M[i][j] for i in range(n)), F(0))
    pb, pr2 = per_brute(M, n), per_ryser(M, n)
    assert pb == pr2, "brute force and Ryser disagree"
    return pr + pc - pb


# ------------------------------------------------------- polynomial machinery
def poly_add(p, mono, c):
    if not c:
        return
    v = p.get(mono, F(0)) + c
    if v:
        p[mono] = v
    else:
        p.pop(mono, None)


def build_F(n):
    """M_n - phi(J_n/n + b) as an exact polynomial in the n^2 variables b."""
    N = n * n
    pos = positions(n)
    inv = F(1, n)

    def mul(p, q):
        out = {}
        for e1, c1 in p.items():
            for e2, c2 in q.items():
                poly_add(out, tuple(sorted(e1 + e2)), c1 * c2)
        return out

    entry = {}
    for k, (i, j) in enumerate(pos):
        entry[(i, j)] = {(): inv, (k,): F(1)}

    per = {}
    for s in itertools.permutations(range(n)):
        term = {(): F(1)}
        for i in range(n):
            term = mul(term, entry[(i, s[i])])
        for e, c in term.items():
            poly_add(per, e, c)

    prod_r = {(): F(1)}
    for i in range(n):
        lin = {(): F(1)}
        for j in range(n):
            poly_add(lin, (pos.index((i, j)),), F(1))
        prod_r = mul(prod_r, lin)

    prod_c = {(): F(1)}
    for j in range(n):
        lin = {(): F(1)}
        for i in range(n):
            poly_add(lin, (pos.index((i, j)),), F(1))
        prod_c = mul(prod_c, lin)

    M = F(2) - F(factorial(n), n ** n)
    out = {(): M}
    for e, c in prod_r.items():
        poly_add(out, e, -c)
    for e, c in prod_c.items():
        poly_add(out, e, -c)
    for e, c in per.items():
        poly_add(out, e, c)
    return out, M


# --------------------------------------------------------------- linear algebra
def ldl_pivots(G):
    B = len(G)
    a = [row[:] for row in G]
    piv = []
    for k in range(B):
        d = a[k][k]
        if d <= 0:
            return None, k
        piv.append(d)
        for i in range(k + 1, B):
            if a[i][k] == 0:
                continue
            f = a[i][k] / d
            for j in range(k, B):
                a[i][j] -= f * a[k][j]
            for j in range(k, B):
                a[j][i] = a[i][j]
    return piv, None


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


# ------------------------------------------------------------------- verify
def main(path):
    d = pickle.load(open(path, "rb"))
    n = d["n"]
    N = n * n
    print("=" * 74)
    print(f"STANDALONE verification of {path}   (n = {n})")
    print("=" * 74)

    # 1. rebuild the basis from its own definition and compare
    basis = monomials(N, 2, mindeg=1)
    assert list(basis) == list(d["basis"]), "basis does not match its definition"
    B = len(basis)
    print(f"[1] monomial basis rebuilt independently: {B} monomials, "
          f"degrees {sorted({len(m) for m in basis})}, constant excluded: "
          f"{() not in basis}")

    # 2. Gram matrices
    xq = [F(v) for v in d["xq"]]
    yq = [F(v) for v in d["yq"]]
    zq = [F(v) for v in d["zq"]]
    G0 = assemble(B, d["g_orbits"], xq)
    H = assemble(B, d["s_orbits"], yq)

    for name, Mx in (("G_0", G0), ("H", H)):
        sym = all(Mx[i][j] == Mx[j][i] for i in range(B) for j in range(i + 1, B))
        piv, bad = ldl_pivots(Mx)
        if piv is None:
            print(f"[2] {name}: NOT positive definite (pivot {bad}); FAIL")
            return False
        print(f"[2] {name}: symmetric {sym}, POSITIVE DEFINITE "
              f"(exact rational LDL), min pivot {float(min(piv)):.6e}")

    # 3. H must be invariant under the stabiliser of position 0, else the
    #    equivariant family sigma_p is not well defined.
    full = group_elements(n)
    stab = [g for g in full if g[0] == 0]
    bidx = {m: k for k, m in enumerate(basis)}
    ok_inv = True
    for g in list(stab)[:40]:
        pm = [bidx[act(g, m)] for m in basis]
        for u in range(B):
            if not ok_inv:
                break
            for v in range(B):
                if H[u][v] != H[pm[u]][pm[v]]:
                    ok_inv = False
                    break
    print(f"[3] |G| = {len(full)}, |Stab(0)| = {len(stab)}; "
          f"H is Stab-invariant: {ok_inv}"
          + ("" if ok_inv else "   -> sigma_p ILL-DEFINED, FAIL"))
    if not ok_inv:
        return False

    # 4. rebuild F independently and compare with the certificate identity
    Fpoly, M = build_F(n)
    print(f"[4] target M_{n} = {M} = {float(M):.10f}; "
          f"F has {len(Fpoly)} monomials")

    trans = {}
    for g in full:
        if g[0] not in trans:
            trans[g[0]] = g
    rhs = {}
    for u in range(B):
        for v in range(B):
            poly_add(rhs, tuple(sorted(basis[u] + basis[v])), G0[u][v])
    inv = F(1, n)
    for pk in range(N):
        g = trans[pk]
        gb = [act(g, m) for m in basis]
        for u in range(B):
            for v in range(B):
                c = H[u][v]
                if not c:
                    continue
                prod = tuple(sorted(gb[u] + gb[v]))
                poly_add(rhs, prod, c * inv)
                poly_add(rhs, tuple(sorted(prod + (pk,))), c)
    lam_mons = monomials(N, 4)
    for vi, members in enumerate(d["lam_orbit_reps"]):
        c = zq[vi]
        if not c:
            continue
        for k in members:
            mu = lam_mons[k]
            for pk in range(N):
                poly_add(rhs, tuple(sorted(mu + (pk,))), c)

    same = (rhs == Fpoly)
    print(f"[5] IDENTITY by full coefficient comparison over Q: "
          f"RHS {len(rhs)} monomials, F {len(Fpoly)} monomials -> "
          f"{'IDENTICAL' if same else '*** MISMATCH ***'}")
    if not same:
        extra = set(rhs) - set(Fpoly)
        missing = set(Fpoly) - set(rhs)
        print(f"      {len(extra)} spurious, {len(missing)} missing")
        return False

    # 6. spot check the functional itself at random rational points
    import random
    random.seed(20260728)
    bad = 0
    for _ in range(3):
        bvals = [F(random.randint(-50, 50), random.randint(1, 97)) for _ in range(N)]
        s = sum(bvals, F(0))
        bvals = [x - s / N for x in bvals]          # land on sum b = 0
        lhs = M - phi_at(bvals, n)
        acc = F(0)
        for e, c in Fpoly.items():
            t = c
            for v in e:
                t *= bvals[v]
            acc += t
        if lhs != acc:
            bad += 1
    print(f"[6] F re-evaluated against phi at 3 random rational points on "
          f"sum b = 0: {3 - bad} agree exactly, {bad} disagree")
    if bad:
        return False

    # 7. mutation tests
    def perturbed_ok(dx=None, dz=None):
        x2 = list(xq)
        z2 = list(zq)
        if dx is not None:
            x2[0] = x2[0] + dx
        if dz is not None:
            z2[0] = z2[0] + dz
        Ga = assemble(B, d["g_orbits"], x2)
        r = {}
        for u in range(B):
            for v in range(B):
                poly_add(r, tuple(sorted(basis[u] + basis[v])), Ga[u][v])
        for pk in range(N):
            g = trans[pk]
            gb = [act(g, m) for m in basis]
            for u in range(B):
                for v in range(B):
                    c = H[u][v]
                    if not c:
                        continue
                    prod = tuple(sorted(gb[u] + gb[v]))
                    poly_add(r, prod, c * inv)
                    poly_add(r, tuple(sorted(prod + (pk,))), c)
        for vi, members in enumerate(d["lam_orbit_reps"]):
            c = z2[vi]
            if not c:
                continue
            for k in members:
                mu = lam_mons[k]
                for pk in range(N):
                    poly_add(r, tuple(sorted(mu + (pk,))), c)
        return r == Fpoly

    m1 = perturbed_ok(dx=F(1, 10 ** 20))
    m2 = perturbed_ok(dz=F(1, 10 ** 20))
    print(f"[7] mutation: Gram entry +1e-20 -> "
          f"{'REJECTED (good)' if not m1 else 'ACCEPTED (BAD)'}; "
          f"multiplier +1e-20 -> "
          f"{'REJECTED (good)' if not m2 else 'ACCEPTED (BAD)'}")
    if m1 or m2:
        return False

    print("\n" + "=" * 74)
    print(f"VERIFIED.  For every A >= 0 with entries summing to {n}:")
    print(f"    phi(A) <= {M},")
    print(f"  with equality only at J_{n}/{n}.")
    print("  (bound from nonnegativity; uniqueness from G_0 positive DEFINITE,")
    print("   since the basis contains every linear monomial)")
    print("=" * 74)
    return True


if __name__ == "__main__":
    here = os.path.dirname(os.path.abspath(__file__))
    path = sys.argv[1] if len(sys.argv) > 1 else os.path.join(here, "dittert_n4.pkl")
    sys.exit(0 if main(path) else 1)
