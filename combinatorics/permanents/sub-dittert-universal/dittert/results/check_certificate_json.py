"""
Reference implementation of Route A in CLAIM.md: verify a Dittert certificate
using ONLY the exported JSON.

This file deliberately imports nothing from this repository -- only the Python
standard library.  It exists to demonstrate that the JSON is self-sufficient, so a
verifier can discard it and write their own in any language.

    python3 check_certificate_json.py dittert_n5_certificate.json

Everything is exact: Fraction arithmetic throughout, no floating point anywhere.
"""

import itertools
import json
import sys
from fractions import Fraction as F
from math import factorial


# ---------------------------------------------------------------- polynomials
# A polynomial is a dict {monomial: coefficient} where a monomial is a sorted
# tuple of variable indices with repetition:  (0,3,3) means b_0 * b_3^2.

def padd(p, q, scale=1):
    for m, c in q.items():
        v = p.get(m, F(0)) + c * scale
        if v:
            p[m] = v
        else:
            p.pop(m, None)
    return p


def pmul(p, q):
    out = {}
    for m1, c1 in p.items():
        for m2, c2 in q.items():
            m = tuple(sorted(m1 + m2))
            v = out.get(m, F(0)) + c1 * c2
            if v:
                out[m] = v
            else:
                out.pop(m, None)
    return out


def linear(const, terms):
    """const + sum of terms, terms a list of variable indices with coefficient 1."""
    p = {(): F(const)} if const else {}
    for k in terms:
        p[(k,)] = p.get((k,), F(0)) + 1
    return p


# ------------------------------------------------------------------ build F
def build_F(n):
    """F(b) = M_n - phi(J_n + b), built from the DEFINITION of phi."""
    N = n * n
    M = F(2) - F(factorial(n), n ** n)

    # A[i][j] = 1/n + b_{i*n+j}
    def entry(i, j):
        return {(): F(1, n), (i * n + j,): F(1)}

    # product of row sums, product of column sums
    prod_r = {(): F(1)}
    for i in range(n):
        prod_r = pmul(prod_r, linear(1, [i * n + j for j in range(n)]))
    prod_c = {(): F(1)}
    for j in range(n):
        prod_c = pmul(prod_c, linear(1, [i * n + j for i in range(n)]))

    # permanent
    per = {}
    for s in itertools.permutations(range(n)):
        term = {(): F(1)}
        for i in range(n):
            term = pmul(term, entry(i, s[i]))
        padd(per, term)

    phi = {}
    padd(phi, prod_r)
    padd(phi, prod_c)
    padd(phi, per, -1)

    Fpoly = {(): M}
    padd(Fpoly, phi, -1)
    return {m: c for m, c in Fpoly.items() if c}, M


# ------------------------------------------------------------------- exact LDL
def is_positive_definite(tri, B):
    """Exact rational LDL^T on a symmetric matrix given by its upper triangle."""
    a = [[F(0)] * B for _ in range(B)]
    for i, j, num, den in tri:
        a[i][j] = F(num, den)
        a[j][i] = F(num, den)
    for k in range(B):
        d = a[k][k]
        if d <= 0:
            return False, k, None
        for i in range(k + 1, B):
            if a[i][k] == 0:
                continue
            f = a[i][k] / d
            for j in range(k, B):
                a[i][j] -= f * a[k][j]
            for j in range(k, B):
                a[j][i] = a[i][j]
    return True, None, min(a[k][k] for k in range(B))


def to_matrix(tri, B):
    a = [[F(0)] * B for _ in range(B)]
    for i, j, num, den in tri:
        a[i][j] = F(num, den)
        a[j][i] = F(num, den)
    return a


def per_matrix(M, n):
    """Permanent by the definition: sum over all n! permutations."""
    tot = F(0)
    for s in itertools.permutations(range(n)):
        p = F(1)
        for i in range(n):
            p *= M[i][s[i]]
        tot += p
    return tot


def random_zero_sum(N, seed):
    """A deterministic rational vector with sum zero (no RNG dependence)."""
    vals = [F((seed * 37 + 11 * k) % 23 - 11, (k % 7) + 3) for k in range(N)]
    s = sum(vals, F(0))
    vals[0] -= s
    return vals


def monomial_value(m, b):
    v = F(1)
    for k in m:
        v *= b[k]
    return v


# ---------------------------------------------------------------------- main
def main(path):
    doc = json.load(open(path))
    n = doc["n"]
    N = n * n
    basis = [tuple(m) for m in doc["basis"]]
    B = len(basis)
    bound = F(*doc["bound"])
    print("=" * 74)
    print(f"JSON-ONLY verification of {path}  (n = {n})")
    print("=" * 74)
    print(f"[0] claim: {doc['claim']}")

    # 1. basis sanity: degrees 1 and 2, constant absent, all linear monomials present
    degs = sorted({len(m) for m in basis})
    lin = {m for m in basis if len(m) == 1}
    print(f"[1] basis: {B} monomials, degrees {degs}, constant present: "
          f"{() in basis}, all {N} linear monomials present: "
          f"{len(lin) == N}")
    if () in basis or degs != [1, 2] or len(lin) != N:
        print("    FAIL: basis is not as the argument requires")
        return False

    # 2. positive definiteness, exactly
    for name in ("G0", "H"):
        ok, bad, minpiv = is_positive_definite(doc[name], B)
        if not ok:
            print(f"[2] {name}: NOT positive definite (pivot {bad}) -- FAIL")
            return False
        print(f"[2] {name}: POSITIVE DEFINITE (exact rational LDL), "
              f"min pivot {float(minpiv):.6e}")

    G0 = to_matrix(doc["G0"], B)
    H = to_matrix(doc["H"], B)
    trans = [list(g) for g in doc["transporters"]]

    # 3. H must be invariant under the stabiliser of position 0, else sigma_p is
    #    not well defined.  Test with every transporter fixing 0.
    bidx = {m: k for k, m in enumerate(basis)}

    def act(g, m):
        return tuple(sorted(g[v] for v in m))

    # Use the stabiliser GENERATORS, and close them up to the whole stabiliser.
    # Testing only the transporters would test essentially nothing: just one of
    # them fixes position 0.
    sgens = [list(g) for g in doc.get("stab_generators", [])]
    stab = {tuple(range(N))}
    frontier = [tuple(range(N))]
    while frontier:
        nxt = []
        for g in frontier:
            for h in sgens:
                c = tuple(h[g[k]] for k in range(N))
                if c not in stab:
                    stab.add(c)
                    nxt.append(c)
        frontier = nxt
    assert all(g[0] == 0 for g in stab), "closure left the stabiliser of 0"
    stab_ok = True
    for g in stab:
        pm = [bidx[act(g, m)] for m in basis]
        for u in range(B):
            if not stab_ok:
                break
            for v in range(B):
                if H[u][v] != H[pm[u]][pm[v]]:
                    stab_ok = False
                    break
        if not stab_ok:
            break
    # NOTE ON WHAT THIS DOES AND DOES NOT ESTABLISH.  Because the transporters are
    # given explicitly, each sigma_p is fully determined by H and its stated
    # transporter, and sigma_p is a sum of squares iff H is PSD -- invariance is
    # nowhere used in the deduction.  So this is a CONSISTENCY check (the family is
    # canonical, and a verifier who re-derives transporters differently will get the
    # same sigma_p), NOT a soundness check.  An earlier version of CLAIM.md wrongly
    # ranked it as a way the theorem could fail.
    print(f"[3] H invariant under the FULL stabiliser of position 0 "
          f"(|Stab| = {len(stab)}, from {len(sgens)} generators): {stab_ok}")
    print("    (consistency only -- soundness needs just H PSD, checked above)")
    if not stab_ok:
        print("    WARNING: certificate is not canonical, but the theorem is "
              "unaffected; continuing")

    # 4. rebuild F from the definition of phi
    Fpoly, M = build_F(n)
    print(f"[4] rebuilt F from phi: M_{n} = {M}, {len(Fpoly)} monomials"
          f"   bound matches JSON: {M == bound}")
    if M != bound:
        print("    FAIL: our M_n disagrees with the certificate's stated bound")
        return False

    # 5. expand the right-hand side of the identity
    rhs = {}
    for u in range(B):
        for v in range(B):
            c = G0[u][v]
            if c:
                m = tuple(sorted(basis[u] + basis[v]))
                rhs[m] = rhs.get(m, F(0)) + c
    inv = F(1, n)
    for p in range(N):
        g = trans[p]
        gb = [act(g, m) for m in basis]
        for u in range(B):
            for v in range(B):
                c = H[u][v]
                if not c:
                    continue
                m = tuple(sorted(gb[u] + gb[v]))
                rhs[m] = rhs.get(m, F(0)) + c * inv
                m2 = tuple(sorted(m + (p,)))
                rhs[m2] = rhs.get(m2, F(0)) + c
    for mono, num, den in doc["lam"]:
        c = F(num, den)
        for k in range(N):
            m = tuple(sorted(tuple(mono) + (k,)))
            rhs[m] = rhs.get(m, F(0)) + c
    touched = len(rhs)
    rhs = {m: c for m, c in rhs.items() if c}

    # Compare over the UNION of supports, not over F's support.  This is the
    # difference between "every coefficient of F is matched" and "RHS - F is
    # identically zero".  The RHS lives in a far bigger space than F's support:
    # every monomial of degree <= 5 in N variables.  Checking only F's support
    # would let a certificate with spurious high-degree terms pass.
    from math import comb
    ambient = comb(N + 5, 5) - 1
    diff = dict(Fpoly)
    for m, c in rhs.items():
        diff[m] = diff.get(m, F(0)) - c
    diff = {m: c for m, c in diff.items() if c}
    same = not diff

    print(f"[5] IDENTITY over Q, checked as RHS - F == 0 over the UNION of supports:")
    print(f"    ambient space (deg <= 5 in {N} vars, constant excluded): {ambient:,} monomials")
    print(f"    distinct monomials touched while expanding RHS: {touched:,}")
    print(f"    support(RHS) = {len(rhs):,}, support(F) = {len(Fpoly):,}, "
          f"nonzero coefficients of RHS - F = {len(diff)}")
    print(f"    -> {'IDENTICAL' if same else '*** MISMATCH ***'}")
    if not same:
        extra = set(rhs) - set(Fpoly)
        missing = set(Fpoly) - set(rhs)
        print(f"    {len(extra)} spurious, {len(missing)} missing")
        return False

    # 6. mutation tests.  The second is the one that matters: it injects a
    #    monomial OUTSIDE F's support, which is exactly what a support-only
    #    comparison would fail to notice.
    bad = dict(rhs)
    key = next(iter(bad))
    bad[key] += F(1, 10 ** 20)
    m1 = bad != Fpoly

    spurious = None
    for cand in itertools.combinations_with_replacement(range(N), 5):
        if cand not in Fpoly:
            spurious = cand
            break
    bad2 = dict(rhs)
    bad2[spurious] = F(1, 10 ** 20)
    m2 = bad2 != Fpoly
    print(f"[6] mutation, perturb an existing coefficient by 1e-20 -> "
          f"{'REJECTED (good)' if m1 else 'ACCEPTED (BAD)'}")
    print(f"    mutation, inject a SPURIOUS monomial {spurious} outside "
          f"support(F) -> {'REJECTED (good)' if m2 else 'ACCEPTED (BAD)'}")
    if not (m1 and m2):
        return False

    # 7. is our permanent right?  Test the permutation-sum expansion used by
    #    build_F against two published integer sequences, then check the
    #    assembled polynomial F against phi evaluated directly.
    ones = [[F(1)] * n for _ in range(n)]
    jmi = [[F(0) if i == j else F(1) for j in range(n)] for i in range(n)]
    der = round(factorial(n) / 2.718281828459045)          # nearest integer to n!/e
    ok_ones = per_matrix(ones, n) == factorial(n)
    ok_der = per_matrix(jmi, n) == der
    print(f"[7] permanent oracle: per(all ones) = {n}! -> {ok_ones}; "
          f"per(J-I) = derangements({n}) = {der} -> {ok_der}")
    if not (ok_ones and ok_der):
        return False

    agree = 0
    for trial in range(5):
        b = random_zero_sum(N, trial)
        lhs = sum((c * monomial_value(m, b) for m, c in Fpoly.items()), F(0))
        A = [[F(1, n) + b[i * n + j] for j in range(n)] for i in range(n)]
        rs = [sum(A[i], F(0)) for i in range(n)]
        cs = [sum((A[i][j] for i in range(n)), F(0)) for j in range(n)]
        pr, pc = F(1), F(1)
        for v in rs:
            pr *= v
        for v in cs:
            pc *= v
        phi = pr + pc - per_matrix(A, n)
        agree += (lhs == M - phi)
    print(f"    F re-evaluated against phi directly at 5 rational points: "
          f"{agree}/5 agree exactly")
    if agree != 5:
        return False

    print()
    print("=" * 74)
    print(f"VERIFIED from JSON alone.  For every real A >= 0 with entries "
          f"summing to {n}:")
    print(f"    prod(row sums) + prod(col sums) - per(A) <= {M},")
    print(f"  with equality only at the constant matrix J_{n}.")
    print("=" * 74)
    return True


if __name__ == "__main__":
    sys.exit(0 if main(sys.argv[1]) else 1)
