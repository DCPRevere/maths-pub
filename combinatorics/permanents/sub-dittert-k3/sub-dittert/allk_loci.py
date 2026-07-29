"""
The two reduction routes that survived random sampling, tested AT THEIR EQUALITY
LOCI, where alone they can fail; plus an in-repo re-derivation of the kills the
orphan scripts reported.

WHY THE EQUALITY LOCUS.  Both surviving claims are equalities on a positive-
dimensional set, and random sampling in K_n never approaches it.  A claim with an
equality locus fails first in a neighbourhood of that locus, at the lowest order
in which the expansion has a free sign.  So the test is: expand there, exactly.

PREDICTIONS, written before the run.

  ROUTE A  Phi_k(A) <= Phi_k(P A), P the orthogonal projection onto the doubly
    stochastic affine plane.  Equality locus: Omega_n itself.  Take A0 in Omega_n
    and B = u 1^T with sum u = 0; then P B = 0, so P(A0 + tB) = A0 for all t and
    the claim demands that t -> Phi_k(A0 + tB) have a local MAX at t = 0.  Its
    derivative is sum_i u_i rho_i with
        rho_i = 2k/n * n - (1/C(n,k)^2) sum_j sigma_{k-1}(A0(i|j)),
    which is non-constant in i for a generic A0.  PREDICTION: ROUTE A DIES at
    first order, with an exact rational witness.

  ROUTE C  Phi_k(A) <= Phi_k(1 c^T/n), c the column sums.  Equality locus: the
    whole rank-one family A = 1 c^T/n.  Note Phi_k(1 c^T/n) = 1 + (1-gamma)E_k(c)
    <= 2 - gamma by Maclaurin, so ROUTE C IMPLIES DITTERT IN ONE LINE and is a
    "trivial reading" -- the prior is that it is false.  At A0 = 1 c^T/n the
    gradient of Phi_k is  1 w^T  (row sums of A0 are all 1, and sigma_{k-1} of a
    minor of a rank-one matrix does not depend on the deleted row), so it is
    orthogonal to every doubly centred direction: the first order vanishes
    IDENTICALLY, for every c and every k.  PREDICTION: route C survives first
    order for that structural reason and the SECOND order decides; at k = 2 it is
    a theorem (proved in NOTES-ALLK), so any failure is at k >= 3 and at c far
    from 1.

Standard library only, Fraction throughout, no float in any decision.

Usage:  GUARD_MEM=4G ../guard.sh python3 allk_loci.py
"""

import random
from fractions import Fraction as Fr
from itertools import combinations, permutations
from math import comb, factorial

# --------------------------------------------------------------- primitives


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
    if k == 0:
        return Fr(1)
    if k > n:
        return Fr(0)
    tot = Fr(0)
    for R in combinations(range(n), k):
        for C in combinations(range(n), k):
            tot += per([[A[i][j] for j in C] for i in R])
    return tot


def lines(A):
    n = len(A)
    return ([sum(A[i][j] for j in range(n)) for i in range(n)],
            [sum(A[i][j] for i in range(n)) for j in range(n)])


def Phi(A, k):
    n = len(A)
    N = Fr(comb(n, k))
    r, c = lines(A)
    return elem_sym(r, k) / N + elem_sym(c, k) / N - sigma_k(A, k) / (N * N)


def gamma(n, k):
    return Fr(factorial(k), n ** k)


def poly_in_t(f, deg):
    """Exact monomial coefficients of the degree-<=deg polynomial t -> f(t)."""
    xs = [Fr(i) for i in range(deg + 1)]
    ys = [f(x) for x in xs]
    coeffs = [Fr(0)] * (deg + 1)
    for i in range(deg + 1):
        num = [Fr(1)]
        den = Fr(1)
        for j in range(deg + 1):
            if j == i:
                continue
            nxt = [Fr(0)] * (len(num) + 1)
            for a, cf in enumerate(num):
                nxt[a] += -xs[j] * cf
                nxt[a + 1] += cf
            num = nxt
            den *= xs[i] - xs[j]
        for d, cf in enumerate(num):
            coeffs[d] += ys[i] * cf / den
    return coeffs


def ldlt_signature(G):
    """Exact symmetric LDL^T with symmetric pivoting.  Returns the list of
    pivots; the form is negative semidefinite iff no pivot is > 0."""
    n = len(G)
    A = [row[:] for row in G]
    idx = list(range(n))
    piv = []
    for s in range(n):
        # pick the largest |diagonal| among the remaining
        best = max(range(s, n), key=lambda i: abs(A[i][i]))
        if A[best][best] == 0:
            # a zero diagonal with a nonzero off-diagonal in the block means the
            # form is indefinite on that 2x2; report it as a positive pivot.
            for i in range(s, n):
                for j in range(i + 1, n):
                    if A[i][j] != 0:
                        piv.append(("indefinite2x2", A[i][j]))
                        return piv
            break
        A[s], A[best] = A[best], A[s]
        for row in A:
            row[s], row[best] = row[best], row[s]
        idx[s], idx[best] = idx[best], idx[s]
        d = A[s][s]
        piv.append(d)
        for i in range(s + 1, n):
            f = A[i][s] / d
            if f == 0:
                continue
            for j in range(s, n):
                A[i][j] -= f * A[s][j]
            for j in range(s, n):
                A[j][i] = A[i][j]
    return piv


# --------------------------------------------------------------------- ROUTE A


def rand_omega(n, rng, terms=4):
    perms = []
    for _ in range(terms):
        p = list(range(n))
        rng.shuffle(p)
        perms.append(p)
    w = [rng.randint(1, 7) for _ in range(terms)]
    tot = sum(w)
    A = [[Fr(0)] * n for _ in range(n)]
    for p, wt in zip(perms, w):
        for i in range(n):
            A[i][p[i]] += Fr(wt, tot)
    return A


def minor(A, i, j):
    n = len(A)
    return [[A[a][b] for b in range(n) if b != j] for a in range(n) if a != i]


def route_A(rng):
    print("ROUTE A.  Phi_k(A) <= Phi_k(P A), tested transverse to Omega_n.")
    print()
    kills = []
    tested = 0
    flat = 0
    for n in (4, 5):
        for trial in range(30):
            # a convex combination of permutations is almost always on the
            # boundary of Omega_n; mixing in J/n makes it interior, which is
            # what the transverse perturbation needs, WITHOUT making it
            # symmetric enough to flatten rho.
            raw = rand_omega(n, rng, terms=3 + (trial % 3))
            A0 = [[(raw[i][j] * 3 + Fr(1, n)) / 4 for j in range(n)]
                  for i in range(n)]
            assert all(x > 0 for row in A0 for x in row)
            for k in range(2, n + 1):
                rho = [sum(sigma_k(minor(A0, i, j), k - 1) for j in range(n))
                       for i in range(n)]
                tested += 1
                if len(set(rho)) == 1:
                    flat += 1
                    continue                      # too symmetric to separate
                # u puts +1 on the largest rho_i and -1 on the smallest
                imax = max(range(n), key=lambda i: rho[i])
                imin = min(range(n), key=lambda i: rho[i])
                u = [Fr(0)] * n
                u[imax], u[imin] = Fr(1), Fr(-1)
                B = [[u[i] for _ in range(n)] for i in range(n)]
                # P B = 0 exactly: row sums n u_i, column sums 0, so the
                # projection subtracts (row mean) and adds nothing else
                # -- confirmed numerically below rather than assumed.
                eps = Fr(1, 64)
                for sgn in (Fr(1), Fr(-1)):
                    t = sgn * eps
                    A = [[A0[i][j] + t * B[i][j] for j in range(n)]
                         for i in range(n)]
                    if any(x < 0 for row in A for x in row):
                        continue
                    PA = _project(A)
                    if any(x != y for ra, rb in zip(PA, A0)
                           for x, y in zip(ra, rb)):
                        raise RuntimeError("P(A0 + tB) != A0")
                    d = Phi(PA, k) - Phi(A, k)
                    if d < 0:
                        kills.append((n, k, t, d, A0, u))
                        break
                if kills and kills[-1][0] == n and kills[-1][1] == k:
                    break
            if kills:
                break
        if kills:
            break
    print(f"  {tested} (A0, k) pairs reached the test; rho was constant in i in"
          f" {flat} of them.")
    if kills:
        n, k, t, d, A0, u = kills[0]
        print(f"  FALSIFIED at n={n} k={k}, t={t}:  Phi_k(P A) - Phi_k(A) = {d}")
        print(f"  u = {[str(x) for x in u]},  B = u 1^T,  P B = 0,  P A = A0.")
        print("  A0 (doubly stochastic, the equality point):")
        for row in A0:
            print("    ", [str(x) for x in row])
        print("  This is a first-order failure: the derivative of")
        print("  t -> Phi_k(A0 + t u 1^T) at 0 is nonzero, so one sign of t")
        print("  always violates.  ROUTE A IS DEAD.")
    else:
        print("  no violation found -- the first-order argument did NOT fire;")
        print("  route A is NOT killed by this test.")
    print()
    return kills


def _project(A):
    n = len(A)
    r, c = lines(A)
    return [[A[i][j] - (r[i] - 1) / Fr(n) - (c[j] - 1) / Fr(n)
             for j in range(n)] for i in range(n)]


# --------------------------------------------------------------------- ROUTE C


def dc_basis(n):
    """A basis of the doubly centred matrices, dimension (n-1)^2."""
    out = []
    for i in range(n - 1):
        for j in range(n - 1):
            B = [[Fr(0)] * n for _ in range(n)]
            B[i][j] = Fr(1)
            B[i][n - 1] = Fr(-1)
            B[n - 1][j] = Fr(-1)
            B[n - 1][n - 1] = Fr(1)
            out.append(B)
    return out


def quad_form_at_rank_one(n, k, c):
    """The Gram matrix of B -> [t^2] Phi_k(1 c^T/n + t B) on the doubly centred
    space.  Route C requires it to be negative SEMIdefinite."""
    A0 = [[c[j] / Fr(n) for j in range(n)] for _ in range(n)]
    basis = dc_basis(n)
    m = len(basis)

    def q(B):
        def f(t):
            A = [[A0[i][j] + t * B[i][j] for j in range(n)] for i in range(n)]
            return Phi(A, k)
        return poly_in_t(f, k)[2]

    diag = [q(B) for B in basis]
    G = [[Fr(0)] * m for _ in range(m)]
    for a in range(m):
        G[a][a] = diag[a]
    for a in range(m):
        for b in range(a + 1, m):
            Bs = [[basis[a][i][j] + basis[b][i][j] for j in range(n)]
                  for i in range(n)]
            G[a][b] = G[b][a] = (q(Bs) - diag[a] - diag[b]) / 2
    return G, basis


def route_C(rng):
    print("ROUTE C.  Phi_k(A) <= Phi_k(1 c^T/n), tested on the rank-one locus.")
    print()
    print("  First order, checked rather than assumed: the gradient of Phi_k at")
    print("  1 c^T/n is 1 w^T, hence orthogonal to every doubly centred B.")
    ok1 = True
    for n in (4, 5):
        for k in range(2, n + 1):
            c = [Fr(2 * (j + 1)) for j in range(n)]
            s = sum(c)
            c = [x * n / s for x in c]
            A0 = [[c[j] / Fr(n) for j in range(n)] for _ in range(n)]
            for B in dc_basis(n)[:4]:
                def f(t, B=B, A0=A0, n=n, k=k):
                    A = [[A0[i][j] + t * B[i][j] for j in range(n)]
                         for i in range(n)]
                    return Phi(A, k)
                if poly_in_t(f, k)[1] != 0:
                    ok1 = False
    print(f"      first-order term vanishes in every case tested: {ok1}")
    print()
    print("  Second order: the Gram of B -> [t^2] Phi_k on the doubly centred")
    print("  space must be negative semidefinite.  Exact LDL^T, no float.")
    print()
    print("     n   k   c (column sums)                    max pivot   verdict")
    fails = []
    cs = {}
    for n in (4, 5):
        base = []
        base.append(("uniform", [Fr(1)] * n))
        base.append(("ramp", None))
        base.append(("skew", None))
        base.append(("very skew", None))
        c1 = [Fr(2 * (j + 1)) for j in range(n)]
        c2 = [Fr(1)] + [Fr(1, 4)] * (n - 1)
        c3 = [Fr(1)] + [Fr(1, 40)] * (n - 1)
        for nm, cc in zip(("ramp", "skew", "very skew"), (c1, c2, c3)):
            s = sum(cc)
            cs.setdefault(n, []).append((nm, [x * n / s for x in cc]))
        cs[n].insert(0, ("uniform", [Fr(1)] * n))
        for t in range(4):
            v = [Fr(rng.randint(1, 30)) for _ in range(n)]
            s = sum(v)
            cs[n].append((f"rand{t}", [x * n / s for x in v]))
    for n in (4, 5):
        for k in range(2, n + 1):
            for nm, c in cs[n]:
                G, basis = quad_form_at_rank_one(n, k, c)
                piv = ldlt_signature(G)
                bad = [p for p in piv if not isinstance(p, tuple) and p > 0]
                worst = max([p for p in piv if not isinstance(p, tuple)],
                            default=Fr(0))
                verdict = "ok" if not bad and not any(
                    isinstance(p, tuple) for p in piv) else "POSITIVE PIVOT"
                cstr = ",".join(str(x) for x in c)
                if len(cstr) > 32:
                    cstr = cstr[:29] + "..."
                print(f"    {n:>3} {k:>3}   {cstr:<34s} {str(worst):>10s}"
                      f"   {verdict}")
                if verdict != "ok":
                    fails.append((n, k, nm, c, G, basis, piv))
    print()
    if fails:
        n, k, nm, c, G, basis, piv = fails[0]
        print(f"  ROUTE C IS DEAD.  n={n} k={k}, c = {[str(x) for x in c]}:")
        print("  the second-order form has a positive direction, so")
        print("  Phi_k(1 c^T/n + tB) > Phi_k(1 c^T/n) for small t in that")
        print("  direction, while the row-average is unchanged.")
    else:
        print("  NO violation of route C at second order anywhere tested.")
        print("  This is NOT evidence that route C is true -- it implies")
        print("  Dittert's conjecture in one line, so the prior is strongly")
        print("  against it, and the failure must then be at higher order or")
        print("  far from the rank-one locus.  Recorded as UNRESOLVED.")
    print()
    return fails


# ------------------------------------------------- provenance: in-repo re-kills


def route_H_rekill(rng):
    """Independently re-derive, with this file's own code, one exact witness for
    each of the three scaling claims the orphan allk_scaling.py reported dead.
    Nothing is taken from that script; the witnesses below are found here."""
    print("PROVENANCE.  Route H (Sinkhorn scaling) re-killed by this file's own")
    print("  code, with witnesses found here and not copied from the orphan.")
    print()
    out = {}

    # (S0) Phi_k(D_u B) <= Phi_k(B),  B doubly stochastic, sum u = n
    found = None
    for n in (4, 5):
        for _ in range(400):
            B = rand_omega(n, rng, terms=3)
            u = [Fr(1)] * n
            e = Fr(1, 20)
            i, j = rng.sample(range(n), 2)
            u[i] += e
            u[j] -= e
            A = [[u[a] * B[a][b] for b in range(n)] for a in range(n)]
            for k in range(2, n + 1):
                d = Phi(B, k) - Phi(A, k)
                if d < 0:
                    found = (n, k, d, B, u)
                    break
            if found:
                break
        if found:
            break
    out["S0"] = found
    if found:
        n, k, d, B, u = found
        print(f"  (S0) FALSIFIED n={n} k={k}: Phi_k(B) - Phi_k(D_u B) = {d} < 0")
        print(f"       u = {[str(x) for x in u]}")
        for row in B:
            print("       ", [str(x) for x in row])

    # (S) one Sinkhorn row step: Phi_k(D_r^{-1} A) >= Phi_k(A)
    found = None
    for n in (4, 5):
        for _ in range(600):
            M = [[rng.randint(0, 9) for _ in range(n)] for _ in range(n)]
            tot = sum(sum(r) for r in M)
            if tot == 0:
                continue
            A = [[Fr(n * M[a][b], tot) for b in range(n)] for a in range(n)]
            r, _ = lines(A)
            if any(x == 0 for x in r):
                continue
            A2 = [[A[a][b] / r[a] for b in range(n)] for a in range(n)]
            for k in range(2, n + 1):
                d = Phi(A2, k) - Phi(A, k)
                if d < 0:
                    found = (n, k, d, A)
                    break
            if found:
                break
        if found:
            break
    out["S"] = found
    if found:
        n, k, d, A = found
        print(f"  (S)  FALSIFIED n={n} k={k}: Phi_k(D_r^-1 A) - Phi_k(A)"
              f" = {d} < 0")
        for row in A:
            print("       ", [str(x) for x in row])
    print()
    print("  Both stand on code in this file alone.  Route H needs")
    print("  Phi_k(D_u B D_v) <= Phi_k(B) for every scaling; a single failure of")
    print("  the one-sided special case kills it.")
    print()
    return out


def main():
    rng = random.Random(20260729)
    print("allk_loci.py -- the surviving routes, tested where they can fail")
    print()
    a = route_A(rng)
    c = route_C(rng)
    h = route_H_rekill(rng)
    print("SUMMARY")
    print(f"  route A (affine projection): {'DEAD' if a else 'not killed'}")
    print(f"  route C (row averaging):     {'DEAD' if c else 'UNRESOLVED'}")
    print(f"  route H (Sinkhorn scaling):  "
          f"{'DEAD, re-derived in repo' if h.get('S0') or h.get('S') else '?'}")


if __name__ == "__main__":
    main()
