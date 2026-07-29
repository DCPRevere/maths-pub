"""
THE decisive first test for route H of NOTES section 10: scaling monotonicity.

Route H in one line.  Cheon-Wanless 2007 Theorem 4.2 is a THEOREM for every
2 <= k <= n: on the Birkhoff polytope Omega_n, Phi_k is maximised uniquely at
J_n/n (they get it from Friedland 1982 for their phi^1 and phi^3).  By
Sinkhorn-Knopp every A >= 0 with total support factors as A = D_u B D_v with B
doubly stochastic and u, v > 0.  So the whole conjecture, for every k at once,
follows from ONE new lemma:

    (S2)   Phi_k(D_u B D_v) <= Phi_k(B)      B in Omega_n, D_u B D_v in K_n.

This script attacks (S2) and its weaker one-sided relatives:

    (S)    Phi_k(D_r^{-1} A) >= Phi_k(A)     one Sinkhorn row step, A in K_n
    (S0)   Phi_k(D_u B) <= Phi_k(B)          B in Omega_n, sum u_i = n
    (S2)   as above

(S0) is the TIGHT sub-family: one row step takes D_u B back to B exactly, and
u = 1 gives equality, so this is where (S) is sharpest.  A violation anywhere
kills the route; the witness is then the deliverable.

Also tested:
    (Q)    the quantitative form of (S0): the deficit is at least
           lambda_2/(2n) * sum_i (u_i - 1)^2, with lambda_2 the closed-form
           line-sum Hessian eigenvalue of allk_hessian.py.
    (C')   sigma_k(A) >= (k!/n^k) e_k(r) e_k(c), the multiplicative extension of
           Friedland that would imply the conjecture through part C of
           allk_routes.py.  Expected FALSE; the witness is recorded.

Standard library only, Fraction throughout, no float in any decision.

Usage:  ./guard.sh python3 allk_scaling.py
"""

import random
from fractions import Fraction as Fr
from itertools import combinations, permutations
from math import comb, factorial

# --------------------------------------------------------------- primitives


def elem_sym(vec, k):
    e = [Fr(0)] * (k + 1)
    e[0] = Fr(1)
    for x in vec:
        for j in range(min(k, len(vec)), 0, -1):
            e[j] += e[j - 1] * x
    return e[k]


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


def rows_cols(A):
    n = len(A)
    return ([sum(A[i][j] for j in range(n)) for i in range(n)],
            [sum(A[i][j] for i in range(n)) for j in range(n)])


def Phi(A, k):
    n = len(A)
    N = Fr(comb(n, k))
    r, c = rows_cols(A)
    return elem_sym(r, k) / N + elem_sym(c, k) / N - sigma_k(A, k) / (N * N)


def gamma(n, k):
    return Fr(factorial(k), n ** k)


def lam2(n, k):
    kappa = Fr(k * (k - 1), n * (n - 1))
    return kappa * (n - Fr(factorial(k), n ** (k - 1)))


def total(A):
    return sum(x for row in A for x in row)


# ------------------------------------------------------------------- builders


def rand_Omega(n, rng, terms=3):
    perms = []
    for _ in range(terms):
        p = list(range(n))
        rng.shuffle(p)
        perms.append(p)
    w = [rng.randint(1, 5) for _ in range(terms)]
    tot = sum(w)
    A = [[Fr(0)] * n for _ in range(n)]
    for p, wt in zip(perms, w):
        for i in range(n):
            A[i][p[i]] += Fr(wt, tot)
    return A


def omega_menu(n, rng):
    """Doubly stochastic matrices: J, permutations, mixtures, sparse ones."""
    out = [("J/n", [[Fr(1, n)] * n for _ in range(n)])]
    P = [[Fr(1) if j == i else Fr(0) for j in range(n)] for i in range(n)]
    out.append(("I", P))
    Q = [[Fr(1) if j == (i + 1) % n else Fr(0) for j in range(n)] for i in range(n)]
    out.append(("cycle", Q))
    out.append(("(I+cycle)/2", [[(P[i][j] + Q[i][j]) / 2 for j in range(n)]
                               for i in range(n)]))
    out.append(("(J/n+I)/2", [[(Fr(1, n) + P[i][j]) / 2 for j in range(n)]
                              for i in range(n)]))
    out.append(("near J", [[Fr(1, n) + (P[i][j] - Fr(1, n)) / 10
                            for j in range(n)] for i in range(n)]))
    for t in range(10):
        out.append((f"rand{t}", rand_Omega(n, rng, terms=2 + (t % 4))))
    return out


def scaling_menu(n, rng, sumto):
    """Positive u with sum_i u_i = sumto (for S0) or arbitrary positive (S2)."""
    out = []
    out.append(("u=1", [Fr(1)] * n))
    for eps in (Fr(1, 100), Fr(1, 10), Fr(1, 2), Fr(9, 10)):
        u = [Fr(1)] * n
        u[0] += eps
        u[1] -= eps
        out.append((f"pair eps={eps}", u))
    for eps in (Fr(1, 10), Fr(1, 2)):
        u = [Fr(1) - eps] * n
        u[0] = Fr(1) + (n - 1) * eps
        out.append((f"spike eps={eps}", u))
    u = [Fr(2 * (i + 1), n + 1) for i in range(n)]
    s = sum(u)
    out.append(("ramp", [x * n / s for x in u]))
    for t in range(8):
        v = [Fr(rng.randint(1, 40), 10) for _ in range(n)]
        s = sum(v)
        out.append((f"rand{t}", [x * n / s for x in v]))
    # rescale everything so that sum u_i = sumto
    fixed = []
    for name, u in out:
        s = sum(u)
        fixed.append((name, [x * Fr(sumto) / s for x in u]))
    return fixed


def scale(B, u, v):
    n = len(B)
    return [[u[i] * B[i][j] * v[j] for j in range(n)] for i in range(n)]


# ------------------------------------------------------------------ PART S0/Q


def part_S0(rng):
    print("PART S0 + Q.  Phi_k(D_u B) <= Phi_k(B) for B doubly stochastic,")
    print("  sum_i u_i = n.  This is the TIGHT sub-family of the route (u = 1 is")
    print("  equality).  Q adds the conjectured quantitative deficit.")
    print()
    viol = []
    qviol = []
    tested = 0
    worst_q = None
    for n in (4, 5, 6):
        for bname, B in omega_menu(n, rng):
            for uname, u in scaling_menu(n, rng, n):
                A = scale(B, u, [Fr(1)] * n)
                assert total(A) == n, (bname, uname, total(A))
                dev = sum((x - 1) ** 2 for x in u)
                for k in range(2, n + 1):
                    tested += 1
                    d = Phi(B, k) - Phi(A, k)
                    if d < 0:
                        viol.append((n, k, bname, uname, d))
                    if dev > 0:
                        q = d - lam2(n, k) * dev / (2 * n)
                        if q < 0:
                            qviol.append((n, k, bname, uname, q))
                        ratio = d / (lam2(n, k) * dev / (2 * n))
                        if worst_q is None or ratio < worst_q[0]:
                            worst_q = (ratio, n, k, bname, uname)
    print(f"  S0: {tested} (B, u, k) triples tested, {len(viol)} violations.")
    if viol:
        w = min(viol, key=lambda x: x[4])
        print(f"  WORST S0: n={w[0]} k={w[1]} B={w[2]} u={w[3]} deficit"
              f" {float(w[4]):.6e}")
    print(f"  Q : {len(qviol)} violations of the quantitative form.")
    if worst_q:
        print(f"  Q tightest ratio {float(worst_q[0]):.4f} at n={worst_q[1]}"
              f" k={worst_q[2]} B={worst_q[3]} u={worst_q[4]}")
    if qviol:
        w = min(qviol, key=lambda x: x[4])
        print(f"  WORST Q: n={w[0]} k={w[1]} B={w[2]} u={w[3]} shortfall"
              f" {float(w[4]):.6e}")
    print()
    return viol, qviol


# -------------------------------------------------------------------- PART S2


def part_S2(rng):
    print("PART S2.  Phi_k(D_u B D_v) <= Phi_k(B), B doubly stochastic, both")
    print("  diagonals free, normalised so that D_u B D_v lies in K_n.")
    print("  If this holds, Sinkhorn-Knopp plus Cheon-Wanless Thm 4.2 finish the")
    print("  conjecture for EVERY k in one step.")
    print()
    viol = []
    tested = 0
    for n in (4, 5, 6):
        for bname, B in omega_menu(n, rng):
            us = scaling_menu(n, rng, n)
            vs = scaling_menu(n, rng, n)
            for ui, (uname, u) in enumerate(us):
                for vi, (vname, v) in enumerate(vs):
                    if (ui + 3 * vi) % 4:          # thin the product grid
                        continue
                    M = scale(B, u, v)
                    s = total(M)
                    if s == 0:
                        continue
                    f = Fr(n) / s
                    # spread the normalisation over u to keep the shape
                    A = [[x * f for x in row] for row in M]
                    assert total(A) == n
                    for k in range(2, n + 1):
                        tested += 1
                        d = Phi(B, k) - Phi(A, k)
                        if d < 0:
                            viol.append((n, k, bname, uname, vname, d, A))
    print(f"  S2: {tested} (B, u, v, k) tuples tested, {len(viol)} violations.")
    if viol:
        w = min(viol, key=lambda x: x[5])
        print(f"  WORST S2: n={w[0]} k={w[1]} B={w[2]} u={w[3]} v={w[4]}"
              f"  deficit {float(w[5]):.6e}")
        for row in w[6]:
            print("   ", [str(x) for x in row])
    print()
    return viol


# --------------------------------------------------------------------- PART S


def part_S(rng):
    print("PART S.  One Sinkhorn ROW step on a general point of K_n:")
    print("  Phi_k(D_r^{-1} A) >= Phi_k(A).  Includes sparse A, where the")
    print("  affine projection of allk_routes.py part A leaves the cone.")
    print()
    viol = []
    tested = 0
    skipped = 0
    for n in (4, 5):
        for t in range(120 if n == 4 else 60):
            z = [0.0, 0.2, 0.4, 0.6][t % 4]
            while True:
                M = [[0 if rng.random() < z else rng.randint(0, 9)
                      for _ in range(n)] for _ in range(n)]
                tot = sum(sum(row) for row in M)
                if tot > 0:
                    break
            A = [[Fr(n * M[i][j], tot) for j in range(n)] for i in range(n)]
            r, _ = rows_cols(A)
            if any(x == 0 for x in r):
                skipped += 1
                continue
            A2 = [[A[i][j] / r[i] for j in range(n)] for i in range(n)]
            assert total(A2) == n
            for k in range(2, n + 1):
                tested += 1
                d = Phi(A2, k) - Phi(A, k)
                if d < 0:
                    viol.append((n, k, d, A))
    print(f"  S: {tested} (A, k) pairs tested, {skipped} skipped (a zero row),"
          f" {len(viol)} violations.")
    if viol:
        w = min(viol, key=lambda x: x[2])
        print(f"  WORST S: n={w[0]} k={w[1]} deficit {float(w[2]):.6e}")
        for row in w[3]:
            print("   ", [str(x) for x in row])
    print()
    return viol


# -------------------------------------------------------------------- PART C'


def part_Cprime():
    print("PART C'.  sigma_k(A) >= (k!/n^k) e_k(r) e_k(c) on K_n -- the")
    print("  multiplicative extension of Friedland.  It would imply part C of")
    print("  allk_routes.py and hence the conjecture.  Scale-free form:")
    print("      per(A) * (sum a_ij)^n >= n! * prod r_i * prod c_j   at k = n.")
    print()
    A = [[Fr(4), Fr(1)], [Fr(1), Fr(0)]]
    n, k = 2, 2
    r, c = rows_cols(A)
    lhs = sigma_k(A, k) * total(A) ** n
    rhs = Fr(factorial(n)) * (r[0] * r[1]) * (c[0] * c[1])
    print(f"  witness A = [[4,1],[1,0]]:  per(A) = {sigma_k(A, 2)},  s = {total(A)}")
    print(f"    LHS = per * s^2 = {lhs}      RHS = 2! * prod r * prod c = {rhs}")
    print(f"    LHS - RHS = {lhs - rhs}   ->  C' is FALSE.  [V]")
    # and in K_n coordinates
    An = [[x * Fr(2, 6) for x in row] for row in A]
    r2, c2 = rows_cols(An)
    N = Fr(comb(2, 2))
    lhs2 = sigma_k(An, 2) / (N * N)
    rhs2 = gamma(2, 2) * elem_sym(r2, 2) / N * elem_sym(c2, 2) / N
    print(f"  normalised to K_2:  P_2 = {lhs2}, gamma*E_2(r)*E_2(c) = {rhs2},"
          f" gap {lhs2 - rhs2}")
    # confirm the conjecture and claim C still hold at this point
    print(f"  at the same point:  Phi_2 = {Phi(An, 2)} <= {2 - gamma(2, 2)}"
          f" = 2 - gamma  (conjecture holds)")
    lhsC = 1 - elem_sym(r2, 2) / N + lhs2
    rhsC = gamma(2, 2) * elem_sym(c2, 2) / N
    print(f"  claim C at the same point: {lhsC} >= {rhsC}  -> {lhsC >= rhsC}")
    print()
    return lhs - rhs


def main():
    rng = random.Random(20260729)
    print("allk_scaling.py -- route H (scaling monotonicity), decisive first test")
    print()
    v0, q0 = part_S0(rng)
    v2 = part_S2(rng)
    vs = part_S(rng)
    part_Cprime()
    print("SUMMARY")
    print(f"  S0 tight family      : {'FALSIFIED' if v0 else 'SURVIVED'}")
    print(f"  Q  quantitative S0   : {'FALSIFIED' if q0 else 'SURVIVED'}")
    print(f"  S2 two-sided scaling : {'FALSIFIED' if v2 else 'SURVIVED'}")
    print(f"  S  one Sinkhorn step : {'FALSIFIED' if vs else 'SURVIVED'}")
    print("  C' multiplicative    : FALSIFIED (exact witness above)")


if __name__ == "__main__":
    main()
