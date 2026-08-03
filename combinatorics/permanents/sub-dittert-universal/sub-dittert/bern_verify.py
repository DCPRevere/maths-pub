"""
GRADED VERIFIER for BERNSTEIN.md.  Exact rational arithmetic throughout; every
claim carries a MUTATION CONTROL that must be reported as caught.

    G1  the normalised Bernstein form                (identity, calibration)
    G2  Theorem R -- the k-reduction                 (structure)
    G3  Theorem D1 -- d_1 >= 0 on K_n, every (k,n)   (PROOF)
    G4  Theorem E -- the equality orbit (I+C)/2      (PROOF of the identity,
                                                      exact check of minimality)
    G5  the KILL -- exact witnesses for d_{n-1} < 0  (REFUTATION of (B))

Usage:  python3 bern_verify.py            (all grades)
        python3 bern_verify.py G3         (one grade)
Exit status 0 iff every grade passes and every mutant is caught.
"""

import sys
from fractions import Fraction as Q

import numpy as np

import bern_core as BC
import fals_core as fc
import reduce_scan as R

FAIL = []


def check(tag, cond, detail=""):
    if not cond:
        FAIL.append(tag)
    print(f"    [{'ok  ' if cond else 'FAIL'}] {tag}" + (f"   {detail}" if detail else ""))
    return cond


def caught(tag, cond, detail=""):
    """A mutation control: `cond` must be True, meaning the mutant WAS detected."""
    if not cond:
        FAIL.append("mutant-not-caught:" + tag)
    print(f"    [{'caught' if cond else 'MISSED'}] mutant {tag}"
          + (f"   {detail}" if detail else ""))
    return cond


def rat_points(n, rng, m=6, spike=None):
    out = []
    for _ in range(m):
        p = spike if spike else rng.choice([1, 2, 5, 12])
        out.append(BC.to_QK(BC.proj_K(rng.random((n, n)) ** p, n), n, den=10 ** 4))
    return out


# ---------------------------------------------------------------------- G1
def G1():
    print("G1  the normalised Bernstein form  d_j = dE_j + gamma(n,k)(Q_{j+1}-Q_j)")
    import reduce_scan_b2 as B2
    rng = np.random.default_rng(1)
    ok_id = ok_d0 = ok_sum = ok_bern = 0
    tot = 0
    for n in (4, 5, 6):
        for k in range(2, n + 1):
            for A in rat_points(n, rng, 3):
                tot += 1
                d_new = BC.dvec_x(A, k)
                d_ref = B2.dvec_x(A, k)
                ok_id += (d_new == d_ref)
                ok_d0 += (d_new[0] == 0)
                F = 2 - Q(fc.fact(k), Q(n) ** k) - R.phi_x(A, k)
                ok_sum += (sum(d_new) == F)
                # Bernstein evaluation of Phi_k(A_t) at t = 1/3, exactly
                t = Q(1, 3)
                J = [[Q(1, n)] * n for _ in range(n)]
                At = [[(1 - t) * A[i][j] + t * J[i][j] for j in range(n)]
                      for i in range(n)]
                beta = [None] * (k + 1)
                r = [sum(row) for row in A]
                c = [sum(A[i][j] for i in range(n)) for j in range(n)]
                for j in range(k + 1):
                    sg = R.sigma_all_x(A)[j]
                    beta[j] = (Q(fc.e_k(r, j), fc.binom(n, j))
                               + Q(fc.e_k(c, j), fc.binom(n, j))
                               - Q(fc.fact(k), fc.fact(j)) * Q(n) ** (j - k)
                               * sg / fc.binom(n, j) ** 2)
                fb = sum(fc.binom(k, mm) * t ** mm * (1 - t) ** (k - mm) * beta[k - mm]
                         for mm in range(k + 1))
                ok_bern += (fb == R.phi_x(At, k))
    check("Q-form d-vector == reduce_scan_b2 literal form (exact)", ok_id == tot,
          f"{ok_id}/{tot}")
    check("d_0 = 0 identically on K_n", ok_d0 == tot, f"{ok_d0}/{tot}")
    check("sum_j d_j = F_{n,k} = 2 - gamma - Phi_k", ok_sum == tot, f"{ok_sum}/{tot}")
    check("Bernstein form evaluates Phi_k(A_t) exactly at t = 1/3",
          ok_bern == tot, f"{ok_bern}/{tot}")
    # mutants
    A = rat_points(5, np.random.default_rng(2), 1)[0]
    Qv, dE = BC.Qvec_x(A), BC.dEvec_x(A)
    g = Q(fc.fact(4), Q(5) ** 4)
    m_sign = [dE[j] - g * (Qv[j + 1] - Qv[j]) for j in range(4)]
    m_shift = [dE[j] + g * (Qv[j + 2] - Qv[j + 1]) if j + 2 <= 5 else Q(0)
               for j in range(4)]
    m_nodE = [g * (Qv[j + 1] - Qv[j]) for j in range(4)]
    ref = BC.dvec_x(A, 4)
    caught("sign-flipped gamma", m_sign != ref)
    caught("index-shifted Q", m_shift != ref)
    caught("dE dropped", m_nodE != ref)
    caught("Q_1 != 1 would break d_0 = 0", BC.Qvec_x(A)[1] == 1)


# ---------------------------------------------------------------------- G2
def G2():
    print("G2  Theorem R:  min over k of d_j^{(k,n)} is at k = j+1")
    bad = 0
    for n in range(2, 40):
        g = [Q(fc.fact(k), Q(n) ** k) for k in range(1, n + 1)]
        if any(g[i + 1] > g[i] for i in range(len(g) - 1)):
            bad += 1
    check("gamma(n,k) = k!/n^k nonincreasing in k on 1..n, n = 2..39 (exact)",
          bad == 0)
    check("gamma(n,n-1) = gamma(n,n) exactly (the tie at the top)",
          all(Q(fc.fact(n - 1), Q(n) ** (n - 1)) == Q(fc.fact(n), Q(n) ** n)
              for n in range(2, 20)))
    rng = np.random.default_rng(3)
    tot = ok = 0
    for n in (4, 5, 6, 7):
        for A in rat_points(n, rng, 4):
            Qv, dE = BC.Qvec_x(A), BC.dEvec_x(A)
            for j in range(1, n):
                vals = [dE[j] + Q(fc.fact(k), Q(n) ** k) * (Qv[j + 1] - Qv[j])
                        for k in range(j + 1, n + 1)]
                tot += 1
                # claim: min(vals) >= 0  <=>  vals[0] >= 0   (k = j+1 decides)
                ok += ((min(vals) >= 0) == (vals[0] >= 0))
    check("(min_k d_j >= 0) <=> (d_j at k=j+1 >= 0), exact", ok == tot, f"{ok}/{tot}")
    # the rival rule "k = n decides" must be detected as WRONG.  No real d_j with
    # j < n-1 is ever negative, so the discriminating input is synthetic: a
    # (dE_j, gap) pair inside the region the rule gets wrong.
    dEs, gap, n = Q(1, 2000), Q(-1, 100), 5
    vs = [dEs + Q(fc.fact(k), Q(n) ** k) * gap for k in range(2, n + 1)]
    caught("'k = n decides'", (min(vs) >= 0) != (vs[-1] >= 0),
           f"k=2 gives {float(vs[0]):+.2e}, k=n gives {float(vs[-1]):+.2e}")
    caught("'k = j+1 decides' is the one that survives the same input",
           (min(vs) >= 0) == (vs[0] >= 0)) 


# ---------------------------------------------------------------------- G3
def G3():
    print("G3  Theorem D1:  d_1 >= 0 on K_n for every 2 <= k <= n, equality only at J/n")
    rng = np.random.default_rng(5)
    tot = okf = okn = 0
    for n in range(2, 9):
        pts = rat_points(n, rng, 5) + [
            [[Q(n) if (i == 0 and j == 0) else Q(0) for j in range(n)] for i in range(n)],
            [[Q(1) if i == j else Q(0) for j in range(n)] for i in range(n)],
            [[Q(1, n) for _ in range(n)] for _ in range(n)]]
        for A in pts:
            r = [sum(row) for row in A]
            c = [sum(A[i][j] for i in range(n)) for j in range(n)]
            X = sum(x * x for x in r) + sum(x * x for x in c) - 2 * n
            F = sum(A[i][j] ** 2 for i in range(n) for j in range(n))
            for k in range(2, n + 1):
                g = Q(fc.fact(k), Q(n) ** k)
                closed = (Q(X, n * (n - 1)) + g * (F - 1 - X) / Q((n - 1) ** 2)
                          if n > 1 else Q(0))
                tot += 1
                okf += (closed == BC.dvec_x(A, k)[1])
                okn += (BC.dvec_x(A, k)[1] >= 0)
    check("closed form  d_1 = X/(n(n-1)) + gamma(F-1-X)/(n-1)^2  (exact)",
          okf == tot, f"{okf}/{tot}")
    check("d_1 >= 0 at every tested point", okn == tot, f"{okn}/{tot}")
    # the two structural inequalities the proof rests on
    bad = 0
    for n in range(2, 40):
        for k in range(2, n + 1):
            coef = Q(1, n * (n - 1)) - Q(fc.fact(k), Q(n) ** k) / Q((n - 1) ** 2)
            if coef < 0:
                bad += 1
    check("coefficient of X is >= 0 for every 2 <= k <= n <= 39 (exact)", bad == 0)
    check("the bound is tight only at (n,k) = (2,2)",
          (Q(1, 2) - Q(2, 4)) == 0
          and all(Q(1, n * (n - 1)) - Q(fc.fact(2), Q(n) ** 2) / Q((n - 1) ** 2) > 0
                  for n in range(3, 30)))
    check("X >= 0 (Cauchy-Schwarz on the line sums) at every tested point",
          all(sum(x * x for x in [sum(row) for row in A])
              + sum(x * x for x in [sum(A[i][j] for i in range(len(A)))
                                    for j in range(len(A))]) - 2 * len(A) >= 0
              for n in range(2, 8) for A in rat_points(n, np.random.default_rng(6), 4)))
    check("F = ||A||_F^2 >= 1 at every tested point",
          all(sum(A[i][j] ** 2 for i in range(len(A)) for j in range(len(A))) >= 1
              for n in range(2, 8) for A in rat_points(n, np.random.default_rng(7), 4)))
    # equality case
    n = 5
    J = [[Q(1, n)] * n for _ in range(n)]
    check("d_1 = 0 exactly at J_n/n", all(BC.dvec_x(J, k)[1] == 0 for k in (2, 3, 4, 5)))
    check("d_1 > 0 off J_n/n (identity, one cell, a permutation mixture)",
          all(BC.dvec_x(A, 3)[1] > 0 for A in [
              [[Q(1) if i == j else Q(0) for j in range(n)] for i in range(n)],
              [[Q(n) if (i == 0 and j == 0) else Q(0) for j in range(n)]
               for i in range(n)],
              [[Q(1, 2) if (i == j or (j - i) % n == 1) else Q(0) for j in range(n)]
               for i in range(n)]]))
    # mutants
    caught("closed form with (n-1) instead of (n-1)^2",
           (lambda A, n, k: (Q(sum(x*x for x in [sum(r) for r in A])
                               + sum(x*x for x in [sum(A[i][j] for i in range(n))
                                                   for j in range(n)]) - 2*n,
                               n*(n-1))
                            + Q(fc.fact(k), Q(n)**k)
                            * (sum(A[i][j]**2 for i in range(n) for j in range(n))
                               - 1 - (sum(x*x for x in [sum(r) for r in A])
                                      + sum(x*x for x in [sum(A[i][j] for i in range(n))
                                                          for j in range(n)]) - 2*n))
                            / Q(n - 1)) != BC.dvec_x(A, k)[1])(
               rat_points(5, np.random.default_rng(8), 1)[0], 5, 3))
    caught("'coefficient of X >= 0' fails if the k!/n^k factor is dropped",
           all(Q(1, n * (n - 1)) - Q(1) / Q((n - 1) ** 2) < 0 for n in range(2, 10)))


# ---------------------------------------------------------------------- G4
def G4():
    print("G4  Theorem E:  A* = (I + C)/2 (C the n-cycle) has d_{n-1} = 0 at k = n")
    ok_sig = ok_d = ok_min = 0
    tot = 0
    for n in range(3, 9):
        A = [[Q(1, 2) if (i == j or (j - i) % n == 1) else Q(0) for j in range(n)]
             for i in range(n)]
        sg = R.sigma_all_x(A)
        tot += 1
        ok_sig += (sg[n - 1] == n * n * sg[n] and sg[n] == Q(2) ** (1 - n))
        d = BC.dvec_x(A, n)
        ok_d += (d[n - 1] == 0 and all(d[j] > 0 for j in range(1, n - 1)))
        # exact first-order minimality on K_n:
        #   grad V = const + per(A(p|q)) - sigma_{n-2}(A(p|q))/n^2,
        #   must be CONSTANT on the support and STRICTLY LARGER off it
        g = {}
        for p in range(n):
            for q in range(n):
                M = [[A[i][j] for j in range(n) if j != q] for i in range(n) if i != p]
                s = R.sigma_all_x(M)
                g[(p, q)] = s[n - 1] - s[n - 2] / Q(n * n)
        supp = {g[(p, q)] for p in range(n) for q in range(n) if A[p][q] != 0}
        zero = [g[(p, q)] for p in range(n) for q in range(n) if A[p][q] == 0]
        ok_min += (len(supp) == 1 and all(z > next(iter(supp)) for z in zero))
    check("sigma_{n-1}(A*) = n^2 per(A*) and per(A*) = 2^{1-n}, n = 3..8",
          ok_sig == tot, f"{ok_sig}/{tot}")
    check("d_{n-1}(A*) = 0 at k = n, and d_j > 0 for 1 <= j <= n-2",
          ok_d == tot, f"{ok_d}/{tot}")
    check("A* is an exact first-order local minimum of V_{n,n} on K_n",
          ok_min == tot, f"{ok_min}/{tot}")
    check("A* is NOT a zero of the Cheon-Hwang deficit (only the top layer vanishes)",
          all(2 - Q(fc.fact(n), Q(n) ** n)
              - R.phi_x([[Q(1, 2) if (i == j or (j - i) % n == 1) else Q(0)
                          for j in range(n)] for i in range(n)], n) > 0
              for n in range(3, 8)))
    caught("(I + T)/2 with T a TRANSPOSITION is not an equality point",
           (lambda n: BC.dvec_x(
               [[Q(1, 2) if (i == j and i > 1) or (i < 2 and j < 2) else Q(0)
                 for j in range(n)] for i in range(n)], n)[n - 1] != 0)(4))


# ---------------------------------------------------------------------- G5
def G5():
    print("G5  the KILL:  exact witnesses with d_{n-1} < 0 at k = n; (B) refuted")
    n = 3
    W = [[Q(3, 4) * m for m in row] for row in [[1, 0, 1], [0, 1, 0], [0, 1, 0]]]
    check("W_3 in K_3", all(x >= 0 for r in W for x in r)
          and sum(sum(r) for r in W) == 3)
    d = BC.dvec_x(W, 3)
    check("d(W_3) = [0, 11/72, -1/16]  ->  D-VECTOR CONJECTURE FALSE",
          d == [Q(0), Q(11, 72), Q(-1, 16)], str([str(x) for x in d]))
    check("per(W_3) = 0 (Frobenius-Koenig), sigma_2(W_3) = 9/4",
          R.sigma_all_x(W)[3] == 0 and R.sigma_all_x(W)[2] == Q(9, 4))
    J = [[Q(1, 3)] * 3 for _ in range(3)]

    def f(t):
        At = [[(1 - t) * W[i][j] + t * J[i][j] for j in range(3)] for i in range(3)]
        return R.phi_x(At, 3)
    check("f'(0) = 3 d_2 = -3/16 < 0", 3 * d[2] == Q(-3, 16))
    check("f(9/53) = 4698/2809 < f(0) = 27/16  ->  (B) REFUTED",
          f(Q(9, 53)) == Q(4698, 2809) and f(Q(9, 53)) < f(0))
    check("the dip is exactly 675/44944", f(0) - f(Q(9, 53)) == Q(675, 44944))
    check("f(1) = 2 - 6/27 = 16/9 (endpoint unchanged)", f(Q(1)) == Q(16, 9))
    check("CHEON-HWANG STILL HOLDS at W_3: Phi_3(W_3) = 27/16 < 16/9",
          R.phi_x(W, 3) == Q(27, 16) and R.phi_x(W, 3) < Q(16, 9))
    check("f is monotone on NEITHER side of t*: f(1/10) < f(0) and f(1/2) > f(1/5)",
          f(Q(1, 10)) < f(0) and f(Q(1, 2)) > f(Q(1, 5)))
    # n = 4 witness
    W4 = [[Q(0)] * 4 for _ in range(4)]
    W4[0][3] = Q(5, 6); W4[1][0] = W4[1][2] = Q(5, 6)
    W4[2][1] = W4[2][3] = Q(1, 3); W4[3][1] = Q(5, 6)
    check("W_4 in K_4", sum(sum(r) for r in W4) == 4
          and all(x >= 0 for r in W4 for x in r))
    check("d_3(W_4) = -35/5184 < 0 at k = 4", BC.dvec_x(W4, 4)[3] == Q(-35, 5184))
    check("per(W_4) = 0", R.sigma_all_x(W4)[4] == 0)
    check("CHEON-HWANG STILL HOLDS at W_4",
          R.phi_x(W4, 4) < 2 - Q(fc.fact(4), Q(4) ** 4))
    # n = 5 witness: the two-path support with a = 2, weights 5/6 and 5/12
    W5 = [[Q(0)] * 5 for _ in range(5)]
    for (p, q), v in zip([(0, 0), (0, 1), (1, 1), (1, 2), (2, 3), (3, 3), (3, 4), (4, 4)],
                         [Q(5, 6), Q(5, 12), Q(5, 12), Q(5, 6),
                          Q(5, 6), Q(5, 12), Q(5, 12), Q(5, 6)]):
        W5[p][q] = v
    check("W_5 in K_5", sum(sum(r) for r in W5) == 5
          and all(x >= 0 for r in W5 for x in r))
    check("d_4(W_5) = -25/5184 < 0 at k = 5", BC.dvec_x(W5, 5)[4] == Q(-25, 5184))
    check("per(W_5) = 0", R.sigma_all_x(W5)[5] == 0)
    check("CHEON-HWANG STILL HOLDS at W_5",
          R.phi_x(W5, 5) < 2 - Q(fc.fact(5), Q(5) ** 5))
    check("W_5: no negative d_j for j < 4, and d_{k-1} >= 0 for every k < 5",
          all(BC.dvec_x(W5, 5)[j] >= 0 for j in range(4))
          and all(BC.dvec_x(W5, k)[k - 1] >= 0 for k in (2, 3, 4)))
    # controls: the kill is confined to the TOP layer and to k = n
    check("no negative d_j at W_3, W_4 for j < n-1",
          all(BC.dvec_x(W, 3)[j] >= 0 for j in range(2))
          and all(BC.dvec_x(W4, 4)[j] >= 0 for j in range(3)))
    check("at k < n the same witnesses give d_{k-1} >= 0",
          all(BC.dvec_x(W, k)[k - 1] >= 0 for k in (2,))
          and all(BC.dvec_x(W4, k)[k - 1] >= 0 for k in (2, 3)))
    caught("W_3 scaled off K_3 is not a valid witness (d_0 detects it)",
           BC.dvec_x([[x * Q(9, 10) for x in r] for r in W], 3)[0] != 0)
    caught("a permutation matrix is not a witness",
           BC.dvec_x([[Q(1) if i == j else Q(0) for j in range(3)]
                      for i in range(3)], 3)[2] > 0)


def main():
    grades = {"G1": G1, "G2": G2, "G3": G3, "G4": G4, "G5": G5}
    want = sys.argv[1:] or list(grades)
    for gname in want:
        grades[gname]()
        print()
    if FAIL:
        print(f"VERIFIER FAILED: {len(FAIL)} problems: {FAIL}")
        sys.exit(1)
    print("VERIFIER: ALL GRADES PASS")


if __name__ == "__main__":
    main()
