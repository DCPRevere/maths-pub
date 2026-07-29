"""
Cheap falsifiable FIRST TESTS for the candidate all-k routes of NOTES section 10.

Standard library only, Fraction throughout, no float in any decision.  Nothing
here is a proof; every part either survives or produces a witness, and a witness
is the deliverable.

PARTS
  A  Projection monotonicity (route H, the transverse step):
        Phi_k(A) <= Phi_k(P A)   where (P A)_ij = a_ij - (r_i-1)/n - (c_j-1)/n
     is the orthogonal projection of A onto the doubly stochastic AFFINE plane.
     If true whenever P A >= 0, then route H reduces the conjecture on that
     region to Cheon-Wanless 2007 Theorem 4.2, which is a THEOREM for all k.
  B  Shape of the slack in k: is k -> s_k(A) convex?  log-convex?  Convexity
     plus s_1 = 0 and s_2 >= 0 would prove every k, INCLUDING k = n, so it is
     expected to fail; the point is to see WHERE.
  C  Row-averaging monotonicity (route R1): Phi_k(A) <= Phi_k(1 c^T / n).
     Tight at J_n/n.  Would also prove Dittert, so likewise expected to fail.
  D  Stability of the Friedland/Tverberg bound on Omega_n with the SHARP local
     constant beta/2 from allk_hessian.py:
        P_k(A) - k!/n^k >= (beta/2) ||A - J/n||_F^2   for A doubly stochastic.
  E  The Laplace recursion (route I): does the (n-1, k-1) statement, fed through
        k sigma_k(A) = sum_ij a_ij sigma_{k-1}(A(i|j)),
     imply the (n, k) statement pointwise?

Usage:  ./guard.sh python3 allk_routes.py
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
    if k == 0:
        return Fr(1)
    tot = Fr(0)
    for R in combinations(range(n), k):
        for C in combinations(range(n), k):
            tot += per([[A[i][j] for j in C] for i in R])
    return tot


def rows_cols(A):
    n = len(A)
    r = [sum(A[i][j] for j in range(n)) for i in range(n)]
    c = [sum(A[i][j] for i in range(n)) for j in range(n)]
    return r, c


def gamma(n, k):
    return Fr(factorial(k), n ** k)


def Phi(A, k):
    n = len(A)
    N = Fr(comb(n, k))
    r, c = rows_cols(A)
    return elem_sym(r, k) / N + elem_sym(c, k) / N - sigma_k(A, k) / (N * N)


def slack(A, k):
    return (2 - gamma(len(A), k)) - Phi(A, k)


def beta_half(n, k):
    kappa = Fr(k * (k - 1), n * (n - 1))
    return kappa * kappa * Fr(factorial(k - 2), n ** (k - 2)) / 2


def fro_sq_dev(A):
    n = len(A)
    return sum((A[i][j] - Fr(1, n)) ** 2 for i in range(n) for j in range(n))


def project(A):
    """Orthogonal projection onto { row sums = col sums = 1 }.  May go negative."""
    n = len(A)
    r, c = rows_cols(A)
    return [
        [A[i][j] - (r[i] - 1) / Fr(n) - (c[j] - 1) / Fr(n) for j in range(n)]
        for i in range(n)
    ]


def nonneg(A):
    return all(x >= 0 for row in A for x in row)


# --------------------------------------------------------------- test menus


def rand_Kn(n, rng, zeros=0.0, spread=9):
    """A random rational point of K_n: nonneg integers rescaled to total n."""
    while True:
        M = [
            [0 if rng.random() < zeros else rng.randint(0, spread) for _ in range(n)]
            for _ in range(n)
        ]
        tot = sum(sum(row) for row in M)
        if tot > 0:
            break
    return [[Fr(n * M[i][j], tot) for j in range(n)] for i in range(n)]


def rand_Omega(n, rng, terms=4):
    """A random rational doubly stochastic matrix: convex hull of permutations."""
    perms = [list(range(n)) for _ in range(terms)]
    for p in perms:
        rng.shuffle(p)
    w = [rng.randint(1, 6) for _ in range(terms)]
    tot = sum(w)
    A = [[Fr(0)] * n for _ in range(n)]
    for p, wt in zip(perms, w):
        for i in range(n):
            A[i][p[i]] += Fr(wt, tot)
    return A


def structured_Kn(n):
    out = []
    out.append(("uniform", [[Fr(1, n)] * n for _ in range(n)]))
    out.append(("identity", [[Fr(1) if i == j else Fr(0) for j in range(n)]
                             for i in range(n)]))
    out.append(("one cell", [[Fr(n) if (i, j) == (0, 0) else Fr(0)
                              for j in range(n)] for i in range(n)]))
    out.append(("first row", [[Fr(1) if i == 0 else Fr(0) for j in range(n)]
                              for i in range(n)]))
    # rank one 1 c^T / n with a skewed c
    c = [Fr(2 * (j + 1), n + 1) for j in range(n)]
    s = sum(c)
    c = [x * n / s for x in c]
    out.append(("rank one", [[c[j] / n for j in range(n)] for i in range(n)]))
    # a doubly stochastic matrix that is not J: (J + P)/2 style
    P = [[Fr(1) if (j == (i + 1) % n) else Fr(0) for j in range(n)] for i in range(n)]
    out.append(("(J/n+P)/2", [[(Fr(1, n) + P[i][j]) / 2 for j in range(n)]
                              for i in range(n)]))
    # support inside a (k-1)-subsquare-ish block: mass on a 2x2 block
    B = [[Fr(0)] * n for _ in range(n)]
    for i in range(2):
        for j in range(2):
            B[i][j] = Fr(n, 4)
    out.append(("2x2 block", B))
    return out


# ------------------------------------------------------------------- PART A


def part_A(rng):
    print("PART A.  Projection monotonicity:  slack_k(A) >= slack_k(P A) ?")
    print("  (equivalently Phi_k(A) <= Phi_k(P A)).  Tested only where P A >= 0.")
    print()
    fails = []
    tested = 0
    skipped = 0
    for n in (4, 5):
        cases = list(structured_Kn(n))
        for t in range(140 if n == 4 else 60):
            z = [0.0, 0.15, 0.35, 0.55][t % 4]
            cases.append((f"rand{t}", rand_Kn(n, rng, zeros=z)))
        for name, A in cases:
            PA = project(A)
            if not nonneg(PA):
                skipped += 1
                continue
            for k in range(2, n + 1):
                d = slack(A, k) - slack(PA, k)
                tested += 1
                if d < 0:
                    fails.append((n, k, name, d, A))
    print(f"  {tested} (A, k) pairs tested, {skipped} matrices skipped (P A had a")
    print(f"  negative entry), {len(fails)} violations.")
    if fails:
        n, k, name, d, A = min(fails, key=lambda x: x[3])
        print(f"  WORST: n={n} k={k} case={name}  deficit {d} = {float(d):.4e}")
        print("  witness A (rows):")
        for row in A:
            print("   ", [str(x) for x in row])
    print()
    return fails


# ------------------------------------------------------------------- PART B


def part_B(rng):
    print("PART B.  Shape of s_k in k.  s_1 = 0 on K_n is checked first.")
    print("  convex means s_{k+1} + s_{k-1} - 2 s_k >= 0 for 2 <= k <= n-1.")
    print()
    nonconvex = 0
    nonlogconvex = 0
    nonlogconcave = 0
    total = 0
    shapes = []
    for n in (4, 5, 6):
        cases = list(structured_Kn(n))
        for t in range(12):
            cases.append((f"rand{t}", rand_Kn(n, rng, zeros=0.2 * (t % 3))))
        for name, A in cases:
            s = [slack(A, k) for k in range(1, n + 1)]
            assert s[0] == 0, (n, name, s[0])
            if all(x >= 0 for x in s):
                pass
            else:
                print(f"  !! s_k < 0 at n={n} {name}: {[float(x) for x in s]}")
            for k in range(2, n):
                total += 1
                second = s[k] + s[k - 2] - 2 * s[k - 1]
                if second < 0:
                    nonconvex += 1
                if s[k - 1] > 0 and s[k] * s[k - 2] < s[k - 1] ** 2:
                    nonlogconvex += 1
                if s[k - 1] > 0 and s[k] * s[k - 2] > s[k - 1] ** 2:
                    nonlogconcave += 1
            if n == 5 and name in ("identity", "rank one", "(J/n+P)/2", "2x2 block"):
                shapes.append((n, name, [float(x) for x in s]))
    print(f"  {total} second differences: {nonconvex} negative (convexity fails),")
    print(f"  {nonlogconvex} log-convexity failures, {nonlogconcave} log-concavity"
          " failures.")
    for n, name, s in shapes:
        print(f"  n={n} {name:10s} s_1..s_n = " + " ".join(f"{x:.5f}" for x in s))
    print()


# ------------------------------------------------------------------- PART C


def part_C(rng):
    print("PART C.  Row-averaging monotonicity:  Phi_k(A) <= Phi_k(1 c^T / n) ?")
    print("  equivalently  1 - E_k(r) + P_k(A) >= gamma(n,k) E_k(c).")
    print()
    fails = []
    tested = 0
    for n in (4, 5):
        cases = list(structured_Kn(n))
        for t in range(60):
            cases.append((f"rand{t}", rand_Kn(n, rng, zeros=0.15 * (t % 4))))
        for name, A in cases:
            n_ = len(A)
            r, c = rows_cols(A)
            Abar = [[c[j] / Fr(n_) for j in range(n_)] for _ in range(n_)]
            for k in range(2, n_ + 1):
                d = Phi(Abar, k) - Phi(A, k)
                tested += 1
                if d < 0:
                    fails.append((n_, k, name, d, A))
    print(f"  {tested} (A, k) pairs tested, {len(fails)} violations.")
    if fails:
        n, k, name, d, A = min(fails, key=lambda x: x[3])
        print(f"  WORST: n={n} k={k} case={name}  deficit {d} = {float(d):.4e}")
        for row in A:
            print("   ", [str(x) for x in row])
    print()
    return fails


# ------------------------------------------------------------------- PART D


def part_D(rng):
    print("PART D.  Stability of the Friedland bound on Omega_n with the sharp")
    print("  local constant:  P_k(A) - k!/n^k >= (beta/2) ||A - J/n||_F^2 ?")
    print()
    fails = []
    tested = 0
    worst_ratio = None
    for n in (4, 5, 6):
        cases = []
        for i, p in enumerate(permutations(range(n))):
            if i >= 3:
                break
            cases.append((f"perm{i}",
                          [[Fr(1) if p[a] == b else Fr(0) for b in range(n)]
                           for a in range(n)]))
        for t in range(25):
            cases.append((f"rand{t}", rand_Omega(n, rng, terms=2 + (t % 4))))
        for name, A in cases:
            d2 = fro_sq_dev(A)
            for k in range(2, n + 1):
                N = Fr(comb(n, k))
                Pk = sigma_k(A, k) / (N * N)
                lhs = Pk - gamma(n, k)
                rhs = beta_half(n, k) * d2
                tested += 1
                if lhs < rhs:
                    fails.append((n, k, name, lhs - rhs))
                if d2 > 0:
                    ratio = lhs / (beta_half(n, k) * d2)
                    if worst_ratio is None or ratio < worst_ratio[0]:
                        worst_ratio = (ratio, n, k, name)
    print(f"  {tested} (A, k) pairs tested, {len(fails)} violations.")
    if worst_ratio:
        rt, n, k, name = worst_ratio
        print(f"  tightest: ratio lhs/rhs = {float(rt):.4f} at n={n} k={k} ({name})")
    if fails:
        for f in fails[:6]:
            print("  violation:", f[0], f[1], f[2], float(f[3]))
    print()
    return fails


# ------------------------------------------------------------------- PART E


def minor(A, i, j):
    n = len(A)
    return [[A[a][b] for b in range(n) if b != j] for a in range(n) if a != i]


def part_E(rng):
    print("PART E.  The Laplace recursion k sigma_k(A) = sum_ij a_ij"
          " sigma_{k-1}(A(i|j)).")
    print("  First the identity, then whether the (n-1, k-1) statement fed through")
    print("  it implies the (n, k) statement pointwise.")
    print()
    # identity check
    for n in (4, 5):
        for _ in range(4):
            A = rand_Kn(n, rng)
            for k in range(1, n + 1):
                lhs = k * sigma_k(A, k)
                rhs = sum(A[i][j] * sigma_k(minor(A, i, j), k - 1)
                          for i in range(n) for j in range(n))
                assert lhs == rhs, (n, k)
    print("  identity verified exactly at n = 4, 5 for every k.  [V]")
    print()
    closes = 0
    fails = 0
    worst = None
    for n in (4, 5):
        m = n - 1
        cases = list(structured_Kn(n))
        for t in range(40):
            cases.append((f"rand{t}", rand_Kn(n, rng, zeros=0.15 * (t % 4))))
        for name, A in cases:
            for k in range(3, n + 1):
                Np = Fr(comb(m, k - 1))
                gp = gamma(m, k - 1)
                # lower bound on sigma_{k-1}(A(i|j)) from the (m, k-1) statement
                bound = Fr(0)
                for i in range(n):
                    for j in range(n):
                        if A[i][j] == 0:
                            continue
                        B = minor(A, i, j)
                        s = sum(x for row in B for x in row)
                        if s == 0:
                            continue
                        scale = s / Fr(m)
                        Bt = [[x / scale for x in row] for row in B]
                        rb, cb = rows_cols(Bt)
                        expr = (elem_sym(rb, k - 1) / Np
                                + elem_sym(cb, k - 1) / Np - 2 + gp)
                        lb = Np * Np * expr * scale ** (k - 1)
                        if lb < 0:
                            lb = Fr(0)          # sigma >= 0 is always available
                        bound += A[i][j] * lb
                bound /= k
                N = Fr(comb(n, k))
                r, c = rows_cols(A)
                need = N * N * (elem_sym(r, k) / N + elem_sym(c, k) / N
                                - 2 + gamma(n, k))
                if bound >= need:
                    closes += 1
                else:
                    fails += 1
                    gap = need - bound
                    if worst is None or gap > worst[0]:
                        worst = (gap, n, k, name)
    print(f"  {closes} points where the recursion closes, {fails} where it does not.")
    if worst:
        gap, n, k, name = worst
        print(f"  worst shortfall {float(gap):.4e} at n={n} k={k} ({name})")
    print()


def main():
    rng = random.Random(20260729)
    print("allk_routes.py -- first tests for the all-k routes of NOTES section 10")
    print()
    fa = part_A(rng)
    part_B(rng)
    fc = part_C(rng)
    fd = part_D(rng)
    part_E(rng)
    print("SUMMARY")
    print(f"  A projection monotonicity: {'FALSIFIED' if fa else 'SURVIVED'}")
    print(f"  C row averaging          : {'FALSIFIED' if fc else 'SURVIVED'}")
    print(f"  D Friedland stability    : {'FALSIFIED' if fd else 'SURVIVED'}")


if __name__ == "__main__":
    main()
