"""
Sanity-check the k = 3 STABILITY constant outside Lean, exactly over Q.

The Lean theorem `subDittert_k3_stability` says: for every n >= 4 and every
A in K_n,

    theta_2(n) * ||A - J_n/n||_F^2  <=  (2 - 6/n^3) - [E_3(r) + E_3(c) - P_3(A)],

with the Frobenius norm the plain sum of squared entry deviations,

    ||A - J_n/n||_F^2 = sum_{i,j} (A_ij - 1/n)^2,

and

    theta_2(n) = (n^4 + 40 n^2 - 84 n + 40) / (n^5 (n-1)^3 (n-2)).

This script re-derives the right-hand side from the DEFINITION in the 1992
paper -- e_3 of the row and column sums, and sigma_3 as an explicit double sum
of 3 x 3 subpermanents -- with `fractions.Fraction` throughout, so every
comparison is exact.  It shares no code with the certificate pipeline, with
`verify_general.py`, or with the Lean file; the certificate is not read at all.
Nothing here is part of the proof: it is a transcription check on the constant
and on the normalisation of the norm.

Two things are measured:

  [A] the inequality itself, at hand-picked exact rational points of K_n,
      including the boundary (matrices with zero entries) and J_n/n, where both
      sides must vanish;

  [B] its ORDER near J_n/n.  Put A = J_n/n + t D with sum(D) = 0 and t rational
      and shrinking.  Both sides are O(t^2), so the slack ratio

          rho(t) = [(2 - 6/n^3) - Phi_3(A)] / [theta_2(n) ||tD||_F^2]

      tends to a finite limit >= 1; a constant of the wrong order would send it
      to 0 or to infinity.  Two kinds of direction are used.  For a DOUBLY
      CENTRED D (all row and column sums zero) the sigma_0 form contributes
      exactly theta_2 ||b||^2 -- the S^2 and line terms of `quadForm_G0` both
      vanish -- so rho -> 1 + (slack from the multiplier half only), which is
      how close to optimal the constant can be seen to be.  For a generic D the
      line terms are present and rho is larger.

Usage:  python3 stability_check.py            # n = 4, 5, 6
"""

from fractions import Fraction as F
from itertools import combinations, permutations


# ----------------------------------------------------------------- definitions

def esym3(v):
    """e_3 of a list, from the definition."""
    tot = F(0)
    for S in combinations(range(len(v)), 3):
        tot += v[S[0]] * v[S[1]] * v[S[2]]
    return tot


def permanent(M):
    """Permanent of a square list-of-lists, from the definition."""
    m = len(M)
    tot = F(0)
    for sg in permutations(range(m)):
        p = F(1)
        for i in range(m):
            p *= M[i][sg[i]]
        tot += p
    return tot


def sigma3(A, n):
    """sum of the permanents of ALL 3 x 3 submatrices, rows and columns chosen
    from independent 3-subsets."""
    tot = F(0)
    subs = list(combinations(range(n), 3))
    for S in subs:
        for T in subs:
            tot += permanent([[A[i][j] for j in T] for i in S])
    return tot


def binom(n, k):
    num, den = 1, 1
    for i in range(k):
        num *= n - i
        den *= i + 1
    return num // den


def phi3(A, n):
    """E_3(r) + E_3(c) - P_3(A), from the 1992 definition."""
    r = [sum(A[i][j] for j in range(n)) for i in range(n)]
    c = [sum(A[i][j] for i in range(n)) for j in range(n)]
    C = binom(n, 3)
    return (F(esym3(r), C) + F(esym3(c), C)
            - F(sigma3(A, n), C * C))


def objective(A, n):
    """(2 - 6/n^3) - Phi_3(A):  the quantity the certificate bounds below."""
    return F(2) - F(6, n ** 3) - phi3(A, n)


def theta2(n):
    return F(n ** 4 + 40 * n ** 2 - 84 * n + 40,
             n ** 5 * (n - 1) ** 3 * (n - 2))


def fro2(A, n):
    """||A - J_n/n||_F^2 = sum (A_ij - 1/n)^2."""
    return sum((A[i][j] - F(1, n)) ** 2
               for i in range(n) for j in range(n))


def in_Kn(A, n):
    return (all(A[i][j] >= 0 for i in range(n) for j in range(n))
            and sum(A[i][j] for i in range(n) for j in range(n)) == n)


# ------------------------------------------------------------------- test data

def uniform(n):
    return [[F(1, n)] * n for _ in range(n)]


def perturb(n, D, t):
    """J_n/n + t D, entrywise."""
    return [[F(1, n) + t * D[i][j] for j in range(n)] for i in range(n)]


def dir_doubly_centred(n):
    """A 2 x 2 alternating block: every row sum and every column sum is 0."""
    D = [[F(0)] * n for _ in range(n)]
    D[0][0] = F(1)
    D[0][1] = F(-1)
    D[1][0] = F(-1)
    D[1][1] = F(1)
    return D


def dir_generic(n):
    """Total sum 0, but row and column sums NOT all 0."""
    D = [[F(0)] * n for _ in range(n)]
    D[0][0] = F(3)
    D[0][1] = F(-1)
    D[1][2] = F(-1)
    D[2][0] = F(-1)
    return D


def named_points(n):
    """Exact rational points of K_n, including the boundary."""
    pts = []
    pts.append(("J_n/n", uniform(n)))

    # interior, off centre
    A = [row[:] for row in uniform(n)]
    A[0][0] += F(1, 2 * n)
    A[1][1] -= F(1, 2 * n)
    pts.append(("J/n + (e00 - e11)/(2n)", A))

    # skewed but still interior
    A = [[F(1, n) * (1 if (i + j) % 2 else 2) for j in range(n)]
         for i in range(n)]
    s = sum(A[i][j] for i in range(n) for j in range(n))
    A = [[A[i][j] * F(n, 1) / s for j in range(n)] for i in range(n)]
    pts.append(("chequerboard 2:1, rescaled", A))

    # boundary: the identity permutation matrix
    A = [[F(1) if i == j else F(0) for j in range(n)] for i in range(n)]
    pts.append(("I_n (boundary)", A))

    # boundary: all mass in the first row
    A = [[F(1) if i == 0 else F(0) for j in range(n)] for i in range(n)]
    pts.append(("first row all 1 (boundary)", A))

    # boundary: one entry carries everything
    A = [[F(0)] * n for _ in range(n)]
    A[0][0] = F(n)
    pts.append(("n e_00 (boundary)", A))
    return pts


# ------------------------------------------------------------------------ main

def run(n):
    print(f"\n================ n = {n} ================")
    th = theta2(n)
    print(f"theta_2({n}) = {th} = {float(th):.6e}")
    ok = True

    print("\n[A] the inequality at named exact points")
    for name, A in named_points(n):
        assert in_Kn(A, n), f"{name} is not in K_{n}"
        lhs = th * fro2(A, n)
        rhs = objective(A, n)
        holds = lhs <= rhs
        ok = ok and holds
        tag = "OK " if holds else "FAIL"
        extra = ""
        if lhs == 0 and rhs == 0:
            extra = "   (both sides vanish -- the equality case)"
        elif lhs != 0:
            extra = f"   slack ratio rhs/lhs = {float(rhs / lhs):.4f}"
        print(f"  {tag} {name:32s} lhs = {float(lhs):.6e}  "
              f"rhs = {float(rhs):.6e}{extra}")

    print("\n[B] order near J_n/n:  A = J/n + tD,  rho = rhs / (theta_2 ||tD||^2)")
    for dname, D in (("doubly centred", dir_doubly_centred(n)),
                     ("generic", dir_generic(n))):
        assert sum(D[i][j] for i in range(n) for j in range(n)) == 0
        rows = [sum(D[i][j] for j in range(n)) for i in range(n)]
        cols = [sum(D[i][j] for i in range(n)) for j in range(n)]
        dc = all(x == 0 for x in rows) and all(x == 0 for x in cols)
        print(f"  direction: {dname}  (row/col sums all zero: {dc})")
        prev = None
        for e in (2, 3, 4, 5, 6):
            t = F(1, 10 ** e)
            A = perturb(n, D, t)
            assert in_Kn(A, n)
            lhs = th * fro2(A, n)
            rhs = objective(A, n)
            holds = lhs <= rhs
            ok = ok and holds
            rho = rhs / lhs
            mono = "" if prev is None else f"  (decreasing: {rho < prev})"
            prev = rho
            print(f"    t = 1e-{e}:  rho = {float(rho):.10f}   "
                  f"inequality holds: {holds}{mono}")
        print(f"    limit of rho as t -> 0 is the ratio of the true Hessian "
              f"form to theta_2 ||D||^2;")
        print(f"    rho > 1 means the constant is valid but not optimal in "
              f"this direction.")
    return ok


if __name__ == "__main__":
    allok = True
    for n in (4, 5, 6):
        allok = run(n) and allok
    print(f"\nall stability checks passed: {allok}")
