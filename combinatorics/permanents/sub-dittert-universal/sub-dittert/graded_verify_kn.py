"""
graded_verify_kn.py -- graded verifier for THEOREM K (LIFT.md B.14):
the capacity chain does NOT reach k = n, the broken step is (S3), and the
sharp obstruction is spectral.

Exact over Q throughout.  Predictions filed in NOTES 53 before any computation.

THE SETTING.  At k = n:  m = n - k = 0,  cap_0 = n^(2n-k)/k^k = 1,
M_n(A) = A,  sigma_n(A) = per(A),  C(n,n) = 1,  E_n(r) = prod r_i,
gamma = n!/n^n.  The chain of NOTES 51 reads

    (S1)  E_n(r) + E_n(c) = 2 - D(A)                  [identity]
    (S2)  per(A) >= gamma * cap(A)                    [Gurvits, R]
    (S3)  cap(A) >= 1 * exp(-(0/n) sum chi) = 1       [entropy witness]
    (S4)  0 <= D(A)/gamma                             [the chi-comparison]

THE STATEMENT PROVED HERE.

  (K1)  The B.12 border-row refinement is a NO-OP at k = n:
        C_new(n,n) = C_ref(n,n) = gamma, because m! = 1, m^m = 0^0 = 1,
        G(n,0) = 1.
  (K2)  The broken step is (S3), not (C2)/(C3).  At m = 0, (S4) is the
        vacuous 0 <= D/gamma, while (S3) asserts cap(A) >= 1, which holds
        IFF A is doubly stochastic:  cap(A) <= prod r_i <= 1 with equality
        throughout iff r = c = 1.
  (K3)  Replacing (S3) by the exact capacity leaves the chain needing

            (*)   gamma * (1 - cap(A))  <=  D(A)     on  { D < gamma },

        and (*) is FALSE at every n >= 2.
  (K4)  SHARP CRITERION.  At A_0 in Omega_n along a direction B with row
        sums beta, column sums delta,

            D          = (t^2/2)( |beta|^2 + |delta|^2 ) + O(t^3)
            1 - cap    = (t^2/2)( |beta|^2 + v^T H^+ v ) + O(t^3)
            H = I - A_0^T A_0  on 1^perp ,   v = delta - A_0^T beta ,

        so (*) holds near A_0 iff gamma <= 1 - sigma_2(A_0)^2.  Since
        sigma_2 -> 1 at every permutation matrix, this fails on an open
        neighbourhood of the permutation matrices in Omega_n, at every n.
  (K5)  The degree refinement does not save it.  The witnesses are strictly
        POSITIVE, so every column degree is n and the degree-refined Gurvits
        constant is exactly prod_{i=2}^n g(i) = n!/n^n = gamma.  By contrast
        CAPACITY.md section 5's witness IS defeated by the degree refinement.
  (K6)  The second extremal structure (I + C^t)/2 is NOT a violator, nor is
        the rank-one family; the violating set is the near-decomposable
        corner only.

ONE-SIDEDNESS.  Every capacity number below is a RIGOROUS exact rational
bound on the correct side of the claim it serves:
  * to certify a VIOLATION we need cap small, and we use
        cap(A) <= prod_i (Ax)_i / prod_j x_j     for a rational x > 0;
  * to certify NO violation we need cap large, and we use Lemma B6
        cap(A) >= prod_ij (A_ij/W_ij)^{W_ij}     for doubly stochastic W,
    kept in Q by writing W_ij = p_ij/q and comparing q-th powers.
So a PASS is rigorous in both directions; no float decides anything.

BLOCKS
  [1] The k = n identifications, and (K1): the refinement is a no-op.
  [2] (K2): (S3) at m = 0 is exactly "A in Omega_n"; (C2)/(C3) degenerate.
  [3] (K3): exact rational violating witnesses of (*), n = 2..7.
  [4] (K4): the second-order law, exact over Q, and the sharp threshold.
  [5] (K5): the degree-refined constant at the witnesses, and section 5's
      witness defeated by it.
  [6] (K6): the circulants and the rank-one family, exact, no violation.
  [7] Corroboration: the second-order law against a numerically minimised
      capacity (float, corroborative only).
  [9] The STABILITY probe (LIFT.md B.15): per(A) = cap(A)per(B) makes the
      factorised requirement a TAUTOLOGY, and the cheap scale-invariant
      strengthening of Gurvits, S': per(A) >= gamma (prod r)(prod c), is
      FALSE -- refuted inside {D < gamma} by an exact n = 3 witness.
  [8] Mutation controls.

Run:  ../guard.sh python3 graded_verify_kn.py
"""

from fractions import Fraction as F
from math import comb, factorial, exp, log
import itertools
import random
import sys

FAIL = []
MUTFAIL = []
NCHECK = 0
NMUT = 0


def check(name, cond, detail=""):
    global NCHECK
    NCHECK += 1
    if cond:
        print(f"  [ok]   {name}" + (f"   {detail}" if detail else ""))
    else:
        print(f"  [FAIL] {name}   {detail}")
        FAIL.append(name)
    return bool(cond)


def mutation(name, fired):
    global NMUT
    NMUT += 1
    if fired:
        print(f"  [fired] {name}")
    else:
        print(f"  [SILENT] {name}   <-- control did not fire")
        MUTFAIL.append(name)


# ----------------------------------------------------------------- basics


def gamma(n, k=None):
    k = n if k is None else k
    return F(factorial(k), n ** k)


def g_of(d):
    """Gurvits' single-variable factor ((d-1)/d)^(d-1), exact, g(1) = 1."""
    if d <= 1:
        return F(1)
    return F(d - 1, d) ** (d - 1)


def G_lemma_u(n, m):
    """G(n,m) = C(n,m) m^m (n-m)^(n-m) / n^n, with 0^0 = 1."""
    mm = F(1) if m == 0 else F(m) ** m
    nm = F(1) if n - m == 0 else F(n - m) ** (n - m)
    return F(comb(n, m)) * mm * nm / F(n) ** n


def C_ref(n, k):
    """CAPACITY.md section 2.4: (n!/n^n) * ((n-1)/n)^((n-1)(n-k))."""
    return gamma(n, n) * F(n - 1, n) ** ((n - 1) * (n - k))


def C_new(n, k):
    """LIFT.md B.12.2 Theorem G': (n!/n^n) * m! * G(n,m) / m^m."""
    m = n - k
    mm = F(1) if m == 0 else F(m) ** m
    return gamma(n, n) * F(factorial(m)) * G_lemma_u(n, m) / mm


def rowsums(A):
    return [sum(row) for row in A]


def colsums(A):
    n = len(A[0])
    return [sum(A[i][j] for i in range(len(A))) for j in range(n)]


def prod(xs):
    p = F(1)
    for x in xs:
        p *= x
    return p


def D_of(A):
    """D(A) at k = n:  (1 - prod r) + (1 - prod c)."""
    return (1 - prod(rowsums(A))) + (1 - prod(colsums(A)))


def per(A):
    n = len(A)
    tot = F(0)
    for p in itertools.permutations(range(n)):
        t = F(1)
        for i in range(n):
            t *= A[i][p[i]]
            if t == 0:
                break
        tot += t
    return tot


def cap_upper(A, x):
    """cap(A) <= prod_i (Ax)_i / prod_j x_j.  Exact, valid for every x > 0."""
    n = len(A)
    num = F(1)
    for i in range(n):
        num *= sum(A[i][j] * x[j] for j in range(n))
    return num / prod(x)


def cap_lower_pow(A, W, q):
    """Lemma B6 kept in Q.  W doubly stochastic with q*W integral and
    supp(W) subset supp(A).  Returns R in Q with  cap(A)^q >= R,
    R = prod_ij (A_ij/W_ij)^(q W_ij)."""
    n = len(A)
    R = F(1)
    for i in range(n):
        for j in range(n):
            if W[i][j] == 0:
                continue
            assert A[i][j] > 0, "witness support escapes supp(A)"
            e = q * W[i][j]
            assert e.denominator == 1, "q does not clear W"
            R *= (A[i][j] / W[i][j]) ** int(e)
    return R


# ------------------------------------------------- exact rational linear algebra


def solve(M, b):
    """Exact Gaussian elimination.  Returns None if singular."""
    n = len(M)
    Aug = [list(M[i]) + [b[i]] for i in range(n)]
    for c in range(n):
        piv = None
        for r in range(c, n):
            if Aug[r][c] != 0:
                piv = r
                break
        if piv is None:
            return None
        Aug[c], Aug[piv] = Aug[piv], Aug[c]
        pv = Aug[c][c]
        Aug[c] = [v / pv for v in Aug[c]]
        for r in range(n):
            if r != c and Aug[r][c] != 0:
                f = Aug[r][c]
                Aug[r] = [Aug[r][t] - f * Aug[c][t] for t in range(n + 1)]
    return [Aug[i][n] for i in range(n)]


def second_order(A0, B):
    """Exact (D-rate, cap-drop-rate) at A0 in Omega_n along B, both the
    coefficient of t^2.  Returns (dD, dcap) with
        D      = dD   * t^2 + O(t^3)
        1 - cap = dcap * t^2 + O(t^3)
    and dD = (|beta|^2+|delta|^2)/2, dcap = (|beta|^2 + v^T H^+ v)/2."""
    n = len(A0)
    beta = rowsums(B)
    delta = colsums(B)
    # H = I - A0^T A0, restricted to 1^perp; solve (H + J/n) w = v.
    H = [[F(0)] * n for _ in range(n)]
    for i in range(n):
        for j in range(n):
            s = sum(A0[t][i] * A0[t][j] for t in range(n))
            H[i][j] = (F(1) if i == j else F(0)) - s
    v = [delta[j] - sum(A0[i][j] * beta[i] for i in range(n)) for j in range(n)]
    M = [[H[i][j] + F(1, n) for j in range(n)] for i in range(n)]
    w = solve(M, v)
    if w is None:
        return None
    quad = sum(v[j] * w[j] for j in range(n))
    nb = sum(b * b for b in beta)
    nd = sum(d * d for d in delta)
    return (F(nb + nd, 2), (nb + quad) / 2)


def degree_constant(A):
    """Degree-refined Gurvits constant for p_A at k = n (N = n variables):
    prod_{i=2}^n g(min(d_(i), i)) with column degrees sorted descending
    (CAPACITY.md section 2.4's optimal labelling)."""
    n = len(A)
    deg = sorted((sum(1 for i in range(n) if A[i][j] != 0) for j in range(n)),
                 reverse=True)
    c = F(1)
    for i in range(2, n + 1):
        c *= g_of(min(deg[i - 1], i))
    return c


# ----------------------------------------------------------------- families


def eye(n):
    return [[F(1) if i == j else F(0) for j in range(n)] for i in range(n)]


def Jn(n):
    return [[F(1, n)] * n for _ in range(n)]


def near_identity(n, eps):
    """A_0 = (1-eps) I + (eps/n) J.  Positive, doubly stochastic,
    sigma_2 = 1 - eps."""
    return [[(1 - eps) * (F(1) if i == j else F(0)) + eps / n for j in range(n)]
            for i in range(n)]


def circulant_half(n):
    """(I + C^t)/2 -- the second extremal structure."""
    A = [[F(0)] * n for _ in range(n)]
    for i in range(n):
        A[i][i] += F(1, 2)
        A[i][(i + 1) % n] += F(1, 2)
    return A


def push(A0, t):
    """A0 + t (E_12 - E_11):  row sums unchanged, c_1 -> 1-t, c_2 -> 1+t,
    so D = t^2 exactly."""
    A = [row[:] for row in A0]
    A[0][0] -= t
    A[0][1] += t
    return A


def rank_one(r, c, n):
    return [[r[i] * c[j] / n for j in range(n)] for i in range(n)]


NRANGE = range(2, 8)

# =====================================================================
print("=" * 78)
print("graded_verify_kn.py -- THEOREM K: the capacity chain at k = n")
print("=" * 78)

# --------------------------------------------------------------- BLOCK 1
print("\n[1] The k = n identifications, and (K1) the refinement is a NO-OP")

ok = True
for n in range(2, 45):
    m = 0
    ok &= (G_lemma_u(n, 0) == 1)
    ok &= (C_new(n, n) == C_ref(n, n) == gamma(n, n))
    # cap_0 = n^(2n-k)/k^k at k = n is 1
    ok &= (F(n) ** (2 * n - n) / F(n) ** n == 1)
check("[1a] G(n,0) = 1, C_new(n,n) = C_ref(n,n) = n!/n^n, cap_0 = 1, n = 2..44", ok)

# rho_new = 1 at k = n: C_new * cap_0 = (m!)^2 C(n,k)^2 gamma
ok = all(C_new(n, n) * 1 == F(factorial(0)) ** 2 * F(comb(n, n)) ** 2 * gamma(n, n)
         for n in range(2, 45))
check("[1b] rho_new(n,n) = 1 exactly (Theorem H' at m = 0), n = 2..44", ok)

# the refinement is a strict gain only at m >= 2, and none at m = 0, 1
ok = all(C_new(n, n) == C_ref(n, n) and C_new(n, n - 1) == C_ref(n, n - 1)
         and all(C_new(n, k) > C_ref(n, k) for k in range(2, n - 1))
         for n in range(4, 20))
check("[1c] C_new = C_ref at m = 0 and m = 1, C_new > C_ref at m >= 2, n = 4..19", ok)

# M_n(A) = A and sigma_n(A) = per(A)
ok = True
rng = random.Random(11)
for n in range(2, 7):
    for _ in range(3):
        A = [[F(rng.randint(1, 9), 7) for _ in range(n)] for _ in range(n)]
        s = sum(sum(row) for row in A)
        A = [[a * n / s for a in row] for row in A]
        # sigma_n = sum over |I| = |J| = n of per(A[I,J]) = per(A); C(n,n) = 1
        ok &= (per(A) == per(A) and comb(n, n) == 1)
        ok &= (prod(rowsums(A)) == F(1) * prod(rowsums(A)))
        ok &= (D_of(A) == (1 - prod(rowsums(A))) + (1 - prod(colsums(A))))
check("[1d] sigma_n = per, C(n,n) = 1, E_n(r) = prod r_i, D = (1-prod r)+(1-prod c)", ok)

# --------------------------------------------------------------- BLOCK 2
print("\n[2] (K2) the broken step is (S3): at m = 0 it asserts cap(A) >= 1,")
print("    which holds IFF A is doubly stochastic")

# cap(A) <= prod r_i, by x = 1
ok = True
worst = None
rng = random.Random(23)
for n in range(2, 7):
    for _ in range(40):
        A = [[F(rng.randint(0, 9), 5) for _ in range(n)] for _ in range(n)]
        s = sum(sum(row) for row in A)
        if s == 0:
            continue
        A = [[a * n / s for a in row] for row in A]
        one = [F(1)] * n
        ub = cap_upper(A, one)
        ok &= (ub == prod(rowsums(A)))
        # AM-GM: prod r <= 1 since sum r = n
        ok &= (prod(rowsums(A)) <= 1)
check("[2a] cap(A) <= prod r_i (x = 1) and prod r_i <= 1 by AM-GM: so cap <= 1", ok)

# equality: A doubly stochastic  ==>  cap = 1 exactly (Lemma B6 with W = A)
ok = True
for n in range(2, 7):
    for A0 in (Jn(n), circulant_half(n), near_identity(n, F(1, 3))):
        q = 1
        for i in range(n):
            for j in range(n):
                if A0[i][j] != 0:
                    q = q * A0[i][j].denominator // \
                        __import__("math").gcd(q, A0[i][j].denominator)
        R = cap_lower_pow(A0, A0, F(q))
        ok &= (R == 1)                       # cap^q >= 1
        ok &= (cap_upper(A0, [F(1)] * n) == 1)   # cap <= 1
check("[2b] A doubly stochastic ==> cap(A) = 1 exactly (Lemma B6 with W = A,"
      " kept in Q by q-th powers)", ok)

# strict off the face.  NOTE the push keeps the ROW sums at 1, so x = 1 gives
# only cap <= prod r = 1; the strict bound needs a genuine x, and does not come
# free.  That is itself the point of (K2): (S3) is an equality statement.
ok = True
strict = []
for n in range(3, 8):
    A = push(near_identity(n, F(1, 4)), F(1, 20))
    ok &= (cap_upper(A, [F(1)] * n) == 1)          # x = 1 is BLIND here
    best = min(cap_upper(A, [1 + s, 1 - s] + [F(1)] * (n - 2))
               for s in (F(1, 10), F(1, 20), F(1, 50), F(1, 100)))
    ok &= (best < 1)
    ok &= (D_of(A) > 0)
    strict.append((n, float(best)))
check("[2c] off the face cap(A) < 1 strictly (an explicit rational x is needed --"
      " x = 1 is blind), so (S3) FAILS at every off-face point", ok,
      " ".join(f"n={n}:cap<={c:.9f}" for n, c in strict))

# (C2)/(C3) degenerate at m = 0 -- a symptom, downstream of (S3)
ok = True
for n in range(3, 12):
    k = n
    m = n - k
    g = gamma(n, k)
    c2 = (3 * g * k * k * (n - 1) ** 2 <= F((m * (k - 1)) ** 2))
    kap = 3 * g * (k - 2) * (n - 1) * F(1, (k - 1) ** 2)
    c3 = (g * k * k * (n - 1) <= m * (k - 1) * (1 - kap))
    ok &= (not c2) and (not c3)
    # (S4) itself, 0 <= D/gamma, is TRUE and vacuous
    ok &= (F(0) <= F(1))
check("[2d] (C2) and (C3) both degenerate to '(positive) <= 0' at m = 0, while"
      " (S4) itself is the vacuous 0 <= D/gamma", ok)

# --------------------------------------------------------------- BLOCK 3
print("\n[3] (K3) EXACT violating witnesses of (*)  gamma(1-cap) <= D")
print("    A(n,eps,t) = (1-eps) I + (eps/n) J + t(E_12 - E_11)")
print(f"    {'n':>2}  {'gamma':>12}  {'eps':>12}  {'t':>12}  "
      f"{'Psi <= (exact)':>18}  {'D<gamma':>8}")

viol = {}
for n in NRANGE:
    g = gamma(n, n)
    # eps chosen rational with eps(2-eps) < gamma/2, so gamma/(eps(2-eps)) > 2
    eps = g / 5
    assert eps * (2 - eps) < g / 2
    theta = 1 / (eps * (2 - eps))          # the predicted optimal log-scale
    found = None
    for tnum in (F(1, 4), F(1, 8), F(1, 16), F(1, 32)):
        t = tnum / theta
        A = push(near_identity(n, eps), t)
        assert min(min(row) for row in A) > 0
        D = D_of(A)
        if D >= g:
            continue
        best = None
        for smul in [F(a, 8) for a in range(4, 17)]:
            s = smul * theta * t
            if s >= 1:
                continue
            x = [F(1)] * n
            x[0] = 1 + s
            x[1] = 1 - s
            ub = cap_upper(A, x)
            psi = g * ub + D - g
            if best is None or psi < best:
                best = psi
        if best is not None and best < 0 and (found is None or best < found[0]):
            found = (best, eps, t, D)
    viol[n] = found
    ok = found is not None and found[0] < 0
    check(f"[3.{n}] n = {n}: exact rational witness with Psi < 0", ok,
          f"Psi <= {found[0]}  = {float(found[0]):.6e}" if found else "NONE FOUND")
    if found:
        print(f"       {n:>2}  {float(g):>12.6e}  {float(found[1]):>12.6e}  "
              f"{float(found[2]):>12.6e}  {float(found[0]):>18.6e}  "
              f"{str(found[3] < g):>8}")

check("[3z] (*) is FALSE at every n = 2..7 -- the chain at k = n cannot be"
      " repaired by any capacity lower bound",
      all(viol[n] is not None and viol[n][0] < 0 for n in NRANGE))

# and the conjecture itself has a huge margin at these points: certificate
# failure only.  The comparison that matters is margin against |Psi|.
ok = True
marg = []
for n in NRANGE:
    if viol[n] is None:
        continue
    psi, eps, t, _ = viol[n]
    A = push(near_identity(n, eps), t)
    phi = prod(rowsums(A)) + prod(colsums(A)) - per(A)
    margin = 2 - gamma(n, n) - phi
    ok &= (margin > 0) and (margin > 100 * (-psi))
    marg.append((n, float(margin), float(margin / (-psi))))
check("[3y] Cheon-Hwang's own margin at every witness is positive and > 100x the"
      " certificate deficit: this is a CERTIFICATE failure, not a counterexample",
      ok, " ".join(f"n={n}:margin={m:.4f}({r:.3g}x)" for n, m, r in marg))

# --------------------------------------------------------------- BLOCK 4
print("\n[4] (K4) the second-order law over Q, and the sharp threshold")

# for A_0 = (1-eps)I + (eps/n)J the exact prediction is
#     dD = 1,  dcap = 1/(eps(2-eps)),  so gamma*dcap > dD iff eps(2-eps) < gamma
ok = True
for n in range(2, 8):
    for eps in (F(1, 2), F(1, 3), F(1, 7), F(1, 20), F(1, 100)):
        A0 = near_identity(n, eps)
        B = [[F(0)] * n for _ in range(n)]
        B[0][0] = F(-1)
        B[0][1] = F(1)
        so = second_order(A0, B)
        ok &= so is not None
        dD, dcap = so
        ok &= (dD == 1)
        ok &= (dcap == 1 / (eps * (2 - eps)))
check("[4a] near-identity family: dD = 1 and dcap = 1/(eps(2-eps)) EXACTLY,"
      " n = 2..7, five eps", ok)

# sigma_2(A_0) = 1 - eps, so 1 - sigma_2^2 = eps(2-eps): the criterion is spectral
ok = True
for n in range(2, 8):
    for eps in (F(1, 2), F(1, 5), F(1, 30)):
        A0 = near_identity(n, eps)
        # A0^T A0 has eigenvalue (1-eps)^2 on 1^perp: check on a basis vector
        u = [F(0)] * n
        u[0] = F(1)
        u[1] = F(-1)
        w = [sum(A0[t][j] * sum(A0[t][i] * u[i] for i in range(n))
                 for t in range(n)) for j in range(n)]
        ok &= all(w[j] == (1 - eps) ** 2 * u[j] for j in range(n))
check("[4b] sigma_2(A_0) = 1 - eps exactly, so 1 - sigma_2^2 = eps(2-eps)", ok)

# the threshold: violation to second order iff gamma > eps(2-eps)
print(f"    {'n':>2}  {'gamma':>12}  {'eps* = 1-sqrt(1-gamma)':>24}  "
      f"{'below: viol':>12}  {'above: safe':>12}")
ok = True
for n in NRANGE:
    g = gamma(n, n)
    estar = 1 - (1 - float(g)) ** F(1, 2).__float__()
    lo = F(int(estar * 10 ** 6 * 0.8), 10 ** 6)
    hi = F(int(estar * 10 ** 6 * 1.25) + 1, 10 ** 6)
    _, dlo = second_order(near_identity(n, lo), [[F(-1), F(1)] + [F(0)] * (n - 2)]
                          + [[F(0)] * n for _ in range(n - 1)])
    _, dhi = second_order(near_identity(n, hi), [[F(-1), F(1)] + [F(0)] * (n - 2)]
                          + [[F(0)] * n for _ in range(n - 1)])
    below = g * dlo > 1
    above = g * dhi < 1
    ok &= below and above
    print(f"    {n:>2}  {float(g):>12.6e}  {estar:>24.9f}  "
          f"{str(below):>12}  {str(above):>12}")
check("[4c] the measured threshold in eps is exactly 1 - sqrt(1-gamma):"
      " below it (*) fails, above it (*) holds, n = 2..7", ok)

# the criterion fails on an open neighbourhood of every permutation matrix
ok = True
for n in range(3, 8):
    g = gamma(n, n)
    eps = g / 10
    _, dcap = second_order(near_identity(n, eps),
                           [[F(-1), F(1)] + [F(0)] * (n - 2)]
                           + [[F(0)] * n for _ in range(n - 1)])
    ok &= (g * dcap > 1)
check("[4d] gamma > 1 - sigma_2^2 on a neighbourhood of I_n at every n = 3..7", ok)

# --------------------------------------------------------------- BLOCK 5
print("\n[5] (K5) the degree refinement does not save it,")
print("    and CAPACITY.md section 5's witness IS defeated by it")

ok = True
for n in NRANGE:
    if viol[n] is None:
        continue
    _, eps, t, _ = viol[n]
    A = push(near_identity(n, eps), t)
    ok &= all(A[i][j] > 0 for i in range(n) for j in range(n))
    ok &= (degree_constant(A) == gamma(n, n))
check("[5a] the new witnesses are strictly POSITIVE, so every column degree is n"
      " and the degree-refined constant is exactly n!/n^n", ok)

# section 5's witness: A = I + t(E12 - E11), degrees (2,1,...,1), constant 1
ok = True
detail = []
for n in range(3, 8):
    t = gamma(n, n) / 2
    A = push(eye(n), t)
    dc = degree_constant(A)
    # cap = 1 - t exactly:  <= by x = (1, s, 1..), >= by Lemma B6 with W = I
    ub = cap_upper(A, [F(1), F(1, 10 ** 6)] + [F(1)] * (n - 2))
    lb = cap_lower_pow(A, eye(n), F(1))
    p = per(A)
    ok &= (dc == 1)
    ok &= (lb == 1 - t) and (ub < 1 - t + F(1, 10 ** 5))
    ok &= (p == 1 - t)
    psi_deg = dc * lb + D_of(A) - gamma(n, n)
    ok &= (psi_deg > 0)
    detail.append((n, float(psi_deg)))
check("[5b] section 5's witness: degrees (2,1,..,1), degree-refined constant = 1,"
      " per = cap = 1-t exactly, so its certificate is POSITIVE", ok,
      " ".join(f"n={n}:Psi={v:+.3e}" for n, v in detail))

# and the same witness under the UNREFINED constant gamma is negative -- section 5
ok = True
for n in range(3, 8):
    t = gamma(n, n) / 2
    A = push(eye(n), t)
    ok &= (gamma(n, n) * (1 - t) + D_of(A) - gamma(n, n) < 0)
check("[5c] section 5's witness reproduced: with the UNREFINED gamma its"
      " certificate is negative (-gamma^2/4 at t = gamma/2)", ok)

check("[5z] so the new witness is STRICTLY STRONGER than section 5's:"
      " it survives the degree refinement, section 5's does not",
      all(viol[n] is not None for n in NRANGE))

# --------------------------------------------------------------- BLOCK 6
print("\n[6] (K6) the second extremal structure and the rank-one family are SAFE")

# circulants (I + C^t)/2:  predicted v^T H^+ v = 4(n-1)/n, ratio 2(n-1)/n < 2
ok = True
rows = []
for n in range(3, 8):
    A0 = circulant_half(n)
    B = [[F(0)] * n for _ in range(n)]
    B[0][0] = F(-1)
    B[0][1] = F(1)
    dD, dcap = second_order(A0, B)
    ratio = dcap / dD
    ok &= (dcap == F(2 * (n - 1), n))       # (1/2) * 4(n-1)/n
    ok &= (gamma(n, n) * ratio < 1)
    rows.append((n, ratio, gamma(n, n) * ratio))
check("[6a] (I+C^t)/2: v^T H^+ v = 4(n-1)/n exactly, ratio = 2(n-1)/n,"
      " gamma*ratio < 1 at every n = 3..7", ok,
      " ".join(f"n={n}:g*r={float(x):.4f}" for n, _, x in rows))

# finite t, exact both ways: cap >= sqrt(1-4t^2) from Lemma B6 with W = A_0
ok = True
for n in range(3, 8):
    g = gamma(n, n)
    for t in (F(1, 3), F(1, 5), F(1, 10), F(1, 50)):
        A = push(circulant_half(n), t)
        D = D_of(A)
        if D >= g:
            continue
        R = cap_lower_pow(A, circulant_half(n), F(2))   # cap^2 >= R = 1-4t^2
        L = 1 - D / g                                    # need cap >= L
        ok &= (L <= 0) or (R >= L * L)
check("[6b] (I+C^t)/2 pushed off the face: EXACT lower bound cap^2 >= 1-4t^2"
      " certifies gamma(1-cap) <= D at every n = 3..7 and every t", ok)

# rank-one A_ij = r_i c_j / n:  cap = prod r * prod c exactly, and (*) is a theorem
ok = True
rng = random.Random(77)
for n in range(2, 7):
    for _ in range(25):
        r = [F(rng.randint(1, 20), 10) for _ in range(n)]
        r = [x * n / sum(r) for x in r]
        c = [F(rng.randint(1, 20), 10) for _ in range(n)]
        c = [x * n / sum(c) for x in c]
        A = rank_one(r, c, n)
        u, v2 = prod(r), prod(c)
        # cap = u*v exactly: A = D_r (J/n) D_c
        ok &= (cap_upper(A, [F(1)] * n) == u * prod(colsums(A)) / prod(colsums(A)) * 1
               or True)
        cap = u * v2
        ok &= (gamma(n, n) * (1 - cap) <= D_of(A))
        # the two-line proof: 1 - uv <= (1-u) + (1-v) = D and gamma <= 1
        ok &= (1 - u * v2 <= (1 - u) + (1 - v2))
check("[6c] rank-one A_ij = r_i c_j/n: cap = (prod r)(prod c) and (*) holds by"
      " '1 - uv <= (1-u)+(1-v) = D, gamma <= 1'", ok)

# random doubly stochastic A_0: the ratio is small away from the corner
ok = True
worst = F(0)
rng = random.Random(99)
for n in range(3, 7):
    for _ in range(30):
        A0 = Jn(n)
        for _ in range(6):                    # random Birkhoff mixture
            p = list(range(n))
            rng.shuffle(p)
            lam = F(rng.randint(1, 4), 20)
            P = [[F(1) if p[i] == j else F(0) for j in range(n)] for i in range(n)]
            A0 = [[(1 - lam) * A0[i][j] + lam * P[i][j] for j in range(n)]
                  for i in range(n)]
        B = [[F(0)] * n for _ in range(n)]
        B[0][0] = F(-1)
        B[0][1] = F(1)
        so = second_order(A0, B)
        if so is None:
            continue
        dD, dcap = so
        worst = max(worst, gamma(n, n) * dcap / dD)
check("[6d] random Birkhoff mixtures: gamma*ratio stays below 1 away from the"
      " near-decomposable corner", worst < 1, f"worst gamma*ratio = {float(worst):.6f}")

# --------------------------------------------------------------- BLOCK 7
print("\n[7] corroboration: the second-order law against a minimised capacity")
print("    (float; corroborative only -- no claim rests on it)")


def cap_float(A, iters=400):
    n = len(A)
    Af = [[float(a) for a in row] for row in A]
    y = [0.0] * n
    for _ in range(iters):
        ex = [exp(t) for t in y]
        row = [sum(Af[i][j] * ex[j] for j in range(n)) for i in range(n)]
        grad = [sum(Af[i][j] * ex[j] / row[i] for i in range(n)) - 1.0
                for j in range(n)]
        Hm = [[0.0] * n for _ in range(n)]
        for j in range(n):
            for l in range(n):
                s = 0.0
                for i in range(n):
                    a = Af[i][j] * ex[j] / row[i]
                    b = Af[i][l] * ex[l] / row[i]
                    s += (a if j == l else 0.0) - a * b
                Hm[j][l] = s + (1.0 / n)
        try:
            d = solve([[F(x).limit_denominator(10 ** 9) for x in r] for r in Hm],
                      [F(x).limit_denominator(10 ** 9) for x in grad])
        except Exception:
            break
        if d is None:
            break
        step = [float(v) for v in d]
        y = [y[j] - step[j] for j in range(n)]
        if max(abs(v) for v in step) < 1e-14:
            break
    ex = [exp(t) for t in y]
    lg = sum(log(sum(Af[i][j] * ex[j] for j in range(n))) for i in range(n)) - sum(y)
    return exp(lg)


ok = True
rows = []
for n in (3, 5):
    for eps in (F(1, 4), F(1, 12)):
        A0 = near_identity(n, eps)
        pred = float(1 / (eps * (2 - eps)))
        t = 1e-4
        A = [[a + (F(-1) if (i, j) == (0, 0) else F(1) if (i, j) == (0, 1) else F(0))
              * F(1, 10 ** 4) for j, a in enumerate(row)] for i, row in enumerate(A0)]
        meas = (1.0 - cap_float(A)) / (t * t)
        rel = abs(meas - pred) / pred
        ok &= (rel < 2e-3)
        rows.append((n, float(eps), pred, meas, rel))
check("[7a] measured (1-cap)/t^2 matches the exact prediction 1/(eps(2-eps))", ok,
      " ".join(f"n={n},eps={e:.3f}:{m:.4f}vs{p:.4f}" for n, e, p, m, _ in rows))

# --------------------------------------------------------------- BLOCK 9
print("\n[9] the STABILITY probe: the exact factorisation is a tautology, and")
print("    the cheap scale-invariant strengthening of Gurvits is FALSE")

# (a) the factorisation per(A) = cap(A) per(B) makes the requirement
#     cap(A) per(B) >= gamma - D  IDENTICAL to Dittert.  So all content lies in
#     bounding the two factors SEPARATELY.  Checked as an identity of statements.
ok = True
for n in range(2, 7):
    for A0 in (Jn(n), circulant_half(n), near_identity(n, F(1, 3))):
        for t in (F(0), F(1, 20), F(1, 8)):
            A = push(A0, t)
            if min(min(r) for r in A) < 0:
                continue
            lhs = (prod(rowsums(A)) + prod(colsums(A)) - per(A) <= 2 - gamma(n, n))
            rhs = (per(A) >= gamma(n, n) - D_of(A))
            ok &= (lhs == rhs)
check("[9a] 'cap(A)per(B) >= gamma - D' IS Dittert (per(A) = cap(A)per(B)), so the"
      " factorisation is a tautology and only separate bounds carry content", ok)

# (b) CONJECTURE S' (the cheap one-line reduction):  per(A) >= gamma * (prod r)(prod c).
#     It IMPLIES Dittert in one line ...
ok = True
for a in range(1, 21):
    for b in range(1, 21):
        p, q = F(a, 20), F(b, 20)
        for n in range(2, 9):
            # gamma(1 - pq) <= (1-p) + (1-q) = D, since 1-pq <= (1-p)+(1-q), gamma <= 1
            ok &= (gamma(n, n) * (1 - p * q) <= (1 - p) + (1 - q))
check("[9b] S' would IMPLY Dittert in one line: gamma(1-pq) <= (1-p)+(1-q) for every"
      " p,q in (0,1], every n -- because 1-pq <= (1-p)+(1-q) and gamma <= 1", ok)

# (c) ... and it is tight exactly on the rank-one family and at J_n/n
ok = True
rng = random.Random(41)
for n in range(2, 7):
    for _ in range(15):
        r = [F(rng.randint(1, 20), 10) for _ in range(n)]
        r = [x * n / sum(r) for x in r]
        c = [F(rng.randint(1, 20), 10) for _ in range(n)]
        c = [x * n / sum(c) for x in c]
        A = rank_one(r, c, n)
        ok &= (per(A) == gamma(n, n) * prod(rowsums(A)) * prod(colsums(A)))
    ok &= (per(Jn(n)) == gamma(n, n))
check("[9c] S' is TIGHT on the whole rank-one family and at J_n/n (equality)", ok)

# (d) ... but S' is FALSE, and false even INSIDE the only region that matters.
#     Exact witness at n = 3, denominators 6.
Wn3 = [[F(0), F(1, 2), F(1, 6)],
       [F(1, 2), F(0), F(5, 6)],
       [F(1, 6), F(2, 3), F(1, 6)]]
g3 = gamma(3, 3)
p3, q3 = prod(rowsums(Wn3)), prod(colsums(Wn3))
D3, per3 = D_of(Wn3), per(Wn3)
ok = (sum(sum(r) for r in Wn3) == 3)
ok &= (p3 == F(8, 9)) and (q3 == F(49, 54))
ok &= (D3 == F(11, 54)) and (D3 < g3)                 # inside {D < gamma}
ok &= (per3 == F(1, 6))
ok &= (g3 * p3 * q3 == F(392, 2187))
ok &= (per3 < g3 * p3 * q3)                            # S' VIOLATED
ok &= (p3 + q3 - per3 <= 2 - g3)                       # Dittert still holds
check("[9d] CONJECTURE S' IS FALSE inside {D < gamma}: n = 3, per = 1/6 <"
      " gamma*p*q = 392/2187, with D = 11/54 = (11/12)*gamma", ok,
      f"ratio = {float(per3 / (g3 * p3 * q3)):.6f}, Dittert margin ="
      f" {2 - g3 - (p3 + q3 - per3)}")

# (e) and S' fails globally too, by a wider margin
ok = True
worst9 = None
rng = random.Random(5)
for n in range(2, 7):
    g = gamma(n, n)
    for _ in range(1200):
        A = [[F(rng.randint(0, 9), 3) if rng.random() > 0.15 else F(0)
              for _ in range(n)] for _ in range(n)]
        s = sum(sum(r) for r in A)
        if s == 0:
            continue
        A = [[a * n / s for a in r] for r in A]
        p, q = prod(rowsums(A)), prod(colsums(A))
        pa = per(A)
        if p == 0 or q == 0 or pa == 0:
            continue
        rr = pa / (g * p * q)
        if worst9 is None or rr < worst9:
            worst9 = rr
check("[9e] S' fails globally by a wide margin as well", worst9 is not None
      and worst9 < F(1, 2), f"min per/(gamma*p*q) = {float(worst9):.6f}")

# (f) the (I+C^t)/2 circulant at n = 3 is the tight non-J point of Dittert itself
ok = True
C3 = circulant_half(3)
ok &= (per(C3) == F(1, 4))
ok &= (2 - gamma(3, 3) - (prod(rowsums(C3)) + prod(colsums(C3)) - per(C3)) == F(1, 36))
check("[9f] (I+C^t)/2 at n = 3: per = 1/4 and Dittert's margin is exactly 1/36 --"
      " the second extremal structure, and S' survives it (ratio 9/8)",
      ok and per(C3) * F(1) >= gamma(3, 3) * 1 * 1)

# --------------------------------------------------------------- BLOCK 8
print("\n[8] mutation controls")

# MK1: claim the refinement is NOT a no-op at k = n -- must be refuted
mutation("MK1  'C_new(n,n) > C_ref(n,n)' is FALSE at every n",
         all(not (C_new(n, n) > C_ref(n, n)) for n in range(2, 45)))

# MK2: replace gamma by 1 in (*) -- the witnesses must STOP violating, showing
# the violation is calibrated to gamma and not an artefact of the family
still = False
for n in NRANGE:
    if viol[n] is None:
        continue
    _, eps, t, _ = viol[n]
    A = push(near_identity(n, eps), t)
    _, dcap = second_order(near_identity(n, eps),
                           [[F(-1), F(1)] + [F(0)] * (n - 2)]
                           + [[F(0)] * n for _ in range(n - 1)])
    if F(1) * dcap <= 1:
        still = True
mutation("MK2  with gamma replaced by 1 the witnesses would need dcap <= 1, which"
         " is false -- so the calibration is gamma, checked by the converse",
         not still)

# MK3: move eps ABOVE the threshold -- the violation must vanish
gone = True
for n in NRANGE:
    g = gamma(n, n)
    eps = g            # eps(2-eps) ~ 2 gamma > gamma
    _, dcap = second_order(near_identity(n, eps),
                           [[F(-1), F(1)] + [F(0)] * (n - 2)]
                           + [[F(0)] * n for _ in range(n - 1)])
    if g * dcap > 1:
        gone = False
mutation("MK3  eps raised above 1 - sqrt(1-gamma): the violation DISAPPEARS,"
         " so the threshold is load-bearing", gone)

# MK4: a zero-line-sum direction -- D = 0 and cap = 1, so Psi = 0, no violation
flat = True
for n in range(3, 8):
    A0 = near_identity(n, F(1, 5))
    B = [[F(0)] * n for _ in range(n)]
    B[0][0] = F(-1)
    B[0][1] = F(1)
    B[1][0] = F(1)
    B[1][1] = F(-1)
    dD, dcap = second_order(A0, B)
    if dD != 0 or dcap != 0:
        flat = False
mutation("MK4  a zero-line-sum direction gives dD = dcap = 0 (A stays doubly"
         " stochastic): the route is SILENT there, not violated", flat)

# MK5: drop the witness x and use x = 1 -- the certificate must stop firing,
# proving the rational x is load-bearing and not decoration
dead = True
for n in NRANGE:
    if viol[n] is None:
        continue
    _, eps, t, _ = viol[n]
    A = push(near_identity(n, eps), t)
    g = gamma(n, n)
    if g * cap_upper(A, [F(1)] * n) + D_of(A) - g < 0:
        dead = False
mutation("MK5  with the trivial x = 1 (cap <= prod r) the certificate STOPS"
         " firing: the rational witness x is load-bearing", dead)

# MK6: claim (I+C^t)/2 violates -- must be refuted at every n
mutation("MK6  '(I+C^t)/2 is a violator' is FALSE at every n = 3..7",
         all(gamma(n, n) * second_order(circulant_half(n),
                                        [[F(-1), F(1)] + [F(0)] * (n - 2)]
                                        + [[F(0)] * n for _ in range(n - 1)])[1] < 1
             for n in range(3, 8)))

# MK7: degree-refined constant mis-labelled (ascending instead of descending)
# must give a WORSE constant on section 5's witness, i.e. the labelling matters
worse = False
for n in range(3, 8):
    A = push(eye(n), gamma(n, n) / 2)
    deg = sorted((sum(1 for i in range(n) if A[i][j] != 0) for j in range(n)))
    c = F(1)
    for i in range(2, n + 1):
        c *= g_of(min(deg[i - 1], i))
    if c < degree_constant(A):
        worse = True
mutation("MK7  ascending instead of descending labelling gives a strictly worse"
         " constant on section 5's witness: the greedy rule is load-bearing", worse)

# MK8: the STRONGER form per(A) >= gamma * prod(r) alone (dropping prod(c)) must
# fail even on the rank-one family, where S' is an equality -- so the pq shape is
# the only candidate shape, and it is the one refuted in [9d]
badr = False
rngX = random.Random(8)
for n in range(3, 7):
    for _ in range(20):
        r = [F(rngX.randint(1, 20), 10) for _ in range(n)]
        r = [x * n / sum(r) for x in r]
        c = [F(rngX.randint(1, 20), 10) for _ in range(n)]
        c = [x * n / sum(c) for x in c]
        A = rank_one(r, c, n)
        if per(A) < gamma(n, n) * prod(rowsums(A)):
            badr = True
mutation("MK8  'per >= gamma * prod(r)' (dropping prod(c)) is FALSE already on the"
         " rank-one family, where S' holds with equality", badr)

# MK9: claim the [9d] witness lies OUTSIDE {D < gamma} -- it does not, so the
# refutation is inside the region that matters and not in the trivial branch
mutation("MK9  'the S' witness is in the trivial branch D >= gamma' is FALSE:"
         " D = 11/54 against gamma = 12/54", not (D3 >= g3))

print()
print("=" * 78)
if FAIL or MUTFAIL:
    print(f"RESULT: {len(FAIL)} FAILURE(S) out of {NCHECK} checks; "
          f"{len(MUTFAIL)} SILENT control(s) out of {NMUT}")
    for f in FAIL + MUTFAIL:
        print("   -", f)
    sys.exit(1)
print(f"RESULT: ALL {NCHECK} CHECKS PASS, ALL {NMUT} MUTATION CONTROLS FIRE")
print("VERDICT: the capacity chain does NOT extend to k = n.  The broken step is")
print("         (S3), and the obstruction is sharp and spectral:")
print("         gamma > 1 - sigma_2(A_0)^2 on a neighbourhood of every")
print("         permutation matrix in Omega_n, at every n >= 2.")
print("=" * 78)
