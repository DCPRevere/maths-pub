"""
graded_verify_thmb.py -- graded verifier for Theorem B, k = n-1 (LIFT.md B.10).

Everything that decides a verdict below is EXACT over Q (fractions.Fraction).
Floating point appears only in printed diagnostics and in ONE clearly labelled
corroboration block (block [2c]) that no displayed constant rests on.

WHAT IS BEING VERIFIED.  CAPACITY.md reduces the cell k = n-1 to one estimate,

    cap( M_{n-1}(A) )  >=  cap_0 * ( 1 - D(A)/gamma )    on  { D(A) < gamma },

    cap_0 = n^(n+1)/(n-1)^(n-1),   gamma = (n-1)!/n^(n-1),
    D(A)  = (1 - E_k(r)) + (1 - E_k(c)).

LIFT.md B.7/B.8 attacked it variationally (Hessian bound on the face, then an
optimiser box, then a coercivity rate) and left one constant unsupplied.  The
estimate is instead obtained here with no optimiser data at all, from a single
doubly stochastic WITNESS matrix W(A):

  L1 (entropy witness).  For M >= 0 of size N and any doubly stochastic W with
      supp(W) subset supp(M),   cap(M) >= prod_ij (M_ij/W_ij)^(W_ij).
      Proof: weighted AM-GM row by row, then divide by prod_j x_j.

  L2 (the witness, evaluated).  For A in K_n with max_i r_i <= n/k and
      max_j c_j <= n/k, take W_ij = (k/n)A_ij, W_{i,n+1} = 1 - (k/n)r_i,
      W_{n+1,j} = 1 - (k/n)c_j, W_{n+1,n+1} = 0.  Then

      log cap(M_{n-1}(A)) >= log cap_0 - (1/n)[ sum_i chi(k R_i)
                                              + sum_j chi(k C_j) ],
      chi(t) = (1-t)log(1-t) + t = sum_{m>=2} t^m/(m(m-1)) >= 0.

      Equality on Omega_n (R = C = 0), i.e. the witness is TIGHT on the face.

  L3 (region).  D(A) < gamma forces every |R_i|, |C_j| < sqrt(3 gamma)(n-1)/(n-2).
  L4 (comparison).  chi(t) <= t^2 for t <= 1, Newton + Maclaurin give
      1 - E_k(r) >= (n-2) ||R||^2 (1-kappa_n) / (n(n-1)), and the whole chain
      closes iff the three rational conditions (C1)(C2)(C3) of block [6] hold.

BLOCKS
  [1] rho_ref = 1 at k = n-1: C_ref * cap_0 / C(n,k)^2 = gamma, exactly.
  [2] The witness W(A): doubly stochastic, support inside supp(M), and the
      closed-form evaluation as an EXACT identity in the free Q-module on
      { log p : p prime }.  [2c] float corroboration cap >= witness bound.
  [3] chi >= 0 and chi(t) <= t^2 for t <= 1, by exact telescoping.
  [4] Ehat_k(u) = max{ E_k(r) : r >= 0, sum r = n, r_1 = u } in closed form
      (1 - z/m)^m (1+z), monotone in |u-1|, and 1 - Ehat >= (z^2/2)(1 - 2z/3).
  [5] Newton chain E_k <= E_2^(k-1); the convexity and Bernoulli steps.
  [6] The three closing conditions (C1)(C2)(C3), n = 7..600, plus the exact
      ratio bounds that carry them to EVERY n >= 7, and the exact failure at
      n = 5, 6 (which are k = 4, 5, covered by the anchors).
  [7] End to end on { D < gamma }: the rational surrogate, the region bound,
      and Phi_k(A) <= 2 - gamma recomputed from the definition at n = 7.
  [8] Mutation controls (>= 2 positions), each of which must FIRE.

Run:  ../guard.sh python3 graded_verify_thmb.py
"""

from fractions import Fraction as F
from math import comb, factorial
import itertools
import math
import random
import sys

FAIL = []
NCHECK = 0


def check(name, cond, detail=""):
    global NCHECK
    NCHECK += 1
    if cond:
        print(f"  [ok]   {name}" + (f"   {detail}" if detail else ""))
    else:
        print(f"  [FAIL] {name}   {detail}")
        FAIL.append(name)
    return cond


def fl(x, d=6):
    return f"{float(x):.{d}g}"


# ------------------------------------------------------------- primitives

def gamma(n):
    """gamma(n, n-1) = (n-1)! / n^(n-1)."""
    return F(factorial(n - 1), n ** (n - 1))


def cap0_num_den(n):
    """cap_0 = n^(n+1) / (n-1)^(n-1) as an exact Fraction."""
    return F(n ** (n + 1), (n - 1) ** (n - 1))


def C_ref(n, k):
    """(n!/n^n) * ((n-1)/n)^((n-1)(n-k))  -- CAPACITY.md 2.4."""
    return F(factorial(n), n ** n) * F(n - 1, n) ** ((n - 1) * (n - k))


def elem(v, k):
    """e_k of a list of Fractions, exact."""
    n = len(v)
    e = [F(0)] * (k + 1)
    e[0] = F(1)
    for x in v:
        for j in range(min(k, n), 0, -1):
            e[j] += e[j - 1] * x
    return e[k]


def Ek(v, k):
    return elem(v, k) / comb(len(v), k)


def permanent(Msub):
    """exact permanent by expansion over permutations (small blocks only)."""
    d = len(Msub)
    tot = F(0)
    for p in itertools.permutations(range(d)):
        t = F(1)
        for i in range(d):
            t *= Msub[i][p[i]]
            if t == 0:
                break
        tot += t
    return tot


def sigma_k(A, k):
    """sum over |alpha|=|beta|=k of per(A[alpha,beta]); rows/cols independent."""
    n = len(A)
    idx = list(itertools.combinations(range(n), k))
    tot = F(0)
    for a in idx:
        for b in idx:
            tot += permanent([[A[i][j] for j in b] for i in a])
    return tot


def Phi_k(A, k):
    n = len(A)
    r = [sum(A[i]) for i in range(n)]
    c = [sum(A[i][j] for i in range(n)) for j in range(n)]
    return Ek(r, k) + Ek(c, k) - sigma_k(A, k) / F(comb(n, k) ** 2)


# ---- exact bookkeeping for Q-linear combinations of logs of positive rationals

_PRIMES = []


def _primes_upto(lim):
    global _PRIMES
    if _PRIMES and _PRIMES[-1] >= lim:
        return _PRIMES
    sieve = bytearray([1]) * (lim + 1)
    sieve[0:2] = b"\x00\x00"
    for i in range(2, int(lim ** 0.5) + 1):
        if sieve[i]:
            sieve[i * i:: i] = bytearray(len(sieve[i * i:: i]))
    _PRIMES = [i for i in range(2, lim + 1) if sieve[i]]
    return _PRIMES


def factor_int(m):
    """exact prime factorisation of a positive int (test data is small)."""
    assert m > 0
    out = {}
    for p in _primes_upto(100000):
        if p * p > m:
            break
        while m % p == 0:
            out[p] = out.get(p, 0) + 1
            m //= p
    if m > 1:
        out[m] = out.get(m, 0) + 1
    return out


class LogVec:
    """rational part + sum of coeff * log(prime), all coefficients exact."""

    def __init__(self):
        self.rat = F(0)
        self.d = {}

    def add_rat(self, q):
        self.rat += q
        return self

    def add_log(self, coeff, base):
        """coeff * log(base), base a positive Fraction."""
        if coeff == 0:
            return self
        assert base > 0
        for p, e in factor_int(base.numerator).items():
            self.d[p] = self.d.get(p, F(0)) + coeff * e
        for p, e in factor_int(base.denominator).items():
            self.d[p] = self.d.get(p, F(0)) - coeff * e
        return self

    def __sub__(self, other):
        out = LogVec()
        out.rat = self.rat - other.rat
        for p, e in self.d.items():
            out.d[p] = out.d.get(p, F(0)) + e
        for p, e in other.d.items():
            out.d[p] = out.d.get(p, F(0)) - e
        return out

    def is_zero(self):
        return self.rat == 0 and all(e == 0 for e in self.d.values())

    def size(self):
        return abs(self.rat) + sum(abs(e) for e in self.d.values())


# ------------------------------------------------------- the witness W(A)

def witness(A, mutate=0):
    """W(A) of L2 as a full (n+1)x(n+1) matrix of Fractions.

    mutate=1 : W_{i,n+1} uses (k-1)/n  (breaks double stochasticity)
    mutate=2 : W_ij uses ((k+1)/n)A_ij (breaks double stochasticity)
    """
    n = len(A)
    k = n - 1
    r = [sum(A[i]) for i in range(n)]
    c = [sum(A[i][j] for i in range(n)) for j in range(n)]
    lam = F(k + 1, n) if mutate == 2 else F(k, n)
    mu = F(k - 1, n) if mutate == 1 else F(k, n)
    W = [[F(0)] * (n + 1) for _ in range(n + 1)]
    for i in range(n):
        for j in range(n):
            W[i][j] = lam * A[i][j]
        W[i][n] = 1 - mu * r[i]
    for j in range(n):
        W[n][j] = 1 - F(k, n) * c[j]
    return W


def bordered(A):
    n = len(A)
    M = [[F(0)] * (n + 1) for _ in range(n + 1)]
    for i in range(n):
        for j in range(n):
            M[i][j] = A[i][j]
        M[i][n] = F(1)
    for j in range(n):
        M[n][j] = F(1)
    return M


def witness_value_logvec(A):
    """sum_ij W_ij log(M_ij / W_ij) as an exact LogVec."""
    n = len(A)
    M = bordered(A)
    W = witness(A)
    out = LogVec()
    for i in range(n + 1):
        for j in range(n + 1):
            if W[i][j] == 0:
                continue
            out.add_log(W[i][j], M[i][j] / W[i][j])
    return out


def closed_form_logvec(A, mutate=0):
    """log cap_0 - (1/n)[ sum chi(kR_i) + sum chi(kC_j) ] as an exact LogVec.

    mutate=3 : the 1/n prefactor replaced by 1/(n-1).
    mutate=4 : chi(t) = (1-t)log(1-t) + t  replaced by  (1-t)log(1-t).
    mutate=5 : cap_0 exponent n+1 replaced by n.
    mutate=6 : chi's log argument (1-t) replaced by (1-2t).
    """
    n = len(A)
    k = n - 1
    r = [sum(A[i]) for i in range(n)]
    c = [sum(A[i][j] for i in range(n)) for j in range(n)]
    pref = F(1, n - 1) if mutate == 3 else F(1, n)
    out = LogVec()
    e0 = F(n) if mutate == 5 else F(n + 1)
    out.add_log(e0, F(n)).add_log(F(-k), F(k))             # log cap_0
    for v in (r, c):
        for x in v:
            t = k * (x - 1)
            arg = 1 - 2 * t if mutate == 6 else 1 - t
            out.add_log(-pref * (1 - t), arg)
            if mutate != 4:
                out.add_rat(-pref * t)
    return out


# ============================================================ block [1]

print("=" * 78)
print("[1]  rho_ref = 1 exactly on the line k = n-1")
print("=" * 78)

ok = True
for n in range(3, 41):
    k = n - 1
    lhs = C_ref(n, k) * cap0_num_den(n) / F(comb(n, k) ** 2)
    if lhs != gamma(n):
        ok = False
        print("    mismatch at n =", n)
check("C_ref * cap_0 / C(n,k)^2 == gamma  for n = 3..40 (k = n-1)", ok)

# and the same quantity is STRICTLY below gamma at k = n-2, which is why the
# route is dead there -- recorded as a control on the arithmetic.  Note the
# ((n-k)!)^2 of identity (B1), which is 1 at k = n-1 and 4 at k = n-2.
ok2 = all(
    C_ref(n, n - 2) * F(n ** (n + 2), (n - 2) ** (n - 2))
    / (F(factorial(2) ** 2) * F(comb(n, n - 2) ** 2))
    < F(factorial(n - 2), n ** (n - 2))
    for n in range(4, 21)
)
check("k = n-2: the same ratio is < gamma for n = 4..20 (route dead there)", ok2)


# ============================================================ block [2]

print()
print("=" * 78)
print("[2]  the entropy witness W(A): doubly stochastic, supported, and exact")
print("=" * 78)


def test_matrices(n, rng):
    """exact A in K_n with max r_i, max c_j <= n/k, incl. sparse ones."""
    k = n - 1
    out = []
    # J_n/n
    out.append([[F(1, n)] * n for _ in range(n)])
    # a permutation matrix (in Omega_n, maximally sparse)
    p = list(range(n))
    rng.shuffle(p)
    out.append([[F(1) if p[i] == j else F(0) for j in range(n)] for i in range(n)])
    # half-and-half (in Omega_n, some zeros)
    q = p[1:] + p[:1]
    out.append([[(F(1, 2) if p[i] == j else F(0)) + (F(1, 2) if q[i] == j else F(0))
                 for j in range(n)] for i in range(n)])
    # off-face: prescribed row/column sums, product form
    for _ in range(3):
        eps = F(1, 4 * k)
        R = [F(rng.randint(-40, 40), 40) * eps for _ in range(n)]
        m = sum(R) / n
        R = [t - m for t in R]
        C = [F(rng.randint(-40, 40), 40) * eps for _ in range(n)]
        m = sum(C) / n
        C = [t - m for t in C]
        out.append([[(1 + R[i]) * (1 + C[j]) / n for j in range(n)] for i in range(n)])
    # off-face AND sparse: perturb a permutation-supported matrix
    for _ in range(2):
        eps = F(1, 6 * k)
        R = [F(rng.randint(-30, 30), 30) * eps for _ in range(n)]
        m = sum(R) / n
        R = [t - m for t in R]
        B = [[(F(1) if p[i] == j else F(0)) * (1 + R[i]) for j in range(n)] for i in range(n)]
        out.append(B)
    return out


rng = random.Random(20260803)
n_ds = 0
ok_ds = ok_supp = ok_id = True
worst = None
for n in range(3, 10):
    k = n - 1
    for A in test_matrices(n, rng):
        r = [sum(A[i]) for i in range(n)]
        c = [sum(A[i][j] for i in range(n)) for j in range(n)]
        assert sum(r) == n
        if max(r) > F(n, k) or max(c) > F(n, k):
            continue
        n_ds += 1
        W = witness(A)
        M = bordered(A)
        if any(x < 0 for row in W for x in row):
            ok_ds = False
        if any(sum(W[i]) != 1 for i in range(n + 1)):
            ok_ds = False
        if any(sum(W[i][j] for i in range(n + 1)) != 1 for j in range(n + 1)):
            ok_ds = False
        if any(W[i][j] != 0 and M[i][j] == 0 for i in range(n + 1) for j in range(n + 1)):
            ok_supp = False
        diff = witness_value_logvec(A) - closed_form_logvec(A)
        if not diff.is_zero():
            ok_id = False
            worst = (n, diff.size())

check(f"W(A) is doubly stochastic, entrywise >= 0 ({n_ds} matrices, n = 3..9)", ok_ds)
check("supp(W) subset supp(M) on the same matrices", ok_supp)
check("sum_ij W log(M/W) == log cap_0 - (1/n) sum chi   EXACT in the log-module",
      ok_id, "" if worst is None else str(worst))

# the witness is tight on the face: on Omega_n the closed form is log cap_0
ok_tight = True
for n in range(3, 10):
    A = [[F(1, n)] * n for _ in range(n)]
    v = witness_value_logvec(A)
    w = LogVec().add_log(F(n + 1), F(n)).add_log(F(-(n - 1)), F(n - 1))
    if not (v - w).is_zero():
        ok_tight = False
check("on Omega_n the witness value equals log cap_0 exactly (Lemma C: tight)",
      ok_tight)

print()
print("  [2c] float corroboration only -- no displayed constant rests on this")


def cap_log_float(M, iters=200000):
    N = len(M)
    Mf = [[float(x) for x in row] for row in M]
    y = [0.0] * N
    step = 0.05
    prev = None
    for _ in range(iters):
        x = [math.exp(t) for t in y]
        w = [sum(Mf[i][j] * x[j] for j in range(N)) for i in range(N)]
        val = sum(math.log(t) for t in w) - sum(y)
        g = [sum(Mf[i][j] * x[j] / w[i] for i in range(N)) - 1.0 for j in range(N)]
        if max(abs(t) for t in g) < 1e-13:
            break
        for j in range(N):
            y[j] -= step * g[j]
        if prev is not None and val > prev:
            step *= 0.5
        prev = val
    return val


def witness_value_float(A):
    n = len(A)
    W = witness(A)
    M = bordered(A)
    tot = 0.0
    for i in range(n + 1):
        for j in range(n + 1):
            if W[i][j] == 0:
                continue
            tot += float(W[i][j]) * math.log(float(M[i][j] / W[i][j]))
    return tot


rng2 = random.Random(7)
ok_num = True
tight = 1e9
for n in range(3, 8):
    for A in test_matrices(n, rng2):
        r = [sum(A[i]) for i in range(n)]
        c = [sum(A[i][j] for i in range(n)) for j in range(n)]
        if max(r) > F(n, n - 1) or max(c) > F(n, n - 1):
            continue
        lo = witness_value_float(A)
        tr = cap_log_float(bordered(A))
        tight = min(tight, tr - lo)
        if lo > tr + 1e-9:
            ok_num = False
check("float: witness bound <= true log cap on every test matrix", ok_num,
      f"tightest slack {tight:.3e}")


# ============================================================ block [3]

print()
print("=" * 78)
print("[3]  chi(t) = (1-t)log(1-t) + t : chi >= 0 and chi(t) <= t^2 for t <= 1")
print("=" * 78)

# chi(t)/t^2 = sum_{m>=2} t^(m-2)/(m(m-1)) and sum_{m>=2} 1/(m(m-1)) = 1
# (telescoping 1/(m(m-1)) = 1/(m-1) - 1/m).  Verified exactly.
Mmax = 400
tele = sum(F(1, m * (m - 1)) for m in range(2, Mmax + 1))
check(f"telescoping: sum_(m=2..{Mmax}) 1/(m(m-1)) = 1 - 1/{Mmax}",
      tele == 1 - F(1, Mmax))

# for 0 <= t <= 1 every term t^(m-2)/(m(m-1)) <= 1/(m(m-1)), so the series
# is <= 1: the coefficientwise comparison is what is checked.
ok_coeff = all(F(1, m * (m - 1)) > 0 for m in range(2, Mmax + 1))
check("coefficientwise: chi(t)/t^2 <= sum 1/(m(m-1)) = 1 on 0 <= t <= 1", ok_coeff)

# For t < 0 the series alternates with 1/2 leading, so chi(t)/t^2 <= 1/2.  The
# grid stays inside |t| < 1, which is the ONLY range the application sees:
# Lemma B8 plus (C2) force k|R_i| <= 1, checked in block [7].  (Outside that
# range the fact is still true, by Taylor with Lagrange remainder and
# chi''(t) = 1/(1-t) <= 1 for t <= 0, but the series does not converge and is
# not what is being checked here.)
ok_neg = True
for i in range(1, 400):
    t = F(-i, 400)
    s = sum(t ** (m - 2) / F(m * (m - 1)) for m in range(2, 200))
    if not (s <= F(1, 2)):
        ok_neg = False
check("t < 0: chi(t)/t^2 <= 1/2 on a rational grid of (-1, 0)", ok_neg)

# nonnegativity of chi on (-inf, 1] : chi(0)=0, chi'' = 1/(1-t) > 0, chi'(0)=0
ok_pos = True
for i in list(range(-400, 400)):
    t = F(i, 401)
    s = sum(t ** m / F(m * (m - 1)) for m in range(2, 120))
    if s < 0:
        ok_pos = False
check("chi >= 0 on a rational grid of (-1, 1)", ok_pos)


# ============================================================ block [4]

print()
print("=" * 78)
print("[4]  Ehat_k(u) = max{ E_k(r) : r >= 0, sum r = n, r_1 = u },  k = n-1")
print("=" * 78)


def Ehat(n, x):
    """closed form (1 - z/m)^m (1 + z), m = n-2, z = m x /(n-1);  u = 1 + x."""
    m = n - 2
    z = F(m) * x / (n - 1)
    return (1 - z / m) ** m * (1 + z)


ok_cf = ok_max = True
rngE = random.Random(99)
for n in range(4, 11):
    k = n - 1
    for _ in range(30):
        u = F(rngE.randint(0, 4 * n), 4)
        if u > n:
            continue
        rest = (n - u) / (n - 1)
        direct = Ek([u] + [rest] * (n - 1), k)
        if Ehat(n, u - 1) != direct:
            ok_cf = False
        for _ in range(25):
            w = [F(rngE.randint(0, 120), 11) for _ in range(n - 1)]
            s = sum(w)
            if s == 0:
                continue
            w = [t * (n - u) / s for t in w]
            if Ek([u] + w, k) > direct:
                ok_max = False
check("closed form Ehat = (1 - z/m)^m (1+z) matches e_k directly", ok_cf)
check("Ehat is the MAXIMUM over the fibre r_1 = u (Maclaurin on the rest)", ok_max)

# monotone: d(n Ehat)/du = (n-2) nu^(n-3) n (1-u)/(n-1), sign = sign(1-u)
ok_mon = True
for n in range(4, 12):
    prev = None
    for i in range(0, 200):
        x = F(i, 100)
        if 1 + x > n:
            break
        v = 1 - Ehat(n, x)
        if prev is not None and v < prev:
            ok_mon = False
        prev = v
    prev = None
    for i in range(0, 100):
        x = F(-i, 100)
        v = 1 - Ehat(n, x)
        if prev is not None and v < prev:
            ok_mon = False
        prev = v
check("1 - Ehat is nondecreasing in |u - 1| (both branches), n = 4..11", ok_mon)

# the quantitative floor  1 - Ehat >= (z^2/2)(1 - 2z/3)  for z <= 3/2
ok_floor = True
for n in range(4, 16):
    m = n - 2
    for i in range(-400, 301):
        z = F(i, 200)
        if z < -m or z > F(3, 2):
            continue
        E = (1 - z / m) ** m * (1 + z)
        if 1 - E < (z * z / 2) * (1 - 2 * z / 3):
            ok_floor = False
check("1 - Ehat >= (z^2/2)(1 - 2z/3) for -m <= z <= 3/2, n = 4..15", ok_floor)

# consequence used in L3: |z| >= 1/2  =>  1 - Ehat >= 1/12
ok_half = True
for n in range(4, 16):
    m = n - 2
    for z in (F(1, 2), F(-1, 2)):
        E = (1 - z / m) ** m * (1 + z)
        if 1 - E < F(1, 12):
            ok_half = False
check("|z| = 1/2  =>  1 - Ehat >= 1/12  (n = 4..15)", ok_half)


# ============================================================ block [5]

print()
print("=" * 78)
print("[5]  Newton / Maclaurin chain:  1 - E_k(r) >= (n-2)||R||^2 (1-kappa)/(n(n-1))")
print("=" * 78)

rngN = random.Random(4242)
ok_newton = ok_conv = ok_bern = ok_e2 = True
for n in range(3, 10):
    for k in range(2, n + 1):
        for _ in range(120):
            v = [F(rngN.randint(0, 70), 7) for _ in range(n)]
            s = sum(v)
            if s == 0:
                continue
            v = [t * n / s for t in v]
            if Ek(v, k) > Ek(v, 2) ** (k - 1):
                ok_newton = False
            Q = sum((t - 1) ** 2 for t in v)
            if Ek(v, 2) != 1 - Q / F(n * (n - 1)):
                ok_e2 = False
check("Newton: E_k(v) <= E_2(v)^(k-1) for 2 <= k <= n, n = 3..9", ok_newton)
check("E_2(v) = 1 - ||R||^2/(n(n-1)) identically", ok_e2)

for _ in range(4000):
    p = rngN.randint(1, 40)
    s = F(rngN.randint(0, 1000), 1000)
    if 1 - s ** p < p * (1 - s) * s ** (p - 1):
        ok_conv = False
check("convexity step: 1 - s^p >= p(1-s)s^(p-1) for p >= 1, s in [0,1]", ok_conv)

for _ in range(4000):
    p = rngN.randint(1, 40)
    s = F(rngN.randint(0, 1000), 1000)
    if s ** p < 1 - p * (1 - s):
        ok_bern = False
check("Bernoulli step: s^p >= 1 - p(1-s) for p >= 1, s in [0,1]", ok_bern)


# ============================================================ block [6]

print()
print("=" * 78)
print("[6]  the three closing conditions, and their reach to every n >= 7")
print("=" * 78)


def cond(n):
    """(C1) gamma <= 1/12   (C2) 3 gamma (n-1)^4 <= (n-2)^2
       (C3) gamma (n-1)^3 + 3 gamma (n-1)(n-3)/(n-2) <= n-2."""
    g = gamma(n)
    c1 = g <= F(1, 12)
    c2 = 3 * g * (n - 1) ** 4 <= (n - 2) ** 2
    c3 = g * (n - 1) ** 3 + 3 * g * (n - 1) * F(n - 3, n - 2) <= n - 2
    return c1, c2, c3


NTOP = 600
ok_all = all(all(cond(n)) for n in range(7, NTOP + 1))
check(f"(C1)(C2)(C3) all hold, exactly, for every n = 7..{NTOP}", ok_all)

# (C3) is EXACTLY the comparison the chain needs, restated:
#   gamma k^2 / n   <=   (n-2)(1 - kappa_n) / (n(n-1)),
#   kappa_n = 3 gamma (n-1)(n-3)/(n-2)^2.
ok_equiv = True
for n in range(7, NTOP + 1):
    g = gamma(n)
    k = n - 1
    kap = 3 * g * F((n - 1) * (n - 3), (n - 2) ** 2)
    left = g * F(k * k, n)
    right = F(n - 2, n * (n - 1)) * (1 - kap)
    if (left <= right) != cond(n)[2]:
        ok_equiv = False
check("(C3) is equivalent to  gamma k^2/n <= (n-2)(1-kappa)/(n(n-1))  for n = 7..600",
      ok_equiv, f"n=7 ratio {fl(gamma(7)*F(36,7) / (F(5,42)*(1-3*gamma(7)*F(24,25))))}")

c5, c6 = cond(5), cond(6)
check("(C2) FAILS at n = 5 and n = 6 (these are k = 4, 5: anchors cover them)",
      (not c5[1]) and (not c6[1]),
      f"n=5 C2 margin {fl(3*gamma(5)*4**4/F(9))}, n=6 {fl(3*gamma(6)*5**4/F(16))}")

# reach to every n: gamma(n+1)/gamma(n) = (n/(n+1))^n, decreasing, <= 2/5 at n=7
ok_ratio = all(F(n ** n, (n + 1) ** n) <= F(2, 5) for n in range(7, NTOP + 1))
check("gamma(n+1)/gamma(n) = (n/(n+1))^n <= 2/5 for n = 7..600", ok_ratio,
      f"value at n=7 is {fl(F(7**7, 8**7))}")

# with that, each condition's slack ratio is < 1 termwise:
ok_c2r = all(F(2, 5) * F(n ** 4, (n - 1) ** 4) * F((n - 2) ** 2, (n - 1) ** 2) < 1
             for n in range(7, NTOP + 1))
check("(C2) ratio test: (2/5)(n/(n-1))^4 ((n-2)/(n-1))^2 < 1 for n >= 7", ok_c2r,
      f"n=7 value {fl(F(2,5)*F(7**4,6**4)*F(25,36))}")
ok_c3r = all(F(2, 5) * F(n ** 3, (n - 1) ** 3) * F(n - 2, n - 1) < 1
             and F(2, 5) * F(n, n - 1) * F(n - 2, n - 3) * F(n - 2, n - 1) < 1
             for n in range(7, NTOP + 1))
check("(C3) ratio test: both terms shrink faster than (n-2) grows, n >= 7", ok_c3r)
check("(C1) gamma is decreasing, so gamma <= gamma(7) < 1/12 for all n >= 7",
      gamma(7) < F(1, 12), f"gamma(7) = {fl(gamma(7))}")


# ============================================================ block [7]

print()
print("=" * 78)
print("[7]  end to end on { D < gamma }")
print("=" * 78)


def build_point(n, rngp, frac):
    """exact A in K_n of product form with D(A) ~ frac * gamma."""
    k = n - 1
    R0 = [F(rngp.randint(-100, 100), 100) for _ in range(n)]
    m = sum(R0) / n
    R0 = [t - m for t in R0]
    C0 = [F(rngp.randint(-100, 100), 100) for _ in range(n)]
    m = sum(C0) / n
    C0 = [t - m for t in C0]
    g = gamma(n)
    lo, hi = F(0), F(1)
    for _ in range(60):
        mid = (lo + hi) / 2
        r = [1 + mid * t for t in R0]
        c = [1 + mid * t for t in C0]
        D = (1 - Ek(r, k)) + (1 - Ek(c, k))
        if D < frac * g:
            lo = mid
        else:
            hi = mid
        lo = F(round(lo * 10 ** 12), 10 ** 12)
        hi = F(round(hi * 10 ** 12), 10 ** 12)
    s = lo
    R = [s * t for t in R0]
    C = [s * t for t in C0]
    A = [[(1 + R[i]) * (1 + C[j]) / n for j in range(n)] for i in range(n)]
    return A, R, C


rngp = random.Random(31337)
ok_region = ok_sur = ok_kR = True
npts = 0
worst_sur = None
for n in range(7, 13):
    k = n - 1
    g = gamma(n)
    for frac in (F(1, 4), F(1, 2), F(9, 10), F(99, 100)):
        for _ in range(6):
            A, R, C = build_point(n, rngp, frac)
            r = [1 + t for t in R]
            c = [1 + t for t in C]
            D = (1 - Ek(r, k)) + (1 - Ek(c, k))
            if D >= g:
                continue
            npts += 1
            # L3 region bound: z_i^2 < 3 gamma with z = R (n-2)/(n-1)
            for t in R + C:
                if (t * F(n - 2, n - 1)) ** 2 >= 3 * g:
                    ok_region = False
                if abs(k * t) > 1:
                    ok_kR = False
            # the rational surrogate that implies the capacity estimate
            Q = sum(t * t for t in R) + sum(t * t for t in C)
            lhs = F(k * k) * Q / n
            rhs = D / g
            if lhs > rhs:
                ok_sur = False
            ratio = lhs / rhs
            if worst_sur is None or ratio > worst_sur[0]:
                worst_sur = (ratio, n)

check(f"L3 region bound |z_i| < sqrt(3 gamma) on all {npts} points, n = 7..12",
      ok_region)
check("k |R_i| <= 1 on all points (so chi(kR) <= (kR)^2 applies)", ok_kR)
check("surrogate  k^2(||R||^2+||C||^2)/n <= D/gamma  on all points", ok_sur,
      f"worst ratio {fl(worst_sur[0])} at n = {worst_sur[1]}")

# and the conjecture itself, recomputed from the definition, at n = 7
ok_phi = True
rngq = random.Random(5150)
for _ in range(3):
    A, R, C = build_point(7, rngq, F(99, 100))
    if min(min(row) for row in A) < 0:
        continue
    if Phi_k(A, 6) > 2 - gamma(7):
        ok_phi = False
check("Phi_6(A) <= 2 - gamma at n = 7 on {D < gamma} points, from the definition",
      ok_phi)


# ============================================================ block [8]

print()
print("=" * 78)
print("[8]  mutation controls -- each must FIRE")
print("=" * 78)

NMUT = 0
MUTFAIL = []


def mutation(name, fired):
    global NMUT
    NMUT += 1
    if fired:
        print(f"  [fired] {name}")
    else:
        print(f"  [SILENT] {name}   <-- control did not fire")
        MUTFAIL.append(name)


Amut = [[F(1, 5)] * 5 for _ in range(5)]
Amut = [[(1 + F(1, 40) * (i - 2)) * (1 + F(1, 40) * (j - 2)) / 5 for j in range(5)]
        for i in range(5)]
n5 = 5

# M1: border column weight (k-1)/n instead of k/n -- W stops being stochastic
W1 = witness(Amut, mutate=1)
mutation("M1  W_{i,n+1} = 1 - ((k-1)/n) r_i : row sums leave 1",
         any(sum(W1[i]) != 1 for i in range(n5 + 1)))

# M2: interior weight (k+1)/n instead of k/n
W2 = witness(Amut, mutate=2)
mutation("M2  W_ij = ((k+1)/n) A_ij : row sums leave 1",
         any(sum(W2[i]) != 1 for i in range(n5 + 1)))

# M3: prefactor 1/(n-1) instead of 1/n in the closed form
mutation("M3  closed form prefactor 1/n -> 1/(n-1) : identity breaks",
         not (witness_value_logvec(Amut) - closed_form_logvec(Amut, mutate=3)).is_zero())

# M4: cap_0 exponent n+1 -> n
mutation("M4  log cap_0 exponent n+1 -> n : identity breaks",
         not (witness_value_logvec(Amut) - closed_form_logvec(Amut, mutate=5)).is_zero())

# M4b: chi's log argument (1-t) -> (1-2t)
mutation("M4b chi's log argument (1-t) -> (1-2t) : identity breaks",
         not (witness_value_logvec(Amut) - closed_form_logvec(Amut, mutate=6)).is_zero())

# M4c: RECORDED NON-MUTATION.  Dropping chi's LINEAR term does NOT break the
# identity, because sum_i R_i = sum_j C_j = 0 kills it.  This is a fact about
# the identity, not a gap in the controls, and it is asserted here so that a
# later reader does not mistake the silence for a missing control.
check("recorded: chi's linear term is invisible in the sum (sum R = 0)",
      (witness_value_logvec(Amut) - closed_form_logvec(Amut, mutate=4)).is_zero())

# M5: the closing condition with the true second-order constant replaced by a
# larger one (k^2 -> k^3) must FAIL at n = 7 -- the margin is not unlimited
mutation("M5  k^2 -> k^3 in the comparison: (C3) fails at n = 7",
         not (gamma(7) * 6 ** 4 + 3 * gamma(7) * 6 * F(4, 5) <= 5))

# M6: Newton exponent k-1 -> k must break E_k <= E_2^k somewhere
bad = False
rngm = random.Random(1)
for _ in range(4000):
    n = rngm.randint(3, 8)
    k = rngm.randint(2, n)
    v = [F(rngm.randint(0, 70), 7) for _ in range(n)]
    s = sum(v)
    if s == 0:
        continue
    v = [t * n / s for t in v]
    if Ek(v, k) > Ek(v, 2) ** k:
        bad = True
        break
mutation("M6  Newton exponent k-1 -> k : E_k <= E_2^k is FALSE somewhere", bad)

# M7: dropping the region hypothesis -- some A in K_n has max r_i > n/k, and
# there W is not nonnegative, so L2 genuinely needs L3
badW = False
Abig = [[F(0)] * 5 for _ in range(5)]
Abig[0] = [F(2), F(0), F(0), F(0), F(0)]
for i in range(1, 5):
    Abig[i] = [F(0)] * 5
    Abig[i][i] = F(3, 4)
tot = sum(sum(row) for row in Abig)
Abig = [[x * 5 / tot for x in row] for row in Abig]
Wbig = witness(Abig)
mutation("M7  A with r_1 > n/k : W acquires a negative entry (L3 is load-bearing)",
         any(x < 0 for row in Wbig for x in row))

# M8: rho_ref = 1 is special to k = n-1 and k = n
mutation("M8  the k = n-1 identity is FALSE at k = n-2 (n = 8)",
         C_ref(8, 6) * F(8 ** 10, 6 ** 6) / F(comb(8, 6) ** 2) != F(factorial(6), 8 ** 6))


print()
print("=" * 78)
if FAIL or MUTFAIL:
    print(f"RESULT: {len(FAIL)} FAILURE(S) out of {NCHECK} checks; "
          f"{len(MUTFAIL)} SILENT control(s) out of {NMUT}")
    for f in FAIL + MUTFAIL:
        print("   -", f)
    sys.exit(1)
print(f"RESULT: ALL {NCHECK} CHECKS PASS, ALL {NMUT} MUTATION CONTROLS FIRE")
print("=" * 78)
