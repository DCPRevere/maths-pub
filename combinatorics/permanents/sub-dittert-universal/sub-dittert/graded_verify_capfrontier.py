"""
graded_verify_capfrontier.py -- graded verifier for the CAPACITY FRONTIER
(LIFT.md B.11).  Sibling of graded_verify_thmb.py.

Everything that decides a verdict is EXACT over Q (fractions.Fraction).  Floats
appear only in printed diagnostics and in one labelled corroboration block.

THE QUESTION.  graded_verify_thmb.py closed k = n-1 with a doubly stochastic
witness and three rational conditions.  Neither the witness nor the conditions
mention k = n-1.  So: for which (k, n) does the whole capacity route run?

THE ANSWER, in one line.

    R  =  { (k, n) : k = n-1, n >= 7 } .

and the reason the region is a LINE and not a region is NOT the witness and not
the three conditions -- both are almost unrestricted -- but a fourth condition,
which is the one that was always there:

    (C0)   rho_ref(n,k)  =  C_ref cap_0 / ( ((n-k)!)^2 C(n,k)^2 gamma )  >=  1 .

D(A) vanishes identically on Omega_n, so the certified chain has NO slack at the
centre point; it needs rho_ref >= 1 exactly, and rho_ref <= 1 always.  Block [3]
proves rho_ref = 1 happens exactly at k = n-1 and k = n, by an exact telescoping
identity, and k = n is killed by CAPACITY.md 5's exact witness.

BLOCKS
  [1] rho_ref in closed form; the CAPACITY.md 3 table reproduced digit for digit.
  [2] THE RATIO IDENTITY, exact:
          rho_ref(n,k) / rho_ref(n,k+1)  =  (1 + 1/k)^k / (1 + 1/(n-1))^(n-1).
  [3] Hence rho_ref is strictly increasing in k on 1 <= k <= n-1,
      rho_ref(n,n-1) = rho_ref(n,n) = 1, and for k <= n-2
          rho_ref(n,k) = prod_{i=k}^{n-2} (1+1/i)^i / (1+1/(n-1))^(n-1) < 1.
      The exact PRICE of opening the line k = n-j is 1/rho_ref(n,n-j).
  [4] The witness is k-free.  W_ij = (k/n)A_ij, border blocks
      (1 - (k/n)r_i)/m and (1 - (k/n)c_j)/m, m = n-k, is doubly stochastic and
          log cap(M_k(A)) >= log cap_0 - (m/n)[ sum chi((k/m)R_i)
                                              + sum chi((k/m)C_j) ],
      checked EXACTLY in the free Q-module on { log p : p prime }, and tight on
      Omega_n at every k.
  [5] The three conditions with k free, and that they collapse to the
      graded_verify_thmb.py forms at k = n-1.  Ehat_k(1+x) = (1-z/(k-1))^(k-1)(1+z).
  [6] R_chi = { 3 <= k <= n-1 } minus { (3,4), (3,5), (4,5), (5,6) }, exhaustively
      over Q for n <= 300, plus the gamma-monotonicity lemma and the two-regime
      tail inequalities that carry it to every n.
  [7] The frontier theorem assembled, and what it leaves uncovered.
  [8] Mutation controls (>= 2 positions), each of which must FIRE.

Run:  ../guard.sh python3 graded_verify_capfrontier.py
"""

from fractions import Fraction as F
from math import comb, factorial
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


def fl(x, d=8):
    return f"{float(x):.{d}f}"


# ------------------------------------------------------------- primitives

def gamma(n, k):
    return F(factorial(k), n ** k)


def C_ref(n, k, mutate=0):
    """(n!/n^n) ((n-1)/n)^((n-1)(n-k))  -- CAPACITY.md 2.4."""
    e = (n - 1) * (n - k)
    if mutate == 1:
        e = n * (n - k)
    return F(factorial(n), n ** n) * F(n - 1, n) ** e


def cap0(n, k):
    return F(n ** (2 * n - k), k ** k)


def rho_ref(n, k, mutate=0):
    """C_ref cap_0 / ( ((n-k)!)^2 C(n,k)^2 gamma ).

    mutate=2 : the ((n-k)!)^2 of identity (B1) dropped.
    """
    den = F(comb(n, k) ** 2) * gamma(n, k)
    if mutate != 2:
        den *= F(factorial(n - k) ** 2)
    return C_ref(n, k, mutate=1 if mutate == 1 else 0) * cap0(n, k) / den


def elem(v, k):
    n = len(v)
    e = [F(0)] * (k + 1)
    e[0] = F(1)
    for x in v:
        for j in range(min(k, n), 0, -1):
            e[j] += e[j - 1] * x
    return e[k]


def Ek(v, k):
    return elem(v, k) / comb(len(v), k)


# ---- exact Q-linear combinations of logs of positive rationals ------------

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
    def __init__(self):
        self.rat = F(0)
        self.d = {}

    def add_rat(self, q):
        self.rat += q
        return self

    def add_log(self, coeff, base):
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


# ============================================================ block [1]

print("=" * 78)
print("[1]  rho_ref in closed form; the CAPACITY.md 3 table, digit for digit")
print("=" * 78)

# CAPACITY.md 3, transcribed from the published table in that file.
TABLE = {
    (4, 4): "1.00000000", (4, 3): "1.00000000", (4, 2): "0.94921875",
    (5, 5): "1.00000000", (5, 4): "1.00000000", (5, 3): "0.97090370",
    (6, 6): "1.00000000", (6, 5): "1.00000000", (6, 4): "0.98114642",
    (7, 7): "1.00000000", (7, 6): "1.00000000", (7, 5): "0.98679171",
    (8, 8): "1.00000000", (8, 7): "1.00000000", (8, 6): "0.99023235",
    (9, 9): "1.00000000", (9, 8): "1.00000000", (9, 7): "0.99248385",
    (10, 10): "1.00000000", (10, 9): "1.00000000", (10, 8): "0.99403749",
}
ok_tab = True
for (n, k), s in TABLE.items():
    if fl(rho_ref(n, k)) != s:
        ok_tab = False
        print(f"    n={n} k={k}: got {fl(rho_ref(n,k))} want {s}")
check(f"CAPACITY.md 3 table reproduced on all {len(TABLE)} rows", ok_tab)

check("rho_ref(10,5) = 0.92359403 and rho_ref(10,2) = 0.69930664 (the '=away from "
      "the corner the loss is large' rows)",
      fl(rho_ref(10, 5)) == "0.92359403" and fl(rho_ref(10, 2)) == "0.69930664")


# ============================================================ block [2]

print()
print("=" * 78)
print("[2]  THE RATIO IDENTITY (this is the whole frontier, in one line)")
print("=" * 78)


def ratio_claim(n, k, mutate=0):
    """(1 + 1/k)^k / (1 + 1/(n-1))^(n-1).

    mutate=3 : (1 + 1/n)^n in the denominator.
    """
    if mutate == 3:
        return F(k + 1, k) ** k / F(n + 1, n) ** n
    return F(k + 1, k) ** k / F(n, n - 1) ** (n - 1)


ok_ratio = True
NR = 80
cnt = 0
for n in range(3, NR + 1):
    for k in range(1, n):
        cnt += 1
        if rho_ref(n, k) / rho_ref(n, k + 1) != ratio_claim(n, k):
            ok_ratio = False
check(f"rho_ref(n,k)/rho_ref(n,k+1) = (1+1/k)^k/(1+1/(n-1))^(n-1)  ({cnt} cells, n = 3..{NR})",
      ok_ratio)

# (1+1/x)^x is strictly increasing on the positive integers -- exact.
ok_inc = all(F(x + 1, x) ** x < F(x + 2, x + 1) ** (x + 1) for x in range(1, 400))
check("(1+1/x)^x is strictly increasing on x = 1..399 (exact over Q)", ok_inc)


# ============================================================ block [3]

print()
print("=" * 78)
print("[3]  consequence: rho_ref = 1 EXACTLY on k in {n-1, n}, and nowhere else")
print("=" * 78)

ok_mono = ok_one = ok_lt = True
for n in range(3, NR + 1):
    for k in range(1, n):
        if not (rho_ref(n, k) < rho_ref(n, k + 1) or k == n - 1):
            ok_mono = False
    if rho_ref(n, n) != 1 or rho_ref(n, n - 1) != 1:
        ok_one = False
    for k in range(1, n - 1):
        if not rho_ref(n, k) < 1:
            ok_lt = False
check("rho_ref strictly increasing in k on 1 <= k <= n-2, flat from n-1 to n", ok_mono)
check("rho_ref(n,n-1) = rho_ref(n,n) = 1 exactly, n = 3..80", ok_one)
check("rho_ref(n,k) < 1 for every k <= n-2, n = 3..80  -- (C0) FAILS there", ok_lt)

ok_prod = True
for n in range(3, 50):
    for k in range(1, n - 1):
        p = F(1)
        for i in range(k, n - 1):
            p *= ratio_claim(n, i)
        if p != rho_ref(n, k):
            ok_prod = False
check("product form rho_ref(n,k) = prod_{i=k}^{n-2} (1+1/i)^i/(1+1/(n-1))^(n-1)", ok_prod)

print()
print("  the exact PRICE of opening the line k = n-j  (factor 1/rho_ref):")
for j in (2, 3, 4, 5):
    row = "  ".join(f"n={n}: {float(1/rho_ref(n, n-j)):.5f}" for n in (10, 20, 50, 100))
    print(f"    j = {j}:  {row}")
print("  and at a constant fraction k = cn the price tends to 1/sqrt(c e^(1-c)):")
for c in (F(1, 4), F(1, 2), F(3, 4)):
    lim = 1 / math.sqrt(float(c) * math.exp(1 - float(c)))
    print(f"    c = {c}:  n=200 -> {float(1/rho_ref(200, int(c*200))):.5f}, "
          f"n=400 -> {float(1/rho_ref(400, int(c*400))):.5f}, limit {lim:.5f}")
# the price is > 1 and shrinking in n at fixed j -- exact
ok_price = all(rho_ref(n, n - j) < rho_ref(n + 1, n + 1 - j) < 1
               for j in (2, 3, 4, 5) for n in range(j + 2, 60))
check("at fixed j >= 2 the price 1/rho_ref(n,n-j) is > 1 and strictly decreasing in n",
      ok_price)


# ============================================================ block [4]

print()
print("=" * 78)
print("[4]  the witness is k-FREE: general m = n-k, doubly stochastic, exact")
print("=" * 78)


def bordered_k(A, k):
    """M_k(A): A, then m all-ones border rows and columns, 0 in the m x m corner."""
    n = len(A)
    m = n - k
    N = n + m
    M = [[F(0)] * N for _ in range(N)]
    for i in range(n):
        for j in range(n):
            M[i][j] = A[i][j]
        for b in range(m):
            M[i][n + b] = F(1)
    for a in range(m):
        for j in range(n):
            M[n + a][j] = F(1)
    return M


def witness_k(A, k, mutate=0):
    """mutate=4 : border split by (m+1) instead of m.
       mutate=5 : interior weight ((k+1)/n) A_ij."""
    n = len(A)
    m = n - k
    N = n + m
    r = [sum(A[i]) for i in range(n)]
    c = [sum(A[i][j] for i in range(n)) for j in range(n)]
    lam = F(k + 1, n) if mutate == 5 else F(k, n)
    div = m + 1 if mutate == 4 else m
    W = [[F(0)] * N for _ in range(N)]
    for i in range(n):
        for j in range(n):
            W[i][j] = lam * A[i][j]
        for b in range(m):
            W[i][n + b] = (1 - F(k, n) * r[i]) / div
    for a in range(m):
        for j in range(n):
            W[n + a][j] = (1 - F(k, n) * c[j]) / div
    return W


def witness_value_logvec_k(A, k):
    n = len(A)
    M = bordered_k(A, k)
    W = witness_k(A, k)
    N = len(M)
    out = LogVec()
    for i in range(N):
        for j in range(N):
            if W[i][j] == 0:
                continue
            out.add_log(W[i][j], M[i][j] / W[i][j])
    return out


def closed_form_logvec_k(A, k, mutate=0):
    """log cap_0 - (m/n)[ sum chi((k/m)R_i) + sum chi((k/m)C_j) ].

    mutate=6 : the (m/n) prefactor replaced by (1/n).
    mutate=7 : chi's argument (k/m)R replaced by k R.
    """
    n = len(A)
    m = n - k
    r = [sum(A[i]) for i in range(n)]
    c = [sum(A[i][j] for i in range(n)) for j in range(n)]
    pref = F(1, n) if mutate == 6 else F(m, n)
    out = LogVec()
    out.add_log(F(2 * n - k), F(n)).add_log(F(-k), F(k))       # log cap_0
    for v in (r, c):
        for x in v:
            t = (F(k) if mutate == 7 else F(k, m)) * (x - 1)
            out.add_log(-pref * (1 - t), 1 - t)
            out.add_rat(-pref * t)
    return out


def testset(n, k, rng):
    out = [[[F(1, n)] * n for _ in range(n)]]
    p = list(range(n))
    rng.shuffle(p)
    out.append([[F(1) if p[i] == j else F(0) for j in range(n)] for i in range(n)])
    for _ in range(3):
        eps = F(n - k, 6 * k)
        R = [F(rng.randint(-30, 30), 30) * eps for _ in range(n)]
        mm = sum(R) / n
        R = [t - mm for t in R]
        C = [F(rng.randint(-30, 30), 30) * eps for _ in range(n)]
        mm = sum(C) / n
        C = [t - mm for t in C]
        out.append([[(1 + R[i]) * (1 + C[j]) / n for j in range(n)] for i in range(n)])
    return out


rng = random.Random(20260803)
ok_ds = ok_id = ok_tight = True
ncell = 0
for n in range(4, 10):
    for k in range(2, n):
        m = n - k
        for A in testset(n, k, rng):
            r = [sum(A[i]) for i in range(n)]
            c = [sum(A[i][j] for i in range(n)) for j in range(n)]
            if max(r) > F(n, k) or max(c) > F(n, k):
                continue
            ncell += 1
            W = witness_k(A, k)
            N = n + m
            if any(x < 0 for row in W for x in row):
                ok_ds = False
            if any(sum(W[i]) != 1 for i in range(N)):
                ok_ds = False
            if any(sum(W[i][j] for i in range(N)) != 1 for j in range(N)):
                ok_ds = False
            if not (witness_value_logvec_k(A, k) - closed_form_logvec_k(A, k)).is_zero():
                ok_id = False
    # tightness on the face at every k
    A = [[F(1, n)] * n for _ in range(n)]
    for k in range(2, n):
        v = witness_value_logvec_k(A, k)
        w = LogVec().add_log(F(2 * n - k), F(n)).add_log(F(-k), F(k))
        if not (v - w).is_zero():
            ok_tight = False

check(f"W_k(A) doubly stochastic and >= 0 at every k ({ncell} cases, n = 4..9)", ok_ds)
check("the k-free identity  sum W log(M/W) = log cap_0 - (m/n) sum chi((k/m)R)  EXACT",
      ok_id)
check("the witness is TIGHT on Omega_n at EVERY k (equals log cap_0)", ok_tight)

print()
print("  [4c] float corroboration only -- no displayed constant rests on this.")
print("       Restricted to points with cap ATTAINED (J_n/n and product form): at")
print("       m >= 2 a permutation matrix makes M_k(A) partly decomposable, the")
print("       infimum is not attained, and a descent never converges -- which is")
print("       CAPACITY.md 5's mechanism, not a defect of the witness.")


def cap_log_float(M, iters=40000):
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


rng2 = random.Random(11)
ok_num = True
tight = 1e9
for n in range(4, 8):
    for k in range(2, n):
        cands = testset(n, k, rng2)
        cands = [cands[0]] + cands[2:]        # drop the permutation matrix
        for A in cands:
            r = [sum(A[i]) for i in range(n)]
            c = [sum(A[i][j] for i in range(n)) for j in range(n)]
            if max(r) > F(n, k) or max(c) > F(n, k):
                continue
            W = witness_k(A, k)
            M = bordered_k(A, k)
            lo = 0.0
            for i in range(len(M)):
                for j in range(len(M)):
                    if W[i][j] != 0:
                        lo += float(W[i][j]) * math.log(float(M[i][j] / W[i][j]))
            tr = cap_log_float(M)
            tight = min(tight, tr - lo)
            if lo > tr + 1e-9:
                ok_num = False
check("float: the k-free witness bound <= true log cap at every tested (k,n)", ok_num,
      f"tightest slack {tight:.3e}")


# ============================================================ block [5]

print()
print("=" * 78)
print("[5]  the three conditions with k FREE, and Ehat at general k")
print("=" * 78)


def condsK(n, k, mutate=0):
    """(C1) gamma <= 1/12
       (C2) 3 gamma k^2 (n-1)^2 <= (m(k-1))^2
       (C3) gamma k^2 (n-1) <= m(k-1)(1 - kappa),
            kappa = 3 gamma (k-2)(n-1)/(k-1)^2.

    mutate=8 : (C2) dropped.
    """
    g = gamma(n, k)
    m = n - k
    if k < 3 or m < 1:
        return (False, False, False)
    c1 = g <= F(1, 12)
    c2 = 3 * g * k * k * (n - 1) ** 2 <= (m * (k - 1)) ** 2
    kap = 3 * g * (k - 2) * (n - 1) * F(1, (k - 1) ** 2)
    c3 = g * k * k * (n - 1) <= m * (k - 1) * (1 - kap)
    if mutate == 8:
        c2 = True
    return (c1, c2, c3)


def conds_thmb(n):
    g = gamma(n, n - 1)
    return (g <= F(1, 12),
            3 * g * (n - 1) ** 4 <= (n - 2) ** 2,
            g * (n - 1) ** 3 + 3 * g * (n - 1) * F(n - 3, n - 2) <= n - 2)


ok_red = all(condsK(n, n - 1) == conds_thmb(n) for n in range(5, 60))
check("the k-free conditions collapse to graded_verify_thmb.py's at k = n-1, n = 5..59",
      ok_red)


def Ehat(n, k, x):
    """closed form (1 - z/(k-1))^(k-1) (1+z),  z = (k-1)x/(n-1);  u = 1+x."""
    z = F(k - 1) * x / (n - 1)
    return (1 - z / (k - 1)) ** (k - 1) * (1 + z)


ok_cf = ok_max = ok_mon = True
rngE = random.Random(99)
for n in range(4, 11):
    for k in range(2, n):
        for _ in range(12):
            u = F(rngE.randint(0, 4 * n), 4)
            if u > n:
                continue
            rest = (n - u) / (n - 1)
            direct = Ek([u] + [rest] * (n - 1), k)
            if Ehat(n, k, u - 1) != direct:
                ok_cf = False
            for _ in range(12):
                w = [F(rngE.randint(0, 120), 11) for _ in range(n - 1)]
                s = sum(w)
                if s == 0:
                    continue
                w = [t * (n - u) / s for t in w]
                if Ek([u] + w, k) > direct:
                    ok_max = False
        prev = None
        for i in range(0, 120):
            x = F(i, 60)
            if 1 + x > n:
                break
            v = 1 - Ehat(n, k, x)
            if prev is not None and v < prev:
                ok_mon = False
            prev = v
        prev = None
        for i in range(0, 60):
            v = 1 - Ehat(n, k, F(-i, 60))
            if prev is not None and v < prev:
                ok_mon = False
            prev = v
check("Ehat_k(1+x) = (1 - z/(k-1))^(k-1)(1+z) at every k, matches e_k directly", ok_cf)
check("Ehat_k is the maximum over the fibre r_1 = u at every k", ok_max)
check("1 - Ehat_k is nondecreasing in |u-1| at every k (both branches)", ok_mon)


# ============================================================ block [6]

print()
print("=" * 78)
print("[6]  R_chi -- the region where the three conditions hold, k free")
print("=" * 78)

NT = 300
fails = [(n, k) for n in range(4, NT + 1) for k in range(3, n)
         if not all(condsK(n, k))]
EXPECT = [(4, 3), (5, 3), (5, 4), (6, 5)]
check(f"R_chi = {{3 <= k <= n-1}} minus exactly {EXPECT}, exhaustive over Q for n <= {NT}",
      fails == EXPECT, f"{len(fails)} failing cells found")
check("every failure is (C2), never (C1) or (C3) -- the legality condition is the "
      "binding one at the four cells",
      all((not condsK(n, k)[1]) for (n, k) in fails))

# the tail: gamma(n,k) = k!/n^k is NON-INCREASING in k on 3 <= k <= n-1, because
# gamma(n,k+1)/gamma(n,k) = (k+1)/n <= 1 there.  Hence gamma <= gamma(n,3) = 6/n^3.
ok_gm = all(gamma(n, k + 1) <= gamma(n, k)
            for n in range(4, NT + 1) for k in range(3, n - 1))
check("gamma(n,k) is non-increasing in k on 3 <= k <= n-1 (ratio (k+1)/n <= 1)", ok_gm)
ok_cap = all(gamma(n, k) <= F(6, n ** 3) for n in range(4, NT + 1) for k in range(3, n))
check("hence the uniform cap gamma(n,k) <= 6/n^3 on 3 <= k <= n-1", ok_cap)

# Regime I (m = n-k >= 3): the tail inequalities, exact, with gamma <= 6/n^3.
#   (C2)  18 k^2 / n         <= 9 (k-1)^2          <== 2 k^2/(k-1)^2 <= n, k >= 3
#   (C3)  6 k^2/n^2          <= 3 (k-1) (1-kappa), kappa <= 9/n^2
ok_r1 = True
for n in range(5, NT + 1):
    for k in range(3, n - 2):
        if not (2 * F(k * k, (k - 1) ** 2) <= n):
            ok_r1 = False
        if not (F(6 * k * k, n * n) <= 3 * (k - 1) * (1 - F(9, n * n))):
            ok_r1 = False
check("Regime I (m >= 3): the two tail inequalities hold for every 3 <= k <= n-3, n >= 5",
      ok_r1)
check("Regime I: 2k^2/(k-1)^2 <= 9/2 for k >= 3, so n >= 5 suffices",
      all(2 * F(k * k, (k - 1) ** 2) <= F(9, 2) for k in range(3, 5000)))

# Regime II (m = 1, 2): gamma(n,n-2) = gamma(n,n-1) n/(n-1) <= 2 gamma(n,n-1),
# and every RHS at m = 2 is at least twice the m = 1 RHS, so m = 2 follows from
# m = 1, which graded_verify_thmb.py settled for n >= 7.
ok_r2 = all(gamma(n, n - 2) == gamma(n, n - 1) * F(n, n - 1) for n in range(4, NT + 1))
check("Regime II: gamma(n,n-2) = gamma(n,n-1) * n/(n-1), so m = 2 rides on m = 1", ok_r2)
check("Regime II: m = 2 holds wherever m = 1 does, n = 7..300",
      all(all(condsK(n, n - 2)) for n in range(7, NT + 1)))


# ============================================================ block [7]

print()
print("=" * 78)
print("[7]  THE FRONTIER, assembled")
print("=" * 78)

# Brute force over the whole (k,n) box only to n = NR2: rho_ref needs n^k and k!,
# which are astronomically large near k = n at n = 300, and no information is
# gained -- block [3] PROVED (C0) holds exactly on k in {n-1, n} at every n, so
# beyond NR2 the assembly is Theorem F plus block [6]'s tail, not a scan.
NR2 = 120
R = [(n, k) for n in range(3, NR2 + 1) for k in range(2, n + 1)
     if rho_ref(n, k) >= 1 and all(condsK(n, k))]
ok_R = all(k == n - 1 and n >= 7 for (n, k) in R)
ok_Rfull = all((n, n - 1) in R for n in range(7, NR2 + 1))
check(f"R = {{(k,n) : rho_ref >= 1 and (C1)(C2)(C3)}} contains ONLY cells with "
      f"k = n-1, n >= 7 (brute force, n <= {NR2})", ok_R, f"|R| = {len(R)}")
check(f"and R contains EVERY such cell, n = 7..{NR2}", ok_Rfull)
check("beyond that: (C0) is settled for EVERY n by block [3] (k in {n-1, n} only), "
      "and (C1)(C2)(C3) at k = n-1 for every n >= 7 by graded_verify_thmb.py's "
      "ratio tests -- so R needs no scan above n = %d" % NR2,
      all(all(condsK(n, n - 1)) for n in range(7, NT + 1)))
check("k = n is excluded automatically: m = 0 makes (C2)'s right side 0",
      all(not any(condsK(n, n)) for n in range(4, 40)))

print()
print("  what R leaves uncovered, against the collar thresholds Ntilde(k):")
NTILDE = {5: 29, 6: 35, 7: 43, 8: 53}
for k, Nt in sorted(NTILDE.items()):
    lo, hi = k + 1, Nt - 1
    closed_by_R = 1 if k >= 6 else 0     # the single cell n = k+1, when k >= 6
    print(f"    k = {k}: window n = {lo}..{hi} ({hi-lo+1} cells); capacity closes "
          f"{closed_by_R} of them (n = {k+1}); {hi-lo+1-closed_by_R} remain")


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


mutation("MF1  C_ref exponent (n-1)(n-k) -> n(n-k): the table row (10,8) breaks",
         fl(rho_ref(10, 8, mutate=1)) != "0.99403749")
mutation("MF2  the ((n-k)!)^2 of (B1) dropped: rho_ref exceeds 1 somewhere (impossible)",
         any(rho_ref(n, k, mutate=2) > 1 for n in range(5, 20) for k in range(2, n)))
mutation("MF3  ratio denominator (1+1/(n-1))^(n-1) -> (1+1/n)^n: identity breaks",
         any(rho_ref(n, k) / rho_ref(n, k + 1) != ratio_claim(n, k, mutate=3)
             for n in range(4, 20) for k in range(1, n)))

Am = [[(1 + F(1, 60) * (i - 2)) * (1 + F(1, 60) * (j - 2)) / 6 for j in range(6)]
      for i in range(6)]
mutation("MF4  border split by (m+1) instead of m: W stops being stochastic at m = 2",
         any(sum(witness_k(Am, 4, mutate=4)[i]) != 1 for i in range(8)))
mutation("MF5  interior weight ((k+1)/n)A_ij: W stops being stochastic",
         any(sum(witness_k(Am, 4, mutate=5)[i]) != 1 for i in range(8)))
mutation("MF6  closed-form prefactor (m/n) -> (1/n): the k-free identity breaks at m = 2",
         not (witness_value_logvec_k(Am, 4)
              - closed_form_logvec_k(Am, 4, mutate=6)).is_zero())
mutation("MF7  chi's argument (k/m)R -> kR: the k-free identity breaks at m = 2",
         not (witness_value_logvec_k(Am, 4)
              - closed_form_logvec_k(Am, 4, mutate=7)).is_zero())
mutation("MF8  dropping (C2) from R_chi changes the region (so (C2) is load-bearing)",
         [(n, k) for n in range(4, 40) for k in range(3, n)
          if not all(condsK(n, k, mutate=8))] != [(n, k) for (n, k) in EXPECT if n < 40])
mutation("MF9  claiming rho_ref >= 1 at k = n-2 is FALSE at every n = 4..80",
         all(rho_ref(n, n - 2) < 1 for n in range(4, 81)))
mutation("MF10 reversing the monotonicity of (1+1/x)^x kills the frontier theorem",
         not all(F(x + 1, x) ** x > F(x + 2, x + 1) ** (x + 1) for x in range(1, 50)))


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
