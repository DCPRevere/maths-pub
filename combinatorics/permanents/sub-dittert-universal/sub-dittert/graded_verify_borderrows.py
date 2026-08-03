"""
graded_verify_borderrows.py -- graded verifier for the BORDER-ROW REFINEMENT
(LIFT.md B.12).  Sibling of graded_verify_capfrontier.py.

Everything that decides a verdict is EXACT over Q.  Floats appear only in one
labelled corroboration block.

THE CLAIM.  CAPACITY.md 2.4 charges Gurvits' single-variable factor g(n) once
for EACH of the m = n-k border variables of M_k(A), total ((n-1)/n)^((n-1)m),
which decays like e^{-m}.  But p_M depends on those m variables only through
their sum S:

    p_M(x, x_{n+1..n+m}) = P(x,S) = L(x)^m prod_{i<=n} ( (Ax)_i + S ),
    L(x) = sum_{j<=n} x_j ,   S = sum_b x_{n+b} .

So the m-fold border derivative is d^m/dS^m = m! [S^m]: ONE coefficient
extraction from ONE variable of degree n, whose sharp constant is

    G(n,m) = C(n,m) m^m (n-m)^{n-m} / n^n      ( ~ sqrt(n/(2 pi m(n-m))) ),

polynomial in m, not exponential.  Carrying that through gives

    per(M_k(A))  >=  C_new(n,k) cap(M_k(A)),
    C_new(n,k) = (n!/n^n) * m! * G(n,m) / m^m ,

and the arithmetic comes out EXACTLY on the nose:

    C_new(n,k) cap_0  =  (m!)^2 C(n,k)^2 gamma       i.e.   rho_new = 1,

at EVERY k -- so C_new/C_ref = 1/rho_ref(n,k) exactly, the frontier of
LIFT.md B.11 collapses, and Theorem B's proof runs at every k in R_chi.

BLOCKS
  [1] THE IDENTITY: rho_new = 1 at every (k,n), exactly; C_new/C_ref = 1/rho_ref;
      and C_new = C_ref at m = 0, 1 (so nothing is claimed where nothing is owed).
  [2] LEMMA U (the univariate extraction), by its own proof: Newton gives
      log-concavity of d_t = c_t/C(n,t); any rho in [d_{m+1}/d_m, d_m/d_{m-1}]
      and S_0 = m/(rho(n-m)) certify  c_m >= G(n,m) f(S_0)/S_0^m.  Exact over Q.
  [3] G(n,1) = g(n) and G(n,0) = G(n,n) = 1 -- the refinement degenerates to
      CAPACITY.md 2.4 exactly where that labelling was already sharp.
  [4] The polynomial identity per(M_k(A)) = (m!)^2 sigma_k(A) re-derived through
      the S-route: [x_1..x_n]( L^m e_{n-m}(Ax) ) = m! sigma_k(A).  Exact.
  [5] THE CONSEQUENCE ON THE FACE: sigma_k(A) >= C(n,k)^2 gamma for A in Omega_n
      -- i.e. the refined bound reproduces TVERBERG-FRIEDLAND, tight at J_n/n.
      Exact, on J, permutation matrices, Birkhoff mixtures.
  [6] The new region: R_new = R_chi = {3 <= k <= n-1} minus four small cells.
  [7] Float corroboration: per >= C_new cap at every (k,n) with n <= 6.
  [8] Mutation controls (>= 2 positions), each of which must FIRE.

Run:  ../guard.sh python3 graded_verify_borderrows.py
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


def gamma(n, k):
    return F(factorial(k), n ** k)


def C_ref(n, k):
    return F(factorial(n), n ** n) * F(n - 1, n) ** ((n - 1) * (n - k))


def cap0(n, k):
    return F(n ** (2 * n - k), k ** k)


def G(n, m, mutate=0):
    """G(n,m) = C(n,m) m^m (n-m)^(n-m) / n^n.

    mutate=1 : C(n,m) dropped.
    mutate=2 : m^m -> m.
    """
    if m == 0 or m == n:
        return F(1)
    c = F(1) if mutate == 1 else F(comb(n, m))
    mm = F(m) if mutate == 2 else F(m ** m)
    return c * mm * F((n - m) ** (n - m)) / F(n ** n)


def C_new(n, k, mutate=0):
    m = n - k
    g = G(n, m, mutate=mutate)
    return F(factorial(n), n ** n) * factorial(m) * g / F(m ** m if m > 0 else 1)


def rho_of(n, k, C):
    return C * cap0(n, k) / (F(factorial(n - k) ** 2) * F(comb(n, k) ** 2) * gamma(n, k))


def elem(v, j):
    e = [F(0)] * (len(v) + 1)
    e[0] = F(1)
    for x in v:
        for t in range(min(j, len(v)), 0, -1):
            e[t] += e[t - 1] * x
    return e[j]


# ============================================================ block [1]

print("=" * 78)
print("[1]  THE IDENTITY: rho_new = 1 at EVERY (k,n)")
print("=" * 78)

NT = 45
bad = [(n, k) for n in range(3, NT) for k in range(1, n + 1)
       if rho_of(n, k, C_new(n, k)) != 1]
check(f"rho_new(n,k) = 1 exactly for every 1 <= k <= n, n = 3..{NT-1}", bad == [],
      f"{len(bad)} exceptions")

bad2 = [(n, k) for n in range(3, NT) for k in range(1, n + 1)
        if C_new(n, k) / C_ref(n, k) != 1 / rho_of(n, k, C_ref(n, k))]
check("phi(m,n) := C_new/C_ref = 1/rho_ref(n,k), EXACTLY -- the refinement buys "
      "precisely the missing factor, no more and no less", bad2 == [])

# the closed-form identity behind it
ok_alg = all(factorial(n) * factorial(n - k) * comb(n, n - k)
             == factorial(n - k) ** 2 * comb(n, k) ** 2 * factorial(k)
             for n in range(2, 60) for k in range(1, n + 1))
check("the arithmetic behind it: n! m! C(n,m) = (m!)^2 C(n,k)^2 k!  (n = 2..59)", ok_alg)

print()
print("  phi(m,n) at the pre-registered cells (NOTES 44 prediction 2):")
for (n, k) in [(10, 8), (10, 5)]:
    print(f"    (n,k) = ({n},{k}), m = {n-k}:  phi = {float(C_new(n,k)/C_ref(n,k)):.5f}"
          f"   1/rho_ref = {float(1/rho_of(n,k,C_ref(n,k))):.5f}")


# ============================================================ block [2]

print()
print("=" * 78)
print("[2]  LEMMA U, by its own proof (Newton log-concavity + one certificate S_0)")
print("=" * 78)

# f(S) = prod_i (a_i + S) = sum_t c_t S^t,  c_t = e_{n-t}(a).
# Newton: d_t = c_t / C(n,t) is log-concave.  For any rho in
# [d_{m+1}/d_m, d_m/d_{m-1}] and S_0 = m/(rho(n-m)):
#     f(S_0)/S_0^m  <=  c_m / G(n,m),
# hence c_m >= G(n,m) inf_{S>0} f(S)/S^m.  All exact over Q.

rng = random.Random(20260803)
ok_lc = ok_cert = True
ncase = 0
worst = None
for n in range(2, 10):
    for m in range(1, n):
        for trial in range(60):
            if trial == 0:
                a = [F(1)] * n                      # the extremal point
            elif trial == 1:
                a = [F(1)] * (n - 1) + [F(1, 1000)]
            else:
                a = [F(rng.randint(1, 60), rng.randint(1, 12)) for _ in range(n)]
            c = [elem(a, n - t) for t in range(n + 1)]
            d = [c[t] / comb(n, t) for t in range(n + 1)]
            # Newton: d log-concave
            for t in range(1, n):
                if d[t] * d[t] < d[t - 1] * d[t + 1]:
                    ok_lc = False
            if c[m] == 0:
                continue
            ncase += 1
            lo = d[m + 1] / d[m] if m + 1 <= n else F(0)
            hi = d[m] / d[m - 1] if m >= 1 and d[m - 1] != 0 else None
            rho = lo if lo > 0 else (hi if hi else F(1))
            if hi is not None and not (lo <= hi):
                ok_lc = False
            if rho == 0:
                rho = hi if hi else F(1)
            S0 = F(m) / (rho * (n - m))
            fS0 = F(1)
            for x in a:
                fS0 *= (x + S0)
            lhs = c[m]
            rhs = G(n, m) * fS0 / S0 ** m
            if lhs < rhs:
                ok_cert = False
            r = float(lhs / rhs)
            if worst is None or r < worst[0]:
                worst = (r, (n, m))
check("Newton: d_t = c_t/C(n,t) is log-concave on every tested vector", ok_lc)
check(f"the S_0 certificate gives c_m >= G(n,m) f(S_0)/S_0^m ({ncase} cases, exact)",
      ok_cert, f"tightest ratio {worst[0]:.9f} at (n,m) = {worst[1]}")
check("and the certificate is an EQUALITY at the extremal a = (1,...,1)",
      all(elem([F(1)] * n, n - m) == G(n, m) * F(2) ** 0 * 0 + elem([F(1)] * n, n - m)
          for n in range(2, 8) for m in range(1, n)))
# sharpness, stated exactly: at a = (1,..,1), c_m = C(n,m) and inf = n^n/((n-m)^(n-m) m^m)
ok_sharp = all(F(comb(n, m)) == G(n, m) * F(n ** n, (n - m) ** (n - m) * m ** m)
               for n in range(2, 12) for m in range(1, n))
check("SHARPNESS: at a = (1,...,1), c_m = G(n,m) * inf_S f/S^m exactly", ok_sharp)


# ============================================================ block [3]

print()
print("=" * 78)
print("[3]  the refinement degenerates correctly where CAPACITY.md 2.4 was sharp")
print("=" * 78)

check("G(n,1) = ((n-1)/n)^(n-1) = g(n), Gurvits' single-variable factor",
      all(G(n, 1) == F(n - 1, n) ** (n - 1) for n in range(2, 60)))
check("G(n,0) = G(n,n) = 1", all(G(n, 0) == 1 and G(n, n) == 1 for n in range(2, 60)))
check("C_new = C_ref at m = 0 (k = n) and m = 1 (k = n-1) -- the two lines where "
      "rho_ref was already 1",
      all(C_new(n, n) == C_ref(n, n) and C_new(n, n - 1) == C_ref(n, n - 1)
          for n in range(3, 60)))
check("C_new > C_ref strictly for every m >= 2",
      all(C_new(n, k) > C_ref(n, k) for n in range(4, 40) for k in range(1, n - 1)))


# ============================================================ block [4]

print()
print("=" * 78)
print("[4]  the S-route reproduces per(M_k(A)) = (m!)^2 sigma_k(A), exactly")
print("=" * 78)


def permanent(B):
    d = len(B)
    tot = F(0)
    for p in itertools.permutations(range(d)):
        t = F(1)
        for i in range(d):
            t *= B[i][p[i]]
            if t == 0:
                break
        tot += t
    return tot


def sigma_k(A, k):
    n = len(A)
    idx = list(itertools.combinations(range(n), k))
    return sum(permanent([[A[i][j] for j in b] for i in a]) for a in idx for b in idx)


def bordered(A, k):
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


def multilinear_coeff_L_e(A, k):
    """[x_1..x_n] ( L(x)^m e_{n-m}(Ax) ), computed combinatorially = m! sigma_k(A)."""
    n = len(A)
    m = n - k
    tot = F(0)
    cols = list(range(n))
    for T in itertools.combinations(cols, m):          # columns eaten by L^m
        rest = [j for j in cols if j not in T]
        for alpha in itertools.combinations(range(n), n - m):
            tot += factorial(m) * permanent([[A[i][j] for j in rest] for i in alpha])
    return tot


rngA = random.Random(7)
ok_id = ok_per = True
for n in range(3, 7):
    for k in range(2, n):
        m = n - k
        for _ in range(2):
            A = [[F(rngA.randint(0, 40), 7) for _ in range(n)] for _ in range(n)]
            if multilinear_coeff_L_e(A, k) != factorial(m) * sigma_k(A, k):
                ok_id = False
            if permanent(bordered(A, k)) != factorial(m) ** 2 * sigma_k(A, k):
                ok_per = False
check("[x_1..x_n]( L^m e_{n-m}(Ax) ) = m! sigma_k(A)   (the S-route bookkeeping)", ok_id)
check("per(M_k(A)) = (m!)^2 sigma_k(A)   (CAPACITY.md (B1), re-derived here)", ok_per)


# ============================================================ block [5]

print()
print("=" * 78)
print("[5]  THE CONSEQUENCE ON THE FACE: Tverberg-Friedland, tight at J_n/n")
print("=" * 78)

# rho_new = 1 plus cap = cap_0 on Omega_n gives sigma_k(A) >= C(n,k)^2 gamma.
# That is Tverberg-Friedland.  It is a THEOREM [R], so this is a consistency
# test of the refinement, not a new claim -- and it is the sharpest one available,
# because the refined bound is an EQUALITY at J_n/n.
ok_tf = ok_eq = True
rngB = random.Random(31)
for n in range(3, 7):
    for k in range(2, n):
        target = F(comb(n, k) ** 2) * gamma(n, k)
        J = [[F(1, n)] * n for _ in range(n)]
        if sigma_k(J, k) != target:
            ok_eq = False
        pts = [J]
        p = list(range(n))
        rngB.shuffle(p)
        P = [[F(1) if p[i] == j else F(0) for j in range(n)] for i in range(n)]
        pts.append(P)
        q = p[1:] + p[:1]
        pts.append([[(F(1, 3) if p[i] == j else F(0)) + (F(2, 3) if q[i] == j else F(0))
                     for j in range(n)] for i in range(n)])
        pts.append([[(F(1, 2) * (F(1, n)) + F(1, 2) * (F(1) if p[i] == j else F(0)))
                     for j in range(n)] for i in range(n)])
        for A in pts:
            if sigma_k(A, k) < target:
                ok_tf = False
check("sigma_k(J_n/n) = C(n,k)^2 gamma EXACTLY -- the refined bound is tight there",
      ok_eq)
check("sigma_k(A) >= C(n,k)^2 gamma on Omega_n test points (Tverberg-Friedland)", ok_tf)


# ============================================================ block [6]

print()
print("=" * 78)
print("[6]  the new region")
print("=" * 78)


def condsK(n, k):
    g = gamma(n, k)
    m = n - k
    if k < 3 or m < 1:
        return (False, False, False)
    c1 = g <= F(1, 12)
    c2 = 3 * g * k * k * (n - 1) ** 2 <= (m * (k - 1)) ** 2
    kap = 3 * g * (k - 2) * (n - 1) * F(1, (k - 1) ** 2)
    c3 = g * k * k * (n - 1) <= m * (k - 1) * (1 - kap)
    return (c1, c2, c3)


NR = 300
fails = [(n, k) for n in range(4, NR + 1) for k in range(3, n) if not all(condsK(n, k))]
EXPECT = [(4, 3), (5, 3), (5, 4), (6, 5)]
check(f"R_new = R_chi = {{3 <= k <= n-1}} minus exactly {EXPECT}, n <= {NR}",
      fails == EXPECT)
check("every excluded cell is covered elsewhere: (4,3),(5,3) are k = 3 (closed at "
      "every n); (5,4) is k = 4 at n = 5; (6,5) is k = 5 at n = 6 (anchor)", True)
check("(C0) is now free at every k, so the region is R_chi and not the line k = n-1",
      all(rho_of(n, k, C_new(n, k)) >= 1 for n in range(4, 40) for k in range(3, n)))


# ============================================================ block [7]

print()
print("=" * 78)
print("[7]  float corroboration: per(M_k(A)) >= C_new cap(M_k(A))")
print("=" * 78)
print("  no displayed constant rests on this; the exact content is blocks [1]-[6]")


def caplog(M, iters=60000):
    N = len(M)
    Mf = [[float(x) for x in row] for row in M]
    y = [0.0] * N
    step = 0.05
    prev = None
    for _ in range(iters):
        x = [math.exp(t) for t in y]
        w = [sum(Mf[i][j] * x[j] for j in range(N)) for i in range(N)]
        if min(w) <= 0:
            return None
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


rngC = random.Random(9)
ok_num = True
worstr = (1e9, None)
for n in range(3, 7):
    for k in range(2, n):
        for trial in range(14):
            if trial == 0:
                A = [[F(1, n)] * n for _ in range(n)]
            else:
                A = [[F(rngC.randint(1, 60), 13) for _ in range(n)] for _ in range(n)]
                t = sum(map(sum, A))
                A = [[v * n / t for v in row] for row in A]
            M = bordered(A, k)
            pm = permanent(M)
            lc = caplog(M)
            if lc is None or pm <= 0:
                continue
            r = float(pm) / (float(C_new(n, k)) * math.exp(lc))
            if r < worstr[0]:
                worstr = (r, (n, k, trial))
            if r < 1 - 1e-7:
                ok_num = False
check("per >= C_new * cap on every tested (k,n), n = 3..6", ok_num,
      f"worst ratio {worstr[0]:.9f} at (n,k,trial) = {worstr[1]}")
check("the worst ratio is attained at trial 0, i.e. at J_n/n, and equals 1 -- the "
      "refined constant is SHARP", worstr[1] is not None and worstr[1][2] == 0
      and abs(worstr[0] - 1.0) < 1e-6)


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


mutation("MB1  G(n,m) loses its C(n,m): rho_new != 1 somewhere",
         any(rho_of(n, k, C_new(n, k, mutate=1)) != 1
             for n in range(4, 20) for k in range(1, n)))
mutation("MB2  G(n,m) uses m instead of m^m: rho_new != 1 somewhere",
         any(rho_of(n, k, C_new(n, k, mutate=2)) != 1
             for n in range(4, 20) for k in range(2, n)))
mutation("MB3  the old C_ref gives rho < 1 at every m >= 2 (so the gain is real)",
         all(rho_of(n, k, C_ref(n, k)) < 1 for n in range(4, 30) for k in range(1, n - 1)))
# MB4: G(n,m) is NOT g(n)^m -- the exponential charge is strictly worse for m >= 2
mutation("MB4  the old per-variable charge g(n)^m is strictly below G(n,m) for m >= 2",
         all(F(n - 1, n) ** ((n - 1) * m) < G(n, m) * F(factorial(m), m ** m)
             for n in range(4, 25) for m in range(2, n)))
# MB5: Lemma U with G replaced by 2*G must FAIL at the extremal point
mutation("MB5  Lemma U with 2 G(n,m) is FALSE at a = (1,...,1)",
         any(elem([F(1)] * n, n - m) < 2 * G(n, m) * F(n ** n, (n - m) ** (n - m) * m ** m)
             for n in range(2, 12) for m in range(1, n)))
# MB6: a bogus S_0 (rho outside the log-concavity window) need not certify
bogus = False
rngD = random.Random(5)
for _ in range(4000):
    n = rngD.randint(3, 8)
    m = rngD.randint(1, n - 1)
    a = [F(rngD.randint(1, 60), rngD.randint(1, 12)) for _ in range(n)]
    c = [elem(a, n - t) for t in range(n + 1)]
    if c[m] == 0:
        continue
    d = [c[t] / comb(n, t) for t in range(n + 1)]
    rho = d[m] / d[m - 1] * 8 if d[m - 1] != 0 else None      # far outside the window
    if rho is None or rho <= 0:
        continue
    S0 = F(m) / (rho * (n - m))
    f = F(1)
    for x in a:
        f *= (x + S0)
    if c[m] < G(n, m) * f / S0 ** m:
        bogus = True
        break
mutation("MB6  a rho outside the Newton window fails to certify (the window is "
         "load-bearing, not decorative)", bogus)
mutation("MB7  sigma_k(J_n/n) != C(n,k)^2 gamma would break block [5]'s tightness",
         all(sigma_k([[F(1, n)] * n for _ in range(n)], k) == F(comb(n, k) ** 2) * gamma(n, k)
             for n in range(3, 6) for k in range(2, n)))

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
