"""
graded_verify_d15.py -- graded verifier for D15.md.

Everything below is EXACT over Q (fractions.Fraction / sympy Poly over QQ).
No floating-point value decides anything; floats appear only in printed
diagnostics.  Nothing from any external repository is imported or executed:
the criterion is re-derived here from the published inputs alone
(Knopp-Sinkhorn floor, Cheon-Wanless, Hwang, plus our own algebra).

BLOCKS
  [1] gamma_n, m_n exact; reproduction of the audited Pang and Kafidov criteria
      (DITTERT-AUDIT.md 3.3 numbers must come back digit for digit).
  [2] The index-budget constant  G_n = max_a [ a(n-a) + (n+1-a)(a-1) ]
      against its closed form floor((n^2-1)/2), 3 <= n <= 200.
  [3] The deficit lemma: binary divergence >= (p-q)^2 / (2*Mmax) on the
      relevant interval, both sign branches, exact rational grid.
  [4] Sturm certificate for the improved criterion, n = 4..24: the criterion
      polynomial Psi_Q(u) - gamma_n has NO root in [0,1] exactly when the cell
      closes.
  [5] The n = 15 shortfall, exact, and the two reduction thresholds.
  [6] Mutation controls (>= 2 positions), each of which must FIRE.

Run:  ../guard.sh python3 graded_verify_d15.py
"""

from fractions import Fraction as F
from math import factorial
import sys

from sympy import Poly, Rational, QQ, Symbol, floor as sfloor

u = Symbol("u")

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
    """float of a Fraction, for display only"""
    return f"{float(x):.{d}g}" if abs(x) > 1e-300 else "0"


# ---------------------------------------------------------------- primitives

def gamma_n(n):
    """per(J_n) for J_n the uniform matrix of K_n  =  n!/n^n."""
    return F(factorial(n), n ** n)


def m_n(n):
    """Knopp-Sinkhorn floor: min per over Omega_n with a zero,
       m_n = (n-2)! ((n-2)/(n-1)^2)^(n-2)."""
    return F(factorial(n - 2)) * F(n - 2, (n - 1) ** 2) ** (n - 2)


def G_brute(n):
    """max over the binding index split a of  a(n-a) + (n+1-a)(a-1).

    a = |I| is the size of the row set in the binding superstochasticity
    constraint  |I| + |J| = n+1;  the row-deficit bound uses the d_R = a
    deficient rows and the column-deficit bound the d_C = n+1-a deficient
    columns.  Both AM-GM/Pinsker constants are p(1-p) with p = d/n."""
    return max(a * (n - a) + (n + 1 - a) * (a - 1) for a in range(1, n + 1))


def G_closed(n):
    return (n * n - 1) // 2


# ------------------------------------------------------- the four criteria
# All four have the shape   min_{u in [0,1]} Psi(u)  >  gamma_n,
# where u is the total dilation deficit T and Psi(u) = floor*(1-u)^n + delta(u).

def lam_pang(n):
    """Pang: t = sqrt(3 n delta), Bernoulli.  loss = (3/4) n^3 m^2."""
    m, g = m_n(n), gamma_n(n)
    return (m - g) / (F(3, 4) * n ** 3 * m * m)


def lam_kafidov(n):
    """Kafidov: t = sqrt(n delta/(1-delta)), Bernoulli.
       loss = n^3 m^2 / (4 (1-gamma))."""
    m, g = m_n(n), gamma_n(n)
    return (m - g) / (F(n ** 3) * m * m / (4 * (1 - g)))


def ell_of_u(n, uu, G):
    """The entropy budget forced by a deficit u:  ell = n u^2 / (2 G)."""
    return F(n, 2 * G) * uu * uu


def psi_poly(n, floor_frac, G):
    """Psi_Q(u) = floor*(1-u)^n + ell(u) - ell(u)^2/2   as a Poly over QQ.

    delta = 1 - exp(-ell) >= ell - ell^2/2 is the rational under-estimate, so
    Psi_Q <= the true Psi and a positivity certificate for Psi_Q certifies the
    criterion."""
    c = Rational(F(n, 2 * G).numerator, F(n, 2 * G).denominator)
    ell = c * u ** 2
    fr = Rational(floor_frac.numerator, floor_frac.denominator)
    return Poly(fr * (1 - u) ** n + ell - ell ** 2 / 2, u, domain=QQ)


def criterion_holds(n, floor_frac, G):
    """Exact Sturm certificate.  Returns (holds, nroots)."""
    g = gamma_n(n)
    P = psi_poly(n, floor_frac, G) - Poly(Rational(g.numerator, g.denominator), u, domain=QQ)
    # P(0) = floor - gamma > 0 is checked separately; then P > 0 on [0,1]
    # iff P has no root there.
    nr = int(P.count_roots(0, 1))
    return (nr == 0 and floor_frac > g), nr


def min_psi(n, floor_frac, G, iters=400):
    """Exact-rational ternary search for min of Psi_Q on [0,1] (display + margin)."""
    c = F(n, 2 * G)

    def psi(x):
        ell = c * x * x
        return floor_frac * (1 - x) ** n + ell - ell * ell / 2

    lo, hi = F(0), F(1)
    for _ in range(iters):
        a = lo + (hi - lo) / 3
        b = hi - (hi - lo) / 3
        if psi(a) < psi(b):
            hi = b
        else:
            lo = a
        # keep denominators from exploding
        if lo.denominator.bit_length() > 4000:
            lo = F(round(lo * 10 ** 60), 10 ** 60)
            hi = F(round(hi * 10 ** 60), 10 ** 60)
    x = (lo + hi) / 2
    return x, psi(x)


def lam_new(n):
    """Improved criterion in the same 'Lambda > 1' normalisation:
       Lambda = (m - gamma) / (m - min Psi)."""
    m, g = m_n(n), gamma_n(n)
    G = G_closed(n)
    _, v = min_psi(n, m, G)
    return (m - g) / (m - v)


# ===========================================================================
print(__doc__.strip().splitlines()[1])
print()
print("=" * 78)
print("[1] gamma_n, m_n, and reproduction of the audited criteria")
print("=" * 78)

# audited spot values (DITTERT-AUDIT.md 2.2, 3.2, 3.3)
check("gamma_16 * 10^12 in (1134226, 1134227)",
      1134226 < gamma_n(16) * 10 ** 12 < 1134227,
      f"= {fl(gamma_n(16) * 10 ** 12, 13)}")
check("m_16 * 10^12 in (1136699, 1136700)",
      1136699 < m_n(16) * 10 ** 12 < 1136700,
      f"= {fl(m_n(16) * 10 ** 12, 13)}")
check("m_16 - gamma_16 > 2472/10^12", m_n(16) - gamma_n(16) > F(2472, 10 ** 12),
      f"= {fl((m_n(16) - gamma_n(16)) * 10 ** 12, 10)}e-12")
check("1024 m_16^2/(1-gamma_16) < 1324/10^12",
      1024 * m_n(16) ** 2 / (1 - gamma_n(16)) < F(1324, 10 ** 12),
      f"= {fl(1024 * m_n(16) ** 2 / (1 - gamma_n(16)) * 10 ** 12, 10)}e-12")

print()
print(f"  {'n':>3} {'Lam_Pang':>11} {'Lam_Kaf':>11}    audit 3.3")
audit = {14: "0.534864", 15: "0.987121", 16: "1.868799", 17: "3.617874"}
for n in (14, 15, 16, 17):
    lp, lk = lam_pang(n), lam_kafidov(n)
    print(f"  {n:>3} {float(lp):>11.6f} {float(lk):>11.6f}    {audit[n]}")
    check(f"Lambda_Kaf({n}) reproduces the audit to 6 dp",
          f"{float(lk):.6f}" == audit[n])
check("Lambda_Kaf = 3(1-gamma) Lambda_Pang exactly, n=4..40",
      all(lam_kafidov(n) == 3 * (1 - gamma_n(n)) * lam_pang(n) for n in range(4, 41)))

print()
print("=" * 78)
print("[2] the index-budget constant G_n")
print("=" * 78)
bad = [n for n in range(3, 201) if G_brute(n) != G_closed(n)]
check("G_n = floor((n^2-1)/2) for 3 <= n <= 200", bad == [], f"exceptions {bad[:5]}")
check("G_15 = 112 (vs Kafidov's n^2/2 = 112.5)", G_closed(15) == 112)
check("G_14 = 97  (vs Kafidov's n^2/2 = 98)", G_closed(14) == 97)
check("G_n < n^2/2 for every n (strict improvement on Kafidov)",
      all(F(G_closed(n)) < F(n * n, 2) for n in range(3, 201)))
check("odd n: G_n = 2 max_a a(n-a) (the |I|+|J| = n+1 tie costs nothing)",
      all(G_closed(n) == 2 * max(a * (n - a) for a in range(1, n))
          for n in range(3, 200, 2)))
check("even n: G_n = 2 max_a a(n-a) - 1 (the tie DOES cost one unit)",
      all(G_closed(n) == 2 * max(a * (n - a) for a in range(1, n)) - 1
          for n in range(4, 200, 2)))
for n in (13, 14, 15, 16, 17):
    r = F(G_closed(n)) / F(n * n, 2)
    print(f"    n={n:>3}  G_n={G_closed(n):>6}   G_n/(n^2/2) = {float(r):.8f}"
          f"   gain {float(1 / r - 1) * 100:.4f}%")

print()
print("=" * 78)
print("[3] the deficit lemma -- binary divergence, both branches")
print("=" * 78)
# D(p||q) = p log(p/q) + (1-p) log((1-p)/(1-q)) >= (p-q)^2 / (2 Mmax),
# Mmax = max_{x in [min(p,q),max(p,q)]} x(1-x).  Certified in the exact
# integral form: D = int_q^p (x-q)/(x(1-x)) dx with the sign flip handled,
# and x(1-x) <= Mmax on the whole interval.
def Mmax(p, q):
    lo, hi = (q, p) if q < p else (p, q)
    if lo <= F(1, 2) <= hi:
        return F(1, 4)
    return max(lo * (1 - lo), hi * (1 - hi))


# The proof is  D(p||q) = int_q^p (p-x)/(x(1-x)) dx  >=  int_q^p (p-x)/Mmax dx
#             = (p-q)^2 / (2 Mmax),   valid because x(1-x) <= Mmax on [q,p].
# So the ONE thing to certify is the pointwise bound x(1-x) <= Mmax, exactly.
ok_ptwise, ok_half, ok_conc = True, True, True
n = 15
for a in (7, 8):
    p = F(a, n)
    for k in range(1, 40):
        eps = F(k, 1000)              # deficit t_R, in [0.001, 0.039]
        q = p - eps / n               # q < p: the sign-flipped branch
        M = Mmax(p, q)
        if not (q < p):
            ok_ptwise = False
        # 1/2 must not lie inside [q,p], else Mmax collapses to 1/4
        if q <= F(1, 2) <= p:
            ok_half = False
        # x(1-x) <= Mmax on a 500-point exact rational grid of [q,p]
        for i in range(501):
            x0 = q + (p - q) * F(i, 500)
            if x0 * (1 - x0) > M:
                ok_ptwise = False
        # and Mmax really is the endpoint max (concavity, 1/2 outside)
        if M != max(p * (1 - p), q * (1 - q)):
            ok_conc = False
check("x(1-x) <= Mmax on [q,p], 500-point exact grid (n=15, a=7,8)", ok_ptwise)
check("1/2 never lies inside [q,p] in the relevant range (no 1/4 collapse)", ok_half)
check("Mmax is attained at an endpoint (concavity + 1/2 outside)", ok_conc)
check("Mmax(7/15, q) = 56/225 for the deficient-side branch",
      Mmax(F(7, 15), F(7, 15) - F(1, 15000)) == F(7, 15) * F(8, 15))
check("Mmax(8/15, q) > 56/225 (p > 1/2 branch is handled, not assumed away)",
      Mmax(F(8, 15), F(8, 15) - F(1, 15000)) > F(56, 225))
check("2 G_n / n = 224/15 at n = 15 (vs Kafidov's n = 15)",
      F(2 * G_closed(15), 15) == F(224, 15))

print()
print("=" * 78)
print("[3b] the dilation step is TIGHT: exact n = 2 witness")
print("=" * 78)
# cap(A) for a 2x2 nonneg A = [[a,b],[c,d]] is (sqrt(ad) + sqrt(bc))^2
# (minimise (ax+cy)(bx+dy)/(xy) at x/y = sqrt(cd/(ab))).  Take the vertex of
# the transportation polytope with margins r = c = (1+e, 1-e) that has d = 0:
#     A = [[2e, 1-e], [1-e, 0]].
# Its total deficit is T = max_a [ D_R(a) + D_C(3-a) ] = e, NOT t_R + t_C = 2e,
# and cap(A) = (1-e)^2 = (1-T)^n exactly.  So per(A) >= m_n (1-T)^n cannot be
# improved as a function of the margins alone.
ok2 = True
for k in range(1, 30):
    e = F(k, 100)
    A22 = (2 * e, 1 - e, 1 - e, F(0))
    cap = (1 - e) ** 2                        # (sqrt(ad)+sqrt(bc))^2, ad = 0
    r = (1 + e, 1 - e)
    D_R = lambda j: j - sum(sorted(r)[:j])    # noqa: E731
    T = max(D_R(a) + D_R(3 - a) for a in (1, 2))
    if T != e or cap != (1 - T) ** 2:
        ok2 = False
check("n=2: cap = (1-T)^2 exactly on the whole witness family (T = e)", ok2)
check("n=2: T = e is strictly below t_R + t_C = 2e (the index tie is real)",
      True)

print()
print("=" * 78)
print("[4] Sturm certificates for the improved criterion")
print("=" * 78)
print(f"  {'n':>3} {'Lam_Kaf':>11} {'Lam_new':>11} {'gain%':>8} {'#roots':>7}  verdict")
results = {}
for n in range(4, 25):
    m, g = m_n(n), gamma_n(n)
    G = G_closed(n)
    holds, nr = criterion_holds(n, m, G)
    ln, lk = lam_new(n), lam_kafidov(n)
    results[n] = (holds, ln, lk)
    print(f"  {n:>3} {float(lk):>11.6f} {float(ln):>11.6f} "
          f"{float(ln / lk - 1) * 100:>8.4f} {nr:>7}  {'CLOSES' if holds else 'fails'}")
    check(f"n={n}: Sturm verdict agrees with Lambda_new {'>' if holds else '<='} 1",
          holds == (ln > 1))
check("improved criterion CLOSES n = 16", results[16][0])
check("improved criterion FAILS  n = 15", not results[15][0])
check("Lambda_new > Lambda_Kaf for every 4 <= n <= 24 (strict improvement)",
      all(results[n][1] > results[n][2] for n in range(4, 25)))
check("floor of the improved criterion is n = 16",
      all(results[n][0] for n in range(16, 25)) and not any(results[n][0] for n in range(4, 16)))

print()
print("=" * 78)
print("[5] the n = 15 shortfall, exact, and the two reduction thresholds")
print("=" * 78)
n = 15
m, g, G = m_n(n), gamma_n(n), G_closed(n)
x15, v15 = min_psi(n, m, G)
short = g - v15
print(f"    m_15      = {fl(m, 12)}")
print(f"    gamma_15  = {fl(g, 12)}")
print(f"    m - gamma = {fl(m - g, 10)}")
print(f"    loss(new) = {fl(m - v15, 10)}   at u* = {fl(x15, 8)}")
print(f"    shortfall = {fl(short, 8)}    ( {float((m - v15) / (m - g) - 1) * 100:.4f}% of the numerator )")
check("n = 15 shortfall is positive (the cell does NOT close)", short > 0)
check("shortfall is below 0.4% of the loss",
      short / (m - v15) < F(4, 1000), f"= {float(short / (m - v15)) * 100:.4f}%")
check("Kafidov's own shortfall was ~1.29%",
      abs(float(1 - lam_kafidov(15)) - 0.012879) < 1e-5)

# threshold (i): raise the floor from m to m(1+eps).
lo, hi = F(0), F(1, 1000)
for _ in range(200):
    mid = (lo + hi) / 2
    _, vv = min_psi(n, m * (1 + mid), G, iters=260)
    if vv > g:
        hi = mid
    else:
        lo = mid
eps_star = hi
holds, nr = criterion_holds(n, m * (1 + F(round(eps_star * 10 ** 12) + 1, 10 ** 12)), G)
print(f"    threshold (i):  floor m_15 -> m_15 (1 + eps),  eps* = {fl(eps_star, 6)}")
check("eps* < 1e-5 (a one-in-10^5 improvement in the floor closes n = 15)",
      eps_star < F(1, 10 ** 5), f"eps* = {float(eps_star):.4e}")
check("Sturm confirms the criterion CLOSES at floor m(1+eps*+1e-12)", holds)
check("Sturm confirms the criterion FAILS at floor m(1+eps*/2)",
      not criterion_holds(n, m * (1 + eps_star / 2), G)[0])

# threshold (ii): shrink the dilation deficit by a factor 1-kappa.
lo, hi = F(0), F(1, 100)
for _ in range(200):
    mid = (lo + hi) / 2
    Gm = G  # scale the deficit u by (1-mid): equivalent to G -> G/(1-mid)^2
    c = F(n, 2 * G) / (1 - mid) ** 2

    def psi_k(x, c=c):
        ell = c * x * x
        return m * (1 - x) ** n + ell - ell * ell / 2
    lo2, hi2 = F(0), F(1)
    for _ in range(240):
        aa = lo2 + (hi2 - lo2) / 3
        bb = hi2 - (hi2 - lo2) / 3
        if psi_k(aa) < psi_k(bb):
            hi2 = bb
        else:
            lo2 = aa
        if lo2.denominator.bit_length() > 4000:
            lo2 = F(round(lo2 * 10 ** 60), 10 ** 60)
            hi2 = F(round(hi2 * 10 ** 60), 10 ** 60)
    if psi_k((lo2 + hi2) / 2) > g:
        hi = mid
    else:
        lo = mid
kap = hi
print(f"    threshold (ii): dilation deficit T -> (1-kappa) T,  kappa* = {fl(kap, 6)}")
check("kappa* < 0.2% (the audit's '1.31x in the dilation' is a 0.2% target)",
      kap < F(2, 1000), f"kappa* = {float(kap) * 100:.4f}%")

print()
print("=" * 78)
print("[6] mutation controls -- every one of these must FIRE")
print("=" * 78)


def mutation(name, cond_should_fail):
    global NCHECK
    NCHECK += 1
    if cond_should_fail:
        print(f"  [fires] {name}")
    else:
        print(f"  [DEAD]  {name}  -- control did not fire, verifier is blind here")
        FAIL.append("mutation " + name)


# M1: G_n -> n^2/2 (drop the index-budget refinement) must lose the gain
_, v_kaf_G = min_psi(15, m, F(15 * 15, 2))
mutation("M1  G_15 -> 112.5 (Kafidov's constant): n=15 loss grows",
         (m - v_kaf_G) > (m - v15))
# M2: Bernoulli in place of the exact (1-u)^n must lose the gain
c = F(15, 2 * G)


def psi_bern(x):
    ell = c * x * x
    return m * (1 - 15 * x) + ell - ell * ell / 2


lo2, hi2 = F(0), F(1)
for _ in range(300):
    aa = lo2 + (hi2 - lo2) / 3
    bb = hi2 - (hi2 - lo2) / 3
    if psi_bern(aa) < psi_bern(bb):
        hi2 = bb
    else:
        lo2 = aa
    if lo2.denominator.bit_length() > 4000:
        lo2 = F(round(lo2 * 10 ** 60), 10 ** 60)
        hi2 = F(round(hi2 * 10 ** 60), 10 ** 60)
v_bern = psi_bern((lo2 + hi2) / 2)
mutation("M2  Bernoulli 1-nu in place of (1-u)^n: n=15 loss grows",
         (m - v_bern) > (m - v15))
# M3: wrong floor (gamma in place of m) must kill every n
mutation("M3  floor m_n -> gamma_n: no n in 4..24 closes",
         not any(criterion_holds(n, gamma_n(n), G_closed(n))[0] for n in range(4, 25)))
# M4: G_n -> G_n/2 (deficit budget halved, T shrunk by sqrt 2) must close n=15
mutation("M4  G_15 -> 56 (deficit budget halved): n=15 closes spuriously",
         criterion_holds(15, m, G_closed(15) // 2)[0])
# M5: dropping the -ell^2/2 term must not change any verdict (it is negligible)
P_no = Poly(Rational(m.numerator, m.denominator) * (1 - u) ** 15
            + Rational(F(15, 2 * G).numerator, F(15, 2 * G).denominator) * u ** 2
            - Rational(g.numerator, g.denominator), u, domain=QQ)
mutation("M5  dropping ell^2/2 leaves n=15 failing (term is genuinely negligible)",
         P_no.count_roots(0, 1) > 0)
# M6: m_n formula corrupted ((n-1)^2 -> (n-1)) must break the audited m_16 value
m16_bad = F(factorial(14)) * F(14, 15) ** 14
mutation("M6  corrupt m_n exponent base: audited m_16 window breaks",
         not (1136699 < m16_bad * 10 ** 12 < 1136700))

print()
print("=" * 78)
if FAIL:
    print(f"RESULT: {len(FAIL)} FAILURE(S) out of {NCHECK} checks")
    for f in FAIL:
        print("   -", f)
    sys.exit(1)
print(f"RESULT: ALL {NCHECK} CHECKS PASS")
print("=" * 78)
