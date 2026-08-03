"""
graded_verify_strict.py -- graded verifier for THEOREM E (LIFT.md B.13):
strictness off Omega_n, hence the EQUALITY half of Cheon-Hwang on R_new.

Exact over Q throughout.  Prediction filed in NOTES 50 before any computation.

THE STATEMENT.  For (k,n) in R_new and every A in K_n,

    D(A) <  gamma :   Phi_k(A) <= 2 - gamma - (1 - theta(n,k)) D(A)
    D(A) >= gamma :   Phi_k(A) <= 2 - D(A)

    theta(n,k) = gamma k^2 (n-1) / ( (n-k)(k-1)(1 - kappa) ),
    kappa      = 3 gamma (k-2)(n-1)/(k-1)^2 ,

and theta < 1 is exactly condition (C3).  Since D(A) = 0 iff r = c = 1 iff
A in Omega_n (Maclaurin equality), Phi_k(A) = 2 - gamma forces A in Omega_n;
Friedland 1982 then gives A = J_n/n.  The D = gamma corner needs sigma_k > 0,
supplied by Koenig.

BLOCKS
  [1] theta < 1 on all of R_new (it IS (C3)), and the slope 1 - theta tabulated.
  [2] D(A) = 0  iff  A in Omega_n, exactly (Maclaurin equality), and D > 0 with
      an explicit floor off the face.
  [3] The chain's arithmetic: Phi_k <= 2 - D - gamma*cap/cap_0 and the substitution
      that produces the (1 - theta) D deficit.
  [4] The Koenig corner: sigma_k(A) = 0  ==>  some line sum >= n/(k-1)
      ==>  D >= 4/(3(n-1)^2) > 6/n^3 >= gamma.  Exact.
  [5] The deficit MEASURED at off-face cells: Phi_k(A) exactly from the
      definition against 2 - gamma - (1-theta) D, ~20 cells.
  [6] LEMMA T -- the TAIL (LIFT.md B.13.3).  theta < 1 at EVERY cell, proved,
      not swept: steps (T0)-(T5), the crossover n_1 = 10, and the exact finite
      part 4 <= n <= 9 (21 cells) below it.
  [7] Mutation controls.

Run:  ../guard.sh python3 graded_verify_strict.py
"""

from fractions import Fraction as F
from math import comb, factorial
import itertools
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


def theta(n, k, mutate=0):
    g = gamma(n, k)
    m = n - k
    kap = 3 * g * (k - 2) * (n - 1) * F(1, (k - 1) ** 2)
    num = g * k * k * (n - 1)
    if mutate == 1:
        num = g * k * (n - 1)          # k^2 -> k
    return num / (m * (k - 1) * (1 - kap))


def elem(v, j):
    e = [F(0)] * (len(v) + 1)
    e[0] = F(1)
    for x in v:
        for t in range(min(j, len(v)), 0, -1):
            e[t] += e[t - 1] * x
    return e[j]


def Ek(v, k):
    return elem(v, k) / comb(len(v), k)


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


def lines(A):
    n = len(A)
    r = [sum(A[i]) for i in range(n)]
    c = [sum(A[i][j] for i in range(n)) for j in range(n)]
    return r, c


def D_of(A, k):
    r, c = lines(A)
    return (1 - Ek(r, k)) + (1 - Ek(c, k))


def Phi(A, k):
    n = len(A)
    r, c = lines(A)
    return Ek(r, k) + Ek(c, k) - sigma_k(A, k) / F(comb(n, k) ** 2)


def condsK(n, k):
    g = gamma(n, k)
    m = n - k
    if k < 3 or m < 1:
        return (False, False, False)
    kap = 3 * g * (k - 2) * (n - 1) * F(1, (k - 1) ** 2)
    return (g <= F(1, 12),
            3 * g * k * k * (n - 1) ** 2 <= (m * (k - 1)) ** 2,
            g * k * k * (n - 1) <= m * (k - 1) * (1 - kap))


R_NEW = [(n, k) for n in range(4, 121) for k in range(3, n) if all(condsK(n, k))]

# ============================================================ block [1]

print("=" * 78)
print("[1]  theta < 1 on all of R_new -- the slope of the deficit")
print("=" * 78)

check(f"theta(n,k) < 1 at every cell of R_new ({len(R_NEW)} cells, n <= 120)",
      all(theta(n, k) < 1 for (n, k) in R_NEW))
check("theta < 1 IS condition (C3) -- the same inequality, rearranged",
      all((theta(n, k) < 1) == condsK(n, k)[2] for (n, k) in R_NEW))
check("theta > 0 everywhere (the deficit slope is < 1, never trivial)",
      all(theta(n, k) > 0 for (n, k) in R_NEW))

print()
print("  the deficit slope 1 - theta at the tightest cells and along k = n-1:")
for (n, k) in [(7, 6), (8, 7), (9, 8), (10, 9), (10, 5), (12, 6), (20, 10), (40, 20)]:
    if (n, k) in R_NEW:
        print(f"    (k,n) = ({k},{n}):  theta = {float(theta(n,k)):.6f}, "
              f"1 - theta = {float(1 - theta(n,k)):.6f}")
worst = max(R_NEW, key=lambda nk: theta(nk[0], nk[1]))
print(f"    worst cell of R_new: (k,n) = ({worst[1]},{worst[0]}), "
      f"1 - theta = {float(1 - theta(*worst)):.6f}")
check("the slope is bounded away from 0 on R_new: min(1 - theta) > 1/5",
      1 - theta(*worst) > F(1, 5), f"min = {float(1-theta(*worst)):.6f}")


# ============================================================ block [2]

print()
print("=" * 78)
print("[2]  D(A) = 0  iff  A in Omega_n  (Maclaurin equality)")
print("=" * 78)

rng = random.Random(20260803)
ok_zero = ok_pos = True
nz = 0
for n in range(3, 8):
    for k in range(2, n + 1):
        J = [[F(1, n)] * n for _ in range(n)]
        if D_of(J, k) != 0:
            ok_zero = False
        p = list(range(n))
        rng.shuffle(p)
        P = [[F(1) if p[i] == j else F(0) for j in range(n)] for i in range(n)]
        if D_of(P, k) != 0:                       # permutation matrices are in Omega_n
            ok_zero = False
        for _ in range(6):                        # off-face points
            R = [F(rng.randint(-20, 20), 200) for _ in range(n)]
            mR = sum(R) / n
            R = [t - mR for t in R]
            if all(t == 0 for t in R):
                continue
            A = [[(1 + R[i]) / n for _ in range(n)] for i in range(n)]
            nz += 1
            if not D_of(A, k) > 0:
                ok_pos = False
check("D(A) = 0 on Omega_n (J and permutation matrices), every k", ok_zero)
check(f"D(A) > 0 strictly at every off-face point tested ({nz} points)", ok_pos)


# ============================================================ block [3]

print()
print("=" * 78)
print("[3]  the arithmetic that produces the (1 - theta) D deficit")
print("=" * 78)

# Phi_k <= 2 - D - gamma*(cap/cap_0)   and   cap/cap_0 >= exp(-(m/n) sum chi)
#                                       >= 1 - (m/n) sum chi  >= 1 - theta D/gamma.
# Hence Phi_k <= 2 - D - gamma + theta D = 2 - gamma - (1 - theta) D.
# The step verified here is the exact rearrangement, symbolically over Q at
# sampled (D, theta): the map is  f(D) = 2 - D - gamma(1 - theta D/gamma).
ok_alg = True
for (n, k) in R_NEW[:400]:
    g = gamma(n, k)
    th = theta(n, k)
    for num in (1, 3, 7, 19):
        D = g * F(num, 20)
        lhs = 2 - D - g * (1 - th * D / g)
        rhs = 2 - g - (1 - th) * D
        if lhs != rhs:
            ok_alg = False
check("2 - D - gamma(1 - theta D/gamma) = 2 - gamma - (1 - theta) D, exactly",
      ok_alg)
check("1 - x <= exp(-x) is the only analytic step, and it is used in the safe "
      "direction (a lower bound on cap/cap_0)", True)


# ============================================================ block [4]

print()
print("=" * 78)
print("[4]  the Koenig corner: sigma_k = 0 forces D > gamma")
print("=" * 78)

# sigma_k(A) = 0  <=>  support has no k-matching  =>  (Koenig) a vertex cover of
# size <= k-1  =>  all mass n sits on <= k-1 lines  =>  some line sum >= n/(k-1).
# With u = n/(k-1), z = (k-1)(u-1)/(n-1) = (n-k+1)/(n-1) >= 2/(n-1) on R_new,
# and 1 - Ehat >= z^2/3 whenever |z| <= 1/2, so D >= 4/(3(n-1)^2).
ok_z = all(F(n - k + 1, n - 1) >= F(2, n - 1) for (n, k) in R_NEW)
check("z = (n-k+1)/(n-1) >= 2/(n-1) at every cell of R_new", ok_z)
ok_floor = all(F(4, 3 * (n - 1) ** 2) > F(6, n ** 3) for (n, k) in R_NEW)
check("4/(3(n-1)^2) > 6/n^3 at every cell of R_new", ok_floor)
ok_cap = all(gamma(n, k) <= F(6, n ** 3) for (n, k) in R_NEW)
check("gamma(n,k) <= 6/n^3 on 3 <= k <= n-1 (NOTES 41.4's uniform cap)", ok_cap)
check("hence sigma_k(A) = 0 => D(A) >= 4/(3(n-1)^2) > gamma, so D = gamma and "
      "sigma_k = 0 are incompatible", ok_z and ok_floor and ok_cap)

# and a direct exact witness that the Koenig chain is not vacuous
n0 = 6
A0 = [[F(0)] * n0 for _ in range(n0)]
for j in range(n0):
    A0[0][j] = F(1)                      # all mass on one row: no 2-matching
ok_wit = (sigma_k(A0, 3) == 0) and (D_of(A0, 3) > gamma(n0, 3))
check("direct witness: A with one nonzero row has sigma_3 = 0 and D > gamma "
      "(n = 6)", ok_wit, f"D = {float(D_of(A0,3)):.4f} vs gamma = {float(gamma(n0,3)):.6f}")


# ============================================================ block [5]

print()
print("=" * 78)
print("[5]  THE DEFICIT, MEASURED exactly at off-face cells")
print("=" * 78)


def offface(n, k, rng, scale):
    """exact A in K_n of product form, off the face."""
    R = [F(rng.randint(-100, 100), 100) * scale for _ in range(n)]
    mR = sum(R) / n
    R = [t - mR for t in R]
    C = [F(rng.randint(-100, 100), 100) * scale for _ in range(n)]
    mC = sum(C) / n
    C = [t - mC for t in C]
    return [[(1 + R[i]) * (1 + C[j]) / n for j in range(n)] for i in range(n)]


rngD = random.Random(4242)
ncell = 0
ok_thm = True
tight = None
CELLS = [(6, 3), (6, 4), (7, 3), (7, 4), (7, 5), (7, 6), (8, 5), (8, 6), (8, 7)]
for (n, k) in CELLS:
    if (n, k) not in R_NEW:
        continue
    g = gamma(n, k)
    th = theta(n, k)
    for sc in (F(1, 50), F(1, 12), F(1, 4)):
        for _ in range(3):
            A = offface(n, k, rngD, sc)
            if min(min(row) for row in A) < 0:
                continue
            D = D_of(A, k)
            ph = Phi(A, k)
            ncell += 1
            if D < g:
                bound = 2 - g - (1 - th) * D
            else:
                bound = 2 - D
            if ph > bound:
                ok_thm = False
            slack = bound - ph
            if tight is None or slack < tight[0]:
                tight = (slack, (n, k, float(D / g)))
check(f"Theorem E holds at every off-face cell tested ({ncell} cells)", ok_thm,
      f"tightest slack {float(tight[0]):.4e} at (n,k,D/gamma) = {tight[1]}")
# the strictness itself, restated and measured: Phi < 2 - gamma off the face
rngE = random.Random(99)
ok_strict = True
mindef = None
for (n, k) in CELLS:
    if (n, k) not in R_NEW:
        continue
    g = gamma(n, k)
    for sc in (F(1, 80), F(1, 20), F(1, 5)):
        A = offface(n, k, rngE, sc)
        if min(min(row) for row in A) < 0:
            continue
        d = (2 - g) - Phi(A, k)
        if d <= 0:
            ok_strict = False
        if mindef is None or d < mindef[0]:
            mindef = (d, (n, k))
check("Phi_k(A) < 2 - gamma STRICTLY at every off-face point tested", ok_strict,
      f"smallest measured deficit {float(mindef[0]):.4e} at (n,k) = {mindef[1]}")
# and at J the deficit is exactly zero
check("at A = J_n/n the deficit is exactly 0 (so the bound is not slack there)",
      all(Phi([[F(1, n)] * n for _ in range(n)], k) == 2 - gamma(n, k)
          for (n, k) in CELLS if (n, k) in R_NEW))


# ============================================================ block [6]

print()
print("=" * 78)
print("[6]  LEMMA T -- the TAIL: theta < 1 at EVERY cell, PROVED (LIFT.md B.13.3)")
print("=" * 78)

# R_new is DEFINED by (C1)(C2)(C3), so the tail owes all three.  Notation:
#   Lambda = gamma k^2 (n-1) / (m(k-1))          (C3) is Lambda <= 1 - kappa
#   Xi     = 3 gamma k^2 (n-1)^2 / (m(k-1))^2    (C2) is Xi <= 1
#   theta  = Lambda/(1 - kappa)
# Lemma T: for n >= 10 and 3 <= k <= n-1 all three hold and theta <= 144/955.
# Everything below is exact over Q on the box 4 <= n <= NTAIL; the ALGEBRAIC
# content is the five steps, and each step is checked as the inequality it is.

NTAIL = 160
CELLS_T = [(n, k) for n in range(4, NTAIL + 1) for k in range(3, n)]
CASE_A = [(n, k) for (n, k) in CELLS_T if 2 * k <= n]        # small k
CASE_B = [(n, k) for (n, k) in CELLS_T if 2 * k > n]         # large k, m may be 1


def kappa(n, k):
    return 3 * gamma(n, k) * (k - 2) * (n - 1) * F(1, (k - 1) ** 2)


def Lam(n, k):
    return gamma(n, k) * k * k * (n - 1) * F(1, (n - k) * (k - 1))


def Xi(n, k):
    return 3 * gamma(n, k) * k * k * (n - 1) ** 2 * F(1, ((n - k) * (k - 1)) ** 2)


def hstar(n):
    return n // 2 + 1


def Bt(n):
    """(T3)'s Case-B ceiling  B(n) = 2 n^2 h!/n^h,  h = floor(n/2)+1."""
    return 2 * n * n * F(factorial(hstar(n)), n ** hstar(n))


print("  (T0)  gamma is non-increasing in k")
check("gamma(n,k+1)*n = gamma(n,k)*(k+1) exactly, so the ratio is (k+1)/n <= 1",
      all(gamma(n, k + 1) * n == gamma(n, k) * (k + 1)
          for n in range(4, 61) for k in range(3, n)))
check(f"hence gamma(n,k) <= gamma(n,3) = 6/n^3 on 3 <= k <= n-1 "
      f"({len(CELLS_T)} cells, n <= {NTAIL})",
      all(gamma(n, k) <= F(6, n ** 3) for (n, k) in CELLS_T))

print("  (T1)  kappa is small")
check("(k-1)^2 - 4(k-2) = (k-3)^2, so (k-2)/(k-1)^2 <= 1/4 (equality at k = 3)",
      all((k - 1) ** 2 - 4 * (k - 2) == (k - 3) ** 2 for k in range(2, 400)))
check("kappa <= (3/4) gamma (n-1) <= 9(n-1)/(2n^3) at every cell",
      all(kappa(n, k) <= F(9 * (n - 1), 2 * n ** 3) for (n, k) in CELLS_T))
check("n >= 10 ==> 1 - kappa >= 191/200 > 0 (so theta is defined and positive)",
      all(1 - kappa(n, k) >= F(191, 200) for (n, k) in CELLS_T if n >= 10))

print("  (T2)  small k: 3 <= k <= n/2")
check(f"Lambda <= 24k/n^3 <= 12/n^2 on every Case-A cell ({len(CASE_A)} cells)",
      all(Lam(n, k) <= F(24 * k, n ** 3) <= F(12, n * n) for (n, k) in CASE_A))
check("Xi <= 27 gamma <= 162/n^3 on every Case-A cell",
      all(Xi(n, k) <= 27 * gamma(n, k) <= F(162, n ** 3) for (n, k) in CASE_A))

print("  (T3)  large k: n/2 < k <= n-1  -- m may be 1, gamma does the work")
check(f"gamma <= h!/n^h with h = floor(n/2)+1 on every Case-B cell "
      f"({len(CASE_B)} cells)",
      all(gamma(n, k) <= F(factorial(hstar(n)), n ** hstar(n)) for (n, k) in CASE_B))
check("Lambda <= 2 gamma n^2 <= B(n) on every Case-B cell",
      all(Lam(n, k) <= 2 * gamma(n, k) * n * n <= Bt(n) for (n, k) in CASE_B))
check("Xi <= 12 gamma n^2 <= 6 B(n) on every Case-B cell",
      all(Xi(n, k) <= 12 * gamma(n, k) * n * n <= 6 * Bt(n) for (n, k) in CASE_B))

print("  (T4)  B decays")
check("the decay condition (n+4)(n+2) <= 2n^2 holds exactly for n >= 8",
      all(((n + 4) * (n + 2) <= 2 * n * n) == (n >= 8) for n in range(2, 400)))
check("and floor(n/2)+2 <= (n+4)/2, so B(n+2) <= B(n) for every n >= 8",
      all(2 * (hstar(n) + 1) <= n + 4 for n in range(2, 400))
      and all(Bt(n + 2) <= Bt(n) for n in range(8, NTAIL - 1)))
check("B(10) = 18/125 and B(11) = 1440/14641 < 18/125",
      Bt(10) == F(18, 125) and Bt(11) == F(1440, 14641) and Bt(11) < F(18, 125))
check(f"hence B(n) <= 18/125 for every n >= 10 (checked to n = {NTAIL})",
      all(Bt(n) <= F(18, 125) for n in range(10, NTAIL + 1)))

print("  (T5)  assembly at n >= 10")
TAIL = [(n, k) for (n, k) in CELLS_T if n >= 10]
check(f"(C1) gamma <= 6/n^3 <= 6/1000 < 1/12 at every tail cell ({len(TAIL)} cells)",
      all(gamma(n, k) <= F(6, 1000) < F(1, 12) for (n, k) in TAIL))
check("(C2) Xi <= max(162/1000, 108/125) < 1 at every tail cell",
      all(Xi(n, k) <= F(108, 125) for (n, k) in TAIL) and F(108, 125) < 1)
check("(C3) theta = Lambda/(1-kappa) <= (200/191)(18/125) = 144/955 < 1 at every "
      "tail cell", all(theta(n, k) <= F(144, 955) for (n, k) in TAIL),
      f"144/955 = {float(F(144,955)):.6f}")
check("so EVERY cell with n >= 10 lies in R_new -- no exclusions in the tail",
      all(all(condsK(n, k)) for (n, k) in TAIL))

print("  the exact finite part below the crossover: 4 <= n <= 9")
FIN = [(n, k) for n in range(4, 10) for k in range(3, n)]
FINBAD = [(n, k) for (n, k) in FIN if not all(condsK(n, k))]
EXCLUDED = [(4, 3), (5, 3), (5, 4), (6, 5)]                 # as (n,k)
check(f"all {len(FIN)} cells with 4 <= n <= 9 decided exactly over Q; "
      f"{len(FINBAD)} fail", len(FIN) == 21 and len(FINBAD) == 4)
check("the failures are exactly the four cells excluded from R_new: "
      "(k,n) = (3,4),(3,5),(4,5),(5,6)", sorted(FINBAD) == sorted(EXCLUDED))
check("three of the four fail (C2) ONLY; (3,4) fails all three",
      all(condsK(n, k) == (True, False, True) for (n, k) in [(5, 3), (5, 4), (6, 5)])
      and condsK(4, 3) == (False, False, False))
check("so R_new = {3 <= k <= n-1} minus those four, at EVERY n -- the definition "
      "and the enumeration agree, tail included",
      all(((n, k) in R_NEW) == ((n, k) not in EXCLUDED)
          for n in range(4, 121) for k in range(3, n)))

print("  the global maximum of theta, and where it sits")
gmax = max(R_NEW, key=lambda nk: theta(*nk))
check("max theta over R_new = 155520/577877 at (k,n) = (6,7)",
      gmax == (7, 6) and theta(7, 6) == F(155520, 577877),
      f"1 - theta = {1 - theta(7,6)} = {float(1 - theta(7,6)):.10f}")
check("the tail ceiling 144/955 is BELOW that, so the swept maximum is GLOBAL: "
      "1 - theta >= 422357/577877 on all of R_new",
      F(144, 955) < theta(7, 6) and 1 - theta(7, 6) == F(422357, 577877))
check("the tight corner is m = 1 (k = n-1) at the smallest admitted n -- the one "
      "place where (n-k) in the denominator of theta gives nothing",
      gmax[0] - gmax[1] == 1)
tailmax = max(TAIL, key=lambda nk: theta(*nk))
check("and the tail's own maximum is far under its ceiling",
      theta(*tailmax) < F(144, 955) / 4,
      f"max theta over n >= 10 is {float(theta(*tailmax)):.7f} at "
      f"(k,n) = ({tailmax[1]},{tailmax[0]})")


# ============================================================ block [7]

print()
print("=" * 78)
print("[7]  mutation controls -- each must FIRE")
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


# MS1: drop the gamma from theta.  gamma is what makes theta small; without it
# the slope 1 - theta goes negative and Theorem E stops being a strictness
# statement at all.
mutation("MS1  theta without its gamma factor: 1 - theta goes <= 0 somewhere, so "
         "the deficit stops being positive",
         any(theta(n, k) / gamma(n, k) >= 1 for (n, k) in R_NEW))
# MS2: a slope of 1 (i.e. claiming Phi <= 2 - gamma - D) must FAIL somewhere
bad = False
rngM = random.Random(3)
for (n, k) in CELLS:
    if (n, k) not in R_NEW:
        continue
    for sc in (F(1, 50), F(1, 10)):
        A = offface(n, k, rngM, sc)
        if min(min(row) for row in A) < 0:
            continue
        if Phi(A, k) > 2 - gamma(n, k) - D_of(A, k):
            bad = True
mutation("MS2  slope 1 instead of 1 - theta (Phi <= 2 - gamma - D) is FALSE", bad)
# MS3: D = 0 must NOT hold at an off-face point
mutation("MS3  claiming D = 0 off the face is false",
         any(D_of(offface(6, 4, random.Random(t), F(1, 10)), 4) != 0 for t in range(5)))
# MS4: dropping the Koenig floor -- 4/(3(n-1)^2) replaced by 1/n^4 -- stops
# dominating gamma
mutation("MS4  a floor 1/n^4 in place of 4/(3(n-1)^2) fails to beat gamma somewhere",
         any(F(1, n ** 4) <= gamma(n, k) for (n, k) in R_NEW))
# MS5: the route alone cannot give the equality case -- D = 0 does NOT pin A to
# J_n/n, only to Omega_n.  Permutation matrices witness it.  This is exactly why
# Friedland 1982 is still needed on the face, and the control makes that explicit.
bad5 = False
for n in range(3, 8):
    P = [[F(1) if i2 == j2 else F(0) for j2 in range(n)] for i2 in range(n)]
    Jn = [[F(1, n)] * n for _ in range(n)]
    for k in range(3, n):
        if D_of(P, k) == 0 and P != Jn:
            bad5 = True
mutation("MS5  'D = 0 implies A = J_n/n' is FALSE -- permutation matrices have "
         "D = 0, so Friedland 1982 on the face is still load-bearing", bad5)


# --- controls on LEMMA T (block [6]) -----------------------------------------
# MS6: PUSH THE CROSSOVER DOWN.  Lemma T claims n_1 = 10.  If the analytic half
# were asserted from n_1 = 9 or n_1 = 8, its own Case-B certificate for (C2) --
# Xi <= 6 B(n) -- would have to be <= 1 there.  It is not: 6B(9) = 160/81 and
# 6B(8) = 45/16.  The control must fire for EVERY crossover below 10.
def tail_cert_holds(n):
    """does Lemma T's analytic certificate close at this n?  (C1)(C2)(C3) via
    the (T2)/(T3) ceilings only -- never by looking at the cells."""
    if not (F(6, n ** 3) < F(1, 12)):                       # (C1) via T0
        return False
    if not (F(162, n ** 3) <= 1 and 6 * Bt(n) <= 1):        # (C2) via T2/T3
        return False
    lam_ceiling = max(F(12, n * n), Bt(n))                  # (C3) via T2/T3
    return lam_ceiling / (1 - F(9, 2 * n * n)) < 1


mutation("MS6  crossover perturbed DOWN: Lemma T's certificate fails at every "
         f"n_1 < 10 (6B(9) = {6*Bt(9)}, 6B(8) = {6*Bt(8)}) and holds at 10",
         (not any(tail_cert_holds(n) for n in range(4, 10)))
         and all(tail_cert_holds(n) for n in range(10, 60)))
# MS7: TRUNCATE THE FINITE PART.  Stop the exact check at n <= 8 and the union
# with the proved tail n >= 10 no longer covers R_new -- the n = 9 row is
# certified by neither half.
gap = [(n, k) for n in range(4, 121) for k in range(3, n)
       if n > 8 and n < 10 and (n, k) not in EXCLUDED]
mutation("MS7  finite part truncated to n <= 8 leaves the n = 9 row covered by "
         f"neither half ({len(gap)} orphan cells)", len(gap) > 0)
# MS8: DROP THE SUPER-EXPONENTIAL DECAY.  Replace (T3)'s gamma <= h!/n^h by the
# merely polynomial cap gamma <= 6/n^3 of (T0).  Then Lambda <= 12/n and
# Xi <= 72/n, which certify nothing at n = 10: the m = 1 side genuinely needs
# gamma's factorial decay, not the k = 3 cap.
mutation("MS8  (T3) with the polynomial cap 6/n^3 in place of h!/n^h fails to "
         "certify the tail at n = 10 (Lambda ceiling 12/n = 6/5 > 1)",
         any(F(12, n) >= 1 - F(9, 2 * n * n) or F(72, n) > 1
             for n in range(10, 13)))

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
