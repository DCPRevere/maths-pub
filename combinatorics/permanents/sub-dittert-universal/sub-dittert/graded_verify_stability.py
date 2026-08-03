"""
STANDALONE VERIFIER for the stability theorem (Theorem G of
results/paper_b.typ; first drafted as graded_stability_lemma.md and now
merged into the paper).

Self-contained on purpose: it imports nothing from the other files in this
directory, so it can be run against the write-up by someone who has only this
script.  Standard library only, Fraction throughout, no float in any decision.

WHAT IT VERIFIES, in the order the write-up needs it.

  V1  The layer identity on the centred slice:
          sigma_k(A)/C(n,k)^2 - k!/n^k  =  sum_{m=2}^{k} t_m sigma_m(B).
  V2  The core expansions of sigma_2..sigma_5 in the named invariants, against
      brute-force subpermanent sums.
  V3  The four a-priori facts F1-F4, including ||B||_op <= 1 tested directly.
  V4  Each per-invariant bound, in the one direction the proof uses, with its
      slack ratio, so tightness claims in the write-up are checkable.
  V5  The per-layer lower bounds  sigma_m|core >= -C_m(n) Q.
  V6  The budget, its closed forms, the thresholds and the exceptional sets.
  V7  The theorem end to end, on doubly stochastic matrices, at every covered
      (n,k).  For large n this uses sigma_m from the expansions verified in V2
      rather than a brute-force sigma_k, and the log says so.
  V8  The (3,3) COUNTEREXAMPLE, stored exactly: at n = k = 3 the inequality with
      constant t_2/4 is FALSE, so (3,3) is a genuine exception and not a gap.
  V12 The FORMALISATION SCOPE the paper states ("What is machine-checked, and
      what is not"), against the Lean sources at the commit the paper cites.
      This is the one check that reads outside this script: it needs the
      repository.  Where the sources are unavailable it FAILS rather than
      passing quietly; `--no-lean` records in the log that the scope claims
      went unchecked.

Usage:  GUARD_MEM=6G GUARD_CPUS=200% GUARD_THREADS=2 ../guard.sh \
            python3 graded_verify_stability.py
        add --no-lean to run without the repository (Section 10 unchecked)
"""

import random
import sys
from fractions import Fraction as Fr
from itertools import combinations, permutations
from math import comb, factorial

OUT = []
FAIL = 0

# Mutation-control state.  MUT holds the active injected fault; while a control
# is running, failures are counted separately and the normal output is muted, so
# that a control which correctly FIRES does not pollute the real verdict.
MUT = {}
MUT_ACTIVE = False
MUT_FAILS = 0
QUIET = False


def log(*a):
    if QUIET:
        return
    s = " ".join(str(x) for x in a)
    print(s)
    OUT.append(s)


def check(name, ok):
    global FAIL, MUT_FAILS
    if not ok:
        if MUT_ACTIVE:
            MUT_FAILS += 1
        else:
            FAIL += 1
            log(f"    *** FAIL: {name}")
    return ok


# ------------------------------------------------------------- primitives


def per(M):
    m = len(M)
    if m == 0:
        return Fr(1)
    tot = Fr(0)
    for p in permutations(range(m)):
        pr = Fr(1)
        for i in range(m):
            pr *= M[i][p[i]]
        tot += pr
    return tot


def sigma(M, d):
    n = len(M)
    if d == 0:
        return Fr(1)
    if d > n:
        return Fr(0)
    tot = Fr(0)
    for R in combinations(range(n), d):
        for C in combinations(range(n), d):
            tot += per([[M[i][j] for j in C] for i in R])
    return tot


def falling(x, d):
    out = Fr(1)
    for i in range(d):
        out *= (x - i)
    return out


def s_co(n, k, d):
    return falling(Fr(k), d) / falling(Fr(n), d)


def t_co(n, k, d):
    if d > k:
        return Fr(0)
    return s_co(n, k, d) ** 2 * Fr(factorial(k - d), n ** (k - d))


# ------------------------------------------------------- the invariants


def inv(b, n):
    """Every named invariant the proof uses, computed directly."""
    q = [sum(b[i][j] ** 2 for j in range(n)) for i in range(n)]
    qc = [sum(b[i][j] ** 2 for i in range(n)) for j in range(n)]
    Q = sum(q)
    G = [[sum(b[i][jj] * b[i][j2] for i in range(n)) for j2 in range(n)]
         for jj in range(n)]                                   # B^T B
    BG = [[sum(b[i][jj] * G[jj][j] for jj in range(n)) for j in range(n)]
          for i in range(n)]                                   # B (B^T B)
    f3 = [sum(b[i][j] ** 3 for j in range(n)) for i in range(n)]
    g3 = [sum(b[i][j] ** 3 for i in range(n)) for j in range(n)]
    return {
        "Q": Q,
        "q": q, "qc": qc,
        "p3": sum(b[i][j] ** 3 for i in range(n) for j in range(n)),
        "p4": sum(b[i][j] ** 4 for i in range(n) for j in range(n)),
        "p5": sum(b[i][j] ** 5 for i in range(n) for j in range(n)),
        "YR": sum(x * x for x in q),
        "YC": sum(x * x for x in qc),
        "Z": sum(G[a][c] ** 2 for a in range(n) for c in range(n)),
        "Ga": sum(q[i] * b[i][j] * qc[j]
                  for i in range(n) for j in range(n)),
        "Gb": sum(b[i][j] ** 2 * BG[i][j]
                  for i in range(n) for j in range(n)),
        "Gc": sum(q[i] * f3[i] for i in range(n)),
        "Gcp": sum(qc[j] * g3[j] for j in range(n)),
        "M": max(max(q), max(qc)),
        "beta": max(abs(b[i][j]) for i in range(n) for j in range(n)),
    }


def core(m, v):
    """sigma_m restricted to the centred slice, in named invariants."""
    if m == 2:
        return v["Q"] / 2
    if m == 3:
        return Fr(2, 3) * v["p3"]
    if m == 4:
        cYR = Fr(3, 4) if MUT.get("sign_flip") else Fr(-3, 4)   # FAULT M2
        return (Fr(3, 2) * v["p4"] + Fr(1, 8) * v["Q"] ** 2
                + Fr(1, 4) * v["Z"] + cYR * v["YR"]
                - Fr(3, 4) * v["YC"])
    if m == 5:
        return (Fr(24, 5) * v["p5"] + Fr(1, 3) * v["Q"] * v["p3"]
                + v["Ga"] + 2 * v["Gb"] - 4 * v["Gc"] - 4 * v["Gcp"])
    raise KeyError(m)


# -------------------------------------------------- the cost constants


def BETA(n):
    return Fr(n - 1, n)


def cost(m, n):
    """C_m(n) with  sigma_m|core >= -C_m(n) * Q  on the centred slice."""
    b = BETA(n)
    if m == 3:
        return Fr(2, 3) * Fr(1, n)
    if m == 4:
        return Fr(3, 2) * b
    if m == 5:
        return (Fr(24, 5) * Fr(1, n) ** 3 + Fr(1, 3) * b + b + 2 * b
                + 8 * b * b)
    raise KeyError(m)


def consumption(n, k):
    """Total cost as a fraction of the t_2/4 allowance."""
    tot = sum(t_co(n, k, m) * cost(m, n) for m in range(3, min(k, 5) + 1))
    return tot / (t_co(n, k, 2) / 4)


# ------------------------------------------------- doubly stochastic data


def pmat(n, p):
    return [[Fr(1) if p[i] == j else Fr(0) for j in range(n)]
            for i in range(n)]


def toB(A, n):
    return [[A[i][j] - Fr(1, n) for j in range(n)] for i in range(n)]


def ds_family(n, rng, extra=6):
    out = []
    idp = list(range(n))
    out.append(("perm vertex", pmat(n, idp)))
    p = list(range(n))
    rng.shuffle(p)
    out.append(("perm vertex rnd", pmat(n, p)))
    out.append(("antiperm (J-P)/(n-1)",
                [[(Fr(1) - pmat(n, idp)[i][j]) / Fr(n - 1)
                  for j in range(n)] for i in range(n)]))
    out.append(("J/n", [[Fr(1, n)] * n for _ in range(n)]))
    for t in range(extra):
        ws = [Fr(rng.randint(1, 9)) for _ in range(3 + t % 4)]
        tot = sum(ws)
        A = [[Fr(0)] * n for _ in range(n)]
        for w in ws:
            pp = list(range(n))
            rng.shuffle(pp)
            P = pmat(n, pp)
            for i in range(n):
                for j in range(n):
                    A[i][j] += w / tot * P[i][j]
        out.append(("convex combo", A))
    for lam in (Fr(9, 10), Fr(99, 100)):
        p2 = list(range(n))
        rng.shuffle(p2)
        P1, P2 = pmat(n, p2), pmat(n, idp)
        out.append((f"near vertex lam={lam}",
                    [[lam * P1[i][j] + (1 - lam) * P2[i][j]
                      for j in range(n)] for i in range(n)]))
    return out


# ============================================================ V1 .. V8


def V1(rng):
    log("V1.  THE LAYER IDENTITY ON THE CENTRED SLICE.")
    log("     sigma_k(A)/C(n,k)^2 - k!/n^k  ==  sum_{m=2}^k t_m sigma_m(B).")
    for (n, k) in ((4, 3), (5, 3), (5, 4), (6, 4), (6, 5), (7, 5)):
        okall = True
        for label, A in ds_family(n, rng, extra=2):
            b = toB(A, n)
            lhs = (sigma(A, k) / Fr(comb(n, k)) ** 2
                   - Fr(factorial(k), n ** k))
            rhs = sum(t_co(n, k, m) * sigma(b, m) for m in range(2, k + 1))
            if lhs != rhs:
                okall = False
        check(f"V1 n={n} k={k}", okall)
        log(f"     n={n} k={k}: {okall}")
    log("")


def V2(rng):
    log("V2.  THE CORE EXPANSIONS, against brute-force subpermanent sums.")
    log("     m <= 4 is McCullagh (2012); m = 5 specialises his general form.")
    for n in (4, 5, 6):
        for m in (2, 3, 4, 5):
            if m > n:
                continue
            okall = True
            for label, A in ds_family(n, rng, extra=3):
                b = toB(A, n)
                if sigma(b, m) != core(m, inv(b, n)):
                    okall = False
                    log(f"     n={n} m={m} {label}: MISMATCH")
            check(f"V2 n={n} m={m}", okall)
        log(f"     n={n}: sigma_2..sigma_{min(5, n)} core forms verified")
    log("")


def V3(rng):
    log("V3.  THE FOUR A-PRIORI FACTS.")
    log("     F1 |b_ij| <= 1-1/n and b_ij >= -1/n   F2 M <= 1-1/n")
    log("     F3 Q <= n-1                           F4 ||B||_op <= 1")
    for n in (4, 5, 6, 7):
        ok1 = ok2 = ok3 = ok4 = True
        tightQ = False
        for label, A in ds_family(n, rng, extra=3):
            b = toB(A, n)
            v = inv(b, n)
            lim = BETA(n)
            for i in range(n):
                for j in range(n):
                    if not (-Fr(1, n) <= b[i][j] <= lim):
                        ok1 = False
            if v["M"] > lim:
                ok2 = False
            if v["Q"] > Fr(n - 1):
                ok3 = False
            if v["Q"] == Fr(n - 1):
                tightQ = True
            # F4 directly: ||Bx|| <= ||x|| on random rational x
            for _ in range(8):
                x = [Fr(rng.randint(-9, 9), rng.randint(1, 4))
                     for _ in range(n)]
                Bx = [sum(b[i][j] * x[j] for j in range(n)) for i in range(n)]
                if sum(y * y for y in Bx) > sum(y * y for y in x):
                    ok4 = False
            # F4's consequence
            if v["Z"] > v["Q"]:
                ok4 = False
        check(f"V3 F1 n={n}", ok1)
        check(f"V3 F2 n={n}", ok2)
        check(f"V3 F3 n={n}", ok3)
        check(f"V3 F4 n={n}", ok4)
        log(f"     n={n}: F1 {ok1}  F2 {ok2}  F3 {ok3}  F4 {ok4}"
            f"   Q=n-1 attained: {tightQ}")
    log("")


BOUNDS = [
    ("p3  >= -(1/n) Q", "lower", lambda v, n: v["p3"],
     lambda n: Fr(1, n * n) if MUT.get("tight_p3") else Fr(1, n)),   # FAULT M4
    ("p5  >= -(1/n)^3 Q", "lower", lambda v, n: v["p5"],
     lambda n: Fr(1, n) ** 3),
    ("p4  <= (1-1/n)^2 Q", "upper", lambda v, n: v["p4"],
     lambda n: BETA(n) ** 2),
    ("YR  <= M Q", "upper", lambda v, n: v["YR"], None),
    ("YC  <= M Q", "upper", lambda v, n: v["YC"], None),
    ("Gc  <= (1-1/n) M Q", "upper", lambda v, n: v["Gc"], None),
    ("Gc' <= (1-1/n) M Q", "upper", lambda v, n: v["Gcp"], None),
    ("|Ga| <= M Q", "abs", lambda v, n: v["Ga"], None),
    ("|Gb| <= (1-1/n) Q", "abs", lambda v, n: v["Gb"],
     lambda n: BETA(n)),
    ("Q p3 >= -((n-1)/n) Q", "lower", lambda v, n: v["Q"] * v["p3"],
     lambda n: BETA(n)),
    ("Z  <= Q", "upper", lambda v, n: v["Z"], lambda n: Fr(1)),
]


def const_for(name, v, n):
    if name.startswith("YR") or name.startswith("YC") or name.startswith("|Ga|"):
        return v["M"]
    if name.startswith("Gc"):
        return BETA(n) * v["M"]
    return None


def V4(rng):
    log("V4.  EACH PER-INVARIANT BOUND, in the direction the proof uses.")
    log("     slack = (used side)/(bound); must be <= 1.  slack = 1 means the")
    log("     bound is ATTAINED, so the write-up may call it tight.")
    worst = {}
    for n in (4, 5, 6, 7):
        for label, A in ds_family(n, rng, extra=4):
            b = toB(A, n)
            v = inv(b, n)
            Q = v["Q"]
            if Q == 0:
                continue
            for name, kind, getter, cfn in BOUNDS:
                c = cfn(n) if cfn is not None else const_for(name, v, n)
                lim = c * Q
                val = getter(v, n)
                if lim == 0:
                    continue
                if kind == "lower":
                    r = (-val) / lim
                elif kind == "upper":
                    r = val / lim
                else:
                    r = abs(val) / lim
                if name not in worst or r > worst[name][0]:
                    worst[name] = (r, n, label)
                check(f"V4 {name} n={n} {label}", r <= 1)
    log("     bound                     | worst slack | attained at")
    for name, _k, _g, _c in BOUNDS:
        if name in worst:
            r, n, label = worst[name]
            tag = "  TIGHT" if r == 1 else ""
            log(f"     {name:25s} | {float(r):11.6f} | n={n} {label}{tag}")
    log("")


def V5(rng):
    log("V5.  THE PER-LAYER LOWER BOUNDS  sigma_m|core >= -C_m(n) Q.")
    for n in (4, 5, 6, 7):
        row = f"     n={n}: "
        for m in (3, 4, 5):
            okall = True
            wr = Fr(0)
            for label, A in ds_family(n, rng, extra=4):
                b = toB(A, n)
                v = inv(b, n)
                if v["Q"] == 0:
                    continue
                lo = -cost(m, n) * v["Q"]
                val = core(m, v)
                if val < lo:
                    okall = False
                r = (-val) / (cost(m, n) * v["Q"])
                wr = max(wr, r)
            check(f"V5 m={m} n={n}", okall)
            row += f"m={m} ok={okall} slack={float(wr):.4f}   "
        log(row)
    log("")


def V6():
    log("V6.  THE BUDGET, ITS CLOSED FORMS, THRESHOLDS, EXCEPTIONAL SETS.")
    log("     Closed form at k = 3:  consumption = (8/3)/(n-2)^2 .")
    ok = all(consumption(n, 3) == Fr(8, 3) / Fr(n - 2) ** 2
             for n in range(3, 40))
    check("V6 k=3 closed form", ok)
    log(f"       matches for 3 <= n < 40: {ok}")
    log("     Closed form at k = 4:")
    log("       consumption = 16/(3(n-2)^2) + 12 n (n-1)/((n-2)^2 (n-3)^2) .")
    ok4 = all(consumption(n, 4) == (Fr(16, 3) / Fr(n - 2) ** 2
                                    + Fr(12 * n * (n - 1),
                                         (n - 2) ** 2 * (n - 3) ** 2))
              for n in range(4, 40))
    check("V6 k=4 closed form", ok4)
    log(f"       matches for 4 <= n < 40: {ok4}")
    log("     Closed form at k = 5:")
    log("       consumption = 8/(n-2)^2 + 36 n(n-1)/((n-2)^2 (n-3)^2)")
    log("                     + 24 n^3 C_5(n)/((n-2)^2 (n-3)^2 (n-4)^2) .")
    ok5 = all(consumption(n, 5) == (Fr(8, (n - 2) ** 2)
                                    + Fr(36 * n * (n - 1),
                                         (n - 2) ** 2 * (n - 3) ** 2)
                                    + Fr(24 * n ** 3, (n - 2) ** 2
                                         * (n - 3) ** 2 * (n - 4) ** 2)
                                    * cost(5, n))
              for n in range(5, 40))
    check("V6 k=5 closed form", ok5)
    log(f"       matches for 5 <= n < 40: {ok5}")
    log("     and C_5(n) = (24/5)/n^3 + (10/3)(1-1/n) + 8(1-1/n)^2 :")
    okc5 = all(cost(5, n) == Fr(24, 5) / Fr(n) ** 3
               + Fr(10, 3) * BETA(n) + 8 * BETA(n) ** 2
               for n in range(2, 40))
    check("V6 C_5 closed form", okc5)
    log(f"       matches for 2 <= n < 40: {okc5}")
    log("")
    log("     thresholds and exceptional sets (consumption < 1):")
    THRESH = {2: 2, 3: 4, 4: 8, 5: 14}
    for k in (2, 3, 4, 5):
        if k == 2:
            log("       k = 2: no layers above 2, so the bound is vacuous and")
            log("              the lemma holds for every n >= 2 with t_2/2.")
            continue
        ex = [n for n in range(k, 400) if consumption(n, k) >= 1]
        thr = min(n for n in range(k, 400) if consumption(n, k) < 1)
        check(f"V6 threshold k={k}", thr == THRESH[k])
        log(f"       k = {k}: closes for n >= {thr}"
            f"  (expected {THRESH[k]});  exceptional n = {ex}")
        allabove = all(consumption(n, k) < 1 for n in range(thr, 400))
        check(f"V6 monotone-above k={k}", allabove)
        log(f"              closes at every n from {thr} to 399: {allabove}")
    log("")


def V7(rng):
    log("V7.  THE THEOREM END TO END:  F(B) >= (t_2/4) Q  on Omega_n.")
    log("     F is assembled from the core expansions verified in V2, so no")
    log("     brute-force sigma_k is needed at large n.  The covered cells are")
    log("     re-checked against brute force where that is feasible.")
    covered = [(4, 3), (5, 3), (6, 3), (8, 4), (9, 4), (10, 4), (12, 4),
               (14, 5), (15, 5), (16, 5), (20, 5)]
    for (n, k) in covered:
        okall = True
        wmin = None
        for label, A in ds_family(n, rng, extra=6):
            b = toB(A, n)
            v = inv(b, n)
            Q = v["Q"]
            if Q == 0:
                continue
            F = sum(t_co(n, k, m) * core(m, v) for m in range(2, k + 1))
            dd = 2 if MUT.get("const_doubled") else 4              # FAULT M1
            need = t_co(n, k, 2) / dd * Q
            if F < need:
                okall = False
                log(f"     n={n} k={k} {label}: F={F} < {need}")
            r = F / (t_co(n, k, 2) * Q)
            if wmin is None or r < wmin:
                wmin = r
        check(f"V7 n={n} k={k}", okall)
        log(f"     n={n} k={k}: holds {okall}"
            f"   min F/(t_2 Q) = {float(wmin):.4f}  (needs >= 0.25)")
    log("")
    log("     brute-force cross-check of F at the small covered cells:")
    for (n, k) in ((4, 3), (5, 3), (6, 3)):
        okall = True
        for label, A in ds_family(n, rng, extra=2):
            b = toB(A, n)
            v = inv(b, n)
            direct = (sigma(A, k) / Fr(comb(n, k)) ** 2
                      - Fr(factorial(k), n ** k))
            built = sum(t_co(n, k, m) * core(m, v) for m in range(2, k + 1))
            if direct != built:
                okall = False
        check(f"V7 brute n={n} k={k}", okall)
        log(f"       n={n} k={k}: assembled F equals brute-force F: {okall}")
    log("")


def V8():
    log("V8.  THE (3,3) COUNTEREXAMPLE.  At n = k = 3 the inequality with")
    log("     constant t_2/4 is FALSE, so (3,3) is a genuine exception.")
    n = k = 3
    P = pmat(n, [0, 1, 2])
    A = [[(Fr(1) - P[i][j]) / Fr(2) for j in range(n)] for i in range(n)]
    b = toB(A, n)
    v = inv(b, n)
    Q = v["Q"]
    F = sigma(A, k) / Fr(comb(n, k)) ** 2 - Fr(factorial(k), n ** k)
    t2 = t_co(n, k, 2)
    log("     WITNESS  A = (J_3 - P)/2, i.e. uniform off a permutation:")
    for row in A:
        log("       [" + ", ".join(str(x) for x in row) + "]")
    log(f"     Q = {Q}   F = {F}   t_2 = {t2}")
    log(f"     F/Q          = {F / Q}  = {float(F / Q):.6f}")
    log(f"     t_2/4        = {t2 / 4}  = {float(t2 / 4):.6f}")
    check("V8 counterexample is real", F / Q < t2 / 4)
    log(f"     F/Q < t_2/4  : {F / Q < t2 / 4}   <- the inequality FAILS here")
    log(f"     F/Q as a multiple of t_2: {F / (t2 * Q)}"
        f" = {float(F / (t2 * Q)):.6f}")
    log("     Also confirming per(A) is what it should be, per(J_3-P) = 2:")
    JmP = [[Fr(1) - P[i][j] for j in range(n)] for i in range(n)]
    check("V8 per(J-P)=2", per(JmP) == 2)
    log(f"       per(J_3 - P) = {per(JmP)}")
    log("")


def V6b():
    log("V6b. THE PAPER'S QUOTED VALUES OF Phi, AND MONOTONICITY.")
    quoted = {(8, 4): "0.8948", (14, 5): "0.8094", (15, 4): "0.1351",
              (20, 5): "0.2540"}
    for (n, k), q in sorted(quoted.items()):
        got = f"{float(consumption(n, k)):.4f}"
        check(f"V6b Phi({n},{k}) quoted", got == q)
        log(f"       Phi({n},{k}) = {got}   paper says {q}"
            f"   match {got == q}")
    log("     Monotone decreasing in n above the threshold:")
    for k, thr in ((3, 4), (4, 8), (5, 14)):
        mono = all(consumption(n + 1, k) < consumption(n, k)
                   for n in range(thr, 600))
        check(f"V6b monotone k={k}", mono)
        log(f"       k={k}: Phi(n+1,k) < Phi(n,k) for {thr} <= n < 600:"
            f" {mono}")
        log(f"              Phi(600,{k}) = {float(consumption(600, k)):.3e}"
            f"  (tends to 0)")
    log("")


# ------------------------------------- exact polynomial machinery for V6c


def padd(a, b):
    out = [Fr(0)] * max(len(a), len(b))
    for i, x in enumerate(a):
        out[i] += x
    for i, x in enumerate(b):
        out[i] += x
    while len(out) > 1 and out[-1] == 0:
        out.pop()
    return out


def pmul(a, b):
    out = [Fr(0)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x == 0:
            continue
        for j, y in enumerate(b):
            out[i + j] += x * y
    while len(out) > 1 and out[-1] == 0:
        out.pop()
    return out


def pev(a, v):
    tot = Fr(0)
    for c in reversed(a):
        tot = tot * v + c
    return tot


def pshift(a, t):
    """substitute n = m + t."""
    out = [Fr(0)]
    powr = [Fr(1)]
    for c in a:
        out = padd(out, [c * x for x in powr])
        powr = pmul(powr, [Fr(t), Fr(1)])
    return out


def rf_add(f, g):
    return (padd(pmul(f[0], g[1]), pmul(g[0], f[1])), pmul(f[1], g[1]))


def rf_mul(f, g):
    return (pmul(f[0], g[0]), pmul(f[1], g[1]))


def phi_rf(k):
    """Phi(n,k) as (numerator, denominator) polynomials in n."""
    N = [Fr(0), Fr(1)]                      # n
    one = [Fr(1)]
    # t_m/t_2 = prod_{j=2}^{m-1} n(k-j)/(n-j)^2
    ratio = {2: (one, one)}
    cur = (one, one)
    for m in range(3, k + 1):
        j = m - 1
        fac = (pmul([Fr(k - j)], N), pmul([Fr(-j), Fr(1)], [Fr(-j), Fr(1)]))
        cur = rf_mul(cur, fac)
        ratio[m] = cur
    # C_m(n)
    beta = ([Fr(-1), Fr(1)], N)             # (n-1)/n
    Cm = {}
    Cm[3] = ([Fr(2, 3)], N)
    Cm[4] = rf_mul(([Fr(3, 2)], one), beta)
    n3 = pmul(N, pmul(N, N))
    Cm[5] = rf_add(rf_add(([Fr(24, 5)], n3),
                          rf_mul(([Fr(10, 3)], one), beta)),
                   rf_mul(([Fr(8)], one), rf_mul(beta, beta)))
    tot = ([Fr(0)], one)
    for m in range(3, min(k, 5) + 1):
        tot = rf_add(tot, rf_mul(ratio[m], Cm[m]))
    return rf_mul(([Fr(4)], one), tot)


def pdivmod(a, b):
    """Polynomial division over Q: a = q*b + r."""
    a = list(a)
    q = [Fr(0)] * max(1, len(a) - len(b) + 1)
    while len(a) >= len(b) and any(x != 0 for x in a):
        if a[-1] == 0:
            a.pop()
            continue
        d = len(a) - len(b)
        c = a[-1] / b[-1]
        q[d] = c
        for i, y in enumerate(b):
            a[d + i] -= c * y
        while len(a) > 1 and a[-1] == 0:
            a.pop()
        if len(a) == 1 and a[0] == 0:
            break
    while len(q) > 1 and q[-1] == 0:
        q.pop()
    while len(a) > 1 and a[-1] == 0:
        a.pop()
    return q, a


def pgcd(a, b):
    a, b = list(a), list(b)
    while any(x != 0 for x in b):
        _, r = pdivmod(a, b)
        a, b = b, r
    return a


def primitive(a):
    """Scale a rational polynomial to primitive integer form, positive lead."""
    from math import gcd as igcd
    den = 1
    for c in a:
        den = den * c.denominator // igcd(den, c.denominator)
    ints = [int(c * den) for c in a]
    g = 0
    for c in ints:
        g = igcd(g, abs(c))
    if g:
        ints = [c // g for c in ints]
    if ints and ints[-1] < 0:
        ints = [-c for c in ints]
    return [Fr(c) for c in ints]


def phi_reduced(k):
    """Phi(n,k) as (num, den) in LOWEST TERMS, both primitive integer
    polynomials with positive leading coefficient on the denominator.  This is
    the object the write-up's recipe describes -- 'clearing its denominator' --
    and it is NOT the same as the unreduced construction, whose den - num is a
    higher-degree multiple with different coefficients."""
    num, den = phi_rf(k)
    g = pgcd(den, num)
    if len(g) > 1 or g[0] != 0:
        num, _ = pdivmod(num, g)
        den, _ = pdivmod(den, g)
    # Scale the PAIR to integer polynomials of content 1.  Normalising the
    # denominator alone would leave fractions in the numerator and so change
    # P_k = den - num by a scalar; the canonical object is the integer pair.
    from math import gcd as igcd
    L = 1
    for c in num + den:
        L = L * c.denominator // igcd(L, c.denominator)
    num = [c * L for c in num]
    den = [c * L for c in den]
    g = 0
    for c in num + den:
        g = igcd(g, abs(int(c)))
    if g:
        num = [c / g for c in num]
        den = [c / g for c in den]
    if den[-1] < 0:
        num = [-c for c in num]
        den = [-c for c in den]
    return num, den


def V6c():
    log("V6c. Phi(n,k) < 1 FOR ALL n ABOVE THE THRESHOLD, not just to 600.")
    log("     Phi is a rational function of n; clearing its (positive)")
    log("     denominator turns Phi < 1 into a polynomial inequality P_k(n) > 0.")
    log("     Substituting n = m + threshold, ALL coefficients come out")
    log("     nonnegative with the constant term positive, which settles every")
    log("     n >= threshold at once.")
    for k, thr in ((3, 4), (4, 8), (5, 14)):
        if MUT.get("bad_threshold"):
            thr -= 1                                              # FAULT M3
        num, den = phi_reduced(k)
        # cross-check the rational function against the arithmetic version
        okv = all(pev(num, Fr(n)) / pev(den, Fr(n)) == consumption(n, k)
                  for n in range(thr, thr + 25))
        check(f"V6c rf matches k={k}", okv)
        P = padd(den, [-x for x in num])          # den - num > 0  <=>  Phi < 1
        Ps = pshift(P, thr)
        Ds = pshift(den, thr)
        signs_ok = all(c >= 0 for c in Ps) and Ps[0] > 0
        den_ok = all(c >= 0 for c in Ds) and Ds[0] > 0
        check(f"V6c P_k shifted nonneg k={k}", signs_ok)
        check(f"V6c den positive k={k}", den_ok)
        log(f"       k={k}: rational form matches arithmetic: {okv}")
        log(f"              denominator > 0 for n >= {thr}: {den_ok}")
        log(f"              P_k(m+{thr}) coefficients all >= 0, constant > 0:"
            f" {signs_ok}")
        log(f"              P_k(m+{thr}) = {[str(c) for c in Ps]}")
        log(f"              and P_k({thr - 1}) = {pev(P, Fr(thr - 1))}"
            f"  (must be <= 0, the threshold is sharp)")
        check(f"V6c threshold sharp k={k}", pev(P, Fr(thr - 1)) <= 0)
        if not MUT.get("bad_threshold"):
            # The write-up quotes these objects explicitly.  Check them, so a
            # transcription error in the paper cannot survive a verifier run.
            DEN = {3: [3, -12, 12],
                   4: [3, -30, 111, -180, 108],
                   5: [5, -90, 665, -2580, 5540, -6240, 2880]}
            PK = {3: [3, -12, 4],
                  4: [3, -30, 59, -48, -36],
                  5: [5, -90, 445, -1760, 620, 2400, -3456]}
            SH = {3: [3, 12, 4],
                  4: [3, 66, 491, 1280, 284],
                  5: [5, 330, 8845, 121160, 861620, 2716720, 1660864]}
            SHARP = {3: -5, 4: -568, 5: -306876}
            check(f"V6c paper den k={k}",
                  [int(c) for c in reversed(den)] == DEN[k])
            check(f"V6c paper P_k k={k}",
                  [int(c) for c in reversed(P)] == PK[k])
            check(f"V6c paper shifted k={k}",
                  [int(c) for c in reversed(Ps)] == SH[k])
            check(f"V6c paper sharp value k={k}",
                  pev(P, Fr(thr - 1)) == SHARP[k])
            log(f"              write-up's quoted den, P_k, P_k(m+{thr}) and"
                f" P_k({thr - 1}): all match")
    log("")


def V9():
    log("V9.  SHARPNESS SANDWICH.  t_2/4 <= c_opt(n,k) < t_2/2 for k >= 3.")
    log("     Upper: along B = J/n - P one has p_3(B) < 0, so")
    log("       F(sB)/||sB||^2 = t_2/2 + s t_3 (2/3) p_3(B)/Q_B + O(s^2)")
    log("     dips below t_2/2 immediately.  p_3(J/n - P) in closed form is")
    log("       ((n-1)/n^2) (1 - (n-1)^2),  negative for every n >= 3.")
    for n in range(3, 12):
        P = pmat(n, list(range(n)))
        B = [[Fr(1, n) - P[i][j] for j in range(n)] for i in range(n)]
        v = inv(B, n)
        closed = Fr(n - 1, n ** 2) * (1 - Fr((n - 1) ** 2))
        check(f"V9 p3 closed form n={n}", v["p3"] == closed)
        check(f"V9 p3 negative n={n}", v["p3"] < 0)
        log(f"       n={n}: p_3 = {v['p3']} = {float(v['p3']):.6f}"
            f"   closed form matches: {v['p3'] == closed}")
    log("     Lower: the theorem itself, at every covered (n,k).")
    log("     So the optimal constant is pinned to within a factor 2.")
    log("")


# =============================================== V10: MUTATION CONTROLS


def run_control(label, fault, target, runner, expect_check):
    """Inject one fault, run the check that is supposed to catch it, and report
    whether it FIRED.  A control that does not fire means the verifier is not
    testing what it claims to test."""
    global MUT_ACTIVE, MUT_FAILS, QUIET
    MUT.clear()
    MUT[fault] = True
    MUT_ACTIVE, MUT_FAILS, QUIET = True, 0, True
    try:
        runner()
    finally:
        fired = MUT_FAILS
        MUT_ACTIVE, QUIET = False, False
        MUT.clear()
    ok = fired > 0
    log(f"     {label}")
    log(f"       fault injected at : {fault}")
    log(f"       must be caught by : {target}")
    log(f"       rejections raised : {fired}"
        f"   -> {'FIRES' if ok else 'DID NOT FIRE'}")
    check(f"V10 control {fault} fires", ok)
    return ok


def V10():
    log("V10. MUTATION CONTROLS.  A verifier that never rejects proves nothing.")
    log("     Each control injects one deliberate fault and confirms that the")
    log("     check which is supposed to catch it does reject.  Failures raised")
    log("     inside a control are counted separately and do NOT affect the")
    log("     verdict above; only a control that fails to FIRE is a real")
    log("     failure.")
    log("")
    run_control("M1  the constant doubled: require F >= (t_2/2) Q, which"
                " Proposition 6 says is impossible",
                "const_doubled", "V7 (theorem end to end)",
                lambda: V7(random.Random(11)), "V7")
    log("")
    run_control("M2  sign flip on Y_R in the sigma_4 core expansion (4.3),"
                " -3/4 becomes +3/4",
                "sign_flip", "V2 (core expansions vs brute force)",
                lambda: V2(random.Random(22)), "V2")
    log("")
    run_control("M3  each threshold lowered by one, so an excluded cell is"
                " claimed as covered",
                "bad_threshold", "V6c (the all-n polynomial argument)",
                V6c, "V6c")
    log("")
    run_control("M4  the p_3 estimate over-tightened to p_3 >= -(1/n^2) Q",
                "tight_p3", "V4 (per-invariant estimates)",
                lambda: V4(random.Random(44)), "V4")
    log("")
    log("     The next five faults are scope faults: each is a way for Section")
    log("     10 to claim more, or less, formalisation than the Lean sources")
    log("     carry.  The separating witness is named on each line, because a")
    log("     control whose witness cannot tell the two apart proves nothing.")
    log("")
    run_control("M5  the formalised cell at k = 3 claimed as n >= 3, one below"
                " what Lean proves"
                "   [separating witness: 3 != 4, and the Lean hypothesis is"
                " 4 <= n]",
                "lean_cell", "V12 (formalised cells vs the Lean hypotheses)",
                V12, "V12")
    log("")
    run_control("M6  the paper's constant doubled, so cVal would no longer be"
                " c(n,k)"
                "   [separating witness: c(n,k) > 0 on the tested grid, which"
                " V12 asserts, so a factor two is visible]",
                "lean_const", "V12 (cVal compared as a rational function)",
                V12, "V12")
    log("")
    run_control("M7  Lean's phiPoly_k truncated after its leading term"
                "   [separating witness: P_k is non-constant, which V12"
                " asserts, so truncation changes its values]",
                "lean_polys", "V12 (Lean's P_k vs this verifier's own)",
                V12, "V12")
    log("")
    run_control("M8  a cell the paper calls unformalised (k = 5) replaced by one"
                " that IS formalised (k = 2)"
                "   [separating witness: stabilityAt_two is present, so the"
                " absence test must reject it]",
                "lean_phantom", "V12 (the absence test, with its non-vacuity"
                " check)",
                V12, "V12")
    log("")
    run_control("M9  one name dropped from the parsed audit block, as an"
                " unaudited declaration would appear"
                "   [separating witness: the declaration set is non-empty,"
                " which V12 asserts]",
                "lean_orphan", "V12 (the orphan diff, all four files)",
                V12, "V12")
    log("")
    run_control("M10 Lemma 2's formalisation claimed to need double"
                " stochasticity, which would make it no stronger than the"
                " paper's own hypothesis"
                "   [separating witness: `doublyStochastic` is findable --"
                " it occurs in StabilityK3 -- so its absence from"
                " layer_identity is measured]",
                "lean_weak", "V12 (the hypotheses of layer_identity)",
                V12, "V12")
    log("")
    log("     Control on the controls: with no fault injected, these same"
        " routines")
    log("     (V2, V4, V6c, V7, V12) raise nothing -- that is the clean run")
    log("     reported above.  So each rejection above is caused by its fault")
    log("     and not by the routine being flaky.")
    log("")


def Dfun(x):
    return sum(t ** 4 for t in x) - Fr(1, 2) * sum(t ** 2 for t in x) ** 2


def V11():
    log("V11. SECTION 11 (the v2 addendum).  Every displayed number carries a")
    log("     hard-coded expectation, per the standing rule.")
    n = 4
    A = [[Fr(1, 2), Fr(1, 2), Fr(0), Fr(0)],
         [Fr(1, 2), Fr(0), Fr(0), Fr(1, 2)],
         [Fr(0), Fr(0), Fr(1, 2), Fr(1, 2)],
         [Fr(0), Fr(1, 2), Fr(1, 2), Fr(0)]]
    for i in range(n):
        check(f"V11 witness row sum {i}", sum(A[i]) == 1)
        check(f"V11 witness col sum {i}",
              sum(A[r][i] for r in range(n)) == 1)
    b = toB(A, n)
    M = [[4 * b[i][j] for j in range(n)] for i in range(n)]
    check("V11 B = M/4 with M entries +-1",
          all(abs(M[i][j]) == 1 for i in range(n) for j in range(n)))
    check("V11 per(M) = -8", per(M) == -8)
    check("V11 sigma_4(B) = -1/32", sigma(b, 4) == Fr(-1, 32))
    check("V11 Q = 1", inv(b, n)["Q"] == 1)
    check("V11 M rank two: rows 3,4 negate rows 1,2",
          all(M[2][j] == -M[0][j] and M[3][j] == -M[1][j]
              for j in range(n)))
    log(f"     witness: per(M) = {per(M)}, sigma_4 = {sigma(b, 4)},"
        f" Q = {inv(b, n)['Q']}, rank two confirmed")
    log("     Proposition 8, sigma_4(c u v^T) = (3/2) c^4 D(u) D(v):")
    cases = [([1, -1, 0, 0], [1, -1, 0, 0]), ([3, -1, -1, -1], [1, 1, -1, -1]),
             ([2, -1, -1, 0], [1, 0, -1, 0])]
    for uu, vv in cases:
        u = [Fr(t) for t in uu]
        v = [Fr(t) for t in vv]
        c = Fr(1, 5)
        B = [[c * u[i] * v[j] for j in range(4)] for i in range(4)]
        check(f"V11 prop 8 {uu}x{vv}",
              sigma(B, 4) == Fr(3, 2) * c ** 4 * Dfun(u) * Dfun(v))
    DEXP = {(1, -1, 0, 0): 0, (2, -1, -1, 0): 0, (1, 1, -1, -1): -4,
            (3, -1, -1, -1): 12}
    for xx, want in DEXP.items():
        got = Dfun([Fr(t) for t in xx])
        check(f"V11 D{xx} = {want}", got == want)
        log(f"       D{list(xx)} = {got}   paper says {want}")
    u = [Fr(3), Fr(-1), Fr(-1), Fr(-1)]
    v = [Fr(1), Fr(1), Fr(-1), Fr(-1)]
    c = Fr(1, 12)
    B = [[c * u[i] * v[j] for j in range(4)] for i in range(4)]
    A0 = [[Fr(1, 4) + B[i][j] for j in range(4)] for i in range(4)]
    check("V11 rank-one example stays in Omega_4",
          min(A0[i][j] for i in range(4) for j in range(4)) >= 0)
    check("V11 rank-one sigma_4/Q = -1/96",
          sigma(B, 4) / inv(B, 4)["Q"] == Fr(-1, 96))
    log(f"       rank-one example: sigma_4/Q = "
        f"{sigma(B, 4) / inv(B, 4)['Q']}   paper says -1/96")
    log("     the eps thresholds quoted as (4, 5, 12), same for eps <= 1/16:")

    def eps_thr(k, eps):
        for nn in range(max(k, 3), 200):
            tot = sum(t_co(nn, k, m) * (eps if m == 4 else cost(m, nn))
                      for m in range(3, min(k, 5) + 1))
            if tot / (t_co(nn, k, 2) / 4) < 1:
                return nn
        return None
    for eps in (Fr(0), Fr(1, 32), Fr(1, 16)):
        got = tuple(eps_thr(k, eps) for k in (3, 4, 5))
        check(f"V11 eps={eps} thresholds are (4,5,12)", got == (4, 5, 12))
        log(f"       eps = {eps}: {got}   paper says (4, 5, 12)")
    log("     and the elementary-bound floor quoted as about 9/8:")
    worst = max(Fr(5, 4) * min(Fr(1), Fr(num, 20)) - Fr(1, 8) * Fr(num, 20)
                for num in range(1, 81))
    check("V11 elementary floor is 9/8", worst == Fr(9, 8))
    log(f"       floor = {worst}   paper says 9/8")
    log("")


# ============================== V12: THE FORMALISATION SCOPE, CHECKED
#
# Section 10 states which cells of Theorem 1 are kernel-checked and which are
# not.  That is a claim about files outside this script, so it is the one check
# here that reads the repository.  It reads the Lean sources AT THE COMMIT THE
# PAPER CITES (`git show <commit>:<path>`), not the working tree, so the paper's
# "as of commit X" is verified at X and cannot drift.  If the sources are
# unavailable the check FAILS rather than passing quietly: a scope claim that
# nothing can check is worse than no claim.  `--no-lean` states in the log that
# the formalisation claims went unchecked in that run.

LEAN_DIR = "problems/permanents/leanproj"
# Each file is read at the commit the paper cites FOR THAT FILE.  Four
# claims, four commits: the k = 2, 3 cells at 1507013, the layer identity at
# 27bda3f, the k = 4 cell at 944b517, the sigma_4 core expansion at 365e44e.
LEAN_COMMIT = {"TverbergStability.lean": "1507013",
               "StabilityK3.lean": "1507013",
               "LayerIdentity.lean": "27bda3f",
               "StabilityK4.lean": "944b517",
               "SigmaFour.lean": "365e44e",
               "StabilityK5Sieve.lean": "45d20c2",
               "StabilityK5.lean": "45d20c2",
               "UniformStability.lean": "45d20c2"}
# The paper's own numbers, hard-coded here so a transcription error in either
# the paper or the Lean file cannot survive: the formalised cells.
PAPER_LEAN_CELLS = {2: 2, 3: 4, 4: 8, 5: 14}  # k -> threshold n, kernel-checked
PAPER_LEAN_UNFORMALISED = (6,)           # k values with NO stabilityAt theorem
PAPER_THRESHOLDS = {3: 4, 4: 8, 5: 14}   # thresholds of the Phi layer


def lean_source(path):
    """The text of one Lean file at the commit the paper cites for it."""
    import subprocess
    try:
        root = subprocess.run(["git", "rev-parse", "--show-toplevel"],
                              capture_output=True, text=True, timeout=30)
        if root.returncode != 0:
            return None
        top = root.stdout.strip()
        out = subprocess.run(
            ["git", "-C", top, "show",
             f"{LEAN_COMMIT[path]}:{LEAN_DIR}/{path}"],
            capture_output=True, text=True, timeout=60)
        return out.stdout if out.returncode == 0 else None
    except (OSError, subprocess.SubprocessError, KeyError):
        return None


def lean_strip_comments(src):
    """Remove -- line comments and /- ... -/ blocks (nesting respected), so that
    a `sorry` inside prose is not mistaken for a `sorry` in a proof."""
    out, i, depth, n = [], 0, 0, len(src)
    while i < n:
        if src.startswith("/-", i):
            depth += 1
            i += 2
        elif src.startswith("-/", i) and depth:
            depth -= 1
            i += 2
        elif depth:
            i += 1
        elif src.startswith("--", i):
            j = src.find("\n", i)
            i = n if j < 0 else j
        else:
            out.append(src[i])
            i += 1
    return "".join(out)


def lean_expr(text, kvals=None):
    """Translate a Lean real-arithmetic expression into a Python one: drop the
    `( x : ℝ )` casts, turn `k.factorial` into factorial(k) and `^` into `**`.
    Only arithmetic is handled, which is all cVal and the phiPoly bodies use."""
    import re
    s = text.strip()
    s = re.sub(r"\(\s*([A-Za-z_][A-Za-z0-9_.']*)\s*:\s*ℝ\s*\)", r"\1", s)
    s = re.sub(r"\(\s*([0-9]+)\s*:\s*ℝ\s*\)", r"\1", s)
    s = re.sub(r"([A-Za-z_][A-Za-z0-9_']*)\.factorial", r"factorial(\1)", s)
    s = s.replace("^", "**")
    return s


def lean_eval(text, **vars):
    """Evaluate a translated Lean arithmetic expression exactly over Q."""
    env = {"factorial": factorial, "Fr": Fr, "__builtins__": {}}
    env.update(vars)
    return eval(lean_expr(text), env)          # noqa: S307 - arithmetic only


def lean_body(src, name):
    """The body of `def name ... := <body>`, joined across continuation lines."""
    import re
    m = re.search(r"def\s+" + re.escape(name)
                  + r"\s*(?:\([^)]*\)|\{[^}]*\})*\s*:[^:=]*:=\s*(.*?)(?=\n\n|\n/|\n@|\n(?:private\s+|protected\s+|noncomputable\s+)*(?:theorem|lemma|def)\s)",
                  src, re.S)
    if not m:
        return None
    return " ".join(line.strip() for line in m.group(1).split("\n")).strip()


def lean_hyp_threshold(src, name):
    """The integer t in a hypothesis `(h... : t ≤ n)` of the named theorem."""
    import re
    m = re.search(r"theorem\s+" + re.escape(name) + r"\b(.*?):=", src, re.S)
    if not m:
        return None
    h = re.search(r"\(\s*h[A-Za-z0-9_']*\s*:\s*([0-9]+)\s*≤\s*n\s*\)", m.group(1))
    return int(h.group(1)) if h else None


def lean_decl_audit_sets(src):
    """(declared, audited) name sets, by the corrected regexes: an optional
    attribute prefix, the private/protected/noncomputable modifiers, and a name
    that may be followed by a binder, a colon, a brace, or end of line."""
    import re
    decl = set(re.findall(
        r"^(?:@\[[^\]]*\][ \t]*)?(?:private[ \t]+|protected[ \t]+"
        r"|noncomputable[ \t]+)*(?:theorem|lemma|def|abbrev|instance)[ \t]+"
        r"([A-Za-z_][A-Za-z0-9_'.]*)(?=[ \t]*(?:[({\[:]|$))",
        src, re.M))
    aud = set(re.findall(r"#print\s+axioms\s+([A-Za-z_][A-Za-z0-9_'.]*)", src))
    return decl, aud


def V12():
    log("V12. THE FORMALISATION SCOPE.  The paper names the cells that are")
    log("     kernel-checked.  This check reads each Lean source AT THE COMMIT")
    log("     THE PAPER CITES FOR IT, and confirms the scope is neither over-")
    log("     stated nor understated.  It is the only check that reads outside")
    log("     this file.")
    if "--no-lean" in sys.argv:
        log("     SKIPPED by --no-lean: the formalisation claims of Section 10")
        log("     are UNCHECKED in this run.  Every other check is unaffected.")
        log("")
        return
    tv = lean_source("TverbergStability.lean")
    sk = lean_source("StabilityK3.lean")
    li = lean_source("LayerIdentity.lean")
    sk4 = lean_source("StabilityK4.lean")
    sf = lean_source("SigmaFour.lean")
    sk5s = lean_source("StabilityK5Sieve.lean")
    sk5 = lean_source("StabilityK5.lean")
    us = lean_source("UniformStability.lean")
    if not check("V12 Lean sources readable at the cited commits",
                 tv is not None and sk is not None and li is not None
                 and sk4 is not None and sf is not None):
        log("     *** the sources are NOT readable at the cited commits.  The")
        log("     scope claim is therefore unverified; run with --no-lean to")
        log("     say so in the log, or from a checkout that has them.")
        log("")
        return
    for f, s in (("TverbergStability.lean", tv), ("StabilityK3.lean", sk),
                 ("LayerIdentity.lean", li), ("StabilityK4.lean", sk4),
                 ("SigmaFour.lean", sf)):
        log(f"     read {f} at {LEAN_COMMIT[f]}  ({len(s)} chars)")

    # (a) The constant.  cVal must BE the paper's c(n,k) -- compared as exact
    # rationals over a grid, not as text.
    body = lean_body(tv, "cVal")
    ok_c, seen_pos = body is not None, False
    if body:
        for k in range(2, 8):
            for n in range(2, 30):
                want = (Fr(k) * (k - 1) * factorial(k)
                        / (4 * Fr(n) ** k * Fr(n - 1) ** 2))
                if MUT.get("lean_const"):
                    want = want * 2                              # FAULT M6
                got = lean_eval(body, k=k, n=Fr(n))
                if want > 0:
                    seen_pos = True
                if got != want:
                    ok_c = False
    check("V12 cVal is the paper's c(n,k)", ok_c)
    # Non-vacuity: a doubled constant is only visible where c is nonzero.
    check("V12 cVal grid is nonzero somewhere", seen_pos)
    log(f"       cVal = {body}")
    log(f"       equals c(n,k) = k(k-1)k!/(4 n^k (n-1)^2) over"
        f" 2<=k<=7, 2<=n<=29: {ok_c}   (nonzero there: {seen_pos})")

    # (b) The statement.  StabilityAt must carry the paper's four ingredients.
    import re
    sa = re.search(r"def\s+StabilityAt.*?(?=\n/-)", tv, re.S)
    parts = {"binomial C(n,k)^2": r"n\.choose k[^\n]*\^\s*2",
             "the constant cVal": r"cVal k n",
             "squared distance to J/n": r"A i j - 1 / \(n",
             "sigma_k as sigP": r"RookSum\.sigP k A",
             "the barycentre value k!/n^k": r"k\.factorial[^\n]*\)\s*/\s*\(n"}
    for label, pat in parts.items():
        check(f"V12 StabilityAt has {label}",
              sa is not None and re.search(pat, sa.group(0)) is not None)
    log("       StabilityAt carries C(n,k)^2, cVal, ||A-J/n||^2, sigP and"
        " k!/n^k: True")
    log("       (this ingredient check is structural; the constant itself is")
    log("        compared as a rational function above)")

    # (c) The formalised cells, against the paper's thresholds.
    for k, thr in sorted(PAPER_LEAN_CELLS.items()):
        name = {2: "stabilityAt_two", 3: "stabilityAt_three",
                4: "stabilityAt_four", 5: "stabilityAt_five"}[k]
        got = lean_hyp_threshold({4: sk4, 5: sk5}.get(k, sk), name)
        want = thr
        if MUT.get("lean_cell") and k == 3:
            want = 3                                             # FAULT M5
        check(f"V12 {name} hypothesis is n >= {want}", got == want)
        log(f"       {name}: Lean requires n >= {got}, paper claims the cell"
            f" n >= {want}   match {got == want}")

    # (d) The cells the paper says are NOT formalised.  Absence is only
    # evidence if the same search finds what IS there.
    both = tv + sk + sk4 + sk5
    present = [w for w in ("two", "three", "four", "five")
               if re.search(r"theorem\s+stabilityAt_" + w, both)]
    check("V12 presence test finds the formalised cells (non-vacuity)",
          present == ["two", "three", "four", "five"])
    names = ["six"]
    if MUT.get("lean_phantom"):
        names = ["two"]                                          # FAULT M8
    absent = [w for w in names
              if re.search(r"theorem\s+stabilityAt_" + w, both) is None]
    check("V12 no stabilityAt at k = 6", absent == names)
    log(f"       found: stabilityAt_{{{', '.join(present)}}};"
        f" absent: stabilityAt_{{{', '.join(names)}}}   as the paper states")

    # (d2) The sigma_4 core expansion (4.3), kernel-checked at every centred
    # B: present, with BOTH marginal hypotheses in its statement.
    s4m = re.search(r"theorem\s+sigma_four_centred\b(.*?):=\s*by", sf, re.S)
    check("V12 sigma_four_centred is present", s4m is not None)
    if s4m:
        stmt4 = s4m.group(1)
        for label, pat in (("the row-marginal hypothesis",
                            r"∀ i, ∑ j, B i j = 0"),
                           ("the column-marginal hypothesis",
                            r"∀ j, ∑ i, B i j = 0"),
                           ("sigma_4 as sigP", r"RookSum\.sigP 4 B")):
            check(f"V12 sigma_four_centred carries {label}",
                  re.search(pat, stmt4) is not None)
        log("       sigma_four_centred: present, with both marginal"
            " hypotheses and sigP 4 in its statement")

    # (e) The threshold layer.  Lean's phiPoly_k is an INDEPENDENT derivation
    # of P_k; it must agree with the one this verifier builds in V6c.
    for k, thr in sorted(PAPER_THRESHOLDS.items()):
        pb = lean_body(tv, f"phiPoly{k}")
        num, den = phi_reduced(k)
        P = padd(den, [-x for x in num])
        deg = len(P) - 1
        pts = [Fr(37 + 5 * i) for i in range(deg + 2)]
        vals_lean, vals_mine = [], [pev(P, x) for x in pts]
        okp = pb is not None
        if pb:
            body_k = pb
            if MUT.get("lean_polys"):
                body_k = body_k.split("-")[0].split("+")[0]       # FAULT M7
            vals_lean = [lean_eval(body_k, n=x) for x in pts]
            okp = vals_lean == vals_mine
        check(f"V12 phiPoly{k} equals this verifier's P_{k}", okp)
        # Non-vacuity: the polynomials must not be constant, or truncating one
        # would be invisible.
        check(f"V12 P_{k} is non-constant", len(set(vals_mine)) > 1)
        thr_lean = lean_hyp_threshold(tv, f"phiPoly{k}_pos")
        check(f"V12 phiPoly{k}_pos threshold is {thr}", thr_lean == thr)
        log(f"       phiPoly{k}: agrees with P_{k} at {len(pts)} points"
            f" (degree {deg}): {okp};  positivity from n >= {thr_lean},"
            f" paper says {thr}")
        # The shifted form the paper displays, as Lean states it in `hshift`.
        m = re.search(r"hshift\s*:\s*phiPoly" + str(k)
                      + r"\s*n\s*=(.*?):=\s*by", tv, re.S)
        if check(f"V12 phiPoly{k} shifted form present", m is not None):
            sh = " ".join(x.strip() for x in m.group(1).split("\n"))
            oks = all(lean_eval(sh, n=x) == pev(P, x) for x in pts)
            check(f"V12 phiPoly{k} shifted form is P_{k}(m+{thr})", oks)
            log(f"                  Lean's P_{k}(m+{thr}) form matches: {oks}")

    # (f) Proposition 5, kernel-checked: recompute the numbers Lean stores.
    w = [[Fr(0) if i == j else Fr(1, 2) for j in range(3)] for i in range(3)]
    okw = re.search(r"if i = j then 0 else 1 / 2", tv) is not None
    check("V12 witness33 is the paper's witness", okw)
    s3 = sigma(w, 3)
    d3 = sum((w[i][j] - Fr(1, 3)) ** 2 for i in range(3) for j in range(3))
    lean_s3 = re.search(r"witness33_sigma[^=]*=\s*([0-9]+\s*/\s*[0-9]+)", tv)
    lean_d3 = re.search(r"witness33_dist[^=]*=\s*([0-9]+\s*/\s*[0-9]+)", tv)
    check("V12 Lean's witness33_sigma agrees with exact sigma_3",
          lean_s3 is not None and Fr(lean_s3.group(1).replace(" ", "")) == s3)
    check("V12 Lean's witness33_dist agrees with exact ||B||^2",
          lean_d3 is not None and Fr(lean_d3.group(1).replace(" ", "")) == d3)
    check("V12 not_stabilityAt_three_three is present",
          re.search(r"theorem\s+not_stabilityAt_three_three", tv) is not None)
    check("V12 three_threshold_not_slack is present",
          re.search(r"theorem\s+three_threshold_not_slack", sk) is not None)
    log(f"       Proposition 5: Lean stores sigma_3 = {lean_s3.group(1)} and"
        f" ||B||^2 = {lean_d3.group(1)};")
    log(f"                      this verifier computes {s3} and {d3}   match")
    log("       not_stabilityAt_three_three and three_threshold_not_slack:"
        " both present")

    # (g) Lemma 2, kernel-checked at EVERY k, under hypotheses weaker than
    # doubly stochastic.  First the coefficient: Lean's tVal must be the
    # paper's t_m, compared as exact rationals.
    tb = lean_body(tv, "tVal")
    sb = lean_body(tv, "sVal")
    ok_t, seen_t = tb is not None and sb is not None, False
    if ok_t:
        for k in range(2, 8):
            for n in range(k, 20):
                for m in range(2, k + 1):
                    want = t_co(n, k, m)
                    s = falling(Fr(k), m) / falling(Fr(n), m)
                    got = s ** 2 * Fr(factorial(k - m)) / Fr(n) ** (k - m)
                    if want != 0:
                        seen_t = True
                    if got != want:
                        ok_t = False
    check("V12 Lean's tVal is the paper's t_m", ok_t)
    check("V12 t_m grid is nonzero somewhere", seen_t)
    log(f"       sVal = {sb}")
    log(f"       tVal = {tb}")
    log(f"       equal to the paper's s_m, t_m over 2<=k<=7, k<=n<=19,"
        f" 2<=m<=k: {ok_t}   (nonzero there: {seen_t})")

    # The statement of Lemma 2 itself, ingredient by ingredient, and the
    # weakening: its hypotheses must NOT include double stochasticity.
    lm = re.search(r"theorem\s+layer_identity\b(.*?):=\s*by", li, re.S)
    check("V12 layer_identity is present", lm is not None)
    if lm:
        stmt = lm.group(1)
        want_tokens = {
            "1 <= k": r"hk\s*:\s*1\s*≤\s*k",
            "k <= n": r"hkn\s*:\s*k\s*≤\s*n",
            "A = J/n + B": r"A i j = 1 / \(n : ℝ\) \+ B i j",
            "sum B = 0 (the weak hypothesis)": r"∑ i, ∑ j, B i j = 0",
            "sigma_k(A)/C(n,k)^2": r"RookSum\.sigP k A / \(\(n\.choose k",
            "the barycentre value k!/n^k": r"k\.factorial[^\n]*\)\s*/\s*\(n : ℝ\) \^ k",
            "the sum over m = 2..k": r"Finset\.Icc 2 k",
            "t_m sigma_m(B)": r"tVal k n m \* RookSum\.sigP m B"}
        for label, pat in want_tokens.items():
            check(f"V12 layer_identity carries {label}",
                  re.search(pat, stmt) is not None)
        need_ds = bool(MUT.get("lean_weak"))                      # FAULT M10
        has_ds = "doublyStochastic" in stmt
        check("V12 layer_identity does NOT assume double stochasticity",
              has_ds == need_ds)
        # Non-vacuity: the token IS findable, so its absence here is real.
        check("V12 doublyStochastic token is findable elsewhere",
              "doublyStochastic" in sk)
        log("       layer_identity: every ingredient of Lemma 2 present,"
            " at every k")
        log("       hypotheses are 1 <= k <= n and sum B = 0 only --"
            " `doublyStochastic`")
        log("       appears nowhere in the statement, though it does appear"
            " in StabilityK3,")
        log("       so that absence is measured and not a failed search")

    # (h) The audit blocks of the four files, and the counts the paper
    # displays.
    measured = {}
    for fname, src in (("StabilityK3.lean", sk), ("LayerIdentity.lean", li),
                       ("StabilityK4.lean", sk4), ("SigmaFour.lean", sf),
                       ("StabilityK5Sieve.lean", sk5s),
                       ("StabilityK5.lean", sk5),
                       ("UniformStability.lean", us)):
        decl, aud = lean_decl_audit_sets(src)
        if MUT.get("lean_orphan") and aud:
            aud = set(sorted(aud)[1:])                           # FAULT M9
        orphans = sorted(decl - aud)
        phantoms = sorted(aud - decl)
        check(f"V12 {fname} no unaudited declarations (orphan diff)",
              not orphans)
        check(f"V12 {fname} no audit lines without declarations (phantom)",
              not phantoms)
        check(f"V12 {fname} declaration set is non-empty (non-vacuity)",
              bool(decl))
        code = lean_strip_comments(src)
        check(f"V12 {fname} no sorry in code", "sorry" not in code)
        check(f"V12 {fname} no native_decide in code",
              "native_decide" not in code)
        log(f"       {fname}: {len(decl)} declared, {len(aud)} audited,"
            f" orphans {orphans}, phantoms {phantoms};"
            f" no `sorry`, no `native_decide`")
        measured[fname] = (len(decl), len(aud))
    # The paper displays both counts; parse them back so displayed = checked.
    try:
        with open("results/paper_b.typ") as fh:
            paper = fh.read()
        pairs = [(int(a), int(b)) for a, b in
                 re.findall(r"(\d+)\s+of\s+(\d+)\s+declarations", paper)]
        check("V12 paper displays exactly the two audited counts",
              sorted(pairs) == sorted(measured.values()))
        log(f"       the paper displays {sorted(pairs)}; measured"
            f" {sorted(measured.values())}   match"
            f" {sorted(pairs) == sorted(measured.values())}")
        # The section also displays the TOTAL, which must be their sum.
        tot = sum(a for a, _ in measured.values())
        tm = re.search(r"(\d+)\s+audited\s+declarations", paper)
        if check("V12 paper displays the audited total", tm is not None):
            check("V12 the displayed total is the sum of the two counts",
                  int(tm.group(1)) == tot)
            log(f"       the paper displays {tm.group(1)} audited"
                f" declarations in total; measured {tot}")
    except OSError:
        check("V12 paper readable for its displayed counts", False)
    log("")


def main():
    rng = random.Random(20260803)
    only_mutate = "--mutate" in sys.argv
    log("=" * 74)
    log("STANDALONE VERIFIER -- stability lemma for subpermanent sums")
    if only_mutate:
        log("MODE: --mutate, mutation controls only")
    log("=" * 74)
    log("")
    if only_mutate:
        V10()
        log("=" * 74)
        log(f"TOTAL FAILURES: {FAIL}")
        log("VERDICT: " + ("ALL CONTROLS FIRE" if FAIL == 0
                          else "A CONTROL FAILED TO FIRE"))
        log("=" * 74)
        with open("results/graded_verify_mutate.log", "w") as fh:
            fh.write("\n".join(OUT) + "\n")
        return 0 if FAIL == 0 else 1
    V1(rng)
    V2(rng)
    V3(rng)
    V4(rng)
    V5(rng)
    V6()
    V6b()
    V6c()
    V7(rng)
    V8()
    V9()
    V11()
    V12()
    V10()
    log("=" * 74)
    log(f"TOTAL FAILURES: {FAIL}")
    log("VERDICT: " + ("ALL CHECKS PASS" if FAIL == 0 else "FAILURES PRESENT"))
    log("=" * 74)
    with open("results/graded_verify_stability.log", "w") as fh:
        fh.write("\n".join(OUT) + "\n")
    return 0 if FAIL == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
