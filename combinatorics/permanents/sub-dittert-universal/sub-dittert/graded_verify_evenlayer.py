#!/usr/bin/env python3
"""Graded verifier for EVENLAYER.md -- uniform even-layer absorption.

Exact Fraction arithmetic throughout; no floating point in any decision
(floats appear only inside format strings).

The object under test is the TIER-GRADED layer bound.  With
K_2 = Q exactly, exp(Q x^2/2) factors out of the exponential formula and

    sigma_m(B) = sum_p (Q/2)^p / p! * r_{m-2p},
    r_j = [x^j] exp( sum_{e>=3} K_e x^e / e! ),      r_0 = 1, r_1 = r_2 = 0,

so a layer is a sum of TIERS indexed by (j, c): j the number of indices not in
a 2-block, c the number of blocks of the partition of those j indices (every
block of size >= 3, hence c <= floor(j/3)).  Tier (j,c) has Q-degree
(m-j)/2 + c and coefficient mass M_{j,c}.  The pairing tier is j = 0, is
non-negative (mu mu = +1, S = prod tr((BB^T)^l)), and is KEPT.

Sections
  X1  the machinery: Lam_e (log-EGF of D_m^2) against the brute-force
      connected Moebius mass; M_{j,c}; the mass identity; the degree cap
  X2  the tier decomposition is an IDENTITY at exact test matrices, and the
      pairing tier equals (Q/2)^{m/2}/(m/2)! and is >= 0
  X3  the hypothesis (S4) at the test matrices, and the layer bound
      sigma_m >= L_m(Q)
  X4  ABSORPTION: the exact threshold Q*_m, its monotonicity, its law, and
      that it is sharp (the tier bound is negative one step below)
  X5  the constant C^abs: validity, the eta identity, and C^abs <= C^hyb
  X6  recomposition of Ntilde(k) through collar_budget.Psi, with witnesses
      at and below the threshold
  X7  the order: where absorption is active, and Ntilde against the collar
      floor at large k
  X8  mutation controls

Run:  GUARD_MEM=4G GUARD_CPUS=200% ../guard.sh python3 -u graded_verify_evenlayer.py
"""
import sys, os
from fractions import Fraction as Fr
from math import factorial, comb

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from collar_budget import Psi, Ntilde, Q_cap, eta, t_coef            # noqa: E402
import collar_budget                                                 # noqa: E402
import graded_verify_oddlayer as OL                                  # noqa: E402

PASS = FAIL = 0
FIRED = []
MUT = {}

MAXE = 34               # highest cumulant index the tables carry


def log(s=""):
    print(s, flush=True)


def check(name, ok, detail=""):
    global PASS, FAIL
    if ok:
        PASS += 1
    else:
        FAIL += 1
        FIRED.append(name)
    log(f"  [{'ok ' if ok else 'FAIL'}] {name}" + (f"   {detail}" if detail else ""))
    return ok


# ======================================================= the coefficient tables

def derang(m):
    d = [1, 0]
    while len(d) <= m:
        i = len(d)
        d.append((i - 1) * (d[i - 1] + d[i - 2]))
    return d[m]


def dfact(x):
    """x!! for odd x >= -1."""
    r = 1
    while x > 1:
        r *= x
        x -= 2
    return r


def _lam_table(E):
    """Lam_e, e = 0..E, from  sum_m D_m^2 x^m/m! = exp( sum_e Lam_e x^e/e! ).

    This is the exponential formula applied to the l^1 Moebius masses: the
    mass of a DISCONNECTED (pi,rho) factorises over components, so the
    connected masses Lam_e are the log of the full masses D_m^2/m!
    (UNIFORM-G sec 4, ODDLAYER W3).  Checked against the brute-force
    connected sum in X1."""
    f = [Fr(derang(m) ** 2, factorial(m)) for m in range(E + 1)]
    g = [Fr(0)] * (E + 1)
    for e in range(1, E + 1):
        acc = f[e]
        for i in range(1, e):
            acc -= Fr(i, e) * g[i] * f[e - i]
        g[e] = acc
    return [g[e] * factorial(e) for e in range(E + 1)]


LAM = _lam_table(MAXE)


def Lam(e):
    if MUT.get("bad_lam"):
        return Fr(derang(e) ** 2)
    return LAM[e]


def _M_table(E):
    """M[j][c] = [x^j y^c] exp( y * sum_{e>=3} Lam_e x^e/e! ).

    M[j][c] is the l^1 mass of the tier of r_j whose partition has c blocks,
    every block of size >= 3."""
    S = [Fr(0)] * (E + 1)
    for e in range(3, E + 1):
        S[e] = Fr(Lam(e), factorial(e))
    M = [[Fr(0)] * (E // 3 + 2) for _ in range(E + 1)]
    M[0][0] = Fr(1)
    cur = [Fr(0)] * (E + 1)
    cur[0] = Fr(1)
    for c in range(1, E // 3 + 1):
        nxt = [Fr(0)] * (E + 1)
        for a in range(E + 1):
            if cur[a] == 0:
                continue
            for e in range(3, E + 1 - a):
                nxt[a + e] += cur[a] * S[e]
        cur = [x / c for x in nxt]
        for j in range(E + 1):
            if cur[j]:
                M[j][c] = cur[j]
    return M


_MCACHE = {}


def Mt():
    key = (MUT.get("bad_lam"),)
    if key not in _MCACHE:
        _MCACHE[key] = _M_table(MAXE)
    return _MCACHE[key]


# ================================================== the tiers and the bound

def tiers(m, et):
    """[(degree, coefficient)] of the NEGATIVE part of layer m, tier by tier.

        sigma_m(B)  >=  pos_m(Q)  -  sum_{(d,cf)} cf * Q^d.

    Inputs consumed, and only these:
      (S1)  K_3 >= -4 eta Q        one-sided, PROVED (paper_b Lemma S3(a),
                                   with the collar's eta = 1/n + sqrt(2 u_max))
      (S4)  |K_e| <= Lam_e Q       e >= 3, the U5 cumulant rate (HYPOTHESIS)
      (S2)  K_3 <= 4 beta Q <= 4 Q the cheap side, used inside mixed tiers

    Two tiers are handled better than by |.|:
      * j = 3c with c EVEN is prod K_3^c >= 0 and is DROPPED;
      * j = 3c with c ODD  is K_3^c >= -(4 eta Q)^c by (S1), so its mass
        carries eta^c rather than 1.
    """
    M = Mt()
    out = []
    j0 = 4 if m % 2 == 0 else 3
    for j in range(j0, m + 1, 2):
        s = (m - j) // 2                    # 2-blocks sitting on top
        pref = Fr(1, 2 ** s * factorial(s))
        if MUT.get("drop_top_tier") and j == m:
            continue
        for c in range(1, len(M[j])):
            v = M[j][c]
            if v == 0:
                continue
            pure3 = (j == 3 * c)
            if pure3 and c % 2 == 0:
                continue                     # K_3^c >= 0
            if pure3:
                v = Fr(2, 3) ** c / factorial(c) * et ** c
            d = s + c
            if MUT.get("deg_shift"):
                d -= 1
            out.append((d, pref * v))
    return out


def pos_coef(m):
    """(degree, coefficient) of the all-pairing tier; None at odd m."""
    if m % 2:
        return None
    P = m // 2
    return (P, Fr(1, 2 ** P * factorial(P)))


def L_layer(m, Q, et):
    """The layer lower bound L_m(Q), exact."""
    v = Fr(0)
    pc = pos_coef(m)
    if pc:
        v += pc[1] * Fr(Q) ** pc[0]
    for d, cf in tiers(m, et):
        v -= cf * Fr(Q) ** d
    return v


_QSCACHE = {}


def Qstar(m, et, hi=10 ** 9):
    """The least INTEGER Q >= 1 with L_m(Q) >= 0, m even.

    Well defined and found by bisection because every negative tier has
    degree <= m/2 - 1 < m/2, so  sum cf Q^{d - m/2}  is strictly decreasing:
    the condition is monotone in Q."""
    if m % 2:
        return None
    key = (m, et, MUT.get("bad_lam"), MUT.get("drop_top_tier"),
           MUT.get("deg_shift"), MUT.get("over_absorb"))
    if key in _QSCACHE:
        return _QSCACHE[key]
    P, b = pos_coef(m)
    T = tiers(m, et)

    def ok(Q):
        return sum(cf * Fr(Q) ** d for d, cf in T) <= b * Fr(Q) ** P

    hb = 1
    while hb <= hi and not ok(hb):
        hb *= 2
    if hb > hi:
        _QSCACHE[key] = None
        return None
    lo = hb // 2
    while lo + 1 < hb:
        mid = (lo + hb) // 2
        if ok(mid):
            hb = mid
        else:
            lo = mid
    if MUT.get("over_absorb"):
        hb = max(1, hb // 2)
    _QSCACHE[key] = hb
    return hb


def C_abs(m, n, k, slice_mode=False, absorb=True):
    """THE TIER-GRADED CONSTANT.  sigma_m(z) >= -C_m Q for every Q <= Q_c.

        C_m = sum over tiers  cf * Qhat^{d-1},
        Qhat = min(Q_c, Q*_m)  at even m (absorption),  Q_c  at odd m.

    Sound because (i) sum cf Q^{d-1} is non-decreasing in Q, so the maximum
    of (negative part)/Q over (0, Qhat] is at Qhat, and (ii) for Q in
    (Q*_m, Q_c] the layer is non-negative outright."""
    Qc = Q_cap(n, k)
    et = Fr(1, n) if slice_mode else eta(n, k)
    if MUT.get("no_eta"):
        et = Fr(1, n)
    Qh = Qc
    if absorb and m % 2 == 0:
        qs = Qstar(m, et)
        if qs is not None and qs < Qc:
            Qh = Fr(qs)
    return sum(cf * Qh ** (d - 1) for d, cf in tiers(m, et))


def C_grade(m, n, k, slice_mode=False):
    """Tier grading with the pairing tier DISCARDED (absorption switched off).
    Isolates how much of the gain is grading and how much is absorption."""
    return C_abs(m, n, k, slice_mode=slice_mode, absorb=False)


# ============================================ the r_j of an actual matrix

def r_series(K, upto):
    """r_j = [x^j] exp( sum_{e>=3} K_e x^e/e! ) from actual cumulants K."""
    f = [Fr(0)] * (upto + 1)
    f[0] = Fr(1)
    for j in range(1, upto + 1):
        acc = Fr(0)
        for e in range(3, j + 1):
            acc += Fr(e, j) * Fr(K[e], factorial(e)) * f[j - e]
        f[j] = acc
    return f


# ================================================================== X1

def X1():
    log("\nX1  the coefficient tables: Lam_e, M_{j,c}, and the mass identity")
    for e in range(2, 6):
        check(f"Lam_{e} (log-EGF) == brute-force connected Moebius mass",
              Lam(e) == OL.Lam(e), f"{Lam(e)}")
    check("Lam_2..Lam_5 == 1, 4, 78, 1896  (ODDLAYER W3)",
          [Lam(e) for e in range(2, 6)] == [1, 4, 78, 1896])
    check("Lam_6 = 68880, Lam_7 = 3386160",
          Lam(6) == 68880 and Lam(7) == 3386160, f"{Lam(6)}, {Lam(7)}")
    M = Mt()
    check("M_{4,1} = Lam_4/4! = 13/4", M[4][1] == Fr(13, 4))
    check("M_{5,1} = Lam_5/5! = 79/5", M[5][1] == Fr(79, 5))
    check("M_{6,2} = (2/3)^2/2! = 2/9   (the (3,3) tier)", M[6][2] == Fr(2, 9))
    check("M_{9,3} = (2/3)^3/3! = 4/81  (the (3,3,3) tier)", M[9][3] == Fr(4, 81))
    for j in range(3, 19):
        cmax = max([c for c in range(len(M[j])) if M[j][c]] or [0])
        check(f"degree cap: M_(j,c) = 0 for c > floor(j/3)   j={j}",
              cmax <= j // 3, f"cmax={cmax}, floor(j/3)={j // 3}")
    for m in range(2, 15):
        tot = Fr(0)
        for p in range(m // 2 + 1):
            j = m - 2 * p
            tot += Fr(comb(m, 2 * p) * dfact(2 * p - 1)) * factorial(j) * sum(M[j])
        check(f"mass identity  sum_p C(m,2p)(2p-1)!! j! M_j = D_m^2   m={m}",
              tot == derang(m) ** 2, f"{tot}")
    check("pairing tier count: (m-1)!! Q^(m/2)/m! == (Q/2)^(m/2)/(m/2)!",
          all(Fr(dfact(m - 1), factorial(m)) == pos_coef(m)[1]
              for m in range(2, 17, 2)))


# ================================================================== X2

def X2():
    log("\nX2  the tier decomposition is an identity, and the pairing tier is >= 0")
    for n in (5, 6, 7):
        for label, A in OL.test_matrices(n):
            B = OL.centre(A, n)
            Q = OL.frob2(B, n)
            sig = OL.sigmas(B, n)
            K = OL.cumulants(sig, n)
            r = r_series(K, n)
            for m in range(2, n + 1):
                got = sum(Fr(Q, 2) ** p / factorial(p) * r[m - 2 * p]
                          for p in range(m // 2 + 1))
                check(f"sigma_{m} = sum_p (Q/2)^p/p! r_(m-2p)   n={n} {label}",
                      got == sig[m])
            check(f"K_2 = Q exactly   n={n} {label}", K[2] == Q)
            check(f"r_0,r_1,r_2 = 1,0,0   n={n} {label}",
                  r[0] == 1 and r[1] == 0 and r[2] == 0)
    # the pairing tier itself: mu mu = +1 and S = prod tr((BB^T)^l) >= 0
    for n in (5, 6):
        for label, A in OL.test_matrices(n):
            B = OL.centre(A, n)
            Q = OL.frob2(B, n)
            for m in (2, 4, 6):
                P = m // 2
                val = Fr(Q, 2) ** P / factorial(P)
                check(f"pairing tier (Q/2)^{P}/{P}! >= 0   m={m} n={n} {label}",
                      val >= 0)
    # UNIFORM-G sec 8.1's pairing tier, and the sub-tier the exponential
    # formula actually isolates.  They are NOT the same object: sec 8.1's tier
    # is every pair (pi,rho) of perfect pairings, whose graph is a union of
    # even CYCLES; the K_2^{m/2} tier is only the diagonal pi = rho, whose
    # graph is a union of DOUBLE EDGES.  The bound proved here keeps the
    # diagonal sub-tier and charges the rest through (S4) -- conservative, and
    # exactly the accounting UNIFORM-G sec 8.3 uses.
    for n in (5, 6):
        for label, A in OL.test_matrices(n)[:3]:
            B = OL.centre(A, n)
            Q = OL.frob2(B, n)
            for m in (2, 4):
                parts = [p for p in OL.set_partitions(m)
                         if all(len(b) == 2 for b in p)]
                check(f"mu(pi) mu(rho) = +1 on every pairing pair   m={m} n={n}",
                      all(OL.mobius(pi) * OL.mobius(rho) == 1
                          for pi in parts for rho in parts))
                tot = sum(OL.mobius(pi) * OL.mobius(rho)
                          * OL.orbit_S(pi, rho, B, n, m)
                          for pi in parts for rho in parts)
                diag = sum(OL.orbit_S(pi, pi, B, n, m) for pi in parts)
                check(f"sec 8.1 pairing tier >= 0   m={m} n={n} {label}", tot >= 0,
                      f"{tot}")
                check(f"diagonal sub-tier = (m-1)!! Q^(m/2)   m={m} n={n} {label}",
                      diag == dfact(m - 1) * Q ** (m // 2), f"{diag}")
                check(f"sec 8.1 tier >= diagonal sub-tier   m={m} n={n} {label}",
                      tot >= diag)


# ================================================================== X3

def X3():
    log("\nX3  the hypotheses at the test matrices, and the layer bound")
    for n in (5, 6, 7, 8):
        for label, A in OL.test_matrices(n):
            B = OL.centre(A, n)
            Q = OL.frob2(B, n)
            if Q == 0:
                continue
            sig = OL.sigmas(B, n)
            K = OL.cumulants(sig, min(n, 8))
            for e in range(3, min(n, 8) + 1):
                check(f"(S4) |K_{e}| <= Lam_{e} Q   n={n} {label}",
                      abs(K[e]) <= Lam(e) * Q)
            check(f"(S1) K_3 >= -4Q/n   n={n} {label}", K[3] >= -4 * Q / n)
            for m in range(3, min(n, 8) + 1):
                check(f"sigma_{m} >= L_{m}(Q)   n={n} {label}",
                      sig[m] >= L_layer(m, Q, Fr(1, n)),
                      f"{float(sig[m]):.6g} >= {float(L_layer(m, Q, Fr(1, n))):.6g}")


# ================================================================== X4

def X4():
    log("\nX4  ABSORPTION: the exact threshold Q*_m")
    et = Fr(1, 10 ** 6)
    log("       m      Q*_m   Q*/m^2   13(m/2)(m/2-1)")
    QS = {}
    for m in range(4, 25, 2):
        qs = Qstar(m, et)
        QS[m] = qs
        log(f"     {m:3d}  {str(qs):>8s}   {qs / m ** 2:6.3f}   "
            f"{13 * (m // 2) * (m // 2 - 1):>8d}")
    check("Q*_4 = 26 = 13*(2)(1) exactly (the (4,1) tier is the only one)",
          QS[4] == 26)
    for m in range(6, 25, 2):
        check(f"Q*_m >= 13(m/2)(m/2-1)   m={m}",
              QS[m] >= 13 * (m // 2) * (m // 2 - 1))
        check(f"Q*_m strictly increasing   m={m}", QS[m] > QS[m - 2])
    for m in range(4, 21, 2):
        qs = QS[m]
        check(f"L_{m}(Q*_m) >= 0   m={m}", L_layer(m, qs, et) >= 0)
        check(f"L_{m}(Q*_m - 1) < 0  (the threshold is exact)   m={m}",
              L_layer(m, qs - 1, et) < 0)
        for mult in (2, 4, 10):
            check(f"L_{m}(Q) >= 0 for Q = {mult} Q*_m   m={m}",
                  L_layer(m, mult * qs, et) >= 0)
    check("the negative tiers have degree <= m/2 - 1 (monotone absorption)",
          all(max(d for d, _ in tiers(m, et)) <= m // 2 - 1
              for m in range(4, 25, 2)))


# ================================================================== X5

def X5():
    log("\nX5  the constant C^abs: validity, the eta identity, C^abs <= C^hyb")
    for n in (5, 6, 7, 8):
        for label, A in OL.test_matrices(n):
            B = OL.centre(A, n)
            Q = OL.frob2(B, n)
            if Q == 0:
                continue
            sig = OL.sigmas(B, n)
            for m in range(3, min(n, 8) + 1):
                k = max(m, 4)
                check(f"sigma_{m} >= -C^abs Q   n={n} {label}",
                      sig[m] >= -C_abs(m, n, k, slice_mode=True) * Q)
    check("C_3^abs on the slice = 2/(3n) (the paper's constant, reproduced)",
          all(C_abs(3, n, 4, slice_mode=True) == Fr(2, 3 * n) for n in (6, 9, 12)))
    check("C_4^abs = 78/24 (pairing tier kept, nothing else at m = 4)",
          C_abs(4, 9, 5, slice_mode=True) == Fr(78, 24))
    check("C_5^abs == C_5^hyb (grading has nothing to do below m = 6)",
          all(C_abs(5, n, 6, slice_mode=True) == OL.C_hyb(5, n, 6, slice_mode=True)
              for n in (40, 300)))
    log("     C_m at (n,k) = (300, 8):")
    n, k = 300, 8
    for m in range(3, k + 1):
        log(f"       m={m}  L0={float(OL.C_L0(m, n, k)):11.4g}"
            f"  L1={float(OL.C_L1(m, n, k)):11.4g}"
            f"  hyb={float(OL.C_hyb(m, n, k)):11.4g}"
            f"  abs={float(C_abs(m, n, k)):11.4g}"
            f"  L2={float(OL.C_L2(m, n, k)):11.4g}")
    for (nn, kk) in ((300, 8), (40, 8), (120, 12), (60, 6)):
        for m in range(3, kk + 1):
            check(f"C_{m}^abs <= C_{m}^hyb   n={nn} k={kk}",
                  C_abs(m, nn, kk) <= OL.C_hyb(m, nn, kk),
                  f"{float(C_abs(m, nn, kk)):.6g} <= {float(OL.C_hyb(m, nn, kk)):.6g}")
        for m in range(6, kk + 1):
            check(f"C_{m}^abs STRICTLY beats C_{m}^hyb   n={nn} k={kk}",
                  C_abs(m, nn, kk) < OL.C_hyb(m, nn, kk))
    # the eta cost is present and is charged
    for (nn, kk, mm) in ((300, 8, 3), (300, 8, 5), (120, 6, 3), (120, 6, 5)):
        cs = C_abs(mm, nn, kk, slice_mode=True)
        cc = C_abs(mm, nn, kk)
        Qc = Q_cap(nn, kk)
        gap = Fr(2, 3) * (eta(nn, kk) - Fr(1, nn)) * Qc ** ((mm - 3) // 2) \
            / (2 ** ((mm - 3) // 2) * factorial((mm - 3) // 2))
        check(f"C_{mm}^abs(collar) = C^abs(slice) + eta-gap   n={nn} k={kk}",
              cc == cs + gap)
        check(f"C_{mm}^abs(collar) > C^abs(slice)   n={nn} k={kk}", cc > cs)


# ================================================================== X6

def X6(ks=None):
    log("\nX6  recomposition: Ntilde(k) through collar_budget.Psi")
    ks = ks or [6, 7, 8, 9, 10, 11, 12]
    log("       k     L0      L1     hyb   grade     abs      L2   floor")
    out = {}
    for k in ks:
        row = [Ntilde(k, C, hi=6000) for C in
               (OL.C_L0, OL.C_L1, OL.C_hyb, C_grade, C_abs, OL.C_L2, OL.C_zero)]
        out[k] = row
        log(f"     {k:3d}  " + "".join(f"{('-' if v is None else v):>7}" for v in row))
    for k in ks:
        L0, L1, hy, gr, ab, L2, fl = out[k]
        check(f"Ntilde ordering L0 >= L1 >= hyb >= abs >= floor   k={k}",
              L0 >= L1 >= hy >= ab >= fl, f"{out[k]}")
        check(f"abs strictly beats hyb   k={k}", ab < hy)
        check(f"abs BEATS the assumed L2 shape   k={k}", ab < L2)
        check(f"abs is within 2 of the collar floor   k={k}", ab - fl <= 2,
              f"abs={ab} floor={fl}")
        check(f"grade == abs (absorption inert at the threshold)   k={k}",
              gr == ab, f"grade={gr} abs={ab}")
    # witnesses at and below the threshold
    for k in ks:
        N = out[k][4]
        p0 = Psi(N, k, C_abs)
        p1 = Psi(N - 1, k, C_abs)
        check(f"WITNESS  Psi({N}, {k}) < 1", p0 < 1, f"{float(p0):.8f}")
        check(f"WITNESS  Psi({N - 1}, {k}) >= 1  (threshold is exact)", p1 >= 1,
              f"{float(p1):.8f}")
    return out


# ================================================================== X7

def X7():
    log("\nX7  the order: is absorption ever active, and what binds instead")
    log("       k   Ntilde   Q_c(Ntilde)   top even m   Q*_m   even m where it fires")
    for k in range(6, 13):
        N = Ntilde(k, C_abs, hi=6000)
        me = k if k % 2 == 0 else k - 1
        et = eta(N, k)
        Qc = Q_cap(N, k)
        fires = [m for m in range(4, me + 1, 2) if Qstar(m, et) < Qc]
        log(f"     {k:3d}   {N:6d}   {float(Qc):11.2f}   {me:10d}   "
            f"{Qstar(me, et):6d}   {fires}")
        check(f"absorption INACTIVE at the TOP even layer m={me}   k={k}",
              Qstar(me, et) >= Qc, f"Q*={Qstar(me, et)} vs Q_c={float(Qc):.2f}")
        check(f"absorption fires ONLY at m = 4, where C_4 has Q-degree 0   k={k}",
              fires == [4], f"{fires}")
        # UNIFORM-G sec 8.3's optimistic 6(m/2)(m/2-1) ~ 1.5 m^2 -- the leading
        # balance under the paper's ONE-SIDED K_4 >= -36 beta Q, which this
        # route does not have -- also exceeds Q_c at the top even layer,
        # at every k EXCEPT k = 7 (where the top even layer is m = 6, giving
        # 36 against Q_c = 42).
        if k != 7:
            check(f"the optimistic 1.5 m^2 threshold also exceeds Q_c   k={k}",
                  6 * (me // 2) * (me // 2 - 1) > Qc,
                  f"{6 * (me // 2) * (me // 2 - 1)} > {float(Qc):.2f}")
    check("k = 7 is the one exception: optimistic Q* = 36 < Q_c = 42",
          6 * 3 * 2 < Q_cap(Ntilde(7, C_abs, hi=6000), 7))
    # the decisive statement, independent of where absorption fires:
    check("C_4^abs is free of Qhat (degree 0), so absorption at m = 4 is vacuous",
          all(C_abs(4, n, k) == Fr(78, 24) for (n, k) in
              ((35, 6), (43, 7), (52, 8), (102, 12), (3000, 12))))
    log("     Ntilde against the collar floor at larger k, and where the")
    log("     pairing tier starts to bite:")
    log("       k     abs   grade   floor   abs/k^2   absorption fires at m =")
    for k in (14, 16, 18, 20, 24):
        a = Ntilde(k, C_abs, hi=4000)
        g = Ntilde(k, C_grade, hi=4000)
        f = Ntilde(k, OL.C_zero, hi=4000)
        et, Qc = eta(a, k), Q_cap(a, k)
        me = k if k % 2 == 0 else k - 1
        fires = [m for m in range(4, me + 1, 2) if Qstar(m, et) < Qc]
        log(f"     {k:3d}  {a:6d}  {g:6d}  {f:6d}   {a / k ** 2:7.4f}   {fires}")
        check(f"abs is within 3 of the collar floor   k={k}", a - f <= 3,
              f"abs={a} floor={f}")
        check(f"abs/k^2 <= 1   k={k}", Fr(a, k * k) <= 1, f"{a / k ** 2:.4f}")
        check(f"the pairing tier is worth at most 1 unit of Ntilde   k={k}",
              g - a <= 1, f"grade={g} abs={a}")
    check("the pairing tier is worth EXACTLY 1 unit, and only at k = 20",
          Ntilde(20, C_grade, hi=4000) - Ntilde(20, C_abs, hi=4000) == 1
          and all(Ntilde(k, C_grade, hi=4000) == Ntilde(k, C_abs, hi=4000)
                  for k in (14, 16, 18, 24)))
    # WHICH PILLAR BINDS.  Zero the collar's own cross-term blocks and read
    # the threshold the INTERFACE alone imposes.  collar_budget is not edited;
    # the two functions are swapped in this process and restored.
    log("     the threshold the INTERFACE alone imposes (collar blocks zeroed):")
    log("       k      L1     hyb     abs   collar floor   interface binds?")
    KS = list(range(6, 13)) + [16, 20]
    G2o, g1o = collar_budget.G2, collar_budget.g1
    collar_budget.G2 = lambda n, k, drop_t=None: Fr(0)
    collar_budget.g1 = lambda n, k: Fr(0)
    try:
        iface = {}
        for k in KS:
            iface[k] = [Ntilde(k, C, hi=6000)
                        for C in (OL.C_L1, OL.C_hyb, C_abs)]
    finally:
        collar_budget.G2, collar_budget.g1 = G2o, g1o
    for k in KS:
        fl = Ntilde(k, OL.C_zero, hi=6000)
        i1, ih, ia = iface[k]
        log(f"     {k:3d}  {i1:6d}  {ih:6d}  {ia:6d}   {fl:12d}   {ia > fl}")
        check(f"the INTERFACE no longer binds under C^abs   k={k}", ia < fl,
              f"interface-only={ia} < collar floor={fl}")
        if k >= 8:
            check(f"the interface DID bind under C^hyb   k={k}", ih > fl,
                  f"interface-only={ih} vs collar floor={fl}")
        check(f"C^abs cuts the interface-only threshold vs C^hyb   k={k}", ia < ih,
              f"{ia} < {ih}")


# ================================================================== X8

def X8():
    log("\nX8  mutation controls")
    global MUT, PASS, FAIL, FIRED
    faults = [
        ("bad_lam", "the connected mass Lam_e replaced by the full mass D_e^2",
         lambda: (X1(), X4())),
        ("drop_top_tier", "the j = m tier (the whole connected mass) dropped",
         lambda: (X3(), X5())),
        ("no_eta", "the collar degradation 1/n -> eta ignored in C^abs",
         lambda: (X5(), X6(ks=[6, 8]))),
        ("over_absorb", "the absorption threshold Q*_m halved",
         lambda: (X4(), X5())),
        ("deg_shift", "every tier degree lowered by one",
         lambda: (X3(), X5())),
    ]
    base = (PASS, FAIL, list(FIRED))
    weak = []
    for key, what, run in faults:
        MUT = {key: True}
        _MCACHE.clear()
        _QSCACHE.clear()
        PASS, FAIL, FIRED = 0, 0, []
        run()
        fired = FAIL
        log(f"     fault '{key}' ({what}): {fired} checks caught it")
        if fired < 2:
            weak.append(key)
            log(f"     *** CONTROL WEAK: '{key}' fired at {fired} positions")
        MUT = {}
        _MCACHE.clear()
        _QSCACHE.clear()
        PASS, FAIL, FIRED = 0, 0, []
    MUT = {}
    _MCACHE.clear()
    _QSCACHE.clear()
    PASS, FAIL, FIRED = base[0], base[1], base[2]
    check("every mutation control fires at >= 2 positions", not weak,
          ", ".join(weak) if weak else "")


# ==================================================================== main

def main():
    log("=" * 74)
    log("graded_verify_evenlayer.py -- uniform even-layer absorption, EVENLAYER.md")
    log("=" * 74)
    X1(); X2(); X3(); X4(); X5(); X6(); X7()
    log(f"\nBASELINE: {PASS} checks, {FAIL} failures")
    if FIRED:
        log("  failures: " + ", ".join(FIRED[:12]))
    X8()
    log(f"\nTOTAL after controls: {PASS} checks, {FAIL} failures")
    return 0 if FAIL == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
