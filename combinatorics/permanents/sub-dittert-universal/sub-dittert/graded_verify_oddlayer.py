#!/usr/bin/env python3
"""Graded verifier for ODDLAYER.md -- the odd-layer lemma.

Exact Fraction arithmetic throughout; no floating point in any decision
(floats appear only inside format strings).

Sections
  W1  the cumulant machinery: K_e from log(sum sigma_m x^m) equals the
      connected-(pi,rho) Moebius sum of UNIFORM-G sec 3
  W2  calibration: K_2 = Q, K_3 = 4p_3, K_4 = 36p_4 + 6Z - 18(Y_R+Y_C),
      K_5 = 576p_5 + 120Ga + 240Gb - 480Gc - 480Gc'
  W3  the connected coefficient mass Lam_e and the mass identity
      sum over set partitions of prod Lam = D_m^2
  W4  THE REFUTATION: the exact permutation-matrix law for K_5 and the
      divergence of -n K_5 / Q
  W5  every odd e in 3..9: |K_e|/Q tends to a nonzero limit, so no bound at
      rate Q/n exists at any j
  W6  what survives: K_3 >= -4Q/n one-sided, p_{2j+1} >= -Q/n^(2j-1),
      |K_e| <= Lam_e Q
  W7  the hybrid constant C_m^hyb and its validity
  W8  recomposition of Ntilde(k) through collar_budget.Psi
  W9  mutation controls

Run:  GUARD_MEM=4G GUARD_CPUS=200% ../guard.sh python3 -u graded_verify_oddlayer.py
"""
import sys, os
from fractions import Fraction as Fr
from math import factorial, comb
from itertools import combinations, permutations

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from collar_budget import Psi, Ntilde, Q_cap, eta, t_coef          # noqa: E402
import collar_budget                                               # noqa: E402

PASS = FAIL = 0
FIRED = []
MUT = {}


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


# ============================================================ combinatorics

def set_partitions(m):
    if m == 0:
        return [()]
    out = []
    for sm in set_partitions(m - 1):
        for i in range(len(sm)):
            out.append(sm[:i] + (sm[i] + (m - 1,),) + sm[i + 1:])
        out.append(sm + ((m - 1,),))
    return out


def mobius(pi):
    v = 1
    for b in pi:
        v *= (-1) ** (len(b) - 1) * factorial(len(b) - 1)
    return v


def derangements(m):
    d = [1, 0]
    for i in range(2, m + 1):
        d.append((i - 1) * (d[i - 1] + d[i - 2]))
    return d[m]


def block_of(pi, r):
    for i, b in enumerate(pi):
        if r in b:
            return i
    raise KeyError(r)


def connected(pi, rho, m):
    """G(pi,rho): row vertices = blocks of pi, column vertices = blocks of rho,
    one edge per r in [m].  Union-find; connected iff one component."""
    U, V = len(pi), len(rho)
    par = list(range(U + V))

    def find(a):
        while par[a] != a:
            par[a] = par[par[a]]
            a = par[a]
        return a

    for r in range(m):
        a, b = find(block_of(pi, r)), find(U + block_of(rho, r))
        if a != b:
            par[a] = b
    return len({find(i) for i in range(U + V)}) == 1


def orbit_S(pi, rho, B, n, m):
    """S(pi,rho) = sum over i: blocks(pi)->[n], j: blocks(rho)->[n] of the
    product over the m edges.  Column blocks factorise given i."""
    c = [[0] * len(rho) for _ in range(len(pi))]
    for r in range(m):
        c[block_of(pi, r)][block_of(rho, r)] += 1
    U, V = len(pi), len(rho)
    tot = Fr(0)
    idx = [0] * U
    while True:
        term = Fr(1)
        for v in range(V):
            s = Fr(0)
            for j in range(n):
                p = Fr(1)
                for u in range(U):
                    if c[u][v]:
                        p *= B[idx[u]][j] ** c[u][v]
                s += p
            term *= s
            if term == 0:
                break
        tot += term
        t = U - 1
        while t >= 0:
            idx[t] += 1
            if idx[t] < n:
                break
            idx[t] = 0
            t -= 1
        if t < 0:
            return tot


def K_connected(B, n, e):
    """K_e by its definition: sum over connected (pi,rho) in Pi_e^{>=2}^2."""
    parts = [p for p in set_partitions(e) if all(len(b) >= 2 for b in p)]
    tot = Fr(0)
    for pi in parts:
        mp = mobius(pi)
        for rho in parts:
            if connected(pi, rho, e):
                tot += mp * mobius(rho) * orbit_S(pi, rho, B, n, e)
    return tot


def Lam(e):
    """Connected l^1 Moebius mass at e:  sum |mu(pi) mu(rho)| over connected."""
    parts = [p for p in set_partitions(e) if all(len(b) >= 2 for b in p)]
    tot = 0
    for pi in parts:
        for rho in parts:
            if connected(pi, rho, e):
                tot += abs(mobius(pi) * mobius(rho))
    return tot


# ============================================ sigma_m and the cumulants K_e

def sigmas(B, n):
    """sigma_m(B), m = 0..n, by a subset DP over rows.  Exact."""
    f = [Fr(0)] * (1 << n)
    f[0] = Fr(1)
    for i in range(n):
        g = f[:]
        for mask in range(1 << n):
            v = f[mask]
            if v == 0:
                continue
            for j in range(n):
                if not (mask >> j & 1):
                    g[mask | (1 << j)] += v * B[i][j]
        f = g
    out = [Fr(0)] * (n + 1)
    for mask in range(1 << n):
        out[bin(mask).count("1")] += f[mask]
    return out


def cumulants(sig, upto):
    """K_e = e! [x^e] log(sum_m sigma_m x^m)."""
    f = [Fr(0)] * (upto + 1)
    for m in range(min(len(sig), upto + 1)):
        f[m] = sig[m]
    g = [Fr(0)] * (upto + 1)
    for e in range(1, upto + 1):
        acc = f[e]
        for i in range(1, e):
            acc -= Fr(i, e) * g[i] * f[e - i]
        g[e] = acc
    return [g[e] * factorial(e) for e in range(upto + 1)]


def sigma_bruteforce(B, n, m):
    tot = Fr(0)
    for S in combinations(range(n), m):
        for T in combinations(range(n), m):
            p = Fr(0)
            for perm in permutations(range(m)):
                q = Fr(1)
                for a in range(m):
                    q *= B[S[a]][T[perm[a]]]
                p += q
            tot += p
    return tot


# ------------------------------------------------- the permutation-matrix law

def sigmas_perm(n, upto):
    """sigma_m(P - J/n) exactly, every n, from
    per(P + sJ) = sum_f C(n,f) D_{n-f} (1+s)^f s^{n-f} with s = t - 1/n;
    only the top upto+1 coefficients in t are needed."""
    D = [1, 0]
    for i in range(2, n + 1):
        D.append((i - 1) * (D[i - 1] + D[i - 2]))
    a, b = Fr(n - 1, n), Fr(-1, n)
    top = [Fr(0)] * (upto + 1)
    for f in range(n + 1):
        w = comb(n, f) * D[n - f]
        if w == 0:
            continue
        for i in range(upto + 1):
            acc = Fr(0)
            for u in range(i + 1):
                v = i - u
                if u > f or v > n - f:
                    continue
                acc += comb(f, u) * a ** u * comb(n - f, v) * b ** v
            top[i] += w * acc
    return [top[m] / factorial(n - m) for m in range(upto + 1)]


def K5_perm_closed(n):
    """The closed form proved in ODDLAYER.md sec 3."""
    return -Fr((n - 1) * (n - 2) * (144 * n * n + 192 * n - 1152), n ** 3)


# ============================================================ test matrices

def perm_matrix(n, sh=1):
    return [[Fr(1) if (j - i) % n == sh % n else Fr(0) for j in range(n)]
            for i in range(n)]


def combo(n, ws):
    M = [[Fr(0)] * n for _ in range(n)]
    for sh, w in ws:
        P = perm_matrix(n, sh)
        for i in range(n):
            for j in range(n):
                M[i][j] += w * P[i][j]
    return M


def centre(A, n):
    return [[A[i][j] - Fr(1, n) for j in range(n)] for i in range(n)]


def frob2(B, n):
    return sum(B[i][j] ** 2 for i in range(n) for j in range(n))


def saturated(n):
    """A doubly stochastic point with A[0][0] = 0 -- the entry bound saturated,
    which is where the paper's one-sided steps are tight."""
    A = [[Fr(0)] * n for _ in range(n)]
    for i in range(n):
        for j in range(n):
            A[i][j] = Fr(1, n - 1) if (i == 0 or j == 0) and not (i == 0 and j == 0) \
                else (Fr(0) if (i == 0 and j == 0) else Fr(n - 2, (n - 1) ** 2))
    return A


def test_matrices(n):
    out = [("perm", perm_matrix(n)),
           ("(J-P)/(n-1)", [[Fr(0) if (j - i) % n == 1 else Fr(1, n - 1)
                             for j in range(n)] for i in range(n)]),
           ("half P + half P^2", combo(n, [(1, Fr(1, 2)), (2, Fr(1, 2))])),
           ("3-mix", combo(n, [(0, Fr(1, 2)), (1, Fr(1, 3)), (2, Fr(1, 6))])),
           ("saturated A00=0", saturated(n)),
           ("uniform shifts", combo(n, [(t, Fr(1, n)) for t in range(n)]))]
    return out


# ============================================== the paper's degree-5 invariants

def invariants(B, n):
    q = [sum(B[i][j] ** 2 for j in range(n)) for i in range(n)]
    qp = [sum(B[i][j] ** 2 for i in range(n)) for j in range(n)]
    f3 = [sum(B[i][j] ** 3 for j in range(n)) for i in range(n)]
    g3 = [sum(B[i][j] ** 3 for i in range(n)) for j in range(n)]
    p = {e: sum(B[i][j] ** e for i in range(n) for j in range(n)) for e in (2, 3, 4, 5)}
    BtB = [[sum(B[a][i] * B[a][j] for a in range(n)) for j in range(n)]
           for i in range(n)]
    Z = sum(BtB[i][j] ** 2 for i in range(n) for j in range(n))
    YR = sum(x * x for x in q)
    YC = sum(x * x for x in qp)
    Ga = sum(q[i] * B[i][j] * qp[j] for i in range(n) for j in range(n))
    BBtB = [[sum(B[i][a] * BtB[a][j] for a in range(n)) for j in range(n)]
            for i in range(n)]
    Gb = sum(B[i][j] ** 2 * BBtB[i][j] for i in range(n) for j in range(n))
    Gc = sum(q[i] * f3[i] for i in range(n))
    Gcp = sum(qp[j] * g3[j] for j in range(n))
    return dict(q=q, qp=qp, f3=f3, p=p, Z=Z, YR=YR, YC=YC, Ga=Ga, Gb=Gb,
                Gc=Gc, Gcp=Gcp)


# ============================================================ the constants

def base_mass(m):
    return Fr(derangements(m) ** 2, factorial(m))


def N3(m):
    """# partitions of [m] into one 3-block and (m-3)/2 2-blocks, m odd."""
    if m < 3 or m % 2 == 0:
        return 0
    r = m - 3
    dd = 1
    for i in range(r - 1, 0, -2):
        dd *= i
    return comb(m, 3) * dd


def matchings(m):
    if m % 2:
        return 0
    dd = 1
    for i in range(m - 1, 0, -2):
        dd *= i
    return dd


def Lam_star(m):
    """D_m^2 minus the two tiers handled separately.  Uses only the mass
    identity of W3, so it needs no enumeration."""
    v = derangements(m) ** 2
    v -= matchings(m)               # the all-pairing tier: prod Lam = 1
    v -= 4 * N3(m)                  # one 3-block + 2-blocks: prod Lam = Lam_3 = 4
    return v


def C_L0(m, n, k):
    """Present state (UNIVERSAL sec 2, C_m^oplus)."""
    Qc = Q_cap(n, k)
    e = m - 2
    if e % 2 == 0:
        return base_mass(m) * Qc ** (e // 2)
    return base_mass(m) * Qc ** (e // 2) * collar_budget.ceil_sqrt(Qc)


def C_L1(m, n, k):
    return base_mass(m) * Q_cap(n, k) ** ((m - 3) // 2)


def C_L2(m, n, k):
    return base_mass(m)


def C_zero(m, n, k):
    return Fr(0)


def C_hyb(m, n, k, slice_mode=False):
    """THE HYBRID.  Drop the non-negative all-pairing tier; charge the
    one-3-block tier through the PROVED one-sided K_3 >= -4 Q eta; charge
    everything else at the U5 cumulant rate |K_e| <= Lam_e Q.

        m! C_m^hyb = 4 N3(m) eta Qc^((m-3)/2)   [m odd]
                     + Lam*_m Qc^(floor(m/2)-2)

    On the slice eta = 1/n; on the collar eta = 1/n + sqrt(2 P_cap)."""
    Qc = Q_cap(n, k)
    et = Fr(1, n) if slice_mode else eta(n, k)
    if MUT.get("no_eta"):
        et = Fr(1, n)
    tot = Fr(0)
    if m % 2 == 1:
        ex = (m - 3) // 2
        tot += 4 * N3(m) * et * Qc ** ex
    ls = Lam_star(m)
    if MUT.get("drop_lamstar"):
        ls = 0
    if ls:
        ex = m // 2 - 2
        assert ex >= 0, m
        tot += ls * Qc ** ex
    return tot / factorial(m)


# ================================================================== W1

def W1():
    log("\nW1  the cumulant machinery == the connected-(pi,rho) definition")
    for n in (4, 5):
        for label, A in test_matrices(n)[:4]:
            B = centre(A, n)
            sig = sigmas(B, n)
            K = cumulants(sig, min(n, 6))
            for e in range(2, min(n, 6) + 1):
                Kc = K_connected(B, n, e)
                check(f"K_{e} log-series == connected sum   n={n} {label}",
                      K[e] == Kc, f"{float(K[e]):.6g}")
        # and sigma_m itself against brute force
        B = centre(test_matrices(n)[2][1], n)
        sig = sigmas(B, n)
        for m in range(2, min(n, 4) + 1):
            check(f"sigma_{m} DP == brute force   n={n}",
                  sig[m] == sigma_bruteforce(B, n, m))


# ================================================================== W2

def W2():
    log("\nW2  calibration of K_2..K_5 against the paper's invariants")
    for n in (5, 6, 7):
        for label, A in test_matrices(n):
            B = centre(A, n)
            Q = frob2(B, n)
            K = cumulants(sigmas(B, n), 5)
            I = invariants(B, n)
            check(f"K_2 = Q            n={n} {label}", K[2] == Q)
            check(f"K_3 = 4 p_3        n={n} {label}", K[3] == 4 * I["p"][3])
            check(f"K_4 = 36p4+6Z-18(YR+YC)  n={n} {label}",
                  K[4] == 36 * I["p"][4] + 6 * I["Z"] - 18 * (I["YR"] + I["YC"]))
            check(f"K_5 = 576p5+120Ga+240Gb-480(Gc+Gc')  n={n} {label}",
                  K[5] == 576 * I["p"][5] + 120 * I["Ga"] + 240 * I["Gb"]
                  - 480 * (I["Gc"] + I["Gcp"]))


# ================================================================== W3

def W3():
    log("\nW3  the connected coefficient mass and the mass identity")
    lam = {e: Lam(e) for e in range(2, 7)}
    for e, want in ((2, 1), (3, 4), (4, 78), (5, 1896)):
        check(f"Lam_{e} = {want}", lam[e] == want, f"got {lam[e]}")
    check("Lam_5 = l^1 mass of K_5's coefficients (576+120+240+480+480)",
          lam[5] == 576 + 120 + 240 + 480 + 480)
    check("Lam_4 = l^1 mass of K_4's coefficients (36+6+18+18)",
          lam[4] == 36 + 6 + 18 + 18)
    # exponential formula for the masses: sum over set partitions of prod Lam
    for m in range(2, 7):
        tot = 0
        for pi in set_partitions(m):
            if any(len(b) < 2 for b in pi):
                continue
            p = 1
            for b in pi:
                p *= lam[len(b)]
            tot += p
        check(f"sum_lambda prod Lam = D_{m}^2", tot == derangements(m) ** 2,
              f"{tot} vs {derangements(m) ** 2}")
    # the Lam_star bookkeeping used by C_hyb
    for m in range(3, 7):
        tot = 0
        for pi in set_partitions(m):
            if any(len(b) < 2 for b in pi):
                continue
            sizes = sorted(len(b) for b in pi)
            if all(s == 2 for s in sizes):
                continue
            if sizes.count(3) == 1 and sizes.count(2) == len(sizes) - 1:
                continue
            p = 1
            for s in sizes:
                p *= lam[s]
            tot += p
        check(f"Lam*_{m} closed form", tot == Lam_star(m),
              f"{tot} vs {Lam_star(m)}")
    check("Lam*_3 = 0 (the m = 3 layer is ENTIRELY the K_3 tier)",
          Lam_star(3) == 0)


# ================================================================== W4

def W4():
    log("\nW4  THE REFUTATION -- the exact permutation-matrix law for K_5")
    ns = [5, 6, 7, 8, 9, 10, 12, 16, 24, 40, 80, 200]
    for n in ns:
        K = cumulants(sigmas_perm(n, 5), 5)
        check(f"K_5(P - J/n) closed form   n={n}", K[5] == K5_perm_closed(n),
              f"{float(K[5]):.6g}")
    log("     the ratio the lemma bounds, -n K_5 / Q, at B = P - J/n:")
    prev = None
    for n in ns:
        K5 = K5_perm_closed(n)
        Q = Fr(n - 1)
        r = -K5 * n / Q
        log(f"       n={n:4d}   -n K_5/Q = {float(r):14.4f}    "
            f"(-K_5/Q = {float(-K5 / Q):10.4f})")
        # the lemma would need r <= c_2, a constant.  It grows without bound:
        check(f"-n K_5/Q >= 100(n-2)   n={n}", r >= 100 * (n - 2))
        if prev is not None:
            check(f"-n K_5/Q strictly increasing at n={n}", r > prev)
        prev = r
    check("(OL) at j=2 is FALSE: no n-free c_2 has K_5 >= -c_2 Q/n",
          all(-K5_perm_closed(n) * n / Fr(n - 1) >= 100 * (n - 2) for n in ns))
    check("the failure is exactly one power of n: -K_5/Q < 144 for every n",
          all(-K5_perm_closed(n) / Fr(n - 1) < 144 for n in ns))


# ================================================================== W5

def W5():
    log("\nW5  every odd e: |K_e|/Q tends to a nonzero limit")
    E = 9
    ns = [10, 12, 16, 24, 40, 80, 200, 1000]
    log("     K_e / Q at B = P - J/n:")
    rows = {}
    for n in ns:
        K = cumulants(sigmas_perm(n, E), E)
        Q = Fr(n - 1)
        rows[n] = [K[e] / Q for e in range(2, E + 1)]
        log(f"       n={n:5d}  " + "".join(f"{float(v):14.4f}" for v in rows[n]))
    # for each odd e >= 3 the ratio is bounded away from 0, uniformly in n,
    # so K_e >= -c Q/n is impossible for any n-free c.
    floors = {3: Fr(3), 5: Fr(-145), 7: Fr(-16000), 9: Fr(10 ** 6)}
    for e in (3, 5, 7, 9):
        vals = [rows[n][e - 2] for n in ns if n >= 24]
        if e in (3, 9):
            ok = all(v >= floors[e] for v in vals)
            det = f"K_{e}/Q >= {floors[e]} at every n >= 24"
        else:
            ok = all(v <= floors[e] / 10 for v in vals)
            det = f"K_{e}/Q <= {float(floors[e] / 10):.1f} at every n >= 24"
        check(f"|K_{e}|/Q bounded away from 0", ok, det)
        check(f"(OL) at j={(e - 1) // 2} FAILS: n|K_{e}|/Q unbounded",
              all(abs(rows[n][e - 2]) * n >= n for n in ns if n >= 24))
    check("j=1 two-sided form already false: K_3/Q -> 4, not 4/n",
          rows[1000][1] >= Fr(39, 10))


# ================================================================== W6

def W6():
    log("\nW6  what survives: the one-sided K_3, the power sums, the Q rate")
    for n in (5, 6, 7, 8):
        for label, A in test_matrices(n):
            B = centre(A, n)
            Q = frob2(B, n)
            if Q == 0:
                continue
            K = cumulants(sigmas(B, n), min(n, 7))
            I = invariants(B, n)
            check(f"K_3 >= -4Q/n   n={n} {label}", K[3] >= -4 * Q / n)
            check(f"p_3 >= -Q/n    n={n} {label}", I["p"][3] >= -Q / n)
            check(f"p_5 >= -Q/n^3  n={n} {label}", I["p"][5] >= -Q / n ** 3)
            check(f"|K_3| <= 4 beta Q  n={n} {label}",
                  abs(K[3]) <= 4 * Fr(n - 1, n) * Q)
            for e in range(4, min(n, 6) + 1):
                check(f"|K_{e}| <= Lam_{e} Q   n={n} {label}",
                      abs(K[e]) <= Lam(e) * Q, f"{float(abs(K[e]) / Q):.4g}")
    log("     the two extremal families, and the two different rates:")
    for n in (5, 6, 7, 8, 9, 12, 20):
        # (J - P)/(n-1): the extremiser of sigma_3/Q, where the rate IS Q/n
        A = [[Fr(0) if (j - i) % n == 1 else Fr(1, n - 1) for j in range(n)]
             for i in range(n)]
        B = centre(A, n)
        Q = frob2(B, n)
        I = invariants(B, n)
        check(f"(J-P)/(n-1): p_3/Q = -(n-2)/(n(n-1)) exactly   n={n}",
              I["p"][3] / Q == -Fr(n - 2, n * (n - 1)))
        check(f"(J-P)/(n-1): the paper's p_3 >= -Q/n is sharp to (n-2)/(n-1)  n={n}",
              I["p"][3] / Q * Fr(-n) == Fr(n - 2, n - 1))
        # P itself: the extremiser that KILLS the lemma at e = 5
        Bp = centre(perm_matrix(n), n)
        Qp = frob2(Bp, n)
        Kp = cumulants(sigmas_perm(n, 5), 5)
        check(f"P: K_3/Q = 4(n-2)/n  (rate Q, one-sided rate Q/n unused)  n={n}",
              Kp[3] / Qp == Fr(4 * (n - 2), n))
        check(f"P: K_4/Q = (6n^2-72n+108)/n^2   n={n}",
              Kp[4] / Qp == Fr(6 * n * n - 72 * n + 108, n * n))
    # the carrier of the failure: Gamma_c saturates its UPPER bound
    log("     the carrier at j=2: Gamma_c against its upper bound beta M Q")
    for n in (8, 12, 20):
        B = centre(perm_matrix(n), n)
        I = invariants(B, n)
        Q = frob2(B, n)
        M = max(max(I["q"]), max(I["qp"]))
        beta = Fr(n - 1, n)
        check(f"Gamma_c <= beta M Q   n={n}", I["Gc"] <= beta * M * Q,
              f"ratio {float(I['Gc'] / (beta * M * Q)):.6f}")
        check(f"Gamma_c = (n-1)^2(n-2)/n^2 exactly   n={n}",
              I["Gc"] == Fr((n - 1) ** 2 * (n - 2), n ** 2))
        check(f"Gamma_c / (beta M Q) = (n-2)/(n-1) -> 1  (ATTAINED)  n={n}",
              I["Gc"] / (beta * M * Q) == Fr(n - 2, n - 1))
        check(f"Gamma_c >= -Y_R/n  (the CHEAP side, unused by K_5)  n={n}",
              I["Gc"] >= -I["YR"] / n)


# ================================================================== W7

def W7():
    log("\nW7  the hybrid constant C_m^hyb and its validity")
    check("C_3^hyb on the slice = 2/(3n)  (the paper's constant, reproduced)",
          all(C_hyb(3, n, 4, slice_mode=True) == Fr(2, 3 * n) for n in (6, 9, 12)))
    check("C_4^hyb = 78/24 (all-pairing tier dropped: 81 -> 78)",
          C_hyb(4, 9, 5, slice_mode=True) == Fr(78, 24))
    check("C_5^hyb is FREE of n up to the eta term",
          C_hyb(5, 40, 6, slice_mode=True) * 120 - 40 * Q_cap(40, 6) / 40 == 1896)
    for n in (5, 6, 7, 8):
        for label, A in test_matrices(n):
            B = centre(A, n)
            Q = frob2(B, n)
            if Q == 0:
                continue
            sig = sigmas(B, n)
            for m in range(3, min(n, 7) + 1):
                k = max(m, 4)
                check(f"sigma_{m} >= -C^hyb Q   n={n} {label}",
                      sig[m] >= -C_hyb(m, n, k, slice_mode=True) * Q)
    log("     C_m^hyb vs the ladder rows at (n,k) = (300, 8):")
    n, k = 300, 8
    for m in range(3, k + 1):
        log(f"       m={m}  L0={float(C_L0(m, n, k)):12.4g}"
            f"  L1={float(C_L1(m, n, k)):12.4g}"
            f"  hyb={float(C_hyb(m, n, k)):12.4g}"
            f"  L2={float(C_L2(m, n, k)):12.4g}")
    for m in (5, 7):
        check(f"C_{m}^hyb < C_{m}^L1 at (300,8)", C_hyb(m, n, k) < C_L1(m, n, k))
    check("C_3,C_5^hyb are BELOW the assumed L2 shape (pairing tier dropped)",
          C_hyb(3, n, k) < C_L2(3, n, k) and C_hyb(5, n, k) < C_L2(5, n, k))
    check("C_6,C_8^hyb exceed L2 (the even layers keep their n-powers)",
          C_hyb(6, n, k) > C_L2(6, n, k) and C_hyb(8, n, k) > C_L2(8, n, k))
    # eta-sensitive: the collar degradation must be present and must be charged
    for (nn, kk, mm) in ((300, 8, 3), (300, 8, 5), (120, 6, 3), (120, 6, 5)):
        Qc = Q_cap(nn, kk)
        ex = (mm - 3) // 2
        gap = 4 * N3(mm) * (eta(nn, kk) - Fr(1, nn)) * Qc ** ex / factorial(mm)
        check(f"C_{mm}^hyb(collar) = C^hyb(slice) + eta-gap   n={nn} k={kk}",
              C_hyb(mm, nn, kk) == C_hyb(mm, nn, kk, slice_mode=True) + gap)
        check(f"C_{mm}^hyb(collar) > C^hyb(slice)   n={nn} k={kk}",
              C_hyb(mm, nn, kk) > C_hyb(mm, nn, kk, slice_mode=True))
    check("C^hyb dominates its own non-K_3 tier at (300,8)",
          all(C_hyb(m, 300, 8) >= Fr(Lam_star(m), factorial(m)) * Q_cap(300, 8) ** (m // 2 - 2)
              for m in range(4, 9)))


# ================================================================== W8

def W8(ks=None):
    log("\nW8  recomposition: Ntilde(k) through collar_budget.Psi")
    ks = ks or [6, 7, 8, 9, 10, 11, 12]
    log("       k     L0      L1     hyb      L2   floor")
    out = {}
    for k in ks:
        row = []
        for C in (C_L0, C_L1, C_hyb, C_L2, C_zero):
            row.append(Ntilde(k, C, hi=6000))
        out[k] = row
        log(f"     {k:3d}  " + "".join(f"{('-' if v is None else v):>7}" for v in row))
    for k in ks:
        L0, L1, hy, L2, fl = out[k]
        check(f"Ntilde ordering L0 >= L1 >= hyb >= L2 >= floor   k={k}",
              L0 >= L1 >= hy >= L2 >= fl, f"{out[k]}")
        check(f"hyb strictly beats L1   k={k}", hy < L1)
    return out


# ================================================================== W9

def W9():
    log("\nW9  mutation controls")
    global MUT, PASS, FAIL, FIRED
    faults = [
        ("no_eta", "the collar degradation 1/n -> eta ignored in C^hyb"),
        ("drop_lamstar", "the non-K_3 tier dropped from C^hyb"),
        ("bad_K5_law", "the permutation-matrix K_5 law off by one coefficient"),
        ("lam_mass", "the connected mass Lam_5 replaced by D_5^2"),
    ]
    base = (PASS, FAIL, list(FIRED))
    for key, what in faults:
        MUT = {key: True}
        PASS, FAIL, FIRED = 0, 0, []
        if key == "bad_K5_law":
            global K5_perm_closed
            good = K5_perm_closed
            K5_perm_closed = lambda n: -Fr((n - 1) * (n - 2) * (144 * n * n + 192 * n - 1151), n ** 3)  # noqa: E731
            W4()
            K5_perm_closed = good
        elif key == "lam_mass":
            global Lam
            good = Lam
            Lam = lambda e: derangements(e) ** 2  # noqa: E731
            W3()
            W6()
            Lam = good
        else:
            W7()
            W8(ks=[6, 8])
        log(f"     fault '{key}' ({what}): {FAIL} checks caught it")
        check_fired = FAIL
        MUT = {}
        PASS, FAIL, FIRED = 0, 0, []
        if check_fired < 2:
            log(f"     *** CONTROL WEAK: '{key}' fired at {check_fired} positions")
    MUT = {}
    PASS, FAIL, FIRED = base[0], base[1], base[2]


# ==================================================================== main

def main():
    log("=" * 74)
    log("graded_verify_oddlayer.py -- the odd-layer lemma, ODDLAYER.md")
    log("=" * 74)
    W1(); W2(); W3(); W4(); W5(); W6(); W7(); W8()
    log(f"\nBASELINE: {PASS} checks, {FAIL} failures")
    if FIRED:
        log("  failures: " + ", ".join(FIRED[:12]))
    W9()
    log(f"\nTOTAL after controls: {PASS} checks, {FAIL} failures")
    return 0 if FAIL == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
