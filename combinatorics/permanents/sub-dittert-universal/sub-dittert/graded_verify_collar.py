"""
VERIFIER FOR UNIFORM-COLLAR.md -- the collar assembly made uniform in k.
Displayed equals checked.

Every quantity the write-up displays is recomputed here over the rationals,
with no floating-point arithmetic in any decision.  Floats appear only in
report columns, never in a comparison.

WHAT IS CHECKED, section by section:
  Sec 1   Theorem X1, the general cross-term reduction, against brute force
          at d = 2..6 and every j, on collar points AND generic points
  Sec 2   Theorem X2, the survivor set: restricting to it changes nothing,
          the closed counts, and N(2) = 0 (the d = 2 cross part vanishes
          identically, which the paper records at k = 4 as an observation)
  Sec 3   the atom expansion and the annihilation principle: dropping every
          atom with an undecorated leaf changes NOTHING, and dropping one
          with a decorated leaf changes something
  Sec 4   the stored k = 4 instance: X_1, X_2, Y_1, Y_2, Y_3 of the paper,
          read out of graded_y_bounds, are the (3,j) and (4,j) cases
  Sec 5   the k = 5 instance, hand-written table against the theorem and
          against brute force
  Sec 6   Lemma CB, the atom cap |I| <= Q^{j/2} P^{l/2}, and the Theta cap
  Sec 7   the merge: the per-entry bound, the odd-power one-sided step at
          m = 3, 5, 7 on BOTH signs, the binomial expansion, the eta collapse
  Sec 8   the merge coefficient: the general formula, and that it is the
          paper's (3n-4)/3 at k = 4
  Sec 9   the end-to-end identity with every t_d in place, EXACTLY over QQ
          (the k = 4 verifier does this half in floats; here it is rational)
  Sec 10  the budget: Psi, and Ntilde(k)
  Sec 11  four mutation controls, each with a SEPARATING witness asserted in
          the same line

Instruments reused and not re-derived: pincer_line.py (t_coef, lam_line,
u_max), pincer_onesided.py (s_coef), graded_y_bounds.py (the paper's stored
k = 4 cross-term closed forms), graded_assembly_k4.py (split).

Usage:  GUARD_MEM=5G GUARD_CPUS=250% GUARD_THREADS=2 ../guard.sh \
            python3 -u graded_verify_collar.py
"""

import random
import sys
from fractions import Fraction as Fr
from math import comb, factorial

from collar_budget import (Ntilde, Psi, C_paper, ceil_sqrt, dbl_coef, eta,
                           merge_coefficient, V, W_coef)
from collar_core import (atom_eval, collar_sample, collar_saturated,
                         cross_brute, cross_general, elem, kappa, lmat,
                         layer_count, rand_split, sigma_of, split, survivors,
                         survivor_count, theta, theta_atoms, theta_atoms_raw,
                         u_max_k)
from collar_k5 import hand_kappa
from graded_y_bounds import generic_collar, invariants
from pincer_line import t_coef
from pincer_onesided import s_coef

OUT = []
FAIL = 0
MUT = {}
QUIET = False


def log(*a):
    if QUIET:
        return
    s = " ".join(str(x) for x in a)
    print(s)
    OUT.append(s)


def check(name, ok):
    global FAIL
    if not ok:
        FAIL += 1
        log(f"    *** FAIL: {name}")
    return ok


def pts(n, k, rng, want=2):
    """Collar points plus generic points.  The algebraic identities hold at
    every (x,y,z) of the right shape, and a test confined to the collar would
    not distinguish an identity from a small-parameter accident."""
    return collar_sample(n, k, rng, want=want) + [rand_split(n, rng)
                                                  for _ in range(want)]


def Qof(z, n):
    return sum(z[i][j] ** 2 for i in range(n) for j in range(n))


def Pof(x, y):
    return sum(t * t for t in x) + sum(t * t for t in y)


# ------------------------------------------------ Sec 1: the general theorem


def s1_theorem_x1(rng):
    log("SEC 1.  THEOREM X1, the general cross-term reduction.")
    log("    X_{d,j} = sum_{r,r'} kappa^{(d,j)}_{r,r'} Theta_j[r,r']")
    log("    must equal sum_{|S|=|T|=j} per(z[S|T]) sigma_{d-j}(L^(S,T)).")
    for (n, dmax) in ((5, 5), (6, 6), (7, 5)):
        ok = True
        for (x, y, z) in pts(n, min(dmax, n), rng):
            for d in range(2, dmax + 1):
                for j in range(1, d):
                    if cross_general(x, y, z, d, j, n) != \
                            cross_brute(x, y, z, d, j, n):
                        ok = False
        check(f"Sec1 Theorem X1 exact n={n} d<={dmax}", ok)
        log(f"    n={n}: exact at every (d,j) with 2 <= d <= {dmax}: {ok}")
    log("")


def s2_theorem_x2(rng):
    log("SEC 2.  THEOREM X2, the survivor set and its count.")
    for (n, dmax) in ((5, 5), (6, 6)):
        ok = True
        for (x, y, z) in pts(n, min(dmax, n), rng, want=1):
            for d in range(2, dmax + 1):
                for j in range(1, d):
                    a = cross_general(x, y, z, d, j, n, use_survivors=True)
                    b = cross_general(x, y, z, d, j, n, use_survivors=False)
                    if a != b:
                        ok = False
        check(f"Sec2 restricting to the survivors changes nothing n={n}", ok)
        log(f"    n={n}: survivor-restricted sum equals the full sum: {ok}")
    okc = all(len(survivors(j, m)) == survivor_count(j, m)
              for j in range(1, 8) for m in range(0, 7))
    check("Sec2 the closed survivor count matches the enumeration", okc)
    log(f"    |S(j,m)| closed form vs enumeration, j<=7, m<=6: {okc}")
    okn = all(layer_count(d) == (d ** 3 - 7 * d + 12) // 6 for d in range(3, 12))
    check("Sec2 N(d) = (d^3-7d+12)/6 for d >= 3", okn)
    log(f"    N(d) closed form, 3 <= d <= 11: {okn}"
        f"   values {[layer_count(d) for d in range(3, 9)]}")
    check("Sec2 N(2) = 0: the d = 2 cross part vanishes identically",
          layer_count(2) == 0 and layer_count(1) == 0)
    log(f"    N(1) = {layer_count(1)}, N(2) = {layer_count(2)}"
        "  -- the d = 2 cross part is EMPTY, not merely small")
    log("")


def s3_atoms(rng):
    log("SEC 3.  THE ATOM EXPANSION AND THE ANNIHILATION PRINCIPLE.")
    log("    Theta_j[r,r'] expands over pairs of set partitions.  A term dies")
    log("    exactly when some degree-1 vertex is undecorated, because a lone")
    log("    line sum of z appears.  Dropping those changes NOTHING.")
    n = 5
    okA, okR, okZ = True, True, True
    for (x, y, z) in pts(n, 4, rng, want=1):
        for j in range(1, 5):
            for tot in range(0, 4):
                for r in range(tot + 1):
                    rp = tot - r
                    tv = theta(x, y, z, j, r, rp, n)
                    at = theta_atoms(j, r, rp)
                    if MUT.get("overdrop") and at:
                        at = dict(list(at.items())[1:])
                    va = sum(c * atom_eval(k2[0], k2[1], k2[2], k2[3], k2[4],
                                           x, y, z, n) for k2, c in at.items())
                    if va != tv:
                        okA = False
                    if not MUT:
                        vr = sum(c * atom_eval(k2[0], k2[1], k2[2], k2[3],
                                               k2[4], x, y, z, n)
                                 for k2, c in
                                 theta_atoms_raw(j, r, rp).items())
                        if vr != tv:
                            okR = False
                        if j == 1 and (r == 0 or rp == 0) and tv != 0:
                            okZ = False
    if not MUT:
        check("Sec3 the atom expansion reproduces Theta", okA)
        check("Sec3 the leaf drop is exactly the vanishing set", okR)
        check("Sec3 Theta_1[r,0] = Theta_1[0,r'] = 0", okZ)
        log(f"    dropped expansion = Theta: {okA}"
            f"   undropped = Theta: {okR}   j=1 rule: {okZ}")
        log("")
    return okA


def s4_stored_k4(rng):
    log("SEC 4.  THE STORED k = 4 INSTANCE, from graded_y_bounds.")
    log("    The paper's X_1, X_2, Y_1, Y_2, Y_3 must BE the (3,j), (4,j)")
    log("    cases of Theorem X1 -- not merely agree numerically by design.")
    for n in (5, 6, 7):
        ok = True
        got = generic_collar(n, 4, want=2, rng=rng)
        for A in got:
            v = invariants(A, n)
            x, y, z = split(A, n)
            pairs = (("X1", 3, 1), ("X2", 3, 2), ("Y1", 4, 1), ("Y2", 4, 2),
                     ("Y3", 4, 3))
            for (nm, d, j) in pairs:
                if v[nm] != cross_general(x, y, z, d, j, n):
                    ok = False
        check(f"Sec4 all five stored cross terms reproduced n={n}", ok)
        check(f"Sec4 non-vacuous n={n} (needs collar witnesses)", len(got) > 0)
        log(f"    n={n}: X_1, X_2, Y_1, Y_2, Y_3 all exact: {ok}"
            f"   ({len(got)} stored-sampler points)")
    log("")


def s5_k5(rng):
    log("SEC 5.  THE k = 5 INSTANCE, hand table vs theorem vs brute force.")
    for n in (5, 6, 7):
        okk, okb = True, True
        for (x, y, z) in pts(n, 5, rng, want=1):
            hk = hand_kappa(n, x, y)
            for (j, (r, rp)), val in hk.items():
                if kappa(x, y, 5, j, r, rp, n) != val:
                    okk = False
            for j in range(1, 5):
                hand = sum(v * theta(x, y, z, j, r, rp, n)
                           for (jj, (r, rp)), v in hk.items() if jj == j)
                if hand != cross_brute(x, y, z, 5, j, n):
                    okb = False
        check(f"Sec5 seventeen hand coefficients = kappa n={n}", okk)
        check(f"Sec5 hand table = brute force n={n}", okb)
        log(f"    n={n}: coefficients {okk}   blocks against brute force {okb}")
    log("")


def s6_caps(rng):
    log("SEC 6.  LEMMA CB, the caps.  Compared as SQUARES, so exactly.")
    log("    per atom  I^2 <= Q^j P^l ;  per moment  Theta^2 <= W^2 Q^j P^l.")
    for (n, k) in ((5, 4), (6, 5), (7, 5)):
        okA, okT, tight = True, True, Fr(0)
        for (x, y, z) in collar_sample(n, k, rng, want=2):
            Q, P = Qof(z, n), Pof(x, y)
            for j in range(1, 5):
                for m in range(1, 4):
                    for (r, rp) in survivors(j, m):
                        tot = r + rp
                        tv = theta(x, y, z, j, r, rp, n)
                        if tv * tv > W_coef(j, r, rp) ** 2 * Q ** j * P ** tot:
                            okT = False
                        for k2, c in theta_atoms(j, r, rp).items():
                            I = atom_eval(k2[0], k2[1], k2[2], k2[3], k2[4],
                                          x, y, z, n)
                            bnd = Q ** j * P ** tot
                            if I * I > bnd:
                                okA = False
                            if bnd and I * I / bnd > tight:
                                tight = I * I / bnd
        check(f"Sec6 atom cap holds n={n} k={k}", okA)
        check(f"Sec6 moment cap holds n={n} k={k}", okT)
        log(f"    n={n} k={k}: atoms {okA}   moments {okT}"
            f"   worst atom slack^2 {float(tight):.4f}"
            "  (1 = attained, at the double edge)")
    log("")


def s7_merge(rng):
    log("SEC 7.  THE MERGE.  z_ij >= -(1/n + x_i + y_j) on the collar, so")
    log("    every ODD one-sided step degrades: p_m(z) >= -sum_ij d_ij^{m-2}")
    log("    z_ij^2 with d_ij = 1/n + x_i + y_j.  Both signs of p_m are tested;")
    log("    a lower bound tested only where the quantity is positive proves")
    log("    nothing.")
    for (n, k) in ((6, 4), (8, 5), (10, 5), (12, 6)):
        sample = collar_sample(n, k, rng, want=4) + [collar_saturated(n, k)]
        okE, okS, okB, okC = True, True, True, True
        neg = 0
        for (x, y, z) in sample:
            Q = Qof(z, n)
            if Q == 0:
                continue
            dl = [[Fr(1, n) + x[i] + y[j] for j in range(n)] for i in range(n)]
            for i in range(n):
                for j in range(n):
                    if z[i][j] < -dl[i][j]:
                        okE = False
            for m in (3, 5, 7):
                pm = sum(z[i][j] ** m for i in range(n) for j in range(n))
                rhs = sum(dl[i][j] ** (m - 2) * z[i][j] ** 2
                          for i in range(n) for j in range(n))
                if pm < -rhs:
                    okS = False
                if m == 3 and pm < 0:
                    neg += 1
                # the binomial expansion of the perturbation
                binom = sum(Fr(comb(m - 2, a)) * Fr(1, n) ** (m - 2 - a)
                            * sum((x[i] + y[j]) ** a * z[i][j] ** 2
                                  for i in range(n) for j in range(n))
                            for a in range(m - 1))
                if binom != rhs:
                    okB = False
                # the eta collapse
                if rhs > eta(n, k) ** (m - 2) * Q:
                    okC = False
        check(f"Sec7 per-entry bound n={n} k={k}", okE)
        check(f"Sec7 odd one-sided step m=3,5,7 n={n} k={k}", okS)
        check(f"Sec7 binomial expansion is an identity n={n} k={k}", okB)
        check(f"Sec7 eta collapse n={n} k={k}", okC)
        check(f"Sec7 NON-VACUOUS n={n} k={k} (needs a p_3 < 0 witness)",
              neg > 0)
        log(f"    n={n} k={k}: entry {okE}  step {okS}  binomial {okB}"
            f"  eta {okC}   points {len(sample)}   with p_3 < 0: {neg}")
    log("    Xi_a = sum_{u+v=a} C(a,u) D_{u,v} and D_{u,v} is the DOUBLE-EDGE")
    log("    atom, whose coefficient inside Theta_2[u,v] is (u+1)(v+1)/2:")
    okD = True
    n = 6
    for (x, y, z) in pts(n, 5, rng, want=1):
        for u in range(3):
            for v in range(3):
                D = sum(z[i][j] ** 2 * x[i] ** u * y[j] ** v
                        for i in range(n) for j in range(n))
                key = (1, 1, ((0, 0), (0, 0)), (u,), (v,))
                c = theta_atoms(2, u, v).get(key, Fr(0))
                if c != dbl_coef(u, v):
                    okD = False
                if u + v <= 1 and theta(x, y, z, 2, u, v, n) != \
                        (D if u + v == 1 else D / 2):
                    okD = False
    check("Sec7 the merge invariants ARE the double-edge cross atoms", okD)
    log(f"    dbl_coef = (u+1)(v+1)/2 and Theta_2[1,0] = D_{{1,0}}: {okD}")
    log("")


def s8_merge_coefficient():
    log("SEC 8.  THE MERGE COEFFICIENT, charged once at the SUMMED weight.")
    ok4 = True
    for n in (10, 12, 16, 20):
        want = t_coef(n, 4, 3) * Fr(3 * n - 4, 3)
        if merge_coefficient(n, 4, 1, 0) != want:
            ok4 = False
    check("Sec8 k=4 merge coefficient is t_3 (3n-4)/3", ok4)
    log(f"    k=4, (u,v)=(1,0), n = 10, 12, 16, 20:  t_3 (3n-4)/3  {ok4}")
    log("    the two sources and their sum, as multiples of t_3 at k = 4:")
    for n in (10, 20):
        cross = merge_coefficient(n, 4, 1, 0, drop_merge_side=True)
        full = merge_coefficient(n, 4, 1, 0)
        log(f"      n={n:3d}  cross side {cross / t_coef(n, 4, 3)}"
            f"   merge side {(full - cross) / t_coef(n, 4, 3)}"
            f"   sum {full / t_coef(n, 4, 3)}")
    log("    the merge INEQUALITY it certifies, at k = 4:")
    log("      (2/3) p_3(z) + (2-n) Xi  >=  -(2/3) Q/n - ((3n-4)/3) Xi")
    okI, sep = True, 0
    for n in (6, 8, 10, 12):
        for (x, y, z) in [collar_saturated(n, 4)]:
            Q = Qof(z, n)
            p3 = sum(z[i][j] ** 3 for i in range(n) for j in range(n))
            Xi = sum(x[i] * sum(z[i][j] ** 2 for j in range(n))
                     for i in range(n)) \
                + sum(y[j] * sum(z[i][j] ** 2 for i in range(n))
                      for j in range(n))
            co = Fr(n - 2) if MUT.get("bad_merge") else Fr(3 * n - 4, 3)
            lhs = Fr(2, 3) * p3 + Fr(2 - n) * Xi
            if lhs < -Fr(2, 3) * Q / n - co * Xi:
                okI = False
            if p3 < -Q / n:
                sep += 1
    if not MUT:
        check("Sec8 the merge inequality holds on the saturated witness", okI)
        check("Sec8 SEPARATING: the slice bound p_3 >= -Q/n FAILS there",
              sep == 4)
        log(f"    holds at n = 6, 8, 10, 12: {okI};"
            f"   slice bound already false at {sep}/4 of them")
        log("")
    return okI


# -------------------------------------------- Sec 9: the end-to-end identity


def F_direct(x, y, z, n, k):
    """F from the 1992 functional, exactly."""
    A = [[Fr(1, n) + x[i] + y[j] + z[i][j] for j in range(n)]
         for i in range(n)]
    R = [sum(A[i][j] for j in range(n)) for i in range(n)]
    C = [sum(A[i][j] for i in range(n)) for j in range(n)]
    N = Fr(comb(n, k))
    Phi = elem(R, k) / N + elem(C, k) / N - sigma_of(A, k) / (N * N)
    return (2 - Fr(factorial(k), n ** k)) - Phi


def F_split(x, y, z, n, k, drop_cross_t=None):
    """F rebuilt from Theorem C + the split + Theorem X1, exactly."""
    L = lmat(x, y, n)
    R = [n * t for t in x]
    C = [n * t for t in y]
    tot = Fr(0)
    for d in range(1, k + 1):
        td = t_coef(n, k, d)
        cr = sum(cross_general(x, y, z, d, j, n) for j in range(1, d))
        tc = Fr(1) if drop_cross_t == d else td
        tot += td * (sigma_of(L, d) + sigma_of(z, d)) + tc * cr
        tot -= s_coef(n, k, d) * (elem(R, d) + elem(C, d))
    return tot


def s9_identity(rng):
    log("SEC 9.  THE END-TO-END IDENTITY, EXACTLY over QQ.")
    log("    F from the 1992 functional = F_line + F_centred + sum_d t_d X_d,")
    log("    with every t_d in place and no floating point anywhere.")
    allok = True
    for (n, k) in ((5, 4), (6, 4), (6, 5), (7, 5)):
        ok, nonvac = True, False
        for (x, y, z) in pts(n, k, rng, want=1):
            a = F_direct(x, y, z, n, k)
            drop = MUT.get("drop_t")
            b = F_split(x, y, z, n, k, drop_cross_t=(k if drop else None))
            if a != b:
                ok = False
            if sum(cross_general(x, y, z, k, j, n) for j in range(1, k)) != 0 \
                    and t_coef(n, k, k) != 1:
                nonvac = True
        allok = allok and ok
        if not MUT:
            check(f"Sec9 identity exact n={n} k={k}", ok)
            check(f"Sec9 SEPARATING for a dropped t_{k} n={n} k={k}", nonvac)
            log(f"    n={n} k={k}: exact {ok}"
                f"   (X_{k} nonzero and t_{k} != 1: {nonvac})")
    if not MUT:
        log("")
    return allok


def s10_budget():
    log("SEC 10.  THE BUDGET.")
    log("    Psi(n,k) = (2/t_2)[ sum_m t_m C_m + G2 + g1^2/(2 lam_line) ] < 1.")
    log("    C_m is the SIBLING'S interface, carried as a symbol; the table")
    log("    below instantiates it and nothing in the collar depends on that.")
    log("    V_{j,m}, the aggregate cross cap, is free of both n and k:")
    log("        j\\m " + "".join(f"{m:>9d}" for m in range(1, 5)))
    for j in range(1, 5):
        log(f"        {j}   " + "".join(f"{str(V(j, m)):>9s}"
                                        for m in range(1, 5)))
    ok = True
    log("      k | Ntilde | Psi(Ntilde) | Psi(Ntilde-1) | collar-only")
    for k in (4, 5, 6, 8, 10, 12):
        N = Ntilde(k, C_paper)
        N0 = Ntilde(k, lambda m, n, kk: Fr(0))
        if N is None or not (Psi(N, k, C_paper) < 1):
            ok = False
            continue
        if N - 1 >= k + 1 and Psi(N - 1, k, C_paper) < 1:
            ok = False
        log(f"     {k:2d} | {N:6d} | {float(Psi(N, k, C_paper)):11.6f}"
            f" | {float(Psi(N - 1, k, C_paper)):13.4f} | {N0:6d}")
    check("Sec10 Ntilde is a genuine threshold at every k tested", ok)
    log(f"    each Ntilde has Psi < 1 at it and Psi >= 1 one below: {ok}")
    log("")


# --------------------------------------------------------- Sec 11: controls


def control(label, fault, target, runner, separating):
    global MUT, FAIL, QUIET
    log(f"    {label}")
    log(f"      separating witness : {separating}")
    MUT = dict(fault)
    before = FAIL
    QUIET = True
    try:
        ok = runner()
    finally:
        MUT = {}
        QUIET = False
    fired = not ok
    log(f"      must be caught by  : {target}")
    log(f"      rejected           : {fired}"
        f"   -> {'FIRES' if fired else 'DID NOT FIRE'}")
    FAIL = before
    check(f"control {label} fires", fired)


def s11_controls(rng):
    log("SEC 11.  MUTATION CONTROLS, each with a separating witness.")
    control("M1  a t_d factor dropped from a cross term",
            {"drop_t": True}, "the exact end-to-end identity (Sec 9)",
            lambda: s9_identity(rng),
            "points with X_k nonzero at n > k, where t_k != 1; at n = k the"
            " coefficient t_k IS 1 and the fault would be invisible")
    log("")
    control("M2  the merge coefficient (3n-4)/3 replaced by (n-2)",
            {"bad_merge": True}, "the merge inequality (Sec 8)",
            s8_merge_coefficient,
            "the saturated collar point A_11 = 0, where p_3(z) < -Q/n so the"
            " slice estimate the wrong coefficient silently assumes is false")
    log("")
    control("M3  one survivor dropped from S(j,m)",
            {}, "Theorem X1 against brute force",
            lambda: s3_dropped_survivor(rng),
            "generic points where the dropped Theta_j[r,r'] is nonzero")
    log("")
    control("M4  the annihilation applied to a DECORATED leaf",
            {"overdrop": True}, "the atom expansion (Sec 3)",
            lambda: s3_atoms(rng),
            "the drop removes a surviving atom, so the expansion no longer"
            " reproduces Theta")
    log("")


def s3_dropped_survivor(rng):
    """M3: keep every survivor but one, and see the reduction break."""
    ok = True
    for n in (5, 6):
        for (x, y, z) in pts(n, 5, rng, want=1):
            for d in (3, 4, 5):
                for j in range(1, d):
                    sv = survivors(j, d - j)
                    if len(sv) < 2:
                        continue
                    drop = sv[-1]
                    tot = sum(kappa(x, y, d, j, r, rp, n)
                              * theta(x, y, z, j, r, rp, n)
                              for (r, rp) in sv if (r, rp) != drop)
                    if tot != cross_brute(x, y, z, d, j, n):
                        ok = False
    return ok


def main():
    rng = random.Random(20260731)
    log("=" * 74)
    log("VERIFIER FOR UNIFORM-COLLAR.md")
    log("=" * 74)
    log("")
    s1_theorem_x1(rng)
    s2_theorem_x2(rng)
    s3_atoms(rng)
    s4_stored_k4(rng)
    s5_k5(rng)
    s6_caps(rng)
    s7_merge(rng)
    s8_merge_coefficient()
    s9_identity(rng)
    s10_budget()
    s11_controls(rng)
    log("=" * 74)
    log(f"TOTAL FAILURES: {FAIL}")
    log("VERDICT: " + ("ALL CHECKS PASS" if FAIL == 0 else "FAILURES PRESENT"))
    log("=" * 74)
    with open("results/graded_verify_collar.log", "w") as fh:
        fh.write("\n".join(OUT) + "\n")
    return 0 if FAIL == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
