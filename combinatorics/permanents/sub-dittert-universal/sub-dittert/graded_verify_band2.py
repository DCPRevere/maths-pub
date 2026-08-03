#!/usr/bin/env python3
"""
GRADED VERIFIER for the band-2 identity half and the correction it carries
(POSITIVITY.md section 9, NOTES section 38).

Exact rational arithmetic in every decision.  The verifier must REJECT: four
mutations are injected and every one must be caught, and the clean run must be
silent.

WHAT IS CHECKED

 [1] THE CORRECTION.  The primal block algebra at deg_basis = 2 is already
     closed form in n.  The four derivation modules re-verify their own closed
     forms against the concrete realisation at n = 5 and n = 6:
     k4_ind16_closed (16x16 Ind(V'|1)), k4_vv14_closed (14x14 (V'|V') and the
     10x10 / 4x4 split), k4_sigma0_closed (sigma_0's ten blocks),
     k4_tail_closed (the last six).  PARAMETRIC section 10 item 2 says these
     closed forms are what Branch S is waiting for; they exist.
 [2] The band-2 rhs law as an IDENTITY IN Q(n), at k = 1..5.
 [3] Cross-validation of the closed-form rhs against the TRUSTED path
     (sos.build_sdp -> exactsd.exact_system) at k = 4 AND k = 5, which is new:
     k4_system.check_against_trusted runs at K = 4 only.  Lemma 1 is re-measured
     in band 2 at the same time (the four matrices must be entrywise equal
     across k).
 [4] The design sizes, band 1 against band 2, with band 1 as the CONTROL: the
     instrument must return 4 there, which is the dimension law B1 designs in.

Run:  ./guard.sh python3 graded_verify_band2.py
"""

import os
import sys
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "dittert"))
sys.path.insert(0, HERE)

import allk_gen2 as gen2                                          # noqa: E402
import band1_certificate as b1                                    # noqa: E402
import band2_family as bf                                         # noqa: E402
import band2_identity as b2                                       # noqa: E402
import general_k3 as g                                            # noqa: E402
import k4_system as k4                                            # noqa: E402
from general_k3 import RF                                         # noqa: E402

RESULTS = os.path.join(HERE, "results")
XVAL_N = 5                       # the n at which the trusted path is affordable
ZERO = RF([])


def check_block_algebra(log):
    import k4_ind16_closed as c16
    import k4_sigma0_closed as cs0
    import k4_tail_closed as ctl
    import k4_vv14_closed as cvv
    ok = True
    for name, mod in (("Ind(V'|1) 16x16", c16), ("(V'|V') 14x14", cvv),
                      ("sigma_0 ten blocks", cs0), ("tail six blocks", ctl)):
        res = mod.verify((5, 6))
        good = res[0] if isinstance(res, tuple) else res
        ok = ok and bool(good)
        log(f"  {name:<24s} closed form in n verified at n = 5, 6: {bool(good)}")
    return ok


def check_rhs_law(log, rows, cvec, evec, tamper=None):
    bad = 0
    for k in (1, 2, 3, 4, 5):
        want = b2.rhs_rf(rows, k)
        cv, ev = cvec, evec
        if tamper is not None:
            d, i, delta = tamper
            cv = {dd: list(v) for dd, v in cvec.items()}
            cv[d][i] = cv[d][i] + delta
        have = b2.theorem2_rf(rows, cv, ev, k, b2.TOPDEG)
        b = sum(1 for i in range(len(rows)) if want[i] != have[i])
        bad += b
        log(f"  k = {k}: {b} mismatches over {len(rows)} rows of Q(n)")
    return bad == 0


def check_trusted(log, sym, n=XVAL_N, tamper=None):
    """Closed-form rhs vs the trusted monomial-table path, at k = 4 and k = 5,
    plus Lemma 1 in band 2."""
    from exactsd import exact_system
    from sos import build_sdp
    rows = sym["rows"]
    systems = {}
    for k in (4, 5):
        d = build_sdp(n, k, 2, verbose=False)
        systems[k] = (d, exact_system(d))
    d4, s4 = systems[4]
    d5, s5 = systems[5]
    ment, mbad = 0, 0
    for i in range(4):
        for r0, r1 in zip(s4[i], s5[i]):
            for a, b in zip(r0, r1):
                ment += 1
                if a != b:
                    mbad += 1
    log(f"  Lemma 1 in band 2 at n = {n}: {ment} matrix entries compared, "
        f"{mbad} mismatches (k = 4 vs k = 5)")

    inv_row = {}
    for mono, r in d4["orbit_of"].items():
        inv_row.setdefault(r, mono)
    rmap = {r: k4.canon(g.cells_of(m, n)) for r, m in inv_row.items()}
    rbad = 0
    for k, (d, s) in systems.items():
        rhs_tr = s[4]
        closed = b2.rhs_rf(rows, k)
        for r, key in rmap.items():
            want = closed[sym["row_index"][key]].at(F(n))
            if tamper is not None and r == tamper[0] and k == tamper[1]:
                want += tamper[2]
            if rhs_tr[r] != want:
                rbad += 1
        log(f"  closed-form rhs vs trusted rhs at (n,k) = ({n},{k}): "
            f"{rbad} cumulative mismatches over {len(rmap)} rows")
    return mbad == 0 and rbad == 0


def check_design(log, tamper=None):
    sym = k4.build(verbose=False)
    M2 = gen2.build_matrix(sym)
    ng, ns, nl = len(sym["gvars"]), len(sym["svars"]), len(sym["lvars"])
    if tamper is not None:
        M2 = [row[:] for row in M2]
        M2[tamper[0]][tamper[1]] = M2[tamper[0]][tamper[1]] + RF([F(1)])
    s2 = b2.design_sizes(M2, ng, ns, nl, "band 2")
    bd1 = b1.Band()
    s1 = b2.design_sizes(bd1.M, len(bd1.sym["gvars"]), len(bd1.sym["svars"]),
                         len(bd1.sym["lvars"]), "band 1")
    ess1 = s1["free"] - 4 - s1["ker_lambda"]
    ess2 = s2["free"] - 18 - s2["ker_lambda"]
    log(f"  band 1: rank {s1['rank']}, free {s1['free']}, "
        f"d(sigma_0) {s1['d_sigma_0']}, d(sigma_11) {s1['d_sigma_11']}, "
        f"design positivity sees {ess1}")
    log(f"  band 2: rank {s2['rank']}, free {s2['free']}, "
        f"d(sigma_0) {s2['d_sigma_0']}, d(sigma_11) {s2['d_sigma_11']}, "
        f"design positivity sees {ess2}")
    expected = (s1["rank"] == 11 and s1["free"] == 8 and ess1 == 4
                and s1["d_sigma_0"] == 0 and s1["d_sigma_11"] == 4
                and s2["rank"] == 86 and s2["free"] == 354 and ess2 == 336
                and s2["d_sigma_0"] == 0 and s2["d_sigma_11"] == 33)
    log(f"  band-1 CONTROL returns 4, the dimension law B1 designs in: "
        f"{ess1 == 4}")
    return expected



def check_gate_and_families(log, tamper=None):
    """The C2 calibration gate, design D1, the degree-filtration facts, and the
    scalar refinement D1s that fails."""
    sym2 = k4.build(verbose=False)
    rows2 = sym2["rows"]
    M2 = gen2.build_matrix(sym2)
    if tamper is not None:
        M2 = [row[:] for row in M2]
        M2[tamper[0]][tamper[1]] = M2[tamper[0]][tamper[1]] + RF([F(1)])
    bd1 = b1.Band()
    sym1 = bd1.sym
    ok = True

    for k in (2, 3):
        fs, _, _ = bd1.build(k)
        x = bf.lift(sym1, sym2, bd1.vals19(("k", k), fs))
        bad = bf.residual(M2, x, b2.rhs_rf(rows2, k))
        ok = ok and bad == 0
        log(f"  GATE k = {k}: C2 lift of law B1 violates {bad} of "
            f"{len(rows2)} band-2 rows over Q(n)")

    tc = bf.type_columns(sym2)
    ng, ns, nl = (len(sym2["gvars"]), len(sym2["svars"]), len(sym2["lvars"]))
    off = set(tc.get(("g", (1, 2)), []) + tc.get(("s", (1, 2)), []))
    keep = [c for c in range(ng + ns + nl) if c not in off]
    for k in (2, 3, 4, 5):
        rk, ninc, _ = bf.rank_and_consistency(M2, keep, b2.rhs_rf(rows2, k))
        ok = ok and ninc == 0 and rk == 86
        log(f"  D1 k = {k}: rank {rk}, inconsistent rows {ninc}")

    degs = bf.row_degrees(sym2)
    hi = [i for i, d in enumerate(degs) if d >= 4]
    low, high, lam = bf.feeding_columns(sym2)
    r_low = bf.submatrix_rank(M2, hi, low)
    r_all = bf.submatrix_rank(M2, hi, low + high + lam)
    r_lam = bf.submatrix_rank(M2, hi, lam)
    ok = ok and (len(hi) == 75 and r_low == 0 and r_all == 75 and r_lam == 28)
    log(f"  FILTRATION: {len(hi)} rows of degree >= 4; the {len(low)} band-1 "
        f"(1,1) classes have rank {r_low} there (must be 0)")
    log(f"  FILTRATION: rank on all columns {r_all}, on lambda alone {r_lam}"
        f"  -> generic-target need {r_all - r_lam}")

    lamvecs = [[M2[i][c] for i in hi] for c in lam]
    rhsvecs = [[b2.rhs_rf(rows2, k)[i] for i in hi] for k in (2, 3, 4, 5)]
    rl = bf.submatrix_rank([list(v) for v in lamvecs], list(range(len(lamvecs))),
                           list(range(len(hi))))
    rall = bf.submatrix_rank([list(v) for v in lamvecs + rhsvecs],
                             list(range(len(lamvecs) + len(rhsvecs))),
                             list(range(len(hi))))
    sharp = rall - rl
    ok = ok and rl == 28 and sharp == 2
    log(f"  SHARP: the four band right-hand sides span {sharp} dimensions of "
        f"the degree->=4 row space modulo lambda")

    gd, sd = bf.diagonal_classes(sym2)
    groups = [[c] for c in low] + [gd, sd] + [[c] for c in lam]
    viol = {}
    for k in (4, 5):
        _, inc = bf.combined_consistency(M2, groups, b2.rhs_rf(rows2, k))
        viol[k] = inc
    ok = ok and viol[4] == 5 and viol[5] == 12
    log(f"  D1s (2 Gram parameters, the scalar direction): INCONSISTENT, "
        f"{viol[4]} rows at k = 4 and {viol[5]} at k = 5")
    return ok



def check_pin(log):
    """The 2-dimensional quotient is about TARGETS: what it pins has an
    identically zero diagonal, so it carries no positivity information."""
    import subprocess
    out = subprocess.run([sys.executable, os.path.join(HERE, "band2_pin.py")],
                         capture_output=True, text=True, cwd=HERE).stdout
    ok = ("dim of the quotient spanned by the four rhs mod lambda: 2" in out
          and "rhs_H(2) in span(lambda, rhs_H(4), rhs_H(5)): True" in out
          and "rhs_H(3) in span(lambda, rhs_H(4), rhs_H(5)): True" in out
          and out.count("325 zero, 0 negative") == 8
          and "nonzero free coords 5 of 339" in out
          and "nonzero free coords 12 of 339" in out)
    for line in out.splitlines():
        if "quotient" in line or "in span" in line or "(2,2) block" in line:
            log("  " + line.strip())
    return ok



def check_d2(log):
    """Design D2: the scaled-identity family reduces band 2 to one PD test,
    and that test FAILS for the canonical completion."""
    import subprocess
    out = subprocess.run([sys.executable, os.path.join(HERE, "band2_d2.py"), "5"],
                         capture_output=True, text=True, cwd=HERE).stdout
    ok = ("h: rank 75, inconsistent 0, nonzero coords 19" in out
          and out.count("NOT PD") == 2
          and "first bad pivot 1" in out and "first bad pivot 34" in out
          and "max |off-diagonal| 3" in out
          and "max |off-diagonal| 0.5" in out)
    for line in out.splitlines():
        if "h:" in line or "M = I - Gram(h)" in line:
            log("  " + line.strip())
    return ok


def main():
    lines = []

    def log(s):
        print(s, flush=True)
        lines.append(s)

    log("=" * 72)
    log("GRADED VERIFIER -- band 2 identity half, and the block-algebra")
    log("correction to PARAMETRIC.md section 10 item 2")
    log("=" * 72)

    sym = k4.build(verbose=False)
    rows = sym["rows"]
    cvec, evec = b2.ce_vectors(rows, b2.TOPDEG)

    results = []

    log("\n[1] the primal block algebra at deg_basis = 2 is CLOSED FORM in n")
    results.append(("[1] block algebra closed form and validated",
                    check_block_algebra(log)))

    log("\n[2] the band-2 rhs law as an identity in Q(n)")
    results.append(("[2] rhs law over Q(n), k = 1..5",
                    check_rhs_law(log, rows, cvec, evec)))

    log("\n[3] closed-form rhs vs the trusted path, at k = 4 AND k = 5")
    results.append(("[3] cross-validated against build_sdp",
                    check_trusted(log, sym)))

    log("\n[4] the design sizes, with band 1 as the control")
    results.append(("[4] design sizes 4 and 336", check_design(log)))

    log("\n[5] the C2 calibration gate, design D1, the filtration, and D1s")
    results.append(("[5] gate, D1, filtration bound, D1s failure",
                    check_gate_and_families(log)))

    log("\n[6] what the 2-dimensional quotient pins: an all-zero diagonal")
    results.append(("[6] the quotient carries no positivity information",
                    check_pin(log)))

    log("\n[7] design D2, the scaled-identity family: one PD test, and it fails")
    results.append(("[7] D2 reduced to I - Gram(h), which is NOT PD",
                    check_d2(log)))

    log("\n" + "=" * 72)
    log("MUTATION CONTROLS -- every one MUST be caught")
    log("=" * 72)
    muts = []

    log("\n(M1) add 1/10^7 to one entry of c^[5]")
    i5 = next(i for i, v in enumerate(cvec[5]) if v)
    caught = not check_rhs_law(lambda s: None, rows, cvec, evec,
                               tamper=(5, i5, RF([F(1, 10 ** 7)])))
    log(f"  rhs law rejected: {caught}")
    muts.append(("M1 c^[5] entry perturbed", caught))

    log("\n(M2) add 1/10^9 to one entry of c^[2]")
    i2 = next(i for i, v in enumerate(cvec[2]) if v)
    caught = not check_rhs_law(lambda s: None, rows, cvec, evec,
                               tamper=(2, i2, RF([F(1, 10 ** 9)])))
    log(f"  rhs law rejected: {caught}")
    muts.append(("M2 c^[2] entry perturbed", caught))

    log("\n(M3) shift one trusted-path rhs comparison by 1/10^6")
    caught = not check_trusted(lambda s: None, sym, XVAL_N,
                               tamper=(0, 5, F(1, 10 ** 6)))
    log(f"  cross-validation rejected: {caught}")
    muts.append(("M3 trusted rhs comparison shifted", caught))

    log("\n(M4) add 1 to one entry of the band-2 constraint matrix")
    caught = not check_design(lambda s: None, tamper=(0, 0))
    log(f"  design sizes rejected: {caught}")
    muts.append(("M4 constraint matrix damaged", caught))

    log("\n(M5) add 1 to a band-2 matrix entry under the gate and the families")
    caught = not check_gate_and_families(lambda s: None, tamper=(3, 4))
    log(f"  gate / D1 / filtration rejected: {caught}")
    muts.append(("M5 matrix damaged under the gate", caught))

    log("\n" + "=" * 72)
    for name, ok in results:
        log(f"  {'PASS' if ok else 'FAIL'}  {name}")
    for name, ok in muts:
        log(f"  {'CAUGHT' if ok else 'MISSED'}  {name}")
    npass = sum(1 for _, ok in results if ok)
    ncau = sum(1 for _, ok in muts if ok)
    allok = npass == len(results) and ncau == len(muts)
    log(f"\nTOTAL: {npass}/{len(results)} checks pass, "
        f"{ncau}/{len(muts)} mutations caught")
    log("VERDICT: " + ("PASS -- band 2 identity half and the correction verified"
                       if allok else "FAIL"))
    log("=" * 72)

    os.makedirs(RESULTS, exist_ok=True)
    with open(os.path.join(RESULTS, "graded_verify_band2.log"), "w") as fh:
        fh.write("\n".join(lines) + "\n")
    return 0 if allok else 1


if __name__ == "__main__":
    sys.exit(main())
