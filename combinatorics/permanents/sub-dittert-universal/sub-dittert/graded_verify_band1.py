#!/usr/bin/env python3
"""
GRADED VERIFIER for the band-1 positivity theorem (POSITIVITY.md, NOTES 37).

Everything below is decided in exact rational arithmetic.  No floating-point
number enters any verdict.  The verifier is required to REJECT: five mutations
are injected and every one of them must be caught, and the clean run must be
silent.

WHAT IS CHECKED

 [1] Lemma 1 inside band 1.  The constraint system built by the ORIGINAL path
     (sos.build_sdp -> exactsd.exact_system) is entrywise identical at k = 2 and
     k = 3 for deg_basis = 1, at several n; only the rhs moves.
 [2] The symbolic band system (general_k3 closed forms) reproduces that trusted
     system entry for entry, rhs included.  The two share no logic.
 [3] Theorem 4's collapse, SYMBOLICALLY in n:  the particular solution of
     rhs(n,k) equals sum_d (k)_d (Y_d + (k!/n^k) Z_d) as elements of Q(n), for
     every k of the band.  (PARAMETRIC.md measured this at integer n only.)
 [4] Law B1's 19 rational functions, specialised at each cell, satisfy the
     TRUSTED linear system exactly -- so the identity half holds at that cell.
 [5] The assembled n^2 x n^2 sigma_0 and sigma_11 Gram matrices are positive
     definite by exact rational LDL^T.  This does not use the block theory, so
     it is an independent confirmation of the ten-quantity reduction.
 [6] The ten UPP quantities are positive on the stated ranges, decided by Sturm
     (complete, not merely sufficient), and the shifted-coefficient thresholds
     agree with the Sturm answer.
 [7] The recorded ranges are SHARP in the sense that the certificate fails one
     step below: k = 2 at n = 2 and k = 3 at n = 3.

Run:  ./guard.sh python3 graded_verify_band1.py
"""

import os
import sys
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "dittert"))
sys.path.insert(0, HERE)

import band1_certificate as b1                                    # noqa: E402
import general_k3 as g                                            # noqa: E402
from exactsd import (assemble, exact_system, full_matrix,          # noqa: E402
                     ldl_pivots)
from sos import build_sdp                                          # noqa: E402
from symmetry import monomials as _mons                            # noqa: E402

DB = 1
CELLS = {2: (3, 4, 5, 6, 7), 3: (4, 5, 6, 7)}
LEMMA1_NS = (4, 5, 6)
RESULTS = os.path.join(HERE, "results")


# --------------------------------------------------------------- trusted path
_CACHE = {}


def trusted(n, k):
    """(d, Mfull, rhs, key->column map) from the original code path."""
    if (n, k) in _CACHE:
        return _CACHE[(n, k)]
    d = build_sdp(n, k, DB, verbose=False)
    A0, A1c, A1l, A2, rhs = exact_system(d)
    M = full_matrix(A0, A1c, A1l, A2, n)
    B = d["B"]
    basis = d["basis"]

    def pair_key(orb, fix):
        u, v = divmod(orb[0], B)
        return g.canon(g.cells_of(basis[u] + basis[v], n), fix)

    gmap = [pair_key(o, False) for o in d["g_orbits"]]
    smap = [pair_key(o, True) for o in d["s_orbits"]]
    lam_mons = _mons(n * n, d["TOPDEG"] - 1)
    lmap = [g.canon(g.cells_of(lam_mons[m[0]], n)) for m in d["lam_orbit_reps"]]
    inv_row = {}
    for mono, r in d["orbit_of"].items():
        inv_row.setdefault(r, mono)
    rmap = {r: g.canon(g.cells_of(m, n)) for r, m in inv_row.items()}
    out = (d, M, rhs, gmap, smap, lmap, rmap)
    _CACHE[(n, k)] = out
    return out


def trusted_vector(bd, vals, n, k):
    """The 19 symbolic values re-ordered into the trusted column order."""
    d, M, rhs, gmap, smap, lmap, rmap = trusted(n, k)
    gvars, svars, lvars = bd.sym["gvars"], bd.sym["svars"], bd.sym["lvars"]
    nq = F(n)
    sym = [v.at(nq) for v in vals]
    xq = [sym[gvars.index(key)] for key in gmap]
    yq = [sym[len(gvars) + svars.index(key)] for key in smap]
    zq = [sym[len(gvars) + len(svars) + lvars.index(key)] for key in lmap]
    return xq, yq, zq


def identity_residual(bd, vals, n, k, tamper=None):
    d, M, rhs, gmap, smap, lmap, rmap = trusted(n, k)
    xq, yq, zq = trusted_vector(bd, vals, n, k)
    v = list(xq) + list(yq) + list(zq)
    if tamper is not None:
        j, delta = tamper
        v[j] += delta
    bad = 0
    for r in range(len(M)):
        s = sum(M[r][t] * v[t] for t in range(len(v)))
        if s != rhs[r]:
            bad += 1
    return bad, v


# ------------------------------------------------------------------- the tests
def check_lemma1(log):
    bad = 0
    for n in LEMMA1_NS:
        s2 = exact_system(build_sdp(n, 2, DB, verbose=False))
        s3 = exact_system(build_sdp(n, 3, DB, verbose=False))
        ent = 0
        for i, name in enumerate(("A0", "A1c", "A1l", "A2")):
            for r0, r1 in zip(s2[i], s3[i]):
                for a, b in zip(r0, r1):
                    ent += 1
                    if a != b:
                        bad += 1
        diff = sum(1 for a, b in zip(s2[4], s3[4]) if a != b)
        log(f"  n = {n}: {ent} matrix entries compared, {bad} mismatches; "
            f"rhs differs on {diff} of {len(s2[4])} rows")
    return bad == 0


def check_symbolic(bd, log):
    bad = 0
    tot = 0
    for k in (2, 3):
        for n in LEMMA1_NS:
            d, M, rhs, gmap, smap, lmap, rmap = trusted(n, k)
            nq = F(n)
            rows = bd.sym["rows"]
            for r in range(len(M)):
                R = bd.sym["row_index"][rmap[r]]
                for j, key in enumerate(gmap):
                    tot += 1
                    if M[r][j] != F(g.peval(
                            bd.sym["A0"][R][bd.sym["gvars"].index(key)], nq)):
                        bad += 1
                off = len(gmap)
                for j, key in enumerate(smap):
                    tot += 1
                    J = bd.sym["svars"].index(key)
                    want = (F(g.peval(bd.sym["A1c"][R][J], nq), 1) / nq
                            + F(g.peval(bd.sym["A1l"][R][J], nq)))
                    if M[r][off + j] != want:
                        bad += 1
                off += len(smap)
                for j, key in enumerate(lmap):
                    tot += 1
                    if M[r][off + j] != F(g.peval(
                            bd.sym["A2"][R][bd.sym["lvars"].index(key)], nq)):
                        bad += 1
                tot += 1
                if rhs[r] != g._rhs_rf(rows[R], k).at(nq):
                    bad += 1
            log(f"  (n,k) = ({n},{k}): {tot} entries compared cumulatively, "
                f"{bad} mismatches")
    return bad == 0


def check_collapse(bd, log):
    bad = 0
    for k in (1, 2, 3):
        direct, coll = bd.particular(("k", k)), bd.collapse(k)
        b = sum(1 for j in range(19) if direct[j] != coll[j])
        bad += b
        log(f"  k = {k}: {b} mismatches over 19 coordinates of Q(n)")
    return bad == 0


def check_identity(bd, built, log, tamper=None):
    bad = 0
    for k in b1.BAND_K:
        vals = built[k][1]
        for n in CELLS[k]:
            b, _ = identity_residual(bd, vals, n, k, tamper)
            bad += b
            log(f"  (n,k) = ({n},{k}): {b} violated rows of "
                f"{len(trusted(n, k)[1])}")
    return bad == 0


def check_grams(bd, built, log, tamper=None):
    ok = True
    for k in b1.BAND_K:
        vals = built[k][1]
        for n in CELLS[k]:
            d = trusted(n, k)[0]
            xq, yq, zq = trusted_vector(bd, vals, n, k)
            if tamper is not None:
                which, j, delta = tamper
                (xq if which == 0 else yq)[j] += delta
            B = d["B"]
            G0 = assemble(B, d["g_orbits"], xq)
            H = assemble(B, d["s_orbits"], yq)
            p0, f0 = ldl_pivots(G0)
            p1, f1 = ldl_pivots(H)
            good = p0 is not None and p1 is not None
            ok = ok and good
            log(f"  (n,k) = ({n},{k}): {B}x{B} sigma_0 "
                f"{'PD' if p0 else f'NOT PD at pivot {f0}'}, sigma_11 "
                f"{'PD' if p1 else f'NOT PD at pivot {f1}'}")
    return ok


def check_positivity(bd, built, log, coeffs=None):
    ok = True
    for k in b1.BAND_K:
        if coeffs is None:
            fs = built[k][0]
        else:
            fs = bd.build(k, coeffs)[0]
        qs = bd.quantities(("k", k), fs)
        n0 = b1.N0[k]
        good = b1.sturm_verdict(qs, n0, verbose=False)
        worst = 0
        for _, rf in qs:
            worst = max(worst, b1.snc_threshold(rf) or 10 ** 6)
        log(f"  k = {k}: all ten Sturm-positive on n >= {n0}: {good}; "
            f"worst shifted-coefficient threshold n1 = {worst} "
            f"(gap {worst - n0})")
        ok = ok and good and worst == n0
    return ok


def check_sharpness(bd, built, log):
    """One step below the recorded range the certificate must FAIL."""
    ok = True
    for k, nbad in ((2, 2), (3, 3)):
        qs = bd.quantities(("k", k), built[k][0])
        neg = []
        for name, rf in qs:
            try:
                if rf.at(F(nbad)) <= 0:
                    neg.append(name)
            except ZeroDivisionError:
                neg.append(name + " (pole)")
        log(f"  k = {k}, n = {nbad}: non-positive quantities {neg}")
        ok = ok and bool(neg)
    return ok


# ------------------------------------------------------------------- driver
def main():
    lines = []

    def log(s):
        print(s, flush=True)
        lines.append(s)

    log("=" * 72)
    log("GRADED VERIFIER -- band 1 (deg_basis = 1, k <= 3) positivity theorem")
    log("exact rational arithmetic throughout; mutation controls at the end")
    log("=" * 72)

    bd = b1.Band()
    built = {k: bd.build(k) for k in b1.BAND_K}
    for k in b1.BAND_K:
        fs, beta, z = built[k]
        built[k] = (fs, bd.vals19(("k", k), fs), beta, z)

    results = []

    log("\n[1] Lemma 1 in band 1 (trusted path, k = 2 vs k = 3)")
    results.append(("[1] cone is k-free in band 1", check_lemma1(log)))

    log("\n[2] symbolic band system vs the trusted system, entry for entry")
    results.append(("[2] symbolic system = trusted system",
                    check_symbolic(bd, log)))

    log("\n[3] Theorem 4's collapse, symbolically in n")
    results.append(("[3] Theorem 4 collapse over Q(n)", check_collapse(bd, log)))

    log("\n[4] law B1 satisfies the trusted linear system at every cell")
    results.append(("[4] identity half at every cell",
                    check_identity(bd, built, log)))

    log("\n[5] assembled n^2 x n^2 Grams, exact rational LDL^T")
    results.append(("[5] both Grams positive definite",
                    check_grams(bd, built, log)))

    log("\n[6] the ten UPP quantities, Sturm on the whole range")
    results.append(("[6] positivity for every n in range",
                    check_positivity(bd, built, log)))

    log("\n[7] sharpness one step below the range")
    results.append(("[7] fails at n0 - 1", check_sharpness(bd, built, log)))

    # ------------------------------------------------------------ mutations
    log("\n" + "=" * 72)
    log("MUTATION CONTROLS -- every one of these MUST be caught")
    log("=" * 72)
    muts = []

    log("\n(M1) perturb one sigma_0 coefficient of the certificate by 1/10^6")
    caught = not check_identity(bd, built, lambda s: None,
                                tamper=(0, F(1, 10 ** 6)))
    log(f"  identity rejected: {caught}")
    muts.append(("M1 sigma_0 coefficient perturbed", caught))

    log("\n(M2) perturb one lambda coefficient by -1/10^9")
    caught = not check_identity(bd, built, lambda s: None,
                                tamper=(14, F(-1, 10 ** 9)))
    log(f"  identity rejected: {caught}")
    muts.append(("M2 lambda coefficient perturbed", caught))

    log("\n(M3) subtract 1 from the top-left sigma_11 Gram entry")
    caught = not check_grams(bd, built, lambda s: None, tamper=(1, 0, F(-1)))
    log(f"  LDL rejected: {caught}")
    muts.append(("M3 sigma_11 Gram damaged", caught))

    log("\n(M4) move law B1's beta9 coefficient 1/2 -> 3/2")
    caught = not check_positivity(bd, built, lambda s: None,
                                  coeffs=(F(3, 2), F(8), F(-5)))
    log(f"  positivity rejected: {caught}")
    muts.append(("M4 beta9 law perturbed", caught))

    log("\n(M5) move law B1's x coefficient 8 -> 0")
    caught = not check_positivity(bd, built, lambda s: None,
                                  coeffs=(F(1, 2), F(0), F(-5)))
    log(f"  positivity rejected: {caught}")
    muts.append(("M5 x law perturbed", caught))

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
    log("VERDICT: " + ("PASS -- band 1 positivity theorem verified"
                       if allok else "FAIL"))
    log("=" * 72)

    os.makedirs(RESULTS, exist_ok=True)
    with open(os.path.join(RESULTS, "graded_verify_band1.log"), "w") as fh:
        fh.write("\n".join(lines) + "\n")
    return 0 if allok else 1


if __name__ == "__main__":
    sys.exit(main())
