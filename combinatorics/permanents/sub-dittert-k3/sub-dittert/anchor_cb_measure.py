"""
MEASURE the C_b route against the stored B x B control, at (k = 4, n = 6).

WHAT IS BEING MEASURED, and against what.  `results/h2anchor_n6.log` is the
control: the two assembled 702x702 Grams factored exactly over Q in 318 s and
1883 s, total 2201 s, both POSITIVE DEFINITE.  `anchor_wtest.py` established, at
n = 5 and n = 6 exactly over Q, that

    H  ~congruent~  (+)_b ( C_b (x) h_b )

with `h_b` the canonical block (size d_b) and `C_b` the matrix of slice scalars
(size e_b, the irrep dimension).  Eigenvalues of a Kronecker product are the
products, so with every `h_b` positive definite, `H` is positive definite exactly
when every `C_b` is.  This file builds the 21 `C_b`, factors each over Q, and
reports the verdict and the WALL TIME beside the control's 2201 s.

WHAT COUNTS AS THE COST, stated before the number is produced so it cannot be
chosen afterwards.  The honest comparison is end to end: everything needed to get
from the stored witness and the canonical blocks to a positive definiteness
verdict on the assembled Gram.  That INCLUDES building the slices, which at
n = 6 took 283 s on its own in `anchor_wtest.py`.  If the slice construction
dominates, the win is single-digit and not the cube-law ratio, and that is the
result -- the ratios sum(e^3)/B^3 of 105x to 4159x are an elimination-work count,
not a wall-time prediction.

WHY THE RATIO IS NOT THE ANSWER.  This folder's last cube-law extrapolation, a
two-point `B^3.50` fit, under-called the (k = 4, n = 7) factorisation by 1.6x
against a shape-matched estimate that landed within 0.6%.  A cube-law ratio is a
count of multiply-adds; it ignores that entry growth in a size-100 elimination is
nothing like a size-702 one.  The number below is measured.

WHAT IS NOT CLAIMED.  That `C_b` is positive definite in general.  At n = 5 and
n = 6 the Gram is ALREADY KNOWN positive definite, so `C_b` coming out positive
definite here is a consequence and not independent evidence -- citing these n as
support for the n-uniform theorem would be circular, and this file does not.
What is measured is the COST of the route, on cells where the answer is known.

VERIFICATION STANDARD.  The `C_b` build shares its slice machinery with
`anchor_wtest.py`, so the congruence is RE-ASSERTED here on the objects actually
built rather than cited: every d_b x d_b sub-block must equal its scalar times
`h_b`, exactly over Q, and the identity slice must return scalar 1.  A shared
code path is exactly where a subtly different extraction would hide.
"""

import os
import sys
import time
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "dittert"))
sys.path.insert(0, HERE)
import sos                                                          # noqa: E402
import k4_pinretest as pr                                           # noqa: E402
import k4_vv14 as vv                                                # noqa: E402
import h2_anchor as ha                                              # noqa: E402
import anchor_check3 as ac                                          # noqa: E402
import anchor_wtest as wt                                           # noqa: E402

K = 4

# Typed in from results/h2anchor_n6.log -- the control this is measured against.
# Verdicts must agree; pivots must NOT be compared, the matrices are different.
# PART 1 (cross-component H-orthogonality) is REQUIRED for the decomposition and
# is NOT performed by this file.  Its measured cost is typed in from
# results/anchor_wtest_n{5,6}.log so the replacement cost below can include it;
# without it this file reports a speedup for a route that does not stand up.
PART1_SECS = {5: 107, 6: 897}

CONTROL = {5: dict(secs=193, g0_secs=18, h_secs=175,
                   g0_pivot="3.380435e-05", h_pivot="1.315071e-05",
                   verdict="both assembled Grams POSITIVE DEFINITE over Q"),
           6: dict(secs=2201, g0_secs=318, h_secs=1883,
                   g0_pivot="4.083407e-05", h_pivot="1.070308e-05",
                   verdict="both assembled Grams POSITIVE DEFINITE over Q")}


def ldl_pd(M):
    """Exact rational LDL^T.  Returns (True, least pivot) or (False, index)."""
    m = len(M)
    a = [list(r) for r in M]
    worst = None
    for k in range(m):
        d = a[k][k]
        if d <= 0:
            return False, k
        worst = d if worst is None else min(worst, d)
        ak = a[k]
        for i in range(k + 1, m):
            f = a[i][k]
            if not f:
                continue
            f = f / d
            ai = a[i]
            for j in range(k, m):
                if ak[j]:
                    ai[j] -= f * ak[j]
    return True, worst


def build_cb(n, out):
    """
    The 21 `C_b`, with the congruence re-asserted on the built objects.

    Returns (ok, per-side results, seconds spent building).
    """
    t0 = time.time()
    lean = ac.lean_sdp(n)
    B, basis = lean["B"], lean["basis"]
    index = {tuple(m): i for i, m in enumerate(basis)}
    w, doc = ha.load_point(n)
    ng, ns = len(lean["g_orbits"]), len(lean["s_orbits"])
    grams = {"sigma_11": ha.assemble(B, lean["s_orbits"], w[ng:ng + ns]),
             "sigma_0": ha.assemble(B, lean["g_orbits"], w[:ng])}
    out(f"  witness {doc.get('kind')}, B = {B}, setup {time.time() - t0:.0f} s")

    ok, sides_out = True, []
    for label, gens, blocks, orbs, off in wt.sides(n, basis, lean):
        G = grams[label]
        perms = [p for p in (wt.induced_perm(basis, index, g) for g in gens)
                 if p is not None]
        cls = pr.orbit_class_array(n, basis, orbs)
        rows = []
        for name, E in blocks:
            d = len(E)
            hb = wt.contract(vv.block_by_class(E, cls, B), d, w, off)
            vE = wt.vecs_of(E, B)
            full = wt.close_component(vE, perms, B, out)
            slices, rank = wt.slice_closure(vE, perms, B, len(full), out)
            if rank != len(full):
                out(f"    {name:26s} slice closure {rank} of {len(full)} -- "
                    f"NOT a union of whole slices")
                ok = False
                continue
            e = len(slices)
            nz = next(((s, t) for s in range(d) for t in range(d) if hb[s][t]),
                      None)
            if nz is None:
                out(f"    {name:26s} h_b identically zero; skipped")
                continue
            # C_b, with the congruence RE-ASSERTED on these very objects
            C = [[F(0)] * e for _ in range(e)]
            bad = None
            for i in range(e):
                Si = slices[i][1]
                GS = [[sum(G[u][v] * a[u] for u in range(B) if a[u])
                       for v in range(B)] for a in Si]
                for j in range(i, e):
                    Sj = slices[j][1]
                    M = [[sum(GS[s][v] * Sj[t][v]
                              for v in range(B) if Sj[t][v])
                          for t in range(d)] for s in range(d)]
                    c = M[nz[0]][nz[1]] / hb[nz[0]][nz[1]]
                    if any(M[s][t] != c * hb[s][t]
                           for s in range(d) for t in range(d)):
                        bad = (i, j)
                        break
                    C[i][j] = C[j][i] = c
                if bad:
                    break
            if bad:
                out(f"    {name:26s} *** sub-block {bad} is NOT a multiple of "
                    f"h_b -- congruence FAILS on the built objects")
                ok = False
                continue
            if C[0][0] != 1:
                out(f"    {name:26s} *** identity slice scalar is {C[0][0]}, "
                    f"expected 1 -- extraction is wired wrongly")
                ok = False
                continue
            rows.append((name, d, e, hb, C))
        sides_out.append((label, rows))
    return ok, sides_out, time.time() - t0


def main(argv):
    ns = [int(a) for a in argv if a.isdigit()] or [6]
    out = lambda s: print(s, flush=True)                       # noqa: E731
    out("=" * 74)
    out("MEASURED cost of the C_b route against the stored B x B control")
    out("=" * 74)
    out("The sum(e^3)/B^3 ratios of 105x to 4159x are a COUNT of elimination")
    out("multiply-adds, NOT a wall-time prediction.  This folder's last")
    out("cube-law extrapolation (a two-point B^3.50 fit) under-called the")
    out("(k = 4, n = 7) factorisation by 1.6x, against a shape-matched estimate")
    out("that landed within 0.6%.  The cost below is END TO END and INCLUDES")
    out("building the slices, which cost 283 s on its own at n = 6.  If the")
    out("slice build dominates, the win is single-digit and that is the result.")
    out("")
    out("NOT evidence for the n-uniform theorem: at these n the Gram is already")
    out("known positive definite, so C_b coming out definite is a consequence.")
    out("=" * 74)

    for n in ns:
        ctl = CONTROL.get(n)
        out(f"\n=== (k = {K}, n = {n}) ===")
        if ctl:
            out(f"  control (results/h2anchor_n{n}.log): {ctl['verdict']}, "
                f"{ctl['g0_secs']} s + {ctl['h_secs']} s = {ctl['secs']} s")
        ok, sides_out, build_s = build_cb(n, out)
        if not ok:
            out(f"\n==> (k = {K}, n = {n}): the congruence FAILED to re-assert "
                f"on the built objects.  No measurement is reportable.")
            return 1
        out(f"  slice build and C_b extraction: {build_s:.0f} s")

        t1 = time.time()
        allpd = True
        for label, rows in sides_out:
            out(f"  {label}: factoring {len(rows)} C_b and {len(rows)} h_b "
                f"over Q")
            for name, d, e, hb, C in rows:
                pdh, ih = ldl_pd(hb)
                pdc, ic = ldl_pd(C)
                allpd = allpd and pdh and pdc
                out(f"    {name:26s} h_b {d:3d}x{d:<3d} "
                    f"{'PD' if pdh else 'NOT PD'}   "
                    f"C_b {e:3d}x{e:<3d} {'PD' if pdc else 'NOT PD'}"
                    + (f"   least C_b pivot {float(ic):.6e}" if pdc else ""))
        fac_s = time.time() - t1
        out(f"  exact factorisations: {fac_s:.0f} s")

        total = build_s + fac_s
        out(f"\n  MEASURED, end to end: {total:.0f} s "
            f"({build_s:.0f} s slices + C_b, {fac_s:.0f} s factorisations)")
        if ctl:
            out(f"  control B x B:        {ctl['secs']} s")
            p1 = PART1_SECS.get(n)
            if p1 is None:
                out(f"  *** PART 1's cost is not recorded at this n, so NO "
                    f"speedup is reportable.  The {total:.0f} s above is the "
                    f"C_b build alone and is NOT a replacement cost.")
            else:
                repl = total + p1
                out(f"  PART 1 (required, not run here): {p1} s")
                out(f"  REPLACEMENT COST:     {repl:.0f} s "
                    f"= {total:.0f} s (this file) + {p1} s (PART 1)")
                out(f"  HONEST SPEEDUP:       {ctl['secs'] / repl:.1f}x")
                out(f"    NOT {ctl['secs'] / total:.1f}x -- that figure omits "
                    f"PART 1, and without cross-component H-orthogonality the "
                    f"decomposition does not hold, so definiteness of the "
                    f"diagonal blocks proves nothing about the Gram.")
                out(f"    (elimination-work ratio was 105x-4159x; the "
                    f"factorisations really are near-free, the cost moved into "
                    f"slices and orthogonality, both O(B^3))")
            agree = allpd
            out(f"  VERDICT AGREEMENT: C_b route says Gram "
                f"{'POSITIVE DEFINITE' if allpd else 'NOT positive definite'}; "
                f"control says positive definite -> "
                f"{'AGREE' if agree else '*** DISAGREE ***'}")
            out(f"  (pivots deliberately NOT compared -- different matrices)")
            if not agree:
                return 1
        if ctl and PART1_SECS.get(n):
            repl = total + PART1_SECS[n]
            out(f"\n==> (k = {K}, n = {n}): C_b route reproduces the control's "
                f"verdict; honest replacement speedup "
                f"{ctl['secs'] / repl:.1f}x")
        else:
            out(f"\n==> (k = {K}, n = {n}): C_b build measured at "
                f"{total:.0f} s; NOT a replacement cost (PART 1 not included)")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
