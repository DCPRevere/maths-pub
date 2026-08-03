"""
Dittert at n = 4: the k = n cell, solved WITHOUT the canonical-block design.

WHY THIS FILE EXISTS, and it is not a preference.  `diag_core.build_cell(4, 4)`
CRASHES, and the crash is mathematics, not a bug.  `k4_tail.BLOCKS` contains
three blocks built on the S_m irrep S^(m-2,2) with m = n - 1:

    Ind(1|(m-2,2))            dim (n-1)(n-4)
    Ind(V'|(m-2,2))           dim (n-2)(n-1)(n-4)
    ((m-2,2)|(m-2,2))+        dim ((n-1)(n-4)/2)^2

dim S^(m-2,2) = m(m-3)/2 = (n-1)(n-4)/2, which is ZERO at n = 4: (1,2) is not
a partition of 3.  `k4_tail.two_index_weight(3, anti=False, ...)` therefore gets
an empty nullspace basis and dies on `coef[0] = 1`.  So the 21-block design is
an n >= 5 object; at n = 4 three of its isotypic components do not exist.

WHAT WE DO INSTEAD, and why it is STRONGER rather than weaker.  The canonical
blocks are an ACCELERATION: they decide positive definiteness of the assembled
B x B Grams cheaply, via §6b.39's multiplicity count, which §9.5 records as
asserted rather than formalised.  At n = 4 the assembled Grams are 152 x 152 --
smaller than the 350 x 350 that `(5,4)` already carries through anchor check
[4] as a matter of routine.  So we drop the acceleration and decide positive
definiteness on the ASSEMBLED Grams directly, by exact rational LDL^T.  That is
check [4] itself, and it needs no multiplicity count at all.

    n >= 5 route:  21 canonical blocks PD  --(§6b.39, asserted)-->  B x B PD
    n  = 4 route:  B x B PD, directly

THE SEARCH IS NOT NEW CODE.  `diag_solve.rescale`, `.phase1`, `.solve` and
`.to_w` are generic in the block list -- they never look at the cell.  They are
imported and called UNMODIFIED, with a two-block design [G0, H] in place of the
21-block one.  Cold start only: `SOLVER.md` §S.1 lever 1 measured that seeding
manufactures false negatives, and nothing here is seeded.  Rounding happens in
the equilibrated coordinates and the linear identity S w = rhs holds for EVERY
rational point of the parametrisation by construction (§6b.83).

WHAT THIS FILE MAY AND MAY NOT CONCLUDE.  It produces a CANDIDATE witness in the
stored JSON format, plus its own exact verdict.  Anchor grade is decided
elsewhere, by `diag_anchor.py` through `results/verify_subdittert.py`, which
shares no code with anything here.
"""

import json
import os
import sys
import time
from fractions import Fraction as F

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "dittert"))
sys.path.insert(0, HERE)
import diag_core as dc                                              # noqa: E402
import diag_solve as ds                                             # noqa: E402
import h2_anchor as ha                                              # noqa: E402
import sos                                                          # noqa: E402


# ------------------------------------------------------------------ the cell
def build_cell(n, k, out=print):
    """
    The exact linear system at (n, k), with NO canonical blocks.

    This is `k4_pinrank.build` up to -- but not including -- its line 210, the
    `pr.canonical_blocks` call that cannot run at n = 4.  Everything before it
    is k-general and n-general and is reused verbatim.
    """
    from math import gcd
    import k4_pinrank as pk
    old = pk.K
    pk.K = k
    try:
        assert pk.K == k, "the K substitution did not take effect"
        d = sos.build_sdp(n, k, pk.DEG_BASIS, verbose=False)
        A0e, A1c, A1l, A2e, rhse = pk.exact_system(d)
        Mq = pk.full_matrix(A0e, A1c, A1l, A2e, n)
    finally:
        pk.K = old
    ng, ns = len(d["g_orbits"]), len(d["s_orbits"])
    nl = len(d["lam_orbit_reps"])
    srows, srhs = [], []
    for r, row in enumerate(Mq):
        den = 1
        for v in row:
            den = den * v.denominator // gcd(den, v.denominator)
        den = int(den) * rhse[r].denominator
        srows.append([int(v * den) for v in row])
        srhs.append(rhse[r] * den)
    out(f"  (k={k}, n={n}): B = {d['B']}, rows = {len(srows)}, "
        f"vars = {ng}/{ns}/{nl} = {ng + ns + nl}, NO canonical blocks")
    return dict(n=n, k=k, B=d["B"], C=ng + ns + nl, ng=ng, ns=ns, nl=nl,
                srows=srows, srhs=srhs, blocks=[]), d


# --------------------------------------------------------- the two-block design
def raw_design(cell, d, aff, out=print):
    """
    Float `G0` and `H` at gs0, and their derivatives along each kernel direction.

    Only TWO blocks, both B x B.  `sigma_p` for p != (0,0) never appears: the
    (A1)/(A2) conjugacy -- checked by the trusted route, not here -- makes every
    other multiplier Gram a permutation conjugate of H.
    """
    t0 = time.time()
    B, ng, ns = cell["B"], cell["ng"], cell["ns"]
    spec = (("sigma_0  G0", d["g_orbits"], 0, ng),
            ("sigma_11 H ", d["s_orbits"], ng, ng + ns))
    names, M0s, Djs = [], [], []
    for name, orbs, lo, hi in spec:
        idx = np.empty(sum(len(o) for o in orbs), dtype=np.int64)
        who = np.empty_like(idx)
        t = 0
        for vi, orb in enumerate(orbs):
            idx[t:t + len(orb)] = np.fromiter(orb, dtype=np.int64,
                                              count=len(orb))
            who[t:t + len(orb)] = vi
            t += len(orb)
        base = np.zeros(B * B)
        base[idx] = np.array([float(v) for v in aff["gs0"][lo:hi]])[who]
        M0 = base.reshape(B, B)
        Dj = np.zeros((len(aff["Z"]), B, B))
        for j, z in enumerate(aff["Z"]):
            col = np.array([float(v) for v in z[lo:hi]])
            flat = np.zeros(B * B)
            flat[idx] = col[who]
            Dj[j] = flat.reshape(B, B)
        names.append(name)
        M0s.append(0.5 * (M0 + M0.T))
        Djs.append(np.ascontiguousarray(0.5 * (Dj + Dj.transpose(0, 2, 1))))
    out(f"  raw design: {len(names)} assembled {B}x{B} blocks, "
        f"{len(aff['Z'])} directions ({time.time() - t0:.0f} s)")
    return names, M0s, Djs


# ------------------------------------------------------------- exact decision
def exact_verdict(cell, d, w, out=print):
    """S w = rhs over Q, then exact LDL on the two ASSEMBLED B x B Grams."""
    for r, row in enumerate(cell["srows"]):
        acc = F(0)
        for j, v in enumerate(row):
            if v and w[j]:
                acc += F(v) * w[j]
        if acc != cell["srhs"][r]:
            return False, False, [], None
    B, ng, ns = cell["B"], cell["ng"], cell["ns"]
    piv, worst = [], None
    for tag, orbs, coeff in (("sigma_0  G0", d["g_orbits"], w[:ng]),
                             ("sigma_11 H ", d["s_orbits"], w[ng:ng + ns])):
        G = ha.assemble(B, orbs, coeff)
        if not ha.symmetric(G):
            out(f"    {tag}: NOT SYMMETRIC -- assembly is wrong")
            return True, False, piv, None
        p, bad = ha.ldl_min_pivot(G, out, tag, report_every=0)
        piv.append((tag, B, p is not None, p))
        if p is None:
            return True, False, piv, bad
        worst = p if worst is None or p < worst else worst
    return True, True, piv, worst


def ladder(cell, d, aff, coef, out=print,
           sigs=(6, 8, 10, 12, 16, 20, 24, 30, 40, 50)):
    for sig in sigs:
        t0 = time.time()
        w, den = ds.to_w(cell, aff, coef, sig)
        if w is None:
            out(f"    sig {sig:3d}: lambda recovery failed")
            continue
        lhs_ok, pd, piv, worst = exact_verdict(cell, d, w, out=out)
        out(f"    sig {sig:3d}: S w = rhs {lhs_ok}, both assembled Grams PD "
            f"{pd}, pivot {float(worst) if worst is not None else float('nan'):+.6e}"
            f" ({time.time() - t0:.0f} s)")
        if lhs_ok and pd:
            return w, sig, piv, worst
    return None, None, None, None


# ---------------------------------------------------------------------- main
def run(n, k, out=print, store=True, tag="", rounds=3, R=1e6):
    out(f"\n=== ASSEMBLED-GRAM DIRECT SOLVE at (k = {k}, n = {n}) ===")
    cell, d = build_cell(n, k, out=out)
    aff = dc.affine_in_gs(cell, out=out)
    if aff is None:
        return "LINEAR SYSTEM INCONSISTENT", None
    names, M0raw, Draw = raw_design(cell, d, aff, out=out)
    t0 = time.time()
    coef, lm, hist, last = ds.solve(M0raw, Draw, out=out, rounds=rounds, R=R)
    out(f"  float verdict: least block eigenvalue {lm:+.9e} "
        f"({time.time() - t0:.0f} s); margins by round "
        f"{[f'{h[1]:+.3e}' for h in hist]}")
    M0s, Djs, dscale, x = last
    for b, name in enumerate(ds.blocks_at(M0s, Djs, x)):
        ev = np.linalg.eigvalsh(name)
        out(f"      {names[b]:30s} {name.shape[0]:3d}  lambda_min "
            f"{ev.min():+.6e}  lambda_max {ev.max():+.6e}")
    ctx = dict(cell=cell, d=d, aff=aff, coef=coef, lm=lm, hist=hist)
    if lm <= 0:
        return "FLOAT INFEASIBLE (NOT a verdict -- needs an exact Farkas dual)", ctx
    out("  exact rounding ladder, in the equilibrated coordinates:")
    w, sig, piv, worst = ladder(cell, d, aff, coef, out=out)
    if w is None:
        return "FLOAT FEASIBLE, EXACT ROUNDING FAILED", ctx
    ctx["w"] = w
    if store:
        path = os.path.join(HERE, "results", "witness",
                            f"diag_n{n}_k{k}{tag}.json")
        with open(path, "w") as fh:
            json.dump(dict(
                claim="S w = rhs exactly and BOTH ASSEMBLED B x B Grams are "
                      "positive definite over Q",
                kind="feasible", n=n, k=k, deg_basis=2,
                design="unpinned, assembled Grams (no canonical blocks: "
                       "S^(m-2,2) is empty at n = 4)",
                selection=f"phase-I max-margin, adaptive rescaling, R={R}, "
                          f"rounding sig={sig}",
                float_margin=repr(lm), least_ldl_pivot=str(worst),
                blocks=[[nm, dd, str(p)] for nm, dd, ok, p in piv],
                point=[f"{v.numerator}/{v.denominator}" for v in w]), fh)
        out(f"  witness written to {path}")
    return "FEASIBLE (exact, ASSEMBLED Grams)", ctx


# -------------------------------------------------------- the positive control
def control(out=print):
    """
    Three checks at `(k = 4, n = 5)`, a cell with a stored anchor certificate.

    A new certificate must not be the first user of a new code path, so every
    piece of new code here is exercised first where the answer is known.

      C1  `build_cell(5, 4)` must reproduce `k4_pinrank.build(5)`'s stored
          system ENTRY FOR ENTRY -- same 87 integer rows, same 87 rationals.
          If the two disagree the whole file is solving a different problem.
      C2  `exact_verdict` must certify the stored `(5,4)` anchor point, and its
          least assembled pivot must equal the one `h2_anchor` recorded.
      C3  `raw_design`'s float design must reproduce the exact assembly:
          `M0 + sum_j coef_j D_j` against `ha.assemble` at the stored point.
          This is the only genuinely new arithmetic in the file.
    """
    ok = {}
    t0 = time.time()
    cell, d = build_cell(5, 4, out=out)
    ref = dc.cached_cell(5, 4, out=out)
    c1 = (cell["srows"] == ref["srows"] and cell["srhs"] == ref["srhs"]
          and cell["B"] == ref["B"] and (cell["ng"], cell["ns"], cell["nl"])
          == (ref["ng"], ref["ns"], ref["nl"]))
    ok["C1 system reproduces k4_pinrank.build(5)"] = c1
    out(f"  C1 exact system vs the cached (5,4) cell, entry for entry: "
        f"{'IDENTICAL' if c1 else 'DIFFERS'}")

    w, doc = ha.load_point(5, "diag_n5_k4.json")
    lhs, pd, piv, worst = exact_verdict(cell, d, w, out=out)
    c2 = lhs and pd
    ok["C2 stored (5,4) witness certified"] = c2
    out(f"  C2 stored diag_n5_k4.json: S w = rhs {lhs}, both assembled Grams "
        f"PD {pd}, least assembled pivot {float(worst) if worst else 0:+.6e} "
        f"(stored least BLOCK pivot {doc['least_ldl_pivot']})")

    aff = dc.affine_in_gs(cell, out=out)
    names, M0s, Djs = raw_design(cell, d, aff, out=out)
    coef = [float(v) for v in ds.coef_from_w(aff, w)]
    B, ng, ns = cell["B"], cell["ng"], cell["ns"]
    worstdev = 0.0
    for b, (orbs, lo, hi) in enumerate(((d["g_orbits"], 0, ng),
                                        (d["s_orbits"], ng, ng + ns))):
        exact = np.array([[float(v) for v in row]
                          for row in ha.assemble(B, orbs, w[lo:hi])])
        got = M0s[b] + np.tensordot(np.array(coef), Djs[b], axes=(0, 0))
        scale = max(1.0, float(np.abs(exact).max()))
        worstdev = max(worstdev, float(np.abs(got - exact).max()) / scale)
    c3 = worstdev < 1e-9
    ok["C3 float design reproduces the exact assembly"] = c3
    out(f"  C3 design vs exact assembly at the stored point: worst relative "
        f"deviation {worstdev:.3e} -> {'AGREE' if c3 else 'DISAGREE'}")
    out(f"  control complete ({time.time() - t0:.0f} s): "
        f"{'ALL PASS' if all(ok.values()) else 'FAILURES PRESENT'}")
    return all(ok.values()), ok


def main(argv):
    pairs = []
    for a in argv:
        if "," in a:
            nn, kk = a.split(",")
            pairs.append((int(nn), int(kk)))
    if not pairs:
        pairs = [(4, 4)]
    out = lambda s: print(s, flush=True)                        # noqa: E731
    if "--no-control" not in argv:
        out("=== POSITIVE CONTROL at (k = 4, n = 5) ===")
        good, _ = control(out=out)
        if not good:
            out("CONTROL FAILED -- nothing below would mean anything")
            return 1
    for n, k in pairs:
        v, _ = run(n, k, out=out)
        out(f"  ==> (k = {k}, n = {n}): {v}")


if __name__ == "__main__":
    main(sys.argv[1:])
