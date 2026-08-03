"""
The pin re-test in the CANONICAL basis -- NOTES §6b.33, §6b.34, §6b.37.

STEP 1 (recorded at §6b.34, `git log` 7a4bb05) was the 173 sigma_11-only pins,
run before `sigma_0` had a canonical basis.  It was ONE-SIDED by construction:
173 is a SUBSET of §6b.12's 201, feasibility is antitone in the constraint set,
so infeasibility would have overturned §6b.12 while feasibility -- what happened
-- said nothing about the other 28.  It must never be reported as confirmation.

Since §6b.36 `sigma_0`'s ten blocks exist, so this file now runs the FULL test:

    H1  the 321-pin configuration (all 21 blocks)          must be INFEASIBLE
    H2  the 201-pin configuration (omit sigma_11's 16x16)  must be FEASIBLE
    H3  every OTHER single-block omission                   must be INFEASIBLE

H3 is §6b.33 FACT 3: the omission configurations are NOT nested in each other,
so §6b.12's two data points do not extend to the other nineteen and each must be
run.  Omitting a 1x1 block removes no condition, so eight of the twenty-one
configurations ARE the full 321 programme identically -- an identity, not a skip.

WHAT IS AND IS NOT BASIS-DEPENDENT, because the whole point of the re-test is
that §6b.12 used `blockdiag`'s numerical basis:

  * the CONE (`H >= 0`) is basis-free.  `H` restricted to an isotypic component
    is positive iff the multiplicity-space form `M = E^T H E` is, for ANY basis
    `E` of that space -- definiteness of a quadratic form does not depend on the
    basis, only eigenvalues do.  So `blockdiag`'s blocks are used for the cone
    without importing any basis choice into the verdict.
  * the PINS are basis-DEPENDENT: "the block is diagonal" means different linear
    conditions in different bases.  These come from the canonical closed-form
    bases of §6b.17-§6b.32 and from nowhere else.  That is the entire content of
    the re-test.

The pins are read off the SHAPE VECTORS rather than reassembled from the six
closed-form modules' differing conventions: with `cls` in the SDP's OWN orbit
indexing, `block_by_class` returns each entry directly as a coefficient vector
over the SDP's `y`, so no svars-to-orbit permutation is needed anywhere.  All 63
shape vectors are built from already-verified code.
"""

import os
import sys

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "dittert"))
sys.path.insert(0, HERE)
import k4_blocks                                                  # noqa: E402
import k4_ind16 as i16                                            # noqa: E402
import k4_sigma0 as s0                                            # noqa: E402
import k4_system as k4                                            # noqa: E402
import k4_tail as tail                                            # noqa: E402
import k4_vv14 as vv                                              # noqa: E402
import sos                                                        # noqa: E402
from general_k3 import cells_of                                   # noqa: E402
from symmetry import orbits                                       # noqa: E402

K, DEG_BASIS = 4, 2


def canonical_blocks(n, basis):
    """
    All eleven sigma_11 isotypic bases as vectors {basis index: integer}.

    Returns [(name, [vector, ...]), ...].  The multiplicities must total 63.
    """
    out = []
    gens = sos.stab_generators(n, (0, 0))

    # 14x14 trivial: the Stab-orbit indicator vectors (§6b.16)
    reps, _ = orbits(basis, gens)
    out.append(("14x14 trivial",
                [{u: 1 for u in mem} for mem in reps.values()]))

    # 7x7 sign: 1_O - 1_{tau O} over the 7 swapped S x S orbit pairs (§6b.18)
    knt = [k4_blocks.canon_nt(cells_of(m, n)) for m in basis]
    grp = {}
    for u, key in enumerate(knt):
        grp.setdefault(key, []).append(u)
    sgn = []
    for o, t in k4_blocks.sign_pairs():
        v = {u: 1 for u in grp[o]}
        v.update({u: -1 for u in grp[t]})
        sgn.append(v)
    out.append(("7x7 sign", sgn))

    # 16x16 Ind(V'|1) (§6b.24)
    w = i16.sum_zero(n, 20260729)
    out.append(("16x16 Ind(V'|1)",
                i16.as_index_vectors(n, i16.shape_vectors(n, w), basis)))

    # 10x10 and 4x4 from (V'|V'), split by the J-eigenbasis (§6b.30)
    wv = i16.sum_zero(n, 20260729)
    zv = i16.sum_zero(n, 20260729 + 101)
    E14 = vv.shape_vectors(n, wv, zv, basis)
    pi, unmatched = vv.measure_J(n, wv, zv, basis)
    assert not unmatched, unmatched
    U, nplus, _, _ = vv.eigenbasis(pi)

    def combine(row):
        acc = {}
        for s, c in enumerate(row):
            if not c:
                continue
            for u, x in E14[s].items():
                acc[u] = acc.get(u, 0) + c * x
        return {u: x for u, x in acc.items() if x}

    out.append(("10x10 (V'|V')+", [combine(U[p]) for p in range(nplus)]))
    out.append(("4x4 (V'|V')-", [combine(U[p]) for p in range(nplus, 14)]))

    # the last six (§6b.32)
    index = {mo: t for t, mo in enumerate(basis)}
    m = n - 1
    for name, rt, ct, mult, _ in tail.BLOCKS:
        wr = (None if rt == "triv" else
              (i16.sum_zero(n, 20260729) if rt == "vec"
               else tail.two_index_weight(m, rt == "asym", 20260729)[0]))
        wc = (None if ct == "triv" else
              (i16.sum_zero(n, 20260729 + 57) if ct == "vec"
               else tail.two_index_weight(m, ct == "asym", 20260729 + 57)[0]))
        cand = tail.candidates(rt, ct)
        vecs = [tail.realise(c, n, rt, ct, wr, wc) for c in cand]
        kept, _, _ = tail.independent_subset(vecs)
        assert len(kept) == mult, (name, len(kept), mult)
        out.append((name, [{index[mo]: c for mo, c in vecs[t].items()}
                           for t in kept]))
    return out


def orbit_class_array(n, basis, orbs):
    """cls[u*B+v] = index of the SDP's own s-orbit containing (u, v)."""
    from array import array
    B = len(basis)
    cls = array("i", bytes(4 * B * B))
    for j, orb in enumerate(orbs):
        for code in orb:
            cls[code] = j
    return cls


def all_pin_rows(n, basis, d):
    """
    Every off-diagonal condition of all TWENTY-ONE canonical blocks, tagged.

    Returns (rows, counts) with rows a list of (side, block name, vector) and
    `side` in {"s11", "s0"} naming which Gram the condition constrains.  The
    vectors are coefficient vectors over the SDP's OWN orbit indexing on that
    side, so no svars/gvars permutation appears anywhere.
    """
    B = len(basis)
    rows, counts = [], []
    sets = (("s11", canonical_blocks(n, basis), d["s_orbits"], 63, 293),
            ("s0", s0.canonical_blocks(n, basis), d["g_orbits"], 23, 28))
    for side, blocks, orbs, mult, npred in sets:
        tot = sum(len(E) for _, E in blocks)
        print(f"  {side}: {len(blocks)} blocks {[len(E) for _, E in blocks]}, "
              f"multiplicity {tot} (must be {mult})")
        assert tot == mult, (side, tot, mult)
        cls = orbit_class_array(n, basis, orbs)
        k0 = len(rows)
        for name, E in blocks:
            dd = len(E)
            if dd < 2:
                counts.append((side, name, dd, 0))
                continue
            N = vv.block_by_class(E, cls, B)
            k = 0
            for i in range(dd):
                for j in range(i + 1, dd):
                    vec = np.zeros(len(orbs))
                    for c, x in N[i][j].items():
                        vec[c] = float(x)
                    rows.append((side, name, vec))
                    k += 1
            counts.append((side, name, dd, k))
        got = len(rows) - k0
        print(f"       pins {got}  (predicted {npred})")
        assert got == npred, (side, got, npred)
    return rows, counts


# The whole feasible region is small in `t`: the UNPINNED control reaches only
# t = +5.66e-04 at n = 5 and +2.31e-04 at n = 6, so every margin in this file
# lives at 1e-4 and below, where a single SCS run is not accurate enough to
# carry a sign.  Measured at 13:56 on 2026-07-29
# (`results/pinretest_h2_ladder_n6.log`): the 201-pin configuration at n = 6
# returned t = -3.700400e-04 at eps 1e-10 and t = +9.699817e-05 at eps 1e-12 --
# the SAME programme, opposite signs.  So:
#
#   * every configuration is run over a LADDER of solver settings, and
#   * the reported value is the MAXIMUM over the ladder.  `t` is being
#     maximised, so a larger attained value is the better-supported one; and
#   * the verdict has a THIRD state.  Anything inside +-NOISE is UNDECIDED, and
#     no numeric run here decides infeasibility at all -- that is the exact
#     route's job (`k4_pinrank.py`).  A negative solver margin is not a proof.
NOISE = 1e-4

LADDER = (("SCS", dict(eps_abs=1e-10, eps_rel=1e-10, max_iters=200000)),
          ("SCS", dict(eps_abs=1e-12, eps_rel=1e-12, max_iters=400000)),
          ("CLARABEL", {}))


def make_solver(n, d, keep, gblocks, sblocks):
    import cvxpy as cp

    def solve(pinrows):
        x = cp.Variable(len(d["g_orbits"]))
        y = cp.Variable(len(d["s_orbits"]))
        z = cp.Variable(len(d["lam_orbit_reps"]))
        t = cp.Variable()
        cons = [d["A0"][keep] @ x + d["A1"][keep] @ y + d["A2"][keep] @ z
                == d["rhs"][keep], t <= 1.0]
        for bl, var in ((gblocks, x), (sblocks, y)):
            for C, _ in bl:
                dd = C.shape[0]
                Mb = cp.reshape(C.reshape(dd * dd, -1) @ var, (dd, dd),
                                order="C")
                cons.append(0.5 * (Mb + Mb.T) - t * np.eye(dd) >> 0)
        for side, _, vec in pinrows:
            cons.append(vec @ (y if side == "s11" else x) == 0)
        prob = cp.Problem(cp.Maximize(t), cons)
        best, tag, spread = None, "none", None
        for name, kw in LADDER:
            try:
                prob.solve(solver=getattr(cp, name), verbose=False, **kw)
            except Exception:                                    # noqa: BLE001
                continue
            if prob.status not in ("optimal", "optimal_inaccurate"):
                continue
            tv = float(t.value)
            spread = tv if spread is None else min(spread, tv)
            if best is None or tv > best:
                best, tag = tv, f"{name}/{prob.status}"
        return best, tag, (None if best is None else best - spread)
    return solve


def run(n, mode="main"):
    from blockdiag import block_structure
    from exactsd import exact_system, full_matrix, independent_rows

    d = sos.build_sdp(n, K, DEG_BASIS, verbose=False)
    B = d["B"]
    basis = d["basis"]
    print(f"\n=== n = {n}:  B = {B} ===")

    rows, counts = all_pin_rows(n, basis, d)
    print(f"  TOTAL canonical pins {len(rows)}  (predicted 321)")
    assert len(rows) == 321, len(rows)

    gblocks = block_structure(d["g_orbits"], B, verbose=False)
    sblocks = block_structure(d["s_orbits"], B, verbose=False)
    A0e, A1c, A1l, A2e, rhse = exact_system(d)
    keep, _, consistent = independent_rows(full_matrix(A0e, A1c, A1l, A2e, n),
                                           rhse)
    if not consistent:
        raise RuntimeError("system inconsistent over Q")
    solve = make_solver(n, d, np.array(keep), gblocks, sblocks)

    def report(label, sel):
        tv, st, spread = solve(sel)
        if tv is None:
            print(f"  {label:44s} {len(sel):3d} pins  FAILED  ({st})",
                  flush=True)
            return None
        verdict = ("feasible" if tv > NOISE else
                   "neg (exact route decides)" if tv < -NOISE else "UNDECIDED")
        print(f"  {label:44s} {len(sel):3d} pins  t = {tv:+.6e}  "
              f"ladder spread {spread:.1e}  ({st})  {verdict}", flush=True)
        return tv

    if mode in ("main", "omit", "s0sweep"):
        report("unpinned control", [])
        report("H1  FULL pinning, all 21 blocks", rows)
        c201 = [r for r in rows if r[1] != "16x16 Ind(V'|1)"]
        report("H2  201: omit sigma_11's 16x16", c201)

    if mode == "s0sweep":
        # A diagnostic, NOT part of §6b.33's programme.  It was written when the
        # n = 6 201-pin margin read -3.70e-04 and that was taken for a boundary
        # lying among sigma_0's five blocks with d >= 2.  The ladder above
        # showed the sign was solver noise, so the premise is withdrawn; the
        # sweep is kept only because it localises WHICH sigma_0 block binds.
        # Drop each in turn from the 201 configuration, and report the
        # all-sigma_0-dropped control (= §6b.34's 173) in the same run.
        c201 = [r for r in rows if r[1] != "16x16 Ind(V'|1)"]
        report("S0  173: also drop ALL of sigma_0",
               [r for r in c201 if r[0] != "s0"])
        for side, nm, dd, k in counts:
            if side != "s0" or k == 0:
                continue
            report(f"S0  201 minus sigma_0 {nm} ({dd}x{dd}, {k} pins)",
                   [r for r in c201 if not (r[0] == "s0" and r[1] == nm)])
        return

    if mode != "omit":
        return

    # H3 -- the word "unique".  Omitting a 1x1 block removes NO condition, so
    # that configuration IS the full 321 one, exactly; only the blocks with
    # d >= 2 give a distinct programme.  Stated as an identity, not a skip.
    blocks = [(side, nm, dd, k) for side, nm, dd, k in counts]
    trivial = [(side, nm) for side, nm, dd, k in blocks if k == 0]
    print(f"\n  H3: 21 single-block omissions.  {len(trivial)} of them omit a "
          f"1x1 block and so remove no condition -- those configurations are "
          f"IDENTICALLY the full 321 programme:")
    print(f"      {[nm for _, nm in trivial]}")
    print(f"  the remaining {21 - len(trivial)} are distinct programmes:")
    for side, nm, dd, k in blocks:
        if k == 0:
            continue
        sel = [r for r in rows if not (r[0] == side and r[1] == nm)]
        report(f"H3  omit {side} {nm} ({dd}x{dd})", sel)


if __name__ == "__main__":
    args = sys.argv[1:]
    mode = ("omit" if "--omit" in args else
            "s0sweep" if "--s0sweep" in args else "main")
    ns = [int(a) for a in args if not a.startswith("-")] or [5, 6]
    print("Canonical-basis pin re-test -- NOTES §6b.9/§6b.33, all 21 blocks")
    print("H1 full 321 pins; H2 the 201 configuration (omit sigma_11's 16x16);"
          " H3 every single-block omission.")
    print("§6b.12 is CONFIRMED only if H1 infeasible, H2 strictly feasible and "
          "every other omission infeasible.")
    for n in ns:
        run(n, mode=mode)
