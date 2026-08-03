"""
BAND 2: a STRUCTURED Gram family, positive definite by construction.

`POSITIVITY.md` section 9 measures the band-2 obstruction: the design positivity
sees is 336-dimensional and `d(alpha) = 0` on every one of the eleven sigma_11
blocks, so no block can be solved on its own.  The lever named there is a
structured ansatz -- a family of Gram pairs, closed form in (n, k), positive
definite BY CONSTRUCTION, and rich enough to meet the 33 inescapable conditions.

This file builds the calibration gate that any such family must pass, and then
tests families against it.

THE GATE.  Corollary C2 of `PARAMETRIC.md` says a certificate at deg_basis = 1
is a certificate at deg_basis = 2: pad each Gram with zero rows and columns for
the new degree-2 basis monomials.  So band 1's solved law B1 must sit inside the
band-2 system exactly.  That is a real cross-check, because the two systems are
built by different code from different class enumerations
(`general_k3.build_symbolic_system` at 12 x 19, `k4_system.build` at 87 x 440),
and it calibrates any family: a family that cannot express the C2 lift of B1
cannot express a band-2 certificate either.

THE DEGREE GRADING, which is what the families use.  The band-2 Gram basis is
the degree-1 monomials (the n^2 cells) together with the degree-2 monomials.
Write a Gram in the induced 2 x 2 block form.  Then

    deg(m_u m_v) = 2      for the (1,1) block  -> feeds rows of degree 2, 3
    deg(m_u m_v) = 3      for the (1,2) block  -> feeds rows of degree 3, 4
    deg(m_u m_v) = 4      for the (2,2) block  -> feeds rows of degree 4, 5

so a family that switches the (1,2) block off is BLOCK DIAGONAL, hence positive
definite exactly when its two diagonal blocks are, and its (1,1) part is
literally band 1's Gram.  That is design D1 below.

Usage:  ../guard.sh python3 band2_family.py
"""

import os
import sys
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "dittert"))
sys.path.insert(0, HERE)

import allk_gen2 as gen2                                          # noqa: E402
import band1_certificate as b1                                    # noqa: E402
import band2_identity as b2                                       # noqa: E402
import general_k3 as g                                            # noqa: E402
import k4_system as k4                                            # noqa: E402
from general_k3 import RF                                         # noqa: E402

ZERO = RF([])
ONE = RF([F(1)])
N = RF([F(0), F(1)])


# ------------------------------------------------------------------ the bridge
def band_bridge(sym1, sym2):
    """Index maps from band 1's 19 coordinates into band 2's 440.

    Row and lambda keys are produced by the SAME `general_k3.canon` in both
    builders, so they compare directly.  Pair keys do not: band 1 stores the
    flat 2-cell multiset, band 2 stores `canon_pair` of two basis monomials.
    A band-1 pair class is a multiset of exactly two cells, so splitting it into
    two degree-1 monomials and re-canonicalising is the bridge, and the swap
    ambiguity is exactly what `canon_pair` quotients by.
    """
    ng2, ns2 = len(sym2["gvars"]), len(sym2["svars"])
    gidx = {key: i for i, key in enumerate(sym2["gvars"])}
    sidx = {key: i for i, key in enumerate(sym2["svars"])}
    lidx = {key: i for i, key in enumerate(sym2["lvars"])}
    ridx = sym2["row_index"]

    def pair_to2(key, fix):
        (c1, c2) = key
        return k4.canon_pair((c1,), (c2,), fix)

    gmap = [gidx[pair_to2(key, False)] for key in sym1["gvars"]]
    smap = [ns2 and sidx[pair_to2(key, True)] for key in sym1["svars"]]
    lmap = [lidx[key] for key in sym1["lvars"]]
    rmap = [ridx[key] for key in sym1["rows"]]
    cols = ([gmap[i] for i in range(len(gmap))]
            + [len(sym2["gvars"]) + s for s in smap]
            + [len(sym2["gvars"]) + ns2 + t for t in lmap])
    assert len(set(cols)) == len(cols), "band-1 -> band-2 bridge is not injective"
    return cols, rmap


def lift(sym1, sym2, vals19):
    """The C2 lift of a band-1 certificate into band 2's 440 coordinates."""
    cols, _ = band_bridge(sym1, sym2)
    x = [ZERO] * (len(sym2["gvars"]) + len(sym2["svars"]) + len(sym2["lvars"]))
    for t, c in enumerate(cols):
        x[c] = vals19[t]
    return x


def residual(M, x, rhs):
    bad = 0
    for r in range(len(M)):
        s = ZERO
        for t in range(len(x)):
            if x[t] and M[r][t]:
                s = s + M[r][t] * x[t]
        if s != rhs[r]:
            bad += 1
    return bad


# ------------------------------------------------------------ degree grading
def pair_degree_type(key):
    """(|u|, |v|) for a band-2 pair class key ((cells of u), (cells of v))."""
    u, v = key
    return tuple(sorted((len(u), len(v))))


def type_columns(sym2):
    """Column index lists per degree type, for sigma_0 and sigma_11."""
    ng = len(sym2["gvars"])
    out = {}
    for name, keys, off in (("g", sym2["gvars"], 0),
                            ("s", sym2["svars"], ng)):
        for j, key in enumerate(keys):
            out.setdefault((name, pair_degree_type(key)), []).append(off + j)
    return out


# ------------------------------------------------------- consistency machinery
def rank_and_consistency(M, cols, rhs):
    """rank of M[:, cols] and of [M[:, cols] | rhs], over Q(n)."""
    nR = len(M)
    A = [[M[i][c] for c in cols] + [rhs[i]] for i in range(nR)]
    nc = len(cols)
    r = 0
    piv = []
    for c in range(nc):
        p = next((i for i in range(r, nR) if A[i][c]), None)
        if p is None:
            continue
        A[r], A[p] = A[p], A[r]
        pv = A[r][c]
        A[r] = [t / pv for t in A[r]]
        for i in range(nR):
            if i != r and A[i][c]:
                f = A[i][c]
                A[i] = [A[i][t] - f * A[r][t] for t in range(nc + 1)]
        piv.append(c)
        r += 1
        if r == nR:
            break
    inconsistent = [i for i in range(r, nR) if A[i][nc]]
    return r, len(inconsistent), inconsistent



# ------------------------------------------------- the degree filtration bound
def row_degrees(sym2):
    return [len(key) for key in sym2["rows"]]


def feeding_columns(sym2):
    """Which column groups can contribute to rows of degree >= 4.

    A Gram column of pair type (|u|,|v|) contributes the monomial m_u m_v of
    degree |u|+|v| to sigma_0's rows, and m_u m_v b_p of degree |u|+|v|+1 to
    sigma_11's.  A lambda column of monomial degree d contributes degree d+1.
    So the (1,1) classes reach degree 2 (sigma_0) and 3 (sigma_11) and NOTHING
    higher: they are invisible to every row of degree >= 4.
    """
    ng, ns = len(sym2["gvars"]), len(sym2["svars"])
    low, high = [], []
    for j, key in enumerate(sym2["gvars"]):
        (low if pair_degree_type(key) == (1, 1) else high).append(j)
    for j, key in enumerate(sym2["svars"]):
        (low if pair_degree_type(key) == (1, 1) else high).append(ng + j)
    lam = list(range(ng + ns, ng + ns + len(sym2["lvars"])))
    return low, high, lam


def submatrix_rank(M, rows, cols):
    A = [[M[i][c] for c in cols] for i in rows]
    nR, nc = len(A), len(cols)
    r = 0
    for c in range(nc):
        p = next((i for i in range(r, nR) if A[i][c]), None)
        if p is None:
            continue
        A[r], A[p] = A[p], A[r]
        pv = A[r][c]
        A[r] = [t / pv for t in A[r]]
        for i in range(nR):
            if i != r and A[i][c]:
                f = A[i][c]
                A[i] = [A[i][t] - f * A[r][t] for t in range(nc)]
        r += 1
        if r == nR:
            break
    return r


def diagonal_classes(sym2):
    """Classes with u == v and |u| = 2: the DIAGONAL of the degree-2 block.
    A positive multiple of this group is the identity on the degree-2 basis."""
    ng = len(sym2["gvars"])
    gd = [j for j, (u, v) in enumerate(sym2["gvars"])
          if u == v and len(u) == 2]
    sd = [ng + j for j, (u, v) in enumerate(sym2["svars"])
          if u == v and len(u) == 2]
    return gd, sd


def combined_consistency(M, colgroups, rhs):
    """Consistency of M C y = rhs where C sums the columns inside each group."""
    nR = len(M)
    A = []
    for i in range(nR):
        row = []
        for grp in colgroups:
            s = ZERO
            for c in grp:
                if M[i][c]:
                    s = s + M[i][c]
            row.append(s)
        row.append(rhs[i])
        A.append(row)
    nc = len(colgroups)
    r = 0
    for c in range(nc):
        p = next((i for i in range(r, nR) if A[i][c]), None)
        if p is None:
            continue
        A[r], A[p] = A[p], A[r]
        pv = A[r][c]
        A[r] = [t / pv for t in A[r]]
        for i in range(nR):
            if i != r and A[i][c]:
                f = A[i][c]
                A[i] = [A[i][t] - f * A[r][t] for t in range(nc + 1)]
        r += 1
        if r == nR:
            break
    inc = sum(1 for i in range(r, nR) if A[i][nc])
    return r, inc


def main():
    print("=" * 74)
    print("BAND 2: structured Gram families, and the calibration gate")
    print("=" * 74)

    sym2 = k4.build(verbose=False)
    rows2 = sym2["rows"]
    ng, ns, nl = (len(sym2["gvars"]), len(sym2["svars"]), len(sym2["lvars"]))
    M2 = gen2.build_matrix(sym2)
    bd1 = b1.Band()
    sym1 = bd1.sym

    print("\n[GATE] Corollary C2: band 1's law B1 lifted into the band-2 system")
    cols, rmap = band_bridge(sym1, sym2)
    print(f"  bridge injective on all 19 band-1 coordinates: True")
    print(f"  band-1 rows land on {len(set(rmap))} distinct band-2 rows "
          f"of {len(rows2)}")
    gate_ok = True
    for k in (2, 3):
        fs, _, _ = bd1.build(k)
        vals19 = bd1.vals19(("k", k), fs)
        x = lift(sym1, sym2, vals19)
        rhs2 = b2.rhs_rf(rows2, k)
        bad = residual(M2, x, rhs2)
        gate_ok = gate_ok and bad == 0
        print(f"  k = {k}: C2 lift of B1 violates {bad} of {len(rows2)} "
              f"band-2 rows over Q(n)")
    print(f"  GATE {'PASSED' if gate_ok else 'FAILED'} -- the family frame "
          f"reproduces band 1 inside band 2")

    print("\n[STRUCTURE] the degree grading of the band-2 Gram basis")
    tc = type_columns(sym2)
    for name, label in (("g", "sigma_0"), ("s", "sigma_11")):
        line = []
        for t in ((1, 1), (1, 2), (2, 2)):
            line.append(f"{t}: {len(tc.get((name, t), []))}")
        print(f"  {label:<10s} pair classes by (|u|,|v|)   " + "   ".join(line))

    print("\n[D1] design 1: switch the (1,2) blocks OFF (block diagonal by")
    print("     degree).  PD by construction iff both diagonal blocks are PD,")
    print("     and the (1,1) block IS band 1's Gram.")
    off = (tc.get(("g", (1, 2)), []) + tc.get(("s", (1, 2)), []))
    keep = [c for c in range(ng + ns + nl) if c not in set(off)]
    print(f"  columns switched off: {len(off)};  columns kept: {len(keep)}")
    d1_ok = True
    for k in (2, 3, 4, 5):
        rhs2 = b2.rhs_rf(rows2, k)
        rk, ninc, which = rank_and_consistency(M2, keep, rhs2)
        ok = ninc == 0
        d1_ok = d1_ok and ok
        print(f"  k = {k}: rank {rk} of 87 rows;  "
              f"{'CONSISTENT' if ok else f'INCONSISTENT ({ninc} rows)'}")
    print(f"  D1 {'SURVIVES' if d1_ok else 'FAILS'} the identity at every k "
          f"of the band")

    print("\n[BOUND] the degree filtration: a LOWER BOUND on any family")
    degs = row_degrees(sym2)
    hi_rows = [i for i, d in enumerate(degs) if d >= 4]
    low, high, lam = feeding_columns(sym2)
    print(f"  rows of degree >= 4: {len(hi_rows)} of {len(degs)}")
    print(f"  columns invisible to them (the (1,1) classes): {len(low)}")
    r_all = submatrix_rank(M2, hi_rows, low + high + lam)
    r_lam = submatrix_rank(M2, hi_rows, lam)
    r_low = submatrix_rank(M2, hi_rows, low)
    print(f"  rank of the degree->=4 rows on ALL columns        : {r_all}")
    print(f"  rank on the lambda columns alone                  : {r_lam}")
    print(f"  rank on the (1,1) columns alone                   : {r_low}"
          f"   (must be 0)")
    print(f"  => any consistent family needs at least {r_all - r_lam} free")
    print(f"     parameters in its (1,2)+(2,2) Gram part, whatever else it does")

    print("\n[D1s] design 1 refined: the (2,2) blocks a SCALAR multiple of the")
    print("      identity on the degree-2 basis -- a handful by construction")
    gd, sd = diagonal_classes(sym2)
    print(f"  diagonal (2,2) classes: sigma_0 {len(gd)}, sigma_11 {len(sd)}")
    groups = ([[c] for c in low] + [gd, sd] + [[c] for c in lam])
    print(f"  parameters: {len(groups)} "
          f"(14 band-1 classes + 2 scalars + 33 lambda)")
    for k in (4, 5):
        rhs2 = b2.rhs_rf(rows2, k)
        rk, inc = combined_consistency(M2, groups, rhs2)
        print(f"  k = {k}: rank {rk};  "
              f"{'CONSISTENT' if inc == 0 else f'INCONSISTENT ({inc} rows)'}")
    return gate_ok, d1_ok



if __name__ == "__main__":
    main()
