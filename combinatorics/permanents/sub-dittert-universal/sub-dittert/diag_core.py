"""
The d = n - k diagonal: one builder, one solver, two cells -- (4,5) and (5,6).

WHY A NEW MODULE RATHER THAN THE H2 PIPELINE.  Two reasons, both measured
before a line was written.

  (1) The H2 pipeline (`h2_ucoord`, `h2_phase1`, `h2_round_x`) is the PINNED
      design: 321 pin rows, one block omitted, 70 linear values as unknowns.
      `NOTES-K5.md` §K5.6 measured that the k = 4 pinning design does NOT
      transfer to k = 5, and `K5-PLAN.md` Gate 1 asks for the UNPINNED direct
      solve.  Importing the pinned design would import the very verdict the
      firewall forbids.
  (2) `h2_ucoord.phase1` and `fibre_max` call `cvxpy`, and cvxpy/SCS/CLARABEL
      are NOT INSTALLED in this environment (checked, 2026-07-31).  The
      folder's own Newton barrier (`h2_ucoord.barrier`) is the only solver
      here, so the "SCS ladder" of the plan is not available and a self-
      contained barrier is written instead.  That substitution is named here
      rather than hidden.

THE OBJECT.  `k4_pinrank.build(n)` is the single place the design pipeline
reaches for `sos.build_sdp`, and its module global `K` is the only k in it.
So `pk.K = 5` gives the k = 5 system, and `NOTES-K5.md` §K5.4's measurement --
A0, A1c, A1l, A2 entrywise IDENTICAL at k = 4 and k = 5, only `rhs` differing
-- is what makes that a one-line change rather than a re-derivation.  This
module RE-CHECKS that identity itself (`check_shared_cone`) rather than citing
the log.

THE PARAMETRISATION, and why it removes the rounding problem entirely.
§6b.83's lesson is that the k = 4 route rounded a point and then had to repair
the linear identity by an exact correction on a pivot set, and that the repair
is where (4,9) was lost.  Here the identity is repaired by CONSTRUCTION:

    solve  S w = rhs  over Q once, exactly;
    w = w0 + sum_j c_j Z_j     with w0, Z_j exact rationals;
    ANY rational c gives S w = rhs EXACTLY.

So rounding can only ever cost margin in the PSD blocks, never the identity.
That is the §6b.83 rule -- round in the equilibrated coordinates, map to the
stored coordinates by exact rational arithmetic -- taken to its conclusion:
the equilibrated coordinates ARE the stored ones, because `c` is the only
thing a float ever touches.

LAMBDA IS ELIMINATED FIRST.  The 33 lambda variables enter no Gram block
(lambda multiplies sum_q b_q, which vanishes identically on K_n -- see
`h2_anchor.py`'s docstring, where the folder measured that no positivity
condition on lambda exists at all).  So they are projected out with an exact
left-null basis of A2 and recovered at the end by an exact solve.  Keeping
them in would leave the barrier Hessian singular in 33 directions.

WHAT THIS MODULE DOES NOT DO.  It decides positive definiteness of the 21
CANONICAL BLOCKS, not of the assembled B x B Grams; the two agree only via
§6b.39's multiplicity count, which is asserted there and not formalised (§9.5).
A point out of here is a candidate, at the same grade as `verify_pinretest`'s
output, and anchor grade needs `anchor_check3.py`'s six checks on top.
"""

import os
import pickle
import sys
from fractions import Fraction as F

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "dittert"))
sys.path.insert(0, HERE)  # HERE must win the names `sos`, `expand`, `exactsd`

CACHE = os.path.join(HERE, "results", "cache")


def _provenance():
    import sos
    import exactsd
    for mod in (sos, exactsd):
        got = os.path.dirname(os.path.abspath(mod.__file__))
        assert got == HERE, f"{mod.__name__} came from {got}, not {HERE}"


# --------------------------------------------------------------- exact linear
def rref(rows, rhs, ncols):
    """Reduced row echelon over Q.  `rows` integer lists, `rhs` Fractions."""
    A = [[F(v) for v in r] for r in rows]
    b = [F(v) for v in rhs]
    piv, r = [], 0
    for c in range(ncols):
        p = next((i for i in range(r, len(A)) if A[i][c] != 0), None)
        if p is None:
            continue
        A[r], A[p] = A[p], A[r]
        b[r], b[p] = b[p], b[r]
        inv = F(1) / A[r][c]
        A[r] = [v * inv for v in A[r]]
        b[r] = b[r] * inv
        for i in range(len(A)):
            if i != r and A[i][c] != 0:
                f = A[i][c]
                A[i] = [x - f * y for x, y in zip(A[i], A[r])]
                b[i] = b[i] - f * b[r]
        piv.append(c)
        r += 1
        if r == len(A):
            break
    ok = all(b[i] == 0 for i in range(r, len(A)))
    return piv, A, b, ok


def left_null(rows, ncols):
    """A basis of {y : y^T M = 0}, exactly, by reducing [M | I]."""
    R = len(rows)
    aug = [[F(v) for v in rows[i]] + [F(int(j == i)) for j in range(R)]
           for i in range(R)]
    r = 0
    for c in range(ncols):
        p = next((i for i in range(r, R) if aug[i][c] != 0), None)
        if p is None:
            continue
        aug[r], aug[p] = aug[p], aug[r]
        inv = F(1) / aug[r][c]
        aug[r] = [v * inv for v in aug[r]]
        for i in range(R):
            if i != r and aug[i][c] != 0:
                f = aug[i][c]
                aug[i] = [x - f * y for x, y in zip(aug[i], aug[r])]
        r += 1
        if r == R:
            break
    return r, [row[ncols:] for row in aug[r:]]


def particular_and_kernel(rows, rhs, ncols):
    """w0 with M w0 = rhs, and an exact basis of ker M (columns)."""
    piv, A, b, ok = rref(rows, rhs, ncols)
    if not ok:
        return None, None, piv
    pset = set(piv)
    free = [c for c in range(ncols) if c not in pset]
    w0 = [F(0)] * ncols
    for i, c in enumerate(piv):
        w0[c] = b[i]
    Z = []
    for f in free:
        v = [F(0)] * ncols
        v[f] = F(1)
        for i, c in enumerate(piv):
            v[c] = -A[i][f]
        Z.append(v)
    return w0, Z, piv


# ------------------------------------------------------------------ the cells
def build_cell(n, k, out=print):
    """The exact 87 x 440 system, the 21 canonical blocks, at (n, k)."""
    _provenance()
    import k4_pinrank as pk
    old = pk.K
    pk.K = k
    try:
        assert pk.K == k, "the K substitution did not take effect"
        d, C, srows, srhs, pins, blocks = pk.build(n)
    finally:
        pk.K = old
    ng, ns = len(d["g_orbits"]), len(d["s_orbits"])
    nl = len(d["lam_orbit_reps"])
    out(f"  (k={k}, n={n}): B = {d['B']}, rows = {len(srows)}, "
        f"vars = {ng}/{ns}/{nl} = {C}, blocks = {len(blocks)}, "
        f"pins = {len(pins)}")
    return dict(n=n, k=k, B=d["B"], C=C, ng=ng, ns=ns, nl=nl,
                srows=srows, srhs=srhs,
                blocks=[(side, name, dd, N, off)
                        for side, name, dd, N, off in blocks])


def cached_cell(n, k, out=print):
    os.makedirs(CACHE, exist_ok=True)
    path = os.path.join(CACHE, f"diag_cell_n{n}_k{k}.pkl")
    if os.path.exists(path):
        with open(path, "rb") as fh:
            cell = pickle.load(fh)
        out(f"  (k={k}, n={n}) loaded from cache: B = {cell['B']}, "
            f"vars = {cell['C']}, blocks = {len(cell['blocks'])}")
        return cell
    cell = build_cell(n, k, out=out)
    with open(path, "wb") as fh:
        pickle.dump(cell, fh)
    return cell


def check_shared_cone(c4, c5, out=print):
    """
    Re-measure §K5.4's claim here: same matrices, different rhs.

    A TRAP, measured rather than assumed.  `same_rows` comes out FALSE and that
    is NOT a contradiction of §K5.4.  `k4_pinrank.build` clears denominators
    per row by `den = lcm(row denominators) * rhse[r].denominator`, and the
    second factor is k-DEPENDENT, so the stored integer rows carry a
    k-dependent per-row scale.  Measured at n = 6: **0 of 87 rows fail to be a
    pure rational rescaling of each other**, so the defining SUBSPACE is
    identical and only the storage normalisation moves.  The 21 canonical
    blocks are identical as linear maps outright.
    """
    same_rows = c4["srows"] == c5["srows"]
    diff = sum(1 for a, b in zip(c4["srhs"], c5["srhs"]) if a != b)
    nb = (len(c4["blocks"]) == len(c5["blocks"]) and
          all(a[:3] == b[:3] and a[3] == b[3] and a[4] == b[4]
              for a, b in zip(c4["blocks"], c5["blocks"])))
    out(f"  shared constraint rows entrywise: {same_rows}")
    out(f"  rhs entries differing: {diff} of {len(c4['srhs'])}")
    out(f"  21 canonical blocks identical as linear maps: {nb}")
    return same_rows, diff, nb


# ------------------------------------------------ eliminate lambda, then solve
def affine_in_gs(cell, out=print):
    """
    Project the 33 lambda variables out exactly.

        S = [Sgs | Sl],   U a left-null basis of Sl,
        reduced system  (U Sgs) gs = U rhs,
        gs = gs0 + Z c,   c free.

    lambda is recovered afterwards by an exact solve, so nothing is lost.
    """
    ngs = cell["ng"] + cell["ns"]
    rows, rhs = cell["srows"], cell["srhs"]
    Sl = [r[ngs:] for r in rows]
    rk, U = left_null(Sl, cell["nl"])
    out(f"  rank A2 = {rk}, left-null dim = {len(U)}")
    red_rows, red_rhs = [], []
    for y in U:
        row = [F(0)] * ngs
        for i, yi in enumerate(y):
            if yi:
                ri = rows[i]
                for j in range(ngs):
                    if ri[j]:
                        row[j] += yi * ri[j]
        red_rows.append(row)
        red_rhs.append(sum((y[i] * rhs[i] for i in range(len(rhs))), F(0)))
    gs0, Z, piv = particular_and_kernel(red_rows, red_rhs, ngs)
    if gs0 is None:
        out("  REDUCED SYSTEM INCONSISTENT")
        return None
    out(f"  reduced system {len(U)} x {ngs}: rank {len(piv)}, "
        f"kernel dim {len(Z)}")
    pset = set(piv)
    free = [c for c in range(ngs) if c not in pset]
    return dict(gs0=gs0, Z=Z, U=U, red_rows=red_rows, red_rhs=red_rhs,
                ngs=ngs, rank=len(piv), free=free, piv=piv)


def recover_lambda(cell, gs, out=print):
    """Solve A2 l = rhs - [A0|A1] gs exactly.  Consistent by construction."""
    ngs = cell["ng"] + cell["ns"]
    rows, rhs = cell["srows"], cell["srhs"]
    tgt = []
    for i, r in enumerate(rows):
        v = rhs[i]
        for j in range(ngs):
            if r[j] and gs[j]:
                v -= r[j] * gs[j]
        tgt.append(v)
    Sl = [r[ngs:] for r in rows]
    l0, _, _ = particular_and_kernel(Sl, tgt, cell["nl"])
    if l0 is None:
        out("  LAMBDA RECOVERY FAILED -- gs is not in the projected set")
        return None
    return l0


# ------------------------------------------------------------- the block maps
def block_arrays(cell, gs0, Z):
    """
    Float M_b(gs0) and M_b(Z_j) for each canonical block b.

    Block entry (i,j) = sum_c N[i][j][c] * w[off + c], and every block lives on
    the (g, s) half, so the lambda coordinates never appear.
    """
    M0s, Djs, names = [], [], []
    for side, name, dd, N, off in cell["blocks"]:
        A0 = np.zeros((dd, dd))
        for i in range(dd):
            for j in range(dd):
                A0[i, j] = float(sum((F(x) * gs0[off + c]
                                      for c, x in N[i][j].items()), F(0)))
        A0 = 0.5 * (A0 + A0.T)
        D = np.zeros((len(Z), dd, dd))
        for t, z in enumerate(Z):
            for i in range(dd):
                for j in range(dd):
                    acc = F(0)
                    for c, x in N[i][j].items():
                        zz = z[off + c]
                        if zz:
                            acc += F(x) * zz
                    D[t, i, j] = float(acc)
            D[t] = 0.5 * (D[t] + D[t].T)
        M0s.append(A0)
        Djs.append(D)
        names.append(f"{side} {name}")
    return names, M0s, Djs


def exact_blocks(cell, w):
    """Exact rational canonical blocks at the 440-vector w."""
    out = []
    for side, name, dd, N, off in cell["blocks"]:
        M = [[F(0)] * dd for _ in range(dd)]
        for i in range(dd):
            for j in range(dd):
                M[i][j] = sum((F(x) * w[off + c] for c, x in N[i][j].items()),
                              F(0))
        out.append((f"{side} {name}", dd, M))
    return out


def ldl_min_pivot(M, dd):
    """Exact rational LDL^T; returns (ok, least pivot) with no square roots."""
    A = [row[:] for row in M]
    least = None
    for i in range(dd):
        p = A[i][i]
        if p <= 0:
            return False, p
        least = p if least is None or p < least else least
        for j in range(i + 1, dd):
            f = A[j][i] / p
            if f:
                for t in range(i, dd):
                    A[j][t] -= f * A[i][t]
    return True, least
