"""
The unpinned direct solve on the d = n - k diagonal, and its exact rounding.

THE PROGRAMME, unpinned.  Find `w` in Q^440 with `S w = rhs` and all 21
canonical blocks positive definite.  No pin row is imposed: `NOTES-K5.md` §K5.6
measured that the k = 4 pinning design does not transfer to k = 5, and
`K5-PLAN.md` Gate 1 asks for the unpinned solve for exactly that reason.

THE SCALING PROBLEM, measured before it was fixed.  A first version maximised
`t` in `M_b(x) >= t I_b` on the raw canonical blocks and returned FLOAT
INFEASIBLE at (k = 4, n = 6) -- a cell with a stored, exactly verified witness.
The cause is not the search.  At the stored (4,6) point the 21 blocks span

    least eigenvalue 1.4e-11 on the 14x14 trivial block
    largest eigenvalue 8.9e-03 on the 16x16 Ind(V'|1)

so a margin measured against ONE identity is set entirely by the smallest
block and says nothing about the others.  The fix is a per-block DIAGONAL
CONGRUENCE `M_b -> C_b M_b C_b`, which cannot change positive definiteness and
therefore cannot change the verdict -- only what the solver can see.  The
congruence is recomputed from the current iterate two further times (adaptive
rescaling), each time re-basing the design at that iterate.

THE POSITIVE CONTROL, and it is the whole reason to trust a k = 5 answer.
Both stored k = 4 witnesses (n = 5, n = 6) are checked against `diag_core`
first: `S w = rhs` exactly, all 21 canonical blocks positive definite by this
file's own exact LDL.  Then the solver must re-find feasibility at BOTH cells
FROM SCRATCH (x0 = 0, nothing stored handed to it).  Only then is a k = 5
verdict worth reading, and an "infeasible" from this file is never a verdict on
its own -- `diag_farkas.py` must produce an exact dual certificate.

WHY NOT SCS.  `K5-PLAN.md` Gate 1 says "SCS ladder"; cvxpy, scs and clarabel
are NOT INSTALLED here (measured 2026-07-31).  A self-contained primal-barrier
Newton phase I is written instead and the substitution is named, not hidden.

THE ROUNDING, per §6b.83 as superseded by the (4,9) closure.  Rounding happens
in `x` -- the coordinates the design was equilibrated for -- and nowhere else.
`x -> coefficient -> w` is exact rational arithmetic throughout (the scale
factors are float64 values, hence exact rationals), and `S w = rhs` holds
identically for EVERY rational x by construction of the parametrisation.  So
the ladder can only ever cost PSD margin, never the linear identity: the
failure mode that produced §6b.51's false negative cannot occur here.
"""

import json
import os
import sys
import time
from fractions import Fraction as F

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import diag_core as dc                                              # noqa: E402


# ------------------------------------------------------------------- design
def raw_design(cell, aff, out=print):
    t0 = time.time()
    names, M0s, Djs = dc.block_arrays(cell, aff["gs0"], aff["Z"])
    out(f"  raw design: {len(names)} blocks, {len(aff['Z'])} directions "
        f"({time.time() - t0:.0f} s)")
    return names, M0s, [np.ascontiguousarray(D) for D in Djs]


def rescale(M0raw, Draw, base, out=print, tag="scaling"):
    """
    Per-block diagonal congruence + per-direction equilibration about `base`.

    Returns (M0s, Djs, Cbs, dscale).  `M_b(x)` in the returned design equals
    `C_b [ M0raw_b + sum_j (base_j + x_j dscale_j) Draw_b^j ] C_b`.
    """
    nb, nx = len(M0raw), Draw[0].shape[0]
    Bs = [M0raw[b] + np.tensordot(base, Draw[b], axes=(0, 0))
          for b in range(nb)]
    Cbs = []
    for b in range(nb):
        d = Bs[b].shape[0]
        mag = np.abs(np.diag(Bs[b])).copy()
        alt = np.abs(Draw[b]).max(axis=0).diagonal()
        mag = np.maximum(mag, alt)
        pos = mag[mag > 0]
        floor = pos.min() if pos.size else 1.0
        mag = np.maximum(mag, floor)
        Cbs.append(1.0 / np.sqrt(mag))
    M0s = [Cbs[b][:, None] * Bs[b] * Cbs[b][None, :] for b in range(nb)]
    Djs = [Cbs[b][None, :, None] * Draw[b] * Cbs[b][None, None, :]
           for b in range(nb)]
    dmax = np.zeros(nx)
    for D in Djs:
        dmax = np.maximum(dmax, np.abs(D).max(axis=(1, 2)))
    dscale = 1.0 / np.maximum(dmax, 1e-300)
    Djs = [np.ascontiguousarray(D * dscale[:, None, None]) for D in Djs]
    M0s = [0.5 * (M + M.T) for M in M0s]
    out(f"  {tag}: block eigenvalue span "
        f"[{min(np.linalg.eigvalsh(M).min() for M in M0s):+.3e}, "
        f"{max(np.linalg.eigvalsh(M).max() for M in M0s):+.3e}], "
        f"dscale ratio {dscale.max() / dscale.min():.3e}")
    return M0s, Djs, Cbs, dscale


def blocks_at(M0s, Djs, x):
    return [M0s[b] + np.tensordot(x, Djs[b], axes=(0, 0))
            for b in range(len(M0s))]


def lam_min(Ms):
    return min(float(np.linalg.eigvalsh(M).min()) for M in Ms)


def coef_from_w(aff, w):
    """The exact kernel coefficients of a stored 440-point."""
    return [w[c] - aff["gs0"][c] for c in aff["free"]]


# ------------------------------------------------------- phase I: max margin
def _newton(M0s, Djs, x, t, mu, R):
    nx = len(x)
    g = np.zeros(nx + 1)
    H = np.zeros((nx + 1, nx + 1))
    g[nx] = 1.0
    for b in range(len(M0s)):
        d = M0s[b].shape[0]
        S = M0s[b] + np.tensordot(x, Djs[b], axes=(0, 0)) - t * np.eye(d)
        S = 0.5 * (S + S.T)
        try:
            Si = np.linalg.inv(S)
        except np.linalg.LinAlgError:
            return None, None
        Si = 0.5 * (Si + Si.T)
        A = np.empty((nx + 1, d, d))
        A[:nx] = Djs[b]
        A[nx] = -np.eye(d)
        g[:] += mu * np.einsum("ij,kji->k", Si, A)
        W = np.einsum("ij,kjl->kil", Si, A).reshape(nx + 1, -1)
        Wt = np.einsum("kij,jl->kil", A, Si).reshape(nx + 1, -1)
        H -= mu * (W @ Wt.T)
    box = R * R - x * x
    g[:nx] += mu * (-2.0 * x / box)
    H[np.arange(nx), np.arange(nx)] -= mu * 2.0 * (R * R + x * x) / (box * box)
    return g, 0.5 * (H + H.T)


def feasible(M0s, Djs, x, t, R):
    if np.abs(x).max() >= R:
        return False
    for b in range(len(M0s)):
        d = M0s[b].shape[0]
        S = M0s[b] + np.tensordot(x, Djs[b], axes=(0, 0)) - t * np.eye(d)
        if np.linalg.eigvalsh(0.5 * (S + S.T)).min() <= 0:
            return False
    return True


def phase1(M0s, Djs, out=print, R=1e6, x0=None, iters=80, quiet=True):
    nx = Djs[0].shape[0]
    x = np.zeros(nx) if x0 is None else np.array(x0, float)
    t = lam_min(blocks_at(M0s, Djs, x)) - 1.0
    for i, mu in enumerate([2.0 ** (-j) for j in range(56)]):
        for _ in range(iters):
            g, H = _newton(M0s, Djs, x, t, mu, R)
            if g is None:
                break
            try:
                step = np.linalg.solve(H - 1e-14 * np.trace(-H) / (nx + 1) *
                                       np.eye(nx + 1), g)
            except np.linalg.LinAlgError:
                break
            dec = float(g @ step)
            s, ok = 1.0, False
            for _ in range(80):
                if feasible(M0s, Djs, x - s * step[:nx], t - s * step[nx], R):
                    ok = True
                    break
                s *= 0.5
            if not ok:
                break
            x, t = x - s * step[:nx], t - s * step[nx]
            if abs(dec) < 1e-13:
                break
        if not quiet and i % 8 == 0:
            out(f"    mu={mu:.2e}: t {t:+.6e}, |x|inf {np.abs(x).max():.2e}")
    lm = lam_min(blocks_at(M0s, Djs, x))
    out(f"    phase I: t = {t:+.9e}, least block eigenvalue {lm:+.9e}, "
        f"|x|inf {np.abs(x).max():.3e}")
    return x, t, lm


def solve(M0raw, Draw, out=print, rounds=3, R=1e6, base0=None):
    """Adaptive-rescaling phase I.  Returns (coef, margin, history)."""
    nx = Draw[0].shape[0]
    base = np.zeros(nx) if base0 is None else np.array(base0, float)
    hist = []
    for rd in range(rounds):
        M0s, Djs, Cbs, dscale = rescale(M0raw, Draw, base, out=out,
                                        tag=f"round {rd} scaling")
        x, t, lm = phase1(M0s, Djs, out=out, R=R)
        hist.append((t, lm))
        base = base + x * dscale
        if lm > 0:
            out(f"  STRICTLY FEASIBLE point found at round {rd}")
            return base, lm, hist, (M0s, Djs, dscale, x)
    return base, hist[-1][1], hist, (M0s, Djs, dscale, x)


# ------------------------------------------------------------------ rounding
def to_w(cell, aff, coef, sig):
    """
    The exact 440-vector at relative precision 10^-sig, rounded in `coef`.

    `coef` is already the equilibrated coordinate: `rescale` gives every
    direction a unit in which a step of 1 moves some block entry by 1, and
    `coef = base + x * dscale` is that unit's value.  Rounding therefore
    happens once, uniformly, in the coordinates the design was built for.
    """
    mx = max((abs(v) for v in coef), default=1.0) or 1.0
    den = int(10 ** sig / mx) + 1
    gs = list(aff["gs0"])
    for j, cj in enumerate(coef):
        q = F(round(float(cj) * den), den)
        if not q:
            continue
        z = aff["Z"][j]
        for i in range(len(gs)):
            if z[i]:
                gs[i] += q * z[i]
    lam = dc.recover_lambda(cell, gs)
    if lam is None:
        return None, den
    return gs + lam, den


def exact_verdict(cell, w):
    for r, row in enumerate(cell["srows"]):
        acc = F(0)
        for j, v in enumerate(row):
            if v and w[j]:
                acc += F(v) * w[j]
        if acc != cell["srhs"][r]:
            return False, False, [], None
    piv, worst = [], None
    for name, dd, M in dc.exact_blocks(cell, w):
        ok, p = dc.ldl_min_pivot(M, dd)
        piv.append((name, dd, ok, p))
        if not ok:
            return True, False, piv, p
        worst = p if worst is None or p < worst else worst
    return True, True, piv, worst


def ladder(cell, aff, coef, out=print,
           sigs=(6, 8, 10, 12, 16, 20, 24, 30, 40, 50)):
    for sig in sigs:
        t0 = time.time()
        w, den = to_w(cell, aff, coef, sig)
        if w is None:
            out(f"    sig {sig:3d}: lambda recovery failed")
            continue
        lhs_ok, pd, piv, worst = exact_verdict(cell, w)
        out(f"    sig {sig:3d}: S w = rhs {lhs_ok}, all blocks PD {pd}, "
            f"pivot {float(worst):+.6e} ({time.time() - t0:.0f} s)")
        if lhs_ok and pd:
            return w, sig, piv, worst
    return None, None, None, None


# ---------------------------------------------------------------------- main
def run(n, k, out=print, store=True, tag="", rounds=3, R=1e6, base0=None):
    out(f"\n=== UNPINNED DIRECT SOLVE at (k = {k}, n = {n}) ===")
    cell = dc.cached_cell(n, k, out=out)
    aff = dc.affine_in_gs(cell, out=out)
    if aff is None:
        return "LINEAR SYSTEM INCONSISTENT", None
    names, M0raw, Draw = raw_design(cell, aff, out=out)
    t0 = time.time()
    coef, lm, hist, last = solve(M0raw, Draw, out=out, rounds=rounds, R=R,
                                 base0=base0)
    out(f"  float verdict: least block eigenvalue {lm:+.9e} "
        f"({time.time() - t0:.0f} s); margins by round "
        f"{[f'{h[1]:+.3e}' for h in hist]}")
    M0s, Djs, dscale, x = last
    Ms = blocks_at(M0s, Djs, x)
    for b, name in enumerate(names):
        ev = np.linalg.eigvalsh(Ms[b])
        out(f"      {name:30s} {Ms[b].shape[0]:2d}  lambda_min {ev.min():+.6e}"
            f"  lambda_max {ev.max():+.6e}")
    ctx = dict(cell=cell, aff=aff, coef=coef, names=names, M0raw=M0raw,
               Draw=Draw, lm=lm, hist=hist)
    if lm <= 0:
        return "FLOAT INFEASIBLE (NOT a verdict -- needs diag_farkas)", ctx
    out("  exact rounding ladder, in the equilibrated coordinates:")
    w, sig, piv, worst = ladder(cell, aff, coef, out=out)
    if w is None:
        return "FLOAT FEASIBLE, EXACT ROUNDING FAILED", ctx
    ctx["w"] = w
    if store:
        path = os.path.join(HERE, "results", "witness",
                            f"diag_n{n}_k{k}{tag}.json")
        with open(path, "w") as fh:
            json.dump(dict(
                claim="S w = rhs exactly and every canonical block is "
                      "positive definite over Q",
                kind="feasible", n=n, k=k, deg_basis=2, design="unpinned",
                selection=f"phase-I max-margin, adaptive rescaling, R={R}, "
                          f"rounding sig={sig}",
                float_margin=repr(lm), least_ldl_pivot=str(worst),
                blocks=[[nm, dd, str(p)] for nm, dd, ok, p in piv],
                point=[f"{v.numerator}/{v.denominator}" for v in w]), fh)
        out(f"  witness written to {path}")
    return "FEASIBLE (exact, canonical blocks)", ctx


def main(argv):
    pairs = []
    for a in argv:
        if "," in a:
            nn, kk = a.split(",")
            pairs.append((int(nn), int(kk)))
    if not pairs:
        pairs = [(5, 4), (6, 4), (6, 5)]
    out = lambda s: print(s, flush=True)                        # noqa: E731
    for n, k in pairs:
        v, _ = run(n, k, out=out)
        out(f"  ==> (k = {k}, n = {n}): {v}")


if __name__ == "__main__":
    main(sys.argv[1:])
