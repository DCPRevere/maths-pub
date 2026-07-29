"""
End-to-end driver for the sub-Dittert certificate: solve, round to exact
rationals, verify independently.

Usage:  run.py <n> <k> [deg_basis]

A numerically satisfied SDP is NOT a proof (METHODS section 5).  What this script
produces is a claim; what makes it a theorem is:

  [2] the linear identity holding IDENTICALLY over Q after an exact correction,
  [3] both Gram matrices positive definite by exact rational LDL^T,
  [4] the certificate polynomial re-derived from scratch and compared with F
      COEFFICIENT BY COEFFICIENT (never by sampling),
  [5] mutation tests that must REJECT -- a verifier that never rejects proves
      nothing,

and, separately, results/verify_subdittert.py, which shares no code with this
pipeline.
"""

import itertools
import os
import pickle
import sys
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "dittert"))
sys.path.insert(0, HERE)  # HERE must win the name `expand` (see sos.py)
from exactsd import (assemble, is_symmetric, ldl_pivots,          # noqa: E402
                     round_and_correct)
from sos import build_sdp, solve, solve_blocked, transporters     # noqa: E402
from symmetry import act, monomials                               # noqa: E402


def independent_identity_check(d, xq, yq, zq):
    """Re-derive the certificate polynomial from scratch and compare with F.

    This does not reuse the constraint matrices at all: it multiplies out
    sigma_0 + sum_ij sigma_ij (1/n + b_ij) + lambda * sum b as monomials, and
    compares the whole dictionary with F.  Full coefficient comparison, no
    sampling.
    """
    n, B = d["n"], d["B"]
    N = n * n
    basis = d["basis"]
    G0 = assemble(B, d["g_orbits"], xq)
    H = assemble(B, d["s_orbits"], yq)
    trans = transporters(n, (0, 0))

    def mm(u, v):
        return tuple(sorted(u + v))

    rhs_poly = {}

    def addm(mono, c):
        if c:
            v = rhs_poly.get(mono, F(0)) + c
            if v:
                rhs_poly[mono] = v
            else:
                rhs_poly.pop(mono, None)

    for u in range(B):
        for v in range(B):
            c = G0[u][v]
            if c:
                addm(mm(basis[u], basis[v]), c)

    inv = F(1, n)
    for pk in range(N):
        g = trans[pk]
        gb = [act(g, m) for m in basis]
        for u in range(B):
            for v in range(B):
                c = H[u][v]
                if not c:
                    continue
                prod = mm(gb[u], gb[v])
                addm(prod, c * inv)
                addm(mm(prod, (pk,)), c)

    lam_mons = monomials(N, d["TOPDEG"] - 1)
    for vi, members in enumerate(d["lam_orbit_reps"]):
        c = zq[vi]
        if not c:
            continue
        for t in members:
            mu = lam_mons[t]
            for pk in range(N):
                addm(mm(mu, (pk,)), c)

    Fmono = {}
    for e, c in d["Fpoly"].items():
        mono = tuple(sorted(itertools.chain.from_iterable(
            [t] * et for t, et in enumerate(e) if et)))
        Fmono[mono] = Fmono.get(mono, F(0)) + c
    Fmono = {t: v for t, v in Fmono.items() if v}
    return rhs_poly == Fmono, len(rhs_poly), len(Fmono)


def results_dir():
    out = os.path.join(HERE, "results")
    os.makedirs(out, exist_ok=True)
    return out


def main(n, k, deg_basis=1):
    tag = f"n{n}k{k}d{deg_basis}"
    print("=" * 74)
    print(f"Cheon-Hwang sub-Dittert at (n,k) = ({n},{k}), "
          f"Gram basis degree {deg_basis}")
    print("=" * 74)

    numcache = os.path.join(results_dir(), f"subdittert_{tag}_numeric.pkl")
    d = build_sdp(n, k, deg_basis, verbose=True)
    if os.path.exists(numcache):
        with open(numcache, "rb") as fh:
            cached = pickle.load(fh)
        xv, yv, zv, tv = cached["x"], cached["y"], cached["z"], cached["t"]
        print(f"[1] SDP: reusing cached solution, margin t = {tv:.6e}")
    else:
        # Over the interior-point memory guard, block-diagonalise first
        # (METHODS section 7); below it, the monolithic program is fine.
        solver = solve_blocked if d["B"] > 200 else solve
        d, prob, x, y, z, t = solver(n, k, deg_basis, verbose=True, d=d)
        print(f"[1] SDP: status {prob.status}, margin t = {t.value:.6e}")
        if prob.status not in ("optimal", "optimal_inaccurate") or t.value <= 0:
            print("    no strictly feasible certificate of this shape; stopping")
            return False
        xv, yv, zv, tv = x.value, y.value, z.value, t.value
        with open(numcache, "wb") as fh:
            pickle.dump(dict(x=xv, y=yv, z=zv, t=tv), fh)
        print(f"    numerical solution cached to {os.path.basename(numcache)}")

    B = d["B"]
    xq = yq = zq = None
    for denom in (10 ** 4, 10 ** 6, 10 ** 8, 10 ** 10, 10 ** 12, 10 ** 14):
        cx, cy, cz, ok, maxdelta = round_and_correct(d, xv, yv, zv, denom)
        if not ok:
            print(f"[2] denominator {denom:.0e}: exact correction FAILED")
            continue
        G = assemble(B, d["g_orbits"], cx)
        H = assemble(B, d["s_orbits"], cy)
        if not (is_symmetric(G) and is_symmetric(H)):
            print(f"[2] denominator {denom:.0e}: assembled Gram not symmetric")
            continue
        pivG, badG = ldl_pivots(G)
        pivH, badH = ldl_pivots(H)
        if pivG is None or pivH is None:
            which = "G_0" if pivG is None else "H"
            bad = badG if pivG is None else badH
            print(f"[2] denominator {denom:.0e}: identity exact, but {which} "
                  f"lost definiteness at pivot {bad} "
                  f"(|correction| = {float(maxdelta):.3e})")
            continue
        xq, yq, zq = cx, cy, cz
        print(f"[2] denominator {denom:.0e}: identity EXACT over Q, "
              f"|correction| = {float(maxdelta):.3e}")
        print(f"[3] Gram matrices {B} x {B}: both POSITIVE DEFINITE by exact "
              f"rational LDL^T")
        print(f"    min pivot G_0 = {min(pivG)} = {float(min(pivG)):.6e}")
        print(f"    min pivot H   = {min(pivH)} = {float(min(pivH)):.6e}")
        break
    if xq is None:
        print("    no denominator gave an exactly-corrected, positive definite "
              "certificate; stopping")
        return False

    same, nr, nf = independent_identity_check(d, xq, yq, zq)
    print(f"[4] independent identity check by FULL coefficient comparison: "
          f"certificate {nr} monomials, F {nf} monomials -> "
          f"{'IDENTICAL' if same else '*** MISMATCH ***'}")

    print("[5] mutation tests (each must be REJECTED)")
    muts = []
    xbad = list(xq)
    xbad[0] += F(1, 10 ** 20)
    muts.append(("sigma_0 Gram coefficient +1e-20",
                 independent_identity_check(d, xbad, yq, zq)[0]))
    ybad = list(yq)
    ybad[0] += F(1, 10 ** 20)
    muts.append(("sigma_11 Gram coefficient +1e-20",
                 independent_identity_check(d, xq, ybad, zq)[0]))
    zbad = list(zq)
    zbad[0] += F(1, 10 ** 20)
    muts.append(("lambda multiplier coefficient +1e-20",
                 independent_identity_check(d, xq, yq, zbad)[0]))
    for name, accepted in muts:
        print(f"    {name}: "
              f"{'REJECTED (good)' if not accepted else 'ACCEPTED (BAD)'}")

    out = os.path.join(results_dir(), f"subdittert_{tag}.pkl")
    with open(out, "wb") as fh:
        pickle.dump(dict(n=n, k=k, deg_basis=deg_basis, xq=xq, yq=yq, zq=zq,
                         basis=d["basis"], g_orbits=d["g_orbits"],
                         s_orbits=d["s_orbits"],
                         lam_orbit_reps=d["lam_orbit_reps"], M=d["M"],
                         TOPDEG=d["TOPDEG"]), fh)
    print(f"\nsaved exact certificate to {out}")
    ncoef = len(xq) + len(yq) + len(zq)
    print(f"certificate size: {ncoef} rationals "
          f"({len(xq)} + {len(yq)} + {len(zq)})")

    ok = same and not any(a for _, a in muts)
    if ok:
        print("\n" + "=" * 74)
        print(f"VERDICT: sub-Dittert VERIFIED at (n,k) = ({n},{k}).")
        print(f"  E_{k}(r) + E_{k}(c) - P_{k}(A) <= {d['M']} "
              f"for every A in K_{n},")
        print(f"  with equality only at J_{n}/{n}.")
        print("=" * 74)
    return ok


if __name__ == "__main__":
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 4
    k = int(sys.argv[2]) if len(sys.argv) > 2 else 3
    db = int(sys.argv[3]) if len(sys.argv) > 3 else 1
    sys.exit(0 if main(n, k, db) else 1)
