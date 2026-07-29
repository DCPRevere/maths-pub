"""
Find the 8 free variables as explicit rational functions of n, by FITTING a curve
through genuinely feasible points rather than searching an ansatz blindly.

Why this shape of attack.  Two things are now known:

  * the necessary-and-sufficient positivity conditions are the TEN quantities of
    blocks.py -- three sigma_0 eigenvalues and the leading principal minors of the
    four sigma_11 blocks.  Diagonal dominance is strictly weaker and provably
    fails on the already-verified certificates, so it is abandoned;
  * "all coefficients non-negative in m" is only a sufficient heuristic; positivity
    on m >= 0 is decided exactly by STURM, with no sufficiency gap.

The blocks make the feasibility problem TINY at every n: 8 unknowns, three linear
conditions and four PSD blocks of sizes 3, 1, 2, 1.  So we can solve it at many n
cheaply, obtain honestly feasible points, fit a low-degree rational curve through
them, and then check the curve exactly.  That replaces guessing an ansatz with
interpolating something that is known to exist.

The fitted curve is a CANDIDATE.  It becomes a proof only after the Sturm step in
sturm.py, which decides positivity of each of the ten numerators on m >= 0
exactly.
"""

import os
import sys
from fractions import Fraction as F

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "dittert"))
sys.path.insert(0, HERE)
import blocks as bl                                              # noqa: E402
import general_k3 as g                                           # noqa: E402

RES = g.solve_symbolic(verbose=False)
SYM = RES["sym"]
FREE = RES["free_cols"]
PIV = RES["piv_cols"]
IDX = bl.svar_index()
NFREE = len(FREE)


def affine_at(n):
    """
    Each of the 19 variables at this n as (constant, coefficients on the 8 free
    variables), in floating point.  Exact versions are used later; here we only
    need enough to pose a small SDP.
    """
    const = np.zeros(19)
    coef = np.zeros((19, NFREE))
    for t, c in enumerate(FREE):
        coef[c, t] = 1.0
    for i, c in enumerate(PIV):
        const[c] = float(RES["b"][i].at(F(n)))
        for t, fc in enumerate(FREE):
            a = RES["A"][i][fc]
            if a:
                coef[c, t] = -float(a.at(F(n)))
    return const, coef


class _Lin:
    """A tiny affine form (constant + coefficient vector) for building blocks."""

    __slots__ = ("c", "v")

    def __init__(self, c=0.0, v=None):
        self.c = float(c)
        self.v = np.zeros(NFREE) if v is None else v

    def __add__(self, o):
        if isinstance(o, _Lin):
            return _Lin(self.c + o.c, self.v + o.v)
        return _Lin(self.c + float(o), self.v.copy())

    __radd__ = __add__

    def __sub__(self, o):
        if isinstance(o, _Lin):
            return _Lin(self.c - o.c, self.v - o.v)
        return _Lin(self.c - float(o), self.v.copy())

    def __rsub__(self, o):
        return _Lin(float(o) - self.c, -self.v)

    def __mul__(self, s):
        s = float(s)
        return _Lin(self.c * s, self.v * s)

    __rmul__ = __mul__

    def __neg__(self):
        return _Lin(-self.c, -self.v)


def quantities_affine(n):
    """The ten positivity quantities as affine forms in the 8 free variables."""
    const, coef = affine_at(n)
    v = [_Lin(const[i], coef[i].copy()) for i in range(19)]
    a, b, c = v[0], v[1], v[2]
    eig = [a + b * (2 * (n - 1)) + c * ((n - 1) ** 2),
           a + b * (n - 2) - c * (n - 1),
           a - b * 2 + c]
    A, B, C, D = bl.blocks_rational_generic(float(n), v[3:14], IDX, one=1.0)
    return eig, A, B, C, D


def solve_small_sdp(n, verbose=False):
    """Maximise a scaled least-eigenvalue margin over the 8 free variables."""
    import cvxpy as cp
    eig, A, B, C, D = quantities_affine(n)
    x = cp.Variable(NFREE)
    t = cp.Variable()

    def lin(L):
        return L.c + L.v @ x

    # scale each condition so the margin means something comparable
    s_eig = float(n) ** -3
    cons = [lin(e) >= t * s_eig for e in eig]
    Amat = cp.bmat([[lin(A[i][j]) for j in range(3)] for i in range(3)])
    Cmat = cp.bmat([[lin(C[i][j]) for j in range(2)] for i in range(2)])
    sA = np.diag([float(n) ** -3, float(n) ** -1, 1.0])
    sC = np.diag([float(n) ** -3, float(n) ** -1])
    cons += [Amat - t * sA >> 0, Cmat - t * sC >> 0,
             lin(B) >= t * float(n) ** -1, lin(D) >= t * float(n) ** -3,
             t <= 1e3]
    prob = cp.Problem(cp.Maximize(t), cons)
    for solver in ("CLARABEL", "SCS"):
        try:
            prob.solve(solver=getattr(cp, solver), verbose=False)
            if prob.status in ("optimal", "optimal_inaccurate"):
                return np.array(x.value, dtype=float), float(t.value)
        except Exception:                                         # noqa: BLE001
            continue
    return None, None


def exact_quantities(n, free_vals):
    """The ten quantities EXACTLY over Q at rational free values."""
    n = F(n)
    vals = [F(0)] * 19
    for t, c in enumerate(FREE):
        vals[c] = free_vals[t]
    for i, c in enumerate(PIV):
        val = RES["b"][i].at(n)
        for t, fc in enumerate(FREE):
            a = RES["A"][i][fc]
            if a:
                val -= a.at(n) * vals[fc]
        vals[c] = val
    a, b, c = vals[0], vals[1], vals[2]
    out = list(zip(["G0.theta0", "G0.theta1", "G0.theta2"],
                   bl.sigma0_eigs_sym(a, b, c, n)))
    A, B, C, D = bl.blocks_rational(int(n), vals[3:14], IDX)
    import search_free as sf
    for i, mm in enumerate(sf.leading_minors(A)):
        out.append((f"H.A minor{i+1}", mm))
    out.append(("H.B", B))
    for i, mm in enumerate(sf.leading_minors(C)):
        out.append((f"H.C minor{i+1}", mm))
    out.append(("H.D", D))
    return out


def main():
    ns = list(range(4, 41))
    print("solving the small blocked SDP at each n (8 unknowns, cones 3,1,2,1)")
    pts = {}
    for n in ns:
        xv, tv = solve_small_sdp(n)
        if xv is None:
            print(f"  n={n}: SDP failed")
            continue
        pts[n] = xv
    print(f"  feasible points obtained at {len(pts)} values of n: "
          f"{min(pts)}..{max(pts)}")

    # confirm they really are feasible, exactly, at a few n
    print("\nexact re-check of the SDP points (rounded to rationals):")
    for n in (4, 8, 16, 32):
        if n not in pts:
            continue
        fv = [F(float(v)).limit_denominator(10 ** 9) for v in pts[n]]
        q = exact_quantities(n, fv)
        bad = [nm for nm, val in q if val <= 0]
        print(f"  n={n}: all ten positive? {not bad}"
              + (f"   violated: {bad}" if bad else ""))

    # fit f_c * (m+4)^E by a polynomial of degree D in m
    print("\nfitting f_c = u_c(m) / n^E with deg u_c <= D:")
    best = None
    for E in (4, 5, 6, 7):
        for D in (1, 2, 3, 4):
            us = []
            for t in range(NFREE):
                m = np.array([n - 4 for n in sorted(pts)], dtype=float)
                y = np.array([pts[n][t] * float(n) ** E for n in sorted(pts)])
                co = np.polyfit(m, y, D)[::-1]
                us.append(co)
            ok, worst = _check_curve(us, E, D, sorted(pts))
            tag = f"  E={E} D={D}: feasible on the fitted range? {ok}"
            if worst is not None:
                tag += f"   worst relative margin {worst:.3e}"
            print(tag)
            if ok and (best is None or worst > best[0]):
                best = (worst, E, D, us)
    if best is None:
        print("\nno (E, D) gave a curve feasible on the whole range")
        return
    worst, E, D, us = best
    print(f"\nbest: E={E}, D={D}, worst relative margin {worst:.3e}")
    np.save(os.path.join(HERE, "results", "fit_curve.npy"),
            np.array([np.pad(u, (0, D + 1 - len(u))) for u in us]))
    print("saved float coefficients to results/fit_curve.npy")
    for t in range(NFREE):
        terms = "  ".join(f"{us[t][j]:+.6g}*m^{j}" for j in range(len(us[t])))
        print(f"  f{FREE[t]:<2d} = ({terms}) / n^{E}")


def _check_curve(us, E, D, ns):
    worst = None
    for n in ns:
        m = n - 4
        fv = []
        for t in range(NFREE):
            val = sum(us[t][j] * m ** j for j in range(len(us[t])))
            fv.append(F(float(val / n ** E)).limit_denominator(10 ** 12))
        q = exact_quantities(n, fv)
        for nm, val in q:
            rel = float(val) * float(n) ** _norm_exp(nm)
            if worst is None or rel < worst:
                worst = rel
            if val <= 0:
                return False, worst
    return True, worst


def _norm_exp(name):
    return {"G0.theta0": 1, "G0.theta1": 1, "G0.theta2": 6,
            "H.A minor1": 3, "H.A minor2": 6, "H.A minor3": 9,
            "H.B": 1, "H.C minor1": 2, "H.C minor2": 5, "H.D": 3}.get(name, 3)


if __name__ == "__main__":
    main()
