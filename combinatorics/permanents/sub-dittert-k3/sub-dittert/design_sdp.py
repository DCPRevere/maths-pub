"""
The design step as a CONVEX semidefinite program.

The key observation, which makes the earlier searching unnecessary.  Put

    f_c = u_c(m) / n^E ,   m = n - 4 ,   deg u_c <= D ,

with the coefficients of u_c as unknowns.  Then f_c is a LINEAR function of those
unknowns; the pivot variables are affine in the f_c; and the four sigma_11 blocks
and the three sigma_0 eigenvalues are affine in the variables.  So for any FIXED n
the condition "all blocks positive definite" is a linear matrix inequality in the
unknown coefficients.  Imposing it on a grid of n is therefore a single CONVEX
semidefinite program -- no ansatz search, no dominance, no non-negative
coefficient requirement, and no local optima.

Two earlier failures are explained by this:
  * diagonal dominance is a strictly weaker sufficient condition and provably
    fails on the verified certificates, so any LP built on it was doomed;
  * least-squares fitting through SDP optima optimises the wrong thing -- it
    minimises squared error rather than maximising the margin, and at E=4, D=3 it
    missed feasibility by only 0.19 in relative margin.

The grid only serves to FIND the coefficients.  The proof for ALL n is the Sturm
step in sturm.py: once u is fixed as exact rationals, each of the ten positivity
quantities is an exact rational function of m, and Sturm decides positivity on
m >= 0 with no sufficiency gap whatever.
"""

import os
import sys
from fractions import Fraction as F

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "dittert"))
sys.path.insert(0, HERE)
import blocks as bl                                              # noqa: E402
import fit_curve as fc                                           # noqa: E402
import general_k3 as g                                           # noqa: E402

RES = fc.RES
FREE = fc.FREE
PIV = fc.PIV
IDX = fc.IDX
NFREE = fc.NFREE


def solve(E=4, D=3, ns=None, verbose=True):
    import cvxpy as cp
    if ns is None:
        ns = list(range(4, 61)) + [70, 80, 100, 120, 150, 200]
    u = cp.Variable((NFREE, D + 1), name="u")
    t = cp.Variable(name="t")
    cons = [t <= 10.0]

    refs = {}
    for n in ns:
        xv, _ = fc.solve_small_sdp(n)
        if xv is None:
            continue
        refs[n] = xv

    for n in ns:
        if n not in refs:
            continue
        m = float(n - 4)
        # f_c as a linear expression in u
        powers = np.array([m ** j for j in range(D + 1)]) / float(n) ** E
        f = u @ powers                                    # length NFREE
        const, coef = fc.affine_at(n)
        vals = [const[i] + coef[i] @ f for i in range(19)]

        a, b, c = vals[0], vals[1], vals[2]
        eig = [a + 2 * (n - 1) * b + (n - 1) ** 2 * c,
               a + (n - 2) * b - (n - 1) * c,
               a - 2 * b + c]
        A, B, C, Dblk = bl.blocks_rational_generic(float(n), vals[3:14], IDX,
                                                   one=1.0)
        # reference scales, from a genuinely feasible point at this n
        rv = _vals_at(n, refs[n])
        rA, rB, rC, rD = bl.blocks_rational(n, [F(float(x)).limit_denominator(
            10 ** 9) for x in rv[3:14]], IDX)
        sA = np.diag([abs(float(rA[i][i])) for i in range(3)])
        sC = np.diag([abs(float(rC[i][i])) for i in range(2)])
        reig = [abs(float(x)) for x in bl.sigma0_eigs_sym(
            F(float(rv[0])).limit_denominator(10 ** 9),
            F(float(rv[1])).limit_denominator(10 ** 9),
            F(float(rv[2])).limit_denominator(10 ** 9), F(n))]

        for e, s in zip(eig, reig):
            cons.append(e >= t * s)
        cons.append(cp.bmat([[A[i][j] for j in range(3)]
                             for i in range(3)]) - t * sA >> 0)
        cons.append(cp.bmat([[C[i][j] for j in range(2)]
                             for i in range(2)]) - t * sC >> 0)
        cons.append(B >= t * abs(float(rB)))
        cons.append(Dblk >= t * abs(float(rD)))

    prob = cp.Problem(cp.Maximize(t), cons)
    for solver in ("CLARABEL", "SCS"):
        try:
            prob.solve(solver=getattr(cp, solver), verbose=False)
            if prob.status in ("optimal", "optimal_inaccurate"):
                break
        except Exception:                                         # noqa: BLE001
            continue
    if verbose:
        print(f"  E={E} D={D}: status {prob.status}, t = {t.value}")
    if prob.status not in ("optimal", "optimal_inaccurate") or t.value is None:
        return None, None
    return np.array(u.value, dtype=float), float(t.value)


def _vals_at(n, free_vals):
    const, coef = fc.affine_at(n)
    return np.array([const[i] + coef[i] @ np.asarray(free_vals)
                     for i in range(19)])


def rational_curve(u, E, D, denom):
    """Round the coefficients to rationals with the given denominator."""
    return [[F(int(round(u[t][j] * denom)), denom) for j in range(D + 1)]
            for t in range(NFREE)]


def free_at(uq, E, n):
    """The 8 free variables at this n, exactly over Q."""
    m = F(n - 4)
    return [sum(uq[t][j] * m ** j for j in range(len(uq[t]))) / F(n) ** E
            for t in range(NFREE)]


def check_exact(uq, E, ns):
    bad = []
    for n in ns:
        q = fc.exact_quantities(n, free_at(uq, E, n))
        for nm, v in q:
            if v <= 0:
                bad.append((n, nm, v))
    return bad


if __name__ == "__main__":
    best = None
    for E in (3, 4, 5):
        for D in (2, 3, 4):
            u, t = solve(E, D)
            if u is not None and t is not None and t > 0:
                if best is None or t > best[1]:
                    best = (u, t, E, D)
    if best is None:
        print("\nno (E, D) gave a strictly feasible SDP")
        sys.exit(1)
    u, t, E, D = best
    print(f"\nbest: E={E}, D={D}, margin t = {t:.6f}")
    test_ns = list(range(4, 121))
    for denom in (10, 100, 1000, 10 ** 4, 10 ** 5, 10 ** 6, 10 ** 7, 10 ** 8):
        uq = rational_curve(u, E, D, denom)
        bad = check_exact(uq, E, test_ns)
        print(f"  denominator {denom:>9}: exact check on n = 4..120 -> "
              f"{'ALL TEN POSITIVE' if not bad else f'{len(bad)} violations'}")
        if not bad:
            out = os.path.join(HERE, "results", f"curve_E{E}_D{D}.txt")
            with open(out, "w") as fh:
                fh.write(f"E={E}\nD={D}\ndenominator={denom}\n")
                for tt in range(NFREE):
                    fh.write(f"f{FREE[tt]} = ("
                             + " + ".join(f"{uq[tt][j]}*m^{j}"
                                          for j in range(D + 1))
                             + f") / n^{E}\n")
            print(f"  saved to {out}")
            for tt in range(NFREE):
                terms = " + ".join(f"({uq[tt][j]})*m^{j}" for j in range(D + 1))
                print(f"    f{FREE[tt]:<2d} = [{terms}] / n^{E}")
            break
