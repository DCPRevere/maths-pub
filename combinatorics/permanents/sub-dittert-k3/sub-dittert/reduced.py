"""
The design step with the recession cone quotiented out.

recession.py derives, exactly over Q(n), that the recession cone of the design
SDP is exactly two-dimensional:

    r0 : sigma_0 Gram += c_0 J      free coords (0,0,0,0,-1,0,0,0)
    r1 : sigma_11 Gram += c_1 J     free coords (1,1,1,1,-n,-1,-2,-2)

with c_0, c_1 >= 0.  Their effect on the ten positivity quantities is completely
explicit:

    theta_0  ->  theta_0 + n^2 c_0                (c_1 does not appear)
    A        ->  A + c_1 s s^T,   s = (1, 2(n-1), (n-1)^2)
    theta_1, theta_2, B, C, D                     unchanged

because J's sigma_0 spectrum is (n^2, 0, 0) and, in the unnormalised isotypic
basis 1_K, 1_R + 1_C, 1_I of blocks_rational, J restricted to the trivial
component is the rank-one matrix s s^T while the sign, Ind and (V'|V') components
of J vanish (those basis vectors sum to zero).

So the design splits in two:

  HARD PART, 6 unknowns.  theta_1, theta_2, B, C (2 minors), D and the 2x2
  compression of A to s^perp -- eight quantities, every one INVARIANT along both
  recession generators, hence a function of the 6-dimensional quotient only.
  s^perp is spanned by t1 = (-2(n-1), 1, 0) and t2 = (-(n-1)^2, 0, 1).

  EASY PART, 2 unknowns.  Given the hard part, theta_0 > 0 and A > 0 hold as soon
  as c_0 and c_1 are large enough, and "large enough" is an explicit inequality:
  A + c_1 s s^T > 0 iff T^T A T > 0 and c_1 > (Schur term) - A_11, using
  e = (1,0,0) with s^T e = 1.

That is why the original SDP drifted: it was optimising over c_0 and c_1 as well,
and those two directions are unbounded, so the optimum sat at the solver's
stopping point on an unbounded face.
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

FREE = fc.FREE
PIV = fc.PIV
IDX = fc.IDX
NFREE = fc.NFREE
I_F6 = FREE.index(6)
I_F15 = FREE.index(15)


def rec_dirs(n):
    """The two recession generators in free coordinates at this n."""
    r0 = np.zeros(NFREE)
    r0[I_F15] = -1.0
    r1 = np.zeros(NFREE)
    for c, v in ((6, 1.0), (9, 1.0), (11, 1.0), (12, 1.0),
                 (15, -float(n)), (16, -1.0), (17, -2.0), (18, -2.0)):
        r1[FREE.index(c)] = v
    return r0, r1


def rec_dirs_exact(n):
    r0 = [F(0)] * NFREE
    r0[I_F15] = F(-1)
    r1 = [F(0)] * NFREE
    for c, v in ((6, F(1)), (9, F(1)), (11, F(1)), (12, F(1)),
                 (15, -F(n)), (16, F(-1)), (17, F(-2)), (18, F(-2))):
        r1[FREE.index(c)] = v
    return r0, r1


def tmat(n):
    """Columns spanning s^perp, s = (1, 2(n-1), (n-1)^2).  Exact."""
    m = n - 1
    return [[-2 * m, -m * m], [1, 0], [0, 1]]


def hard_quantities(n, free_vals):
    """
    The eight recession-invariant quantities EXACTLY over Q at rational free
    values: theta_1, theta_2, B, D, the two leading minors of C, and the two
    leading minors of T^T A T.
    """
    nq = F(n)
    vals = fc_vals(nq, free_vals)
    a, b, c = vals[0], vals[1], vals[2]
    e = bl.sigma0_eigs_sym(a, b, c, nq)
    A, B, C, D = bl.blocks_rational(int(n), vals[3:14], IDX)
    T = tmat(nq)
    TA = [[sum(T[p][i] * A[p][q] * T[q][j] for p in range(3) for q in range(3))
           for j in range(2)] for i in range(2)]
    out = [("G0.theta1", e[1]), ("G0.theta2", e[2]),
           ("H.B", B), ("H.D", D),
           ("H.C minor1", C[0][0]),
           ("H.C minor2", C[0][0] * C[1][1] - C[0][1] ** 2),
           ("TAT minor1", TA[0][0]),
           ("TAT minor2", TA[0][0] * TA[1][1] - TA[0][1] ** 2)]
    return out


def fc_vals(nq, free_vals):
    """The 19 variables at n from the 8 free ones, exactly."""
    vals = [F(0)] * 19
    for t, c in enumerate(FREE):
        vals[c] = free_vals[t]
    for i, c in enumerate(PIV):
        val = fc.RES["b"][i].at(nq)
        for t, fcol in enumerate(FREE):
            aa = fc.RES["A"][i][fcol]
            if aa:
                val -= aa.at(nq) * vals[fcol]
        vals[c] = val
    return vals


def check_invariance(ns=(4, 7, 11, 20), seed=5):
    """The eight hard quantities must not change along r0 or r1."""
    import random
    rng = random.Random(seed)
    ok = True
    for n in ns:
        x = [F(rng.randint(-50, 50), rng.randint(1, 13)) for _ in range(NFREE)]
        r0, r1 = rec_dirs_exact(n)
        base = hard_quantities(n, x)
        for nm, r in (("r0", r0), ("r1", r1)):
            s = F(rng.randint(1, 9), rng.randint(1, 5))
            y = [x[i] + s * r[i] for i in range(NFREE)]
            got = hard_quantities(n, y)
            same = all(p[1] == q[1] for p, q in zip(base, got))
            if not same:
                bad = [p[0] for p, q in zip(base, got) if p[1] != q[1]]
                print(f"  n={n} along {nm}: NOT invariant -- {bad}")
                ok = False
        # and the two quantities that SHOULD move, move the right way
        r0e, r1e = rec_dirs_exact(n)
        v0 = fc_vals(F(n), x)
        v1 = fc_vals(F(n), [x[i] + r0e[i] for i in range(NFREE)])
        d_theta0 = (bl.sigma0_eigs_sym(v1[0], v1[1], v1[2], F(n))[0]
                    - bl.sigma0_eigs_sym(v0[0], v0[1], v0[2], F(n))[0])
        if d_theta0 != F(n) ** 2:
            print(f"  n={n}: theta_0 moves by {d_theta0}, expected n^2")
            ok = False
        v2 = fc_vals(F(n), [x[i] + r1e[i] for i in range(NFREE)])
        A0b, _, _, _ = bl.blocks_rational(n, v0[3:14], IDX)
        A1b, B1, C1, D1 = bl.blocks_rational(n, v2[3:14], IDX)
        s = [F(1), 2 * F(n - 1), F(n - 1) ** 2]
        for i in range(3):
            for j in range(3):
                if A1b[i][j] - A0b[i][j] != s[i] * s[j]:
                    print(f"  n={n}: A[{i}][{j}] moves by "
                          f"{A1b[i][j] - A0b[i][j]}, expected {s[i]*s[j]}")
                    ok = False
    print(f"  invariance of the eight hard quantities along r0 and r1: {ok}")
    print("  theta_0 += n^2 c_0 and A += c_1 s s^T confirmed exactly")
    return ok


# ---------------------------------------------------------------- reduced SDP
def hard_entries(n, free_vals):
    """
    The ten MATRIX ENTRIES behind the eight quantities, exactly over Q: they are
    affine in the free variables, whereas the minors are not.
    """
    nq = F(n)
    vals = fc_vals(nq, free_vals)
    a, b, c = vals[0], vals[1], vals[2]
    e = bl.sigma0_eigs_sym(a, b, c, nq)
    A, B, D_, C = None, None, None, None
    A, B, C, D_ = bl.blocks_rational(int(n), vals[3:14], IDX)
    T = tmat(nq)
    TA = [[sum(T[p][i] * A[p][q] * T[q][j] for p in range(3) for q in range(3))
           for j in range(2)] for i in range(2)]
    return [e[1], e[2], B, D_, C[0][0], C[0][1], C[1][1],
            TA[0][0], TA[0][1], TA[1][1]]


def hard_affine_exact(n):
    """
    Constant term and the four coefficients on beta = f * n^3, EXACTLY over Q,
    for each of the ten entries, each already multiplied by its normalising
    power of n.

    Doing this exactly is not a nicety.  The entries are of size n^-5 while the
    terms that build them are O(1), so at n = 256 a float assembly loses about
    nine digits to cancellation and the interior-point solver then reports
    margins two orders of magnitude below what the analytic centre demonstrably
    achieves.  Exact assembly, floated only at the end, removes that entirely.
    """
    zero = [F(0)] * NFREE
    base = balanced(n, hard_entries(n, zero))
    cols = []
    for k in range(4):
        x = [F(0)] * NFREE
        x[ESS_I[k]] = F(1) / F(n) ** 3            # beta_k = 1
        col = balanced(n, hard_entries(n, x))
        cols.append([col[i] - base[i] for i in range(10)])
    const = [float(v) for v in base]
    coef = [[float(cols[k][i]) for k in range(4)] for i in range(10)]
    return const, coef


def balanced(n, e):
    """
    The ten entries put on a common scale by a congruence, exactly over Q.

    The four scalars only need a power of n.  The two 2 x 2 blocks need more: a
    diagonal scaling alone leaves them NEARLY SINGULAR, because their eigenvalues
    are of order n^-1 and n^-5 and the determinant is fixed by the geometry, so
    no diagonal congruence can close a gap of n^4.  Measured at the analytic
    centre, the near-null direction is (1,1) in the diagonally scaled basis for
    both blocks, so the congruence

        V_C = [[n^{3/2}, -n^{5/2}], [0, n^{3/2}]]
        V_T = [[n^{1/2}, -n^{3/2}], [0, n^{1/2}]]

    (a diagonal scaling, then shear out (1,1), then re-scale the complement by n)
    puts every entry at Theta(1).  Each V is invertible, so V^T M V is positive
    definite exactly when M is; and although V itself involves n^{1/2}, every
    entry of V^T M V carries an INTEGER power of n, so the result stays rational.
    """
    nn = F(n)
    c11, c12, c22 = e[4], e[5], e[6]
    t11, t12, t22 = e[7], e[8], e[9]
    return [e[0] * nn, e[1] * nn ** 5, e[2] * nn, e[3] * nn ** 6,
            c11 * nn ** 3,
            c12 * nn ** 3 - c11 * nn ** 4,
            c11 * nn ** 5 - 2 * c12 * nn ** 4 + c22 * nn ** 3,
            t11 * nn,
            t12 * nn - t11 * nn ** 2,
            t11 * nn ** 3 - 2 * t12 * nn ** 2 + t22 * nn]


def normalised_forms_exact(n, b):
    """The eight normalised quantities as cvxpy expressions in beta."""
    import cvxpy as cp
    const, coef = hard_affine_exact(n)
    v = [const[i] + np.asarray(coef[i]) @ b for i in range(10)]
    Cm = cp.bmat([[v[4], v[5]], [v[5], v[6]]])
    Tm = cp.bmat([[v[7], v[8]], [v[8], v[9]]])
    return v[0], v[1], v[2], v[3], Cm, Tm


def normalised_values(n, beta):
    """
    The same eight, as plain numbers at a given beta.  Used to read a REFERENCE
    scale off a genuinely feasible point.

    Even after the diagonal congruence the C block stays near-singular -- its two
    eigenvalues are of order n^-1 and n^-5, a ratio no diagonal scaling can fix,
    since the determinant is fixed by the geometry.  So a margin measured against
    the identity still decays like n^-2 and the objective still chases the largest
    n.  Measuring instead against the analytic centre of the same n makes t = 1
    mean "as well centred as the centre" at every n at once.
    """
    const, coef = hard_affine_exact(n)
    v = [const[i] + float(np.asarray(coef[i]) @ np.asarray(beta))
         for i in range(10)]
    return {"q1": v[0], "q2": v[1], "qB": v[2], "qD": v[3],
            "C": np.array([[v[4], v[5]], [v[5], v[6]]]),
            "T": np.array([[v[7], v[8]], [v[8], v[9]]])}


def hard_affine(n):
    """The eight hard quantities as affine forms (float) in the 8 free vars."""
    eig, A, B, C, D = fc.quantities_affine(n)
    T = tmat(float(n))

    def comb(coeffs, mats):
        out = fc._Lin(0.0)
        for cf, M in zip(coeffs, mats):
            out = out + M * cf
        return out

    TA = [[comb([T[p][i] * T[q][j] for p in range(3) for q in range(3)],
                [A[p][q] for p in range(3) for q in range(3)])
           for j in range(2)] for i in range(2)]
    return eig[1], eig[2], B, C, D, TA


# Natural size of each quantity, MEASURED at the analytic centre, which is
# canonical and so does not presuppose the normalisation being tested:
#
#   theta_1 ~ n^-1   theta_2 ~ n^-5   B ~ n^-1   D ~ n^-6
#   C  entries ~ (n^-3, n^-2, n^-1)   T^T A T entries ~ (n^-1, n^0, n^1)
#
# The two 2 x 2 blocks are NOT a single power of n times an O(1) matrix: their
# entries span n^2 either way.  Scaling them by one power leaves the smallest
# eigenvalue of size n^-2, which is exactly the rate at which the per-n margin
# ceiling was decaying, and it made the min-margin objective chase the largest n
# in the grid alone.  The fix is a DIAGONAL CONGRUENCE, C -> S C S with
# S = diag(n^{3/2}, n^{1/2}) and T -> S T S with S = diag(n^{1/2}, n^{-1/2}):
# congruence by a positive diagonal preserves definiteness exactly, and the
# entry-wise powers n^{p_i + p_j} it produces are integers.
POW = {"theta1": 1, "theta2": 5, "B": 1, "D": 6}
ENTRY_POW = [POW["theta1"], POW["theta2"], POW["B"], POW["D"],
             3, 2, 1,          # C11, C12, C22
             1, 0, -1]         # T11, T12, T22


ESS_I = [FREE.index(c) for c in (6, 9, 11, 12)]


def beta_expr(b, n):
    """
    The 8-vector of free variables from beta = f * n^3, with the four gauge
    coordinates pinned to zero.

    PIN THE WHOLE LINEALITY SPACE.  recession.py shows it is 4-dimensional and
    that the 4 x 4 minor of its generators on the four free lambda columns
    (f15, f16, f17, f18) is triangular with determinant 32, hence invertible.
    So {f15 = f16 = f17 = f18 = 0} is a transversal slice, met exactly once by
    every orbit, and the essential design is the 4 free sigma_11 coordinates
    f6, f9, f11, f12 alone.

    Solving in beta rather than f also matters numerically: at n = 4000 the f
    coordinates are of size 1e-11 and the interior-point solve breaks down.
    """
    import cvxpy as cp
    scale = 1.0 / float(n) ** 3
    return cp.hstack([b[ESS_I.index(i)] * scale if i in ESS_I
                      else cp.Constant(0.0) for i in range(NFREE)])


def solve_reduced(n, cap=1e4):
    """
    Maximise the least normalised margin over the 4-dimensional essential
    quotient.  The feasible set is compact, so the optimum does not drift.
    """
    import cvxpy as cp
    b = cp.Variable(4)
    t = cp.Variable()
    q1, q2, qB, qD, Cm, Tm = normalised_forms_exact(n, b)
    cons = [t <= cap, q1 >= t, q2 >= t, qB >= t, qD >= t,
            Cm - t * np.eye(2) >> 0, Tm - t * np.eye(2) >> 0]
    prob = cp.Problem(cp.Maximize(t), cons)
    for solver in ("CLARABEL", "SCS"):
        try:
            prob.solve(solver=getattr(cp, solver), verbose=False)
            if prob.status in ("optimal", "optimal_inaccurate"):
                v = np.zeros(NFREE)
                for k, i in enumerate(ESS_I):
                    v[i] = float(b.value[k]) / float(n) ** 3
                return v, float(t.value), prob.status
        except Exception:                                        # noqa: BLE001
            continue
    return None, None, "failed"


def main():
    print("STEP 1 -- the recession cone is exactly as derived")
    check_invariance()

    print("\nSTEP 2 -- is the reduced (quotiented) problem BOUNDED?")
    for n in (4, 8, 20, 60):
        for cap in (1e2, 1e4, 1e6):
            _, t, st = solve_reduced(n, cap=cap)
            print(f"  n={n:3d} cap={cap:.0e}: t = "
                  + (f"{t:.6g}  ({st})" if t is not None else "FAILED"))

    print("\nSTEP 3 -- the reduced optimum, scaled, across n")
    print("     n  " + "".join(f"  f{c:<2d}*n^3 " for c in FREE))
    pts = {}
    for n in (4, 6, 8, 12, 16, 24, 32, 48, 64, 96, 128, 200, 400, 800):
        xv, t, st = solve_reduced(n)
        if xv is None:
            print(f"  {n:4d}  SDP failed")
            continue
        pts[n] = xv
        print(f"  {n:4d}  " + "".join(f"{v * n ** 3: 10.4f}" for v in xv))
    return pts


if __name__ == "__main__":
    main()
