"""
The design step SOLVED IN CLOSED FORM over Q(n) -- no grid, no fit, no rounding.

WHY FITTING CANNOT WORK HERE.  In beta = f * n^3 coordinates the essential
feasible set is a SLIVER.  Writing the ten balanced entries out (reduced.balanced)
shows four of them are differences of terms of size n^2 or n^3 that must cancel to
O(1):

    theta_2 :  n^2 [ c(n) - (n-2)(beta11 - 2 beta12) - 2 beta6 + 4 beta9 ]
    D       :  n^3 [ (beta11 - 2 beta12) - d(n) ]
    C01     :  (n/2)[ 1 - 2 beta6 + 2 beta9 + beta12 ] + ...
    T11     :  n^2 [ 2 + 2(beta6 - 2 beta9) - (beta11 - 2 beta12) ] + ...

so beta11 - 2 beta12 has to be pinned to within O(n^-3) of a specific rational
function, beta6 - 2 beta9 to within O(n^-2), and beta12 - (2 beta9 - 1) to within
O(n^-1).  Asymptotically that forces

    beta6 -> 2b ,  beta9 -> b ,  beta11 -> 4b ,  beta12 -> 2b - 1 ,

a ONE-parameter family with 1/2 < b < 1 (from B > 0 and theta_1 > 0), and the
analytic centre sits at b = 0.8486.  A least-squares curve through numerically
computed points cannot hold a relation to O(n^-3); that, and not the earlier
unboundedness, is why every fitted curve failed off the grid.

WHAT TO DO INSTEAD.  All ten entries are AFFINE in beta with coefficients in Q(n),
and they can be built exactly.  So impose four linear conditions and solve the
4 x 4 system over Q(n) exactly:

    theta_2 = t2(n) ,   D = tD(n) ,   C01 = 0 ,   T01 = 0 .

Killing the two off-diagonal entries DIAGONALISES both 2 x 2 blocks, so
C > 0 becomes C00 > 0 and C11 > 0, and T > 0 becomes T00 > 0 and T11 > 0 -- no
determinants at all.  What remains is six explicit rational functions of n to be
kept positive, plus theta_0 and A which the gauge supplies in closed form.
"""

import os
import sys
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "dittert"))
sys.path.insert(0, HERE)
import blocks as bl                                              # noqa: E402
import essential as es                                           # noqa: E402
import fit_curve as fc                                           # noqa: E402
import general_k3 as g                                           # noqa: E402
import sturm                                                     # noqa: E402
from general_k3 import RF                                        # noqa: E402

ZERO = RF([])
ONE = RF([F(1)])
TWO = RF([F(2)])
N = RF([F(0), F(1)])
IDX = fc.IDX
FREE = fc.FREE
NFREE = fc.NFREE
ESS_I = es.ESS_I
ENAMES = ["theta1", "theta2", "B", "D", "C00", "C01", "C11",
          "T00", "T01", "T11"]


def entries_rf(fs):
    """The ten entries as exact rational functions of n, from the 8 free vars."""
    vals = es.vals19_rf(fs)
    a, b, c = vals[0], vals[1], vals[2]
    m = N - ONE
    theta1 = a + b * (N - TWO) - c * m
    theta2 = a - b * TWO + c
    A, B, C, D = bl.blocks_rational_generic(N, vals[3:14], IDX, one=ONE)
    # columns of T spanning s^perp, s = (1, 2(n-1), (n-1)^2)
    T = [[ZERO - TWO * m, ZERO - m * m], [ONE, ZERO], [ZERO, ONE]]
    TA = [[sum((T[p][i] * A[p][q] * T[q][j] for p in range(3)
                for q in range(3)), ZERO) for j in range(2)] for i in range(2)]
    return [theta1, theta2, B, D, C[0][0], C[0][1], C[1][1],
            TA[0][0], TA[0][1], TA[1][1]]


def balanced_rf(e):
    """The same congruence as reduced.balanced, over Q(n)."""
    n2 = N * N
    n3 = n2 * N
    n4 = n3 * N
    n5 = n4 * N
    n6 = n5 * N
    c11, c12, c22 = e[4], e[5], e[6]
    t11, t12, t22 = e[7], e[8], e[9]
    return [e[0] * N, e[1] * n5, e[2] * N, e[3] * n6,
            c11 * n3,
            c12 * n3 - c11 * n4,
            c11 * n5 - c12 * TWO * n4 + c22 * n3,
            t11 * N,
            t12 * N - t11 * n2,
            t11 * n3 - t12 * TWO * n2 + t22 * N]


def affine_data():
    """Constant term and the four beta coefficients of each balanced entry."""
    zero = [ZERO] * NFREE
    base = balanced_rf(entries_rf(zero))
    cols = []
    for k in range(4):
        fs = [ZERO] * NFREE
        fs[ESS_I[k]] = ONE / (N * N * N)                 # beta_k = 1
        col = balanced_rf(entries_rf(fs))
        cols.append([col[i] - base[i] for i in range(10)])
    return base, cols


def solve_rf(M, rhs):
    """Exact Gauss-Jordan over Q(n).  Returns (solution, ok)."""
    nr, nc = len(M), len(M[0])
    A = [row[:] for row in M]
    b = rhs[:]
    piv, r = [], 0
    for c in range(nc):
        p = next((i for i in range(r, nr) if A[i][c]), None)
        if p is None:
            continue
        A[r], A[p] = A[p], A[r]
        b[r], b[p] = b[p], b[r]
        pv = A[r][c]
        A[r] = [x / pv for x in A[r]]
        b[r] = b[r] / pv
        for i in range(nr):
            if i != r and A[i][c]:
                f = A[i][c]
                A[i] = [A[i][j] - f * A[r][j] for j in range(nc)]
                b[i] = b[i] - f * b[r]
        piv.append(c)
        r += 1
    if len(piv) < nc:
        return None, False
    x = [ZERO] * nc
    for i, c in enumerate(piv):
        x[c] = b[i]
    return x, True


ROWS = {"theta2": 1, "D": 3, "C01": 5, "T01": 8}


def design(targets, base=None, cols=None):
    """
    Solve for beta so that the four chosen balanced entries hit `targets`.
    Returns (beta, fs_essential) with everything exact over Q(n).
    """
    if base is None:
        base, cols = affine_data()
    idx = [ROWS["theta2"], ROWS["D"], ROWS["C01"], ROWS["T01"]]
    M = [[cols[k][i] for k in range(4)] for i in idx]
    rhs = [targets[j] - base[i] for j, i in enumerate(idx)]
    beta, ok = solve_rf(M, rhs)
    if not ok:
        return None, None
    fs = [ZERO] * NFREE
    for k in range(4):
        fs[ESS_I[k]] = beta[k] / (N * N * N)
    return beta, fs


def report(beta, fs, base, cols, verbose=True):
    """All ten balanced entries at this beta, and the Sturm verdict."""
    ent = balanced_rf(entries_rf(fs))
    if verbose:
        print("    balanced entries as rational functions of n:")
        for i, nm in enumerate(ENAMES):
            s = sturm.sign_on_n_ge_4(ent[i].den)
            num = g.pscale(ent[i].num, F(s)) if s else ent[i].num
            ok, det = (sturm.positive_on_nonneg(sturm.shift_to_m(num))
                       if s else (False, "denominator not sign-definite"))
            val = float(ent[i].at(F(1000)))
            print(f"      {nm:<7s} {'POS' if ok else 'not>0'}"
                  f"   at n=1000: {val: .6g}")
    return ent


# Balanced entry values at the analytic centre, as n -> infinity (centre_ess.py):
#   theta1 0.3076  theta2 4.524  B 1.386  D 4.537
#   C00 2.702  C01 -2.715  C11 7.223   T00 1.386  T01 -1.419  T11 10.47
# Pinning to simple rationals near these puts the closed-form solution where the
# centre is, which is the best available guess at an interior point.
TARGET = [F(3, 10), F(9, 2), F(7, 5), F(9, 2), F(27, 10), F(-27, 10),
          F(7), F(7, 5), F(-7, 5), F(21, 2)]


def screen(test_ns=(4, 5, 6, 7, 8, 11, 17, 30, 60, 130, 400, 1500, 10 ** 4,
                    10 ** 6), target=None):
    """
    Numerically, for every 4-subset of the ten conditions: pin it to the target
    values, solve for beta at each test n, and keep the subsets whose remaining
    conditions all come out positive.  Cheap filter before the exact solve.
    """
    import itertools
    import numpy as np
    import reduced as rd
    target = TARGET if target is None else target
    data = {}
    for n in test_ns:
        const, coef = rd.hard_affine_exact(n)
        data[n] = (np.array(const), np.array(coef))
    survivors = []
    for S in itertools.combinations(range(10), 4):
        ok = True
        worst = None
        for n in test_ns:
            const, coef = data[n]
            M = coef[list(S)]
            if abs(np.linalg.det(M)) < 1e-12 * abs(M).max() ** 4:
                ok = False
                break
            rhs = np.array([float(target[i]) for i in S]) - const[list(S)]
            try:
                beta = np.linalg.solve(M, rhs)
            except np.linalg.LinAlgError:
                ok = False
                break
            v = const + coef @ beta
            margins = [v[0], v[1], v[2], v[3], v[4],
                       v[4] * v[6] - v[5] ** 2, v[7], v[7] * v[9] - v[8] ** 2]
            mn = min(margins)
            worst = mn if worst is None else min(worst, mn)
            if mn <= 0:
                ok = False
                break
        if ok:
            survivors.append((worst, S))
    survivors.sort(reverse=True)
    return survivors


def main():
    print("exact design over Q(n): affine data")
    base, cols = affine_data()
    print(f"  ten balanced entries, each affine in beta with coefficients "
          f"in Q(n)")
    print(f"  example -- D:  const {base[3]}")
    for k in range(4):
        print(f"                 coef beta_{es.ESS[k]:<3d} {cols[3][k]}")

    print("\nscreening all 210 four-subsets numerically")
    surv = screen()
    print(f"  {len(surv)} subsets give all ten positive at every test n")
    for w, S in surv[:12]:
        print(f"    worst margin {w:9.5f}   pin " + ", ".join(ENAMES[i]
                                                             for i in S))
    if not surv:
        return None

    print("\nexact solve over Q(n) and STURM, best subsets first")
    for w, S in surv[:8]:
        names = ", ".join(ENAMES[i] for i in S)
        idx = list(S)
        M = [[cols[k][i] for k in range(4)] for i in idx]
        rhs = [RF([TARGET[i]]) - base[i] for i in idx]
        beta, ok = solve_rf(M, rhs)
        if not ok:
            print(f"  pin {names}: SINGULAR over Q(n)")
            continue
        fs = [ZERO] * NFREE
        for k in range(4):
            fs[ESS_I[k]] = beta[k] / (N * N * N)
        full = es.apply_gauge(fs, ONE / (N * N * N), ONE / N)
        good, bad = es.sturm_report(full, verbose=False)
        print(f"  pin {names}")
        print(f"     STURM: {len(good)}/10 positive for all n >= 4")
        for nm, det in bad:
            print(f"       FAILS {nm}: {det}")
        if not bad:
            for k in range(4):
                print(f"     beta_{es.ESS[k]:<3d} = {beta[k]}")
            out = os.path.join(HERE, "results", "exact_design.txt")
            with open(out, "w") as fh:
                fh.write(repr([(str(f.num), str(f.den)) for f in full]))
            print(f"     ALL TEN POSITIVE FOR EVERY n >= 4.  saved {out}")
            return full
    return None


if __name__ == "__main__":
    main()
