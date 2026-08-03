"""
Solve the k = 4 system over Q(n), and report the shape of the solution space.

This is the k = 4 analogue of general_k3.solve_symbolic.  The system is

    A0 x + (A1c/n + A1l) y + A2 z = rhs

with 87 equations and 440 unknowns (51 + 356 + 33).  Exact Gauss-Jordan over the
field Q(n) gives the rank, the consistency verdict, and the free-variable count.

The number that matters for the design step is NOT 440 but the count of
ESSENTIAL free variables -- at k = 3 the 8 free variables collapsed to 4 once the
lineality space was quotiented out, and the same reduction has to be done here
before any SDP is posed.  Rank first, though: if the system were inconsistent
over Q(n) the whole approach would die here, as it nearly did at (3,3).
"""

import os
import sys
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "dittert"))
sys.path.insert(0, HERE)
import general_k3 as g                                           # noqa: E402
import k4_system as k4                                           # noqa: E402
from general_k3 import RF                                        # noqa: E402


def solve(verbose=True):
    sym = k4.build(verbose=verbose)
    rows, gvars, svars, lvars = (sym["rows"], sym["gvars"], sym["svars"],
                                 sym["lvars"])
    nR = len(rows)
    ncol = len(gvars) + len(svars) + len(lvars)
    n_poly = [F(0), F(1)]

    M = []
    for r in range(nR):
        row = [RF(p) for p in sym["A0"][r]]
        row += [RF(sym["A1c"][r][j], n_poly) + RF(sym["A1l"][r][j])
                for j in range(len(svars))]
        row += [RF(p) for p in sym["A2"][r]]
        M.append(row)
    rhs = [_rhs_rf(rows[r]) for r in range(nR)]

    piv_cols, r = [], 0
    A = [row[:] for row in M]
    b = rhs[:]
    for c in range(ncol):
        p = next((i for i in range(r, nR) if A[i][c]), None)
        if p is None:
            continue
        A[r], A[p] = A[p], A[r]
        b[r], b[p] = b[p], b[r]
        pv = A[r][c]
        A[r] = [v / pv for v in A[r]]
        b[r] = b[r] / pv
        for i in range(nR):
            if i != r and A[i][c]:
                f = A[i][c]
                A[i] = [A[i][j] - f * A[r][j] for j in range(ncol)]
                b[i] = b[i] - f * b[r]
        piv_cols.append(c)
        r += 1
        if r == nR:
            break
    rank = r
    dependent = list(range(rank, nR))
    consistent = all(not b[i] for i in dependent)
    free_cols = [c for c in range(ncol) if c not in piv_cols]

    if verbose:
        print(f"  equations {nR}, unknowns {ncol}, rank over Q(n) = {rank}")
        print(f"  dependent rows {len(dependent)}, consistent: {consistent}")
        print(f"  free variables: {len(free_cols)}")
        ng, ns = len(gvars), len(svars)
        fg = [c for c in free_cols if c < ng]
        fs = [c for c in free_cols if ng <= c < ng + ns]
        fl = [c for c in free_cols if c >= ng + ns]
        print(f"    of which sigma_0 {len(fg)}, sigma_11 {len(fs)}, "
              f"lambda {len(fl)}")
    return dict(A=A, b=b, piv_cols=piv_cols, free_cols=free_cols, rank=rank,
                consistent=consistent, sym=sym, ncol=ncol)


def _rhs_rf(rowkey):
    """|orbit| * [coefficient of that monomial in F], exactly, at k = 4."""
    from math import factorial
    size = g.orbit_size_poly(rowkey, False)
    d = len(rowkey)
    if d == 0 or d > k4.K:
        return RF([])
    rows = [r for r, _ in rowkey]
    cols = [c for _, c in rowkey]
    dr = len(set(rows)) == d
    dc = len(set(cols)) == d
    cnk = g._binom_poly(k4.K, 0)
    cndk = g._binom_poly(k4.K - d, d)
    term = RF([])
    if dr:
        term = term + RF(cndk, cnk)
    if dc:
        term = term + RF(cndk, cnk)
    if dr and dc:
        npow = [F(0)] * (k4.K - d) + [F(1)]
        term = term - (RF(g.pmul(cndk, cndk), g.pmul(cnk, cnk))
                       * RF([F(factorial(k4.K - d))]) / RF(npow))
    return RF([]) - RF(size) * term


if __name__ == "__main__":
    print("k = 4: solving the system over Q(n)\n")
    res = solve()
    print(f"\nconsistent over Q(n): {res['consistent']}")
