"""
Choose the four essential parameters as f_c = (sum_j w_j s^j)/n^3, s = (n-4)/n,
and decide the result for every n >= 4 by Sturm.

Two independent routes to the coefficients, because they fail differently:

  LS   least squares through the ANALYTIC CENTRES of the essential feasible set.
       The centres exist and are unique because recession.py quotients out the
       whole four-dimensional lineality space, leaving a COMPACT set; and an
       analytic centre is an analytic function of the data, so it traces a smooth
       curve in n, which is what a low-degree fit needs.

  SDP  one curve maximising the least margin over the grid, measured RELATIVE to
       the centre at each n.  An absolute margin cannot work: the C block has
       eigenvalues of order n^-1 and n^-5, so any fixed normalisation leaves the
       least eigenvalue decaying like n^-2 and the objective ends up optimising
       the largest n in the grid alone.

Validation is on n OFF the fitting grid.  A curve that only holds at the grid
points is an overfit, and earlier attempts failed exactly that way -- feasible at
every grid point, negative at n = 17, at n = 71, at n = 811.
"""

import os
import sys
from fractions import Fraction as F

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "dittert"))
sys.path.insert(0, HERE)
import centre_ess as ce                                          # noqa: E402
import essential as es                                           # noqa: E402
import general_k3 as g                                           # noqa: E402
import reduced as rd                                             # noqa: E402
import sturm                                                     # noqa: E402

GRID = (list(range(4, 41)) + [44, 48, 56, 64, 80, 96, 128, 160, 192, 256, 320,
                              384, 512, 700, 1000, 1400, 2000])
OFFGRID = [41, 42, 43, 45, 46, 47, 49, 50, 51, 53, 59, 61, 67, 71, 89, 97,
           113, 131, 149, 173, 211, 277, 349, 433, 577, 811, 1201, 1777,
           3001, 6007, 10007, 100003, 1000003]
SPOT = [4, 5, 6, 7, 8, 12, 20, 100, 1000]


def centres(ns):
    """Analytic centre at each n, kept only where it is exactly feasible."""
    pts, refs = {}, {}
    for n in ns:
        v = ce.analytic_centre(n)
        if v is None:
            continue
        fv = [F(float(t)).limit_denominator(10 ** 14) for t in v]
        if any(q <= 0 for _, q in rd.hard_quantities(n, fv)):
            continue
        beta = np.array([v[i] * n ** 3 for i in rd.ESS_I])
        pts[n] = beta
        refs[n] = rd.normalised_values(n, beta)
    return pts, refs


def round_ladder(u, D):
    for md in (1, 2, 3, 4, 6, 8, 12, 16, 24, 32, 48, 64, 128, 256, 512, 1024,
               4096, 10 ** 5, 10 ** 6, 10 ** 8, 10 ** 10):
        yield md, [[F(float(u[i][j])).limit_denominator(md)
                    for j in range(D + 1)] for i in range(4)]


def try_curve(u, D, label):
    """Round, check off the grid, then Sturm.  Returns (wq, D) on success."""
    for md, wq in round_ladder(u, D):
        fs = es.build_s(wq, D)
        if es.exact_check(fs, SPOT):
            continue
        bad2 = es.exact_check(fs, OFFGRID)
        if bad2:
            print(f"    {label} D={D} denom<={md}: off-grid FAILS at "
                  f"n={bad2[0][0]} ({bad2[0][1]}), {len(bad2)} in all")
            continue
        print(f"    {label} D={D} denom<={md}: exact and OFF-GRID CLEAN")
        good, bad = es.sturm_report(fs, verbose=False)
        print(f"      STURM: {len(good)}/10 positive for all n >= 4")
        if bad:
            for nm, det in bad:
                print(f"        fails: {nm}   {det}")
            return None
        return wq
    return None


def main():
    print("STEP 1 -- analytic centres over the grid")
    pts, refs = centres(GRID)
    print(f"  exactly feasible centres at {len(pts)} of {len(GRID)} grid points"
          f"  (n = {min(pts)} .. {max(pts)})")
    ns = sorted(pts)
    ss = np.array([1.0 - 4.0 / n for n in ns])

    print("\nSTEP 2 -- least squares through the centres, then off-grid + Sturm")
    for D in range(1, 8):
        u = np.array([np.polyfit(ss, np.array([pts[n][k] for n in ns]), D)[::-1]
                      for k in range(4)])
        res = max(abs(np.polyval(u[k][::-1], ss) - [pts[n][k] for n in ns]).max()
                  for k in range(4))
        print(f"  D={D}: max residual {res:.4g}")
        wq = try_curve(u, D, "LS ")
        if wq is not None:
            return save(wq, D)

    print("\nSTEP 3 -- centre-relative max-margin curve, then off-grid + Sturm")
    for D in range(1, 8):
        u, t = es.solve_alpha_ref(ns, D, refs)
        if u is None:
            print(f"  D={D}: SDP failed")
            continue
        print(f"  D={D}: relative margin t = {t:+.6g}"
              + ("   (t = 1 is as well centred as the centre)" if D == 1 else ""))
        if t <= 0:
            continue
        wq = try_curve(u, D, "SDP")
        if wq is not None:
            return save(wq, D)
    print("\nno curve certified all ten")
    return None


def save(wq, D):
    print("\n  CURVE (exact):")
    for i in range(4):
        terms = " + ".join(f"({wq[i][j]})*s^{j}" for j in range(D + 1))
        print(f"    f{es.ESS[i]:<2d} = [{terms}] / n^3      s = (n-4)/n")
    out = os.path.join(HERE, "results", "essential_curve.txt")
    with open(out, "w") as fh:
        fh.write(repr((D, [[str(x) for x in r] for r in wq])))
    print(f"\n  ALL TEN POSITIVE FOR EVERY n >= 4.  saved {out}")
    return wq, D


if __name__ == "__main__":
    main()
