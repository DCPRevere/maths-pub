"""
The design step in coordinates adapted to the sliver.

exact_design.py shows the essential feasible set is a sliver: in beta = f*n^3
coordinates the balanced entries theta_2, D, C01 and T11 are differences of terms
of size n^2 and n^3 that must cancel to O(1), which forces

    beta6 - 2 beta9  = O(n^-2) ,
    beta12 - (2 beta9 - 1) = O(n^-1) ,
    beta11 - 2 beta12 - 2 = O(n^-2) ,

with the remaining freedom a single b = beta9 in (1/2, 1).  Fitting cannot hold
relations to that precision, and pinning four entries to constant targets fails
because the centre's own entries move by a factor of four between n = 4 and
n = infinity.

So put the cancellation into the COORDINATES:

    beta9  = b
    beta6  = 2b + x/n^2
    beta12 = 2b - 1 + y/n
    beta11 = 2 beta12 + 2 + z/n^2

with (b, x, y, z) each a polynomial in 1/n of degree <= d.  The map to beta is
affine, so the ten balanced entries stay affine, and their coefficients on
(b, x, y, z) are now Theta(1) -- the n^3 pieces cancel symbolically instead of
numerically.  At d = 0 this is four constants.

Everything is assembled exactly over Q(n); floats are used only to pick the
constants, and Sturm decides the result for every n >= 4.
"""

import os
import sys
from fractions import Fraction as F

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "dittert"))
sys.path.insert(0, HERE)
import essential as es                                           # noqa: E402
import exact_design as ed                                        # noqa: E402
import general_k3 as g                                           # noqa: E402
import sturm                                                     # noqa: E402
from general_k3 import RF                                        # noqa: E402

ZERO, ONE, TWO, N = ed.ZERO, ed.ONE, ed.TWO, ed.N
NFREE = ed.NFREE
ESS_I = ed.ESS_I
ENAMES = ed.ENAMES
INV = ONE / N


def adapted_beta(params, d):
    """params grouped as b_0..b_d, x_0..x_d, y_0..y_d, z_0..z_d."""
    def poly(idx):
        acc, p = ZERO, ONE
        for j in range(d + 1):
            c = params[idx * (d + 1) + j]
            if c:
                acc = acc + c * p
            p = p * INV
        return acc
    b, x, y, z = poly(0), poly(1), poly(2), poly(3)
    b9 = b
    b6 = TWO * b + x * INV * INV
    b12 = TWO * b - ONE + y * INV
    b11 = TWO * b12 + TWO + z * INV
    return [b6, b9, b11, b12]


def fs_from_beta(beta):
    fs = [ZERO] * NFREE
    for k in range(4):
        fs[ESS_I[k]] = beta[k] / (N * N * N)
    return fs


def adapted_affine(d):
    """Constant term and parameter coefficients of each balanced entry, over Q(n)."""
    npar = 4 * (d + 1)
    zero = [ZERO] * npar
    base = ed.balanced_rf(ed.entries_rf(fs_from_beta(adapted_beta(zero, d))))
    cols = []
    for k in range(npar):
        p = [ZERO] * npar
        p[k] = ONE
        col = ed.balanced_rf(ed.entries_rf(fs_from_beta(adapted_beta(p, d))))
        cols.append([col[i] - base[i] for i in range(10)])
    return base, cols


def eliminate_z(base, cols, d):
    """
    Remove z by imposing theta_2 = D exactly, over Q(n).

    Both are affine in z with opposite-sign coefficients of size n^2, and the
    window between "D > 0" and "theta_2 > 0" has width O(n^-2) about z = 6.14.
    So z cannot be fitted: at n = 10^6 it would have to be right to twelve
    digits, and no set of grid constraints in floating point can deliver that.
    Setting theta_2 = D puts z exactly in that window whenever the window is
    non-empty, and leaves ONE quantity where there were two.  The remaining
    parameters b, x, y all carry Theta(1) coefficients.

    Only z_0 is eliminated; z_1..z_d stay as free parameters, so no generality
    is lost at higher degree.
    """
    npar = len(cols)
    kz = 3 * (d + 1)                       # index of z_0
    alpha = cols[kz][1] - cols[kz][3]
    if not alpha:
        raise RuntimeError("theta_2 - D does not involve z_0")
    keep = [k for k in range(npar) if k != kz]
    dbase = base[1] - base[3]
    nbase = [base[i] - cols[kz][i] * dbase / alpha for i in range(10)]
    ncols = []
    for k in keep:
        dk = cols[k][1] - cols[k][3]
        ncols.append([cols[k][i] - cols[kz][i] * dk / alpha
                      for i in range(10)])
    return nbase, ncols, keep


def numeric(base, cols, n):
    npar = len(cols)
    nq = F(n)
    c = np.array([float(base[i].at(nq)) for i in range(10)])
    M = np.array([[float(cols[k][i].at(nq)) for k in range(npar)]
                  for i in range(10)])
    return c, M


def solve_params(base, cols, ns, cap=1e3):
    """Maximise the least of the eight conditions over the grid."""
    import cvxpy as cp
    npar = len(cols)
    p = cp.Variable(npar)
    t = cp.Variable()
    cons = [t <= cap]
    for n in ns:
        c, M = numeric(base, cols, n)
        v = [c[i] + M[i] @ p for i in range(10)]
        Cm = cp.bmat([[v[4], v[5]], [v[5], v[6]]])
        Tm = cp.bmat([[v[7], v[8]], [v[8], v[9]]])
        cons += [v[0] >= t, v[1] >= t, v[2] >= t, v[3] >= t,
                 Cm - t * np.eye(2) >> 0, Tm - t * np.eye(2) >> 0]
    prob = cp.Problem(cp.Maximize(t), cons)
    for solver in ("CLARABEL", "SCS"):
        try:
            prob.solve(solver=getattr(cp, solver), verbose=False)
            if prob.status in ("optimal", "optimal_inaccurate"):
                return np.array(p.value, dtype=float), float(t.value)
        except Exception:                                        # noqa: BLE001
            continue
    return None, None


def exact_entries(pq, d):
    fs = fs_from_beta(adapted_beta([RF([v]) if v else ZERO for v in pq], d))
    return ed.balanced_rf(ed.entries_rf(fs)), fs


def check_numeric(base, cols, pq, ns):
    """The eight conditions at exact parameters, evaluated exactly at each n."""
    bad = []
    npar = len(cols)
    for n in ns:
        nq = F(n)
        v = [base[i].at(nq) + sum(cols[k][i].at(nq) * pq[k]
                                  for k in range(npar)) for i in range(10)]
        tests = [v[0], v[1], v[2], v[3], v[4], v[4] * v[6] - v[5] ** 2,
                 v[7], v[7] * v[9] - v[8] ** 2]
        for j, q in enumerate(tests):
            if q <= 0:
                bad.append((n, j))
    return bad


GRID = (list(range(4, 41)) + [48, 64, 96, 128, 200, 320, 512, 1000, 2000,
                              5000, 20000, 10 ** 5, 10 ** 6])
TEST = [4, 5, 6, 7, 9, 13, 19, 29, 43, 71, 113, 181, 293, 467, 751, 1213,
        3001, 10007, 100003, 3 * 10 ** 6]


def z_value(base, cols, d, pq, keep):
    """Recover the eliminated z_0 as an exact rational function of n."""
    kz = 3 * (d + 1)
    alpha = cols[kz][1] - cols[kz][3]
    num = base[1] - base[3]
    for j, k in enumerate(keep):
        if pq[j]:
            num = num + (cols[k][1] - cols[k][3]) * RF([pq[j]])
    return ZERO - num / alpha


def main():
    for d in (0, 1, 2):
        print(f"\n=== adapted coordinates, degree d = {d} in 1/n ===")
        base0, cols0 = adapted_affine(d)
        base, cols, keep = eliminate_z(base0, cols0, d)
        p, t = solve_params(base, cols, GRID)
        if p is None:
            print("  SDP failed")
            continue
        print(f"  least condition over the grid: t = {t:+.6g}")
        allnames = [f"{c}{j}" for c in "bxyz" for j in range(d + 1)]
        names = [allnames[k] for k in keep]
        print("  " + "  ".join(f"{nm}={v:+.6f}" for nm, v in zip(names, p)))
        if t <= 0:
            continue
        for md in (1, 2, 3, 4, 6, 8, 12, 16, 24, 32, 64, 128, 512, 4096,
                   10 ** 5, 10 ** 7):
            pq = [F(float(v)).limit_denominator(md) for v in p]
            bad = check_numeric(base, cols, pq, TEST)
            if bad:
                continue
            print(f"  denominator <= {md:>8}: exact and off-grid clean")
            print("    " + "  ".join(f"{nm}={v}" for nm, v in zip(names, pq)))
            zrf = z_value(base0, cols0, d, pq, keep)
            print(f"    z_0 = {zrf}")
            full_p = [ZERO] * (4 * (d + 1))
            for j, k in enumerate(keep):
                full_p[k] = RF([pq[j]]) if pq[j] else ZERO
            full_p[3 * (d + 1)] = zrf
            fs = fs_from_beta(adapted_beta(full_p, d))
            ent = ed.balanced_rf(ed.entries_rf(fs))
            full = es.apply_gauge(fs, ONE / (N * N * N), ONE / N)
            good, bad2 = es.sturm_report(full, verbose=False)
            print(f"    STURM: {len(good)}/10 positive for all n >= 4")
            for nm, det in bad2:
                print(f"      FAILS {nm}: {det}")
            if not bad2:
                out = os.path.join(HERE, "results", "adapted_certificate.txt")
                with open(out, "w") as fh:
                    fh.write(repr((d, [str(v) for v in pq],
                                   [(str(f.num), str(f.den)) for f in full])))
                print(f"    ALL TEN POSITIVE FOR EVERY n >= 4.  saved {out}")
                return pq, d, full
            break
    return None


if __name__ == "__main__":
    main()
