"""
Choose the 8 free variables of the k = 3 certificate family as explicit functions
of n, so that both Gram matrices are positive definite for every n.

The linear algebra is settled: general_k3.solve_symbolic shows the constraint
system has rank 11 in 19 unknowns and is CONSISTENT over Q(n), so a certificate of
this shape exists for every n as far as the equalities go.  What remains is the
cone condition, and that is the actual content.

The numerical SDP optima are useless as a formula: they maximise the least
eigenvalue, so they sit wherever the two cones balance and their n-dependence is
not rational.  Instead we take an ansatz f_c = alpha_c / n^{p_c} with exponents
read off the observed scaling, and choose the CONSTANTS alpha to keep every block
positive across a wide range of n at once.  Positive definiteness is decided on
the four blocks of blocks.py plus the three sigma_0 eigenvalues, all exactly over
Q -- no eigensolver, no floating point in any decision.
"""

import os
import sys
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "dittert"))
sys.path.insert(0, HERE)
import blocks as bl                                              # noqa: E402
import general_k3 as g                                           # noqa: E402

RES = g.solve_symbolic(verbose=False)
SYM = RES["sym"]
FREE = RES["free_cols"]
PIV = RES["piv_cols"]
EXP = {6: 3, 9: 3, 11: 3, 12: 3, 15: 2, 16: 3, 17: 3, 18: 3}
IDX = bl.svar_index()


def full_solution(n, alpha):
    """All 19 variables at this n as exact Fractions, given rational alpha."""
    n = F(n)
    vals = [F(0)] * 19
    for t, c in enumerate(FREE):
        vals[c] = F(alpha[t]) / n ** EXP[c]
    for i, c in enumerate(PIV):
        v = RES["b"][i].at(n)
        for fc in FREE:
            a = RES["A"][i][fc]
            if a:
                v -= a.at(n) * vals[fc]
        vals[c] = v
    return vals


def leading_minors(M):
    """Exact leading principal minors of a small symmetric rational matrix."""
    out = []
    for s in range(1, len(M) + 1):
        out.append(_det([row[:s] for row in M[:s]]))
    return out


def _det(M):
    k = len(M)
    if k == 1:
        return M[0][0]
    if k == 2:
        return M[0][0] * M[1][1] - M[0][1] * M[1][0]
    tot = F(0)
    for j in range(k):
        minor = [[M[i][c] for c in range(k) if c != j] for i in range(1, k)]
        tot += (-1) ** j * M[0][j] * _det(minor)
    return tot


def pd_certificates(n, alpha):
    """
    Every quantity that must be positive, exactly over Q.

    sigma_0 contributes its three eigenvalues.  sigma_11 contributes the leading
    principal minors of each block (Sylvester's criterion), which is equivalent to
    definiteness and stays polynomial in the entries.
    """
    vals = full_solution(n, alpha)
    a, b, c = vals[0], vals[1], vals[2]
    out = list(zip(["G0.theta0", "G0.theta1", "G0.theta2"],
                   bl.sigma0_eigs_sym(a, b, c, F(n))))
    y = vals[3:14]
    A, B, C, D = bl.blocks_rational(n, y, IDX)
    for i, m in enumerate(leading_minors(A)):
        out.append((f"H.A minor{i+1}", m))
    out.append(("H.B", B))
    for i, m in enumerate(leading_minors(C)):
        out.append((f"H.C minor{i+1}", m))
    out.append(("H.D", D))
    return out


def worst_scaled(alpha, ns):
    """Smallest of the positivity quantities, each scaled to be O(1) in n."""
    w = None
    for n in ns:
        for name, v in pd_certificates(n, alpha):
            s = _scale(name, n)
            t = float(v) * s
            if w is None or t < w:
                w = t
    return w


def _scale(name, n):
    """Normalising powers of n, so the different quantities are comparable."""
    if name.startswith("G0"):
        return float(n) ** 3
    if name.startswith("H.A minor1"):
        return float(n) ** 3
    if name.startswith("H.A minor2"):
        return float(n) ** 5
    if name.startswith("H.A minor3"):
        return float(n) ** 7
    if name.startswith("H.C minor1"):
        return float(n) ** 3
    if name.startswith("H.C minor2"):
        return float(n) ** 5
    return float(n) ** 3


def main():
    import numpy as np
    from scipy.optimize import minimize
    ns = [4, 5, 6, 8, 12, 20, 40]
    seed = np.array([20.9, 2.4, 39.0, 2.05, -6.06, -21.2, -20.9, -4.56])

    def obj(a):
        try:
            return -worst_scaled([F(float(x)).limit_denominator(10 ** 6)
                                  for x in a], ns)
        except ZeroDivisionError:
            return 1e9

    best = (-obj(seed), seed)
    print(f"seed worst scaled quantity: {best[0]:.6e}")
    rng = np.random.default_rng(5)
    for trial in range(30):
        x0 = best[1] if trial == 0 else best[1] * (
            1 + 0.3 * rng.standard_normal(8))
        r = minimize(obj, x0, method="Nelder-Mead",
                     options={"maxiter": 1500, "fatol": 1e-14, "xatol": 1e-10})
        if -r.fun > best[0]:
            best = (-r.fun, r.x)
    print(f"best worst scaled quantity: {best[0]:.6e}")
    print("alpha =", np.array2string(best[1], precision=5))
    print()
    print("rounded candidates, tested on a wide range of n:")
    wide = [4, 5, 6, 7, 8, 10, 12, 16, 20, 30, 40, 60, 100, 200]
    for denom in (1, 2, 3, 4, 6, 8, 12, 24):
        cand = [F(int(round(v * denom)), denom) for v in best[1]]
        try:
            w = worst_scaled(cand, wide)
        except ZeroDivisionError:
            continue
        print(f"  denom {denom:3d}: {[str(x) for x in cand]}")
        print(f"            worst = {w: .6e}  {'OK' if w > 0 else 'FAILS'}")


if __name__ == "__main__":
    main()
