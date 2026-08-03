"""
Core for the D-VECTOR conjecture (Bernstein coefficients of the flow-to-J
derivative).  See BERNSTEIN.md.

Setting (paper_b section 1):

    K_n = { A >= 0 : sum_ij a_ij = n },   r = row sums, c = column sums,
    sigma_k(A) = sum_{|alpha|=|beta|=k} per(A[alpha,beta]),
    E_k(v) = e_k(v)/C(n,k),   P_k(A) = sigma_k(A)/C(n,k)^2,
    gamma(n,k) = k!/n^k,      Phi_k(A) = E_k(r) + E_k(c) - P_k(A).

REDUCTIONS.md section 4b: f(t) = Phi_k((1-t)A + tJ/n) is in Bernstein form and

    f'(t) = k sum_{j=0}^{k-1} d_j C(k-1,j) t^{k-1-j} (1-t)^j,
    d_j   = dE_j + (k!/j!) n^{j-k} [ n P_{j+1}/(j+1) - P_j ],
    dE_j  = E_j(r) - E_{j+1}(r) + E_j(c) - E_{j+1}(c)  >= 0 (Maclaurin).

THE NORMALISED FORM used throughout this file.  Put

    Q_j(A) = n^j sigma_j(A) / ( j! C(n,j)^2 ),        Q_j(J_n/n) = 1,

so that gamma(n,k) Q_j(A) = (k!/j!) n^{j-k} P_j(A).  Then

    ***  d_j = dE_j + gamma(n,k) ( Q_{j+1}(A) - Q_j(A) )  ***

which separates the dependence on k COMPLETELY into the scalar gamma(n,k).
Q_0 = Q_1 = 1 on K_n, so d_0 = 0.  sum_{j<k} d_j = 2 - gamma - Phi_k = F_{n,k}.

Usage: import; `python3 bern_core.py selftest` runs the calibration.
"""

import sys
from fractions import Fraction as Q
from itertools import combinations

import numpy as np

import fals_core as fc
import reduce_scan as R


# --------------------------------------------------------------- float layer
def Qvec_f(A, sig=None):
    """[Q_0, ..., Q_n] as floats."""
    n = A.shape[0]
    if sig is None:
        sig = R.sigma_all_f(A)
    return np.array([n ** j * sig[j] / (fc.fact(j) * fc.binom(n, j) ** 2)
                     for j in range(n + 1)])


def dEvec_f(A):
    """[dE_0, ..., dE_{n-1}] as floats."""
    n = A.shape[0]
    r, c = A.sum(1), A.sum(0)
    Er = [R.e_k_f(r, j) / fc.binom(n, j) for j in range(n + 1)]
    Ec = [R.e_k_f(c, j) / fc.binom(n, j) for j in range(n + 1)]
    return np.array([(Er[j] - Er[j + 1]) + (Ec[j] - Ec[j + 1])
                     for j in range(n)])


def dvec_f(A, k, sig=None):
    """[d_0, ..., d_{k-1}] as floats, via the normalised form."""
    n = A.shape[0]
    Qv = Qvec_f(A, sig)
    dE = dEvec_f(A)
    g = fc.fact(k) / float(n) ** k
    return np.array([dE[j] + g * (Qv[j + 1] - Qv[j]) for j in range(k)])


def V_f(A, k, sig=None):
    """f'(0)/k = d_{k-1}."""
    return dvec_f(A, k, sig)[k - 1]


# --------------------------------------------------------------- exact layer
def Qvec_x(A, sig=None):
    n = len(A)
    if sig is None:
        sig = R.sigma_all_x(A)
    return [Q(n) ** j * sig[j] / (fc.fact(j) * fc.binom(n, j) ** 2)
            for j in range(n + 1)]


def dEvec_x(A):
    n = len(A)
    r = [sum(row) for row in A]
    c = [sum(A[i][j] for i in range(n)) for j in range(n)]
    Er = [Q(fc.e_k(r, j), fc.binom(n, j)) for j in range(n + 1)]
    Ec = [Q(fc.e_k(c, j), fc.binom(n, j)) for j in range(n + 1)]
    return [(Er[j] - Er[j + 1]) + (Ec[j] - Ec[j + 1]) for j in range(n)]


def dvec_x(A, k, sig=None):
    n = len(A)
    Qv = Qvec_x(A, sig)
    dE = dEvec_x(A)
    g = Q(fc.fact(k), Q(n) ** k)
    return [dE[j] + g * (Qv[j + 1] - Qv[j]) for j in range(k)]


def to_QK(A, n, den=10 ** 6):
    """Rationalise then rescale EXACTLY to entry sum n (d_0 = 0 detects any
    drift off K_n -- the control that caught the first calibration bug)."""
    M = [[Q(float(x)).limit_denominator(den) for x in row] for row in A]
    s = sum(sum(r) for r in M)
    return [[Q(n) * x / s for x in r] for r in M]


def proj_K(A, n):
    """Nonnegative part rescaled to K_n (float)."""
    X = np.maximum(A, 0.0)
    s = X.sum()
    if s <= 0:
        return np.full_like(X, 1.0 / X.shape[0])
    return X * (n / s)


# ------------------------------------------------------ Omega_n reformulation
def omega_layer_gap_x(A, j):
    """On Omega_n, d_j >= 0 <=> n p_{j+1} >= (n-j) p_j with p_j = sigma_j/C(n,j);
    equivalently  n(j+1) C(n,j) sigma_{j+1}  -  (n-j)^2 C(n,j) sigma_j ... .
    Returns the cleared-denominator quantity
        G_j(A) = n (j+1) sigma_{j+1} - (n-j)^2 sigma_j / ...
    in the form  n^2 (j+1) sigma_{j+1} / (n-j)^2 - n sigma_j  is avoided;
    we return  Qv[j+1] - Qv[j]  exactly, which has the same sign."""
    Qv = Qvec_x(A)
    return Qv[j + 1] - Qv[j]


# ------------------------------------------------------------------- selftest
def selftest(log=print):
    """Calibration: the normalised form against reduce_scan_b2's literal form,
    against direct Phi_k, and the Bernstein evaluation against Phi_k(A_t)."""
    import reduce_scan_b2 as B2
    rng = np.random.default_rng(4242)
    bad = 0
    tot = 0

    log("C1  Q-form d-vector == reduce_scan_b2 literal d-vector (float)")
    for n in (4, 5, 6, 7):
        for k in range(2, n + 1):
            for _ in range(4):
                A = proj_K(rng.random((n, n)) ** rng.choice([1, 3]), n)
                a, b = dvec_f(A, k), B2.dvec_f(A, k)
                tot += 1
                if np.max(np.abs(a - b)) > 1e-9 * max(1, np.max(np.abs(b))):
                    bad += 1
                    log(f"    MISMATCH n={n} k={k}  {a} vs {b}")
    log(f"    {tot} comparisons, {bad} mismatches")

    log("C2  exact: d_0 = 0, sum_j d_j = 2 - gamma - Phi_k, Q_0 = Q_1 = 1")
    t2 = b2 = 0
    for n in (4, 5, 6):
        for k in range(2, n + 1):
            for _ in range(3):
                Ax = to_QK(proj_K(rng.random((n, n)), n), n)
                d = dvec_x(Ax, k)
                Qv = Qvec_x(Ax)
                ph = R.phi_x(Ax, k)
                F = 2 - Q(fc.fact(k), Q(n) ** k) - ph
                t2 += 1
                ok = (d[0] == 0 and sum(d) == F and Qv[0] == 1 and Qv[1] == 1)
                if not ok:
                    b2 += 1
                    log(f"    FAIL n={n} k={k} d0={d[0]} sum-F={sum(d)-F}")
    log(f"    {t2} exact points, {b2} failures")

    log("C3  Bernstein evaluation of f' == numerical derivative of Phi_k(A_t)")
    t3 = b3 = 0
    for n in (4, 5, 6):
        for k in range(2, n + 1):
            A = proj_K(rng.random((n, n)), n)
            J = np.full((n, n), 1.0 / n)
            d = dvec_f(A, k)
            for t in (0.0, 0.13, 0.5, 0.87, 1.0):
                fp = k * sum(d[j] * fc.binom(k - 1, j) * t ** (k - 1 - j)
                             * (1 - t) ** j for j in range(k))
                h = 1e-6
                tp, tm = min(t + h, 1.0), max(t - h, 0.0)
                num = (R.phi_f((1 - tp) * A + tp * J, k)
                       - R.phi_f((1 - tm) * A + tm * J, k)) / (tp - tm)
                t3 += 1
                if abs(fp - num) > 1e-4 * max(1.0, abs(fp)):
                    b3 += 1
                    log(f"    FAIL n={n} k={k} t={t} bern={fp} num={num}")
    log(f"    {t3} checks, {b3} failures")

    log("C4  MUTATION CONTROLS (each must FAIL the checks above)")
    n, k = 5, 4
    A = proj_K(rng.random((n, n)), n)
    Qv = Qvec_f(A)
    dE = dEvec_f(A)
    g = fc.fact(k) / float(n) ** k
    good = np.array([dE[j] + g * (Qv[j + 1] - Qv[j]) for j in range(k)])
    m1 = np.array([dE[j] + g * (Qv[j + 1] - Qv[j]) for j in range(k)])
    m1[1] += 1e-3                                     # perturbed coefficient
    m2 = np.array([dE[j] - g * (Qv[j + 1] - Qv[j]) for j in range(k)])
    m3 = np.array([g * (Qv[j + 1] - Qv[j]) for j in range(k)])   # dE dropped
    ref = B2.dvec_f(A, k)
    for nm, m in (("true", good), ("mut-shift", m1), ("mut-sign", m2),
                  ("mut-nodE", m3)):
        ok = np.max(np.abs(m - ref)) < 1e-9
        log(f"    {nm:10s} matches reference: {ok}"
            + ("  <-- expected" if (nm == "true") == ok else "  <-- WRONG"))
        if (nm == "true") != ok:
            bad += 1

    log(f"\nSELFTEST {'PASS' if bad + b2 + b3 == 0 else 'FAIL'}")
    return bad + b2 + b3


if __name__ == "__main__":
    if len(sys.argv) > 1 and sys.argv[1] == "selftest":
        selftest()
