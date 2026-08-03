"""
THE GENERAL COLLAR BUDGET, uniform in k.

Everything exact over QQ.  Square roots enter only as rational UPPER bounds
(ceil_sqrt), so every inequality below is decided exactly and in the safe
direction.

WHAT IS ASSEMBLED.  With  B = A - J/n = L + z,  P = mu + nu = ||L||_F^2 / n,
Q = ||z||_F^2, Theorem C and Theorem X1 give

    F  =  F_line(x,y)  +  sum_{m=2}^{k} t_m sigma_m(z)  +  sum_{d=3}^{k} t_d X_d,
    X_d = sum_{j=1}^{d-1} X_{d,j}.

Three inputs are consumed:

  (L)  F_line  >=  (1/2) lam_line(n,k) P            [pincer_line, the paper]
  (S)  sigma_m(z) >= -C_m Q  for 3 <= m <= k        [THE SIBLING'S INTERFACE]
  (C)  |X_{d,j}| <= V_{j,d-j} n^{d-j} P^{(d-j)/2} Q^{j/2}   [Lemma CB below]

LEMMA CB (the cross-term cap).  |kappa^{(d,j)}_{r,r'}| <= A2(w) n^m P^{w/2}
with w = m-r-r', m = d-j, because c(m,p,N) <= N^m <= n^m and
|e_u(x)| <= A(u) mu^{u/2} with A(u) = D_u/u! the derangement ratio (A(1) = 0);
and |Theta_j[r,r']| <= W(j,r,r') Q^{j/2} P^{(r+r')/2} with
W(j,r,r') = j! C(r+j-1,j-1) C(r'+j-1,j-1), by Claim C atom by atom.  The two
P-powers ALWAYS add to P^{m/2}: the line suppression at (d,j) is P^{(d-j)/2}
whatever (r,r') is.  Hence V_{j,m} = sum over survivors of A2(m-r-r') W(j,r,r').

Only (K3) and confinement are consumed here: Q <= Q_c = n-1+rho^2 and
P <= u_max.  (K1), (K2), (K4) are consumed inside C_m and inside the merge.

THE BUDGET.  Splitting the j = 1 block (which carries sqrt(Q), not Q) off the
centred budget by AM-GM at the optimal weight,

    Psi(n,k) = (2/t_2) [ sum_{m=3}^k t_m C_m + G2 + g1^2 / (2 lam_line) ]  <  1

is sufficient for F >= 0 on the collar, and Psi < 1/2 leaves the quarter-budget
that a stability form needs.  Ntilde(k) is the least N with Psi(n,k) < 1 for
all n >= N.

Usage:  imported by graded_verify_collar.py; runnable for its own table.
"""

import sys
from fractions import Fraction as Fr
from math import comb, factorial, isqrt

from collar_core import c_coef, survivors
from pincer_line import lam_line, t_coef, u_max

# --------------------------------------------------------------- helpers


def ceil_sqrt(x, E=10 ** 12):
    """A rational r with r >= sqrt(x), accurate to RELATIVE 1/E.

    Absolute rounding is useless here: u_max is of order k!/n^k, so an absolute
    1e-15 floor would swamp sqrt(u_max) at large k and inflate every threshold.
    Writing x = a/b and sqrt(x) = sqrt(ab)/b makes the error relative.
    Rounding is always upward, and every use is on the large side of an
    inequality, so the direction is safe."""
    if x == 0:
        return Fr(0)
    assert x > 0
    a, b = x.numerator, x.denominator
    r = isqrt(a * b * E * E) + 1
    out = Fr(r, b * E)
    assert out * out >= x
    return out


def derange(u):
    """D_u, the derangement numbers.  A(u) = D_u/u! is the sum of the absolute
    values of the coefficients expressing e_u in power sums when p_1 = 0, so
    |e_u(x)| <= A(u) mu^{u/2}; A(1) = 0 is exactly e_1(x) = 0."""
    d = [1, 0]
    while len(d) <= u:
        m = len(d)
        d.append((m - 1) * (d[m - 1] + d[m - 2]))
    return d[u]


def A_e(u):
    return Fr(derange(u), factorial(u))


def A2(w):
    """sum_{u+v=w} A(u) A(v)."""
    return sum(A_e(u) * A_e(w - u) for u in range(w + 1))


def W_coef(j, r, rp):
    """The atom-count cap on Theta_j[r,r']: j! C(r+j-1,j-1) C(r'+j-1,j-1).

    sum over set partitions of |mu(pi)| is j!, and the (alpha,beta) count is
    the two binomials, so this bounds the sum of |atom coefficients|, which is
    all Claim C needs."""
    return Fr(factorial(j) * comb(r + j - 1, j - 1) * comb(rp + j - 1, j - 1))


_VCACHE = {}


def V(j, m):
    """V_{j,m} = sum over survivors (r,r') of A2(m-r-r') W(j,r,r')."""
    if (j, m) not in _VCACHE:
        _VCACHE[(j, m)] = sum(A2(m - r - rp) * W_coef(j, r, rp)
                              for (r, rp) in survivors(j, m))
    return _VCACHE[(j, m)]


# --------------------------------------------------------- collar constants


def rho2(n, k):
    return Fr((n - 1) * factorial(k), n ** (k - 1))


def Q_cap(n, k):
    """(K3) on the collar, transferred to z: L and z are Frobenius-orthogonal,
    so Q(z) <= Q(B) <= n - 1 + rho^2."""
    return Fr(n - 1) + rho2(n, k)


def P_cap(n, k):
    """Confinement: mu + nu <= u_max(n,k)."""
    return u_max(n, k)


def eta(n, k):
    """The collar's replacement for 1/n in every odd-power one-sided step:
    z_ij >= -(1/n + x_i + y_j) >= -(1/n + Delta), Delta <= sqrt(2 P)."""
    return Fr(1, n) + ceil_sqrt(2 * P_cap(n, k))


# ------------------------------------------------------------ the two blocks


def g1(n, k):
    """The j = 1 aggregate: sum_d t_d V_{1,d-1} n^{d-1} u_max^{(d-2)/2}.
    Multiplies sqrt(P) sqrt(Q)."""
    su = ceil_sqrt(P_cap(n, k))
    tot = Fr(0)
    for d in range(3, k + 1):
        v = V(1, d - 1)
        if v:
            tot += t_coef(n, k, d) * v * Fr(n) ** (d - 1) * su ** (d - 2)
    return tot


def G2(n, k, drop_t=None):
    """The j >= 2 aggregate; multiplies Q.

    drop_t = d  omits the t_d factor from layer d, which is mutation control
    M1: a dropped t_d is one of the two historically real errors."""
    su = ceil_sqrt(P_cap(n, k))
    sQ = ceil_sqrt(Q_cap(n, k))
    tot = Fr(0)
    for d in range(3, k + 1):
        td = Fr(1) if drop_t == d else t_coef(n, k, d)
        for j in range(2, d):
            m = d - j
            v = V(j, m)
            if v:
                tot += td * v * Fr(n) ** m * su ** m * sQ ** (j - 2)
    return tot


def Psi(n, k, C, drop_t=None):
    """The budget functional.  C is a callable C(m, n, k) -> Fraction, the
    SIBLING'S interface constants for sigma_m(z) >= -C_m Q on the collar."""
    t2 = t_coef(n, k, 2)
    core = sum(t_coef(n, k, m) * C(m, n, k) for m in range(3, k + 1))
    a = g1(n, k)
    lam = lam_line(n, k)
    return (2 / t2) * (core + G2(n, k, drop_t=drop_t) + a * a / (2 * lam))


def Ntilde(k, C, lo=5, hi=3000, want=1):
    """Least N such that Psi(n,k) < want, with the tail checked rather than
    assumed: after the first crossing the condition is re-verified on a grid
    up to hi and at hi itself.  Returns None if no crossing below hi."""
    n0 = max(lo, k + 1)
    N = None
    for n in range(n0, hi + 1):
        if Psi(n, k, C) < want:
            N = n
            break
    if N is None:
        return None
    step = max(1, (hi - N) // 40)
    for n in list(range(N, hi + 1, step)) + [hi]:
        if not Psi(n, k, C) < want:
            return None
    return N


# ------------------------------------------------------------- the merge


def dbl_coef(u, v):
    """The coefficient of the double-edge atom D_{u,v} = sum_ij z_ij^2 x_i^u
    y_j^v inside Theta_2[u,v].  It is (u+1)(v+1)/2: the only partition pair
    with no singleton block is the coarse one, contributing mu = -1 twice and
    (u+1)(v+1) exponent splittings, divided by j! = 2."""
    return Fr((u + 1) * (v + 1), 2)


def merge_coefficient(n, k, u, v, drop_merge_side=False):
    """The weight at which D_{u,v} must be charged ONCE.

    Two independent sources reach the same invariant:
      merge side  every odd layer m with m-2 >= a = u+v, through the one-sided
                  step  p_m(z) >= -sum_ij (1/n + x_i + y_j)^{m-2} z_ij^2,
                  whose binomial expansion is sum_a C(m-2,a) n^{-(m-2-a)} Xi_a
                  and Xi_a = sum_{u+v=a} C(a,u) D_{u,v};
      cross side  the layer d = a + 2 cross term at j = 2, at w = 0, whose
                  coefficient is (-1)^a c(a,u,n-2) and whose D_{u,v} content is
                  dbl_coef(u,v).

    Counting once deletes the double count, NOT a coefficient: the weight is
    the SUM.  At k = 4 and (u,v) = (1,0) this is t_3 (3n-4)/3, the paper's
    value, here derived rather than observed.

    drop_merge_side reproduces the historical error (the cross side alone,
    t_3 (n-2)): mutation control M2.
    """
    a = u + v
    tot = Fr(0)
    if not drop_merge_side:
        for m in range(3, k + 1, 2):
            if m - 2 >= a:
                tot += (t_coef(n, k, m) * Fr(factorial(m - 1), m)
                        * comb(m - 2, a) * comb(a, u) * Fr(1, n) ** (m - 2 - a))
    d = a + 2
    if d <= k:
        tot += dbl_coef(u, v) * t_coef(n, k, d) * c_coef(a, u, n - 2)
    return tot


# ------------------------------------- a named instance of the interface


def C_paper(m, n, k):
    """The sibling's constants as the paper has them at m = 3, 4, 5, with the
    collar degradation 1/n -> eta applied to every odd-power one-sided step
    (Lemma M below), and the ansatz C_m <= c_star lam^{m-2} above that.

    This is ONE instantiation.  Psi is stated for arbitrary C_m; nothing in
    the collar argument depends on these values.
    """
    b = Fr(n - 1, n)
    e = eta(n, k)
    if m == 3:
        return Fr(2, 3) * e
    if m == 4:
        return Fr(3, 2) * b
    if m == 5:
        return Fr(24, 5) * e ** 3 + Fr(10, 3) * b + 8 * b * b
    return C_ansatz(m, n, k)


C_STAR = Fr(12)
C_LAM = Fr(3)


def C_ansatz(m, n, k):
    """C_m <= c_star lam^{m-2}, the growth law the assembly is priced against."""
    return C_STAR * C_LAM ** (m - 2)


def C_pure_ansatz(m, n, k):
    return C_ansatz(m, n, k)


# ----------------------------------------------------------------- report


def main():
    global C_STAR, C_LAM
    out = []

    def log(*a):
        s = " ".join(str(x) for x in a)
        print(s)
        out.append(s)

    log("=" * 74)
    log("THE GENERAL COLLAR BUDGET")
    log("=" * 74)
    log("")
    log("V_{j,m}, the aggregate cross cap (k-free, n-free):")
    log("      m =      1        2        3        4        5")
    for j in range(1, 7):
        log(f"  j={j}  " + "  ".join(f"{str(V(j, m)):>7s}" for m in range(1, 6)))
    log("")
    log("Ntilde(k) under the named interface C_paper (c_star = "
        f"{C_STAR}, lam = {C_LAM} above m = 5):")
    log("   k |  Ntilde |  Psi(Ntilde)  |  Psi(Ntilde-1)")
    for k in range(3, 13):
        N = Ntilde(k, C_paper)
        if N is None:
            log(f"  {k:2d} |   none found below 4000")
            continue
        p0 = float(Psi(N, k, C_paper))
        p1 = float(Psi(N - 1, k, C_paper)) if N - 1 >= max(5, k) else float("nan")
        log(f"  {k:2d} | {N:6d}  |  {p0:11.6f}  |  {p1:11.4f}")
    log("")
    log("THE COLLAR IS NOT THE BOTTLENECK.  Ntilde with the sibling's C_m set")
    log("to zero is the threshold the CROSS TERMS alone impose:")
    log("   k |  collar-only Ntilde  |  with C_paper  |  N/k^2   |  N/k^2.5")
    for k in list(range(4, 13)) + [14, 16, 20, 24, 30]:
        N0 = Ntilde(k, lambda m, n, kk: Fr(0), hi=100000)
        N1 = Ntilde(k, C_paper, hi=100000)
        log(f"  {k:2d} | {str(N0):>18s}   | {str(N1):>12s}  |"
            f" {N1 / k ** 2:7.3f}  | {N1 / k ** 2.5:8.4f}")
    log("   Measured: Ntilde ~ 0.7 k^2 over 4 <= k <= 30.  The analytic tail is")
    log("   O(k^{5/2}): the binding block is (d,j) = (k,k-1), whose weight")
    log("   V_{k-1,1} = 2(k-1)(k-1)! runs against n^{3/2-k}.")
    log("")
    log("Sensitivity of Ntilde to the sibling's growth law C_m = c_star lam^{m-2}:")
    log("   c_star  lam |" + "".join(f"  k={k:<2d}" for k in range(4, 11)))
    keep = (C_STAR, C_LAM)
    for cs in (Fr(4), Fr(12), Fr(40)):
        for lam in (Fr(2), Fr(3), Fr(5)):
            C_STAR, C_LAM = cs, lam
            row = []
            for k in range(4, 11):
                N = Ntilde(k, C_pure_ansatz)
                row.append(f"{N if N else '-':>6}")
            log(f"   {str(cs):>6s} {str(lam):>4s} |" + "".join(row))
    C_STAR, C_LAM = keep
    log("")
    log("The merge coefficient of D_{u,v}, charged once at the summed weight:")
    for (k, u, v) in ((4, 1, 0), (5, 1, 0), (5, 0, 1), (5, 1, 1), (5, 2, 0),
                      (6, 1, 0), (7, 1, 0)):
        n = 20
        m1 = merge_coefficient(n, k, u, v)
        m2 = merge_coefficient(n, k, u, v, drop_merge_side=True)
        log(f"   k={k} (u,v)=({u},{v})  n=20 : full {float(m1):.6e}"
            f"   cross-side-only {float(m2):.6e}"
            f"   ratio {float(m1 / m2):.6f}")
    log("")
    log("k = 4 check, in the paper's normalisation 2 t_3 / t_2 * coef:")
    for n in (10, 12, 16, 20):
        got = merge_coefficient(n, 4, 1, 0) / t_coef(n, 4, 3)
        log(f"   n={n:3d}  merge_coefficient / t_3 = {got}"
            f"   (3n-4)/3 = {Fr(3 * n - 4, 3)}   equal: {got == Fr(3 * n - 4, 3)}")
    log("=" * 74)
    with open("results/collar_budget.log", "w") as fh:
        fh.write("\n".join(out) + "\n")
    return 0


if __name__ == "__main__":
    sys.exit(main())
