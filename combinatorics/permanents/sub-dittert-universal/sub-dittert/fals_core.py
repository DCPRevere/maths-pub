"""
Core exact-rational machinery for the falsification pass against Cheon-Hwang.

    K_n = { A >= 0 : sum_ij a_ij = n },   r = row sums, c = column sums,
    sigma_k(A) = sum over k-subsets alpha of rows and k-subsets beta of columns
                 of per(A[alpha, beta])          (rows and columns independent),
    E_k(v)     = e_k(v) / C(n,k),
    P_k(A)     = sigma_k(A) / C(n,k)^2,
    Phi_k(A)   = E_k(r) + E_k(c) - P_k(A),
    CONJECTURE:  Phi_k(A) <= 2 - k!/n^k  on K_n, equality only at J_n/n.

Everything below is over Fraction.  No float takes part in any decision.
"""

from fractions import Fraction as Q
from itertools import combinations, permutations


def binom(n, k):
    if k < 0 or k > n:
        return 0
    r = 1
    for i in range(k):
        r = r * (n - i) // (i + 1)
    return r


def fact(k):
    r = 1
    for i in range(2, k + 1):
        r *= i
    return r


def gamma(n, k):
    return Q(fact(k), n ** k)


def bound(n, k):
    return Q(2) - gamma(n, k)


# --------------------------------------------------------------- sigma_k, slow
def sigma_k_direct(A, k):
    """Definition, verbatim: sum over (alpha, beta) of per(A[alpha, beta])."""
    n = len(A)
    tot = Q(0)
    for al in combinations(range(n), k):
        for be in combinations(range(n), k):
            for s in permutations(range(k)):
                p = Q(1)
                for t in range(k):
                    p *= A[al[t]][be[s[t]]]
                tot += p
    return tot


# --------------------------------------------------------------- sigma_k, fast
def sigma_k_ryser(A, k):
    """sigma_k from per(A + xJ) = sum_j x^{n-j} (n-j)! sigma_j(A), the order-n
    permanent by Ryser inclusion-exclusion.  Structurally unrelated to the
    direct enumeration above."""
    n = len(A)

    def umul(p, q):
        o = [Q(0)] * (len(p) + len(q) - 1)
        for i, a in enumerate(p):
            if a:
                for j, b in enumerate(q):
                    if b:
                        o[i + j] += a * b
        return o

    def uadd(p, q):
        m = max(len(p), len(q))
        return [(p[i] if i < len(p) else Q(0)) + (q[i] if i < len(q) else Q(0))
                for i in range(m)]

    tot = [Q(0)]
    for r in range(1, n + 1):
        for S in combinations(range(n), r):
            prod = [Q(1)]
            for i in range(n):
                s = [Q(0), Q(0)]
                for j in S:
                    s = uadd(s, [A[i][j], Q(1)])
                prod = umul(prod, s)
            sgn = Q((-1) ** (n - r))
            tot = uadd(tot, [sgn * c for c in prod])
    while len(tot) < n + 1:
        tot.append(Q(0))
    return tot[n - k] / fact(n - k)


def e_k(v, k):
    e = [Q(1)] + [Q(0)] * k
    for x in v:
        for j in range(k, 0, -1):
            e[j] += e[j - 1] * x
    return e[k]


def phi(A, k, sigma=None):
    """Phi_k(A) from the raw definition."""
    n = len(A)
    r = [sum(row) for row in A]
    c = [sum(A[i][j] for i in range(n)) for j in range(n)]
    if sigma is None:
        sigma = sigma_k_ryser(A, k)
    return (Q(e_k(r, k), binom(n, k)) + Q(e_k(c, k), binom(n, k))
            - Q(sigma, binom(n, k) ** 2))


def margin(A, k):
    """bound - Phi_k(A).  Negative  <=>  COUNTEREXAMPLE."""
    n = len(A)
    return bound(n, k) - phi(A, k)


# ------------------------------------------------------- structured closed forms
def phi_rank_one(x, y, k):
    """A = x y^T with (sum x)(sum y) = n.  sigma_k = k! e_k(x) e_k(y);
    r = (sum y) x,  c = (sum x) y."""
    n = len(x)
    sx, sy = sum(x), sum(y)
    ex, ey = e_k(x, k), e_k(y, k)
    ekr = sy ** k * ex
    ekc = sx ** k * ey
    sig = fact(k) * ex * ey
    return (Q(ekr, binom(n, k)) + Q(ekc, binom(n, k))
            - Q(sig, binom(n, k) ** 2))


def phi_direct_sum(sizes, masses, k):
    """A = block-diagonal, block i is p_i x p_i with every entry m_i/p_i^2
    (so block mass m_i, every row and column sum of that block m_i/p_i).
    sigma_j(block i) = C(p_i,j)^2 j! (m_i/p_i^2)^j;  sigma_k = convolution."""
    n = sum(sizes)
    # sigma of each block, as a list indexed by j
    sig = [Q(1)] + [Q(0)] * k
    for p, m in zip(sizes, masses):
        a = Q(m, p * p)
        blk = [Q(binom(p, j) ** 2 * fact(j)) * a ** j for j in range(k + 1)]
        new = [Q(0)] * (k + 1)
        for j in range(k + 1):
            if sig[j]:
                for t in range(k + 1 - j):
                    new[j + t] += sig[j] * blk[t]
        sig = new
    rows = []
    for p, m in zip(sizes, masses):
        rows += [Q(m, p)] * p
    ek = e_k(rows, k)
    return (Q(2) * Q(ek, binom(n, k)) - Q(sig[k], binom(n, k) ** 2))


def sigma_k_aJ_bI(n, k, a, b):
    """sigma_k(a J_n + b I_n), exact closed form.

    A k x k submatrix (alpha, beta) with |alpha cap beta| = m is a J_k plus b
    times a partial permutation matrix of rank m, whose permanent is
    sum_s C(m,s) b^s a^{k-s} (k-s)!.  The number of (alpha, beta) pairs with a
    given m is C(n,m) C(n-m,k-m) C(n-k,k-m)."""
    tot = Q(0)
    for m in range(0, k + 1):
        cnt = binom(n, m) * binom(n - m, k - m) * binom(n - k, k - m)
        if not cnt:
            continue
        per = Q(0)
        for s in range(m + 1):
            per += Q(binom(m, s) * fact(k - s)) * b ** s * a ** (k - s)
        tot += cnt * per
    return tot


def phi_perm_pencil(n, k, t):
    """A = (1-t) J_n/n + t P for ANY permutation matrix P.  sigma_k is invariant
    under independent row and column permutations and a J is too, so every
    permutation gives the same value as P = I.  All row and column sums are 1."""
    a, b = Q(1 - t, 1) / n if not isinstance(t, Q) else (Q(1) - t) / n, t
    a = (Q(1) - Q(t)) / n
    b = Q(t)
    sig = sigma_k_aJ_bI(n, k, a, b)
    return Q(2) - Q(sig, binom(n, k) ** 2)


def hessian_eigs(n, k):
    """Exact tangent-space eigenvalues of the Hessian of
    F = (2 - k!/n^k) - Phi_k  at J_n/n, restricted to T = { sum X = 0 }.

        lam_(V|V) = k(k-1) k! / (n^k (n-1)^2) = k(k-1) gamma / (n-1)^2,
                    multiplicity (n-1)^2
        lam_fused = k(k-1) (1 - k!/n^k) / (n-1) = k(k-1)(1 - gamma)/(n-1),
                    multiplicity 2(n-1)

    Convention: H is the matrix of second partial derivatives, so
    F(J/n + tX) = t^2 * (1/2) X^T H X + O(t^3).  This is the convention of
    hessian.py, against which both formulas are checked exactly.
    POSITIVE = J_n/n is a strict local MAXIMUM of Phi_k.

    Returns (lam_VV, mult_VV, lam_fused, mult_fused)."""
    g = gamma(n, k)
    lam_vv = Q(k * (k - 1)) * g / Q((n - 1) ** 2)
    lam_fu = Q(k * (k - 1), n - 1) * (Q(1) - g)
    return lam_vv, (n - 1) ** 2, lam_fu, 2 * (n - 1)
