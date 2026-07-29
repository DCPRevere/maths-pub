"""
Exact rational Hessian of F(b) = (2 - gamma) - [E_k(r) + E_k(c) - P_k] at b = 0,
restricted to the tangent space T = { X : sum_ij X_ij = 0 } of K_n.

Everything is over Q.  Floating point is used nowhere.

WHY THIS MATTERS.  The standing failure mode of this project (METHODS section 2)
is that a TIGHT bound forces the optimal Gram matrix to be singular, and a
singular Gram cannot be rounded to exact rationals.  A positive DEFINITE Hessian
on T says the interior maximum is nondegenerate, so the only forced kernel
direction is the constraint normal (1,...,1), which centring and the exclusion of
the constant monomial remove anyway.  If instead the Hessian had a kernel inside
T, exact rounding would be blocked and the target should be abandoned.

METHOD.  Let P = I - (1/N) J be the orthogonal projector onto T.  The compression
of H to T is P H P, whose spectrum is {0} (from the normal direction) together
with the spectrum of H restricted to T.  P H P is rational, so its characteristic
polynomial is computed exactly by Faddeev-LeVerrier, and eigenvalue multiplicities
are confirmed independently by exact nullity over Q -- never by a numerical
eigensolver.

REPRESENTATION-THEORETIC PREDICTION.  G = (S_n x S_n) : Z_2 acts on R^{n x n} by
permuting rows, permuting columns and transposing.  With V the (n-1)-dimensional
standard representation of S_n,

    R^{n x n} = R^n (x) R^n = (1 + V) (x) (1 + V) = 1 + (V|1) + (1|V) + (V|V).

The tangent space T drops the trivial summand, leaving (V|1) + (1|V) + (V|V) of
dimensions (n-1), (n-1) and (n-1)^2.  Transposition swaps the first two, fusing
them into ONE irreducible of dimension 2(n-1); and V|V is irreducible for
S_n x S_n.  So T is a sum of exactly TWO non-isomorphic irreducibles, each of
multiplicity one.  Since H is G-equivariant, Schur's lemma forces H|_T to be a
SCALAR on each.  The Hessian therefore has exactly two eigenvalues, of
multiplicities (n-1)^2 and 2(n-1), for every n and k -- this is not a numerical
coincidence, and the script checks the prediction rather than assuming it.
"""

import os
import sys
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import expand                                                    # noqa: E402


# --------------------------------------------------------- exact linear algebra
def mat_mul(A, B):
    n, m, p = len(A), len(B), len(B[0])
    out = [[F(0)] * p for _ in range(n)]
    for i in range(n):
        Ai = A[i]
        Oi = out[i]
        for t in range(m):
            a = Ai[t]
            if a:
                Bt = B[t]
                for j in range(p):
                    if Bt[j]:
                        Oi[j] += a * Bt[j]
    return out


def mat_trace(A):
    return sum(A[i][i] for i in range(len(A)))


def mat_sub_scalar(A, s):
    return [[A[i][j] - (s if i == j else 0) for j in range(len(A))]
            for i in range(len(A))]


def identity(n):
    return [[F(1) if i == j else F(0) for j in range(n)] for i in range(n)]


def charpoly(A):
    """Faddeev-LeVerrier: exact coefficients of det(xI - A), highest first."""
    n = len(A)
    coeffs = [F(1)]
    M = [[F(0)] * n for _ in range(n)]
    for k in range(1, n + 1):
        # M_k = A M_{k-1} + c_{k-1} I
        if k == 1:
            M = identity(n)
        else:
            M = mat_mul(A, M)
            for i in range(n):
                M[i][i] += coeffs[-1]
        AM = mat_mul(A, M)
        c = -mat_trace(AM) / k
        coeffs.append(c)
    return coeffs


def rank(A):
    """Exact rank over Q by Gaussian elimination."""
    M = [row[:] for row in A]
    rows, cols = len(M), len(M[0])
    r = 0
    for c in range(cols):
        piv = None
        for i in range(r, rows):
            if M[i][c]:
                piv = i
                break
        if piv is None:
            continue
        M[r], M[piv] = M[piv], M[r]
        pv = M[r][c]
        M[r] = [x / pv for x in M[r]]
        for i in range(rows):
            if i != r and M[i][c]:
                f = M[i][c]
                M[i] = [M[i][j] - f * M[r][j] for j in range(cols)]
        r += 1
        if r == rows:
            break
    return r


def nullity(A):
    return len(A) - rank(A)


def is_positive_definite(A):
    """Exact rational LDL^T without pivoting; A symmetric.  True iff every
    pivot is strictly positive."""
    n = len(A)
    M = [row[:] for row in A]
    for k in range(n):
        if M[k][k] <= 0:
            return False, k
        p = M[k][k]
        for i in range(k + 1, n):
            f = M[i][k] / p
            if f:
                for j in range(k, n):
                    M[i][j] -= f * M[k][j]
            M[i][k] = F(0)
    return True, None


def poly_str(coeffs):
    n = len(coeffs) - 1
    parts = []
    for i, c in enumerate(coeffs):
        if not c:
            continue
        d = n - i
        s = f"{c}" if d == 0 else (f"{c}*x" if d == 1 else f"{c}*x^{d}")
        parts.append(s)
    return " + ".join(parts).replace("+ -", "- ")


# ------------------------------------------------------------ isotypic testing
def isotypic_bases(n):
    """Explicit rational bases of (V|1)+(1|V) [dimension 2(n-1)] and (V|V)
    [dimension (n-1)^2] inside the tangent space of R^{n x n}."""
    N = n * n

    def vec(f):
        return [F(f(i, j)) for i in range(n) for j in range(n)]

    rowcol = []
    for a in range(n - 1):                          # row-only patterns
        rowcol.append(vec(lambda i, j, a=a: (1 if i == a else 0)
                          - (1 if i == n - 1 else 0)))
    for a in range(n - 1):                          # column-only patterns
        rowcol.append(vec(lambda i, j, a=a: (1 if j == a else 0)
                          - (1 if j == n - 1 else 0)))
    tensor = []
    for a in range(n - 1):
        for b in range(n - 1):
            def f(i, j, a=a, b=b):
                ra = (1 if i == a else 0) - (1 if i == n - 1 else 0)
                cb = (1 if j == b else 0) - (1 if j == n - 1 else 0)
                return ra * cb
            tensor.append(vec(f))
    return rowcol, tensor


def apply(H, v):
    n = len(H)
    return [sum(H[i][j] * v[j] for j in range(n)) for i in range(n)]


def scalar_on(H, basis):
    """If H acts as a scalar on span(basis), return it; else None."""
    lam = None
    for v in basis:
        w = apply(H, v)
        nz = next((t for t, x in enumerate(v) if x), None)
        c = w[nz] / v[nz]
        if lam is None:
            lam = c
        if [c * x for x in v] != w:
            return None
    return lam


def report(n, k, verbose=True):
    d = expand.build(n, k)
    N = n * n
    H = expand.hessian(d["F"], N)

    # projector onto the tangent space sum X = 0
    P = [[(F(1) if i == j else F(0)) - F(1, N) for j in range(N)]
         for i in range(N)]
    PHP = mat_mul(mat_mul(P, H), P)

    cp = charpoly(PHP)
    rowcol, tensor = isotypic_bases(n)
    lam_rc = scalar_on(H, rowcol)
    lam_tn = scalar_on(H, tensor)

    if verbose:
        print(f"=== (n,k) = ({n},{k}) ===")
        print(f"  ambient dimension {N}, tangent dimension {N - 1}")
        print(f"  charpoly of P H P (exact over Q):")
        print(f"    {poly_str(cp)}")

    # multiplicities by exact nullity, and definiteness by exact LDL^T
    evals = {}
    for lam in {lam_rc, lam_tn} - {None}:
        m = nullity(mat_sub_scalar(PHP, lam))
        evals[lam] = m
    zero_mult = nullity(PHP)

    if verbose:
        print(f"  Schur prediction: H is scalar on each isotypic component")
        print(f"    (V|1)+(1|V), dim {2*(n-1)}: "
              f"{'scalar ' + str(lam_rc) if lam_rc is not None else 'NOT SCALAR'}")
        print(f"    (V|V),       dim {(n-1)**2}: "
              f"{'scalar ' + str(lam_tn) if lam_tn is not None else 'NOT SCALAR'}")
        for lam, m in sorted(evals.items()):
            print(f"  eigenvalue {lam} = {float(lam):.10f}, "
                  f"exact multiplicity (nullity over Q) = {m}")
        print(f"  eigenvalue 0 multiplicity = {zero_mult} "
              f"(expected 1: the constraint normal)")
        tot = sum(evals.values()) + zero_mult
        print(f"  multiplicities sum to {tot} (must be {N})")

    # positive definiteness on the tangent space, from an exact basis
    B = [[F(1) if t == i else F(0) for i in range(N - 1)] + [F(0)]
         for t in range(N - 1)]
    for t in range(N - 1):
        B[t][N - 1] = F(-1)                        # e_t - e_{N-1} spans T
    G = [[sum(B[a][i] * H[i][j] * B[b][j] for i in range(N) for j in range(N))
          for b in range(N - 1)] for a in range(N - 1)]
    pd, fail = is_positive_definite(G)
    if verbose:
        print(f"  exact rational LDL^T of H restricted to T (basis e_t - e_N): "
              f"{'POSITIVE DEFINITE' if pd else f'FAILED at pivot {fail}'}")
        print()
    return dict(charpoly=cp, evals=evals, zero_mult=zero_mult, pd=pd,
                lam_rc=lam_rc, lam_tn=lam_tn)


if __name__ == "__main__":
    targets = [(4, 3), (4, 4), (4, 2), (5, 3), (5, 4)]
    if len(sys.argv) > 1:
        targets = [tuple(int(x) for x in a.split(",")) for a in sys.argv[1:]]
    for (n, k) in targets:
        report(n, k)
