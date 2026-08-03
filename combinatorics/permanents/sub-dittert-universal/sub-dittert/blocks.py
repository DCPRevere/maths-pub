"""
Exact block-diagonalisation of the two Gram matrices at k = 3, SYMBOLICALLY in n.

This replaces the numerical block-diagonalisation of METHODS.md section 7.  There
the blocks are found in floating point from a random commutant element, and are
only a solver preconditioner.  Here they are derived in closed form, because the
whole point is to decide positive definiteness for EVERY n at once, and a
floating-point basis at one n cannot do that.

sigma_0.  Its Gram is G0 = a*I + b*A1 + c*A2 on the n^2 cells, where A1 is the
rook's-graph adjacency ("same row or same column, distinct cells") and
A2 = J - I - A1.  This is the Bose-Mesner algebra of K_n [] K_n, so G0 has exactly
three eigenvalues:

    theta_0 = a + 2(n-1) b + (n-1)^2 c        multiplicity 1
    theta_1 = a + (n-2) b - (n-1) c           multiplicity 2(n-1)
    theta_2 = a - 2 b + c                     multiplicity (n-1)^2

sigma_11.  Its Gram H is invariant under Stab((0,0)) = (S_{n-1} x S_{n-1}) : Z_2.
Split the cells into corner K = {(0,0)}, row R = {(0,j) : j > 0},
column C = {(i,0) : i > 0} and interior I = {(i,j) : i,j > 0}.  With V' the
standard (n-2)-dimensional representation of S_{n-1},

    R^n = <delta_0> + <1'> + V'        (two trivials and V'),
    R^{n^2} = (2.1 + V') (x) (2.1 + V')
            = 4(1|1) + 2(V'|1) + 2(1|V') + (V'|V').

Transposition fixes delta_0 (x) delta_0 and 1' (x) 1', swaps delta_0 (x) 1' with
1' (x) delta_0, and swaps (V'|1) with (1|V').  So over the FULL stabiliser:

    trivial type          multiplicity 3     -> a 3 x 3 block
    sign type             multiplicity 1     -> a 1 x 1 block
    Ind(V'|1) type        multiplicity 2     -> a 2 x 2 block, each eigenvalue
                                                of multiplicity 2(n-2)
    (V'|V') type          multiplicity 1     -> a 1 x 1 block, multiplicity (n-2)^2

Consistency, and it is a real check rather than decoration:
    sum d(d+1)/2 = 6 + 1 + 3 + 1 = 11 = the number of orbit parameters, and
    3 + 1 + 2*2(n-2) + (n-2)^2 = n^2.

H is positive definite if and only if all four blocks are.  Every block entry is a
Q(n)-linear form in the 11 orbit coefficients, so definiteness for all n becomes a
finite list of rational functions of n to be kept positive -- which is what Sturm
sequences can settle.

Explicit orthonormal multiplicity bases used below:
    trivial: u1 = 1_K,  u2 = (1_R + 1_C)/sqrt(2(n-1)),  u3 = 1_I/(n-1)
    sign:    w  = (1_R - 1_C)/sqrt(2(n-1))
    Ind:     p1 = v on R,  p2 = v on each row of I, scaled by 1/sqrt(n-1)
             (v any unit sum-zero vector on {1..n-1})
    (V'|V'): q  = v (x) v' on I, v, v' unit and sum-zero
"""

import os
import sys
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "dittert"))
sys.path.insert(0, HERE)
import general_k3 as g                                            # noqa: E402


# The 11 sigma_11 orbit keys, named for readability.  Cells are written relative
# to the fixed corner (0,0): row 0 and column 0 are special.
def svar_index():
    return {k: i for i, k in enumerate(g.build_symbolic_system(3)["svars"])}


def sigma0_eigs_sym(a, b, c, n):
    """The three eigenvalues of G0, as exact values at a given n."""
    return [a + 2 * (n - 1) * b + (n - 1) ** 2 * c,
            a + (n - 2) * b - (n - 1) * c,
            a - 2 * b + c]


def _cellclass(cell):
    i, j = cell
    if i == 0 and j == 0:
        return "K"
    if i == 0:
        return "R"
    if j == 0:
        return "C"
    return "I"


def h_entry(y, cell_u, cell_v, idx):
    """H[u][v] from the 11 orbit coefficients y, via the canonical key."""
    return y[idx[g.canon((cell_u, cell_v), True)]]


def blocks_numeric(n, y, idx):
    """
    The four blocks of H at a given n, computed exactly over Q from the orbit
    coefficients y (a list of 11 Fractions).

    Sums over the classes are done in closed form rather than by looping over all
    n^2 cells, so this is exact and fast for any n.  Representative cells:
      K  = (0,0)
      R  = (0,1), a second row cell (0,2)
      C  = (1,0), a second column cell (2,0)
      I  = (1,1), and (1,2) same row, (2,1) same column, (2,2) generic
    """
    K, R1, R2 = (0, 0), (0, 1), (0, 2)
    C1, C2 = (1, 0), (2, 0)
    I11, I12, I21, I22 = (1, 1), (1, 2), (2, 1), (2, 2)
    e = lambda u, v: h_entry(y, u, v, idx)                      # noqa: E731
    m = n - 1                                                    # |R| = |C| = m

    # ---- sums needed, all closed form in n
    # within R: diagonal e(R1,R1) once, off-diagonal e(R1,R2) m-1 times
    S_RR = e(R1, R1) + (m - 1) * e(R1, R2)
    S_RC = m * e(R1, C1)          # every pair (row cell, column cell) is
    # equivalent except when they "share" the corner -- they never do, since
    # (0,j) and (i,0) with i,j > 0 always have distinct rows and columns.
    S_KR = e(K, R1)
    S_KI = e(K, I11)
    S_RI_samecol = e(R1, I11)     # (0,j) with (i,j): same column
    S_RI_diffcol = e(R1, I12)     # (0,j) with (i,j'), j' != j
    S_RI = S_RI_samecol + (m - 1) * S_RI_diffcol      # over one row cell, all I
    S_II = (e(I11, I11) + (m - 1) * e(I11, I12) + (m - 1) * e(I11, I21)
            + (m - 1) * (m - 1) * e(I11, I22))        # one I cell against all I

    # ---- trivial-type 3 x 3 block, orthonormal basis u1, u2, u3
    # u1 = 1_K ; u2 = (1_R + 1_C)/sqrt(2m) ; u3 = 1_I/m
    A11 = e(K, K)
    A12 = (2 * m * S_KR) / _sqrt_sym(2 * m)
    A13 = (m * m * S_KI) / m
    # u2^T H u2 = [ sum over R,R + 2 sum over R,C + sum over C,C ] / (2m)
    A22 = (2 * m * S_RR + 2 * m * S_RC) / (2 * m)
    A23 = (2 * m * m * S_RI) / (_sqrt_sym(2 * m) * m)
    A33 = (m * m * S_II) / (m * m)
    Ablk = [[A11, A12, A13], [A12, A22, A23], [A13, A23, A33]]

    # ---- sign-type 1 x 1 block: w = (1_R - 1_C)/sqrt(2m)
    Bblk = (2 * m * S_RR - 2 * m * S_RC) / (2 * m)

    # ---- Ind(V'|1) 2 x 2 block, with v unit and sum-zero on {1..m}
    # p1 = v on R.  p1^T H p1 = sum_{j,j'} v_j v_j' e(R_j, R_j')
    #                          = e(R1,R1) - e(R1,R2)         (since sum v = 0)
    C11 = e(R1, R1) - e(R1, R2)
    # p2 = v on each row of I, normalised by sqrt(m)
    C22 = (e(I11, I11) - e(I11, I12)
           + (m - 1) * (e(I11, I21) - e(I11, I22)))
    C12 = (S_RI_samecol - S_RI_diffcol) * _sqrt_sym(m) / _sqrt_sym(m) ** 0
    C12 = (e(R1, I11) - e(R1, I12)) * _sqrt_sym(m)
    Cblk = [[C11, C12], [C12, C22]]

    # ---- (V'|V') 1 x 1 block: q = v (x) v' on I
    Dblk = (e(I11, I11) - e(I11, I12) - e(I11, I21) + e(I11, I22))
    return Ablk, Bblk, Cblk, Dblk


def _sqrt_sym(x):
    """Only ever used in pairs that cancel; kept explicit so the algebra is
    auditable.  Returns a float only when a genuine square root is needed, which
    the caller must avoid for exact work -- see blocks_rational below."""
    import math
    return math.sqrt(float(x))


def blocks_rational(n, y, idx):
    """
    The same four blocks, but CONGRUENT to them by a positive diagonal scaling, so
    every entry is rational.  Congruence by a positive diagonal preserves positive
    definiteness, which is all we need.

    Scaling used: u2 and w are left unnormalised (norm^2 = 2(n-1)), u3 unnormalised
    (norm^2 = (n-1)^2), p2 unnormalised (norm^2 = n-1).  Concretely we compute
    x^T H x for the UNNORMALISED vectors, giving D^{1/2} B D^{1/2} for the positive
    diagonal D of squared norms; that matrix is positive definite exactly when B is.
    """
    K, R1, R2 = (0, 0), (0, 1), (0, 2)
    C1 = (1, 0)
    I11, I12, I21, I22 = (1, 1), (1, 2), (2, 1), (2, 2)
    e = lambda u, v: h_entry(y, u, v, idx)                      # noqa: E731
    m = F(n - 1)

    S_RR = e(R1, R1) + (m - 1) * e(R1, R2)
    S_RC = m * e(R1, C1)
    S_KR = e(K, R1)
    S_KI = e(K, I11)
    S_RI = e(R1, I11) + (m - 1) * e(R1, I12)
    S_II = (e(I11, I11) + (m - 1) * e(I11, I12) + (m - 1) * e(I11, I21)
            + (m - 1) ** 2 * e(I11, I22))

    # unnormalised u1 = 1_K, u2 = 1_R + 1_C, u3 = 1_I
    A11 = e(K, K)
    A12 = 2 * m * S_KR
    A13 = m * m * S_KI
    A22 = 2 * m * S_RR + 2 * m * S_RC
    A23 = 2 * m * m * S_RI
    A33 = m * m * S_II
    Ablk = [[A11, A12, A13], [A12, A22, A23], [A13, A23, A33]]

    Bblk = 2 * m * S_RR - 2 * m * S_RC

    C11 = e(R1, R1) - e(R1, R2)
    C12 = m * (e(R1, I11) - e(R1, I12))
    C22 = m * (e(I11, I11) - e(I11, I12)
               + (m - 1) * (e(I11, I21) - e(I11, I22)))
    Cblk = [[C11, C12], [C12, C22]]

    Dblk = e(I11, I11) - e(I11, I12) - e(I11, I21) + e(I11, I22)
    return Ablk, Bblk, Cblk, Dblk


def blocks_rational_generic(n, y, idx, one):
    """
    The same four blocks as blocks_rational, but written so that `n` may be a
    rational FUNCTION of n and the entries `y` may be affine forms in unknowns.

    Only ring operations are used, and every entry is multiplied by scalars only,
    so the blocks stay LINEAR in y.  That is what lets the design step become a
    linear program.  The scaling is the same positive-diagonal congruence used in
    blocks_rational, so definiteness is unchanged.
    """
    K, R1, R2 = (0, 0), (0, 1), (0, 2)
    C1 = (1, 0)
    I11, I12, I21, I22 = (1, 1), (1, 2), (2, 1), (2, 2)
    e = lambda u, v: y[idx[g.canon((u, v), True)]]              # noqa: E731
    m = n - one                                                  # n - 1
    m1 = m - one                                                 # n - 2
    two = one + one

    S_RR = e(R1, R1) + e(R1, R2) * m1
    S_RC = e(R1, C1) * m
    S_KR = e(K, R1)
    S_KI = e(K, I11)
    S_RI = e(R1, I11) + e(R1, I12) * m1
    S_II = (e(I11, I11) + e(I11, I12) * m1 + e(I11, I21) * m1
            + e(I11, I22) * (m1 * m1))

    A11 = e(K, K)
    A12 = S_KR * (two * m)
    A13 = S_KI * (m * m)
    A22 = S_RR * (two * m) + S_RC * (two * m)
    A23 = S_RI * (two * m * m)
    A33 = S_II * (m * m)
    Ablk = [[A11, A12, A13], [A12, A22, A23], [A13, A23, A33]]

    Bblk = S_RR * (two * m) - S_RC * (two * m)

    C11 = e(R1, R1) - e(R1, R2)
    C12 = (e(R1, I11) - e(R1, I12)) * m
    C22 = (e(I11, I11) - e(I11, I12)
           + (e(I11, I21) - e(I11, I22)) * m1) * m
    Cblk = [[C11, C12], [C12, C22]]

    Dblk = e(I11, I11) - e(I11, I12) - e(I11, I21) + e(I11, I22)
    return Ablk, Bblk, Cblk, Dblk


def check_generic_agrees(ns=(4, 5, 6, 7), seed=11):
    """The generic version must reproduce blocks_rational exactly."""
    import random
    from fractions import Fraction as Fr
    idx = svar_index()
    rng = random.Random(seed)
    ok = True
    for n in ns:
        y = [Fr(rng.randint(-30, 30), rng.randint(1, 7)) for _ in range(11)]
        a = blocks_rational(n, y, idx)
        b = blocks_rational_generic(Fr(n), y, idx, Fr(1))
        same = (a[0] == b[0] and a[1] == b[1] and a[2] == b[2] and a[3] == b[3])
        print(f"  n={n}: generic block builder matches the concrete one: {same}")
        ok = ok and same
    return ok


def check_blocks(ns=(4, 5, 6, 7, 8), seed=3):
    """
    Verify the block decomposition against a direct eigendecomposition of the
    assembled n^2 x n^2 matrix, on RANDOM orbit coefficients.

    Random coefficients matter: a check on the actual certificate could pass by
    accident on a matrix with extra structure.  We compare the full spectrum with
    the union of the block spectra, each taken with its predicted multiplicity.
    """
    import random
    import numpy as np
    idx = svar_index()
    ok = True
    rng = random.Random(seed)
    for n in ns:
        y = [F(rng.randint(-40, 40), rng.randint(1, 9)) for _ in range(11)]
        cells = [(i, j) for i in range(n) for j in range(n)]
        Hm = np.array([[float(h_entry(y, u, v, idx)) for v in cells]
                       for u in cells])
        full = np.sort(np.linalg.eigvalsh(Hm))

        A, B, C, D = blocks_numeric(n, [float(t) for t in y], idx)
        eA = list(np.linalg.eigvalsh(np.array(A)))
        eC = list(np.linalg.eigvalsh(np.array(C)))
        pred = eA + [B] + eC * (2 * (n - 2)) + [D] * (n - 2) ** 2
        pred = np.sort(np.array(pred))
        err = float(np.max(np.abs(full - pred))) if len(pred) == len(full) else None
        print(f"  n={n}: full spectrum {len(full)} vs blocks {len(pred)}; "
              f"max difference {err:.3e}" if err is not None
              else f"  n={n}: LENGTH MISMATCH {len(full)} vs {len(pred)}")
        ok = ok and err is not None and err < 1e-9

        # and the rational (diagonally scaled) version must agree on definiteness
        Ar, Br, Cr, Dr = blocks_rational(n, y, idx)
        import numpy.linalg as la
        pd_full = bool(full[0] > 0)
        pd_blk = (la.eigvalsh(np.array([[float(x) for x in r] for r in Ar]))[0] > 0
                  and float(Br) > 0
                  and la.eigvalsh(np.array([[float(x) for x in r]
                                            for r in Cr]))[0] > 0
                  and float(Dr) > 0)
        if pd_full != pd_blk:
            print(f"    definiteness disagreement at n={n}: "
                  f"full {pd_full}, rational blocks {pd_blk}")
            ok = False
    return ok


if __name__ == "__main__":
    print("=== block decomposition of the sigma_11 Gram, checked against the "
          "full spectrum ===")
    ok = check_blocks()
    print("PASS" if ok else "FAIL")
    sys.exit(0 if ok else 1)
