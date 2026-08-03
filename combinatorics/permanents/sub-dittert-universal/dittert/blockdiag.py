"""
Block-diagonalisation of the invariant Gram matrices.

WHY THIS EXISTS.  The certificate constrains two B x B matrices to be positive
semidefinite, with B = 350 at n = 5.  An interior-point solver factorises a KKT
system dense in the SCALED cone dimension B(B+1)/2 = 61425, so it needs about
61425^2 doubles ~ 30 GB per cone.  With two cones that exhausted 61 GB of RAM
plus 20 GB of swap and crashed the machine.  A first-order solver survives but
returns a residual (5.6e-5) larger than the margin we must round (1.0e-4), which
is useless.  Neither solver can do n = 5 as posed.

WHAT FIXES IT.  Both Gram matrices are constrained to lie in the commutant of a
permutation representation.  By Schur's lemma the commutant is isomorphic to a
direct sum of small full matrix algebras,

    A  ~  (+)_lambda  R^{d_lambda x d_lambda},        sum_lambda d_lambda^2 = dim A,

and X in A is positive (semi)definite if and only if every block M_lambda(X) is.
So ONE cone of size 350 becomes a handful of cones of size at most a dozen or so,
and interior-point becomes both affordable and accurate.

WHAT THIS IS NOT.  The block-diagonalising basis is computed in floating point
and is NOT part of any proof.  It is a solver preconditioner and nothing more.
The certificate is still assembled as sum_k x_k E_k with x_k rational, and still
verified by exact rational LDL^T in the ORIGINAL basis.  A numerical error here
can only cost us a certificate; it can never create a false one.

METHOD (Murota-Kanno-Kojima-Kojima / de Klerk-Dobre-Pasechnik).
  1. Take a random symmetric R in the commutant.  Its eigenspaces are the
     irreducible constituents: an eigenvalue of M_lambda(R) appears with
     multiplicity m_lambda = dim of the irreducible.
  2. Two eigenspaces carry the same irreducible iff some element of the commutant
     maps one onto the other.  A second random element X0 detects this generically.
  3. Inside one isomorphism class, transport a basis from a chosen root eigenspace
     to the others THROUGH X0.  Because Hom_G(W,W) = R for a real-type
     irreducible, the transported bases are coherent up to one positive scalar,
     which normalisation removes.
  4. In those coherent bases, V_i^T X V_j = M_lambda(X)_{ij} * I for every X in the
     commutant.  That scalar is the block entry.

Step 4 is CHECKED numerically (`scalar_defect`), not assumed.  It is exactly the
step that fails if some irreducible is of complex or quaternionic type, and a
silent failure there would produce wrong blocks.
"""

import numpy as np


def basis_permutations(basis, gens):
    """Permutation of the Gram basis induced by each group generator."""
    from symmetry import act
    index = {m: k for k, m in enumerate(basis)}
    return [np.array([index[act(g, m)] for m in basis], dtype=np.int64) for g in gens]


def orbit_pairs(orbs, B):
    """Each orbit as a pair of index arrays (rows, cols) into a B x B matrix."""
    out = []
    for orb in orbs:
        codes = np.asarray(orb, dtype=np.int64)
        out.append((codes // B, codes % B))
    return out


def _random_commutant_element(pairs, B, rng):
    """A random symmetric element of the commutant: sum of orbits with random weights."""
    X = np.zeros((B, B))
    for (r, c) in pairs:
        X[r, c] = rng.standard_normal()
    return 0.5 * (X + X.T)


def _eigenspaces(R, tol):
    """Eigen-decompose a symmetric matrix and group columns by eigenvalue."""
    w, V = np.linalg.eigh(R)
    groups, start = [], 0
    for k in range(1, len(w) + 1):
        if k == len(w) or w[k] - w[k - 1] > tol:
            groups.append(V[:, start:k])
            start = k
    return w, groups


def block_structure(orbs, B, seed=20260728, tol=1e-6, verbose=True, dims_only=False):
    """
    Return the linear maps sending orbit coefficients to the small blocks.

    Output: list of pairs (C, m) with C.shape == (d, d, r) and m the dimension of
    the irreducible.  For a coefficient vector x of length r, block lambda is
    M = C @ x, i.e. M[i,j] = sum_k C[i,j,k] x[k].  X = sum_k x_k E_k is positive
    definite iff every M is; the spectrum of X is the union of the block spectra,
    each eigenvalue repeated m times.
    """
    rng = np.random.default_rng(seed)
    pairs = orbit_pairs(orbs, B)
    r = len(pairs)

    R = _random_commutant_element(pairs, B, rng)
    _, spaces = _eigenspaces(R, tol)
    X0 = _random_commutant_element(pairs, B, rng)

    # --- which eigenspaces carry the same irreducible?  X0 links them.
    s = len(spaces)
    link = [[False] * s for _ in range(s)]
    for a in range(s):
        for b in range(a + 1, s):
            M = spaces[a].T @ X0 @ spaces[b]
            link[a][b] = link[b][a] = np.linalg.norm(M) > 1e-8

    parent = list(range(s))

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    for a in range(s):
        for b in range(a + 1, s):
            if link[a][b]:
                ra, rb = find(a), find(b)
                if ra != rb:
                    parent[max(ra, rb)] = min(ra, rb)

    classes = {}
    for a in range(s):
        classes.setdefault(find(a), []).append(a)

    # --- coherent bases inside each class, transported through X0
    blocks, defect = [], 0.0
    for members in classes.values():
        root = members[0]
        m = spaces[root].shape[1]
        V = [spaces[root]]
        for a in members[1:]:
            W = spaces[a] @ (spaces[a].T @ X0 @ spaces[root])
            scale = np.sqrt(np.sum(W * W) / m)
            if scale < 1e-12:
                raise RuntimeError("transport through X0 collapsed; retry with a new seed")
            V.append(W / scale)
        d = len(V)

        if dims_only:
            # Only the shape of the algebra is wanted (how the SDP scales in n).
            # Skip the O(sum d^2 * B^2) coefficient extraction.
            blocks.append((np.zeros((d, d, 0)), m))
            continue

        C = np.zeros((d, d, r))
        for i in range(d):
            for j in range(d):
                Y = V[j] @ V[i].T                      # B x B
                for k, (rr, cc) in enumerate(pairs):
                    C[i, j, k] = Y[cc, rr].sum() / m
        blocks.append((C, m))

        # --- CHECK step 4: V_i^T X V_j really is a scalar matrix.
        for _ in range(2):
            Xr = _random_commutant_element(pairs, B, rng)
            for i in range(d):
                for j in range(d):
                    M = V[i].T @ Xr @ V[j]
                    sc = np.trace(M) / m
                    defect = max(defect, np.max(np.abs(M - sc * np.eye(m))))

    # The orbits passed in are SYMMETRISED (each merged with its transpose), so r
    # counts symmetric invariant matrices, not the whole commutant.  Hence the
    # dimension identity to check is sum d(d+1)/2 = r, not sum d^2 = r.  Together
    # with sum d*m = B these pin the block sizes down completely.
    dims = sorted((C.shape[0] for C, _ in blocks), reverse=True)
    tri = sum(d * (d + 1) // 2 for d in dims)
    covered = sum(C.shape[0] * m for C, m in blocks)
    if verbose:
        print(f"    symmetric invariant dim r = {r}; blocks {dims}")
        print(f"    sum d(d+1)/2 = {tri} vs r = {r}"
              f"  {'OK' if tri == r else '*** MISMATCH ***'}")
        print(f"    sum d*m      = {covered} vs B = {B}"
              f"  {'OK' if covered == B else '*** MISMATCH ***'}")
        print(f"    scalar-multiple defect = {defect:.3e}  "
              f"{'(real type confirmed)' if defect < 1e-6 else '*** NOT SCALAR ***'}")
    if tri != r:
        raise RuntimeError(f"sum of d(d+1)/2 = {tri} != symmetric invariant dimension {r}")
    if covered != B:
        raise RuntimeError(f"sum of d*m = {covered} != basis size {B}")
    if defect > 1e-6:
        raise RuntimeError(f"blocks are not scalar on isotypic pieces (defect {defect:.3e}); "
                           "an irreducible is probably not of real type")
    return blocks


def verify_against_dense(blocks, orbs, B, seed=7, trials=3):
    """
    Independent check that the blocks are right: for a random coefficient vector,
    the spectrum of the assembled B x B matrix must equal the union of the block
    spectra with each block eigenvalue repeated m times.

    This is decisive.  It tests the multiplicities, the block sizes and the entries
    all at once, and it uses the dense matrix -- the object the exact verification
    will actually work with -- as ground truth.  Returns the worst spectral
    discrepancy over the trials.
    """
    rng = np.random.default_rng(seed)
    pairs = orbit_pairs(orbs, B)
    worst = 0.0
    for _ in range(trials):
        x = rng.standard_normal(len(pairs))
        X = np.zeros((B, B))
        for k, (r, c) in enumerate(pairs):
            X[r, c] = x[k]
        X = 0.5 * (X + X.T)
        dense = np.sort(np.linalg.eigvalsh(X))
        parts = []
        for C, m in blocks:
            M = C @ x
            parts.append(np.repeat(np.linalg.eigvalsh(0.5 * (M + M.T)), m))
        recon = np.sort(np.concatenate(parts))
        if recon.shape != dense.shape:
            raise RuntimeError(f"block spectrum has {recon.size} eigenvalues, "
                               f"dense matrix has {dense.size}")
        worst = max(worst, float(np.max(np.abs(recon - dense))))
    return worst


if __name__ == "__main__":
    import os
    import sys
    sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
    from symmetry import generators, monomials
    from sos import DEG_BASIS, stab_generators, sym_pair_orbits

    n = int(sys.argv[1]) if len(sys.argv) > 1 else 4
    N = n * n
    basis = monomials(N, DEG_BASIS, mindeg=1)
    B = len(basis)
    print(f"n = {n}: Gram basis B = {B}  (one cone of this size is what crashed us)")

    print("  sigma_0, full group G:")
    g_orbs = sym_pair_orbits(basis, generators(n))
    gb = block_structure(g_orbs, B)
    print(f"    spectrum check vs dense matrix: {verify_against_dense(gb, g_orbs, B):.3e}")

    print("  sigma_11, stabiliser of position (1,1):")
    s_orbs = sym_pair_orbits(basis, stab_generators(n, (0, 0)))
    sb = block_structure(s_orbs, B)
    print(f"    spectrum check vs dense matrix: {verify_against_dense(sb, s_orbs, B):.3e}")

    big = max([C.shape[0] for C, _ in gb] + [C.shape[0] for C, _ in sb])
    print(f"\n  largest block: {big} x {big}   (was {B} x {B})")
    print(f"  interior-point KKT memory falls by a factor of about "
          f"{(B * (B + 1) // 2) ** 2 / max((big * (big + 1) // 2) ** 2, 1):.3g}")
