"""
Symmetry-adapted Positivstellensatz for the Cheon-Hwang sub-Dittert conjecture.

Certificate sought, in centred coordinates b = A - J_n/n:

    F(b) = sigma_0(b) + sum_{ij} sigma_ij(b) (1/n + b_ij) + lambda(b) (sum_kl b_kl)

with F(b) = (2 - gamma(n,k)) - [E_k(r) + E_k(c) - P_k(J_n/n + b)]; sigma_0 and
every sigma_ij a sum of squares; lambda free.  The linear forms 1/n + b_ij are
exactly the constraints a_ij >= 0, and sum b_kl = 0 is the affine constraint of
K_n.  Every term on the right is then >= 0 on K_n, so F >= 0 on K_n.

SYMMETRY.  G = (S_n x S_n) : Z_2 permutes the variables, of order 2(n!)^2 = 1152
at n = 4.  Averaging any certificate over G lets us assume sigma_0 and lambda are
G-invariant and the family {sigma_ij} equivariant, so only TWO Gram matrices are
unknown: that of sigma_0 (G-invariant) and that of sigma_11 (invariant under the
stabiliser of the position (1,1)).

DEGREE, and why this is EASIER than Dittert at the same n.  deg F = k, not n.
At (n,k) = (4,3) that is 3, whereas Dittert at n = 4 has degree 4.  With a Gram
basis of degree exactly 1 we get deg sigma <= 2 and deg(sigma_ij * b_ij) <= 3,
which matches deg F = 3 EXACTLY -- no surplus band has to be cancelled, and the
Gram matrices are only n^2 x n^2 = 16 x 16.  DEG_BASIS = 2 is available as a
fallback if the degree-1 ansatz turns out to be infeasible.

The parity trap of METHODS section 4 does not arise here in the same form,
because the relevant degree is k rather than n.
"""

import itertools
import os
import sys

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
# ORDER MATTERS.  dittert/ also contains a module called expand.py.  It must be
# reachable (symmetry.py lives there and is field-agnostic) but must NEVER win
# the name `expand`, or this pipeline would silently certify Dittert instead of
# sub-Dittert.  HERE is inserted last, so it sits at index 0 and takes priority.
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "dittert"))
sys.path.insert(0, HERE)
from expand import build                                         # noqa: E402
from symmetry import act, generators, group_elements, monomials, orbits, positions  # noqa: E402

import expand as _expand_mod
assert os.path.dirname(os.path.abspath(_expand_mod.__file__)) == HERE, (
    f"wrong expand module loaded: {_expand_mod.__file__}")


def stab_generators(n, tgt=(0, 0)):
    """Generators of the stabiliser of position tgt in G."""
    pos = positions(n)
    idx = {p: k for k, p in enumerate(pos)}
    ti, tj = tgt
    rows = [r for r in range(n) if r != ti]
    cols = [c for c in range(n) if c != tj]
    gens = []
    for a in range(len(rows) - 1):
        r1, r2 = rows[a], rows[a + 1]

        def rp(p, r1=r1, r2=r2):
            i, j = p
            i = r2 if i == r1 else (r1 if i == r2 else i)
            return (i, j)
        gens.append(tuple(idx[rp(p)] for p in pos))
    for a in range(len(cols) - 1):
        c1, c2 = cols[a], cols[a + 1]

        def cp(p, c1=c1, c2=c2):
            i, j = p
            j = c2 if j == c1 else (c1 if j == c2 else j)
            return (i, j)
        gens.append(tuple(idx[cp(p)] for p in pos))
    if ti == tj:
        gens.append(tuple(idx[(p[1], p[0])] for p in pos))
    return gens


def sym_pair_orbits(basis, gens):
    """Orbits on ordered pairs of basis monomials, merged with transposes."""
    index = {m: k for k, m in enumerate(basis)}
    B = len(basis)
    gperm = [[index[act(g, m)] for m in basis] for g in gens]
    parent = list(range(B * B))

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    def union(x, y):
        rx, ry = find(x), find(y)
        if rx != ry:
            parent[max(rx, ry)] = min(rx, ry)

    for gp in gperm:
        for a in range(B):
            base, gbase = a * B, gp[a] * B
            for b in range(B):
                union(base + b, gbase + gp[b])
    for a in range(B):
        for b in range(a + 1, B):
            union(a * B + b, b * B + a)
    buckets = {}
    for t in range(B * B):
        buckets.setdefault(find(t), []).append(t)
    return list(buckets.values())


def transporters(n, tgt=(0, 0)):
    """
    For each position p, one group element g with g(tgt) = p.

    EXPLICIT, not searched.  The obvious implementation scans group_elements(n)
    until every position has been hit, which enumerates the whole of
    G = (S_n x S_n) : Z_2 -- 2(n!)^2 elements.  That is 1152 at n = 4 but
    1.0e6 at n = 6 and 5.1e7 at n = 7, so it makes n >= 7 unreachable.

    There is no need to search.  To carry tgt = (ti,tj) to p = (i,j), take the
    row transposition (ti i) together with the column transposition (tj j).
    That element is a product of a row permutation and a column permutation, so
    it lies in G, and it sends (ti,tj) to (i,j) by construction.  Cost O(n^2) per
    position.

    Any transporter will do.  sigma_p is DEFINED as sigma_tgt composed with
    g_p^{-1}, and that is well defined precisely because the Gram of sigma_tgt is
    invariant under Stab(tgt): two transporters differ by an element of the
    stabiliser.  So changing this function changes the certificate but not its
    validity, and the exact identity check confirms it either way.
    """
    ti, tj = tgt
    out = {}
    for i in range(n):
        for j in range(n):
            def rmap(a, i=i):
                return i if a == ti else (ti if a == i else a)

            def cmap(b, j=j):
                return j if b == tj else (tj if b == j else b)

            out[i * n + j] = tuple(rmap(a) * n + cmap(b)
                                   for a in range(n) for b in range(n))
    return out


def build_sdp(n, k, deg_basis=1, verbose=True):
    """Assemble the symmetry-reduced linear system for (n, k)."""
    N = n * n
    d = build(n, k)
    Fpoly = d["F"]
    gens = generators(n)

    basis = monomials(N, deg_basis, mindeg=1)
    B = len(basis)

    TOPDEG = 2 * deg_basis + 1
    degF = max(sum(e) for e in Fpoly)
    assert TOPDEG >= degF, f"basis degree {deg_basis} cannot reach deg F = {degF}"
    allmons = monomials(N, TOPDEG)
    reps, _ = orbits(allmons, gens)
    orbit_of = {}
    for oid, (_, members) in enumerate(reps.items()):
        for t in members:
            orbit_of[allmons[t]] = oid
    n_rows = len(reps)

    g_orbits = sym_pair_orbits(basis, gens)
    sgens = stab_generators(n, (0, 0))
    s_orbits = sym_pair_orbits(basis, sgens)
    lam_mons = monomials(N, TOPDEG - 1)
    lreps, _ = orbits(lam_mons, gens)
    lam_orbit_reps = [members for _, members in lreps.items()]

    if verbose:
        print(f"(n,k)=({n},{k}) deg_basis={deg_basis}: deg F = {degF}, "
              f"TOPDEG = {TOPDEG}")
        print(f"  |basis| = {B}, constraint rows (orbits) = {n_rows} "
              f"(from {len(allmons)} monomials)")
        print(f"  sigma_0 vars = {len(g_orbits)}, sigma_11 vars = "
              f"{len(s_orbits)}, lambda vars = {len(lam_orbit_reps)}")

    trans = transporters(n, (0, 0))

    def mm(u, v):
        return tuple(sorted(u + v))

    A0 = np.zeros((n_rows, len(g_orbits)))
    for vi, orb in enumerate(g_orbits):
        for code in orb:
            u, v = divmod(code, B)
            A0[orbit_of[mm(basis[u], basis[v])], vi] += 1.0

    A1 = np.zeros((n_rows, len(s_orbits)))
    inv_n = 1.0 / n
    for vi, orb in enumerate(s_orbits):
        for code in orb:
            u, v = divmod(code, B)
            for pk in range(N):
                g = trans[pk]
                prod = mm(act(g, basis[u]), act(g, basis[v]))
                A1[orbit_of[prod], vi] += inv_n
                A1[orbit_of[mm(prod, (pk,))], vi] += 1.0

    A2 = np.zeros((n_rows, len(lam_orbit_reps)))
    for vi, members in enumerate(lam_orbit_reps):
        for t in members:
            mu = lam_mons[t]
            for pk in range(N):
                A2[orbit_of[mm(mu, (pk,))], vi] += 1.0

    rhs = np.zeros(n_rows)
    for e, c in Fpoly.items():
        mono = tuple(sorted(itertools.chain.from_iterable(
            [t] * et for t, et in enumerate(e) if et)))
        rhs[orbit_of[mono]] += float(c)

    return dict(n=n, k=k, deg_basis=deg_basis, B=B, basis=basis,
                g_orbits=g_orbits, s_orbits=s_orbits,
                lam_orbit_reps=lam_orbit_reps, A0=A0, A1=A1, A2=A2, rhs=rhs,
                n_rows=n_rows, Fpoly=Fpoly, orbit_of=orbit_of, M=d["M"],
                gamma=d["gamma"], TOPDEG=TOPDEG)


def _orbit_map(B, orbs):
    import scipy.sparse as sp
    rows, cols, data = [], [], []
    for vi, orb in enumerate(orbs):
        for code in orb:
            rows.append(code)
            cols.append(vi)
            data.append(1.0)
    return sp.csr_matrix((data, (rows, cols)), shape=(B * B, len(orbs)))


def solve(n, k, deg_basis=1, verbose=True, d=None):
    """
    Solve the symmetry-reduced SDP, maximising the least eigenvalue margin t.

    MEMORY CHECK (METHODS section 8).  Interior-point KKT memory grows like the
    SQUARE of the scaled cone dimension m(m+1)/2.  We print it and refuse to run
    an interior-point method on a cone above the safe size.
    """
    import cvxpy as cp
    from exactsd import exact_system, full_matrix, independent_rows

    if d is None:
        d = build_sdp(n, k, deg_basis, verbose)
    B = d["B"]
    scaled = B * (B + 1) // 2
    if verbose:
        print(f"  cone size m = {B}; m(m+1)/2 = {scaled}; "
              f"interior-point KKT ~ {scaled**2 * 8 / 2**30:.4f} GB per cone")
    if B > 200:
        raise RuntimeError(f"cone size {B} > 200: block-diagonalise first "
                           "(METHODS section 7), do not run this monolithically")

    # The orbit-matching system is rank deficient in this family too.  Identify
    # the dependent rows EXACTLY over Q and drop them from the FLOAT solve only;
    # verification later uses every row.
    A0e, A1c, A1l, A2e, rhse = exact_system(d)
    Mfull = full_matrix(A0e, A1c, A1l, A2e, n)
    keep, drop, consistent = independent_rows(Mfull, rhse)
    if not consistent:
        raise RuntimeError("orbit-matching system is INCONSISTENT over Q: "
                           "no certificate of this shape can exist")
    if verbose:
        print(f"  equality rows: {d['n_rows']} total, rank {len(keep)}, "
              f"{len(drop)} dependent row(s) dropped from the float solve "
              f"(implied over Q, verified)")
    keep = np.array(keep)

    P0 = _orbit_map(B, d["g_orbits"])
    P1 = _orbit_map(B, d["s_orbits"])
    x = cp.Variable(P0.shape[1], name="x")
    y = cp.Variable(P1.shape[1], name="y")
    z = cp.Variable(len(d["lam_orbit_reps"]), name="z")
    t = cp.Variable(name="t")

    G0 = cp.reshape(P0 @ x, (B, B), order="C")
    H = cp.reshape(P1 @ y, (B, B), order="C")
    cons = [d["A0"][keep] @ x + d["A1"][keep] @ y + d["A2"][keep] @ z
            == d["rhs"][keep],
            G0 - t * np.eye(B) >> 0,
            H - t * np.eye(B) >> 0,
            t <= 1.0]
    prob = cp.Problem(cp.Maximize(t), cons)

    # Solver ladder, not a solver (METHODS section 7 trap 2).
    attempts = [("CLARABEL", {}),
                ("SCS", dict(eps_abs=1e-12, eps_rel=1e-12, max_iters=1000000)),
                ("SCS", dict(eps_abs=1e-10, eps_rel=1e-10, max_iters=1000000))]
    last = None
    for name, kw in attempts:
        try:
            prob.solve(solver=getattr(cp, name), verbose=False, **kw)
            if prob.status in ("optimal", "optimal_inaccurate"):
                if verbose:
                    print(f"  solver {name} {kw or ''}: status {prob.status}, "
                          f"t = {t.value:.6e}")
                return d, prob, x, y, z, t
            last = f"{name}: status {prob.status}"
        except Exception as exc:                                  # noqa: BLE001
            last = f"{name}: {str(exc)[:80]}"
        if verbose:
            print(f"  solver {name} did not succeed ({last}); trying next")
    raise RuntimeError(f"no solver succeeded ({last})")


def solve_blocked(n, k, deg_basis=2, verbose=True, d=None):
    """
    The same program as solve(), with each B x B cone replaced by its Schur
    blocks.  Needed once B exceeds the interior-point memory guard: at
    (n,k) = (5,4) with deg_basis = 2, B = 350 and a monolithic interior-point
    solve needs about 30 GB per cone (METHODS section 8).

    The two formulations are mathematically identical -- the spectrum of an
    invariant matrix is the union of its block spectra -- so the difference is
    purely computational.  The blocks are floating point and are NOT part of any
    proof: the solution is still returned as orbit coefficients, still rounded to
    rationals, and still checked by exact LDL^T on the assembled B x B matrix.
    """
    import cvxpy as cp
    from blockdiag import block_structure
    from exactsd import exact_system, full_matrix, independent_rows

    if d is None:
        d = build_sdp(n, k, deg_basis, verbose)
    B = d["B"]
    if verbose:
        print("  block-diagonalising sigma_0:")
    gblocks = block_structure(d["g_orbits"], B, verbose=verbose)
    if verbose:
        print("  block-diagonalising sigma_11:")
    sblocks = block_structure(d["s_orbits"], B, verbose=verbose)

    A0e, A1c, A1l, A2e, rhse = exact_system(d)
    Mfull = full_matrix(A0e, A1c, A1l, A2e, n)
    keep, drop, consistent = independent_rows(Mfull, rhse)
    if not consistent:
        raise RuntimeError("orbit-matching system is INCONSISTENT over Q: "
                           "no certificate of this shape can exist")
    if verbose:
        print(f"  equality rows: {d['n_rows']} total, rank {len(keep)}, "
              f"{len(drop)} dependent row(s) dropped from the float solve")
    keep = np.array(keep)

    x = cp.Variable(len(d["g_orbits"]), name="x")
    y = cp.Variable(len(d["s_orbits"]), name="y")
    z = cp.Variable(len(d["lam_orbit_reps"]), name="z")
    t = cp.Variable(name="t")

    cons = [d["A0"][keep] @ x + d["A1"][keep] @ y + d["A2"][keep] @ z
            == d["rhs"][keep], t <= 1.0]
    for blocks, var in ((gblocks, x), (sblocks, y)):
        for C, _ in blocks:
            dd = C.shape[0]
            Mb = cp.reshape(C.reshape(dd * dd, -1) @ var, (dd, dd), order="C")
            cons.append(0.5 * (Mb + Mb.T) - t * np.eye(dd) >> 0)

    prob = cp.Problem(cp.Maximize(t), cons)
    if verbose:
        sizes = sorted([C.shape[0] for C, _ in gblocks]
                       + [C.shape[0] for C, _ in sblocks], reverse=True)
        print(f"  cones: {sizes}  (largest {sizes[0]}, was {B})")

    # CLARABEL solves monolithic programs but has failed on blocked ones in this
    # project; SCS solves them.  Ladder, not a single solver.
    attempts = [("SCS", dict(eps_abs=1e-12, eps_rel=1e-12, max_iters=1000000)),
                ("SCS", dict(eps_abs=1e-10, eps_rel=1e-10, max_iters=1000000)),
                ("CLARABEL", {})]
    last = None
    for name, kw in attempts:
        try:
            prob.solve(solver=getattr(cp, name), verbose=False, **kw)
            if prob.status in ("optimal", "optimal_inaccurate"):
                if verbose:
                    print(f"  solver {name} {kw or ''}: status {prob.status}, "
                          f"t = {t.value:.6e}")
                return d, prob, x, y, z, t
            last = f"{name}: status {prob.status}"
        except Exception as exc:                                  # noqa: BLE001
            last = f"{name}: {str(exc)[:80]}"
        if verbose:
            print(f"  solver {name} did not succeed ({last}); trying next")
    raise RuntimeError(f"no solver succeeded on the blocked program ({last})")


if __name__ == "__main__":
    for (n, k, db) in [(4, 3, 1), (4, 3, 2), (5, 3, 1), (5, 4, 1), (5, 4, 2)]:
        try:
            build_sdp(n, k, db)
        except AssertionError as e:
            print(f"(n,k)=({n},{k}) deg_basis={db}: {e}")
        print()
