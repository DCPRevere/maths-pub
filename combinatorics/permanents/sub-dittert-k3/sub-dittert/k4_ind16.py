"""
Ind(V'|1) -- the 16 x 16 isotypic block of sigma_11 at k = 4.

NOTES.md 6b.24 derives the BASIS in closed form: a (V'|1) vector is linear in a
sum-zero row weight w on rows 1..n-1 and symmetric in the columns, and the
shapes are enumerated by the row of the second cell -- 5 + 4 + 5 = 14 of degree
2, plus 2 of degree 1, total 16.  This file realises that basis at a concrete
rational w, assembles the block and runs the three acceptance obligations of
6b.24.

WHY M(w) IS THE BLOCK, UP TO SCALE.  Each shape gives an S_{n-1} x S_{n-1}
EQUIVARIANT map e_s : V' -> R^B (linear in w, column-invariant), so by Schur --
V' is absolutely irreducible -- every invariant pairing V' x V' -> R is a
multiple of the standard form.  Hence

    M(w)[s][t] = e_s(w)^T H e_t(w) = q(w) * Bl[s][t],    q(w) = sum_i w_i^2,
    G(w)[s][t] = e_s(w)^T e_t(w)   = q(w) * g[s][t],

for ONE 16 x 16 pair (Bl, g) independent of w.  Two consequences, and both are
tests rather than assumptions:

  * M(w') / M(w) is the CONSTANT q(w')/q(w) entrywise -- this is the B (x) Q
    re-check of 6b.23 against this hand-built basis;
  * the GENERALISED eigenvalues of (M(w), G(w)) equal those of (Bl, g), which is
    scale-free, and are exactly the eigenvalues of H restricted to the
    (V'|1)-isotypic component.  Each occurs n-2 times there and n-2 more times
    on the transposed (1|V') component, so multiplicity 2(n-2) in spec(H).

THE FOLDER RULE (6b.21).  Every route below indexes the coefficient vector y by
the SYMBOLIC `svars` ordering, mapping the pair class through `canon_pair`.
Never index one y by two orderings; that error imitates several unrelated bugs
at once.

TWO INDEPENDENT ROUTES TO M(w), which is the assembly check:
  route A  per-class integer counts N^{st}_c accumulated over supp(e_s) x
           supp(e_t), with the class read from the UNION-FIND map
           (`unionfind_class_array`), then contracted with y;
  route B  dense row vectors e_s^T H, with the class computed by calling
           `canon_pair` DIRECTLY on every pair (no union-find), and y
           substituted before the contraction.
The two share the shape vectors and nothing else -- different class algorithm,
different contraction order.  Route A's N is the object the certificate build
needs: the block entries as linear forms in the 356 sigma_11 variables.
"""

import itertools
import os
import sys
from array import array

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "dittert"))
sys.path.insert(0, HERE)

import k4_system as k4                                            # noqa: E402
import sos                                                        # noqa: E402
from general_k3 import cells_of                                   # noqa: E402
from symmetry import act                                          # noqa: E402

NSHAPE = 16


# --------------------------------------------------------------- the 16 shapes
def shape_vectors(n, w):
    """
    The 16 basis elements of 6b.24, realised at the sum-zero weight w.

    `w` is w_1..w_{n-1} (length n-1); rows and columns 1..n-1 are the free ones,
    row 0 and column 0 are fixed by Stab((0,0)).  Each element is returned as a
    dict {monomial: integer coefficient} with monomials in `symmetry`'s encoding
    (sorted tuple of variable indices v = row*n + col, repetition allowed).
    """
    assert len(w) == n - 1

    def V(r, c):
        return r * n + c

    def wt(i):
        return w[i - 1]

    R = range(1, n)                      # free rows: the w-carrying row i, and k
    C = range(1, n)                      # free columns a, b

    out = []

    def start(name):
        out.append((name, {}))
        return out[-1][1]

    def add(d, cells, coef):
        m = tuple(sorted(cells))
        d[m] = d.get(m, 0) + coef

    # ---- degree 1 (2 shapes) -- the pair already found at k = 3 (6b.22)
    d = start("D1  w_i b_i0")
    for i in R:
        add(d, (V(i, 0),), wt(i))

    d = start("D2  w_i b_ia")
    for i in R:
        for a in C:
            add(d, (V(i, a),), wt(i))

    # ---- degree 2, second row = 0 (5 shapes)
    d = start("A1  w_i b_i0 b_00")
    for i in R:
        add(d, (V(i, 0), V(0, 0)), wt(i))

    d = start("A2  w_i b_ia b_00")
    for i in R:
        for a in C:
            add(d, (V(i, a), V(0, 0)), wt(i))

    d = start("A3  w_i b_i0 b_0b")
    for i in R:
        for b in C:
            add(d, (V(i, 0), V(0, b)), wt(i))

    d = start("A4  w_i b_ia b_0a")
    for i in R:
        for a in C:
            add(d, (V(i, a), V(0, a)), wt(i))

    d = start("A5  w_i b_ia b_0b (a!=b)")
    for i in R:
        for a in C:
            for b in C:
                if a != b:
                    add(d, (V(i, a), V(0, b)), wt(i))

    # ---- degree 2, second row = i, the same row (4 shapes)
    d = start("B1  w_i b_i0^2")
    for i in R:
        add(d, (V(i, 0), V(i, 0)), wt(i))

    d = start("B2  w_i b_i0 b_ia")
    for i in R:
        for a in C:
            add(d, (V(i, 0), V(i, a)), wt(i))

    d = start("B3  w_i b_ia^2")
    for i in R:
        for a in C:
            add(d, (V(i, a), V(i, a)), wt(i))

    d = start("B4  w_i b_ia b_ib (a!=b)")
    for i in R:
        for a in C:
            for b in C:
                if a != b:
                    add(d, (V(i, a), V(i, b)), wt(i))

    # ---- degree 2, second row = k, free and summed (5 shapes)
    d = start("C1  w_i b_i0 b_k0")
    for i in R:
        for k in R:
            if k != i:
                add(d, (V(i, 0), V(k, 0)), wt(i))

    d = start("C2  w_i b_ia b_k0")
    for i in R:
        for k in R:
            if k != i:
                for a in C:
                    add(d, (V(i, a), V(k, 0)), wt(i))

    d = start("C3  w_i b_i0 b_kb")
    for i in R:
        for k in R:
            if k != i:
                for b in C:
                    add(d, (V(i, 0), V(k, b)), wt(i))

    d = start("C4  w_i b_ia b_ka")
    for i in R:
        for k in R:
            if k != i:
                for a in C:
                    add(d, (V(i, a), V(k, a)), wt(i))

    d = start("C5  w_i b_ia b_kb (a!=b)")
    for i in R:
        for k in R:
            if k != i:
                for a in C:
                    for b in C:
                        if a != b:
                            add(d, (V(i, a), V(k, b)), wt(i))

    assert len(out) == NSHAPE, len(out)
    return out


def as_index_vectors(n, shapes, basis):
    """{monomial: coef} -> {basis index: coef}, dropping zero coefficients."""
    index = {m: t for t, m in enumerate(basis)}
    out = []
    for _, d in shapes:
        out.append({index[m]: c for m, c in d.items() if c})
    return out


# ------------------------------------------------------- the two class routes
def _norm_pair(u, v):
    """
    Relabel the used rows and columns to 0,1,2,... in increasing order, keeping
    0 fixed.  That relabelling is a specific element of S_{n-1} x S_{n-1} (a
    pair uses at most 4 rows and 4 columns, so it always extends for n >= 5), so
    `canon_pair(., ., True)` is constant on the fibre.  Purely a cache key: it
    turns B^2 canonicalisations into a few thousand.
    """
    allc = tuple(u) + tuple(v)
    rows = sorted({r for r, _ in allc})
    cols = sorted({c for _, c in allc})
    rm, t = {}, 1
    for r in rows:
        if r == 0:
            rm[0] = 0
        else:
            rm[r] = t
            t += 1
    cm, t = {}, 1
    for c in cols:
        if c == 0:
            cm[0] = 0
        else:
            cm[c] = t
            t += 1
    U = tuple(sorted((rm[r], cm[c]) for r, c in u))
    W = tuple(sorted((rm[r], cm[c]) for r, c in v))
    return (U, W) if U <= W else (W, U)


def unionfind_class_array(n, basis, sidx):
    """
    The same array by the ORBIT route: enumerate Stab-orbits on ordered pairs by
    union-find over the generators, then call `canon_pair` on ONE representative
    per orbit.  This is `k4_pilot.pair_class_map` with the class keys passed in
    rather than recomputed -- that function calls `k4_system.build`, which also
    enumerates the 142506 monomials of degree <= 5 for the constraint rows, and
    on a memory-throttled machine that dominates everything else here.

    The union-find is `sos.sym_pair_orbits` re-inlined over `array('i')` and
    with the per-orbit code LISTS never materialised -- the class is read off
    each root instead.  Same algorithm, same generators; only the bookkeeping
    changes.  At n = 6 the orbit lists hold 492804 boxed integers spread over
    356 Python lists, and on a memory-throttled slice that allocation dominates
    the whole run.
    """
    B = len(basis)
    index = {m: t for t, m in enumerate(basis)}
    gperm = [[index[act(g, m)] for m in basis]
             for g in sos.stab_generators(n, (0, 0))]
    parent = array("i", range(B * B))

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

    cells = [cells_of(m, n) for m in basis]
    cls = array("i", bytes(4 * B * B))
    root_cls = {}
    for code in range(B * B):
        r = find(code)
        j = root_cls.get(r)
        if j is None:
            u, v = divmod(r, B)
            j = root_cls[r] = sidx[k4.canon_pair(cells[u], cells[v], True)]
        cls[code] = j
    return cls, len(root_cls)


def direct_class_array(n, basis, sidx):
    """
    cls[u*B + v] = index of the sigma_11 pair class of (basis[u], basis[v]) in
    the symbolic `svars` ordering, by calling `canon_pair` directly.  No orbit
    enumeration and no union-find: the independent route.
    """
    B = len(basis)
    cells = [cells_of(m, n) for m in basis]
    cache = {}
    cls = array("i", bytes(4 * B * B))
    for u in range(B):
        cu = cells[u]
        base = u * B
        for v in range(u, B):
            key = _norm_pair(cu, cells[v])
            j = cache.get(key)
            if j is None:
                j = cache[key] = sidx[k4.canon_pair(key[0], key[1], True)]
            cls[base + v] = j
            cls[v * B + u] = j
    return cls, len(cache)


# ------------------------------------------------------------ the two routes
def block_by_class(E, cls, B):
    """Route A: N[s][t] = {class index: integer count}, the block as a form in y."""
    sup = [sorted(d.items()) for d in E]
    N = [[None] * NSHAPE for _ in range(NSHAPE)]
    for s in range(NSHAPE):
        for t in range(NSHAPE):
            acc = {}
            for u, cu in sup[s]:
                base = u * B
                for v, cv in sup[t]:
                    c = cls[base + v]
                    acc[c] = acc.get(c, 0) + cu * cv
            N[s][t] = {c: x for c, x in acc.items() if x}
    return N


def contract(N, y):
    return [[sum(x * y[c] for c, x in N[s][t].items())
             for t in range(NSHAPE)] for s in range(NSHAPE)]


def block_dense(E, cls, B, y):
    """Route B: dense e_s^T H, y substituted first, classes from `cls`."""
    rows = []
    for s in range(NSHAPE):
        r = [0] * B
        for u, cu in E[s].items():
            base = u * B
            for v in range(B):
                r[v] += cu * y[cls[base + v]]
        rows.append(r)
    return [[sum(rows[s][v] * cv for v, cv in E[t].items())
             for t in range(NSHAPE)] for s in range(NSHAPE)]


def gram(E):
    return [[sum(c * E[t].get(u, 0) for u, c in E[s].items())
             for t in range(NSHAPE)] for s in range(NSHAPE)]


# ------------------------------------------------------------- equivariance
def basis_perm(basis, g):
    index = {m: t for t, m in enumerate(basis)}
    return [index[act(g, m)] for m in basis]


def pushforward(vec, perm):
    """(P_g e)[perm[u]] = e[u] -- the pushforward, a homomorphism in g."""
    return {perm[u]: c for u, c in vec.items()}


def check_action_direction(n, basis):
    """
    Gyires' second warning, measured (6b.23, METHODS 7.1b trap 2).

    `act` composes as act(g, act(h, m)) = act(g.h, m) with (g.h)[v] = g[h[v]].
    The question is which composition the induced maps on VECTORS obey, since
    f -> f o rho_g reverses it.  Reported, not assumed.
    """
    gens = sos.stab_generators(n, (0, 0))
    g, h = gens[0], gens[-1]
    comp_gh = tuple(g[h[v]] for v in range(n * n))
    comp_hg = tuple(h[g[v]] for v in range(n * n))
    Pg, Ph = basis_perm(basis, g), basis_perm(basis, h)
    Pgh, Phg = basis_perm(basis, comp_gh), basis_perm(basis, comp_hg)
    lhs = [Pg[Ph[u]] for u in range(len(basis))]        # apply h then g
    return lhs == Pgh, lhs == Phg


def check_equivariance(n, w, E, basis):
    """
    e_s must be (a) invariant under column permutations fixing column 0 and
    (b) equivariant under row permutations: P_sigma e_s(w) = e_s(sigma.w).

    Linear in w plus these two facts PROVE that e_s(w) lies in the (V'|1)
    isotypic component -- Hom(V', R^B) lands in the V'-isotypic part because V'
    is irreducible.  So this is the derivation's own check, not a proxy.
    """
    bad_col = bad_row = 0
    for a in range(1, n - 1):
        r1, r2 = a, a + 1
        # column transposition (r1 r2) on columns, rows untouched
        gcol = tuple((p // n) * n + (r2 if p % n == r1 else
                                     (r1 if p % n == r2 else p % n))
                     for p in range(n * n))
        perm = basis_perm(basis, gcol)
        for s in range(NSHAPE):
            if pushforward(E[s], perm) != E[s]:
                bad_col += 1
        # row transposition (r1 r2) on rows
        grow = tuple((r2 if p // n == r1 else
                      (r1 if p // n == r2 else p // n)) * n + p % n
                     for p in range(n * n))
        perm = basis_perm(basis, grow)
        wp = list(w)
        wp[r1 - 1], wp[r2 - 1] = wp[r2 - 1], wp[r1 - 1]
        Ep = as_index_vectors(n, shape_vectors(n, tuple(wp)), basis)
        for s in range(NSHAPE):
            if pushforward(E[s], perm) != Ep[s]:
                bad_row += 1
    return bad_col, bad_row


# ------------------------------------------------------------------- driver
def svars_cached():
    """
    The 356 sigma_11 pair-class keys, cached.  They are n-INDEPENDENT canonical
    forms (k4_system's a priori bound: a pair uses at most 4 rows and 4 columns,
    so the key is a complete class invariant for every n >= 5), so caching them
    is caching a constant, not a fit.

    Taken from `pair_classes(5, True)` directly, which is what `k4_system.build`
    itself sets `svars` to.  Going through `build` would also enumerate the
    142506 monomials of degree <= 5 for the constraint rows, none of which this
    file needs -- hundreds of MB of allocation, and on a memory-throttled
    machine that is the difference between seconds and a stall.
    """
    import pickle
    path = os.path.join(HERE, "results", "k4_svars.pkl")
    if os.path.exists(path):
        with open(path, "rb") as f:
            return pickle.load(f)
    s = sorted(k4.pair_classes(5, True))
    with open(path, "wb") as f:
        pickle.dump(s, f)
    return s


def sum_zero(n, seed):
    """A sum-zero INTEGER weight w_1..w_{n-1}, from a fixed seed."""
    import random
    rng = random.Random(seed)
    r = [rng.randint(-9, 9) for _ in range(n - 1)]
    s = sum(r)
    w = [(n - 1) * x - s for x in r]
    assert sum(w) == 0
    g = 0
    for x in w:
        g = __import__("math").gcd(g, abs(x))
    if g > 1:
        w = [x // g for x in w]
    assert sum(w) == 0 and any(w)
    return tuple(w)


def run(n, svars, sidx, seed=20260729, spectrum=True):
    """
    `spectrum=False` runs obligations 1 and 2 and skips obligation 3, WITHOUT
    importing numpy.  Obligation 3 needs the full spectrum of the B x B matrix
    and so needs numpy; obligations 1 and 2 are exact integer arithmetic and do
    not.  Splitting them matters on a memory-throttled slice: importing numpy
    charges tens of MB of file-backed pages, which under `memory.high` pressure
    are evicted and re-faulted faster than they can be used.
    """
    import random

    basis = k4.basis_of(n)
    B = len(basis)
    print(f"\n=== n = {n}:  B = {B},  sigma_11 classes = {len(svars)} ===")

    w = sum_zero(n, seed)
    w2 = sum_zero(n, seed + 1)
    qw = sum(x * x for x in w)
    qw2 = sum(x * x for x in w2)
    print(f"  w  = {w}   q(w)  = {qw}")
    print(f"  w' = {w2}   q(w') = {qw2}")

    shapes = shape_vectors(n, w)
    E = as_index_vectors(n, shapes, basis)
    supp = [len(d) for d in E]
    print(f"  shape supports: {supp}  (total {sum(supp)})")

    # --- the action-direction checkpoint
    homo, anti = check_action_direction(n, basis)
    print(f"  action direction: P_g P_h == P_(g.h): {homo};  == P_(h.g): {anti}")

    # --- equivariance: proves membership in the (V'|1) component
    bad_col, bad_row = check_equivariance(n, w, E, basis)
    print(f"  equivariance: column-invariance failures {bad_col}, "
          f"row-equivariance failures {bad_row}")

    # --- the two class routes, compared elementwise (the 6b.21 trap)
    cls_uf, norb = unionfind_class_array(n, basis, sidx)
    cls_dir, ncache = direct_class_array(n, basis, sidx)
    diff = sum(1 for t in range(B * B) if cls_uf[t] != cls_dir[t])
    print(f"  class arrays: union-find ({norb} orbits) vs direct canon_pair "
          f"({ncache} distinct normalised pairs) -> {diff} differing entries "
          f"of {B * B}")

    # --- OBLIGATION 1: the block, two routes
    rng = random.Random(4242)
    y = [rng.randint(-40, 40) or 7 for _ in range(len(svars))]
    N = block_by_class(E, cls_uf, B)
    M_A = contract(N, y)
    M_B = block_dense(E, cls_dir, B, y)
    mism = sum(1 for s in range(NSHAPE) for t in range(NSHAPE)
               if M_A[s][t] != M_B[s][t])
    print(f"  OBLIGATION 1: route A (class counts, union-find) vs route B "
          f"(dense, direct canon_pair) -> {mism} mismatched entries of "
          f"{NSHAPE * NSHAPE}")
    sym = sum(1 for s in range(NSHAPE) for t in range(s)
              if M_A[s][t] != M_A[t][s])
    print(f"                symmetry of M: {sym} failures of "
          f"{NSHAPE * (NSHAPE - 1) // 2}")
    nz = sum(1 for s in range(NSHAPE) for t in range(NSHAPE) if M_A[s][t])
    print(f"                nonzero entries: {nz} of {NSHAPE * NSHAPE}")

    # --- OBLIGATION 2: B (x) Q against a second w'
    E2 = as_index_vectors(n, shape_vectors(n, w2), basis)
    N2 = block_by_class(E2, cls_uf, B)
    M2 = contract(N2, y)
    from fractions import Fraction as F
    ratios = set()
    zeros = 0
    for s in range(NSHAPE):
        for t in range(NSHAPE):
            if M_A[s][t] == 0:
                if M2[s][t] != 0:
                    ratios.add("INF")
                else:
                    zeros += 1
                continue
            ratios.add(F(M2[s][t], M_A[s][t]))
    print(f"  OBLIGATION 2: entrywise ratio M(w')/M(w): {len(ratios)} distinct "
          f"value(s) over {NSHAPE * NSHAPE - zeros} nonzero entries")
    print(f"                values {sorted(ratios, key=str)[:4]}   "
          f"predicted q(w')/q(w) = {F(qw2, qw)}")

    # Sharper than the contraction above: the coefficient of EVERY class must
    # scale by q(w), not merely the y-weighted sum.  N/q(w) is then the block as
    # a form in the 356 sigma_11 variables, free of w -- the object the Q(n)
    # design needs, here at one concrete n.
    def normalise(NN, q):
        return [[{c: F(x, q) for c, x in NN[s][t].items()}
                 for t in range(NSHAPE)] for s in range(NSHAPE)]

    Nn, Nn2 = normalise(N, qw), normalise(N2, qw2)
    bad = sum(1 for s in range(NSHAPE) for t in range(NSHAPE)
              if Nn[s][t] != Nn2[s][t])
    used = set()
    for s in range(NSHAPE):
        for t in range(NSHAPE):
            used |= set(Nn[s][t])
    denom = {x.denominator for s in range(NSHAPE) for t in range(NSHAPE)
             for x in Nn[s][t].values()}
    print(f"                per-CLASS check: N(w)/q(w) vs N(w')/q(w') -> "
          f"{bad} differing entries of {NSHAPE * NSHAPE}; "
          f"{len(used)} of {len(svars)} classes occur; "
          f"denominators {sorted(denom)[:5]}")

    if not spectrum:
        print("  OBLIGATION 3: skipped (spectrum=False)")
        return dict(n=n, M=M_A, N=N, Nn=Nn, w=w, y=y, mism=mism,
                    ratios=ratios, cls_diff=diff, used=used, ge=None,
                    counts=None)

    # --- OBLIGATION 3: multiplicity 2(n-2) in spec(H)
    import numpy as np
    G = gram(E)
    Gf = np.array([[float(x) for x in row] for row in G])
    Mf = np.array([[float(x) for x in row] for row in M_A])
    detG = np.linalg.slogdet(Gf)
    print(f"  Gram G(w): rank {np.linalg.matrix_rank(Gf)} of {NSHAPE}, "
          f"log|det| = {detG[1]:.3f}, sign {detG[0]:+.0f}")
    # Generalised eigenvalues of (M, G) without scipy: G is symmetric positive
    # definite (rank 16, det > 0 above), so with G = L L^T the pencil's spectrum
    # is that of L^-1 M L^-T.  scipy.linalg would do the same thing and costs
    # 40 MB of import, which on a throttled slice is the dominant expense.
    L = np.linalg.cholesky(Gf)
    C1 = np.linalg.solve(L, Mf)
    Cm = np.linalg.solve(L, C1.T).T
    ge = np.linalg.eigvalsh(0.5 * (Cm + Cm.T))

    yv = np.array(y, dtype=float)
    ca = np.frombuffer(cls_dir, dtype=np.int32).reshape(B, B)
    H = yv[ca]
    assert np.array_equal(H, H.T)
    spec = np.sort(np.linalg.eigvalsh(H))
    scale = max(abs(spec[0]), abs(spec[-1]))
    tol = 1e-7 * scale
    want = 2 * (n - 2)
    counts = []
    for mu in ge:
        counts.append(int(np.sum(np.abs(spec - mu) < tol)))
    gaps = np.diff(np.unique(np.round(spec / scale, 9)))
    print(f"  OBLIGATION 3: |spec(H)| = {B}, scale {scale:.4g}, "
          f"tol {tol:.3g}, smallest normalised gap {gaps.min():.3g}")
    print(f"                multiplicities of the 16 generalised eigenvalues "
          f"in spec(H): {sorted(counts)}")
    print(f"                predicted 2(n-2) = {want};  "
          f"{sum(1 for c in counts if c == want)} of {NSHAPE} agree;  "
          f"covered {sum(counts)} of {B}")
    print(f"                generalised eigenvalues: "
          f"{np.array2string(np.sort(ge), precision=4, max_line_width=100)}")

    # --- bonus: the transposed copy is H-orthogonal to this one
    gtr = tuple((p % n) * n + (p // n) for p in range(n * n))
    ptr = basis_perm(basis, gtr)
    Etr = [pushforward(E[s], ptr) for s in range(NSHAPE)]
    cross = 0
    for s in range(NSHAPE):
        r = [0] * B
        for u, cu in Etr[s].items():
            base = u * B
            for v in range(B):
                r[v] += cu * y[cls_dir[base + v]]
        for t in range(NSHAPE):
            if sum(r[v] * cv for v, cv in E[t].items()):
                cross += 1
    print(f"  cross terms <tau e_s, H e_t> nonzero: {cross} of "
          f"{NSHAPE * NSHAPE}  (must be 0: (1|V') and (V'|1) do not pair)")

    return dict(n=n, M=M_A, N=N, Nn=Nn, G=G, w=w, y=y, ge=ge, counts=counts,
                mism=mism, ratios=ratios, cls_diff=diff, used=used)


if __name__ == "__main__":
    args = sys.argv[1:]
    spectrum = "--no-spectrum" not in args
    ns = [int(a) for a in args if not a.startswith("-")] or [5, 6]
    print("Ind(V'|1) 16 x 16 -- assembly and the three obligations of 6b.24")
    svars = svars_cached()
    sidx = {k: i for i, k in enumerate(svars)}
    res = [run(n, svars, sidx, spectrum=spectrum) for n in ns]
    if len(res) > 1:
        print("\nclass-set stabilisation of the block across n.  NOT a pass/fail "
              "line: a class may be absent at the smaller n because its "
              "coefficient polynomial has a root there -- at n = 5 twelve of "
              "them do, by cancellation between merge patterns, NOT by any "
              "falling factorial running out (NOTES 6b.26).  So "
              "`identical: False` is expected; what must hold is that the "
              "smaller set is CONTAINED in the larger:")
        for a in range(len(res)):
            for b in range(a + 1, len(res)):
                A, Bs = res[a]["used"], res[b]["used"]
                print(f"  n={res[a]['n']} vs n={res[b]['n']}: "
                      f"{len(A)} vs {len(Bs)} classes, "
                      f"identical: {A == Bs}, symmetric difference "
                      f"{len(A ^ Bs)}, smaller contained in larger: "
                      f"{A <= Bs or Bs <= A}")
