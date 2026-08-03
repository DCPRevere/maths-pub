"""
The `(V'|V')` isotypic component of sigma_11 at k = 4: the 10x10 and the 4x4.

NOTES 6b.29 designs this before any assembly.  The 14 templates are enumerated
there and reproduced below; `i` carries the sum-zero ROW weight `w` and `a` the
sum-zero COLUMN weight `z`, `k` and `b` are free labels summed over values
distinct from `i` and `a`, and `0` is the fixed row/column of Stab((0,0)).

THE SPLIT, which is the whole point of this block.  `(V'|V')` extends to
Stab((0,0)) = (S_{n-1} x S_{n-1}) : Z_2 in TWO ways, and 6b.21's rule applies in
its original form -- the two are separated by their BASIS VECTORS, not by their
class keys.  The separator is the involution

    (J Phi)(w (x) z) := P_tau Phi(z (x) w)

on the 14-dimensional multiplicity space.  `J` is predicted to act as a
PERMUTATION of the templates with 6 fixed points and 4 swapped pairs, giving
dim(+1) = 10 and dim(-1) = 4; that permutation is MEASURED here rather than
assumed, by matching `P_tau e_s(z, w)` against the realised shapes.

Then, because `H` is invariant under the full group, the induced form on the
multiplicity space satisfies `Bl(J Phi, J Psi) = Bl(Phi, Psi)`, so
`Bl(Phi_+, Phi_-) = -Bl(Phi_+, Phi_-) = 0`:

    in the J-eigenbasis the 10 x 4 off-diagonal block of M is EXACTLY ZERO.

That is the acceptance test.  It is a claim about 40 exact rationals, it cannot
be passed by a basis that merely has the right total multiplicity, and its
failure signature is distinct from a wrong `J` (which shows up as a
non-involution or the wrong trace).

The same holds for the Gram `G` (take `H = I`, also invariant), which gives the
test for free a second time.
"""

import itertools
import os
import sys
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "dittert"))
sys.path.insert(0, HERE)
import k4_ind16 as i16                                            # noqa: E402
import k4_system as k4                                            # noqa: E402
import sos                                                        # noqa: E402

NSHAPE = 14

# 6b.29's enumeration.  Row labels 0/i/k, column labels 0/a/b; `i` must appear
# as a row label and `a` as a column label, which is what forces the count.
TEMPLATES = [
    ("D    b_ia",              (("i", "a"),)),
    ("E1   b_ia b_00",         (("i", "a"), ("0", "0"))),
    ("E2   b_i0 b_0a",         (("i", "0"), ("0", "a"))),
    ("E3   b_ia b_0a",         (("i", "a"), ("0", "a"))),
    ("E4   b_ia b_0b",         (("i", "a"), ("0", "b"))),
    ("E5   b_ib b_0a",         (("i", "b"), ("0", "a"))),
    ("F1   b_ia b_ka",         (("i", "a"), ("k", "a"))),
    ("F2   b_ia b_k0",         (("i", "a"), ("k", "0"))),
    ("F3   b_i0 b_ka",         (("i", "0"), ("k", "a"))),
    ("F4   b_ia b_kb",         (("i", "a"), ("k", "b"))),
    ("F5   b_ib b_ka",         (("i", "b"), ("k", "a"))),
    ("G1   b_i0 b_ia",         (("i", "0"), ("i", "a"))),
    ("G2   b_ia b_ib",         (("i", "a"), ("i", "b"))),
    ("G3   b_ia^2",            (("i", "a"), ("i", "a"))),
]

ROWLAB, COLLAB = ("i", "k"), ("a", "b")


def free_labels(cells):
    rows = [x for x in ROWLAB if any(r == x for r, _ in cells)]
    cols = [x for x in COLLAB if any(c == x for _, c in cells)]
    return rows, cols


def realise(cells, n, w, z):
    """{monomial: coefficient}, summed over assignments of distinct values."""
    rows, cols = free_labels(cells)
    d = {}
    for rv in itertools.permutations(range(1, n), len(rows)):
        rmap = dict(zip(rows, rv))
        rmap["0"] = 0
        wi = w[rmap["i"] - 1]
        for cv in itertools.permutations(range(1, n), len(cols)):
            cmap = dict(zip(cols, cv))
            cmap["0"] = 0
            m = tuple(sorted(rmap[r] * n + cmap[c] for r, c in cells))
            d[m] = d.get(m, 0) + wi * z[cmap["a"] - 1]
    return {m: c for m, c in d.items() if c}


def shape_vectors(n, w, z, basis):
    index = {m: t for t, m in enumerate(basis)}
    return [{index[m]: c for m, c in realise(cells, n, w, z).items()}
            for _, cells in TEMPLATES]


# ------------------------------------------------------------ the involution J
def measure_J(n, w, z, basis):
    """
    The permutation pi with P_tau e_s(z, w) = e_pi(s)(w, z), MEASURED.

    Returns (pi, unmatched).  `unmatched` lists shapes whose tau-image is not
    one of the 14 realised shapes -- if it is nonempty then J is not a
    permutation of the templates and 6b.29's Prediction 2 is wrong, which is a
    different failure from a wrong trace.
    """
    gtr = tuple((p % n) * n + (p // n) for p in range(n * n))
    perm = i16.basis_perm(basis, gtr)
    here = shape_vectors(n, w, z, basis)
    swapped = shape_vectors(n, z, w, basis)          # e_s(z (x) w)
    lookup = {tuple(sorted(v.items())): s for s, v in enumerate(here)}
    pi, unmatched = [None] * NSHAPE, []
    for s in range(NSHAPE):
        img = i16.pushforward(swapped[s], perm)
        t = lookup.get(tuple(sorted(img.items())))
        if t is None:
            unmatched.append(TEMPLATES[s][0].split()[0])
        pi[s] = t
    return pi, unmatched


def eigenbasis(pi):
    """
    Rows of U: the +1 eigenvectors of J first, then the -1 eigenvectors.

    Fixed templates give `e_s`; each swapped pair {s, t} gives `e_s + e_t` in
    the + space and `e_s - e_t` in the - space.  Returns (U, n_plus, fixed,
    pairs).
    """
    fixed = [s for s in range(NSHAPE) if pi[s] == s]
    pairs = sorted({(min(s, pi[s]), max(s, pi[s]))
                    for s in range(NSHAPE) if pi[s] != s})
    plus, minus = [], []
    for s in fixed:
        row = [0] * NSHAPE
        row[s] = 1
        plus.append(row)
    for s, t in pairs:
        row = [0] * NSHAPE
        row[s], row[t] = 1, 1
        plus.append(row)
        row = [0] * NSHAPE
        row[s], row[t] = 1, -1
        minus.append(row)
    return plus + minus, len(plus), fixed, pairs


def congruence(U, M):
    """U M U^T, exact."""
    tmp = [[sum(U[p][s] * M[s][t] for s in range(NSHAPE) if U[p][s])
            for t in range(NSHAPE)] for p in range(len(U))]
    return [[sum(tmp[p][t] * U[q][t] for t in range(NSHAPE) if U[q][t])
             for q in range(len(U))] for p in range(len(U))]


# ----------------------------------------------------------------- the driver
def check_equivariance(n, w, z, E, basis):
    """
    Linear in w, linear in z, and equivariant on each side separately -- that
    places every e_s in the (V'|V') isotypic component, which is the claim the
    rest of the file rests on.
    """
    bad_row = bad_col = 0
    for a in range(1, n - 1):
        r1, r2 = a, a + 1
        grow = tuple((r2 if p // n == r1 else
                      (r1 if p // n == r2 else p // n)) * n + p % n
                     for p in range(n * n))
        wp = list(w)
        wp[r1 - 1], wp[r2 - 1] = wp[r2 - 1], wp[r1 - 1]
        want = shape_vectors(n, tuple(wp), z, basis)
        perm = i16.basis_perm(basis, grow)
        for s in range(NSHAPE):
            if i16.pushforward(E[s], perm) != want[s]:
                bad_row += 1

        gcol = tuple((p // n) * n + (r2 if p % n == r1 else
                                     (r1 if p % n == r2 else p % n))
                     for p in range(n * n))
        zp = list(z)
        zp[r1 - 1], zp[r2 - 1] = zp[r2 - 1], zp[r1 - 1]
        want = shape_vectors(n, w, tuple(zp), basis)
        perm = i16.basis_perm(basis, gcol)
        for s in range(NSHAPE):
            if i16.pushforward(E[s], perm) != want[s]:
                bad_col += 1
    return bad_row, bad_col


def run(n, svars, sidx, seed=20260729, spectrum=True):
    import random

    basis = k4.basis_of(n)
    B = len(basis)
    print(f"\n=== n = {n}:  B = {B} ===")

    # 6b.29 obligation 2: q(w) != q(z) DELIBERATELY, so that a route which
    # confuses the row and column weights cannot pass by symmetry.
    w = i16.sum_zero(n, seed)
    z = i16.sum_zero(n, seed + 101)
    qw, qz = sum(x * x for x in w), sum(x * x for x in z)
    assert qw != qz, "pick different seeds: q(w) == q(z) hides a w/z swap"
    w2 = i16.sum_zero(n, seed + 202)
    z2 = i16.sum_zero(n, seed + 303)
    qw2, qz2 = sum(x * x for x in w2), sum(x * x for x in z2)
    print(f"  w  = {w}  q(w)  = {qw}      z  = {z}  q(z)  = {qz}")
    print(f"  w' = {w2}  q(w') = {qw2}     z' = {z2}  q(z') = {qz2}")

    E = shape_vectors(n, w, z, basis)
    print(f"  shape supports: {[len(d) for d in E]}  "
          f"(total {sum(len(d) for d in E)})")

    bad_row, bad_col = check_equivariance(n, w, z, E, basis)
    print(f"  equivariance: row failures {bad_row}, column failures {bad_col}")

    # --- the involution, MEASURED
    pi, unmatched = measure_J(n, w, z, basis)
    U, nplus, fixed, pairs = eigenbasis(pi)
    invol = all(pi[pi[s]] == s for s in range(NSHAPE)) if not unmatched else None
    trace = sum(1 for s in range(NSHAPE) if pi[s] == s)
    print(f"  J: unmatched shapes {unmatched or 'none'};  involution "
          f"{invol};  trace {trace} (predicted 6)")
    print(f"     fixed {[TEMPLATES[s][0].split()[0] for s in fixed]}")
    print(f"     pairs {[(TEMPLATES[s][0].split()[0], TEMPLATES[t][0].split()[0]) for s, t in pairs]}")
    print(f"     dim(+1) = {nplus} (predicted 10), "
          f"dim(-1) = {NSHAPE - nplus} (predicted 4)")

    # --- the two class routes and the block, two ways
    cls_uf, norb = i16.unionfind_class_array(n, basis, sidx)
    cls_dir, ncache = i16.direct_class_array(n, basis, sidx)
    diff = sum(1 for t in range(B * B) if cls_uf[t] != cls_dir[t])
    print(f"  class arrays: union-find ({norb} orbits) vs direct canon_pair "
          f"-> {diff} differing entries of {B * B}")

    rng = random.Random(4242)
    y = [rng.randint(-40, 40) or 7 for _ in range(len(svars))]
    N = block_by_class(E, cls_uf, B)
    M_A = contract(N, y)
    M_B = block_dense(E, cls_dir, B, y)
    mism = sum(1 for s in range(NSHAPE) for t in range(NSHAPE)
               if M_A[s][t] != M_B[s][t])
    sym = sum(1 for s in range(NSHAPE) for t in range(s)
              if M_A[s][t] != M_A[t][s])
    print(f"  OBLIGATION 1: route A vs route B -> {mism} mismatched entries "
          f"of {NSHAPE * NSHAPE};  symmetry {sym} failures of "
          f"{NSHAPE * (NSHAPE - 1) // 2}")

    # --- OBLIGATION 2: B (x) Q, now with a PRODUCT of two sum-zero norms
    E2 = shape_vectors(n, w2, z2, basis)
    M2 = contract(block_by_class(E2, cls_uf, B), y)
    ratios, zeros = set(), 0
    for s in range(NSHAPE):
        for t in range(NSHAPE):
            if M_A[s][t] == 0:
                zeros += 1 if M2[s][t] == 0 else 0
                if M2[s][t]:
                    ratios.add("INF")
                continue
            ratios.add(F(M2[s][t], M_A[s][t]))
    pred = F(qw2 * qz2, qw * qz)
    print(f"  OBLIGATION 2: entrywise M(w',z')/M(w,z): {len(ratios)} distinct "
          f"value(s) over {NSHAPE * NSHAPE - zeros} nonzero entries")
    print(f"                values {sorted(ratios, key=str)[:3]}   predicted "
          f"q(w')q(z')/(q(w)q(z)) = {pred}")

    G = gram(E)
    Msplit = congruence(U, M_A)
    Gsplit = congruence(U, G)
    offM = sum(1 for p in range(nplus) for q in range(nplus, NSHAPE)
               if Msplit[p][q])
    offG = sum(1 for p in range(nplus) for q in range(nplus, NSHAPE)
               if Gsplit[p][q])
    print(f"  OBLIGATION 3 (THE SPLIT TEST): off-diagonal {nplus} x "
          f"{NSHAPE - nplus} block in the J-eigenbasis -> {offM} nonzero of "
          f"{nplus * (NSHAPE - nplus)} in M, {offG} nonzero of "
          f"{nplus * (NSHAPE - nplus)} in G   (predicted 0 and 0)")

    if not spectrum:
        print("  OBLIGATION 4: skipped (spectrum=False)")
        return dict(n=n, pi=pi, nplus=nplus, mism=mism, ratios=ratios,
                    offM=offM, offG=offG, N=N, U=U)

    import numpy as np
    spec = None
    counts = {}
    yv = np.array(y, dtype=float)
    ca = np.frombuffer(cls_dir, dtype=np.int32).reshape(B, B)
    H = yv[ca]
    spec = np.sort(np.linalg.eigvalsh(H))
    scale = max(abs(spec[0]), abs(spec[-1]))
    tol = 1e-7 * scale
    want = (n - 2) ** 2
    for name, lo, hi in (("10x10", 0, nplus), ("4x4", nplus, NSHAPE)):
        sub = [[float(Msplit[p][q]) for q in range(lo, hi)] for p in range(lo, hi)]
        subG = [[float(Gsplit[p][q]) for q in range(lo, hi)] for p in range(lo, hi)]
        Mf, Gf = np.array(sub), np.array(subG)
        L = np.linalg.cholesky(Gf)
        C1 = np.linalg.solve(L, Mf)
        Cm = np.linalg.solve(L, C1.T).T
        ge = np.linalg.eigvalsh(0.5 * (Cm + Cm.T))
        c = [int(np.sum(np.abs(spec - mu) < tol)) for mu in ge]
        counts[name] = c
        print(f"  OBLIGATION 4: {name} block, Gram rank "
              f"{np.linalg.matrix_rank(Gf)} of {hi - lo};  multiplicities in "
              f"spec(H) {sorted(c)}")
        print(f"                predicted (n-2)^2 = {want}; "
              f"{sum(1 for x in c if x == want)} of {hi - lo} agree")
    tot = sum(sum(v) for v in counts.values())
    print(f"                covered {tot} of {B}, predicted "
          f"{NSHAPE * want}")
    return dict(n=n, pi=pi, nplus=nplus, mism=mism, ratios=ratios,
                offM=offM, offG=offG, counts=counts, N=N, U=U)


# reuse the two contraction routes verbatim -- they take NSHAPE from the caller
def block_by_class(E, cls, B):
    sup = [sorted(d.items()) for d in E]
    N = [[None] * len(E) for _ in E]
    for s in range(len(E)):
        for t in range(len(E)):
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
             for t in range(len(N))] for s in range(len(N))]


def block_dense(E, cls, B, y):
    rows = []
    for s in range(len(E)):
        r = [0] * B
        for u, cu in E[s].items():
            base = u * B
            for v in range(B):
                r[v] += cu * y[cls[base + v]]
        rows.append(r)
    return [[sum(rows[s][v] * cv for v, cv in E[t].items())
             for t in range(len(E))] for s in range(len(E))]


def gram(E):
    return [[sum(c * E[t].get(u, 0) for u, c in E[s].items())
             for t in range(len(E))] for s in range(len(E))]


if __name__ == "__main__":
    args = sys.argv[1:]
    spectrum = "--no-spectrum" not in args
    ns = [int(a) for a in args if not a.startswith("-")] or [5, 6]
    print("(V'|V') at k = 4 -- the 10x10 and the 4x4, per NOTES 6b.29")
    print("PREDICTED: 14 shapes; J an involution with trace 6; dim(+1) = 10, "
          "dim(-1) = 4; split-test off-diagonal exactly 0; multiplicity "
          "(n-2)^2 for both blocks.")
    svars = i16.svars_cached()
    sidx = {k: i for i, k in enumerate(svars)}
    for n in ns:
        run(n, svars, sidx, spectrum=spectrum)
