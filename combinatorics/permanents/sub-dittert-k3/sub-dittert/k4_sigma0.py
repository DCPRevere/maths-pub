"""
`sigma_0`'s TEN canonical blocks at k = 4 -- the §6b.33 FACT 2 blocker.

Designed in NOTES §6b.35, which fixes every number below before it is measured.
`sigma_0`'s group is the WHOLE of G = (S_n x S_n) : Z_2, so relative to
§6b.24-§6b.32 three things change and all of them simplify:

  * no fixed row 0 and no fixed column 0 -- templates carry no `0` label, row
    labels are {i, k} and column labels are {a, b};
  * free labels range over n values, not m = n - 1;
  * the partitions are of n, so V has dimension n-1, (n-2,2) has n(n-3)/2 and
    (n-2,1,1) has (n-1)(n-2)/2.

The contraction table of §6b.32 is unchanged: it rests on the trace condition
`sum_b W_ab = 0`, the zero diagonal and the symmetry sign, none of which mention
the size of the index set.

ONE GENUINELY NEW INSTRUMENT.  §6b.30 measured the involution J as a PERMUTATION
of templates.  That cannot work here: on the `triv triv` family two J-FIXED
templates coincide as vectors, so J must be measured as a MATRIX on the
independent set, by an exact rational solve (`solve_in_span`).  `J^2 = I` and
`trace(J)` are then the tests -- trace 3 for `triv triv` (4 - 1) and 4 for
`vec vec` (5 - 1).

THE FOLDER RULE (§6b.21) still binds: every route indexes the coefficient vector
`y` by the SAME `gvars` ordering, mapping the pair class through
`canon_pair(., ., False)`.
"""

import itertools
import os
import sys
from array import array
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "dittert"))
sys.path.insert(0, HERE)
import k4_system as k4                                            # noqa: E402
import k4_tail as tail                                            # noqa: E402
import k4_vv14 as vv                                              # noqa: E402
from general_k3 import cells_of                                   # noqa: E402
from symmetry import act, generators, orbits                      # noqa: E402

ROWLAB, COLLAB = ("i", "k"), ("a", "b")
NEED_ROW = {"triv": (), "vec": ("i",), "sym": ("i", "k"), "asym": ("i", "k")}
NEED_COL = {"triv": (), "vec": ("a",), "sym": ("a", "b"), "asym": ("a", "b")}

# (row type, col type, split by J?, [(block name, predicted mult, dim(n)), ...])
# The order inside a split family is (+ extension, - extension).
FAMILIES = [
    ("triv", "triv", True,
     [("(1|1) ext +", 4, lambda n: 1), ("(1|1) ext -", 1, lambda n: 1)]),
    ("triv", "vec", False,
     [("Ind(1|V)", 5, lambda n: 2 * (n - 1))]),
    ("vec", "vec", True,
     [("(V|V) ext +", 5, lambda n: (n - 1) ** 2),
      ("(V|V) ext -", 1, lambda n: (n - 1) ** 2)]),
    ("triv", "sym", False,
     [("Ind(1|(n-2,2))", 2, lambda n: n * (n - 3))]),
    ("vec", "sym", False,
     [("Ind(V|(n-2,2))", 2, lambda n: n * (n - 1) * (n - 3))]),
    ("vec", "asym", False,
     [("Ind(V|(n-2,1,1))", 1, lambda n: (n - 1) ** 2 * (n - 2))]),
    ("triv", "asym", False,
     [("Ind(1|(n-2,1,1))  ABSENT", 0, lambda n: 0)]),
    ("sym", "sym", True,
     [("((n-2,2)|(n-2,2)) ext +", 1, lambda n: (n * (n - 3) // 2) ** 2),
      ("((n-2,2)|(n-2,2)) ext -", 0, lambda n: 0)]),
    ("asym", "asym", True,
     [("((n-2,1,1)|(n-2,1,1)) ext +", 1,
       lambda n: ((n - 1) * (n - 2) // 2) ** 2),
      ("((n-2,1,1)|(n-2,1,1)) ext -", 0, lambda n: 0)]),
    ("sym", "asym", False,
     [("Ind((n-2,2)|(n-2,1,1))  ABSENT", 0, lambda n: 0)]),
]


# ------------------------------------------------------------------- weights
def sum_zero_full(n, seed):
    """A sum-zero INTEGER weight w_0..w_{n-1} -- n values, not n-1."""
    import math
    import random
    rng = random.Random(seed)
    r = [rng.randint(-9, 9) for _ in range(n)]
    s = sum(r)
    w = [n * x - s for x in r]
    g = 0
    for x in w:
        g = math.gcd(g, abs(x))
    if g > 1:
        w = [x // g for x in w]
    assert sum(w) == 0 and any(w)
    return tuple(w)


def two_index_full(n, anti, seed):
    """
    A generic element of S^(n-2,2) (sym) or S^(n-2,1,1) (asym) on 0..n-1.

    `tail.two_index_weight` builds exactly this on 1..m from an EXACT nullspace
    basis of the trace condition; only the index set moves, so it is reused and
    shifted rather than rewritten.
    """
    W1, dim = tail.two_index_weight(n, anti, seed)
    return {(a - 1, b - 1): v for (a, b), v in W1.items()}, dim


def wnorm(kind, w, n):
    if kind == "triv":
        return 1
    if kind == "vec":
        return sum(x * x for x in w)
    return sum(w[(a, b)] ** 2 for a in range(n) for b in range(n))


# ------------------------------------------------------------------ templates
def candidates(rowtype, coltype):
    """Every template on the labels its weights require -- NO `0` label."""
    cells = [(r, c) for r in ROWLAB for c in COLLAB]
    out = []
    for deg in (1, 2):
        for combo in itertools.combinations_with_replacement(cells, deg):
            rl = {r for r, _ in combo}
            cl = {c for _, c in combo}
            if "k" in rl and "i" not in rl:
                continue
            if "b" in cl and "a" not in cl:
                continue
            if any(x not in rl for x in NEED_ROW[rowtype]):
                continue
            if any(x not in cl for x in NEED_COL[coltype]):
                continue
            out.append(tuple(sorted(combo)))
    return sorted(set(out))


def realise(cells, n, rowtype, coltype, wrow, wcol):
    """{monomial: coefficient}, summed over assignments of DISTINCT values."""
    rows = [x for x in ROWLAB if any(r == x for r, _ in cells)]
    cols = [x for x in COLLAB if any(c == x for _, c in cells)]
    d = {}
    for rv in itertools.permutations(range(n), len(rows)):
        rmap = dict(zip(rows, rv))
        if rowtype == "triv":
            rf = 1
        elif rowtype == "vec":
            rf = wrow[rmap["i"]]
        else:
            rf = wrow[(rmap["i"], rmap["k"])]
        if rf == 0:
            continue
        for cv in itertools.permutations(range(n), len(cols)):
            cmap = dict(zip(cols, cv))
            if coltype == "triv":
                cf = 1
            elif coltype == "vec":
                cf = wcol[cmap["a"]]
            else:
                cf = wcol[(cmap["a"], cmap["b"])]
            if cf == 0:
                continue
            mono = tuple(sorted(rmap[r] * n + cmap[c] for r, c in cells))
            d[mono] = d.get(mono, 0) + rf * cf
    return {mo: c for mo, c in d.items() if c}


def fmt(cells):
    return "".join(f"({r}{c})" for r, c in cells)


# ---------------------------------------------------- the two class routes
def _gnorm_pair(u, v):
    """
    Relabel all used rows (and columns) to 0,1,2,... in increasing order.

    With no fixed row 0 that relabelling is an element of S_n x S_n (a pair uses
    at most 4 rows and 4 columns, so it extends for every n >= 4), hence
    `canon_pair(., ., False)` is constant on the fibre.  Purely a cache key.
    """
    allc = tuple(u) + tuple(v)
    rm = {r: t for t, r in enumerate(sorted({r for r, _ in allc}))}
    cm = {c: t for t, c in enumerate(sorted({c for _, c in allc}))}
    U = tuple(sorted((rm[r], cm[c]) for r, c in u))
    W = tuple(sorted((rm[r], cm[c]) for r, c in v))
    return (U, W) if U <= W else (W, U)


def g_direct_class_array(n, basis, gidx):
    """cls[u*B+v] = sigma_0 pair class of (basis[u], basis[v]), direct route."""
    B = len(basis)
    cells = [cells_of(m, n) for m in basis]
    cache = {}
    cls = array("i", bytes(4 * B * B))
    for u in range(B):
        cu = cells[u]
        base = u * B
        for v in range(u, B):
            key = _gnorm_pair(cu, cells[v])
            j = cache.get(key)
            if j is None:
                j = cache[key] = gidx[k4.canon_pair(key[0], key[1], False)]
            cls[base + v] = j
            cls[v * B + u] = j
    return cls, len(cache)


def g_unionfind_class_array(n, basis, gidx):
    """The same array by union-find over the FULL group's generators."""
    B = len(basis)
    index = {m: t for t, m in enumerate(basis)}
    gperm = [[index[act(g, m)] for m in basis] for g in generators(n)]
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
            j = root_cls[r] = gidx[k4.canon_pair(cells[u], cells[v], False)]
        cls[code] = j
    return cls, len(root_cls)


def gvars_cached():
    """
    The sigma_0 pair-class keys.  n-INDEPENDENT canonical forms by the same a
    priori bound as `svars`: a pair of degree-<=2 monomials uses at most 4 rows
    and 4 columns, so the key is a complete class invariant for every n >= 4.
    METHODS §7 measures 51 of them at n = 4, 5 and 6 alike.
    """
    import pickle
    path = os.path.join(HERE, "results", "k4_gvars.pkl")
    if os.path.exists(path):
        with open(path, "rb") as f:
            return pickle.load(f)
    s = sorted(k4.pair_classes(5, False))
    with open(path, "wb") as f:
        pickle.dump(s, f)
    return s


# --------------------------------------------------- exact linear algebra
def solve_in_span(E, targets):
    """
    A with targets[s] = sum_t A[s][t] E[t], exactly; None if some target is
    outside the span.  E must be independent (asserted).
    """
    ns = len(E)
    redu = []
    for t, v in enumerate(E):
        cur = {k: F(x) for k, x in v.items()}
        co = [F(0)] * ns
        co[t] = F(1)
        for piv, rv, rc in redu:
            f = cur.get(piv)
            if f:
                f = f / rv[piv]
                for k2, x in rv.items():
                    cur[k2] = cur.get(k2, F(0)) - f * x
                cur = {k2: x for k2, x in cur.items() if x}
                co = [a - f * b for a, b in zip(co, rc)]
        assert cur, "E is not independent"
        redu.append((min(cur), cur, co))
    out = []
    for tg in targets:
        cur = {k: F(x) for k, x in tg.items()}
        co = [F(0)] * ns
        for piv, rv, rc in redu:
            f = cur.get(piv)
            if f:
                f = f / rv[piv]
                for k2, x in rv.items():
                    cur[k2] = cur.get(k2, F(0)) - f * x
                cur = {k2: x for k2, x in cur.items() if x}
                co = [a + f * b for a, b in zip(co, rc)]
        if cur:
            return None
        out.append(co)
    return out


def independent_rows(M):
    """Indices of a maximal independent set of rows, exactly."""
    redu, keep = [], []
    for t, row in enumerate(M):
        cur = {j: F(x) for j, x in enumerate(row) if x}
        for piv, rv in redu:
            f = cur.get(piv)
            if f:
                f = f / rv[piv]
                for k2, x in rv.items():
                    cur[k2] = cur.get(k2, F(0)) - f * x
                cur = {k2: x for k2, x in cur.items() if x}
        if cur:
            redu.append((min(cur), cur))
            keep.append(t)
    return keep


def eigen_split(A):
    """
    Rows of U over the template basis: the +1 eigenvectors of J first.

    In coordinates a vector c transforms as c -> c A, so the +1 eigenspace is
    the row space of (I + A)/2 and the -1 eigenspace that of (I - A)/2.
    """
    ns = len(A)
    plus = [[(F(1) if s == t else F(0)) + A[t][s] for t in range(ns)]
            for s in range(ns)]
    minus = [[(F(1) if s == t else F(0)) - A[t][s] for t in range(ns)]
             for s in range(ns)]
    up = [plus[t] for t in independent_rows(plus)]
    um = [minus[t] for t in independent_rows(minus)]
    return up + um, len(up), len(um)


def combine(U, E):
    """Integer vectors for the rows of U against the template vectors E."""
    import math
    out = []
    for row in U:
        acc = {}
        for t, c in enumerate(row):
            if not c:
                continue
            for u, x in E[t].items():
                acc[u] = acc.get(u, F(0)) + c * x
        acc = {u: x for u, x in acc.items() if x}
        den = 1
        for x in acc.values():
            den = den * x.denominator // math.gcd(den, x.denominator)
        iv = {u: int(x * den) for u, x in acc.items()}
        g = 0
        for x in iv.values():
            g = math.gcd(g, abs(x))
        if g > 1:
            iv = {u: x // g for u, x in iv.items()}
        out.append(iv)
    return out


def congruence(U, M):
    ns, nu = len(M), len(U)
    tmp = [[sum(U[p][s] * M[s][t] for s in range(ns) if U[p][s])
            for t in range(ns)] for p in range(nu)]
    return [[sum(tmp[p][t] * U[q][t] for t in range(ns) if U[q][t])
             for q in range(nu)] for p in range(nu)]


# ------------------------------------------------------------------ the driver
def basis_perm(basis, g):
    index = {m: t for t, m in enumerate(basis)}
    return [index[act(g, m)] for m in basis]


def pushforward(vec, perm):
    return {perm[u]: c for u, c in vec.items()}


def check_action_direction(n, basis):
    """METHODS §7.1b trap 2, on the FULL group's generators."""
    gens = generators(n)
    g, h = gens[0], gens[-1]
    comp_gh = tuple(g[h[v]] for v in range(n * n))
    comp_hg = tuple(h[g[v]] for v in range(n * n))
    Pg, Ph = basis_perm(basis, g), basis_perm(basis, h)
    Pgh, Phg = basis_perm(basis, comp_gh), basis_perm(basis, comp_hg)
    lhs = [Pg[Ph[u]] for u in range(len(basis))]
    return lhs == Pgh, lhs == Phg


def check_equivariance(n, rowtype, coltype, kept, wr, wc, E, basis):
    """
    Row-equivariance and column-equivariance of every kept shape, which is what
    places it in the claimed isotypic component (linear in each weight plus
    equivariance => an element of Hom_{SxS}(lambda (x) mu, R^B)).
    """
    def permuted(w, kind, r1, r2):
        if kind == "triv":
            return w
        if kind == "vec":
            v = list(w)
            v[r1], v[r2] = v[r2], v[r1]
            return tuple(v)
        sw = (lambda x: r2 if x == r1 else (r1 if x == r2 else x))
        return {(sw(a), sw(b)): v for (a, b), v in w.items()}

    bad_row = bad_col = 0
    for a in range(n - 1):
        r1, r2 = a, a + 1
        grow = tuple((r2 if p // n == r1 else
                      (r1 if p // n == r2 else p // n)) * n + p % n
                     for p in range(n * n))
        want = [realise(c, n, rowtype, coltype,
                        permuted(wr, rowtype, r1, r2), wc) for c in kept]
        perm = basis_perm(basis, grow)
        index = {mo: t for t, mo in enumerate(basis)}
        for s, c in enumerate(kept):
            if (pushforward(E[s], perm)
                    != {index[mo]: x for mo, x in want[s].items()}):
                bad_row += 1
        gcol = tuple((p // n) * n + (r2 if p % n == r1 else
                                     (r1 if p % n == r2 else p % n))
                     for p in range(n * n))
        want = [realise(c, n, rowtype, coltype, wr,
                        permuted(wc, coltype, r1, r2)) for c in kept]
        perm = basis_perm(basis, gcol)
        for s, c in enumerate(kept):
            if (pushforward(E[s], perm)
                    != {index[mo]: x for mo, x in want[s].items()}):
                bad_col += 1
    return bad_row, bad_col


def weights(n, rowtype, coltype, seed):
    wr = (None if rowtype == "triv" else
          (sum_zero_full(n, seed) if rowtype == "vec"
           else two_index_full(n, rowtype == "asym", seed)[0]))
    wc = (None if coltype == "triv" else
          (sum_zero_full(n, seed + 57) if coltype == "vec"
           else two_index_full(n, coltype == "asym", seed + 57)[0]))
    return wr, wc


def run_family(rowtype, coltype, split, blocks, n, basis, cls_uf, cls_dir, y,
               seed=20260729):
    B = len(basis)
    index = {mo: t for t, mo in enumerate(basis)}
    wr, wc = weights(n, rowtype, coltype, seed)
    cand = candidates(rowtype, coltype)
    vecs = [realise(c, n, rowtype, coltype, wr, wc) for c in cand]
    kept_i, dropped, zero = tail.independent_subset(vecs)
    kept = [cand[t] for t in kept_i]
    want = sum(m for _, m, _ in blocks)
    names = " / ".join(nm for nm, _, _ in blocks)
    print(f"\n  --- {rowtype:4s} {coltype:4s}  ->  {names} ---")
    print(f"    candidates {len(cand)}: {len(kept_i)} independent, "
          f"{len(dropped)} dependent, {len(zero)} identically zero  "
          f"(predicted {want} / see §6b.35)")
    print(f"    degree-1 kept {sum(1 for c in kept if len(c) == 1)}, "
          f"degree-2 kept {sum(1 for c in kept if len(c) == 2)}")
    if zero:
        print(f"    vanished:  {[fmt(cand[t]) for t in zero]}")
    if dropped:
        print(f"    dependent: {[fmt(cand[t]) for t in dropped]}")
    print(f"    kept:      {[fmt(c) for c in kept]}")
    if len(kept_i) != want:
        print(f"    *** multiplicity {len(kept_i)} != predicted {want} ***")
        return []
    if not kept:
        return []

    E = [{index[mo]: c for mo, c in vecs[t].items()} for t in kept_i]
    br, bc = check_equivariance(n, rowtype, coltype, kept, wr, wc, E, basis)
    print(f"    equivariance: row failures {br}, column failures {bc}")

    # OBLIGATION 1 -- two independent routes to M
    N = vv.block_by_class(E, cls_uf, B)
    M_A = vv.contract(N, y)
    M_B = vv.block_dense(E, cls_dir, B, y)
    ns = len(E)
    mism = sum(1 for s in range(ns) for t in range(ns) if M_A[s][t] != M_B[s][t])
    sym = sum(1 for s in range(ns) for t in range(s) if M_A[s][t] != M_A[t][s])
    print(f"    OBLIGATION 1: route A vs route B {mism} mismatched of "
          f"{ns * ns};  symmetry {sym} failures")

    # OBLIGATION 2 -- B (x) Q, norms deliberately unequal
    wr2, wc2 = weights(n, rowtype, coltype, seed + 909)
    E2 = [{index[mo]: c for mo, c in
           realise(cand[t], n, rowtype, coltype, wr2, wc2).items()}
          for t in kept_i]
    M2 = vv.contract(vv.block_by_class(E2, cls_uf, B), y)
    ratios = set()
    for s in range(ns):
        for t in range(ns):
            if M_A[s][t]:
                ratios.add(F(M2[s][t], M_A[s][t]))
            elif M2[s][t]:
                ratios.add("INF")
    q1 = wnorm(rowtype, wr, n) * wnorm(coltype, wc, n)
    q2 = wnorm(rowtype, wr2, n) * wnorm(coltype, wc2, n)
    print(f"    OBLIGATION 2: {len(ratios)} distinct ratio(s) "
          f"{sorted(ratios, key=str)[:2]};  predicted {F(q2, q1)}"
          f"   (norms {q1} vs {q2}, unequal sides "
          f"{wnorm(rowtype, wr, n)} / {wnorm(coltype, wc, n)})")
    ok2 = ratios == {F(q2, q1)}

    G = vv.gram(E)
    out = []
    if not split:
        out.append(dict(name=blocks[0][0], dim=blocks[0][2](n), E=E, M=M_A,
                        G=G, N=N, kept=kept, ok=(mism == 0 and sym == 0
                                                 and ok2 and br == 0
                                                 and bc == 0)))
        return out

    # --- OBLIGATION 4: the J split, measured as a MATRIX (§6b.35 Prediction 3)
    gtr = tuple((p % n) * n + (p // n) for p in range(n * n))
    perm = basis_perm(basis, gtr)
    swapped = [realise(c, n, coltype, rowtype, wc, wr) for c in kept]
    Jimg = [pushforward({index[mo]: x for mo, x in sv.items()}, perm)
            for sv in swapped]
    A = solve_in_span(E, Jimg)
    if A is None:
        print("    *** J leaves the span: the templates are not J-stable ***")
        return []
    A2 = [[sum(A[s][u] * A[u][t] for u in range(ns)) for t in range(ns)]
          for s in range(ns)]
    invol = all(A2[s][t] == (1 if s == t else 0)
                for s in range(ns) for t in range(ns))
    trace = sum(A[s][s] for s in range(ns))
    U, npl, nmi = eigen_split(A)
    print(f"    J as a matrix on the {ns} kept shapes: J^2 = I {invol}, "
          f"trace {trace} (predicted {blocks[0][1] - blocks[1][1]})")
    print(f"    dim(+1) = {npl} (predicted {blocks[0][1]}), "
          f"dim(-1) = {nmi} (predicted {blocks[1][1]})")
    Ms, Gs = congruence(U, M_A), congruence(U, G)
    offM = sum(1 for p in range(npl) for q in range(npl, ns) if Ms[p][q])
    offG = sum(1 for p in range(npl) for q in range(npl, ns) if Gs[p][q])
    print(f"    SPLIT TEST: off-diagonal {npl} x {nmi} block -> {offM} nonzero "
          f"in M, {offG} nonzero in G  (predicted 0 and 0)")
    okall = (mism == 0 and sym == 0 and ok2 and br == 0 and bc == 0
             and invol and offM == 0 and offG == 0
             and npl == blocks[0][1] and nmi == blocks[1][1])
    Ecomb = combine(U, E)
    for bi, (nm, mult, dimf) in enumerate(blocks):
        lo, hi = (0, npl) if bi == 0 else (npl, ns)
        if mult == 0:
            print(f"    {nm}: predicted absent, measured dim {hi - lo}")
            continue
        out.append(dict(
            name=nm, dim=dimf(n), E=Ecomb[lo:hi],
            M=[[Ms[p][q] for q in range(lo, hi)] for p in range(lo, hi)],
            G=[[Gs[p][q] for q in range(lo, hi)] for p in range(lo, hi)],
            N=None, kept=kept, U=[U[p] for p in range(lo, hi)], ok=okall))
    return out


def run(n, gvars, gidx, y=None, spectrum=True, seed=20260729):
    import random
    basis = k4.basis_of(n)
    B = len(basis)
    print(f"\n=== n = {n}:  B = {B} ===")

    hom, anti = check_action_direction(n, basis)
    print(f"  action direction (full group): P_g P_h == P_(g.h) {hom}, "
          f"== P_(h.g) {anti}   (want True, False)")

    cls_dir, ncache = g_direct_class_array(n, basis, gidx)
    cls_uf, norb = g_unionfind_class_array(n, basis, gidx)
    diff = sum(1 for t in range(B * B) if cls_uf[t] != cls_dir[t])
    print(f"  class arrays: union-find ({norb} orbits, predicted 51) vs direct "
          f"canon_pair ({ncache} cache keys) -> {diff} differing of {B * B}")

    reps, _ = orbits(basis, generators(n))
    print(f"  G-orbits on the monomial basis: {len(reps)}  (predicted 4)")

    if y is None:
        rng = random.Random(4242)
        y = [rng.randint(-40, 40) or 7 for _ in range(len(gvars))]

    res = []
    for rt, ct, split, blocks in FAMILIES:
        res += run_family(rt, ct, split, blocks, n, basis, cls_uf, cls_dir, y,
                          seed=seed)
    print(f"\n  blocks with multiplicity > 0: {len(res)}  (predicted 10)")
    print(f"  multiplicity total {sum(len(r['E']) for r in res)}  "
          f"(predicted 23)")
    npins = sum(len(r["E"]) * (len(r["E"]) - 1) // 2 for r in res)
    print(f"  off-diagonal pin conditions {npins}  (predicted 28)")

    # OBLIGATION 6: (1|1) ext + against the G-orbit indicators
    triv = next((r for r in res if r["name"] == "(1|1) ext +"), None)
    if triv is not None:
        ind = [{u: 1 for u in mem} for mem in reps.values()]
        rows = []
        for v in ind + triv["E"]:
            rows.append([v.get(u, 0) for u in range(B)])
        r_ind = len(independent_rows(rows[:len(ind)]))
        r_all = len(independent_rows(rows))
        print(f"  OBLIGATION 6: rank(G-orbit indicators) {r_ind}, "
              f"rank(indicators + (1|1) ext + basis) {r_all}  "
              f"(both predicted 4)")

    if spectrum:
        import numpy as np
        yv = np.array(y, dtype=float)
        ca = np.frombuffer(cls_dir, dtype=np.int32).reshape(B, B)
        spec = np.sort(np.linalg.eigvalsh(yv[ca]))
        tol = 1e-7 * max(abs(spec[0]), abs(spec[-1]))
        print("\n  OBLIGATION 3: multiplicity in spec(H_0)")
        covered = 0
        for r in res:
            Mf = np.array([[float(x) for x in row] for row in r["M"]])
            Gf = np.array([[float(x) for x in row] for row in r["G"]])
            L = np.linalg.cholesky(Gf)
            C1 = np.linalg.solve(L, Mf)
            Cm = np.linalg.solve(L, C1.T).T
            ge = np.linalg.eigvalsh(0.5 * (Cm + Cm.T))
            c = [int(np.sum(np.abs(spec - mu) < tol)) for mu in ge]
            covered += sum(c)
            print(f"    {r['name']:28s} {sorted(c)}  predicted {r['dim']}  -> "
                  f"{sum(1 for x in c if x == r['dim'])} of {len(c)} agree")
        print(f"    the ten blocks cover {covered} of {B}  (predicted {B})")
    return res


def canonical_blocks(n, basis, gvars=None, gidx=None, seed=20260729):
    """
    The ten canonical bases as {basis index: integer} vectors, for the pin
    re-test.  Silent: no obligations, no spectrum -- those are `run`'s job.
    """
    index = {mo: t for t, mo in enumerate(basis)}
    out = []
    for rt, ct, split, blocks in FAMILIES:
        wr, wc = weights(n, rt, ct, seed)
        cand = candidates(rt, ct)
        vecs = [realise(c, n, rt, ct, wr, wc) for c in cand]
        kept_i, _, _ = tail.independent_subset(vecs)
        want = sum(m for _, m, _ in blocks)
        assert len(kept_i) == want, (rt, ct, len(kept_i), want)
        if not kept_i:
            continue
        E = [{index[mo]: c for mo, c in vecs[t].items()} for t in kept_i]
        if not split:
            out.append((blocks[0][0], E))
            continue
        gtr = tuple((p % n) * n + (p // n) for p in range(n * n))
        perm = basis_perm(basis, gtr)
        Jimg = [pushforward({index[mo]: x for mo, x in
                             realise(cand[t], n, ct, rt, wc, wr).items()},
                            perm) for t in kept_i]
        A = solve_in_span(E, Jimg)
        assert A is not None, (rt, ct)
        U, npl, nmi = eigen_split(A)
        assert (npl, nmi) == (blocks[0][1], blocks[1][1]), (rt, ct, npl, nmi)
        Ec = combine(U, E)
        for bi, (nm, mult, _) in enumerate(blocks):
            if mult == 0:
                continue
            lo, hi = (0, npl) if bi == 0 else (npl, len(E))
            out.append((nm, Ec[lo:hi]))
    return out


if __name__ == "__main__":
    args = sys.argv[1:]
    spectrum = "--no-spectrum" not in args
    ns = [int(a) for a in args if not a.startswith("-")] or [5, 6]
    print("sigma_0's ten canonical blocks -- NOTES §6b.35")
    print("PREDICTED: candidate/kept/dependent/zero per family as tabulated; "
          "multiplicities 5,5,4,2,2,1,1,1,1,1 summing to 23; two ABSENT "
          "families all-zero; degree-1 kept exactly 3 in total; J traces 3 and "
          "4; split-test off-diagonals 0; 28 pin conditions; 51 classes.")
    gvars = gvars_cached()
    gidx = {k: i for i, k in enumerate(gvars)}
    print(f"  |gvars| = {len(gvars)}  (predicted 51)")
    for n in ns:
        run(n, gvars, gidx, spectrum=spectrum)
