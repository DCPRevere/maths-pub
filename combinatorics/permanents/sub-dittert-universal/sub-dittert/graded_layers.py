"""
THE GRADED (TAYLOR-LAYER) DECOMPOSITION of the sub-Dittert deficit.

Everything here is DERIVED and then CHECKED exactly over Fraction.  Nothing is
fitted.  Ground truth is always F computed from the 1992 functional Phi.

SETTING.  A in K_n (nonnegative, total sum n).  Put B = A - J_n/n, so the total
sum of B is 0 -- B lives on the sum-zero hyperplane, NOT on the doubly-centred
subspace.  Write R_i = sum_j B_ij, C_j = sum_i B_ij (both sum to 0).

    F_{n,k}(B) := (2 - k!/n^k) - [E_k(r) + E_k(c) - P_k(A)]

and the conjecture is F >= 0.

THE LAYER CLAIM.  The universal identity (allk_universal.py, and Lean
SubDittertUniversal.lean) reads

    F = sum_{d=1}^{k} [ t_d sigma_d(B) - s_d (e_d(R) + e_d(C)) ],
    s_d = [k]_d/[n]_d,   t_d = s_d^2 (k-d)!/n^(k-d).

Each summand is ALREADY homogeneous of degree d in B, because sigma_d, e_d(R),
e_d(C) all are.  So the Taylor layers of F at the barycentre are read off with no
work at all:

    L_m(B) = t_m sigma_m(B) - s_m (e_m(R) + e_m(C)),     1 <= m <= k,
    L_m    = 0                                          m = 0 or m > k.

PART 1 verifies this (homogeneity, and F(cB) = sum c^m L_m(B) identically in c).

PART 2 derives closed forms for sigma_m by Moebius inversion over PAIRS of set
partitions of [m].  Writing S_m for the sum over m-tuples with distinct rows and
distinct columns, sigma_m = S_m/m! and

    S_m = sum_{P,Q} mu(P) mu(Q) g(P,Q),   mu(P) = prod_{blocks} (-1)^(|b|-1)(|b|-1)!,

where g(P,Q) sums the same product with row index constant on blocks of P and
column index constant on blocks of Q, each block value ranging freely over [n].
That sum FACTORISES over the connected components of the bipartite multigraph
G(P,Q) whose row vertices are blocks of P, column vertices blocks of Q, and whose
m edges are the m factors.  So sigma_m is a rational combination of products of
CONNECTED bipartite-multigraph invariants -- exactly the S_n x S_n orbit sums.

Two filtration facts fall out and are checked:

  * a component with exactly ONE edge contributes the total sum, so it dies on the
    sum-zero hyperplane;
  * a vertex of DEGREE ONE contributes a row sum or a column sum, so on the
    doubly-centred subspace (R = C = 0) only invariants with MINIMUM DEGREE >= 2
    survive.

Usage:  GUARD_MEM=8G GUARD_CPUS=250% GUARD_THREADS=2 ../guard.sh \
            python3 graded_layers.py
"""

import random
import sys
from fractions import Fraction as Fr
from itertools import combinations, permutations, product
from math import comb, factorial, gcd

OUT = []


def log(*a):
    s = " ".join(str(x) for x in a)
    print(s)
    OUT.append(s)


# ============================================================ 0. primitives


def elem_sym(vec, d):
    e = [Fr(0)] * (d + 1)
    e[0] = Fr(1)
    for x in vec:
        for j in range(min(d, len(vec)), 0, -1):
            e[j] += e[j - 1] * x
    return e[d]


def per(M):
    m = len(M)
    if m == 0:
        return Fr(1)
    tot = Fr(0)
    for p in permutations(range(m)):
        prod = Fr(1)
        for i in range(m):
            prod *= M[i][p[i]]
        tot += prod
    return tot


def sigma_direct(A, d):
    """Sum of all d x d subpermanents.  Ground truth, brute force."""
    n = len(A)
    if d == 0:
        return Fr(1)
    if d > n:
        return Fr(0)
    tot = Fr(0)
    for R in combinations(range(n), d):
        for C in combinations(range(n), d):
            tot += per([[A[i][j] for j in C] for i in R])
    return tot


def lines(M):
    n = len(M)
    return ([sum(M[i][j] for j in range(n)) for i in range(n)],
            [sum(M[i][j] for i in range(n)) for j in range(n)])


def Phi(A, k):
    n = len(A)
    N = Fr(comb(n, k))
    r, c = lines(A)
    return elem_sym(r, k) / N + elem_sym(c, k) / N - sigma_direct(A, k) / (N * N)


def F_direct(b, k):
    """GROUND TRUTH: F from the definition of the 1992 functional."""
    n = len(b)
    A = [[Fr(1, n) + b[i][j] for j in range(n)] for i in range(n)]
    return (2 - Fr(factorial(k), n ** k)) - Phi(A, k)


def falling(x, d):
    out = Fr(1)
    for i in range(d):
        out *= (x - i)
    return out


def s_coef(n, k, d):
    return falling(Fr(k), d) / falling(Fr(n), d)


def t_coef(n, k, d):
    if d > k:
        return Fr(0)
    return s_coef(n, k, d) ** 2 * Fr(factorial(k - d), n ** (k - d))


def L_layer(b, n, k, m):
    """The claimed degree-m Taylor layer of F at the barycentre."""
    if m == 0 or m > k:
        return Fr(0)
    R, C = lines(b)
    return (t_coef(n, k, m) * sigma_direct(b, m)
            - s_coef(n, k, m) * (elem_sym(R, m) + elem_sym(C, m)))


# ------------------------------------------------------------- test matrices


def rand_hyperplane(n, rng, spread=6, denom=4):
    """Random rational b with total sum 0 (row/col sums NOT zero)."""
    b = [[Fr(rng.randint(-spread, spread), rng.randint(1, denom))
          for _ in range(n)] for _ in range(n)]
    tot = sum(sum(r) for r in b)
    b[0][0] -= tot
    return b


def rand_general(n, rng, spread=6, denom=4):
    """Random rational b, total sum unconstrained."""
    return [[Fr(rng.randint(-spread, spread), rng.randint(1, denom))
             for _ in range(n)] for _ in range(n)]


def rand_centred(n, rng, spread=4):
    """Random b with every row sum and every column sum zero."""
    M = [[Fr(0)] * n for _ in range(n)]
    for _ in range(3 * n):
        i, i2 = rng.sample(range(n), 2)
        j, j2 = rng.sample(range(n), 2)
        v = Fr(rng.randint(-spread, spread), rng.randint(1, 3))
        M[i][j] += v
        M[i2][j2] += v
        M[i][j2] -= v
        M[i2][j] -= v
    return M


# ================================================== 1. the layers are the layers


def part1(rng):
    log("=" * 74)
    log("PART 1.  L_m IS the degree-m Taylor layer of F at the barycentre.")
    log("=" * 74)
    log("  L_m(b) := t_m sigma_m(b) - s_m (e_m(R) + e_m(C)).")
    log("  Three checks, all exact over Q:")
    log("   (a) sum_m L_m(b) == F_direct(b)   for b on the sum-zero hyperplane;")
    log("   (b) L_m(c b) == c^m L_m(b)        (homogeneity, so these ARE layers);")
    log("   (c) F(c b) == sum_m c^m L_m(b)    identically in c.")
    log("")
    bad = 0
    for (n, k) in ((5, 3), (5, 4), (6, 4), (6, 5), (7, 5)):
        for trial in range(3):
            b = rand_hyperplane(n, rng)
            Ls = [L_layer(b, n, k, m) for m in range(0, k + 1)]
            # (a)
            f = F_direct(b, k)
            if sum(Ls) != f:
                bad += 1
                log(f"  n={n} k={k} (a) FAIL  F={f}  sum L={sum(Ls)}")
            # (b)
            for c in (Fr(2), Fr(-1), Fr(3, 5)):
                cb = [[c * x for x in row] for row in b]
                for m in range(0, k + 1):
                    if L_layer(cb, n, k, m) != c ** m * Ls[m]:
                        bad += 1
                        log(f"  n={n} k={k} m={m} (b) FAIL at c={c}")
            # (c)
            for c in (Fr(2), Fr(-1), Fr(3, 5), Fr(-7, 4)):
                cb = [[c * x for x in row] for row in b]
                lhs = F_direct(cb, k)
                rhs = sum(c ** m * Ls[m] for m in range(0, k + 1))
                if lhs != rhs:
                    bad += 1
                    log(f"  n={n} k={k} (c) FAIL at c={c}")
            if trial == 0:
                log(f"  n={n} k={k}:  L_0={Ls[0]}  L_1={Ls[1]}"
                    f"   (both must be 0 on the hyperplane)")
    log("")
    log("  Also: OFF the hyperplane, L_1 = (t_1 - 2 s_1) * (total sum),")
    log("  which is the criticality fact and the only linear term there is.")
    for (n, k) in ((5, 3), (6, 4), (7, 5)):
        b = rand_general(n, rng)
        tot = sum(sum(r) for r in b)
        claim = (t_coef(n, k, 1) - 2 * s_coef(n, k, 1)) * tot
        got = L_layer(b, n, k, 1)
        ok = (claim == got)
        if not ok:
            bad += 1
        log(f"    n={n} k={k}: L_1 = {got}  claim {claim}  match {ok}")
    log("")
    log(f"  PART 1 mismatches: {bad}")
    log("")
    return bad


# ======================================== 2. Moebius expansion of sigma_m


def set_partitions(m):
    """All set partitions of range(m), each as a tuple of frozensets."""
    if m == 0:
        return [()]
    out = []

    def rec(i, blocks):
        if i == m:
            out.append(tuple(frozenset(b) for b in blocks))
            return
        for t in range(len(blocks)):
            blocks[t].append(i)
            rec(i + 1, blocks)
            blocks[t].pop()
        blocks.append([i])
        rec(i + 1, blocks)
        blocks.pop()

    rec(0, [])
    return out


def mu_bot(P):
    """mu(bottom, P) in the partition lattice."""
    out = 1
    for blk in P:
        out *= (-1) ** (len(blk) - 1) * factorial(len(blk) - 1)
    return out


def block_index(P, m):
    """map element -> block number."""
    idx = [0] * m
    for t, blk in enumerate(P):
        for x in blk:
            idx[x] = t
    return idx


def components(edges, nr, nc):
    """Split an edge list (row,col) into connected components.
    Returns list of edge lists, each relabelled to consecutive vertices."""
    parent = list(range(nr + nc))

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    def union(a, b):
        ra, rb = find(a), find(b)
        if ra != rb:
            parent[ra] = rb

    for (u, w) in edges:
        union(u, nr + w)
    buckets = {}
    for (u, w) in edges:
        buckets.setdefault(find(u), []).append((u, w))
    out = []
    for es in buckets.values():
        rs = sorted({u for u, _ in es})
        cs = sorted({w for _, w in es})
        rmap = {u: i for i, u in enumerate(rs)}
        cmap = {w: j for j, w in enumerate(cs)}
        out.append((tuple(sorted((rmap[u], cmap[w]) for u, w in es)),
                    len(rs), len(cs)))
    return out


_CANON_CACHE = {}


def canon(edges, nr, nc):
    """Canonical form of a bipartite multigraph: the multiplicity matrix,
    minimised over row and column relabellings.  Rows and columns are NOT
    interchangeable (they are matrix rows and columns)."""
    key = (edges, nr, nc)
    if key in _CANON_CACHE:
        return _CANON_CACHE[key]
    M = [[0] * nc for _ in range(nr)]
    for (u, w) in edges:
        M[u][w] += 1
    best = None
    for rp in permutations(range(nr)):
        rows = [M[rp[i]] for i in range(nr)]
        for cp in permutations(range(nc)):
            cand = tuple(tuple(rows[i][cp[j]] for j in range(nc))
                         for i in range(nr))
            if best is None or cand < best:
                best = cand
    _CANON_CACHE[key] = best
    return best


NAMES = {
    ((1,),): "T",
    ((2,),): "Q",
    ((1, 1),): "p2R",
    ((1,), (1,)): "p2C",
    ((3,),): "p3b",
    ((1, 2),): "URb",
    ((1,), (2,)): "UCb",
    ((1, 1, 1),): "p3R",
    ((1,), (1,), (1,)): "p3C",
    ((0, 1), (1, 1)): "W",
    ((4,),): "p4b",
    ((2, 2),): "YR",
    ((2,), (2,)): "YC",
    ((0, 1), (1, 1)): "W",
    ((1, 1), (1, 1)): "Z4",
    ((1, 1, 1, 1),): "p4R",
    ((1,), (1,), (1,), (1,)): "p4C",
    ((1, 3),): "p3_R1",
    ((1,), (3,)): "p3_C1",
    ((0, 0, 1), (1, 1, 1)): "W4R",
    ((0, 1), (0, 1), (1, 1)): "W4C",
    ((0, 1), (1, 2)): "WQ_R",
    ((0, 2), (1, 1)): "WQ_C",
    ((1, 2, 0), (0, 1, 1)): "PATH5",
}


def nameof(cf):
    if cf in NAMES:
        return NAMES[cf]
    return "G" + "|".join("".join(str(x) for x in row) for row in cf)


def sigma_expansion(m):
    """sigma_m as a dict: {sorted tuple of canonical components : Fraction}."""
    parts = set_partitions(m)
    terms = {}
    for P in parts:
        muP = mu_bot(P)
        ip = block_index(P, m)
        for Q in parts:
            muQ = mu_bot(Q)
            iq = block_index(Q, m)
            edges = [(ip[a], iq[a]) for a in range(m)]
            comps = components(edges, len(P), len(Q))
            key = tuple(sorted(canon(*c) for c in comps))
            terms[key] = terms.get(key, Fr(0)) + Fr(muP * muQ, factorial(m))
    return {k: v for k, v in terms.items() if v != 0}


# ------------------------------------------- evaluate an invariant exactly


_EVAL_CACHE = {}


def eval_invariant(cf, b, n):
    """Sum over free assignments of the graph's vertices to [n] of the product
    over edges of b.  Tensor-network contraction, exact."""
    key = (cf, id(b))
    if key in _EVAL_CACHE:
        return _EVAL_CACHE[key]
    nr, nc = len(cf), len(cf[0])
    factors = []
    base = {(i, j): b[i][j] for i in range(n) for j in range(n)}
    for i in range(nr):
        for j in range(nc):
            for _ in range(cf[i][j]):
                factors.append(((("r", i), ("c", j)), base))
    live = set()
    for vs, _ in factors:
        live |= set(vs)
    while live:
        # eliminate the variable giving the smallest residual scope
        pick, pscope = None, None
        for v in live:
            sc = set()
            for vs, _ in factors:
                if v in vs:
                    sc |= set(vs)
            sc.discard(v)
            if pscope is None or len(sc) < len(pscope):
                pick, pscope = v, sc
        inv = [f for f in factors if pick in f[0]]
        rest = [f for f in factors if pick not in f[0]]
        scope = tuple(sorted(pscope))
        tab = {}
        for assign in product(range(n), repeat=len(scope)):
            amap = dict(zip(scope, assign))
            tot = Fr(0)
            for val in range(n):
                amap[pick] = val
                pr = Fr(1)
                for vs, t in inv:
                    pr *= t.get(tuple(amap[x] for x in vs), Fr(0))
                    if pr == 0:
                        break
                tot += pr
            if tot != 0:
                tab[assign] = tot
        factors = rest + [(scope, tab)]
        live.discard(pick)
    out = Fr(1)
    for _, t in factors:
        out *= t.get((), Fr(0))
    _EVAL_CACHE[key] = out
    return out


def eval_expansion(terms, b, n):
    tot = Fr(0)
    for comps, coef in terms.items():
        v = coef
        for cf in comps:
            v *= eval_invariant(cf, b, n)
        tot += v
    return tot


def show_expansion(terms, label, restrict=None):
    """restrict: None | 'hyper' | 'centred'."""
    keep = {}
    for comps, coef in terms.items():
        if restrict in ("hyper", "centred"):
            if any(sum(sum(r) for r in cf) == 1 for cf in comps):
                continue
        if restrict == "centred":
            drop = False
            for cf in comps:
                rd = [sum(r) for r in cf]
                cd = [sum(cf[i][j] for i in range(len(cf)))
                      for j in range(len(cf[0]))]
                if min(rd + cd) < 2:
                    drop = True
            if drop:
                continue
        keep[comps] = coef
    items = sorted(keep.items(),
                   key=lambda kv: (sum(len(c) for c in kv[0]),
                                   [nameof(c) for c in kv[0]]))
    pieces = []
    for comps, coef in items:
        nm = "*".join(nameof(c) for c in comps)
        a = abs(coef)
        astr = "" if a == 1 else f"{a} "
        pieces.append(("- " if coef < 0 else "+ ") + astr + nm)
    body = " ".join(pieces).lstrip("+ ") if pieces else "0"
    log("  " + label + " = " + body)
    return keep


def part2(rng):
    log("=" * 74)
    log("PART 2.  Closed forms for sigma_m, by Moebius inversion over pairs of")
    log("         set partitions of [m].  Derived, then checked against the")
    log("         brute-force subpermanent sum.")
    log("=" * 74)
    log("  Atom dictionary (connected bipartite multigraph -> invariant):")
    log("    T   = sum_ij b_ij                  (single edge)")
    log("    Q   = sum_ij b_ij^2                (double edge)")
    log("    p2R = sum_i R_i^2                  (one row, two cols)")
    log("    p2C = sum_j C_j^2")
    log("    p3b = sum_ij b_ij^3                (triple edge)")
    log("    p3R = sum_i R_i^3 ,  p3C = sum_j C_j^3")
    log("    URb = sum_ij b_ij^2 R_i ,  UCb = sum_ij b_ij^2 C_j")
    log("    W   = sum_ij R_i b_ij C_j          (3-edge path)")
    log("    p4b = sum_ij b_ij^4                (quadruple edge)")
    log("    YR  = sum_i (sum_j b_ij^2)^2 ,  YC = sum_j (sum_i b_ij^2)^2")
    log("    Z4  = sum_{i,i',j,j'} b_ij b_ij' b_i'j b_i'j'  = ||b^T b||_F^2")
    log("    Gxxx = the canonical multiplicity matrix, rows | separated")
    log("")
    exps = {}
    for m in (2, 3, 4, 5):
        exps[m] = sigma_expansion(m)
        log(f"  --- sigma_{m} : {len(exps[m])} orbit terms in full generality")
        show_expansion(exps[m], f"sigma_{m}")
        log(f"      on the sum-zero hyperplane (T = 0):")
        show_expansion(exps[m], f"sigma_{m}|T=0", restrict="hyper")
        log(f"      on the doubly-centred subspace (R = C = 0):")
        show_expansion(exps[m], f"sigma_{m}|R=C=0", restrict="centred")
        log("")

    log("  VALIDATION of the closed forms against brute force:")
    bad = 0
    for n in (4, 5, 6):
        for kind, gen in (("general ", rand_general),
                          ("hyper  ", rand_hyperplane),
                          ("centred", rand_centred)):
            for _ in range(2):
                b = gen(n, rng)
                _EVAL_CACHE.clear()
                for m in (2, 3, 4, 5):
                    if m > n:
                        continue
                    want = sigma_direct(b, m)
                    got = eval_expansion(exps[m], b, n)
                    if want != got:
                        bad += 1
                        log(f"    n={n} {kind} m={m} FAIL  direct {want}"
                            f"  expansion {got}")
            log(f"    n={n} {kind}: sigma_2..sigma_5 checked")
    log(f"  PART 2 mismatches: {bad}")
    log("")
    return bad, exps


# ============================================ 3. the layer forms, named


def part3(exps, rng):
    log("=" * 74)
    log("PART 3.  The layers themselves, on the sum-zero hyperplane.")
    log("=" * 74)
    log("  With e_1(R) = T = 0, Newton gives  e_2 = -p2/2,  e_3 = p3/3,")
    log("  e_4 = p2^2/8 - p4/4.  Substituting the sigma expansions:")
    log("")
    log("  L_2 = (t_2/2) Q  +  ((s_2 - t_2)/2) (p2R + p2C)")
    log("")
    log("  L_3 = ((t_3 - s_3)/3) (p3R + p3C)")
    log("        + t_3 ( W - URb - UCb + (2/3) p3b )")
    log("")
    log("  L_4 : coefficients printed below from the sigma_4 expansion.")
    log("")
    bad = 0
    log("  CHECK of the hand forms for L_2 and L_3 against L_layer:")
    for (n, k) in ((5, 3), (5, 4), (6, 4), (6, 5), (7, 5)):
        s2, t2 = s_coef(n, k, 2), t_coef(n, k, 2)
        s3, t3 = s_coef(n, k, 3), t_coef(n, k, 3)
        for _ in range(2):
            b = rand_hyperplane(n, rng)
            R, C = lines(b)
            Q = sum(b[i][j] ** 2 for i in range(n) for j in range(n))
            p2R = sum(x * x for x in R)
            p2C = sum(x * x for x in C)
            p3R = sum(x ** 3 for x in R)
            p3C = sum(x ** 3 for x in C)
            p3b = sum(b[i][j] ** 3 for i in range(n) for j in range(n))
            URb = sum(b[i][j] ** 2 * R[i] for i in range(n) for j in range(n))
            UCb = sum(b[i][j] ** 2 * C[j] for i in range(n) for j in range(n))
            W = sum(R[i] * b[i][j] * C[j] for i in range(n) for j in range(n))
            l2 = t2 / 2 * Q + (s2 - t2) / 2 * (p2R + p2C)
            l3 = (t3 - s3) / 3 * (p3R + p3C) + t3 * (W - URb - UCb
                                                     + Fr(2, 3) * p3b)
            if l2 != L_layer(b, n, k, 2):
                bad += 1
                log(f"    n={n} k={k} L_2 FAIL")
            if l3 != L_layer(b, n, k, 3):
                bad += 1
                log(f"    n={n} k={k} L_3 FAIL")
        log(f"    n={n} k={k}: L_2, L_3 hand forms match")
    log("")
    log("  THE p_m COEFFICIENT LAW.  The only partition pair whose graph is a")
    log("  single m-fold edge is P = Q = top, with mu = ((-1)^(m-1)(m-1)!)^2,")
    log("  so the coefficient of p_m(b) = sum b_ij^m in sigma_m is exactly")
    log("  ((m-1)!)^2/m! = (m-1)!/m.  Checked from the expansions:")
    for m in (2, 3, 4, 5):
        cf = tuple([tuple([m])])
        got = exps[m].get((cf,), Fr(0))
        want = Fr(factorial(m - 1), m)
        ok = got == want
        if not ok:
            bad += 1
        log(f"    m={m}: coefficient of p{m}b = {got}   (m-1)!/m = {want}"
            f"   match {ok}")
    log("")
    log(f"  PART 3 mismatches: {bad}")
    log("")
    return bad


# ================================================ 4. the layer-size ledger


def partitions_of(m):
    out = []

    def rec(rem, mx, cur):
        if rem == 0:
            out.append(tuple(cur))
            return
        for p in range(min(rem, mx), 0, -1):
            cur.append(p)
            rec(rem - p, p, cur)
            cur.pop()

    rec(m, m, [])
    return out


def tables_with_margins(lam, mu):
    """All nonneg integer matrices with row sums lam, col sums mu."""
    nr, nc = len(lam), len(mu)
    out = []

    def rec(i, colrem, rows):
        if i == nr:
            if all(c == 0 for c in colrem):
                out.append(tuple(rows))
            return

        def fill(j, rem, cur):
            if j == nc:
                if rem == 0:
                    nc2 = list(colrem)
                    for jj in range(nc):
                        nc2[jj] -= cur[jj]
                    rec(i + 1, nc2, rows + [tuple(cur)])
                return
            for v in range(min(rem, colrem[j]) + 1):
                cur.append(v)
                fill(j + 1, rem - v, cur)
                cur.pop()

        fill(0, lam[i], [])

    rec(0, list(mu), [])
    return out


def equal_part_perms(lam):
    """Permutations of positions preserving the multiset of equal parts."""
    groups = {}
    for i, p in enumerate(lam):
        groups.setdefault(p, []).append(i)
    blocks = list(groups.values())
    outs = [tuple(range(len(lam)))]
    for blk in blocks:
        new = []
        for base in outs:
            for pp in permutations(blk):
                cur = list(base)
                for a, b in zip(blk, pp):
                    cur[a] = base[b]
                new.append(tuple(cur))
        outs = new
    return outs


def is_connected_ok(M):
    """True if no connected component has exactly one edge."""
    nr, nc = len(M), len(M[0])
    parent = list(range(nr + nc))

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    for i in range(nr):
        for j in range(nc):
            if M[i][j]:
                a, b = find(i), find(nr + j)
                if a != b:
                    parent[a] = b
    tot = {}
    for i in range(nr):
        for j in range(nc):
            if M[i][j]:
                tot[find(i)] = tot.get(find(i), 0) + M[i][j]
    return all(v != 1 for v in tot.values())


def cycle_type_count(m, lam):
    """Number of permutations of [m] with cycle type lam."""
    mult = {}
    for p in lam:
        mult[p] = mult.get(p, 0) + 1
    den = 1
    for i, c in mult.items():
        den *= i ** c * factorial(c)
    return factorial(m) // den


def series_mul(a, b, N):
    out = [Fr(0)] * (N + 1)
    for i, x in enumerate(a):
        if x == 0 or i > N:
            continue
        for j, y in enumerate(b):
            if i + j > N:
                break
            if y:
                out[i + j] += x * y
    return out


def count_all(mmax):
    """count_all[m] = number of m-edge bipartite multigraphs up to iso, by
    Burnside over S_m x S_m acting on the cells of an m x m grid.  Orbits of
    size-m cell multisets ARE the isomorphism classes (isolated vertices carry
    no information, and m edges never need more than m vertices a side)."""
    out = [1] + [0] * mmax
    for m in range(1, mmax + 1):
        tot = Fr(0)
        parts = partitions_of(m)
        for lam in parts:
            nl = cycle_type_count(m, lam)
            for mu in parts:
                nm = cycle_type_count(m, mu)
                # cell orbits: gcd(a,b) orbits of length lcm(a,b) per cycle pair
                gen = [Fr(1)] + [Fr(0)] * m
                for a in lam:
                    for b in mu:
                        g = gcd(a, b)
                        L = a * b // g
                        # multiply by (1/(1-x^L))^g
                        for _ in range(g):
                            inv = [Fr(0)] * (m + 1)
                            e = 0
                            while e <= m:
                                inv[e] = Fr(1)
                                e += L
                            gen = series_mul(gen, inv, m)
                tot += nl * nm * gen[m]
        out[m] = tot / Fr(factorial(m)) ** 2
        assert out[m].denominator == 1, (m, out[m])
        out[m] = int(out[m])
    return out


def connected_counts(allc, mmax):
    """Inverse Euler transform: allc is the multiset-of-components count."""
    A = [Fr(x) for x in allc]
    # L = log A, power series, A[0] = 1
    L = [Fr(0)] * (mmax + 1)
    for N in range(1, mmax + 1):
        acc = A[N]
        for j in range(1, N):
            acc -= Fr(j, N) * L[j] * A[N - j]
        L[N] = acc
    a = [0] * (mmax + 1)
    for N in range(1, mmax + 1):
        D = N * L[N]
        for m in range(1, N):
            if N % m == 0:
                D -= m * a[m]
        assert (D / N).denominator == 1, (N, D)
        a[N] = int(D / N)
    return a


def multiset_counts(atoms, mmax, minedges):
    """Number of multisets of connected atoms, all with >= minedges edges."""
    gen = [Fr(1)] + [Fr(0)] * mmax
    for m in range(minedges, mmax + 1):
        for _ in range(atoms[m]):
            inv = [Fr(0)] * (mmax + 1)
            e = 0
            while e <= mmax:
                inv[e] = Fr(1)
                e += m
            gen = series_mul(gen, inv, mmax)
    return [int(x) for x in gen]


def count_mindeg2(m):
    """m-edge bipartite multigraphs with every degree >= 2, up to iso.  Both
    margins then have at most m/2 parts, so direct canonicalisation is cheap."""
    seen = set()
    for lam in partitions_of(m):
        if min(lam) < 2:
            continue
        rperms = equal_part_perms(lam)
        for mu in partitions_of(m):
            if min(mu) < 2:
                continue
            cperms = equal_part_perms(mu)
            for M in tables_with_margins(lam, mu):
                best = None
                for rp in rperms:
                    for cp in cperms:
                        cand = tuple(tuple(M[rp[i]][cp[j]]
                                           for j in range(len(mu)))
                                     for i in range(len(lam)))
                        if best is None or cand < best:
                            best = cand
                seen.add((len(lam), len(mu), best))
    return len(seen)


def ledger(mmax=8):
    log("=" * 74)
    log("PART 4.  THE LAYER-SIZE LEDGER.  How many S_n x S_n orbit terms a")
    log("         degree-m layer can carry (n >= m).  An orbit of degree-m")
    log("         monomials in B IS a bipartite multigraph with m edges, up to")
    log("         row and column relabelling.  Counted by Burnside over")
    log("         S_m x S_m on the cells of an m x m grid; the connected count")
    log("         is the inverse Euler transform; the T = 0 count is the")
    log("         multiset count over atoms with at least 2 edges.")
    log("=" * 74)
    allc = count_all(mmax)
    atoms = connected_counts(allc, mmax)
    hyper = multiset_counts(atoms, mmax, 2)
    log("   m |    all | connected | survives T=0 | survives R=C=0")
    log("  ---+--------+-----------+--------------+---------------")
    for m in range(1, mmax + 1):
        cen = count_mindeg2(m)
        log(f"  {m:2d} | {allc[m]:6d} | {atoms[m]:9d} | {hyper[m]:12d}"
            f" | {cen:14d}")
    log("")
    log("  Growth ratio of the 'all' column:")
    log("    " + "  ".join(f"{allc[i] / allc[i - 1]:.2f}"
                           for i in range(2, mmax + 1)))
    log("  This is the price of the graded route: superexponential, but it is")
    log("  the DOUBLY-CENTRED column that a certificate must actually carry.")
    log("")
    return allc, atoms, hyper


# ============================== 5. parity, absorption, tail, confinement


def part5(exps):
    log("=" * 74)
    log("PART 5.  PARITY, ABSORPTION, TAIL, CONFINEMENT -- exact numbers.")
    log("=" * 74)
    log("  (5a) Parity is exact and unavoidable: L_m(-B) = (-1)^m L_m(B),")
    log("       because L_m is homogeneous of degree m (PART 1b).  So every ODD")
    log("       layer takes both signs on any ball and CANNOT be certified")
    log("       nonnegative.  It must be absorbed.")
    log("")
    log("  (5b) THE COEFFICIENT RATIOS, in closed form and checked exactly:")
    log("        s_{d+1}/s_d = (k-d)/(n-d)")
    log("        t_{d+1}/t_d = n (k-d) / (n-d)^2")
    bad = 0
    for (n, k) in ((5, 3), (5, 4), (6, 4), (6, 5), (7, 5), (9, 7), (12, 9)):
        for d in range(1, k):
            ls = s_coef(n, k, d + 1) / s_coef(n, k, d)
            rs = Fr(k - d, n - d)
            lt = t_coef(n, k, d + 1) / t_coef(n, k, d)
            rt = Fr(n * (k - d), (n - d) ** 2)
            if ls != rs or lt != rt:
                bad += 1
                log(f"    n={n} k={k} d={d} RATIO FAIL")
    log(f"        ratio-law mismatches: {bad}")
    log("")
    log("  (5c) THE DOUBLY-CENTRED CORE.  On R = C = 0 every e_m(R), e_m(C)")
    log("       vanishes, so F = sum_{m>=2} t_m sigma_m(B) with ALL t_m > 0.")
    log("       And A = J/n + B is then doubly stochastic, E_k(r) = E_k(c) = 1,")
    log("       so F = sigma_k(A)/C(n,k)^2 - k!/n^k.  Checked:")
    rng = random.Random(20260729)
    for (n, k) in ((5, 3), (5, 4), (6, 4), (6, 5), (7, 5)):
        b = rand_centred(n, rng)
        A = [[Fr(1, n) + b[i][j] for j in range(n)] for i in range(n)]
        lhs = sum(t_coef(n, k, m) * sigma_direct(b, m) for m in range(2, k + 1))
        rhs = sigma_direct(A, k) / Fr(comb(n, k)) ** 2 - Fr(factorial(k), n ** k)
        f = F_direct(b, k)
        ok = (lhs == rhs == f)
        if not ok:
            bad += 1
        log(f"    n={n} k={k}: sum t_m sigma_m = F = sigma_k/C^2 - k!/n^k"
            f"   match {ok}")
    log("")
    log("       At k = n, s_d = 1 and t_d = (n-d)!/n^(n-d), so this core is")
    log("       LITERALLY van der Waerden: per(A) >= n!/n^n.  Checked:")
    for n in (4, 5, 6):
        ok = all(t_coef(n, n, d) == Fr(factorial(n - d), n ** (n - d))
                 for d in range(2, n + 1))
        log(f"    n={n}: t_d(n,n) == (n-d)!/n^(n-d) for all d : {ok}")
        if not ok:
            bad += 1
    log("       -> the graded framework CANNOT close k = n without vdW.")
    log("       (Same wall as lih-wang/NOTES.md (M2) at t = 1.)")
    log("")
    log("  (5d) THE MIN-DEGREE FILTRATION on the core.  A degree-1 vertex")
    log("       contributes R_i or C_j, so on R = C = 0 only min-degree >= 2")
    log("       invariants survive.  Reduced cores:")
    for m in (2, 3, 4, 5):
        show_expansion(exps[m], f"sigma_{m}|R=C=0", restrict="centred")
    log("")
    log("  (5e) THE L_3 ABSORPTION.  Two pieces, two different inequalities.")
    log("")
    log("   (i) The p3R, p3C piece, absorbed into L_2's (p2R + p2C) term using")
    log("       CONFINEMENT.  |p3R| <= max_i|R_i| * p2R <= p2R^(3/2), so with")
    log("       rho^2 := (n-1) k!/n^(k-1)  (Lean confinement', which bounds")
    log("       p2R + p2C, NOT ||B||^2), the inequality to certify is")
    log("            (s_3/3) * rho  <=  (1/2) * (s_2 - t_2) / 2 .")
    log("       (the extra 1/2 keeps half the line-sum gap for the tail)")
    log("       Compared as SQUARES so the test stays exact over Q:")
    log("            (s_3/3)^2 * rho^2  <=  ((s_2 - t_2)/4)^2 .")
    log("   n   k | (s3/3)^2 rho^2 | ((s2-t2)/4)^2 | holds")
    seen_ks = set()
    for n in (5, 6, 8, 12, 20, 40):
        for k in sorted({2, 3, 4, 5, n // 2, n}):
            if not (2 <= k <= n) or (n, k) in seen_ks:
                continue
            seen_ks.add((n, k))
            s2, t2 = s_coef(n, k, 2), t_coef(n, k, 2)
            s3 = s_coef(n, k, 3)
            rho2 = Fr(n - 1) * Fr(factorial(k), n ** (k - 1))
            lhs = (s3 / 3) ** 2 * rho2          # compare squares, exact
            rhs = ((s2 - t2) / 4) ** 2
            log(f"  {n:3d} {k:2d} | {float(lhs):14.4e} | {float(rhs):13.4e}"
                f" | {lhs <= rhs}")
    log("")
    log("   (ii) The p3b piece, absorbed into L_2's Q term and L_4's p4b term")
    log("        by a SHIFTED SQUARE (Cauchy-Schwarz then AM-GM), which is a")
    log("        genuine SOS step and needs NO radius:")
    log("            (sum b^3)^2 <= (sum b^2)(sum b^4) = Q * p4b,")
    log("        so  (2/3) t_3 |p3b| <= (2/3) t_3 sqrt(Q * p4b)")
    log("                            <= (t_2/4) Q + (4 t_3^2/(9 t_2)) p4b.")
    log("        L_4's p4b coefficient is (3/2) t_4 (PART 3 law), so the")
    log("        inequality to certify, using only HALF of L_2's Q gap, is")
    log("            4 t_3^2 / (9 t_2) <= (3/2) t_4,  i.e.  8 t_3^2 <= 27 t_2 t_4,")
    log("        and by the ratio law t_3^2/(t_2 t_4) = (k-2)(n-3)^2/((k-3)(n-2)^2)")
    log("        so the condition is  8(k-2)(n-3)^2 <= 27(k-3)(n-2)^2.")
    log("   n   k | t3^2/(t2 t4) | (k-2)(n-3)^2/((k-3)(n-2)^2) | <= 27/8 ?")
    for n in (6, 7, 8, 10, 16, 30, 60):
        for k in (4, 5, 6, n // 2, n):
            if not (4 <= k <= n) or k <= 3:
                continue
            t2, t3, t4 = (t_coef(n, k, 2), t_coef(n, k, 3), t_coef(n, k, 4))
            if t4 == 0:
                continue
            r = t3 ** 2 / (t2 * t4)
            cf = Fr((k - 2) * (n - 3) ** 2, (k - 3) * (n - 2) ** 2)
            ok = (r == cf)
            if not ok:
                bad += 1
            log(f"  {n:3d} {k:2d} | {float(r):12.6f} | {float(cf):27.6f}"
                f" | {r <= Fr(27, 8)}  (law {ok})")
    log("")
    log("  (5f) THE TAIL.  On the doubly-centred core with A doubly stochastic,")
    log("       every entry of A is in [0,1] so |b_ij| <= 1 - 1/n < 1, hence")
    log("       p_m(|b|) <= Q for every m >= 2 and, by the min-degree law, every")
    log("       surviving invariant of layer m is bounded by Q^(ceil(m/2)) at")
    log("       worst and by Q at best.  The crude uniform tail bound is")
    log("           |sum_{m>=M+1} L_m| <= sum_{m=M+1}^{k} t_m N_c(m) Q^(ceil(m/2))")
    log("       with N_c(m) the min-degree>=2 ledger column (PART 4).  Against a")
    log("       layer-2 gap c(n,k) Q this needs Q^(ceil(m/2)-1) small, i.e. it")
    log("       is NOT dominated for Q of order 1 -- reported, not hidden.")
    log("       The honest smallest M is therefore M = k (no truncation) unless")
    log("       an entrywise or Q bound beyond confinement is supplied.")
    log("   n   k | t_2/2 (Q gap) |     t_3 |     t_4 |  t_k  | rho^2")
    for n in (5, 6, 8, 12, 20):
        for k in (2, 3, 4, n // 2, n):
            if not (2 <= k <= n):
                continue
            t2 = t_coef(n, k, 2)
            t3 = t_coef(n, k, 3)
            t4 = t_coef(n, k, 4)
            tk = t_coef(n, k, k)
            rho2 = Fr(n - 1) * Fr(factorial(k), n ** (k - 1))
            log(f"  {n:3d} {k:2d} | {float(t2 / 2):13.4e} | {float(t3):7.1e} |"
                f" {float(t4):7.1e} | {float(tk):5.1e} | {float(rho2):.4e}")
    log("")
    log(f"  PART 5 mismatches: {bad}")
    log("")
    return bad


# ================================================ 6. theta2 reconciliation


def part6():
    log("=" * 74)
    log("PART 6.  RECONCILIATION WITH THE k = 3 CERTIFICATE (theta2's role).")
    log("=" * 74)
    log("  SubDittertK3.lean line 646 records the sigma_0 Gram quadratic form as")
    log("      c0Total * S^2 + c0Line * (sum R^2 + sum C^2) + theta2 * sum b^2,")
    log("  which is EXACTLY the shape of L_2 on the hyperplane (S = T = 0 there):")
    log("      L_2 = (t_2/2) Q + ((s_2 - t_2)/2)(p2R + p2C).")
    log("  So theta2 is the k=3 certificate's stand-in for the Q coefficient and")
    log("  c0Line for the line-sum coefficient.  Orders of magnitude compared:")
    log("      theta2(n) = (n^4 + 40n^2 - 84n + 40) / (n^5 (n-1)^3 (n-2))")
    log("   n | t_2/2 at k=3           | theta2(n)              | ratio")
    for n in (4, 5, 6, 8, 12, 20, 40):
        t2 = t_coef(n, 3, 2)
        num = n ** 4 + 40 * n ** 2 - 84 * n + 40
        den = n ** 5 * (n - 1) ** 3 * (n - 2)
        th = Fr(num, den)
        log(f"  {n:2d} | {float(t2 / 2):.10e} | {float(th):.10e} |"
            f" {float((t2 / 2) / th):8.4f}")
    log("")
    log("  Both are Theta(n^-5).  t_2/2 = 18/(n^3 (n-1)^2) at k = 3 exactly.")
    log("  The certificate's Q eigenvalue and the layer-2 Q gap agree in order,")
    log("  which is the reconciliation the band-one proof predicts.")
    log("")


# ==================================================================== main


def main():
    rng = random.Random(20260729)
    bad = 0
    bad += part1(rng)
    b2, exps = part2(rng)
    bad += b2
    bad += part3(exps, rng)
    ledger(7)
    bad += part5(exps)
    part6()
    log("=" * 74)
    log(f"TOTAL MISMATCHES ACROSS ALL PARTS: {bad}")
    log("=" * 74)
    with open("results/graded_layers.log", "w") as fh:
        fh.write("\n".join(OUT) + "\n")
    return 0 if bad == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
