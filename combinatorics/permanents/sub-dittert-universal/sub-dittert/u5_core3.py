#!/usr/bin/env python3
"""Minimum-degree-3 cores of U5 patterns: census, and the two new terminal
lemmas (L-PRISM, L-CS2).

A *core* is what the local moves M1 (series), M2 (parallel), M3 (loop) of
U5.md sec 4.2 leave behind: a SIMPLE graph, not necessarily bipartite
(contraction breaks bipartiteness), with minimum degree >= 3, whose edges
carry matrices X in D_n = {A - J/n : A doubly stochastic}.

A core H is first realised by a pattern with

    e_min(H) = e(H) + (e(H) - maxcut(H)) = 2 e(H) - maxcut(H)

edges: a pattern is BIPARTITE, so every monochromatic edge of a best
2-colouring of H must be subdivided once (one subdivision suffices, and it is
a legal pattern vertex because its degree is 2).

Nothing here decides anything by floating point.
"""
from fractions import Fraction
from itertools import combinations, permutations, product


# ------------------------------------------------------------------ graphs

def canon(v, edges):
    """Canonical form of a graph on vertices 0..v-1 (brute force, v <= 8)."""
    best = None
    for p in permutations(range(v)):
        cur = tuple(sorted((min(p[a], p[b]), max(p[a], p[b])) for (a, b) in edges))
        if best is None or cur < best:
            best = cur
    return (v, best)


def degrees(v, edges):
    d = [0] * v
    for (a, b) in edges:
        d[a] += 1
        d[b] += 1
    return d


def connected(v, edges):
    adj = {i: set() for i in range(v)}
    for (a, b) in edges:
        adj[a].add(b)
        adj[b].add(a)
    seen, stack = {0}, [0]
    while stack:
        u = stack.pop()
        for w in adj[u]:
            if w not in seen:
                seen.add(w)
                stack.append(w)
    return len(seen) == v


def maxcut(v, edges):
    best = 0
    for mask in range(1 << v):
        c = sum(1 for (a, b) in edges
                if ((mask >> a) & 1) != ((mask >> b) & 1))
        if c > best:
            best = c
    return best


def enumerate_cores(vmax=8, emax=14):
    """All connected simple graphs with min degree >= 3, up to isomorphism,
    on <= vmax vertices with <= emax edges, keyed by canonical form."""
    out = {}
    for v in range(4, vmax + 1):
        labelled = set()
        slots = list(combinations(range(v), 2))
        ns = len(slots)
        lo = -(-3 * v // 2)
        # last slot index touching each vertex: after it, its degree is frozen
        last = [max(i for i, (a, b) in enumerate(slots) if x in (a, b))
                for x in range(v)]
        for e in range(lo, emax + 1):
            if e > ns:
                break
            # backtracking over edge slots with a degree-feasibility prune
            deg = [0] * v
            chosen = []

            def rec(i, left):
                if left == 0:
                    if all(d >= 3 for d in deg):
                        es = tuple(sorted(chosen))
                        if connected(v, es):
                            labelled.add(es)
                    return
                if ns - i < left:
                    return
                # prune: a vertex whose slots are all behind us is frozen
                for x in range(v):
                    if last[x] < i and deg[x] < 3:
                        return
                # prune: every vertex must still be able to reach degree 3
                need = sum(max(0, 3 - deg[x]) for x in range(v))
                if need > 2 * left:
                    return
                a, b = slots[i]
                deg[a] += 1
                deg[b] += 1
                chosen.append((a, b))
                rec(i + 1, left - 1)
                chosen.pop()
                deg[a] -= 1
                deg[b] -= 1
                rec(i + 1, left)

            rec(0, e)
        # orbit dedup: cheaper than canonicalising every labelled graph
        perms = list(permutations(range(v)))
        while labelled:
            es = min(labelled)
            out[(v, es)] = (v, es)
            for p in perms:
                labelled.discard(
                    tuple(sorted((min(p[a], p[b]), max(p[a], p[b]))
                                 for (a, b) in es)))
    return out


# ------------------------------------------------- the two structural tests

def prismatic_split(v, edges):
    """L-PRISM applies: V = V_A u V_B, |V_A| = |V_B|, the crossing edges are
    EXACTLY a perfect matching between them, and both halves are connected
    with at least one edge.  Returns (V_A, matching) or None."""
    if v % 2:
        return None
    E = set(tuple(sorted(e)) for e in edges)
    for mask in range(1, 1 << (v - 1)):
        A = [x for x in range(v) if (mask >> x) & 1]
        B = [x for x in range(v) if not (mask >> x) & 1]
        if len(A) != len(B) or not A:
            continue
        cross = [(a, b) for (a, b) in E
                 if ((a in A) != (b in A))]
        if len(cross) != len(A):
            continue
        seen = set()
        ok = True
        for (a, b) in cross:
            if a in seen or b in seen:
                ok = False
                break
            seen.add(a)
            seen.add(b)
        if not ok or len(seen) != v:
            continue
        EA = [(a, b) for (a, b) in E if a in A and b in A]
        EB = [(a, b) for (a, b) in E if a in B and b in B]
        if not EA or not EB:
            continue
        ia = {x: i for i, x in enumerate(A)}
        ib = {x: i for i, x in enumerate(B)}
        if not connected(len(A), [(ia[a], ia[b]) for (a, b) in EA]):
            continue
        if not connected(len(B), [(ib[a], ib[b]) for (a, b) in EB]):
            continue
        return (A, B, EA, EB, cross)
    return None


def bipartition(v, edges):
    col = [None] * v
    col[0] = 0
    stack = [0]
    adj = {i: set() for i in range(v)}
    for (a, b) in edges:
        adj[a].add(b)
        adj[b].add(a)
    while stack:
        u = stack.pop()
        for w in adj[u]:
            if col[w] is None:
                col[w] = 1 - col[u]
                stack.append(w)
            elif col[w] == col[u]:
                return None
    return col


def covering_groups(R, nbrs, J):
    """Does the column set J contain j, j' (possibly equal) with
    N(j) u N(j') = R and N(j) n N(j') != {} ?"""
    for j in J:
        for k in J:
            S, T = nbrs[j], nbrs[k]
            if S | T == R and S & T:
                return (j, k)
    return None


def wheel_split(v, edges):
    """L-WHEEL applies: some vertex h has G - h a single spanning cycle of
    V - h, and h is joined to every vertex of it.  Then

        S = sum_a tr(D_1 C_1 ... D_m C_m),  D_i = diag(row a of the spoke),

    and splitting the cyclic word into two arcs of lengths p, q = m - p,

        sum_a ||A_a||_F^2 <= beta^{2p-1} Q ,     |S| <= beta^{m-1} Q .

    Returns (h, cycle) or None."""
    adj = {i: set() for i in range(v)}
    for (a, b) in edges:
        adj[a].add(b)
        adj[b].add(a)
    for h in range(v):
        rest = [x for x in range(v) if x != h]
        if any(x not in adj[h] for x in rest):
            continue
        if len(rest) < 3:
            continue
        sub = [(a, b) for (a, b) in edges if a != h and b != h]
        if len(sub) != len(rest):
            continue
        if any(len(adj[x] - {h}) != 2 for x in rest):
            continue
        idx = {x: i for i, x in enumerate(rest)}
        if not connected(len(rest), [(idx[a], idx[b]) for (a, b) in sub]):
            continue
        # walk the cycle
        cyc = [rest[0]]
        prev = None
        while len(cyc) < len(rest):
            nxt = [w for w in adj[cyc[-1]] - {h} if w != prev]
            prev = cyc[-1]
            cyc.append(nxt[0])
        return (h, cyc)
    return None


def cs2_general(v, edges):
    """L-CS2, non-bipartite form.  Pick an INDEPENDENT set C; R = V - C.
    Edges inside R are paid pointwise at beta each (|X| <= beta).  Need
    C = J_1 u J_2 with each J_i carrying j, k (possibly equal) with
    N(j) u N(k) = R and N(j) n N(k) != {}."""
    adj = {i: set() for i in range(v)}
    for (a, b) in edges:
        adj[a].add(b)
        adj[b].add(a)
    best = None
    for mask in range(1, 1 << v):
        C = [x for x in range(v) if (mask >> x) & 1]
        if any(b in adj[a] for a in C for b in C if a != b):
            continue
        R = set(range(v)) - set(C)
        if not R:
            continue
        if any(len(adj[j]) < 2 for j in C):
            continue
        pairs = [(j, k) for j in C for k in C
                 if adj[j] | adj[k] == R and adj[j] & adj[k]]
        for (j1, k1) in pairs:
            for (j2, k2) in pairs:
                if not ({j1, k1} & {j2, k2}):
                    nER = sum(1 for (a, b) in edges if a in R and b in R)
                    cand = (nER, tuple(C), (j1, k1), (j2, k2))
                    if best is None or cand < best:
                        best = cand
    return best


def cs2_split(v, edges):
    """L-CS2 applies on one side: the core is bipartite with parts R, C and
    C = J_1 u J_2 with each J_i carrying a covering pair."""
    col = bipartition(v, edges)
    if col is None:
        return None
    nbrs = {i: set() for i in range(v)}
    for (a, b) in edges:
        nbrs[a].add(b)
        nbrs[b].add(a)
    for side in (0, 1):
        C = [x for x in range(v) if col[x] == side]
        R = frozenset(x for x in range(v) if col[x] != side)
        # search for two DISJOINT covering groups inside C
        pairs = [(j, k) for j in C for k in C
                 if nbrs[j] | nbrs[k] == set(R) and nbrs[j] & nbrs[k]]
        for (j1, k1) in pairs:
            for (j2, k2) in pairs:
                if len({j1, k1} & {j2, k2}) == 0:
                    return (side, (j1, k1), (j2, k2))
    return None


# ---------------------------------------------------------------- matrices

def bmat(A, n):
    """B = A - J/n for A a list of rows of Fractions."""
    return [[A[i][j] - Fraction(1, n) for j in range(n)] for i in range(n)]


def matmul(X, Y, n):
    return [[sum(X[i][k] * Y[k][j] for k in range(n)) for j in range(n)]
            for i in range(n)]


def transpose(X, n):
    return [[X[j][i] for j in range(n)] for i in range(n)]


def frob2(X, n):
    return sum(X[i][j] * X[i][j] for i in range(n) for j in range(n))


# --------------------------------------------------- exact invariant S_G(X)

def invariant(v, edges, mats, n):
    """S_G = sum over x: V -> [n] of prod_f X_f(x_u, x_v), by bucket
    elimination.  mats[i] is the matrix on edges[i], oriented (u, v)."""
    factors = [(tuple(e), {}) for e in edges]
    facs = []
    for (a, b), X in zip(edges, mats):
        tbl = {}
        for i in range(n):
            for j in range(n):
                if X[i][j]:
                    tbl[(i, j)] = X[i][j]
        facs.append(((a, b), tbl))
    order = sorted(range(v), key=lambda u: sum(1 for (vs, _) in facs if u in vs))
    for u in order:
        hit = [f for f in facs if u in f[0]]
        rest = [f for f in facs if u not in f[0]]
        if not hit:
            continue
        vs = []
        for (sc, _) in hit:
            for x in sc:
                if x != u and x not in vs:
                    vs.append(x)
        newtbl = {}
        for assign in product(range(n), repeat=len(vs)):
            amap = dict(zip(vs, assign))
            tot = 0
            for xu in range(n):
                amap[u] = xu
                p = 1
                for (sc, tb) in hit:
                    key = tuple(amap[y] for y in sc)
                    val = tb.get(key)
                    if val is None:
                        p = 0
                        break
                    p *= val
                tot += p
            if tot:
                newtbl[assign] = tot
        facs = rest + [(tuple(vs), newtbl)]
    tot = 0
    for (sc, tb) in facs:
        assert sc == ()
        tot = tb.get((), 0) if not tot else tot * tb.get((), 0)
    if not facs:
        return n ** v
    out = 1
    for (sc, tb) in facs:
        out *= tb.get((), 0)
    return out
