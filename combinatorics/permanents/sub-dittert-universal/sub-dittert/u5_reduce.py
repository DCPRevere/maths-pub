#!/usr/bin/env python3
"""The U5 reduction calculus, as a certificate search.

State.  A multigraph on the live vertices (contraction breaks bipartiteness,
so the calculus runs on general multigraphs).  Every edge carries a matrix X
and every vertex a weight omega, each with a tag recording which of the
lemmas of U5.md sec 2 apply to it:

  edge tags
    D   X is a product of B's and B^T's, hence X = A_X - J/n with A_X doubly
        stochastic: ||X||_op <= 1, max|X| <= beta, row/col l2 <= sqrt(beta),
        ||X||_F <= sqrt(Q), each row/column splits into positive and negative
        parts of l1 mass <= beta each, and X has zero row and column sums
    H   X is a Hadamard product of >= 2 such matrices: additionally
        sum_{ab}|X_ab| <= Q  and  max_a sum_b |X_ab| <= beta
    P   X >= 0 entrywise

  vertex tags
    w   carries a weight with ||omega||_inf <= 1        (absent = omega == 1)
    hv  ||omega||_1 <= Q
    pos omega >= 0                                       (the trivial 1 is pos)

Moves, each a lemma:
  M1 series   deg-2 vertex, distinct neighbours          -> edge X D_omega Y
  M2 parallel two edges u--v                             -> X o Y   (gains H,
                                                            and P if both same)
  M3 loop     loop at v                                  -> heavy weight at v
  M4 leaf     deg-1 vertex, weight pos (or edge H)       -> weight at neighbour
  M9 vanish   deg-1 vertex, NO weight, edge tagged D     -> S = 0
Terminals:
  M5 point    one vertex, no edges, a heavy weight       -> |S| <= Q
  M6 bridge   two vertices, one edge, both heavy         -> |S| <= Q
  M7 single   two vertices, one edge tagged H            -> |S| <= Q
"""
from functools import lru_cache

DISABLE = set()          # mutation controls: move names switched off


# ---------------------------------------------------------------- state repr
# edges: tuple of (u, v, tags) with u <= v, tags a frozenset subset of {'D','H','P'}
# verts: dict v -> frozenset subset of {'w','hv','pos'}

def norm(edges, verts):
    live = sorted({u for (u, v, t) in edges} | {v for (u, v, t) in edges}
                  | {k for k in verts})
    idx = {v: i for i, v in enumerate(live)}
    E = tuple(sorted((min(idx[u], idx[v]), max(idx[u], idx[v]), t)
                     for (u, v, t) in edges))
    V = tuple(sorted((idx[v], verts[v]) for v in live))
    return E, V


def degrees(E, V):
    d = {v: 0 for (v, _) in V}
    for (u, v, t) in E:
        d[u] = d.get(u, 0) + 1
        d[v] = d.get(v, 0) + 1
        if u == v:
            d[u] += 1
    return d


def vtag(V, v):
    for (a, t) in V:
        if a == v:
            return t
    return frozenset()


def setv(V, v, t):
    return tuple(sorted([(a, (t if a == v else s)) for (a, s) in V]))


NAMED = {
    # named terminal lemmas, proved by hand in U5.md sec 5, for patterns the
    # local moves cannot reach.  Each is keyed by its sorted edge multiset on
    # a canonical vertex labelling; matched up to isomorphism by iso_match.
    "L-K4": ([(0, 3), (0, 4), (0, 5), (1, 3), (1, 4), (1, 5), (2, 3), (2, 4)],
             "L-K4 (U5.md sec 5.1): |S| <= beta^2 Q by Cauchy-Schwarz on "
             "(BB^T, V) with ||V||_F <= beta^2 sqrt(Q)"),
    "L-K33": ([(0, 3), (0, 4), (0, 5), (1, 3), (1, 4), (1, 5),
               (2, 3), (2, 4), (2, 5)],
              "L-K33 (U5.md sec 5.2): |S| <= max|T| * sum H^3 <= beta^2 Q"),
}


def iso_match(E, V, target):
    """Is the plain (no weights, all edges D) multigraph E isomorphic to the
    target edge list?"""
    from itertools import permutations
    if any(t != frozenset({'pos'}) and t != frozenset() for (_, t) in V):
        return False
    if any('D' not in t for (_, _, t) in E):
        return False
    if len(E) != len(target):
        return False
    nv = len({x for (a, b, _) in E for x in (a, b)})
    tv = len({x for (a, b) in target for x in (a, b)})
    if nv != tv or nv > 8:
        return False
    lab = sorted({x for (a, b, _) in E for x in (a, b)})
    base = sorted((min(a, b), max(a, b)) for (a, b, _) in E)
    tgt = sorted((min(a, b), max(a, b)) for (a, b) in target)
    for p in permutations(range(nv)):
        mp = {lab[i]: p[i] for i in range(nv)}
        cur = sorted((min(mp[a], mp[b]), max(mp[a], mp[b])) for (a, b, _) in E)
        if cur == tgt:
            return True
    return False


# ------------------------------------------ core-level structural terminals
#
# U5-CORES.md secs 3-5.  These are keyed on the SHAPE OF THE CORE, not on a
# fixed pattern edge list, which is the bug they exist to fix: `L-K4` above is
# keyed on one 8-edge pattern and `iso_match` demands every edge still carry
# the tag `D`, so the five e = 9 classes whose reduced core IS K_4 were never
# matched -- three of them lose `D` when M1 contracts through an M2-merged
# (Hadamard) edge, and two reach K_4 at 4 vertices, which is not the
# registered 6-vertex target.  `L-WHEEL` at m = 3 is `L-K4` stated on the core
# and closes all five.
#
# No tag is required.  Every edge the calculus can produce satisfies
#     ||X||_op <= 1,  max|X| <= beta,  row/col l2 <= beta,  ||X||_F^2 <= Q
# ("B", bounded) -- true of D, of H, and closed under both M1 (X D_omega Y,
# with ||D_omega||_op <= 1) and M2 (Schur: ||X o Y||_op <= r(X)c(Y) <= beta).
# Those four facts are all the four lemmas consume; in particular NONE of them
# consumes the entry bound (U5-CORES.md sec 8(iii)).  Vertex weights are NOT
# allowed, so the terminals demand a weightless state.

CORE_LEMMAS = ("L-WHEEL", "L-PRISM", "L-CS2", "L-ROOT2")

_CP6 = (6, ((0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 5),
            (2, 4), (3, 5), (4, 5)))


def core_terminal(E, V):
    """Does a core-level lemma close this state?  Returns a description."""
    import u5_core3 as CO
    # Vertex weights are FINE.  Every weight the calculus can carry has
    # ||omega||_inf <= 1 (U5.md sec 4.1, and M4/T4 preserves it), and in each
    # of the four lemmas a weight enters only as a diagonal factor
    # diag(omega) of operator norm <= 1: at a wheel hub it multiplies the
    # trace term by omega(a) pointwise; at a cycle vertex it multiplies D_i;
    # in L-PRISM it multiplies T_A or T_B pointwise, and |T^omega| <= |T|;
    # in L-CS2 it multiplies inside g_j, and every step there is a
    # Cauchy-Schwarz or an l^inf bound that survives it.  So no bound moves.
    verts = sorted({x for (a, b, _) in E for x in (a, b)})
    idx = {x: i for i, x in enumerate(verts)}
    es = []
    for (a, b, _) in E:
        if a == b:
            return None                   # loops: out of scope
        es.append((min(idx[a], idx[b]), max(idx[a], idx[b])))
    if len(set(es)) != len(es):
        return None                       # parallel edges: M2 fires first
    nv = len(verts)
    if nv < 4 or min(CO.degrees(nv, es)) < 3:
        return None
    if 'L-WHEEL' not in DISABLE:
        w = CO.wheel_split(nv, es)
        if w:
            m = len(w[1])
            return (f"L-WHEEL (U5-CORES.md sec 3): hub {w[0]}, {m}-cycle; "
                    f"|S| <= beta^{m-1} Q")
    if 'L-PRISM' not in DISABLE:
        p = CO.prismatic_split(nv, es)
        if p:
            VA, VB, EA, EB, cross = p
            cA = 2 * len(EA) - len(VA)
            cB = 2 * len(EB) - len(VB)
            return (f"L-PRISM (U5-CORES.md sec 4): matching sum, "
                    f"|S| <= beta^{(cA + cB) / 2} Q")
    if 'L-CS2' not in DISABLE:
        s = CO.cs2_general(nv, es)
        if s:
            return (f"L-CS2 (U5-CORES.md sec 5): independent set {s[1]}, "
                    f"covering pairs {s[2]}, {s[3]}")
    if 'L-ROOT2' not in DISABLE:
        if CO.canon(nv, tuple(sorted(es))) == CO.canon(*_CP6):
            return ("L-ROOT2 (U5-CORES.md sec 5): root + 2-cut, "
                    "|S| <= beta^4 Q")
    return None


def certify(E, V, depth=0, seen=None, path=()):
    """Depth-first search for a certificate.  Returns the move list or None."""
    if seen is None:
        seen = set()
    key = (E, V)
    if key in seen or depth > 24:
        return None
    seen.add(key)
    d = degrees(E, V)
    live = [v for (v, _) in V]

    # ---------------- named terminal lemmas (U5.md sec 5)
    for nm, (tgt, desc) in NAMED.items():
        if nm in DISABLE:
            continue
        if iso_match(E, V, tgt):
            return path + (desc,)
    ct = core_terminal(E, V)
    if ct is not None:
        return path + (ct,)

    # ---------------- terminals
    if not E and len(live) == 1:
        if 'hv' in vtag(V, live[0]):
            return path + ("M5 point: heavy weight, |S| <= Q",)
        return None
    if len(E) == 1 and E[0][0] != E[0][1]:
        u, v, t = E[0]
        if 'hv' in vtag(V, u) and 'hv' in vtag(V, v):
            return path + ("M6 bridge: two heavy weights (l2-l2), |S| <= Q",)
        if 'H' in t:
            return path + ("M7 single Hadamard edge: |S| <= sum|X| <= Q",)

    moves = []

    # ---------------- M9 vanish: a leaf with no weight on a D edge
    for v in (live if 'M9' not in DISABLE else []):
        if d[v] == 1 and 'w' not in vtag(V, v):
            for (a, b, t) in E:
                if (a == v or b == v) and 'D' in t:
                    return path + (f"M9 vanish at {v}: zero column sum, S = 0",)

    # ---------------- M3 loop
    for i, (a, b, t) in (enumerate(E) if 'M3' not in DISABLE else []):
        if a == b:
            E2 = E[:i] + E[i + 1:]
            tg = set(vtag(V, a)) | {'w', 'hv'}
            tg.add('pos')          # palindromic contraction: diag(M D M^T) >= 0
            moves.append((f"M3 loop at {a}", E2, setv(V, a, frozenset(tg))))

    # ---------------- M2 parallel
    for i in (range(len(E)) if 'M2' not in DISABLE else []):
        for j in range(i + 1, len(E)):
            a1, b1, t1 = E[i]
            a2, b2, t2 = E[j]
            if (a1, b1) == (a2, b2) and a1 != b1:
                nt = {'H'}
                if 'P' in t1 and 'P' in t2:
                    nt.add('P')
                if t1 == t2 and 'D' in t1:
                    nt.add('P')     # X o X >= 0
                E2 = tuple(sorted([E[k] for k in range(len(E)) if k not in (i, j)]
                                  + [(a1, b1, frozenset(nt))]))
                moves.append((f"M2 parallel {a1}-{b1}", E2, V))

    # ---------------- M1 series
    for v in (live if 'M1' not in DISABLE else []):
        if d[v] == 2:
            inc = [(k, E[k]) for k in range(len(E)) if E[k][0] == v or E[k][1] == v]
            if len(inc) == 2:
                (k1, (a1, b1, t1)), (k2, (a2, b2, t2)) = inc
                u = b1 if a1 == v else a1
                x = b2 if a2 == v else a2
                if u != x:
                    nt = set()
                    if 'D' in t1 and 'D' in t2 and 'w' not in vtag(V, v):
                        nt.add('D')
                    if 'P' in t1 and 'P' in t2 and 'pos' in vtag(V, v):
                        nt.add('P')
                    E2 = tuple(sorted([E[k] for k in range(len(E)) if k not in (k1, k2)]
                                      + [(min(u, x), max(u, x), frozenset(nt))]))
                    V2 = tuple((a, t) for (a, t) in V if a != v)
                    moves.append((f"M1 series at {v}", E2, V2))

    # ---------------- M4 leaf
    for v in (live if 'M4' not in DISABLE else []):
        if d[v] == 1:
            k = [i for i in range(len(E)) if E[i][0] == v or E[i][1] == v][0]
            a, b, t = E[k]
            u = b if a == v else a
            tv = vtag(V, v)
            # l-infinity bound survives if (weight >= 0 and edge in D) or edge in H
            if not (('pos' in tv and 'D' in t) or ('H' in t)):
                continue
            new = set(vtag(V, u)) | {'w'}
            if 'H' in t:                       # ||X^T omega||_1 <= sum|X| <= Q
                new.add('hv')
            elif 'hv' in tv:
                pass                           # heaviness not propagated through D
            if 'P' in t and 'pos' in tv:
                new.add('pos')
            elif 'pos' in vtag(V, u) and 'pos' not in new:
                new.discard('pos')
            E2 = tuple(E[:k] + E[k + 1:])
            V2 = tuple((a2, t2) for (a2, t2) in V if a2 != v)
            V2 = setv(V2 + ((u, vtag(V, u)),) if u not in [x for (x, _) in V2]
                      else V2, u, frozenset(new))
            moves.append((f"M4 leaf {v} -> {u}", E2, V2))

    for name, E2, V2 in moves:
        E2, V2 = norm(E2, dict(V2))
        r = certify(E2, V2, depth + 1, seen, path + (name,))
        if r:
            return r
    return None


def pattern_state(c):
    """Incidence matrix -> initial state: every edge tagged D, no weights."""
    U, V = len(c), len(c[0])
    E = []
    for u in range(U):
        for v in range(V):
            E += [(u, U + v, frozenset({'D'}))] * c[u][v]
    verts = {i: frozenset({'pos'}) for i in range(U + V)}   # trivial weight 1 >= 0
    return norm(tuple(sorted(E)), verts)


if __name__ == "__main__":
    import sys
    import u5_hunt as H
    emax = int(sys.argv[1]) if len(sys.argv) > 1 else 8
    for e in range(2, emax + 1):
        pats = H.patterns(e)
        bad, tot, badmass = [], 0, 0
        for key, (sgn, mass) in pats.items():
            E, V = pattern_state([list(r) for r in key])
            tot += mass
            if certify(E, V) is None:
                bad.append((key, mass))
                badmass += mass
        print(f"e={e}: {len(pats)} classes, {len(bad)} NOT certified; "
              f"mass {badmass} of {tot} ({100.0*badmass/tot:.4f}%)", flush=True)
        for key, mass in bad[:8]:
            print(f"    NOT CERTIFIED {key} mass={mass}")


# ------------------------------------------------- direct pattern enumeration

def enum_patterns(e):
    """All connected bipartite multigraphs with e edges and every degree >= 2,
    up to row/col permutation, as incidence matrices."""
    import itertools
    out = {}
    for U in range(1, e // 2 + 1):
        for V in range(1, e // 2 + 1):
            # row sums r_u >= 2 summing to e; col sums >= 2 summing to e
            def comps(total, k):
                if k == 1:
                    if total >= 2:
                        yield (total,)
                    return
                for first in range(2, total - 2 * (k - 1) + 1):
                    for rest in comps(total - first, k - 1):
                        yield (first,) + rest
            for rs in comps(e, U):
                for cs in comps(e, V):
                    for M in matrices_with_margins(rs, cs):
                        c = [list(r) for r in M]
                        if not u5_hunt.is_connected(c):
                            continue
                        out.setdefault(u5_hunt.canon(c), c)
    return out


def matrices_with_margins(rs, cs):
    """All non-negative integer matrices with the given row and column sums."""
    U, V = len(rs), len(cs)

    def rec(i, remaining_cs, acc):
        if i == U:
            if all(x == 0 for x in remaining_cs):
                yield tuple(acc)
            return
        for row in rows_with_sum(rs[i], remaining_cs):
            yield from rec(i + 1, tuple(remaining_cs[j] - row[j] for j in range(V)),
                           acc + [row])

    def rows_with_sum(s, caps):
        V = len(caps)

        def r2(j, left, cur):
            if j == V:
                if left == 0:
                    yield tuple(cur)
                return
            for x in range(min(left, caps[j]) + 1):
                yield from r2(j + 1, left - x, cur + [x])
        return r2(0, s, [])

    return rec(0, tuple(cs), [])


import u5_hunt                                                   # noqa: E402
