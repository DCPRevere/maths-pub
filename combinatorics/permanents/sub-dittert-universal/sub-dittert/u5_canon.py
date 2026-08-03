#!/usr/bin/env python3
"""A canonical form for U5 patterns that drops the |V|! factor exactly, plus
the two enumerators the e >= 10 sweeps need.

`u5_hunt.canon` minimises the row-major key over BOTH row and column
permutations by brute force, |R|! |C|!.  The |C|! half is unnecessary:

  For a FIXED row order the row-major key is the concatenation
  row_0, row_1, ..., row_{U-1}.  All of row 0 is compared before any of
  row 1, so the minimising column order sorts the columns ascending by
  c[0][v]; ties are then broken by c[1][v], and so on.  That is exactly
  sorting the columns ascending as VECTORS (c[0][v], ..., c[U-1][v]).

So  canon(c) = min over row permutations of (columns sorted as vectors),
which is |R|! * V log V instead of |R|! |C|!, and returns the IDENTICAL
representative -- not merely some other valid canonical form.  At e = 9
(U, V <= 4) that is 24x; at e = 12 (U, V <= 6) it is 720x.

Memoising on the raw matrix removes almost all of the remaining work, since
the pair loop revisits the same incidence matrix many times.

`classes_direct(e)` enumerates the iso classes straight off, without the
partition-pair loop.  It carries no Moebius mass, but the e_0 decision only
needs the class list, and the pair loop is Theta(A_e^2) with A_e the
associated Bell number -- 3.4e11 pairs at e = 12, which is out of reach in
any language, let alone this one.
"""
from functools import lru_cache
from math import factorial
from itertools import permutations

import u5_hunt as H

_MEMO = {}
_ROWPERMS = {}


def _rowperms(u):
    if u not in _ROWPERMS:
        _ROWPERMS[u] = list(permutations(range(u)))
    return _ROWPERMS[u]


def canon(c):
    """Identical output to u5_hunt.canon, without the |C|! factor."""
    key = tuple(tuple(r) for r in c)
    got = _MEMO.get(key)
    if got is not None:
        return got
    U = len(c)
    V = len(c[0])
    best = None
    for rp in _rowperms(U):
        rows = [c[rp[u]] for u in range(U)]
        # sort columns ascending as vectors (c[0][v], ..., c[U-1][v])
        cols = sorted(range(V), key=lambda v: tuple(rows[u][v] for u in range(U)))
        cand = tuple(tuple(rows[u][v] for v in cols) for u in range(U))
        if best is None or cand < best:
            best = cand
    _MEMO[key] = best
    return best


def connected(c):
    U, V = len(c), len(c[0])
    seen_r, seen_c = {0}, set()
    stack = [(0, 0)]
    while stack:
        side, x = stack.pop()
        if side == 0:
            for v in range(V):
                if c[x][v] and v not in seen_c:
                    seen_c.add(v)
                    stack.append((1, v))
        else:
            for u in range(U):
                if c[u][x] and u not in seen_r:
                    seen_r.add(u)
                    stack.append((0, u))
    return len(seen_r) == U and len(seen_c) == V


# --------------------------------------------------- the partition-pair loop

def patterns(e):
    """Same contract as u5_hunt.patterns: {canon key: (signed, l1 mass)}."""
    parts = [p for p in H.set_partitions(e) if all(len(b) >= 2 for b in p)]
    bidx, mob, nb = [], [], []
    for p in parts:
        idx = [0] * e
        for i, b in enumerate(p):
            for r in b:
                idx[r] = i
        bidx.append(idx)
        mob.append(H.mobius(p))
        nb.append(len(p))
    out = {}
    seen = {}
    npart = len(parts)
    for a in range(npart):
        ia, ma, ua = bidx[a], mob[a], nb[a]
        for b in range(npart):
            ib, vb = bidx[b], nb[b]
            c = [[0] * vb for _ in range(ua)]
            for r in range(e):
                c[ia[r]][ib[r]] += 1
            raw = tuple(tuple(r) for r in c)
            got = seen.get(raw)
            if got is None:
                got = canon(c) if connected(c) else False
                seen[raw] = got
            if got is False:
                continue
            w = ma * mob[b]
            cur = out.get(got)
            if cur is None:
                out[got] = (w, abs(w))
            else:
                out[got] = (cur[0] + w, cur[1] + abs(w))
    return out


# ------------------------------------------------- direct class enumeration

def classes_direct(e):
    """Every connected pattern class with e edges and min degree >= 2, as
    canon keys.  No Moebius mass."""
    out = set()
    half = e // 2
    for U in range(1, half + 1):
        for V in range(1, half + 1):
            if U * 1 > e or V * 1 > e:
                continue
            # columns enumerated in non-decreasing vector order, each of
            # weight >= 2, total weight e
            cols = []

            def col_vecs(s):
                """all U-vectors of non-negative ints summing to s"""
                if U == 1:
                    yield (s,)
                    return
                def rec(i, left, acc):
                    if i == U - 1:
                        yield tuple(acc + [left])
                        return
                    for t in range(left + 1):
                        yield from rec(i + 1, left - t, acc + [t])
                yield from rec(0, s, [])

            allcols = []
            for s in range(2, e - 2 * (V - 1) + 1):
                allcols += list(col_vecs(s))
            # sort by (weight, tuple) so the `break` below is valid: choosing
            # indices non-decreasing then visits every multiset exactly once
            allcols.sort(key=lambda t: (sum(t), t))
            ncol = len(allcols)

            def rec(start, left, chosen):
                k = len(chosen)
                if k == V:
                    if left:
                        return
                    c = [[chosen[v][u] for v in range(V)] for u in range(U)]
                    if any(sum(row) < 2 for row in c):
                        return
                    if not connected(c):
                        return
                    out.add(canon(c))
                    return
                rem = V - k
                for i in range(start, ncol):
                    w = sum(allcols[i])
                    if w * rem > left:
                        break
                    if left - w < 2 * (rem - 1):
                        continue
                    rec(i, left - w, chosen + [allcols[i]])

            rec(0, e, [])
    return out
