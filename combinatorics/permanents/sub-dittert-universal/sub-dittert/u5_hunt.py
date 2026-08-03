#!/usr/bin/env python3
"""U5 hunt (EXPLORATORY, floats -- [I], never a decision).

Enumerates every connected bipartite multigraph pattern with all degrees >= 2
that occurs in the connected Moebius expansion of K_e, and hunts for a
doubly stochastic A with

    |S_G(A - J/n)|  >  Q = ||A - J/n||_F^2 .

That is the U5 claim with constant 1.  Also reports the permutation-matrix
value (the known killer point) in closed form.
"""
import sys
import numpy as np
from itertools import combinations
from math import factorial
from fractions import Fraction as Fr

# ------------------------------------------------------------ partitions

def set_partitions(m):
    if m == 0:
        return [()]
    out = []
    for sm in set_partitions(m - 1):
        for i in range(len(sm)):
            out.append(sm[:i] + (sm[i] + (m - 1,),) + sm[i + 1:])
        out.append(sm + ((m - 1,),))
    return out


def mobius(pi):
    v = 1
    for b in pi:
        v *= (-1) ** (len(b) - 1) * factorial(len(b) - 1)
    return v


def block_of(pi, r):
    for i, b in enumerate(pi):
        if r in b:
            return i
    raise KeyError(r)


def incidence(pi, rho, m):
    c = [[0] * len(rho) for _ in range(len(pi))]
    for r in range(m):
        c[block_of(pi, r)][block_of(rho, r)] += 1
    return c


def is_connected(c):
    U, V = len(c), len(c[0])
    par = list(range(U + V))

    def find(a):
        while par[a] != a:
            par[a] = par[par[a]]
            a = par[a]
        return a

    for u in range(U):
        for v in range(V):
            if c[u][v]:
                a, b = find(u), find(U + v)
                if a != b:
                    par[a] = b
    return len({find(i) for i in range(U + V)}) == 1


def canon(c):
    """Canonical form of the incidence matrix under row/col permutation."""
    import itertools
    U, V = len(c), len(c[0])
    best = None
    for rp in itertools.permutations(range(U)):
        rows = [tuple(c[rp[u]]) for u in range(U)]
        for cp in itertools.permutations(range(V)):
            key = tuple(tuple(rows[u][cp[v]] for v in range(V)) for u in range(U))
            if best is None or key < best:
                best = key
    return best


def patterns(e):
    """All connected patterns with e edges, min degree >= 2, with the total
    |mu(pi)mu(rho)| mass attached to each iso class."""
    parts = [p for p in set_partitions(e) if all(len(b) >= 2 for b in p)]
    out = {}
    for pi in parts:
        mp = mobius(pi)
        for rho in parts:
            c = incidence(pi, rho, e)
            if not is_connected(c):
                continue
            key = canon(c)
            w = mp * mobius(rho)
            a, b = out.get(key, (0, 0))
            out[key] = (a + w, b + abs(w))
    return out


# ------------------------------------------------------------ evaluation

def S_float(c, B):
    """S_G(B) for the incidence matrix c, dense float.

    S = sum_{i_1..i_U} prod_v T_v(i),  T_v(i) = sum_j prod_u B[i_u,j]^c[u][v].
    """
    U, V = len(c), len(c[0])
    n = B.shape[0]
    tot = np.ones((1,) * U)
    for v in range(V):
        T = np.ones((1,) * U + (n,))          # axes: i_1..i_U, j
        for u in range(U):
            if c[u][v]:
                leg = np.power(B, c[u][v])    # (i_u, j)
                shape = [1] * (U + 1)
                shape[u] = n
                shape[U] = n
                T = T * leg.reshape(shape)
        tot = tot * T.sum(axis=U)
    return float(tot.sum())


def S_perm_closed(c, n):
    """S_G(P - J/n) exactly, as a Fraction, via
       S = sum_{F subset E} (-1)^{|F|} n^{c(E-F) - |F|}."""
    U, V = len(c), len(c[0])
    edges = []
    for u in range(U):
        for v in range(V):
            edges += [(u, U + v)] * c[u][v]
    e = len(edges)
    tot = Fr(0)
    for mask in range(1 << e):
        keep = [edges[i] for i in range(e) if not (mask >> i & 1)]
        f = bin(mask).count("1")
        par = list(range(U + V))

        def find(a):
            while par[a] != a:
                par[a] = par[par[a]]
                a = par[a]
            return a
        for (a, b) in keep:
            x, y = find(a), find(b)
            if x != y:
                par[x] = y
        comp = len({find(i) for i in range(U + V)})
        tot += Fr((-1) ** f) * Fr(n) ** (comp - f)
    return tot


# ------------------------------------------------------------ the hunt

def sinkhorn(X, iters=200):
    A = np.exp(X)
    for _ in range(iters):
        A /= A.sum(axis=1, keepdims=True)
        A /= A.sum(axis=0, keepdims=True)
    A /= A.sum(axis=1, keepdims=True)
    return A


def hunt(c, n, restarts=60, steps=400, seed=0):
    rng = np.random.default_rng(seed)
    J = np.ones((n, n)) / n
    best = (-1e18, None)
    for r in range(restarts):
        X = rng.normal(size=(n, n)) * (0.5 + 3.0 * rng.random())
        cur = None
        for s in range(steps):
            A = sinkhorn(X)
            B = A - J
            Q = (B * B).sum()
            if Q < 1e-12:
                break
            val = abs(S_float(c, B)) / Q
            if cur is None or val > cur:
                cur = val
                if val > best[0]:
                    best = (val, A.copy())
            # crude coordinate ascent
            g = rng.normal(size=(n, n)) * 0.3 / (1 + s / 50)
            A2 = sinkhorn(X + g)
            B2 = A2 - J
            Q2 = (B2 * B2).sum()
            if Q2 > 1e-12 and abs(S_float(c, B2)) / Q2 > val:
                X = X + g
    return best


if __name__ == "__main__":
    emax = int(sys.argv[1]) if len(sys.argv) > 1 else 6
    ns = [int(x) for x in (sys.argv[2].split(",") if len(sys.argv) > 2 else ["5", "6", "7"])]
    for e in range(2, emax + 1):
        pats = patterns(e)
        print(f"=== e = {e}:  {len(pats)} connected iso classes, "
              f"l1 mass Lam_{e} = {sum(b for _, b in pats.values())}")
        for key, (sgn, mass) in sorted(pats.items()):
            c = [list(row) for row in key]
            rd = [sum(row) for row in c]
            cd = [sum(row[v] for row in c) for v in range(len(c[0]))]
            line = f"  {key}  deg_r={rd} deg_c={cd} mass={mass}"
            # permutation matrix, exact
            pv = [(n, S_perm_closed(c, n), n - 1) for n in (6, 10, 20)]
            worst = max(float(v) / (nn - 1) for nn, v, _ in pv)
            print(line + f"  perm ratio S/Q: " +
                  ", ".join(f"n={nn}:{float(v)/(nn-1):.6f}" for nn, v, _ in pv))
            for n in ns:
                val, A = hunt(c, n, restarts=int(sys.argv[3]) if len(sys.argv) > 3 else 25,
                              steps=120, seed=hash(key) % 10000 + n)
                flag = "  <<< VIOLATION" if val > 1.0 + 1e-9 else ""
                print(f"      hunt n={n}: max |S|/Q = {val:.6f}{flag}")
