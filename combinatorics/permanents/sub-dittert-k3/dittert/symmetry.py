"""
Symmetry reduction for the Dittert Positivstellensatz.

The group  G = (S_n x S_n) semidirect Z_2  acts on the n^2 centred coordinates
b_ij by permuting rows, permuting columns, and transposing.  |G| = 2 (n!)^2,
which is 28800 at n = 5.  Because it acts by PERMUTING the variables, it also
permutes monomials, so every representation we need is a permutation
representation and orbit arithmetic suffices -- no character theory required.

We use this twice.

1. CONSTRAINTS.  Both sides of the certificate identity are G-invariant, so
   their coefficients are constant on G-orbits of monomials.  Matching one
   representative per orbit is therefore equivalent to matching all
   142506 monomials of degree <= 5, and there are only a few hundred orbits.

2. GRAM MATRICES.  A G-invariant Gram matrix is a nonnegative combination of the
   orbit indicator matrices of G acting on ORDERED PAIRS of basis monomials.
   That parametrises the commutant in a few hundred scalars while keeping a
   single honest positive-semidefiniteness constraint on the assembled matrix.

Monomials are stored as sorted tuples of variable indices with repetition, e.g.
(0,3,3,7,12) is b_0 b_3^2 b_7 b_12.
"""

import itertools
from fractions import Fraction as F


def positions(n):
    return [(i, j) for i in range(n) for j in range(n)]


def generators(n):
    """Permutations of the n^2 positions generating G = (S_n x S_n) : Z_2."""
    pos = positions(n)
    idx = {p: k for k, p in enumerate(pos)}
    gens = []
    for a in range(n - 1):           # adjacent row transposition
        def rp(p, a=a):
            i, j = p
            i = a + 1 if i == a else (a if i == a + 1 else i)
            return (i, j)
        gens.append(tuple(idx[rp(p)] for p in pos))
    for a in range(n - 1):           # adjacent column transposition
        def cp(p, a=a):
            i, j = p
            j = a + 1 if j == a else (a if j == a + 1 else j)
            return (i, j)
        gens.append(tuple(idx[cp(p)] for p in pos))
    gens.append(tuple(idx[(p[1], p[0])] for p in pos))   # transpose
    return gens


def group_elements(n, limit=None):
    """Full group as tuples, by closure on the generators."""
    gens = generators(n)
    N = n * n
    ident = tuple(range(N))
    seen = {ident}
    frontier = [ident]
    while frontier:
        nxt = []
        for g in frontier:
            for h in gens:
                comp = tuple(h[g[k]] for k in range(N))
                if comp not in seen:
                    seen.add(comp)
                    nxt.append(comp)
                    if limit and len(seen) > limit:
                        return seen
        frontier = nxt
    return seen


def monomials(N, maxdeg, mindeg=0):
    """All monomials as sorted index tuples, degrees mindeg..maxdeg."""
    out = []
    for d in range(mindeg, maxdeg + 1):
        out.extend(itertools.combinations_with_replacement(range(N), d))
    return out


def act(g, mono):
    return tuple(sorted(g[v] for v in mono))


def orbits(items, gens):
    """Union-find orbits of `items` under the given generator permutations."""
    index = {m: k for k, m in enumerate(items)}
    parent = list(range(len(items)))

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    def union(x, y):
        rx, ry = find(x), find(y)
        if rx != ry:
            parent[max(rx, ry)] = min(rx, ry)

    for k, m in enumerate(items):
        for g in gens:
            union(k, index[act(g, m)])
    reps = {}
    for k in range(len(items)):
        reps.setdefault(find(k), []).append(k)
    return reps, index


def pair_orbits(basis, gens):
    """Orbits of G on ordered pairs of basis monomials, as a list of lists."""
    index = {m: k for k, m in enumerate(basis)}
    B = len(basis)
    gperm = []
    for g in gens:
        gperm.append([index[act(g, m)] for m in basis])
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
            ga = gp[a]
            base = a * B
            gbase = ga * B
            for b in range(B):
                union(base + b, gbase + gp[b])
    buckets = {}
    for k in range(B * B):
        buckets.setdefault(find(k), []).append(k)
    return list(buckets.values()), B


def stabiliser_gens(n, pos_index):
    """Generators of the stabiliser of the position with index pos_index."""
    pos = positions(n)
    tgt = pos[pos_index]
    full = group_elements(n)
    stab = [g for g in full if g[pos_index] == pos_index]
    return stab, tgt


if __name__ == "__main__":
    for n in [4, 5]:
        N = n * n
        gens = generators(n)
        G = group_elements(n)
        import math
        print(f"n={n}: |G| = {len(G)}  (expected {2*math.factorial(n)**2})")

        mons = monomials(N, n)          # degrees 0..n
        reps, _ = orbits(mons, gens)
        print(f"   monomials of degree <= {n} in {N} vars: {len(mons)}")
        print(f"   G-orbits of these monomials: {len(reps)}"
              f"   -> that many equality constraints instead of {len(mons)}")

        basis = monomials(N, 2, mindeg=1)   # degrees 1,2  (constant excluded)
        print(f"   Gram basis (degrees 1,2): {len(basis)}")
        po, B = pair_orbits(basis, gens)
        print(f"   G-orbits on ordered pairs of basis monomials: {len(po)}"
              f"   -> invariant Gram has {len(po)} free scalars")

        stab, tgt = stabiliser_gens(n, 0)
        print(f"   |Stab(position {tgt})| = {len(stab)}")
        pos_s, _ = pair_orbits(basis, list(stab)[:60])
        print(f"   Stab-orbits on ordered pairs (using 60 elements): {len(pos_s)}")
        print()
