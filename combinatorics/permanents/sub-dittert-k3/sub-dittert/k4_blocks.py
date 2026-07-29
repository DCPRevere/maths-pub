"""
Symbolic isotypic blocks for sigma_11 at k = 4 — closed form in n.

BLOCK 1: THE TRIVIAL ISOTYPIC COMPONENT, 14 x 14.

Its basis needs no representation theory: the Stab((0,0))-invariant vectors are
spanned by the orbit-indicator vectors, one per Stab-orbit of basis monomials.
And the orbits are already named elsewhere in this folder:

    degree-1 monomials (single cells):  K, R u C, I                    ->  3
    degree-2 monomials (pairs of cells): patterns(2, fix_zero=True)    -> 11
                                                                  total  14

The 11 are EXACTLY the k = 3 sigma_11 orbit keys (general_k3's `svars`), which is
why 3 + 11 = 14 matches the measured Stab-orbit count of §6b.6 on the nose.

The block is T[i][j] = sum over u in O_i, v in O_j of H[u][v], with
H[u][v] = y[pairclass(u,v)] over the 356 pair-classes.  So

    T[i][j] = sum_c y_c * N^{ij}_c ,   N^{ij}_c = #{(u,v) in O_i x O_j : class = c}

and the whole job is the counts N as POLYNOMIALS IN n.

HOW THE COUNTS ARE DERIVED, not interpolated.  By Stab-transitivity on O_i,
N^{ij}_c = |O_i| * #{v in O_j : class(u_0, v) = c} for any fixed u_0 in O_i.  For
the inner count, enumerate v ABSTRACTLY: each of v's cells takes a row label from
{row 0} u {u_0's other rows} u {new_1, new_2} and a column label likewise.  The
number of concrete v with a given abstract pattern is a product of two falling
factorials — [n-1-p]_(#new rows) * [n-1-q]_(#new cols) — because row 0 and
column 0 are fixed by the stabiliser and the "new" labels range over the rest.
The class is constant on an abstract pattern, so each pattern contributes its
falling-factorial product to one c.  Finite case analysis, exact for all n.
"""

import itertools
import os
import sys
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "dittert"))
sys.path.insert(0, HERE)
import general_k3 as g                                           # noqa: E402
import k4_system as k4                                           # noqa: E402
from general_k3 import falling, padd, pmul, pscale, peval, pzero, _shift  # noqa: E402

MAXNEW = 2          # a degree-<=2 monomial introduces at most 2 new rows/cols


def canon_nt(cells, fix_zero=True):
    """
    Canonical form under S_{n-1} x S_{n-1} ONLY -- the transposition suppressed.
    Needed for the sign block, whose basis is indexed by the transposition-SWAPPED
    pairs of S x S orbits, information that `canon` destroys by construction.
    """
    cells = tuple(sorted(cells))
    rows = sorted({r for r, _ in cells})
    cols = sorted({c for _, c in cells})

    def rel(used):
        free = [x for x in used if x != 0] if fix_zero else list(used)
        out = []
        for pm in itertools.permutations(free):
            d = dict(zip(pm, range(1, len(pm) + 1) if fix_zero
                         else range(len(pm))))
            if fix_zero:
                d[0] = 0
            out.append(d)
        return out

    best = None
    for rm in rel(rows):
        for cm in rel(cols):
            cand = tuple(sorted((rm[r], cm[c]) for r, c in cells))
            if best is None or cand < best:
                best = cand
    return best


def transpose_cells(cells):
    return tuple(sorted((c, r) for r, c in cells))


def ss_orbit_size(P):
    """|S x S orbit of P|, fixing row 0 and column 0, as a polynomial in n.

    Same orbit-stabiliser count as general_k3.orbit_size_poly but WITHOUT its
    factor of 2 for the transposition, and with the stabiliser taken in
    S_{n-1} x S_{n-1} rather than the full stabiliser.
    """
    rows = sorted({r for r, _ in P})
    cols = sorted({c for _, c in P})
    rfree = [r for r in rows if r != 0]
    cfree = [c for c in cols if c != 0]
    stab = 0
    target = tuple(sorted(P))
    for pm in itertools.permutations(rfree):
        rm = dict(zip(rfree, pm))
        rm[0] = 0
        for qm in itertools.permutations(cfree):
            cm = dict(zip(cfree, qm))
            cm[0] = 0
            if tuple(sorted((rm[r], cm[c]) for r, c in P)) == target:
                stab += 1
    return pscale(pmul(_shift_by(falling(len(rfree)), 0),
                       _shift_by(falling(len(cfree)), 0)), F(1, stab))


def trivial_orbit_reps():
    """
    The 14 Stab-orbit representatives: 3 single cells and 11 cell-pairs.
    Returned as (key, cells) with cells a tuple of (row, col).
    """
    reps = []
    for cells in (((0, 0),), ((0, 1),), ((1, 1),)):        # K, R (~ C), I
        reps.append((g.canon(cells, True), cells))
    for key in g.patterns(2, fix_zero=True):
        reps.append((key, key))
    return reps


def _labels(used, extra):
    """Row (or column) labels available to a cell of v: 0, u_0's, or new."""
    return [("fix", 0)] + [("used", r) for r in used if r != 0] \
        + [("new", i) for i in range(extra)]


def inner_counts(u0, deg, vkey=None):
    """
    {class-key: polynomial} for #{v of degree `deg` : class(u_0, v) = key}.

    Exact: each abstract pattern of v contributes [n-1-p]_a * [n-1-q]_b, the
    number of ways to instantiate its `a` new rows and `b` new columns among the
    n-1 rows and n-1 columns other than 0.
    """
    urows = sorted({r for r, _ in u0})
    ucols = sorted({c for _, c in u0})
    p = len([r for r in urows if r != 0])
    q = len([c for c in ucols if c != 0])
    rlab = _labels(urows, MAXNEW)
    clab = _labels(ucols, MAXNEW)
    # concrete indices for instantiating labels, kept disjoint from u_0's
    hi_r = max(urows) + 1
    hi_c = max(ucols) + 1
    out = {}
    seen = set()
    for cellpat in itertools.combinations_with_replacement(
            [(a, b) for a in rlab for b in clab], deg):
        newr = sorted({lab[1] for lab, _ in cellpat if lab[0] == "new"})
        newc = sorted({lab[1] for _, lab in cellpat if lab[0] == "new"})
        a, b = len(newr), len(newc)
        # CANONICALISE over all relabellings of the new row and column labels,
        # and count how many reproduce the canonical form -- that count is
        # |Aut| of the template's label symmetry.  The falling factorials count
        # INJECTIONS of the new labels into the free rows and columns, and the
        # map from injections to concrete v is |Aut|-to-one, so the contribution
        # must be divided by it.  Omitting this was the 2x / 4x error of §6b.16:
        # the key sets were right and only the multiplicities were wrong.
        best, aut = None, 0
        for pr in itertools.permutations(range(a)):
            for pc in itertools.permutations(range(b)):
                rmap = {lab: pr[i] for i, lab in enumerate(newr)}
                cmap = {lab: pc[i] for i, lab in enumerate(newc)}
                cells = []
                for rl, cl in cellpat:
                    r = 0 if rl[0] == "fix" else (
                        rl[1] if rl[0] == "used" else hi_r + rmap[rl[1]])
                    c = 0 if cl[0] == "fix" else (
                        cl[1] if cl[0] == "used" else hi_c + cmap[cl[1]])
                    cells.append((r, c))
                cells = tuple(sorted(cells))
                if best is None or cells < best:
                    best, aut = cells, 1
                elif cells == best:
                    aut += 1
        if best in seen:
            continue
        seen.add(best)
        cnt = pscale(pmul(_shift_by(falling(a), p), _shift_by(falling(b), q)),
                     F(1, aut))
        # keyed by (v's own Stab-orbit, the pair class) -- the first is needed
        # to restrict to v in O_j when assembling the block.
        vk = (vkey or (lambda c: g.canon(c, True)))(best)
        key = (vk, k4.canon_pair(u0, best, True))
        out[key] = padd(out.get(key, pzero()), cnt)
    return out


def _shift_by(poly, k):
    """p(n) -> p(n - 1 - k)."""
    out = pzero()
    acc = [F(1)]
    for i, co in enumerate(poly):
        if i:
            acc = pmul(acc, [F(-1 - k), F(1)])
        out = padd(out, pscale(acc, co))
    return out


def trivial_block():
    """
    The 14 x 14 block, entry (i,j) as {pair-class key: polynomial in n}.

    T[i][j] = sum over u in O_i, v in O_j of H[u][v].  By Stab-transitivity on
    O_i this is |O_i| times the inner count at a fixed representative u_0,
    restricted to v in O_j.
    """
    reps = trivial_orbit_reps()
    sizes = [g.orbit_size_poly(cells, True) for _, cells in reps]
    T = [[dict() for _ in range(len(reps))] for _ in range(len(reps))]
    for i, (_, u0) in enumerate(reps):
        inner = {1: inner_counts(u0, 1), 2: inner_counts(u0, 2)}
        for j, (keyj, vcells) in enumerate(reps):
            acc = {}
            for (vorb, cls), poly in inner[len(vcells)].items():
                if vorb != keyj:
                    continue
                acc[cls] = padd(acc.get(cls, pzero()), pmul(sizes[i], poly))
            T[i][j] = acc
    return reps, sizes, T


def verify_block(ns=(5, 6)):
    """The closed-form 14 x 14 against k4_pilot's brute-force construction."""
    import k4_pilot
    reps, sizes, T = trivial_block()
    keyidx = {k2: i for i, (k2, _) in enumerate(reps)}
    ok = True
    for n in ns:
        svars = k4.build(verbose=False)["svars"]
        sidx = {k2: i for i, k2 in enumerate(svars)}
        norb, N = k4_pilot.trivial_block_counts(n, True)
        # k4_pilot's orbit ordering comes from union-find; match by key
        from symmetry import monomials as _m
        import sos as _sos
        from symmetry import orbits as _orb
        basis = k4.basis_of(n)
        reps_n, _ = _orb(basis, _sos.stab_generators(n, (0, 0)))
        order = [g.canon(g.cells_of(basis[m[0]], n), True)
                 for _, m in reps_n.items()]
        bad = 0
        for a in range(norb):
            for b in range(norb):
                want = N.get((a, b))
                i, j = keyidx[order[a]], keyidx[order[b]]
                got = [0] * len(svars)
                for cls, poly in T[i][j].items():
                    got[sidx[cls]] += peval(poly, n)
                w = want if want is not None else [0] * len(svars)
                if [F(x) for x in w] != [F(x) for x in got]:
                    bad += 1
        print(f"  n={n}: 14x14 closed form vs brute force -> "
              f"{bad} mismatched entries of {norb * norb}")
        ok = ok and bad == 0
    return ok


def verify_against_enumeration(ns=(5, 6)):
    """
    The closed-form inner counts against brute-force enumeration at each n.

    This is the check that matters: the abstract-pattern analysis is a finite
    case split and a missed case would silently drop a term.
    """
    from symmetry import monomials
    from general_k3 import cells_of
    ok = True
    reps = trivial_orbit_reps()
    for n in ns:
        allmon = {1: [((i, j),) for i in range(n) for j in range(n)],
                  2: [tuple(sorted(m)) for m in
                      itertools.combinations_with_replacement(
                          [(i, j) for i in range(n) for j in range(n)], 2)]}
        for _, u0 in reps:
            for deg in (1, 2):
                brute = {}
                for v in allmon[deg]:
                    key = k4.canon_pair(u0, v, True)
                    brute[key] = brute.get(key, 0) + 1
                # inner_counts is keyed by (v-orbit, pair-class); the brute
                # force is keyed by pair-class alone, so aggregate first.
                agg = {}
                for (_, cls), poly in inner_counts(u0, deg).items():
                    agg[cls] = agg.get(cls, 0) + peval(poly, n)
                closed = dict(agg)
                closed = {k2: v for k2, v in closed.items() if v}
                if brute != closed:
                    ok = False
                    miss = set(brute) ^ set(closed)
                    diff = {k2 for k2 in set(brute) & set(closed)
                            if brute[k2] != closed[k2]}
                    print(f"    n={n} u0={u0} deg={deg}: MISMATCH "
                          f"({len(miss)} key diffs, {len(diff)} value diffs)")
                    for k2 in list(miss)[:2]:
                        print(f"      key {k2}: brute {brute.get(k2)}, "
                              f"closed {closed.get(k2)}")
                    for k2 in list(diff)[:2]:
                        print(f"      key {k2}: brute {brute[k2]} vs "
                              f"closed {closed[k2]}")
        print(f"  n={n}: closed-form inner counts vs enumeration over "
              f"{len(reps)} orbit reps x 2 degrees: "
              f"{'ALL MATCH' if ok else 'mismatches above'}")
    return ok


if __name__ == "__main__":
    print("trivial isotypic component of sigma_11 at k = 4\n")
    reps = trivial_orbit_reps()
    print(f"  {len(reps)} Stab-orbit representatives "
          f"({sum(1 for _, c in reps if len(c) == 1)} of degree 1, "
          f"{sum(1 for _, c in reps if len(c) == 2)} of degree 2)")
    print("\nclosed-form inner counts vs brute-force enumeration:")
    ok = verify_against_enumeration()
    print("\nassembled 14 x 14 block vs brute force:")
    ok2 = verify_block()
    print(f"\ncounts verified: {ok};  block verified: {ok2}")


# ------------------------------------------------------------- the sign block
def sign_pairs():
    """The 7 transposition-SWAPPED pairs of S x S orbits, as (O, tau O)."""
    reps = set()
    for cells in (((0, 0),), ((0, 1),), ((1, 1),), ((1, 0),)):
        reps.add(canon_nt(cells))
    grid = [(i, j) for i in range(4) for j in range(4)]
    for combo in itertools.combinations_with_replacement(grid, 2):
        reps.add(canon_nt(combo))
    out = []
    for k in sorted(reps):
        t = canon_nt(transpose_cells(k))
        if t != k and k < t:
            out.append((k, t))
    return out


def sign_block():
    """
    The 7 x 7 sign block, entry (i,j) as {pair-class key: polynomial in n}.

    S[i][j] = 2 ( sum_{O_i x O_j} H - sum_{O_i x tau O_j} H ), by the
    transposition-invariance of H (NOTES section 6b.19).
    """
    prs = sign_pairs()
    sizes = [ss_orbit_size(o) for o, _ in prs]
    S = [[dict() for _ in prs] for _ in prs]
    for i, (o_i, _) in enumerate(prs):
        inner = {1: inner_counts(o_i, 1, vkey=canon_nt),
                 2: inner_counts(o_i, 2, vkey=canon_nt)}
        for j, (o_j, t_j) in enumerate(prs):
            acc = {}
            for sgn, target in ((1, o_j), (-1, t_j)):
                for (vorb, cls), poly in inner[len(o_j)].items():
                    if vorb != target:
                        continue
                    term = pscale(pmul(sizes[i], poly), F(2 * sgn))
                    acc[cls] = padd(acc.get(cls, pzero()), term)
            S[i][j] = {c: p for c, p in acc.items() if p}
    return prs, S


def verify_sign_block(ns=(5, 6)):
    """Closed-form 7 x 7 against brute force over all B^2 pairs."""
    import random
    import sos as _sos
    from general_k3 import cells_of
    prs, S = sign_block()
    ok = True
    for n in ns:
        basis = k4.basis_of(n)
        B = len(basis)
        knt = [canon_nt(cells_of(m, n)) for m in basis]
        grp = {}
        for u, k2 in enumerate(knt):
            grp.setdefault(k2, []).append(u)
        # The class index MUST be in the symbolic `svars` ordering, not
        # build_sdp's orbit ordering -- the two are unrelated, and indexing the
        # same random y by both is the error that made this look like a
        # 48-of-49 failure with non-constant ratios (NOTES 6b.20).
        orbs = _sos.sym_pair_orbits(basis, _sos.stab_generators(n, (0, 0)))
        svars = k4.build(verbose=False)["svars"]
        sidx = {k2: i for i, k2 in enumerate(svars)}
        cls = [0] * (B * B)
        for orb in orbs:
            u, v = divmod(orb[0], B)
            j = sidx[k4.canon_pair(cells_of(basis[u], n),
                                   cells_of(basis[v], n), True)]
            for code in orb:
                cls[code] = j
        rng = random.Random(11)
        y = [F(rng.randint(-20, 20), rng.randint(1, 7)) for _ in orbs]

        def bsum(A, C):
            t = F(0)
            for u in A:
                base = u * B
                for v in C:
                    t += y[cls[base + v]]
            return t

        bad = 0
        for i, (o_i, t_i) in enumerate(prs):
            for j, (o_j, t_j) in enumerate(prs):
                brute = (bsum(grp[o_i], grp[o_j]) - bsum(grp[o_i], grp[t_j])
                         - bsum(grp[t_i], grp[o_j]) + bsum(grp[t_i], grp[t_j]))
                closed = sum((peval(p, n) * y[sidx[c]]
                              for c, p in S[i][j].items()), F(0))
                if brute != closed:
                    bad += 1
        print(f"  n={n}: 7x7 sign block closed form vs brute force -> "
              f"{bad} mismatched entries of {len(prs) ** 2}")
        ok = ok and bad == 0
    return ok
