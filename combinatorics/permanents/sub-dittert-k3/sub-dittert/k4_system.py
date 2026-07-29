"""
The k = 4 constraint system in CLOSED FORM over Q(n) -- no interpolation.

Structure, and what changes from k = 3 (general_k3.py).

  * deg F = 4, and a Gram basis of degree d gives deg(sigma_p b_p) = 2d + 1, so
    d = 1 tops out at 3 < 4 and is impossible on degree grounds alone.  d = 2 is
    forced, TOPDEG = 5, and the Gram basis is every monomial of degree 1 or 2.

  * At k = 3 the basis was a single cell, so basis[u]*basis[v] WAS the pair
    {u,v}: the sigma_0 variable orbits and the constraint-row orbits were the
    same objects.  That coincidence is gone.  Here basis[u]*basis[v] is a
    multiset of 2, 3 or 4 cells, and two different PAIRS can share a product
    ({a}{b,c} and {a,b}{c}).  So the Gram variables are orbits of PAIRS OF
    MONOMIALS, a strictly finer object than orbits of the product, and they must
    be enumerated and sized as such.

  * Everything else carries over unchanged, and for the same reasons:
      - canonicalisation is G-invariant and g_p(0,0) = p, so
        key(g_p(u) g_p(v)) = key(u v) and key(g_p(u) g_p(v) b_p) = key(u v b_00),
        both independent of p.  Hence A1c and A1l are again n^2 times a class
        size times a 0/1 incidence.
      - A2 is again an orbit size times a count over the n^2 positions, and the
        count splits by whether the new cell's row (column) is one of those
        already used or a new one -- a product of two linear counts.
      - coef_F is already written for general k.

  * Orbit sizes are by orbit-stabiliser.  A pair uses at most 4 cells, hence at
    most 4 rows and 4 columns; a row monomial at most 5 of each.  So every class
    size is a polynomial in n of degree at most 10, and every canonical form is a
    complete invariant of the class for n >= 5.  That is the a priori bound which
    makes this a derivation rather than a fit.

ENUMERATION STRATEGY.  Canonicalising every pair from a 5x5 grid would be about
3e8 relabellings.  Instead the classes are enumerated by union-find at a
reference n (cheap, and already used in k4_size.py), one representative is taken
per class, and the n-independent key and size polynomial are computed for those
few hundred representatives only.  Completeness is then CHECKED, not assumed, by
recomputing the key sets at a second n and requiring them to be identical.
"""

import itertools
import os
import sys
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "dittert"))
sys.path.insert(0, HERE)
import general_k3 as g                                           # noqa: E402
import sos                                                       # noqa: E402
from general_k3 import (canon, cells_of, falling, padd, pmul,     # noqa: E402
                        pscale, peval, pzero, _shift)
from symmetry import act, generators, monomials                   # noqa: E402

K = 4
DEG_BASIS = 2
TOPDEG = 2 * DEG_BASIS + 1                    # 5


# ------------------------------------------------------------- canonical forms
def _relabellings(used, fix_zero):
    """All relabellings of the used rows (or columns) onto a canonical range."""
    if fix_zero:
        free = [x for x in used if x != 0]
        out = []
        for p in itertools.permutations(free):
            d = dict(zip(p, range(1, len(p) + 1)))
            d[0] = 0
            out.append(d)
        return out
    return [dict(zip(p, range(len(p))))
            for p in itertools.permutations(used)]


def canon_pair(u, v, fix_zero=False):
    """
    Canonical form of the UNORDERED pair {u, v} of cell-multisets, under row
    permutations, column permutations, transposition and the swap u <-> v.

    The swap is included because the Gram matrix is symmetric, so (u,v) and
    (v,u) index the same variable -- exactly what sos.sym_pair_orbits does by
    unioning a*B+b with b*B+a.
    """
    best = None
    for transpose in (False, True):
        U = tuple(sorted((c, r) for r, c in u)) if transpose else tuple(sorted(u))
        V = tuple(sorted((c, r) for r, c in v)) if transpose else tuple(sorted(v))
        allc = U + V
        rows = sorted({r for r, _ in allc})
        cols = sorted({c for _, c in allc})
        for rm in _relabellings(rows, fix_zero):
            for cm in _relabellings(cols, fix_zero):
                A = tuple(sorted((rm[r], cm[c]) for r, c in U))
                B = tuple(sorted((rm[r], cm[c]) for r, c in V))
                for cand in ((A, B), (B, A)):
                    if best is None or cand < best:
                        best = cand
    return best


def pair_class_size(u, v, fix_zero=False):
    """
    The number of ORDERED pairs in this class, as an exact polynomial in n.

    Orbit-stabiliser.  An image is determined by an injection of the used rows
    into the n rows, an injection of the used columns, a transposition choice and
    a swap choice: 2 * 2 * [n]_r * [n]_c parameter tuples, mapping s-to-one onto
    the class, where s is the number of tuples that reproduce the canonical form.
    With fix_zero, row 0 and column 0 are fixed and only the others are free, so
    the falling factorials are taken at n - 1.
    """
    key = canon_pair(u, v, fix_zero)
    s = 0
    for transpose in (False, True):
        U = tuple(sorted((c, r) for r, c in u)) if transpose else tuple(sorted(u))
        V = tuple(sorted((c, r) for r, c in v)) if transpose else tuple(sorted(v))
        allc = U + V
        rows = sorted({r for r, _ in allc})
        cols = sorted({c for _, c in allc})
        for rm in _relabellings(rows, fix_zero):
            for cm in _relabellings(cols, fix_zero):
                A = tuple(sorted((rm[r], cm[c]) for r, c in U))
                B = tuple(sorted((rm[r], cm[c]) for r, c in V))
                for cand in ((A, B), (B, A)):
                    if cand == key:
                        s += 1
    allc = tuple(u) + tuple(v)
    rows = sorted({r for r, _ in allc})
    cols = sorted({c for _, c in allc})
    if fix_zero:
        fr = _shift(falling(len([x for x in rows if x != 0])))
        fc = _shift(falling(len([x for x in cols if x != 0])))
    else:
        fr, fc = falling(len(rows)), falling(len(cols))
    return pscale(pmul(pmul([F(4)], fr), fc), F(1, s))


# ------------------------------------------------------------ class enumeration
def basis_of(n):
    return monomials(n * n, DEG_BASIS, mindeg=1)


def pair_classes(n, fix_zero):
    """
    One representative per class of unordered pairs of basis monomials, by
    union-find at this n.  Returns {key: (u_cells, v_cells)}.
    """
    basis = basis_of(n)
    gens = sos.stab_generators(n, (0, 0)) if fix_zero else generators(n)
    orbs = sos.sym_pair_orbits(basis, gens)
    B = len(basis)
    out = {}
    for orb in orbs:
        u, v = divmod(orb[0], B)
        cu, cv = cells_of(basis[u], n), cells_of(basis[v], n)
        out[canon_pair(cu, cv, fix_zero)] = (cu, cv)
    return out


def monomial_classes(n, maxdeg):
    """One representative per G-orbit of monomials of degree <= maxdeg."""
    from symmetry import orbits as _orbits
    mons = monomials(n * n, maxdeg)
    reps, _ = _orbits(mons, generators(n))
    out = {}
    for _, members in reps.items():
        cells = cells_of(mons[members[0]], n)
        out[canon(cells)] = cells
    return out


# --------------------------------------------------------------- the A2 counts
def extend_counts(mu):
    """
    Classify every cell p of the grid by the canonical key of mu + {p}, and
    return {key: count-polynomial}.  A cell is described by whether its row is
    one of mu's rows or a new one, and likewise its column; there is 1 choice for
    a specific used row and (n - |rows(mu)|) for a new one, and the key depends
    only on the case, so each case contributes a product of two linear counts.
    """
    rows = sorted({r for r, _ in mu})
    cols = sorted({c for _, c in mu})
    newr = padd([F(-len(rows))], [F(0), F(1)])          # n - |rows|
    newc = padd([F(-len(cols))], [F(0), F(1)])          # n - |cols|
    fresh_r = max(rows) + 1 if rows else 0
    fresh_c = max(cols) + 1 if cols else 0
    out = {}

    def add(key, poly):
        out[key] = padd(out.get(key, pzero()), poly)

    for r in rows + [fresh_r]:
        for c in cols + [fresh_c]:
            key = canon(tuple(mu) + ((r, c),))
            pr = [F(1)] if r in rows else newr
            pc = [F(1)] if c in cols else newc
            add(key, pmul(pr, pc))
    return out


# ------------------------------------------------------------------ the system
def build(n_ref=5, verbose=True):
    """Assemble the whole system as exact polynomials in n."""
    rows_map = monomial_classes(n_ref, TOPDEG)
    lam_map = monomial_classes(n_ref, K)
    g_map = pair_classes(n_ref, False)
    s_map = pair_classes(n_ref, True)

    rows = sorted(rows_map)
    lvars = sorted(lam_map)
    gvars = sorted(g_map)
    svars = sorted(s_map)
    row_index = {r: i for i, r in enumerate(rows)}
    nR, nG, nS, nL = len(rows), len(gvars), len(svars), len(lvars)
    if verbose:
        print(f"  rows {nR}, sigma_0 {nG}, sigma_11 {nS}, lambda {nL}, "
              f"unknowns {nG + nS + nL}")

    A0 = [[pzero() for _ in range(nG)] for _ in range(nR)]
    for j, key in enumerate(gvars):
        u, v = g_map[key]
        prod = canon(tuple(u) + tuple(v))
        A0[row_index[prod]][j] = pair_class_size(u, v, False)

    n2 = [F(0), F(0), F(1)]
    A1c = [[pzero() for _ in range(nS)] for _ in range(nR)]
    A1l = [[pzero() for _ in range(nS)] for _ in range(nR)]
    for j, key in enumerate(svars):
        u, v = s_map[key]
        sz = pmul(pair_class_size(u, v, True), n2)
        prod = tuple(u) + tuple(v)
        A1c[row_index[canon(prod)]][j] = sz
        A1l[row_index[canon(prod + ((0, 0),))]][j] = sz

    A2 = [[pzero() for _ in range(nL)] for _ in range(nR)]
    for j, key in enumerate(lvars):
        mu = lam_map[key]
        sz = g.orbit_size_poly(key, False)
        for k2, cnt in extend_counts(mu).items():
            A2[row_index[k2]] = A2[row_index[k2]]
            A2[row_index[k2]][j] = padd(A2[row_index[k2]][j], pmul(sz, cnt))

    def rhs_at(n):
        return [peval(g.orbit_size_poly(r, False), n) * g.coef_F(r, n, K)
                for r in rows]

    return dict(rows=rows, gvars=gvars, svars=svars, lvars=lvars,
                A0=A0, A1c=A1c, A1l=A1l, A2=A2, rhs_at=rhs_at,
                row_index=row_index, g_map=g_map, s_map=s_map,
                lam_map=lam_map, rows_map=rows_map)


# ------------------------------------------------------------------- self-tests
def check_stabilisation(n1=5, n2=6):
    """The key SETS must be identical at two different n, or n1 misses types."""
    ok = True
    for name, fn in (("sigma_0 pairs", lambda n: set(pair_classes(n, False))),
                     ("sigma_11 pairs", lambda n: set(pair_classes(n, True))),
                     ("lambda monomials", lambda n: set(monomial_classes(n, K))),
                     ("rows", lambda n: set(monomial_classes(n, TOPDEG)))):
        a, b = fn(n1), fn(n2)
        same = a == b
        print(f"  {name}: {len(a)} at n={n1}, {len(b)} at n={n2}, "
              f"key sets identical: {same}")
        ok = ok and same
    return ok


def check_class_sizes(ns=(5, 6)):
    """Closed-form class sizes against brute-force enumeration."""
    ok = True
    for n in ns:
        basis = basis_of(n)
        B = len(basis)
        for fix in (False, True):
            gens = sos.stab_generators(n, (0, 0)) if fix else generators(n)
            orbs = sos.sym_pair_orbits(basis, gens)
            bad = 0
            for orb in orbs:
                u, v = divmod(orb[0], B)
                cu, cv = cells_of(basis[u], n), cells_of(basis[v], n)
                want = len(orb)
                got = peval(pair_class_size(cu, cv, fix), n)
                if want != got:
                    bad += 1
                    if bad <= 3:
                        print(f"    n={n} fix={fix} {cu}|{cv}: "
                              f"enumerated {want}, formula {got}")
            print(f"  n={n} fix_zero={fix}: {len(orbs)} classes, "
                  f"{bad} size mismatches")
            ok = ok and bad == 0
    return ok


def check_against_trusted(ns=(5,)):
    """
    The symbolic system against exact_system(build_sdp(n,4,2)) -- the code path
    that produced the verified (5,4) certificate.  The two share no logic: one
    evaluates closed forms, the other counts by union-find over every monomial.
    """
    from exactsd import exact_system
    sym = build(verbose=False)
    ok = True
    for n in ns:
        d = sos.build_sdp(n, K, DEG_BASIS, verbose=False)
        A0, A1c, A1l, A2, rhs = exact_system(d)
        B = d["B"]
        basis = d["basis"]

        inv_row = {}
        for mono, r in d["orbit_of"].items():
            inv_row.setdefault(r, mono)
        rmap = {r: canon(cells_of(m, n)) for r, m in inv_row.items()}

        def pkey(orb, fix):
            u, v = divmod(orb[0], B)
            return canon_pair(cells_of(basis[u], n), cells_of(basis[v], n), fix)

        gmap = {j: pkey(o, False) for j, o in enumerate(d["g_orbits"])}
        smap = {j: pkey(o, True) for j, o in enumerate(d["s_orbits"])}
        lam_mons = monomials(n * n, d["TOPDEG"] - 1)
        lmap = {j: canon(cells_of(lam_mons[m[0]], n))
                for j, m in enumerate(d["lam_orbit_reps"])}

        gi = {k2: i for i, k2 in enumerate(sym["gvars"])}
        si = {k2: i for i, k2 in enumerate(sym["svars"])}
        li = {k2: i for i, k2 in enumerate(sym["lvars"])}
        bad = 0
        for r_i, key_r in rmap.items():
            R = sym["row_index"][key_r]
            for j, kg in gmap.items():
                if F(A0[r_i][j]) != peval(sym["A0"][R][gi[kg]], n):
                    bad += 1
            for j, ks in smap.items():
                J = si[ks]
                if F(A1c[r_i][j]) != peval(sym["A1c"][R][J], n):
                    bad += 1
                if F(A1l[r_i][j]) != peval(sym["A1l"][R][J], n):
                    bad += 1
            for j, kl in lmap.items():
                if F(A2[r_i][j]) != peval(sym["A2"][R][li[kl]], n):
                    bad += 1
        rr = sym["rhs_at"](n)
        for r_i, key_r in rmap.items():
            if rhs[r_i] != rr[sym["row_index"][key_r]]:
                bad += 1
        entries = len(rmap) * (len(gmap) + 2 * len(smap) + len(lmap) + 1)
        print(f"  n={n}: symbolic vs exact_system -> {bad} mismatches over "
              f"{len(rmap)} rows x {len(gmap) + 2*len(smap) + len(lmap) + 1} "
              f"entries ({entries} comparisons)")
        ok = ok and bad == 0
    return ok


if __name__ == "__main__":
    if len(sys.argv) > 1 and sys.argv[1] == "trusted":
        ns = [int(a) for a in sys.argv[2:]] or [5]
        print("cross-check against the trusted pipeline:")
        print(f"\nresult: {check_against_trusted(ns)}")
        sys.exit(0)
    print("k = 4 closed-form system\n")
    print("stabilisation of the class sets:")
    s_ok = check_stabilisation()
    print("\nclass sizes vs brute force:")
    z_ok = check_class_sizes()
    print("\nbuilding the system:")
    sym = build()
    print(f"\nstabilisation OK: {s_ok};  class sizes OK: {z_ok}")
