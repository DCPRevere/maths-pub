"""
Towards the Cheon-Hwang conjecture at k = 3 for EVERY n, as one theorem.

The opportunity, restated.  At k = 3 with a Gram basis of degree 1, the
symmetry-reduced program has 12 constraint rows of rank 11 and 3 + 11 + 5 = 19
variables -- IDENTICALLY at n = 4, 5, 6, 7, 8.  Only the cone size n^2 and the
numerical entries change.  Crucially deg F = k = 3 is FIXED while n grows, so the
degree argument that blocks a uniform-in-n Dittert proof (METHODS.md section 7.1:
deg F = n outgrows an ansatz capped at degree 5, with a proof at n = 6 that no
degree-<=4-multiplier certificate exists) does not arise here at all.

WHAT MAKES A UNIFORM CLAIM A THEOREM RATHER THAN A FIT.  Interpolating the
constraint entries from finitely many n gives a CANDIDATE.  It becomes a proof
only if the entries are known a priori to be polynomials in n of bounded degree,
so that enough sample points determine them uniquely.  This module establishes
that, and in two places avoids interpolation entirely by deriving closed forms.

THE STRUCTURE THAT COLLAPSES THE WORK.  Write mm for the canonical form of a
multiset of positions under (S_n x S_n) : Z_2.  Then, for the degree-1 basis:

  * basis[u] is the single position u, so the product basis[u]*basis[v] IS the
    pair {u,v}.  Its G-orbit is therefore the SAME object as the sigma_0 variable
    orbit.  Hence A0[r][gv] = |orbit(gv)| when r = key(gv), and 0 otherwise.

  * For sigma_11, the code applies the transporter g_p (with g_p(0,0) = p) and
    then canonicalises.  Since g_p lies in G and canonicalisation is G-invariant,
    canon({g_p(u), g_p(v)}) = canon({u,v}), independent of p.  So
    A1c[r][sv] = n^2 * |orbit(sv)| * [r = canon(pair)].

  * Likewise canon({g_p(u), g_p(v), p}) = canon({u, v, (0,0)}) because
    g_p(0,0) = p.  And the Stab((0,0))-orbit fixes (0,0), so that key is constant
    on the orbit.  So A1l[r][sv] = n^2 * |orbit(sv)| * [r = canon(pair + (0,0))].

  * A2[r][lv] = |orbit(lv)| * #{ p : canon(rep(lv) + {p}) = r }, by transitivity
    of G on the orbit.

So EVERY entry is an orbit size times a 0/1 incidence, or an orbit size times a
count over n^2 positions.  Orbit sizes of tuples of at most 3 positions in an
n x n grid involve at most 3 distinct rows and 3 distinct columns, so they are
polynomials in n of degree at most 6.  That is the a priori bound that makes a
finite fit exact.

The right-hand side needs no fit at all: section `coef_F` below derives the
coefficient of an arbitrary monomial of F in closed form, for all n at once.
"""

import itertools
import os
import sys
from fractions import Fraction as F
from math import comb, factorial

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "dittert"))
sys.path.insert(0, HERE)  # HERE must win the name `expand` (see sos.py)


# ---------------------------------------------------------------- canonical form
def canon(cells, fix_zero=False):
    """
    Canonical form of a multiset of grid positions under row permutations,
    column permutations and transposition.

    `cells` is an iterable of (row, col).  With fix_zero the group is restricted
    to the stabiliser of (0,0): row 0 and column 0 must be preserved.
    Transposition fixes (0,0), so it is allowed in both cases.

    Validity.  A relabelling of the used rows extends to a permutation of [n]
    whenever the number of used rows is at most n.  Degree <= 3 uses at most 3
    rows and 3 columns, so this is a complete invariant of the orbit for every
    n >= 3.  It is therefore n-INDEPENDENT, which is exactly what lets orbits be
    matched across different n.
    """
    cells = tuple(sorted(cells))
    best = None
    for transpose in (False, True):
        cur = tuple(sorted((c, r) for (r, c) in cells)) if transpose else cells
        rows = sorted({r for r, _ in cur})
        cols = sorted({c for _, c in cur})
        if fix_zero:
            rfree = [r for r in rows if r != 0]
            cfree = [c for c in cols if c != 0]
            rperms = [dict(zip(p, range(1, len(p) + 1)))
                      for p in itertools.permutations(rfree)]
            for d in rperms:
                d[0] = 0
            cperms = [dict(zip(p, range(1, len(p) + 1)))
                      for p in itertools.permutations(cfree)]
            for d in cperms:
                d[0] = 0
        else:
            rperms = [dict(zip(p, range(len(p))))
                      for p in itertools.permutations(rows)]
            cperms = [dict(zip(p, range(len(p))))
                      for p in itertools.permutations(cols)]
        for rm in rperms:
            for cm in cperms:
                cand = tuple(sorted((rm[r], cm[c]) for r, c in cur))
                if best is None or cand < best:
                    best = cand
    return best


def cells_of(mono, n):
    """Monomial as a tuple of variable indices -> tuple of (row, col)."""
    return tuple((v // n, v % n) for v in mono)


# ------------------------------------------------------- closed-form coefficients
def coef_F(cells, n, k=3):
    """
    The coefficient of the monomial prod b_{ij} (over `cells`, with multiplicity)
    in F(b) = (2 - k!/n^k) - [E_k(r) + E_k(c) - P_k(J/n + b)], EXACTLY, for all n.

    Derivation, which is the whole point -- it replaces interpolation by proof.

    e_k(r) = sum over k-subsets {i_1<...<i_k} of prod r_i, and r_i = 1 + L_i with
    L_i = sum_j b_ij.  A monomial of degree d arises by choosing d of the k
    factors to contribute their L, one b each.  Two b's from the same row would
    need the same factor twice, which cannot happen inside a single product.  So:

        [monomial] e_k(r) = C(n-d, k-d)   if the d cells lie in DISTINCT ROWS,
                          = 0             otherwise,

    the count being the number of k-subsets containing the d used rows.
    Symmetrically for e_k(c) with columns.

    sigma_k(A) = sum over k-subsets alpha, beta of per(A[alpha|beta]).  A term of
    per is a bijection alpha -> beta; choosing which d of the k matched entries
    contribute b (the rest contribute 1/n) forces the d cells to form a PARTIAL
    PERMUTATION: distinct rows AND distinct columns.  Given such cells, alpha must
    contain their d rows and beta their d columns, and the remaining k-d matched
    pairs may be any bijection between the leftovers.  So:

        [monomial] sigma_k = C(n-d, k-d)^2 * (k-d)! * n^{-(k-d)},

    again 0 unless the cells form a partial permutation.

    Finally E_k = e_k/C(n,k), P_k = sigma_k/C(n,k)^2, and F = const - (E+E-P), so
    the sign is flipped.  The constant term is 0 because equality holds at b = 0.
    """
    cells = tuple(cells)
    d = len(cells)
    if d == 0:
        return F(0)                       # F(0) = 0
    if d > k:
        return F(0)
    rows = [r for r, _ in cells]
    cols = [c for _, c in cells]
    distinct_rows = len(set(rows)) == d
    distinct_cols = len(set(cols)) == d

    cnk = comb(n, k)
    e_r = F(comb(n - d, k - d), cnk) if distinct_rows else F(0)
    e_c = F(comb(n - d, k - d), cnk) if distinct_cols else F(0)
    if distinct_rows and distinct_cols:
        p_k = F(comb(n - d, k - d) ** 2 * factorial(k - d),
                cnk ** 2 * n ** (k - d))
    else:
        p_k = F(0)
    return -(e_r + e_c - p_k)


def check_coef_F(ns=(4, 5, 6), k=3):
    """Cross-check the closed form against the fully expanded polynomial."""
    import expand
    ok = True
    for n in ns:
        d = expand.build(n, k)
        N = n * n
        got = {}
        for e, c in d["F"].items():
            mono = tuple(itertools.chain.from_iterable(
                [t] * et for t, et in enumerate(e) if et))
            got[tuple(sorted(mono))] = c
        # every monomial of degree <= k, present or absent
        allm = []
        for deg in range(0, k + 1):
            allm.extend(itertools.combinations_with_replacement(range(N), deg))
        bad = 0
        for mono in allm:
            want = got.get(mono, F(0))
            have = coef_F(cells_of(mono, n), n, k)
            if want != have:
                bad += 1
                if bad <= 3:
                    print(f"    n={n} mono {mono}: expanded {want}, "
                          f"closed form {have}")
        print(f"  coef_F closed form vs expand.build at n={n}: "
              f"{len(allm)} monomials checked, {bad} mismatches")
        ok = ok and bad == 0
    return ok


# ------------------------------------------------------------- polynomials in n
# A polynomial in n is a list of Fractions, constant term first.
def pzero():
    return []


def ptrim(p):
    while p and p[-1] == 0:
        p.pop()
    return p


def padd(a, b):
    m = max(len(a), len(b))
    return ptrim([(a[i] if i < len(a) else F(0)) + (b[i] if i < len(b) else F(0))
                  for i in range(m)])


def pmul(a, b):
    if not a or not b:
        return []
    out = [F(0)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                if y:
                    out[i + j] += x * y
    return ptrim(out)


def pscale(a, s):
    return [] if s == 0 else ptrim([c * s for c in a])


def peval(p, n):
    v = F(0)
    for c in reversed(p):
        v = v * n + c
    return v


def pstr(p, var="n"):
    if not p:
        return "0"
    out = []
    for i in reversed(range(len(p))):
        c = p[i]
        if not c:
            continue
        out.append(f"{c}" if i == 0 else
                   (f"{c}*{var}" if i == 1 else f"{c}*{var}^{i}"))
    return " + ".join(out).replace("+ -", "- ")


def falling(r):
    """The falling factorial n(n-1)...(n-r+1) as a polynomial in n."""
    p = [F(1)]
    for i in range(r):
        p = pmul(p, [F(-i), F(1)])
    return p


# --------------------------------------------------- orbit sizes, in closed form
def _relabel(cells, rmap, cmap):
    return tuple(sorted((rmap[r], cmap[c]) for r, c in cells))


def stabiliser_order(P, fix_zero=False):
    """
    |Stab(P)| inside the acting group, by brute force over at most 2*3!*3!
    elements.  P is a canonical pattern: its rows are 0..r-1 and columns
    0..c-1 (with fix_zero, label 0 is reserved and cannot be moved).
    """
    rows = sorted({r for r, _ in P})
    cols = sorted({c for _, c in P})
    count = 0
    for transpose in (False, True):
        Q = tuple(sorted((c, r) for (r, c) in P)) if transpose else tuple(sorted(P))
        qrows = sorted({r for r, _ in Q})
        qcols = sorted({c for _, c in Q})
        if len(qrows) != len(rows) or len(qcols) != len(cols):
            continue
        if fix_zero:
            if (0 in qrows) != (0 in rows) or (0 in qcols) != (0 in cols):
                continue
            qrf = [r for r in qrows if r != 0]
            rtgt = [r for r in rows if r != 0]
            qcf = [c for c in qcols if c != 0]
            ctgt = [c for c in cols if c != 0]
        else:
            qrf, rtgt, qcf, ctgt = qrows, rows, qcols, cols
        for rp in itertools.permutations(rtgt):
            rmap = dict(zip(qrf, rp))
            if fix_zero:
                rmap[0] = 0
            for cp in itertools.permutations(ctgt):
                cmap = dict(zip(qcf, cp))
                if fix_zero:
                    cmap[0] = 0
                if _relabel(Q, rmap, cmap) == tuple(sorted(P)):
                    count += 1
    return count


def orbit_size_poly(P, fix_zero=False):
    """
    |orbit of P| as an exact polynomial in n.

    Orbit-stabiliser.  An image of P is determined by an injection of P's rows
    into the n available rows, an injection of P's columns into the n columns,
    and whether transposition was applied; that is 2 * [n]_r * [n]_c parameter
    choices, and the map to images is |Stab(P)|-to-one.  With fix_zero, row 0 and
    column 0 are FIXED, so only the other rows and columns are free: the counts
    become [n-1]_{r'} and [n-1]_{c'} where r', c' exclude label 0.

    Degree is r + c <= 6 for a multiset of at most 3 cells, which is the a priori
    bound that makes any finite fit unnecessary here.
    """
    rows = sorted({r for r, _ in P})
    cols = sorted({c for _, c in P})
    s = stabiliser_order(P, fix_zero)
    if fix_zero:
        r = len([x for x in rows if x != 0])
        c = len([x for x in cols if x != 0])
        # [n-1]_r as a polynomial in n: substitute n -> n-1 into falling(r)
        fr = _shift(falling(r))
        fc = _shift(falling(c))
    else:
        fr, fc = falling(len(rows)), falling(len(cols))
    return pscale(pmul(pmul([F(2)], fr), fc), F(1, s))


def _shift(p):
    """p(n) -> p(n-1)."""
    out = []
    acc = [F(1)]
    for i, c in enumerate(p):
        if i:
            acc = pmul(acc, [F(-1), F(1)])
        out = padd(out, pscale(acc, c))
    return out


def check_orbit_sizes(ns=(4, 5, 6, 7), k=3):
    """Cross-check the closed-form orbit sizes against brute-force enumeration."""
    ok = True
    for n in ns:
        N = n * n
        for deg, fix in ((1, False), (2, False), (3, False), (2, True)):
            counts = {}
            for mono in itertools.combinations_with_replacement(range(N), deg):
                key = canon(cells_of(mono, n), fix)
                counts[key] = counts.get(key, 0) + 1
            bad = 0
            for key, cnt in counts.items():
                got = peval(orbit_size_poly(key, fix), n)
                if got != cnt:
                    bad += 1
                    if bad <= 2:
                        print(f"    n={n} deg={deg} fix={fix} key={key}: "
                              f"enumerated {cnt}, formula {got}")
            print(f"  n={n} deg={deg} fix_zero={fix}: {len(counts)} orbits, "
                  f"{bad} size mismatches")
            ok = ok and bad == 0
    return ok


# --------------------------------------------------------- the system, symbolic
def patterns(deg, fix_zero=False, k=3):
    """All canonical keys of multisets of exactly `deg` cells.  Generated from a
    3x3 corner, which suffices because a multiset of at most 3 cells involves at
    most 3 rows and 3 columns."""
    grid = [(i, j) for i in range(3) for j in range(3)]
    keys = set()
    for combo in itertools.combinations_with_replacement(grid, deg):
        keys.add(canon(combo, fix_zero))
    return sorted(keys)


def ordered_pair_orbit_poly(key, fix_zero):
    """|orbit| counted as ORDERED pairs (u,v), which is what sym_pair_orbits
    produces: it is twice the multiset-orbit size unless the two cells coincide."""
    base = orbit_size_poly(key, fix_zero)
    return base if len(set(key)) == 1 and len(key) == 2 else pscale(base, F(2))


def build_symbolic_system(k=3):
    """
    The whole constraint system as exact polynomials in n (and, for the right-hand
    side, exact rational functions of n).  No interpolation anywhere.

    Returns row keys, variable keys, and callables giving each entry.
    """
    rows = []
    for deg in range(0, k + 1):
        rows.extend(patterns(deg))
    row_index = {r: i for i, r in enumerate(rows)}

    gvars = patterns(2)                       # sigma_0: pairs of cells
    svars = patterns(2, fix_zero=True)        # sigma_11: pairs, (0,0) fixed
    lvars = []                                # lambda: monomials of degree <= 2
    for deg in range(0, 3):
        lvars.extend(patterns(deg))

    nR, nG, nS, nL = len(rows), len(gvars), len(svars), len(lvars)

    A0 = [[pzero() for _ in range(nG)] for _ in range(nR)]
    for j, gv in enumerate(gvars):
        A0[row_index[gv]][j] = ordered_pair_orbit_poly(gv, False)

    A1c = [[pzero() for _ in range(nS)] for _ in range(nR)]
    A1l = [[pzero() for _ in range(nS)] for _ in range(nR)]
    n2 = [F(0), F(0), F(1)]                   # the polynomial n^2
    for j, sv in enumerate(svars):
        sz = pmul(ordered_pair_orbit_poly(sv, True), n2)
        A1c[row_index[canon(sv)]][j] = sz
        A1l[row_index[canon(tuple(sv) + ((0, 0),))]][j] = sz

    A2 = [[pzero() for _ in range(nL)] for _ in range(nR)]
    for j, lv in enumerate(lvars):
        sz = orbit_size_poly(lv, False)
        for key, cnt in _extend_counts(lv).items():
            A2[row_index[key]][j] = padd(A2[row_index[key]][j], pmul(sz, cnt))

    # right-hand side: |orbit| * coefficient, the latter in closed form
    def rhs_at(n):
        return [peval(orbit_size_poly(r, False), n) * coef_F(r, n, k)
                for r in rows]

    return dict(rows=rows, gvars=gvars, svars=svars, lvars=lvars,
                A0=A0, A1c=A1c, A1l=A1l, A2=A2, rhs_at=rhs_at,
                row_index=row_index)


def _extend_counts(mu):
    """
    For a representative monomial `mu` (at most 2 cells), classify every cell p of
    the grid by the canonical key of mu + {p}, and return {key: count-polynomial}.

    A cell p = (a,b) is described by whether a is one of mu's rows or a NEW row,
    and likewise for b.  There is 1 choice for each specific row, and
    (n - |rows(mu)|) choices for a new one; the canonical key depends only on the
    case, so each case contributes a product of two linear counts.  Degree <= 2.
    """
    rows = sorted({r for r, _ in mu})
    cols = sorted({c for _, c in mu})
    newr, newc = (max(rows) + 1 if rows else 0), (max(cols) + 1 if cols else 0)
    out = {}
    row_opts = [(r, [F(1)]) for r in rows] + [(newr, [F(-len(rows)), F(1)])]
    col_opts = [(c, [F(1)]) for c in cols] + [(newc, [F(-len(cols)), F(1)])]
    for a, ca in row_opts:
        for b, cb in col_opts:
            key = canon(tuple(mu) + ((a, b),))
            out[key] = padd(out.get(key, pzero()), pmul(ca, cb))
    return out


def check_system(ns=(4, 5, 6), k=3):
    """
    Cross-check the symbolic system against exact_system(build_sdp(...)), which is
    the code path that produced the already-verified certificates.  The two share
    no logic: one counts orbits by union-find over every monomial, the other
    evaluates closed forms.
    """
    from sos import build_sdp
    from exactsd import exact_system
    import expand
    ok = True
    sym = build_symbolic_system(k)
    for n in ns:
        d = build_sdp(n, k, 1, verbose=False)
        A0, A1c, A1l, A2, rhs = exact_system(d)
        B = d["B"]
        basis = d["basis"]

        # map the trusted path's indices onto canonical keys
        inv_row = {}
        for mono, r in d["orbit_of"].items():
            inv_row.setdefault(r, mono)
        rmap = {r: canon(cells_of(m, n)) for r, m in inv_row.items()}

        def pair_key(orb, fix):
            code = orb[0]
            u, v = divmod(code, B)
            return canon(cells_of(basis[u] + basis[v], n), fix)

        gmap = {j: pair_key(o, False) for j, o in enumerate(d["g_orbits"])}
        smap = {j: pair_key(o, True) for j, o in enumerate(d["s_orbits"])}
        from symmetry import monomials as _mons
        lam_mons = _mons(n * n, d["TOPDEG"] - 1)
        lmap = {j: canon(cells_of(lam_mons[m[0]], n))
                for j, m in enumerate(d["lam_orbit_reps"])}

        bad = 0
        for r_i, key_r in rmap.items():
            R = sym["row_index"][key_r]
            for j, key_g in gmap.items():
                want = F(A0[r_i][j])
                have = peval(sym["A0"][R][sym["gvars"].index(key_g)], n)
                if want != have:
                    bad += 1
            for j, key_s in smap.items():
                J = sym["svars"].index(key_s)
                if F(A1c[r_i][j]) != peval(sym["A1c"][R][J], n):
                    bad += 1
                if F(A1l[r_i][j]) != peval(sym["A1l"][R][J], n):
                    bad += 1
            for j, key_l in lmap.items():
                want = F(A2[r_i][j])
                have = peval(sym["A2"][R][sym["lvars"].index(key_l)], n)
                if want != have:
                    bad += 1
        rr = sym["rhs_at"](n)
        for r_i, key_r in rmap.items():
            if rhs[r_i] != rr[sym["row_index"][key_r]]:
                bad += 1
        print(f"  n={n}: symbolic system vs exact_system -> {bad} mismatches "
              f"over {len(rmap)} rows x {len(gmap)+2*len(smap)+len(lmap)+1} entries")
        ok = ok and bad == 0
    return ok


# ------------------------------------------------- rational functions of n over Q
def pdivmod(a, b):
    a = list(a)
    q = [F(0)] * max(1, len(a) - len(b) + 1)
    while len(a) >= len(b) and any(a):
        da = len(ptrim(a)) - 1
        if da < len(b) - 1:
            break
        f = a[da] / b[-1]
        s = da - (len(b) - 1)
        q[s] += f
        for i, c in enumerate(b):
            a[i + s] -= f * c
        a = ptrim(a)
        if not a:
            break
    return ptrim(q), ptrim(list(a))


def pgcd(a, b):
    a, b = ptrim(list(a)), ptrim(list(b))
    while b:
        _, r = pdivmod(a, b)
        a, b = b, r
    if a:
        a = pscale(a, F(1) / a[-1])          # monic
    return a


class RF:
    """An exact rational function in n over Q, kept in lowest terms."""

    __slots__ = ("num", "den")

    def __init__(self, num, den=None):
        num = ptrim(list(num))
        den = ptrim(list(den)) if den is not None else [F(1)]
        if not den:
            raise ZeroDivisionError("zero denominator")
        if not num:
            self.num, self.den = [], [F(1)]
            return
        g = pgcd(num, den)
        if g and len(g) > 1:
            num, _ = pdivmod(num, g)
            den, _ = pdivmod(den, g)
        lead = den[-1]
        self.num = pscale(num, F(1) / lead)
        self.den = pscale(den, F(1) / lead)

    @staticmethod
    def const(c):
        return RF([F(c)] if c else [])

    def __add__(self, o):
        return RF(padd(pmul(self.num, o.den), pmul(o.num, self.den)),
                  pmul(self.den, o.den))

    def __sub__(self, o):
        return self + RF(pscale(o.num, F(-1)), o.den)

    def __mul__(self, o):
        return RF(pmul(self.num, o.num), pmul(self.den, o.den))

    def __truediv__(self, o):
        if not o.num:
            raise ZeroDivisionError
        return RF(pmul(self.num, o.den), pmul(self.den, o.num))

    def __bool__(self):
        return bool(self.num)

    def __eq__(self, o):
        return self.num == o.num and self.den == o.den

    def at(self, n):
        d = peval(self.den, n)
        if d == 0:
            raise ZeroDivisionError(f"denominator vanishes at n={n}")
        return peval(self.num, n) / d

    def __repr__(self):
        if self.den == [F(1)]:
            return f"({pstr(self.num)})"
        return f"({pstr(self.num)}) / ({pstr(self.den)})"


def solve_symbolic(k=3, verbose=True):
    """
    Solve A0 x + (A1c/n + A1l) y + A2 z = rhs over the field Q(n).

    12 equations, 19 unknowns, rank 11 -- so an 8-dimensional solution space over
    Q(n).  We row-reduce exactly and return the general solution: each pivot
    variable as an exact rational function of n plus a Q(n)-linear combination of
    the free variables.
    """
    sym = build_symbolic_system(k)
    rows, gvars, svars, lvars = (sym["rows"], sym["gvars"], sym["svars"],
                                 sym["lvars"])
    nR = len(rows)
    ncol = len(gvars) + len(svars) + len(lvars)

    n_poly = [F(0), F(1)]
    M = []
    for r in range(nR):
        row = [RF(p) for p in sym["A0"][r]]
        row += [RF(sym["A1c"][r][j], n_poly) + RF(sym["A1l"][r][j])
                for j in range(len(svars))]
        row += [RF(p) for p in sym["A2"][r]]
        M.append(row)

    # right-hand side: |orbit| * coef_F, as an exact rational function of n.
    rhs = [_rhs_rf(rows[r], k) for r in range(nR)]

    # exact Gauss-Jordan over Q(n)
    piv_cols, r = [], 0
    A = [row[:] for row in M]
    b = rhs[:]
    for c in range(ncol):
        p = next((i for i in range(r, nR) if A[i][c]), None)
        if p is None:
            continue
        A[r], A[p] = A[p], A[r]
        b[r], b[p] = b[p], b[r]
        pv = A[r][c]
        A[r] = [v / pv for v in A[r]]
        b[r] = b[r] / pv
        for i in range(nR):
            if i != r and A[i][c]:
                f = A[i][c]
                A[i] = [A[i][j] - f * A[r][j] for j in range(ncol)]
                b[i] = b[i] - f * b[r]
        piv_cols.append(c)
        r += 1
        if r == nR:
            break
    rank = r
    dependent = [i for i in range(rank, nR)]
    consistent = all(not b[i] for i in dependent)
    free_cols = [c for c in range(ncol) if c not in piv_cols]

    if verbose:
        print(f"  equations {nR}, unknowns {ncol}, rank over Q(n) = {rank}")
        print(f"  dependent rows {len(dependent)}, consistent over Q(n): "
              f"{consistent}")
        print(f"  free variables: {len(free_cols)}")
    return dict(A=A, b=b, piv_cols=piv_cols, free_cols=free_cols, rank=rank,
                consistent=consistent, sym=sym, ncol=ncol)


def _rhs_rf(rowkey, k=3):
    """|orbit(rowkey)| * [coefficient of that monomial in F], as an element of
    Q(n).  Both factors are closed forms, so this is exact for all n."""
    size = orbit_size_poly(rowkey, False)
    d = len(rowkey)
    if d == 0 or d > k:
        return RF([])
    rows = [r for r, _ in rowkey]
    cols = [c for _, c in rowkey]
    dr = len(set(rows)) == d
    dc = len(set(cols)) == d
    # C(n,k) and C(n-d,k-d) as polynomials in n
    cnk = _binom_poly(k, 0)
    cndk = _binom_poly(k - d, d)
    term = RF([])
    if dr:
        term = term + RF(cndk, cnk)
    if dc:
        term = term + RF(cndk, cnk)
    if dr and dc:
        npow = [F(0)] * (k - d) + [F(1)]
        term = term - (RF(pmul(cndk, cndk), pmul(cnk, cnk))
                       * RF([F(factorial(k - d))]) / RF(npow))
    return RF([]) - RF(size) * term


def _binom_poly(j, shift):
    """C(n-shift, j) as a polynomial in n."""
    p = [F(1)]
    for i in range(j):
        p = pmul(p, [F(-shift - i), F(1)])
    return pscale(p, F(1, factorial(j))) if j else [F(1)]


if __name__ == "__main__":
    print("=== closed-form coefficient check ===")
    ok1 = check_coef_F()
    print()
    print("=== closed-form orbit-size check ===")
    ok2 = check_orbit_sizes()
    print()
    print("PASS" if (ok1 and ok2) else "FAIL")
    sys.exit(0 if (ok1 and ok2) else 1)
