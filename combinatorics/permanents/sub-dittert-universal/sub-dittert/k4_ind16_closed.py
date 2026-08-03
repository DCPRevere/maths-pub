"""
The 16 x 16 Ind(V'|1) block in CLOSED FORM in n -- derived, not interpolated.

`k4_ind16.py` realises the 6b.24 basis at a concrete n and a concrete sum-zero
w, and its three obligations show the realisation is right.  What the Q(n)
design needs is the block as a form in the 356 sigma_11 variables with
coefficients POLYNOMIAL IN n, like the trivial (6b.17) and sign (6b.21) blocks.
This file derives them.

THE DERIVATION.  Write each shape as a TEMPLATE: a multiset of at most two cells
whose row entry is either the fixed row `0` or a free label (`i`, the w-carrying
row, and possibly `k`), and whose column entry is either the fixed column `0` or
a free label (`a`, possibly `b`).  The shape vector is the sum over all
assignments of DISTINCT values in 1..n-1 to the free labels, weighted by
w_{value of i}.  That is exactly the enumeration in 6b.24, and `realise` below
reproduces the explicit loops of k4_ind16.shape_vectors from the templates
alone, which is checked rather than assumed.

Now fix shapes s and t.  For an assignment pair (phi_s, phi_t) the pair class of
(u, v) depends ONLY on which of s's free labels take the same value as which of
t's -- a partial injection mu on the row labels and nu on the column labels
(within one shape the labels are distinct by construction, so nothing merges
there).  Each (mu, nu) fixes the class, and the weighted number of assignments
realising it is a product of falling factorials:

    R = |S_r| + |T_r| - |mu|   row groups,  C = |S_c| + |T_c| - |nu|   column groups

    s.i and t.i in the SAME group:  sum_v w_v^2 * [n-2]_{R-1} = q(w) [n-2]_{R-1}
    in DIFFERENT groups:  sum_{v != v'} w_v w_v' * [n-3]_{R-2} = -q(w) [n-3]_{R-2}

the second line by SUM-ZEROness alone -- (sum w)^2 = 0 gives
sum_{v != v'} w_v w_v' = -sum_v w_v^2.  Columns carry no weight and contribute
[n-1]_C.  So every contribution is +-q(w) times a product of two falling
factorials, q(w) divides out, and

    Ntilde^{st}_c(n) = sum over (mu, nu) of class c of  eps * frow * [n-1]_C

with eps = +1, frow = [n-2]_{R-1} when the two i-labels merge and eps = -1,
frow = [n-3]_{R-2} when they do not.  Degree at most (R-1) + C <= 7.

WHY THERE IS NO |Aut| DIVISOR HERE, unlike 6b.16/6b.17.  There the count went
through canonical templates with a dedup, so the falling factorials
overcounted by the label-symmetry group.  Here the shape vector is DEFINED as a
sum over assignments, and the enumeration is over assignments too -- a monomial
that two assignments produce (C5 gives b_ia b_kb the coefficient w_i + w_k)
is meant to be counted twice.  Nothing is deduplicated, so nothing is divided.

VERIFICATION: against `k4_ind16`'s concrete-n block, class by class, at n = 5
and n = 6 -- the folder standard.  The two routes share only the shape
definitions: this one enumerates abstract merge patterns, that one sums over
every pair in the supports with the class read off a B x B table.
"""

import itertools
import os
import sys
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "dittert"))
sys.path.insert(0, HERE)
import k4_ind16 as ind16                                          # noqa: E402
import k4_system as k4                                            # noqa: E402
from general_k3 import falling, padd, peval, pmul, pstr, pzero    # noqa: E402
from k4_blocks import _shift_by                                   # noqa: E402

NSHAPE = 16

# The 16 shapes of 6b.24 as templates.  The ORDER must match
# k4_ind16.shape_vectors; `check_templates` enforces that by comparing the
# realised vectors, not by trusting the listing.
TEMPLATES = [
    ("D1", (("i", "0"),)),
    ("D2", (("i", "a"),)),
    ("A1", (("i", "0"), ("0", "0"))),
    ("A2", (("i", "a"), ("0", "0"))),
    ("A3", (("i", "0"), ("0", "b"))),
    ("A4", (("i", "a"), ("0", "a"))),
    ("A5", (("i", "a"), ("0", "b"))),
    ("B1", (("i", "0"), ("i", "0"))),
    ("B2", (("i", "0"), ("i", "a"))),
    ("B3", (("i", "a"), ("i", "a"))),
    ("B4", (("i", "a"), ("i", "b"))),
    ("C1", (("i", "0"), ("k", "0"))),
    ("C2", (("i", "a"), ("k", "0"))),
    ("C3", (("i", "0"), ("k", "b"))),
    ("C4", (("i", "a"), ("k", "a"))),
    ("C5", (("i", "a"), ("k", "b"))),
]


def free_labels(cells):
    rows = sorted({r for r, _ in cells if r != "0"})
    cols = sorted({c for _, c in cells if c != "0"})
    return rows, cols


def realise(cells, n, w):
    """The shape vector from the template alone: {monomial: coefficient}."""
    rows, cols = free_labels(cells)
    d = {}
    for rv in itertools.permutations(range(1, n), len(rows)):
        rmap = dict(zip(rows, rv))
        rmap["0"] = 0
        for cv in itertools.permutations(range(1, n), len(cols)):
            cmap = dict(zip(cols, cv))
            cmap["0"] = 0
            m = tuple(sorted(rmap[r] * n + cmap[c] for r, c in cells))
            d[m] = d.get(m, 0) + w[rmap["i"] - 1]
    return {m: c for m, c in d.items() if c}


def check_templates(n, w):
    """Templates vs the explicit loops of k4_ind16.shape_vectors."""
    explicit = ind16.shape_vectors(n, w)
    bad, names = 0, []
    for s, (name, cells) in enumerate(TEMPLATES):
        got = realise(cells, n, w)
        want = {m: c for m, c in explicit[s][1].items() if c}
        if got != want:
            bad += 1
            names.append(f"{name}/{explicit[s][0].split()[0]}")
    return bad, names


def partial_injections(S, T):
    """Every partial injection from list S into list T, as a dict."""
    out = []
    for r in range(min(len(S), len(T)) + 1):
        for sub in itertools.combinations(S, r):
            for tgt in itertools.permutations(T, r):
                out.append(dict(zip(sub, tgt)))
    return out


def _groups(S, T, mu):
    """Group id per label of s and of t, merging along mu.  Returns (gs, gt, N)."""
    gs = {lab: t for t, lab in enumerate(S)}
    inv = {v: k for k, v in mu.items()}
    gt, nxt = {}, len(S)
    for lab in T:
        if lab in inv:
            gt[lab] = gs[inv[lab]]
        else:
            gt[lab] = nxt
            nxt += 1
    return gs, gt, nxt


def block_closed(sidx):
    """
    Ntilde[s][t] = {class index: polynomial in n}: the 16 x 16 as a form in the
    sigma_11 variables, closed form in n.
    """
    N = [[dict() for _ in range(NSHAPE)] for _ in range(NSHAPE)]
    for s, (_, cs) in enumerate(TEMPLATES):
        Sr, Sc = free_labels(cs)
        for t, (_, ct) in enumerate(TEMPLATES):
            Tr, Tc = free_labels(ct)
            acc = {}
            for mu in partial_injections(Sr, Tr):
                grs, grt, R = _groups(Sr, Tr, mu)
                same = grs["i"] == grt["i"]
                if same:
                    frow = _shift_by(falling(R - 1), 1)        # [n-2]_{R-1}
                    eps = 1
                else:
                    frow = _shift_by(falling(R - 2), 2)        # [n-3]_{R-2}
                    eps = -1
                for nu in partial_injections(Sc, Tc):
                    gcs, gct, C = _groups(Sc, Tc, nu)
                    u = tuple(sorted((0 if r == "0" else grs[r] + 1,
                                      0 if c == "0" else gcs[c] + 1)
                                     for r, c in cs))
                    v = tuple(sorted((0 if r == "0" else grt[r] + 1,
                                      0 if c == "0" else gct[c] + 1)
                                     for r, c in ct))
                    key = sidx[k4.canon_pair(u, v, True)]
                    term = pmul(frow, _shift_by(falling(C), 0))   # x [n-1]_C
                    if eps < 0:
                        term = [-x for x in term]
                    acc[key] = padd(acc.get(key, pzero()), term)
            N[s][t] = {c: p for c, p in acc.items() if p}
    return N


def verify(ns=(5, 6)):
    """Closed form vs k4_ind16's concrete-n block, class by class."""
    svars = ind16.svars_cached()
    sidx = {k: i for i, k in enumerate(svars)}
    Nc = block_closed(sidx)
    used = set()
    for s in range(NSHAPE):
        for t in range(NSHAPE):
            used |= set(Nc[s][t])
    degs = [len(p) - 1 for s in range(NSHAPE) for t in range(NSHAPE)
            for p in Nc[s][t].values()]
    print(f"closed form: {len(used)} of {len(svars)} sigma_11 classes occur, "
          f"polynomial degrees {min(degs)}..{max(degs)}")
    print(f"  symmetry Ntilde[s][t] == Ntilde[t][s]: "
          f"{all(Nc[s][t] == Nc[t][s] for s in range(NSHAPE) for t in range(NSHAPE))}")

    ok = True
    for n in ns:
        basis = k4.basis_of(n)
        B = len(basis)
        w = ind16.sum_zero(n, 20260729)
        q = sum(x * x for x in w)
        bad, names = check_templates(n, w)
        print(f"  n={n}: templates vs explicit shape loops -> "
              f"{bad} differing shapes of {NSHAPE} {names if names else ''}")
        E = ind16.as_index_vectors(n, ind16.shape_vectors(n, w), basis)
        cls, _ = ind16.direct_class_array(n, basis, sidx)
        Nn = ind16.block_by_class(E, cls, B)
        mism = 0
        first = []
        for s in range(NSHAPE):
            for t in range(NSHAPE):
                conc = {c: F(x, q) for c, x in Nn[s][t].items() if x}
                clsd = {c: peval(p, n) for c, p in Nc[s][t].items()}
                clsd = {c: x for c, x in clsd.items() if x}
                if conc != clsd:
                    mism += 1
                    if len(first) < 3:
                        kd = set(conc) ^ set(clsd)
                        vd = {c for c in set(conc) & set(clsd)
                              if conc[c] != clsd[c]}
                        first.append((TEMPLATES[s][0], TEMPLATES[t][0],
                                      len(kd), len(vd)))
        print(f"  n={n}: closed form vs concrete realisation -> {mism} "
              f"mismatched entries of {NSHAPE * NSHAPE}"
              + (f"   first: {first}" if first else ""))
        ok = ok and mism == 0
    return ok, Nc


if __name__ == "__main__":
    ns = [int(a) for a in sys.argv[1:]] or [5, 6]
    print("Ind(V'|1) 16 x 16 -- closed form in n\n")
    ok, Nc = verify(ns)
    print(f"\nclosed form verified: {ok}")
    if ok:
        print("\nsample entries (class index: polynomial):")
        for s, t in ((0, 0), (0, 11), (15, 15)):
            items = sorted(Nc[s][t].items())[:3]
            print(f"  [{TEMPLATES[s][0]}][{TEMPLATES[t][0]}]  "
                  f"{len(Nc[s][t])} classes; " +
                  "; ".join(f"c{c}: {pstr(p)}" for c, p in items))
