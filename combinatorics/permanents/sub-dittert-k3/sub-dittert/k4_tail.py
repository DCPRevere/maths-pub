"""
The last six blocks of §6b.15 -- the ones whose weights are two-index arrays.

    Ind(1|(m-2,2))          4x4      Ind(V'|(m-2,2))         3x3
    Ind(V'|(m-2,1,1))       2x2      Ind(1|(m-2,1,1))        1x1
    ((m-2,2)|(m-2,2)) ext + 1x1      ((m-2,1,1)|(m-2,1,1)) ext + 1x1

Designed in NOTES §6b.31.  With `m = n - 1`, the row/column module is
`R^m = 1 + V'`, and the two degree-2 partitions are the ROW-SUM KERNELS inside
the two-index arrays:

    S^(m-2,2)    symmetric,  zero diagonal, sum_b W_ab = 0 for every a
    S^(m-2,1,1)  antisymmetric,             sum_b W_ab = 0 for every a

That trace condition replaces sum-zeroness, and it is what makes the counts come
out: a free label summed against a two-index weight contributes `sum_b W_ab = 0`
and kills the shape.

WEIGHT TYPES, as used below:
    triv   no weight; the label is merely summed
    vec    V':  weight w_{val(i)},           needs label i
    sym    S^(m-2,2):  weight W_{val(i),val(k)},  needs i and k
    asym   S^(m-2,1,1): the same, antisymmetric

THE COUNT IS MEASURED.  Candidate templates are enumerated generously, realised
at concrete rational weights, and a greedy maximal INDEPENDENT SUBSET is taken
-- of templates, not of combinations, so a closed form still applies term by
term.  The rank must equal the multiplicity that `k4_chars.py` derived from a
character sum, and the templates that drop out must be the ones §6b.31 predicts
vanish or coincide.  Which ones dropped is reported.
"""

import itertools
import os
import sys
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "dittert"))
sys.path.insert(0, HERE)
import k4_ind16 as i16                                            # noqa: E402
import k4_system as k4                                            # noqa: E402
import k4_vv14 as vv                                              # noqa: E402

# name -> (row weight type, column weight type, predicted multiplicity,
#          irrep dimension as a function of n)
BLOCKS = [
    ("Ind(1|(m-2,2))",      "triv", "sym",  4,
     lambda n: (n - 1) * (n - 4)),
    ("Ind(V'|(m-2,2))",     "vec",  "sym",  3,
     lambda n: (n - 2) * (n - 1) * (n - 4)),
    ("Ind(V'|(m-2,1,1))",   "vec",  "asym", 2,
     lambda n: (n - 2) ** 2 * (n - 3)),
    ("Ind(1|(m-2,1,1))",    "triv", "asym", 1,
     lambda n: (n - 2) * (n - 3)),
    ("((m-2,2)|(m-2,2))+",  "sym",  "sym",  1,
     lambda n: ((n - 1) * (n - 4) // 2) ** 2),
    ("((m-2,1,1)|(m-2,1,1))+", "asym", "asym", 1,
     lambda n: ((n - 2) * (n - 3) // 2) ** 2),
]

# Labels a weight type requires.  Rows and columns need SEPARATE tables: the
# row labels are i, k and the column labels are a, b.  Sharing one table made
# every candidate list empty, which is how it was caught.
NEED_ROW = {"triv": (), "vec": ("i",), "sym": ("i", "k"), "asym": ("i", "k")}
NEED_COL = {"triv": (), "vec": ("a",), "sym": ("a", "b"), "asym": ("a", "b")}


# ------------------------------------------------------------------- weights
def _nullspace(rows, ncol):
    """Exact basis of {x : rows . x = 0}, as a list of Fraction vectors."""
    A = [list(map(F, r)) for r in rows]
    piv, r = [], 0
    for c in range(ncol):
        p = next((i for i in range(r, len(A)) if A[i][c]), None)
        if p is None:
            continue
        A[r], A[p] = A[p], A[r]
        inv = A[r][c]
        A[r] = [x / inv for x in A[r]]
        for i in range(len(A)):
            if i != r and A[i][c]:
                f = A[i][c]
                A[i] = [A[i][j] - f * A[r][j] for j in range(ncol)]
        piv.append(c)
        r += 1
        if r == len(A):
            break
    freec = [c for c in range(ncol) if c not in piv]
    basis = []
    for fc in freec:
        v = [F(0)] * ncol
        v[fc] = F(1)
        for i, pc in enumerate(piv):
            v[pc] = -A[i][fc]
        basis.append(v)
    return basis


def two_index_weight(m, anti, seed):
    """
    A generic rational element of S^(m-2,1,1) (anti) or S^(m-2,2) (sym), as a
    dict {(a,b): value} on 1..m, built as a random combination of an EXACT
    basis of the row-sum kernel.  Returns (W, dim).
    """
    import random
    idx, pos = [], {}
    for a in range(1, m + 1):
        for b in range(a + 1, m + 1):
            pos[(a, b)] = len(idx)
            idx.append((a, b))
    rows = []
    for a in range(1, m + 1):                    # sum_b W_ab = 0
        r = [0] * len(idx)
        for b in range(1, m + 1):
            if b == a:
                continue
            key = (min(a, b), max(a, b))
            sgn = 1 if (not anti or a < b) else -1
            r[pos[key]] += sgn
        rows.append(r)
    basis = _nullspace(rows, len(idx))
    rng = random.Random(seed)
    coef = [rng.randint(-6, 6) for _ in basis]
    if not any(coef):
        coef[0] = 1
    vec = [sum(c * b[t] for c, b in zip(coef, basis)) for t in range(len(idx))]
    den = 1
    for x in vec:
        den = den * x.denominator // __import__("math").gcd(den, x.denominator)
    vec = [int(x * den) for x in vec]
    W = {}
    for (a, b), v in zip(idx, vec):
        W[(a, b)] = v
        W[(b, a)] = -v if anti else v
    for a in range(1, m + 1):
        W[(a, a)] = 0
    return W, len(basis)


def wnorm(kind, w, m):
    if kind == "triv":
        return 1
    if kind == "vec":
        return sum(x * x for x in w)
    return sum(w[(a, b)] ** 2 for a in range(1, m + 1) for b in range(1, m + 1))


# ------------------------------------------------------------------ templates
def candidates(rowtype, coltype):
    """Every template using the labels its weights require."""
    cells = [(r, c) for r in ("0", "i", "k") for c in ("0", "a", "b")]
    out = []
    for deg in (1, 2):
        for combo in itertools.combinations_with_replacement(cells, deg):
            rl = {r for r, _ in combo}
            cl = {c for _, c in combo}
            if "k" in rl and "i" not in rl:
                continue
            if "b" in cl and "a" not in cl:
                continue
            if any(x not in rl for x in NEED_ROW[rowtype]):
                continue
            if any(x not in cl for x in NEED_COL[coltype]):
                continue
            out.append(tuple(sorted(combo)))
    return sorted(set(out))


def realise(cells, n, rowtype, coltype, wrow, wcol):
    rows = [x for x in ("i", "k") if any(r == x for r, _ in cells)]
    cols = [x for x in ("a", "b") if any(c == x for _, c in cells)]
    d = {}
    for rv in itertools.permutations(range(1, n), len(rows)):
        rmap = dict(zip(rows, rv))
        rmap["0"] = 0
        if rowtype == "triv":
            rf = 1
        elif rowtype == "vec":
            rf = wrow[rmap["i"] - 1]
        else:
            rf = wrow[(rmap["i"], rmap["k"])]
        if rf == 0:
            continue
        for cv in itertools.permutations(range(1, n), len(cols)):
            cmap = dict(zip(cols, cv))
            cmap["0"] = 0
            if coltype == "triv":
                cf = 1
            elif coltype == "vec":
                cf = wcol[cmap["a"] - 1]
            else:
                cf = wcol[(cmap["a"], cmap["b"])]
            if cf == 0:
                continue
            mono = tuple(sorted(rmap[r] * n + cmap[c] for r, c in cells))
            d[mono] = d.get(mono, 0) + rf * cf
    return {mo: c for mo, c in d.items() if c}


def independent_subset(vectors):
    """Greedy maximal independent subset; returns (kept indices, dropped, zero)."""
    rowsred = []            # reduced echelon rows, as dicts
    kept, dropped, zero = [], [], []
    for t, v in enumerate(vectors):
        if not v:
            zero.append(t)
            continue
        cur = dict(v)
        for piv, row in rowsred:
            if piv in cur and cur[piv]:
                f = F(cur[piv], row[piv])
                for k2, x in row.items():
                    cur[k2] = cur.get(k2, 0) - f * x
                cur = {k2: x for k2, x in cur.items() if x}
        if not cur:
            dropped.append(t)
            continue
        piv = min(cur)
        rowsred.append((piv, cur))
        kept.append(t)
    return kept, dropped, zero


# -------------------------------------------------------------------- driver
def run_block(name, rowtype, coltype, mult, dimf, n, basis, sidx, cls_uf,
              cls_dir, y, seed=20260729):
    B = len(basis)
    m = n - 1

    def weights(s):
        if rowtype == "triv":
            wr = None
        elif rowtype == "vec":
            wr = i16.sum_zero(n, s)
        else:
            wr, _ = two_index_weight(m, rowtype == "asym", s)
        if coltype == "triv":
            wc = None
        elif coltype == "vec":
            wc = i16.sum_zero(n, s + 57)
        else:
            wc, _ = two_index_weight(m, coltype == "asym", s + 57)
        return wr, wc

    wr, wc = weights(seed)
    cand = candidates(rowtype, coltype)
    vecs = [realise(c, n, rowtype, coltype, wr, wc) for c in cand]
    kept, dropped, zero = independent_subset(vecs)
    print(f"\n  --- {name}  (predicted multiplicity {mult}, "
          f"irrep dimension {dimf(n)}) ---")
    print(f"    candidates {len(cand)}: {len(kept)} independent, "
          f"{len(dropped)} dependent, {len(zero)} identically zero")
    print(f"    measured multiplicity {len(kept)}  -> matches: {len(kept) == mult}")
    if zero:
        print(f"    vanished: {[_fmt(cand[t]) for t in zero]}")
    if dropped:
        print(f"    dependent: {[_fmt(cand[t]) for t in dropped]}")
    print(f"    kept: {[_fmt(cand[t]) for t in kept]}")
    if len(kept) != mult:
        return dict(name=name, ok=False)

    index = {mo: t for t, mo in enumerate(basis)}
    E = [{index[mo]: c for mo, c in vecs[t].items()} for t in kept]
    ns = len(E)

    M_A = vv.contract(vv.block_by_class(E, cls_uf, B), y)
    M_B = vv.block_dense(E, cls_dir, B, y)
    mism = sum(1 for s in range(ns) for t in range(ns) if M_A[s][t] != M_B[s][t])
    print(f"    OBLIGATION 1: route A vs route B -> {mism} mismatched of "
          f"{ns * ns}")

    wr2, wc2 = weights(seed + 909)
    E2 = [{index[mo]: c for mo, c in
           realise(cand[t], n, rowtype, coltype, wr2, wc2).items()}
          for t in kept]
    M2 = vv.contract(vv.block_by_class(E2, cls_uf, B), y)
    ratios = set()
    for s in range(ns):
        for t in range(ns):
            if M_A[s][t]:
                ratios.add(F(M2[s][t], M_A[s][t]))
            elif M2[s][t]:
                ratios.add("INF")
    n1 = wnorm(rowtype, wr, m) * wnorm(coltype, wc, m)
    n2 = wnorm(rowtype, wr2, m) * wnorm(coltype, wc2, m)
    print(f"    OBLIGATION 2: {len(ratios)} distinct ratio(s) "
          f"{sorted(ratios, key=str)[:2]};  predicted {F(n2, n1)}")

    return dict(name=name, ok=(mism == 0 and ratios == {F(n2, n1)}),
                E=E, M=M_A, kept=[cand[t] for t in kept], dim=dimf(n))


def _fmt(cells):
    return "".join(f"({r}{c})" for r, c in cells)


def check_J(n, basis, name, rowtype, coltype, seed=20260729):
    """
    §6b.29's involution on the single shape of a (mu|mu) block.

    k4_chars puts BOTH such blocks in the `+` extension, so `J = +1` is a
    two-valued prediction on a one-dimensional space.  The lead's instruction
    was to verify the transfer rather than assume it, so `J` is applied here in
    exactly its §6b.29 form: push the shape realised at the SWAPPED weights
    through P_tau and compare with the shape at the original weights.
    """
    m = n - 1
    W, _ = two_index_weight(m, rowtype == "asym", seed)
    Z, _ = two_index_weight(m, coltype == "asym", seed + 57)
    cand = candidates(rowtype, coltype)
    here = [realise(c, n, rowtype, coltype, W, Z) for c in cand]
    kept, _, _ = independent_subset(here)
    t = kept[0]
    # e_s(Z (x) W): the row weight becomes Z and the column weight W, which
    # is only meaningful because the two types coincide for a (mu|mu) block.
    swapped = realise(cand[t], n, rowtype, coltype, Z, W)
    gtr = tuple((p % n) * n + (p // n) for p in range(n * n))
    perm = i16.basis_perm(basis, gtr)
    index = {mo: q for q, mo in enumerate(basis)}
    img = i16.pushforward({index[mo]: c for mo, c in swapped.items()}, perm)
    base = {index[mo]: c for mo, c in here[t].items()}
    if img == base:
        verdict = "+1"
    elif img == {k2: -v for k2, v in base.items()}:
        verdict = "-1"
    else:
        verdict = "NEITHER (J is not scalar on this shape)"
    print(f"    J on {name}: {verdict}   (predicted +1 by the character sum)")
    return verdict


if __name__ == "__main__":
    args = sys.argv[1:]
    spectrum = "--no-spectrum" not in args
    ns = [int(a) for a in args if not a.startswith("-")] or [5, 6]
    print("The last six blocks of §6b.15 -- NOTES §6b.31")
    print("PREDICTED multiplicities 4, 3, 2, 1, 1, 1; the three vanishing "
          "mechanisms; J = +1 on both (mu|mu) shapes.")
    svars = i16.svars_cached()
    sidx = {k: i for i, k in enumerate(svars)}
    import random
    for n in ns:
        basis = k4.basis_of(n)
        B = len(basis)
        print(f"\n=== n = {n}:  B = {B} ===")
        cls_uf, _ = i16.unionfind_class_array(n, basis, sidx)
        cls_dir, _ = i16.direct_class_array(n, basis, sidx)
        diff = sum(1 for t in range(B * B) if cls_uf[t] != cls_dir[t])
        print(f"  class arrays: {diff} differing entries of {B * B}")
        rng = random.Random(4242)
        y = [rng.randint(-40, 40) or 7 for _ in range(len(svars))]
        res = []
        for name, rt, ct, mult, dimf in BLOCKS:
            res.append(run_block(name, rt, ct, mult, dimf, n, basis, sidx,
                                 cls_uf, cls_dir, y))
            if rt == ct and rt in ("sym", "asym"):
                check_J(n, basis, name, rt, ct)
        if spectrum:
            import numpy as np
            yv = np.array(y, dtype=float)
            ca = np.frombuffer(cls_dir, dtype=np.int32).reshape(B, B)
            spec = np.sort(np.linalg.eigvalsh(yv[ca]))
            scale = max(abs(spec[0]), abs(spec[-1]))
            tol = 1e-7 * scale
            print("\n  OBLIGATION 3: multiplicity in spec(H)")
            covered = 0
            for r in res:
                if not r.get("ok"):
                    print(f"    {r['name']}: skipped (block not accepted)")
                    continue
                E, M = r["E"], r["M"]
                G = vv.gram(E)
                Mf = np.array([[float(x) for x in row] for row in M])
                Gf = np.array([[float(x) for x in row] for row in G])
                L = np.linalg.cholesky(Gf)
                C1 = np.linalg.solve(L, Mf)
                Cm = np.linalg.solve(L, C1.T).T
                ge = np.linalg.eigvalsh(0.5 * (Cm + Cm.T))
                c = [int(np.sum(np.abs(spec - mu) < tol)) for mu in ge]
                covered += sum(c)
                print(f"    {r['name']:24s} {sorted(c)}  predicted "
                      f"{r['dim']}  -> "
                      f"{sum(1 for x in c if x == r['dim'])} of {len(c)} agree")
            print(f"    these six cover {covered} of {B}")
