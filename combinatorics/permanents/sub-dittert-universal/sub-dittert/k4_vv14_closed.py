"""
The `(V'|V')` 14 x 14 in CLOSED FORM in n, and the 10x10 / 4x4 that split off it.

§6b.26's merge-pattern derivation extends with one change: BOTH sides now carry
a sum-zero weight, so both get the sum-zero identity rather than just the rows.
For shapes `s, t` and a pair of partial injections `mu` (rows), `nu` (columns),
with `R` and `C` the resulting group counts,

    rows:  s.i and t.i in the SAME group -> +[n-2]_{R-1},  else -> -[n-3]_{R-2}
    cols:  s.a and t.a in the SAME group -> +[n-2]_{C-1},  else -> -[n-3]_{C-2}

and the contribution is the PRODUCT, signs included.  `q(w) q(z)` divides out of
every term, exactly as `q(w)` did in §6b.26.

DEGREE, predicted before running: `|S_r|, |T_r| <= 2` so `R <= 4`, and merging
the two `i` labels costs at least one, so the merged branch has `R <= 3`.  Both
branches therefore give a row factor of degree at most 2, and likewise for the
columns -- so **every entry has degree at most 4**, one lower on each side than
§6b.26's 6, because there the columns were unweighted and could reach `[n-1]_4`.
"""

import os
import sys
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "dittert"))
sys.path.insert(0, HERE)
import k4_ind16 as i16                                            # noqa: E402
import k4_ind16_closed as c16                                     # noqa: E402
import k4_system as k4                                            # noqa: E402
import k4_vv14 as vv                                              # noqa: E402
from general_k3 import falling, padd, peval, pmul, pstr, pzero    # noqa: E402
from k4_blocks import _shift_by                                   # noqa: E402

NSHAPE = vv.NSHAPE


def _factor(same, D):
    """The row (or column) factor of a merge pattern, with its sign."""
    if same:
        return _shift_by(falling(D - 1), 1), 1            # +[n-2]_{D-1}
    return _shift_by(falling(D - 2), 2), -1               # -[n-3]_{D-2}


def block_closed(sidx):
    """Ntilde[s][t] = {class index: polynomial in n} for the 14 x 14."""
    N = [[dict() for _ in range(NSHAPE)] for _ in range(NSHAPE)]
    for s, (_, cs) in enumerate(vv.TEMPLATES):
        Sr, Sc = vv.free_labels(cs)
        for t, (_, ct) in enumerate(vv.TEMPLATES):
            Tr, Tc = vv.free_labels(ct)
            acc = {}
            for mu in c16.partial_injections(Sr, Tr):
                grs, grt, R = c16._groups(Sr, Tr, mu)
                frow, srow = _factor(grs["i"] == grt["i"], R)
                for nu in c16.partial_injections(Sc, Tc):
                    gcs, gct, C = c16._groups(Sc, Tc, nu)
                    fcol, scol = _factor(gcs["a"] == gct["a"], C)
                    u = tuple(sorted((0 if r == "0" else grs[r] + 1,
                                      0 if cc == "0" else gcs[cc] + 1)
                                     for r, cc in cs))
                    v = tuple(sorted((0 if r == "0" else grt[r] + 1,
                                      0 if cc == "0" else gct[cc] + 1)
                                     for r, cc in ct))
                    key = sidx[k4.canon_pair(u, v, True)]
                    term = pmul(frow, fcol)
                    if srow * scol < 0:
                        term = [-x for x in term]
                    acc[key] = padd(acc.get(key, pzero()), term)
            N[s][t] = {cl: p for cl, p in acc.items() if p}
    return N


def verify(ns=(5, 6)):
    svars = i16.svars_cached()
    sidx = {k: i for i, k in enumerate(svars)}
    Nc = block_closed(sidx)
    used = set()
    for s in range(NSHAPE):
        for t in range(NSHAPE):
            used |= set(Nc[s][t])
    degs = [len(p) - 1 for s in range(NSHAPE) for t in range(NSHAPE)
            for p in Nc[s][t].values()]
    print(f"closed form: {len(used)} of {len(svars)} sigma_11 classes occur, "
          f"polynomial degrees {min(degs)}..{max(degs)}  (predicted max 4)")
    print(f"  symmetry Ntilde[s][t] == Ntilde[t][s]: "
          f"{all(Nc[s][t] == Nc[t][s] for s in range(NSHAPE) for t in range(NSHAPE))}")

    ok = True
    for n in ns:
        basis = k4.basis_of(n)
        B = len(basis)
        w = i16.sum_zero(n, 20260729)
        z = i16.sum_zero(n, 20260729 + 101)
        q = sum(x * x for x in w) * sum(x * x for x in z)
        E = vv.shape_vectors(n, w, z, basis)
        cls, _ = i16.direct_class_array(n, basis, sidx)
        Nn = vv.block_by_class(E, cls, B)
        mism = 0
        for s in range(NSHAPE):
            for t in range(NSHAPE):
                conc = {cl: F(x, q) for cl, x in Nn[s][t].items() if x}
                clsd = {cl: peval(p, n) for cl, p in Nc[s][t].items()}
                clsd = {cl: x for cl, x in clsd.items() if x}
                if conc != clsd:
                    mism += 1
        print(f"  n={n}: closed form vs concrete realisation -> {mism} "
              f"mismatched entries of {NSHAPE * NSHAPE}")
        ok = ok and mism == 0

    # The split must hold SYMBOLICALLY too: congruence by U over polynomials.
    pi = [None] * NSHAPE
    for s, (_, cs) in enumerate(vv.TEMPLATES):
        img = tuple(sorted(({"0": "0", "a": "i", "b": "k"}[cc],
                            {"0": "0", "i": "a", "k": "b"}[r])
                           for r, cc in cs))
        pi[s] = next(t for t, (_, ct) in enumerate(vv.TEMPLATES)
                     if tuple(sorted(ct)) == img)
    U, nplus, _, _ = vv.eigenbasis(pi)
    off = 0
    for p in range(nplus):
        for qq in range(nplus, NSHAPE):
            acc = {}
            for s in range(NSHAPE):
                if not U[p][s]:
                    continue
                for t in range(NSHAPE):
                    if not U[qq][t]:
                        continue
                    f = U[p][s] * U[qq][t]
                    for cl, poly in Nc[s][t].items():
                        acc[cl] = padd(acc.get(cl, pzero()),
                                       [x * f for x in poly])
            off += sum(1 for poly in acc.values() if poly)
    print(f"  SPLIT TEST symbolically: {nplus} x {NSHAPE - nplus} off-diagonal "
          f"block -> {off} nonzero class-coefficients (predicted 0), "
          f"pi from the LABEL map alone")
    return ok and off == 0, Nc


if __name__ == "__main__":
    ns = [int(a) for a in sys.argv[1:]] or [5, 6]
    print("(V'|V') 14 x 14 -- closed form in n\n")
    ok, Nc = verify(ns)
    print(f"\nclosed form verified: {ok}")
    if ok:
        print("\nsample entries (class index: polynomial):")
        for s, t in ((0, 0), (0, 13), (9, 9)):
            items = sorted(Nc[s][t].items())[:3]
            print(f"  [{vv.TEMPLATES[s][0].split()[0]}]"
                  f"[{vv.TEMPLATES[t][0].split()[0]}]  "
                  f"{len(Nc[s][t])} classes; " +
                  "; ".join(f"c{cl}: {pstr(p)}" for cl, p in items))
