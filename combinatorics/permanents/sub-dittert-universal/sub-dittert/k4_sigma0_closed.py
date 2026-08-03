"""
Closed form in n for `sigma_0`'s ten blocks -- NOTES §6b.35 Prediction 4.

The merge-pattern derivation of §6b.26 and §6b.32 carries over with ONE change,
and it is the only change: free labels range over n values instead of m = n - 1,
so every falling factorial moves up by one.

    side       §6b.26/§6b.32 (sigma_11)          here (sigma_0)
    triv       [n-1]_D                           [n]_D
    vec        +[n-2]_{R-1} merged               +[n-1]_{R-1} merged
               -[n-3]_{R-2} not merged           -[n-2]_{R-2} not merged
    sym/asym   contraction table, an INTEGER     UNCHANGED

The contraction table is unchanged because it rests on `W_aa = 0`,
`W_ba = eps W_ab` and the trace condition `sum_b W_ab = 0` -- none of which
mentions the size of the index set.  `k4_tail_closed.check_contractions` already
self-tests it at m = 5, 6, 7 in both symmetry types; it is re-run here at the
sigma_0 index sizes so that the reuse is measured rather than argued.

`<W,W>` and `q(w) = sum_v w_v^2` divide out of every term exactly as before, so
the closed form is a polynomial in n per pair class, per template pair.

TWO CHECKS, both against things this file does not compute:
  * closed form vs the CONCRETE realisation of `k4_sigma0`, class by class, at
    n = 5 and n = 6 -- the templates-vs-loops test of §6b.26;
  * the SPLIT TEST symbolically: for the three J-split families the off-diagonal
    block of Ntilde in the J-eigenbasis must vanish as a POLYNOMIAL identity,
    with the eigenbasis taken from the label-derived J rather than the measured
    one.
"""

import os
import sys
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "dittert"))
sys.path.insert(0, HERE)
import k4_ind16_closed as c16                                     # noqa: E402
import k4_sigma0 as s0                                            # noqa: E402
import k4_system as k4                                            # noqa: E402
import k4_tail_closed as tc                                       # noqa: E402
import k4_vv14 as vv                                              # noqa: E402
from general_k3 import falling, padd, peval, pmul, pzero          # noqa: E402
from k4_blocks import _shift_by                                   # noqa: E402

# label renaming for the tau image of a cell: (R, C) -> (in(C), out(R))
TAU_IN = {"a": "i", "b": "k"}
TAU_OUT = {"i": "a", "k": "b"}

# PREDICTED maximum degree per family (§6b.35 Prediction 4)
MAXDEG = {("triv", "triv"): 8, ("triv", "vec"): 6, ("vec", "vec"): 4,
          ("triv", "sym"): 4, ("vec", "sym"): 2, ("vec", "asym"): 2,
          ("sym", "sym"): 0, ("asym", "asym"): 0}


def side_factor(kind, mu, gs, gt, D, eps):
    """One side's polynomial factor for a merge pattern -- the table above."""
    if kind == "triv":
        return falling(D)
    if kind == "vec":
        if gs["i"] == gt["i"]:
            return _shift_by(falling(D - 1), 0)          # +[n-1]_{D-1}
        return [-x for x in _shift_by(falling(D - 2), 1)]  # -[n-2]_{D-2}
    return [F(tc.contraction_coeff(mu, eps))]


def block_closed(rowtype, coltype, kept, gidx):
    """Ntilde[s][t] = {sigma_0 class index: polynomial in n}, over `kept`."""
    ns = len(kept)
    eps_r = -1 if rowtype == "asym" else 1
    eps_c = -1 if coltype == "asym" else 1
    N = [[dict() for _ in range(ns)] for _ in range(ns)]
    for s in range(ns):
        cs = kept[s]
        Sr = [x for x in s0.ROWLAB if any(r == x for r, _ in cs)]
        Sc = [x for x in s0.COLLAB if any(c == x for _, c in cs)]
        for t in range(ns):
            ct = kept[t]
            Tr = [x for x in s0.ROWLAB if any(r == x for r, _ in ct)]
            Tc = [x for x in s0.COLLAB if any(c == x for _, c in ct)]
            acc = {}
            for mu in c16.partial_injections(Sr, Tr):
                grs, grt, R = c16._groups(Sr, Tr, mu)
                frow = side_factor(rowtype, mu, grs, grt, R, eps_r)
                if not frow:
                    continue
                for nu in c16.partial_injections(Sc, Tc):
                    gcs, gct, C = c16._groups(Sc, Tc, nu)
                    nu_ik = {TAU_IN[k2]: TAU_IN[v] for k2, v in nu.items()}
                    gcs_ik = {TAU_IN[k2]: v for k2, v in gcs.items()}
                    gct_ik = {TAU_IN[k2]: v for k2, v in gct.items()}
                    fcol = side_factor(coltype, nu_ik, gcs_ik, gct_ik, C, eps_c)
                    if not fcol:
                        continue
                    u = tuple(sorted((grs[r], gcs[c]) for r, c in cs))
                    v = tuple(sorted((grt[r], gct[c]) for r, c in ct))
                    key = gidx[k4.canon_pair(u, v, False)]
                    acc[key] = padd(acc.get(key, pzero()), pmul(frow, fcol))
            N[s][t] = {cl: p for cl, p in acc.items() if p}
    return N


def label_J(kept):
    """
    The J-eigenbasis from the LABEL renaming alone, as in §6b.30's symbolic
    split test.  Returns (U, n_plus) with U over the `kept` templates, or None
    if some tau-image is not itself a kept template (which is a real
    possibility here: on `triv triv` one J-fixed template was dropped as
    dependent, so its partner's image must be re-expressed).
    """
    pos = {c: t for t, c in enumerate(kept)}
    A = [[F(0)] * len(kept) for _ in kept]
    for t, cells in enumerate(kept):
        img = tuple(sorted((TAU_IN[c], TAU_OUT[r]) for r, c in cells))
        if img in pos:
            A[t][pos[img]] = F(1)
            continue
        # the image coincides with a dropped template; the only coincidence in
        # this build is {(i,a),(k,b)} <-> {(i,b),(k,a)}, equal up to the sign
        # eps_c of the column weight, so map it onto the kept partner.
        alt = tuple(sorted((TAU_IN[c], TAU_OUT[r]) for r, c in
                           [(r2, "b" if c2 == "a" else "a")
                            for r2, c2 in cells]))
        if alt in pos:
            A[t][pos[alt]] = F(1)
        else:
            return None
    return s0.eigen_split(A)


def verify(ns=(5, 6)):
    print("contraction table re-checked at the sigma_0 index sizes:")
    tok = tc.check_contractions(ms=ns)
    print(f"  table verified: {tok}\n")

    gvars = s0.gvars_cached()
    gidx = {k: i for i, k in enumerate(gvars)}
    allok = tok
    n0 = ns[0]
    for rt, ct, split, blocks in s0.FAMILIES:
        want = sum(m for _, m, _ in blocks)
        if want == 0:
            print(f"  {rt} {ct}: multiplicity 0, no closed form needed")
            continue
        cand = s0.candidates(rt, ct)
        wr, wc = s0.weights(n0, rt, ct, 20260729)
        vecs = [s0.realise(c, n0, rt, ct, wr, wc) for c in cand]
        import k4_tail as tail
        kept_i, _, _ = tail.independent_subset(vecs)
        kept = [cand[t] for t in kept_i]
        Nc = block_closed(rt, ct, kept, gidx)
        nk = len(kept)
        degs = [len(p) - 1 for a in range(nk) for b in range(nk)
                for p in Nc[a][b].values()] or [0]
        used = set()
        for a in range(nk):
            used |= set().union(*[set(Nc[a][b]) for b in range(nk)])
        symm = all(Nc[a][b] == Nc[b][a] for a in range(nk) for b in range(nk))
        names = " / ".join(nm for nm, m, _ in blocks if m)
        print(f"  {names}")
        print(f"    {nk} shapes, {len(used)} of 51 classes, degrees "
              f"{min(degs)}..{max(degs)} (predicted max {MAXDEG[(rt, ct)]}), "
              f"symmetric {symm}")
        allok = allok and symm and max(degs) <= MAXDEG[(rt, ct)]

        if split:
            UJ = label_J(kept)
            if UJ is None:
                print("    *** label-derived J not expressible on kept ***")
                allok = False
            else:
                U, npl, nmi = UJ
                off = 0
                for p in range(npl):
                    for q in range(npl, nk):
                        acc = {}
                        for a in range(nk):
                            if not U[p][a]:
                                continue
                            for b in range(nk):
                                if not U[q][b]:
                                    continue
                                f = U[p][a] * U[q][b]
                                for cl, poly in Nc[a][b].items():
                                    acc[cl] = padd(acc.get(cl, pzero()),
                                                   [f * x for x in poly])
                        off += sum(1 for cl, p2 in acc.items() if p2)
                print(f"    SYMBOLIC SPLIT TEST: dim(+1) {npl} dim(-1) {nmi}; "
                      f"{off} nonzero class-coefficients in the "
                      f"{npl} x {nmi} block  (predicted 0)")
                allok = allok and off == 0 and npl == blocks[0][1]

        for n in ns:
            wr, wc = s0.weights(n, rt, ct, 20260729)
            q = s0.wnorm(rt, wr, n) * s0.wnorm(ct, wc, n)
            basis = k4.basis_of(n)
            B = len(basis)
            index = {mo: t for t, mo in enumerate(basis)}
            E = [{index[mo]: c for mo, c in
                  s0.realise(cc, n, rt, ct, wr, wc).items()} for cc in kept]
            cls, _ = s0.g_direct_class_array(n, basis, gidx)
            Nn = vv.block_by_class(E, cls, B)
            mism = 0
            for a in range(nk):
                for b in range(nk):
                    conc = {cl: F(x, q) for cl, x in Nn[a][b].items() if x}
                    clsd = {cl: peval(p, n) for cl, p in Nc[a][b].items()}
                    clsd = {cl: x for cl, x in clsd.items() if x}
                    if conc != clsd:
                        mism += 1
            print(f"      n={n}: closed form vs concrete -> {mism} mismatched "
                  f"of {nk * nk}")
            allok = allok and mism == 0
    return allok


if __name__ == "__main__":
    ns = [int(a) for a in sys.argv[1:]] or [5, 6]
    print("Closed form in n for sigma_0's ten blocks -- NOTES §6b.35\n")
    ok = verify(tuple(ns))
    print(f"\nall eight nonzero sigma_0 closed forms verified: {ok}")
