"""
HOW THE INESCAPABLE sigma_11 CONDITIONS DISTRIBUTE OVER THE BLOCKS.

A bounded probe, not design work.  allk_design.py found that the constraints the
designer cannot escape are 33 conditions on sigma_11 alone at e = 2 (4 at
e = 1), with sigma_0 free at both.  This file asks WHERE those conditions sit in
the block basis.

THE OBJECT.  Let  C := S_sigma11 intersect rowspace(M),  of dimension 33 at
e = 2 and 4 at e = 1.  Each block alpha carries a linear map
`N_alpha : Q(n)^{n_svars} -> Sym(m_alpha)` -- the block entries as forms in the
orbit coefficients.  Then

    dim pi_alpha(C)   =  how many independent conditions constrain block alpha,
    sum_alpha dim pi_alpha(C)  >=  dim C,  with equality iff C splits.

INDEXING, and this is the trap the folder has already paid for (NOTES 6b.21):
the class ORDERING differs between modules.  `k4_ind16_closed.block_closed`
takes the index map as an argument, so it is called with THIS file's ordering --
the one `k4_system` uses -- and never with its own.

SCOPE, deliberately bounded.  At e = 1 all four blocks are measured, which is the
control.  At e = 2 only `Ind(V'|1)`, the 16 x 16, is measured: it is the block
NOTES 6b.12 found resists pinning, and it is the lead's question.  The other ten
are not measured and nothing is claimed about them.

PREDICTIONS, registered before the run.

  P1  e = 1 control: the 4 conditions do NOT all sit in one block; at least the
      Ind(V'|1) 2 x 2 carries one, since NOTES 6a.8c had to PIN that block
      (`C01 = 0`) to get a determinate design.
  P2  e = 2: the 16 x 16 carries the BULK -- dim pi_Ind16(C) >= 17, a majority of
      33.  Reason: a block that resists pinning is one whose entries cannot be
      set freely, i.e. one that is heavily constrained.
  P3  sum over blocks of dim pi_alpha(C) > dim C at e = 1, i.e. the conditions
      couple blocks rather than splitting cleanly.

Read-only use of `k4_system`, `k4_ind16_closed`, `blocks`; no file of another
thread is written.

Usage:  GUARD_MEM=8G ../guard.sh python3 allk_blockmap.py
"""

import os
import sys
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "dittert"))
sys.path.insert(0, HERE)
import allk_gen2 as gen2                                          # noqa: E402
import general_k3 as g                                            # noqa: E402
from general_k3 import RF                                         # noqa: E402

N_RF = RF([F(0), F(1)])
ONE = RF([F(1)])
ZERO = RF.const(0)


# --------------------------------------------------------------- linear algebra


def left_null(M, cols):
    """Basis of { y : y^T M[:, cols] = 0 }, over Q(n)."""
    nR = len(M)
    A = [[M[i][c] for c in cols] for i in range(nR)]
    T = [[ONE if i == j else ZERO for j in range(nR)] for i in range(nR)]
    nc = len(cols)
    r = 0
    for c in range(nc):
        p = next((i for i in range(r, nR) if A[i][c]), None)
        if p is None:
            continue
        A[r], A[p] = A[p], A[r]
        T[r], T[p] = T[p], T[r]
        pv = A[r][c]
        A[r] = [t / pv for t in A[r]]
        T[r] = [t / pv for t in T[r]]
        for i in range(nR):
            if i != r and A[i][c]:
                f = A[i][c]
                A[i] = [A[i][t] - f * A[r][t] for t in range(nc)]
                T[i] = [T[i][t] - f * T[r][t] for t in range(nR)]
        r += 1
        if r == nR:
            break
    return [T[i] for i in range(r, nR)]


def rank_rows(vecs):
    if not vecs:
        return 0
    m, nc = len(vecs), len(vecs[0])
    A = [row[:] for row in vecs]
    r = 0
    for c in range(nc):
        p = next((i for i in range(r, m) if A[i][c]), None)
        if p is None:
            continue
        A[r], A[p] = A[p], A[r]
        pv = A[r][c]
        A[r] = [t / pv for t in A[r]]
        for i in range(m):
            if i != r and A[i][c]:
                f = A[i][c]
                A[i] = [A[i][t] - f * A[r][t] for t in range(nc)]
        r += 1
        if r == m:
            break
    return r


def condition_space(M, ng, ns, nl):
    """C = S_sigma11 intersect rowspace(M), as a list of vectors of length ns."""
    other = list(range(0, ng)) + list(range(ng + ns, ng + ns + nl))
    Y = left_null(M, other)
    rows = []
    for y in Y:
        v = []
        for j in range(ng, ng + ns):
            acc = ZERO
            for i in range(len(M)):
                if y[i] and M[i][j]:
                    acc = acc + y[i] * M[i][j]
            v.append(acc)
        if any(v):
            rows.append(v)
    # reduce to a basis
    keep = []
    for v in rows:
        if rank_rows(keep + [v]) > len(keep):
            keep.append(v)
    return keep


def project_rank(C, funcs):
    """dim of the image of C under a list of linear functionals on Q(n)^ns.

    Each functional is a dict {coordinate: RF}."""
    imgs = []
    for v in C:
        row = []
        for f in funcs:
            acc = ZERO
            for j, coef in f.items():
                if v[j]:
                    acc = acc + coef * v[j]
            row.append(acc)
        imgs.append(row)
    return rank_rows(imgs)


# ------------------------------------------------------------------ e = 1 case


def control_e1():
    import blocks as bl
    print("CONTROL, e = 1 (k = 3).  All four sigma_11 blocks measured.")
    sym = g.build_symbolic_system(3)
    ng, ns, nl = (len(sym["gvars"]), len(sym["svars"]), len(sym["lvars"]))
    n2 = [F(0), F(1)]
    M = []
    for r in range(len(sym["rows"])):
        row = [RF(p) for p in sym["A0"][r]]
        row += [RF(sym["A1c"][r][j], n2) + RF(sym["A1l"][r][j])
                for j in range(ns)]
        row += [RF(p) for p in sym["A2"][r]]
        M.append(row)
    C = condition_space(M, ng, ns, nl)
    print(f"  dim C = {len(C)}   (allk_design reported 4)")

    idx = bl.svar_index()
    # columns of each block map, by feeding unit vectors
    names = ["trivial 3x3", "sign 1x1", "Ind(V'|1) 2x2", "(V'|V') 1x1"]
    slots = {nm: [] for nm in names}
    for j in range(ns):
        y = [ONE if t == j else ZERO for t in range(ns)]
        A, B, Cb, D = bl.blocks_rational_generic(N_RF, y, idx, ONE)
        slots["trivial 3x3"].append([A[a][b] for a in range(3)
                                     for b in range(a, 3)])
        slots["sign 1x1"].append([B])
        slots["Ind(V'|1) 2x2"].append([Cb[a][b] for a in range(2)
                                       for b in range(a, 2)])
        slots["(V'|V') 1x1"].append([D])
    tot = 0
    print("     block            entries   dim pi(C)")
    for nm in names:
        cols = slots[nm]
        nent = len(cols[0])
        funcs = [{j: cols[j][e] for j in range(ns) if cols[j][e]}
                 for e in range(nent)]
        d = project_rank(C, funcs)
        tot += d
        print(f"     {nm:<16} {nent:>7}   {d:>9}")
    print(f"  sum over blocks = {tot}  vs dim C = {len(C)}")
    print(f"  P3 (conditions couple blocks): "
          f"{'HOLDS' if tot > len(C) else 'FAILS -- C splits cleanly'}")
    return len(C), tot


# ------------------------------------------------------------------ e = 2 case


def probe_e2():
    import k4_system as k4
    import k4_ind16_closed as ind
    print()
    print("e = 2 (k = 4, 5).  The 16 x 16 Ind(V'|1) block only.")
    sym = k4.build(verbose=False)
    M = gen2.build_matrix(sym)
    ng, ns, nl = (len(sym["gvars"]), len(sym["svars"]), len(sym["lvars"]))
    C = condition_space(M, ng, ns, nl)
    print(f"  dim C = {len(C)}   (allk_design reported 33)")

    sidx = {key: i for i, key in enumerate(sym["svars"])}
    print("  block map built with THIS file's class ordering (NOTES 6b.21)")
    N = ind.block_closed(sidx)
    m = len(N)
    funcs = []
    for a in range(m):
        for b in range(a, m):
            funcs.append({c: RF(p) for c, p in N[a][b].items()})
    print(f"  block size {m} x {m}, {len(funcs)} independent entries")
    d = project_rank(C, funcs)
    print(f"  dim pi_Ind16(C) = {d}  of  dim C = {len(C)}")
    print(f"  P2 (the 16x16 carries the bulk, >= 17): "
          f"{'HOLDS' if d >= 17 else 'FAILS'}")

    # A COMPARISON BLOCK, without which "carries the bulk" is not a
    # distinguishing statement: at e = 1 the trivial block also saw all of C.
    import k4_blocks as kb
    print()
    print("  COMPARISON: the trivial 14 x 14, same instrument.")
    reps, sizes, T = kb.trivial_block()
    mt = len(T)
    tfuncs = []
    missing = 0
    for a in range(mt):
        for b in range(a, mt):
            fn = {}
            for key, poly in T[a][b].items():
                j = sidx.get(key)
                if j is None:
                    missing += 1
                    continue
                fn[j] = RF(poly)
            tfuncs.append(fn)
    if missing:
        print(f"    {missing} class keys did not resolve in this ordering --")
        print("    the conventions differ; NOT reporting a number (NOTES 6b.21).")
        return len(C), d, None
    dt = project_rank(C, tfuncs)
    print(f"    block size {mt} x {mt}, {len(tfuncs)} entries, all keys resolved")
    print(f"    dim pi_trivial14(C) = {dt}  of  dim C = {len(C)}")
    print()
    if d == len(C) and dt == len(C):
        print("    BOTH see all of C.  So 'the 16x16 carries the bulk' is NOT a")
        print("    distinguishing statement at e = 2 either: the correct reading")
        print("    is that no inescapable condition is invisible to either block.")
    elif d > dt:
        print("    The 16x16 sees strictly more.  It IS the distinguished block.")
    else:
        print("    The trivial block sees at least as much; P2's reading fails.")
    corollary(C, funcs, tfuncs, d, dt)
    return len(C), d, dt


def corollary(C, ind_funcs, triv_funcs, d, dt):
    """d(alpha) = dim(C ∩ S_alpha) for EVERY one of the eleven blocks, from the
    two measurements above.

    S_alpha is the set of orbit vectors whose image is zero in every block other
    than alpha.  Suppose c lies in C ∩ S_alpha.  Pick a measured block beta with
    beta != alpha -- always possible, since two are measured and alpha can equal
    at most one of them.  Then pi_beta(c) = 0.  But pi_beta restricted to C is
    INJECTIVE, because dim pi_beta(C) = dim C.  So c = 0.

    Hence d(alpha) = 0 for all eleven blocks, from two block maps.
    """
    n = len(C)
    print()
    print("  COROLLARY: d(alpha) = dim(C ∩ S_alpha), for ALL ELEVEN blocks.")
    print(f"    pi_Ind16 injective on C:      {d} = {n}   {d == n}")
    print(f"    pi_trivial14 injective on C:  {dt} = {n}   {dt == n}")
    if d != n or dt != n:
        print("    at least one is not injective -- the argument does not run.")
        return
    # direct confirmation on the two measured blocks
    kern_ind = kernel_in(C, ind_funcs)
    kern_tri = kernel_in(C, triv_funcs)
    print(f"    dim (C ∩ ker pi_Ind16)    = {kern_ind}")
    print(f"    dim (C ∩ ker pi_trivial14) = {kern_tri}")
    print()
    print("    Any c in C confined to ONE block has zero image in the other")
    print("    measured block, and injectivity there forces c = 0.  So")
    print("    d(alpha) = 0 for EVERY one of the eleven blocks:")
    print()
    print("      NO inescapable condition lives on a single block.")
    print("      All 33 couple blocks together.")
    print()
    print("    This is the number the design step needs, and it is bad news for")
    print("    block-local design: there is no block one can solve on its own.")


def kernel_in(C, funcs):
    """dim of { c in C : every functional vanishes on c }."""
    imgs = []
    for v in C:
        row = []
        for f in funcs:
            acc = ZERO
            for j, coef in f.items():
                if v[j]:
                    acc = acc + coef * v[j]
            row.append(acc)
        imgs.append(row)
    return len(C) - rank_rows(imgs)


def main():
    print("allk_blockmap.py -- where the inescapable conditions sit, by block")
    print()
    print("PREDICTIONS, before the run:")
    print("  P1  e = 1: the 4 conditions do not all sit in one block; the")
    print("      Ind(V'|1) 2x2 carries at least one")
    print("  P2  e = 2: dim pi_Ind16(C) >= 17, a majority of 33")
    print("  P3  e = 1: sum over blocks > dim C -- the conditions couple")
    print()
    control_e1()
    probe_e2()
    print()
    print("  NOT MEASURED: the other ten blocks at e = 2.  Nothing is claimed")
    print("  about them, and the sum over all eleven is not available here.")
    print()
    print("DONE")


if __name__ == "__main__":
    main()
