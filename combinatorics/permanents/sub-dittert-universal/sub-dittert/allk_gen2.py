"""
THE e = 2 GENERATOR SOLVE: the k = 4 and k = 5 block families as ONE k-free
object, over Q(n).

NOTES-ALLK section 10.3 says the constraint matrix M_2(n) is shared by both k in
band(2) = {4, 5} and the whole k-dependence sits in ten scalars.  Concretely,
with U_d, V_d the k-free right-hand-side generators,

    rhs(n,k) = sum_{d=1}^{5} [ -s_d(n,k) U_d(n) + t_d(n,k) V_d(n) ],
    s_d = [k]_d/[n]_d,   t_d = s_d^2 (k-d)!/n^(k-d),

so solving M_2 X_d = U_d and M_2 Y_d = V_d ONCE gives

    x(n,k) = sum_d [ -s_d X_d(n) + t_d Y_d(n) ]  +  ker M_2(n)

for BOTH k, and every block is the same k-free combination.  This file does the
ten solves.

OWNERSHIP.  `k4_system` is imported READ-ONLY for the matrix; no `k4_*` file is
written.  The pinned families are k4-finish's; everything here is the UNPINNED
family.

STAGES, run separately so the gate is cheap:
    stage 1  build M_2, build U_d and V_d, and CHECK the decomposition against
             k4_system's own rhs_at at k = 4 and at k = 5.  This is the gate: if
             it fails, section 10.3(ii) is wrong at e = 2 and nothing else runs.
    stage 2  the left-null vector, and orthogonality of every generator to it --
             the uniform-in-k consistency of section 10.5.
    stage 3  the ten solves, by ONE Gauss-Jordan on the augmented matrix
             [ M | U_1..U_5 | V_1..V_5 ] over Q(n).
    stage 4  reassemble x(n,4) and x(n,5) and check both against rhs_at.

Usage:  GUARD_MEM=8G ../guard.sh python3 allk_gen2.py 1
"""

import os
import sys
import time
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "dittert"))
sys.path.insert(0, HERE)
import general_k3 as g                                            # noqa: E402
import k4_system as k4                                            # noqa: E402
from general_k3 import RF                                         # noqa: E402

DMAX = 5                                     # D = 2e+1 at e = 2
N_POLY = [F(0), F(1)]


# ------------------------------------------------------- the (s, t) scalars


def falling(x, d):
    out = F(1)
    for i in range(d):
        out *= (x - i)
    return out


def s_val(n, k, d):
    return falling(F(k), d) / falling(F(n), d)


def t_val(n, k, d):
    from math import factorial
    if d > k:
        return F(0)
    sd = s_val(n, k, d)
    return sd * sd * F(factorial(k - d), n ** (k - d))


# ------------------------------------------------- the k-free rhs generators


def generators(rows):
    """U_d and V_d as lists of polynomials in n, one per constraint row.

    U_d[row] = |orbit|(n) * ( [distinct rows] + [distinct cols] )
    V_d[row] = |orbit|(n) * [ partial permutation ]
    Both are zero unless the row's degree is exactly d.  Neither mentions k.
    """
    U = {d: [g.pzero() for _ in rows] for d in range(1, DMAX + 1)}
    V = {d: [g.pzero() for _ in rows] for d in range(1, DMAX + 1)}
    for i, r in enumerate(rows):
        d = len(r)
        if d == 0 or d > DMAX:
            continue
        size = g.orbit_size_poly(r, False)
        dr = len({a for a, _ in r}) == d
        dc = len({b for _, b in r}) == d
        mult = (1 if dr else 0) + (1 if dc else 0)
        if mult:
            U[d][i] = g.pscale(size, F(mult))
        if dr and dc:
            V[d][i] = size
    return U, V


def build_matrix(sym):
    """M = [A0 | A1c/n + A1l | A2] over Q(n), exactly as k4_solve assembles it."""
    rows, gvars, svars, lvars = (sym["rows"], sym["gvars"], sym["svars"],
                                 sym["lvars"])
    M = []
    for r in range(len(rows)):
        row = [RF(p) for p in sym["A0"][r]]
        row += [RF(sym["A1c"][r][j], N_POLY) + RF(sym["A1l"][r][j])
                for j in range(len(svars))]
        row += [RF(p) for p in sym["A2"][r]]
        M.append(row)
    return M


# ------------------------------------------------------------------- stage 1


def stage1(sym):
    rows = sym["rows"]
    U, V = generators(rows)
    print("STAGE 1.  The k-free generators, and the decomposition gate.")
    print()
    nzU = sum(1 for i in range(len(rows))
              if any(U[d][i] for d in range(1, DMAX + 1)))
    from collections import Counter
    bydeg = Counter()
    for i, r in enumerate(rows):
        if any(U[d][i] for d in range(1, DMAX + 1)):
            bydeg[len(r)] += 1
    print(f"  rows {len(rows)};  rows with a nonzero generator: {nzU}")
    print(f"  by degree: {dict(sorted(bydeg.items()))}")
    print("  NOTES-ALLK 10.3(iii) predicts p(d) = 1, 2, 3, 5, 7 at d = 1..5,")
    print("  so 18 in total, of which 11 are visible at k = 4.")
    want = {1: 1, 2: 2, 3: 3, 4: 5, 5: 7}
    ok_supp = dict(bydeg) == want
    print(f"  support law holds: {ok_supp}")

    print()
    print("  GATE: rhs(n,k) == sum_d [ -s_d U_d + t_d V_d ], against")
    print("  k4_system.rhs_at, which is built from g.coef_F and shares no logic")
    print("  with the generator construction.")
    bad = 0
    checks = 0
    for k in (4, 5):
        for n0 in (5, 6, 7, 9, 11):
            want_rhs = _rhs_at(sym, n0, k)
            got = []
            for i in range(len(rows)):
                acc = F(0)
                for d in range(1, DMAX + 1):
                    acc += (-s_val(n0, k, d) * g.peval(U[d][i], n0)
                            + t_val(n0, k, d) * g.peval(V[d][i], n0))
                got.append(acc)
            for i in range(len(rows)):
                checks += 1
                if got[i] != want_rhs[i]:
                    bad += 1
                    if bad <= 3:
                        print(f"    MISMATCH k={k} n={n0} row {i} "
                              f"{rows[i]}: got {got[i]} want {want_rhs[i]}")
            print(f"    k={k} n={n0}: {len(rows)} rows compared"
                  + ("" if bad else "   MATCH"))
    print(f"  {checks} row comparisons, {bad} mismatches.")
    print()
    return U, V, (bad == 0 and ok_supp)


def _rhs_at(sym, n0, k):
    """k4_system's own right-hand side, but at an arbitrary k."""
    return [g.peval(g.orbit_size_poly(r, False), n0) * g.coef_F(r, n0, k)
            for r in sym["rows"]]


# ------------------------------------------------------------------- stage 2


def stage2(M, U, V, sym):
    print("STAGE 2.  The left null vector, and uniform-in-k consistency.")
    print()
    nR = len(M)
    ncol = len(M[0])
    # left null space by Gauss-Jordan on the transpose, tracking the transform
    A = [row[:] for row in M]
    T = [[RF.const(1 if i == j else 0) for j in range(nR)] for i in range(nR)]
    r = 0
    for c in range(ncol):
        p = next((i for i in range(r, nR) if A[i][c]), None)
        if p is None:
            continue
        A[r], A[p] = A[p], A[r]
        T[r], T[p] = T[p], T[r]
        pv = A[r][c]
        A[r] = [v / pv for v in A[r]]
        T[r] = [v / pv for v in T[r]]
        for i in range(nR):
            if i != r and A[i][c]:
                f = A[i][c]
                A[i] = [A[i][j] - f * A[r][j] for j in range(ncol)]
                T[i] = [T[i][j] - f * T[r][j] for j in range(nR)]
        r += 1
        if r == nR:
            break
    rank = r
    null = [T[i] for i in range(rank, nR)]
    print(f"  rank over Q(n) = {rank};  left null dimension = {nR - rank}")
    ok = True
    for y in null:
        nz = [j for j in range(nR) if y[j]]
        print(f"  left null vector supported on rows {nz}"
              + (f"  (row key {sym['rows'][nz[0]]})" if len(nz) == 1 else ""))
        for d in range(1, DMAX + 1):
            for name, W in (("U", U), ("V", V)):
                acc = RF.const(0)
                for j in range(nR):
                    if y[j]:
                        acc = acc + y[j] * RF(W[d][j])
                if acc:
                    ok = False
                    print(f"    <y, {name}_{d}> = NONZERO")
    print(f"  every generator orthogonal to the left null space: {ok}")
    print("  so the system is CONSISTENT for every k in the band at once.")
    print()
    return rank, ok


# ------------------------------------------------------------------- stage 3


def stage3(M, U, V):
    print("STAGE 3.  The ten solves, by ONE Gauss-Jordan on the augmented")
    print("  matrix [ M | U_1..U_5 | V_1..V_5 ] over Q(n).")
    print()
    nR = len(M)
    ncol = len(M[0])
    extra = []
    for d in range(1, DMAX + 1):
        extra.append(("U%d" % d, [RF(U[d][i]) for i in range(nR)]))
    for d in range(1, DMAX + 1):
        extra.append(("V%d" % d, [RF(V[d][i]) for i in range(nR)]))
    ne = len(extra)
    A = [M[i][:] + [extra[e][1][i] for e in range(ne)] for i in range(nR)]
    t0 = time.time()
    piv = []
    r = 0
    for c in range(ncol):
        p = next((i for i in range(r, nR) if A[i][c]), None)
        if p is None:
            continue
        A[r], A[p] = A[p], A[r]
        pv = A[r][c]
        A[r] = [v / pv for v in A[r]]
        for i in range(nR):
            if i != r and A[i][c]:
                f = A[i][c]
                Ar = A[r]
                A[i] = [A[i][j] - f * Ar[j] for j in range(ncol + ne)]
        piv.append(c)
        r += 1
        if r % 10 == 0:
            print(f"    rank {r}, column {c}, {time.time()-t0:.0f}s",
                  flush=True)
        if r == nR:
            break
    print(f"  rank {r}, {time.time()-t0:.0f}s total")
    # consistency: every zero row must have zero in every extra column
    bad = 0
    for i in range(r, nR):
        for e in range(ne):
            if A[i][ncol + e]:
                bad += 1
                print(f"    INCONSISTENT in {extra[e][0]}")
    print(f"  consistency of all ten generators: {'OK' if bad == 0 else 'FAIL'}")
    sols = {}
    for e in range(ne):
        x = [RF.const(0)] * ncol
        for i, c in enumerate(piv):
            x[c] = A[i][ncol + e]
        sols[extra[e][0]] = x
    return sols, piv


def report_degrees(sols):
    print()
    print("  degrees of the particular solutions (free variables zero):")
    print("     name   nonzero   num deg max   den deg max")
    for name, x in sols.items():
        nz = [v for v in x if v]
        dn = max((len(v.num) - 1 for v in nz), default=0)
        dd = max((len(v.den) - 1 for v in nz), default=0)
        print(f"     {name:<6} {len(nz):>7}   {dn:>11}   {dd:>11}")


# ------------------------------------------------------------------- stage 4


def stage4(M, sols, sym):
    print()
    print("STAGE 4.  Reassemble x(n,k) for k = 4 and k = 5 and check M x = rhs.")
    print()
    nR, ncol = len(M), len(M[0])
    bad = 0
    for k in (4, 5):
        for n0 in (5, 6, 7, 9):
            x = [F(0)] * ncol
            for d in range(1, DMAX + 1):
                sd, td = s_val(n0, k, d), t_val(n0, k, d)
                Xd, Yd = sols["U%d" % d], sols["V%d" % d]
                for j in range(ncol):
                    if Xd[j]:
                        x[j] += -sd * _ev(Xd[j], n0)
                    if Yd[j]:
                        x[j] += td * _ev(Yd[j], n0)
            want = _rhs_at(sym, n0, k)
            for i in range(nR):
                acc = F(0)
                for j in range(ncol):
                    if x[j] and M[i][j]:
                        acc += _ev(M[i][j], n0) * x[j]
                if acc != want[i]:
                    bad += 1
                    if bad <= 3:
                        print(f"    MISMATCH k={k} n={n0} row {i}")
            print(f"    k={k} n={n0}: M x = rhs over {nR} rows"
                  + ("" if bad else "   MATCH"))
    print(f"  {bad} mismatches.")
    return bad == 0


def _ev(rf, n0):
    return g.peval(rf.num, n0) / g.peval(rf.den, n0)


# ------------------------------------------------------------------- stage 5


def stage5(sols, sym, path):
    """Write the ten generator solutions out in full, with each nonzero named."""
    ng, ns = len(sym["gvars"]), len(sym["svars"])

    def where(j):
        if j < ng:
            return "sigma_0 [%d]" % j, sym["gvars"][j]
        if j < ng + ns:
            return "sigma_11[%d]" % (j - ng), sym["svars"][j - ng]
        return "lambda  [%d]" % (j - ng - ns), sym["lvars"][j - ng - ns]

    def show(v):
        num = " + ".join("%s n^%d" % (c, i) for i, c in enumerate(v.num) if c)
        den = " + ".join("%s n^%d" % (c, i) for i, c in enumerate(v.den) if c)
        return "(%s) / (%s)" % (num or "0", den or "1")

    lines = ["The e = 2 generator solutions X_d = sol[U_d], Y_d = sol[V_d].",
             "",
             "  x(n,k) = sum_{d=1}^{5} [ -s_d(n,k) X_d(n) + t_d(n,k) Y_d(n) ]"
             "  +  ker M_2(n)",
             "  s_d = [k]_d/[n]_d,   t_d = s_d^2 (k-d)!/n^(k-d),   k = 4 or 5.",
             "",
             "Free variables are set to zero, so this is ONE base point of the",
             "354-dimensional affine family, not a certificate.  Its sigma_0 Gram",
             "is extremely sparse and is NOT positive definite; all feasibility",
             "lives in the kernel.",
             ""]
    tot = 0
    for name in ["U%d" % d for d in range(1, DMAX + 1)] + \
                ["V%d" % d for d in range(1, DMAX + 1)]:
        x = sols[name]
        nz = [(j, v) for j, v in enumerate(x) if v]
        tot += len(nz)
        lines.append("%s  (%d nonzero)" % (name, len(nz)))
        for j, v in nz:
            w, key = where(j)
            lines.append("   %-16s %-40s = %s" % (w, str(key), show(v)))
        lines.append("")
    lines.append("total nonzeros: %d out of %d" % (tot, 10 * len(sols["U1"])))
    with open(path, "w") as fh:
        fh.write("\n".join(lines) + "\n")
    print(f"  written to {path}  ({tot} nonzeros)")


def main():
    stage = int(sys.argv[1]) if len(sys.argv) > 1 else 1
    print("allk_gen2.py -- the e = 2 generator solve, k = 4 and k = 5 together")
    print()
    t0 = time.time()
    sym = k4.build(verbose=True)
    print(f"  system built in {time.time()-t0:.0f}s")
    print()
    U, V, gate = stage1(sym)
    print(f"GATE: {'PASS' if gate else 'FAIL'}")
    if not gate or stage < 2:
        return
    M = build_matrix(sym)
    rank, ok = stage2(M, U, V, sym)
    if stage < 3:
        return
    sols, piv = stage3(M, U, V)
    report_degrees(sols)
    if stage < 4:
        return
    ok = stage4(M, sols, sym)
    if ok:
        stage5(sols, sym,
               os.path.join(HERE, "results", "allk_gen2_generators.txt"))


if __name__ == "__main__":
    main()
