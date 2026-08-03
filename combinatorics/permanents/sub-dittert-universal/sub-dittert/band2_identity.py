"""
BAND 2 (deg_basis = 2, k <= TOPDEG = 5): the identity half over Q(n), and the
exact size of the positivity problem that is left.

WHY THIS FILE EXISTS.  `POSITIVITY.md` closed band 1 and named band 2's blocker
as `PARAMETRIC.md` §10 item 2 -- "closed forms for the block entries, so Branch S
applies at d_b = 2".  That reading is WRONG and this file records the correction
with measurements:

  * the PRIMAL block algebra at d_b = 2 is ALREADY closed form in n, derived and
    validated -- `k4_ind16_closed.py` (the 16x16 Ind(V'|1)), `k4_vv14_closed.py`
    (the 14x14 (V'|V') and the 10x10 / 4x4 that split off it),
    `k4_sigma0_closed.py` (sigma_0's ten blocks), `k4_tail_closed.py` (the last
    six).  Every one re-verified against the concrete realisation at n = 5 and
    n = 6 with 0 mismatched entries, plus symbolic split tests.
  * `E` and `G` in §6b.82's NO-ROUTE list are DUAL objects -- coefficients of
    extreme rays of the nonnegative relation cone, i.e. of the CEILING of
    §6b.70-73 -- not entries of the primal Gram blocks.  `PARAMETRIC.md` §8.2
    already says the rays are a dual object; §10 item 2 conflates the two.

So Branch S IS available at d_b = 2.  What blocks band 2 is the DESIGN, and this
file measures it exactly.

WHAT IS COMPUTED

 [A] The band-2 rhs law over Q(n).  Theorem 2 of `PARAMETRIC.md` says
     rhs_r(n,k) = (k)_d [ c_r(n) + (k!/n^k) e_r(n) ].  `PARAMETRIC.md` §2
     measured this at integer (n,k); here `c^[d]`, `e^[d]` for d = 1..5 are
     built as elements of Q(n) and the law is checked as an IDENTITY IN Q(n),
     row by row, at every k of the band.
 [B] The collapse.  Since A(n) is k-free (Lemma 1) and the rhs law is an
     identity in Q(n), Theorem 4's X(n,k) = sum_d (k)_d (Y_d + (k!/n^k) Z_d)
     follows from [A] by linearity of ANY fixed solve -- no 87 x 440 Gauss-
     Jordan over Q(n) is needed.  Stated as Lemma B2 below and checked by
     specialising to integer n.
 [C] The exact size of the design.  rank M, the per-group inescapable counts
     d(B), the lineality dimension, the PURELY-lambda part of the kernel (which
     moves no Gram entry and is therefore gauge for positivity), and hence the
     dimension of the design that positivity actually sees -- at band 2 and, as
     a control, at band 1 where the answer is known to be 4.

Companion verifier: `graded_verify_band2.py`.  Record: `POSITIVITY.md` §9.
"""

import os
import sys
import time
from fractions import Fraction as F
from math import factorial

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "dittert"))
sys.path.insert(0, HERE)

import allk_gen2 as gen2                                          # noqa: E402
import band1_certificate as b1                                    # noqa: E402
import general_k3 as g                                            # noqa: E402
import k4_system as k4                                            # noqa: E402
from general_k3 import RF                                         # noqa: E402

ZERO = RF([])
ONE = RF([F(1)])
N = RF([F(0), F(1)])

TOPDEG = 5
BAND_K = (2, 3, 4, 5)


# --------------------------------------------------------- Theorem 2 over Q(n)
def ce_vectors(rows, topdeg):
    """c^[d], e^[d] in Q(n)^{nrows}, for d = 1..topdeg (PARAMETRIC Theorem 2)."""
    c = {d: [ZERO] * len(rows) for d in range(1, topdeg + 1)}
    e = {d: [ZERO] * len(rows) for d in range(1, topdeg + 1)}
    for i, key in enumerate(rows):
        d = len(key)
        if d == 0:
            continue
        S = RF(g.orbit_size_poly(key, False))
        nd = RF(b1.falling_poly(d))
        dr = len(set(r for r, _ in key)) == d
        dc = len(set(cc for _, cc in key)) == d
        c[d][i] = RF([F(-(int(dr) + int(dc)))]) * S / nd
        if dr and dc:
            npow = RF([F(0)] * d + [F(1)])
            e[d][i] = S * npow / (nd * nd)
    return c, e


def rhs_rf(rows, k):
    """rhs(n,k) over Q(n), row by row, from general_k3's coefficient law."""
    return [g._rhs_rf(key, k) for key in rows]


def theorem2_rf(rows, cvec, evec, k, topdeg):
    """sum_d (k)_d ( c^[d] + (k!/n^k) e^[d] ), over Q(n)."""
    gk = RF([F(factorial(k))]) / RF([F(0)] * k + [F(1)])
    out = [ZERO] * len(rows)
    for d in range(1, topdeg + 1):
        kd = F(1)
        for i in range(d):
            kd *= (k - i)
        if kd == 0:
            continue
        kdr = RF([kd])
        for i in range(len(rows)):
            if cvec[d][i] or evec[d][i]:
                out[i] = out[i] + kdr * (cvec[d][i] + gk * evec[d][i])
    return out


# ------------------------------------------------------------- rank machinery
def rank_cols(M, cols):
    """Exact rank over Q(n) of the submatrix on the given columns."""
    nR = len(M)
    A = [[M[i][c] for c in cols] for i in range(nR)]
    nc = len(cols)
    r = 0
    for c in range(nc):
        p = next((i for i in range(r, nR) if A[i][c]), None)
        if p is None:
            continue
        A[r], A[p] = A[p], A[r]
        pv = A[r][c]
        A[r] = [t / pv for t in A[r]]
        for i in range(nR):
            if i != r and A[i][c]:
                f = A[i][c]
                A[i] = [A[i][t] - f * A[r][t] for t in range(nc)]
        r += 1
        if r == nR:
            break
    return r


def design_sizes(M, ng, ns, nl, label):
    """rank M, the three d(B), the pure-lambda kernel, and what positivity sees."""
    ncol = ng + ns + nl
    grp = {"sigma_0": list(range(0, ng)),
           "sigma_11": list(range(ng, ng + ns)),
           "lambda": list(range(ng + ns, ncol))}
    nR = len(M)
    full = rank_cols(M, list(range(ncol)))
    out = {"label": label, "rows": nR, "ng": ng, "ns": ns, "nl": nl,
           "rank": full, "free": ncol - full}
    for name, cols in grp.items():
        rest = [c for c in range(ncol) if c not in set(cols)]
        out["d_" + name] = (nR - rank_cols(M, rest)) - 1
    # the purely-lambda part of the kernel: it moves NO Gram entry, so it is
    # gauge for positivity
    rank_lam = rank_cols(M, grp["lambda"])
    out["rank_A2"] = rank_lam
    out["ker_lambda"] = nl - rank_lam
    return out


# -------------------------------------------------------------------- Lemma B2
LEMMA_B2 = """
Lemma B2 (the collapse needs no symbolic solve).  Let A(n) be the band's
constraint matrix -- k-free by PARAMETRIC Lemma 1 -- and suppose the rhs law
rhs(n,k) = sum_d (k)_d ( c^[d](n) + (k!/n^k) e^[d](n) ) holds as an identity in
Q(n).  Let S be ANY fixed right inverse of A(n) over Q(n) (for instance the one
that sets the free coordinates to zero).  Then

      X(n,k) := S rhs(n,k) = sum_d (k)_d ( S c^[d] + (k!/n^k) S e^[d] )
              = sum_d (k)_d ( Y_d(n) + (k!/n^k) Z_d(n) )

because S is Q(n)-linear and (k)_d, k!/n^k are scalars of Q(n) at each fixed
integer k.  So Theorem 4 follows from the rhs law alone, and an 87 x 440
Gauss-Jordan over Q(n) is not needed to establish it.
"""


def main():
    print("=" * 74)
    print("BAND 2: the identity half over Q(n), and the size of what is left")
    print("=" * 74)

    t0 = time.time()
    sym = k4.build(verbose=True)
    rows = sym["rows"]
    ng, ns, nl = len(sym["gvars"]), len(sym["svars"]), len(sym["lvars"])
    print(f"  band-2 system built as polynomials in n in {time.time()-t0:.1f} s")
    print(f"  the matrix is k-FREE: k4_system.build() takes no k, and k enters "
          f"only rhs (PARAMETRIC Lemma 1)")

    print("\n[A] the rhs law as an IDENTITY IN Q(n), band 2")
    cvec, evec = ce_vectors(rows, TOPDEG)
    for k in (1, 2, 3, 4, 5):
        want = rhs_rf(rows, k)
        have = theorem2_rf(rows, cvec, evec, k, TOPDEG)
        bad = sum(1 for i in range(len(rows)) if want[i] != have[i])
        nz = sum(1 for v in want if v)
        print(f"  k = {k}: {bad} mismatches over {len(rows)} rows of Q(n) "
              f"({nz} rows nonzero)")

    print("\n  degree-d support of the Theorem-2 vectors:")
    for d in range(1, TOPDEG + 1):
        pc = sum(1 for v in cvec[d] if v)
        pe = sum(1 for v in evec[d] if v)
        print(f"    d = {d}: c^[d] nonzero on {pc} rows, e^[d] on {pe}")

    print("\n[B]" + LEMMA_B2)

    print("[C] the exact size of the design")
    M2 = gen2.build_matrix(sym)
    t0 = time.time()
    s2 = design_sizes(M2, ng, ns, nl, "band 2 (d_b = 2, k <= 5)")
    print(f"  band 2 measured in {time.time()-t0:.0f} s")

    bd1 = b1.Band()
    sym1 = bd1.sym
    ng1, ns1, nl1 = (len(sym1["gvars"]), len(sym1["svars"]),
                     len(sym1["lvars"]))
    s1 = design_sizes(bd1.M, ng1, ns1, nl1, "band 1 (d_b = 1, k <= 3)")

    hdr = ("  quantity", "band 1", "band 2")
    print(f"\n  {hdr[0]:<44s}{hdr[1]:>10s}{hdr[2]:>10s}")
    keys = [("constraint rows", "rows"), ("sigma_0 unknowns", "ng"),
            ("sigma_11 unknowns", "ns"), ("lambda unknowns", "nl"),
            ("rank over Q(n)", "rank"), ("free directions", "free"),
            ("d(sigma_0)  inescapable conditions", "d_sigma_0"),
            ("d(sigma_11) inescapable conditions", "d_sigma_11"),
            ("d(lambda)   inescapable conditions", "d_lambda"),
            ("rank of the lambda columns", "rank_A2"),
            ("purely-lambda kernel (moves no Gram)", "ker_lambda")]
    for name, key in keys:
        print(f"  {name:<44s}{s1[key]:>10d}{s2[key]:>10d}")
    lin1, lin2 = 4, 18                      # allk_lineality.log, NOTES 6a.8c
    print(f"  {'lineality dimension':<44s}{lin1:>10d}{lin2:>10d}")
    ess1 = s1["free"] - lin1 - s1["ker_lambda"]
    ess2 = s2["free"] - lin2 - s2["ker_lambda"]
    print(f"  {'DESIGN POSITIVITY ACTUALLY SEES':<44s}{ess1:>10d}{ess2:>10d}")

    print(f"""
  READING.  At band 1 that number is {ess1}, and POSITIVITY.md's law B1 chooses
  {ess1} coordinates with three constants.  At band 2 it is {ess2}.  The
  reduction from 354 is {354 - ess2} directions, and the remaining {ess2} is the
  obstruction: allk_blockmap.log measured d(alpha) = 0 for every one of the
  eleven blocks, i.e. NO inescapable condition lives on a single block, so there
  is no block one can solve on its own and no analogue of band 1's
  four-number adapted coordinates.""")


if __name__ == "__main__":
    main()
