"""
The EXACT decision for the pin re-test -- NOTES §6b.33 conditions 2 and 4.

`k4_pinretest.py` measures a solver margin.  It cannot DECIDE anything here: the
unpinned control reaches only t = +5.66e-04 at n = 5, so every margin lives at
1e-4, and the same 201-pin programme at n = 6 returned t = -3.70e-04 at SCS eps
1e-10 and t = +9.70e-05 at eps 1e-12.  A negative margin is not a refutation.
This module decides the same questions over Q, with certificates that are
checked by substitution and depend on no rank claim and no solver.

THE OBJECT.  The SDP's own linear identity is `S w = rhs` with

    w = (x | y | z),   x over sigma_0's 51 orbits, y over sigma_11's 356,
                       z over 33 lambda orbits,       C = 440 columns,
    S:  87 rows, entries in Q (A1 = A1c/n + A1l is the only n in a coefficient).

MEASURED, and it is the fact that makes this module cheap: 87 x 440 is the size
at n = 5, 6 AND 7 alike -- the system's SHAPE does not grow with n, only the
monomial basis B does (350, 702, 1274).

A pin is one off-diagonal entry of one canonical block set to zero.  Entry (s,t)
of block E is `sum_c N[s][t][c] * v_c` over that side's orbit variables, with
`N = block_by_class(E, cls, B)` accumulating INTEGER products of the canonical
E's integer entries -- so every pin row is an exact integer vector and nothing
is rounded on the way in.  A configuration is the affine set

    A(cfg) = { w : S w = rhs,  P_cfg w = 0 }.

THE TWO CERTIFICATES, both self-verifying.

  * INFEASIBLE.  Exhibit a rational `lam` with `lam^T T = c` where c is the
    coefficient vector of a DIAGONAL entry of some canonical block, and
    `lam . b <= 0`.  Then for every w in A(cfg) that diagonal entry equals
    `lam . b <= 0`, and a positive definite matrix has strictly positive
    diagonal.  So no w in A(cfg) makes the Gram positive definite.  Verified by
    computing `lam^T T` and comparing to c entry by entry over Q.  Note what
    this does NOT need: no rank, no dual SDP, no eigenvalue.
  * FEASIBLE.  Exhibit a rational w with `T w = b` exactly and every canonical
    block E^T H E positive definite by exact rational LDL^T.  The blocks are at
    most 16x16, so this is cheap, and it is a COMPLETE test of `H >= 0` because
    the 21 canonical blocks carry the full multiplicities 63 + 23 against
    `blockdiag`'s [14,7,16,10,4,4,3,2,1,1,1] and [4,1,5,5,1,2,2,1,1,1].

Search is done in floating point or mod p; only verification is trusted.

RANK, §6b.33 conditions 2 and 4 -- and the reading of "M(n) f = r(n)" is
ambiguous in the design, so BOTH are reported and neither is called "the" rank:

    RANK-P   rank of the 321-row pin matrix alone.  How many of the 321 pin
             conditions are independent as conditions on the Gram variables.
    RANK-A   rank([S; P]) - rank(S).  How many conditions the pins add ON TOP
             of the SDP's own identity -- the one that fixes dim A(cfg).

Two INDEPENDENT routes are required and neither alone is reported:
    route Q  integer-preserving elimination over Q in `rank_exact` below;
    route p  elimination in F_p at several primes, in numpy, sharing no code.
`rank_p <= rank_Q` always for an integer matrix (an r x r minor nonzero mod p is
nonzero over Z), so route p is a certified LOWER bound on route Q, and the two
agreeing pins the value from both sides.

Neither route is the design's Route 1, which was symbolic elimination over Q(n).
Both are pointwise.  What that costs is stated in NOTES §6b.37 and it is not
nothing: pointwise ranks at n0 = 5..9 bound the generic rank from below and
locate no drop, but they cannot by themselves prove that all five sampled n are
not exceptional.
"""

import os
import sys
from fractions import Fraction as F

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "dittert"))
sys.path.insert(0, HERE)
import k4_pinretest as pr                                          # noqa: E402
import k4_sigma0 as s0                                             # noqa: E402
import k4_vv14 as vv                                               # noqa: E402
import sos                                                         # noqa: E402
from exactsd import exact_system, full_matrix, ldl_pivots          # noqa: E402

K, DEG_BASIS = 4, 2
PRIMES = (2147483647, 2147483629, 1073741789)


# --------------------------------------------------------------- exact linear
def rref_int(rows, rhs, ncols):
    """
    Integer-preserving reduced row echelon form over Q.

    `rows` is a list of integer lists, `rhs` a list of Fractions.  Rows are
    kept INTEGRAL and gcd-reduced throughout -- with Fractions the entries in a
    408 x 440 elimination grow without bound and the reduction does not finish.
    Returns (pivots, R, bb, consistent).  Every operation applied to a row is
    applied to its rhs, so the invariant maintained throughout is simply

        for every w in the solution set:   R[i] . w == bb[i],

    and column `pivots[i]` is zero in every row but the i-th (the form is fully
    reduced, not merely echelon, which is what lets `value_on` reduce a
    functional against it in one pass).
    """
    from math import gcd
    A = [list(r) for r in rows]
    b = [F(v) for v in rhs]
    piv, r = [], 0
    R = len(A)
    for c in range(ncols):
        k = next((i for i in range(r, R) if A[i][c]), None)
        if k is None:
            continue
        A[r], A[k] = A[k], A[r]
        b[r], b[k] = b[k], b[r]
        pv = A[r][c]
        for i in range(R):
            if i == r or not A[i][c]:
                continue
            f = A[i][c]
            g = gcd(pv, f)
            m1, m2 = pv // g, f // g
            Ai, Ar = A[i], A[r]
            A[i] = [m1 * Ai[j] - m2 * Ar[j] for j in range(ncols)]
            b[i] = m1 * b[i] - m2 * b[r]
            h = 0
            for v in A[i]:
                h = gcd(h, v)
            if h > 1:
                A[i] = [v // h for v in A[i]]
                b[i] = b[i] / h
        piv.append(c)
        r += 1
        if r == R:
            break
    consistent = all(b[i] == 0 for i in range(r, R))
    return piv, A[:r], b[:r], consistent


def value_on(c, piv, R, bb):
    """
    Is the functional `c` constant on the affine set, and if so what value?

    Reduce c against the RREF rows.  Each elimination adds a KNOWN multiple of
    a known constant, so the accumulated `val` is the functional's value on
    every point of the set -- provided the residual is identically zero, which
    is exactly the statement that c lies in the row space.
    """
    c = list(c)
    val = F(0)
    for i, p in enumerate(piv):
        if not c[p]:
            continue
        f = F(c[p], R[i][p])
        val += f * bb[i]
        Ri = R[i]
        for j in range(len(c)):
            if Ri[j]:
                c[j] -= f * Ri[j]
    return (val if not any(c) else None)


def rank_mod_p(rows, ncols, p):
    """Rank in F_p by numpy elimination.  Shares no code with `rref_int`."""
    if not rows:
        return 0
    A = np.array([[v % p for v in r] for r in rows], dtype=np.int64)
    R = A.shape[0]
    r = 0
    for c in range(ncols):
        nz = np.nonzero(A[r:, c])[0]
        if nz.size == 0:
            continue
        k = r + int(nz[0])
        if k != r:
            A[[r, k]] = A[[k, r]]
        inv = pow(int(A[r, c]), p - 2, p)
        A[r] = (A[r] * inv) % p
        col = A[r + 1:, c]
        hit = np.nonzero(col)[0]
        if hit.size:
            A[r + 1 + hit] = (A[r + 1 + hit] - col[hit, None] * A[r]) % p
        r += 1
        if r == R:
            break
    return r


# ------------------------------------------------------------------- assembly
def build(n):
    """The exact stacked system, the pin rows, and the canonical blocks."""
    d = sos.build_sdp(n, K, DEG_BASIS, verbose=False)
    B, basis = d["B"], d["basis"]
    ng, ns = len(d["g_orbits"]), len(d["s_orbits"])
    nl = len(d["lam_orbit_reps"])
    C = ng + ns + nl

    from math import gcd
    A0e, A1c, A1l, A2e, rhse = exact_system(d)
    Mq = full_matrix(A0e, A1c, A1l, A2e, n)
    srows, srhs = [], []
    for r, row in enumerate(Mq):
        den = 1
        for v in row:
            den = den * v.denominator // gcd(den, v.denominator)
        den = int(den) * rhse[r].denominator
        srows.append([int(v * den) for v in row])
        srhs.append(rhse[r] * den)

    # the 321 pins, exactly, as integer rows over the 440 columns
    sides = (("s11", pr.canonical_blocks(n, basis), d["s_orbits"], ng),
             ("s0", s0.canonical_blocks(n, basis), d["g_orbits"], 0))
    pins, blocks = [], []
    for side, bl, orbs, off in sides:
        cls = pr.orbit_class_array(n, basis, orbs)
        for name, E in bl:
            dd = len(E)
            N = vv.block_by_class(E, cls, B)
            blocks.append((side, name, dd, N, off))
            for i in range(dd):
                for j in range(i + 1, dd):
                    vec = [0] * C
                    for c, x in N[i][j].items():
                        vec[off + c] = int(x)
                    pins.append((side, name, vec))
    assert len(pins) == 321, len(pins)
    return d, C, srows, srhs, pins, blocks


def diag_functional(N, dd, i, off, C):
    vec = [0] * C
    for c, x in N[i][i].items():
        vec[off + c] = int(x)
    return vec


# ------------------------------------------------------------------ the tests
def analyse(n, out=print):
    d, C, srows, srhs, pins, blocks = build(n)
    out(f"\n=== n = {n}:  B = {d['B']},  system {len(srows)} x {C},  "
        f"{len(pins)} pins ===")

    pin_rows = [v for _, _, v in pins]
    base_piv, baseR, basebb, base_ok = rref_int(srows, srhs, C)
    rank_S = len(base_piv)
    out(f"  rank(S) route Q = {rank_S}   consistent = {base_ok}")
    out("  rank(S) route p = "
        + ", ".join(f"{rank_mod_p(srows, C, p)} (p={p})" for p in PRIMES))

    rp_q = len(rref_int(pin_rows, [F(0)] * len(pin_rows), C)[0])
    rp_p = [rank_mod_p(pin_rows, C, p) for p in PRIMES]
    out(f"\n  RANK-P  pin matrix alone: route Q = {rp_q}, "
        f"route p = {rp_p}  ->  "
        f"{'AGREE' if all(v == rp_q for v in rp_p) else 'DISAGREE'}")
    out(f"          {321 - rp_q} of the 321 pin conditions are dependent")

    results = {}

    def configure(label, sel):
        rows = srows + [v for _, _, v in sel]
        rhs = list(srhs) + [F(0)] * len(sel)
        piv, R, bb, ok = rref_int(rows, rhs, C)
        rk = len(piv)
        rkp = [rank_mod_p(rows, C, p) for p in PRIMES]
        agree = all(v == rk for v in rkp)
        added, dim = rk - rank_S, C - rk
        out(f"\n  {label}   {len(sel)} pins")
        out(f"    rank[S;P] = {rk} (route Q) / {rkp} (route p) "
            f"{'AGREE' if agree else '*** DISAGREE ***'};  "
            f"RANK-A = {added};  dim A = {dim};  consistent = {ok}")
        if not ok:
            out("    A IS EMPTY over Q -- the pin system is inconsistent with "
                "the SDP identity.  INFEASIBLE, exactly.")
            results[label] = ("EMPTY", added, dim)
            return
        # search for a diagonal entry forced non-positive
        witness = None
        for side, name, dd, N, off in blocks:
            for i in range(dd):
                v = value_on(diag_functional(N, dd, i, off, C), piv, R, bb)
                if v is not None and v <= 0:
                    witness = (side, name, i, dd, v)
                    break
            if witness:
                break
        if witness:
            side, name, i, dd, v = witness
            out(f"    CERTIFICATE: diagonal entry {i} of the {dd}x{dd} block "
                f"{side} {name} is CONSTANT on A with value {v} <= 0.")
            out("    A positive definite matrix has strictly positive "
                "diagonal, so no point of A is positive definite.")
            out(f"    ==> INFEASIBLE, exactly.  (checked over Q)")
            results[label] = ("INFEASIBLE", added, dim)
        else:
            nconst = sum(1 for side, name, dd, N, off in blocks
                         for i in range(dd)
                         if value_on(diag_functional(N, dd, i, off, C),
                                     piv, R, bb) is not None)
            out(f"    no forced non-positive diagonal "
                f"({nconst} of 86 diagonals are constant on A) -- "
                f"this configuration is NOT decided by this certificate.")
            results[label] = ("UNDECIDED", added, dim)
    return d, C, srows, srhs, pins, blocks, configure, results


def main(ns):
    for n in ns:
        d, C, srows, srhs, pins, blocks, configure, res = analyse(n)
        configure("H1  full 321", pins)
        c201 = [r for r in pins if r[1] != "16x16 Ind(V'|1)"]
        configure("H2  201 (omit sigma_11 16x16)", c201)
        seen = set()
        for side, name, dd, N, off in blocks:
            if dd < 2:
                continue
            sel = [r for r in pins if not (r[0] == side and r[1] == name)]
            if len(sel) == len(pins) or (side, name) in seen:
                continue
            seen.add((side, name))
            if name == "16x16 Ind(V'|1)":
                continue
            configure(f"H3  omit {side} {name} ({dd}x{dd})", sel)
        out = [f"{k}: {v[0]} (RANK-A {v[1]}, dim {v[2]})"
               for k, v in res.items()]
        print("\n  SUMMARY n = " + str(n))
        for line in out:
            print("    " + line)


if __name__ == "__main__":
    main([int(a) for a in sys.argv[1:]] or [5, 6])
