"""
THE THREE d = 4 CROSS TERMS: exact reductions, bounds, and the final k = 4 table.

Completes graded_assembly_k4.py.  Every cross term of the (k = 4) assembly now has
an EXACT reduction, verified against brute force, and a bound derived from it — no
orderings, no measured-only quantities in the table.

THE REDUCTIONS.  L = b_line with L_ij = x_i + y_j, z doubly centred, r and s the
row and column squared norms of z, H = z z^T, G = z^T z, f_3(a) = sum_b z_ab^3,
g_3(b) = sum_a z_ab^3, p = ||x||^2, q = ||y||^2, Q = ||z||_F^2.

  d = 3   (from the k = 3 template, reused)
    X_1 = (n-2)^2 x^T z y
    X_2 = (2-n)(sum_i x_i r_i + sum_j y_j s_j) =: (2-n) Xinv

  d = 4   (derived here)
    Y_1 = -(n-2)(n-3)^2 [ x^T z (y*y) + (x*x)^T z y ]
          Mechanism: on I = [n]\\{a}, J = [n]\\{b} the restricted line block has
          e_1(x_I) = -x_a, e_1(y_J) = -y_b, and e_2(y_J) = e_2(y) + y_b^2.  In the
          (S4) closed form for sigma_3 the t = 0 and t = 3 terms depend on b alone
          and a alone and are annihilated; the t = 1, 2 terms leave x_a y_b^2 and
          x_a^2 y_b.

    Y_2 = (n-2)(n-3) [ -sum_{s1<s2} H_{s1s2} e_2(x_I) - sum_{t1<t2} G_{t1t2} e_2(y_J) ]
          + 2 (n-3)^2 sum_ij z_ij^2 x_i y_j
          Mechanism: the two e_2 pieces depend on S alone and T alone, and
          sum_T per(z[S|T]) = -H_{s1s2}, sum_S per(z[S|T]) = -G_{t1t2}.  The x_S y_T
          piece has VANISHING LIFT: the unrestricted four-index sum is identically
          zero because every expanded piece carries a lone sum_s z_st or sum_t z_st.
          So it is a pure diagonal correction, and equals 2 sum_ij z_ij^2 x_i y_j.
          An absolute-value bound discards exactly that cancellation and overshoots
          by four orders.

    Y_3 = -(n-3) [ 2 A1 - A2 + 2 A3 - A4 ],
          A1 = sum_a x_a f_3(a), A2 = x^T z s, A3 = sum_b y_b g_3(b), A4 = r^T z y
          Mechanism: sigma_1(L^(S,T)) = -(n-3)(x_S + y_T), and
          sum_{S,T} per(z[S|T]) x_S = sum_a x_a Psi_a with
          Psi_a = sum_b z_ab sigma_2(z^(a,b)) = 2 f_3(a) - (z s)_a.

CHARGING.  A cross term with j factors of z and 4-j of L carries (p+q)^((4-j)/2),
so Y_1 (three L) and Y_2 (two L) divide cleanly by (p+q) and go to LINE; Y_3 (one
L) carries sqrt(p+q) and is split between both budgets by AM-GM.

TWO CHECKS ADDED AFTER SLIPS OF MINE, both of which shipped in earlier drafts:
  * THE t_d CHECK.  A cross term from layer d enters the budget as t_d times the
    term.  I once omitted t_4 and caught it only because the number was absurd —
    absurdity is not a control.  PART 2 verifies the END-TO-END IDENTITY
        F(B) = F_line(x,y) + F_centred(z) + sum_d t_d (cross parts of sigma_d),
    with F(B) computed from the 1992 functional.  A missing or wrong t_d fails it.
  * THE NON-VACUITY CHECK.  A bound is only tested by configurations where the
    bounded quantity is nonzero, and my structured configurations gave Y_3 = 0
    identically.  PART 3 asserts, for every cross term, that the pricing set
    contains a configuration where it is provably nonzero.

Usage:  GUARD_MEM=8G GUARD_CPUS=250% GUARD_THREADS=2 ../guard.sh \
            python3 -u graded_y_bounds.py
"""

import random
import sys
from fractions import Fraction as Fr
from itertools import combinations
from math import comb, isqrt

from graded_assembly_k4 import _per, delete, lmat, sigma_of, split
from graded_layers import elem_sym
from pincer_line import (F_line, lam_line, line_margin, s_coef, t_coef, u_max)
from pincer_onesided import deficit_centred, sigma_d

OUT = []
FAIL = 0


def log(*a):
    s = " ".join(str(x) for x in a)
    print(s)
    OUT.append(s)


def check(name, ok):
    global FAIL
    if not ok:
        FAIL += 1
        log(f"    *** FAIL: {name}")
    return ok


def sq(x, D=10 ** 12):
    if x == 0:
        return Fr(0)
    r = isqrt(x.numerator * D * D // x.denominator) + 1
    out = Fr(r, D)
    assert out * out >= x
    return out


def rho2(n, k):
    return Fr(n - 1) * Fr(24 if k == 4 else 6, n ** (k - 1))


# ------------------------------------------------------------ collar sampler


def generic_collar(n, k=4, want=4, rng=None):
    r2 = rho2(n, k)
    out = []
    for _ in range(20000):
        w = [[Fr(rng.randint(1, 20)) for _ in range(n)] for _ in range(n)]
        tot = sum(sum(r) for r in w)
        A = [[w[i][j] * n / tot for j in range(n)] for i in range(n)]
        R = [sum(A[i][j] for j in range(n)) - 1 for i in range(n)]
        C = [sum(A[i][j] for i in range(n)) - 1 for j in range(n)]
        if sum(v * v for v in R) + sum(v * v for v in C) > r2:
            continue
        out.append(A)
        if len(out) >= want:
            break
    return out


# ------------------------------------------------------ the exact reductions


def invariants(A, n):
    x, y, z = split(A, n)
    L = lmat(x, y, n)
    r = [sum(z[i][j] ** 2 for j in range(n)) for i in range(n)]
    s = [sum(z[i][j] ** 2 for i in range(n)) for j in range(n)]
    f3 = [sum(z[i][j] ** 3 for j in range(n)) for i in range(n)]
    g3 = [sum(z[i][j] ** 3 for i in range(n)) for j in range(n)]
    H = [[sum(z[a][t] * z[b][t] for t in range(n)) for b in range(n)]
         for a in range(n)]
    G = [[sum(z[t][a] * z[t][b] for t in range(n)) for b in range(n)]
         for a in range(n)]
    p = sum(v * v for v in x)
    q = sum(v * v for v in y)
    Q = sum(z[i][j] ** 2 for i in range(n) for j in range(n))
    rng_ = range(n)
    X1 = Fr((n - 2) ** 2) * sum(x[a] * z[a][b] * y[b] for a in rng_ for b in rng_)
    Xinv = sum(x[i] * r[i] for i in rng_) + sum(y[j] * s[j] for j in rng_)
    X2 = Fr(2 - n) * Xinv
    Y1 = -Fr((n - 2) * (n - 3) ** 2) * (
        sum(x[a] * z[a][b] * y[b] ** 2 for a in rng_ for b in rng_)
        + sum(x[a] ** 2 * z[a][b] * y[b] for a in rng_ for b in rng_))
    m = n - 2

    def e2x(S):
        return ((x[S[0]] + x[S[1]]) ** 2 - p + x[S[0]] ** 2 + x[S[1]] ** 2) / 2

    def e2y(T):
        return ((y[T[0]] + y[T[1]]) ** 2 - q + y[T[0]] ** 2 + y[T[1]] ** 2) / 2
    Y2 = (2 * comb(m, 2)
          * (-sum(H[S[0]][S[1]] * e2x(S) for S in combinations(rng_, 2))
             - sum(G[T[0]][T[1]] * e2y(T) for T in combinations(rng_, 2)))
          + Fr((m - 1) ** 2) * 2
          * sum(z[i][j] ** 2 * x[i] * y[j] for i in rng_ for j in rng_))
    A1 = sum(x[a] * f3[a] for a in rng_)
    A2 = sum(x[a] * sum(z[a][j] * s[j] for j in rng_) for a in rng_)
    A3 = sum(y[b] * g3[b] for b in rng_)
    A4 = sum(y[b] * sum(z[i][b] * r[i] for i in rng_) for b in rng_)
    Y3 = -Fr(n - 3) * (2 * A1 - A2 + 2 * A3 - A4)
    return dict(x=x, y=y, z=z, L=L, p=p, q=q, Q=Q, X1=X1, X2=X2, Xinv=Xinv,
                Y1=Y1, Y2=Y2, Y3=Y3, r=r, s=s)


def brute_cross(L, z, d, n):
    """The j = 1 .. d-1 cross parts of sigma_d(z + L), by brute force."""
    parts = []
    for j in range(1, d):
        tot = Fr(0)
        for S in combinations(range(n), j):
            for T in combinations(range(n), j):
                pz = _per([[z[i][jj] for jj in T] for i in S])
                if pz:
                    tot += pz * sigma_of(delete(L, set(S), set(T), n), d - j)
        parts.append(tot)
    return parts


def part1(rng):
    log("=" * 74)
    log("PART 1.  THE FIVE EXACT REDUCTIONS, against brute force.")
    log("=" * 74)
    bad = 0
    for n in (5, 6, 7):
        ok = True
        for A in generic_collar(n, rng=rng):
            v = invariants(A, n)
            c3 = brute_cross(v["L"], v["z"], 3, n)
            c4 = brute_cross(v["L"], v["z"], 4, n)
            if c3[0] != v["X1"] or c3[1] != v["X2"]:
                ok = False
            if c4[0] != v["Y1"] or c4[1] != v["Y2"] or c4[2] != v["Y3"]:
                ok = False
        check(f"reductions n={n}", ok)
        log(f"    n={n}: X_1, X_2, Y_1, Y_2, Y_3 all match brute force: {ok}")
        if not ok:
            bad += 1
    log("")
    return bad


def part2(rng):
    log("=" * 74)
    log("PART 2.  THE END-TO-END IDENTITY, with the t_d factors in place.")
    log("=" * 74)
    log("  F(B) from the 1992 functional must equal")
    log("     F_line(x,y) + F_centred(z) + sum_d t_d (cross parts of sigma_d).")
    log("  This is the check that would have caught my omitted t_4.")
    for n in (5, 6):
        k = 4
        ok = True
        for A in generic_collar(n, k, want=2, rng=rng):
            v = invariants(A, n)
            # F from the 1992 functional.  NOT sigma_k/C^2 - k!/n^k: that is
            # the DOUBLY STOCHASTIC form, where E_k(r) = E_k(c) = 1.  On a
            # general collar point the line sums are not 1 and both E_k terms
            # must be computed.  (This check caught that error of mine.)
            R = [sum(A[i][j] for j in range(n)) for i in range(n)]
            C = [sum(A[i][j] for i in range(n)) for j in range(n)]
            N = Fr(comb(n, k))
            Phi = (elem_sym(R, k) / N + elem_sym(C, k) / N
                   - sigma_d(A, k) / (N * N))
            Fdir = (2 - Fr(24, n ** k)) - Phi
            fl = F_line(v["x"], v["y"], n, k)          # float
            fc = deficit_centred(v["z"], n, k)         # exact
            cross = (t_coef(n, k, 3) * (v["X1"] + v["X2"])
                     + t_coef(n, k, 4) * (v["Y1"] + v["Y2"] + v["Y3"]))
            resid = float(Fdir - fc - cross) - fl
            if abs(resid) > 1e-9 * max(1.0, abs(float(Fdir))):
                ok = False
                log(f"    n={n} MISMATCH residual {resid:.3e}")
        check(f"end-to-end identity n={n}", ok)
        log(f"    n={n}: identity holds to float tolerance on F_line: {ok}")
    log("")
    log("  CONTROL: dropping the t_4 factor must BREAK it.")
    for n in (5,):
        broke = False
        for A in generic_collar(n, 4, want=2, rng=rng):
            v = invariants(A, n)
            R = [sum(A[i][j] for j in range(n)) for i in range(n)]
            C = [sum(A[i][j] for i in range(n)) for j in range(n)]
            N = Fr(comb(n, 4))
            Phi = (elem_sym(R, 4) / N + elem_sym(C, 4) / N
                   - sigma_d(A, 4) / (N * N))
            Fdir = (2 - Fr(24, n ** 4)) - Phi
            fl = F_line(v["x"], v["y"], n, 4)
            fc = deficit_centred(v["z"], n, 4)
            bad_cross = (t_coef(n, 4, 3) * (v["X1"] + v["X2"])
                         + (v["Y1"] + v["Y2"] + v["Y3"]))     # t_4 DROPPED
            if abs(float(Fdir - fc - bad_cross) - fl) > 1e-9:
                broke = True
        check("t_4-drop control fires", broke)
        log(f"    n={n}: identity with t_4 dropped is REJECTED: {broke}")
    log("")


def part3(rng):
    log("=" * 74)
    log("PART 3.  NON-VACUITY: every priced cross term is nonzero somewhere in")
    log("         the pricing set.")
    log("=" * 74)
    log("  My structured configurations gave Y_3 = 0 identically, so a pricing")
    log("  run on them proved nothing.  Generic collar points are used instead,")
    log("  and each term is asserted nonzero on at least one of them.")
    for n in (5, 6, 7):
        pts = generic_collar(n, rng=rng)
        nz = {kk: 0 for kk in ("X1", "X2", "Y1", "Y2", "Y3")}
        for A in pts:
            v = invariants(A, n)
            for kk in nz:
                if v[kk] != 0:
                    nz[kk] += 1
        for kk in nz:
            check(f"non-vacuous {kk} n={n}", nz[kk] > 0)
        log(f"    n={n}: nonzero counts over {len(pts)} points "
            + "  ".join(f"{kk}={nz[kk]}" for kk in
                        ("X1", "X2", "Y1", "Y2", "Y3")))
    log("")


def collar_consts(n, k=4):
    r2 = rho2(n, k)
    rho = sq(r2)
    um = u_max(n, k)
    beta_c = 1 + rho - Fr(1, n)
    beta_z = beta_c + 2 * sq(um)
    Op_c = sq((1 + rho) ** 2 + r2 / n)
    Op_z = Op_c + sq(2 * n * um)
    M_c = (1 + rho) ** 2 - Fr(1, n) + 2 * rho / n
    Q_c = Fr(n - 1) + r2
    return dict(rho=rho, um=um, beta=beta_z, Op=Op_z, M=M_c, Q=Q_c)


def budget(n, k=4, cond=False):
    c = collar_consts(n, k)
    t2, t3, t4 = t_coef(n, k, 2), t_coef(n, k, 3), t_coef(n, k, 4)
    s2 = s_coef(n, k, 2)
    qb, lam = t2 / 2, lam_line(n, k) / 2
    um, Qc, Mc, bz, Op = c["um"], c["Q"], c["M"], c["beta"], c["Op"]
    # ---- Q budget
    core3 = t3 * Fr(2, 3 * n) / qb
    core4 = t4 * (Fr(1, 32) if cond else Fr(3, 2) * (1 - Fr(1, n))) / qb
    xinv = Fr(3 * n - 4, 3) * sq(2 * um)
    # Y_3 split by AM-GM: sqrt(2(p+q)) sqrt(MQ) <= d(p+q) + M Q/(2d)
    K3 = t4 * Fr(n - 3) * (2 * bz + Op)
    delta = sq(lam * Mc / (2 * t2)) if t2 else Fr(1)
    y3q = K3 * Mc / (2 * delta) / qb
    y3l = K3 * delta / lam
    Qtot = core3 + core4 + xinv + y3q
    # ---- LINE budget
    marg = line_margin(n, k, True)
    tail = Fr(1) / Fr(marg).limit_denominator(10 ** 9) if marg > 0 else Fr(9)
    x1 = t3 * Fr((n - 2) ** 2, 2) * sq(Qc) / lam
    y1 = t4 * Fr((n - 2) * (n - 3) ** 2) * Op * sq(um) / lam
    y2 = (t4 * Qc * Fr((n - 2) * (n - 3) * (n - 1) + (n - 3) ** 2) / lam)
    Ltot = tail + x1 + y1 + y2 + y3l
    return Qtot, Ltot, dict(core3=core3, core4=core4, xinv=xinv, y3q=y3q,
                            tail=tail, x1=x1, y1=y1, y2=y2, y3l=y3l)


def part4():
    log("=" * 74)
    log("PART 4.  THE FINAL k = 4 TABLE.  All cross terms BOUNDED.")
    log("=" * 74)
    log("  Q budget pieces: m=3 core, m=4 core, Xinv (merged, coefficient")
    log("  (3n-4)/3), and Y_3's AM-GM share.  LINE pieces: line tail, X_1, Y_1,")
    log("  Y_2, and Y_3's AM-GM share.")
    log("")
    log("   n |   Q tot | LINE tot | honest |  Q tot (cond) | cond")
    for n in list(range(6, 21)) + [25, 30]:
        qh, lh, _ = budget(n, 4, False)
        qc, lc, _ = budget(n, 4, True)
        log(f"  {n:3d} | {float(qh):7.4f} | {float(lh):8.4f} |"
            f" {str(qh < 1 and lh < 1):6s} | {float(qc):13.4f} |"
            f" {qc < 1 and lc < 1}")
    log("")
    for lab, cond in (("HONEST (crude sigma_4)", False),
                      ("CONDITIONAL (parked eps = 1/32)", True)):
        thr = None
        for n in range(5, 400):
            q, l, _ = budget(n, 4, cond)
            if q < 1 and l < 1:
                thr = n
                break
        log(f"  {lab}: closes for (k = 4, n >= {thr})")
    log("")
    log("  BREAKDOWN at the honest threshold and above:")
    log("   n | core3  | core4  | Xinv   | Y3(Q)  | tail   | X1     | Y1"
        "     | Y2     | Y3(L)")
    for n in (11, 12, 16, 20):
        q, l, d = budget(n, 4, False)
        log(f"  {n:2d} | " + " | ".join(f"{float(d[kk]):6.4f}" for kk in
            ("core3", "core4", "xinv", "y3q", "tail", "x1", "y1", "y2",
             "y3l")))
    log("")


def main():
    rng = random.Random(20260815)
    log("=" * 74)
    log("THE d = 4 CROSS TERMS: REDUCTIONS, BOUNDS, AND THE FINAL k = 4 TABLE")
    log("=" * 74)
    log("")
    part1(rng)
    part2(rng)
    part3(rng)
    part4()
    log("=" * 74)
    log(f"TOTAL FAILURES: {FAIL}")
    log("=" * 74)
    with open("results/graded_y_bounds.log", "w") as fh:
        fh.write("\n".join(OUT) + "\n")
    return 0 if FAIL == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
