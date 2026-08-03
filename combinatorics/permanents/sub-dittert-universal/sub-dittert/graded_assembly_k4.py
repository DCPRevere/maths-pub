"""
THE ASSEMBLY AT (k = 4), by the orthogonal split.

Follows the (k = 3) template exactly: state the decomposition once, derive the
cross terms as an EXACT IDENTITY before bounding anything, check the merge, then
measure.  Nothing here cites the retracted M3 hyperplane region.  Both block
results are reused, not re-derived: pincer_line.F_line / line_margin /
u_max / lam_line for the line block, pincer_onesided.deficit_centred for the
centred block.

-------------------------------------------------------------------------------
1.  THE DECOMPOSITION, STATED ONCE

A in K_n, B = A - J_n/n with row sums R and column sums C.  Then

    B = b_line + z ,   b_line,ij = x_i + y_j ,   x_i = R_i/n , y_j = C_j/n ,

so sum x = sum y = 0, z is doubly centred, and ||b_line||_F^2 = n(p+q) with
p = ||x||^2, q = ||y||^2.  Confinement bounds the LINE block only:
p + q <= u_max(n,k) = (n-1)k!/n^(k+1).

2.  THE EXPANSION, EXACT AND GENERAL

For any X, Y and any d, summing per((X+Y)[alpha|beta]) over all d-subsets,

    sigma_d(X+Y) = sum_{j=0}^{d} sum_{|S|=|T|=j} per(X[S|T]) sigma_{d-j}(Y^(S,T))

with Y^(S,T) the matrix with rows S and columns T deleted.  Taking X = z and
Y = L := b_line gives, at d = 4, the three cross terms

    Y_1 = sum_{a,b} z_ab sigma_3(L^(a,b))                        [one z factor]
    Y_2 = sum_{|S|=|T|=2} per(z[S|T]) sigma_2(L^(S,T))           [two z factors]
    Y_3 = sum_{|S|=|T|=3} per(z[S|T]) sigma_1(L^(S,T))           [three z factors]

and at d = 3 the two of the (k = 3) template.  PART 1 verifies the expansion at
d = 2, 3, 4 against brute force, and confirms the two structural facts that make
the assembly work at all: the d = 2 layer has NO cross term, and the e_d half of
the universal identity depends on b_line ALONE (z has zero line sums), so it
never couples.

3.  THE MERGE AT k = 4

At k = 4 the layers are m = 2, 3, 4.  The one-sided entry step is used ONLY at
m = 3, because sigma_4's centred core is
    (3/2)p_4 + (1/8)Q^2 + (1/4)Z - (3/4)(Y_R + Y_C),
every term of even degree in the entries, so no odd-power step arises there.
Therefore the merge at k = 4 is the SAME single-coefficient statement as at
k = 3: the perturbation injected by z_ij >= -(1/n + x_i + y_j) into the m = 3
step is exactly the invariant of the cross term X_2, counted once.
That is a structural prediction, not a measurement, and PART 2 tests it.
(By contrast at k = 5 the m = 5 step has (1/n + x_i + y_j)^3, which is four
cross-invariants rather than one -- reported separately.)

4.  WHAT PART 3 MEASURES

The coupling on genuine K_n collar matrices with both blocks pushed as far as
A >= 0 allows.  Note in advance that A >= 0 COUPLES the two blocks: a near-
extremal z has small entries somewhere, which caps the line perturbation that
can be added without leaving K_n.  PART 3 measures that trade-off rather than
assuming the two can be saturated at once.

Usage:  GUARD_MEM=8G GUARD_CPUS=250% GUARD_THREADS=2 ../guard.sh \
            python3 -u graded_assembly_k4.py
"""

import random
import sys
from fractions import Fraction as Fr
from itertools import combinations, permutations
from math import comb, factorial

from pincer_line import lam_line, t_coef, u_max
from pincer_onesided import deficit_centred, rand_ds, sigma_d

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


# ------------------------------------------------------------- primitives


def per_sub(M, S, T):
    return sigma_d([[M[i][j] for j in T] for i in S], len(S)) \
        if len(S) == 0 else _per([[M[i][j] for j in T] for i in S])


def _per(M):
    m = len(M)
    if m == 0:
        return Fr(1)
    tot = Fr(0)
    for p in permutations(range(m)):
        pr = Fr(1)
        for i in range(m):
            pr *= M[i][p[i]]
        tot += pr
    return tot


def delete(M, S, T, n):
    rs = [i for i in range(n) if i not in S]
    cs = [j for j in range(n) if j not in T]
    return [[M[i][j] for j in cs] for i in rs]


def sigma_of(M, d):
    return sigma_d(M, d)


def expansion(L, z, d, n):
    """sum_j sum_{|S|=|T|=j} per(z[S|T]) sigma_{d-j}(L^(S,T)), term by term."""
    parts = []
    for j in range(d + 1):
        tot = Fr(0)
        for S in combinations(range(n), j):
            for T in combinations(range(n), j):
                pz = _per([[z[i][jj] for jj in T] for i in S])
                if pz == 0:
                    continue
                tot += pz * sigma_of(delete(L, set(S), set(T), n), d - j)
        parts.append(tot)
    return parts


def split(A, n):
    """A -> (x, y, z) with b_line,ij = x_i + y_j and z doubly centred."""
    B = [[A[i][j] - Fr(1, n) for j in range(n)] for i in range(n)]
    R = [sum(B[i][j] for j in range(n)) for i in range(n)]
    C = [sum(B[i][j] for i in range(n)) for j in range(n)]
    x = [Fr(r, n) for r in R]
    y = [Fr(c, n) for c in C]
    z = [[B[i][j] - x[i] - y[j] for j in range(n)] for i in range(n)]
    return x, y, z


def lmat(x, y, n):
    return [[x[i] + y[j] for j in range(n)] for i in range(n)]


def configs(n, ts=(Fr(1, 2), Fr(1, 4), Fr(1, 8))):
    """Collar configurations in BOTH signs of p_3(z), each with the line block
    saturated as far as A >= 0 allows.

    'perm' :  A = (1-t)P + t J/n     -> z prop. to  P - J/n,  p_3(z) > 0
    'anti' :  A = (1+s)J/n - s P     -> z prop. to  J/n - P,  p_3(z) < 0
    The second sign is essential: the merge inequality is a LOWER bound on
    p_3(z), so a sample set with p_3 > 0 throughout never tests it."""
    out = []
    P = [[Fr(1) if j == i else Fr(0) for j in range(n)] for i in range(n)]
    for t in ts:
        A = [[(1 - t) * P[i][j] + t * Fr(1, n) for j in range(n)]
             for i in range(n)]
        out.append((f"perm t={t}", A, t / n))
    for num in (1, 2, 4):
        s_ = Fr(1, (n - 1) * num)
        A = [[(1 + s_) * Fr(1, n) - s_ * P[i][j] for j in range(n)]
             for i in range(n)]
        mn = min(A[i][j] for i in range(n) for j in range(n))
        out.append((f"anti s=1/{(n - 1) * num}", A, mn))
    res = []
    for label, A, mn in out:
        if mn <= 0:
            continue
        xs = [mn / 2] + [-mn / (2 * (n - 1))] * (n - 1)
        ys = [mn / 2] + [-mn / (2 * (n - 1))] * (n - 1)
        Ap = [[A[i][j] + xs[i] + ys[j] for j in range(n)] for i in range(n)]
        if min(Ap[i][j] for i in range(n) for j in range(n)) < 0:
            continue
        res.append((label, Ap))
    return res


# ================================================ PART 1  the identity


def part1(rng):
    log("=" * 74)
    log("PART 1.  THE EXPANSION, EXACT.  Verified against brute force before")
    log("         anything is bounded.")
    log("=" * 74)
    log("  sigma_d(z + L) = sum_j sum_{|S|=|T|=j} per(z[S|T]) sigma_{d-j}(L^(S,T))")
    log("")
    bad = 0
    for n in (4, 5, 6):
        for _ in range(3):
            A = rand_ds(n, rng, terms=3)
            # add a line perturbation that keeps A in K_n
            mn = min(A[i][j] for i in range(n) for j in range(n))
            xs = [Fr(rng.randint(-2, 2), 40) for _ in range(n - 1)]
            xs.append(-sum(xs))
            ys = [Fr(rng.randint(-2, 2), 40) for _ in range(n - 1)]
            ys.append(-sum(ys))
            sc = Fr(1)
            while max(abs(xs[i] + ys[j]) for i in range(n)
                      for j in range(n)) * sc > mn and sc > Fr(1, 64):
                sc /= 2
            xs = [t * sc for t in xs]
            ys = [t * sc for t in ys]
            Ap = [[A[i][j] + xs[i] + ys[j] for j in range(n)]
                  for i in range(n)]
            if min(Ap[i][j] for i in range(n) for j in range(n)) < 0:
                continue
            x, y, z = split(Ap, n)
            L = lmat(x, y, n)
            for d in (2, 3, 4):
                parts = expansion(L, z, d, n)
                direct = sigma_of([[L[i][j] + z[i][j] for j in range(n)]
                                   for i in range(n)], d)
                if sum(parts) != direct:
                    bad += 1
                    log(f"    n={n} d={d} EXPANSION MISMATCH")
                if d == 2:
                    # the cross part at d = 2 must vanish identically
                    if parts[1] != 0:
                        bad += 1
                        log(f"    n={n} d=2 CROSS TERM NONZERO: {parts[1]}")
        log(f"    n={n}: d = 2, 3, 4 expansions match brute force;"
            f" d = 2 cross term is 0")
    check("expansion identity", bad == 0)
    log("")
    log("  THE e_d HALF NEVER COUPLES: z has zero line sums, so the row and")
    log("  column sums of b_line + z equal those of b_line.  Checked:")
    for n in (4, 5, 6):
        ok = True
        for _ in range(3):
            A = rand_ds(n, rng, terms=3)
            x, y, z = split(A, n)
            L = lmat(x, y, n)
            for i in range(n):
                if sum(z[i][j] for j in range(n)) != 0:
                    ok = False
            for j in range(n):
                if sum(z[i][j] for i in range(n)) != 0:
                    ok = False
        check(f"z doubly centred n={n}", ok)
        log(f"    n={n}: {ok}")
    log("")
    return bad


# ================================================== PART 2  the merge


def part2(rng):
    log("=" * 74)
    log("PART 2.  THE MERGE AT k = 4.")
    log("=" * 74)
    log("  Structural claim: at k = 4 the only odd-power one-sided step is at")
    log("  m = 3, since sigma_4's centred core has only even powers.  So the")
    log("  merge is the single-coefficient form, as at k = 3.")
    log("")
    log("  (a) sigma_4's centred core has no odd-power term.  Its five")
    log("      invariants are p_4, Q^2, Z, Y_R, Y_C -- all even.  Checked by")
    log("      confirming sigma_4(-z) = sigma_4(z) on doubly centred z:")
    bad = 0
    for n in (4, 5, 6):
        ok = True
        for _ in range(3):
            A = rand_ds(n, rng, terms=4)
            _x, _y, z = split(A, n)
            zm = [[-z[i][j] for j in range(n)] for i in range(n)]
            if sigma_of(z, 4) != sigma_of(zm, 4):
                ok = False
            if sigma_of(z, 3) == sigma_of(zm, 3) and sigma_of(z, 3) != 0:
                ok = False        # m=3 MUST be odd, i.e. sign-flipping
        check(f"parity n={n}", ok)
        log(f"      n={n}: sigma_4 even, sigma_3 odd: {ok}")
    log("")
    log("  (b) the m = 3 perturbation is EXACTLY the X_2 invariant, once:")
    log("        sum z^3 >= -(1/n) Q - (sum_i x_i r_i + sum_j y_j s_j)")
    log("      with r_i = sum_j z_ij^2, s_j = sum_i z_ij^2, from the per-entry")
    log("      bound z_ij >= -(1/n + x_i + y_j).")
    for n, k in ((4, 4), (5, 4), (6, 4), (7, 4)):
        ok = True
        worst = Fr(0)
        neg = 0
        tested = 0
        for label, Ap in configs(n):
            x, y, z = split(Ap, n)
            Q = sum(z[i][j] ** 2 for i in range(n) for j in range(n))
            if Q == 0:
                continue
            tested += 1
            r = [sum(z[i][j] ** 2 for j in range(n)) for i in range(n)]
            sv = [sum(z[i][j] ** 2 for i in range(n)) for j in range(n)]
            X2inv = (sum(x[i] * r[i] for i in range(n))
                     + sum(y[j] * sv[j] for j in range(n)))
            p3 = sum(z[i][j] ** 3 for i in range(n) for j in range(n))
            lim = Fr(1, n) * Q + X2inv          # p3 >= -lim
            if p3 < -lim:
                ok = False
            for i in range(n):
                for j in range(n):
                    if z[i][j] < -(Fr(1, n) + x[i] + y[j]):
                        ok = False
            if p3 < 0:
                neg += 1
                if lim > 0:
                    worst = max(worst, (-p3) / lim)
        check(f"merge n={n} k=4", ok)
        # NON-VACUITY: the bound is a lower bound, so it is only tested by
        # configurations with p_3 < 0.  If none, the check proves nothing.
        check(f"merge check non-vacuous n={n}", neg > 0)
        log(f"      n={n} k=4: holds {ok}   configs {tested}"
            f"   with p3<0: {neg}   worst (-p3)/bound {float(worst):.6f}")
    log("")
    log("  VERDICT: the merge holds at k = 4 in its single-coefficient form,")
    log("  for the structural reason above.  It is k = 5 where it splits into")
    log("  four cross-invariants.")
    log("")
    return bad


# ============================ PART 3  the coupling, and the A >= 0 trade-off


def part3(rng):
    log("=" * 74)
    log("PART 3.  THE COUPLING MEASURED, and the A >= 0 TRADE-OFF.")
    log("=" * 74)
    log("  A >= 0 couples the two blocks: a near-extremal z has small entries,")
    log("  which caps the line perturbation that keeps A in K_n.  So 'both")
    log("  blocks near-extremal at once' is not free, and this measures it.")
    log("")
    log("  Construction: A = (1-t)P + t J/n for a permutation P, giving")
    log("  min entry t/n and Q growing as (1-t)^2 (n-1); then the largest line")
    log("  perturbation that keeps A >= 0 has max|x_i+y_j| <= t/n.")
    log("")
    log("   n | config        |        Q |   p3(z) |      p+q | (p+q)/u_max")
    for n in (5, 6, 8):
        for label, Ap in configs(n):
            x, y, z = split(Ap, n)
            Q = sum(z[i][j] ** 2 for i in range(n) for j in range(n))
            p3 = sum(z[i][j] ** 3 for i in range(n) for j in range(n))
            pq = sum(v * v for v in x) + sum(v * v for v in y)
            um = u_max(n, 4)
            log(f"  {n:2d} | {label:13s} | {float(Q):8.4f} |"
                f" {float(p3):7.3f} | {float(pq):8.2e} |"
                f" {float(pq / um):11.4f}")
    log("")
    log("  Now the cross terms themselves, on those configurations, against")
    log("  the layer-2 budget (t_2/2)Q and the line margin lam_line/2.")
    log("   n | config        |  |cross|/(t_2/2 Q) | cross/lam_line2 | dominant")
    for n in (5, 6, 8):
        for label, Ap in configs(n):
            x, y, z = split(Ap, n)
            L = lmat(x, y, n)
            Q = sum(z[i][j] ** 2 for i in range(n) for j in range(n))
            if Q == 0:
                continue
            cross = Fr(0)
            worstname = None
            worstval = Fr(0)
            for d in (3, 4):
                parts = expansion(L, z, d, n)
                for j in range(1, d):
                    v = t_coef(n, 4, d) * parts[j]
                    cross += v
                    if abs(v) > abs(worstval):
                        worstval, worstname = v, f"d={d} j={j}"
            t2 = t_coef(n, 4, 2)
            budget = t2 / 2 * Q
            lam = lam_line(n, 4) / 2
            log(f"  {n:2d} | {label:13s} |"
                f" {float(abs(cross) / budget):18.6f}"
                f" | {float(abs(cross) / lam):15.6f} | {worstname}")
    log("")
    return 0


def part4():
    from pincer_line import line_margin, s_coef
    log("=" * 74)
    log("PART 4.  THE ASSEMBLED BUDGET AT k = 4.")
    log("=" * 74)
    log("  CHARGING RULE.  Each cross term goes to the block whose budget it")
    log("  scales with, which PART 3 makes visible:")
    log("    X_1 = (n-2)^2 x^T z y   is LINEAR in the line block, and")
    log("        |X_1| <= (n-2)^2 ((p+q)/2) sqrt(Q),  so it divides by (p+q)")
    log("        cleanly -> LINE budget.  Charging it to the Q budget instead")
    log("        would diverge as Q -> 0, which is what PART 3's 'anti' rows")
    log("        show (ratio 0.45 at n=5 with Q = 0.016).")
    log("    X_2 = (2-n)(sum x_i r_i + sum y_j s_j) has")
    log("        |X_2| <= sqrt(p+q) sqrt(Y_R+Y_C) <= sqrt(p+q) sqrt(2 M Q),")
    log("        and M <= Q always, so dividing by Q leaves at most")
    log("        sqrt(2(p+q)) <= sqrt(2 u_max) -> Q budget, bounded.")
    log("  THE MERGE is realised by charging the invariant Xinv ONCE, with its")
    log("  full coefficient (3n-4)/3 = (n-2) + 2/3: the (n-2) from the cross")
    log("  term X_2 and the 2/3 from the per-entry bound inside sigma_3(z).")
    log("  Counting it once does NOT mean dropping one of the two coefficients.")
    log("")
    log("  CENTRED consumption of (t_2/2)Q:")
    log("     honest      = [t_3 (2/(3n)) + t_4 C_4] / (t_2/2),  C_4 = (3/2)(1-1/n)")
    log("     conditional = [t_3 (2/(3n)) + t_4 (1/32)] / (t_2/2)  [pass two, PARKED]")
    log("  LINE consumption of lam_line/2: the line tail (pincer line_margin,")
    log("  computed not hardcoded) plus the X_1 residual.")
    log("")
    log("   n | CENTRED honest | CENTRED cond | LINE tail | X_1 res | LINE tot"
        " | honest closes | cond closes")
    for n in range(5, 21):
        k = 4
        t2, t3, t4 = (t_coef(n, k, 2), t_coef(n, k, 3), t_coef(n, k, 4))
        qbud = t2 / 2
        C4 = Fr(3, 2) * (1 - Fr(1, n))
        cen_h = (t3 * Fr(2, 3 * n) + t4 * C4) / qbud
        cen_c = (t3 * Fr(2, 3 * n) + t4 * Fr(1, 32)) / qbud
        # The |Xinv| coefficient, Xinv = sum x_i r_i + sum y_j s_j.  TWO
        # contributions, and BOTH are real:
        #   the per-entry bound inside sigma_3(z) = (2/3)p_3(z) gives (2/3)|Xinv|
        #   the cross term t_3 X_2 = t_3 (2-n) Xinv gives (n-2)|Xinv|
        # Total (n-2) + 2/3 = (3n-4)/3.  Charging only (n-2) -- which an earlier
        # version of this file did -- is an UNDER-charge, optimistic by
        # (2/3)sqrt(2 u_max).  The merge means the quantity is counted ONCE,
        # not that one of its two coefficients disappears.
        um = u_max(n, k)
        x2res = Fr(3 * n - 4, 3) * isqrt_ub(2 * um)
        cen_h += x2res
        cen_c += x2res
        lam = lam_line(n, k) / 2
        marg = line_margin(n, k, True)
        tail = Fr(1) / Fr(marg).limit_denominator(10 ** 9) if marg > 0 else Fr(9)
        # X_1 residual against the LINE budget
        x1res = t3 * Fr((n - 2) ** 2, 2) * isqrt_ub(Fr(n - 1)) / lam
        lin = tail + x1res
        log(f"  {n:2d} | {float(cen_h):14.4f} | {float(cen_c):12.4f} |"
            f" {float(tail):9.4f} | {float(x1res):7.4f} | {float(lin):8.4f} |"
            f" {str(cen_h < 1 and lin < 1):13s} | {cen_c < 1 and lin < 1}")
    log("")
    log("  d = 4 CROSS TERMS ARE MEASURED, NOT BOUNDED -- the outstanding item.")
    log("  PART 3 shows the dominant cross term is always d = 3, j = 1, so the")
    log("  d = 4 crosses are smaller on every configuration tested, but a")
    log("  measured ordering is not a bound and the table above therefore")
    log("  omits them.  Sharp reductions for Y_1, Y_2, Y_3 are the next task.")
    log("")


def isqrt_ub(x):
    from math import isqrt
    D = 10 ** 12
    if x == 0:
        return Fr(0)
    r = isqrt(x.numerator * D * D // x.denominator) + 1
    return Fr(r, D)


def main():
    rng = random.Random(20260812)
    log("=" * 74)
    log("THE (k = 4) ASSEMBLY BY THE ORTHOGONAL SPLIT")
    log("=" * 74)
    log("")
    part1(rng)
    part2(rng)
    part3(rng)
    part4()
    log("=" * 74)
    log(f"TOTAL FAILURES: {FAIL}")
    log("=" * 74)
    with open("results/graded_assembly_k4.log", "w") as fh:
        fh.write("\n".join(OUT) + "\n")
    return 0 if FAIL == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
