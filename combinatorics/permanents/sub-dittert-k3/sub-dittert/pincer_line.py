"""
THE LINE BLOCK — HARD CHECKPOINT.  The measured gap, per (k, n), before proving.

WHAT THE LINE BLOCK IS.  On the feasible hyperplane sum b = 0, split
b = b_line + z with b_line,ij = x_i + y_j (sum x = sum y = 0) and z doubly
centred.  Then R_i = n x_i, C_j = n y_j, ||b_line||_F^2 = n(p + q) with
p := ||x||^2, q := ||y||^2, and confinement bites HERE and only here:

    sum R^2 + sum C^2 = n^2 (p + q) <= rho_conf = (n-1) k!/n^(k-1),
    so   p + q  <=  u_max := (n-1) k! / n^(k+1).

FOUR STRUCTURAL FACTS, verified in PART 1:

 (S1) R(b_line + z) = R(b_line) exactly: z has zero line sums, so the whole
      -s_d(e_d R + e_d C) half of the deficit is a function of (x, y) ALONE.
 (S2) Hence every b_line-z coupling sits inside t_d sigma_d(b), carrying the
      factorially small t_d = s_d^2 (k-d)!/n^(k-d).  The blocks decouple at
      every order except through the small half.
 (S3) e_d(R) = n^d e_d(x), so only e_d(x) > 0 can hurt and the constant needed
      is M_d^+ = max e_d on the zero-sum unit sphere, NOT sup|e_d|.
 (S4) sigma_d ON THE LINE BLOCK HAS A CLOSED FORM.  b_line = x 1^T + 1 y^T has
      rank <= 2, and expanding the permanent of a d x d submatrix by the subset
      of rows taking the x part gives

        sigma_d(b_line) = sum_{m=0}^{d} m!(d-m)! C(n-m, d-m) C(n-d+m, m)
                                        e_m(x) e_{d-m}(y).

      Derivation: per((x_i + y_j)_{S,T}) = sum_m e_m(x_S) m!(d-m)! e_{d-m}(y_T),
      then sum over S of e_m(x_S) is C(n-m, d-m) e_m(x) and likewise for T.
      This turns every evaluation from C(n,d)^2 d! permanent terms into O(d),
      which is what makes PART 3 and PART 4 reach n = 12.

WHAT WAS CRUDE.  pincer_order2.py used |e_d(R)| <= n^(d/2)||R||^d/d!, i.e. the
constant n^(d/2)/d! on the unit sphere where the truth is M_d^+.  At
(d = 3, n = 10) that is 5.27 against 0.281 — loose by 19x, and the looseness
grows like n^(d/2).

Usage:  GUARD_MEM=8G GUARD_CPUS=250% GUARD_THREADS=2 ../guard.sh \
            python3 pincer_line.py
"""

import random
import sys
from fractions import Fraction as Fr
from itertools import combinations, permutations
from math import comb, factorial, sqrt

# ------------------------------------------------------------------ primitives


def per(M):
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


def sigma_d_exact(A, d):
    n = len(A)
    if d == 0:
        return Fr(1)
    if d > n:
        return Fr(0)
    tot = Fr(0)
    for R in combinations(range(n), d):
        for C in combinations(range(n), d):
            tot += per([[A[i][j] for j in C] for i in R])
    return tot


def sigma_d_float(A, d, n):
    if d == 0:
        return 1.0
    if d > n:
        return 0.0
    tot = 0.0
    for R in combinations(range(n), d):
        for C in combinations(range(n), d):
            s = 0.0
            for pi in permutations(range(d)):
                pr = 1.0
                for i in range(d):
                    pr *= A[R[i]][C[pi[i]]]
                s += pr
            tot += s
    return tot


def esym(v, d):
    e = [Fr(0)] * (d + 1)
    e[0] = Fr(1)
    for x in v:
        for j in range(min(d, len(v)), 0, -1):
            e[j] += e[j - 1] * x
    return e[d]


def esym_all_f(v, D):
    """[e_0, ..., e_D] of v, float."""
    e = [0.0] * (D + 1)
    e[0] = 1.0
    for x in v:
        for j in range(min(D, len(v)), 0, -1):
            e[j] += e[j - 1] * x
    return e


def falling(x, d):
    o = Fr(1)
    for i in range(d):
        o *= (x - i)
    return o


def s_coef(n, k, d):
    return falling(Fr(k), d) / falling(Fr(n), d)


def t_coef(n, k, d):
    if d > k:
        return Fr(0)
    return s_coef(n, k, d) ** 2 * Fr(factorial(k - d), n ** (k - d))


def kappa(n, k):
    return Fr(k * (k - 1), n * (n - 1))


def lam_line(n, k):
    return kappa(n, k) * (Fr(n) - Fr(factorial(k), n ** (k - 1)))


def rho_conf(n, k):
    return Fr((n - 1) * factorial(k), n ** (k - 1))


def u_max(n, k):
    return rho_conf(n, k) / Fr(n * n)


def lines(M):
    n = len(M)
    return ([sum(M[i][j] for j in range(n)) for i in range(n)],
            [sum(M[i][j] for i in range(n)) for j in range(n)])


# ------------------------------------------------- (S4) the line-block closed form


def sigma_line_closed(ex, ey, n, d):
    """sigma_d(b_line) from e_m(x), e_m(y) lists.  O(d) work."""
    tot = 0.0
    for m in range(d + 1):
        if m > n or d - m > n:
            continue
        c1 = comb(n - m, d - m) if n - m >= d - m >= 0 else 0
        c2 = comb(n - d + m, m) if n - d + m >= m >= 0 else 0
        if c1 == 0 or c2 == 0:
            continue
        tot += factorial(m) * factorial(d - m) * c1 * c2 * ex[m] * ey[d - m]
    return tot


def F_line(xv, yv, n, k):
    """Deficit on the line block, float, via the universal identity + (S4)."""
    ex = esym_all_f(xv, k)
    ey = esym_all_f(yv, k)
    eR = esym_all_f([n * t for t in xv], k)
    eC = esym_all_f([n * t for t in yv], k)
    tot = 0.0
    for d in range(1, k + 1):
        td = float(t_coef(n, k, d))
        if td != 0.0:
            tot += td * sigma_line_closed(ex, ey, n, d)
        tot -= float(s_coef(n, k, d)) * (eR[d] + eC[d])
    return tot


# =========================================== PART 1  the structural facts


def rand_zero_sum(n, rng, spread=4, den=3):
    v = [Fr(rng.randint(-spread, spread), rng.randint(1, den))
         for _ in range(n - 1)]
    return v + [-sum(v)]


def rand_dc(n, rng, spread=3):
    M = [[Fr(0)] * n for _ in range(n)]
    for _ in range(2 * n):
        i, i2 = rng.sample(range(n), 2)
        j, j2 = rng.sample(range(n), 2)
        v = Fr(rng.randint(-spread, spread))
        M[i][j] += v
        M[i2][j2] += v
        M[i][j2] -= v
        M[i2][j] -= v
    return M


def part1(rng):
    print("=" * 78)
    print("PART 1.  The structural facts.")
    print()
    print("  (S1) R(b_line + z) = R(b_line);  (S3) e_d(R) = n^d e_d(x). Exact:")
    ok13 = True
    for n in range(4, 8):
        good = True
        for _ in range(5):
            x, y = rand_zero_sum(n, rng), rand_zero_sum(n, rng)
            z = rand_dc(n, rng)
            bl = [[x[i] + y[j] for j in range(n)] for i in range(n)]
            b = [[bl[i][j] + z[i][j] for j in range(n)] for i in range(n)]
            R1, C1 = lines(bl)
            R2, C2 = lines(b)
            if R1 != R2 or C1 != C2:
                good = False
            if any(R1[i] != n * x[i] for i in range(n)):
                good = False
            for d in (3, 4):
                if esym(R2, d) != Fr(n) ** d * esym(x, d):
                    good = False
        ok13 = ok13 and good
        print(f"      n={n}: {good}")
    print()
    print("  (S4) the closed form for sigma_d(b_line), against direct")
    print("       subpermanent summation, EXACT:")
    ok4 = True
    for n in range(4, 8):
        good = True
        for _ in range(3):
            x, y = rand_zero_sum(n, rng), rand_zero_sum(n, rng)
            bl = [[x[i] + y[j] for j in range(n)] for i in range(n)]
            exf = esym_all_f([float(t) for t in x], n)
            eyf = esym_all_f([float(t) for t in y], n)
            for d in range(2, min(n, 5) + 1):
                direct = float(sigma_d_exact(bl, d))
                closed = sigma_line_closed(exf, eyf, n, d)
                if abs(direct - closed) > 1e-6 * max(1.0, abs(direct)):
                    good = False
        ok4 = ok4 and good
        print(f"      n={n}: d = 2..{min(n,5)}: {good}")
    print()
    print(f"  (S1)+(S3): {ok13}    (S4): {ok4}")
    print()
    print("  (S2) THE SIZE OF THE COUPLING.  F(b_line+z) - F(b_line) - F(z) can")
    print("  only enter through t_d sigma_d, so it should be far below the")
    print("  quadratic layer.  Float, both parts scaled to norm 1/20:")
    print()
    print(f"    {'n':>3} {'k':>3} {'|coupling|':>13} {'D_2':>13} {'ratio':>11}")
    for (n, k) in ((5, 3), (5, 4), (6, 3), (6, 4)):
        x = [float(t) for t in rand_zero_sum(n, rng)]
        y = [float(t) for t in rand_zero_sum(n, rng)]
        z = [[float(t) for t in row] for row in rand_dc(n, rng)]
        bl = [[x[i] + y[j] for j in range(n)] for i in range(n)]
        nb = sqrt(sum(v * v for r in bl for v in r))
        nz = sqrt(sum(v * v for r in z for v in r))
        if nb == 0 or nz == 0:
            continue
        sc = 0.05
        x = [t * sc / nb for t in x]
        y = [t * sc / nb for t in y]
        z = [[v * sc / nz for v in r] for r in z]
        bl = [[x[i] + y[j] for j in range(n)] for i in range(n)]
        b = [[bl[i][j] + z[i][j] for j in range(n)] for i in range(n)]

        def Ffull(M):
            R, C = lines([[Fr(v).limit_denominator(10 ** 9) for v in r]
                          for r in M])
            eR = esym_all_f([float(t) for t in R], k)
            eC = esym_all_f([float(t) for t in C], k)
            tot = 0.0
            for d in range(1, k + 1):
                td = float(t_coef(n, k, d))
                if td != 0.0:
                    tot += td * sigma_d_float(M, d, n)
                tot -= float(s_coef(n, k, d)) * (eR[d] + eC[d])
            return tot
        coup = Ffull(b) - Ffull(bl) - Ffull(z)
        d2 = (float(lam_line(n, k) / 2) * sum(v * v for r in bl for v in r)
              + float(t_coef(n, k, 2) / 2) * sum(v * v for r in z for v in r))
        print(f"    {n:3d} {k:3d} {abs(coup):13.4e} {d2:13.4e} "
              f"{abs(coup)/d2:11.3e}")
    print()
    return ok13 and ok4


# ================================== PART 2  the sharp one-sided constant


def Md_plus(n, d):
    best = -1e18
    for p in range(1, n):
        q = n - p
        a = sqrt(q / (n * p))
        b = -sqrt(p / (n * q))
        best = max(best, esym_all_f([a] * p + [b] * q, d)[d])
    return best


def crude_const(n, d):
    return n ** (d / 2) / factorial(d)


def part2():
    print("=" * 78)
    print("PART 2.  Old constant against the sharp one-sided constant.")
    print()
    print(f"    {'n':>3} {'d':>3} {'crude n^(d/2)/d!':>17} {'M_d^+':>12} "
          f"{'loose by':>10}")
    for n in (4, 6, 8, 10, 12):
        for d in (3, 4, 5):
            if d > n:
                continue
            c, m = crude_const(n, d), Md_plus(n, d)
            print(f"    {n:3d} {d:3d} {c:17.6f} {m:12.6f} {c/m:10.2f}x")
    print()
    print("  Looseness grows like n^(d/2) -- worse at larger k, which is")
    print("  exactly the pattern the crude margins showed.")
    print()


# ============================ PART 3  the measured gap, old and sharp


def line_margin(n, k, sharp):
    """(lambda_line/2) / (tail bound at u = u_max).  >= 1 means CLOSED."""
    u = float(u_max(n, k))
    tot = 0.0
    for d in range(3, k + 1):
        K = Md_plus(n, d) if sharp else crude_const(n, d)
        e_part = float(s_coef(n, k, d)) * n ** (d - 1) * K * u ** ((d - 2) / 2)
        s_part = (float(t_coef(n, k, d)) * comb(n, d) * n ** (d / 2 - 1)
                  * u ** (d / 2 - 1))
        tot += e_part + s_part
    return float(lam_line(n, k) / 2) / tot if tot > 0 else float("inf")


def part3():
    print("=" * 78)
    print("PART 3.  THE MEASURED GAP per (k, n).  Margin >= 1 means CLOSED;")
    print("         below 1, the reciprocal is the factor missed.")
    print()
    print(f"    {'n':>3} {'k':>3} {'margin CRUDE':>13} {'misses by':>11} "
          f"{'margin SHARP':>13} {'CLOSED now':>11}")
    cf, sf = [], []
    for n in range(4, 13):
        for k in range(3, n + 1):
            mc, ms = line_margin(n, k, False), line_margin(n, k, True)
            if mc < 1:
                cf.append((k, n))
            if ms < 1:
                sf.append((k, n))
            if k in (3, 4, n) or n in (4, 8, 12):
                print(f"    {n:3d} {k:3d} {mc:13.4f} {1/mc:11.2f}x "
                      f"{ms:13.4f} {str(ms >= 1):>11}")
    print()
    print(f"  CRUDE fails at {len(cf)} cells (k >= 3, 4 <= n <= 12).")
    print(f"  SHARP fails at {len(sf)} cells: {sf if sf else 'NONE'}")
    print()
    return cf, sf


# ==================== PART 4  the measured extremal configuration


def part4(rng):
    print("=" * 78)
    print("PART 4.  THE EXTREMAL CONFIGURATION, measured.  Minimise the exact")
    print("         line-block deficit subject to p + q <= u_max.")
    print()
    print(f"    {'n':>3} {'k':>3} {'min F':>13} {'D_2 there':>12} "
          f"{'p/(p+q)':>8} {'distinct x':>10} {'top-count':>9} {'F>=0':>6}")
    ok = True
    for (n, k) in ((4, 3), (5, 3), (5, 4), (6, 3), (6, 4), (7, 4), (7, 5),
                   (8, 4), (10, 4), (12, 4)):
        U = float(u_max(n, k))
        R = sqrt(U)
        best = None
        for _ in range(24):
            xv = [rng.gauss(0, 1) for _ in range(n)]
            yv = [rng.gauss(0, 1) for _ in range(n)]

            def proj(xv, yv, rad):
                mx, my = sum(xv) / n, sum(yv) / n
                xv = [v - mx for v in xv]
                yv = [v - my for v in yv]
                nr = sqrt(sum(v * v for v in xv) + sum(v * v for v in yv))
                if nr > rad and nr > 0:
                    s = rad / nr
                    xv = [v * s for v in xv]
                    yv = [v * s for v in yv]
                return xv, yv
            xv, yv = proj(xv, yv, R)
            step = 0.25 * R
            cur = F_line(xv, yv, n, k)
            for _ in range(400):
                h = R * 1e-5
                gx, gy = [0.0] * n, [0.0] * n
                for i in range(n):
                    xp = xv[:]
                    xp[i] += h
                    gx[i] = (F_line(xp, yv, n, k) - cur) / h
                    yp = yv[:]
                    yp[i] += h
                    gy[i] = (F_line(xv, yp, n, k) - cur) / h
                gn = sqrt(sum(v * v for v in gx) + sum(v * v for v in gy))
                if gn == 0:
                    break
                nx = [xv[i] - step * gx[i] / gn for i in range(n)]
                ny = [yv[i] - step * gy[i] / gn for i in range(n)]
                nx, ny = proj(nx, ny, R)
                nv = F_line(nx, ny, n, k)
                if nv < cur:
                    xv, yv, cur = nx, ny, nv
                else:
                    step *= 0.7
                    if step < R * 1e-9:
                        break
            if best is None or cur < best[0]:
                best = (cur, xv[:], yv[:])
        v, xv, yv = best
        p = sum(t * t for t in xv)
        q = sum(t * t for t in yv)
        d2 = float(lam_line(n, k) / 2) * n * (p + q)
        xs = sorted(xv, reverse=True)
        nd = len({round(t / max(abs(xs[0]), 1e-30), 5) for t in xs})
        top = sum(1 for t in xs if t > (xs[0] + xs[-1]) / 2)
        ok = ok and (v >= -1e-13 * max(1.0, abs(d2)))
        print(f"    {n:3d} {k:3d} {v:13.5e} {d2:12.5e} {p/(p+q):8.4f} "
              f"{nd:10d} {top:9d} {str(v >= -1e-13*max(1.0,abs(d2))):>6}")
    print()
    print(f"  the true deficit stays >= 0 on the confined line block: {ok}")
    print("  'distinct x' is against the at-most-(d-1)-values lemma;")
    print("  'top-count' is the analogue of the split p; 'p/(p+q)' says")
    print("  whether the extremal mass sits on rows, columns, or both.")
    print()
    return ok


# ============= PART 5  does the entry bound help on the line block?


def part5():
    print("=" * 78)
    print("PART 5.  Does graded's entry bound help HERE?  NO, and structurally.")
    print()
    print("  On K_n, r_i = 1 + n x_i >= 0 gives x_i >= -1/n, the same")
    print("  asymmetric range.  The right test is whether the EXTREMAL")
    print("  configuration violates it, not whether the norm exceeds 1/n:")
    print("  the e_3 extremal is x = ||x||(n-1,-1,..,-1)/sqrt(n(n-1)), whose")
    print("  most negative entry is -||x||/sqrt(n(n-1)), far above -||x||.")
    print()
    print(f"    {'n':>3} {'k':>3} {'||x||<=sqrt(u)':>15} {'min entry':>12} "
          f"{'-1/n':>10} {'active?':>9}")
    active = []
    for n in (4, 6, 8, 10, 12):
        for k in (3, 4, n):
            if k < 3 or k > n:
                continue
            nx = sqrt(float(u_max(n, k)))
            mn = -nx / sqrt(n * (n - 1))
            a = mn < -1.0 / n
            if a:
                active.append((k, n))
            print(f"    {n:3d} {k:3d} {nx:15.5e} {mn:12.5e} "
                  f"{-1/n:10.6f} {str(a):>9}")
    print()
    print(f"  cells where the entry bound is active: "
          f"{active if active else 'NONE'}")
    print()
    print("  So the entry mechanism that won on the centred slice does NOT")
    print("  transfer here: confinement puts us far inside the entry")
    print("  constraint.  On the line block the one-sided idea survives only")
    print("  as 'use max e_d, not sup|e_d|' -- the same word, a different use.")
    print()
    return active



# ============ PART 6  THE SHARPENED CHAIN: the cancellation the old one lost


def Md_signed(n, d):
    """(max e_d, -min e_d) over the two-value zero-sum unit sphere."""
    hi, lo = -1e18, 1e18
    for p in range(1, n):
        q = n - p
        a = sqrt(q / (n * p))
        b = -sqrt(p / (n * q))
        v = esym_all_f([a] * p + [b] * q, d)[d]
        hi = max(hi, v)
        lo = min(lo, v)
    return hi, -lo


def layer_cost(n, k, d, u):
    """Cost of layer d on the line block at p + q <= u, divided by n*u.

    From (S4), and using e_1 = 0 which KILLS the m = 1 and m = d-1 terms,

      D_d(b_line) = A_d (e_d(x) + e_d(y))
                    + sum_{m=2}^{d-2} c_{d,m} e_m(x) e_{d-m}(y),
      A_d   := d! C(n,d) t_d - s_d n^d,
      c_{d,m} := m!(d-m)! C(n-m,d-m) C(n-d+m,m) t_d  >  0.

    THE POINT: the sigma_d half and the e_d half are multiples of the SAME
    quantity with OPPOSITE signs, so they partially CANCEL.  The old chain
    bounded |t_d sigma_d| and |s_d e_d| separately and ADDED them, destroying
    the cancellation -- that is where most of the looseness was.
    """
    td = float(t_coef(n, k, d))
    sd = float(s_coef(n, k, d))
    A = factorial(d) * comb(n, d) * td - sd * n ** d
    hi, lo = Md_signed(n, d)
    # one-sided: if A < 0 the hurting side is e_d > 0, else e_d < 0
    cost = (-A) * hi if A < 0 else A * lo
    cost = max(cost, 0.0) * u ** (d / 2)
    for m in range(2, d - 1):
        if m == d - m == 1:
            continue
        c1 = comb(n - m, d - m) if n - m >= d - m >= 0 else 0
        c2 = comb(n - d + m, m) if n - d + m >= m >= 0 else 0
        if c1 == 0 or c2 == 0:
            continue
        c = factorial(m) * factorial(d - m) * c1 * c2 * td
        hm = max(Md_signed(n, m))
        hj = max(Md_signed(n, d - m))
        cost += c * hm * hj * u ** (d / 2)
    return cost / (n * u)


def sharp_margin(n, k):
    u = float(u_max(n, k))
    tot = sum(layer_cost(n, k, d, u) for d in range(3, k + 1))
    return float(lam_line(n, k) / 2) / tot if tot > 0 else float("inf")


def part6():
    print("=" * 78)
    print("PART 6.  THE SHARPENED CHAIN.  Same one-sided constants, but the")
    print("         sigma_d and e_d halves are COMBINED before bounding.")
    print()
    print("  On the line block, (S4) plus e_1 = 0 gives")
    print("      D_d = A_d (e_d(x)+e_d(y)) + sum_{m=2}^{d-2} c_{d,m} e_m(x)e_{d-m}(y)")
    print("  with A_d = d! C(n,d) t_d - s_d n^d and every c_{d,m} > 0.  The two")
    print("  halves are multiples of the SAME quantity with OPPOSITE signs.")
    print("  At d = 3 there are NO cross terms at all, so D_3 is exactly one")
    print("  multiple of e_3(x)+e_3(y).")
    print()
    print(f"    {'n':>3} {'k':>3} {'margin PART 3':>14} {'margin SHARPENED':>17} "
          f"{'gain':>7} {'CLOSED':>7}")
    fails = []
    for n in range(4, 13):
        for k in range(3, n + 1):
            m3 = line_margin(n, k, True)
            m6 = sharp_margin(n, k)
            if m6 < 1:
                fails.append((k, n))
            if k in (3, 4, n) or n in (4, 5, 12):
                print(f"    {n:3d} {k:3d} {m3:14.4f} {m6:17.4f} "
                      f"{m6/m3:7.2f}x {str(m6 >= 1):>7}")
    print()
    print(f"  SHARPENED chain fails at: {fails if fails else 'NO CELLS'}")
    print()
    print("  (k = 4, n = 4) was the single cell PART 3 left open, at margin")
    print("  0.9493.  The cancellation closes it.")
    print()
    return fails


def main():
    rng = random.Random(20260805)
    print()
    print("LINE BLOCK CHECKPOINT.  Measured first; nothing proved here.")
    print()
    sys.stdout.flush()
    r1 = part1(rng)
    sys.stdout.flush()
    part2()
    cf, sf = part3()
    sys.stdout.flush()
    r4 = part4(rng)
    act = part5()
    f6 = part6()
    print("=" * 78)
    print("CHECKPOINT SUMMARY")
    print(f"  (S1),(S3),(S4) verified                       : {r1}")
    print(f"  crude bound fails at                          : {len(cf)} cells")
    print(f"  sharp one-sided bound fails at                : {len(sf)} cells")
    print(f"  true deficit >= 0 on confined line block      : {r4}")
    print(f"  entry bound active on the line block          : "
          f"{'no' if not act else act}")
    print(f"  SHARPENED chain open cells                    : "
          f"{f6 if f6 else 'NONE'}")
    print()


if __name__ == "__main__":
    main()
