#!/usr/bin/env python3
"""Graded verifier for KSK.md -- the general-k Knopp-Sinkhorn boundary gap (KS_k).

Standard library only.  Exact `Fraction` arithmetic; no floating point enters
any decision.  Mutation controls at the end: each injected fault must be caught
at >= 2 positions, and with no fault injected nothing may fire.

    python3 graded_verify_ksk.py            # full run
    python3 graded_verify_ksk.py --quick    # smaller grids
"""
import sys, random, itertools
from fractions import Fraction as Fr
from math import comb, factorial, gcd

QUICK = '--quick' in sys.argv

# ----------------------------------------------------------------- bookkeeping
CHECKS = 0
FAILS = []
SECTION = ''

def check(cond, label, detail=''):
    global CHECKS
    CHECKS += 1
    if not cond:
        FAILS.append((SECTION, label, detail))

def section(name):
    global SECTION
    SECTION = name
    print(f'\n--- {name} ---')

# ----------------------------------------------------------------- primitives
def _derangements(N):
    d = [1, 0]
    for m in range(2, N + 1):
        d.append((m - 1) * (d[m - 1] + d[m - 2]))
    return d

DERANGE = _derangements(60)
assert DERANGE[:9] == [1, 0, 1, 2, 9, 44, 265, 1854, 14833]

def falling(a, m):
    r = 1
    for i in range(m):
        r *= (a - i)
    return r

def sigma_all(M, n):
    """sigma_0..sigma_n of the n x n matrix M, exact.  DP over rows, column-mask state."""
    size = 1 << n
    f = [0] * size
    f[0] = Fr(1)
    for i in range(n):
        g = f[:]
        row = M[i]
        for S in range(size):
            v = f[S]
            if v == 0:
                continue
            for j in range(n):
                b = 1 << j
                if S & b:
                    continue
                a = row[j]
                if a:
                    g[S | b] += v * a
        f = g
    out = [Fr(0)] * (n + 1)
    for S in range(size):
        out[bin(S).count('1')] += f[S]
    return out

def submatrix(M, n, i, j):
    return [[M[r][c] for c in range(n) if c != j] for r in range(n) if r != i]

def J(n):
    return [[Fr(1, n)] * n for _ in range(n)]

def T_matrix(n):
    """the Knopp-Sinkhorn matrix: 0 at (1,1), 1/(n-1) on the rest of row/col 1,
    (n-2)/(n-1)^2 elsewhere."""
    M = [[Fr(n - 2, (n - 1) ** 2)] * n for _ in range(n)]
    for j in range(1, n):
        M[0][j] = Fr(1, n - 1)
        M[j][0] = Fr(1, n - 1)
    M[0][0] = Fr(0)
    return M

def centred(M, n):
    return [[M[i][j] - Fr(1, n) for j in range(n)] for i in range(n)]

def frob2(X):
    return sum(x * x for r in X for x in r)

def t_m(n, k, m):
    return Fr(falling(k, m) ** 2, falling(n, m) ** 2) * Fr(factorial(k - m), n ** (k - m))

def u_coef(n, k, m):
    """t_m / gamma  with gamma = k!/n^k;  E_k/G_k - 1 = sum_m u_coef * sigma_m(X)."""
    return Fr(falling(k, m) * n ** m, falling(n, m) ** 2)

def W(n, k, m):
    """t_m/t_2 of UNIFORM-G section 2."""
    num = n ** (m - 2)
    for j in range(2, m):
        num *= (k - j)
    den = 1
    for j in range(2, m):
        den *= (n - j) ** 2
    return Fr(num, den)

# ------------------------------------------- closed forms for the T_n deviation
def e_m_u_closed(n, m):
    """e_m of u = e_1 - 1_n/n, in closed form."""
    if m == 0:
        return Fr(1)
    return Fr((-1) ** (m - 1) * comb(n - 1, m - 1) * (m - 1), n ** (m - 1) * m)

def e_m_u_direct(n, m):
    """e_m of u by the two-block split, independently of the closed form."""
    tot = Fr(0)
    for a in (0, 1):                                # a = 1 -> use the first entry
        if a > m:
            continue
        rest = m - a
        if rest > n - 1:
            continue
        head = Fr(n - 1, n) ** a
        tot += head * comb(n - 1, rest) * Fr(-1, n) ** rest
    return tot

def sigma_m_XT(n, m):
    """sigma_m(T_n - J_n/n) in closed form (rank one)."""
    lam = Fr(-n, (n - 1) ** 2)
    return lam ** m * factorial(m) * e_m_u_closed(n, m) ** 2

def F_Tn(n, k):
    """P_k(T_n) - k!/n^k, exact, from the layer identity plus the rank-one form."""
    return sum(t_m(n, k, m) * sigma_m_XT(n, m) for m in range(2, k + 1))

def relgap_Tn(n, k):
    """E_k/G_k - 1 at T_n."""
    return sum(u_coef(n, k, m) * sigma_m_XT(n, m) for m in range(2, k + 1))

def ks_claim(n, k):
    """the right-hand side of (KS_k)."""
    return Fr(k * (k - 1) * factorial(k), 4 * n ** k * (n - 1) ** 4)

def ks_claim_weak(n, k):
    """(KS_k) with the constant k(k-1)/4 replaced by 1."""
    return Fr(factorial(k), n ** k * (n - 1) ** 4)

# ------------------------------------------------------------- test matrices
def perm_matrix(p, n):
    M = [[Fr(0)] * n for _ in range(n)]
    for i, j in enumerate(p):
        M[i][j] = Fr(1)
    return M

def circulant(n, Tset):
    d = len(Tset)
    M = [[Fr(0)] * n for _ in range(n)]
    for i in range(n):
        for t in Tset:
            M[i][(i + t) % n] = Fr(1, d)
    return M

def direct_sum_J(parts):
    n = sum(parts)
    M = [[Fr(0)] * n for _ in range(n)]
    off = 0
    for p in parts:
        for i in range(p):
            for j in range(p):
                M[off + i][off + j] = Fr(1, p)
        off += p
    return M

def partitions(n, mx=None):
    if mx is None:
        mx = n
    if n == 0:
        yield []
        return
    for a in range(min(n, mx), 0, -1):
        for rest in partitions(n - a, a):
            yield [a] + rest

def rand_ds(n, rng, face=False):
    nterms = rng.randint(2, n + 3)
    ws = [rng.randint(1, 12) for _ in range(nterms)]
    tot = sum(ws)
    M = [[Fr(0)] * n for _ in range(n)]
    for w in ws:
        while True:
            p = list(range(n))
            rng.shuffle(p)
            if not face or p[0] != 0:
                break
        for i in range(n):
            M[i][p[i]] += Fr(w, tot)
    return M

def near_J(n, rng):
    M = J(n)
    for _t in range(rng.randint(1, 3)):
        i, ii = rng.sample(range(n), 2)
        j, jj = rng.sample(range(n), 2)
        e = Fr(rng.randint(1, 5), 100 * n)
        M[i][j] += e; M[ii][jj] += e; M[i][jj] -= e; M[ii][j] -= e
    return M if all(x >= 0 for r in M for x in r) else None

def build_pool(nmax, rng, nrand=30):
    """(name, n, M) for a wide family of exact doubly stochastic matrices."""
    pool = []
    for n in range(3, nmax + 1):
        pool.append(('J', n, J(n)))
        pool.append(('T_n', n, T_matrix(n)))
        pool.append(('I', n, perm_matrix(list(range(n)), n)))
        pool.append(('cyc', n, perm_matrix([(i + 1) % n for i in range(n)], n)))
        for parts in partitions(n):
            pool.append((f'dsumJ{parts}', n, direct_sum_J(parts)))
        for r in range(2, min(n, 4) + 1):
            for Tset in itertools.combinations(range(n), r):
                if 0 in Tset:
                    pool.append((f'circ{Tset}', n, circulant(n, Tset)))
        for _ in range(nrand):
            pool.append(('rand', n, rand_ds(n, rng)))
        for _ in range(nrand):
            pool.append(('face', n, rand_ds(n, rng, face=True)))
        for _ in range(nrand // 2):
            M = near_J(n, rng)
            if M is not None:
                pool.append(('nearJ', n, M))
    return pool

# =============================================================== A. exact fact
def part_A(FAULT):
    section('A. Theorem KSK-A: the minimum deviation on the zero face is 1/(n-1)^2')
    NMAX = 20 if QUICK else 40
    bad_target = Fr(1, 1)
    for n in range(2, NMAX + 1):
        Tn = T_matrix(n)
        target = Fr(1, (n - 1) ** 2)
        if FAULT == 'M1':
            target = Fr(1, (n - 1) ** 2) * (1 + Fr(1, n))
        check(all(x >= 0 for r in Tn for x in r), 'A1 T_n nonneg', f'n={n}')
        check(all(sum(r) == 1 for r in Tn) and
              all(sum(Tn[i][j] for i in range(n)) == 1 for j in range(n)),
              'A1 T_n doubly stochastic', f'n={n}')
        check(Tn[0][0] == 0, 'A1 T_n has a zero entry', f'n={n}')
        X = centred(Tn, n)
        check(frob2(X) == target, 'A2 ||T_n - J/n||^2 = 1/(n-1)^2', f'n={n}')
        # A3 rank-one closed form
        u = [Fr(n - 1, n)] + [Fr(-1, n)] * (n - 1)
        lam = Fr(-n, (n - 1) ** 2)
        check(all(X[i][j] == lam * u[i] * u[j] for i in range(n) for j in range(n)),
              'A3 T_n - J/n = -(n/(n-1)^2) u u^T', f'n={n}')
        check(sum(x * x for x in u) == Fr(n - 1, n), 'A6 ||u||^2 = (n-1)/n', f'n={n}')
        check(frob2([[u[i] * u[j] for j in range(n)] for i in range(n)]) ==
              Fr(n - 1, n) ** 2, 'A6 ||u u^T||_F^2 = ((n-1)/n)^2', f'n={n}')

    # A4: the identity u^T X u = X_11 on the doubly centred slice -- the whole proof
    rng = random.Random(11)
    for n in range(3, 10):
        u = [Fr(n - 1, n)] + [Fr(-1, n)] * (n - 1)
        for _ in range(12):
            M = rand_ds(n, rng)
            X = centred(M, n)
            val = sum(u[i] * X[i][j] * u[j] for i in range(n) for j in range(n))
            check(val == X[0][0], 'A4 u^T X u = X_11 on the centred slice', f'n={n}')

    # A5: Cauchy-Schwarz consequence, tested on the zero face
    pool = build_pool(8 if not QUICK else 6, random.Random(3), nrand=20)
    nface = 0
    for name, n, M in pool:
        if M[0][0] != 0:
            continue
        nface += 1
        Q = frob2(centred(M, n))
        floor = Fr(1, (n - 1) ** 2)
        if FAULT == 'M1':
            floor = floor * (1 + Fr(1, n))
        check(Q >= floor, 'A5 Q >= 1/(n-1)^2 on the zero face', f'{name} n={n} Q={Q}')
        if Q == Fr(1, (n - 1) ** 2):
            check(name == 'T_n', 'A5 equality only at T_n', f'{name} n={n}')
    print(f'    zero-face matrices tested: {nface}')

# ======================================================= B. the value at T_n
def part_B(FAULT):
    section('B. the rank-one closed form and (KS_k) at T_n')
    NMAX = 8 if QUICK else 9
    for n in range(3, 13):
        for m in range(0, n + 1):
            emc = e_m_u_closed(n, m)
            if FAULT == 'M5' and m >= 2:
                emc = Fr((-1) ** (m - 1) * comb(n - 1, m - 1), n ** (m - 1))
            check(emc == e_m_u_direct(n, m), 'B1 e_m(u) closed form', f'n={n} m={m}')

    for n in range(3, NMAX + 1):
        Tn = T_matrix(n)
        X = centred(Tn, n)
        s = sigma_all(X, n)
        sT = sigma_all(Tn, n)
        for m in range(1, n + 1):
            cf = sigma_m_XT(n, m)
            if FAULT == 'M5' and m >= 2:
                cf = Fr(-n, (n - 1) ** 2) ** m * factorial(m) * \
                     Fr((-1) ** (m - 1) * comb(n - 1, m - 1), n ** (m - 1)) ** 2
            check(s[m] == cf, 'B2 sigma_m(T_n - J/n) = lam^m m! e_m(u)^2', f'n={n} m={m}')
        for k in range(2, n + 1):
            gam = Fr(factorial(k), n ** k)
            direct = sT[k] / comb(n, k) ** 2 - gam
            check(direct == F_Tn(n, k), 'B3 F(T_n) layer sum = brute force', f'n={n} k={k}')
            check(direct == gam * relgap_Tn(n, k), 'B3 E_k/G_k form agrees', f'n={n} k={k}')

    # B4/B5: (KS_k) at T_n over the grid
    NG = 25 if QUICK else 60
    worst = None
    best = None
    for n in range(3, NG + 1):
        for k in range(3, n + 1):
            g = F_Tn(n, k)
            cl = ks_claim(n, k)
            if FAULT == 'M2':
                cl = cl * 2
            check(g >= cl, 'B4 (KS_k) holds at T_n', f'n={n} k={k}')
            r = g / cl
            if worst is None or r < worst[0]:
                worst = (r, n, k)
            if best is None or r > best[0]:
                best = (r, n, k)
    print(f'    grid 3<=k<=n<={NG}: ratio (true gap)/(claim) in '
          f'[{float(worst[0]):.5f} @ n={worst[1]},k={worst[2]}, '
          f'{float(best[0]):.5f} @ n={best[1]},k={best[2]}]')
    check(worst[0] >= Fr(4, 3), 'B5 ratio bounded below by 4/3', str(float(worst[0])))
    check(best[0] < 2, 'B5 ratio strictly below 2', str(float(best[0])))

    # the diagonal, further out
    ND = 40 if QUICK else 120
    for n in range(3, ND + 1):
        cl = ks_claim(n, n)
        if FAULT == 'M2':
            cl = cl * 2
        check(F_Tn(n, n) >= cl, 'B4 (KS_k) at T_n on the diagonal k=n', f'n={n}')

    # B6: how lossy Lemma U3 is at T_n
    for n in (7, 9, 11):
        Q = Fr(1, (n - 1) ** 2)
        m = n
        bound_sq = Fr(DERANGE[m] ** 2, factorial(m)) ** 2 * Q ** m
        true_sq = sigma_m_XT(n, m) ** 2
        check(true_sq <= bound_sq, 'B6 U3 bound holds at T_n', f'n={n}')
        print(f'    n={n}, m=k=n: (true/U3 bound)^2 = {float(true_sq / bound_sq):.3e}')

# ===================================================== C. the ratio inequality
def rat_slack(s, n, k):
    """n k sigma_k - (n-k+1)^2 sigma_{k-1}."""
    return n * k * s[k] - (n - k + 1) ** 2 * s[k - 1]

def part_C(FAULT):
    section('C. (RAT): n k sigma_k >= (n-k+1)^2 sigma_{k-1} on Omega_n')
    rng = random.Random(20260731)
    NMAX = 7 if QUICK else 8
    pool = build_pool(NMAX, rng, nrand=20 if QUICK else 30)

    # C1/C2: the two elementary cases, as identities
    for name, n, M in pool[:400]:
        s = sigma_all(M, n)
        check(rat_slack(s, n, 1) == 0, 'C1 (RAT) at k=1 is an identity', f'{name} n={n}')
        fro = frob2(M)
        check(2 * s[2] == n * n - 2 * n + fro, 'C2 2 sigma_2 = n^2-2n+||M||^2', f'{name} n={n}')
        check(rat_slack(s, n, 2) == n * (fro - 1), 'C2 (RAT) at k=2 is ||M||^2 >= 1',
              f'{name} n={n}')

    # C3: the centred-layer form of (RAT) at k
    for name, n, M in pool[:250]:
        X = centred(M, n)
        sX = sigma_all(X, n)
        s = sigma_all(M, n)
        Q = frob2(X)
        for k in range(2, n + 1):
            lhs = Q + sum(l * W(n, k, l) * sX[l] for l in range(3, k + 1))
            # (RAT) at k  <=>  lhs >= 0 ; check the exact proportionality
            sl = rat_slack(s, n, k)
            fac = Fr(comb(n, k - 1) ** 2 * (n - k + 1) ** 2 * factorial(k - 1),
                     n ** (k - 1)) * Fr(k - 1, (n - 1) ** 2)
            check(sl == fac * lhs, 'C3 centred-layer form of (RAT)', f'{name} n={n} k={k}')

    # C4: (RAT) at k=3 from p_3 >= -Q/n
    for name, n, M in pool[:250]:
        X = centred(M, n)
        sX = sigma_all(X, n)
        Q = frob2(X)
        p3 = sum(x ** 3 for r in X for x in r)
        check(p3 >= -Q / n, 'C4 p_3 >= -Q/n', f'{name} n={n}')
        check(sX[3] == Fr(2, 3) * p3, 'C4 sigma_3(X) = (2/3) p_3', f'{name} n={n}')
        if n >= 4:
            check(sX[3] >= -Q * Fr((n - 2) ** 2, 3 * n),
                  'C4 (RAT) at k=3 holds for n>=4', f'{name} n={n}')
    check(Fr(2, 3 * 4) <= Fr((4 - 2) ** 2, 3 * 4), 'C4 arithmetic: 2 <= (n-2)^2 at n=4')
    check(Fr(2, 3 * 3) > Fr((3 - 2) ** 2, 3 * 3), 'C4 arithmetic: fails at n=3')

    # C5: the exact census
    nfail = 0
    tight = {}
    for name, n, M in pool:
        s = sigma_all(M, n)
        for k in range(2, n + 1):
            sl = rat_slack(s, n, k)
            if FAULT == 'M3':
                sl = n * k * s[k] - (n - k + 1) ** 2 * s[k - 1] * (1 + Fr(1, n))
            ok = sl >= 0
            check(ok, 'C5 (RAT) census', f'{name} n={n} k={k}')
            if not ok:
                nfail += 1
            # dsumJ[n] and circ(0,1,..,n-1) ARE J_n/n; only genuine points are of interest
            if sl == 0 and M != J(n):
                tight.setdefault((n, k), []).append(name)
    print(f'    census: {len(pool)} matrices, n=3..{NMAX}, all k; failures {nfail}')
    eq_fams = sorted({(n, k, tuple(sorted(set(v)))) for (n, k), v in tight.items()})
    print(f'    non-trivial equality cells: {len(eq_fams)}')
    for e in eq_fams[:8]:
        print(f'      n={e[0]} k={e[1]}: {e[2]}')
    # C6: the predicted equality family -- 2-regular circulants at k = n
    for n in range(3, NMAX + 1):
        for t in range(1, n):
            M = circulant(n, (0, t))
            s = sigma_all(M, n)
            sl = rat_slack(s, n, n)
            if gcd(t, n) == 1:
                check(sl == 0, 'C6 equality at (I+C^t)/2, gcd(t,n)=1, k=n', f'n={n} t={t}')
            else:
                check(sl > 0, 'C6 strict when gcd(t,n)>1', f'n={n} t={t}')

    # C8: how far up the layers (RAT) is PROVABLE from one-sided layer bounds.
    # (RAT) at j holds as soon as  sum_(l=3)^j l W_l(n,j) C_l <= 1.
    def Rmaj(n):
        r = 1
        while (r + 1) ** 2 <= n - 1:
            r += 1
        return Fr(n - 1 + r * r, 2 * r)

    def C_U4(n, m):
        return Fr(DERANGE[m] ** 2, factorial(m)) * Fr(n - 1) ** ((m - 2) // 2) * \
            (Rmaj(n) if (m - 2) % 2 else 1)

    def C_U5(n, m):                       # conjectural, UNIFORM-G section 8.2
        return Fr(DERANGE[m] ** 2, factorial(m)) * Fr(n - 1) ** ((m - 1) // 2 - 1)

    def C_paper(n, m):
        b = Fr(n - 1, n)
        return {3: Fr(2, 3 * n), 4: Fr(3, 2) * b,
                5: Fr(24, 5 * n ** 3) + Fr(10, 3) * b + 8 * b * b}.get(m)

    def loss(n, j, mode):
        tot = Fr(0)
        for l in range(3, j + 1):
            c = C_paper(n, l) if mode.startswith('paper') else None
            if c is None:
                c = C_U5(n, l) if mode.endswith('U5') else C_U4(n, l)
            tot += l * W(n, j, l) * c
        return tot

    def n_rat(j, mode):
        for n in range(max(j, 3), 40000):
            if loss(n, j, mode) <= 1:
                return n
        return None

    print('    n_RAT(j) = least n at which (RAT) at layer j is PROVED from layer bounds')
    print(f"    {'mode':>10} " + " ".join(f'j={j:<5}' for j in range(3, 13)))
    for mode in ('paper', 'U4', 'U5', 'paper+U5'):
        vals = [n_rat(j, mode) for j in range(3, 13)]
        print(f'    {mode:>10} ' + " ".join(f'{v:<7}' for v in vals))
    # the paper column must reproduce the paper's own stability thresholds 4, 8, 14
    for j, want in ((3, 4), (4, 8), (5, 14)):
        check(n_rat(j, 'paper') == want,
              'C8 n_RAT matches the paper stability threshold at j<=5', f'j={j}')
        check(loss(want, j, 'paper') <= 1 < loss(want - 1, j, 'paper'),
              'C8 n_RAT is the exact boundary', f'j={j}')
    for j in range(6, 13):
        check(n_rat(j, 'U5') < n_rat(j, 'U4'), 'C8 (U5) would lower n_RAT', f'j={j}')
        check(n_rat(j, 'paper') < 8 * j * j * (j - 2) ** 2, 'C8 n_RAT below N(k)', f'j={j}')

    # C7: (MON) <=> (RAT) -- the derivative identity
    rng2 = random.Random(5)
    for n in range(3, 7):
        for _ in range(6):
            A = rand_ds(n, rng2)
            X = centred(A, n)
            for r in (Fr(1, 3), Fr(2, 3), Fr(1)):
                Mr = [[Fr(1, n) + r * X[i][j] for j in range(n)] for i in range(n)]
                sMr = sigma_all(Mr, n)
                for k in range(2, n + 1):
                    deriv = Fr(0)
                    for i in range(n):
                        for j in range(n):
                            if X[i][j] == 0:
                                continue
                            sub = sigma_all(submatrix(Mr, n, i, j), n - 1)
                            deriv += X[i][j] * (sub[k - 1] if k - 1 <= n - 1 else 0)
                    rhs = (k * sMr[k] - Fr((n - k + 1) ** 2, n) * sMr[k - 1]) / r
                    check(deriv == rhs, 'C7 d/dr sigma_k(J/n+rX) = (k sigma_k - '
                          '(n-k+1)^2 sigma_{k-1}/n)/r', f'n={n} k={k} r={r}')

# ================================================== D. the assembly of (KS_k)
def phi_q1(n, k, shift=0):
    """Phi(n,k,q_1) with q_1 = k(k-1)/(4(n-1)^2) and sqrt(q_1) <= (2k-1)/(4(n-1))."""
    q1 = Fr(k * (k - 1), 4 * (n - 1) ** 2)
    sq = Fr(2 * k - 1, 4 * (n - 1))
    tot = Fr(0)
    for m in range(3, k + 1):
        Cm = Fr(DERANGE[m] ** 2, factorial(m))
        pw = q1 ** ((m - 2) // 2) * (sq if (m - 2) % 2 else 1)
        tot += W(n, k, m) * Cm * pw
    return 4 * tot

def n_loc(k, shift=0):
    for n in range(k, 20000):
        if phi_q1(n, k) < 1:
            return n + shift
    return None

def part_D(FAULT):
    section('D. the assembly: (KS_k) from (RAT) + (LOC)')
    rng = random.Random(99)
    pool = [(nm, n, M) for nm, n, M in build_pool(7 if QUICK else 8, rng, nrand=25)
            if M[0][0] == 0]

    # D1: a_k = E_k/G_k is non-decreasing (= (RAT)) and a_2 = 1 + Q/(n-1)^2
    for name, n, M in pool:
        s = sigma_all(M, n)
        X = centred(M, n)
        Q = frob2(X)
        a = []
        for k in range(0, n + 1):
            G = Fr(comb(n, k) * factorial(k), n ** k)
            a.append(Fr(s[k], comb(n, k)) / G)
        check(a[2] == 1 + Q / (n - 1) ** 2, 'D1 a_2 = 1 + Q/(n-1)^2', f'{name} n={n}')
        bump = (1 + Fr(1, n)) if FAULT == 'M3' else 1
        check(all(a[k] >= a[k - 1] * bump for k in range(2, n + 1)),
              'D1 a_k non-decreasing', f'{name} n={n}')
        # D2/D3: the two strengths of (KS_k) on the zero face
        for k in range(3, n + 1):
            gam = Fr(factorial(k), n ** k)
            gap = Fr(s[k], comb(n, k) ** 2) - gam
            check(gap >= ks_claim_weak(n, k), 'D2 (KS_k) weak on the zero face',
                  f'{name} n={n} k={k}')
            cl = ks_claim(n, k)
            if FAULT == 'M2':
                cl = cl * 2
            check(gap >= cl, 'D3 (KS_k) full on the zero face', f'{name} n={n} k={k}')
    print(f'    zero-face matrices: {len(pool)}')

    # D4: the (LOC) threshold table, exact, and sharp
    KM = 12 if QUICK else 25
    rows = []
    for k in range(3, KM + 1):
        nl = n_loc(k)
        if FAULT == 'M4':
            nl = nl - 1
        rows.append((k, nl))
        check(phi_q1(nl, k) < 1, 'D4 Phi(n_LOC,k,q1) < 1', f'k={k} n={nl}')
        if nl - 1 >= k:
            check(phi_q1(nl - 1, k) >= 1, 'D4 Phi(n_LOC-1,k,q1) >= 1 (threshold exact)',
                  f'k={k} n={nl}')
        check(nl <= 3 * k, 'D4 n_LOC(k) <= 3k', f'k={k} n_LOC={nl}')
        check(nl < 8 * k * k * (k - 2) ** 2, 'D4 n_LOC(k) << N(k)', f'k={k}')
    print('    k     n_LOC   N(k)=8k^2(k-2)^2   ratio')
    for k, nl in rows[:10] + rows[-3:]:
        Nk = 8 * k * k * (k - 2) ** 2
        print(f'    {k:<5} {nl:<7} {Nk:<18} {Nk / nl:.0f}x')

    # D5: boundary witnesses far below the old N(k)
    for k in (6, 8, 12):
        Nk = 8 * k * k * (k - 2) ** 2
        for n in (k, k + 2, 2 * k, 3 * k, 10 * k):
            if n < k:
                continue
            check(F_Tn(n, k) >= ks_claim(n, k),
                  'D5 (KS_k) at T_n far below N(k)', f'k={k} n={n} N(k)={Nk}')
            check(n < Nk, 'D5 witness is below N(k)', f'k={k} n={n}')

# ================================================================= E. payoff
def works(n, k, g_low, gT):
    gam = Fr(factorial(k), n ** k)
    return gam * g_low > Fr(3, 4) * n ** 2 * (n - 1) * Fr(k, k - 1) * (gam * (1 + gT)) ** 2

def _ok(n, k, mode):
    g_low = Fr(k * (k - 1), 4 * (n - 1) ** 4) if mode == 'full' else Fr(1, (n - 1) ** 4)
    return works(n, k, g_low, relgap_Tn(n, k))

def nmin(k, mode, cap=1 << 22):
    """least n >= max(k,3) with the Pang comparison (*) satisfied; None if never.
    (*) is eventually monotone in n, so: exponential search then bisection, then a
    downward linear sweep to make the threshold exact."""
    lo = max(k, 3)
    hi = lo
    while hi < cap and not _ok(hi, k, mode):
        hi *= 2
    if hi >= cap:
        return None
    a, b = lo, hi
    while a < b:
        mid = (a + b) // 2
        if _ok(mid, k, mode):
            b = mid
        else:
            a = mid + 1
    while a > lo and _ok(a - 1, k, mode):
        a -= 1
    return a

def part_E(FAULT):
    section('E. payoff: which (k,n) the transferred Pang route reaches')
    known = {8: 2464, 9: 128, 10: 50, 11: 32, 12: 25, 13: 22, 14: 20, 17: 18, 18: 18}
    # composed collar thresholds, UNIVERSAL.md section 3 (branch L0), exact
    NTILDE = {3: 19, 4: 43, 5: 110, 6: 244, 7: 449, 8: 736, 9: 1111, 10: 1583,
              11: 2160, 12: 2850, 20: 13552, 30: 47707, 40: 124373}
    print(f"    {'k':>4} {'full':>8} {'weak':>8} {'n_LOC':>7} {'collar Ntilde':>14} "
          f"{'MAXIMISER':>10}")
    for k in list(range(8, 15)) + [17, 18, 20, 25, 30]:
        nf = nmin(k, 'full')
        nw = nmin(k, 'weak')
        nl = n_loc(k) - (1 if FAULT == 'M4' else 0)
        check(phi_q1(nl, k) < 1, 'E1 n_LOC really certifies the near branch',
              f'k={k} n_LOC={nl}')
        col = NTILDE.get(k)
        print(f'    {k:>4} {str(nf):>8} {str(nw):>8} {str(nl):>7} '
              f'{str(col) if col else "-":>14} {str(known.get(k, "-")):>10}')
        if k in known:
            check(nf == known[k], 'E1 reproduces MAXIMISER section 8.1 n_min',
                  f'k={k} got {nf} want {known[k]}')
        check(nw is not None and nf is not None and nw >= nf,
              'E1 weak constant costs nothing but n', f'k={k}')
        if col is not None and k >= 9:
            check(nw < col, 'E1 weak (KS_k) still beats the collar for k>=9',
                  f'k={k} nw={nw} collar={col}')
            check(nf < col, 'E1 full (KS_k) beats the collar for k>=9',
                  f'k={k} nf={nf} collar={col}')
        if col is not None and k == 8:
            check(nw > col, 'E1 at k=8 the weak constant hands the cell back',
                  f'k=8 nw={nw} collar={col}')
    # the diagonal: the collar can never reach k = n, the Pang route does
    for k in (20, 25, 30):
        check(nmin(k, 'weak') <= k + 6, 'E1 the weak route stays near the diagonal',
              f'k={k}')
    # the route is dead for k <= 7 STRUCTURALLY: with the (KS_k) gap put in, (*) is
    # n^(k-2)(k-1)^2 > 3(n-1)^5 k!, and k-2 <= 5 makes the left side lose at every n.
    for k in (3, 4, 5, 6, 7):
        check(nmin(k, 'full', cap=1 << 24) is None, 'E1 route stays dead for k<=7',
              f'k={k}')
        for n in (k + 1, 100, 10 ** 4, 10 ** 8, 10 ** 12):
            if n <= k:
                continue
            check(n ** (k - 2) * (k - 1) ** 2 <= 3 * (n - 1) ** 5 * factorial(k),
                  'E1 the exponent count kills k<=7 at every n', f'k={k} n={n}')
    for k in (8, 9, 12):
        n = nmin(k, 'full')
        check(n ** (k - 2) * (k - 1) ** 2 > 3 * (n - 1) ** 5 * factorial(k),
              'E1 the exponent count agrees with (*) at k>=8', f'k={k} n={n}')

# =================================================================== driver
def run(FAULT=None):
    global CHECKS, FAILS
    CHECKS = 0
    FAILS = []
    part_A(FAULT)
    part_B(FAULT)
    part_C(FAULT)
    part_D(FAULT)
    part_E(FAULT)
    return CHECKS, list(FAILS)

def main():
    print('graded_verify_ksk.py -- exact rational verification of KSK.md')
    print(f'mode: {"quick" if QUICK else "full"}')
    n_checks, fails = run(None)
    print('\n' + '=' * 68)
    print(f'CLEAN RUN: {n_checks} checks, {len(fails)} failures')
    for f in fails[:30]:
        print('   FAIL', f)

    print('\n' + '=' * 68)
    print('MUTATION CONTROLS (each fault must be caught at >= 2 positions)')
    muts = {
        'M1': 'inflate the zero-face deviation floor 1/(n-1)^2 by (1+1/n)',
        'M2': 'double the claimed (KS_k) constant k(k-1)/4 -> k(k-1)/2',
        'M3': 'strengthen (RAT) by the factor (1+1/n)',
        'M4': 'lower n_LOC(k) by one',
        'M5': 'drop the (m-1)/m factor from the closed form of e_m(u)',
    }
    allgood = True
    for tag, desc in muts.items():
        _, f = run(tag)
        pos = len({(a, b) for a, b, _ in f})
        print(f'  {tag}: {len(f):>5} checks catch it at {pos} distinct positions  -- {desc}')
        if len(f) < 2:
            allgood = False
    print('\n' + '=' * 68)
    ok = (len(fails) == 0) and allgood
    print('RESULT:', 'ALL CHECKS PASS' if ok else 'FAILURES PRESENT')
    return 0 if ok else 1

if __name__ == '__main__':
    sys.exit(main())
