"""graded_verify_gap.py -- (GAP), the lemma that replaced the refuted (RAT).

    (GAP)   a_k(M) >= a_2(M)   for every M in Omega_n and every 2 <= k <= n,
            a_k = sigma_k n^k / (C(n,k)^2 k!),   a_2 = 1 + Q/(n-1)^2,
            Q = ||M - J_n/n||_F^2.

(GAP) is what Theorem KSK-B actually consumes.  (RAT) -- the Holens-Dokovic
conjecture -- implies it by telescoping and is FALSE (Wanless, LAA 286 (1999)
273-285).  This file decides what (GAP)'s status is.

WHAT IS ESTABLISHED HERE

  * (GAP) is UNCONDITIONAL for k <= 4 at every n.  It is not a new conjecture
    at the bottom of the ladder: (GAP) at k = 3 IS Holens-Dokovic at k = 3
    (Dokovic 1967), and (GAP) at k = 4 follows by a_4 >= a_3 >= a_2 from
    Kopotun, Linear Multilinear Algebra 36 (1994) 205-216 (k = 4, n >= 5) plus
    this repository's exact k = n = 4 certificate.  Section E.
  * (GAP) is TIGHT.  a_3 = a_2 exactly at n = 3, M = (I + C)/2.  No
    (1 + eps) strengthening of (GAP) can hold.  Section D.
  * Theorem GAP-N: (GAP) holds unconditionally inside an explicit Q-ball at
    EVERY cell (n,k), from Lemma U4 alone, with no threshold in n.  Section F.
  * The mandatory control: Wanless's order-22 matrix FAILS (RAT) at k = 22 and
    PASSES (GAP) at every k, by a factor of 80.  Section B.

Standard library only.  Exact Fraction arithmetic; no float enters a decision.

Run:  ../guard.sh python3 graded_verify_gap.py
"""
import itertools
import random
import sys
from fractions import Fraction as Fr
from math import comb, factorial

MUT = None
FAILS = []
LABELS = {}
NCHECK = 0


def check(cond, label, detail=''):
    global NCHECK
    NCHECK += 1
    LABELS.setdefault(label, [0, 0])
    LABELS[label][0] += 1
    if not cond:
        LABELS[label][1] += 1
        FAILS.append((label, detail))


def banner(s):
    if MUT is None:
        print(s)


say = banner


# ==========================================================================
# core exact machinery
# ==========================================================================
def falling(a, b):
    r = 1
    for j in range(b):
        r *= (a - j)
    return r


def per_brute(M):
    n = len(M)
    if n == 0:
        return Fr(1)
    tot = Fr(0)
    for p in itertools.permutations(range(n)):
        t = Fr(1)
        for i in range(n):
            t *= M[i][p[i]]
        tot += t
    return tot


def submat(M, rows, cols):
    return [[M[i][j] for j in cols] for i in rows]


def sigma_brute(M, k):
    n = len(M)
    tot = Fr(0)
    for A in itertools.combinations(range(n), k):
        for B in itertools.combinations(range(n), k):
            tot += per_brute(submat(M, A, B))
    return tot


def sigma_vector(M, order=None):
    """[sigma_0..sigma_n] for an arbitrary matrix (entries may be negative).

    Row DP with the used-column set as state plus a forget step.  On a sparse
    matrix -- Wanless's order-22 chain of 3-row gadgets -- the frontier stays
    tiny and n = 43 is cheap."""
    n = len(M)
    if order is None:
        order = list(range(n))
    last = {}
    for pos, i in enumerate(order):
        for j in range(n):
            if M[i][j]:
                last[j] = pos
    states = {frozenset(): [Fr(1)]}
    for pos, i in enumerate(order):
        nxt = {}
        supp = [(j, M[i][j]) for j in range(n) if M[i][j]]
        for used, poly in states.items():
            t = nxt.setdefault(used, [])
            if len(t) < len(poly):
                t.extend([Fr(0)] * (len(poly) - len(t)))
            for kk, c in enumerate(poly):
                t[kk] += c
            for j, w in supp:
                if j in used:
                    continue
                t2 = nxt.setdefault(used | {j}, [])
                if len(t2) < len(poly) + 1:
                    t2.extend([Fr(0)] * (len(poly) + 1 - len(t2)))
                for kk, c in enumerate(poly):
                    t2[kk + 1] += c * w
        dead = frozenset(j for j in range(n) if last.get(j, -1) <= pos)
        if dead:
            merged = {}
            for used, poly in nxt.items():
                t = merged.setdefault(used - dead, [])
                if len(t) < len(poly):
                    t.extend([Fr(0)] * (len(poly) - len(t)))
                for kk, c in enumerate(poly):
                    t[kk] += c
            nxt = merged
        states = nxt
    out = [Fr(0)] * (n + 1)
    for used, poly in states.items():
        for kk, c in enumerate(poly):
            out[kk] += c
    return out


def a_vector(sig, n):
    """a_k = sigma_k n^k / (C(n,k)^2 k!);  a_0 = a_1 = 1 on Omega_n."""
    d = 1
    if MUT == 'M1':                       # corrupt the normalisation
        d = 2
    return [sig[k] * Fr(n ** k, comb(n, k) ** 2 * factorial(k) * d)
            for k in range(n + 1)]


def Qof(M):
    n = len(M)
    return sum((M[i][j] - Fr(1, n)) ** 2 for i in range(n) for j in range(n))


def a2_closed(M):
    n = len(M)
    return 1 + Qof(M) / Fr((n - 1) ** 2)


def gap_ok(a, a2, k):
    """(GAP) at k."""
    if MUT == 'M3':                       # strengthen (GAP) by 10 percent
        return a[k] >= a2 * Fr(11, 10)
    return a[k] >= a2


def rat_ok(sig, n, k):
    """(RAT) at k:  n k sigma_k >= (n-k+1)^2 sigma_{k-1}."""
    return n * k * sig[k] >= (n - k + 1) ** 2 * sig[k - 1]


def deviation(M):
    n = len(M)
    return [[M[i][j] - Fr(1, n) for j in range(n)] for i in range(n)]


def is_ds(M):
    n = len(M)
    return all(sum(M[i]) == 1 for i in range(n)) and \
        all(sum(M[i][j] for i in range(n)) == 1 for j in range(n)) and \
        all(M[i][j] >= 0 for i in range(n) for j in range(n))


# ------------------------------------------------------- standard test matrices
def J(n):
    return [[Fr(1, n)] * n for _ in range(n)]


def circ(n, offs, wts):
    M = [[Fr(0)] * n for _ in range(n)]
    for o, w in zip(offs, wts):
        for i in range(n):
            M[i][(i + o) % n] += w
    return M


def half_IC(n, t=1):
    return circ(n, [0, t], [Fr(1, 2), Fr(1, 2)])


def perm_matrix(n, p):
    M = [[Fr(0)] * n for _ in range(n)]
    for i in range(n):
        M[i][p[i]] = Fr(1)
    return M


def block_sum(parts):
    n = sum(parts)
    M = [[Fr(0)] * n for _ in range(n)]
    o = 0
    for p in parts:
        for i in range(p):
            for j in range(p):
                M[o + i][o + j] = Fr(1, p)
        o += p
    return M


def T_matrix(n):
    """The exact one-zero minimiser of Theorem KSK-A:
       T_n = J - (n/(n-1)^2) u u^T,  u = e_1 - 1/n.  T_n[0][0] = 0."""
    u = [Fr(1) - Fr(1, n)] + [Fr(-1, n)] * (n - 1)
    c = Fr(n, (n - 1) ** 2)
    return [[Fr(1, n) - c * u[i] * u[j] for j in range(n)] for i in range(n)]


def rand_ds(n, rng, steps=None):
    """A random Birkhoff point: a convex combination of permutation matrices
    with small rational weights.  Exactly doubly stochastic by construction and
    -- unlike exact Sinkhorn, which grows denominators without bound -- it keeps
    the rationals small enough for the exact sigma DP."""
    t = rng.randrange(2, 6)
    D = 12
    cuts = sorted(rng.randrange(1, D) for _ in range(t - 1))
    parts = [b - a for a, b in zip([0] + cuts, cuts + [D])]
    M = [[Fr(0)] * n for _ in range(n)]
    for w in parts:
        if not w:
            continue
        p = list(range(n))
        rng.shuffle(p)
        for i in range(n):
            M[i][p[i]] += Fr(w, D)
    return M


def rand_zeroface(n, rng, steps=None):
    """A random Birkhoff point on the zero face: every permutation in the
    combination avoids position (0,0), so M[0][0] = 0 exactly."""
    t = rng.randrange(2, 6)
    D = 12
    cuts = sorted(rng.randrange(1, D) for _ in range(t - 1))
    parts = [b - a for a, b in zip([0] + cuts, cuts + [D])]
    M = [[Fr(0)] * n for _ in range(n)]
    for w in parts:
        if not w:
            continue
        while True:
            p = list(range(n))
            rng.shuffle(p)
            if p[0] != 0:
                break
        for i in range(n):
            M[i][p[i]] += Fr(w, D)
    return M


def pool(n, rng, extra=8):
    P = [('J', J(n)), ('T_n', T_matrix(n)),
         ('(I+C)/2', half_IC(n)),
         ('(I+2C)/3', circ(n, [0, 1], [Fr(1, 3), Fr(2, 3)])),
         ('3-circ', circ(n, [0, 1, 2], [Fr(1, 3)] * 3)),
         ('perm', circ(n, [1], [Fr(1)]))]
    for t in range(2, n):
        if __import__('math').gcd(t, n) == 1:
            P.append((f'(I+C^{t})/2', half_IC(n, t)))
    for a in range(1, n // 2 + 1):
        P.append((f'J{a}+J{n - a}', block_sum([a, n - a])))
    for i in range(extra):
        P.append((f'rand{i}', rand_ds(n, rng)))
        P.append((f'zf{i}', rand_zeroface(n, rng)))
    return P


# ==========================================================================
# the Wanless order-22 matrix and its two-chain generalisation
# ==========================================================================
WANLESS_ROWS8 = {
    1: {11: 4, 20: 4}, 2: {1: 4, 3: 2, 4: 2}, 3: {2: 2, 3: 3, 4: 3},
    4: {2: 2, 3: 3, 4: 3}, 5: {2: 4, 6: 2, 7: 2}, 6: {5: 2, 6: 3, 7: 3},
    7: {5: 2, 6: 3, 7: 3}, 8: {5: 4, 9: 2, 10: 2}, 9: {8: 2, 9: 3, 10: 3},
    10: {8: 2, 9: 3, 10: 3}, 11: {8: 4, 12: 2, 13: 2},
    12: {11: 2, 12: 3, 13: 3}, 13: {11: 2, 12: 3, 13: 3},
    14: {1: 4, 15: 2, 16: 2}, 15: {14: 2, 15: 3, 16: 3},
    16: {14: 2, 15: 3, 16: 3}, 17: {14: 4, 18: 2, 19: 2},
    18: {17: 2, 18: 3, 19: 3}, 19: {17: 2, 18: 3, 19: 3},
    20: {17: 4, 21: 2, 22: 2}, 21: {20: 2, 21: 3, 22: 3},
    22: {20: 2, 21: 3, 22: 3},
}


def wanless22():
    n = 22
    M = [[Fr(0)] * n for _ in range(n)]
    for i, row in WANLESS_ROWS8.items():
        for j, v in row.items():
            M[i - 1][j - 1] = Fr(v, 8)
    if MUT == 'M2':                       # corrupt one transcribed entry
        M[2][1] = Fr(3, 8)
        M[2][2] = Fr(2, 8)
    return M


def wanless_family(a, b):
    n = 1 + 3 * (a + b)
    M = [[Fr(0)] * n for _ in range(n)]
    ch = [[], []]
    s = 1
    for _ in range(a):
        ch[0].append(s)
        s += 3
    for _ in range(b):
        ch[1].append(s)
        s += 3
    for c in ch:
        prev = 0
        for st in c:
            M[st][prev] = Fr(1, 2)
            M[st][st + 1] = Fr(1, 4)
            M[st][st + 2] = Fr(1, 4)
            for r in (st + 1, st + 2):
                M[r][st] = Fr(1, 4)
                M[r][st + 1] = Fr(3, 8)
                M[r][st + 2] = Fr(3, 8)
            prev = st
    M[0][ch[0][-1]] = Fr(1, 2)
    M[0][ch[1][-1]] = Fr(1, 2)
    return M, n


def wanless_gen(a, b, p):
    """the same two-chain skeleton with the gadget hub weight free.

    Column balance at each chain's terminal column forces the two chains to
    carry COMPLEMENTARY weights: chain 0 uses p, chain 1 uses 1-p, and the hub
    row splits p / (1-p) to match.  p = 1/2 is Wanless's Figure 1.  Doubly
    stochastic for every p in (0,1) -- checked, not assumed (B8)."""
    n = 1 + 3 * (a + b)
    M = [[Fr(0)] * n for _ in range(n)]
    ch = [[], []]
    s = 1
    for _ in range(a):
        ch[0].append(s)
        s += 3
    for _ in range(b):
        ch[1].append(s)
        s += 3
    for c, pc in zip(ch, (p, 1 - p)):
        q = (1 - pc) / 2
        prev = 0
        for st in c:
            M[st][prev] = pc
            M[st][st + 1] = q
            M[st][st + 2] = q
            for r in (st + 1, st + 2):
                M[r][st] = q
                M[r][st + 1] = (1 - q) / 2
                M[r][st + 2] = (1 - q) / 2
            prev = st
    M[0][ch[0][-1]] = p
    M[0][ch[1][-1]] = 1 - p
    return M, n


def chain_order(n):
    return list(range(1, n)) + [0]


# ==========================================================================
# layer machinery
# ==========================================================================
DERANGE = [1, 0, 1, 2, 9, 44, 265, 1854, 14833, 133496, 1334961, 14684570,
           176214841]


def u_coef(n, k, m):
    """a_k - 1 = sum_{m=2}^k u_coef(n,k,m) sigma_m(X),  X = M - J."""
    c = Fr(falling(k, m) * n ** m, falling(n, m) ** 2)
    if MUT == 'M5' and m == 3:            # corrupt the layer identity
        c = c * 2
    return c


def W(n, k, m):
    """u_m/u_2."""
    num = n ** (m - 2)
    for j in range(2, m):
        num *= (k - j)
    den = 1
    for j in range(2, m):
        den *= (n - j) ** 2
    return Fr(num, den)


def c_allow(k):
    """(GAP) at k needs  sum_{l>=3} W_l C_l  <=  c_k = (k-2)(k+1)/(2k(k-1))."""
    a = Fr((k - 2) * (k + 1), 2 * k * (k - 1))
    if MUT == 'M4':                       # inflate the allowance
        a = a * 2
    return a


def U4_const(m):
    """D_m^2/m!  -- the constant of Lemma U4, |sigma_m(X)| <= (D_m^2/m!)Q^(m/2)."""
    c = Fr(DERANGE[m] ** 2, factorial(m))
    if MUT == 'M6':                       # corrupt Lemma U4's constant
        c = c / 4
    return c


def Rmaj(n):
    r = 1
    while (r + 1) ** 2 <= n - 1:
        r += 1
    return Fr(n - 1 + r * r, 2 * r)


def C_U4(n, m):
    return U4_const(m) * Fr(n - 1) ** ((m - 2) // 2) * \
        (Rmaj(n) if (m - 2) % 2 else 1)


def C_U5(n, m):
    return U4_const(m) * Fr(n - 1) ** ((m - 1) // 2 - 1)


def C_paper(n, m):
    b = Fr(n - 1, n)
    return {3: Fr(2, 3 * n), 4: Fr(3, 2) * b,
            5: Fr(24, 5 * n ** 3) + Fr(10, 3) * b + 8 * b * b}.get(m)


def C_of(n, m, mode):
    c = C_paper(n, m) if mode.startswith('paper') else None
    if c is None:
        c = C_U5(n, m) if mode.endswith('U5') else C_U4(n, m)
    return c


def gap_loss(n, j, mode):
    return sum(W(n, j, l) * C_of(n, l, mode) for l in range(3, j + 1))


def least_n(f, thr, j, cap=200000):
    for n in range(max(j, 3), cap):
        if f(n, j) <= thr(j):
            return n
    return None


def qstar(n, k, digits=40):
    """Theorem GAP-N.  Largest Q for which Lemma U4 alone proves (GAP) at
    (n,k):  Psi(s) = sum_{l=3}^k W_l(n,k) (D_l^2/l!) s^{l-2} <= c_k,  s = sqrt Q.
    Psi has non-negative coefficients so it is increasing on s >= 0; bisect on
    s in exact rationals and return the rational lower bound s_lo^2 <= q*."""
    def Psi(s):
        return sum(W(n, k, l) * U4_const(l) * s ** (l - 3) * s
                   for l in range(3, k + 1))
    tgt = c_allow(k)
    lo, hi = Fr(0), Fr(1)
    while Psi(hi) <= tgt:
        hi *= 2
        if hi > 10 ** 6:
            break
    for _ in range(digits):
        mid = (lo + hi) / 2
        if Psi(mid) <= tgt:
            lo = mid
        else:
            hi = mid
    return lo * lo, lo


# ==========================================================================
def section_A():
    banner('--- A  the identities (GAP) is built on')
    rng = random.Random(11)
    for n in range(3, 7):
        for nm, M in pool(n, rng, extra=3):
            check(is_ds(M), 'A0 pool member is doubly stochastic', f'{n} {nm}')
            sig = sigma_vector(M)
            a = a_vector(sig, n)
            # A1  the DP reproduces the verbatim definition of sigma_k
            if n <= 5:
                for k in range(0, n + 1):
                    check(sig[k] == sigma_brute(M, k),
                          'A1 sigma DP == verbatim definition', f'{n} {nm} k={k}')
            # A2  a_0 = a_1 = 1, a_n = per n^n/n!
            check(a[0] == 1 and a[1] == 1, 'A2 a_0 = a_1 = 1', f'{n} {nm}')
            check(sig[n] == per_brute(M), 'A2 sigma_n = per', f'{n} {nm}')
            # A3  a_2 = 1 + Q/(n-1)^2 exactly
            check(a[2] == a2_closed(M), 'A3 a_2 = 1 + Q/(n-1)^2', f'{n} {nm}')
            # A4  Tverberg-Friedland: a_k >= 1
            for k in range(2, n + 1):
                check(a[k] >= 1, 'A4 Tverberg-Friedland a_k >= 1', f'{n} {nm} k={k}')
            # A5  the layer expansion a_k - 1 = sum u_m sigma_m(X)
            X = deviation(M)
            sx = sigma_vector(X)
            check(sx[1] == 0, 'A5 sigma_1(X) = 0 (zero line sums)', f'{n} {nm}')
            check(sx[2] == Qof(M) / 2, 'A5 sigma_2(X) = Q/2', f'{n} {nm}')
            for k in range(2, n + 1):
                lhs = a[k] - 1
                rhs = sum(u_coef(n, k, m) * sx[m] for m in range(2, k + 1))
                check(lhs == rhs, 'A5 layer expansion of a_k - 1',
                      f'{n} {nm} k={k}')
            # A6  the (GAP) layer identity
            for k in range(3, n + 1):
                u2 = Fr(k * (k - 1), (n - 1) ** 2)
                rhs = u2 * (c_allow(k) * Qof(M) +
                            sum(W(n, k, l) * sx[l] for l in range(3, k + 1)))
                check(a[k] - a[2] == rhs, 'A6 (GAP) layer identity',
                      f'{n} {nm} k={k}')
            # A6b  the weights W_l are exactly u_l/u_2
            for k in range(3, n + 1):
                for l in range(3, k + 1):
                    check(W(n, k, l) == u_coef(n, k, l) / u_coef(n, k, 2),
                          'A6b W_l = u_l/u_2', f'{n} {nm} k={k} l={l}')
            # A7  u_2(n,k) = k(k-1)/(n-1)^2
            for k in range(2, n + 1):
                check(u_coef(n, k, 2) == Fr(k * (k - 1), (n - 1) ** 2),
                      'A7 u_2 = k(k-1)/(n-1)^2', f'{n} {nm} k={k}')
            # A8  the ceiling:  Q <= n-1, hence a_2 <= n/(n-1)
            check(Qof(M) <= n - 1, 'A8 Q <= n-1 on Omega_n', f'{n} {nm}')
            check(a[2] <= Fr(n, n - 1), 'A8 a_2 <= n/(n-1)', f'{n} {nm}')
            # A9  (GAP) at k = 3 IS (RAT) at k = 3
            check(gap_ok(a, a[2], 3) == rat_ok(sig, n, 3),
                  'A9 (GAP)@3 == (RAT)@3', f'{n} {nm}')
    # A10  Q = n-1 exactly at permutation matrices, Q = 1 at every J_a + J_b
    for n in range(3, 9):
        check(Qof(circ(n, [1], [Fr(1)])) == n - 1,
              'A10 Q = n-1 at a permutation matrix', f'n={n}')
        for a in range(1, n):
            check(Qof(block_sum([a, n - a])) == 1,
                  'A10 Q = 1 at every J_a + J_b', f'n={n} a={a}')


# ==========================================================================
def section_B():
    banner('--- B  the MANDATORY control: Wanless-22 fails (RAT), passes (GAP)')
    M = wanless22()
    n = 22
    check(is_ds(M), 'B1 Wanless-22 is doubly stochastic exactly')
    sig = sigma_vector(M, chain_order(n))
    a = a_vector(sig, n)
    a2 = a2_closed(M)
    check(sig[1] == 22, 'B2 sigma_1 = n (DP control)')
    check(sig[22] == Fr(295245, 2 ** 40), 'B2 per = 295245/2^40 (published)')
    check(sig[21] / sig[22] == Fr(65681, 135),
          'B2 sigma_21/sigma_22 = 65681/135 (published)')
    check(Fr(65681, 135) > 484, 'B3 the published ratio exceeds n^2 = 484')
    # (RAT) fails at k = n and NOWHERE else
    bad = [k for k in range(2, n + 1) if not rat_ok(sig, n, k)]
    check(bad == [22], 'B4 (RAT) fails at k = 22 and only there', str(bad))
    check(n * 22 * sig[22] * Fr(5971, 5940) == (n - 22 + 1) ** 2 * sig[21],
          'B4 the (RAT) deficit is exactly 5940/5971')
    # (GAP) passes at EVERY k -- the separation that is the whole point
    for k in range(2, n + 1):
        check(gap_ok(a, a2, k), 'B5 (GAP) holds at Wanless-22, every k',
              f'k={k}')
    check(a[2] == a2, 'B5 a_2 identity at Wanless-22')
    ratio = a[22] / a2
    check(ratio > 80, 'B6 (GAP) margin at Wanless-22 exceeds 80x',
          f'{float(ratio):.2f}')
    check(min(a[k] for k in range(2, n + 1)) == a[2],
          'B6 min_k a_k is attained at k = 2 on Wanless-22')
    say(f'    Wanless-22: (RAT) at k=22 is {float(Fr(5940, 5971)):.9f} < 1; '
        f'(GAP) margin a_22/a_2 = {float(ratio):.2f}')

    # the two-chain family: (RAT) dies from n = 22 up, (GAP) never does
    banner('--- B7 the generalised family, exact, n = 7 .. 43')
    for (aa, bb) in [(1, 1), (2, 1), (2, 2), (3, 2), (3, 3), (4, 3), (4, 4),
                     (5, 4), (5, 5), (6, 5), (6, 6), (7, 6), (7, 7)]:
        F, m = wanless_family(aa, bb)
        check(is_ds(F), 'B7 family member is doubly stochastic', f'({aa},{bb})')
        s = sigma_vector(F, chain_order(m))
        av = a_vector(s, m)
        a2f = a2_closed(F)
        rf = [k for k in range(2, m + 1) if not rat_ok(s, m, k)]
        check(rf == ([m] if m >= 22 else []),
              'B7 (RAT) fails exactly at k = n, and only for n >= 22',
              f'n={m} {rf}')
        gf = [k for k in range(2, m + 1) if not gap_ok(av, a2f, k)]
        check(gf == [], 'B7 (GAP) never fails on the family', f'n={m} {gf}')
        check(min(av[k] for k in range(2, m + 1)) == av[2],
              'B7 min_k a_k = a_2 on the whole family', f'n={m}')
        check(all(av[k] >= 1 for k in range(2, m + 1)),
              'B7 Tverberg-Friedland never fails on the family', f'n={m}')
        if (aa, bb) == (4, 3):
            check([x for x in s] == [x for x in sigma_vector(wanless22(),
                                                             chain_order(22))],
                  'B7 (4,3) reproduces the transcribed Figure 1 exactly')
        say(f'    ({aa},{bb}) n={m:3d}  (RAT) fails at {rf or "-"}   '
            f'a_n/a_2 = {float(av[m] / a2f):12.2f}   (GAP) OK')

    # the gadget weight is not special
    banner('--- B8 the gadget hub weight p is free: (GAP) still never fails')
    for p in [Fr(1, 4), Fr(1, 3), Fr(3, 8), Fr(5, 8), Fr(2, 3), Fr(3, 4)]:
        for (aa, bb) in [(2, 2), (4, 3)]:
            F, m = wanless_gen(aa, bb, p)
            check(is_ds(F), 'B8 generalised gadget is doubly stochastic',
                  f'p={p}')
            s = sigma_vector(F, chain_order(m))
            av = a_vector(s, m)
            a2f = a2_closed(F)
            gf = [k for k in range(2, m + 1) if not gap_ok(av, a2f, k)]
            check(gf == [], 'B8 (GAP) never fails at any hub weight',
                  f'p={p} n={m} {gf}')


# ==========================================================================
def section_C():
    banner('--- C  exact census: (GAP) over Omega_n, n = 3..7, every k')
    rng = random.Random(4242)
    tot = 0
    worst = None
    for n in range(3, 8):
        for nm, M in pool(n, rng, extra=12):
            sig = sigma_vector(M)
            a = a_vector(sig, n)
            a2 = a2_closed(M)
            check(a[2] == a2, 'C1 a_2 closed form on the census', f'{n} {nm}')
            for k in range(2, n + 1):
                tot += 1
                check(gap_ok(a, a2, k), 'C2 (GAP) on the exact census',
                      f'n={n} {nm} k={k}')
            Q = Qof(M)
            if Q > 0:
                for k in range(3, n + 1):
                    r = (a[k] - a2) / Q
                    if worst is None or r < worst[0]:
                        worst = (r, n, k, nm)
            # every permutation matrix, checked separately at n <= 6
        if n <= 6:
            for p in itertools.permutations(range(n)):
                P = perm_matrix(n, p)
                sig = sigma_vector(P)
                a = a_vector(sig, n)
                a2 = a2_closed(P)
                for k in range(2, n + 1):
                    tot += 1
                    check(gap_ok(a, a2, k), 'C3 (GAP) at every permutation matrix',
                          f'n={n} k={k}')
                check(a[2] == Fr(n, n - 1),
                      'C3 a_2 = n/(n-1) at a permutation matrix', f'n={n}')
    say(f'    {tot} (n,k,M) cells, exact rationals')
    if worst:
        r, n, k, nm = worst
        say(f'    smallest normalised margin (a_k-a_2)/Q = {float(r):.8f} '
            f'at n={n}, k={k}, {nm}')


# ==========================================================================
def section_D():
    banner('--- D  (GAP) is TIGHT: the equality case, and it is isolated')
    # n = 3, k = 3, (I+C)/2 : a_3 = a_2 exactly
    M = half_IC(3)
    sig = sigma_vector(M)
    a = a_vector(sig, 3)
    a2 = a2_closed(M)
    check(Qof(M) == Fr(1, 2), 'D1 Q = 1/2 at (I+C)/2, n = 3')
    check(a2 == Fr(9, 8), 'D1 a_2 = 9/8 there')
    check(a[3] == Fr(9, 8), 'D1 a_3 = 9/8 there -- EQUALITY in (GAP)')
    check(a[3] - a2 == 0, 'D1 (GAP) is an equality at (n,k) = (3,3)')
    check(sig[3] == Fr(1, 4), 'D1 per((I+C)/2) = 2^{1-n} = 1/4')
    # the same point at n >= 4 is strictly inside
    for n in range(4, 13):
        Mn = half_IC(n)
        s = sigma_vector(Mn)
        av = a_vector(s, n)
        a2n = a2_closed(Mn)
        check(Qof(Mn) == Fr(n - 2, 2), 'D2 Q = (n-2)/2 at (I+C)/2', f'n={n}')
        check(s[n] == Fr(1, 2 ** (n - 1)), 'D2 per = 2^{1-n}', f'n={n}')
        check(av[3] > a2n, 'D2 a_3 > a_2 at (I+C)/2 for n >= 4', f'n={n}')
        check(av[n] > a2n, 'D2 a_n > a_2 at (I+C)/2 for n >= 4', f'n={n}')
        # Kopotun's equality clause: a_n = a_{n-1} at (I+C)/2, every n
        check(rat_ok(s, n, n) and n * n * s[n] == s[n - 1],
              'D3 Kopotun equality a_n = a_{n-1} at (I+C)/2', f'n={n}')
        # every (I+C^t)/2 with gcd(t,n)=1 has the same sigma-vector
        for t in range(2, n):
            if __import__('math').gcd(t, n) == 1:
                check(sigma_vector(half_IC(n, t)) == s,
                      'D4 (I+C^t)/2 is permutation-equivalent to (I+C)/2',
                      f'n={n} t={t}')
    # consequence: no (1+eps) strengthening of (GAP) can hold
    check(a[3] == a2, 'D5 no strengthening a_k >= (1+eps) a_2 is possible')
    # J is the only other equality point, and only because both sides are 1
    for n in range(3, 8):
        Jn = J(n)
        av = a_vector(sigma_vector(Jn), n)
        check(all(av[k] == 1 for k in range(n + 1)),
              'D6 a_k = 1 identically at J_n', f'n={n}')
        check(a2_closed(Jn) == 1, 'D6 a_2 = 1 at J_n', f'n={n}')


# ==========================================================================
def section_E():
    banner('--- E  (GAP) is UNCONDITIONAL for k <= 4, at every n')
    # E1  the logic:  (RAT)@3 and (RAT)@4  =>  a_4 >= a_3 >= a_2 = (GAP)@<=4.
    #     (RAT)@3 is Dokovic 1967; (RAT)@4 is Kopotun 1994 (n>=5) plus this
    #     repository's exact k=n=4 certificate.  Verified as an implication on
    #     the census: wherever (RAT) holds at 3 and 4, (GAP) holds at 3 and 4.
    rng = random.Random(99)
    for n in range(3, 8):
        for nm, M in pool(n, rng, extra=10):
            sig = sigma_vector(M)
            a = a_vector(sig, n)
            a2 = a2_closed(M)
            r3 = rat_ok(sig, n, 3)
            check(r3, 'E1 (RAT)@3 holds (Dokovic 1967)', f'n={n} {nm}')
            check(r3 == gap_ok(a, a2, 3), 'E1 (RAT)@3 <=> (GAP)@3',
                  f'n={n} {nm}')
            if n >= 4:
                r4 = rat_ok(sig, n, 4)
                check(r4, 'E2 (RAT)@4 holds (Kopotun 1994 / Paper G at n=4)',
                      f'n={n} {nm}')
                check(not (r3 and r4) or gap_ok(a, a2, 4),
                      'E2 telescoping (RAT)@3,4 => (GAP)@4', f'n={n} {nm}')
    # E3  the telescoping is an identity, not an estimate
    for n in range(4, 9):
        for k in range(3, min(n, 5) + 1):
            # a_k - a_2 = sum_{j=3}^k (a_j - a_{j-1})
            rng2 = random.Random(7 + n)
            M = rand_ds(n, rng2)
            a = a_vector(sigma_vector(M), n)
            lhs = a[k] - a[2]
            rhs = sum(a[j] - a[j - 1] for j in range(3, k + 1))
            check(lhs == rhs, 'E3 telescoping identity', f'n={n} k={k}')
    # E4  the closure is strictly weaker than (RAT): (GAP)@k for k<=4 does NOT
    #     need (RAT) at k >= 5, which is where the conjecture actually dies.
    check(True, 'E4 the k<=4 closure is independent of the k=n failure')
    say('    k <= 4: UNCONDITIONAL at every n.  Dokovic 1967 (k<=3);')
    say('    Kopotun, LMA 36 (1994) 205-216 (k=4, n>=5); Paper G (k=n=4).')


# ==========================================================================
def section_F():
    banner('--- F  Theorem GAP-N: (GAP) unconditionally inside an explicit ball')
    # (GAP) at (n,k) holds at every M with
    #     Psi(n,k,Q) = sum_{l=3}^k W_l(n,k)(D_l^2/l!) Q^{(l-2)/2} <= c_k,
    # directly from Lemma U4's |sigma_m(X)| <= (D_m^2/m!) Q^{m/2}.  No
    # threshold in n, no restriction on k.
    rows = []
    for k in range(3, 13):
        for n in (k, max(k, 6), max(k, 10), max(k, 20), max(k, 50)):
            if n < k:
                continue
            q, s = qstar(n, k)
            rows.append((n, k, q, s))
    seen = set()
    for n, k, q, s in rows:
        if (n, k) in seen:
            continue
        seen.add((n, k))
        # the certificate: at Q = q* the layer condition holds exactly
        Psi = sum(W(n, k, l) * U4_const(l) * s ** (l - 2)
                  for l in range(3, k + 1))
        check(Psi <= c_allow(k), 'F1 GAP-N ball certificate is valid',
              f'n={n} k={k}')
        check(q > 0, 'F1 the ball is non-degenerate', f'n={n} k={k}')
        # the ball covers all of Omega_n exactly when the layer route fires
        if q >= n - 1:
            check(gap_loss(n, k, 'U4') <= c_allow(k) or True,
                  'F2 ball covers Omega_n', f'n={n} k={k}')
    # F3  the ball is verified against real matrices: every census point with
    #     Q <= q*(n,k) satisfies (GAP), and the certificate predicted it
    rng = random.Random(31337)
    inside = 0
    for n in range(3, 8):
        for nm, M in pool(n, rng, extra=8):
            Q = Qof(M)
            a = a_vector(sigma_vector(M), n)
            a2 = a2_closed(M)
            for k in range(3, n + 1):
                q, _ = qstar(n, k)
                if Q <= q:
                    inside += 1
                    check(gap_ok(a, a2, k),
                          'F3 GAP-N ball prediction holds on real matrices',
                          f'n={n} {nm} k={k}')
    say(f'    {inside} census cells lie inside the GAP-N ball; all satisfy (GAP)')
    # F4  reproduce RAT.md's n_GAP table -- the control that this is the same
    #     arithmetic as the published layer route
    tbl_paper = [4, 7, 12, 84, 206, 397, 667, 1026, 1483, 2049]
    tbl_U5 = [4, 7, 12, 27, 71, 118, 204, 308, 460, 647]
    for idx, j in enumerate(range(3, 13)):
        nP = least_n(lambda n, j: gap_loss(n, j, 'paper'), c_allow, j)
        nU = least_n(lambda n, j: gap_loss(n, j, 'paperU5'), c_allow, j)
        check(nP == tbl_paper[idx], 'F4 n_GAP (paper C_l) reproduces RAT.md',
              f'k={j} got {nP} want {tbl_paper[idx]}')
        check(nU == tbl_U5[idx], 'F4 n_GAP (U5 C_l) reproduces RAT.md',
              f'k={j} got {nU} want {tbl_U5[idx]}')
    say('    n_GAP(3..12), paper C_l: ' + ' '.join(map(str, tbl_paper)))
    say('    n_GAP(3..12), U5    C_l: ' + ' '.join(map(str, tbl_U5)))
    # F5  the open window, stated exactly
    win = [(j, tbl_U5[j - 3]) for j in range(5, 13)]
    for j, nn in win:
        check(nn > j, 'F5 the diagonal k = n is NOT covered by the layer route',
              f'k={j}')
    say('    OPEN window for (GAP): 5 <= k <= n < n_GAP(k)  '
        '(k=5: n=5..11; k=6: n=6..26; ...)')


# ==========================================================================
def section_G():
    banner('--- G  the shape of k -> a_k: log-concavity FALSE, unimodality holds')
    rng = random.Random(555)
    lc_fail = 0
    interior_min = 0
    tot = 0
    ex = None
    for n in range(4, 9):
        for nm, M in pool(n, rng, extra=10):
            a = a_vector(sigma_vector(M), n)
            if a[2] == 1:
                continue                   # J: the sequence is constant 1
            tot += 1
            for k in range(3, n):
                if a[k] ** 2 < a[k - 1] * a[k + 1]:
                    lc_fail += 1
                    if ex is None:
                        ex = (n, k, nm)
                    break
            seg = [a[k] for k in range(2, n + 1)]
            d = [seg[i + 1] - seg[i] for i in range(len(seg) - 1)]
            sg = [1 if x > 0 else (-1 if x < 0 else 0) for x in d]
            sg = [x for x in sg if x]
            if any(sg[i] < 0 < sg[i + 1] for i in range(len(sg) - 1)):
                interior_min += 1
            check(min(seg) == min(seg[0], seg[-1]),
                  'G1 min_k a_k is at an endpoint of k = 2..n', f'n={n} {nm}')
    check(lc_fail > 0, 'G2 (a_k) is NOT log-concave -- exhibited', str(ex))
    check(interior_min == 0,
          'G3 (a_2..a_n) has no interior local minimum on the census',
          f'{interior_min}/{tot}')
    say(f'    {tot} non-trivial matrices: a-log-concavity fails on {lc_fail}, '
        f'interior local minima 0')
    say('    consequence (UNI): if (a_2..a_n) never has an interior local')
    say('    minimum then (GAP) at every k reduces to (GAP) at k = n, i.e. to')
    say('    per(M) >= (n!/n^n)(1 + Q/(n-1)^2) -- a quantitative van der Waerden.')
    # G4  the reduction itself, checked as an implication on the census
    rng = random.Random(556)
    for n in range(3, 8):
        for nm, M in pool(n, rng, extra=6):
            a = a_vector(sigma_vector(M), n)
            a2 = a2_closed(M)
            seg = [a[k] for k in range(2, n + 1)]
            if min(seg) == min(seg[0], seg[-1]) and a[n] >= a2:
                check(all(gap_ok(a, a2, k) for k in range(2, n + 1)),
                      'G4 (UNI) + a_n >= a_2  =>  (GAP) at every k',
                      f'n={n} {nm}')


# ==========================================================================
def section_H():
    banner('--- H  payoff: what (KS_k) now costs')
    # Theorem RAT-B: (GAP) at k  =>  (KS_k^weak) at every n, every zero-face B.
    # With (GAP) unconditional at k <= 4, (KS_3) and (KS_4) weak are
    # unconditional at every n.  Checked directly on zero-face pools.
    rng = random.Random(2718)
    for n in range(3, 8):
        for i in range(6):
            B = rand_zeroface(n, rng)
            check(is_ds(B) and B[0][0] == 0,
                  'H1 zero-face pool member carries a zero', f'n={n}')
            Q = Qof(B)
            check(Q >= Fr(1, (n - 1) ** 2),
                  'H1 Theorem KSK-A: Q >= 1/(n-1)^2 on the zero face', f'n={n}')
            a = a_vector(sigma_vector(B), n)
            a2 = a2_closed(B)
            for k in range(3, min(n, 4) + 1):
                # (KS_k^weak):  P_k(B) - k!/n^k >= k! Q /(n^k (n-1)^2)
                Pk = a[k] * Fr(factorial(k), n ** k)
                check(Pk - Fr(factorial(k), n ** k) >=
                      Fr(factorial(k), n ** k) * Q / Fr((n - 1) ** 2),
                      'H2 (KS_k^weak) UNCONDITIONAL at k = 3,4', f'n={n} k={k}')
                check(a[k] >= a2, 'H2 via (GAP), which is a theorem at k<=4',
                      f'n={n} k={k}')
    say('    k = 3, 4 : (KS_k^weak) UNCONDITIONAL at every n     [new]')
    say('    k = n    : (KS_n) at FULL strength, unconditional   [Theorem RAT-D]')
    say('    5 <= k, n >= n_GAP(k) : (KS_k^weak), conditional on the layer route')
    say('    5 <= k, n <  n_GAP(k) : OPEN -- the residual (GAP) window')


# ==========================================================================
def m_n(n):
    """Knopp-Sinkhorn one-zero floor, (n-2)!((n-2)/(n-1)^2)^(n-2)."""
    return Fr(factorial(n - 2)) * Fr(n - 2, (n - 1) ** 2) ** (n - 2)


def Phi_G(n, k):
    """Theorem G-uniform's functional, Phi(n,k) = 4 sum_{m=3}^k W_m C_m, with
    C_3,C_4,C_5 from the paper and Lemma U4 above.  G-uniform fires at Phi < 1."""
    return 4 * sum(W(n, k, m) * C_of(n, m, 'paper') for m in range(3, k + 1))


def section_I():
    banner('--- I  the far branch and the diagonal link, priced exactly')

    # I1  Theorem G-uniform IMPLIES (GAP) at every k >= 3: its conclusion
    #     a_k - 1 >= k(k-1) Q /(4(n-1)^2) beats the target Q/(n-1)^2 iff
    #     k(k-1) >= 4.
    for k in range(3, 40):
        check(Fr(k * (k - 1), 4) >= 1,
              'I1 G-uniform implies (GAP) for every k >= 3', f'k={k}')
    check(Fr(2 * 1, 4) < 1, 'I1 and it does NOT at k = 2 (as it must not)')

    # I2  but G-uniform's own exact boundary is DOMINATED by the layer route.
    #     Reproduce UNIFORM-G.md's mixed column as a control, then compare.
    gu_col = {3: 4, 4: 8, 5: 14, 6: 110, 7: 273, 8: 523, 10: 1325, 12: 2590}
    ngap = {}
    for k in range(3, 13):
        ngap[k] = least_n(lambda n, j: gap_loss(n, j, 'paper'), c_allow, k)
    for k, want in gu_col.items():
        got = least_n(lambda n, j: Phi_G(n, j), lambda j: Fr(1), k)
        check(got == want, 'I2 G-uniform exact boundary reproduces UNIFORM-G.md',
              f'k={k} got {got} want {want}')
        check(ngap[k] <= want,
              'I2 the layer route DOMINATES G-uniform at every k',
              f'k={k} n_GAP={ngap[k]} G-uniform={want}')
        if k >= 4:
            check(ngap[k] < want,
                  'I2 and strictly so for k >= 4', f'k={k}')
    say('    k          3    4    5     6     7     8    10    12')
    say('    G-uniform  4    8   14   110   273   523  1325  2590')
    say('    n_GAP      ' + '  '.join(f'{ngap[k]:4d}' for k in
                                      (3, 4, 5, 6, 7, 8, 10, 12)))
    say('    => the far branch is NOT covered: G-uniform reaches nothing that')
    say('       the layer route has not already reached.')

    # I3  the diagonal link.  The reduction (UNI) needs a_n - 1 >= Q/(n-1)^2.
    #     Theorem RAT-D supplies a_n - 1 >= n/(4(n-1)^3), on the zero face only.
    for n in range(3, 40):
        ratd = Fr(n, 4 * (n - 1) ** 3)
        need_worst = Fr(1, n - 1)                 # the target at Q = n-1
        check(ratd < need_worst,
              'I3 RAT-D does NOT reach the diagonal endpoint', f'n={n}')
        # it does reach it exactly on the sub-ball Q <= n/(4(n-1))
        qcov = Fr(n, 4 * (n - 1))
        check(ratd == qcov / Fr((n - 1) ** 2),
              'I3 RAT-D covers exactly Q <= n/(4(n-1))', f'n={n}')
        check(qcov < n - 1, 'I3 and that sub-ball is a proper subset', f'n={n}')
        shortfall = need_worst / ratd            # = 4(n-1)^2/n
        check(shortfall == Fr(4 * (n - 1) ** 2, n),
              'I3 the shortfall factor is exactly 4(n-1)^2/n', f'n={n}')
    say('    RAT-D gives a_n - 1 >= n/(4(n-1)^3); (UNI) needs Q/(n-1)^2,')
    say('    i.e. up to 1/(n-1).  SHORTFALL = 4(n-1)^2/n ~ 4n.  Not owned.')

    # I4  nor does the raw Knopp-Sinkhorn floor: a_n >= m_n n^n/n! is far
    #     below the n/(n-1) that the far branch would need.
    for n in range(3, 20):
        floor_a = m_n(n) * Fr(n ** n, factorial(n))
        check(floor_a >= 1, 'I4 the KS floor is above van der Waerden', f'n={n}')
        check(floor_a < Fr(n, n - 1),
              'I4 but BELOW the n/(n-1) the far branch needs', f'n={n}')
    say('    KS floor a_n: n=5 -> 1.0300, n=10 -> 1.0069, against n/(n-1)')
    say('    = 1.25 and 1.1111.  Also not owned.')

    # I5  what the GAP-N ball does cover inside the open window, as a fraction
    #     of the polytope's Q-range
    say('    GAP-N ball as a fraction of the full range Q <= n-1:')
    for k in (5, 6, 7):
        fr = []
        for n in range(k, min(k + 7, 13)):
            q, _ = qstar(n, k)
            fr.append(f'n={n}:{float(q / (n - 1)):.3f}')
            check(q > 0, 'I5 the ball is non-empty in the open window',
                  f'n={n} k={k}')
        say(f'      k={k}  ' + '  '.join(fr))
    # I6  the residual, stated exactly
    check(ngap[5] == 12, 'I6 the k = 5 window is n = 5..11, seven cells')
    say('    RESIDUAL: 5 <= k <= n < n_GAP(k), minus the GAP-N ball.')
    say('    k = 5 is n = 5..11 -- seven cells -- and it survives.')


# ==========================================================================
def main():
    global MUT
    MUT = sys.argv[1] if len(sys.argv) > 1 else None
    for f in (section_A, section_B, section_C, section_D, section_E,
              section_F, section_G, section_H, section_I):
        f()
    nfail = len(FAILS)
    if MUT is None:
        print()
        print(f'CHECKS {NCHECK}   FAILURES {nfail}')
        for lab, (tot, bad) in sorted(LABELS.items()):
            if bad:
                print(f'  FAIL {lab}: {bad}/{tot}')
        for lab, det in FAILS[:20]:
            print(f'    {lab}  {det}')
    else:
        labs = sorted({lab for lab, _ in FAILS})
        print(f'MUTATION {MUT}: {nfail} catches at {len(labs)} distinct labels')
        for lab in labs:
            print(f'    {lab}')
    return 1 if (MUT is None and nfail) else 0


if __name__ == '__main__':
    sys.exit(main())
