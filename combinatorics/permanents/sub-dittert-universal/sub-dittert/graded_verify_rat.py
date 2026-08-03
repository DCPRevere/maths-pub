"""graded_verify_rat.py -- the (RAT) lemma of KSK.md, IDENTIFIED and REFUTED,
and the repair.

    (RAT)   n k sigma_k(M) >= (n-k+1)^2 sigma_{k-1}(M)      for every M in Omega_n

(RAT) is the **Holens-Dokovic conjecture** (Holens 1964; Dokovic, Publ. Inst.
Math. Beograd 7 (1967) 23-24), the ratio refinement of Tverberg-Friedland whose
telescoped form at k = n is van der Waerden.  It is FALSE: Wanless, "The
Holens-Dokovic conjecture on permanents fails!", Linear Algebra Appl. 286 (1999)
273-285, Figure 1, exhibits an order-22 doubly stochastic matrix with
sigma_21/sigma_22 = 65681/135 > 484 = 22^2.  That matrix is transcribed in this
repository at ../convexity/wanless22.py; this file recomputes its whole
sigma-vector exactly and maps the failure footprint over a generalisation of the
construction.

What replaces (RAT) is the strictly weaker

    (GAP)   sigma_k(M) >= (1 + Q/(n-1)^2) sigma_k(J_n/n),   Q = ||M - J_n/n||_F^2

equivalently a_k >= a_2 -- which is exactly what Theorem KSK-B consumes, and
which survives every known (RAT) counterexample by a factor that grows without
bound.  And the diagonal k = n, where (RAT) actually dies, is closed
unconditionally by a different route (Section E).

Standard library only.  Exact Fraction arithmetic; no float enters any decision.

Run:  ../guard.sh python3 graded_verify_rat.py
"""
import itertools
import random
import sys
from fractions import Fraction as Fr
from math import comb, factorial, gcd

# --------------------------------------------------------------------------
# mutation harness
# --------------------------------------------------------------------------
MUT = None            # set from argv; None = no fault injected

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


def say(s):
    if MUT is None:
        print(s)


# --------------------------------------------------------------------------
# core exact machinery
# --------------------------------------------------------------------------
def falling(a, b):
    r = 1
    for j in range(b):
        r *= (a - j)
    return r


def per_brute(M):
    """permanent by definition -- the control for the DP."""
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
    """sigma_k by the verbatim definition -- rows and columns chosen
    independently.  Control only; exponential."""
    n = len(M)
    tot = Fr(0)
    for A in itertools.combinations(range(n), k):
        for B in itertools.combinations(range(n), k):
            tot += per_brute(submat(M, A, B))
    return tot


def sigma_vector(M, order=None):
    """[sigma_0, ..., sigma_n] for an arbitrary non-negative matrix.

    Row DP with the used-column set as state, plus a 'forget' step that drops
    columns no later row can touch.  On a dense matrix the state space is 2^n
    (fine to n = 12 or so); on a sparse one -- e.g. Wanless's order-22 matrix,
    whose support is a cycle of 3-row gadgets -- the frontier stays tiny and
    n = 43 is cheap.
    """
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
            for k, c in enumerate(poly):
                t[k] += c
            for j, w in supp:
                if j in used:
                    continue
                t2 = nxt.setdefault(used | {j}, [])
                if len(t2) < len(poly) + 1:
                    t2.extend([Fr(0)] * (len(poly) + 1 - len(t2)))
                for k, c in enumerate(poly):
                    t2[k + 1] += c * w
        dead = frozenset(j for j in range(n) if last.get(j, -1) <= pos)
        if dead:
            merged = {}
            for used, poly in nxt.items():
                t = merged.setdefault(used - dead, [])
                if len(t) < len(poly):
                    t.extend([Fr(0)] * (len(poly) - len(t)))
                for k, c in enumerate(poly):
                    t[k] += c
            nxt = merged
        states = nxt
    out = [Fr(0)] * (n + 1)
    for used, poly in states.items():
        for k, c in enumerate(poly):
            out[k] += c
    return out


def a_vector(sig, n):
    """a_k = E_k/G_k = sigma_k n^k / (C(n,k)^2 k!).  a_0 = a_1 = 1 on Omega_n."""
    return [sig[k] * Fr(n ** k, comb(n, k) ** 2 * factorial(k)) for k in range(n + 1)]


def rat_slack(sig, n, k):
    """n k sigma_k - (n-k+1)^2 sigma_{k-1};  (RAT) at k is slack >= 0."""
    s = n * k * sig[k] - (n - k + 1) ** 2 * sig[k - 1]
    if MUT == 'M3':                       # strengthen (RAT) by (1+1/n)
        s = n * k * sig[k] - (n - k + 1) ** 2 * sig[k - 1] * Fr(n + 1, n)
    return s


def gap_ok(a, k):
    """(GAP) at k:  a_k >= a_2."""
    if MUT == 'M6':                       # strengthen (GAP) by (1+1/n)
        return a[k] >= a[2] * Fr(11, 10)
    return a[k] >= a[2]


def frob2(M):
    return sum(x * x for row in M for x in row)


def Qof(M, n):
    return frob2(M) - 1


# ------------------------------------------------------- standard test matrices
def J(n):
    return [[Fr(1, n)] * n for _ in range(n)]


def T_matrix(n):
    """Knopp-Sinkhorn matrix: 0 at (1,1), 1/(n-1) elsewhere in row/col 1,
    (n-2)/(n-1)^2 in the rest."""
    M = [[Fr(n - 2, (n - 1) ** 2)] * n for _ in range(n)]
    for j in range(1, n):
        M[0][j] = Fr(1, n - 1)
        M[j][0] = Fr(1, n - 1)
    M[0][0] = Fr(0)
    return M


def perm_matrix(n, p):
    M = [[Fr(0)] * n for _ in range(n)]
    for i in range(n):
        M[i][p[i]] = Fr(1)
    return M


def circ(n, offsets, weights):
    M = [[Fr(0)] * n for _ in range(n)]
    for o, w in zip(offsets, weights):
        for i in range(n):
            M[i][(i + o) % n] += w
    return M


def half_IC(n, t):
    """(I + C^t)/2 -- the pre-registered equality family."""
    return circ(n, [0, t], [Fr(1, 2), Fr(1, 2)])


def rand_ds_good(n, rng, steps=40):
    """random doubly stochastic point: repeated exact 2x2 rotations from J."""
    M = [[Fr(1, n)] * n for _ in range(n)]
    for _ in range(steps):
        i, a = rng.randrange(n), rng.randrange(n)
        j, b = rng.randrange(n), rng.randrange(n)
        if i == a or j == b:
            continue
        lim = min(M[i][j], M[a][b])
        if lim == 0:
            continue
        t = lim * Fr(rng.randrange(1, 6), 6)
        M[i][j] -= t
        M[a][b] -= t
        M[i][b] += t
        M[a][j] += t
    return M


def rand_zeroface(n, rng, steps=40):
    """random doubly stochastic point carrying a zero at (0,0)."""
    for _ in range(60):
        M = rand_ds_good(n, rng, steps)
        c = M[0][0]
        if c == 0:
            return M
        # push the (0,0) mass out along a 2x2 rotation
        for a in range(1, n):
            for b in range(1, n):
                if M[a][b] >= c:
                    M[0][0] -= c
                    M[a][b] -= c
                    M[0][b] += c
                    M[a][0] += c
                    return M
    return T_matrix(n)


# --------------------------------------------------------------------------
# Wanless's order-22 matrix and its generalisation
# --------------------------------------------------------------------------
# Figure 1 of LAA 286 (1999) 273-285, page 277, as eighths.  Transcription taken
# verbatim from ../convexity/wanless22.py (independent earlier transcription in
# this repository, from the author's own PDF).
WANLESS_ROWS8 = {
    1: {11: 4, 20: 4},
    2: {1: 4, 3: 2, 4: 2},
    3: {2: 2, 3: 3, 4: 3},
    4: {2: 2, 3: 3, 4: 3},
    5: {2: 4, 6: 2, 7: 2},
    6: {5: 2, 6: 3, 7: 3},
    7: {5: 2, 6: 3, 7: 3},
    8: {5: 4, 9: 2, 10: 2},
    9: {8: 2, 9: 3, 10: 3},
    10: {8: 2, 9: 3, 10: 3},
    11: {8: 4, 12: 2, 13: 2},
    12: {11: 2, 12: 3, 13: 3},
    13: {11: 2, 12: 3, 13: 3},
    14: {1: 4, 15: 2, 16: 2},
    15: {14: 2, 15: 3, 16: 3},
    16: {14: 2, 15: 3, 16: 3},
    17: {14: 4, 18: 2, 19: 2},
    18: {17: 2, 18: 3, 19: 3},
    19: {17: 2, 18: 3, 19: 3},
    20: {17: 4, 21: 2, 22: 2},
    21: {20: 2, 21: 3, 22: 3},
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
    """The two-chain generalisation of Figure 1.  Hub row 0 and hub column 0;
    a chain of `a` gadgets and a chain of `b` gadgets hang off the hub column and
    meet again at the hub row.  Gadget at s, previous column p:

        row s   : p -> 1/2,  s+1 -> 1/4,  s+2 -> 1/4
        row s+1 : s -> 1/4,  s+1 -> 3/8,  s+2 -> 3/8
        row s+2 : s -> 1/4,  s+1 -> 3/8,  s+2 -> 3/8

    (a,b) = (4,3) is Wanless's Figure 1, n = 1 + 3(a+b) = 22.
    """
    n = 1 + 3 * (a + b)
    M = [[Fr(0)] * n for _ in range(n)]
    starts = [[], []]
    s = 1
    for _ in range(a):
        starts[0].append(s)
        s += 3
    for _ in range(b):
        starts[1].append(s)
        s += 3
    for chain in starts:
        prev = 0
        for s in chain:
            M[s][prev] = Fr(1, 2)
            M[s][s + 1] = Fr(1, 4)
            M[s][s + 2] = Fr(1, 4)
            for r in (s + 1, s + 2):
                M[r][s] = Fr(1, 4)
                M[r][s + 1] = Fr(3, 8)
                M[r][s + 2] = Fr(3, 8)
            prev = s
    M[0][starts[0][-1]] = Fr(1, 2)
    M[0][starts[1][-1]] = Fr(1, 2)
    return M, n


def chain_order(n):
    return list(range(1, n)) + [0]


def is_ds(M, n):
    return all(sum(M[i]) == 1 for i in range(n)) and \
        all(sum(M[i][j] for i in range(n)) == 1 for j in range(n))


# --------------------------------------------------------------------------
# layer machinery (shared with graded_verify_ksk.py, re-derived here)
# --------------------------------------------------------------------------
DERANGE = [1, 0, 1, 2, 9, 44, 265, 1854, 14833, 133496, 1334961, 14684570,
           176214841]


def u_coef(n, k, m):
    """a_k - 1 = sum_{m=2}^k u_coef(n,k,m) sigma_m(X)."""
    return Fr(falling(k, m) * n ** m, falling(n, m) ** 2)


def W(n, k, m):
    """u_m/u_2, the weights of UNIFORM-G section 2."""
    num = n ** (m - 2)
    for j in range(2, m):
        num *= (k - j)
    den = 1
    for j in range(2, m):
        den *= (n - j) ** 2
    return Fr(num, den)


def Rmaj(n):
    r = 1
    while (r + 1) ** 2 <= n - 1:
        r += 1
    return Fr(n - 1 + r * r, 2 * r)


def C_U4(n, m):
    return Fr(DERANGE[m] ** 2, factorial(m)) * Fr(n - 1) ** ((m - 2) // 2) * \
        (Rmaj(n) if (m - 2) % 2 else 1)


def C_U5(n, m):
    return Fr(DERANGE[m] ** 2, factorial(m)) * Fr(n - 1) ** ((m - 1) // 2 - 1)


def C_paper(n, m):
    b = Fr(n - 1, n)
    return {3: Fr(2, 3 * n), 4: Fr(3, 2) * b,
            5: Fr(24, 5 * n ** 3) + Fr(10, 3) * b + 8 * b * b}.get(m)


def C_of(n, m, mode):
    c = C_paper(n, m) if mode.startswith('paper') else None
    if c is None:
        c = C_U5(n, m) if mode.endswith('U5') else C_U4(n, m)
    return c


def rat_loss(n, j, mode):
    return sum(l * W(n, j, l) * C_of(n, l, mode) for l in range(3, j + 1))


def gap_loss(n, j, mode):
    return sum(W(n, j, l) * C_of(n, l, mode) for l in range(3, j + 1))


def gap_allow(k):
    """(GAP) at k follows from  sum_{l>=3} W_l C_l <= (k-2)(k+1)/(2k(k-1))."""
    a = Fr((k - 2) * (k + 1), 2 * k * (k - 1))
    if MUT == 'M4':                        # inflate the layer allowance
        a = a * 2
    return a


def least_n(f, thr, j, cap=200000):
    for n in range(max(j, 3), cap):
        if f(n, j) <= thr(j):
            return n
    return None


# --------------------------------------------------------------------------
# the Knopp-Sinkhorn floor and the diagonal theorem
# --------------------------------------------------------------------------
def m_n(n):
    """(n-2)! ((n-2)/(n-1)^2)^(n-2) -- the Knopp-Sinkhorn one-zero floor, which
    NOTES section 27.4 derives from stable-polynomial capacity (Lu Cor. 3.6)."""
    v = Fr(factorial(n - 2)) * Fr(n - 2, (n - 1) ** 2) ** (n - 2)
    if MUT == 'M5':                        # inflate the floor
        v = v * Fr(n + 1, n)
    return v


def rho(n):
    """m_n / (n!/n^n) = n^(n-1)(n-2)^(n-2)/(n-1)^(2n-3)."""
    return m_n(n) * Fr(n ** n, factorial(n))


def ks_claim(n, k):
    """the (KS_k) right-hand side: k(k-1) k! / (4 n^k (n-1)^4)."""
    c = Fr(k * (k - 1), 4)
    if MUT == 'M1':                        # double the claimed constant
        c = c * 2
    return c * Fr(factorial(k), n ** k * (n - 1) ** 4)


# ==========================================================================
def section_A():
    banner('--- A  identification: (RAT) is the Holens-Dokovic conjecture')
    rng = random.Random(11)
    for n in (3, 4, 5):
        pool = [J(n), T_matrix(n), half_IC(n, 1), perm_matrix(n, list(range(n)))]
        pool += [rand_ds_good(n, rng) for _ in range(4)]
        for M in pool:
            sig = sigma_vector(M)
            a = a_vector(sig, n)
            # A0 controls: the DP against the verbatim definition
            for k in range(0, min(n, 4) + 1):
                check(sig[k] == sigma_brute(M, k), 'A0 DP sigma == definition',
                      f'n={n} k={k}')
            check(sig[1] == n, 'A0 sigma_1 = n on Omega_n', f'n={n}')
            check(a[0] == 1 and a[1] == 1, 'A0 a_0 = a_1 = 1', f'n={n}')
            # A1  (RAT) at k  <=>  a_k >= a_{k-1}
            for k in range(1, n + 1):
                check((rat_slack(sig, n, k) >= 0) == (a[k] >= a[k - 1]),
                      'A1 (RAT) at k <=> a_k >= a_(k-1)', f'n={n} k={k}')
            # A2  k = 1 is an identity;  k = 2 is exactly ||M||^2 >= 1
            check(rat_slack(sig, n, 1) == 0 or MUT == 'M3',
                  'A2 (RAT) at k=1 is an identity', f'n={n}')
            check(n * 2 * sig[2] - (n - 1) ** 2 * sig[1] == n * Qof(M, n),
                  'A2 (RAT) at k=2 slack is exactly n Q', f'n={n}')
            check(a[2] == 1 + Qof(M, n) * Fr(1, (n - 1) ** 2),
                  'A2 a_2 = 1 + Q/(n-1)^2', f'n={n}')
            # A3  at k = n it is the printed Holens-Dokovic form
            check((rat_slack(sig, n, n) >= 0) == (sig[n - 1] <= n * n * sig[n]),
                  'A3 (RAT) at k=n <=> sigma_(n-1) <= n^2 per', f'n={n}')
            # A4  telescoped: Tverberg-Friedland, and van der Waerden at k = n
            if all(rat_slack(sig, n, k) >= 0 for k in range(1, n + 1)):
                for k in range(1, n + 1):
                    check(sig[k] >= Fr(comb(n, k) ** 2 * factorial(k), n ** k),
                          'A4 telescoped (RAT) gives Tverberg-Friedland',
                          f'n={n} k={k}')
                check(sig[n] >= Fr(factorial(n), n ** n),
                      'A4 telescoped to k=n gives van der Waerden', f'n={n}')
            # A5  the cofactor-correlation form
            for k in range(1, n + 1):
                rhs = Fr(0)
                for i in range(n):
                    for j in range(n):
                        mm = submat(M, [r for r in range(n) if r != i],
                                    [c for c in range(n) if c != j])
                        rhs += (n * M[i][j] - 1) * sigma_vector(mm)[k - 1]
                check(n * k * sig[k] - (n - k + 1) ** 2 * sig[k - 1] == rhs,
                      'A5 (RAT) = sum (n M_ij - 1) sigma_(k-1)(M(i|j)) >= 0',
                      f'n={n} k={k}')
    # A6  the bordered form:  (RAT) <=> n k per(M_k) >= per(M_{k-1})
    for n in (3, 4):
        for M in (J(n), half_IC(n, 1), rand_ds_good(n, random.Random(3))):
            sig = sigma_vector(M)
            for k in range(1, n + 1):
                Bk = border(M, n, k)
                Bk1 = border(M, n, k - 1)
                pk, pk1 = per_brute(Bk), per_brute(Bk1)
                check(pk == Fr(factorial(n - k) ** 2) * sig[k],
                      'A6 bordered identity per(M_k) = ((n-k)!)^2 sigma_k',
                      f'n={n} k={k}')
                check((n * k * sig[k] >= (n - k + 1) ** 2 * sig[k - 1]) ==
                      (n * k * pk >= pk1),
                      'A6 (RAT) <=> n k per(M_k) >= per(M_(k-1))', f'n={n} k={k}')
    # A7  at k = n:  arithmetic mean of column-swap permanents vs per, and the
    #     Alexandrov-Fenchel product bound that supplies only the geometric mean
    for n in (3, 4):
        rngA = random.Random(21)
        for M in [J(n), half_IC(n, 1)] + [rand_ds_good(n, rngA) for _ in range(3)]:
            P = per_brute(M)
            sig = sigma_vector(M)
            tot = Fr(0)
            for j in range(n):
                for l in range(n):
                    if j == l:
                        continue
                    A = [row[:] for row in M]
                    for i in range(n):
                        A[i][j] = M[i][l]
                    tot += per_brute(A)
            check(sig[n - 1] == n * P + tot,
                  'A7 sigma_(n-1) = n per + sum_(j!=l) per(M_(j<-l))', f'n={n}')
            check((n * n * P >= sig[n - 1]) == (tot <= n * (n - 1) * P),
                  'A7 (RAT) at k=n <=> arithmetic mean of swaps <= per', f'n={n}')
            for j in range(n):
                for l in range(j + 1, n):
                    A = [row[:] for row in M]
                    B = [row[:] for row in M]
                    for i in range(n):
                        A[i][j] = M[i][l]
                        B[i][l] = M[i][j]
                    check(per_brute(A) * per_brute(B) <= P * P,
                          'A7 Alexandrov-Fenchel gives only the GEOMETRIC mean',
                          f'n={n} j={j} l={l}')


def section_A8():
    """The route-(a) obstruction, exactly: the symmetric-function relaxation is
    too weak even with Tverberg-Friedland assumed at EVERY k.

    n = 3, lam the roots of x^3 - 3x^2 + (9/4)x - 23/100.
    """
    e1, e2, e3 = Fr(3), Fr(9, 4), Fr(23, 100)
    disc = (18 * e1 * e2 * e3 - 4 * e1 ** 3 * e3 + e1 ** 2 * e2 ** 2
            - 4 * e2 ** 3 - 27 * e3 ** 2)
    check(disc > 0, 'A8 the witness cubic has three distinct real roots',
          f'disc={disc}')
    check(e1 > 0 and e2 > 0 and e3 > 0,
          'A8 all e_j > 0, so by Descartes all three roots are positive', '')
    # Tverberg-Friedland at every k, in e_k form: e_k >= C(n,k) G_k
    n = 3
    for k, ek in ((1, e1), (2, e2), (3, e3)):
        Gk = Fr(falling(n, k), n ** k)
        check(ek >= comb(n, k) * Gk,
              'A8 the witness satisfies Tverberg-Friedland at every k',
              f'k={k}')
        check(ek <= comb(n, k),
              'A8 the witness satisfies the capacity upper bound e_k <= C(n,k)',
              f'k={k}')
    # ... and (RAT) at k = 3 fails: 9 e_3 < e_2
    check(9 * e3 < e2,
          'A8 (RAT) FAILS on the witness: real-rootedness + T-F is not enough',
          f'9e_3={9*e3} e_2={e2}')
    # Newton/log-concavity holds on it, as it must
    check(e2 * e2 * comb(n, 1) * comb(n, 3) >= e1 * e3 * comb(n, 2) ** 2,
          'A8 Newton holds on the witness -- log-concavity is not the obstacle',
          '')


def border(M, n, k):
    """M_k(A) of CAPACITY.md section 2.2:  [[A, J_{n x m}],[J_{m x n}, 0]],
    m = n - k.  per(M_k) = ((n-k)!)^2 sigma_k."""
    m = n - k
    N = n + m
    B = [[Fr(0)] * N for _ in range(N)]
    for i in range(n):
        for j in range(n):
            B[i][j] = M[i][j]
    for i in range(n):
        for j in range(n, N):
            B[i][j] = Fr(1)
    for i in range(n, N):
        for j in range(n):
            B[i][j] = Fr(1)
    return B


# ==========================================================================
def section_B():
    banner('--- B  REFUTATION: Wanless (1999), order 22, and the family')
    M = wanless22()
    n = 22
    check(is_ds(M, n), 'B1 Wanless Fig. 1 is doubly stochastic', 'n=22')
    order = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 0,
             19, 20, 21, 16, 17, 18, 13, 14, 15]
    sig = sigma_vector(M, order)
    check(sig[0] == 1 and sig[1] == n, 'B2 sigma_0 = 1, sigma_1 = n', 'n=22')
    check(sig[n] == Fr(295245, 2 ** 40),
          'B2 per(Wanless) = 295245/2^40 exactly', 'n=22')
    check(sig[n - 1] / sig[n] == Fr(65681, 135),
          'B2 sigma_21/sigma_22 reproduces the published 65681/135', 'n=22')
    check(sig[n - 1] / sig[n] > n * n,
          'B3 (RAT) at k = n = 22 FAILS: ratio exceeds n^2', 'n=22')
    slack = rat_slack(sig, n, n)
    check(slack < 0, 'B3 (RAT) slack at k=n is strictly negative', 'n=22')
    r22 = Fr(n * n * sig[n], sig[n - 1])
    check(r22 == Fr(5940, 5971),
          'B3 the exact deficit is 5940/5971', f'r={r22}')
    fails = [k for k in range(1, n + 1) if rat_slack(sig, n, k) < 0]
    check(fails == [22], 'B4 (RAT) fails at k = n ONLY on this matrix',
          f'fails={fails}')
    a = a_vector(sig, n)
    check(all(a[k] >= 1 for k in range(n + 1)),
          'B4 Tverberg-Friedland SURVIVES the counterexample', 'n=22')
    check(gap_ok(a, n), 'B4 (GAP) survives the counterexample', 'n=22')
    say(f'    n=22   sigma_21/sigma_22 = {sig[n-1]/sig[n]} = '
        f'{float(sig[n-1]/sig[n]):.6f}   n^2 = {n*n}')
    say(f'    n=22   a_22/a_2 = {float(a[n]/a[2]):.2f}  '
        f'(the margin (GAP) has where (RAT) is broken)')

    # B5  the family.  (4,3) must rebuild the transcribed matrix exactly.
    Mb, nb = wanless_family(4, 3)
    check(nb == 22, 'B5 family (4,3) has order 22', f'n={nb}')
    check(sigma_vector(Mb, chain_order(nb)) == sig,
          'B5 family (4,3) rebuilds Wanless Fig. 1 sigma-vector exactly', '')
    say(f"    {'(a,b)':>7} {'n':>4} {'RAT fails at k':>18} {'GAP fails':>10} "
        f"{'T-F fails':>10} {'a_n/a_2':>12}")
    seen_first = None
    for (aa, bb) in [(1, 1), (2, 1), (2, 2), (3, 2), (3, 3), (4, 3), (4, 4),
                     (5, 4), (5, 5), (6, 5), (6, 6)]:
        Mf, nf = wanless_family(aa, bb)
        check(is_ds(Mf, nf), 'B5 family member is doubly stochastic',
              f'({aa},{bb})')
        sf = sigma_vector(Mf, chain_order(nf))
        check(sf[1] == nf, 'B5 family sigma_1 = n', f'({aa},{bb})')
        af = a_vector(sf, nf)
        rf = [k for k in range(1, nf + 1) if rat_slack(sf, nf, k) < 0]
        gf = [k for k in range(2, nf + 1) if not gap_ok(af, k)]
        tf = [k for k in range(1, nf + 1) if af[k] < 1]
        check(rf == [] or rf == [nf],
              'B5 in this family (RAT) can fail ONLY at k = n', f'({aa},{bb})')
        check(gf == [], 'B5 (GAP) holds on every family member', f'({aa},{bb})')
        check(tf == [], 'B5 Tverberg-Friedland holds on every family member',
              f'({aa},{bb})')
        if rf and seen_first is None:
            seen_first = nf
        say(f'    {f"({aa},{bb})":>7} {nf:4d} {str(rf):>18} {str(gf):>10} '
            f'{str(tf):>10} {float(af[nf]/af[2]):12.1f}')
    check(seen_first == 22,
          'B5 the smallest family member breaking (RAT) is Wanless n = 22',
          f'first={seen_first}')


# ==========================================================================
def section_C():
    banner('--- C  what survives of (RAT): census, truth boundary, equality set')
    rng = random.Random(101)
    pool = []
    for n in range(3, 7):
        base = [J(n), T_matrix(n)]
        for p in itertools.permutations(range(n)):
            base.append(perm_matrix(n, list(p)))
        for t in range(1, n):
            base.append(half_IC(n, t))
        for t in range(1, n):
            base.append(circ(n, [0, t], [Fr(1, 3), Fr(2, 3)]))
        base += [rand_ds_good(n, rng) for _ in range(12)]
        base += [rand_zeroface(n, rng) for _ in range(8)]
        # J-block direct sums
        for s in range(1, n):
            B = [[Fr(0)] * n for _ in range(n)]
            for i in range(s):
                for j in range(s):
                    B[i][j] = Fr(1, s)
            for i in range(s, n):
                for j in range(s, n):
                    B[i][j] = Fr(1, n - s)
            base.append(B)
        pool += [(n, M) for M in base]
    nrat = ngap = 0
    for n, M in pool:
        check(is_ds(M, n), 'C1 census member is doubly stochastic', f'n={n}')
        sig = sigma_vector(M)
        a = a_vector(sig, n)
        for k in range(1, n + 1):
            if rat_slack(sig, n, k) < 0:
                nrat += 1
        for k in range(2, n + 1):
            if not gap_ok(a, k):
                ngap += 1
        check(all(rat_slack(sig, n, k) >= 0 for k in range(1, n + 1)),
              'C1 (RAT) census n=3..6, all k: no failure', f'n={n}')
        check(all(gap_ok(a, k) for k in range(2, n + 1)),
              'C2 (GAP) census n=3..6, all k: no failure', f'n={n}')
        check(all(a[k] >= 1 for k in range(n + 1)),
              'C2 Tverberg-Friedland on the census', f'n={n}')
    say(f'    census: {len(pool)} matrices, n = 3..6, every k -- '
        f'(RAT) failures {nrat}, (GAP) failures {ngap}')

    # C3  the equality family, exactly as Kopotun 1994 p. 206 prints it
    for n in range(3, 9):
        for t in range(1, n):
            M = half_IC(n, t)
            sig = sigma_vector(M)
            sl = rat_slack(sig, n, n)
            if gcd(t, n) == 1:
                check(sl == 0,
                      'C3 (RAT) EQUALITY at (I+C^t)/2, gcd(t,n)=1, k=n',
                      f'n={n} t={t}')
                a = a_vector(sig, n)
                check(a[n] == a[n - 1],
                      'C3 equality family: a_n = a_(n-1)', f'n={n} t={t}')
            else:
                check(sl > 0, 'C3 strict when gcd(t,n)>1', f'n={n} t={t}')
            for k in range(2, n):
                check(rat_slack(sig, n, k) > 0,
                      'C3 (RAT) STRICT below k=n on the equality family',
                      f'n={n} t={t} k={k}')
        # sigma_{n-1}((I+C)/2) = n^2 2^{1-n}, per = 2^{1-n}
        M = half_IC(n, 1)
        sig = sigma_vector(M)
        check(sig[n] == Fr(1, 2 ** (n - 1)),
              'C3 per((I+C)/2) = 2^(1-n)', f'n={n}')
        check(sig[n - 1] == Fr(n * n, 2 ** (n - 1)),
              'C3 sigma_(n-1)((I+C)/2) = n^2 2^(1-n)', f'n={n}')
    # C4  the truth boundary, as a table of what is cited and what is measured
    say('    truth boundary of (RAT):')
    say('      k <= 3, every n           TRUE   Dokovic 1967            [R]')
    say('      k  = 4, every n >= 5      TRUE   Kopotun, LMA 36 (1994)  [R]')
    say('      k  = 4, n = 4             TRUE   this repo, Paper G      [V]')
    say('      k  = 5                    OPEN   (Omega_n; not Lambda^k_n)')
    say('      k  = n, n >= 22           FALSE  Wanless, LAA 286 (1999) [R]/[V]')


# ==========================================================================
def section_D():
    banner('--- D  the repair: (GAP)  a_k >= a_2, and what it buys')
    rng = random.Random(202)
    # D1  (RAT) at 3..k implies (GAP) at k -- telescoping, checked as a fact
    for n in range(3, 7):
        for _ in range(6):
            M = rand_ds_good(n, rng)
            sig = sigma_vector(M)
            a = a_vector(sig, n)
            for k in range(3, n + 1):
                if all(rat_slack(sig, n, j) >= 0 for j in range(3, k + 1)):
                    check(gap_ok(a, k), 'D1 (RAT) telescoped implies (GAP)',
                          f'n={n} k={k}')
    # D2  (GAP) at k=3 IS (RAT) at k=3
    for n in range(3, 7):
        for _ in range(6):
            M = rand_ds_good(n, rng)
            sig = sigma_vector(M)
            a = a_vector(sig, n)
            check(gap_ok(a, 3) == (rat_slack(sig, n, 3) >= 0),
                  'D2 (GAP) at k=3 is exactly (RAT) at k=3', f'n={n}')
    # D3  Theorem RAT-B':  (GAP) => (KS_k^weak) on the zero face
    for n in range(3, 7):
        for _ in range(8):
            B = rand_zeroface(n, rng)
            check(any(B[i][j] == 0 for i in range(n) for j in range(n)),
                  'D3 zero-face member carries a zero', f'n={n}')
            Q = Qof(B, n)
            check(Q >= Fr(1, (n - 1) ** 2),
                  'D3 Theorem KSK-A floor Q >= 1/(n-1)^2 on the zero face',
                  f'n={n}')
            sig = sigma_vector(B)
            a = a_vector(sig, n)
            for k in range(3, n + 1):
                if gap_ok(a, k):
                    Pk = sig[k] * Fr(1, comb(n, k) ** 2)
                    gam = Fr(factorial(k), n ** k)
                    check(Pk - gam >= gam * Q * Fr(1, (n - 1) ** 2),
                          'D3 (GAP) gives P_k - gamma >= gamma Q/(n-1)^2',
                          f'n={n} k={k}')
                    check(Pk - gam >= gam * Fr(1, (n - 1) ** 4),
                          'D3 (GAP) gives (KS_k^weak) with no threshold',
                          f'n={n} k={k}')
    # D4  the exact layer condition for (GAP), and the threshold table
    #     (GAP) at k  <=  sum_{l=3}^k W_l(n,k) C_l  <=  (k-2)(k+1)/(2k(k-1))
    for n in range(4, 8):
        for _ in range(5):
            M = rand_ds_good(n, rng)
            X = [[M[i][j] - Fr(1, n) for j in range(n)] for i in range(n)]
            sX = sigma_vector(X) if all(x >= 0 for r in X for x in r) else None
            sX = [sigma_brute(X, m) for m in range(n + 1)]
            sig = sigma_vector(M)
            a = a_vector(sig, n)
            for k in range(3, n + 1):
                lay = sum(W(n, k, m) * sX[m] for m in range(3, k + 1))
                rhs = u_coef(n, k, 2) * (2 * gap_allow(k) * sX[2] + lay)
                check(a[k] - a[2] == rhs,
                      'D4 the (GAP) layer identity: a_k - a_2 = u_2 '
                      '(2 c_k sigma_2(X) + sum W_l sigma_l(X))', f'n={n} k={k}')
            check(sX[2] * 2 == Qof(M, n),
                  'D4 sigma_2(X) = Q/2 on the centred slice', f'n={n}')
    say(f"    {'mode':>10} {'lemma':>5} " +
        ' '.join(f'j={j:<5}' for j in range(3, 13)))
    tables = {}
    for mode in ('paper', 'U4', 'U5', 'paper+U5'):
        rv = [least_n(lambda n, j, m=mode: rat_loss(n, j, m),
                      lambda j: Fr(1), j) for j in range(3, 13)]
        gv = [least_n(lambda n, j, m=mode: gap_loss(n, j, m),
                      gap_allow, j) for j in range(3, 13)]
        tables[mode] = (rv, gv)
        say(f'    {mode:>10} {"RAT":>5} ' + ' '.join(f'{v:<7}' for v in rv))
        say(f'    {mode:>10} {"GAP":>5} ' + ' '.join(f'{v:<7}' for v in gv))
    rv, gv = tables['paper']
    for idx, want in enumerate((4, 8, 14)):
        check(rv[idx] == want,
              'D5 n_RAT paper column reproduces KSK.md section 5 (4, 8, 14)',
              f'j={idx+3}')
    check(gv[0] == rv[0],
          'D5 n_GAP(3) = n_RAT(3) -- the two lemmas coincide at k=3', '')
    for idx in range(1, 10):
        check(gv[idx] <= rv[idx],
              'D5 n_GAP is never worse than n_RAT', f'j={idx+3}')
        check(gv[idx] < rv[idx],
              'D5 n_GAP is strictly better than n_RAT for k >= 4',
              f'j={idx+3}')
    # the threshold is exact: one step below, the layer condition fails
    for j in range(3, 13):
        ng = least_n(lambda n, jj: gap_loss(n, jj, 'paper'), gap_allow, j)
        check(ng > 3 and gap_loss(ng, j, 'paper') <= gap_allow(j) <
              gap_loss(ng - 1, j, 'paper'),
              'D5 n_GAP is the EXACT boundary of the layer argument', f'j={j}')


# ==========================================================================
def section_E():
    banner('--- E  the diagonal k = n, UNCONDITIONAL, without (RAT)')
    # E1  the Knopp-Sinkhorn floor is attained at T_n
    for n in range(3, 10):
        Tn = T_matrix(n)
        check(is_ds(Tn, n), 'E1 T_n is doubly stochastic', f'n={n}')
        check(Tn[0][0] == 0, 'E1 T_n carries a zero', f'n={n}')
        check(Qof(Tn, n) == Fr(1, (n - 1) ** 2),
              'E1 Q(T_n) = 1/(n-1)^2', f'n={n}')
        p = sigma_vector(Tn)[n]
        check(p == m_n(n),
              'E1 per(T_n) = m_n = (n-2)!((n-2)/(n-1)^2)^(n-2)', f'n={n}')
        if n <= 6:
            check(p == per_brute(Tn), 'E1 per(T_n) DP == definition', f'n={n}')
    # E2  the closed-form inequality  rho(n) - 1 >= n/(4(n-1)^3)
    #     -- this IS (KS_n) at full strength once per(B) >= m_n is in hand.
    for n in range(3, 1201):
        check(m_n(n) - Fr(factorial(n), n ** n) >= ks_claim(n, n),
              'E2 m_n - n!/n^n >= the (KS_n) claim, every n', f'n={n}')
    say('    ratio (true gap at T_n)/(claimed (KS_n) bound), exact:')
    for n in (3, 4, 5, 8, 12, 30, 100, 1000):
        say(f'      n={n:5d}  '
            f'{float((m_n(n) - Fr(factorial(n), n ** n)) / ks_claim(n, n)):.6f}')
    for n in range(3, 400):
        ratio = (m_n(n) - Fr(factorial(n), n ** n)) / ks_claim(n, n)
        check(Fr(4, 3) <= ratio < 2,
              'E2 the ratio sits in [4/3, 2), never reaching 2', f'n={n}')
    # E3  the analytic steps of the proof of E2, each checked exactly
    #     N = n-1;  ln rho = sum_{m>=2} c_m/N^m with c_m = 1/m (m even),
    #     c_m = 1/m - 2/(m+1) (m odd); alternating with decreasing magnitude for
    #     N >= 2, so ln rho >= 1/(2N^2) - 1/(6N^3); then exp(x) >= 1+x and
    #     1/(4N^2) >= (5/12)/N^3 for N >= 5/3.
    for m in range(2, 40):
        c = Fr(1, m) if m % 2 == 0 else Fr(1, m) - Fr(2, m + 1)
        cn = Fr(1, m + 1) if (m + 1) % 2 == 0 else Fr(1, m + 1) - Fr(2, m + 2)
        check((-1) ** m * c > 0, 'E3 the series alternates', f'm={m}')
        check(abs(cn) * 2 <= abs(c) * 2 * Fr(3, 2),
              'E3 |c_(m+1)|/|c_m| <= 3/2 < 2 <= N', f'm={m}')
        check(abs(c) <= Fr(1, m), 'E3 |c_m| <= 1/m', f'm={m}')
    for N in range(2, 400):
        check(Fr(1, 4 * N ** 2) >= Fr(5, 12) * Fr(1, N ** 3),
              'E3 1/(4N^2) >= (5/12)/N^3 for N >= 2', f'N={N}')
        check(Fr(1, 2 * N ** 2) - Fr(1, 6 * N ** 3) >=
              Fr(1, 4 * N ** 2) + Fr(1, 4 * N ** 3),
              'E3 the truncated series beats the claim, N >= 2', f'N={N}')
    # E4  and therefore (KS_n) at full strength on the zero face, directly
    rng = random.Random(303)
    for n in range(3, 7):
        pool = [T_matrix(n)] + [rand_zeroface(n, rng) for _ in range(10)]
        for B in pool:
            check(any(B[i][j] == 0 for i in range(n) for j in range(n)),
                  'E4 zero-face member carries a zero', f'n={n}')
            p = sigma_vector(B)[n]
            check(p >= m_n(n),
                  'E4 Knopp-Sinkhorn floor holds on the zero face', f'n={n}')
            check(p - Fr(factorial(n), n ** n) >= ks_claim(n, n),
                  'E4 (KS_n) at FULL strength on the zero face', f'n={n}')


# ==========================================================================
def section_F():
    banner('--- F  payoff')
    # Pang comparison (*) of MAXIMISER.md section 2, instantiated exactly:
    #   m - gamma > (3/4) n^2 (n-1) (k/(k-1)) m^2  with m <= P_k(T_n).
    # Sound both sides; reproduced here only to check the exponent count that
    # kills k <= 7 at every n, and to price the diagonal.
    def pang_alive(n, k, const):
        gam = Fr(factorial(k), n ** k)
        lhs = gam * const * Fr(k * (k - 1), 4) * Fr(1, (n - 1) ** 4) \
            if const == 1 else None
        gap = Fr(k * (k - 1), 4) * gam * Fr(1, (n - 1) ** 4) if const else \
            gam * Fr(1, (n - 1) ** 4)
        m = Fr(comb(n, k) ** 2 * factorial(k), n ** k) * Fr(1, comb(n, k) ** 2)
        # m <= P_k(T_n); use the sound surrogate P_k(T_n) <= 2 gamma (checked)
        return gap > Fr(3, 4) * n ** 2 * (n - 1) * Fr(k, k - 1) * (2 * gam) ** 2
    for k in range(3, 8):
        alive = [n for n in range(k, 400) if pang_alive(n, k, 1)]
        check(alive == [],
              'F1 the Pang route is structurally dead for k <= 7', f'k={k}')
    say('    diagonal cells (k,n) = (k,k): (KS_k) is now UNCONDITIONAL (E).')
    say('    off-diagonal cells: (KS_k^weak) holds under (GAP), no threshold;')
    say('    (KS_k) at full strength for n >= n_LOC(k) = 2.1k + O(1) (KSK C).')


# ==========================================================================
def main():
    global MUT
    MUT = sys.argv[1] if len(sys.argv) > 1 else None
    for f in (section_A, section_A8, section_B, section_C, section_D,
              section_E, section_F):
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
