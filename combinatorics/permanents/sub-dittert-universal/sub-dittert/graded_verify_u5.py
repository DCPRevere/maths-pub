#!/usr/bin/env python3
"""Graded verifier for U5.md -- the connected-graph bound.

Exact Fraction arithmetic throughout; no floating point in any decision
(floats appear only inside format strings).

Sections
  V1  the pattern machinery: connected patterns G(pi,rho), the connected
      l^1 Moebius mass Lam_e against ODDLAYER/EVENLAYER, the mass identity
  V2  the toolkit, lemma by lemma, at exact doubly stochastic witnesses:
      T0 D-closure, T1 entry/row/operator facts, T2 Hadamard, T3 diagonal,
      T4 propagation, T6 vanishing
  V3  the certificate calculus: every connected pattern with e <= 7 is
      certified; the residue at e = 8, 9 is exactly the min-degree-3 cores
  V4  U5 itself: |S_G(B)| <= Q at every witness, every pattern e <= 6,
      with membership in Omega_n asserted EXACTLY for every witness;
      the permutation matrix, the (I + C^t)/2 circulants, block families
  V5  THE SEPARATION: U5 is FALSE for doubly centred z with ||z||_op <= 1;
      the exact family, its exact spectrum, and the rate
  V6  recomposition: Ntilde(k) with (S4) PROVED for e <= 7 and the Finner
      rate above, against EVENLAYER's conditional table
  V7  mutation controls

Run:  GUARD_MEM=4G GUARD_CPUS=200% ../guard.sh python3 -u graded_verify_u5.py
"""
import sys
import os
from fractions import Fraction as Fr
from math import factorial

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from collar_budget import Ntilde, Q_cap, eta, t_coef                # noqa: E402
import graded_verify_evenlayer as EL                                # noqa: E402
import graded_verify_oddlayer as OL                                 # noqa: E402
import u5_hunt as HU                                                # noqa: E402
import u5_reduce as RD                                              # noqa: E402

PASS = FAIL = 0
FIRED = []
MUT = {}


def log(s=""):
    print(s, flush=True)


def check(name, ok, detail=""):
    global PASS, FAIL
    if ok:
        PASS += 1
    else:
        FAIL += 1
        FIRED.append(name)
    log(f"  [{'ok ' if ok else 'FAIL'}] {name}" + (f"   {detail}" if detail else ""))
    return ok


# ==================================================== exact matrix utilities

def mat_mul(X, Y):
    n = len(X)
    return [[sum(X[i][t] * Y[t][j] for t in range(n)) for j in range(n)]
            for i in range(n)]


def transpose(X):
    return [list(r) for r in zip(*X)]


def is_doubly_stochastic(A):
    n = len(A)
    if any(len(r) != n for r in A):
        return False
    if any(x < 0 for r in A for x in r):
        return False
    if any(sum(r) != 1 for r in A):
        return False
    return all(sum(A[i][j] for i in range(n)) == 1 for j in range(n))


def centred(B):
    n = len(B)
    return (all(sum(r) == 0 for r in B)
            and all(sum(B[i][j] for i in range(n)) == 0 for j in range(n)))


def B_of(A):
    n = len(A)
    return [[A[i][j] - Fr(1, n) for j in range(n)] for i in range(n)]


def frob2(X):
    return sum(x * x for r in X for x in r)


def ldl_psd(M):
    """Exact PSD test for a symmetric rational matrix, by LDL^T with symmetric
    pivoting.  Returns True iff M is positive semidefinite."""
    n = len(M)
    A = [row[:] for row in M]
    idx = list(range(n))
    for k in range(n):
        p = max(range(k, n), key=lambda i: A[i][i])
        if A[p][p] < 0:
            return False
        if A[p][p] == 0:
            # the whole remaining block must vanish
            for i in range(k, n):
                for j in range(k, n):
                    if A[i][j] != 0:
                        return False
            return True
        if p != k:
            A[k], A[p] = A[p], A[k]
            for r in A:
                r[k], r[p] = r[p], r[k]
            idx[k], idx[p] = idx[p], idx[k]
        d = A[k][k]
        for i in range(k + 1, n):
            f = A[i][k] / d
            if f == 0:
                continue
            for j in range(k, n):
                A[i][j] -= f * A[k][j]
    return True


def op_le_one(B):
    """||B||_op <= 1, exactly:  I - B^T B is PSD."""
    n = len(B)
    G = mat_mul(transpose(B), B)
    M = [[(Fr(1) if i == j else Fr(0)) - G[i][j] for j in range(n)]
         for i in range(n)]
    return ldl_psd(M)


# ==================================================== exact witnesses in Omega_n

def perm_matrix(n, sigma=None):
    sigma = sigma or list(range(n))
    return [[Fr(1) if sigma[i] == j else Fr(0) for j in range(n)]
            for i in range(n)]


def circ_half(n, t):
    """(I + C^t)/2 -- the mandatory circulant witnesses."""
    return [[Fr(1, 2) if (j == i or j == (i + t) % n) else Fr(0)
             for j in range(n)] for i in range(n)]


def block_family(n, m):
    """I_m  (+)  J_{n-m}/(n-m)."""
    A = [[Fr(0)] * n for _ in range(n)]
    for i in range(m):
        A[i][i] = Fr(1)
    r = n - m
    for i in range(m, n):
        for j in range(m, n):
            A[i][j] = Fr(1, r)
    return A


def anti_perm(n):
    """(J - P)/(n-1): ODDLAYER's other extremal family."""
    return [[Fr(0) if i == j else Fr(1, n - 1) for j in range(n)]
            for i in range(n)]


def mixed(n):
    """A rational interior point: a convex combination of three permutations."""
    P0 = perm_matrix(n)
    P1 = perm_matrix(n, [(i + 1) % n for i in range(n)])
    P2 = perm_matrix(n, [(2 * i + 3) % n for i in range(n)]) \
        if n % 2 else perm_matrix(n, [(i + 2) % n for i in range(n)])
    w = (Fr(1, 2), Fr(1, 3), Fr(1, 6))
    return [[w[0] * P0[i][j] + w[1] * P1[i][j] + w[2] * P2[i][j]
             for j in range(n)] for i in range(n)]


def saturated(n):
    """A doubly stochastic point with a zero entry and unequal row profiles."""
    A = [[Fr(0)] * n for _ in range(n)]
    for i in range(n):
        for j in range(n):
            A[i][j] = Fr(1, n)
    A[0][0] -= Fr(1, n)
    A[0][1] += Fr(1, n)
    A[1][1] -= Fr(1, n)
    A[1][0] += Fr(1, n)
    return A


def witnesses(n):
    out = [("perm I", perm_matrix(n)),
           ("perm shift", perm_matrix(n, [(i + 1) % n for i in range(n)])),
           ("circ (I+C)/2", circ_half(n, 1)),
           ("circ (I+C^2)/2", circ_half(n, 2)),
           ("anti-perm", anti_perm(n)),
           ("mixed", mixed(n)),
           ("saturated", saturated(n))]
    for m in (1, 2, n - 2):
        if 1 <= m <= n - 2:
            out.append((f"block I_{m}+J/{n-m}", block_family(n, m)))
    return out


# ==================================================== pattern evaluation

def S_exact(c, B, n):
    """S_G(B) exactly, for the incidence matrix c (rows x cols)."""
    U, V = len(c), len(c[0])
    tot = Fr(0)
    idx = [0] * U
    while True:
        term = Fr(1)
        for v in range(V):
            s = Fr(0)
            for j in range(n):
                p = Fr(1)
                for u in range(U):
                    if c[u][v]:
                        p *= B[idx[u]][j] ** c[u][v]
                s += p
            term *= s
            if term == 0:
                break
        tot += term
        t = U - 1
        while t >= 0:
            idx[t] += 1
            if idx[t] < n:
                break
            idx[t] = 0
            t -= 1
        if t < 0:
            return tot


PATCACHE = {}


def pats(e):
    if e not in PATCACHE:
        PATCACHE[e] = HU.patterns(e)
    return PATCACHE[e]


# ============================================================== V1

def V1():
    log("\nV1  pattern machinery and the connected mass Lam_e")
    tab = {2: 1, 3: 4, 4: 78, 5: 1896, 6: 68880, 7: 3386160}
    for e in range(2, 8):
        m = sum(b for _, b in pats(e).values())
        check(f"Lam_{e} = sum |mu mu| over connected pairs = {tab[e]}",
              m == tab[e], f"got {m}")
    for e in range(2, 8):
        check(f"Lam_{e} agrees with EVENLAYER's log-EGF table",
              Fr(sum(b for _, b in pats(e).values())) == EL.Lam(e))
    counts = {2: 1, 3: 1, 4: 4, 5: 5, 6: 21, 7: 37}
    for e in range(2, 8):
        check(f"e = {e}: {counts[e]} connected iso classes",
              len(pats(e)) == counts[e], f"got {len(pats(e))}")
    # every pattern really has all degrees >= 2 and is connected
    okall = True
    for e in range(2, 8):
        for key in pats(e):
            c = [list(r) for r in key]
            rd = [sum(r) for r in c]
            cd = [sum(r[v] for r in c) for v in range(len(c[0]))]
            if min(rd + cd) < 2 or not HU.is_connected(c) or sum(rd) != e:
                okall = False
    check("every enumerated pattern: connected, e edges, min degree >= 2", okall)


# ============================================================== V2

def V2():
    log("\nV2  the toolkit, at exact doubly stochastic witnesses")
    for n in (5, 6):
        for name, A in witnesses(n):
            beta = Fr(n - 1, n)
            check(f"n={n} {name}: A in Omega_n (exact)", is_doubly_stochastic(A))
            B = B_of(A)
            Q = frob2(B)
            check(f"n={n} {name}: B doubly centred", centred(B))
            # T1(b) entry bound, T1(d) row/col square bound
            check(f"n={n} {name}: T1b max|b_ij| <= beta",
                  max(abs(x) for r in B for x in r) <= beta)
            check(f"n={n} {name}: T1d row and column squares <= beta",
                  max(max(sum(x * x for x in r) for r in B),
                      max(sum(B[i][j] ** 2 for i in range(n)) for j in range(n)))
                  <= beta)
            # T1(c) positive/negative row split
            sp = max(max(sum(x for x in r if x > 0) for r in B),
                     max(sum(-x for x in r if x < 0) for r in B))
            check(f"n={n} {name}: T1c row +/- split <= beta", sp <= beta)
            # T1(e) operator norm
            check(f"n={n} {name}: T1e ||B||_op <= 1 (exact PSD test)",
                  op_le_one(B))
            # T0 closure: B B^T = A A^T - J/n with A A^T doubly stochastic
            AAt = mat_mul(A, transpose(A))
            BBt = mat_mul(B, transpose(B))
            check(f"n={n} {name}: T0 B B^T = A A^T - J/n, A A^T in Omega_n",
                  is_doubly_stochastic(AAt)
                  and all(BBt[i][j] == AAt[i][j] - Fr(1, n)
                          for i in range(n) for j in range(n)))
            # T2 Hadamard
            H2 = [[B[i][j] ** 2 for j in range(n)] for i in range(n)]
            check(f"n={n} {name}: T2 sum|B o B| = Q",
                  sum(x for r in H2 for x in r) == Q)
            check(f"n={n} {name}: T2 max_a sum_b |B o B| <= beta",
                  max(sum(r) for r in H2) <= beta)
            # T3 diagonal: sum_a |(B B^T)_aa| = Q and each <= 1
            check(f"n={n} {name}: T3 tr(B B^T) = Q, diag >= 0, diag <= 1",
                  sum(BBt[i][i] for i in range(n)) == Q
                  and all(BBt[i][i] >= 0 and BBt[i][i] <= 1 for i in range(n)))
            # T3 for the 4-cycle: tr((BB^T)^2) <= Q
            B4 = mat_mul(BBt, BBt)
            check(f"n={n} {name}: T3 tr((BB^T)^2) <= Q",
                  sum(B4[i][i] for i in range(n)) <= Q)
            # T4 propagation with a non-negative weight
            om = [BBt[i][i] for i in range(n)]          # >= 0, <= 1, l1 = Q
            h = [sum(om[i] * B[i][j] for i in range(n)) for j in range(n)]
            check(f"n={n} {name}: T4 ||B^T om||_inf <= beta ||om||_inf",
                  max(abs(x) for x in h) <= beta * max(om))
            # T4 through a Hadamard edge, trivial weight
            hh = [sum(H2[i][j] for i in range(n)) for j in range(n)]
            check(f"n={n} {name}: T4 (B o B)^T 1 is heavy and non-negative",
                  sum(hh) == Q and min(hh) >= 0 and max(hh) <= beta)
            # T6 vanishing
            check(f"n={n} {name}: T6 zero column sums",
                  all(sum(B[i][j] for i in range(n)) == 0 for j in range(n)))


# ============================================================== V3

def V3():
    log("\nV3  the certificate calculus")
    tot = 0
    for e in range(2, 9):
        bad = []
        for key in pats(e):
            c = [list(r) for r in key]
            E, V = RD.pattern_state(c)
            if RD.certify(E, V) is None:
                bad.append(key)
            else:
                tot += 1
        check(f"e = {e}: every connected pattern is certified "
              f"({len(pats(e))} classes)", not bad,
              f"uncertified: {bad[:4]}")
    check(f"e <= 8: all {tot} classes certified, so U5 holds with constant 1",
          tot == 196, f"{tot}")
    # the residue: the first uncertified patterns are the min-degree-3 cores
    K4core = [[1, 1, 1], [1, 1, 1], [1, 1, 0]]          # e = 8
    K33 = [[1, 1, 1], [1, 1, 1], [1, 1, 1]]             # e = 9
    for nm, c in (("K4-core (e=8)", K4core), ("K33 (e=9)", K33)):
        E, V = RD.pattern_state(c)
        cert = RD.certify(E, V)
        check(f"{nm}: the LOCAL moves alone do not reach it",
              RD.certify(*RD.pattern_state(c)) is not None
              and cert[-1].startswith("L-"),
              f"closed by {cert[-1][:12] if cert else None}")
        # the named lemmas now include the CORE-level terminals of
        # U5-CORES.md (L-WHEEL subsumes L-K4, L-CS2 subsumes L-K33), so the
        # control has to switch off the whole set, not just one member --
        # a control that leaves a synonym enabled is not a control.
        RD.DISABLE.add("L-K4")
        RD.DISABLE.add("L-K33")
        for _nm in RD.CORE_LEMMAS:
            RD.DISABLE.add(_nm)
        check(f"{nm}: without the named lemmas it is NOT certified",
              RD.certify(*RD.pattern_state(c)) is None)
        RD.DISABLE.clear()
    # ... and everything the calculus does reach, it reaches for a reason:
    # a pattern with a degree-1 vertex must NOT be certified as <= Q by M9
    # unless the edge is a D edge; check the tree-of-cycles family instead
    spider = [[2, 0, 0, 1], [0, 2, 0, 1], [0, 0, 2, 1]]      # e = 9
    dumb = [[1, 1, 0, 0], [1, 1, 1, 0], [0, 0, 1, 1], [0, 0, 1, 1]]  # e = 9
    for nm, c in (("spider3 (e=9)", spider), ("dumbbell (e=9)", dumb)):
        E, V = RD.pattern_state(c)
        check(f"beyond e=7: {nm} (a tree of cycles) is certified",
              RD.certify(E, V) is not None)


# ============================================================== V4

def V4():
    log("\nV4  U5 at the witnesses, exactly:  |S_G(B)| <= Q")
    worst = (Fr(0), None)
    for n in (5, 6):
        for name, A in witnesses(n):
            assert is_doubly_stochastic(A), name
            B = B_of(A)
            Q = frob2(B)
            if Q == 0:
                continue
            bad = []
            for e in range(2, 7):
                for key in pats(e):
                    c = [list(r) for r in key]
                    S = S_exact(c, B, n)
                    if MUT.get("half_constant"):
                        okk = abs(S) <= Q / 2
                    else:
                        okk = abs(S) <= Q
                    if not okk:
                        bad.append((e, key, S, Q))
                    if abs(S) * worst[0].denominator > worst[0].numerator * Q:
                        worst = (Fr(abs(S), Q), (n, name, e, key))
            check(f"n={n} {name}: |S_G| <= Q for all patterns e <= 6",
                  not bad, f"{bad[:2]}")
    log(f"      worst ratio |S_G|/Q over the witness set: "
        f"{float(worst[0]):.8f} at {worst[1]}")
    check("the worst observed ratio is exactly 1 (attained, by a cycle)",
          worst[0] == 1, f"{worst[0]}")
    # the permutation matrix in closed form: S_G(P - J/n) <= n - 1 at every
    # pattern and every n on a grid -- the known killer point
    bad = []
    for e in range(2, 8):
        for key in pats(e):
            c = [list(r) for r in key]
            for n in (5, 8, 20, 60, 200):
                S = HU.S_perm_closed(c, n)
                if abs(S) > n - 1:
                    bad.append((e, key, n, S))
    check("permutation matrix, closed form: |S_G| <= Q = n-1 at every "
          "pattern e <= 7 and n in {5,8,20,60,200}", not bad, f"{bad[:2]}")
    # and it is attained exactly by the even cycles
    c4 = [[1, 1], [1, 1]]
    check("the 4-cycle attains it: S = n-1 exactly at P - J/n",
          all(HU.S_perm_closed(c4, n) == n - 1 for n in (5, 8, 20, 60)))


# ============================================================== V5

def V5():
    log("\nV5  THE SEPARATION: U5 fails for doubly centred z with ||z||_op <= 1")

    def family(m, M, s, t):
        s, t = Fr(s), Fr(t)
        u = -(s + t)
        r_h = s * s + t * t + u * u
        k = m * s * s + t * t + u * u
        r_l = Fr(m * m * s * s + m * (t * t + u * u), M * M)
        Q = m * r_h + M * r_l
        D = r_h - r_l
        S = D ** 3 * m * (m * m * s ** 3 + t ** 3 + u ** 3)
        a11 = r_h - s * s + m * s * s
        a22 = M * r_l
        a12sq = Fr(k, M) ** 2 * m * M
        return Q, S, (a11, a22, a12sq), r_h - s * s

    def build(m, M, s, t):
        """The explicit (m+M) x (m+M) doubly centred matrix, for small sizes."""
        s, t = Fr(s), Fr(t)
        u = -(s + t)
        n = m + M
        ncols = 1 + 2 * m
        assert ncols <= n
        Z = [[Fr(0)] * n for _ in range(n)]
        for w in range(m):
            Z[w][0] = s
            Z[w][1 + 2 * w] = t
            Z[w][2 + 2 * w] = u
        for l in range(m, n):
            Z[l][0] = Fr(-m * s, M)
            for w in range(m):
                Z[l][1 + 2 * w] = Fr(-t, M)
                Z[l][2 + 2 * w] = Fr(-u, M)
        return Z

    # the closed forms, validated against the explicit matrix at small size
    for (m, M) in ((2, 6), (3, 10)):
        s, t = Fr(1, 3), Fr(7, 10)
        Z = build(m, M, s, t)
        check(f"m={m},M={M}: the explicit z is doubly centred", centred(Z))
        Q, S, g, rest = family(m, M, s, t)
        check(f"m={m},M={M}: closed-form Q matches ||z||_F^2",
              Q == frob2(Z), f"{Q} vs {frob2(Z)}")
        c = [[2, 0, 0, 1], [0, 2, 0, 1], [0, 0, 2, 1]]      # SPIDER3, e = 9
        Sx = S_exact(c, Z, m + M)
        check(f"m={m},M={M}: closed-form S matches S_SPIDER3(z)",
              S == Sx, f"{S} vs {Sx}")
        # spectrum: the Gram matrix's eigenvalues are the two roots of the
        # 2x2 block, plus (r_h - s^2) with multiplicity m-1, plus 0
        a11, a22, a12sq = g
        lam_hi_bound = a11 + a22          # a rational upper bound for the top root
        G = mat_mul(Z, transpose(Z))
        Mx = [[(lam_hi_bound if i == j else Fr(0)) - G[i][j]
               for j in range(m + M)] for i in range(m + M)]
        check(f"m={m},M={M}: a11+a22 dominates the spectrum of z z^T (exact PSD)",
              ldl_psd(Mx))
    # the violation, at the scale where it bites
    log("      the rate:  S / (Q ||z||_op^7)  along the family")
    hits = 0
    for m in (64, 256, 1024, 4096, 16384):
        M = 8 * m + 8
        import math
        s = Fr(round(10 ** 9 / math.sqrt(m)), 10 ** 9)
        t = Fr(7, 10)
        Q, S, g, rest = family(m, M, s, t)
        a11, a22, a12sq = g
        lam = a11 + a22                     # >= the top eigenvalue of z z^T
        lam = max(lam, rest)
        lhs, rhs = S * S, Q * Q * lam ** 7
        ratio = float(lhs / rhs) ** 0.5 if rhs else 0.0
        if lhs > rhs:
            hits += 1
        log(f"      m = {m:6d}:  Q = {float(Q):12.3f}  S = {float(S):14.3f}  "
            f"tau^2 <= {float(lam):.4f}   S/(Q tau^7) = {ratio:.4f}")
    check("U5 with constant 1 FAILS for doubly centred z with ||z||_op <= 1, "
          "at >= 3 scales of the family", hits >= 3, f"{hits} of 5")
    # and the same family is NOT of the form A - J/n
    m, M = 3, 10
    Z = build(m, M, Fr(1, 3), Fr(7, 10))
    n = m + M
    A = [[Z[i][j] + Fr(1, n) for j in range(n)] for i in range(n)]
    check("the separating z is NOT A - J/n for any A in Omega_n "
          "(some entry of z is below -1/n)",
          not is_doubly_stochastic(A) and min(x for r in Z for x in r) < Fr(-1, n))


# ============================================================== V6

_MPCACHE = {}


def M_partial_top(maxm, e0):
    """M[j][c][D]: D = 2 * (sum of block Q-degrees), where a block of size
    e has Q-degree 1 for e <= e0  (U5, PROVED) and e/2 for e > e0
    (Finner/U3, the fallback)."""
    if (maxm, e0) in _MPCACHE:
        return _MPCACHE[(maxm, e0)]
    S = {}
    for e in range(3, maxm + 1):
        w = 2 if e <= e0 else e
        S[e] = (Fr(EL.Lam(e), factorial(e)), w)
    Mt = [[dict() for _ in range(maxm // 3 + 2)] for _ in range(maxm + 1)]
    Mt[0][0][0] = Fr(1)
    cur = {(0, 0): Fr(1)}
    for c in range(1, maxm // 3 + 1):
        nxt = {}
        for (a, D), v in cur.items():
            for e in range(3, maxm + 1 - a):
                lam, w = S[e]
                key = (a + e, D + w)
                nxt[key] = nxt.get(key, Fr(0)) + v * lam
        cur = {k: v / c for k, v in nxt.items()}
        for (j, D), v in cur.items():
            if v:
                Mt[j][c][D] = Mt[j][c].get(D, Fr(0)) + v
    _MPCACHE[(maxm, e0)] = Mt
    return Mt


def kappa_collar(n, k):
    """The per-edge collar degradation of the U5 toolkit.

    Every slice fact U5 consumes is an entry-bound or operator-norm fact, and
    each degrades by the SAME single scalar:
      row +/- split   sum_b (z_ab)_- <= sum_b delta_ab = 1 + n x_a <= 1 + eps
      entry bound     |z_ij| <= beta + Delta
      operator norm   ||z||_op <= sqrt((1+max R)(1+max C)) <= 1 + eps
    with eps = n * max_i |x_i| <= n * Delta, Delta = sqrt(2 u_max) the collar's
    own quantity (collar_budget.eta = 1/n + Delta).  A certificate on e edges
    uses at most one fact per edge, so it pays at most kappa^e with

        kappa(n,k) = (1 + eps) / beta,   eps = n * Delta.

    eps = n * sqrt(u_max) uses max_i |x_i| <= ||x||_2 <= sqrt(P) <= sqrt(u_max),
    which is what the row split actually needs -- Lemma M's
    Delta = sqrt(2 u_max) bounds max_ij |x_i + y_j| and is a factor sqrt(2)
    larger than required here.  Still conservative: not every edge of a
    certificate consumes an entry-bound fact."""
    import collar_budget as CB
    if MUT.get("no_kappa"):
        return Fr(1)                     # mutation: the eta cost dropped
    eps = n * CB.ceil_sqrt(CB.u_max(n, k))
    if MUT.get("kappa_delta"):
        eps = n * (CB.eta(n, k) - Fr(1, n))
    return (1 + eps) / Fr(n - 1, n)


def make_C(e0, collar_kappa):
    """sigma_m(z) >= -C_m Q with (S4) proved for e <= e0 and the Finner rate
    above it; collar_kappa switches the eta re-pricing on."""
    MT = M_partial_top(EL.MAXE, e0)

    def tiers_u5(m, et, kap):
        out = []
        j0 = 4 if m % 2 == 0 else 3
        for j in range(j0, m + 1, 2):
            s = (m - j) // 2
            pref = Fr(1, 2 ** s * factorial(s))
            for c in range(1, len(MT[j])):
                for D, v in MT[j][c].items():
                    if v == 0:
                        continue
                    pure3 = (j == 3 * c)
                    if pure3 and c % 2 == 0:
                        continue
                    if pure3:
                        v = Fr(2, 3) ** c / factorial(c) * et ** c
                    else:
                        v = v * kap ** j        # x -> kappa x in the tier GF
                    out.append((2 * s + D, pref * v))    # degree in HALF units
        return out

    def C_u5(m, n, k):
        """sigma_m(z) >= -C_m Q, with (S4) proved for e <= e0 and the Finner
        rate for the blocks above it.  Degrees are in half units, so a
        rational majorant of sqrt(Qhat) is used where they are odd."""
        Qc = Q_cap(n, k)
        et = eta(n, k)
        kap = kappa_collar(n, k) if collar_kappa else Fr(1)
        # rational majorant of sqrt(Qc)
        r = 1
        while (r + 1) ** 2 <= Qc:
            r += 1
        sq = (Qc + r * r) / (2 * r) if r else Fr(1)
        tot = Fr(0)
        for D2, cf in tiers_u5(m, et, kap):
            d2 = D2 - 2                       # degree - 1, in half units
            if d2 < 0:
                tot += cf / Qc if Qc else cf
            elif d2 % 2 == 0:
                tot += cf * Qc ** (d2 // 2)
            else:
                tot += cf * Qc ** (d2 // 2) * sq
        return tot

    return C_u5


def C_evenlayer(m, n, k):
    return EL.C_abs(m, n, k)


def V6():
    log("\nV6  recomposition on the slice: what e0 = 8 buys")
    E0 = MUT.get("e0", 8)
    C_u5 = make_C(E0, collar_kappa=False)
    log(f"      e0 = {E0}: blocks of size <= {E0} charged Q, above it Q^(e/2)")
    log("      k    Ntilde(U5-proved)   Ntilde(EVENLAYER, conditional)   floor")
    rows = []
    for k in range(6, 13):
        Nu = Ntilde(k, C_u5)
        Ne = Ntilde(k, C_evenlayer)
        fl = Ntilde(k, lambda m, n, kk: Fr(0))
        rows.append((k, Nu, Ne, fl))
        log(f"      {k:2d}   {str(Nu):>10s}          {str(Ne):>10s}"
            f"              {str(fl):>6s}")
    PROVED = {6: 35, 7: 43, 8: 52, 9: 324, 10: 627, 11: 1030, 12: 1544}
    for k, Nu, Ne, fl in rows:
        check(f"k = {k}: Ntilde under the PROVED (S4) is {PROVED[k]}",
              Nu == PROVED[k], f"got {Nu}")
        if k <= 8:
            check(f"k = {k} <= 8: the U5-proved threshold EQUALS "
                  f"EVENLAYER's conditional one", Nu == Ne, f"{Nu} vs {Ne}")
    if E0 == 8:
        check("k = 6, 7, 8 are UNCONDITIONAL at 35, 43, 52",
              (rows[0][1], rows[1][1], rows[2][1]) == (35, 43, 52),
              f"{rows[0][1]}, {rows[1][1]}, {rows[2][1]}")
    return rows


# ============================================================== V8

def V8():
    log("\nV8  the eta re-pricing: U5 consumes (F1), so the collar degrades it")
    E0 = MUT.get("e0", 8)
    C_slice = make_C(E0, collar_kappa=False)
    C_coll = make_C(E0, collar_kappa=True)
    log("      k    eps                kappa       kappa^8    "
        "Ntilde slice   Ntilde eta-priced")
    rows = []
    for k in range(5, 13):
        n0 = {5: 24, 6: 35, 7: 43, 8: 52, 9: 324, 10: 627, 11: 1030,
              12: 1544}.get(k, 50)
        kap = kappa_collar(n0, k)
        eps = kap * Fr(n0 - 1, n0) - 1
        Ns = Ntilde(k, C_slice)
        Nc = Ntilde(k, C_coll)
        rows.append((k, eps, kap, Ns, Nc))
        log(f"      {k:2d}   {float(eps):.6e}   {float(kap):.6f}   "
            f"{float(kap ** 8):.4f}     {str(Ns):>6s}         {str(Nc):>6s}")
    for k, eps, kap, Ns, Nc in rows:
        check(f"k = {k}: kappa > 1, so the eta re-pricing is a real cost",
              kap > 1)
        check(f"k = {k}: the eta-priced threshold is finite and >= the slice one",
              Nc is not None and Nc >= Ns, f"{Nc} vs {Ns}")
    # the headline: does the table move?
    PRICED = {k: Nc for k, _, _, _, Nc in rows}
    PRICED_EXPECT = {5: 29, 6: 35, 7: 43, 8: 53, 9: 326, 10: 630,
                     11: 1033, 12: 1547}
    for k in sorted(PRICED):
        check(f"k = {k}: the eta-priced threshold is {PRICED_EXPECT[k]}",
              PRICED[k] == PRICED_EXPECT[k], f"got {PRICED[k]}")
    # robustness: how large may a per-edge inflation be before Ntilde moves?
    log("      robustness: the largest constant per-edge inflation kappa* "
        "that leaves Ntilde unchanged")
    for k in (6, 7, 8):
        base = PRICED[k]
        lo, hi = Fr(1), Fr(4)
        for _ in range(30):
            mid = (lo + hi) / 2
            Cm = make_C(E0, collar_kappa=False)

            def Cx(m, n, kk, _m=mid, _C=Cm):
                return _C(m, n, kk) * _m ** 8
            if Ntilde(k, Cx) == base:
                lo = mid
            else:
                hi = mid
        kap_actual = rows[k - 5][2]
        log(f"      k = {k}: kappa* = {float(lo):.4f}   actual kappa = "
            f"{float(kap_actual):.6f}")
        check(f"k = {k}: a uniform per-edge inflation up to kappa* > 1 leaves "
              f"Ntilde(k) unchanged", lo > 1, f"kappa* = {float(lo)}")
    return rows


# ============================================================== V9

def V9():
    log("\nV9  the k = 5 threshold on the improved chain")
    E0 = MUT.get("e0", 8)
    C_slice = make_C(E0, collar_kappa=False)
    C_coll = make_C(E0, collar_kappa=True)
    fl = Ntilde(5, lambda m, n, kk: Fr(0))
    N_L0 = Ntilde(5, lambda m, n, kk: EL.Lam(m) / Fr(factorial(m))
                  * Q_cap(n, kk) ** ((m - 2) // 2)
                  * (1 if m % 2 == 0 else Q_cap(n, kk)))
    N_abs = Ntilde(5, C_evenlayer)
    N_u5 = Ntilde(5, C_slice)
    N_eta = Ntilde(5, C_coll)
    log(f"      collar floor      : {fl}")
    log(f"      EVENLAYER 'abs'   : {N_abs}")
    log(f"      U5-proved (slice) : {N_u5}")
    log(f"      U5-proved + eta   : {N_eta}")
    check("k = 5: every block size is <= 5 <= e0, so the chain is "
          "UNCONDITIONAL at k = 5", 5 <= E0)
    check("k = 5: the U5-proved threshold equals EVENLAYER's tier-graded one",
          N_u5 == N_abs, f"{N_u5} vs {N_abs}")
    check("k = 5: the eta re-pricing costs exactly one unit",
          N_eta == N_u5 + 1, f"{N_eta} vs {N_u5}")
    check("k = 5: the threshold is at or above the collar floor",
          N_eta >= fl, f"{N_eta} vs {fl}")
    log(f"      => Ntilde(5) = {N_eta}, unconditional")
    return N_eta


# ============================================================== V7

def V7():
    log("\nV7  mutation controls")
    faults = [
        ("half_constant", "U5 asserted with constant 1/2 instead of 1"),
        ("no_M1", "the series move M1 (degree-2 contraction) removed"),
        ("no_M4", "the leaf move M4 (weight propagation) removed"),
        ("no_M2", "the parallel/Hadamard move M2 removed"),
        ("e0_12", "e0 raised to 12 without proof (the tail bound ignored)"),
        ("no_kappa", "the collar eta re-pricing of the U5 toolkit dropped"),
    ]
    global PASS, FAIL, FIRED
    results = []
    for tag, desc in faults:
        p0, f0, fired0 = PASS, FAIL, len(FIRED)
        MUT.clear()
        RD.DISABLE.clear()
        if tag == "e0_12":
            MUT["e0"] = 12
        elif tag.startswith("no_M"):
            RD.DISABLE.add(tag[3:])
        else:
            MUT[tag] = True
        log(f"\n  --- injecting [{tag}] {desc}")
        if tag == "half_constant":
            V4()
        elif tag.startswith("no_M"):
            V3()
        elif tag == "no_kappa":
            V8()
            V9()
        else:
            V6()
        fired = len(FIRED) - fired0
        MUT.clear()
        RD.DISABLE.clear()
        # roll the section's own tally back: only the control counts
        PASS, FAIL = p0, f0
        del FIRED[fired0:]
        results.append((tag, desc, fired))
    log("")
    for tag, desc, fired in results:
        check(f"control [{tag}] fires at >= 2 independent positions",
              fired >= 2, f"{fired} positions -- {desc}")


# ============================================================== main

def main():
    log("=" * 74)
    log("graded_verify_u5.py -- U5.md, the connected-graph bound")
    log("=" * 74)
    V1()
    V2()
    V3()
    V4()
    V5()
    V6()
    V8()
    V9()
    V7()
    log("\n" + "=" * 74)
    log(f"RESULT: {PASS} checks passed, {FAIL} failed")
    if FIRED:
        log("failures:")
        for f in FIRED:
            log(f"  {f}")
    log("=" * 74)
    return 1 if FAIL else 0


if __name__ == "__main__":
    sys.exit(main())
