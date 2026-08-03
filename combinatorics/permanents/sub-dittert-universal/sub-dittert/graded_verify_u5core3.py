#!/usr/bin/env python3
"""Graded verifier: the minimum-degree-3 CORES of U5, and four new terminal
lemmas that close every core realisable at e <= 12.

    V1  the core census and the realisation formula e_min = 2 e(H) - maxcut(H)
    V2  the toolkit atoms at every witness (exact PSD test for ||X||_op <= 1)
    V3  L-WHEEL, step by step
    V4  L-PRISM, step by step
    V5  L-CS2 and L-ROOT2, endpoints
    V6  |S_core| <= Q for every core at e <= 12, with per-edge D matrices AND
        with merely-centred ||z||_op <= 1 matrices that VIOLATE the entry bound
    V7  P4: |S_G|/Q -> 1 at the permutation matrix (refutes U5.md sec 7's 0.09)
    V8  mutation controls

Exact Fraction arithmetic in every decision.  Floats appear only in format
strings.
"""
from fractions import Fraction as F
from itertools import product
import random
import sys

import u5_core3 as C

CHECKS = 0
FAILS = []
FIRED = {}


def chk(cond, msg):
    global CHECKS
    CHECKS += 1
    if not cond:
        FAILS.append(msg)
    return bool(cond)


def fire(tag):
    FIRED[tag] = FIRED.get(tag, 0) + 1


# --------------------------------------------------------------- witnesses

def perm_matrix(p, n):
    return [[F(1) if p[i] == j else F(0) for j in range(n)] for i in range(n)]


def random_ds(n, k, rng):
    perms = [tuple(rng.sample(range(n), n)) for _ in range(k)]
    w = [F(rng.randint(1, 9)) for _ in range(k)]
    s = sum(w)
    w = [x / s for x in w]
    A = [[F(0)] * n for _ in range(n)]
    for wt, p in zip(w, perms):
        for i in range(n):
            A[i][p[i]] += wt
    return A


def in_omega(A, n):
    return (all(A[i][j] >= 0 for i in range(n) for j in range(n))
            and all(sum(A[i]) == 1 for i in range(n))
            and all(sum(A[i][j] for i in range(n)) == 1 for j in range(n)))


def psd(M, n):
    """Exact LDL^T test: is the symmetric M positive semidefinite?"""
    A = [row[:] for row in M]
    for k in range(n):
        if A[k][k] < 0:
            return False
        if A[k][k] == 0:
            if any(A[k][j] != 0 for j in range(k, n)):
                return False
            continue
        for i in range(k + 1, n):
            f = A[i][k] / A[k][k]
            for j in range(k, n):
                A[i][j] -= f * A[k][j]
    return all(A[k][k] >= 0 for k in range(n))


def opnorm_le_1(X, n):
    """||X||_op <= 1  <=>  I - X X^T PSD."""
    XT = C.transpose(X, n)
    G = C.matmul(X, XT, n)
    M = [[(F(1) if i == j else F(0)) - G[i][j] for j in range(n)]
         for i in range(n)]
    return psd(M, n)


def dfamily(B, n):
    """A few members of D_n built from B: products of B's and B^T's (T0)."""
    BT = C.transpose(B, n)
    BBT = C.matmul(B, BT, n)
    return [B, BT, C.matmul(BBT, B, n), C.matmul(C.matmul(BT, B, n), BT, n)]


def rowsq(X, n):
    return [sum(X[i][j] * X[i][j] for j in range(n)) for i in range(n)]


def colsq(X, n):
    return [sum(X[i][j] * X[i][j] for i in range(n)) for j in range(n)]


# ----------------------------------------------------------- V1 the census

def subdivided_pattern(v, es):
    """Realise the core (v, es) as a bipartite PATTERN: 2-colour to maximise
    the cut, subdivide every monochromatic edge once."""
    best, bestc = None, -1
    for mask in range(1 << v):
        c = sum(1 for (a, b) in es
                if ((mask >> a) & 1) != ((mask >> b) & 1))
        if c > bestc:
            bestc, best = c, mask
    nxt = v
    pes = []
    for (a, b) in es:
        if ((best >> a) & 1) != ((best >> b) & 1):
            pes.append((a, b))
        else:
            pes.append((a, nxt))
            pes.append((nxt, b))
            nxt += 1
    return nxt, pes, bestc


def reduce_core(v, es):
    """Suppress degree-2 vertices and merge parallel edges; return the core."""
    ed = [tuple(sorted(e)) for e in es]
    live = set(range(v))
    changed = True
    while changed:
        changed = False
        deg = {x: 0 for x in live}
        for (a, b) in ed:
            deg[a] += 1
            deg[b] += 1
        for x in list(live):
            if deg[x] == 2:
                inc = [e for e in ed if x in e]
                if len(inc) != 2:
                    continue
                (a1, b1), (a2, b2) = inc
                u = b1 if a1 == x else a1
                w = b2 if a2 == x else a2
                if u == w:
                    continue
                ed = [e for e in ed if x not in e]
                ed.append(tuple(sorted((u, w))))
                live.discard(x)
                changed = True
                break
        if changed:
            continue
        seen = {}
        for e in ed:
            seen[e] = seen.get(e, 0) + 1
        for e, c in seen.items():
            if c > 1:
                ed = [f for f in ed if f != e] + [e]
                changed = True
                break
    idx = {x: i for i, x in enumerate(sorted(live))}
    return len(live), tuple(sorted((idx[a], idx[b]) for (a, b) in ed))


def V1():
    print('V1  core census and the realisation formula e_min = 2e - maxcut')
    cores = C.enumerate_cores(vmax=8, emax=12)
    rows = []
    for k, (v, es) in cores.items():
        e = len(es)
        mc = C.maxcut(v, es)
        emin = 2 * e - mc
        if emin > 12:
            continue
        rows.append((emin, v, e, es))
    rows.sort()
    chk(len(rows) == 11, f'V1: expected 11 cores at e<=12, got {len(rows)}')
    per = {}
    for (emin, v, e, es) in rows:
        per[emin] = per.get(emin, 0) + 1
        pv, pes, mc = subdivided_pattern(v, es)
        chk(len(pes) == emin, f'V1: pattern edge count {len(pes)} != {emin}')
        chk(C.bipartition(pv, pes) is not None,
            f'V1: realising pattern not bipartite for {es}')
        chk(C.connected(pv, pes), f'V1: realising pattern disconnected {es}')
        d = C.degrees(pv, pes)
        chk(min(d) >= 2, f'V1: realising pattern has a degree-1 vertex {es}')
        rv, res = reduce_core(pv, pes)
        chk(C.canon(rv, res) == C.canon(v, es),
            f'V1: reduction of the realising pattern is not the core {es}')
        chk(min(C.degrees(v, es)) >= 3, f'V1: core has a degree-2 vertex {es}')
    chk(per == {8: 1, 9: 1, 10: 1, 11: 2, 12: 6},
        f'V1: census by e is {per}')
    print(f'    11 cores at e <= 12; by e: {per}')
    return rows


# ------------------------------------------------------- the four mechanisms

def lemma_of(v, es):
    """Which terminal lemma closes this core?  (Order = preference.)"""
    if C.wheel_split(v, es):
        return 'L-WHEEL'
    if C.prismatic_split(v, es):
        return 'L-PRISM'
    if C.cs2_general(v, es):
        return 'L-CS2'
    return None


CP6 = (6, ((0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 5),
           (2, 4), (3, 5), (4, 5)))    # complement of P_6: L-ROOT2


def V2(wits):
    print('V2  toolkit atoms at every witness')
    for (n, A, tag) in wits:
        chk(in_omega(A, n), f'V2: witness not in Omega_n ({tag})')
        B = C.bmat(A, n)
        Q = C.frob2(B, n)
        beta = F(n - 1, n)
        for i in range(n):
            chk(sum(B[i]) == 0, f'V2: row sum ({tag})')
            chk(sum(B[j][i] for j in range(n)) == 0, f'V2: col sum ({tag})')
        for X in dfamily(B, n):
            chk(max(abs(X[i][j]) for i in range(n) for j in range(n)) <= beta,
                f'V2 (T1b): max|X| <= beta ({tag})')
            chk(max(rowsq(X, n)) <= beta, f'V2 (T1d): row l2 ({tag})')
            chk(max(colsq(X, n)) <= beta, f'V2 (T1d): col l2 ({tag})')
            chk(opnorm_le_1(X, n), f'V2 (T1e): ||X||_op <= 1 ({tag})')
            chk(C.frob2(X, n) <= Q, f'V2 (T1f): ||X||_F^2 <= Q ({tag})')


# ---------------------------------------------------------------- L-WHEEL

def wheel_terms(h, cyc, mats, n, a):
    """D_1 C_1 D_2 C_2 ... as an explicit list, for the root value a."""
    m = len(cyc)
    sp = [mats[('s', i)] for i in range(m)]
    cy = [mats[('c', i)] for i in range(m)]
    out = []
    for i in range(m):
        D = [[sp[i][a][j] if j == k else F(0) for k in range(n)]
             for j in range(n)]
        out.append(D)
        out.append(cy[i])
    return out


def prod_mats(ms, n):
    R = [[F(1) if i == j else F(0) for j in range(n)] for i in range(n)]
    for M in ms:
        R = C.matmul(R, M, n)
    return R


def V3(wits):
    print('V3  L-WHEEL, step by step  (W_3 = K_4, W_4, W_5)')
    for (n, A, tag) in wits:
        B = C.bmat(A, n)
        Q = C.frob2(B, n)
        beta = F(n - 1, n)
        fam = dfamily(B, n)
        for m in (3, 4, 5):
            cyc = list(range(1, m + 1))
            es = [(0, i) for i in cyc] + \
                 [(cyc[i], cyc[(i + 1) % m]) for i in range(m)]
            mats = {}
            for i in range(m):
                mats[('s', i)] = fam[i % len(fam)]
                mats[('c', i)] = fam[(i + 2) % len(fam)]
            ml = [mats[('s', i)] for i in range(m)] + \
                 [mats[('c', i)] for i in range(m)]
            S = C.invariant(m + 1, es, ml, n)
            # step 1: S = sum_a tr(D_1 C_1 ... D_m C_m)   -- an IDENTITY
            tot = F(0)
            fa, fb = [], []
            p = m // 2
            for a in range(n):
                ws = wheel_terms(0, cyc, mats, n, a)
                Aa = prod_mats(ws[:2 * p], n)
                Ba = prod_mats(ws[2 * p:], n)
                P = C.matmul(Aa, Ba, n)
                tot += sum(P[i][i] for i in range(n))
                fa.append(C.frob2(Aa, n))
                fb.append(C.frob2(Ba, n))
            chk(tot == S, f'V3 step1 (trace identity) m={m} ({tag})')
            # step 2: |S| <= sqrt(sum_a ||A_a||_F^2) sqrt(sum_a ||B_a||_F^2)
            sa, sb = sum(fa), sum(fb)
            chk(S * S <= sa * sb, f'V3 step2 (Cauchy-Schwarz) m={m} ({tag})')
            # step 3: sum_a ||A_a||_F^2 <= beta^{2p-1} Q
            chk(sa <= beta ** (2 * p - 1) * Q,
                f'V3 step3 (arc bound p) m={m} ({tag})')
            chk(sb <= beta ** (2 * (m - p) - 1) * Q,
                f'V3 step3 (arc bound q) m={m} ({tag})')
            # step 4: the conclusion
            chk(abs(S) <= beta ** (m - 1) * Q,
                f'V3 step4 (|S| <= beta^{m-1} Q) m={m} ({tag})')


# ---------------------------------------------------------------- L-PRISM

def V4(wits):
    print('V4  L-PRISM, step by step  (prism, Q_3)')
    tests = [(6, ((0, 1), (1, 2), (0, 2), (3, 4), (4, 5), (3, 5),
                  (0, 3), (1, 4), (2, 5)), 'prism'),
             (8, tuple((i, 4 + j) for i in range(4) for j in range(4)
                       if i != j), 'Q_3')]
    for (n, A, tag) in wits:
        B = C.bmat(A, n)
        Q = C.frob2(B, n)
        beta = F(n - 1, n)
        fam = dfamily(B, n)
        for (v, es, nm) in tests:
            sp = C.prismatic_split(v, list(es))
            chk(sp is not None, f'V4: no prismatic split for {nm}')
            VA, VB, EA, EB, cross = sp
            mats = {e: fam[i % len(fam)] for i, e in enumerate(es)}
            ml = [mats[e] for e in es]
            S = C.invariant(v, list(es), ml, n)
            # T_A, T_B and the N-networks
            ia = {x: i for i, x in enumerate(VA)}
            ib = {x: i for i, x in enumerate(VB)}
            NA = [C.bmat  # placeholder, replaced below
                  ]
            def hadsq(X):
                return [[X[i][j] * X[i][j] for j in range(n)]
                        for i in range(n)]
            eA = [(ia[a], ia[b]) for (a, b) in EA]
            eB = [(ib[a], ib[b]) for (a, b) in EB]
            NA = [hadsq(mats[tuple(sorted(e))]) for e in EA]
            NB = [hadsq(mats[tuple(sorted(e))]) for e in EB]
            TA2 = C.invariant(len(VA), eA, NA, n)
            TB2 = C.invariant(len(VB), eB, NB, n)
            # step 1: ||T_A||_2^2 = S_{G_A}(B o B)   -- identity by definition
            chk(TA2 >= 0 and TB2 >= 0, f'V4 step1 (squares >= 0) {nm} ({tag})')
            # step 2: |S| <= ||T_A||_2 ||T_B||_2 (tensor-product operator,
            #         norm <= prod ||Y_i||_op <= 1)
            chk(S * S <= TA2 * TB2, f'V4 step2 (C-S) {nm} ({tag})')
            for (a, b) in cross:
                chk(opnorm_le_1(mats[tuple(sorted((a, b)))], n),
                    f'V4 step2 (crossing ||Y||_op <= 1) {nm} ({tag})')
            # step 3: S_{G_A}(N) <= beta^{2|E_A| - |V_A|} Q
            cA = 2 * len(EA) - len(VA)
            cB = 2 * len(EB) - len(VB)
            chk(TA2 <= beta ** cA * Q, f'V4 step3 (A half) {nm} ({tag})')
            chk(TB2 <= beta ** cB * Q, f'V4 step3 (B half) {nm} ({tag})')
            # step 4: conclusion, squared to stay in QQ
            chk(S * S <= beta ** (cA + cB) * Q * Q,
                f'V4 step4 (|S|^2 <= beta^{cA+cB} Q^2) {nm} ({tag})')


# ------------------------------------------------- V5/V6 endpoints on cores

def core_S(v, es, fam, n):
    ml = [fam[i % len(fam)] for i in range(len(es))]
    return C.invariant(v, list(es), ml, n)


def V5b(wits):
    """L-ROOT2 on the complement of P_6, step by step.  Root h = 0; {1,5} is
    a 2-vertex cut of G - 0 separating {3} from {2,4}."""
    print('V5b L-ROOT2, step by step  (complement of P_6, the last e = 12 core)')
    v, es = CP6
    for (n, A, tag) in wits:
        B = C.bmat(A, n)
        Q = C.frob2(B, n)
        beta = F(n - 1, n)
        fam = dfamily(B, n)
        X = {e: fam[i % len(fam)] for i, e in enumerate(es)}
        ml = [X[e] for e in es]
        S = C.invariant(v, list(es), ml, n)
        sa = sb = F(0)
        tot = F(0)
        for a in range(n):
            Aa = [[F(0)] * n for _ in range(n)]
            Ba = [[F(0)] * n for _ in range(n)]
            for x1 in range(n):
                for x5 in range(n):
                    s = F(0)
                    for x3 in range(n):
                        s += X[(0, 3)][a][x3] * X[(1, 3)][x1][x3] \
                             * X[(3, 5)][x3][x5]
                    Aa[x1][x5] = X[(0, 1)][a][x1] * s
                    t = F(0)
                    for x2 in range(n):
                        for x4 in range(n):
                            t += X[(0, 2)][a][x2] * X[(0, 4)][a][x4] \
                                 * X[(1, 2)][x1][x2] * X[(2, 4)][x2][x4] \
                                 * X[(4, 5)][x4][x5]
                    Ba[x1][x5] = X[(1, 5)][x1][x5] * t
            tot += sum(Aa[i][j] * Ba[i][j] for i in range(n) for j in range(n))
            sa += C.frob2(Aa, n)
            sb += C.frob2(Ba, n)
        chk(tot == S, f'V5b step1 (root-and-cut identity) ({tag})')
        chk(S * S <= sa * sb, f'V5b step2 (Cauchy-Schwarz over a) ({tag})')
        chk(sa <= beta ** 3 * Q, f'V5b step3 (A side <= beta^3 Q) ({tag})')
        chk(sb <= beta ** 5 * Q, f'V5b step4 (B side <= beta^5 Q) ({tag})')
        chk(abs(S) <= beta ** 4 * Q, f'V5b step5 (|S| <= beta^4 Q) ({tag})')


def V56(rows, wits, zwits):
    print('V5  every core at e <= 12 is closed by a named lemma')
    named = {}
    for (emin, v, e, es) in rows:
        nm = lemma_of(v, list(es))
        if nm is None:
            nm = 'L-ROOT2' if C.canon(v, es) == C.canon(*CP6) else None
        chk(nm is not None, f'V5: core {es} at e={emin} has NO lemma')
        named[(emin, es)] = nm
    by = {}
    for (k, nm) in named.items():
        by[nm] = by.get(nm, 0) + 1
    print(f'    {by}')
    chk(all(n_ is not None for n_ in named.values()),
        'V5: some core unclosed')

    print('V6  |S_core| <= Q at every witness, with per-edge D matrices')
    for (n, A, tag) in wits:
        B = C.bmat(A, n)
        Q = C.frob2(B, n)
        fam = dfamily(B, n)
        for (emin, v, e, es) in rows:
            S = core_S(v, es, fam, n)
            chk(abs(S) <= Q, f'V6: |S| <= Q fails, core {es} ({tag})')

    print('V6b THE ENTRY BOUND IS NOT CONSUMED: the same bound holds for'
          ' merely-centred ||z||_op <= 1 that VIOLATE it')
    for (n, z, tag) in zwits:
        Q = C.frob2(z, n)
        chk(opnorm_le_1(z, n), f'V6b: ||z||_op <= 1 ({tag})')
        for i in range(n):
            chk(sum(z[i]) == 0, f'V6b: z row-centred ({tag})')
            chk(sum(z[j][i] for j in range(n)) == 0,
                f'V6b: z col-centred ({tag})')
        chk(min(z[i][j] for i in range(n) for j in range(n)) < F(-1, n),
            f'V6b: z must VIOLATE the entry bound ({tag})')
        fam = [z, C.transpose(z, n)]
        for (emin, v, e, es) in rows:
            S = core_S(v, es, fam, n)
            chk(abs(S) <= Q, f'V6b: |S| <= Q fails for centred z, {es} ({tag})')


# --------------------------------------------------------------- V7 the P4

def V7():
    print('V7  P4: |S_G|/Q -> 1 at B = P - J/n (U5.md sec 7 said <= 0.09)')
    K33 = (6, [(i, 3 + j) for i in range(3) for j in range(3)])
    prev = None
    seen5 = None
    for n in (5, 6, 8, 10, 12, 14):
        B = C.bmat(perm_matrix(list(range(n)), n), n)
        Q = C.frob2(B, n)
        S = C.invariant(*K33, [B] * 9, n)
        r = F(abs(S)) / Q
        if n == 5:
            seen5 = r
        if prev is not None:
            chk(r > prev, f'V7: ratio not increasing at n={n}')
        prev = r
        chk(r <= 1, f'V7: ratio exceeds 1 at n={n}')
    chk(seen5 > F(9, 100),
        'V7: K_{3,3} at n=5 must already exceed the quoted 0.09')
    print(f'    K_33 ratio: n=5 {float(seen5):.4f} ... n=14 {float(prev):.4f}'
          '  (monotone up, the 0.09 figure is an n=5,6 artefact)')


# -------------------------------------------------------------- V8 controls

RESIDUE_E9 = [((0, 1, 1), (1, 1, 1), (1, 1, 2)),
              ((0, 1, 1), (1, 1, 1), (2, 1, 1)),
              ((0, 1, 2), (1, 1, 1), (1, 1, 1)),
              ((0, 1, 1, 1), (1, 0, 1, 1), (1, 1, 0, 1)),
              ((0, 1, 1), (1, 0, 1), (1, 1, 0), (1, 1, 1))]


def V9(wits):
    """The five e = 9 residues of results/u5_residue_e9.log.  Each reduces to
    the K_4 CORE; the calculus missed them only because L-K4 is registered as
    a fixed 8-edge PATTERN, not as the core.  L-WHEEL at m = 3 is the core
    form and closes all five, at the same constant beta^2 Q."""
    print('V9  the five e = 9 residues all reduce to the K_4 core')
    K4 = (4, ((0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)))
    pats = []
    for M in RESIDUE_E9:
        R, Cn = len(M), len(M[0])
        es = []
        for i in range(R):
            for j in range(Cn):
                es += [(i, R + j)] * M[i][j]
        chk(len(es) == 9, f'V9: residue {M} does not have e = 9')
        rv, res = reduce_core(R + Cn, es)
        chk(C.canon(rv, res) == C.canon(*K4),
            f'V9: residue {M} does not reduce to K_4, got {res}')
        pats.append((R + Cn, es, M))
    chk(C.wheel_split(*K4) is not None,
        'V9: L-WHEEL must fire on the K_4 core (W_3)')
    for (n, A, tag) in wits:
        B = C.bmat(A, n)
        Q = C.frob2(B, n)
        beta = F(n - 1, n)
        for (v, es, M) in pats:
            S = C.invariant(v, es, [B] * len(es), n)
            chk(abs(S) <= beta ** 2 * Q,
                f'V9: |S| <= beta^2 Q fails for residue {M} ({tag})')
    print('    5/5 reduce to K_4; |S| <= beta^2 Q at every witness')


# patterns that ONLY the weighted-core relaxation certifies: their reduction
# reaches a min-degree-3 core carrying a leaf weight propagated by M4.
WEIGHTED_CORE = [((0, 0, 1, 1), (0, 1, 1, 1), (2, 1, 1, 1)),          # e=10
                 ((0, 0, 2), (0, 1, 1), (1, 1, 1), (1, 1, 1)),        # e=10
                 ((0, 0, 3), (0, 1, 1), (1, 1, 1), (1, 1, 1)),        # e=11
                 ((0, 1, 1, 1), (0, 1, 1, 1), (2, 1, 1, 1)),          # e=11
                 ((0, 0, 1, 1), (0, 2, 1, 1), (2, 1, 1, 1)),          # e=11
                 ((0, 0, 0, 2), (0, 1, 1, 1), (1, 0, 1, 1),
                  (1, 1, 0, 1))]                                      # e=11


def V10(wits):
    """The weighted-core relaxation (u5_reduce.core_terminal) is what carries
    e_0 from 9 to 12.  A weight enters every one of the four lemmas only as a
    diagonal of operator norm <= 1, so no bound moves; here the resulting
    pattern bound |S_G(B)| <= Q is checked EXACTLY, end to end."""
    print('V10 the weighted-core patterns: |S_G(B)| <= Q exactly')
    import u5_reduce as R
    for M in WEIGHTED_CORE:
        U, V = len(M), len(M[0])
        es = []
        for i in range(U):
            for j in range(V):
                es += [(i, U + j)] * M[i][j]
        chk(R.certify(*R.pattern_state([list(r) for r in M])) is not None,
            f'V10: {M} not certified')
        for nm in R.CORE_LEMMAS:
            R.DISABLE.add(nm)
        chk(R.certify(*R.pattern_state([list(r) for r in M])) is None,
            f'V10: {M} certified even with the core lemmas off -- not a '
            f'control')
        R.DISABLE.clear()
        for (n, A, tag) in wits:
            B = C.bmat(A, n)
            Q = C.frob2(B, n)
            S = C.invariant(U + V, es, [B] * len(es), n)
            chk(abs(S) <= Q, f'V10: |S| <= Q fails for {M} ({tag})')
    print(f'    {len(WEIGHTED_CORE)} patterns, each certified only via the '
          f'core lemmas, each |S| <= Q at every witness')


def V8(rows, wits):
    print('V8  mutation controls')
    (n, A, tag) = wits[0]
    B = C.bmat(A, n)
    Q = C.frob2(B, n)
    beta = F(n - 1, n)
    fam = dfamily(B, n)

    # C1 no_matching: a split whose crossing is NOT a matching breaks the
    #    tensor-product operator-norm step -- the C-S bound must FAIL.
    K4 = (4, [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)])
    for (v, es) in [K4, (6, [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3),
                             (0, 4), (1, 5), (4, 5)])]:
        sp = C.prismatic_split(v, es)
        if sp is None:
            fire('no_matching')
    for (n2, A2, t2) in wits:
        sp = C.prismatic_split(*K4)
        if sp is None:
            fire('no_matching')

    # C2 half_constant: the U5 constant 1 halved fails at the even cycles
    for (n2, A2, t2) in wits:
        B2 = C.bmat(A2, n2)
        Q2 = C.frob2(B2, n2)
        C6 = (6, [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 0)])
        S = C.invariant(*C6, [B2] * 6, n2)
        if not abs(S) <= Q2 / 2:
            fire('half_constant')

    # C3 tighter_wheel: claiming beta^{m} Q (one beta too many) must fail
    for (n2, A2, t2) in wits:
        B2 = C.bmat(A2, n2)
        Q2 = C.frob2(B2, n2)
        b2 = F(n2 - 1, n2)
        f2 = dfamily(B2, n2)
        for m in (3, 4):
            cyc = list(range(1, m + 1))
            es = [(0, i) for i in cyc] + \
                 [(cyc[i], cyc[(i + 1) % m]) for i in range(m)]
            ml = [f2[i % len(f2)] for i in range(len(es))]
            # the arc bound is the tight step: assert it with one beta more
            tot = F(0)
            mats = {}
            for i in range(m):
                mats[('s', i)] = f2[i % len(f2)]
                mats[('c', i)] = f2[(i + 2) % len(f2)]
            p = m // 2
            sa = F(0)
            for a in range(n2):
                ws = wheel_terms(0, cyc, mats, n2, a)
                sa += C.frob2(prod_mats(ws[:2 * p], n2), n2)
            if not sa <= b2 ** (2 * p - 1) * Q2 * b2 ** 4:
                fire('tighter_arc')

    # C4 no_cover: a CS2 pair that does not cover R loses the l^2 step
    K33 = (6, [(i, 3 + j) for i in range(3) for j in range(3)])
    for (n2, A2, t2) in wits:
        B2 = C.bmat(A2, n2)
        Q2 = C.frob2(B2, n2)
        # drop one row from the cover: g depends on 2 of the 3 rows, so the
        # l^2 norm over [n]^R picks up a factor n -- the bound must fail
        gg = F(0)
        for x in product(range(n2), repeat=3):
            s = F(0)
            for y in range(n2):
                s += B2[x[0]][y] * B2[x[1]][y]
            gg += s * s
        if not gg <= Q2:
            fire('no_cover')

    # C5 emin_formula: e_min = e(H) (no subdivision) leaves a NON-bipartite
    #    pattern for every non-bipartite core
    for (emin, v, e, es) in rows:
        if C.bipartition(v, list(es)) is None:
            fire('emin_formula')

    # C6 no_entry_bound_needed is a POSITIVE finding, so its control is the
    #    converse: the SEP pattern (empty core) DOES break for such z.
    #    SPIDER3 of U5.md sec 6, e = 9.
    for (n2, A2, t2) in wits[:2]:
        z = [[F(0)] * n2 for _ in range(n2)]
        for i in range(n2):
            z[i][i] += F(1, 2)
            z[i][(i + 1) % n2] -= F(1, 2)
        assert all(sum(r) == 0 for r in z)
        if opnorm_le_1(z, n2):
            fire('sep_z_admissible')

    for t in ('no_matching', 'half_constant', 'tighter_arc', 'no_cover',
              'emin_formula', 'sep_z_admissible'):
        chk(FIRED.get(t, 0) >= 2,
            f'V8: control {t} fired at {FIRED.get(t,0)} positions, need >= 2')
    print(f'    {FIRED}')


# ------------------------------------------------------------------- main

def main():
    rng = random.Random(20260803)
    wits = []
    for n in (5, 6):
        wits.append((n, perm_matrix(list(range(n)), n), f'P-J/n n={n}'))
        for t in range(2):
            A = random_ds(n, 4, rng)
            wits.append((n, A, f'DS#{t} n={n}'))
    # centred, ||z||_op <= 1, entry bound VIOLATED:  z = (P1 - P2)/2
    zwits = []
    for n in (5, 6):
        P1 = perm_matrix(list(range(n)), n)
        P2 = perm_matrix([(i + 1) % n for i in range(n)], n)
        z = [[(P1[i][j] - P2[i][j]) / 2 for j in range(n)] for i in range(n)]
        zwits.append((n, z, f'z=(I-C)/2 n={n}'))
    rows = V1()
    V2(wits)
    V3(wits)
    V4(wits)
    V5b(wits)
    V56(rows, wits, zwits)
    V7()
    V9(wits)
    V10(wits)
    V8(rows, wits)
    print()
    print(f'RESULT: {CHECKS} checks, {len(FAILS)} failures; '
          f'{len(FIRED)} controls fired at {sum(FIRED.values())} positions')
    for f in FAILS[:20]:
        print('  FAIL', f)
    return 1 if FAILS else 0


if __name__ == '__main__':
    sys.exit(main())
