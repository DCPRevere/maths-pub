"""
STANDALONE VERIFIER for Theorem G-uniform (UNIFORM-G.md in this directory):
Theorem G of results/paper_b.typ, proved for EVERY k with an explicit
threshold N(k) = 8 k^2 (k-2)^2 and the sharp constant c(n,k) = t_2/4.

Self-contained on purpose: standard library only, Fraction throughout, no
float in any decision.

WHAT IT VERIFIES, in the order UNIFORM-G.md needs it.

  V1  Lemma U1, the partition expansion
          sigma_m(B) = (1/m!) sum_{pi,rho} mu(pi) mu(rho) S(pi,rho),
      against brute-force subpermanent sums, and the vanishing of the pairs
      with a singleton block on the centred slice.
  V2  Lemma U2, sum |mu(pi)| = D_m over partitions with all blocks >= 2.
  V3  The coefficient-mass identity D_m^2/m! = sum |coefficients| of the
      paper's sigma_3, sigma_4, sigma_5 expansions.
  V4  Lemma U3 (Finner), |S(pi,rho)| <= Q^(m/2), checked squared over Q.
  V5  Lemma U4, sigma_m(B) >= -C_m(n) Q, at every test matrix.
  V6  The uniform C_3, C_4, C_5 against the paper's, with the ratio: the
      honest direction is that the uniform constants are WORSE.
  V7  The endgame chain (E1)-(E4) term by term on a grid of (k,n).
  V8  The exact thresholds of section 7: Phi(N,k) < 1 and Phi(N-1,k) >= 1.
  V9  Theorem G end to end on the permutation pencil at k = 6 and k = 7,
      beyond anything previously proved, using a closed form for
      sigma_m(P - J/n) that is itself verified against brute force.
  V10 Mutation controls: four injected faults, each of which must be caught,
      and which raise nothing when not injected.

Usage:  GUARD_MEM=4G GUARD_CPUS=200% GUARD_THREADS=2 ../guard.sh \
            python3 graded_verify_uniformG.py
"""

import sys
from fractions import Fraction as Fr
from itertools import combinations, permutations
from math import comb, factorial, isqrt

OUT = []
FAIL = 0
MUT = {}
MUT_ACTIVE = False
MUT_FAILS = 0
QUIET = False


def log(s=""):
    if not QUIET:
        OUT.append(s)
        print(s)


def check(name, ok, detail=""):
    global FAIL, MUT_FAILS
    if MUT_ACTIVE:
        if not ok:
            MUT_FAILS += 1
        return ok
    if not ok:
        FAIL += 1
    log(f"  [{'ok ' if ok else 'FAIL'}] {name}" + (f"   {detail}" if detail else ""))
    return ok


# ----------------------------------------------------------------- combinatorics

def set_partitions(m):
    """All set partitions of range(m), each a tuple of tuples."""
    if m == 0:
        return [()]
    out = []
    for smaller in set_partitions(m - 1):
        for i in range(len(smaller)):
            out.append(smaller[:i] + (smaller[i] + (m - 1,),) + smaller[i + 1:])
        out.append(smaller + ((m - 1,),))
    return out


def mobius(pi):
    """mu(0-hat, pi) = prod (-1)^(|P|-1) (|P|-1)!."""
    v = 1
    for blk in pi:
        v *= (-1) ** (len(blk) - 1) * factorial(len(blk) - 1)
    return v


def all_blocks_ge2(pi):
    return all(len(b) >= 2 for b in pi)


def derangements(m):
    d = [1, 0]
    for i in range(2, m + 1):
        d.append((i - 1) * (d[i - 1] + d[i - 2]))
    return d[m]


def block_of(pi, r):
    for idx, blk in enumerate(pi):
        if r in blk:
            return idx
    raise KeyError(r)


def multiplicity(pi, rho, m):
    """c[u][v] = number of r in [m] with pi(r) = u, rho(r) = v."""
    c = [[0] * len(rho) for _ in range(len(pi))]
    for r in range(m):
        c[block_of(pi, r)][block_of(rho, r)] += 1
    return c


def orbit_S(pi, rho, B, n, m):
    """S(pi,rho): sum over i: blocks(pi)->[n], j: blocks(rho)->[n] of the
    product over the m edges.  Column blocks factorise given i, so the cost is
    n^|pi| * |rho| * n * |pi| rather than n^(|pi|+|rho|)."""
    c = multiplicity(pi, rho, m)
    U, V = len(pi), len(rho)
    total = Fr(0)
    idx = [0] * U
    while True:
        term = Fr(1)
        for v in range(V):
            s = Fr(0)
            for j in range(n):
                p = Fr(1)
                for u in range(U):
                    e = c[u][v]
                    if e:
                        p *= B[idx[u]][j] ** e
                s += p
            term *= s
            if term == 0:
                break
        total += term
        t = U - 1
        while t >= 0:
            idx[t] += 1
            if idx[t] < n:
                break
            idx[t] = 0
            t -= 1
        if t < 0:
            break
    return total


def sigma_bruteforce(B, n, m):
    """sigma_m(B) = sum over |S|=|T|=m of per(B[S|T])."""
    tot = Fr(0)
    rows = list(combinations(range(n), m))
    for S in rows:
        for T in rows:
            p = Fr(0)
            for perm in permutations(range(m)):
                q = Fr(1)
                for a in range(m):
                    q *= B[S[a]][T[perm[a]]]
                p += q
            tot += p
    return tot


def sigma_from_expansion(B, n, m, restrict_ge2=True):
    """(1/m!) sum_{pi,rho} mu mu S, over all partitions or only those with all
    blocks of size >= 2."""
    parts = [p for p in set_partitions(m) if (all_blocks_ge2(p) or not restrict_ge2)]
    tot = Fr(0)
    for pi in parts:
        mp = mobius(pi)
        for rho in parts:
            tot += mp * mobius(rho) * orbit_S(pi, rho, B, n, m)
    return Fr(tot, factorial(m))


# ------------------------------------------------------------- test matrices

def perm_matrix(n, shift=1):
    return [[Fr(1) if (j - i) % n == shift % n else Fr(0) for j in range(n)]
            for i in range(n)]


def uniform(n):
    return [[Fr(1, n)] * n for _ in range(n)]


def combo(n, weights):
    """convex combination sum_t w_t P_(shift t), weights a list of (shift, w)."""
    M = [[Fr(0)] * n for _ in range(n)]
    for sh, w in weights:
        P = perm_matrix(n, sh)
        for i in range(n):
            for j in range(n):
                M[i][j] += w * P[i][j]
    return M


def centre(A, n):
    return [[A[i][j] - Fr(1, n) for j in range(n)] for i in range(n)]


def frob2(B, n):
    return sum(B[i][j] ** 2 for i in range(n) for j in range(n))


def test_matrices(n):
    """Exact doubly stochastic test matrices at size n, with a label each."""
    out = [("perm", perm_matrix(n)),
           ("J/n", uniform(n)),
           ("(J-P)/(n-1)", [[Fr(0) if (j - i) % n == 1 else Fr(1, n - 1)
                             for j in range(n)] for i in range(n)]),
           ("half P + half P^2", combo(n, [(1, Fr(1, 2)), (2, Fr(1, 2))])),
           ("uniform over all shifts", combo(n, [(t, Fr(1, n)) for t in range(n)])),
           ("3-mix", combo(n, [(0, Fr(1, 2)), (1, Fr(1, 3)), (2, Fr(1, 6))]))]
    if n >= 4:
        out.append(("skew-mix", combo(n, [(0, Fr(2, 5)), (2, Fr(2, 5)),
                                          (3, Fr(1, 5))])))
    return out


# ------------------------------------------------------------ the constants

def W(m, n, k):
    """t_m / t_2."""
    num = n ** (m - 2)
    for j in range(m - 2):
        num *= (k - 2 - j)
    den = 1
    for j in range(2, m):
        den *= (n - j) ** 2
    return Fr(num, den)


def t_coeff(m, n, k):
    """t_m itself."""
    num = 1
    for j in range(m):
        num *= (k - j) ** 2
    den = 1
    for j in range(m):
        den *= (n - j) ** 2
    return Fr(num, den) * Fr(factorial(k - m), n ** (k - m))


def Rup(n):
    """rational R >= sqrt(n-1), by AM-GM on r = floor(sqrt(n-1))."""
    r = isqrt(n - 1)
    if r == 0:
        return Fr(1)
    return Fr(n - 1 + r * r, 2 * r)


def C_uniform(m, n):
    """Lemma U4: (D_m^2/m!) (n-1)^((m-2)/2), in rational form."""
    base = Fr(derangements(m) ** 2, factorial(m))
    if MUT.get("halve_C"):
        base = base / 2
    if MUT.get("derangement_mass"):
        base = Fr(factorial(m - 1) ** 2, factorial(m))
    if MUT.get("finner_exponent"):
        e = m - 3
        return base * Fr((n - 1) ** (e // 2)) * (Rup(n) if e % 2 else Fr(1))
    if m % 2 == 0:
        return base * Fr((n - 1) ** ((m - 2) // 2))
    return base * Fr((n - 1) ** ((m - 3) // 2)) * Rup(n)


def C_bound(m, n):
    """(E2): the majorant (m!/4)(n-1)^((m-2)/2), in rational form."""
    base = Fr(factorial(m), 4)
    if m % 2 == 0:
        return base * Fr((n - 1) ** ((m - 2) // 2))
    return base * Fr((n - 1) ** ((m - 3) // 2)) * Rup(n)


def C_paper(m, n):
    b = Fr(n - 1, n)
    if m == 3:
        return Fr(2, 3 * n)
    if m == 4:
        return Fr(3, 2) * b
    if m == 5:
        return Fr(24, 5 * n ** 3) + Fr(10, 3) * b + 8 * b * b
    return None


def C_m(m, n, mixed):
    c = C_uniform(m, n)
    if mixed and m <= 5:
        c = min(c, C_paper(m, n))
    return c


def Phi(n, k, mixed=False):
    return 4 * sum(W(m, n, k) * C_m(m, n, mixed) for m in range(3, k + 1))


def w_of(n, k):
    return Fr(n * (k - 2), (n - k + 1) ** 2)


def theta_of(n, k):
    return w_of(n, k) * Rup(n)


def N_closed(k):
    return 8 * k * k * (k - 2) ** 2


def least_n(k, mixed, hi=10 ** 8):
    """Least n with Phi(n,k) < 1, by doubling then bisection.  The result is
    confirmed by the caller with Phi(N-1) >= 1 > Phi(N), so no monotonicity is
    assumed in the claim itself."""
    lo, n = max(k, 2), max(k, 2)
    while n < hi and Phi(n, k, mixed) >= 1:
        lo, n = n, 2 * n + 1
    if n >= hi:
        return None
    while n - lo > 1:
        mid = (lo + n) // 2
        if Phi(mid, k, mixed) < 1:
            n = mid
        else:
            lo = mid
    return n


# ===================================================================== checks

def V1():
    log("V1  Lemma U1: the partition expansion against brute force")
    for n in (4, 5):
        for lab, A in test_matrices(n):
            B = centre(A, n)
            for m in range(2, min(n, 5) + 1):
                bf = sigma_bruteforce(B, n, m)
                ex = sigma_from_expansion(B, n, m, restrict_ge2=True)
                check(f"n={n} m={m} {lab}: expansion = brute force", bf == ex,
                      f"{bf}")
    # the >=2 restriction is not an extra assumption: the full sum agrees
    n = 4
    B = centre(test_matrices(n)[0][1], n)
    for m in (3, 4):
        full = sigma_from_expansion(B, n, m, restrict_ge2=False)
        ge2 = sigma_from_expansion(B, n, m, restrict_ge2=True)
        check(f"n=4 m={m}: singleton blocks contribute 0", full == ge2)
    log()


def V2():
    log("V2  Lemma U2: sum |mu| over partitions with all blocks >= 2 = D_m")
    for m in range(2, 10):
        tot = sum(abs(mobius(p)) for p in set_partitions(m) if all_blocks_ge2(p))
        check(f"m={m}: sum |mu| = D_m = {derangements(m)}",
              tot == derangements(m))
    log()


def V3():
    log("V3  coefficient mass D_m^2/m! against the paper's expansions")
    # paper_b.typ eq-stab-core4 / eq-stab-core5, absolute values of coefficients
    paper_mass = {3: Fr(2, 3),
                  4: Fr(3, 2) + Fr(1, 8) + Fr(1, 4) + Fr(3, 4) + Fr(3, 4),
                  5: Fr(24, 5) + Fr(1, 3) + 1 + 2 + 4 + 4}
    for m in (3, 4, 5):
        mass = Fr(derangements(m) ** 2, factorial(m))
        check(f"m={m}: D_m^2/m! = sum |coeff| = {mass}", mass == paper_mass[m])
    log()


def V4():
    log("V4  Lemma U3 (Finner): S(pi,rho)^2 <= Q^m for every surviving pair")
    worst = None
    for n, mmax in ((4, 5), (3, 6)):
        for lab, A in test_matrices(n):
            B = centre(A, n)
            Q = frob2(B, n)
            for m in range(2, mmax + 1):
                parts = [p for p in set_partitions(m) if all_blocks_ge2(p)]
                bad = 0
                for pi in parts:
                    for rho in parts:
                        S = orbit_S(pi, rho, B, n, m)
                        if S * S > Q ** m:
                            bad += 1
                        if Q > 0 and S != 0:
                            rat = S * S / Q ** m
                            if worst is None or rat > worst[0]:
                                worst = (rat, n, m, lab)
                check(f"n={n} m={m} {lab}: all pairs obey |S| <= Q^(m/2)",
                      bad == 0, f"{len(parts)**2} pairs")
    if worst:
        log(f"      tightest observed (S/Q^(m/2))^2 = {worst[0]} at n={worst[1]}"
            f" m={worst[2]} {worst[3]}")
    log()


def V5():
    log("V5  Lemma U4: sigma_m(B) >= -C_m(n) Q at every test matrix")
    for n in (4, 5, 6):
        for lab, A in test_matrices(n):
            B = centre(A, n)
            Q = frob2(B, n)
            for m in range(3, min(n, 6) + 1):
                s = sigma_bruteforce(B, n, m)
                bound = -C_uniform(m, n) * Q
                check(f"n={n} m={m} {lab}: sigma_m >= -C_m Q", s >= bound,
                      f"sigma={s} bound={bound}")
    log()


def V6():
    log("V6  the uniform C_m against the paper's (the honest direction)")
    for n in (8, 14, 50, 200):
        for m in (3, 4, 5):
            cu, cp = C_uniform(m, n), C_paper(m, n)
            check(f"n={n} m={m}: uniform C_m >= paper C_m (uniform is weaker)",
                  cu >= cp, f"ratio uniform/paper = {float(cu / cp):.3g}")
    log()


def V7():
    log("V7  the endgame chain (E1)-(E4)")
    ks = [6, 7, 8, 10, 12, 15, 20, 30, 40]
    for k in ks:
        N = N_closed(k)
        for n in (N, 2 * N, 5 * N):
            w, th = w_of(n, k), theta_of(n, k)
            # (E1)
            e1 = all(W(m, n, k) <= w ** (m - 2) for m in range(3, k + 1))
            check(f"k={k} n={n}: (E1) W_m <= w^(m-2) for all m", e1)
            # (E2)
            e2 = all(C_uniform(m, n) <= C_bound(m, n) for m in range(3, k + 1))
            check(f"k={k} n={n}: (E2) C_m <= (m!/4)(n-1)^((m-2)/2)", e2)
            # (E3)
            tail = sum(Fr(factorial(m)) * th ** (m - 2) for m in range(3, k + 1))
            check(f"k={k} n={n}: (E3) Phi <= sum m! theta^(m-2)",
                  Phi(n, k) <= tail)
            check(f"k={k} n={n}: (E4) k*theta <= 2/5", k * th <= Fr(2, 5),
                  f"k*theta = {float(k * th):.4g}")
            check(f"k={k} n={n}: geometric tail <= 10 theta", tail <= 10 * th)
            check(f"k={k} n={n}: 10 theta <= 4/k < 1", 10 * th <= Fr(4, k))
            check(f"k={k} n={n}: Phi < 1", Phi(n, k) < 1,
                  f"Phi = {float(Phi(n, k)):.4g}")
    # the two rational steps inside (E4)
    for k in ks + [50, 100]:
        N = N_closed(k)
        check(f"k={k}: 2(k-1)/N <= 1/100", Fr(2 * (k - 1), N) <= Fr(1, 100))
        check(f"k={k}: (N-k+1)^2 >= (99/100) N^2",
              Fr((N - k + 1) ** 2) >= Fr(99, 100) * N ** 2)
        check(f"k={k}: N >= (250/99)^2 k^2 (k-2)^2",
              Fr(N) >= Fr(250, 99) ** 2 * k ** 2 * (k - 2) ** 2)
    log()


def V8(ks=None):
    log("V8  the exact thresholds of UNIFORM-G.md section 7")
    claimed_pure = {3: 14, 4: 81, 5: 236, 6: 497, 7: 871, 8: 1367, 10: 2748,
                    12: 4688, 15: 8738, 20: 18964, 30: 57420, 50: 289608}
    claimed_mixed = {3: 4, 4: 8, 5: 14, 6: 110, 7: 273, 8: 523, 10: 1325,
                     12: 2590, 15: 5515, 20: 13817, 30: 49702, 50: 280192}
    if ks is not None:
        claimed_pure = {k: v for k, v in claimed_pure.items() if k in ks}
        claimed_mixed = {k: v for k, v in claimed_mixed.items() if k in ks}
    for mixed, claimed, name in ((False, claimed_pure, "uniform C_m"),
                                 (True, claimed_mixed, "mixed C_m")):
        for k, N in sorted(claimed.items()):
            check(f"{name} k={k}: Phi({N},{k}) < 1", Phi(N, k, mixed) < 1,
                  f"Phi = {float(Phi(N, k, mixed)):.4g}")
            check(f"{name} k={k}: Phi({N - 1},{k}) >= 1 (threshold is exact)",
                  Phi(N - 1, k, mixed) >= 1)
            check(f"{name} k={k}: least n = {N}", least_n(k, mixed) == N)
    for k in (3, 4, 5):
        if k in claimed_mixed:
            check(f"mixed k={k} reproduces the paper's threshold",
                  claimed_mixed[k] == {3: 4, 4: 8, 5: 14}[k])
    for k in sorted(claimed_mixed):
        if k >= 6 and k in claimed_pure:
            check(f"k={k}: closed form N(k)={N_closed(k)} exceeds the exact "
                  f"boundary {claimed_pure[k]}", N_closed(k) >= claimed_pure[k])
    log()


def V_perm(m, n):
    """sigma_m(P - J/n), closed form."""
    s = Fr(0)
    for d in range(m + 1):
        s += Fr((-1) ** (m - d) * factorial(m - d) * comb(n, d)
                * comb(n - d, m - d) ** 2, n ** (m - d))
    return s


def V9():
    log("V9  Theorem G end to end on the permutation pencil, k = 6 and 7")
    for n in (4, 5, 6):
        B = centre(perm_matrix(n), n)
        for m in range(2, n + 1):
            check(f"n={n} m={m}: closed form for sigma_m(P - J/n)",
                  V_perm(m, n) == sigma_bruteforce(B, n, m))
    cells = [(6, 110), (6, 497), (6, 4608), (7, 273), (7, 871), (7, 9800)]
    for k, n in cells:
        for lab, sgn, ss in (("A = (1-s)J/n + sP", 1,
                              [Fr(1, n - 1), Fr(1, 4), Fr(1, 2), Fr(1)]),
                             ("A = (1+s)J/n - sP", -1,
                              [Fr(1, n - 1), Fr(1, 2 * (n - 1))])):
            for s in ss:
                Q = s * s * (n - 1)
                F = sum(t_coeff(m, n, k) * (sgn * s) ** m * V_perm(m, n)
                        for m in range(2, k + 1))
                c = t_coeff(2, n, k) / 4
                check(f"k={k} n={n} {lab} s={s}: F >= c(n,k) Q",
                      F >= c * Q,
                      f"F/(cQ) = {float(F / (c * Q)):.6g}" if Q else "Q=0")
    log()


def V10():
    """Mutation controls.  Each fault must be caught by at least one check;
    with no fault injected the same checks must raise nothing."""
    global MUT, MUT_ACTIVE, MUT_FAILS, QUIET
    log("V10 mutation controls")

    def run_controls():
        V5()
        V8(ks=(6, 7, 8))

    faults = [({}, "no fault injected", False),
              ({"halve_C": True}, "C_m halved", True),
              ({"derangement_mass": True}, "D_m^2 replaced by ((m-1)!)^2", True),
              ({"finner_exponent": True}, "Finner exponent m/2 -> (m-1)/2", True)]
    results = []
    for fault, name, must_fire in faults:
        MUT, MUT_ACTIVE, MUT_FAILS, QUIET = fault, True, 0, True
        try:
            run_controls()
        finally:
            fired = MUT_FAILS
            MUT, MUT_ACTIVE, QUIET = {}, False, False
        results.append((name, must_fire, fired))
    # the fifth control is structural, not a code fault: claiming the
    # threshold one step lower must be refuted by the arithmetic itself.
    fired = 0
    for k, N, mixed in ((6, 497, False), (7, 871, False), (8, 1367, False),
                        (6, 110, True), (7, 273, True)):
        if Phi(N - 1, k, mixed) >= 1:
            fired += 1
    results.append(("each threshold lowered by one", True, fired))
    for name, must_fire, fired in results:
        if must_fire:
            check(f"control fires: {name}", fired > 0, f"{fired} checks caught it")
        else:
            check(f"control silent: {name}", fired == 0,
                  "no check raised anything")
    log()


def main():
    log("=" * 74)
    log("VERIFIER for Theorem G-uniform  (UNIFORM-G.md)")
    log("exact rational arithmetic; no float in any decision")
    log("=" * 74)
    log()
    V1()
    V2()
    V3()
    V4()
    V5()
    V6()
    V7()
    V8()
    V9()
    V10()
    log("=" * 74)
    log(f"TOTAL FAILURES: {FAIL}")
    log("VERDICT: " + ("ALL CHECKS PASS" if FAIL == 0 else "FAILURES PRESENT"))
    log("=" * 74)
    with open("results/graded_verify_uniformG.log", "w") as fh:
        fh.write("\n".join(OUT) + "\n")
    return 0 if FAIL == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
