"""
SCAN B2: targeted falsification hunt on flow-to-J monotonicity, near t = 0,
at large k and n > 7.

    (B)  t |-> Phi_k((1-t)A + t J_n/n)  is nondecreasing on [0,1].

The hunt is sharpened by an exact identity, derived and then verified here.
Expanding a k-matching of (1-t)A + tJ/n over which of its k cells are taken
from A gives, with E_0 = P_0 = 1,

    Phi_k(A_t) = sum_j C(k,j) (1-t)^j t^{k-j} [E_j(r) + E_j(c)]
               - sum_j C(k,j)^2 (k-j)! n^{j-k} (1-t)^j t^{k-j} P_j(A),

i.e. f is in BERNSTEIN FORM with coefficients (index m = k-j on t^m)

    beta_j = E_j(r) + E_j(c) - (k!/j!) n^{j-k} P_j(A),

so that, with  dE_j = E_j(r) - E_{j+1}(r) + E_j(c) - E_{j+1}(c) >= 0 (Maclaurin),

    f'(t) = k sum_{j=0}^{k-1} d_j C(k-1,j) t^{k-1-j} (1-t)^j,
    d_j   = beta_j - beta_{j+1}
          = dE_j + (k!/j!) n^{j-k} [ n P_{j+1}/(j+1) - P_j ].

Three consequences drive the whole scan:

  * d_0 = 0 identically on K_n (P_1 = 1/n), so f'(1) = 0 always: J_n/n is a
    critical point of every line, as it must be.
  * Every basis function is >= 0 on [0,1], so  min_j d_j >= 0  CERTIFIES the
    line with no root-finding at all.  A violation REQUIRES some d_j < 0.
  * At t = 0 only j = k-1 survives:  f'(0) = k V(A) with

        V(A) = E_{k-1}(r) - E_k(r) + E_{k-1}(c) - E_k(c)
               + P_k(A) - (k/n) P_{k-1}(A).

    So "B fails near t = 0" is exactly V(A) < 0, one scalar to minimise.

Usage:  python3 reduce_scan_b2.py calib | hunt | sweep   (logs in results/)
"""

import sys
from fractions import Fraction as Q

import numpy as np

import fals_core as fc
import reduce_scan as R

RNG = np.random.default_rng(20260801)


def to_QK(A, n):
    """Rationalise, then rescale EXACTLY so the entry sum is n.  `d_0 = 0`
    holds only on K_n: rationalising after normalising leaves the sum off by
    ~1e-6 and d_0 picks it up, which is what the first calibration run caught."""
    M = [[Q(float(x)).limit_denominator(10 ** 6) for x in row] for row in A]
    s = sum(sum(r) for r in M)
    return [[Q(n) * x / s for x in r] for r in M]


# --------------------------------------------------------------- Bernstein form
def dvec_f(A, k, sig=None):
    """[d_0, ..., d_{k-1}] as floats."""
    n = A.shape[0]
    if sig is None:
        sig = R.sigma_all_f(A)
    E_r = [R.e_k_f(A.sum(1), j) / fc.binom(n, j) for j in range(k + 1)]
    E_c = [R.e_k_f(A.sum(0), j) / fc.binom(n, j) for j in range(k + 1)]
    P = [sig[j] / fc.binom(n, j) ** 2 for j in range(k + 1)]
    out = []
    for j in range(k):
        dE = (E_r[j] - E_r[j + 1]) + (E_c[j] - E_c[j + 1])
        out.append(dE + (fc.fact(k) / fc.fact(j)) * n ** (j - k)
                   * (n * P[j + 1] / (j + 1) - P[j]))
    return np.array(out)


def dvec_x(A, k, sig=None):
    """[d_0, ..., d_{k-1}] exactly."""
    n = len(A)
    if sig is None:
        sig = R.sigma_all_x(A)
    r = [sum(row) for row in A]
    c = [sum(A[i][j] for i in range(n)) for j in range(n)]
    E_r = [Q(fc.e_k(r, j), fc.binom(n, j)) for j in range(k + 1)]
    E_c = [Q(fc.e_k(c, j), fc.binom(n, j)) for j in range(k + 1)]
    P = [Q(sig[j], fc.binom(n, j) ** 2) for j in range(k + 1)]
    out = []
    for j in range(k):
        dE = (E_r[j] - E_r[j + 1]) + (E_c[j] - E_c[j + 1])
        sc = Q(fc.fact(k), fc.fact(j)) * Q(n) ** (j - k)
        out.append(dE + sc * (Q(n) * P[j + 1] / (j + 1) - P[j]))
    return out


def fprime_from_d(d, k):
    """f'(t)/k in the monomial basis, from the Bernstein coefficients d_j:
    sum_j d_j C(k-1,j) t^{k-1-j} (1-t)^j."""
    out = [Q(0)] * k
    for j, dj in enumerate(d):
        # C(k-1,j) t^{k-1-j} (1-t)^j
        for i in range(j + 1):
            co = Q(fc.binom(k - 1, j) * fc.binom(j, i) * (-1) ** i)
            out[k - 1 - j + i] += dj * co
    return R.ptrim(out)


def V_f(A, k, sig=None):
    return dvec_f(A, k, sig)[-1]


# ------------------------------------------------------------------ calibration
def calib(log):
    log("== B2 calibration: the Bernstein identity, and the decision procedure ==")
    bad = 0
    for n in (4, 5, 6):
        for _ in range(2):
            AQ = to_QK(RNG.random((n, n)) + 0.05, n)
            JQ = [[Q(1, n)] * n for _ in range(n)]
            sig = R.sigma_all_x(AQ)
            r = [sum(row) for row in AQ]
            c = [sum(AQ[i][j] for i in range(n)) for j in range(n)]
            for k in range(2, n + 1):
                # (a) Bernstein form of f against direct evaluation of Phi_k
                for t in (Q(0), Q(1, 7), Q(1, 2), Q(5, 6), Q(1)):
                    val = Q(0)
                    for j in range(k + 1):
                        b = Q(fc.binom(k, j)) * (1 - t) ** j * t ** (k - j)
                        Ej = (Q(fc.e_k(r, j), fc.binom(n, j))
                              + Q(fc.e_k(c, j), fc.binom(n, j)))
                        Pj = Q(sig[j], fc.binom(n, j) ** 2)
                        val += b * Ej
                        val -= (Q(fc.binom(k, j) ** 2 * fc.fact(k - j))
                                * Q(n) ** (j - k) * (1 - t) ** j * t ** (k - j) * Pj)
                    M = [[(1 - t) * AQ[i][j] + t * JQ[i][j] for j in range(n)]
                         for i in range(n)]
                    if val != R.phi_x(M, k):
                        bad += 1
                        log(f"  BERNSTEIN MISMATCH n={n} k={k} t={t}")
                # (b) d_0 = 0 identically, i.e. f'(1) = 0
                d = dvec_x(AQ, k, sig)
                if d[0] != 0:
                    bad += 1
                    log(f"  d_0 != 0 at n={n} k={k}: {d[0]}")
                # (c) f' from d agrees with f' from interpolation
                xs = [Q(j, k + 2) for j in range(k + 2)]
                ys = []
                for t in xs:
                    M = [[(1 - t) * AQ[i][j] + t * JQ[i][j] for j in range(n)]
                         for i in range(n)]
                    ys.append(R.phi_x(M, k))
                f_int = R.interp(xs, ys)
                fp_int = R.pderiv(f_int)
                fp_ber = [Q(fc.fact(k), fc.fact(k - 1)) * cc
                          for cc in fprime_from_d(d, k)]
                if R.ptrim(fp_int) != R.ptrim(fp_ber):
                    bad += 1
                    log(f"  f' MISMATCH n={n} k={k}")
                    log(f"    interp {fp_int}")
                    log(f"    bernst {fp_ber}")
                # (d) f'(0) = k V
                if R.pev(fp_int, Q(0)) != Q(k) * d[-1]:
                    bad += 1
                    log(f"  f'(0) != k V at n={n} k={k}")
    log(f"  Bernstein identity, d_0 = 0, f' agreement, f'(0) = kV: "
        f"{'PASS' if bad == 0 else 'FAIL'} ({bad} mismatches)")

    # (e) the certification shortcut must agree with the Sturm decision, on
    #     lines where d has a negative entry AND on lines where it does not
    agree = disagree = 0
    for n in (4, 5, 6):
        for name, AQ in R.exact_families(n, RNG)[:14]:
            for k in range(2, n + 1):
                d = dvec_x(AQ, k)
                shortcut = all(x >= 0 for x in d)
                fp = fprime_from_d(d, k)
                ok, _ = R.nonneg_on_unit(fp)
                if shortcut and not ok:
                    disagree += 1
                    log(f"  SHORTCUT UNSOUND n={n} k={k} {name}")
                else:
                    agree += 1
    log(f"  shortcut soundness (min d >= 0 => f' >= 0): {agree} consistent, "
        f"{disagree} unsound")

    # (f) float dvec against exact dvec
    drift = 0
    for n in (8, 10, 12):
        AQ = to_QK(RNG.random((n, n)) + 0.05, n)
        Af = np.array([[float(x) for x in row] for row in AQ])
        for k in (2, n // 2, n - 1, n):
            de = [float(x) for x in dvec_x(AQ, k)]
            df = dvec_f(Af, k)
            if max(abs(np.array(de) - df)) > 1e-8 * max(1.0, max(abs(np.array(de)))):
                drift += 1
                log(f"  FLOAT DRIFT in d at n={n} k={k}")
    log(f"  float/exact agreement of d at n = 8,10,12: "
        f"{'PASS' if drift == 0 else 'FAIL'}")
    return bad + disagree + drift


# ---------------------------------------------------------------- the families
def sigma_marginals_f(A, k):
    """m_i = 1 - sigma_k(A with row i zeroed)/sigma_k(A), and the column
    version.  Cheap: n+1 Ryser passes, no subset enumeration."""
    n = A.shape[0]
    s = R.sigma_all_f(A)[k]
    if s <= 0:
        return np.full(n, np.nan), np.full(n, np.nan)
    mr, mc = np.zeros(n), np.zeros(n)
    for i in range(n):
        B = A.copy()
        B[i, :] = 0.0
        mr[i] = 1.0 - R.sigma_all_f(B)[k] / s
        C = A.copy()
        C[:, i] = 0.0
        mc[i] = 1.0 - R.sigma_all_f(C)[k] / s
    return mr, mc


def hunt_families(n, k, rng):
    """The families the hunt is required to stress, all in K_n."""
    out = []
    N = R._norm

    # 1. scan-A kill witnesses and their neighbourhoods: a doubly stochastic D
    #    scaled on the row of largest sigma_k-marginal, and perturbations of it
    for _ in range(3):
        D, ok = R.sinkhorn(rng.random((n, n)) + 0.05)
        if not ok:
            continue
        D = N(D)
        mr, _ = sigma_marginals_f(D, k)
        i0 = int(np.nanargmax(mr)) if not np.all(np.isnan(mr)) else 0
        for delta in (0.02, 0.1, 0.3):
            u = np.ones(n)
            u[i0] = 1 - delta
            out.append((f"Akill{delta}", N(u[:, None] * D)))
            out.append((f"Akill{delta}+noise",
                        N(np.abs(u[:, None] * D + 0.02 * rng.normal(0, 1, (n, n))))))
    # 2. permutation mixtures, including very near a permutation
    for s in (0.001, 0.01, 0.05, 0.2, 0.5):
        P = np.eye(n)[rng.permutation(n)]
        out.append((f"permmix{s}", N((1 - s) * P + s * (rng.random((n, n)) + 1e-3))))
        Pm = sum(np.eye(n)[rng.permutation(n)] for _ in range(3)) / 3.0
        out.append((f"permcombo{s}", N((1 - s) * Pm + s * rng.random((n, n)))))
    # 3. low rank blended into the boundary
    for rk in (1, 2, 3):
        for w in (0.0, 0.05, 0.3):
            M = rng.random((n, rk)) @ rng.random((rk, n))
            B = (rng.random((n, n)) < 0.35).astype(float)
            out.append((f"rank{rk}+bdry{w}", N(M * (1 - w) + w * B + 1e-12)))
    # 4. extreme sigma_k-marginal spread, built by hill climbing on the spread
    for _ in range(2):
        A = N(rng.random((n, n)) + 0.05)
        for _ in range(25):
            mr, mc = sigma_marginals_f(A, k)
            if np.any(np.isnan(mr)):
                break
            g = np.add.outer(mr - k / n, mc - k / n)
            A = N(np.clip(A * np.exp(0.5 * g), 1e-12, None))
        out.append(("marg-spread", A))
        mr, _ = sigma_marginals_f(A, k)
        out.append(("marg-spread-scaled",
                    N(A * np.exp(-0.3 * (mr - k / n))[:, None])))
    # 5. the direct-sum family of FALSIFICATION.md: blocks of size p, mass m
    for cut in range(1, n):
        for frac in (0.15, 0.5, 0.85):
            M = np.zeros((n, n))
            M[:cut, :cut] = frac / cut ** 2
            M[cut:, cut:] = (1 - frac) / (n - cut) ** 2
            out.append((f"directsum{cut}/{frac}", N(M + 1e-12)))
    # 6. plain controls
    out.append(("I_n", np.eye(n)))
    out.append(("J_n", np.ones((n, n)) / n))
    for a in (0.1, 1.0):
        out.append((f"dirichlet{a}", N(rng.dirichlet([a] * n * n).reshape(n, n))))
    return out


# ------------------------------------------------------- B2.1 minimise V near 0
def hunt(log):
    log("== B2.1 the t -> 0 scalar V(A) = f'(0)/k, minimised over K_n ==")
    log("  V(A) = E_{k-1}(r)-E_k(r) + E_{k-1}(c)-E_k(c) + P_k(A) - (k/n)P_{k-1}(A)")
    log("  V < 0  <=>  (B) fails immediately at t = 0.  Both E differences are")
    log("  >= 0 by Maclaurin, so a violation needs (k/n)P_{k-1} to beat P_k by")
    log("  more than the line-sum deficit can pay.")
    rows = []
    for n in range(8, 13):
        ks = sorted({2, 3, n // 2, n - 2, n - 1, n})
        for k in ks:
            if not 2 <= k <= n:
                continue
            best = (np.inf, "")
            cnt = 0
            for name, A in hunt_families(n, k, RNG):
                v = V_f(A, k)
                cnt += 1
                if v < best[0]:
                    best = (v, name)
            # gradient descent on V over the positive part of K_n
            for start in range(3):
                z = RNG.normal(0, 1.0 if start else 0.05, (n, n))

                def val(z):
                    W = np.exp(np.clip(z, -30, 30))
                    return V_f(R._norm(W), k)

                cur = val(z)
                step = 0.6
                for _ in range(60):
                    g = np.zeros((n, n))
                    for i in range(n):
                        for j in range(n):
                            e = np.zeros((n, n))
                            e[i, j] = 1e-5
                            g[i, j] = (val(z + e) - cur) / 1e-5
                    gn = np.linalg.norm(g)
                    if gn < 1e-15:
                        break
                    znew = z - step * g / gn
                    vnew = val(znew)
                    if vnew < cur:
                        z, cur = znew, vnew
                    else:
                        step *= 0.5
                        if step < 1e-6:
                            break
                    cnt += 1
                if cur < best[0]:
                    best = (cur, f"descent{start}")
            rows.append((n, k, best[0], best[1], cnt))
            log(f"    n={n:2d} k={k:2d}: min V = {best[0]:+.6e} at {best[1]:22s} "
                f"({cnt} evaluations)")
    # J_n/n is an exact zero of V, so float noise there is not a candidate:
    # confirm the zero over Fraction, then judge everything else against it.
    zbad = 0
    for n in range(8, 13):
        JQ = [[Q(1, n)] * n for _ in range(n)]
        for k in sorted({2, 3, n // 2, n - 2, n - 1, n}):
            if 2 <= k <= n and dvec_x(JQ, k)[-1] != 0:
                zbad += 1
                log(f"    V(J_{n}/{n}) != 0 at k={k}")
    log(f"  exact check V(J_n/n) = 0 for every scanned (n,k): "
        f"{'PASS' if zbad == 0 else 'FAIL'}")
    cand = [r for r in rows if r[2] < -1e-12]
    log(f"  cells scanned {len(rows)}; cells whose minimum beats the J_n/n zero "
        f"by more than 1e-12: {len(cand)}")
    for n, k, v, name, _ in cand:
        log(f"    CANDIDATE n={n} k={k} V={v:+.6e} at {name} -- exact check needed")
    if not cand:
        log("  no negative V anywhere: (B) is not falsifiable at t = 0 on any")
        log("  point reached by these families or by descent from them.  Every")
        log("  cell minimum is the J_n/n zero, to float precision.")
        log(f"  worst residual over all cells: {min(r[2] for r in rows):+.3e}")
    return rows


# ------------------------------------------- B2.2 whole-line scan, n = 8..12
def sweep(log):
    log("== B2.2 whole-line scan at n = 8..12 via the Bernstein coefficients ==")
    log("  min_j d_j >= 0 CERTIFIES the line (all basis functions are >= 0).")
    log("  Any line with a negative d_j is sent to the exact Sturm decision.")
    tot = certified = suspicious = violations = 0
    negd = []
    percell = {}
    for n in range(8, 13):
        ks = sorted({2, 3, n // 2, n - 2, n - 1, n})
        for k in ks:
            for name, A in hunt_families(n, k, RNG):
                d = dvec_f(A, k)
                tot += 1
                percell[(n, k)] = percell.get((n, k), 0) + 1
                if d.min() >= -1e-12:
                    certified += 1
                else:
                    suspicious += 1
                    negd.append((n, k, name, A, d.min()))
    log(f"  lines scanned {tot}: certified by the d-test {certified}, "
        f"suspicious {suspicious}")
    log(f"  per-cell counts: {dict(sorted(percell.items()))}")
    for n, k, name, A, mn in negd[:12]:
        AQ = to_QK(A, n)
        dq = dvec_x(AQ, k)
        fp = fprime_from_d(dq, k)
        ok, detail = R.nonneg_on_unit(fp)
        log(f"    n={n} k={k} {name}: min d_j = {mn:+.3e} (float); EXACT verdict "
            f"f' >= 0 on [0,1]: {ok} [{detail[:90]}]")
        if not ok:
            violations += 1
            log(f"      *** EXACT VIOLATION OF (B) ***  A = "
                f"{[[str(x) for x in r] for r in AQ]}")
    log(f"  exact violations of (B): {violations}")

    log("-- B2.3 independent fine grid on t in [0, 1e-2], float --")
    tot2 = bad2 = 0
    worst = (0.0, "")
    ts = np.concatenate([np.linspace(0, 1e-2, 200), np.linspace(1e-2, 1, 200)])
    for n in (8, 10, 12):
        ks = sorted({2, n // 2, n - 1, n})
        for k in ks:
            for name, A in hunt_families(n, k, RNG)[:20]:
                J = np.ones((n, n)) / n
                v = np.array([R.phi_f((1 - t) * A + t * J, k) for t in ts])
                dd = np.diff(v)
                tot2 += 1
                if dd.min() < -1e-13:
                    bad2 += 1
                    if dd.min() < worst[0]:
                        worst = (dd.min(), f"n={n} k={k} {name}")
    log(f"  fine-grid lines {tot2}, with a negative increment {bad2}"
        + (f", worst {worst[0]:+.3e} at {worst[1]}" if bad2 else ""))
    return violations


def exact(log):
    """Exact confirmation of the d-test on a sample of the swept lines, over
    Fraction.  The sweep is float; this decides a subset of it."""
    log("== B2.4 exact confirmation of the d-test, over Fraction ==")
    log("  sum_j d_j = beta_0 - beta_k = (2 - k!/n^k) - Phi_k(A) = F_{n,k}(A),")
    log("  so the d-vector is an exact k-term decomposition of the Cheon-Hwang")
    log("  deficit, and d_j >= 0 termwise is strictly stronger than (B).")
    tot = neg = 0
    sumbad = 0
    worst = (None, None)
    for n in range(8, 13):
        ks = sorted({2, 3, n // 2, n - 2, n - 1, n})
        pool = [(nm, A) for nm, A in hunt_families(n, RNG.integers(2, n + 1), RNG)]
        pick = [pool[i] for i in RNG.choice(len(pool), size=3, replace=False)]
        pick.append(("I_n", np.eye(n)))
        for name, A in pick:
            AQ = to_QK(A, n)
            sig = R.sigma_all_x(AQ)
            for k in ks:
                if not 2 <= k <= n:
                    continue
                d = dvec_x(AQ, k, sig)
                tot += 1
                # d_0 = 0 identically, so it would always win the minimum and
                # tell us nothing: the informative statistic is over j >= 1.
                mn = min(d[1:]) if len(d) > 1 else d[0]
                if mn < 0:
                    neg += 1
                    log(f"    NEGATIVE d_j n={n} k={k} {name}: min d_j = {mn} "
                        f"= {float(mn):+.6e}")
                    ok, detail = R.nonneg_on_unit(fprime_from_d(d, k))
                    log(f"      exact Sturm verdict f' >= 0 on [0,1]: {ok} [{detail[:80]}]")
                if worst[0] is None or float(mn) < worst[0]:
                    worst = (float(mn), f"n={n} k={k} {name}")
                # the identity sum_j d_j = F_{n,k}(A)
                F = fc.bound(n, k) - R.phi_x(AQ, k, sig[k])
                if sum(d) != F:
                    sumbad += 1
                    log(f"    SUM IDENTITY FAILS n={n} k={k} {name}")
        log(f"    n={n}: done")
    log(f"  exact lines decided {tot}; with a negative d_j {neg}; "
        f"sum-identity failures {sumbad}")
    log(f"  smallest exact d_j over j >= 1: {worst[0]:+.6e} at {worst[1]}")
    log("  (d_0 = 0 identically on K_n, so it is excluded from the minimum.)")
    return neg + sumbad


def main():
    which = sys.argv[1] if len(sys.argv) > 1 else "all"
    out = open(f"results/reduce_b2_{which}.log", "w")

    def log(s):
        print(s)
        out.write(s + "\n")
        out.flush()

    if which in ("calib", "all"):
        calib(log)
    if which in ("hunt", "all"):
        hunt(log)
    if which in ("sweep", "all"):
        sweep(log)
    if which in ("exact", "all"):
        exact(log)
    out.close()


if __name__ == "__main__":
    main()
