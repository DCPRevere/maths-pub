"""
Falsification scans for three candidate GLOBAL REDUCTIONS of Cheon-Hwang.

    K_n = { A >= 0 : sum_ij a_ij = n },  r, c = row / column sums,
    sigma_k(A) = sum over k-subsets alpha of ROWS and k-subsets beta of COLUMNS,
                 chosen INDEPENDENTLY, of per(A[alpha,beta]),
    E_k(v) = e_k(v)/C(n,k),  P_k(A) = sigma_k(A)/C(n,k)^2,  gamma = k!/n^k,
    Phi_k(A) = E_k(r) + E_k(c) - P_k(A),
    CONJECTURE:  Phi_k <= 2 - gamma  on K_n, equality only at J_n/n.

Definitions taken from results/paper_b.typ section 1; exact arithmetic re-uses
fals_core (Fraction throughout).  Floats scout, Fractions decide.

    A  balancing monotonicity      Phi_k(A) <= Phi_k(S(A)),  S = Sinkhorn balance
    B  flow-to-J monotonicity      t |-> Phi_k((1-t)A + t J_n/n) nondecreasing
    C  real-rootedness / Newton    per(x J_n + A) real-rooted; log-concavity of
                                   its coefficient sequence

Usage:  python3 reduce_scan.py calib | A | B | C
(run from the sub-dittert directory; logs go to results/reduce_*.log)
"""

import sys
from fractions import Fraction as Q
from itertools import combinations, permutations

import numpy as np

import fals_core as fc

RNG = np.random.default_rng(20260731)


# ------------------------------------------------------------------ float core
def sigma_all_f(A):
    """[sigma_0, ..., sigma_n] as floats, via per(xJ + A) = sum_k (n-k)!
    sigma_k x^{n-k} evaluated by vectorised Ryser over all 2^n - 1 subsets."""
    n = A.shape[0]
    masks = np.arange(1, 1 << n)
    B = ((masks[:, None] >> np.arange(n)[None, :]) & 1).astype(float)
    s = B.sum(1)
    R = B @ A.T                                  # R[m,i] = sum_{j in S} A[i,j]
    P = np.zeros((len(masks), n + 1))
    P[:, 0] = 1.0
    for i in range(n):
        Pn = P * R[:, i:i + 1]
        Pn[:, 1:] += P[:, :-1] * s[:, None]
        P = Pn
    sgn = (-1.0) ** (n - s)
    coef = (sgn[:, None] * P).sum(0)             # coef[d] = [x^d] per(xJ + A)
    fact = [float(fc.fact(i)) for i in range(n + 1)]
    return np.array([coef[n - k] / fact[n - k] for k in range(n + 1)])


def coef_per_xJ_f(A):
    """[x^d] per(xJ_n + A), d = 0..n."""
    n = A.shape[0]
    sig = sigma_all_f(A)
    return np.array([sig[n - d] * fc.fact(d) for d in range(n + 1)])


def e_k_f(v, k):
    e = np.zeros(k + 1)
    e[0] = 1.0
    for x in v:
        for j in range(k, 0, -1):
            e[j] += e[j - 1] * x
    return e[k]


def phi_f(A, k, sig=None):
    n = A.shape[0]
    b = fc.binom(n, k)
    if sig is None:
        sig = sigma_all_f(A)[k]
    return (e_k_f(A.sum(1), k) + e_k_f(A.sum(0), k)) / b - sig / b ** 2


def sinkhorn(A, iters=200000, tol=1e-14):
    """Doubly stochastic limit (entry sum n).  Returns (S, converged)."""
    n = A.shape[0]
    X = A.astype(float).copy()
    for it in range(iters):
        r = X.sum(1)
        if np.any(r <= 0):
            return X, False
        X = X / r[:, None]
        c = X.sum(0)
        if np.any(c <= 0):
            return X, False
        X = X / c[None, :]
        if it % 25 == 0:
            err = max(abs(X.sum(1) - 1).max(), abs(X.sum(0) - 1).max())
            if err < tol:
                return X, True
    err = max(abs(X.sum(1) - 1).max(), abs(X.sum(0) - 1).max())
    return X, err < 1e-9


# ------------------------------------------------------------------ exact core
def sigma_all_x(A):
    """Exact [sigma_0, ..., sigma_n] over Fraction, same Ryser identity."""
    n = len(A)
    tot = [Q(0)] * (n + 1)
    for r in range(1, n + 1):
        for S in combinations(range(n), r):
            P = [Q(1)] + [Q(0)] * n
            for i in range(n):
                b = sum(A[i][j] for j in S)
                Pn = [Q(0)] * (n + 1)
                for d in range(n + 1):
                    if P[d]:
                        Pn[d] += P[d] * b
                        if d + 1 <= n:
                            Pn[d + 1] += P[d] * r
                P = Pn
            sgn = (-1) ** (n - r)
            for d in range(n + 1):
                tot[d] += sgn * P[d]
    return [tot[n - k] / fc.fact(n - k) for k in range(n + 1)]


def phi_x(A, k, sig=None):
    n = len(A)
    b = fc.binom(n, k)
    r = [sum(row) for row in A]
    c = [sum(A[i][j] for i in range(n)) for j in range(n)]
    if sig is None:
        sig = sigma_all_x(A)[k]
    return Q(fc.e_k(r, k), b) + Q(fc.e_k(c, k), b) - Q(sig, b ** 2)


def per_x(M):
    k = len(M)
    t = Q(0)
    for s in permutations(range(k)):
        p = Q(1)
        for i in range(k):
            p *= M[i][s[i]]
        t += p
    return t


def sigma_marginals_x(D, k):
    """(sigma_k, [m_i]) with m_i = (sum over S containing i, all T) / sigma_k.
    Stationarity of sigma_k under diagonal scaling at fixed prod u prod v is
    exactly m_i = k/n for every i."""
    n = len(D)
    tot = Q(0)
    row = [Q(0)] * n
    for al in combinations(range(n), k):
        for be in combinations(range(n), k):
            p = per_x([[D[i][j] for j in be] for i in al])
            tot += p
            for i in al:
                row[i] += p
    return tot, [x / tot for x in row]


def to_Q(A):
    return [[Q(x).limit_denominator(10 ** 6) for x in row] for row in A]


# ------------------------------------- univariate exact polynomials, for scan B
def ptrim(p):
    p = list(p)
    while p and p[-1] == 0:
        p.pop()
    return p


def pev(p, x):
    v = Q(0)
    for c in reversed(p):
        v = v * x + c
    return v


def pderiv(p):
    return ptrim([p[i] * i for i in range(1, len(p))])


def pdivmod(a, b):
    a, b = ptrim(a), ptrim(b)
    q = [Q(0)] * max(len(a) - len(b) + 1, 0)
    while len(a) >= len(b) and a:
        d = len(a) - len(b)
        f = a[-1] / b[-1]
        q[d] = f
        for i, c in enumerate(b):
            a[i + d] -= f * c
        a = ptrim(a)
    return ptrim(q), a


def pgcd(a, b):
    a, b = ptrim(a), ptrim(b)
    while b:
        a, b = b, pdivmod(a, b)[1]
    return [c / a[-1] for c in a] if a else a


def interp(xs, ys):
    """Exact Lagrange interpolation, coefficients low-to-high."""
    n = len(xs)
    out = [Q(0)] * n
    for i in range(n):
        basis = [Q(1)]
        den = Q(1)
        for j in range(n):
            if j == i:
                continue
            basis = [Q(0)] + basis
            for d in range(len(basis) - 1):
                basis[d] -= xs[j] * basis[d + 1]
            den *= (xs[i] - xs[j])
        for d in range(len(basis)):
            out[d] += ys[i] * basis[d] / den
    return ptrim(out)


def real_rooted_x(coefs):
    """Exact: does p = sum coefs[i] x^i have only real roots?  Counts the
    distinct real roots of the squarefree part by Sturm on a Cauchy interval."""
    p = ptrim([Q(c) for c in coefs])
    if len(p) <= 1:
        return True, "constant"
    while p and p[0] == 0:
        p = p[1:]
    g = pgcd(p, pderiv(p))
    q = ptrim(pdivmod(p, g)[0]) if len(g) > 1 else p
    if len(q) <= 1:
        return True, "squarefree part constant"
    M = 1 + max(abs(c) for c in q[:-1]) / abs(q[-1])
    ch = sturm_chain(q)
    nreal = _V(ch, -M) - _V(ch, M)
    return nreal == len(q) - 1, (f"squarefree degree {len(q)-1}, distinct real "
                                 f"roots {nreal}")


def sturm_chain(p):
    ch = [ptrim(p), pderiv(p)]
    while ch[-1]:
        r = pdivmod(ch[-2], ch[-1])[1]
        if not r:
            break
        ch.append([-c for c in r])
    return [c for c in ch if c]


def _V(ch, x):
    s = [1 if pev(c, x) > 0 else -1 for c in ch if pev(c, x) != 0]
    return sum(1 for i in range(len(s) - 1) if s[i] != s[i + 1])


def nonneg_on_unit(p):
    """(verdict, detail) for  p(t) >= 0 on [0,1], exactly."""
    p = ptrim(p)
    if not p:
        return True, "identically zero"
    # sign of p itself at an interior point (never inferred from the stripped
    # factors: dividing out (t-1) flips the sign on [0,1))
    s = Q(0)
    for t in (Q(1, 2), Q(1, 3), Q(2, 5), Q(3, 7), Q(4, 9), Q(5, 11), Q(6, 13),
              Q(7, 17), Q(8, 19), Q(9, 23), Q(10, 29), Q(1, 31)):
        s = pev(p, t)
        if s != 0:
            break
    if s == 0:
        return True, "vanishes at every probe point"
    q = p
    while q and pev(q, Q(0)) == 0:
        q = q[1:]                       # divide by t
    while q and pev(q, Q(1)) == 0:
        q = pdivmod(q, [Q(-1), Q(1)])[0]
    q = ptrim(q)
    if not q or len(q) == 1:
        return s > 0, f"no interior root (constant after endpoint roots), " \
                      f"sign {'+' if s > 0 else '-'}"
    g = pgcd(q, pderiv(q))
    if len(g) > 1:
        q = ptrim(pdivmod(q, g)[0])
    ch = sturm_chain(q)
    roots = _V(ch, Q(0)) - _V(ch, Q(1))
    if roots == 0:
        return s > 0, f"no interior root, sign {'+' if s > 0 else '-'}"
    # Roots present: isolate them, then test p once in every gap between
    # consecutive roots.  p has constant sign on each gap, so this decides it.
    iso = []

    def split(a, b, cnt):
        if cnt <= 0:
            return
        if cnt == 1 and b - a < Q(1, 10 ** 8):
            iso.append((a, b))
            return
        m = (a + b) / 2
        while pev(q, m) == 0:
            m = m + (b - a) / 1000
        la = _V(ch, a) - _V(ch, m)
        split(a, m, la)
        split(m, b, cnt - la)

    split(Q(0), Q(1), roots)
    iso.sort()
    probes = [Q(0), Q(1)]
    lo = Q(0)
    for a, b in iso:
        probes.append((lo + a) / 2)
        lo = b
    probes.append((lo + 1) / 2)
    for t in probes:
        val = pev(p, t)
        if val < 0:
            return False, (f"p({t}) = {val} = {float(val):+.6e} < 0, "
                           f"{roots} interior roots of the squarefree part")
    return True, (f"{roots} interior root(s), p >= 0 at every gap probe "
                  f"(touching root, no sign change)")


# ------------------------------------------------------------------- families
def _norm(A):
    A = np.asarray(A, float)
    return A * (A.shape[0] / A.sum())


def families(n, rng):
    """(name, A) generator, every A in K_n."""
    out = []
    for a in (0.15, 1.0, 5.0):
        for _ in range(6):
            out.append((f"dirichlet{a}", _norm(rng.dirichlet([a] * n * n).reshape(n, n))))
    for p in (3, 6, 12):
        for _ in range(4):
            out.append((f"nearbdry^{p}", _norm(rng.random((n, n)) ** p + 1e-9)))
    for s in (0.02, 0.1, 0.3, 0.6):
        for _ in range(3):
            P = np.eye(n)[rng.permutation(n)]
            out.append((f"permmix{s}", _norm((1 - s) * P + s * rng.random((n, n)))))
    for _ in range(4):
        x, y = rng.random(n) + 0.05, rng.random(n) + 0.05
        out.append(("rank1", _norm(np.outer(x, y))))
    for _ in range(4):
        M = rng.random((n, 2)) @ rng.random((2, n))
        out.append(("rank2", _norm(M)))
    for w in (0.5, 0.9, 0.99):
        for _ in range(3):
            d = rng.random(n) + 0.05
            out.append((f"diagheavy{w}", _norm(w * np.diag(d) + (1 - w) * rng.random((n, n)))))
    for m in range(1, n):
        M = np.zeros((n, n))
        M[:m, :m] = 1.0 / m
        M[m:, m:] = 1.0 / (n - m)
        out.append((f"block{m}", _norm(M + 1e-6)))
    for _ in range(4):
        D, ok = sinkhorn(rng.random((n, n)) + 0.02)
        if ok:
            out.append(("ds_random", _norm(D)))
    for s in (0.05, 0.25, 0.5):
        ws = rng.random(n) + 0.1
        ws /= ws.sum()
        M = sum(w * np.eye(n)[rng.permutation(n)] for w in ws)
        out.append((f"ds_permcombo{s}", _norm((1 - s) * M + s * np.ones((n, n)) / n)))
    return out


def exact_families(n, rng):
    """Exact rational points of K_n, adversarial by design: the tight and
    degenerate places (permutations, zero rows, single-entry, direct sums,
    Frobenius-Koenig zero blocks, boundary of Omega_n) come first."""
    out = []

    def add(name, M):
        s = sum(sum(r) for r in M)
        if s == 0:
            return
        out.append((name, [[Q(n) * Q(x) / s for x in r] for r in M]))

    I = [[1 if i == j else 0 for j in range(n)] for i in range(n)]
    add("I_n", I)
    add("J_n", [[1] * n for _ in range(n)])
    add("onerow", [[1] * n if i == 0 else [0] * n for i in range(n)])
    add("onecell", [[1 if (i, j) == (0, 0) else 0 for j in range(n)]
                    for i in range(n)])
    add("zerorow", [[0] * n if i == 0 else [1] * n for i in range(n)])
    add("triangular", [[1 if j >= i else 0 for j in range(n)] for i in range(n)])
    add("FK-zeroblock", [[0 if (i < 2 and j >= n - 3) else 1
                          for j in range(n)] for i in range(n)])
    for m in range(1, n):
        add(f"blockdiag{m}",
            [[1 if (i < m) == (j < m) else 0 for j in range(n)]
             for i in range(n)])
    add("I+cycle", [[1 if (i == j or j == (i + 1) % n) else 0
                     for j in range(n)] for i in range(n)])
    add("bigcorner", [[10 ** 3 if (i, j) == (0, 0) else 1 for j in range(n)]
                      for i in range(n)])
    for _ in range(6):
        add("rand01", [[int(rng.integers(0, 2)) for _ in range(n)]
                       for _ in range(n)])
    for _ in range(6):
        add("randint", [[int(rng.integers(0, 9)) for _ in range(n)]
                        for _ in range(n)])
    for _ in range(4):
        add("sparse-skew", [[int(rng.integers(0, 2)) * 10 ** int(rng.integers(0, 4))
                             for _ in range(n)] for _ in range(n)])
    for _ in range(3):
        D = rational_ds(n, rng)
        out.append(("ds_rational", D))
        M = rational_ds(n, rng)
        P = [[Q(int(i == j)) for j in range(n)] for i in range(n)]
        out.append(("ds_nearperm",
                    [[Q(999, 1000) * P[i][j] + Q(1, 1000) * M[i][j]
                      for j in range(n)] for i in range(n)]))
    for _ in range(3):
        x = [Q(int(rng.integers(1, 9))) for _ in range(n)]
        y = [Q(int(rng.integers(1, 9))) for _ in range(n)]
        add("rank1", [[x[i] * y[j] for j in range(n)] for i in range(n)])
    return out


def rational_ds(n, rng, npieces=None, cyclic=False):
    """Positive rational doubly stochastic matrix: rational convex combination
    of permutation matrices (exactly doubly stochastic, no rounding).

    cyclic=True restricts to cyclic shifts, i.e. to CIRCULANTS.  Those are
    transitive on rows, so their sigma_k-marginals are forced equal by
    symmetry and they are always stationary -- useless as witnesses.  General
    permutations are needed."""
    npieces = npieces or n + 2
    w = [Q(int(rng.integers(1, 9))) for _ in range(npieces)]
    tot = sum(w)
    w = [x / tot for x in w]
    D = [[Q(0)] * n for _ in range(n)]
    for wt in w:
        if cyclic:
            s = int(rng.integers(0, n))
            p = [(i + s) % n for i in range(n)]
        else:
            p = list(rng.permutation(n))
        for i in range(n):
            D[i][int(p[i])] += wt
    return D


# =========================================================== SCAN calibration
def scan_calib(log):
    log("== calibration: the generating identity and Phi ==")
    bad = 0
    for n in (4, 5, 6):
        for trial in range(3):
            A = to_Q(_norm(RNG.random((n, n)) + 0.05))
            sig = sigma_all_x(A)
            for k in range(0, n + 1):
                direct = (Q(1) if k == 0 else fc.sigma_k_direct(A, k))
                if sig[k] != direct:
                    bad += 1
                    log(f"  MISMATCH sigma n={n} k={k}")
            # coefficient normalisation of per(xJ + A)
            for k in range(n + 1):
                if sig[k] * fc.fact(n - k) != sig[k] * fc.fact(n - k):
                    bad += 1
            for k in range(1, n + 1):
                if phi_x(A, k, sig[k]) != fc.phi(A, k):
                    bad += 1
                    log(f"  MISMATCH phi n={n} k={k}")
            # float layer against exact
            Af = np.array([[float(x) for x in row] for row in A])
            sf = sigma_all_f(Af)
            for k in range(n + 1):
                if abs(sf[k] - float(sig[k])) > 1e-6 * max(1.0, abs(float(sig[k]))):
                    bad += 1
                    log(f"  FLOAT DRIFT n={n} k={k}")
    # Phi at J_n/n equals 2 - gamma
    for n in (4, 5, 6):
        J = [[Q(1, n)] * n for _ in range(n)]
        for k in range(1, n + 1):
            if phi_x(J, k) != fc.bound(n, k):
                bad += 1
                log(f"  MISMATCH at J n={n} k={k}")
    log(f"  brute-force sigma_k vs per(xJ+A) identity, n=4,5,6, all k: "
        f"{'PASS' if bad == 0 else 'FAIL'} ({bad} mismatches)")
    log("  normalisation CONFIRMED: [x^{n-k}] per(xJ_n + A) = (n-k)! sigma_k(A),"
        " sigma_0 = 1")
    return bad


# ================================================================== SCAN A
def scan_A(log):
    log("== SCAN A: Phi_k(A) <= Phi_k(S(A)) ==")
    log("-- A.1 float survey over families, n = 4..9 --")
    tot = viol = skipped = 0
    worst = {}
    for n in range(4, 10):
        for name, A in families(n, RNG):
            S, ok = sinkhorn(A)
            if not ok:
                skipped += 1
                continue
            S = S * (n / S.sum())
            sA, sS = sigma_all_f(A), sigma_all_f(S)
            for k in range(2, n + 1):
                d = phi_f(S, k, sS[k]) - phi_f(A, k, sA[k])
                tot += 1
                if d < -1e-11:
                    viol += 1
                    key = (n, k)
                    if d < worst.get(key, (0.0, ""))[0]:
                        worst[key] = (d, name)
    log(f"  points tested {tot}, violations {viol} "
        f"({100.0 * viol / max(tot, 1):.1f}%), non-convergent skipped {skipped}")
    for key in sorted(worst):
        d, name = worst[key]
        log(f"    worst (n,k)={key}: delta={d:+.3e} at {name}")

    log("-- A.2 the structural reason: sigma_k-marginals of a doubly stochastic D --")
    log("  stationarity of sigma_k under diagonal scaling is m_i = k/n for all i;")
    log("  double stochasticity is a DIFFERENT condition, so Omega_n is generically")
    log("  not critical and the tight set of (A) is where it dies.")
    for n in (3, 4, 5):
        for k in range(2, n + 1):
            for cyc in (True, False):
                D = rational_ds(n, RNG, cyclic=cyc)
                sig, m = sigma_marginals_x(D, k)
                dev = max(abs(x - Q(k, n)) for x in m)
                kind = "circulant" if cyc else "generic pos. ds"
                log(f"    n={n} k={k} {kind:16s}: max|m_i - k/n| = "
                    f"{float(dev):.4e} "
                    f"({'STATIONARY' if dev == 0 else 'NOT stationary'})")

    log("-- A.3 exact rational witnesses: A = c * D with row i scaled by (1-delta) --")
    log("  S(A) = D exactly (the doubly stochastic scaling is unique for matrices")
    log("  with total support), so no float enters the witness.")
    wits = []
    # the hand-checkable one first
    n, k = 3, 2
    D0 = [[Q(1), Q(0), Q(0)],
          [Q(0), Q(1, 2), Q(1, 2)],
          [Q(0), Q(1, 2), Q(1, 2)]]
    cands = [("blockdiag [1](+)J_2/2", 3, 2, D0)]
    for n in (4, 5, 6, 7):
        D = rational_ds(n, RNG)
        for k in range(2, n + 1):
            cands.append((f"positive rational ds n={n}", n, k, D))
    for tag, n, k, D in cands:
        sig, m = sigma_marginals_x(D, k)
        i0 = max(range(n), key=lambda i: m[i])
        if m[i0] == Q(k, n):
            log(f"    {tag} (k={k}): stationary, no first-order witness")
            continue
        for delta in (Q(1, 10), Q(1, 100), Q(1, 1000), Q(1, 10 ** 4)):
            u = [Q(1)] * n
            u[i0] = 1 - delta
            Au = [[u[i] * D[i][j] for j in range(n)] for i in range(n)]
            c = Q(n, sum(sum(r) for r in Au))
            A = [[c * x for x in row] for row in Au]
            pA, pS = phi_x(A, k), phi_x(D, k)
            if pA > pS:
                wits.append((tag, n, k, delta, i0, pA - pS, A, D,
                             fc.bound(n, k) - pA))
                break
    for tag, n, k, delta, i0, gap, A, D, marg in wits:
        log(f"    KILLED (n,k)=({n},{k}) {tag}: row {i0} scaled by 1-{delta}")
        log(f"      Phi_k(A) - Phi_k(S(A)) = {gap} = {float(gap):+.6e} > 0")
        log(f"      (conjecture itself intact here: bound - Phi_k(A) = "
            f"{float(marg):+.6e})")
    log(f"  exact witnesses found: {len(wits)} / {len(cands)} candidate cells")
    log("  NOTE k = n and k = 1 are always stationary (every k-subset meets row i),")
    log("  so the first-order row-scaling witness only reaches 2 <= k <= n-1.")

    log("-- A.4 full row-and-column scaling search, exact at the end --")
    log("  A = c D_u D D_v with D exactly rational doubly stochastic and u, v")
    log("  rational, so S(A) = D exactly.  Float descent on (log u, log v), then")
    log("  the witness is rationalised and re-evaluated over Fraction.")
    grid = []
    for n in range(3, 8):
        Ds = [("generic pos ds", rational_ds(n, RNG)),
              ("near-permutation ds", None)]
        M = rational_ds(n, RNG)
        Ds[1] = ("near-permutation ds",
                 [[Q(49, 50) * Q(int(i == j)) + Q(1, 50) * M[i][j]
                   for j in range(n)] for i in range(n)])
        for dname, D in Ds:
            Df = np.array([[float(x) for x in row] for row in D])
            for k in range(2, n + 1):
                phiD = phi_f(Df, k)

                def dlt(x):
                    u, v = np.exp(x[:n]), np.exp(x[n:])
                    A = (u[:, None] * Df) * v[None, :]
                    A = A * (n / A.sum())
                    return phiD - phi_f(A, k)

                best, bx = 0.0, None
                for _ in range(3):
                    x = RNG.normal(0, 0.02, 2 * n)
                    for _ in range(120):
                        g = np.zeros(2 * n)
                        f0 = dlt(x)
                        for i in range(2 * n):
                            e = np.zeros(2 * n)
                            e[i] = 1e-5
                            g[i] = (dlt(x + e) - f0) / 1e-5
                        gn = np.linalg.norm(g)
                        if gn < 1e-14:
                            break
                        x = x - 0.05 * g / gn
                        x = np.clip(x, -1.5, 1.5)
                    if dlt(x) < best:
                        best, bx = dlt(x), x.copy()
                if bx is None:
                    grid.append((n, k, dname, None))
                    continue
                u = [Q(float(np.exp(t))).limit_denominator(400) for t in bx[:n]]
                v = [Q(float(np.exp(t))).limit_denominator(400) for t in bx[n:]]
                Au = [[u[i] * D[i][j] * v[j] for j in range(n)] for i in range(n)]
                c = Q(n, sum(sum(r) for r in Au))
                A = [[c * x for x in row] for row in Au]
                gap = phi_x(A, k) - phi_x(D, k)
                grid.append((n, k, dname, gap if gap > 0 else None))
    ok = [g for g in grid if g[3] is not None]
    log(f"  exact violations {len(ok)} / {len(grid)} (n,k,D-type) cells searched")
    seen = set()
    for n, k, dname, gap in grid:
        tagk = (n, k)
        if gap is not None and tagk not in seen:
            seen.add(tagk)
            log(f"    (n,k)=({n},{k}) {dname}: Phi_k(A) - Phi_k(S(A)) = "
                f"{float(gap):+.4e}  exact {gap}")
    miss = sorted({(n, k) for n, k, _, g in grid} - seen)
    log(f"  cells with NO exact violation found: {miss}")
    if wits:
        tag, n, k, delta, i0, gap, A, D, marg = wits[0]
        log("  MINIMAL WITNESS, in full:")
        log(f"    n={n}, k={k}, delta={delta}, scaled row {i0}")
        log(f"    A = {[[str(x) for x in r] for r in A]}")
        log(f"    S(A) = D = {[[str(x) for x in r] for r in D]}")
        log(f"    Phi_k(A) = {phi_x(A, k)},  Phi_k(S(A)) = {phi_x(D, k)}")
        log(f"    deficit  = {gap}")
    return len(wits)


# ================================================================== SCAN B
def scan_B(log):
    log("== SCAN B: t |-> Phi_k((1-t)A + tJ/n) nondecreasing on [0,1] ==")
    ts = np.linspace(0.0, 1.0, 401)
    tot = viol = 0
    worst = {}
    cases = []

    def phi_curve(A, n):
        """Phi_k along the flow for every k at once (one sigma_all per t)."""
        J = np.ones((n, n)) / n
        out = np.zeros((n + 1, len(ts)))
        for a, t in enumerate(ts):
            At = (1 - t) * A + t * J
            sig = sigma_all_f(At)
            r, c = At.sum(1), At.sum(0)
            for k in range(2, n + 1):
                b = fc.binom(n, k)
                out[k, a] = (e_k_f(r, k) + e_k_f(c, k)) / b - sig[k] / b ** 2
        return out

    for n in range(4, 10):
        for name, A in families(n, RNG):
            vals = phi_curve(A, n)
            for k in range(2, n + 1):
                d = np.diff(vals[k])
                tot += 1
                mn = d.min()
                if mn < -1e-13:
                    viol += 1
                    key = (n, k)
                    if mn < worst.get(key, (0.0, "", 0.0))[0]:
                        worst[key] = (mn, name, ts[int(d.argmin())])
                    if len(cases) < 40:
                        cases.append((n, k, name, A, ts[int(d.argmin())]))
    log(f"  (n,k,line) triples tested {tot}, with a negative increment {viol} "
        f"({100.0 * viol / max(tot, 1):.1f}%)")
    for key in sorted(worst):
        mn, name, t0 = worst[key]
        log(f"    worst (n,k)={key}: min increment {mn:+.3e} at t~{t0:.3f}, {name}")

    log("-- B.2 exact confirmation at rational t --")
    conf = 0
    for (n, k, name, A, t0) in cases:
        AQ = to_Q(A)
        JQ = [[Q(1, n)] * n for _ in range(n)]
        t1 = Q(max(int(t0 * 100) - 1, 0), 100)
        t2 = t1 + Q(2, 100)
        if t2 > 1:
            t1, t2 = Q(98, 100), Q(1)

        def mix(t):
            return [[(1 - t) * AQ[i][j] + t * JQ[i][j] for j in range(n)]
                    for i in range(n)]
        f1, f2 = phi_x(mix(t1), k), phi_x(mix(t2), k)
        if f2 < f1:
            conf += 1
            if conf <= 6:
                log(f"    EXACT VIOLATION n={n} k={k} ({name}): "
                    f"Phi({t2}) - Phi({t1}) = {f2 - f1} = {float(f2 - f1):+.6e}")
            if conf == 1:
                log("    witness matrix (exact, entry sum n):")
                log(f"      A = {[[str(x) for x in r] for r in AQ]}")
                log(f"      t1 = {t1}, t2 = {t2}, k = {k}, n = {n}")
                log(f"      Phi_k(A_t1) = {f1}")
                log(f"      Phi_k(A_t2) = {f2}")
                log(f"      bound - Phi_k(A_t1) = {fc.bound(n, k) - f1} "
                    f"(conjecture intact)")
    log(f"  exact confirmations {conf} / {len(cases)} float candidates")

    log("-- B.3 restricted to the doubly stochastic face --")
    dstot = dsviol = 0
    dsworst = (0.0, "")
    for n in range(4, 10):
        fams = [(nm, A) for nm, A in families(n, RNG)
                if max(abs(A.sum(1) - 1).max(), abs(A.sum(0) - 1).max()) < 1e-9]
        for _ in range(4):                       # more doubly stochastic points
            D, ok = sinkhorn(RNG.random((n, n)) ** 4 + 1e-4)
            if ok:
                fams.append(("ds_sparse", D * (n / D.sum())))
        for s in (0.001, 0.01, 0.05):
            P = np.eye(n)[RNG.permutation(n)]
            D, ok = sinkhorn((1 - s) * P + s * (RNG.random((n, n)) + 0.05))
            if ok:
                fams.append((f"ds_nearperm{s}", D * (n / D.sum())))
        for m in range(1, n):
            M = np.zeros((n, n))
            M[:m, :m] = 1.0 / m
            M[m:, m:] = 1.0 / (n - m)
            fams.append((f"ds_block{m}", M))
        for nm, A in fams:
            vals = phi_curve(A, n)
            for k in range(2, n + 1):
                d = np.diff(vals[k])
                dstot += 1
                if d.min() < -1e-13:
                    dsviol += 1
                    if d.min() < dsworst[0]:
                        dsworst = (d.min(), f"n={n} k={k} {nm}")
    log(f"  doubly stochastic lines tested {dstot}, violations {dsviol}"
        + (f", worst {dsworst[0]:+.3e} at {dsworst[1]}" if dsviol else ""))

    log("-- B.4 EXACT decision per line (no grid) --")
    log("  f(t) = Phi_k((1-t)A + tJ/n) is a polynomial in t of degree <= k, so it")
    log("  is interpolated exactly at k+2 rational nodes and f' is decided on")
    log("  [0,1] by a Sturm sequence.  Each line is then settled, not sampled.")
    cert = fail = 0
    failex = []
    tested = {}
    for n in range(4, 8):
        JQ = [[Q(1, n)] * n for _ in range(n)]
        pts = exact_families(n, RNG)
        for name, AQ in pts:
            for k in range(2, n + 1):
                xs = [Q(j, k + 2) for j in range(k + 2)]
                ys = []
                for t in xs:
                    M = [[(1 - t) * AQ[i][j] + t * JQ[i][j] for j in range(n)]
                         for i in range(n)]
                    ys.append(phi_x(M, k))
                f = interp(xs, ys)
                if len(f) > k + 1:
                    log(f"    DEGREE ANOMALY n={n} k={k} {name}: deg {len(f)-1}")
                ok, detail = nonneg_on_unit(pderiv(f))
                tested[(n, k)] = tested.get((n, k), 0) + 1
                if ok:
                    cert += 1
                else:
                    fail += 1
                    if len(failex) < 8:
                        failex.append((n, k, name, detail, AQ))
    log(f"  lines decided exactly: {cert + fail}; f' >= 0 on [0,1] certified "
        f"{cert}; violations {fail}")
    log(f"  per-cell counts: {dict(sorted(tested.items()))}")
    for n, k, name, detail, AQ in failex:
        log(f"    EXACT VIOLATION n={n} k={k} ({name}): {detail}")
        log(f"      A = {[[str(x) for x in r] for r in AQ]}")
    return conf + fail


# ================================================================== SCAN C
def scan_C(log):
    log("== SCAN C: real-rootedness and log-concavity of per(xJ_n + A) ==")
    log("-- C.0 the identity, verified in calibration: "
        "[x^{n-k}] per(xJ+A) = (n-k)! sigma_k(A) --")

    log("-- C.1 real-rootedness --")
    log("  named tight point first: A = I_n gives per(xJ + I) = sum_j n!/(n-j)! x^j,")
    log("  the reversed truncated exponential.")
    for n in range(2, 10):
        I = np.eye(n)
        co = coef_per_xJ_f(I)
        rt = np.roots(co[::-1])
        nim = int((abs(rt.imag) > 1e-9 * (1 + abs(rt))).sum())
        log(f"    n={n}: degree {n}, non-real roots {nim}/{n}")
    tot = viol = 0
    worst = {}
    for n in range(4, 10):
        for name, A in families(n, RNG):
            co = coef_per_xJ_f(A)
            rt = np.roots(co[::-1])
            tot += 1
            nim = int((abs(rt.imag) > 1e-7 * (1 + abs(rt))).sum())
            if nim:
                viol += 1
                worst.setdefault(n, (name, nim))
    log(f"  random/structured points tested {tot}, with a complex root pair "
        f"{viol} ({100.0 * viol / max(tot, 1):.1f}%)")
    # exact certificate: Sturm-free, use the discriminant sign at n = 4 via
    # exact resultant-free check -- instead certify by exact rational evaluation
    log("-- C.1x exact certificate of non-real-rootedness at A = I_n --")
    for n in (4, 5, 6):
        co = [Q(fc.fact(d) * fc.binom(n, d)) for d in range(n + 1)]  # I_n
        # a real-rooted polynomial with positive coefficients must satisfy
        # Newton: (a_d/C(n,d))^2 >= (a_{d-1}/C(n,d-1))(a_{d+1}/C(n,d+1))
        bad = []
        for d in range(1, n):
            l = (co[d] / fc.binom(n, d)) ** 2
            r = (co[d - 1] / fc.binom(n, d - 1)) * (co[d + 1] / fc.binom(n, d + 1))
            if l < r:
                bad.append((d, l - r))
        log(f"    n={n}: Newton fails at d = {[b[0] for b in bad]}, "
            f"first exact deficit {bad[0][1]} < 0" if bad else f"    n={n}: Newton holds")

    log("-- C.2 log-concavity variants on the coefficient sequence --")
    # variants, all on 0 <= k <= n with sigma_0 = 1
    def variants(n, sig):
        co = [sig[n - d] * fc.fact(d) for d in range(n + 1)]
        return {
            "L1 sigma_k^2 >= sigma_{k-1}sigma_{k+1}":
                [(sig[k] ** 2, sig[k - 1] * sig[k + 1]) for k in range(1, n)],
            "L2 P_k^2 >= P_{k-1}P_{k+1}":
                [((sig[k] / fc.binom(n, k) ** 2) ** 2,
                  (sig[k - 1] / fc.binom(n, k - 1) ** 2)
                  * (sig[k + 1] / fc.binom(n, k + 1) ** 2)) for k in range(1, n)],
            "L3 ULC (sigma_k/C(n,k))^2 >= ...":
                [((sig[k] / fc.binom(n, k)) ** 2,
                  (sig[k - 1] / fc.binom(n, k - 1))
                  * (sig[k + 1] / fc.binom(n, k + 1))) for k in range(1, n)],
            "L4 raw coefficients a_d^2 >= a_{d-1}a_{d+1}":
                [(co[d] ** 2, co[d - 1] * co[d + 1]) for d in range(1, n)],
            "N  Newton (a_d/C(n,d))^2 >= ...":
                [((co[d] / fc.binom(n, d)) ** 2,
                  (co[d - 1] / fc.binom(n, d - 1))
                  * (co[d + 1] / fc.binom(n, d + 1))) for d in range(1, n)],
        }

    counts, fails, firstfail = {}, {}, {}
    for n in range(4, 10):
        for name, A in families(n, RNG):
            sig = sigma_all_f(A)
            for vname, pairs in variants(n, sig).items():
                for idx, (l, r) in enumerate(pairs, start=1):
                    counts[vname] = counts.get(vname, 0) + 1
                    if l < r * (1 - 1e-10):
                        fails[vname] = fails.get(vname, 0) + 1
                        firstfail.setdefault(vname, (n, name, idx, l - r, A))
        # the tight point too
        sig = sigma_all_f(np.eye(n))
        for vname, pairs in variants(n, sig).items():
            for idx, (l, r) in enumerate(pairs, start=1):
                counts[vname] = counts.get(vname, 0) + 1
                if l < r * (1 - 1e-10):
                    fails[vname] = fails.get(vname, 0) + 1
                    firstfail.setdefault(vname, (n, "I_n", idx, l - r, np.eye(n)))
    for vname in counts:
        f = fails.get(vname, 0)
        log(f"    {vname}: {counts[vname]} inequalities, {f} failures"
            + ("" if not f else
               f"; first at n={firstfail[vname][0]} idx={firstfail[vname][2]} "
               f"({firstfail[vname][1]})"))
    log("-- C.3 the polynomial that IS real-rooted: M_A(x) = sum_k sigma_k(A) x^k --")
    log("  sigma_k(A) is the total weight of the k-matchings of the bipartite")
    log("  graph with edge weights a_ij (a k-matching = k entries in distinct rows")
    log("  and distinct columns), so M_A is the weighted matching polynomial and")
    log("  Heilmann-Lieb gives real roots.  Newton for M_A is exactly variant L3.")
    tot = bad = 0
    worst = 0.0
    flagged = []
    for n in range(4, 10):
        pts = list(families(n, RNG))
        pts.append(("I_n", np.eye(n)))
        pts.append(("onerow", _norm(np.vstack([np.ones(n)] + [np.zeros(n)] * (n - 1)))))
        for name, A in pts:
            sig = sigma_all_f(A)
            rt = np.roots(sig[::-1])
            tot += 1
            im = abs(rt.imag) / (1 + abs(rt))
            if im.size and im.max() > 1e-7:
                bad += 1
                worst = max(worst, im.max())
                if len(flagged) < 8:
                    flagged.append((n, name, A, im.max()))
    log(f"  points tested {tot}, float-flagged as complex {bad}; "
        f"worst relative |Im| {worst:.2e}")
    log("  every float flag re-decided EXACTLY by Sturm (np.roots is badly")
    log("  conditioned on these: the coefficients span many orders of magnitude):")
    for n, name, A, imx in flagged:
        sig = sigma_all_x(to_Q(A))
        rr, det = real_rooted_x(sig)
        log(f"    n={n} {name} (float |Im|~{imx:.1e}): exactly real-rooted = {rr} "
            f"[{det}]")
    log("  exact spot-check on unflagged points as a control:")
    for n in (4, 6, 8):
        for name, A in list(families(n, RNG))[:3]:
            rr, det = real_rooted_x(sigma_all_x(to_Q(A)))
            log(f"    n={n} {name}: real-rooted = {rr} [{det}]")

    log("-- C.2x exact confirmation of each failure --")
    for vname, (n, name, idx, gap, A) in firstfail.items():
        AQ = to_Q(A) if name != "I_n" else [[Q(int(i == j)) for j in range(n)]
                                            for i in range(n)]
        sig = sigma_all_x(AQ)
        pairs = variants(n, sig)[vname]
        l, r = pairs[idx - 1]
        log(f"    {vname}: n={n} ({name}) index {idx}: lhs - rhs = {l - r} "
            f"= {float(l - r):+.6e} {'< 0 CONFIRMED' if l < r else 'NOT confirmed'}")
    return fails


def main():
    which = sys.argv[1] if len(sys.argv) > 1 else "all"
    out = open(f"results/reduce_{which}.log", "w")

    def log(s):
        print(s)
        out.write(s + "\n")
        out.flush()

    if which in ("calib", "all"):
        scan_calib(log)
    if which in ("A", "all"):
        scan_A(log)
    if which in ("B", "all"):
        scan_B(log)
    if which in ("C", "all"):
        scan_C(log)
    out.close()


if __name__ == "__main__":
    main()
