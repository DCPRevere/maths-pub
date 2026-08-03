#!/usr/bin/env python3
"""
Rank-one slice scan for a counterexample to the Cheon-Hwang conjecture

    Phi_k(A) = E_k(r) + E_k(c) - P_k(A)  <=  2 - k!/n^k        on K_n.

REDUCTION USED (validated exactly against results/verify_subdittert.py by
falsify_rankone_validate.py).  A rank-one A = x y^T in K_n has row sums
r = (sum y) x and column sums c = (sum x) y, and (sum x)(sum y) = n.  Putting
u = r, v = c gives A = u v^T / n with u, v >= 0 and sum u = sum v = n, and

    sigma_k(A) = k! e_k(x) e_k(y) = k! e_k(u) e_k(v) / n^k,

so with a = e_k(u)/C(n,k), b = e_k(v)/C(n,k), gamma = k!/n^k,

    Phi_k = a + b - gamma * a * b,        bound = 2 - gamma.

Every rank-one point of K_n is (u,v) for exactly one such pair up to the free
scale, so scanning (u,v) scans the whole rank-one slice.

The scan is exact (fractions.Fraction throughout).  No floating point enters any
comparison.

Usage:  python3 falsify_rankone.py [--nmax 30] [--grid 40] [--full-pairs-nmax 10]
"""

import argparse
import itertools
import random
import sys
import time
from fractions import Fraction as Q


# --------------------------------------------------------------- basic exact bits
def binom(n, k):
    r = 1
    for i in range(k):
        r = r * (n - i) // (i + 1)
    return r


def fact(k):
    r = 1
    for i in range(2, k + 1):
        r *= i
    return r


def ek(vec, k):
    """e_k by the O(nk) truncated recurrence."""
    e = [Q(0)] * (k + 1)
    e[0] = Q(1)
    for t in vec:
        for j in range(min(k, len(e) - 1), 0, -1):
            e[j] += e[j - 1] * t
    return e[k]


def ek_polyprod(vec, k):
    """e_k by full expansion of prod (1 + t_i z) -- a structurally different
    route, used only as a cross-check on ek()."""
    coef = [Q(1)]
    for t in vec:
        new = coef + [Q(0)]
        for i, c in enumerate(coef):
            new[i + 1] += c * t
        coef = new
    return coef[k]


# ------------------------------------------------------------------- the families
def two_value(n, p, alpha):
    """p entries equal alpha, n-p entries equal beta, total n.  Needs
    0 <= alpha <= n/p so that beta >= 0."""
    beta = Q(n - p * alpha, n - p)
    return [alpha] * p + [beta] * (n - p)


def one_spike(n, s):
    """(1+s, 1, ..., 1) rescaled to sum n.  s >= -1."""
    raw = [Q(1) + s] + [Q(1)] * (n - 1)
    tot = sum(raw)
    return [t * Q(n) / tot for t in raw]


def three_value(n, p, q_, alpha, beta):
    """p copies of alpha, q_ copies of beta, rest equal, total n."""
    rest = n - p - q_
    if rest <= 0:
        return None
    used = p * alpha + q_ * beta
    if used > n:
        return None
    return [alpha] * p + [beta] * q_ + [Q(n - used, rest)] * rest


def family_vectors(n, grid, rng, n_random=120):
    """All candidate u-vectors (each sums exactly to n).  Returns
    [(label, vector), ...]."""
    out = []
    ones = [Q(1)] * n
    out.append(("centre", ones))

    # two-value: p blocks, alpha swept over [0, n/p]
    for p in range(1, n):
        hi = Q(n, p)
        for j in range(grid + 1):
            alpha = hi * Q(j, grid)
            out.append((f"2val p={p} a={alpha}", two_value(n, p, alpha)))

    # one-spike, s in [-1, 12]
    for j in range(grid + 1):
        s = Q(-1) + Q(13 * j, grid)
        out.append((f"spike s={s}", one_spike(n, s)))

    # support-restricted uniform (vertices of the simplex faces)
    for m in range(1, n + 1):
        out.append((f"supp m={m}",
                    [Q(n, m)] * m + [Q(0)] * (n - m)))

    # three-value, coarse (small n only to keep the count sane)
    if n <= 14:
        g3 = 6
        for p in range(1, n - 1):
            for q_ in range(1, n - p):
                for i in range(g3 + 1):
                    for j in range(g3 + 1):
                        alpha = Q(n, p) * Q(i, g3)
                        beta = Q(n, max(q_, 1)) * Q(j, g3)
                        vec = three_value(n, p, q_, alpha, beta)
                        if vec is not None:
                            out.append((f"3val p={p},q={q_}", vec))

    # random exact rationals
    for _ in range(n_random):
        raw = [Q(rng.randint(0, 40), rng.randint(1, 12)) for _ in range(n)]
        tot = sum(raw)
        if tot == 0:
            continue
        out.append(("random", [t * Q(n) / tot for t in raw]))

    return out


# ------------------------------------------------------------------ the functional
def phi(a, b, gamma):
    return a + b - gamma * a * b


def scan_cell(n, k, grid, rng, full_pairs, log):
    """Scan one (n,k) cell.  Returns a dict of findings."""
    C = binom(n, k)
    gamma = Q(fact(k), n ** k)
    bound = Q(2) - gamma

    vecs = family_vectors(n, grid, rng)
    # a-values, keeping the label and whether the vector is the centre
    avals = []
    for label, vec in vecs:
        assert sum(vec) == n, f"vector does not sum to n: {label}"
        assert all(t >= 0 for t in vec), f"negative entry: {label}"
        a = Q(ek(vec, k), C)
        avals.append((a, label, vec))

    # cross-check the two e_k routes on a sample
    for a, label, vec in rng.sample(avals, min(12, len(avals))):
        assert Q(ek_polyprod(vec, k), C) == a, f"e_k routes disagree: {label}"

    # Maclaurin sanity: a <= 1 for every nonneg vector summing to n
    over = [(a, lab) for a, lab, _ in avals if a > 1]

    # ---- maximisation.  phi is increasing in a whenever 1 - gamma*b > 0 and in
    # b whenever 1 - gamma*a > 0; gamma <= 1/2 here and a,b <= 1, so both hold
    # and the max over the product family is at (max a, max b).  For small n the
    # full pair scan is run as well and must agree.
    amax, alab, avec = max(avals, key=lambda t: t[0])
    best = phi(amax, amax, gamma)
    best_lab = (alab, alab)

    pairs_checked = len(avals)
    if full_pairs:
        # coarse subsample of the pair product, exhaustive over a reduced set
        sub = avals if len(avals) <= 260 else rng.sample(avals, 260)
        bf, bl = None, None
        for a, la, _ in sub:
            for b, lb, _ in sub:
                p = phi(a, b, gamma)
                if bf is None or p > bf:
                    bf, bl = p, (la, lb)
        pairs_checked = len(sub) ** 2
        assert bf <= best, (
            f"full pair scan beat the monotone shortcut at ({n},{k}): "
            f"{bf} > {best} at {bl}")

    # ---- best strictly off-centre: at least one of u,v not the all-ones vector
    off = [(a, lab, vec) for a, lab, vec in avals
           if any(t != 1 for t in vec)]
    a2, lab2, vec2 = max(off, key=lambda t: t[0])
    best_off = phi(a2, amax, gamma)          # off-centre u paired with the best v

    # ---- margin at a FIXED separation from the barycentre.  The unconstrained
    # off-centre optimum just crawls back to u = 1, so it says nothing about the
    # size of the gap.  This measures max Phi over family points held at least
    # delta away from 1 in sup-norm, which is a real margin.
    delta = Q(1, 10)
    sep = [(a, lab) for a, lab, vec in avals
           if max(abs(t - 1) for t in vec) >= delta]
    if sep:
        a3, lab3 = max(sep)
        margin = phi(a3, amax, gamma)
        ratio_sep = margin / bound
    else:
        a3, lab3, margin, ratio_sep = None, "none", None, None

    # ---- exact 1-D refinement on the best off-centre two-value direction
    refined, refined_lab = best_off, lab2
    if lab2.startswith("2val"):
        p = int(lab2.split("p=")[1].split()[0])
        lo, hi = Q(0), Q(n, p)
        # local subdivision around the grid winner, 8 rounds, exact
        centre_alpha = vec2[0]
        step = Q(n, p) / grid
        for _ in range(8):
            cands = []
            for j in range(-4, 5):
                al = centre_alpha + step * Q(j, 4)
                if al < 0 or al > hi:
                    continue
                vv = two_value(n, p, al)
                if all(t == 1 for t in vv):
                    continue                 # exclude the centre itself
                cands.append((Q(ek(vv, k), C), al))
            if not cands:
                break
            bestc = max(cands)
            centre_alpha = bestc[1]
            step /= 4
        vv = two_value(n, p, centre_alpha)
        if any(t != 1 for t in vv):
            cand = phi(Q(ek(vv, k), C), amax, gamma)
            if cand > refined:
                refined, refined_lab = cand, f"2val p={p} a={centre_alpha} (refined)"

    hit = best > bound
    res = dict(n=n, k=k, bound=bound, best=best, best_lab=best_lab,
               ratio=Q(best, 1) / bound, best_off=max(best_off, refined),
               off_lab=refined_lab, ratio_off=max(best_off, refined) / bound,
               hit=hit, npoints=len(avals), pairs=pairs_checked,
               maclaurin_violations=over,
               amax=amax, amax_vec=avec,
               ratio_sep=ratio_sep, sep_lab=lab3, margin=margin)
    log(f"  n={n:2d} k={k:2d}  points={len(avals):5d} pairs={pairs_checked:9d}"
        f"  max ratio={float(res['ratio']):.12f}"
        f"  best off-centre ratio={float(res['ratio_off']):.12f}"
        f"  {'*** HIT ***' if hit else ''}")
    if over:
        log(f"     *** Maclaurin violated at {len(over)} points, e.g. {over[0][1]}")
    return res


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--nmax", type=int, default=30)
    ap.add_argument("--nmin", type=int, default=6)
    ap.add_argument("--grid", type=int, default=40)
    ap.add_argument("--full-pairs-nmax", type=int, default=10)
    ap.add_argument("--seed", type=int, default=20260731)
    ap.add_argument("--ksample", type=int, default=0,
                    help="if > 0, sample this many k values per n (spread over "
                         "[5, n-1], endpoints included) instead of all of them")
    ap.add_argument("--nlist", type=str, default="",
                    help="explicit comma-separated list of n, overrides nmin/nmax")
    args = ap.parse_args()

    rng = random.Random(args.seed)
    t0 = time.time()

    def log(msg):
        print(msg, flush=True)

    log("rank-one slice scan for Cheon-Hwang counterexamples")
    log(f"range: {args.nmin} <= n <= {args.nmax}, 5 <= k < n; grid={args.grid}; "
        f"full pair product for n <= {args.full_pairs_nmax}")
    log("")

    results = []
    hits = []
    nvals = ([int(t) for t in args.nlist.split(",")] if args.nlist
             else list(range(args.nmin, args.nmax + 1)))
    for n in nvals:
        ks = list(range(5, n))
        if args.ksample and len(ks) > args.ksample:
            m = args.ksample
            idx = sorted({round(i * (len(ks) - 1) / (m - 1)) for i in range(m)})
            ks = [ks[i] for i in idx]
        for k in ks:
            r = scan_cell(n, k, args.grid, rng,
                          full_pairs=(n <= args.full_pairs_nmax), log=log)
            results.append(r)
            if r["hit"]:
                hits.append(r)
        log(f"  [n={n} done, {time.time()-t0:.1f}s]")

    log("")
    log("=" * 74)
    log(f"cells scanned: {len(results)}   hits (ratio > 1): {len(hits)}")
    tot_pts = sum(r["npoints"] for r in results)
    log(f"total family points evaluated: {tot_pts}")
    mv = sum(len(r["maclaurin_violations"]) for r in results)
    log(f"Maclaurin (a <= 1) violations: {mv}")

    log("")
    log("TOP 10 by max ratio Phi_k/(2 - k!/n^k)  [exact]")
    for r in sorted(results, key=lambda r: -r["ratio"])[:10]:
        log(f"  n={r['n']:2d} k={r['k']:2d}  ratio = {r['ratio']}  "
            f"(= {float(r['ratio']):.15f})  Phi={r['best']}  bound={r['bound']}"
            f"  at {r['best_lab']}")

    log("")
    log("TOP 10 by best STRICTLY OFF-CENTRE ratio  [exact]")
    for r in sorted(results, key=lambda r: -r["ratio_off"])[:10]:
        log(f"  n={r['n']:2d} k={r['k']:2d}  ratio = {r['ratio_off']}")
        log(f"       (= {float(r['ratio_off']):.15f})  Phi={r['best_off']}  "
            f"at u={r['off_lab']}, v=centre")

    log("")
    log("TOP 10 by ratio at FIXED separation ||u - 1||_inf >= 1/10  [exact]")
    withsep = [r for r in results if r["ratio_sep"] is not None]
    for r in sorted(withsep, key=lambda r: -r["ratio_sep"])[:10]:
        log(f"  n={r['n']:2d} k={r['k']:2d}  ratio = {r['ratio_sep']}")
        log(f"       (= {float(r['ratio_sep']):.15f})  Phi={r['margin']}  "
            f"at u={r['sep_lab']}, v=centre")

    log("")
    if hits:
        log("*** CANDIDATE HITS -- must go through the hit protocol ***")
        for r in hits:
            log(f"  n={r['n']} k={r['k']} Phi={r['best']} > {r['bound']} "
                f"at {r['best_lab']}, vector {r['amax_vec']}")
        return 1
    log("NO COUNTEREXAMPLE FOUND on the rank-one slice in the scanned range.")
    log(f"elapsed {time.time()-t0:.1f}s")
    return 0


if __name__ == "__main__":
    sys.exit(main())
