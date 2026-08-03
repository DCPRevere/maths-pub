#!/usr/bin/env python3
"""Randomised closure of the two gaps the structured sweep leaves open:

  * non-circulant regular bipartite supports (random m-regular 0/1 matrices,
    i.e. unions of m random disjoint permutations -- these are exactly the
    supports of the Latin-square-pattern family without the Latin condition);
  * a hill climb.  From random Birkhoff points, repeatedly take one exact
    gradient-ascent step inside {sum b = 0} until the step stops improving.
    On the doubly stochastic face Phi_k = 2 - sigma_k/C(n,k)^2, so this is a
    descent on sigma_k over the Birkhoff polytope; if the conjecture holds it
    must converge to J_n/n.

Time-capped: pass a wall-clock budget in seconds as argv[2].
"""
import math
import os
import random
import sys
import time
from fractions import Fraction as Q

sys.set_int_max_str_digits(500000)

GRID = 10 ** 7      # iterates are snapped to this denominator each step, so the
                    # climb stays exact but the rationals cannot blow up


def snap(A, n):
    """Nearest point of the 1/GRID lattice in K_n: round, then repair the sum
    on the largest entry and clip to nonnegativity."""
    M = [[max(0, round(A[i][j] * GRID)) for j in range(n)] for i in range(n)]
    tot = sum(sum(r) for r in M)
    want = n * GRID
    bi = max(range(n * n), key=lambda t: M[t // n][t % n])
    M[bi // n][bi % n] += want - tot
    if M[bi // n][bi % n] < 0:
        return None
    return M, GRID

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import falsify_pencils as fp                       # noqa: E402
import falsify_pencils_structure as st             # noqa: E402


def random_regular(n, m, rng):
    """Union of m random disjoint permutations: an m-regular 0/1 matrix."""
    M = [[0] * n for _ in range(n)]
    used = [set() for _ in range(n)]
    for _ in range(m):
        for _try in range(200):
            p = list(range(n))
            rng.shuffle(p)
            if all(p[i] not in used[i] for i in range(n)):
                break
        else:
            return None
        for i in range(n):
            M[i][p[i]] = 1
            used[i].add(p[i])
    return M, m


def random_birkhoff(n, rng, terms=4, scale=12):
    """Random doubly stochastic matrix: a rational convex combination of
    `terms` random permutations."""
    ws = [rng.randint(1, scale) for _ in range(terms)]
    tot = sum(ws)
    M = [[0] * n for _ in range(n)]
    for w in ws:
        p = list(range(n))
        rng.shuffle(p)
        for i in range(n):
            M[i][p[i]] += w
    return M, tot


def main():
    budget = float(sys.argv[1]) if len(sys.argv) > 1 else 300.0
    t0 = time.time()
    rng = random.Random(7)
    best = []
    hits = []

    print("== random m-regular (non-circulant) supports ==", flush=True)
    for n in (8, 9, 10, 11, 12):
        ks = list(range(5, n))
        for m in (2, 3, 4, n - 2):
            if not (1 <= m < n):
                continue
            for rep in range(3):
                if time.time() - t0 > budget * 0.55:
                    break
                R = random_regular(n, m, rng)
                if R is None:
                    continue
                dn, dd = fp.dir_from_B(*R, n)
                if sum(sum(r) for r in dn) != 0:
                    continue
                lo, hi = fp.dir_admissible(dn, dd, n)
                polys = fp.dir_polys(dn, dd, n, ks)
                for k in ks:
                    p = polys[k]
                    vmax, targ = fp.scan_interval(p, lo, hi, steps=60)
                    M = fp.bound(n, k)
                    if vmax > 0:
                        hits.append((n, k, f"rand-{m}-regular#{rep}", str(vmax)))
                        print("  *** HIT ***", n, k, m, rep, vmax, flush=True)
                    v1 = fp.pev(p, Q(1))
                    best.append((Q(1) + v1 / M, n, k,
                                 f"rand-{m}-regular#{rep}"))
        print(f"  n={n} done {time.time() - t0:.1f}s", flush=True)

    print("\n== hill climb from random Birkhoff points ==", flush=True)
    for n, k in ((7, 5), (8, 6), (9, 7), (10, 5), (12, 5)):
        for rep in range(3):
            if time.time() - t0 > budget:
                break
            Mi, D = random_birkhoff(n, rng)
            cur = fp.phi_all_k(Mi, D, n)[k] - fp.bound(n, k)
            start = cur
            steps = 0
            while steps < 8 and time.time() - t0 < budget:
                r = st.ascend(Mi, D, n, k, "climb")
                if r is None:
                    break
                v = Q(r["p_max"])
                if v <= cur:
                    break
                # re-materialise the argmax point and iterate
                g = st.gradient(Mi, D, n, k)
                mean = sum(g[i][j] for i in range(n) for j in range(n)) / (n * n)
                b = [[g[i][j] - mean for j in range(n)] for i in range(n)]
                s = Q(r["s_argmax"])
                A = [[Q(Mi[i][j], D) + s * b[i][j] for j in range(n)]
                     for i in range(n)]
                sn = snap(A, n)
                if sn is None:
                    break
                Mi, D = sn
                cur = fp.phi_all_k(Mi, D, n)[k] - fp.bound(n, k)
                steps += 1
                if cur > 0:
                    hits.append((n, k, "climb", str(cur)))
                    print("  *** HIT ***", n, k, cur, flush=True)
                    break
            print(f"  n={n} k={k} rep={rep}: p from {float(start):.3e} to "
                  f"{float(cur):.3e} in {steps} steps "
                  f"(0 = the bound, attained only at J_n/n)", flush=True)

    best.sort(reverse=True)
    print("\nTOP-10 random regular supports by Phi_k/M at t=1:")
    for v, n, k, lab in best[:10]:
        print(f"  {float(v):.9f}  n={n} k={k} {lab}   exact={v}")
    print(f"\nhits={len(hits)}")
    print("VERDICT:", "COUNTEREXAMPLE CANDIDATES" if hits else
          "no point with Phi_k > 2 - k!/n^k found")


if __name__ == "__main__":
    main()
