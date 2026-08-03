#!/usr/bin/env python3
"""Wide sweep: EXHAUSTIVE circulant supports plus extra named objects.

Observation that drives the design.  If A is doubly stochastic then r = c = 1,
so E_k(r) = E_k(c) = 1 exactly and

    Phi_k(A) = 2 - sigma_k(A)/C(n,k)^2.

So on the doubly stochastic face the conjecture is EXACTLY the statement
sigma_k(A) >= C(n,k)^2 k!/n^k, a k-th order van der Waerden / Dittert-type
minimisation.  Every doubly stochastic matrix below is therefore a direct test
of that minimisation; the ratio Phi_k/M is a monotone decreasing function of
sigma_k, so ranking by ratio = ranking by how small sigma_k gets.

Coverage here:
  * every circulant support S subset of Z_n with 0 in S (all 2^(n-1) of them,
    which is every circulant 0/1 matrix up to rotation) for n <= 10;
    |S| <= 3 or |S| >= n-3 for n = 11, 12 where the full sweep is too slow;
  * Hadamard-12 support, Paley tournament supports, band matrices, two-block
    matrices, bordered matrices, near-vertex matrices.
"""
import itertools
import json
import os
import sys
import time
from fractions import Fraction as Q

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import falsify_pencils as fp  # noqa: E402


def hadamard12_support():
    """(0,1) support of a normalised Hadamard matrix of order 12 (Paley I on
    GF(11)): rows are translates of QR(11) shifted into 12 columns."""
    QR = {1, 3, 4, 5, 9}
    M = [[0] * 12 for _ in range(12)]
    for i in range(12):
        for j in range(12):
            if i == 0 or j == 0:
                M[i][j] = 1
            else:
                M[i][j] = 1 if ((j - i) % 11) in QR or i == j else 0
    return M


def band(n, w):
    return [[1 if abs(i - j) <= w else 0 for j in range(n)] for i in range(n)]


def two_block(n, p, a, b):
    """a on the p x p leading block and on its complement block, b elsewhere."""
    return [[a if (i < p) == (j < p) else b for j in range(n)]
            for i in range(n)]


def bordered(n, w):
    M = [[1] * n for _ in range(n)]
    for j in range(n):
        M[0][j] = w
        M[j][0] = w
    return M


def near_vertex(n, w):
    """Permutation matrix with weight w on the support, the rest of the mass
    spread uniformly."""
    M = [[1] * n for _ in range(n)]
    for i in range(n):
        M[i][i] = w
    return M


def wide_families(n):
    out = []
    # ---- exhaustive circulant supports -----------------------------------
    rest = list(range(1, n))
    if n <= 10:
        subsets = [(0,) + c for r in range(0, n) for c in
                   itertools.combinations(rest, r)]
    else:
        subsets = []
        for r in list(range(0, 3)) + list(range(n - 4, n)):
            subsets += [(0,) + c for c in itertools.combinations(rest, r)]
    for S in subsets:
        if len(S) == n:
            continue                       # that is J/n itself
        out.append((f"circ:{'.'.join(map(str, S))}",)
                   + fp.dir_from_B(*fp.circulant(list(S), n), n))
    # ---- extra named objects ---------------------------------------------
    if n == 12:
        H = hadamard12_support()
        out.append(("design:Hadamard-12-support",)
                   + fp.dir_from_B(*fp.from_01(H, 12), 12))
    for w in (1, 2, 3):
        if 2 * w + 1 < n:
            out.append((f"band:w={w}",)
                       + fp.dir_from_B(*fp.from_01(band(n, w), n), n))
    for p in (2, n // 2):
        for a, b in ((2, 1), (3, 1), (5, 1), (1, 2), (1, 3)):
            if 0 < p < n:
                out.append((f"two-block:p={p},{a}/{b}",)
                           + fp.dir_from_B(*fp.from_01(two_block(n, p, a, b),
                                                       n), n))
    for w in (2, 3, 5, 8):
        out.append((f"bordered:w={w}",)
                   + fp.dir_from_B(*fp.from_01(bordered(n, w), n), n))
        out.append((f"near-vertex:w={w}",)
                   + fp.dir_from_B(*fp.from_01(near_vertex(n, w), n), n))
    return out


def main():
    nmin = int(sys.argv[1]) if len(sys.argv) > 1 else 6
    nmax = int(sys.argv[2]) if len(sys.argv) > 2 else 12
    recs, hits = [], []
    t0 = time.time()
    for n in range(nmin, nmax + 1):
        ks = list(range(5, n))
        if not ks:
            continue
        fam = wide_families(n)
        print(f"### n={n} k in {ks} families={len(fam)}", flush=True)
        for lab, dnum, dden in fam:
            if sum(sum(r) for r in dnum) != 0:
                continue
            lo, hi = fp.dir_admissible(dnum, dden, n)
            polys = fp.dir_polys(dnum, dden, n, ks)
            for k in ks:
                p = polys[k]
                assert p[0] == 0
                M = fp.bound(n, k)
                vmax, targ = fp.scan_interval(p, lo, hi, steps=120)
                v1 = fp.pev(p, Q(1)) if lo <= 1 <= hi else None
                rec = dict(n=n, k=k, family=lab, max_p=str(vmax),
                           argmax=str(targ), ratio_max=str(1 + vmax / M),
                           ratio_t1=(str(1 + v1 / M) if v1 is not None
                                     else None),
                           lead_coeff=str(fp.low_order(p)[1]))
                recs.append(rec)
                if vmax > 0:
                    hits.append(rec)
                    print("  *** HIT ***", json.dumps(rec), flush=True)
        print(f"    [n={n} done {time.time() - t0:.1f}s]", flush=True)

    with open(os.path.join(HERE, "results",
                           "falsify_pencils_wide_records.json"), "w") as f:
        json.dump(recs, f)
    print(f"\nrecords={len(recs)} hits={len(hits)}")
    ep = [r for r in recs if r["ratio_t1"] is not None]
    ep.sort(key=lambda r: Q(r["ratio_t1"]), reverse=True)
    print("\nTOP-20 structured POINTS (t=1) by Phi_k/M:")
    for r in ep[:20]:
        print(f"  {float(Q(r['ratio_t1'])):.12f}  n={r['n']} k={r['k']} "
              f"{r['family']}  exact={r['ratio_t1']}")
    print("\nVERDICT:", "COUNTEREXAMPLE CANDIDATES" if hits else
          "no point with Phi_k > 2 - k!/n^k found")
    return 0


if __name__ == "__main__":
    sys.exit(main())
