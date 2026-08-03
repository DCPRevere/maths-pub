#!/usr/bin/env python3
"""Exact scan of the SHARPEST slice of the block-direct-sum family.

The two-block sweep in falsify_directsum.py finds that the deficit
D(s) = (2 - k!/n^k) - Phi_k(A(p,s)) always attains its minimum over s at s = p,
i.e. at the point where every row and column sum equals 1 and the matrix is the
doubly stochastic direct sum J_p/p (+) J_q/q.  There E_k(r) = E_k(c) = 1, so

    Phi_k = 2 - sigma_k(A)/C(n,k)^2,     D = sigma_k(A)/C(n,k)^2 - k!/n^k,

and the conjecture on this slice is exactly "J_n/n minimises sigma_k over doubly
stochastic matrices".  This script evaluates that slice EXACTLY (no subdivision,
no bisection, no floats in any decision) for every direct sum of 2 or 3 flat
doubly stochastic blocks, all 5 <= k < n <= 40.

Usage: python3 falsify_directsum_ds.py <n_lo> <n_hi> <maxblocks>
"""

import json
import sys
from fractions import Fraction as Q

from falsify_directsum import (binom, bound, factorial, sigma_direct_sum)


def scan(n_lo, n_hi, maxblocks=3):
    hits, tops, cells = [], [], 0
    for n in range(n_lo, n_hi + 1):
        C = binom(n, n // 2)  # placeholder, real one per k below
        parts = []
        for p in range(1, n):
            parts.append((p, n - p))
        if maxblocks >= 3:
            for p in range(1, n - 1):
                for q in range(p, n - p):
                    r = n - p - q
                    if r >= q:
                        parts.append((p, q, r))
        for k in range(5, n):
            Ck = binom(n, k)
            gam = Q(factorial(k), n**k)
            bnd = Q(2) - gam
            for sizes in parts:
                cells += 1
                sig = sigma_direct_sum(list(sizes), [Q(s) for s in sizes], k)
                phi = Q(2) - sig / (Ck * Ck)
                d = bnd - phi          # = sig/Ck^2 - k!/n^k
                if d < 0:
                    hits.append((n, k, sizes, str(phi), str(bnd)))
                    print(json.dumps({"event": "HIT-CANDIDATE-DS", "n": n, "k": k,
                                      "sizes": list(sizes)}), flush=True)
                tops.append((phi / bnd, n, k, sizes, phi, bnd, d))
        print(json.dumps({"event": "n-done-ds", "n": n, "cells": cells,
                          "hits": len(hits)}), flush=True)
    tops.sort(key=lambda t: -t[0])
    out = {"cells": cells, "hits": hits,
           "top": [{"n": n, "k": k, "sizes": list(sz), "phi": str(phi),
                    "bound": str(b), "deficit": str(d), "ratio": str(r),
                    "ratio_float": float(r)}
                   for (r, n, k, sz, phi, b, d) in tops[:20]]}
    print("RESULTDS " + json.dumps(out), flush=True)


if __name__ == "__main__":
    scan(int(sys.argv[1]), int(sys.argv[2]),
         int(sys.argv[3]) if len(sys.argv) > 3 else 3)
