#!/usr/bin/env python3
"""Close the gap the wide sweep left: middle-size circulant supports at
n = 11 and n = 12 (|S| between 4 and n-5, which falsify_pencils_wide.py skips
for time).  Time-capped; reports how far it got so the coverage claim can be
stated honestly.
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


def main():
    budget = float(sys.argv[1]) if len(sys.argv) > 1 else 600.0
    t0 = time.time()
    hits, done, best = [], {}, []
    for n in (11, 12):
        ks = list(range(5, n))
        rest = list(range(1, n))
        for m in range(4, n - 4):                       # the skipped band
            todo = [(0,) + c for c in itertools.combinations(rest, m - 1)]
            cnt = 0
            for S in todo:
                if time.time() - t0 > budget:
                    break
                dn, dd = fp.dir_from_B(*fp.circulant(list(S), n), n)
                lo, hi = fp.dir_admissible(dn, dd, n)
                polys = fp.dir_polys(dn, dd, n, ks)
                for k in ks:
                    p = polys[k]
                    vmax, targ = fp.scan_interval(p, lo, hi, steps=60)
                    if vmax > 0:
                        hits.append((n, k, S, str(vmax)))
                        print("  *** HIT ***", n, k, S, vmax, flush=True)
                    best.append((Q(1) + fp.pev(p, Q(1)) / fp.bound(n, k),
                                 n, k, "circ:" + ".".join(map(str, S))))
                cnt += 1
            done[(n, m)] = (cnt, len(todo))
            print(f"  n={n} |S|={m}: {cnt}/{len(todo)} supports "
                  f"({time.time() - t0:.0f}s)", flush=True)
            if time.time() - t0 > budget:
                break
        if time.time() - t0 > budget:
            break
    print("\ncoverage of the previously-skipped band:")
    for (n, m), (c, tot) in sorted(done.items()):
        print(f"  n={n} |S|={m}: {c}/{tot}"
              f"{'  COMPLETE' if c == tot else '  PARTIAL'}")
    best.sort(reverse=True)
    print("\nTOP-5 by Phi_k/M at t=1:")
    for v, n, k, lab in best[:5]:
        print(f"  {float(v):.12f}  n={n} k={k} {lab}  exact={v}")
    print(f"\nevaluations={len(best)}  hits={len(hits)}")
    print("VERDICT:", "COUNTEREXAMPLE CANDIDATES" if hits else
          "no point with Phi_k > 2 - k!/n^k found")


if __name__ == "__main__":
    main()
