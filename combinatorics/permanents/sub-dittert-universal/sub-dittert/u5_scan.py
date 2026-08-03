#!/usr/bin/env python3
"""U5 scan (EXPLORATORY, floats -- [I]).

For every connected pattern with e edges and all degrees >= 2, maximise
|S_G(A - J/n)| / Q over the Birkhoff polytope (Sinkhorn parametrisation,
L-BFGS with random restarts).  U5 with constant 1 says the answer is <= 1.
"""
import sys
import numpy as np
from scipy.optimize import minimize
import u5_hunt as H


def sinkhorn(X, iters=300):
    A = np.exp(np.clip(X, -25.0, 25.0))
    for _ in range(iters):
        A = A / A.sum(axis=1, keepdims=True)
        A = A / A.sum(axis=0, keepdims=True)
    return A / A.sum(axis=1, keepdims=True)


def ds_defect(A):
    return max(abs(A.sum(axis=1) - 1).max(), abs(A.sum(axis=0) - 1).max())


def ratio(x, c, n, sign):
    A = sinkhorn(x.reshape(n, n))
    if not np.isfinite(A).all() or ds_defect(A) > 1e-9:
        return 0.0                      # not doubly stochastic: reject
    B = A - 1.0 / n
    Q = (B * B).sum()
    if Q < 1e-14:
        return 0.0
    return sign * H.S_float(c, B) / Q


def scan(c, n, restarts, rng):
    best = (-1e18, None)
    for sign in (1.0, -1.0):
        for r in range(restarts):
            scale = 10 ** rng.uniform(-0.5, 1.2)
            x0 = rng.normal(size=n * n) * scale
            res = minimize(lambda x: -ratio(x, c, n, sign), x0,
                           method="L-BFGS-B",
                           options=dict(maxiter=400, ftol=1e-14, gtol=1e-12))
            v = -res.fun
            if v > best[0]:
                best = (v, sinkhorn(res.x.reshape(n, n)))
    return best


if __name__ == "__main__":
    emin = int(sys.argv[1]) if len(sys.argv) > 1 else 4
    emax = int(sys.argv[2]) if len(sys.argv) > 2 else 6
    ns = [int(v) for v in (sys.argv[3].split(",") if len(sys.argv) > 3 else ["4", "5", "6"])]
    restarts = int(sys.argv[4]) if len(sys.argv) > 4 else 8
    rng = np.random.default_rng(20260731)
    worst_overall = 0.0
    for e in range(emin, emax + 1):
        pats = H.patterns(e)
        print(f"=== e = {e}: {len(pats)} classes", flush=True)
        for key, (sgn, mass) in sorted(pats.items()):
            c = [list(r) for r in key]
            line = []
            for n in ns:
                v, A = scan(c, n, restarts, rng)
                line.append(f"n={n}:{v:.5f}")
                if v > worst_overall:
                    worst_overall = v
                    arg = (e, key, n, A)
                if v > 1.0 + 1e-7:
                    print(f"    VIOLATION e={e} {key} n={n} ratio={v:.8f}")
                    print(np.round(A, 5))
            print(f"  {key} mass={mass}  " + "  ".join(line), flush=True)
    print(f"\nWORST |S|/Q over everything scanned: {worst_overall:.8f}")
    print(f"  at e={arg[0]} pattern={arg[1]} n={arg[2]}")
    print(np.round(arg[3], 5))
