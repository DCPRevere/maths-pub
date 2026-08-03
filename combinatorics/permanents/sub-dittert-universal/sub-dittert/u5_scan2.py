#!/usr/bin/env python3
"""U5 scan, second pass (EXPLORATORY, floats -- [I], never a decision).

Two ambient sets, both with every witness validated before it counts:
  DS : A doubly stochastic (Sinkhorn), witness rejected unless the row and
       column sums are 1 to 1e-9 and A >= 0;
  CE : B doubly centred with ||B||_op <= 1 (projection + spectral clip),
       witness rejected unless the sums vanish and sigma_max <= 1 + 1e-9.

For each connected pattern with all degrees >= 2 we maximise |S_G(B)|/Q.
U5 with constant 1 says the answer is <= 1 in both.
"""
import sys
import numpy as np
from scipy.optimize import minimize
import u5_hunt as H


# ---------------------------------------------------------------- ambient DS

def sinkhorn(X, iters=400):
    A = np.exp(np.clip(X, -25.0, 25.0))
    for _ in range(iters):
        A = A / A.sum(axis=1, keepdims=True)
        A = A / A.sum(axis=0, keepdims=True)
    return A / A.sum(axis=1, keepdims=True)


def ds_ok(A):
    return (np.isfinite(A).all() and A.min() >= -1e-12
            and abs(A.sum(axis=1) - 1).max() < 1e-9
            and abs(A.sum(axis=0) - 1).max() < 1e-9)


def B_of_DS(x, n):
    A = sinkhorn(x.reshape(n, n))
    if not ds_ok(A):
        return None, None
    return A - 1.0 / n, A


# ---------------------------------------------------------------- ambient CE

def centre(M):
    M = M - M.mean(axis=1, keepdims=True)
    M = M - M.mean(axis=0, keepdims=True)
    return M


def clip_op(M):
    U, s, Vt = np.linalg.svd(M)
    s = np.minimum(s, 1.0)
    return U @ np.diag(s) @ Vt


def ce_ok(B):
    return (np.isfinite(B).all()
            and abs(B.sum(axis=1)).max() < 1e-9
            and abs(B.sum(axis=0)).max() < 1e-9
            and np.linalg.svd(B, compute_uv=False)[0] <= 1 + 1e-9)


def B_of_CE(x, n):
    B = centre(clip_op(centre(x.reshape(n, n))))
    if not ce_ok(B):
        return None, None
    return B, B


def ratio(x, c, n, sign, amb):
    B, _ = (B_of_DS if amb == "DS" else B_of_CE)(x, n)
    if B is None:
        return 0.0
    Q = (B * B).sum()
    if Q < 1e-13:
        return 0.0
    return sign * H.S_float(c, B) / Q


def scan(c, n, restarts, rng, amb):
    best = (-1e18, None)
    for sign in (1.0, -1.0):
        for r in range(restarts):
            scale = 10 ** rng.uniform(-0.7, 1.2)
            x0 = rng.normal(size=n * n) * scale
            res = minimize(lambda x: -ratio(x, c, n, sign, amb), x0,
                           method="L-BFGS-B",
                           options=dict(maxiter=500, ftol=1e-15, gtol=1e-13))
            if -res.fun > best[0]:
                B, W = (B_of_DS if amb == "DS" else B_of_CE)(res.x, n)
                if B is not None:
                    best = (-res.fun, W)
    return best


PATTERNS_BIG = {
    "K33 (e=9, 3-regular)": [[1, 1, 1], [1, 1, 1], [1, 1, 1]],
    "K34 (e=12)": [[1, 1, 1, 1], [1, 1, 1, 1], [1, 1, 1, 1]],
    "cube Q3 (e=12, 3-reg)": [[1, 1, 1, 0], [1, 1, 0, 1], [1, 0, 1, 1], [0, 1, 1, 1]],
    "K44 (e=16)": [[1] * 4 for _ in range(4)],
    "spider: 3 double-edges on a path": [[2, 0, 0, 1], [0, 2, 0, 1], [0, 0, 2, 1]],
    "dumbbell 4cyc-bridge-4cyc": [[1, 1, 0, 0], [1, 1, 1, 0], [0, 0, 1, 1], [0, 0, 1, 1]],
}


if __name__ == "__main__":
    mode = sys.argv[1] if len(sys.argv) > 1 else "small"
    ns = [int(v) for v in (sys.argv[2].split(",") if len(sys.argv) > 2 else ["5", "6"])]
    restarts = int(sys.argv[3]) if len(sys.argv) > 3 else 6
    rng = np.random.default_rng(20260803)
    worst = {"DS": (0.0, None), "CE": (0.0, None)}
    if mode == "small":
        items = []
        for e in range(3, 7):
            for key in sorted(H.patterns(e)):
                items.append((f"e={e} {key}", [list(r) for r in key]))
    else:
        items = [(k, v) for k, v in PATTERNS_BIG.items()]
    for name, c in items:
        line = []
        for amb in ("DS", "CE"):
            for n in ns:
                v, W = scan(c, n, restarts, rng, amb)
                line.append(f"{amb}n{n}:{v:.5f}")
                if v > worst[amb][0]:
                    worst[amb] = (v, (name, n, W))
                if v > 1.0 + 1e-6:
                    print(f"  !! VIOLATION {amb} n={n} {name} ratio={v:.8f}", flush=True)
                    print(np.round(W, 6), flush=True)
        print(f"{name:44s} " + "  ".join(line), flush=True)
    for amb in ("DS", "CE"):
        v, w = worst[amb]
        print(f"\nWORST {amb}: {v:.8f} at {w[0]} n={w[1]}")
        print(np.round(w[2], 5))
