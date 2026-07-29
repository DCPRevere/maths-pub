"""
Verify the identity at LARGE n by exact arithmetic in F_p, for several primes.

At n = 25 the Gram matrices are 625 x 625 and there are 625 multipliers, so the
rational evaluation of verify_general.py needs about 2.4e8 Fraction
multiplications per point -- hours.  The same computation in F_p is exact, and
vectorises: with p below 2^20 every intermediate stays well inside int64, so the
625 quadratic forms are 625 numpy matrix-vector products.

This is a genuine algebraic check, not a floating-point one: it proves the
identity modulo p.  Run over several unrelated primes it is conclusive for any
discrepancy that is not divisible by all of them, and the discrepancy would have
to be an exact rational with an astronomically structured numerator to hide.

Definiteness is NOT checked here -- verify_general.py does that over Q.
"""

import itertools
import os
import random
import sys
from fractions import Fraction as F
from math import comb, factorial

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "dittert"))
sys.path.insert(0, HERE)
import sos                                                       # noqa: E402
import verify_general as vg                                      # noqa: E402

K = 3
PRIMES = [1048573, 1048571, 1048559]


def fp(x, p):
    x = F(x)
    return (x.numerator % p) * pow(x.denominator % p, -1, p) % p


def sigma3_modp(A, n, p):
    """sum over 3-subsets I, J of per(A[I][J]), in F_p, vectorised."""
    trips = np.array(list(itertools.combinations(range(n), K)), dtype=np.int64)
    perms = list(itertools.permutations(range(K)))
    tot = 0
    for I in trips:
        sub = A[I][:, trips]                     # (3, T, 3)
        sub = np.transpose(sub, (1, 0, 2))       # (T, 3, 3)
        s = np.zeros(len(trips), dtype=np.int64)
        for pm in perms:
            t = np.ones(len(trips), dtype=np.int64)
            for a in range(K):
                t = (t * sub[:, a, pm[a]]) % p
            s = (s + t) % p
        tot = (tot + int(s.sum() % p)) % p
    return tot


def esym3_modp(v, p):
    e = [1, 0, 0, 0]
    for x in v:
        for j in range(K, 0, -1):
            e[j] = (e[j] + e[j - 1] * int(x)) % p
    return e[K]


def objective_modp(b, n, p):
    """F(b) mod p, from the definition."""
    inv_n = pow(n % p, -1, p)
    A = np.array([[(inv_n + b[i * n + j]) % p for j in range(n)]
                  for i in range(n)], dtype=np.int64)
    r = A.sum(axis=1) % p
    c = A.sum(axis=0) % p
    Cnk = comb(n, K) % p
    iC = pow(Cnk, -1, p)
    M = (2 - factorial(K) * pow(pow(n % p, K, p), -1, p)) % p
    e_r = esym3_modp(r, p)
    e_c = esym3_modp(c, p)
    s3 = sigma3_modp(A, n, p)
    Pk = s3 * iC % p * iC % p
    return (M - (e_r * iC % p + e_c * iC % p - Pk)) % p


def rhs_modp(b, n, G0, H, lam, p):
    N = n * n
    inv_n = pow(n % p, -1, p)
    tot = int(b @ ((G0 @ b) % p) % p)
    trans = sos.transporters(n, (0, 0))
    for q in range(N):
        gq = trans[q]
        w = b[np.array([gq[u] for u in range(N)], dtype=np.int64)]
        s = int(w @ ((H @ w) % p) % p)
        tot = (tot + (inv_n + int(b[q])) % p * s) % p
    lv = 0
    for mono, c in lam.items():
        t = c % p
        for v in mono:
            t = t * int(b[v]) % p
        lv = (lv + t) % p
    return (tot + lv * int(b.sum() % p)) % p


def run(n, trials=2, seed=5, vals19=None):
    print(f"\n=== n = {n}: identity in F_p, {len(PRIMES)} primes ===")
    vals19, G0q, Hq, lamq, basis = vg.certificate_at(n, vals19)
    N = n * n
    rng = random.Random(seed)
    pts = [[F(rng.randint(-40, 40), rng.randint(1, 9) * n) for _ in range(N)]
           for _ in range(trials)]
    allok = True
    for p in PRIMES:
        G0 = np.array([[fp(x, p) for x in row] for row in G0q], dtype=np.int64)
        H = np.array([[fp(x, p) for x in row] for row in Hq], dtype=np.int64)
        lam = {m: fp(c, p) for m, c in lamq.items()}
        for t, bq in enumerate(pts):
            b = np.array([fp(x, p) for x in bq], dtype=np.int64)
            lhs = objective_modp(b, n, p)
            rhs = rhs_modp(b, n, G0, H, lam, p)
            ok = lhs == rhs
            allok = allok and ok
            print(f"  p = {p}, point {t + 1}: F(b) == certificate -> {ok}"
                  + ("" if ok else f"   {lhs} vs {rhs}"))
    return allok


if __name__ == "__main__":
    ns = [int(a) for a in sys.argv[1:]] or [25]
    ok = True
    for n in ns:
        ok = run(n) and ok
    print(f"\nidentity confirmed in F_p at every prime and point: {ok}")
