#!/usr/bin/env python3
"""Validate falsify_pencils.phi_all_k against the TRUSTED builder in
results/verify_subdittert.py at (n,k) = (4,3) and (5,4).

Two independent checks per case:
  A. sigma_k from my integer Ryser route == direct_sigma_k (subpermanent
     enumeration from the definition) on random rational A in K_n.
  B. my Phi_k(A) == M - F(A - J/n) where (F, M) come from build_F(n,k),
     the symbolic construction used by the certificate verifier.
"""
import os
import random
import sys
from fractions import Fraction as Q

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, "results"))

import falsify_pencils as fp                      # noqa: E402
import verify_subdittert as vs                    # noqa: E402


def rand_K(n, rng, dmax=9):
    """Random A in K_n as (integer numerator matrix, denominator)."""
    while True:
        M = [[rng.randint(0, dmax) for _ in range(n)] for _ in range(n)]
        tot = sum(sum(r) for r in M)
        if tot:
            break
    # A = M/D with sum A = n  =>  D = tot/n
    return [[x * n for x in row] for row in M], tot


def evalF(F, b, n):
    tot = Q(0)
    for mono, c in F.items():
        v = c
        for idx in mono:
            v *= b[idx // n][idx % n]
        tot += v
    return tot


def main():
    rng = random.Random(20260731)
    ok = True
    for n, k in ((4, 3), (5, 4)):
        F, M, _ = vs.build_F(n, k)
        assert M == fp.bound(n, k), (n, k, M, fp.bound(n, k))
        for trial in range(6):
            Mi, D = rand_K(n, rng)
            A = [[Q(Mi[i][j], D) for j in range(n)] for i in range(n)]
            assert sum(sum(r) for r in A) == n
            s_mine = Q(fp.sigma_all_int(Mi, n)[k], Q(D) ** k)
            s_ref = vs.direct_sigma_k(A, n, k)
            phi_mine = fp.phi_all_k(Mi, D, n)[k]
            b = [[A[i][j] - Q(1, n) for j in range(n)] for i in range(n)]
            phi_ref = M - evalF(F, b, n)
            good = (s_mine == s_ref) and (phi_mine == phi_ref)
            ok &= good
            print(f"n={n} k={k} trial={trial}  sigma_k match={s_mine == s_ref}"
                  f"  Phi match={phi_mine == phi_ref}  Phi={phi_mine}")
        # also at J/n itself: Phi must equal M exactly
        Jn = [[1] * n for _ in range(n)]      # A = Jn/n, entry sum = n
        phiJ = fp.phi_all_k(Jn, n, n)[k]
        print(f"n={n} k={k}  Phi(J/n) == M : {phiJ == M}   (M = {M})")
        ok &= (phiJ == M)
        # cross-check Ryser route in the reference against mine on one point
        Mi, D = rand_K(n, rng)
        A = [[Q(Mi[i][j], D) for j in range(n)] for i in range(n)]
        r2 = vs.ryser_sigma_k(A, n, k)
        ok &= (r2 == Q(fp.sigma_all_int(Mi, n)[k], Q(D) ** k))
        print(f"n={n} k={k}  reference-Ryser cross-check: "
              f"{r2 == Q(fp.sigma_all_int(Mi, n)[k], Q(D) ** k)}")
    print("VALIDATION", "PASS" if ok else "FAIL")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
