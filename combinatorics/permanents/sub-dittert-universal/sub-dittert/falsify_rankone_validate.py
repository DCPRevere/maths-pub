#!/usr/bin/env python3
"""
Validation of the rank-one Phi_k implementation against the TRUSTED builder in
results/verify_subdittert.py (build_F and direct_sigma_k).

Claim under test.  For x, y >= 0 with (sum x)(sum y) = n, put A = x y^T.  Set
u = (sum y) * x  (= the row sums r) and v = (sum x) * y  (= the column sums c);
then sum u = sum v = n and A = u v^T / n.  With

    a = e_k(u)/C(n,k),   b = e_k(v)/C(n,k),   gamma = k!/n^k,

the claim is

    Phi_k(A) = E_k(r) + E_k(c) - P_k(A) = a + b - gamma * a * b.

Three independent evaluations are compared, exactly over Q:
  (i)   the closed form above (the scanner's formula),
  (ii)  E_k(r) + E_k(c) - sigma_k/C(n,k)^2 with sigma_k from the trusted
        direct_sigma_k (brute-force subpermanent enumeration),
  (iii) (2 - gamma) - F(A - J/n) with F the trusted build_F polynomial.

Run:  python3 falsify_rankone_validate.py
"""

import importlib.util
import itertools
import os
import sys
from fractions import Fraction as Q

HERE = os.path.dirname(os.path.abspath(__file__))
TRUSTED = os.path.join(HERE, "results", "verify_subdittert.py")

spec = importlib.util.spec_from_file_location("trusted_verifier", TRUSTED)
T = importlib.util.module_from_spec(spec)
spec.loader.exec_module(T)


# ------------------------------------------------------- the scanner's formula
def ek(vec, k):
    """e_k of a list of Fractions, by the standard O(nk) recurrence."""
    e = [Q(0)] * (k + 1)
    e[0] = Q(1)
    for t in vec:
        for j in range(k, 0, -1):
            e[j] += e[j - 1] * t
    return e[k]


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


def phi_closed(u, v, n, k):
    """Phi_k on A = u v^T / n, by the closed rank-one form."""
    C = binom(n, k)
    a = Q(ek(u, k), C)
    b = Q(ek(v, k), C)
    gamma = Q(fact(k), n ** k)
    return a + b - gamma * a * b, a, b


# --------------------------------------------------- routes through the trusted code
def phi_via_direct_sigma(u, v, n, k):
    A = [[u[i] * v[j] / n for j in range(n)] for i in range(n)]
    r = [sum(A[i][j] for j in range(n)) for i in range(n)]
    c = [sum(A[i][j] for i in range(n)) for j in range(n)]
    C = binom(n, k)
    sig = T.direct_sigma_k(A, n, k)
    return Q(ek(r, k), C) + Q(ek(c, k), C) - Q(sig, C * C), A


def phi_via_buildF(Fpoly, M, A, n):
    """(2 - gamma) - F(b) at b = A - J/n, using the trusted F polynomial."""
    b = [A[i][j] - Q(1, n) for i in range(n) for j in range(n)]
    tot = Q(0)
    for mono, coef in Fpoly.items():
        p = coef
        for idx in mono:
            p *= b[idx]
        tot += p
    return M - tot


# ------------------------------------------------------------------------ cases
def cases(n):
    """A spread of rank-one data: u, v >= 0 with sum u = sum v = n."""
    out = []
    ones = [Q(1)] * n
    out.append((ones, ones))
    # two-value
    u = [Q(3, 2)] * 2 + [Q(n - 3, n - 2)] * (n - 2)
    u = [x * Q(n, sum(u)) for x in u]
    v = [Q(1, 3)] * (n - 1) + [Q(1)]
    v = [x * Q(n, sum(v)) for x in v]
    out.append((u, v))
    # one spike
    u = [Q(5, 2)] + [Q(1)] * (n - 1)
    u = [x * Q(n, sum(u)) for x in u]
    v = [Q(1)] * (n - 1) + [Q(7, 3)]
    v = [x * Q(n, sum(v)) for x in v]
    out.append((u, v))
    # a zero entry (boundary of K_n)
    u = [Q(0)] + [Q(n, n - 1)] * (n - 1)
    v = [Q(0), Q(0)] + [Q(n, n - 2)] * (n - 2)
    out.append((u, v))
    # ragged rationals
    u = [Q(i * 7 % 11 + 1, 5) for i in range(n)]
    u = [x * Q(n, sum(u)) for x in u]
    v = [Q(i * 3 % 7 + 2, 4) for i in range(n)]
    v = [x * Q(n, sum(v)) for x in v]
    out.append((u, v))
    # extreme concentration
    u = [Q(n)] + [Q(0)] * (n - 1)
    v = [Q(n, 2), Q(n, 2)] + [Q(0)] * (n - 2)
    out.append((u, v))
    return out


def main():
    allok = True
    for (n, k) in [(4, 3), (5, 4)]:
        print("=" * 70)
        print(f"(n,k) = ({n},{k})   gamma = {k}!/{n}^{k} = "
              f"{Q(fact(k), n ** k)}   bound 2-gamma = {Q(2) - Q(fact(k), n**k)}")
        Fpoly, M, _ = T.build_F(n, k)
        assert M == Q(2) - Q(fact(k), n ** k)
        for idx, (u, v) in enumerate(cases(n)):
            assert sum(u) == n and sum(v) == n, "normalisation broken"
            p1, a, b = phi_closed(u, v, n, k)
            p2, A = phi_via_direct_sigma(u, v, n, k)
            p3 = phi_via_buildF(Fpoly, M, A, n)
            ok = (p1 == p2 == p3)
            allok &= ok
            print(f"  case {idx}: closed={p1}  direct_sigma={p2}  buildF={p3}"
                  f"  -> {'AGREE' if ok else '*** DISAGREE ***'}")
            if not ok:
                print(f"     u={u}\n     v={v}")
        # also confirm sigma_k(xy^T) = k! e_k(x) e_k(y) on the raw (unnormalised) form
        for idx, (u, v) in enumerate(cases(n)):
            x = u
            y = [t / n for t in v]          # A = x y^T with this split
            A = [[x[i] * y[j] for j in range(n)] for i in range(n)]
            lhs = T.direct_sigma_k(A, n, k)
            rhs = fact(k) * ek(x, k) * ek(y, k)
            ok = (lhs == rhs)
            allok &= ok
            if not ok:
                print(f"  *** sigma_k identity failed, case {idx}: "
                      f"{lhs} != {rhs}")
        print(f"  sigma_k(x y^T) = k! e_k(x) e_k(y) on all cases: OK")
    print()
    print("VALIDATION " + ("PASSED" if allok else "*** FAILED ***"))
    return 0 if allok else 1


if __name__ == "__main__":
    sys.exit(main())
