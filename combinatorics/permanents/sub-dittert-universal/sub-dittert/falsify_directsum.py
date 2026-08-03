#!/usr/bin/env python3
"""
Counterexample scan for the Cheon-Hwang sub-Dittert conjecture over BLOCK DIRECT
SUMS of scaled flat blocks.

    K_n  = { A >= 0 entrywise, sum_ij A_ij = n }
    E_k(v) = e_k(v)/C(n,k)          P_k(A) = sigma_k(A)/C(n,k)^2
    Phi_k(A) = E_k(r) + E_k(c) - P_k(A)   <=?   2 - k!/n^k

Family scanned:

    two-block   A(p,s) = (s * J_p / p)  (+)  ((n-s) * J_q / q),   p+q = n, 0<=s<=n
    three-block A       = (s1*J_p/p) (+) (s2*J_q/q) (+) (s3*J_r/r), s1+s2+s3 = n

Closed forms used (each validated against brute force below):

    a p x p flat block of total mass t has entry t/p^2 and row sum t/p, so
        sigma_j = j! * C(p,j)^2 * (t/p^2)^j
    sigma_k(B1 (+) B2) = sum_j sigma_j(B1) sigma_{k-j}(B2)      [block convolution]
    row sums = p copies of s/p and q copies of (n-s)/q, so e_k(r) is the
    two-value elementary symmetric  sum_i C(p,i) C(q,k-i) a^i b^{k-i}.

NOTE.  This family never contains J_n/n: at s = p all row and column sums equal 1
(the matrix is doubly stochastic) but the matrix is block diagonal with entries
1/p and 1/q, not 1/n.  So D is expected to be strictly positive on [0,n] and the
Bernstein certificate has no touching-zero degeneracy to work around.  The point
s = p is nevertheless the most dangerous one in the family: there Phi reduces to
2 - P_k(A), so the conjecture there is exactly the claim that J_n/n minimises
sigma_k over doubly stochastic matrices.

Everything is Fraction (exact).  Floats are never used in a decision.

The scan works with the DEFICIT polynomial

    D(s) = (2 - k!/n^k) - Phi_k(A(p,s)),

a polynomial in s of degree k with rational coefficients.  A counterexample is a
point of [0,n] with D(s) < 0.  We decide the sign of D on [0,n] with an exact
Bernstein positivity certificate plus dyadic subdivision: all Bernstein
coefficients of a cell positive PROVES D > 0 on that cell, and a negative
endpoint value is an attained counterexample.  Independently, the exact critical
points of D (roots of D', isolated by exact bisection) give the largest Phi in
the family, reported as an exact ratio Phi/(2 - k!/n^k).

Usage:
    python3 falsify_directsum.py validate
    python3 falsify_directsum.py sweep  <n_lo> <n_hi>
    python3 falsify_directsum.py three  <n_lo> <n_hi>
"""

import itertools
import json
import random
import sys
from fractions import Fraction as Q

# --------------------------------------------------------------------------
# brute force, straight from the definitions
# --------------------------------------------------------------------------


def binom(n, k):
    if k < 0 or k > n:
        return 0
    r = 1
    for i in range(k):
        r = r * (n - i) // (i + 1)
    return r


def factorial(n):
    r = 1
    for i in range(2, n + 1):
        r *= i
    return r


def brute_sigma_k(A, n, k):
    """sum of permanents of all k x k submatrices, row set and column set chosen
    independently.  Definition, no shortcuts."""
    tot = Q(0)
    for al in itertools.combinations(range(n), k):
        for be in itertools.combinations(range(n), k):
            for s in itertools.permutations(range(k)):
                pr = Q(1)
                for t in range(k):
                    pr *= A[al[t]][be[s[t]]]
                tot += pr
    return tot


def ryser_sigma_k(A, n, k):
    """Second, structurally different route: per(A + xJ) = sum_j x^{n-j} (n-j)!
    sigma_j(A), the order-n permanent by Ryser inclusion-exclusion."""

    def umul(p, q):
        o = [Q(0)] * (len(p) + len(q) - 1)
        for i, a in enumerate(p):
            if a:
                for j, b in enumerate(q):
                    if b:
                        o[i + j] += a * b
        return o

    def uadd(p, q):
        m = max(len(p), len(q))
        return [
            (p[i] if i < len(p) else Q(0)) + (q[i] if i < len(q) else Q(0))
            for i in range(m)
        ]

    tot = [Q(0)]
    for r in range(1, n + 1):
        for S in itertools.combinations(range(n), r):
            prod = [Q(1)]
            for i in range(n):
                s = [Q(0), Q(0)]
                for j in S:
                    s = uadd(s, [A[i][j], Q(1)])
                prod = umul(prod, s)
            sgn = Q((-1) ** (n - r))
            tot = uadd(tot, [sgn * c for c in prod])
    while len(tot) < n + 1:
        tot.append(Q(0))
    return tot[n - k] / factorial(n - k)


def elem_sym(vec, k):
    e = [Q(1)] + [Q(0)] * k
    for v in vec:
        for j in range(k, 0, -1):
            e[j] += e[j - 1] * v
    return e[k]


def brute_phi(A, n, k, sigma=None):
    """Phi_k(A) = E_k(r) + E_k(c) - P_k(A), from the definition."""
    r = [sum(row, Q(0)) for row in A]
    c = [sum(A[i][j] for i in range(n)) for j in range(n)]
    C = binom(n, k)
    if sigma is None:
        sigma = brute_sigma_k(A, n, k)
    return elem_sym(r, k) / C + elem_sym(c, k) / C - sigma / (C * C)


def bound(n, k):
    return Q(2) - Q(factorial(k), n**k)


def block_matrix(parts, n):
    """parts = [(size, total mass), ...]; returns the direct sum, entries Fractions."""
    A = [[Q(0)] * n for _ in range(n)]
    off = 0
    for (sz, mass) in parts:
        val = Q(mass) / (sz * sz)          # total mass `mass`, row sum mass/sz
        for i in range(sz):
            for j in range(sz):
                A[off + i][off + j] = val
        off += sz
    return A


# --------------------------------------------------------------------------
# closed forms
# --------------------------------------------------------------------------


def sigma_flat(j, p, t):
    """sigma_j of the p x p flat block of TOTAL MASS t (entry t/p^2, row sum t/p):
    every j x j submatrix is flat, so its permanent is j! (t/p^2)^j, and there are
    C(p,j)^2 of them."""
    if j > p:
        return Q(0)
    return Q(factorial(j)) * binom(p, j) ** 2 * (Q(t) / (p * p)) ** j


def sigma_direct_sum(sizes, masses, k):
    """sigma_k of a direct sum, by convolution over the blocks."""
    conv = [Q(1)] + [Q(0)] * k
    for (p, t) in zip(sizes, masses):
        new = [Q(0)] * (k + 1)
        for j in range(k + 1):
            if conv[j] == 0:
                continue
            for i in range(0, min(p, k - j) + 1):
                new[j + i] += conv[j] * sigma_flat(i, p, t)
        conv = new
    return conv[k]


def phi_closed(sizes, masses, n, k):
    rows = []
    for (p, t) in zip(sizes, masses):
        rows += [Q(t) / p] * p
    C = binom(n, k)
    e = elem_sym(rows, k)
    return Q(2) * e / C - sigma_direct_sum(sizes, masses, k) / (C * C)


# --------------------------------------------------------------------------
# polynomial helpers (dense coefficient lists, index = power of s)
# --------------------------------------------------------------------------


def pmul(a, b):
    o = [Q(0)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                if y:
                    o[i + j] += x * y
    return o


def padd(a, b):
    m = max(len(a), len(b))
    return [
        (a[i] if i < len(a) else Q(0)) + (b[i] if i < len(b) else Q(0))
        for i in range(m)
    ]


def pscale(a, s):
    return [c * s for c in a]


def peval(a, x):
    r = Q(0)
    for c in reversed(a):
        r = r * x + c
    return r


def pderiv(a):
    return [a[i] * i for i in range(1, len(a))] or [Q(0)]


def pow_n_minus_s(n, m):
    """(n - s)^m as a coefficient list."""
    return [Q(binom(m, i) * n ** (m - i) * (-1) ** i) for i in range(m + 1)]


def deficit_poly(n, k, p):
    """D(s) = (2 - k!/n^k) - Phi_k(A(p,s)) as an exact polynomial in s."""
    q = n - p
    C = binom(n, k)
    # e_k(r) = sum_i C(p,i) C(q,k-i) s^i (n-s)^{k-i} / (p^i q^{k-i})
    ek = [Q(0)]
    for i in range(max(0, k - q), min(k, p) + 1):
        coef = Q(binom(p, i) * binom(q, k - i), p**i * q ** (k - i))
        term = pmul([Q(0)] * i + [Q(1)], pow_n_minus_s(n, k - i))
        ek = padd(ek, pscale(term, coef))
    # sigma_k = sum_j j! C(p,j)^2 (s/p)^j (k-j)! C(q,k-j)^2 ((n-s)/q)^{k-j}
    sg = [Q(0)]
    for j in range(max(0, k - q), min(k, p) + 1):
        coef = Q(
            factorial(j) * binom(p, j) ** 2 * factorial(k - j) * binom(q, k - j) ** 2,
            p ** (2 * j) * q ** (2 * (k - j)),
        )
        term = pmul([Q(0)] * j + [Q(1)], pow_n_minus_s(n, k - j))
        sg = padd(sg, pscale(term, coef))
    phi = padd(pscale(ek, Q(2, C)), pscale(sg, Q(-1, C * C)))
    D = padd([bound(n, k)], pscale(phi, Q(-1)))
    while len(D) > 1 and D[-1] == 0:
        D.pop()
    return D


def divide_root(a, r):
    """Synthetic division of a by (s - r).  Returns (quotient, remainder)."""
    d = len(a) - 1
    out = [Q(0)] * d
    acc = a[d]
    for i in range(d - 1, -1, -1):
        out[i] = acc
        acc = a[i] + acc * r
    return out, acc


# --------------------------------------------------------------------------
# exact Bernstein positivity certificate on [0, n]
# --------------------------------------------------------------------------


def to_bernstein(coeffs, n):
    """Bernstein coefficients on [0,n] of the polynomial given in the power basis."""
    d = len(coeffs) - 1
    A = [coeffs[j] * Q(n) ** j for j in range(d + 1)]
    b = []
    for i in range(d + 1):
        s = Q(0)
        for j in range(i + 1):
            s += Q(binom(i, j), binom(d, j)) * A[j]
        b.append(s)
    return b


def de_casteljau_halves(b):
    """Split Bernstein control coefficients at the midpoint."""
    d = len(b) - 1
    tri = [list(b)]
    for _ in range(d):
        prev = tri[-1]
        tri.append([(prev[i] + prev[i + 1]) / 2 for i in range(len(prev) - 1)])
    left = [tri[i][0] for i in range(d + 1)]
    right = [tri[d - i][i] for i in range(d + 1)]
    return left, right


def certify_positive(coeffs, n, max_depth=14):
    """Decide the sign of the polynomial on [0,n].

    Returns (verdict, info).  verdict is
      'positive'    -- proved > 0 on the whole interval,
      'negative'    -- an exact point with value < 0 was found (info = (s, value)),
      'unresolved'  -- subdivision depth exhausted (info = worst cell + min value).
    """
    b0 = to_bernstein(coeffs, n)
    stack = [(Q(0), Q(n), b0, 0)]
    worst = None  # (min attained value, s)
    unresolved = []
    while stack:
        lo, hi, b, dep = stack.pop()
        for (val, s) in ((b[0], lo), (b[-1], hi)):
            if worst is None or val < worst[0]:
                worst = (val, s)
            if val < 0:
                return "negative", (s, val)
        if min(b) > 0:
            continue
        if dep >= max_depth:
            unresolved.append((lo, hi, min(b)))
            continue
        L, R = de_casteljau_halves(b)
        mid = (lo + hi) / 2
        stack.append((lo, mid, L, dep + 1))
        stack.append((mid, hi, R, dep + 1))
    if unresolved:
        return "unresolved", (unresolved, worst)
    return "positive", worst


# --------------------------------------------------------------------------
# non-trivial critical points of Phi
# --------------------------------------------------------------------------


def isolate_roots(poly, lo, hi, samples, iters=48):
    """Rational approximations to sign-change roots of poly on [lo,hi]."""
    out = []
    step = (Q(hi) - Q(lo)) / samples
    xs = [Q(lo) + step * i for i in range(samples + 1)]
    vals = [peval(poly, x) for x in xs]
    for i in range(samples):
        a, fa, bb, fb = xs[i], vals[i], xs[i + 1], vals[i + 1]
        if fa == 0:
            out.append(a)
            continue
        if fa * fb < 0:
            for _ in range(iters):
                m = (a + bb) / 2
                fm = peval(poly, m)
                if fm == 0:
                    a = bb = m
                    break
                if fa * fm < 0:
                    bb, fb = m, fm
                else:
                    a, fa = m, fm
            out.append((a + bb) / 2)
    if peval(poly, Q(hi)) == 0:
        out.append(Q(hi))
    return out


# --------------------------------------------------------------------------
# validation
# --------------------------------------------------------------------------


def validate():
    ok = True
    print("=== 1. block convolution identity vs brute force ===")
    for (n, k, p) in [(5, 3, 2), (5, 3, 1), (6, 4, 3), (6, 3, 2)]:
        qq = n - p
        for s in [Q(0), Q(1), Q(3, 2), Q(n, 2), Q(7, 3), Q(n)]:
            A = block_matrix([(p, s), (qq, Q(n) - s)], n)
            bf = brute_sigma_k(A, n, k)
            cf = sigma_direct_sum([p, qq], [s, Q(n) - s], k)
            good = bf == cf
            ok &= good
            if not good:
                print(f"  MISMATCH n={n} k={k} p={p} s={s}: {bf} vs {cf}")
        print(f"  n={n} k={k} p={p}: convolution matches brute sigma_k at all s  OK")

    print("=== 1b. brute sigma_k vs Ryser (independent algorithm) ===")
    rnd = random.Random(20260731)
    for n in (4, 5):
        for k in (2, 3, 4):
            if k > n:
                continue
            A = [[Q(rnd.randrange(0, 7), rnd.randrange(1, 5)) for _ in range(n)]
                 for _ in range(n)]
            a, b = brute_sigma_k(A, n, k), ryser_sigma_k(A, n, k)
            ok &= a == b
            print(f"  n={n} k={k}: direct={a == b and 'Ryser' or 'MISMATCH'} OK")

    print("=== 2. closed-form Phi vs definition, (n,k) = (4,3) and (5,4) ===")
    for (n, k) in [(4, 3), (5, 4)]:
        for trial in range(6):
            p = rnd.randrange(1, n)
            qq = n - p
            s = Q(rnd.randrange(0, 4 * n + 1), 4)
            A = block_matrix([(p, s), (qq, Q(n) - s)], n)
            assert sum(sum(row) for row in A) == n
            direct = brute_phi(A, n, k)
            closed = phi_closed([p, qq], [s, Q(n) - s], n, k)
            polyv = bound(n, k) - peval(deficit_poly(n, k, p), s)
            good = direct == closed == polyv
            ok &= good
            print(f"  n={n} k={k} p={p} s={s}: Phi={direct}  "
                  f"closed {'OK' if direct == closed else 'MISMATCH'}  "
                  f"poly {'OK' if direct == polyv else 'MISMATCH'}")

    print("=== 2b. three-block closed form vs definition ===")
    for (n, k, parts) in [(6, 3, (1, 2, 3)), (6, 4, (2, 2, 2)), (5, 3, (1, 1, 3))]:
        ms = [Q(1), Q(3, 2), Q(n) - Q(1) - Q(3, 2)]
        A = block_matrix(list(zip(parts, ms)), n)
        direct = brute_phi(A, n, k)
        closed = phi_closed(list(parts), ms, n, k)
        ok &= direct == closed
        print(f"  n={n} k={k} sizes={parts}: {'OK' if direct == closed else 'MISMATCH'}")

    print("=== 3. sanity: J_n/n attains the bound exactly ===")
    for (n, k) in [(4, 3), (5, 4), (6, 5)]:
        A = block_matrix([(n, Q(n))], n)
        v = brute_phi(A, n, k)
        good = v == bound(n, k)
        ok &= good
        print(f"  n={n} k={k}: Phi={v} bound={bound(n,k)} {'OK' if good else 'BAD'}")

    print("\nVALIDATION", "PASSED" if ok else "FAILED")
    return ok


# --------------------------------------------------------------------------
# two-block sweep
# --------------------------------------------------------------------------


def sweep(n_lo, n_hi):
    hits = []
    unresolved = []
    approaches = []
    ncells = 0
    for n in range(n_lo, n_hi + 1):
        for k in range(5, n):
            gam = bound(n, k)
            for p in range(1, n // 2 + 1):
                ncells += 1
                D = deficit_poly(n, k, p)
                verdict, info = certify_positive(D, n)
                if verdict == "negative":
                    s, val = info
                    hits.append((n, k, p, s, val))
                    print(json.dumps({"event": "HIT-CANDIDATE", "n": n, "k": k,
                                      "p": p, "s": str(s)}), flush=True)
                elif verdict == "unresolved":
                    cells, worst = info
                    unresolved.append((n, k, p, [(str(a), str(b), str(c))
                                                 for a, b, c in cells[:3]]))
                    print(json.dumps({"event": "UNRESOLVED", "n": n, "k": k,
                                      "p": p, "cells": len(cells)}), flush=True)
                # largest Phi in the family = smallest D: endpoints + critical points
                cand = [Q(0), Q(n)] + isolate_roots(pderiv(D), 0, n, max(8, 2 * n))
                best = None
                for s in cand:
                    if s < 0 or s > n:
                        continue
                    d = peval(D, s)
                    if best is None or d < best[0]:
                        best = (d, s)
                if best is not None:
                    d, s = best
                    approaches.append((gam - d, gam, n, k, p, s, d))
        print(json.dumps({"event": "n-done", "n": n, "cells": ncells,
                          "hits": len(hits), "unresolved": len(unresolved)}),
              flush=True)
    approaches.sort(key=lambda t: -(t[0] / t[1]))
    out = {
        "cells": ncells,
        "hits": [(n, k, p, str(s), str(v)) for (n, k, p, s, v) in hits],
        "unresolved": unresolved,
        "top": [
            {"n": n, "k": k, "p": p, "s": str(s),
             "phi": str(phi), "bound": str(g), "deficit": str(d),
             "ratio": str(phi / g), "ratio_float": float(phi / g)}
            for (phi, g, n, k, p, s, d) in approaches[:15]
        ],
    }
    print("RESULT " + json.dumps(out), flush=True)
    return out


# --------------------------------------------------------------------------
# three-block scan
# --------------------------------------------------------------------------


def three(n_lo, n_hi, grid=None):
    hits = []
    approaches = []
    ncells = 0
    for n in range(n_lo, n_hi + 1):
        G = grid or max(12, 2 * n)
        for k in range(5, n):
            gam = bound(n, k)
            for p in range(1, n - 1):
                for qq in range(p, n - p):
                    r = n - p - qq
                    if r < qq:
                        continue
                    ncells += 1
                    for i in range(G + 1):
                        for j in range(G + 1 - i):
                            s1 = Q(n * i, G)
                            s2 = Q(n * j, G)
                            s3 = Q(n) - s1 - s2
                            phi = phi_closed([p, qq, r], [s1, s2, s3], n, k)
                            d = gam - phi
                            if d < 0:
                                hits.append((n, k, p, qq, r, s1, s2, s3, phi))
                                print(json.dumps({"event": "HIT-CANDIDATE-3",
                                                  "n": n, "k": k,
                                                  "sizes": [p, qq, r],
                                                  "masses": [str(s1), str(s2),
                                                             str(s3)]}), flush=True)
                            approaches.append((phi, gam, n, k,
                                               (p, qq, r), (s1, s2, s3)))
        print(json.dumps({"event": "n-done-3", "n": n, "cells": ncells,
                          "hits": len(hits)}), flush=True)
    approaches.sort(key=lambda t: -(t[0] / t[1]))
    out = {
        "cells": ncells,
        "hits": len(hits),
        "top": [
            {"n": n, "k": k, "sizes": list(sz),
             "masses": [str(x) for x in ms],
             "phi": str(phi), "bound": str(g), "ratio": str(phi / g),
             "ratio_float": float(phi / g)}
            for (phi, g, n, k, sz, ms) in approaches[:15]
        ],
    }
    print("RESULT3 " + json.dumps(out), flush=True)
    return out


if __name__ == "__main__":
    cmd = sys.argv[1] if len(sys.argv) > 1 else "validate"
    if cmd == "validate":
        sys.exit(0 if validate() else 1)
    elif cmd == "sweep":
        sweep(int(sys.argv[2]), int(sys.argv[3]))
    elif cmd == "three":
        three(int(sys.argv[2]), int(sys.argv[3]),
              int(sys.argv[4]) if len(sys.argv) > 4 else None)
    else:
        raise SystemExit("unknown command " + cmd)
