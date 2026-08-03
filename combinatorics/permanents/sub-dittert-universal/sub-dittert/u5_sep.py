#!/usr/bin/env python3
"""The separating family for U5.

Pattern SPIDER3 (e = 9): a centre column vertex of degree 3, joined by one
edge each to three row vertices, each of which carries a double edge to a
private column vertex.  Degrees (3,3,3 | 2,2,2,3), all >= 2, connected --
a genuine term of K_9.

    S = sum_j h_j^3,   h = B^T r,   r_w = row-w squared norm.

Family CE(m, M, s, t): doubly centred, but NOT of the form A - J/n.
  m heavy rows: entry s in the centre column, t and -(s+t) in two private
  columns of its own;  M light rows, all equal, cancelling every column sum.
Exact rational data; the operator norm is certified by a rational bound on
the top eigenvalue of the Gram matrix.
"""
from fractions import Fraction as Fr


def family(m, M, s, t):
    """Return (Q, S, gram2x2, r_h, r_l) exactly."""
    s, t = Fr(s), Fr(t)
    u = -(s + t)
    r_h = s * s + t * t + u * u
    k = m * s * s + t * t + u * u
    r_l = (m * m * s * s + m * (t * t + u * u)) / Fr(M * M)
    Q = m * r_h + M * r_l
    D = r_h - r_l
    S = D ** 3 * m * (m * m * s ** 3 + t ** 3 + u ** 3)
    # Gram top block on the (1_m, 1_M) plane, exact 2x2
    a11 = r_h - s * s + m * s * s
    a22 = M * r_l
    a12sq = (Fr(k, M) ** 2) * m * M          # (a12)^2
    return Q, S, (a11, a22, a12sq), r_h, r_l


def op2_upper(g):
    """Rational upper bound for the top eigenvalue of the 2x2 [[a11,a12],[a12,a22]]
    (and hence for ||B||_op^2, the rest of the spectrum being <= r_h - s^2)."""
    a11, a22, a12sq = g
    # lam = (a11+a22)/2 + sqrt(((a11-a22)/2)^2 + a12sq);  bound the sqrt above
    c = ((a11 - a22) / 2) ** 2 + a12sq
    # rational upper bound for sqrt(c): (c + q^2) / (2q) for any q > 0  (AM-GM)
    q = Fr(int(float(c) ** 0.5 * 10 ** 6) + 1, 10 ** 6)
    for _ in range(3):
        q = ((q + c / q) / 2).limit_denominator(10 ** 12)
    return (a11 + a22) / 2 + (c + q * q) / (2 * q)


if __name__ == "__main__":
    print(f"{'m':>6} {'M':>7} {'Q':>12} {'S':>14} {'tau^2<=':>10} "
          f"{'S/(Q tau^7)':>14}")
    for m in (4, 16, 64, 128, 256, 1024, 4096):
        M = 8 * m + 8
        s, t = Fr(1, m), Fr(7, 10)      # s ~ 1/m keeps the Gram tame
        Q, S, g, r_h, r_l = family(m, M, s, t)
        lam = op2_upper(g)
        lam = max(lam, r_h - s * s)
        rhs = Q * lam ** Fr(7, 2) if False else None
        # compare S^2 against Q^2 lam^7 (exact, avoids the square root)
        lhs = S * S
        rhs = Q * Q * lam ** 7
        ratio = float(lhs / rhs) ** 0.5
        print(f"{m:>6} {M:>7} {float(Q):>12.4f} {float(S):>14.4f} "
              f"{float(lam):>10.4f} {ratio:>14.6f}"
              + ("   <<< U5 FAILS" if lhs > rhs else ""))
    print()
    print("with s = 1/sqrt(m) (the aligned choice), rationalised as s = p/q ~ m^-1/2:")
    for m in (4, 16, 64, 144, 256, 1024, 4096, 16384):
        M = 8 * m + 8
        import math
        s = Fr(round(10 ** 6 / math.sqrt(m)), 10 ** 6)
        t = Fr(7, 10)
        Q, S, g, r_h, r_l = family(m, M, s, t)
        lam = max(op2_upper(g), r_h - s * s)
        lhs, rhs = S * S, Q * Q * lam ** 7
        ratio = float(lhs / rhs) ** 0.5
        print(f"{m:>6} {M:>7} {float(Q):>12.4f} {float(S):>14.4f} "
              f"{float(lam):>10.4f} {ratio:>14.6f}"
              + ("   <<< U5 FAILS" if lhs > rhs else ""))
