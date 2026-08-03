"""
Decide, EXACTLY and for every n >= 4 at once, whether a candidate curve makes all
ten positivity quantities strictly positive.

This is the step that would make the k = 3 result uniform in n.  Everything before
it -- the closed-form constraint system, the solution over Q(n), the closed-form
block-diagonalisation -- reduces the conjecture at k = 3 to exactly this: ten
rational functions of n, all required positive on n >= 4.

Method.  Substitute n = m + 4 so the range becomes m >= 0.  Each quantity is a
ratio of polynomials in m; the denominators are products of powers of n, n-1 and
n-2, hence strictly positive there, so the sign is the numerator's (the sign of
the denominator is *checked*, not assumed).  Positivity of a univariate polynomial
on [0, infinity) is then decided by a STURM sequence: p > 0 on [0, inf) iff
p(0) > 0 and p has no root in (0, infinity), and the root count is the difference
of sign-variation counts of the Sturm sequence at 0 and at +infinity.

There is NO sufficiency gap here.  This is why the earlier "all coefficients
non-negative in m" idea was only ever a search heuristic: m^2 - m + 1 is positive
everywhere yet has a negative coefficient.
"""

import ast
import os
import sys
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "dittert"))
sys.path.insert(0, HERE)
import blocks as bl                                              # noqa: E402
import general_k3 as g                                           # noqa: E402
from general_k3 import RF, pdivmod, pmul, pscale, ptrim, pstr    # noqa: E402

RES = g.solve_symbolic(verbose=False)
FREE = RES["free_cols"]
PIV = RES["piv_cols"]
IDX = bl.svar_index()
NFREE = len(FREE)


# ------------------------------------------------------------------ Sturm chain
def poly_deriv(p):
    return ptrim([p[i] * i for i in range(1, len(p))])


def poly_gcd(a, b):
    a, b = ptrim(list(a)), ptrim(list(b))
    while b:
        _, r = pdivmod(a, b)
        a, b = b, r
    return pscale(a, F(1) / a[-1]) if a else a


def sturm_chain(p):
    """p0 = p, p1 = p', p_{k+1} = -rem(p_{k-1}, p_k)."""
    chain = [ptrim(list(p)), poly_deriv(p)]
    while chain[-1]:
        _, r = pdivmod(chain[-2], chain[-1])
        if not r:
            break
        chain.append(pscale(r, F(-1)))
    return [c for c in chain if c]


def sign_changes_at(chain, x):
    signs = []
    for c in chain:
        v = F(0)
        for co in reversed(c):
            v = v * x + co
        if v:
            signs.append(1 if v > 0 else -1)
    return sum(1 for i in range(len(signs) - 1) if signs[i] != signs[i + 1])


def sign_changes_at_infinity(chain):
    signs = [1 if c[-1] > 0 else -1 for c in chain if c]
    return sum(1 for i in range(len(signs) - 1) if signs[i] != signs[i + 1])


def positive_on_nonneg(p):
    """
    True iff p(m) > 0 for every real m >= 0.  Returns (verdict, detail).

    Squarefree part first: repeated roots do not change the sign pattern but do
    break the Sturm count, so we divide by gcd(p, p').
    """
    p = ptrim(list(p))
    if not p:
        return False, "identically zero"
    d = poly_gcd(p, poly_deriv(p))
    q, r = (p, []) if len(d) <= 1 else pdivmod(p, d)
    if r:
        return False, "gcd division was inexact"
    q = ptrim(list(q))
    if len(q) == 1:
        return (q[0] > 0), f"constant {q[0]}"
    at0 = q[0]
    if at0 == 0:
        return False, "vanishes at m = 0"
    chain = sturm_chain(q)
    v0 = sign_changes_at(chain, F(0))
    vinf = sign_changes_at_infinity(chain)
    roots = v0 - vinf
    ok = (at0 > 0) and roots == 0
    return ok, (f"squarefree degree {len(q)-1}, chain length {len(chain)}, "
                f"V(0)={v0}, V(inf)={vinf}, roots in (0,inf) = {roots}, "
                f"p(0) = {at0}")


# --------------------------------------------------------- the ten quantities
def shift_to_m(poly, shift=4):
    out, acc = [], [F(1)]
    for i, co in enumerate(poly):
        if i:
            acc = pmul(acc, [F(shift), F(1)])
        out = g.padd(out, pscale(acc, co))
    return ptrim(out)


def sign_on_n_ge_4(poly):
    p = shift_to_m(poly)
    if not p:
        return 0
    if all(c >= 0 for c in p) and p[0] > 0:
        return 1
    if all(c <= 0 for c in p) and p[0] < 0:
        return -1
    ok, _ = positive_on_nonneg(p)
    if ok:
        return 1
    ok, _ = positive_on_nonneg(pscale(p, F(-1)))
    return -1 if ok else 0


def quantities_rf(uq, E):
    """The ten quantities as exact rational functions of n."""
    nE = RF([F(0)] * E + [F(1)])
    fs = []
    for t in range(NFREE):
        num = []
        acc = [F(1)]
        for j, co in enumerate(uq[t]):
            if j:
                acc = pmul(acc, [F(-4), F(1)])       # (n-4)^j
            num = g.padd(num, pscale(acc, co))
        fs.append(RF(num) / nE)
    return quantities_rf_from(fs)


def quantities_rf_from(fs):
    """
    The ten quantities as exact rational functions of n, from the eight free
    variables given directly as elements of Q(n).  This is the general entry
    point; `quantities_rf` is the special case f_c = u_c(n-4)/n^E.
    """
    npoly = [F(0), F(1)]
    vals = [None] * 19
    for t, c in enumerate(FREE):
        vals[c] = fs[t]
    for i, c in enumerate(PIV):
        v = RES["b"][i]
        for t, fc in enumerate(FREE):
            a = RES["A"][i][fc]
            if a:
                v = v - a * fs[t]
        vals[c] = v

    a, b, c = vals[0], vals[1], vals[2]
    one = RF([F(1)])
    nrf = RF(npoly)
    m1 = nrf - one
    out = [("G0.theta0", a + b * (m1 * RF([F(2)])) + c * (m1 * m1)),
           ("G0.theta1", a + b * (nrf - RF([F(2)])) - c * m1),
           ("G0.theta2", a - b * RF([F(2)]) + c)]
    A, B, C, D = bl.blocks_rational_generic(nrf, vals[3:14], IDX, one=one)
    out.append(("H.A minor1", A[0][0]))
    out.append(("H.A minor2", A[0][0] * A[1][1] - A[0][1] * A[0][1]))
    out.append(("H.A minor3", _det3(A)))
    out.append(("H.B", B))
    out.append(("H.C minor1", C[0][0]))
    out.append(("H.C minor2", C[0][0] * C[1][1] - C[0][1] * C[0][1]))
    out.append(("H.D", D))
    return out


def _det3(M):
    return (M[0][0] * (M[1][1] * M[2][2] - M[1][2] * M[2][1])
            - M[0][1] * (M[1][0] * M[2][2] - M[1][2] * M[2][0])
            + M[0][2] * (M[1][0] * M[2][1] - M[1][1] * M[2][0]))


def verify_rf(qs, verbose=True):
    """Decide positivity on n >= 4 for a list of (name, rational function)."""
    allok = True
    for name, rf in qs:
        s = sign_on_n_ge_4(rf.den)
        if s == 0:
            print(f"  {name}: DENOMINATOR not sign-definite on n >= 4 -- "
                  f"cannot conclude")
            allok = False
            continue
        num_m = shift_to_m(pscale(rf.num, F(s)))
        ok, detail = positive_on_nonneg(num_m)
        allok = allok and ok
        if verbose:
            print(f"  {name:<12s} {'POSITIVE' if ok else '*** NOT POSITIVE'} "
                  f"on n >= 4")
            print(f"      denominator sign {s:+d};  {detail}")
    return allok


def verify(uq, E, verbose=True):
    return verify_rf(quantities_rf(uq, E), verbose=verbose)


def load_candidate(path=None):
    path = path or os.path.join(HERE, "results", "candidate_curve.txt")
    E, D, rows = ast.literal_eval(open(path).read())
    return [[F(x) for x in row] for row in rows], E, D


if __name__ == "__main__":
    uq, E, D = load_candidate()
    print(f"candidate curve: E={E}, D={D}")
    for t in range(NFREE):
        print(f"  f{FREE[t]:<2d} = ({pstr(uq[t], 'm')}) / n^{E}")
    print()
    print("STURM verification of the ten positivity quantities on n >= 4:")
    ok = verify(uq, E)
    print()
    print("ALL TEN POSITIVE FOR EVERY n >= 4" if ok
          else "NOT ESTABLISHED for all n >= 4")
    sys.exit(0 if ok else 1)
