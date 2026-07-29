"""
Close the design step for k = 3, ALL n >= 4, by linear programming over Q.

The previous attempt searched for a rigid ansatz passing near the SDP optima.
That was the wrong tool: the optimum maximises a least eigenvalue, sits wherever
the two cones happen to balance, and has no reason to be a rational function of n.
We do not need an optimum -- ANY feasible point is a certificate.  So trade
optimality for structure and make the search exact and finite.

THREE LINEARISATIONS, all sufficient rather than necessary, which is fine.

1.  HANDELMAN ON A HALF-LINE.  Substitute n = 4 + m and require m >= 0.  Every
    quantity is a rational function of n whose denominator is a product of powers
    of n, (n-1) and (n-2), all strictly positive for n >= 4.  So the sign is the
    sign of the numerator.  A polynomial in m with ALL COEFFICIENTS >= 0 and a
    strictly positive constant term is strictly positive on m >= 0.  That is a
    sufficient condition, and it is LINEAR in the unknown coefficients.

2.  DIAGONAL DOMINANCE INSTEAD OF MINORS.  Six of the ten positivity quantities
    are principal minors, which are non-linear in the Gram entries.  Strict
    diagonal dominance with positive diagonal is sufficient for positive
    definiteness and is linear in the entries.  The absolute values are removed by
    imposing every sign pattern: row i needs
        A_ii - sum_{j != i} eps_j A_ij > 0   for all eps in {-1,+1}^{k-1},
    which is 2^{k-1} linear conditions.

3.  A LOW-DEGREE ANSATZ.  Put each free variable f_c = u_c(m) / n^3 with u_c an
    unknown polynomial in m of degree <= D.  The scaling n^-3 is the one observed
    numerically; a polynomial numerator in m recovers the n^-2 behaviour of f15 and
    anything else nearby, so this is more general than the earlier fixed-exponent
    ansatz.

Together these turn the whole design step into a RATIONAL LINEAR PROGRAM in
8(D+1) unknowns.  If it is feasible the answer is exact with no rounding at all.
If it is infeasible at degree D we raise D -- a finite ladder.

If it succeeds, two steps still remain before this is a theorem: Sturm sequences
for the ten numerators, and re-verification of the identity as a polynomial
identity in n.  Handelman feasibility makes the Sturm step a formality (a
polynomial with non-negative coefficients has no positive root at all), but it
must still be exhibited.
"""

import os
import sys
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "dittert"))
sys.path.insert(0, HERE)
import blocks as bl                                              # noqa: E402
import general_k3 as g                                           # noqa: E402
from general_k3 import RF, padd, pmul, pscale, ptrim, pstr       # noqa: E402

RES = g.solve_symbolic(verbose=False)
SYM = RES["sym"]
FREE = RES["free_cols"]
PIV = RES["piv_cols"]
IDX = bl.svar_index()
NFREE = len(FREE)
N_RF = RF([F(0), F(1)])                     # the rational function n


class Aff:
    """An affine form  c + sum_t v[t] * f_t  over Q(n), in the 8 free variables."""

    __slots__ = ("c", "v")

    def __init__(self, c=None, v=None):
        self.c = c if c is not None else RF([])
        self.v = v if v is not None else [RF([]) for _ in range(NFREE)]

    @staticmethod
    def const(rf):
        return Aff(rf, None)

    @staticmethod
    def unit(t):
        v = [RF([]) for _ in range(NFREE)]
        v[t] = RF([F(1)])
        return Aff(RF([]), v)

    def __add__(self, o):
        if not isinstance(o, Aff):
            o = Aff.const(_asrf(o))
        return Aff(self.c + o.c, [a + b for a, b in zip(self.v, o.v)])

    __radd__ = __add__

    def __sub__(self, o):
        if not isinstance(o, Aff):
            o = Aff.const(_asrf(o))
        return Aff(self.c - o.c, [a - b for a, b in zip(self.v, o.v)])

    def __rsub__(self, o):
        return Aff.const(_asrf(o)) - self

    def __mul__(self, s):
        s = _asrf(s)
        return Aff(self.c * s, [a * s for a in self.v])

    __rmul__ = __mul__

    def __neg__(self):
        return Aff(RF([]) - self.c, [RF([]) - a for a in self.v])


def _asrf(x):
    if isinstance(x, RF):
        return x
    if isinstance(x, Aff):
        raise TypeError("quadratic term: the conditions must stay linear")
    return RF([F(x)])


def variables_as_affine():
    """All 19 certificate variables as affine forms in the 8 free variables."""
    vals = [None] * 19
    for t, c in enumerate(FREE):
        vals[c] = Aff.unit(t)
    for i, c in enumerate(PIV):
        a = Aff.const(RES["b"][i])
        for t, fc in enumerate(FREE):
            coef = RES["A"][i][fc]
            if coef:
                a = a - Aff.unit(t) * coef
        vals[c] = a
    return vals


def conditions():
    """
    Every quantity that must be strictly positive, as an affine form over Q(n).

    Three sigma_0 eigenvalues, then diagonal dominance of each sigma_11 block with
    all sign patterns expanded.
    """
    vals = variables_as_affine()
    a, b, c = vals[0], vals[1], vals[2]
    out = []

    m = N_RF - RF([F(1)])
    out.append(("G0.theta0", a + b * (m * RF([F(2)])) + c * (m * m)))
    out.append(("G0.theta1", a + b * (N_RF - RF([F(2)])) - c * m))
    out.append(("G0.theta2", a - b * RF([F(2)]) + c))

    y = vals[3:14]
    A, B, C, D = bl.blocks_rational_generic(N_RF, y, IDX, one=RF([F(1)]))

    # WEIGHTED diagonal dominance.  Plain dominance is far too lossy here: it
    # FAILS on the already-verified certificates at n = 4, 5, 6, in row 0 of both
    # blocks.  The reason is scaling, not the mathematics -- blocks_rational uses
    # UNNORMALISED isotypic vectors, so u1 covers 1 cell, u2 covers 2(n-1) and u3
    # covers (n-1)^2, and the diagonal entries differ by orders of magnitude.
    #
    # Positive definiteness is invariant under a diagonal congruence D M D, and
    # dominance of D M D reads   M_ii d_i > sum_{j!=i} |M_ij| d_j,  i.e. the
    # comparison matrix applied to d is positive.  Such a d exists exactly when the
    # block is an H-matrix, and the verified certificates ARE H-matrices at
    # n = 4, 5, 6 (checked).  So we fix d to the natural cell-count normalisation
    # and impose weighted dominance, which stays LINEAR in the entries.
    wA = [RF([F(1)]),
          RF([F(1)], pscale_poly(2, [F(-1), F(1)])),     # 1/(2(n-1))
          RF([F(1)], pmul([F(-1), F(1)], [F(-1), F(1)]))]  # 1/(n-1)^2
    wC = [RF([F(1)]), RF([F(1)], [F(-1), F(1)])]         # 1/(n-1)

    for i in range(3):
        others = [j for j in range(3) if j != i]
        for s0 in (1, -1):
            for s1 in (1, -1):
                eps = {others[0]: s0, others[1]: s1}
                expr = A[i][i] * wA[i]
                for j in others:
                    expr = expr - A[i][j] * (wA[j] * RF([F(eps[j])]))
                out.append((f"H.A dom row{i} eps{s0:+d}{s1:+d}", expr))

    out.append(("H.B", B))

    for i in range(2):
        j = 1 - i
        for s in (1, -1):
            out.append((f"H.C dom row{i} eps{s:+d}",
                        C[i][i] * wC[i] - C[i][j] * (wC[j] * RF([F(s)]))))

    out.append(("H.D", D))
    return out


def pscale_poly(k, poly):
    return [F(k) * c for c in poly]


# ------------------------------------------------------------------ the program
def shift_to_m(poly, shift=4):
    """p(n) -> p(m + shift), a polynomial in m."""
    out = []
    acc = [F(1)]
    for i, co in enumerate(poly):
        if i:
            acc = pmul(acc, [F(shift), F(1)])
        out = padd(out, pscale(acc, co))
    return ptrim(out)


def build_lp(D=2, denom_power=3):
    """
    Substitute f_t = u_t(m) / n^{denom_power} with deg u_t <= D, clear
    denominators, and return the coefficient conditions.

    Returns (rows, names) where each row is (list of coefficients on the unknowns,
    constant), and the requirement is  constant + coeffs . u  >= 0, with the m^0
    coefficient of each condition required to be strictly positive.
    """
    conds = conditions()
    nunk = NFREE * (D + 1)
    rows = []
    for name, aff in conds:
        # value = aff.c + sum_t aff.v[t] * u_t(m)/n^p ,  m = n - 4
        # common denominator: den(aff.c) * prod den(aff.v[t]) * n^p  -- but we can
        # do better: put everything over a single denominator via RF arithmetic.
        npow = RF([F(0)] * denom_power + [F(1)])
        total_num = aff.c
        pieces = []
        for t in range(NFREE):
            if aff.v[t]:
                pieces.append((t, aff.v[t] / npow))
        # common denominator of total_num and all pieces
        den = total_num.den
        for _, rf in pieces:
            den = pmul(den, rf.den)
        den = ptrim(den)
        # numerator contributions
        const_num = pmul(total_num.num, _quotient(den, total_num.den))
        coeff_num = [[] for _ in range(nunk)]
        for t, rf in pieces:
            base = pmul(rf.num, _quotient(den, rf.den))
            for j in range(D + 1):
                # multiply by m^j = (n-4)^j
                mj = [F(1)]
                for _ in range(j):
                    mj = pmul(mj, [F(-4), F(1)])
                coeff_num[t * (D + 1) + j] = padd(coeff_num[t * (D + 1) + j],
                                                  pmul(base, mj))
        # the denominator is positive for n >= 4 by inspection (a product of
        # powers of n, n-1, n-2 up to a positive constant); record its sign
        sgn = _positive_for_n_ge_4(den)
        if sgn == 0:
            raise RuntimeError(f"denominator of {name} is not sign-definite "
                               f"on n >= 4: {pstr(den)}")
        const_m = shift_to_m(pscale(const_num, F(sgn)))
        coeff_m = [shift_to_m(pscale(cn, F(sgn))) for cn in coeff_num]
        deg = max([len(const_m) - 1] + [len(cm) - 1 for cm in coeff_m])
        for d in range(deg + 1):
            rows.append((name, d,
                         [cm[d] if d < len(cm) else F(0) for cm in coeff_m],
                         const_m[d] if d < len(const_m) else F(0)))
    return rows, nunk, [c[0] for c in conds]


def _quotient(a, b):
    from general_k3 import pdivmod
    q, r = pdivmod(a, b)
    assert not r, "inexact division building the common denominator"
    return q


def _positive_for_n_ge_4(poly):
    """+1 if poly(n) > 0 for all n >= 4, -1 if < 0, else 0.  Decided by shifting
    to m = n - 4 and inspecting coefficient signs, which is exact and sufficient
    for the denominators that occur here (products of n, n-1, n-2)."""
    p = shift_to_m(poly)
    if not p:
        return 0
    if all(c >= 0 for c in p) and p[0] > 0:
        return 1
    if all(c <= 0 for c in p) and p[0] < 0:
        return -1
    return 0


def solve_lp(D=2, denom_power=3, strict=F(1)):
    """
    Feasibility LP: every coefficient row >= 0, and the m^0 row of each condition
    >= `strict` > 0.  Solved in floating point, then the candidate is rounded to
    rationals and re-checked EXACTLY.
    """
    import numpy as np
    from scipy.optimize import linprog

    rows, nunk, names = build_lp(D, denom_power)
    A_ub, b_ub = [], []
    for name, d, coeffs, const in rows:
        rhs = -const + (strict if d == 0 else F(0))
        A_ub.append([-float(c) for c in coeffs])
        b_ub.append(-float(rhs))
    A_ub = np.array(A_ub)
    b_ub = np.array(b_ub)
    res = linprog(c=np.zeros(nunk), A_ub=A_ub, b_ub=b_ub,
                  bounds=[(-1e4, 1e4)] * nunk, method="highs")
    return res, rows, nunk, names


def exact_check(u, D=2, denom_power=3):
    """Re-check a rational candidate u EXACTLY: every coefficient in m >= 0 and
    each condition's constant coefficient > 0."""
    rows, nunk, names = build_lp(D, denom_power)
    assert len(u) == nunk
    bad, worst = [], None
    percond = {}
    for name, d, coeffs, const in rows:
        v = const + sum(c * x for c, x in zip(coeffs, u))
        percond.setdefault(name, {})[d] = v
        if v < 0:
            bad.append((name, d, v))
        if d == 0 and v <= 0:
            bad.append((name, "constant not strictly positive", v))
    return bad, percond


if __name__ == "__main__":
    import numpy as np
    for D in (0, 1, 2, 3, 4):
        try:
            res, rows, nunk, names = solve_lp(D)
        except RuntimeError as e:
            print(f"D={D}: {e}")
            continue
        print(f"D={D}: unknowns {nunk}, coefficient rows {len(rows)}, "
              f"LP status: {res.message.strip()}")
        if res.success:
            print("  FEASIBLE (float).  x =", np.array2string(res.x, precision=4))
            for denom in (1, 2, 4, 8, 16, 32, 64, 128, 256, 1024):
                u = [F(int(round(v * denom)), denom) for v in res.x]
                bad, _ = exact_check(u, D)
                if not bad:
                    print(f"  EXACT rational solution at denominator {denom}:")
                    for t in range(NFREE):
                        poly = [u[t * (D + 1) + j] for j in range(D + 1)]
                        print(f"    f{FREE[t]:<2d} = ({pstr(poly, 'm')}) / n^3")
                    sys.exit(0)
            print("  no simple rational rounding passed the exact check")
        print()
