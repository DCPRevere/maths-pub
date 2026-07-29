"""
Exact CERTIFICATES for the pin re-test -- NOTES §6b.33, §6b.39, the deciding step.

`k4_pinretest.py` measures a solver margin and cannot decide anything here: the
unpinned control reaches only t = +5.66e-04 at n = 5, so every margin lives at
1e-4, and the same 201-pin programme at n = 6 returned t = -3.70e-04 at SCS eps
1e-10 and +9.70e-05 at eps 1e-12.  This module decides the same questions over
Q.  `k4_pinrank.py` first ruled out the cheap route: A is 33-dimensional even
under all 321 pins, and NOT ONE of the 86 canonical block diagonals is constant
on it, so no single forced entry decides anything.

INFEASIBLE.  Rational `Y_b` per canonical block, every `Y_b` positive
semidefinite, with `w -> sum_b <Y_b, M_b(w)>` CONSTANT on A and `<= 0`.  Then no
w in A makes H positive definite, since `<Y, M> > 0` for `Y >= 0`, `Y =/= 0`,
`M > 0`; so `t* <= 0`.

FEASIBLE.  A rational `w` satisfying `S w = rhs` and every pin BY SUBSTITUTION,
with every canonical block positive definite by exact rational LDL^T.  That is a
COMPLETE test of `H > 0`: the 21 canonical blocks carry the full multiplicities
63 + 23 against `blockdiag`'s dimensions, and their bases were checked linearly
independent at n = 5, 6 and 7, so a singular block is a fact about H and not an
artefact of the basis.

THE SHAPE OF THE PROBLEM, which is what makes this tractable.  Under the full
pinning every off-diagonal entry of every canonical block is zero on A by
construction -- verified here entry by entry, not assumed.  A diagonal block is
positive definite iff its diagonal is positive, so the question is a LINEAR
PROGRAMME and its Farkas certificate is `Y = diag(c)` with `c >= 0`, positive
semidefinite for free.  Rank-one generators `v v^T` for rational `v` extend the
cone on the one non-diagonal block of an omission configuration on the same
terms.  Nothing is factorised and there is no interior margin to lose -- which
matters, because the general PSD route returns a Y with least eigenvalue 2e-06
that survives no rounding at all.  Only when the generator cone cannot express
the certificate is the full mixed multiplier tried.

WHY THE SEARCH IS NOT TRUSTED.  Verification calls `value_on`, which returns a
value only when the functional's residual against the exact reduced form is
IDENTICALLY zero, plus a sign test on coefficients or an exact LDL^T.  It reads
no float, no null-space basis, no particular solution and no solver output.  A
wrong Y fails verification rather than passing it, so the numerical search may
be as sloppy as it likes.

Both directions are attempted for EVERY configuration.  One that neither
certifies is reported UNDECIDED -- never as agreement with a solver's sign.  Two
are: H2 at n = 6 and n = 7, and the 14x14 omission at all three n.  See §6b.40
for what is known about each and what would settle it.
"""

import os
import sys
from fractions import Fraction as F

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "dittert"))
sys.path.insert(0, HERE)
import k4_pinrank as pk                                            # noqa: E402
from exactsd import ldl_pivots                                     # noqa: E402


def particular_and_nullspace(piv, R, bb, C):
    """w0 in A and a basis of the direction space, from the reduced form."""
    w0 = [F(0)] * C
    for i, p in enumerate(piv):
        w0[p] = F(bb[i]) / R[i][p]
    free = [j for j in range(C) if j not in set(piv)]
    Z = []
    for j in free:
        z = [F(0)] * C
        z[j] = F(1)
        for i, p in enumerate(piv):
            if R[i][j]:
                z[p] = -F(R[i][j], R[i][p])
        Z.append(_primitive(z))
    return w0, Z


def _primitive(z):
    """
    Rescale a direction to coprime integers.

    Scaling a null vector changes nothing mathematically, but the raw vectors
    out of the reduction carry enormous numerators, and every M_b(z) built from
    them inherits that size.  The rounding step then has to correct a residual
    of the same magnitude and no denominator is ever fine enough.  This is
    conditioning, not arithmetic: the vector still spans the same line.
    """
    from math import gcd
    d = 1
    for v in z:
        d = d * v.denominator // gcd(d, v.denominator)
    ints = [int(v * d) for v in z]
    g = 0
    for v in ints:
        g = gcd(g, v)
    if g > 1:
        ints = [v // g for v in ints]
    return [F(v) for v in ints]


def contract(N, dd, w, off):
    """M_b(w) exactly: the canonical block evaluated at w."""
    return [[sum(x * w[off + c] for c, x in N[s][t].items())
             for t in range(dd)] for s in range(dd)]


def check_point(w, srows, srhs, sel, blocks, C):
    """Substitute: is w in A, and is every canonical block positive definite?"""
    for r, row in enumerate(srows):
        if sum(F(row[j]) * w[j] for j in range(C) if row[j]) != srhs[r]:
            return False, f"SDP identity row {r} violated"
    for k, (_, _, vec) in enumerate(sel):
        if sum(F(vec[j]) * w[j] for j in range(C) if vec[j]) != 0:
            return False, f"pin {k} violated"
    worst = None
    for side, name, dd, N, off in blocks:
        M = contract(N, dd, w, off)
        pivots, bad = ldl_pivots(M)
        if pivots is None:
            return False, f"block {side} {name} not PD at pivot {bad}"
        m = min(pivots)
        worst = m if worst is None else min(worst, m)
    return True, worst


def check_dual_psd(Y, blocks, piv, R, bb, C):
    """
    Verify the certificate for a DIAGONAL Y, where semidefiniteness is exactly
    "every entry >= 0" and nothing has to be factorised.  Diagonality is
    checked, not assumed, so this cannot be handed a non-diagonal Y by mistake.
    """
    nz = False
    for (side, name, dd, N, off), Yb in zip(blocks, Y):
        for s in range(dd):
            for t in range(dd):
                if s != t and Yb[s][t]:
                    return None, f"Y for {side} {name} is not diagonal"
            if Yb[s][s] < 0:
                return None, f"Y for {side} {name} has a negative entry"
            if Yb[s][s]:
                nz = True
    if not nz:
        return None, "Y is identically zero"
    return _value_of(Y, blocks, piv, R, bb, C)


def _value_of(Y, blocks, piv, R, bb, C):
    c = [F(0)] * C
    for (side, name, dd, N, off), Yb in zip(blocks, Y):
        for s in range(dd):
            for t in range(dd):
                if not Yb[s][t]:
                    continue
                for cl, x in N[s][t].items():
                    c[off + cl] += Yb[s][t] * x
    v = pk.value_on(c, piv, R, bb)
    if v is None:
        return None, "the functional is NOT constant on A"
    return v, "constant on A"


# -------------------------------------------------- the diagonal (LP) route
# Under the full pinning EVERY off-diagonal entry of EVERY canonical block is
# zero on A -- measured, `max |off-diagonal| of M(w0)| = 0` over all 21 blocks
# at n = 5.  So on A each block is DIAGONAL, "positive definite" means "all 86
# diagonal entries positive", and the whole question is a linear programme.
# Its Farkas certificate is a DIAGONAL Y = diag(c) with c >= 0, which is
# positive semidefinite for free -- no eigenvalue, no rounding of a matrix,
# and no interior margin to lose.  That last point is what matters: the general
# SDP search returns a Y whose least eigenvalue is ~2e-06, far too thin to
# survive the exact correction, whereas here the support of c is bounded away
# from zero and the null space is computed over Q from the start.
def reduce_functional(c, piv, R, bb, C, free):
    """Split a functional into (residual on the free columns, constant part)."""
    val = F(0)
    for k, p in enumerate(piv):
        if c[p]:
            f = c[p] / R[k][p]
            val += f * bb[k]
            Rk = R[k]
            for j in range(C):
                if Rk[j]:
                    c[j] -= f * Rk[j]
    return [c[j] for j in free], val


def quad_functional(N, dd, off, v, C):
    """The functional w -> v^T M_b(w) v, exactly."""
    c = [F(0)] * C
    for s in range(dd):
        if not v[s]:
            continue
        for t in range(dd):
            if not v[t]:
                continue
            vv = v[s] * v[t]
            for cl, x in N[s][t].items():
                c[off + cl] += vv * x
    return c


def diag_data(blocks, piv, R, bb, C, extra=()):
    """
    Generators of the certificate cone, each reduced against A.

    Every generator is a multiplier Y that is positive semidefinite BY
    CONSTRUCTION, so a nonnegative combination of them is too and no matrix
    ever has to be rounded or factorised:

      * `e_i e_i^T` for each of the 86 block diagonals, and
      * `v v^T` for each supplied rational v on a block that is NOT diagonal
        on A -- a rank-one form is positive semidefinite for ANY rational v,
        which is the whole point.

    That last family is what settles the "omit the 14x14" configuration.  The
    general SDP route cannot: its Y has an interior margin of 1.5e-02 while the
    exact correction onto the 124 equality constraints moves the entries by
    1e-01, because freezing the zero coefficients leaves barely more free
    coordinates than there are constraints and the system is badly conditioned.
    No denominator fixes a correction two orders of magnitude too big.  Here
    there is nothing to correct: the LP is solved over Q on the vertex support.
    """
    free = [j for j in range(C) if j not in set(piv)]
    cols, vals, labels = [], [], []
    for side, name, dd, N, off in blocks:
        for i in range(dd):
            c = [F(0)] * C
            for cl, x in N[i][i].items():
                c[off + cl] += x
            res, val = reduce_functional(c, piv, R, bb, C, free)
            cols.append(res)
            vals.append(val)
            labels.append(("diag", side, name, i, dd))
    for b, v in extra:
        side, name, dd, N, off = blocks[b]
        res, val = reduce_functional(quad_functional(N, dd, off, v, C),
                                     piv, R, bb, C, free)
        cols.append(res)
        vals.append(val)
        labels.append(("rank1", side, name, tuple(v), dd))
    # Rescale each generator to O(1).  A generator is e e^T or v v^T; dividing
    # it by a POSITIVE rational is still exactly that shape and still positive
    # semidefinite, so this is a change of units, not of the cone.  Without it
    # the columns span many orders of magnitude and the float LP returns a
    # vertex whose support has NO exact kernel -- which is what "the restricted
    # kernel is trivial" meant for the 10x10 at n = 6: a vertex that satisfied
    # the equalities to LP tolerance and to nothing better.
    scales = []
    for j in range(len(cols)):
        s = max((abs(x) for x in cols[j] if x), default=F(0))
        if not s:
            s = abs(vals[j]) or F(1)
        scales.append(s)
        cols[j] = [x / s for x in cols[j]]
        vals[j] = vals[j] / s
    return cols, vals, labels, free, scales


def rank1_candidates(blocks, flags, Ynum, dens=(10, 100, 1000)):
    """Rational vectors for the rank-one generators on the non-diagonal blocks."""
    out = []
    for b, (side, name, dd, N, off) in enumerate(blocks):
        if flags[b] or dd < 2:
            continue
        for i in range(dd):
            for j in range(i + 1, dd):
                for sg in (1, -1):
                    v = [F(0)] * dd
                    v[i], v[j] = F(1), F(sg)
                    out.append((b, v))
        if Ynum is None:
            continue
        try:
            w, U = np.linalg.eigh(np.array([[float(x) for x in row]
                                            for row in Ynum[b]]))
        except Exception:                                        # noqa: BLE001
            continue
        for k in range(dd):
            for den in dens:
                col = U[:, k]
                sc = np.abs(col).max() or 1.0
                v = [F(int(round(x / sc * den)), den) for x in col]
                if any(v):
                    out.append((b, v))
    return out


def exact_nullvector(cols, support):
    """A rational kernel vector of the columns restricted to `support`."""
    from math import gcd
    m = len(cols[0]) if cols else 0
    rows = []
    for r in range(m):
        row = [cols[j][r] for j in support]
        d = 1
        for v in row:
            d = d * v.denominator // gcd(d, v.denominator)
        rows.append([int(v * d) for v in row])
    k = len(support)
    piv, R, bb, _ = pk.rref_int(rows, [F(0)] * m, k)
    freek = [j for j in range(k) if j not in set(piv)]
    if not freek:
        return None
    z = [F(0)] * k
    z[freek[0]] = F(1)
    for i, p in enumerate(piv):
        if R[i][freek[0]]:
            z[p] = -F(R[i][freek[0]], R[i][p])
    return z


def cone_certificate(blocks, piv, R, bb, C, out, extra=(), tag="diagonal"):
    """Exact Farkas certificate over the PSD-by-construction generators."""
    from scipy.optimize import linprog
    cols, vals, labels, free, scales = diag_data(blocks, piv, R, bb, C, extra)
    m, N = len(free), len(cols)
    if m == 0:
        return None
    rows = [[float(cols[j][r]) for j in range(N)] for r in range(m)]
    for r in range(m):                       # row scaling: the rhs is 0, so a
        mx = max(abs(x) for x in rows[r])    # positive row multiple changes
        if mx:                               # nothing but the LP conditioning
            rows[r] = [x / mx for x in rows[r]]
    Aeq = np.array(rows + [[1.0] * N])
    beq = np.array([0.0] * m + [1.0])
    res = linprog(np.array([float(v) for v in vals]), A_eq=Aeq, b_eq=beq,
                  bounds=[(0, None)] * N, method="highs")
    if not res.success or res.fun >= 0:
        out(f"    {tag} LP over {N} generators: "
            f"{('best value %+.6e' % res.fun) if res.success else 'infeasible'}"
            f" -- no refutation")
        return None
    order = sorted(range(N), key=lambda j: -res.x[j])
    support = [j for j in order if res.x[j] > 1e-9]
    out(f"    {tag} LP over {N} generators: value {res.fun:+.6e} at a vertex; "
        f"support {len(support)}")
    # An LP vertex is exact only to LP tolerance.  If its support carries no
    # exact kernel, widen it a column at a time -- the extra columns simply
    # give the exact solution more room, and every one of them is still a
    # positive semidefinite generator.
    z, used = None, None
    k = len(support)
    while k <= min(N, len(support) + 40):
        cand = order[:k]
        z = exact_nullvector(cols, cand)
        if z is not None and (all(v >= 0 for v in z) or all(v <= 0 for v in z)):
            used = cand
            break
        z = None
        k += 1
    if z is None:
        out("    no sign-definite exact kernel vector on any widened support")
        return None
    if all(v <= 0 for v in z):
        z = [-v for v in z]
    if len(used) > len(support):
        out(f"    support widened to {len(used)} to reach an exact kernel")
    c = [F(0)] * N
    for i, j in enumerate(used):
        c[j] = z[i] / scales[j]
    return c, labels, vals


def assemble_Y(c, labels, blocks):
    """Y = sum of nonnegative multiples of e_i e_i^T and v v^T.  PSD by build."""
    Y = [[[F(0)] * dd for _ in range(dd)] for _, _, dd, _, _ in blocks]
    index = {(side, name): b for b, (side, name, _, _, _) in enumerate(blocks)}
    for j, lab in enumerate(labels):
        if not c[j]:
            continue
        if lab[0] == "diag":
            _, side, name, i, dd = lab
            Y[index[(side, name)]][i][i] += c[j]
        else:
            _, side, name, v, dd = lab
            b = index[(side, name)]
            for s in range(dd):
                for t in range(dd):
                    if v[s] and v[t]:
                        Y[b][s][t] += c[j] * v[s] * v[t]
    return Y


def check_cone(c, labels, Y, blocks, piv, R, bb, C):
    """
    Verify without factorising anything.

    Semidefiniteness needs no test: Y is a NONNEGATIVE combination of e_i e_i^T
    and v v^T, so `c >= 0` is the whole of it.  What is checked is that the
    coefficients really are nonnegative and not all zero, that the assembled Y
    agrees with those coefficients, and that the resulting functional is
    constant on A -- the last by `value_on`, which returns a value only when
    the residual is identically zero.
    """
    if any(x < 0 for x in c):
        return None, "a generator coefficient is negative"
    if not any(c):
        return None, "all generator coefficients are zero"
    if Y != assemble_Y(c, labels, blocks):
        return None, "Y does not match its generator coefficients"
    return _value_of(Y, blocks, piv, R, bb, C)


# ------------------------------------------------- the mixed (LP + one SDP)
# For an H3 configuration "omit X" the diagonal route is not enough: measured at
# n = 5 for "omit the 14x14", the diagonal LP is INFEASIBLE -- no nonnegative
# combination of the 86 diagonals is even constant on A, so the other blocks'
# diagonals can all be made positive and the obstruction is block X failing to
# be positive definite AS A MATRIX.  But only X is non-diagonal on A; the other
# twenty stay diagonal.  So the certificate is
#     Y_b = diag(c_b), c_b >= 0   for the twenty pinned blocks,
#     Y_X  a genuine PSD matrix,  dd x dd with dd <= 14,
# which is an SDP with ONE small PSD block instead of twenty-one.  That is what
# makes it roundable: the interior margin only has to survive on X.
def offdiag_zero_blocks(blocks, piv, R, bb, C):
    """Which blocks are DIAGONAL on A?  Checked, not assumed."""
    flags = []
    for side, name, dd, N, off in blocks:
        diagonal = True
        for s in range(dd):
            for t in range(s + 1, dd):
                c = [F(0)] * C
                for cl, x in N[s][t].items():
                    c[off + cl] += x
                v = pk.value_on(c, piv, R, bb)
                if v is None or v != 0:
                    diagonal = False
                    break
            if not diagonal:
                break
        flags.append(diagonal)
    return flags


def search_mixed(blocks, flags, w0, Z, frac):
    """Diagonal nonnegative Y on the pinned blocks, full PSD on the rest."""
    import cvxpy as cp
    var, cons = [], []
    for b, (_, _, dd, _, _) in enumerate(blocks):
        if flags[b]:
            v = cp.Variable(dd, nonneg=True)
            var.append(("d", v))
        else:
            Y = cp.Variable((dd, dd), symmetric=True)
            var.append(("m", Y))

    def pair(Ms):
        terms = []
        for (kind, v), M in zip(var, Ms):
            if kind == "d":
                terms.append(cp.sum(cp.multiply(v, np.diag(M))))
            else:
                terms.append(cp.sum(cp.multiply(v, M)))
        return cp.sum(terms)

    Mw0 = [np.array([[float(x) for x in row]
                     for row in contract(N, dd, w0, off)])
           for _, _, dd, N, off in blocks]
    s = max((np.abs(M).max() for M in Mw0 if M.size), default=1.0) or 1.0
    Mw0 = [M / s for M in Mw0]
    MZ = []
    for z in Z:
        blk = [np.array([[float(x) for x in row]
                         for row in contract(N, dd, z, off)])
               for (_, _, dd, N, off) in blocks]
        sz = max((np.abs(M).max() for M in blk if M.size), default=0.0)
        MZ.append([M / sz for M in blk] if sz > 0 else blk)
    lam = cp.Variable()
    base = [cp.sum([cp.sum(v) if k == "d" else cp.trace(v)
                    for k, v in var]) == 1]
    base += [pair(blk) == 0 for blk in MZ]
    psd = [v >> 0 for k, v in var if k == "m"]
    val = pair(Mw0)
    try:
        cp.Problem(cp.Minimize(val), base + psd).solve(
            solver=cp.SCS, eps_abs=1e-11, eps_rel=1e-11, max_iters=200000)
    except Exception:                                            # noqa: BLE001
        return None, None, None
    if val.value is None or float(val.value) >= 0:
        return None, (None if val.value is None else float(val.value)), None
    v0 = float(val.value)
    # The margin must cover the DIAGONAL coefficients too, not just the matrix
    # blocks.  If some diagonal coefficient is allowed to sit at zero it has to
    # be frozen during the exact correction (a zero that drifts negative
    # destroys semidefiniteness), and freezing leaves barely more free
    # coordinates than there are equality constraints -- the system is then so
    # ill conditioned that the correction came out at 1e-01 against a margin of
    # 1.5e-02.  With every coordinate strictly interior nothing is frozen and
    # the correction spreads over all of them.
    marg = [v >> lam * np.eye(v.shape[0]) for k, v in var if k == "m"]
    marg += [v >= lam for k, v in var if k == "d"]
    try:
        cp.Problem(cp.Maximize(lam),
                   base + marg + [val <= frac * v0]).solve(
            solver=cp.SCS, eps_abs=1e-11, eps_rel=1e-11, max_iters=200000)
    except Exception:                                            # noqa: BLE001
        return None, v0, None
    if lam.value is None or any(v.value is None for _, v in var):
        return None, v0, None
    Y = []
    for b, (kind, v) in enumerate(var):
        dd = blocks[b][2]
        if kind == "d":
            Y.append([[float(v.value[i]) if i == j else 0.0
                       for j in range(dd)] for i in range(dd)])
        else:
            Y.append([[float(x) for x in row] for row in np.array(v.value)])
    return Y, v0, float(lam.value)


def in_span(basis, target, denom):
    """
    Round INSIDE the subspace instead of rounding then correcting.

    Every failure of this module so far came from the same shape: round a
    numerical point, then correct it exactly back onto the constraints, and
    watch the correction -- not the rounding -- destroy the positivity that was
    the whole point.  The correction was 1e-01 against a margin of 1.5e-02 for
    "omit the 14x14", and it left H2 at n = 6 indefinite at every denominator.

    The cure is to never leave the constraint set.  `basis` is an EXACT
    rational basis of the affine directions; a rounded rational combination of
    exact basis vectors satisfies the constraints IDENTICALLY, with no
    correction step to undo it.  The only error left is the rounding itself,
    which is bounded by `denom` and can simply be made smaller.
    """
    import numpy as np
    if not basis:
        return []
    Bf = np.array([[float(x) for x in b] for b in basis]).T
    f, *_ = np.linalg.lstsq(Bf, np.asarray(target, dtype=float), rcond=None)
    # limit_denominator, NOT round(x * denom) / denom.  The coefficients here
    # are ~1e-07, because the direction vectors are primitive integers with
    # entries up to 3.5e+06, so a FIXED denominator of 1e+09 keeps two
    # significant digits of each one and throws the rest away -- which is why
    # the same point read positive definite at 1e-15 and indefinite at 1e-09.
    # limit_denominator gives the best rational approximation of that size
    # whatever the magnitude, so the precision is relative, as it must be.
    return [F(float(x)).limit_denominator(denom) for x in f]


def subspace_basis(rows, ncols):
    """Exact primitive-integer basis of the null space of `rows`."""
    piv, R, bb, _ = pk.rref_int(rows, [F(0)] * len(rows), ncols)
    pivset = set(piv)
    out = []
    for j in range(ncols):
        if j in pivset:
            continue
        z = [F(0)] * ncols
        z[j] = F(1)
        for i, p in enumerate(piv):
            if R[i][j]:
                z[p] = -F(R[i][j], R[i][p])
        out.append(_primitive(z))
    return out


def least_norm(A, r, k):
    """
    The MINIMUM-NORM exact rational solution of A delta = r.

    The obvious correction -- dump the whole residual on the pivot coordinates,
    as `round_and_correct` does -- is what defeated the first attempt at the
    "omit the 14x14" certificate: a 14x14 multiplier with an interior margin of
    1.5e-02 was still knocked indefinite at every denominator down to 1e-12,
    because the pivot coordinates took a correction far larger than the margin
    while the other 400-odd coordinates took none.  Spreading it as
    `delta = A^T (A A^T)^-1 r` keeps the perturbation as small as it can be.
    Dependent rows are dropped first, so a singular Gram cannot arise.
    """
    m = len(A)
    if m == 0:
        return [F(0)] * k
    keep, _, _ = _independent(A)
    A = [A[i] for i in keep]
    r = [r[i] for i in keep]
    m = len(A)
    G = [[F(sum(A[i][t] * A[j][t] for t in range(k))) for j in range(m)]
         for i in range(m)]
    for i in range(m):
        G[i].append(F(r[i]))
    for c in range(m):                                   # exact Gauss-Jordan
        p = next((i for i in range(c, m) if G[i][c] != 0), None)
        if p is None:
            return None
        G[c], G[p] = G[p], G[c]
        pv = G[c][c]
        G[c] = [v / pv for v in G[c]]
        for i in range(m):
            if i != c and G[i][c] != 0:
                f = G[i][c]
                G[i] = [x - f * y for x, y in zip(G[i], G[c])]
    y = [G[i][m] for i in range(m)]
    return [sum(y[i] * A[i][t] for i in range(m)) for t in range(k)]


def _independent(A):
    """Row indices of a maximal independent subset, over Q."""
    piv, rows, order = [], [], list(range(len(A)))
    work = [[F(v) for v in row] for row in A]
    r = 0
    k = len(A[0])
    for c in range(k):
        p = next((i for i in range(r, len(work)) if work[i][c] != 0), None)
        if p is None:
            continue
        work[r], work[p] = work[p], work[r]
        order[r], order[p] = order[p], order[r]
        pv = work[r][c]
        for i in range(r + 1, len(work)):
            if work[i][c] != 0:
                f = work[i][c] / pv
                work[i] = [x - f * y for x, y in zip(work[i], work[r])]
        rows.append(order[r])
        r += 1
        if r == len(work):
            break
    return sorted(rows), piv, r


def round_mixed(Ynum, blocks, flags, Z, denom, tol):
    """
    Round, then correct EXACTLY -- but only along coordinates that have room.

    A diagonal coefficient the search set to zero must STAY zero, or the
    correction can push it negative and destroy semidefiniteness for the sake
    of an equality it could have satisfied elsewhere.  So the correction is
    restricted to the PSD blocks' entries and to the strictly positive
    diagonal coefficients; the rest are frozen.
    """
    from math import gcd
    idx, cols, allowed = [], 0, []
    for b, (_, _, dd, _, _) in enumerate(blocks):
        idx.append([[-1] * dd for _ in range(dd)])
        for s in range(dd):
            for t in range(s, dd):
                if flags[b] and s != t:
                    continue
                idx[b][s][t] = idx[b][t][s] = cols
                allowed.append((not flags[b]) or Ynum[b][s][s] > tol)
                cols += 1
    u = [F(0)] * cols
    for b, (_, _, dd, _, _) in enumerate(blocks):
        for s in range(dd):
            for t in range(s, dd):
                if idx[b][s][t] < 0:
                    continue
                x = Ynum[b][s][t]
                u[idx[b][s][t]] = F(0) if (flags[b] and x <= tol) \
                    else F(round(x * denom), denom)
    rows = []
    for z in Z:
        row = [F(0)] * cols
        for b, (_, _, dd, N, off) in enumerate(blocks):
            M = contract(N, dd, z, off)
            for s in range(dd):
                for t in range(s, dd):
                    if idx[b][s][t] >= 0:
                        row[idx[b][s][t]] += M[s][t] * (1 if s == t else 2)
        rows.append(row)
    # Round INSIDE the constraint subspace, as on the primal side: an exact
    # rational basis of { u : <Y(u), M(z)> = 0 for all z }, then a rounded
    # rational combination of those basis vectors.  The result satisfies the
    # equalities identically and there is no correction to knock Y indefinite.
    irows = []
    for row in rows:
        d = 1
        for v in row:
            d = d * v.denominator // gcd(d, v.denominator)
        irows.append([int(v * d) for v in row])
    basis = subspace_basis(irows, cols)
    # Normalise each basis vector to largest entry 1.  `_primitive` makes them
    # coprime INTEGERS, which can be astronomically large, and then the
    # coefficients that reproduce an O(1) Y are ~1e-12 and round to zero -- the
    # "Y is identically zero" rejections.  Scaling a basis vector changes
    # neither the subspace nor the exactness, only the size of the number that
    # has to survive rounding.
    basis = [[x / max(abs(t) for t in b if t) for x in b]
             for b in basis if any(b)]
    coef = in_span(basis, [float(x) for x in u], denom)
    u = [F(0)] * cols
    for k, ck in enumerate(coef):
        if not ck:
            continue
        bk = basis[k]
        for j in range(cols):
            if bk[j]:
                u[j] += ck * bk[j]
    Y = []
    for b, (_, _, dd, _, _) in enumerate(blocks):
        Y.append([[u[idx[b][s][t]] if idx[b][s][t] >= 0 else F(0)
                   for t in range(dd)] for s in range(dd)])
    return Y


def check_mixed(Y, blocks, flags, piv, R, bb, C):
    """Diagonal blocks: entries >= 0.  The rest: exact LDL^T positive definite."""
    nz = False
    for b, ((side, name, dd, N, off), Yb) in enumerate(zip(blocks, Y)):
        if any(Yb[s][t] != Yb[t][s] for s in range(dd) for t in range(dd)):
            return None, f"Y for {side} {name} is not symmetric"
        if flags[b]:
            for s in range(dd):
                for t in range(dd):
                    if s != t and Yb[s][t]:
                        return None, f"Y for {side} {name} is not diagonal"
                if Yb[s][s] < 0:
                    return None, f"Y for {side} {name} has a negative entry"
                if Yb[s][s]:
                    nz = True
        else:
            if all(not Yb[s][t] for s in range(dd) for t in range(dd)):
                continue
            if ldl_pivots(Yb)[0] is None:
                return None, f"Y for {side} {name} is not positive definite"
            nz = True
    if not nz:
        return None, "Y is identically zero"
    return _value_of(Y, blocks, piv, R, bb, C)


WITNESS_DIR = os.path.join(HERE, "results", "witness")


def _q(x):
    """A rational as an exact 'num/den' string -- no float ever reaches disk."""
    x = F(x)
    return f"{x.numerator}/{x.denominator}"


def store_witness(n, omit, kind, payload, out, suffix=""):
    """
    Write the exact witness a verdict cites.  METHODS §5: a verdict whose
    certificate lives only in a log does not exist.

    Everything is written as exact rationals.  The file carries WHAT the
    configuration is (n, and which block is left unpinned) and WHAT the witness
    is -- never the verdict's reasoning, which `results/verify_pinretest.py`
    redoes from the problem definition with its own arithmetic.
    """
    import json
    os.makedirs(WITNESS_DIR, exist_ok=True)
    # `suffix` keeps two DIFFERENT claims about the same configuration in two
    # different files.  Without it the zero-value-LP certificate for H2 lands
    # on the same name as H2's feasible point -- discard 12 a second time, and
    # at n = 5 it would have destroyed a committed witness.
    tag = "H1_full321" if omit is None else f"omit_{omit[0]}_{omit[1]}"
    safe = "".join(ch if ch.isalnum() or ch in "_-" else "_" for ch in tag)
    path = os.path.join(WITNESS_DIR, f"n{n}_{safe}{suffix}.json")
    doc = {"n": n, "k": 4, "deg_basis": 2,
           "omit_side": None if omit is None else omit[0],
           "omit_block": None if omit is None else omit[1],
           "kind": kind}
    doc.update(payload)
    with open(path, "w") as fh:
        json.dump(doc, fh, indent=1, sort_keys=True)
    out(f"    witness stored: results/witness/{os.path.basename(path)}")
    return path


def infeasible_witness(n, omit, c, labels, v, out):
    """The Farkas multiplier, as the generators it is a nonnegative sum of."""
    gens = []
    for j, lab in enumerate(labels):
        if not c[j]:
            continue
        g = {"coef": _q(c[j]), "side": lab[1], "block": lab[2], "dim": lab[4]}
        if lab[0] == "diag":
            g["kind"] = "diag"
            g["index"] = lab[3]
        else:
            g["kind"] = "rank1"
            g["v"] = [_q(t) for t in lab[3]]
        gens.append(g)
    return store_witness(n, omit, "infeasible",
                         {"generators": gens, "value": _q(v),
                          "claim": "sum_b <Y_b, M_b(w)> equals `value` for "
                                   "every w in A, and value <= 0"}, out)


def feasible_witness(n, omit, w, least, out):
    """The exact rational point, and the least LDL pivot it achieves."""
    return store_witness(n, omit, "feasible",
                         {"point": [_q(t) for t in w],
                          "least_ldl_pivot": _q(least),
                          "claim": "S w = rhs, every pin vanishes, and every "
                                   "canonical block is positive definite"}, out)


def report_certificate(c, labels, v, out, tag):
    used = [(labels[j], c[j]) for j in range(len(c)) if c[j]]
    nd = sum(1 for lab, _ in used if lab[0] == "diag")
    out(f"    CERTIFICATE, exact ({tag}): Y = sum of {nd} terms c_i e_i e_i^T "
        f"and {len(used) - nd} terms a_k v_k v_k^T, every coefficient >= 0.")
    out("    Positive semidefiniteness needs no check: a nonnegative "
        "combination of e e^T and v v^T is PSD by construction.")
    for lab, w in used[:6]:
        if lab[0] == "diag":
            out(f"      c = {float(w):.6g}  on entry {lab[3]} of the "
                f"{lab[4]}x{lab[4]} {lab[1]} {lab[2]}")
        else:
            out(f"      a = {float(w):.6g}  on a rank-one form of the "
                f"{lab[4]}x{lab[4]} {lab[1]} {lab[2]}")
    if len(used) > 6:
        out(f"      ... and {len(used) - 6} more")
    out(f"    sum_b <Y_b, M_b(w)> = {float(v):+.6e} <= 0 for EVERY w in A, "
        f"checked over Q.")
    out("    <Y, M> > 0 whenever Y >= 0, Y =/= 0 and M > 0, so no w in A "
        "makes H positive definite.")
    out("    ==> NOT strictly feasible.  t* <= 0.  INFEASIBLE, exactly.")


def decide(n, sel, label, ctx, out=print, omit=None):
    d, C, srows, srhs, pins, blocks = ctx
    rows = srows + [v for _, _, v in sel]
    rhs = list(srhs) + [F(0)] * len(sel)
    piv, R, bb, ok = pk.rref_int(rows, rhs, C)
    out(f"\n  {label}   {len(sel)} pins   rank {len(piv)}  dim A {C - len(piv)}")
    if not ok:
        out("    A is EMPTY over Q  ==>  INFEASIBLE, exactly.")
        return "INFEASIBLE(empty)"
    w0, Z = particular_and_nullspace(piv, R, bb, C)
    flags = offdiag_zero_blocks(blocks, piv, R, bb, C)
    ndiag = sum(flags)
    out(f"    {ndiag} of the 21 blocks are DIAGONAL on A "
        f"(verified entry by entry)")

    # Stage 1: the diagonals alone.  Cheapest, and it settles most cases.
    got = cone_certificate(blocks, piv, R, bb, C, out, (), "diagonal")
    tag = "diagonal"
    if got is None and ndiag < len(blocks):
        # Stage 2: add rank-one generators on the blocks that are NOT diagonal
        # on A.  A numeric SDP supplies candidate directions; it is a source of
        # guesses only -- v v^T is PSD whatever v is, so a bad guess costs an
        # LP column and can never produce a false certificate.
        Ynum = search_mixed(blocks, flags, w0, Z, 0.5)[0]
        extra = rank1_candidates(blocks, flags, Ynum)
        out(f"    adding {len(extra)} rank-one generators on the "
            f"{len(blocks) - ndiag} non-diagonal block(s)")
        got = cone_certificate(blocks, piv, R, bb, C, out, extra, "rank-one")
        tag = "diagonal + rank-one"
    if got is not None:
        c, labels, vals = got
        Y = assemble_Y(c, labels, blocks)
        v, why = check_cone(c, labels, Y, blocks, piv, R, bb, C)
        if v is not None and v <= 0:
            report_certificate(c, labels, v, out, tag)
            infeasible_witness(n, omit, c, labels, v, out)
            return "INFEASIBLE"
        out(f"    the certificate did not verify: {why}")

    # Stage 3: the full mixed multiplier, rounded and corrected.  Only reached
    # when the generator cone above cannot express the certificate -- a Y whose
    # eigenvectors are irrational is not a nonnegative combination of any
    # finite list of rational rank-one forms.
    if ndiag < len(blocks):
        for frac in (0.5, 0.1, 0.01):
            Ynum, v0, lam = search_mixed(blocks, flags, w0, Z, frac)
            if Ynum is None:
                out(f"    mixed search (slack {frac}): no negative value "
                    f"(best {v0 if v0 is not None else 'n/a'})")
                break
            out(f"    mixed search (slack {frac}): value {v0:+.6e}, "
                f"interior margin {lam:+.3e}")
            if lam <= 0:
                continue
            for denom in (10 ** 9, 10 ** 12, 10 ** 15, 10 ** 18):
                Y = round_mixed(Ynum, blocks, flags, Z, denom, 1e-12)
                if Y is None:
                    continue
                v, why = check_mixed(Y, blocks, flags, piv, R, bb, C)
                if v is None:
                    out(f"      denom 1e{len(str(denom)) - 1}: {why}")
                    continue
                if v <= 0:
                    out(f"      denom 1e{len(str(denom)) - 1}: VERIFIED over "
                        f"Q.  sum_b <Y_b, M_b(w)> = {float(v):+.6e} <= 0 for "
                        f"every w in A, every Y_b PSD by exact LDL^T.")
                    out("    ==> NOT strictly feasible.  t* <= 0.  "
                        "INFEASIBLE, exactly.")
                    store_witness(n, omit, "infeasible_matrix",
                                  {"Y": [[[_q(t) for t in row] for row in Yb]
                                         for Yb in Y],
                                   "blocks": [[b[0], b[1], b[2]]
                                              for b in blocks],
                                   "value": _q(v),
                                   "claim": "sum_b <Y_b, M_b(w)> equals "
                                            "`value` for every w in A, every "
                                            "Y_b is PSD, and value <= 0"}, out)
                    return "INFEASIBLE"
                out(f"      denom 1e{len(str(denom)) - 1}: constant but "
                    f"value {float(v):+.3e} > 0 -- not a refutation")

    ok2, info = feasible_point(n, sel, ctx, piv, R, bb, w0, Z, out)
    if ok2:
        least, wpt = info
        out(f"    ==> STRICTLY FEASIBLE, exactly.  Exact rational point in A "
            f"with every canonical block PD (least LDL pivot "
            f"{float(least):.3e}).")
        feasible_witness(n, omit, wpt, least, out)
        return "FEASIBLE"
    out(f"    ==> UNDECIDED.  No certificate and no exact PD point ({info}).")
    return "UNDECIDED"


def _cand_canonical(ctx, w0, Z, out):
    """Maximise the margin of the 21 CANONICAL blocks over w = w0 + Z f."""
    import cvxpy as cp
    d, C, srows, srhs, pins, blocks = ctx
    m = len(Z)
    fv = cp.Variable(m)
    t = cp.Variable()
    ones = cp.hstack([cp.Constant(1.0), fv])
    cons = [t <= 1.0]
    for side, name, dd, N, off in blocks:
        cols = [np.array([[float(x) for x in row]
                          for row in contract(N, dd, w0, off)]).reshape(-1)]
        for z in Z:
            cols.append(np.array([[float(x) for x in row]
                                  for row in contract(N, dd, z, off)]
                                 ).reshape(-1))
        Am = np.stack(cols, axis=1)
        sc = np.abs(Am).max() or 1.0
        Mb = cp.reshape((Am / sc) @ ones, (dd, dd), order="C")
        cons.append(0.5 * (Mb + Mb.T) - t * np.eye(dd) >> 0)
    best = None
    for kw in (dict(eps_abs=1e-12, eps_rel=1e-12, max_iters=400000),
               dict(eps_abs=1e-9, eps_rel=1e-9, max_iters=100000)):
        try:
            cp.Problem(cp.Maximize(t), cons).solve(solver=cp.SCS, **kw)
        except Exception:                                        # noqa: BLE001
            continue
        if fv.value is not None and (best is None or float(t.value) > best[0]):
            best = (float(t.value), np.array(fv.value))
    if best is None:
        return None
    out(f"    canonical-basis margin search: t = {best[0]:+.6e}")
    w = [float(x) for x in w0]
    for k in range(len(Z)):
        fk = float(best[1][k])
        if fk:
            for j in range(C):
                if Z[k][j]:
                    w[j] += fk * float(Z[k][j])
    return w


def _cand_logdet(ctx, w0, Z, out):
    """
    The ANALYTIC CENTRE of A: maximise sum_b log det M_b(w).

    Maximising the least eigenvalue lands on the boundary of the region it is
    optimising over -- exactly the worst place to round from.  The log
    barrier instead pushes as far into the interior as the geometry allows, so
    the point it returns has room on every block at once rather than a thin
    margin on one.  Same feasible set, different point in it.
    """
    import cvxpy as cp
    d, C, srows, srhs, pins, blocks = ctx
    fv = cp.Variable(len(Z))
    ones = cp.hstack([cp.Constant(1.0), fv])
    terms = []
    for side, name, dd, N, off in blocks:
        cols = [np.array([[float(x) for x in row]
                          for row in contract(N, dd, w0, off)]).reshape(-1)]
        for z in Z:
            cols.append(np.array([[float(x) for x in row]
                                  for row in contract(N, dd, z, off)]
                                 ).reshape(-1))
        Am = np.stack(cols, axis=1)
        sc = np.abs(Am).max() or 1.0
        Mb = cp.reshape((Am / sc) @ ones, (dd, dd), order="C")
        terms.append(cp.log_det(0.5 * (Mb + Mb.T)))
    try:
        cp.Problem(cp.Maximize(cp.sum(terms))).solve(solver=cp.SCS,
                                                     eps_abs=1e-11,
                                                     eps_rel=1e-11,
                                                     max_iters=400000)
    except Exception:                                            # noqa: BLE001
        return None
    if fv.value is None:
        return None
    out("    analytic-centre (log det) search returned a point")
    w = [float(x) for x in w0]
    for k in range(len(Z)):
        fk = float(fv.value[k])
        if fk:
            for j in range(C):
                if Z[k][j]:
                    w[j] += fk * float(Z[k][j])
    return w


def _cand_blockdiag(ctx, sel, out):
    """The SDP in `blockdiag`'s numerical basis -- a SECOND source of guesses."""
    import cvxpy as cp
    from blockdiag import block_structure
    d, C, srows, srhs, pins, blocks = ctx
    gb = block_structure(d["g_orbits"], d["B"], verbose=False)
    sb = block_structure(d["s_orbits"], d["B"], verbose=False)
    ng = len(d["g_orbits"])
    x = cp.Variable(ng)
    y = cp.Variable(len(d["s_orbits"]))
    z = cp.Variable(len(d["lam_orbit_reps"]))
    t = cp.Variable()
    cons = [d["A0"] @ x + d["A1"] @ y + d["A2"] @ z == d["rhs"], t <= 1.0]
    for bl, var in ((gb, x), (sb, y)):
        for Cb, _ in bl:
            dd = Cb.shape[0]
            Mb = cp.reshape(Cb.reshape(dd * dd, -1) @ var, (dd, dd), order="C")
            cons.append(0.5 * (Mb + Mb.T) - t * np.eye(dd) >> 0)
    for side, _, vec in sel:
        v = np.array(vec, dtype=float)
        cons.append((v[:ng] @ x if side == "s0" else v[ng:ng + y.size] @ y)
                    == 0)
    try:
        cp.Problem(cp.Maximize(t), cons).solve(solver=cp.SCS, eps_abs=1e-12,
                                               eps_rel=1e-12, max_iters=400000)
    except Exception:                                            # noqa: BLE001
        return None
    if x.value is None:
        return None
    out(f"    blockdiag-basis margin search: t = {float(t.value):+.6e}")
    return list(x.value) + list(y.value) + list(z.value)


def feasible_point(n, sel, ctx, piv, R, bb, w0, Z, out):
    """
    Exhibit an exact rational point of A at which all 21 canonical blocks are
    positive definite, or report that none was found.

    TWO independent sources of candidate points are tried, because neither
    dominates: the canonical-basis search asks the solver about exactly the
    blocks that will be tested, but the blockdiag-basis search is the one that
    actually certified H2 at n = 5 (least LDL pivot 5.11e-05) where the
    canonical one stalls at t = -1.24e-06.  Whichever produces a point that
    passes `check_point` wins; both are guesses and the exact test decides.

    Each candidate is projected into A in the EXACT parametrisation
    `w = w0 + sum f_k z_k` with rounded rational `f_k`, so the point satisfies
    every pin and every row of the SDP identity identically -- there is no
    correction step that could undo the positivity.
    """
    d, C, srows, srhs, pins, blocks = ctx
    if not Z:
        return False, "A is a single point"
    info = "no candidate gave a positive definite point"
    Zf = np.array([[float(x) for x in zz] for zz in Z]).T
    w0f = np.array([float(x) for x in w0])
    for make in (lambda: _cand_blockdiag(ctx, sel, out),
                 lambda: _cand_logdet(ctx, w0, Z, out),
                 lambda: _cand_canonical(ctx, w0, Z, out)):
        wnum = make()
        if wnum is None:
            continue
        f, *_ = np.linalg.lstsq(Zf, np.asarray(wnum) - w0f, rcond=None)
        # ONE denominator shared by all the coefficients, scaled to their size.
        # Rounding each f_k to its OWN best denominator is more accurate per
        # coefficient and catastrophic for the witness: the 153 denominators
        # have no common factor, so `w = w0 + sum f_k z_k` acquires their lcm
        # and the stored point came out with entries of 1688 digits and
        # denominators of 846.  That is the trap already recorded twice in this
        # project -- an exact witness nobody can carry into Lean is not much of
        # a witness.  With a common D every entry has denominator dividing
        # D * den(w0), and `scale` keeps D's RELATIVE precision fixed, which is
        # the property the fixed-denominator version lacked.
        scale = max((abs(float(x)) for x in f), default=1.0) or 1.0
        for sig in (6, 9, 12, 15):
            D = int(10 ** sig / scale) + 1
            w = list(w0)
            for k in range(len(Z)):
                fk = F(round(float(f[k]) * D), D)
                if not fk:
                    continue
                zk = Z[k]
                for j in range(C):
                    if zk[j]:
                        w[j] += fk * zk[j]
            good, info = check_point(w, srows, srhs, sel, blocks, C)
            if good:
                return True, (info, w)
    return False, info


def main(ns):
    for n in ns:
        d, C, srows, srhs, pins, blocks = pk.build(n)
        ctx = (d, C, srows, srhs, pins, blocks)
        print(f"\n=== n = {n}:  B = {d['B']},  system {len(srows)} x {C} ===",
              flush=True)
        res = {}
        res["H1  full 321"] = decide(n, pins, "H1  full 321", ctx)
        c201 = [r for r in pins if r[1] != "16x16 Ind(V'|1)"]
        res["H2  201"] = decide(n, c201, "H2  201 (omit sigma_11 16x16)", ctx,
                                omit=("s11", "16x16 Ind(V'|1)"))
        for side, name, dd, N, off in blocks:
            if dd < 2 or name == "16x16 Ind(V'|1)":
                continue
            sel = [r for r in pins if not (r[0] == side and r[1] == name)]
            lab = f"H3  omit {side} {name} ({dd}x{dd})"
            res[lab] = decide(n, sel, lab, ctx, omit=(side, name))
        print(f"\n  SUMMARY n = {n}", flush=True)
        for k, v in res.items():
            print(f"    {k:52s} {v}", flush=True)


if __name__ == "__main__":
    main([int(a) for a in sys.argv[1:]] or [5, 6])
