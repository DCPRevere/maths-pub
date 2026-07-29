"""
The recession cone of the design SDP, derived rather than probed.

WHY THIS IS THE BLOCKER.  design_sdp.py maximises a margin over an UNBOUNDED
feasible set, so the optimum is whatever point the solver stops at on an
unbounded face; the scaled optima oscillate (f6*n^3 = 149, 20.3, 9.69, 35311,
13.3, 83681, 6.66 at n = 20..2000) and no low-degree curve can track them.

THE RECESSION CONE, EXACTLY.  The certificate sought is

    F(b) = sigma_0(b) + sum_ij sigma_ij(b) (1/n + b_ij) + lambda(b) (sum_kl b_kl)

with sigma_0, sigma_ij sums of squares in the degree-1 basis {b_ij} and lambda
free.  A recession direction is a homogeneous solution with the sigmas still PSD:

    0 = s_0(b) + sum_ij s_ij(b) (1/n + b_ij) + l(b) (sum b_kl).

Restrict to the hyperplane H = {sum b = 0}.  There the last term vanishes and the
other terms are all >= 0 on K_n (which has non-empty interior in H), so EACH
vanishes on K_n, hence identically on H.  Now s_0 = b^T G b with G PSD, and it
vanishes on H, so b^T G b = (1^T b)(w^T b); symmetrising, G = (1 w^T + w 1^T)/2,
which is PSD only if w = c*1 with c >= 0.  So G = c_0 * J.  The same argument
applies to each s_ij, because (1/n + b_ij) is not identically zero on H.

    RECESSION CONE = { sigma_0 Gram = c_0 * J,  sigma_11 Gram = c_1 * J,
                       c_0, c_1 >= 0 },  lambda determined.

It is exactly TWO-dimensional.  In orbit coordinates that is (a,b,c) = c_0(1,1,1)
and all eleven sigma_11 orbit variables equal to c_1.

WHAT IT DOES TO THE TEN QUANTITIES.  c_0 * J has sigma_0 eigenvalues
(n^2 c_0, 0, 0), so it moves theta_0 ONLY.  c_1 * J is n^2 times the projection
onto the all-ones vector, which lies in the trivial isotypic component, so it
moves the 3x3 A block by a rank-one PSD matrix and leaves B, C and D untouched.

CONSEQUENCE.  Fix the two recession coordinates by two linear equations and the
feasible set becomes COMPACT (a closed convex set is bounded iff its recession
cone is trivial).  Then the max-margin point and the analytic centre are both
canonical and vary smoothly with n, which is what a low-degree fit needs.
"""

import os
import sys
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "dittert"))
sys.path.insert(0, HERE)
import blocks as bl                                              # noqa: E402
import general_k3 as g                                           # noqa: E402
from general_k3 import RF                                        # noqa: E402

RES = g.solve_symbolic(verbose=False)
SYM = RES["sym"]
FREE = RES["free_cols"]
PIV = RES["piv_cols"]
NG = len(SYM["gvars"])
NS = len(SYM["svars"])
NL = len(SYM["lvars"])
NVAR = NG + NS + NL
IDX = bl.svar_index()


def system_rows():
    """The 12 x 19 coefficient matrix over Q(n), and the right-hand side."""
    n_poly = [F(0), F(1)]
    M = []
    for r in range(len(SYM["rows"])):
        row = [RF(p) for p in SYM["A0"][r]]
        row += [RF(SYM["A1c"][r][j], n_poly) + RF(SYM["A1l"][r][j])
                for j in range(NS)]
        row += [RF(p) for p in SYM["A2"][r]]
        M.append(row)
    return M


def homogeneous_map():
    """
    x -> the 19 variables, for x the 8 free variables, with the INHOMOGENEOUS
    part dropped.  Exact over Q(n).  (RES["A"] is the reduced row echelon form,
    so pivot = -sum A[i][free]*x_free.)
    """
    cols = [[RF([]) for _ in range(len(FREE))] for _ in range(NVAR)]
    for t, c in enumerate(FREE):
        cols[c][t] = RF([F(1)])
    for i, c in enumerate(PIV):
        for t, fc in enumerate(FREE):
            a = RES["A"][i][fc]
            if a:
                cols[c][t] = RF([]) - a
    return cols


def in_kernel(vec19, M):
    """Is this 19-vector an exact solution of the homogeneous system over Q(n)?"""
    bad = []
    for r, row in enumerate(M):
        s = RF([])
        for j in range(NVAR):
            if vec19[j]:
                s = s + row[j] * vec19[j]
        if s:
            bad.append(r)
    return bad


def direction(gvals, svals, M=None):
    """
    The homogeneous solution whose sigma_0 orbit values are `gvals` and sigma_11
    orbit values are `svals`, with lambda solved for exactly over Q(n).
    Returns (19-vector, failing rows) or (None, None) if no lambda exists.
    """
    M = system_rows() if M is None else M
    v = [RF([]) for _ in range(NVAR)]
    for j in range(NG):
        v[j] = gvals[j]
    for j in range(NS):
        v[NG + j] = svals[j]
    rhs = []
    for r, row in enumerate(M):
        s = RF([])
        for j in range(NG + NS):
            if v[j]:
                s = s + row[j] * v[j]
        rhs.append(RF([]) - s)
    A = [[M[r][NG + NS + j] for j in range(NL)] for r in range(len(M))]
    z, ok = solve_rf(A, rhs)
    if not ok:
        return None, None
    for j in range(NL):
        v[NG + NS + j] = z[j]
    return v, in_kernel(v, M)


def class_of(cell):
    i, j = cell
    if i == 0 and j == 0:
        return "K"
    if i == 0 or j == 0:
        return "R"
    return "I"


def lineality_generators():
    """
    The LINEALITY SPACE of the design problem after theta_0 and the s-direction
    of the A block are removed -- that is, of the eight recession-invariant
    "hard" quantities.

    Derivation.  A direction d is in it iff the homogeneous identity holds with
    G(d) and H(d) positive semidefinite ON 1^perp (the hyperplane sum b = 0 is
    exactly 1^perp, and it is where the Positivstellensatz argument of the module
    docstring lives).  A quadratic form that is PSD on 1^perp and vanishes there
    identically is exactly P G P = 0, i.e.

        G = 1 u^T + u 1^T ,      H = 1 v^T + v 1^T .

    G must be invariant under the full group, which is transitive on cells, so
    u = mu * 1 and G = 2 mu J -- one dimension.  H need only be invariant under
    Stab((0,0)), whose orbits on cells are {K}, R u C and I, so v is constant on
    those three classes -- three dimensions.  Total FOUR, and it is a subspace,
    not just a cone, because no sign condition survives.

    Effect: theta_0 moves freely, A moves by s w^T + w s^T with w arbitrary
    (s = (1, 2(n-1), (n-1)^2)), and nothing else moves at all.
    """
    M = system_rows()
    svars = SYM["svars"]
    zero_g = [RF([]) for _ in range(NG)]
    zero_s = [RF([]) for _ in range(NS)]
    gens = []

    # mu: G = J, H = 0
    gens.append(("mu   (G = J)",
                 direction([RF([F(1)])] * NG, zero_s, M)))
    # v supported on one class at a time
    for cls in ("K", "R", "I"):
        sv = []
        for key in svars:
            val = sum(1 for cell in key if class_of(cell) == cls)
            sv.append(RF([F(val)]) if val else RF([]))
        gens.append((f"v_{cls} (H = 1 v^T + v 1^T)", direction(zero_g, sv, M)))
    return gens


def lineality_free():
    """The four lineality generators as 8-vectors of free coordinates over Q(n).

    Order: mu (sigma_0 Gram += J), then v_K, v_R, v_I.
    """
    out = []
    for _, (v, bad) in lineality_generators():
        if v is None or bad:
            raise RuntimeError("lineality generator failed its kernel check")
        out.append(free_coords(v))
    return out


def recession_generators():
    """
    r0 : sigma_0 Gram = J, sigma_11 Gram = 0
    r1 : sigma_0 Gram = 0, sigma_11 Gram = J
    with lambda solved for, exactly over Q(n).  Returns their FREE coordinates.
    """
    M = system_rows()
    out = []
    for which in (0, 1):
        # the sigma part is forced; solve the 12 rows for the 5 lambda unknowns
        v = [RF([]) for _ in range(NVAR)]
        if which == 0:
            for j in range(NG):
                v[j] = RF([F(1)])
        else:
            for j in range(NS):
                v[NG + j] = RF([F(1)])
        rhs = []
        for r, row in enumerate(M):
            s = RF([])
            for j in range(NG + NS):
                if v[j]:
                    s = s + row[j] * v[j]
            rhs.append(RF([]) - s)
        # least-structure solve of A2 z = rhs over Q(n)
        A = [[M[r][NG + NS + j] for j in range(NL)] for r in range(len(M))]
        z, ok = solve_rf(A, rhs)
        if not ok:
            out.append((None, None))
            continue
        for j in range(NL):
            v[NG + NS + j] = z[j]
        out.append((v, in_kernel(v, M)))
    return out


def solve_rf(A, b):
    """Gauss-Jordan over Q(n); returns (solution with free vars = 0, consistent)."""
    nr, nc = len(A), len(A[0])
    A = [row[:] for row in A]
    b = b[:]
    piv, r = [], 0
    for c in range(nc):
        p = next((i for i in range(r, nr) if A[i][c]), None)
        if p is None:
            continue
        A[r], A[p] = A[p], A[r]
        b[r], b[p] = b[p], b[r]
        pv = A[r][c]
        A[r] = [x / pv for x in A[r]]
        b[r] = b[r] / pv
        for i in range(nr):
            if i != r and A[i][c]:
                f = A[i][c]
                A[i] = [A[i][j] - f * A[r][j] for j in range(nc)]
                b[i] = b[i] - f * b[r]
        piv.append(c)
        r += 1
    for i in range(r, nr):
        if b[i]:
            return None, False
    z = [RF([]) for _ in range(nc)]
    for i, c in enumerate(piv):
        z[c] = b[i]
    return z, True


def free_coords(vec19):
    """The free coordinates of a 19-vector in the solution space."""
    return [vec19[c] for c in FREE]


def main():
    print("recession cone of the k = 3 design SDP, derived exactly over Q(n)")
    print(f"  variables: sigma_0 {NG}, sigma_11 {NS}, lambda {NL}  (total {NVAR})")
    print(f"  free columns {FREE}")
    print(f"  pivot columns {PIV}")
    print()

    gens = recession_generators()
    names = ["r0  (sigma_0 Gram = J)", "r1  (sigma_11 Gram = J)"]
    hom = homogeneous_map()
    good = []
    for nm, (v, bad) in zip(names, gens):
        if v is None:
            print(f"  {nm}: NO lambda exists -- not a recession direction")
            continue
        print(f"  {nm}: exact homogeneous solution, failing rows {bad}")
        if bad:
            continue
        # round trip: its free coordinates must regenerate it
        fcoord = free_coords(v)
        rt_ok = True
        for j in range(NVAR):
            s = RF([])
            for t in range(len(FREE)):
                if hom[j][t] and fcoord[t]:
                    s = s + hom[j][t] * fcoord[t]
            if s != v[j]:
                rt_ok = False
        print(f"      round trip through the free coordinates: {rt_ok}")
        print("      free coordinates: "
              + ", ".join(f"f{FREE[t]}={fcoord[t]}" for t in range(len(FREE))))
        good.append(fcoord)

    print("\nLINEALITY SPACE of the eight recession-invariant quantities")
    lin = []
    for nm, (v, bad) in lineality_generators():
        if v is None:
            print(f"  {nm}: NO lambda exists")
            continue
        print(f"  {nm}: exact homogeneous solution, failing rows {bad}")
        if bad:
            continue
        lin.append(free_coords(v))
        print("      " + ", ".join(f"f{FREE[t]}={lin[-1][t]}"
                                   for t in range(len(FREE))))
    print(f"\n  generators found: {len(lin)}")
    if lin:
        rk = rank_rf(lin)
        print(f"  rank over Q(n): {rk}")
    return good, lin


def rank_rf(rows):
    """Rank of a list of Q(n)-vectors."""
    A = [r[:] for r in rows]
    nr, nc = len(A), len(A[0])
    r = 0
    for c in range(nc):
        p = next((i for i in range(r, nr) if A[i][c]), None)
        if p is None:
            continue
        A[r], A[p] = A[p], A[r]
        pv = A[r][c]
        A[r] = [x / pv for x in A[r]]
        for i in range(nr):
            if i != r and A[i][c]:
                f = A[i][c]
                A[i] = [A[i][j] - f * A[r][j] for j in range(nc)]
        r += 1
    return r


if __name__ == "__main__":
    main()
