"""
PILOT for the §6b.5 mitigation: can the blocks be made DIAGONAL by linear
conditions on the free variables?

Why this is the right first test.  §6b.5 shows the naive route -- all leading
principal minors of blocks up to 16x16 -- puts Sturm at degree of order 240.  The
escape is the k = 3 move: at k = 3, pinning C01 = 0 and T01 = 0 made both 2x2
blocks diagonal, so definiteness became positivity of the DIAGONAL entries, of
degree ~15 rather than ~240.  Off-diagonal block entries are LINEAR in the free
variables, so this is a linear solvability question, not a search.

The pilot uses only the TRIVIAL isotypic blocks, which need no representation
theory at all: their basis is the orbit-indicator vectors, and the block is
E^T H E for E the matrix of orbit indicators.  E has full column rank, so H > 0
implies this block > 0 -- it is a genuine necessary condition and a genuine
block, not a proxy.  Measured sizes: 14 Stab-orbits on the basis and 4 G-orbits,
both stable at n = 5, 6, 7.

WHAT IS BEING DECIDED.  14x14 gives 91 off-diagonal conditions and 4x4 gives 6,
so 97 linear equations in the 354 free variables.  If they are solvable here, the
full programme's 322 conditions against 354 free variables is plausible and the
expensive symbolic block-diagonalisation is worth paying for.  If they are NOT
solvable on the easiest block, the mitigation is dead and we learn it cheaply.

A rank computed at one specific n is enough to conclude over Q(n): rank can only
DROP at special n, so full rank at a single n proves full rank generically.
Solvability, by contrast, has to be read the other way round -- so both the rank
and the consistency are checked at two different n.
"""

import os
import sys
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "dittert"))
sys.path.insert(0, HERE)
import k4_solve                                                  # noqa: E402
import k4_system as k4                                           # noqa: E402
import sos                                                       # noqa: E402
from general_k3 import cells_of                                  # noqa: E402
from symmetry import act, generators, monomials, orbits          # noqa: E402


def pair_class_map(n, fix_zero):
    """
    (u, v) index pair -> symbolic variable index, via union-find at this n.

    canon_pair is called only on the few hundred class REPRESENTATIVES, never on
    all B^2 pairs -- at n = 6 that is 356 calls instead of 492804.
    """
    basis = k4.basis_of(n)
    B = len(basis)
    gens = sos.stab_generators(n, (0, 0)) if fix_zero else generators(n)
    orbs = sos.sym_pair_orbits(basis, gens)
    keys = k4.build(verbose=False)["svars" if fix_zero else "gvars"]
    kindex = {k2: i for i, k2 in enumerate(keys)}
    cls = [0] * (B * B)
    for orb in orbs:
        u, v = divmod(orb[0], B)
        key = k4.canon_pair(cells_of(basis[u], n), cells_of(basis[v], n),
                            fix_zero)
        j = kindex[key]
        for code in orb:
            cls[code] = j
    return basis, B, cls


def trivial_block_counts(n, fix_zero):
    """
    N[(i,j)][c] = #{(u,v) in O_i x O_j : class(u,v) = c}, for the orbit-sum
    basis of the trivial isotypic component.  Returns (norb, N).
    """
    basis, B, cls = pair_class_map(n, fix_zero)
    gens = sos.stab_generators(n, (0, 0)) if fix_zero else generators(n)
    reps, _ = orbits(basis, gens)
    orbit_of = [0] * B
    for oi, (_, members) in enumerate(reps.items()):
        for t in members:
            orbit_of[t] = oi
    norb = len(reps)
    nvar = max(cls) + 1
    N = {}
    for u in range(B):
        ou = orbit_of[u]
        base = u * B
        for v in range(B):
            key = (ou, orbit_of[v])
            row = N.get(key)
            if row is None:
                row = N[key] = [0] * nvar
            row[cls[base + v]] += 1
    return norb, N


def rank_and_consistency(M, rhs):
    """Exact rank over Q, and whether M f = rhs is solvable."""
    nr = len(M)
    nc = len(M[0]) if nr else 0
    A = [row[:] + [rhs[i]] for i, row in enumerate(M)]
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
                A[i] = [A[i][j] - f * A[r][j] for j in range(nc + 1)]
        r += 1
        if r == nr:
            break
    inconsistent = any(all(A[i][c] == 0 for c in range(nc)) and A[i][nc] != 0
                       for i in range(nr))
    return r, not inconsistent


def pilot(n):
    print(f"\n=== n = {n} ===")
    res = k4_solve.solve(verbose=False)
    sym = res["sym"]
    ng, ns = len(sym["gvars"]), len(sym["svars"])
    free = res["free_cols"]
    nf = len(free)

    # affine parametrisation of all 440 variables at this n
    const = [F(0)] * res["ncol"]
    coef = [[F(0)] * nf for _ in range(res["ncol"])]
    for t, c in enumerate(free):
        coef[c][t] = F(1)
    for i, c in enumerate(res["piv_cols"]):
        const[c] = res["b"][i].at(F(n))
        for t, fc in enumerate(free):
            a = res["A"][i][fc]
            if a:
                coef[c][t] = -a.at(F(n))

    rows, rhs = [], []
    total_off = 0
    for fix_zero, offset, label in ((True, ng, "sigma_11 trivial"),
                                    (False, 0, "sigma_0 trivial")):
        norb, N = trivial_block_counts(n, fix_zero)
        off = norb * (norb - 1) // 2
        total_off += off
        print(f"  {label} block: {norb} x {norb}, {off} off-diagonal conditions")
        for i in range(norb):
            for j in range(i + 1, norb):
                cnt = N.get((i, j))
                if cnt is None:
                    continue
                c0 = F(0)
                row = [F(0)] * nf
                for c, m in enumerate(cnt):
                    if not m:
                        continue
                    v = offset + c
                    c0 += m * const[v]
                    cv = coef[v]
                    for t in range(nf):
                        if cv[t]:
                            row[t] += m * cv[t]
                rows.append(row)
                rhs.append(-c0)

    r, ok = rank_and_consistency(rows, rhs)
    print(f"  {len(rows)} conditions in {nf} free variables: rank {r}, "
          f"solvable: {ok}")
    print(f"  -> {'FULL rank' if r == len(rows) else 'RANK DEFICIENT'}"
          f" ({r} of {len(rows)});  free variables left after imposing: "
          f"{nf - r}")
    return r, len(rows), ok, nf


if __name__ == "__main__":
    ns = [int(a) for a in sys.argv[1:]] or [6]
    for n in ns:
        pilot(n)
