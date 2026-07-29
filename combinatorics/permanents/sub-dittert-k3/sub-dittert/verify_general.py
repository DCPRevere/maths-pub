"""
Verify the general-n k = 3 certificate AT SPECIFIC n, exactly over Q.

Everything here re-derives the objective from the DEFINITION in the 1992 paper --
elementary symmetric functions of the row and column sums, and sigma_k as a sum
of subpermanents -- and never uses the closed forms of general_k3.py, the block
decomposition of blocks.py, or the Sturm machinery.  The only shared code is the
orbit bookkeeping needed to inflate 19 numbers into two n^2 x n^2 matrices, and
that is exercised against the ALREADY-VERIFIED stored certificates as a positive
control, and against deliberate mutations as a negative control.

Checks at each n:
  [1] both Gram matrices symmetric and POSITIVE DEFINITE, by exact rational
      LDL^T on the full n^2 x n^2 matrices;
  [2] the identity F(b) = sigma_0(b) + sum_p (1/n + b_p) sigma_p(b)
      + lambda(b) (sum_q b_q), by exact evaluation at random rational points,
      with F computed from the definition;
  [3] the bound M = 2 - k!/n^k.

Positive definiteness of the single Gram H at the corner gives it for every
sigma_p, because sigma_p's Gram is a permutation conjugate of H.
"""

import itertools
import os
import random
import sys
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "dittert"))
sys.path.insert(0, HERE)
import certificate as cert                                       # noqa: E402
import exactsd                                                   # noqa: E402
import general_k3 as g                                           # noqa: E402
import sos                                                       # noqa: E402
from symmetry import generators, monomials, orbits               # noqa: E402

K = 3


# ------------------------------------------------------- the objective, from scratch
def esym(vals, k):
    """Elementary symmetric polynomial e_k, by the standard recurrence."""
    e = [F(0)] * (k + 1)
    e[0] = F(1)
    for v in vals:
        for j in range(min(k, len(e) - 1), 0, -1):
            e[j] += e[j - 1] * v
    return e[k]


def sigma_k(A, n, k):
    """sum over k-subsets I, J of per(A[I][J]) -- the definition, directly."""
    tot = F(0)
    idx = list(range(n))
    perms = list(itertools.permutations(range(k)))
    for I in itertools.combinations(idx, k):
        rows = [A[i] for i in I]
        for J in itertools.combinations(idx, k):
            s = F(0)
            for pm in perms:
                t = F(1)
                for a in range(k):
                    t *= rows[a][J[pm[a]]]
                s += t
            tot += s
    return tot


def objective_F(b, n, k=K):
    """F(b) = (2 - k!/n^k) - [E_k(r) + E_k(c) - P_k(A)] at A = J/n + b."""
    A = [[F(1, n) + b[i * n + j] for j in range(n)] for i in range(n)]
    r = [sum(row) for row in A]
    c = [sum(A[i][j] for i in range(n)) for j in range(n)]
    from math import comb, factorial
    Cnk = F(comb(n, k))
    M = F(2) - F(factorial(k), n ** k)
    Ek_r = esym(r, k) / Cnk
    Ek_c = esym(c, k) / Cnk
    Pk = sigma_k(A, n, k) / (Cnk * Cnk)
    return M - (Ek_r + Ek_c - Pk), M


# --------------------------------------------------------------- the certificate
def orbit_data(n):
    """Gram-basis orbits at this n, and the map onto the symbolic orbit keys."""
    N = n * n
    basis = [(u,) for u in range(N)]
    gens = generators(n)
    sgens = sos.stab_generators(n, (0, 0))
    g_orbits = sos.sym_pair_orbits(basis, gens)
    s_orbits = sos.sym_pair_orbits(basis, sgens)
    lam_mons = monomials(N, 2)
    lreps, _ = orbits(lam_mons, gens)
    lam_orbit_reps = [members for _, members in lreps.items()]
    return basis, g_orbits, s_orbits, lam_mons, lam_orbit_reps


def cells_of(mono, n):
    return [(t // n, t % n) for t in mono]


def certificate_at(n, vals19=None):
    """The 19 rationals at this n, and the two Gram matrices."""
    sym = g.build_symbolic_system(K)
    if vals19 is None:
        fs, _ = cert.build()
        vals19 = [v.at(F(n)) for v in cert.vals19(fs)]
    x = vals19[:3]
    y = vals19[3:14]
    z = vals19[14:]
    basis, g_orbits, s_orbits, lam_mons, lam_reps = orbit_data(n)
    B = len(basis)

    def key_of(orb, fix):
        u, v = divmod(orb[0], B)
        return g.canon(cells_of(basis[u] + basis[v], n), fix)

    xs = [x[sym["gvars"].index(key_of(o, False))] for o in g_orbits]
    ys = [y[sym["svars"].index(key_of(o, True))] for o in s_orbits]
    zs = [z[sym["lvars"].index(g.canon(cells_of(lam_mons[m[0]], n)))]
          for m in lam_reps]
    G0 = exactsd.assemble(B, g_orbits, xs)
    H = exactsd.assemble(B, s_orbits, ys)
    lam = {}
    for vi, members in enumerate(lam_reps):
        if not zs[vi]:
            continue
        for t in members:
            lam[lam_mons[t]] = lam.get(lam_mons[t], F(0)) + zs[vi]
    return vals19, G0, H, lam, basis


def rhs_at(b, n, G0, H, lam, basis):
    """sigma_0(b) + sum_p (1/n + b_p) sigma_p(b) + lambda(b) * sum_q b_q."""
    N = n * n
    B = len(basis)
    tot = F(0)
    for u in range(B):
        bu = b[u]
        if not bu:
            continue
        row = G0[u]
        for v in range(B):
            if row[v] and b[v]:
                tot += row[v] * bu * b[v]
    trans = sos.transporters(n, (0, 0))
    for p in range(N):
        gp = trans[p]
        w = [b[gp[u]] for u in range(B)]            # sigma_p(b) = sigma_11(g_p b)
        s = F(0)
        for u in range(B):
            wu = w[u]
            if not wu:
                continue
            row = H[u]
            for v in range(B):
                if row[v] and w[v]:
                    s += row[v] * wu * w[v]
        tot += (F(1, n) + b[p]) * s
    sb = sum(b)
    lv = F(0)
    for mono, c in lam.items():
        t = c
        for v in mono:
            t *= b[v]
        lv += t
    return tot + lv * sb


def run(n, vals19=None, trials=2, seed=1, label=""):
    print(f"\n=== n = {n} {label}===")
    vals19, G0, H, lam, basis = certificate_at(n, vals19)
    N = n * n
    print(f"  Gram size {N} x {N}, lambda monomials {len(lam)}")

    print("  [1] symmetry and exact rational LDL^T")
    for nm, G in (("sigma_0 ", G0), ("sigma_11", H)):
        if not exactsd.is_symmetric(G):
            print(f"      {nm}: NOT SYMMETRIC")
            return False
        piv, badk = exactsd.ldl_pivots(G)
        if piv is None:
            print(f"      {nm}: NOT positive definite (pivot {badk} <= 0)")
            return False
        print(f"      {nm}: positive definite, min pivot {float(min(piv)):.6e}")

    from math import factorial
    M = F(2) - F(factorial(K), n ** K)
    print(f"  [3] bound M = {M} = 2 - {K}!/n^{K}")

    print(f"  [2] identity at {trials} random rational points, exactly over Q")
    rng = random.Random(seed)
    for t in range(trials):
        b = [F(rng.randint(-40, 40), rng.randint(1, 9) * n)
             for _ in range(N)]
        lhs, _ = objective_F(b, n)
        rhs = rhs_at(b, n, G0, H, lam, basis)
        same = lhs == rhs
        print(f"      point {t + 1}: F(b) == certificate  ->  {same}")
        if not same:
            print(f"        F   = {lhs}")
            print(f"        cert= {rhs}")
            print(f"        difference = {lhs - rhs}")
            return False
    return True


def mutation_test(n, seed=3):
    """A verifier that never rejects proves nothing."""
    print(f"\n=== mutation test at n = {n} ===")
    fs, _ = cert.build()
    vals = [v.at(F(n)) for v in cert.vals19(fs)]
    rng = random.Random(seed)
    for which in (0, 5, 16):
        bad = list(vals)
        bad[which] += F(1, 10 ** 6)
        try:
            ok = run(n, bad, trials=1, seed=9,
                     label=f"(variable {which} perturbed) ")
        except Exception as exc:                                 # noqa: BLE001
            ok = False
            print(f"      rejected with {type(exc).__name__}")
        print(f"  perturbing variable {which}: "
              f"{'REJECTED as it must be' if not ok else 'ACCEPTED -- BAD'}")
        if ok:
            return False
    return True


def stored_control(n=4, k=3, db=1):
    """
    POSITIVE CONTROL.  Run the same objective_F and rhs_at on the STORED,
    already-verified certificate, using its own orbit data rather than any
    mapping of ours.  If this fails, the verifier is wrong, not the certificate.
    """
    import pickle
    src = os.path.join(HERE, "results", f"subdittert_n{n}k{k}d{db}.pkl")
    if not os.path.exists(src):
        print(f"\n(no stored certificate at {src})")
        return None
    with open(src, "rb") as fh:
        c = pickle.load(fh)
    basis = c["basis"]
    B = len(basis)
    G0 = exactsd.assemble(B, c["g_orbits"], c["xq"])
    H = exactsd.assemble(B, c["s_orbits"], c["yq"])
    lam_mons = monomials(n * n, c["TOPDEG"] - 1)
    lam = {}
    for vi, members in enumerate(c["lam_orbit_reps"]):
        if not c["zq"][vi]:
            continue
        for t in members:
            lam[lam_mons[t]] = lam.get(lam_mons[t], F(0)) + c["zq"][vi]
    print(f"\n=== POSITIVE CONTROL: stored certificate at n = {n} ===")
    rng = random.Random(17)
    ok = True
    for t in range(2):
        b = [F(rng.randint(-40, 40), rng.randint(1, 9) * n)
             for _ in range(n * n)]
        lhs, _ = objective_F(b, n, k)
        rhs = rhs_at(b, n, G0, H, lam, basis)
        print(f"  point {t + 1}: stored certificate reproduces F  ->  "
              f"{lhs == rhs}")
        ok = ok and lhs == rhs
    return ok


if __name__ == "__main__":
    args = sys.argv[1:]
    if args and args[0] == "control":
        stored_control(4)
        stored_control(5)
        mutation_test(4)
        sys.exit(0)
    ns = [int(a) for a in args] or [12]
    allok = True
    for n in ns:
        allok = run(n) and allok
    print(f"\nall checks passed: {allok}")
