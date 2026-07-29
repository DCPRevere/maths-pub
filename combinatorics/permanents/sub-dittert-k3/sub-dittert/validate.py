"""
Independent validation of the sub-Dittert objective.

Three separate things are tested, because getting sigma_k wrong is the easiest
way to prove a theorem about the wrong function.

1. TWO STRUCTURALLY DIFFERENT ALGORITHMS FOR sigma_k.

   Route A (used by expand.py): enumerate all C(n,k)^2 pairs of k-subsets and
   sum the permanent of each k x k submatrix over the k! permutations.

   Route B (only here): the generating identity

       per(A + x J_n) = sum_{k=0}^{n} x^{n-k} (n-k)! sigma_k(A),

   with the order-n permanent computed by RYSER inclusion-exclusion over the
   2^n column subsets, in the polynomial ring Q[x].  Route B never forms a
   submatrix and never enumerates a k-subset, so a shared bug is implausible.

   Proof of the identity, for the record: expanding prod_i (a_{i,s(i)} + x) over
   permutations s and over the subset S of rows that contribute their a-term
   gives, for each S with |S| = j, the sum over injections S -> columns of
   prod_{i in S} a; the other n - j rows are free, contributing (n-j)! .
   Grouping the injections by their image set T yields sum_T per(A[S|T]).

2. THE k = n POSITIVE CONTROL.  At k = n the statement is Dittert's conjecture
   verbatim.  The polynomial built here at (4,4) is compared COEFFICIENT BY
   COEFFICIENT with the one built by dittert/expand.py, which is already the
   basis of a verified certificate.  This is ground truth, not self-consistency.

3. THE 61/32 TRAP.  2 - gamma(4,3) = 2 - gamma(4,4) = 61/32.  So the right-hand
   side alone cannot tell the two cases apart.  We assert explicitly that the
   two F polynomials DIFFER, and that F(4,3) has degree 3 while F(4,4) has
   degree 4.
"""

import itertools
import os
import random
import sys
from fractions import Fraction as F
from math import comb, factorial

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import expand                                                    # noqa: E402


# ---------------------------------------------------------------- univariate
def upoly_mul(p, q):
    out = [F(0)] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        if not a:
            continue
        for j, b in enumerate(q):
            if b:
                out[i + j] += a * b
    return out


def upoly_add(p, q):
    m = max(len(p), len(q))
    return [(p[i] if i < len(p) else F(0)) + (q[i] if i < len(q) else F(0))
            for i in range(m)]


def ryser_permanent_upoly(M):
    """per(M) for M with entries in Q[x], by Ryser inclusion-exclusion."""
    m = len(M)
    total = [F(0)]
    for r in range(1, m + 1):
        for S in itertools.combinations(range(m), r):
            prod = [F(1)]
            for i in range(m):
                s = [F(0)]
                for j in S:
                    s = upoly_add(s, M[i][j])
                prod = upoly_mul(prod, s)
            sign = F((-1) ** (m - r))
            total = upoly_add(total, [sign * c for c in prod])
    return total


def sigma_k_route_B(A, k):
    """sigma_k via per(A + xJ), Ryser, coefficient of x^{n-k} over (n-k)!."""
    n = len(A)
    M = [[[A[i][j], F(1)] for j in range(n)] for i in range(n)]   # a_ij + x
    p = ryser_permanent_upoly(M)
    while len(p) < n + 1:
        p.append(F(0))
    return p[n - k] / factorial(n - k)


def sigma_k_route_A(A, k):
    """sigma_k by explicit enumeration of k x k subpermanents."""
    n = len(A)
    tot = F(0)
    for alpha in itertools.combinations(range(n), k):
        for beta in itertools.combinations(range(n), k):
            for s in itertools.permutations(range(k)):
                pr = F(1)
                for i in range(k):
                    pr *= A[alpha[i]][beta[s[i]]]
                tot += pr
    return tot


def e_k(vals, k):
    e = [F(1)] + [F(0)] * k
    for v in vals:
        for j in range(min(k, len(e) - 1), 0, -1):
            e[j] += e[j - 1] * v
    return e[k]


def objective_direct(A, k):
    """E_k(r) + E_k(c) - P_k(A), computed from scratch, route B for sigma."""
    n = len(A)
    r = [sum(A[i][j] for j in range(n)) for i in range(n)]
    c = [sum(A[i][j] for i in range(n)) for j in range(n)]
    return (e_k(r, k) / comb(n, k) + e_k(c, k) / comb(n, k)
            - sigma_k_route_B(A, k) / comb(n, k) ** 2)


def random_matrix(rng, n, bound=9):
    return [[F(rng.randint(0, bound), rng.randint(1, bound))
             for _ in range(n)] for _ in range(n)]


# ---------------------------------------------------------------------- tests
def test_sigma_two_routes(trials=40, seed=20260728):
    rng = random.Random(seed)
    bad = 0
    for _ in range(trials):
        n = rng.choice([2, 3, 4, 5])
        k = rng.randint(1, n)
        A = random_matrix(rng, n)
        a, b = sigma_k_route_A(A, k), sigma_k_route_B(A, k)
        if a != b:
            bad += 1
            print(f"    MISMATCH n={n} k={k}: {a} vs {b}")
    print(f"  [1] sigma_k, naive enumeration vs Ryser on per(A+xJ): "
          f"{trials - bad}/{trials} agree")
    return bad == 0


def test_symbolic_against_direct(nk_list, trials=8, seed=5150):
    """The polynomial F(b) evaluated vs the objective recomputed from scratch."""
    rng = random.Random(seed)
    ok = True
    for (n, k) in nk_list:
        d = expand.build(n, k)
        N = n * n
        for _ in range(trials):
            b = [F(rng.randint(-30, 30), rng.randint(1, 17)) for _ in range(N)]
            A = [[F(1, n) + b[i * n + j] for j in range(n)] for i in range(n)]
            lhs = expand.evaluate(d["F"], b)
            rhs = d["M"] - objective_direct(A, k)
            if lhs != rhs:
                ok = False
                print(f"    MISMATCH (n,k)=({n},{k}): {lhs} vs {rhs}")
    print(f"  [2] symbolic F(b) vs from-scratch objective on random rational "
          f"points, {nk_list}: {'ALL AGREE' if ok else 'FAILED'}")
    return ok


def _load_dittert_expand():
    """Load dittert/expand.py under its own module name (both files are
    called expand.py, so a plain import would return this package's one)."""
    import importlib.util
    path = os.path.join(os.path.dirname(HERE), "dittert", "expand.py")
    spec = importlib.util.spec_from_file_location("dittert_expand", path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def test_k_equals_n_is_dittert():
    """(4,4) must reproduce dittert/expand.py exactly, coefficient by coefficient."""
    dexp = _load_dittert_expand()
    assert dexp is not expand
    Fd, idx, M, *_ = dexp.build(4)
    d = expand.build(4, 4)
    Fs = d["F"]
    same_M = (M == d["M"])
    keys = set(Fd) | set(Fs)
    diff = [e for e in keys if Fd.get(e, F(0)) != Fs.get(e, F(0))]
    print(f"  [3] k=n control: dittert/expand.py build(4) vs sub-dittert (4,4)")
    print(f"      M equal: {same_M} ({M})")
    print(f"      monomials: dittert {len(Fd)}, sub-dittert {len(Fs)}, "
          f"differing coefficients: {len(diff)}")
    return same_M and not diff


def test_61_32_trap():
    """2 - gamma(n,k) collides for k = n-1 and k = n at n = 4 AND at n = 5.
    The bound alone therefore cannot tell the two cases apart, and at n = 5 the
    colliding value 1226/625 is the published Dittert n=5 constant.  Assert that
    the POLYNOMIALS differ in each case."""
    ok = True
    for n, expect in [(4, F(61, 32)), (5, F(1226, 625))]:
        da = expand.build(n, n - 1)
        db = expand.build(n, n)
        same_rhs = (da["M"] == db["M"] == expect)
        keys = set(da["F"]) | set(db["F"])
        diff = sum(1 for e in keys
                   if da["F"].get(e, F(0)) != db["F"].get(e, F(0)))
        dga = max(sum(e) for e in da["F"])
        dgb = max(sum(e) for e in db["F"])
        good = same_rhs and diff > 0 and dga == n - 1 and dgb == n
        ok = ok and good
        print(f"  [4] n={n}: 2-gamma identical at k={n-1} and k={n} "
              f"(= {expect}): {same_rhs}")
        print(f"      polynomials differ in {diff} coefficients, "
              f"degrees {dga} and {dgb}: {'separated' if good else 'FAILED'}")
    return ok


def test_k_one_identity(seed=99):
    """k=1 is an identity ON K_n, not on all of R^{n x n}: F is a multiple of
    (sum_ij b_ij), so it vanishes exactly where the affine constraint holds."""
    rng = random.Random(seed)
    ok = True
    for n in [3, 4, 5]:
        d = expand.build(n, 1)
        N = n * n
        # every monomial of F must be linear -> F = c * sum b
        cs = {c for e, c in d["F"].items() if sum(e) == 1}
        higher = [e for e in d["F"] if sum(e) != 1]
        if higher or len(cs) != 1:
            ok = False
            print(f"    n={n}: F is not c*(sum b); coeffs {cs}, "
                  f"{len(higher)} non-linear terms")
            continue
        # and it must vanish on random points of the constraint hyperplane
        for _ in range(20):
            b = [F(rng.randint(-20, 20), rng.randint(1, 11))
                 for _ in range(N - 1)]
            b.append(-sum(b))
            if expand.evaluate(d["F"], b) != 0:
                ok = False
                print(f"    n={n}: F != 0 on the hyperplane sum b = 0")
                break
    print(f"  [5] k=1 is an identity on K_n (F = c * sum b, vanishes when "
          f"sum b = 0): {ok}")
    return ok


def test_barycentre():
    ok = True
    for (n, k) in [(3, 2), (3, 3), (4, 2), (4, 3), (4, 4), (5, 3), (5, 4)]:
        d = expand.build(n, k)
        v = expand.evaluate(d["F"], [F(0)] * (n * n))
        if v != 0:
            ok = False
            print(f"    F(0) != 0 at ({n},{k}): {v}")
    print(f"  [6] equality attained at J_n/n for every tested (n,k): {ok}")
    return ok


if __name__ == "__main__":
    print("sub-Dittert validation")
    results = []
    results.append(("sigma_k two routes", test_sigma_two_routes()))
    results.append(("symbolic vs direct",
                    test_symbolic_against_direct([(3, 2), (4, 3), (4, 4),
                                                  (5, 3), (5, 4)])))
    results.append(("k=n Dittert control", test_k_equals_n_is_dittert()))
    results.append(("61/32 trap separated", test_61_32_trap()))
    results.append(("k=1 identity on K_n", test_k_one_identity()))
    results.append(("equality at J_n/n", test_barycentre()))
    print()
    for name, ok in results:
        print(f"  {'PASS' if ok else 'FAIL'}  {name}")
    sys.exit(0 if all(ok for _, ok in results) else 1)
