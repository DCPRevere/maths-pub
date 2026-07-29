"""
THE BAND STRUCTURE: one k-free matrix per band, and the whole k-dependence in
2D scalars.  With the two known instances reproduced exactly, not approximately.

Everything here follows from the universal form verified in allk_universal.py:

    F_{n,k}(b) = sum_{d=1}^{k} [ t_d sigma_d(b) - s_d (e_d(R) + e_d(C)) ],
    s_d = [k]_d/[n]_d,   t_d = s_d^2 (k-d)!/n^(k-d).

PART A -- THE SUPPORT LAW.  Order the constraint rows by orbits of monomials of
degree <= D.  The right-hand side is nonzero exactly on the orbits whose
representative has distinct rows or distinct columns.  At degree d those are: the
d-cell partial permutation (one orbit, coefficient -2 s_d + t_d), and, for each
partition lambda of d with a part >= 2, the orbit "d cells in distinct rows with
column multiplicities lambda" (coefficient -s_d).  So the count at degree d is
1 + (p(d) - 1) = p(d), the PARTITION FUNCTION, and the total is sum_{d<=min(k,D)}
p(d).  Predicts 6 at (e,k) = (1,3), 3 at (1,2), 11 at (2,4), 18 at (2,5).

PART B -- THE BLOCK MULTIPLICITY BY CHARACTERS.  The Ind(V'|1) multiplicity is
the multiplicity of (V'|1) in the Gram-basis module  W_e = sum_{j=1}^{e} Sym^j M,
M = R^n (x) R^n as a module for Stab((0,0)) = (S_m x S_m) : Z_2, m = n-1.
Computed by Burnside over conjugacy-class pairs, sharing nothing with the shape
enumeration of NOTES 6b.24.  It must return 2 at e = 1 and 16 at e = 2, and the
trivial and sign multiplicities must return 3, 1 and 14, 7.

PART C -- THE DECOMPOSITION, at e = 1, over Q(n) with s_1..s_3, t_1..t_3 kept as
INDEPENDENT SYMBOLS.  Solve M X_d = U_d and M Y_d = V_d once; then for every k in
the band the certificate is x(n,k) = sum_d [ -s_d X_d(n) + t_d Y_d(n) ] + ker M,
and every block is the same combination of k-free matrices.  Hard checkpoint: the
stored k = 3 certificate of results/general_k3_certificate.txt must lie in
x(n,3) + ker M(n), exactly over Q(n).

Usage:  GUARD_MEM=8G ../guard.sh .venv/bin/python allk_band.py
"""

import os
import sys
from fractions import Fraction as Fr
from itertools import permutations

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "dittert"))
sys.path.insert(0, HERE)


# =========================================================== PART A: support law


def partitions(m, maxpart=None):
    if maxpart is None:
        maxpart = m
    if m == 0:
        yield ()
        return
    for p in range(min(m, maxpart), 0, -1):
        for rest in partitions(m - p, p):
            yield (p,) + rest


def p_of(d):
    return sum(1 for _ in partitions(d))


def support_count(k, D):
    """Predicted number of constraint rows with nonzero right-hand side."""
    return sum(p_of(d) for d in range(1, min(k, D) + 1))


def part_A():
    print("PART A.  Support of the right-hand side: the partition function.")
    print()
    print("   d   p(d)   orbits with distinct rows or distinct columns")
    for d in range(1, 8):
        lam = [l for l in partitions(d)]
        nontriv = [l for l in lam if max(l) >= 2]
        print(f"   {d}    {p_of(d):>2}     1 partial permutation"
              f" + {len(nontriv)} row-distinct shapes = {1 + len(nontriv)}")
        assert 1 + len(nontriv) == p_of(d)
    print()
    print("  predicted nonzero rhs entries:")
    for (e, k) in ((1, 2), (1, 3), (2, 4), (2, 5), (3, 6), (3, 7)):
        D = 2 * e + 1
        print(f"      e={e} D={D} k={k}:  {support_count(k, D)}")
    print()
    print("  MEASURED, by two other agents and not by this script:")
    print("      k = 4:  11   k = 5:  18   [results/k5_system_n5.log, n = 5 and 6]")
    assert support_count(4, 5) == 11 and support_count(5, 5) == 18
    print("      predicted 11 and 18.  MATCH, and the difference 18 - 11 = 7 is")
    print("      p(5): the six degree-5 column-multiplicity shapes plus the")
    print("      5-cell partial permutation, all invisible to k = 4 because")
    print("      s_5 = [4]_5/[n]_5 = 0.")
    print()
    return True


# ================================================ PART B: multiplicity by Burnside


def class_data(m):
    """(partition, class size, fixed points of g^r for r = 1..8) for S_m."""
    from math import factorial
    out = []
    for lam in partitions(m):
        # class size = m! / prod(p^{a_p} a_p!)
        cnt = {}
        for p in lam:
            cnt[p] = cnt.get(p, 0) + 1
        den = 1
        for p, a in cnt.items():
            den *= (p ** a) * factorial(a)
        size = factorial(m) // den
        fix = [sum(p for p in lam if r % p == 0) for r in range(0, 9)]
        out.append((lam, size, fix))
    return out


def h_from_p(pw, jmax):
    """Complete homogeneous h_1..h_jmax from power sums pw[1..jmax], over Q."""
    h = [Fr(1)] + [Fr(0)] * jmax
    for j in range(1, jmax + 1):
        acc = Fr(0)
        for r in range(1, j + 1):
            acc += Fr(pw[r]) * h[j - r]
        h[j] = acc / j
    return h


def mults(n, emax):
    """Multiplicities of trivial, sign and Ind(V'|1) in sum_{j=1..e} Sym^j M."""
    from math import factorial
    m = n - 1
    cls = class_data(m)
    mfact = factorial(m)

    # --- the Gamma = S_m x S_m part
    triv_G = [Fr(0)] * (emax + 1)          # <chi, (1|1)>
    ind_G = [Fr(0)] * (emax + 1)           # <chi, (V'|1)>
    for lg, sg, fg in cls:
        chi_V = Fr(fg[1] - 1)              # standard character of S_m
        for lh, sh, fh in cls:
            pw = [0] * (emax + 1)
            for r in range(1, emax + 1):
                pw[r] = (1 + fg[r]) * (1 + fh[r])       # f(x) = 1 + fix_m(x)
            hh = h_from_p(pw, emax)
            w = Fr(sg * sh, mfact * mfact)
            for j in range(1, emax + 1):
                triv_G[j] += w * hh[j]
                ind_G[j] += w * hh[j] * chi_V
    # --- the tau coset: (g,h)tau depends only on the class of w = h g
    tau = [Fr(0)] * (emax + 1)
    for lw, sw, fw in cls:
        pw = [0] * (emax + 1)
        for r in range(1, emax + 1):
            if r % 2 == 1:
                pw[r] = 1 + fw[r]
            else:
                pw[r] = (1 + fw[r // 2]) ** 2
        hh = h_from_p(pw, emax)
        w = Fr(sw, mfact)
        for j in range(1, emax + 1):
            tau[j] += w * hh[j]

    out = {}
    for e in range(1, emax + 1):
        tG = sum(triv_G[1:e + 1])
        tT = sum(tau[1:e + 1])
        out[e] = dict(trivial=(tG + tT) / 2, sign=(tG - tT) / 2,
                      ind=sum(ind_G[1:e + 1]))
    return out


def part_B():
    print("PART B.  Block multiplicities by Burnside over conjugacy-class pairs.")
    print("  Nothing here touches the shape enumeration of NOTES 6b.24 or the")
    print("  measured block sizes of 6b.15; it is an independent route to the")
    print("  same three numbers.")
    print()
    print("     n    e   trivial   sign   Ind(V'|1)")
    table = {}
    for n in (6, 7, 8, 9):
        r = mults(n, 3)
        for e in (1, 2, 3):
            v = r[e]
            for key in ("trivial", "sign", "ind"):
                assert v[key].denominator == 1, (n, e, key, v[key])
            table.setdefault(e, []).append((n, v))
            print(f"   {n:>3}    {e}    {int(v['trivial']):>5}   "
                  f"{int(v['sign']):>4}   {int(v['ind']):>7}")
    print()
    ok = True
    for e, exp in ((1, (3, 1, 2)), (2, (14, 7, 16))):
        got = {(int(v["trivial"]), int(v["sign"]), int(v["ind"]))
               for _, v in table[e]}
        agree = got == {exp}
        ok = ok and agree
        print(f"  e = {e}: expected (trivial, sign, Ind) = {exp}, got {got}"
              f"   {'MATCH' if agree else 'MISMATCH'}")
    print("        e = 1 is the k = 3 dictionary of blocks.py;")
    print("        e = 2 is the k = 4 dictionary of NOTES 6b.15.")
    e3 = {(int(v["trivial"]), int(v["sign"]), int(v["ind"]))
          for _, v in table[3]}
    print(f"  e = 3 (the band k = 6, 7), PREDICTED here first: {e3}")
    print()
    print("  The Ind(V'|1) multiplicity is the size of the binding block.  It")
    print("  GROWS with e, hence with k.  That is the exact obstruction to")
    print("  reaching k = n: Dittert needs e ~ n/2, and then the block size is")
    print("  not n-free at all.")
    print()
    return ok


# ================================================ PART C: the e = 1 decomposition


def part_C():
    import sympy as sp
    import general_k3 as g

    print("PART C.  e = 1: solve once, specialise to every k in the band.")
    print()
    nsym = sp.Symbol("n")
    sym = g.build_symbolic_system(3)
    rows, gvars, svars, lvars = (sym["rows"], sym["gvars"],
                                 sym["svars"], sym["lvars"])
    nR = len(rows)
    print(f"  rows {nR}, sigma_0 {len(gvars)}, sigma_11 {len(svars)}, "
          f"lambda {len(lvars)}, unknowns "
          f"{len(gvars) + len(svars) + len(lvars)}")

    def P(poly):
        return sum(sp.Rational(c) * nsym ** i for i, c in enumerate(poly))

    M = sp.zeros(nR, len(gvars) + len(svars) + len(lvars))
    for i in range(nR):
        for j in range(len(gvars)):
            M[i, j] = P(sym["A0"][i][j])
        for j in range(len(svars)):
            M[i, len(gvars) + j] = (P(sym["A1c"][i][j]) / nsym
                                    + P(sym["A1l"][i][j]))
        for j in range(len(lvars)):
            M[i, len(gvars) + len(svars) + j] = P(sym["A2"][i][j])
    M = sp.simplify(M)

    # --- the k-free right-hand-side generators
    U = {d: sp.zeros(nR, 1) for d in range(1, 4)}
    V = {d: sp.zeros(nR, 1) for d in range(1, 4)}
    for i, r in enumerate(rows):
        d = len(r)
        if d == 0:
            continue
        size = P(g.orbit_size_poly(r, False))
        dr = len({a for a, _ in r}) == d
        dc = len({b for _, b in r}) == d
        U[d][i] = size * ((1 if dr else 0) + (1 if dc else 0))
        V[d][i] = size * (1 if (dr and dc) else 0)
    nz = sum(1 for i in range(nR)
             if any(U[d][i] != 0 for d in (1, 2, 3)))
    print(f"  rows with nonzero rhs generator: {nz}   (PART A predicted "
          f"{support_count(3, 3)})")
    assert nz == support_count(3, 3)

    # --- the left null vector, and consistency of every generator separately
    NS = M.T.nullspace()
    print(f"  left null space of M over Q(n): dimension {len(NS)}")
    for y in NS:
        y = sp.simplify(y)
        for d in (1, 2, 3):
            assert sp.simplify((y.T * U[d])[0, 0]) == 0
            assert sp.simplify((y.T * V[d])[0, 0]) == 0
    print("  every U_d and V_d is orthogonal to it, so the system is CONSISTENT")
    print("  for EVERY k at once -- no case analysis in k.  [P]")

    # --- solve once per generator
    X, Y = {}, {}
    for d in (1, 2, 3):
        X[d] = _solve(sp, M, U[d])
        Y[d] = _solve(sp, M, V[d])
    print("  solved M X_d = U_d and M Y_d = V_d over Q(n) for d = 1, 2, 3.")

    ss = sp.symbols("s1 s2 s3")
    tt = sp.symbols("t1 t2 t3")
    x_sym = sp.zeros(M.shape[1], 1)
    rhs_sym = sp.zeros(nR, 1)
    for i, d in enumerate((1, 2, 3)):
        x_sym += -ss[i] * X[d] + tt[i] * Y[d]
        rhs_sym += -ss[i] * U[d] + tt[i] * V[d]
    x_sym = sp.simplify(x_sym)
    resid = sp.expand(M * x_sym - rhs_sym)
    ok_sym = all(sp.simplify(resid[i]) == 0 for i in range(nR))
    print(f"  M x(n; s, t) = rhs(n; s, t) identically in six free symbols: "
          f"{ok_sym}")

    # --- specialise and compare with the trusted right-hand side
    from math import factorial
    def sval(n, k, d):
        num = den = Fr(1)
        for i in range(d):
            num *= (k - i)
            den *= (n - i)
        return Fr(num, 1) / Fr(den, 1)

    bad = 0
    for k in (2, 3):
        for n0 in (4, 5, 6, 7, 9, 12):
            subs = {}
            for i, d in enumerate((1, 2, 3)):
                sd = sval(n0, k, d)
                subs[ss[i]] = sp.Rational(sd.numerator, sd.denominator)
                td = sd * sd * Fr(factorial(k - d), n0 ** (k - d)) if d <= k \
                    else Fr(0)
                subs[tt[i]] = sp.Rational(td.numerator, td.denominator)
            got = [sp.simplify((M * x_sym).subs(subs).subs(nsym, n0)[i])
                   for i in range(nR)]
            if k == 3:
                want = sym["rhs_at"](n0)
                for i in range(nR):
                    if sp.Rational(want[i].numerator, want[i].denominator) \
                            != sp.nsimplify(got[i]):
                        bad += 1
            print(f"      k={k} n={n0}: specialised rhs assembled"
                  + ("  vs trusted rhs_at: MATCH" if k == 3 and bad == 0
                     else ("  vs trusted rhs_at: MISMATCH" if k == 3 else "")))
    print(f"  total mismatches against general_k3.rhs_at: {bad}")

    # --- HARD CHECKPOINT: the stored k = 3 certificate lies in x(n,3) + ker M
    stored = _read_stored(sp, nsym)
    if stored is None:
        print("  stored certificate not found -- HARD CHECKPOINT NOT RUN")
        return False
    subs3 = {}
    for i, d in enumerate((1, 2, 3)):
        sd = sp.Rational(int(_ff(3, d)), 1) / _ffsym(sp, nsym, d)
        subs3[ss[i]] = sd
        subs3[tt[i]] = sd * sd * sp.Rational(factorial(3 - d), 1) / nsym ** (3 - d)
    x3 = sp.simplify(x_sym.subs(subs3))
    diff = sp.simplify(stored - x3)
    resid2 = sp.simplify(M * diff)
    inker = all(sp.simplify(resid2[i]) == 0 for i in range(nR))
    print()
    print("  HARD CHECKPOINT.  results/general_k3_certificate.txt minus the")
    print(f"  decomposition's particular solution lies in ker M(n): {inker}")
    if inker:
        print("  so the stored 19-rational k = 3 certificate is EXACTLY a member")
        print("  of the family  x(n,k) = sum_d [-s_d X_d(n) + t_d Y_d(n)] + ker M,")
        print("  reproduced, not merely resembled.")
    return ok_sym and bad == 0 and inker


def _ff(x, d):
    out = 1
    for i in range(d):
        out *= (x - i)
    return out


def _ffsym(sp, nsym, d):
    out = sp.Integer(1)
    for i in range(d):
        out *= (nsym - i)
    return out


def _solve(sp, M, rhs):
    """One particular solution of M x = rhs over Q(n), free variables zero."""
    aug = M.row_join(rhs)
    rref, piv = aug.rref(simplify=True)
    x = sp.zeros(M.shape[1], 1)
    for i, j in enumerate(piv):
        if j == M.shape[1]:
            raise RuntimeError("inconsistent system")
        x[j] = sp.simplify(rref[i, M.shape[1]])
    return x


def _read_stored(sp, nsym):
    path = os.path.join(HERE, "results", "general_k3_certificate.txt")
    if not os.path.exists(path):
        return None
    vals = []
    with open(path) as fh:
        for line in fh:
            if "=" not in line or "[" not in line:
                continue
            rhs = line.split("=", 1)[1].strip()
            num, den = rhs.split(") / (")
            num = num.lstrip("(")
            den = den.rstrip(")\n").rstrip(")")
            vals.append(sp.sympify(num.replace("^", "**"))
                        / sp.sympify(den.replace("^", "**")))
    if len(vals) != 19:
        return None
    return sp.Matrix(19, 1, vals)


from math import factorial                                        # noqa: E402


def main():
    print("allk_band.py -- one k-free matrix per band; the k-dependence is 2D "
          "scalars")
    print()
    a = part_A()
    b = part_B()
    c = part_C()
    print()
    print(f"SUMMARY   support law {a}   multiplicities {b}   e=1 decomposition {c}")


if __name__ == "__main__":
    main()
