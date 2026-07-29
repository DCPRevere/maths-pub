"""
The CENTRED DECOMPOSITION of sigma_11, exactly, and its bridge to the seven pivot
theorems of SubDittertK3.lean.  RE-RUN IF ANY ORBIT VALUE CHANGES.

Claim under test (m = n-1, corner p = (a,c)):

  sigma_p(b) = QA(P, s, tau) + Bb d^2
               + sum_{i != a} QC(ehat_i, rhat_i) + sum_{j != c} QC(fhat_j, chat_j)
               + g sum w^2

with s = kappa+rho, d = kappa-rho,
  QA(x,y,z) = A11 x^2 + 2 A12 x y + 2 A13 x z + A22 y^2 + 2 A23 y z + A33 z^2,
  QC(x,y)   = aq x^2 + 2 bq x y + q22 y^2,
  ehat_i = e_i - kappa/m, rhat_i = r_i - tau/m, w_ij = B_ij - r_i/m - c_j/m + tau/m^2.

Checked exactly over Q at n = 4, 5, 6 against `sigma_local` (itself checked against
the assembled Gram in verify_H_identity.py), with a mutation control.

FINDING RECORDED HERE.  The seven `pivot*` of SubDittertK3.lean are NOT the leading
principal minors of these blocks; they are those minors times the POSITIVE CONSTANTS

    pivotA1 : 1   pivotA2 : 2   pivotA3 : 4   pivotB : 2
    pivotC1 : 1   pivotC2 : 4   pivotD  : 1

(constant in n, verified below as an identity of rational functions).  Positivity is
therefore equivalent, which is all the Lean proof needs -- but the minors themselves
must be introduced with these constants or the bridge lemmas are false.
"""
import random
import sys
from fractions import Fraction as F

import sympy as sp

sys.path.insert(0, "/home/ae/src/dcprevere/maths/problems/permanents/leanproj")
from verify_H_identity import hs_rat, sigma_local, globals_of      # noqa: E402


def blocks_rat(n):
    n = F(n)
    m = n - 1
    h = hs_rat(n)
    aq = h[3] - h[4]
    bq = h[6] - h[7]
    cq = h[9] - h[10]
    g = h[8] - 2*h[9] + h[10]
    return dict(A11=h[0], A12=h[1], A13=h[2],
                A22=(h[4] + h[5])/2 + aq/(2*m),
                A23=h[7] + bq/m,
                A33=h[10] + 2*cq/m + g/m**2,
                Bb=(h[4] - h[5])/2 + aq/(2*m),
                aq=aq, bq=bq, q22=cq + g/m, g=g)


def decomposition(b, n, a, c):
    B = lambda i, j: b[i*n + j]
    m = F(n - 1)
    bl = blocks_rat(n)
    rows = [i for i in range(n) if i != a]
    cols = [j for j in range(n) if j != c]
    P = B(a, c)
    e = {i: B(i, c) for i in rows}
    f = {j: B(a, j) for j in cols}
    r = {i: sum(B(i, j) for j in cols) for i in rows}
    cl = {j: sum(B(i, j) for i in rows) for j in cols}
    kappa = sum(e.values())
    rho = sum(f.values())
    tau = sum(r.values())
    s, d = kappa + rho, kappa - rho
    QA = (bl["A11"]*P*P + 2*bl["A12"]*P*s + 2*bl["A13"]*P*tau
          + bl["A22"]*s*s + 2*bl["A23"]*s*tau + bl["A33"]*tau*tau)
    QC = lambda x, y: bl["aq"]*x*x + 2*bl["bq"]*x*y + bl["q22"]*y*y
    tot = QA + bl["Bb"]*d*d
    tot += sum(QC(e[i] - kappa/m, r[i] - tau/m) for i in rows)
    tot += sum(QC(f[j] - rho/m, cl[j] - tau/m) for j in cols)
    tot += bl["g"]*sum((B(i, j) - r[i]/m - cl[j]/m + tau/m**2)**2
                       for i in rows for j in cols)
    return tot


def part1():
    print("PART 1  the centred decomposition, exactly over Q\n")
    rng = random.Random(4099)
    allok = True
    for n in (4, 5, 6):
        h = hs_rat(n)
        for t in range(4):
            b = [F(rng.randint(-30, 30), rng.randint(1, 7)) for _ in range(n*n)]
            for (a, c) in ((0, 0), (1, 2), (n-1, n-2)):
                lhs = sigma_local(h, **globals_of(b, n, a, c))
                rhs = decomposition(b, n, a, c)
                ok = (lhs == rhs)
                allok = allok and ok
                if not ok:
                    print(f"  n={n} t={t} p=({a},{c}): MISMATCH, "
                          f"difference {lhs - rhs}")
        print(f"  n={n}: decomposition reproduces sigma_p at every corner -> "
              f"{'OK' if allok else 'FAILED'}")
    # mutation control
    b = [F(rng.randint(-30, 30), rng.randint(1, 7)) for _ in range(16)]
    good = decomposition(b, 4, 0, 0)
    print(f"  mutation control: perturbed form differs -> "
          f"{good + F(1, 10**6) != sigma_local(hs_rat(4), **globals_of(b, 4, 0, 0))}")
    print(f"\nCENTRED DECOMPOSITION CONFIRMED: {allok}\n")
    return allok


# ------------------------------------------- part 2: the bridge, symbolically in n

n = sp.Symbol('n')


def blocks_sym():
    from verify_H_identity import hs_field
    m = n - 1
    h = hs_field(n)
    aq = sp.cancel(h[3] - h[4])
    bq = sp.cancel(h[6] - h[7])
    cq = sp.cancel(h[9] - h[10])
    g = sp.cancel(h[8] - 2*h[9] + h[10])
    return dict(A11=h[0], A12=h[1], A13=h[2],
                A22=sp.cancel((h[4] + h[5])/2 + aq/(2*m)),
                A23=sp.cancel(h[7] + bq/m),
                A33=sp.cancel(h[10] + 2*cq/m + g/m**2),
                Bb=sp.cancel((h[4] - h[5])/2 + aq/(2*m)),
                aq=aq, bq=bq, q22=sp.cancel(cq + g/m), g=g)


PIVOT = {
 "pivotA1": sp.Integer(1)/n**3,
 "pivotA2": (n**5 - 2*n**4 + 16*n**3 + 16*n**2 - 52*n + 20)/(n**11 - 2*n**10 + n**9),
 "pivotA3": ((31*n**13 - 279*n**12 + 503*n**11 + 4281*n**10 - 27723*n**9 + 64281*n**8
              - 30296*n**7 - 172276*n**6 + 423952*n**5 - 428368*n**4 + 161856*n**3
              + 59072*n**2 - 74240*n + 19200)
             / (n**24 - 15*n**23 + 101*n**22 - 403*n**21 + 1059*n**20 - 1925*n**19
                + 2471*n**18 - 2241*n**17 + 1408*n**16 - 584*n**15 + 144*n**14
                - 16*n**13)),
 "pivotB": (n**5 - 2*n**4 + 8*n**2 + 12*n - 20)/(n**8 - 2*n**7 + n**6),
 "pivotC1": (3*n**5 - 6*n**4 + 12*n**3 - 4*n**2 - 44*n + 40)/(n**8 - 3*n**7 + 2*n**6),
 "pivotC2": ((95*n**12 - 743*n**11 + 1535*n**10 + 2451*n**9 - 17746*n**8 + 33092*n**7
              - 10820*n**6 - 60308*n**5 + 107640*n**4 - 58736*n**3 - 24608*n**2
              + 40960*n - 12800)
             / (n**20 - 11*n**19 + 52*n**18 - 138*n**17 + 225*n**16 - 231*n**15
                + 146*n**14 - 52*n**13 + 8*n**12)),
 "pivotD": (n**4 + 40*n**2 - 84*n + 40)/(n**10 - 5*n**9 + 9*n**8 - 7*n**7 + 2*n**6),
}


def part2():
    print("PART 2  the seven bridges, as identities of rational functions of n\n")
    B = blocks_sym()
    det3 = (B["A11"]*(B["A22"]*B["A33"] - B["A23"]**2)
            - B["A12"]*(B["A12"]*B["A33"] - B["A23"]*B["A13"])
            + B["A13"]*(B["A12"]*B["A23"] - B["A22"]*B["A13"]))
    minors = {
     "pivotA1": (1, B["A11"]),
     "pivotA2": (2, B["A11"]*B["A22"] - B["A12"]**2),
     "pivotA3": (4, det3),
     "pivotB": (2, B["Bb"]),
     "pivotC1": (1, B["aq"]),
     "pivotC2": (4, B["aq"]*B["q22"] - B["bq"]**2),
     "pivotD": (1, B["g"]),
    }
    allok = True
    for k, (const, minor) in minors.items():
        d = sp.cancel(sp.together(PIVOT[k] - const*minor))
        ok = (d == 0)
        allok = allok and ok
        print(f"  {k:8s} = {const} * (block minor)      {ok}")
        if not ok:
            print(f"      difference {sp.simplify(d)}")
    bad = sp.cancel(sp.together(PIVOT["pivotA3"] - 5*minors["pivotA3"][1]))
    print(f"  mutation control (constant 5 for pivotA3) rejected     {bad != 0}")
    print(f"\nALL SEVEN BRIDGES HOLD WITH THESE CONSTANTS: {allok}\n")

    print("EMITTED for Lean -- block entries as (numerator) / (denominator)\n")
    for name in ("A11", "A12", "A13", "A22", "A23", "A33", "Bb", "aq", "bq",
                 "q22", "g"):
        num, den = sp.fraction(sp.cancel(B[name]))
        print(f"  {name:4s} : ({sp.expand(num)})")
        print(f"       / ({sp.expand(den)})")
    return allok


if __name__ == "__main__":
    ok1 = part1()
    ok2 = part2()
    print(f"all checks passed: {ok1 and ok2}")
