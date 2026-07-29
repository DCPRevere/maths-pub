"""
The GLOBAL form of the sigma_11 family, and the certificate identity in the ten
invariants.  RE-RUN THIS IF ANY ORBIT VALUE CHANGES; the Lean coefficients of
`quadForm_H` and of the identity are EMITTED here, never typed.

Part 1.  Rewrites the orbit closed form of `verify_H_pivots.py` (which is stated in
LOCAL quantities: the corner value, the two tails, the body sums) into quantities
that are GLOBAL sums over the whole matrix, corrected at the corner's own row and
column:

  sigma_p(b),  p = (a,c), with  P = b_ac,  Ra = row sum a,  Cc = column sum c,
  ECc = sum_i b_ic^2,  ERa = sum_j b_aj^2,  UCc = sum_i b_ic Ri,  VRa = sum_j b_aj Cj,
  and the constants S, T2, SR2, SC2.

That is the shape Lean can prove, because every sum runs over all of `Fin n` and the
corrections are single terms.  Checked against the assembled Gram at n = 4, 5, 6 with
a mutation control.

Part 2.  Sums that global form over p, symbolically in n, through the closed
substitution table for sum_{a,c} of each monomial (valid when S = sum b = 0, which is
what `A in K_n` gives).  Emits

    sum_p sigma_p(b)               -> E1(n) . invariants
    sum_p sigma_p(b) * b_p         -> E2(n) . invariants

Part 3.  Checks the whole certificate identity as an identity of RATIONAL FUNCTIONS
of n, coefficient by coefficient in the ten invariants T2, T3, SR2, SC2, SR3, SC3,
M1, M2, M3 (S = 0):

    objPoly(J/n + b)  ==  quadForm G0 b  +  (1/n) sum_p sigma_p(b)
                         + sum_p sigma_p(b) b_p.

No sampling anywhere in part 3: it is a full coefficient comparison.
"""
import random
import sys
from fractions import Fraction as F

import sympy as sp

sys.path.insert(0, "/home/ae/src/dcprevere/maths/problems/permanents/sub-dittert")

# ---------------------------------------------------------------- orbit values

def hs_field(n):
    """h0..h10 over any field where n is invertible (Fraction or sympy)."""
    D6 = n**11 - 7*n**10 + 19*n**9 - 25*n**8 + 16*n**7 - 4*n**6
    h = {}
    h[0] = h[1] = h[2] = 1/n**3
    h[3] = (5*n**3 + 16*n + 40)/n**6
    h[4] = (2*n**5 - 9*n**4 + 14*n**3 - 4*n**2 - 44*n + 40)/(n**8 - 3*n**7 + 2*n**6)
    h[5] = (n**3 + 8*n + 20)/n**6
    h[6] = (5*n**8 - 34*n**7 + 89*n**6 - sp.Rational(181, 2)*n**5 - 68*n**4 + 312*n**3
            - 420*n**2 + 288*n - 80)/D6
    h[7] = (2*n**8 - sp.Rational(33, 2)*n**7 + 51*n**6 - 66*n**5 - 22*n**4 + 209*n**3
            - 344*n**2 + 268*n - 80)/D6
    h[8] = (9*n**8 - 59*n**7 + 131*n**6 - 15*n**5 - 472*n**4 + 932*n**3 - 936*n**2
            + 576*n - 160)/D6
    h[9] = (6*n**8 - 42*n**7 + 98*n**6 - 13*n**5 - 352*n**4 + 678*n**3 - 620*n**2
            + 328*n - 80)/D6
    h[10] = (3*n**7 - 19*n**6 + 27*n**5 + 44*n**4 - 146*n**3 + 172*n**2 - 124*n + 40)/(
            n**10 - 5*n**9 + 9*n**8 - 7*n**7 + 2*n**6)
    return h


def hs_rat(n):
    n = F(n)
    D6 = n**11 - 7*n**10 + 19*n**9 - 25*n**8 + 16*n**7 - 4*n**6
    h = {}
    h[0] = h[1] = h[2] = F(1)/n**3
    h[3] = (5*n**3 + 16*n + 40)/n**6
    h[4] = (2*n**5 - 9*n**4 + 14*n**3 - 4*n**2 - 44*n + 40)/(n**8 - 3*n**7 + 2*n**6)
    h[5] = (n**3 + 8*n + 20)/n**6
    h[6] = (5*n**8 - 34*n**7 + 89*n**6 - F(181, 2)*n**5 - 68*n**4 + 312*n**3
            - 420*n**2 + 288*n - 80)/D6
    h[7] = (2*n**8 - F(33, 2)*n**7 + 51*n**6 - 66*n**5 - 22*n**4 + 209*n**3
            - 344*n**2 + 268*n - 80)/D6
    h[8] = (9*n**8 - 59*n**7 + 131*n**6 - 15*n**5 - 472*n**4 + 932*n**3 - 936*n**2
            + 576*n - 160)/D6
    h[9] = (6*n**8 - 42*n**7 + 98*n**6 - 13*n**5 - 352*n**4 + 678*n**3 - 620*n**2
            + 328*n - 80)/D6
    h[10] = (3*n**7 - 19*n**6 + 27*n**5 + 44*n**4 - 146*n**3 + 172*n**2 - 124*n + 40)/(
            n**10 - 5*n**9 + 9*n**8 - 7*n**7 + 2*n**6)
    return h


# ------------------------------------------------- part 1: the global local-form

def sigma_local(h, P, Ra, Cc, S, ECc, ERa, UCc, VRa, SR2, SC2, T2):
    """sigma_p written in GLOBAL quantities.  Field-agnostic."""
    aq = h[3] - h[4]
    bq = h[6] - h[7]
    cq = h[9] - h[10]
    g = h[8] - 2*h[9] + h[10]
    kappa = Cc - P
    rho = Ra - P
    tau = S - Ra - Cc + P
    Se2 = ECc - P**2
    Sf2 = ERa - P**2
    Ser = (UCc - P*Ra) - (ECc - P**2)
    Sfc = (VRa - P*Cc) - (ERa - P**2)
    Sr2 = (SR2 - 2*UCc + ECc) - (Ra - P)**2
    Sc2 = (SC2 - 2*VRa + ERa) - (Cc - P)**2
    Sb2 = T2 - ERa - ECc + P**2
    return (h[0]*P*P + 2*h[1]*P*(kappa + rho) + 2*h[2]*P*tau
            + h[4]*(kappa*kappa + rho*rho) + 2*h[5]*kappa*rho
            + 2*h[7]*(kappa + rho)*tau + h[10]*tau*tau
            + aq*(Se2 + Sf2) + 2*bq*(Ser + Sfc) + cq*(Sr2 + Sc2) + g*Sb2)


def globals_of(b, n, a, c):
    B = lambda i, j: b[i*n + j]
    R = [sum(B(i, j) for j in range(n)) for i in range(n)]
    C = [sum(B(i, j) for i in range(n)) for j in range(n)]
    return dict(
        P=B(a, c), Ra=R[a], Cc=C[c], S=sum(b),
        ECc=sum(B(i, c)**2 for i in range(n)),
        ERa=sum(B(a, j)**2 for j in range(n)),
        UCc=sum(B(i, c)*R[i] for i in range(n)),
        VRa=sum(B(a, j)*C[j] for j in range(n)),
        SR2=sum(x*x for x in R), SC2=sum(x*x for x in C),
        T2=sum(x*x for x in b))


def part1():
    import verify_general as vg
    print("PART 1  sigma_p in global quantities, against the assembled Gram\n")
    rng = random.Random(2027)
    allok = True
    for n in (4, 5, 6):
        vals19, G0, H, lam, basis = vg.certificate_at(n)
        import sos
        trans = sos.transporters(n, (0, 0))
        N = n*n
        h = hs_rat(n)
        for t in range(3):
            b = [F(rng.randint(-30, 30), rng.randint(1, 7)) for _ in range(N)]
            for (a, c) in ((0, 0), (1, 2), (n-1, n-2)):
                gp = trans[a*n + c]
                w = [b[gp[u]] for u in range(N)]
                lhs = sum(w[u]*H[u][v]*w[v] for u in range(N) for v in range(N)
                          if w[u] and w[v])
                rhs = sigma_local(h, **globals_of(b, n, a, c))
                ok = (lhs == rhs)
                allok = allok and ok
                if not ok:
                    print(f"  n={n} t={t} p=({a},{c}): MISMATCH  {lhs} vs {rhs}")
        print(f"  n={n}: all corners, all trials agree -> "
              f"{'OK' if allok else 'FAILED'}")
        # mutation control: a verifier that never rejects proves nothing
        bad = dict(globals_of(b, n, 0, 0))
        bad["UCc"] += F(1, 10**6)
        gp = trans[0]
        w = [b[gp[u]] for u in range(N)]
        lhs = sum(w[u]*H[u][v]*w[v] for u in range(N) for v in range(N)
                  if w[u] and w[v])
        print(f"  n={n} mutation control (UCc perturbed) rejected -> "
              f"{lhs != sigma_local(h, **bad)}")
    print(f"\nGLOBAL FORM OF sigma_p CONFIRMED: {allok}\n")
    return allok


# --------------------------------------------- part 2: the sum over p, symbolic

n = sp.Symbol('n')
# indexed symbols (depend on the corner) and the global constants
P, Ra, Cc, ECc, ERa, UCc, VRa = sp.symbols('P Ra Cc ECc ERa UCc VRa')
T2, T3, SR2, SC2, SR3, SC3, M1, M2, M3 = sp.symbols('T2 T3 SR2 SC2 SR3 SC3 M1 M2 M3')

INVARIANTS = (T2, T3, SR2, SC2, SR3, SC3, M1, M2, M3)

# sum over (a,c) of each monomial in the indexed symbols, when S = sum b = 0.
SUMTABLE = {
    sp.Integer(1): n**2,
    P: 0, Ra: 0, Cc: 0,
    P**2: T2, P*Ra: SR2, P*Cc: SC2,
    Ra**2: n*SR2, Cc**2: n*SC2, Ra*Cc: 0,
    ECc: n*T2, ERa: n*T2, UCc: n*SR2, VRa: n*SC2,
    P**3: T3, P**2*Ra: M2, P**2*Cc: M3,
    P*Ra**2: SR3, P*Cc**2: SC3, P*Ra*Cc: M1,
    Ra**3: n*SR3, Cc**3: n*SC3, Ra**2*Cc: 0, Ra*Cc**2: 0,
    P*ECc: M3, P*ERa: M2, P*UCc: M1, P*VRa: M1,
    Ra*ECc: 0, Ra*ERa: n*M2, Ra*UCc: 0, Ra*VRa: n*M1,
    Cc*ECc: n*M3, Cc*ERa: 0, Cc*UCc: n*M1, Cc*VRa: 0,
}
INDEXED = (P, Ra, Cc, ECc, ERa, UCc, VRa)


def sum_over_p(expr):
    """Apply the substitution table monomial by monomial.  Rejects any monomial
    outside the table rather than silently dropping it."""
    poly = sp.Poly(sp.expand(expr), *INDEXED)
    out = 0
    for mono, coeff in zip(poly.monoms(), poly.coeffs()):
        key = sp.Integer(1)
        for sym, e in zip(INDEXED, mono):
            key *= sym**e
        key = sp.expand(key)
        if key not in SUMTABLE:
            raise KeyError(f"monomial outside the substitution table: {key}")
        out += coeff * SUMTABLE[key]
    return sp.expand(out)


def part2():
    print("PART 2  sum_p sigma_p and sum_p sigma_p b_p, symbolically in n\n")
    h = hs_field(n)
    sig = sigma_local(h, P, Ra, Cc, 0, ECc, ERa, UCc, VRa, SR2, SC2, T2)
    sig = sp.expand(sp.cancel(sp.together(sig)))
    E1 = sum_over_p(sig)
    E2 = sum_over_p(sp.expand(sig*P))
    return E1, E2


# ----------------------------------------------- part 3: the certificate identity

def objpoly_in_invariants():
    """objPoly n (J/n + b) with S = 0, in the ten invariants."""
    C3 = n*(n - 1)*(n - 2)/6                       # = choose(n,3)
    tot = n                                        # sum of all entries
    sr2 = n + SR2                                  # sum_i (row sum of A)^2
    sc2 = n + SC2
    sr3 = n + 3*SR2 + SR3
    sc3 = n + 3*SC2 + SC3
    a2 = 1 + T2                                    # sum A_ij^2
    arc = n + SR2 + SC2 + M1                       # sum A_ij r_i c_j
    a2r = 1 + 2*SR2/n + T2 + M2                    # sum A_ij^2 r_i
    a2c = 1 + 2*SC2/n + T2 + M3
    a3 = 1/n + 3*T2/n + T3                         # sum A_ij^3
    e3 = (2*tot**3 - 3*tot*(sr2 + sc2) + 2*sr3 + 2*sc3)/(6*C3)
    s3 = (tot**3 - 3*tot*(sr2 + sc2) + 3*a2*tot + 6*arc + 2*sr3 + 2*sc3
          - 6*a2r - 6*a2c + 4*a3)/(6*C3**2)
    return 2 - 6/n**3 - e3 + s3


def g0_in_invariants():
    """quadForm G0 b with S = 0."""
    c0Line = ((n**8 - n**7 - 51*n**6 + 255*n**5 - 497*n**4 + 430*n**3 - 52*n**2
               - 168*n + 80)
              / (n**11 - 7*n**10 + 19*n**9 - 25*n**8 + 16*n**7 - 4*n**6))
    theta2 = ((n**4 + 40*n**2 - 84*n + 40)
              / (n**9 - 5*n**8 + 9*n**7 - 7*n**6 + 2*n**5))
    return c0Line*(SR2 + SC2) + theta2*T2


def part3(E1, E2):
    print("PART 3  the certificate identity, coefficient by coefficient in n\n")
    lhs = objpoly_in_invariants()
    rhs = g0_in_invariants() + E1/n + E2
    diff = sp.cancel(sp.together(sp.expand(lhs - rhs)))
    dpoly = sp.Poly(sp.expand(sp.numer(diff)), *INVARIANTS)
    print("  invariant           coefficient of the difference (must be 0)")
    allz = True
    for mono, coeff in zip(dpoly.monoms(), dpoly.coeffs()):
        key = sp.Integer(1)
        for sym, e in zip(INVARIANTS, mono):
            key *= sym**e
        c = sp.cancel(coeff)
        allz = allz and c == 0
        print(f"    {str(key):12s}  {sp.simplify(c)}")
    print(f"\n  denominator of the difference: {sp.factor(sp.denom(diff))}")
    print(f"\nIDENTITY HOLDS AS RATIONAL FUNCTIONS OF n: {allz and sp.cancel(diff) == 0}")
    return sp.cancel(diff) == 0


def emit(E1, E2):
    print("\nEMITTED for Lean -- coefficients of the two sums over p\n")
    for name, E in (("sumSigma", E1), ("sumSigmaB", E2)):
        poly = sp.Poly(sp.expand(E), *INVARIANTS)
        print(f"  {name}:")
        for mono, coeff in zip(poly.monoms(), poly.coeffs()):
            key = sp.Integer(1)
            for sym, e in zip(INVARIANTS, mono):
                key *= sym**e
            num, den = sp.fraction(sp.cancel(coeff))
            print(f"    {str(key):6s} : ({sp.expand(num)}) / ({sp.factor(den)})")


if __name__ == "__main__":
    ok1 = part1()
    E1, E2 = part2()
    emit(E1, E2)
    ok3 = part3(E1, E2)
    print(f"\nall checks passed: {ok1 and ok3}")
