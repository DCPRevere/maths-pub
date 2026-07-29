"""Cross-check the Lean `objPoly` formula against the 1992 definition."""
import sys, os, random, itertools
from fractions import Fraction as F
from math import comb
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                os.pardir, "sub-dittert"))
import verify_general as vg          # the independent exact verifier

def objPoly(A, n):
    """Exactly the Lean definition of SubDittertK3.objPoly."""
    C = F(comb(n, 3))
    T  = sum(A[i][j] for i in range(n) for j in range(n))
    r  = [sum(A[i]) for i in range(n)]
    c  = [sum(A[i][j] for i in range(n)) for j in range(n)]
    Qr = sum(x**2 for x in r); Qc = sum(x**2 for x in c)
    Kr = sum(x**3 for x in r); Kc = sum(x**3 for x in c)
    p2 = sum(A[i][j]**2 for i in range(n) for j in range(n))
    p3 = sum(A[i][j]**3 for i in range(n) for j in range(n))
    er = sum(A[i][j]**2 * r[i] for i in range(n) for j in range(n))
    ec = sum(A[i][j]**2 * c[j] for i in range(n) for j in range(n))
    et = sum(A[i][j] * r[i] * c[j] for i in range(n) for j in range(n))
    return (F(2) - F(6, n**3)
            - (2*T**3 - 3*T*(Qr+Qc) + 2*Kr + 2*Kc) / (6*C)
            + (T**3 - 3*T*(Qr+Qc) + 3*p2*T + 6*et + 2*Kr + 2*Kc
               - 6*er - 6*ec + 4*p3) / (6*C**2))

rng = random.Random(2026)
allok = True
for n in (4, 5, 6, 7):
    for trial in range(3):
        # random b, exactly as verify_general does, then A = J/n + b
        b = [F(rng.randint(-40, 40), rng.randint(1, 9) * n) for _ in range(n*n)]
        A = [[F(1, n) + b[i*n + j] for j in range(n)] for i in range(n)]
        lhs = objPoly(A, n)
        rhs, M = vg.objective_F(b, n)          # M - (E3(r)+E3(c)-P3), from the definition
        ok = (lhs == rhs)
        allok = allok and ok
        print(f"  n={n} trial={trial}: objPoly == (2-6/n^3) - Phi_3  ->  {ok}")
    # and at the conjectured maximiser J/n, where the value must be exactly 0
    Ju = [[F(1, n)] * n for _ in range(n)]
    z = objPoly(Ju, n)
    print(f"  n={n}: objPoly(J/n) = {z}  (must be 0)  -> {z == 0}")
    allok = allok and z == 0
# a mutation control: a verifier that never rejects proves nothing
bad = [[F(1, 4)] * 4 for _ in range(4)]
bad[0][0] += F(1, 1000)
print(f"\n  mutation control at n=4: objPoly(J/4 + e_00/1000) = {objPoly(bad,4)} (must be != 0)"
      f" -> {objPoly(bad,4) != 0}")
print(f"\nALL OK: {allok}")
