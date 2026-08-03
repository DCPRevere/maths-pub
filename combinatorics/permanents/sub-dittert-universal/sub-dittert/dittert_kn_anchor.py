"""
The anchor run at the TERMINAL cells `k = n`: (k = 4, n = 4) and (k = 5, n = 5).

WHAT IS NEW HERE, and it is only bookkeeping.  `diag_anchor.py` already runs the
trusted route -- `results/verify_subdittert.py` loaded by path and unmodified,
plus `anchor_check3`'s checks [1] [2] [3] [5] [6] and the (A1)/(A2) conjugacy.
Three of `anchor_check3`'s TYPED-IN expectation tables simply have no entry at
`k = n`, because no `k = n` cell had ever been run.  They are supplied here, by
hand, from closed forms -- never from the pipeline, which is the whole point of
their existing.

  EXPECT_B[4] = 152
      the count of degree-1 and degree-2 monomials in n^2 = 16 variables:
      16 + C(17,2) = 16 + 136 = 152.  (Generally n^2(n^2+3)/2, which gives the
      stored 350, 702, 1274, 2144, 3402 at n = 5..9 -- five hits.)

  EXPECT_BOUND[4] = 61/32
      2 - 4!/4^4 = 2 - 24/256 = 2 - 3/32.

  EXPECT_F_MONOMIALS[(4,4)] = 1040,  [(5,5)] = 14005
      the support of F(b) = (2 - k!/n^k) - [E_k(r) + E_k(c) - P_k(A)] is the
      union of R (<= 1 variable per ROW, <= k of them), C (its transpose) and
      P (<= 1 per row AND per column -- sigma_k's partial permutations), and
      R n C = P exactly, so

          |supp F| = 2 * sum_{t<=k} C(n,t) n^t
                     -   sum_{t<=k} C(n,t)^2 t!   -   1

      the -1 being the constant, which cancels because F(0) = 0.  This closed
      form reproduces the stored anchor numbers 7875 at (5,4) and 809529 at
      (5,7), neither of which it was fitted to.

  EXPECT_LAM_COEFFS[4] = 4845
      monomials of degree <= TOPDEG - 1 = 4 in 16 variables: C(20,4).  This one
      is a NOTE inside `anchor_check3`, not an abort.

THE BOUND CHECK IS DEGENERATE AT BOTH TERMINAL CELLS, and this file says so
rather than letting a pass look stronger than it is:

    n = 4:  2 - 4!/4^4  =  61/32     =  2 - 3!/4^3
    n = 5:  2 - 5!/5^5  =  1226/625  =  2 - 4!/5^4

so check [2] cannot distinguish `k = n` from `k = n - 1` at either cell.  (The
n = 5 collision is the one `diag_anchor.py` records as "a THIRD collision";
n = 4 is a fourth, and NOTES §6 already records two more.)  The k-DISCRIMINATING
evidence is check [3]'s monomial count, which separates cleanly:

    n = 4:   k = 3 -> 552      k = 4 -> 1040
    n = 5:   k = 4 -> 7875     k = 5 -> 14005

ORDER MATTERS.  `anchor_check3.control` -- the streamed-vs-dense engine control
-- is a `k = 4, n = 5` object and reads `EXPECT_F_MONOMIALS[5] = 7875`.  So the
n = 5 override must not be installed until after the control has run.  It is
installed by wrapping `ac.run`, which fires only inside the job loop.
"""

import sys

import anchor_check3 as ac
import diag_anchor as da
import h2_anchor6 as ha6

# ------------------------------------------------- typed in, by hand, from above
ac.EXPECT_B[4] = 152
ac.EXPECT_BOUND[4] = "61/32"
ac.EXPECT_LAM_COEFFS[4] = 4845
# The (3,3) row, added 2026-08-03 by the same three closed forms and by hand:
#   B            = n^2(n^2+3)/2 = 9*12/2 = 54
#   bound        = 2 - 3!/3^3 = 2 - 6/27 = 16/9
#   lam coeffs   = monomials of degree <= TOPDEG - 1 = 4 in n^2 = 9 variables
#                = C(13,4) = 715   (C(29,4) = 23751 at n = 5 and C(20,4) = 4845
#                  at n = 4 are the same formula, and both are stored already)
#   F monomials  = 2*64 - 34 - 1 = 93, from |R| = sum_{t<=3} C(3,t) 3^t = 64 and
#                  |P| = sum_{t<=3} C(3,t)^2 t! = 34
# Check [2] is degenerate here too, and worse than at n = 4, 5: 16/9 is also
# 2 - 2!/3^2, so it cannot even tell k = 3 from k = 2.  The k-evidence is again
# check [3]: 93 monomials against 45 at (3,2).
ac.EXPECT_B[3] = 54
ac.EXPECT_BOUND[3] = "16/9"
ac.EXPECT_LAM_COEFFS[3] = 715
F_MON_KN = {(3, 3): 93, (4, 4): 1040, (5, 5): 14005}
da.BOUND_K5[4] = "61/32"          # unused at k = 5, present so a typo cannot pass

_REAL_RUN = ac.run


def run(n, vs, **kw):
    """`anchor_check3.run`, with the k = n monomial expectation swapped in."""
    key = (n, ac.K)
    if key not in F_MON_KN:
        return _REAL_RUN(n, vs, **kw)
    old = dict(ac.EXPECT_F_MONOMIALS)
    oldK6 = ha6.K
    ac.EXPECT_F_MONOMIALS[n] = F_MON_KN[key]
    # The (A1)/(A2) conjugacy check rebuilds the system through
    # `h2_anchor6.K`, a module constant left at its k = 4 value (line 51).  At
    # n = 4, 5 that is harmless -- `k` enters only `rhs`, which the conjugacy
    # check never reads (NOTES §24, §K5.4).  At n = 3 it is NOT harmless:
    # `comb(3, 4) = 0` and `E_k` divides by it, so the check dies with a
    # ZeroDivisionError before it can say anything.  Point it at the cell's own
    # k.  This changes no verdict at n = 4, 5, where it already held that value.
    ha6.K = ac.K
    kw.get("out", print)(
        f"  [k = n cell] check [3] expectation set to "
        f"{F_MON_KN[key]} monomials, typed in from the closed form; note that "
        f"check [2] is DEGENERATE at n = {n} (2 - {ac.K}!/{n}^{ac.K} equals "
        f"2 - {ac.K - 1}!/{n}^{ac.K - 1}) and carries no k-information here")
    try:
        return _REAL_RUN(n, vs, **kw)
    finally:
        ac.EXPECT_F_MONOMIALS.clear()
        ac.EXPECT_F_MONOMIALS.update(old)
        ha6.K = oldK6


ac.run = run

if __name__ == "__main__":
    sys.exit(da.main(sys.argv[1:]))
