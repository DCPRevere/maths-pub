/-
# Theorem E's endgame, and `theta < 1` on all of `R_new` — stones 10 and 20

Two things live here.

**Stone 10 (`ThetaStrict`).**  `LEAN-ROADMAP.md` A9 records the correction edge: `(C3)` is
`theta <= 1`, NOT `theta < 1`, and strictness is a separate fact that must be proved
separately.  `Theta.theta_le_one_iff_C3` keeps the two apart; this file supplies the strict
half at every cell of `R_new`, in two pieces — `LemmaT.thetaT` gives `theta <= 144/955` on the
tail `n >= 10`, and the 17 surviving cells of `4 <= n <= 9` are spelled out one lemma each.

**Stone 20's endgame (the `theta` algebra).**  `LIFT.md` §B.13.2 displays Theorem E as

```
    D(A) <  gamma :   Phi_k(A) <= 2 - gamma - (1 - theta(n,k)) D(A)
    D(A) >= gamma :   Phi_k(A) <= 2 - D(A)
```

and the whole equality half of Cheon-Hwang on `R_new` is the observation that the near branch's
deficit `(1 - theta) D` is STRICTLY positive off `D = 0`.  §2 below is that step, over any
linear ordered field, taking the chain's own output as a hypothesis: what the chain produces is
`Phi <= 2 - D - gamma(1 - theta D/gamma)`, and `Theta.deficit_algebra` turns it into the
displayed form identically in `D`.

## What is hypothesised, and why

The chain bound itself — steps (S1)-(S4) of `LIFT.md` §B.13.1 — is NOT proved here.  It needs
stones 7, 8, 15, 17, 18 and 19, of which only 15's `H'` half and the `chi` estimates are built.
So `theoremE_endgame` takes it as an explicit argument, in the `SubDittertM.MaclaurinBound`
shape used throughout this tree.  What is unconditional here is everything downstream of it:
the algebra, the strictness, and `theta < 1` at every cell.
-/

import Mathlib.Tactic
import Theta
import LemmaT

namespace TheoremE

open Theta

/-! ## §1  Stone 10 — `theta < 1` at every cell of `R_new` -/

theorem theta_lt_one_three_six : theta 6 3 < 1 := by
  norm_num [theta, thetaNum, thetaDen, kappa, gamma, Nat.factorial]

theorem theta_lt_one_four_six : theta 6 4 < 1 := by
  norm_num [theta, thetaNum, thetaDen, kappa, gamma, Nat.factorial]

theorem theta_lt_one_three_seven : theta 7 3 < 1 := by
  norm_num [theta, thetaNum, thetaDen, kappa, gamma, Nat.factorial]

theorem theta_lt_one_four_seven : theta 7 4 < 1 := by
  norm_num [theta, thetaNum, thetaDen, kappa, gamma, Nat.factorial]

theorem theta_lt_one_five_seven : theta 7 5 < 1 := by
  norm_num [theta, thetaNum, thetaDen, kappa, gamma, Nat.factorial]

theorem theta_lt_one_six_seven : theta 7 6 < 1 := by
  norm_num [theta, thetaNum, thetaDen, kappa, gamma, Nat.factorial]

theorem theta_lt_one_three_eight : theta 8 3 < 1 := by
  norm_num [theta, thetaNum, thetaDen, kappa, gamma, Nat.factorial]

theorem theta_lt_one_four_eight : theta 8 4 < 1 := by
  norm_num [theta, thetaNum, thetaDen, kappa, gamma, Nat.factorial]

theorem theta_lt_one_five_eight : theta 8 5 < 1 := by
  norm_num [theta, thetaNum, thetaDen, kappa, gamma, Nat.factorial]

theorem theta_lt_one_six_eight : theta 8 6 < 1 := by
  norm_num [theta, thetaNum, thetaDen, kappa, gamma, Nat.factorial]

theorem theta_lt_one_seven_eight : theta 8 7 < 1 := by
  norm_num [theta, thetaNum, thetaDen, kappa, gamma, Nat.factorial]

theorem theta_lt_one_three_nine : theta 9 3 < 1 := by
  norm_num [theta, thetaNum, thetaDen, kappa, gamma, Nat.factorial]

theorem theta_lt_one_four_nine : theta 9 4 < 1 := by
  norm_num [theta, thetaNum, thetaDen, kappa, gamma, Nat.factorial]

theorem theta_lt_one_five_nine : theta 9 5 < 1 := by
  norm_num [theta, thetaNum, thetaDen, kappa, gamma, Nat.factorial]

theorem theta_lt_one_six_nine : theta 9 6 < 1 := by
  norm_num [theta, thetaNum, thetaDen, kappa, gamma, Nat.factorial]

theorem theta_lt_one_seven_nine : theta 9 7 < 1 := by
  norm_num [theta, thetaNum, thetaDen, kappa, gamma, Nat.factorial]

theorem theta_lt_one_eight_nine : theta 9 8 < 1 := by
  norm_num [theta, thetaNum, thetaDen, kappa, gamma, Nat.factorial]

/-- **STONE 10.**  `theta(n,k) < 1` at every cell of `R_new`: the tail by `LemmaT.thetaT`, the
17 surviving cells of `4 ≤ n ≤ 9` one at a time.  Stated and proved SEPARATELY from `(C3)`'s
`theta ≤ 1` — see `Theta.theta_le_one_iff_C3`. -/
theorem theta_lt_one {n k : ℕ} (h3 : 3 ≤ k) (hkn : k < n)
    (e1 : ¬(n = 4 ∧ k = 3)) (e2 : ¬(n = 5 ∧ k = 3)) (e3 : ¬(n = 5 ∧ k = 4))
    (e4 : ¬(n = 6 ∧ k = 5)) : theta n k < 1 := by
  rcases le_or_lt 10 n with hn | hn
  · have := LemmaT.thetaT hn h3 hkn
    linarith
  · interval_cases n <;> interval_cases k <;>
      simp_all <;>
      first
        | exact theta_lt_one_three_six
        | exact theta_lt_one_four_six
        | exact theta_lt_one_three_seven
        | exact theta_lt_one_four_seven
        | exact theta_lt_one_five_seven
        | exact theta_lt_one_six_seven
        | exact theta_lt_one_three_eight
        | exact theta_lt_one_four_eight
        | exact theta_lt_one_five_eight
        | exact theta_lt_one_six_eight
        | exact theta_lt_one_seven_eight
        | exact theta_lt_one_three_nine
        | exact theta_lt_one_four_nine
        | exact theta_lt_one_five_nine
        | exact theta_lt_one_six_nine
        | exact theta_lt_one_seven_nine
        | exact theta_lt_one_eight_nine

/-! ## §2  The endgame algebra

Over any linear ordered field, so it serves the `ℚ` bookkeeping and the `ℝ` statement of
`Phi_k` alike. -/

variable {K : Type*} [LinearOrderedField K]

/-- **The near branch, rearranged** (`graded_verify_strict.py` block [3]).  What the chain
produces is the left form; what Theorem E displays is the right one, and they are equal
identically in `D`. -/
theorem near_branch {Phi D g th : K} (hg : g ≠ 0)
    (hchain : Phi ≤ 2 - D - g * (1 - th * D / g)) :
    Phi ≤ 2 - g - (1 - th) * D := by
  rwa [deficit_algebra g th D hg] at hchain

/-- **The strictness clause.**  Off `D = 0` the near branch is strictly below `2 - gamma`. -/
theorem near_branch_strict {Phi D g th : K} (hth : th < 1) (hD : 0 < D)
    (h : Phi ≤ 2 - g - (1 - th) * D) : Phi < 2 - g := by
  have : 0 < (1 - th) * D := mul_pos (by linarith) hD
  linarith

/-- **The equality half.**  `Phi = 2 - gamma` forces the line-sum deficit to vanish.  This is
the step `LIFT.md` §B.13.2 ends on, and the reason `theta < 1` (stone 10, §1) is load-bearing
rather than cosmetic. -/
theorem D_eq_zero_of_eq {Phi D g th : K} (hth : th < 1) (hD : 0 ≤ D)
    (h : Phi ≤ 2 - g - (1 - th) * D) (heq : Phi = 2 - g) : D = 0 := by
  rcases eq_or_lt_of_le hD with h0 | h0
  · exact h0.symm
  · exact absurd heq (near_branch_strict hth h0 h).ne

/-- **Theorem E's endgame, assembled.**  On any cell of `R_new`, a chain bound of the shape
(S1)-(S4) produce forces `D = 0` at equality.  `theta < 1` comes from §1, so the only
hypothesis left is the chain bound itself. -/
theorem theoremE_endgame {n k : ℕ} (h3 : 3 ≤ k) (hkn : k < n)
    (e1 : ¬(n = 4 ∧ k = 3)) (e2 : ¬(n = 5 ∧ k = 3)) (e3 : ¬(n = 5 ∧ k = 4))
    (e4 : ¬(n = 6 ∧ k = 5)) {Phi D : ℚ} (hD : 0 ≤ D) (hg : gamma n k ≠ 0)
    (hchain : Phi ≤ 2 - D - gamma n k * (1 - theta n k * D / gamma n k))
    (heq : Phi = 2 - gamma n k) : D = 0 :=
  D_eq_zero_of_eq (theta_lt_one h3 hkn e1 e2 e3 e4) hD (near_branch hg hchain) heq

section AxiomAudit

#print axioms theta_lt_one_three_six
#print axioms theta_lt_one_four_six
#print axioms theta_lt_one_three_seven
#print axioms theta_lt_one_four_seven
#print axioms theta_lt_one_five_seven
#print axioms theta_lt_one_six_seven
#print axioms theta_lt_one_three_eight
#print axioms theta_lt_one_four_eight
#print axioms theta_lt_one_five_eight
#print axioms theta_lt_one_six_eight
#print axioms theta_lt_one_seven_eight
#print axioms theta_lt_one_three_nine
#print axioms theta_lt_one_four_nine
#print axioms theta_lt_one_five_nine
#print axioms theta_lt_one_six_nine
#print axioms theta_lt_one_seven_nine
#print axioms theta_lt_one_eight_nine
#print axioms theta_lt_one
#print axioms near_branch
#print axioms near_branch_strict
#print axioms D_eq_zero_of_eq
#print axioms theoremE_endgame

end AxiomAudit

end TheoremE
