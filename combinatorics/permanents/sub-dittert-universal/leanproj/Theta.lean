/-
# `θ`, `κ` and the three conditions — `LEAN-ROADMAP.md` stones 9–10 (inventory A9)

Theorem E (`LIFT.md` §B.13.2, roadmap A16) reads

```
    D(A) <  gamma :   Phi_k(A) <= 2 - gamma - (1 - theta(n,k)) D(A)
    D(A) >= gamma :   Phi_k(A) <= 2 - D(A)
```

so the whole strictness half of Cheon–Hwang on `R_new` rests on one rational quantity being
below `1`.  This file is that quantity and its algebra — pure `ℚ`, no analysis, kernel-friendly.

## What is here

| § | content |
|---|---|
| 1 | `gamma`, `kappa`, `theta`, `C1`, `C2`, `C3`, transcribed from `graded_verify_strict.py` |
| 2 | the rearrangement: `theta ≤ 1` **is** `(C3)`, and `theta < 1` is `(C3)` made strict |
| 3 | the deficit algebra of Theorem E (`graded_verify_strict.py` block [3]) |
| 4 | the pinned cells: the worst cell of `R_new`, and the four cells `R_new` excludes |

## The correction edge, made explicit

`CORRECTIONS.md` 2026-08-03 records that `(C3)` is `theta ≤ 1`, **NOT** `theta < 1` — the two
are the same inequality rearranged, and strictness is a SEPARATE fact.  `theta_le_one_iff_C3`
and `theta_lt_one_iff_C3_strict` are that distinction in the kernel: the first consumes `(C3)`
as written and yields only `≤`; the second needs the strict hypothesis and is what Theorem E
actually requires.  Nothing here silently upgrades one to the other.

## Cross-check against the verifiers

Every definition is transcribed from `graded_verify_strict.py` (`gamma`, `theta`, `condsK`) and
every displayed constant below is that script's own value:

* `theta(7,6) = 155520/577877`, so `1 - theta = 422357/577877` — block [1]'s worst cell of
  `R_new`, and its "slope bounded away from `0`: `min(1 - theta) > 1/5`" check.
* the four cells `R_new` excludes: `(3,5)`, `(4,5)`, `(5,6)` fail `(C2)` **only**, while
  `(3,4)` fails all three — the `CORRECTIONS.md` reading, not `LIFT.md` §B.11.4's.
* the deficit identity `2 - D - gamma(1 - theta D/gamma) = 2 - gamma - (1 - theta) D` is
  block [3].

## What is NOT here

Stone 9 proper — `(C1)(C2)(C3)` at EVERY cell of `R_new`, i.e. reaching every `n` rather than
tabulating — is the roadmap's largest non-keystone item (size L) and is not attempted.  The
cells below are pinned individually; the uniform-in-`n` argument is owed.
-/

import Mathlib.Tactic

namespace Theta

/-! ## §1  The definitions, transcribed from `graded_verify_strict.py`

Casts are taken into `ℚ` before any subtraction, so no truncated `ℕ` subtraction can appear. -/

/-- `gamma = k!/n^k`. -/
def gamma (n k : ℕ) : ℚ := (k.factorial : ℚ) / (n : ℚ) ^ k

/-- `kappa = 3 gamma (k-2)(n-1)/(k-1)^2`. -/
def kappa (n k : ℕ) : ℚ :=
  3 * gamma n k * ((k : ℚ) - 2) * ((n : ℚ) - 1) / ((k : ℚ) - 1) ^ 2

/-- The denominator of `theta`: `(n-k)(k-1)(1-kappa)`. -/
def thetaDen (n k : ℕ) : ℚ := ((n : ℚ) - (k : ℚ)) * ((k : ℚ) - 1) * (1 - kappa n k)

/-- The numerator of `theta`: `gamma k^2 (n-1)`. -/
def thetaNum (n k : ℕ) : ℚ := gamma n k * (k : ℚ) ^ 2 * ((n : ℚ) - 1)

/-- **`LIFT.md` §B.11.1.**  `theta(n,k) = gamma k^2 (n-1) / ((n-k)(k-1)(1-kappa))`. -/
def theta (n k : ℕ) : ℚ := thetaNum n k / thetaDen n k

/-- `(C1)`: `gamma <= 1/12`. -/
def C1 (n k : ℕ) : Prop := gamma n k ≤ 1 / 12

/-- `(C2)`: `3 gamma k^2 (n-1)^2 <= ((n-k)(k-1))^2`. -/
def C2 (n k : ℕ) : Prop :=
  3 * gamma n k * (k : ℚ) ^ 2 * ((n : ℚ) - 1) ^ 2 ≤ (((n : ℚ) - (k : ℚ)) * ((k : ℚ) - 1)) ^ 2

/-- `(C3)`: `gamma k^2 (n-1) <= (n-k)(k-1)(1-kappa)`.  Note the `≤` — see the header. -/
def C3 (n k : ℕ) : Prop := thetaNum n k ≤ thetaDen n k

/-- The conditions of `graded_verify_strict.py`'s `condsK`, with its own guard `k ≥ 3`,
`n > k`. -/
def Conds (n k : ℕ) : Prop := 3 ≤ k ∧ k < n ∧ C1 n k ∧ C2 n k ∧ C3 n k

/-! ## §2  The rearrangement

`theta ≤ 1` and `(C3)` are the same inequality; `theta < 1` is a strictly stronger fact.  Both
need the denominator positive, which is the content of `(C1)` plus `k < n` in the region — here
it is carried as an explicit hypothesis so that no cell-specific reasoning leaks into the
algebra. -/

theorem thetaNum_pos {n k : ℕ} (hk : 2 ≤ k) (hn : k < n) : 0 < thetaNum n k := by
  have hk0 : (0 : ℚ) < (k : ℚ) := by
    have : 0 < k := by omega
    exact_mod_cast this
  have hn1 : (1 : ℚ) < (n : ℚ) := by
    have : 1 < n := by omega
    exact_mod_cast this
  have hg : 0 < gamma n k := by
    unfold gamma
    have hkf : (0 : ℚ) < (k.factorial : ℚ) := by
      exact_mod_cast k.factorial_pos
    positivity
  unfold thetaNum
  have : (0 : ℚ) < (n : ℚ) - 1 := by linarith
  positivity

/-- **`CORRECTIONS.md` 2026-08-03.**  `(C3)` says `theta ≤ 1` — and no more. -/
theorem theta_le_one_iff_C3 {n k : ℕ} (hden : 0 < thetaDen n k) :
    theta n k ≤ 1 ↔ C3 n k := by
  unfold theta C3
  exact div_le_one hden

/-- Strictness is a SEPARATE fact, and this is the only route to it. -/
theorem theta_lt_one_iff_C3_strict {n k : ℕ} (hden : 0 < thetaDen n k) :
    theta n k < 1 ↔ thetaNum n k < thetaDen n k := by
  unfold theta
  exact div_lt_one hden

theorem theta_pos {n k : ℕ} (hk : 2 ≤ k) (hn : k < n) (hden : 0 < thetaDen n k) :
    0 < theta n k :=
  div_pos (thetaNum_pos hk hn) hden

/-- The deficit slope `1 - theta` is positive exactly when `(C3)` is strict. -/
theorem one_sub_theta_pos {n k : ℕ} (hden : 0 < thetaDen n k)
    (h : thetaNum n k < thetaDen n k) : 0 < 1 - theta n k := by
  have := (theta_lt_one_iff_C3_strict hden).mpr h
  linarith

/-! ## §3  The deficit algebra of Theorem E

`graded_verify_strict.py` block [3].  The chain produces `Phi_k <= 2 - D - gamma(1 - theta
D/gamma)`; the displayed form of Theorem E is `2 - gamma - (1 - theta) D`.  They are equal,
identically in `D`, and that is the whole of the rearrangement. -/

/-- **Block [3], exactly.**  `2 - D - gamma(1 - theta D/gamma) = 2 - gamma - (1 - theta) D`. -/
theorem deficit_algebra {K : Type*} [Field K] (g th D : K) (hg : g ≠ 0) :
    2 - D - g * (1 - th * D / g) = 2 - g - (1 - th) * D := by
  field_simp
  ring

/-- The consequence Theorem E is stated for: on `D < gamma` the bound beats `2 - gamma` by the
deficit `(1 - theta) D`, and that deficit is strictly positive off `D = 0`. -/
theorem deficit_lt_of_pos {K : Type*} [LinearOrderedField K] {g th D : K}
    (hth : th < 1) (hD : 0 < D) : 2 - g - (1 - th) * D < 2 - g := by
  have : 0 < (1 - th) * D := mul_pos (by linarith) hD
  linarith

/-! ## §4  The pinned cells

Exact rational arithmetic, cross-checked against `graded_verify_strict.py`. -/

/-- The worst cell of `R_new`, `graded_verify_strict.py` block [1]: `(k,n) = (6,7)`. -/
theorem theta_six_seven : theta 7 6 = 155520 / 577877 := by
  norm_num [theta, thetaNum, thetaDen, kappa, gamma, Nat.factorial]

/-- The deficit slope at the worst cell: `1 - theta = 422357/577877`. -/
theorem one_sub_theta_six_seven : 1 - theta 7 6 = 422357 / 577877 := by
  rw [theta_six_seven]
  norm_num

/-- Block [1]'s "the slope is bounded away from `0` on `R_new`: `min(1 - theta) > 1/5`", at the
cell where the minimum is attained. -/
theorem slope_six_seven_gt_fifth : (1 : ℚ) / 5 < 1 - theta 7 6 := by
  rw [one_sub_theta_six_seven]
  norm_num

theorem conds_six_seven : Conds 7 6 := by
  refine ⟨by norm_num, by norm_num, ?_, ?_, ?_⟩ <;>
    norm_num [C1, C2, C3, thetaNum, thetaDen, kappa, gamma, Nat.factorial]

theorem conds_three_six : Conds 6 3 := by
  refine ⟨by norm_num, by norm_num, ?_, ?_, ?_⟩ <;>
    norm_num [C1, C2, C3, thetaNum, thetaDen, kappa, gamma, Nat.factorial]

/-! ### The four cells `R_new` excludes

`CORRECTIONS.md` 2026-08-03: `(3,5)`, `(4,5)` and `(5,6)` fail `(C2)` alone, but `(3,4)` fails
`(C1)` and `(C3)` as well — `LIFT.md` §B.11.4's reading, that `(C2)` is the only obstruction,
is the corrected one.  Cells are written `(k, n)`. -/

theorem not_C2_three_five : ¬ C2 5 3 := by
  norm_num [C2, gamma, Nat.factorial]

theorem not_C2_four_five : ¬ C2 5 4 := by
  norm_num [C2, gamma, Nat.factorial]

theorem not_C2_five_six : ¬ C2 6 5 := by
  norm_num [C2, gamma, Nat.factorial]

theorem not_C1_three_four : ¬ C1 4 3 := by
  norm_num [C1, gamma, Nat.factorial]

theorem not_C2_three_four : ¬ C2 4 3 := by
  norm_num [C2, gamma, Nat.factorial]

theorem not_C3_three_four : ¬ C3 4 3 := by
  norm_num [C3, thetaNum, thetaDen, kappa, gamma, Nat.factorial]

/-- All four excluded cells are outside the region, as `Conds`. -/
theorem not_conds_three_five : ¬ Conds 5 3 := fun h => not_C2_three_five h.2.2.2.1

theorem not_conds_four_five : ¬ Conds 5 4 := fun h => not_C2_four_five h.2.2.2.1

theorem not_conds_five_six : ¬ Conds 6 5 := fun h => not_C2_five_six h.2.2.2.1

theorem not_conds_three_four : ¬ Conds 4 3 := fun h => not_C1_three_four h.2.2.1

section AxiomAudit

#print axioms gamma
#print axioms kappa
#print axioms thetaDen
#print axioms thetaNum
#print axioms theta
#print axioms C1
#print axioms C2
#print axioms C3
#print axioms Conds
#print axioms thetaNum_pos
#print axioms theta_le_one_iff_C3
#print axioms theta_lt_one_iff_C3_strict
#print axioms theta_pos
#print axioms one_sub_theta_pos
#print axioms deficit_algebra
#print axioms deficit_lt_of_pos
#print axioms theta_six_seven
#print axioms one_sub_theta_six_seven
#print axioms slope_six_seven_gt_fifth
#print axioms conds_six_seven
#print axioms conds_three_six
#print axioms not_C2_three_five
#print axioms not_C2_four_five
#print axioms not_C2_five_six
#print axioms not_C1_three_four
#print axioms not_C2_three_four
#print axioms not_C3_three_four
#print axioms not_conds_three_five
#print axioms not_conds_four_five
#print axioms not_conds_five_six
#print axioms not_conds_three_four

end AxiomAudit

end Theta
