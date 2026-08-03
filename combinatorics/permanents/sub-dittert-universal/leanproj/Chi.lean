/-
# The entropy cost function `χ` — `LEAN-ROADMAP.md` stone 4 (inventory A5)

`LIFT.md` §B.10.2 reads the capacity loss off the doubly stochastic face as an explicit sum of
values of

    chi(t) = (1-t) log(1-t) + t = sum_{m>=2} t^m / (m(m-1)) ,

one term per line of the witness `W`, and §B.10.4 spends that sum against the `E_k` deficit
using exactly two estimates:

> `chi >= 0` on `t < 1`, and `chi(t) <= t^2` for every `t <= 1`.

This file is those two estimates and nothing else (roadmap inventory A5, consumed at chain step
(S4)).

## The proofs are one Mathlib lemma, twice

Substituting `u = 1 - t >= 0` turns `chi` into `u log u + 1 - u`, and then

* `chi(t) <= t^2` is `log u <= u - 1` multiplied by `u`, and
* `chi(t) >= 0` is the same inequality applied at `1/u` and multiplied by `u`.

Both are `Real.log_le_sub_one_of_pos`.  The roadmap costs this stone at size M on the strength
of the series argument of §B.10.4 (`chi(t)/t^2` increasing, telescoping to `1`); the `u`
substitution removes the series entirely, so the stone came in at S.

## The `u = 0` endpoint is not a special case in Lean

Lean's `Real.log 0 = 0`, so `chi 1 = 0 * 0 + 1 = 1`, and both estimates hold AT `t = 1` — the
second with equality, `chi 1 = 1 = 1^2`.  That is why the statements below say `t ≤ 1` and not
`t < 1`: the junk value happens to be the right value, and carrying the closed interval saves
the consumer a case split.  Nothing downstream evaluates `chi` at `t > 1`; Lemma B8 with (C2)
guarantees `|t| ≤ 1` at every point where `chi` is used (`LIFT.md` §B.10.4).
-/

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Finset

namespace Chi

/-- **`LIFT.md` §B.10.2.**  `chi t = (1 - t) log (1 - t) + t`. -/
noncomputable def chi (t : ℝ) : ℝ := (1 - t) * Real.log (1 - t) + t

@[simp] theorem chi_zero : chi 0 = 0 := by simp [chi]

/-- At the endpoint, `chi 1 = 1`: Lean's `Real.log 0 = 0` gives the analytic limit value. -/
@[simp] theorem chi_one : chi 1 = 1 := by simp [chi]

/-! ## §1  The two estimates

Both are the single inequality `log u ≤ u - 1`, in the substitution `u = 1 - t`. -/

/-- The substituted form: `chi (1 - u) = u log u + 1 - u`. -/
theorem chi_sub (u : ℝ) : chi (1 - u) = u * Real.log u + 1 - u := by
  simp only [chi]
  ring_nf

/-- **A5, first estimate.**  `chi ≥ 0` for every `t ≤ 1`.  Equality only at `t = 0`. -/
theorem chi_nonneg {t : ℝ} (ht : t ≤ 1) : 0 ≤ chi t := by
  have hu : 0 ≤ 1 - t := by linarith
  have hrw : chi t = (1 - t) * Real.log (1 - t) + 1 - (1 - t) := by
    simp only [chi]; ring
  rcases eq_or_lt_of_le hu with h | h
  · rw [hrw, ← h]
    simp
  · -- `log u ≥ 1 - 1/u`, from `log (1/u) ≤ 1/u - 1`
    have hinv : Real.log (1 / (1 - t)) ≤ 1 / (1 - t) - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_div one_ne_zero h.ne', Real.log_one, zero_sub] at hinv
    have hkey : (1 - t) - 1 ≤ (1 - t) * Real.log (1 - t) := by
      have := mul_le_mul_of_nonneg_left hinv h.le
      have hne : (1 - t) ≠ 0 := h.ne'
      field_simp at this
      linarith
    rw [hrw]
    linarith

/-- **A5, second estimate.**  `chi t ≤ t²` for every `t ≤ 1`, with equality at `t = 0` and at
`t = 1`.  This is the step that turns the entropy loss of `LIFT.md` §B.10.2 into a quadratic
form comparable with the `E_k` deficit. -/
theorem chi_le_sq {t : ℝ} (ht : t ≤ 1) : chi t ≤ t ^ 2 := by
  have hu : 0 ≤ 1 - t := by linarith
  have hrw : chi t = (1 - t) * Real.log (1 - t) + 1 - (1 - t) := by
    simp only [chi]; ring
  rcases eq_or_lt_of_le hu with h | h
  · rw [hrw, ← h]
    have : t = 1 := by linarith
    simp [this]
  · have hlog : Real.log (1 - t) ≤ (1 - t) - 1 := Real.log_le_sub_one_of_pos h
    have hkey : (1 - t) * Real.log (1 - t) ≤ (1 - t) * ((1 - t) - 1) :=
      mul_le_mul_of_nonneg_left hlog h.le
    rw [hrw]
    nlinarith

/-! ## §2  The `Finset` forms

The shape the witness sum of `LIFT.md` §B.10.2 is consumed in: one `chi` per line of `W`. -/

variable {ι : Type*} [Fintype ι]

theorem sum_chi_nonneg (f : ι → ℝ) (hf : ∀ i, f i ≤ 1) : 0 ≤ ∑ i, chi (f i) :=
  Finset.sum_nonneg fun i _ => chi_nonneg (hf i)

/-- The `(S4)` comparison in its raw form: the entropy sum is dominated by the quadratic form
`∑ (f i)²`, which is what Lemma B9 then spends against `1 - E_k(r)`. -/
theorem sum_chi_le_sum_sq (f : ι → ℝ) (hf : ∀ i, f i ≤ 1) :
    ∑ i, chi (f i) ≤ ∑ i, (f i) ^ 2 :=
  Finset.sum_le_sum fun i _ => chi_le_sq (hf i)

/-- With a uniform bound `|f i| ≤ b` the sum is at most `card ι * b²` — the form used with
Lemma B8's `k|R_i| ≤ 1`. -/
theorem sum_chi_le_card_mul (f : ι → ℝ) (hf : ∀ i, f i ≤ 1) {b : ℝ} (hb : ∀ i, (f i) ^ 2 ≤ b) :
    ∑ i, chi (f i) ≤ (Fintype.card ι : ℝ) * b := by
  refine (sum_chi_le_sum_sq f hf).trans ?_
  calc ∑ i, (f i) ^ 2 ≤ ∑ _i : ι, b := Finset.sum_le_sum fun i _ => hb i
    _ = (Fintype.card ι : ℝ) * b := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

section AxiomAudit

#print axioms chi
#print axioms chi_zero
#print axioms chi_one
#print axioms chi_sub
#print axioms chi_nonneg
#print axioms chi_le_sq
#print axioms sum_chi_nonneg
#print axioms sum_chi_le_sum_sq
#print axioms sum_chi_le_card_mul

end AxiomAudit

end Chi
