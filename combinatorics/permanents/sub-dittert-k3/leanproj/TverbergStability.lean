/-
# A stability form of Tverberg–Friedland: the coefficient and threshold layer

This file is **application material** for `graded_stability_lemma.md`, Theorem 1: for
`2 ≤ k ≤ 5` and `n` above an explicit threshold, every doubly stochastic `A` satisfies

    σ_k(A) − C(n,k)² k!/nᵏ  ≥  C(n,k)² c(n,k) ‖A − Jₙ/n‖²_F ,   c(n,k) = k(k−1)k!/(4nᵏ(n−1)²).

**Stage 0 of the formalisation.**  What is here is the arithmetic layer: the coefficients
`s_m, t_m` with their two laws, the three threshold inequalities `Φ(n,k) < 1`, the statement
of Theorem 1 itself as an indexed proposition, and Proposition 5 — the proof that the cell
`(k,n) = (3,3)` is a genuine counterexample.  **Theorem 1 itself is not proved here**, and
nothing in this file asserts it; `StabilityAt` is a `def` returning a `Prop`, precisely so that
the target can be named and later discharged cell by cell without statement drift.

## What is proved

* §1 `sVal`, `tVal`, and **`tVal_two`** — (2.1), `t₂ = k(k−1)k!/(nᵏ(n−1)²)` — together with
  **`cVal_eq_tVal_div_four`**, which is the form the statement uses: `c(n,k) = t₂/4`.
* §2 the threshold layer.  `phiPoly3/4/5` are the cleared numerators of `1 − Φ(·,k)`;
  `phiPoly3_pos`, `phiPoly4_pos`, `phiPoly5_pos` prove them positive above the thresholds
  `4, 8, 14`, by the shift `n = m + n_k`, after which every coefficient is a positive integer;
  and `Phi3_lt_one`, `Phi4_lt_one`, `Phi5_lt_one` convert those into `Φ(n,k) < 1`.
* §3 `cVal` and `StabilityAt`, the statement of Theorem 1 as a proposition per `(k,n)`.
* §4 `witness33` with `witness33_mem`, `witness33_sigma`, `witness33_dist`, and
  **`not_stabilityAt_three_three`** — Theorem 1 is FALSE at `(k,n) = (3,3)`, with the witness
  stored here rather than cited.

## What is NOT here

**(2.2), the ratio law `t_{m+1}/t_m = n(k−m)/(n−m)²`, is not formalised.**  It is the one
Stage 0 item outstanding.  Nothing in this file depends on it: the threshold inequalities of
§2 are stated in the closed forms (7.3)–(7.5), which is what the assembly consumes, and the
ratio law is only needed to derive those closed forms from `∑ t_m C_m` — assembly work, at
Stage 3 and Stage 4.  It is stated in the source as "immediate from the definitions", and the
obstacle is not mathematical: it is that `t_m` carries three truncated natural subtractions
(`k−m`, `k−(m+1)`, `n−m`), so the proof needs the same substitution discipline `tVal_two` uses,
generalised to a symbolic `m`.

## The threshold argument, and a correction to the source

Section 7 of the source clears the denominator of `Φ(·,k) < 1` into a polynomial inequality
`P_k(n) > 0`, substitutes `n = m + n_k`, and observes that every coefficient in `m` is then
nonnegative with positive constant term.  That argument is sound and is what §2 formalises.

The specific polynomials the source quotes as illustration are **wrong**, and the corrected
values are the ones used here (verified in exact rational arithmetic before this file was
written).  The source states `P₃(m+4) = 16/3 + 52m/3 + 8m² + m³`, degree three; the cleared
numerator is `3n² − 12n + 4`, so `P₃(m+4) = 3m² + 12m + 4`, degree **two**.  The source states
`P₄` has degree eight with constant term `218112` and `P₄(7) = −695800/3`; the cleared
numerator is degree **four**, with `P₄(m+8) = 3m⁴ + 66m³ + 491m² + 1280m + 284` and
`P₄(7) = −568`.  Only the illustrations are affected: every load-bearing claim of Section 7
survives unchanged — the three closed forms, the thresholds `4, 8, 14` as the least `n` with
`Φ < 1`, the strict failure at `n_k − 1`, and the four quoted values of `Φ`.  The error runs
in the direction that makes this section *cheaper* than the source suggests.

## Correspondence to the source

| here | source |
|---|---|
| `tVal_two` | (2.1), `t₂ = k(k−1)k!/(nᵏ(n−1)²)`, hence `c(n,k) = t₂/4` |
| `Phi3_lt_one` | (7.3) with the threshold `n ≥ 4` |
| `Phi4_lt_one` | (7.4) with the threshold `n ≥ 8` |
| `Phi5_lt_one` | (7.5) with the threshold `n ≥ 14` |
| `StabilityAt k n` | Theorem 1's conclusion at the cell `(k, n)` |
| `not_stabilityAt_three_three` | Proposition 5 |

`Φ(·,k)` is written here in the closed forms (7.3)–(7.5) rather than as `(4/t₂)∑ t_m C_m`;
the two agree by the ratio law, and the closed forms are what the threshold argument consumes.
-/

import Mathlib.Tactic
import Mathlib.Data.Matrix.DoublyStochastic
import RookSum

open Finset

namespace TverbergStability

/-! ## §1  The layer coefficients and their two laws -/

/-- `s_m = k(k−1)⋯(k−m+1) / (n(n−1)⋯(n−m+1))`. -/
noncomputable def sVal (k n m : ℕ) : ℝ :=
  (k.descFactorial m : ℝ) / (n.descFactorial m : ℝ)

/-- `t_m = s_m² (k−m)! / n^{k−m}`. -/
noncomputable def tVal (k n m : ℕ) : ℝ :=
  (sVal k n m) ^ 2 * ((k - m).factorial : ℝ) / (n : ℝ) ^ (k - m)

/-- **(2.1)** `t₂ = k(k−1)k!/(nᵏ(n−1)²)`.  Since `c(n,k) = t₂/4`, this is what ties the
constant of Theorem 1 to the layer coefficients. -/
theorem tVal_two {k n : ℕ} (hk : 2 ≤ k) (hn : 2 ≤ n) :
    tVal k n 2 = (k : ℝ) * ((k : ℝ) - 1) * (k.factorial : ℝ)
      / ((n : ℝ) ^ k * ((n : ℝ) - 1) ^ 2) := by
  -- Substituting `k = j+2`, `n = i+2` removes every truncated subtraction.
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  obtain ⟨i, rfl⟩ : ∃ i, n = i + 2 := ⟨n - 2, by omega⟩
  have hne : ((i : ℝ) + 2) ≠ 0 := by positivity
  have hne1 : ((i : ℝ) + 1) ≠ 0 := by positivity
  have hpowne : ((i : ℝ) + 2) ^ j ≠ 0 := pow_ne_zero _ hne
  -- The three ingredient identities, each kept in FACTORED form: an expanded denominator
  -- is what defeats `field_simp`.
  have hdk : (((j + 2).descFactorial 2 : ℕ) : ℝ) = ((j : ℝ) + 2) * ((j : ℝ) + 1) := by
    simp [Nat.descFactorial_succ]
    ring
  have hdn : (((i + 2).descFactorial 2 : ℕ) : ℝ) = ((i : ℝ) + 2) * ((i : ℝ) + 1) := by
    simp [Nat.descFactorial_succ]
    ring
  have hfac : (((j + 2).factorial : ℕ) : ℝ)
      = ((j : ℝ) + 2) * ((j : ℝ) + 1) * ((j.factorial : ℕ) : ℝ) := by
    rw [Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    ring
  unfold tVal sVal
  rw [show j + 2 - 2 = j from by omega, hdk, hdn, hfac]
  push_cast
  -- `positivity` cannot clear `(i+2)-1`; put it in the form `i+1` first.
  rw [show ((i : ℝ) + 2 - 1) = (i : ℝ) + 1 from by ring]
  rw [div_eq_div_iff (by positivity) (by positivity), div_pow,
    div_mul_eq_mul_div, div_mul_eq_mul_div, div_eq_iff (by positivity)]
  ring

/-! ## §2  The threshold layer -/

/-- The cleared numerator of `1 − Φ(n,3)`, over the positive denominator `3(n−2)²`. -/
def phiPoly3 (n : ℝ) : ℝ := 3 * n ^ 2 - 12 * n + 4

/-- The cleared numerator of `1 − Φ(n,4)`, over `3(n−3)²(n−2)²`. -/
def phiPoly4 (n : ℝ) : ℝ := 3 * n ^ 4 - 30 * n ^ 3 + 59 * n ^ 2 - 48 * n - 36

/-- The cleared numerator of `1 − Φ(n,5)`, over `5(n−4)²(n−3)²(n−2)²`. -/
def phiPoly5 (n : ℝ) : ℝ :=
  5 * n ^ 6 - 90 * n ^ 5 + 445 * n ^ 4 - 1760 * n ^ 3 + 620 * n ^ 2 + 2400 * n - 3456

/-- `P₃(m+4) = 3m² + 12m + 4`: every coefficient positive, so `P₃ > 0` for `n ≥ 4`. -/
theorem phiPoly3_pos {n : ℝ} (hn : 4 ≤ n) : 0 < phiPoly3 n := by
  have hm : (0:ℝ) ≤ n - 4 := by linarith
  have hshift : phiPoly3 n = 3 * (n - 4) ^ 2 + 12 * (n - 4) + 4 := by
    unfold phiPoly3; ring
  rw [hshift]
  have := sq_nonneg (n - 4)
  linarith

/-- `P₄(m+8) = 3m⁴ + 66m³ + 491m² + 1280m + 284`, all coefficients positive. -/
theorem phiPoly4_pos {n : ℝ} (hn : 8 ≤ n) : 0 < phiPoly4 n := by
  have hm : (0:ℝ) ≤ n - 8 := by linarith
  have hshift : phiPoly4 n
      = 3 * (n - 8) ^ 4 + 66 * (n - 8) ^ 3 + 491 * (n - 8) ^ 2 + 1280 * (n - 8) + 284 := by
    unfold phiPoly4; ring
  rw [hshift]
  have h2 := sq_nonneg (n - 8)
  have h3 : (0:ℝ) ≤ (n - 8) ^ 3 := by positivity
  have h4 : (0:ℝ) ≤ (n - 8) ^ 4 := by positivity
  linarith

/-- `P₅(m+14) = 5m⁶ + 330m⁵ + 8845m⁴ + 121160m³ + 861620m² + 2716720m + 1660864`. -/
theorem phiPoly5_pos {n : ℝ} (hn : 14 ≤ n) : 0 < phiPoly5 n := by
  have hm : (0:ℝ) ≤ n - 14 := by linarith
  have hshift : phiPoly5 n
      = 5 * (n - 14) ^ 6 + 330 * (n - 14) ^ 5 + 8845 * (n - 14) ^ 4
        + 121160 * (n - 14) ^ 3 + 861620 * (n - 14) ^ 2 + 2716720 * (n - 14) + 1660864 := by
    unfold phiPoly5; ring
  rw [hshift]
  have h2 : (0:ℝ) ≤ (n - 14) ^ 2 := by positivity
  have h3 : (0:ℝ) ≤ (n - 14) ^ 3 := by positivity
  have h4 : (0:ℝ) ≤ (n - 14) ^ 4 := by positivity
  have h5 : (0:ℝ) ≤ (n - 14) ^ 5 := by positivity
  have h6 : (0:ℝ) ≤ (n - 14) ^ 6 := by positivity
  linarith

/-- **(7.3)** `Φ(n,3) = 8/(3(n−2)²) < 1` for every `n ≥ 4`. -/
theorem Phi3_lt_one {n : ℝ} (hn : 4 ≤ n) : 8 / (3 * (n - 2) ^ 2) < 1 := by
  have h2 : (0:ℝ) < (n - 2) ^ 2 := by nlinarith
  have hD : (0:ℝ) < 3 * (n - 2) ^ 2 := by linarith
  rw [div_lt_one hD]
  have := phiPoly3_pos hn
  unfold phiPoly3 at this
  nlinarith [this]

/-- **(7.4)** `Φ(n,4) < 1` for every `n ≥ 8`. -/
theorem Phi4_lt_one {n : ℝ} (hn : 8 ≤ n) :
    16 / (3 * (n - 2) ^ 2) + 12 * n * (n - 1) / ((n - 2) ^ 2 * (n - 3) ^ 2) < 1 := by
  have h2 : (0:ℝ) < (n - 2) ^ 2 := by nlinarith
  have h3 : (0:ℝ) < (n - 3) ^ 2 := by nlinarith
  have h2' : (n : ℝ) - 2 ≠ 0 := by intro h; rw [h] at h2; simp at h2
  have h3' : (n : ℝ) - 3 ≠ 0 := by intro h; rw [h] at h3; simp at h3
  have hD : (0:ℝ) < 3 * (n - 2) ^ 2 * (n - 3) ^ 2 :=
    mul_pos (mul_pos (by norm_num) h2) h3
  rw [← sub_pos]
  have hid : 1 - (16 / (3 * (n - 2) ^ 2) + 12 * n * (n - 1) / ((n - 2) ^ 2 * (n - 3) ^ 2))
      = phiPoly4 n / (3 * (n - 2) ^ 2 * (n - 3) ^ 2) := by
    unfold phiPoly4
    field_simp
    ring
  rw [hid]
  exact div_pos (phiPoly4_pos hn) hD

/-- **(7.5)** `Φ(n,5) < 1` for every `n ≥ 14`.  `Φ(·,5)` is written in the form
`4(55n⁴ − 205n³ + 1230n² − 2160n + 1584) / (5(n−4)²(n−3)²(n−2)²)`, which is (7.5) with the
three fractions put over a common denominator and `C₅(n)` expanded. -/
theorem Phi5_lt_one {n : ℝ} (hn : 14 ≤ n) :
    4 * (55 * n ^ 4 - 205 * n ^ 3 + 1230 * n ^ 2 - 2160 * n + 1584)
      / (5 * ((n - 4) ^ 2 * (n - 3) ^ 2 * (n - 2) ^ 2)) < 1 := by
  have h2 : (0:ℝ) < (n - 2) ^ 2 := by nlinarith
  have h3 : (0:ℝ) < (n - 3) ^ 2 := by nlinarith
  have h4 : (0:ℝ) < (n - 4) ^ 2 := by nlinarith
  have hD : (0:ℝ) < 5 * ((n - 4) ^ 2 * (n - 3) ^ 2 * (n - 2) ^ 2) :=
    mul_pos (by norm_num) (mul_pos (mul_pos h4 h3) h2)
  rw [div_lt_one hD]
  have := phiPoly5_pos hn
  unfold phiPoly5 at this
  nlinarith [this]

/-! ## §3  The statement of Theorem 1 -/

/-- `c(n,k) = k(k−1)k!/(4nᵏ(n−1)²)`, the constant of Theorem 1.  By `cVal_eq_tVal_div_four`
this is `t₂/4`, which is (2.1). -/
noncomputable def cVal (k n : ℕ) : ℝ :=
  (k : ℝ) * ((k : ℝ) - 1) * (k.factorial : ℝ) / (4 * (n : ℝ) ^ k * ((n : ℝ) - 1) ^ 2)

/-- **(2.1), in the form the statement uses:** `c(n,k) = t₂/4`. -/
theorem cVal_eq_tVal_div_four {k n : ℕ} (hk : 2 ≤ k) (hn : 2 ≤ n) :
    cVal k n = tVal k n 2 / 4 := by
  rw [tVal_two hk hn, cVal, div_div]
  congr 1
  ring

/-- **Theorem 1 at the cell `(k, n)`.**  This is a `def` returning a `Prop`: nothing in this
file asserts it, and no stage may weaken it.  Later stages discharge it cell by cell. -/
noncomputable def StabilityAt (k n : ℕ) : Prop :=
  ∀ A : Matrix (Fin n) (Fin n) ℝ, A ∈ doublyStochastic ℝ (Fin n) →
    (n.choose k : ℝ) ^ 2 * cVal k n * (∑ i, ∑ j, (A i j - 1 / (n : ℝ)) ^ 2)
      ≤ RookSum.sigP k A - (n.choose k : ℝ) ^ 2 * (k.factorial : ℝ) / (n : ℝ) ^ k

/-! ## §4  Proposition 5: the cell `(k, n) = (3, 3)` is a genuine counterexample

The witness is stored here, not cited: `A = (J₃ − P)/2`, uniform off a permutation.  `σ₃` is
evaluated through `RookSum.sigma_three_closed`, the general-`n` closed form, so no permanent
is ever computed. -/

/-- The witness of Proposition 5: `1/2` off the diagonal, `0` on it. -/
noncomputable def witness33 : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun i j => if i = j then 0 else 1 / 2

theorem witness33_apply (i j : Fin 3) :
    witness33 i j = if i = j then 0 else 1 / 2 := rfl

theorem witness33_mem : witness33 ∈ doublyStochastic ℝ (Fin 3) := by
  rw [mem_doublyStochastic_iff_sum]
  refine ⟨?_, ?_, ?_⟩
  · intro i j; fin_cases i <;> fin_cases j <;> norm_num [witness33_apply, Fin.ext_iff]
  · intro i; fin_cases i <;> norm_num [witness33_apply, Fin.sum_univ_three, Fin.ext_iff]
  · intro j; fin_cases j <;> norm_num [witness33_apply, Fin.sum_univ_three, Fin.ext_iff]

/-- `σ₃(A) = 1/4` at the witness, via the closed form rather than a permanent. -/
theorem witness33_sigma : RookSum.sigP 3 witness33 = 1 / 4 := by
  have h := RookSum.sigma_three_closed witness33
  norm_num [witness33_apply, Fin.sum_univ_three, Fin.ext_iff] at h
  linarith

/-- `‖A − J₃/3‖²_F = 1/2` at the witness. -/
theorem witness33_dist : ∑ i, ∑ j, (witness33 i j - 1 / (3:ℝ)) ^ 2 = 1 / 2 := by
  norm_num [witness33_apply, Fin.sum_univ_three, Fin.ext_iff]

/-- **Proposition 5.**  Theorem 1 is FALSE at `(k, n) = (3, 3)`: the witness gives
`F/Q = 1/18` against `c(3,3) = 1/12`. -/
theorem not_stabilityAt_three_three : ¬ StabilityAt 3 3 := by
  intro h
  have hw := h witness33 witness33_mem
  rw [witness33_sigma] at hw
  push_cast at hw
  rw [witness33_dist] at hw
  norm_num [cVal, Nat.factorial] at hw

/-! ## §5  Axiom audit

**Every declaration in this file depends only on axioms among `propext,
Classical.choice, Quot.sound`.**  No `native_decide`, no `sorry`. -/

section AxiomAudit

#print axioms sVal
#print axioms tVal
#print axioms tVal_two
#print axioms phiPoly3
#print axioms phiPoly4
#print axioms phiPoly5
#print axioms phiPoly3_pos
#print axioms phiPoly4_pos
#print axioms phiPoly5_pos
#print axioms Phi3_lt_one
#print axioms Phi4_lt_one
#print axioms Phi5_lt_one
#print axioms cVal
#print axioms cVal_eq_tVal_div_four
#print axioms StabilityAt
#print axioms witness33
#print axioms witness33_apply
#print axioms witness33_mem
#print axioms witness33_sigma
#print axioms witness33_dist
#print axioms not_stabilityAt_three_three

end AxiomAudit

end TverbergStability
