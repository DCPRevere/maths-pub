/-
# The `k = 5` per-layer atoms that do not need F4

`graded_stability_lemma.md` Lemma 4 items **(b), (c), (e), (h)**, plus Lemma 3 **(F3)**.

## What this file is, and what it is NOT

The `(k = 5, n ≥ 14)` cell needs six of Lemma 4's estimates.  Two of them — (f) `|Γₐ| ≤ MQ`
and (g) `|Γ_b| ≤ βQ` — rest on **F4**, `‖B‖_op ≤ 1`, which needs Birkhoff's theorem together
with an operator norm on `EuclideanSpace` and the mixed bound `‖BᵀB‖_F ≤ ‖Bᵀ‖_op‖B‖_F`.
Those two, and the `σ₅` core expansion (4.4), are **not here** and the cell is **not closed**.

What IS here is the complement: every Lemma 3/4 item the `k = 5` assembly needs that is free of
F4, each reusing material already committed.  They are worth having on their own — a later
attempt on the cell would otherwise rederive them — and each is stated at the same generality
as its `k ≤ 4` counterpart.

## The one-sided pattern, again

(b), (c) and (e) are all the source's (6.1) discipline at other degrees: on `[−1/n, β]` an odd
power is bounded below by a lower power times `−(1/n)^{...}`, and an even power above by `β^{...}`
times a lower one.  Each reduces to a pointwise polynomial inequality with a visible
factorisation, and none needs a sign hypothesis on the bounding constant — exactly as
`StabilityK3.cube_ge` did not.

| here | source |
|---|---|
| `quintic_ge`, `sum_quintic_ge`, `pFive_ge` | Lemma 4(b), `p₅ ≥ −n⁻³Q` |
| `quartic_le`, `sum_quartic_le`, `pFour_le` | Lemma 4(c), `p₄ ≤ β²Q` |
| `cube_le` | (6.1), the upper side |
| `frobQ_le` | Lemma 3 (F3), `Q ≤ n−1` |
| `frobQ_pThree_ge` | Lemma 4(h), `Q p₃ ≥ −βQ` |
| `gammaC_le`, `gammaC'_le` | Lemma 4(e), `Γ_c ≤ βMQ ≤ β²Q` |
-/

import Mathlib.Tactic
import Mathlib.Data.Matrix.DoublyStochastic
import RookSum
import SigmaFour
import StabilityK3
import StabilityK4
import GradedInequalities

open Finset

namespace StabilityK5Atoms

variable {n : ℕ}

/-! ## §1  The degree-five and degree-four pointwise estimates -/

/-- **(6.1) at degree five.**  `b⁵ ≥ −c³b²` whenever `b ≥ −c`; the factorisation is
`b²(b + c)(b² − bc + c²) ≥ 0`, whose last factor is `(b − c/2)² + 3c²/4`.

As with `StabilityK3.cube_ge`, NO sign hypothesis on `c` is needed: `b + c ≥ 0` is the whole
content. -/
theorem quintic_ge {b c : ℝ} (h : -c ≤ b) : -(c ^ 3 * b ^ 2) ≤ b ^ 5 := by
  have hbc : (0:ℝ) ≤ b + c := by linarith
  have hq : (0:ℝ) ≤ b ^ 2 - b * c + c ^ 2 := by nlinarith [sq_nonneg (b - c / 2), sq_nonneg c]
  nlinarith [mul_nonneg (mul_nonneg (sq_nonneg b) hbc) hq]

/-- **(6.1), the upper side.**  `b³ ≤ c·b²` whenever `b ≤ c`; the factorisation is
`b²(c − b) ≥ 0`. -/
theorem cube_le {b c : ℝ} (h : b ≤ c) : b ^ 3 ≤ c * b ^ 2 := by
  nlinarith [mul_nonneg (sq_nonneg b) (by linarith : (0:ℝ) ≤ c - b)]

/-- **Lemma 4(c), pointwise.**  `b⁴ ≤ c²b²` whenever `|b| ≤ c`. -/
theorem quartic_le {b c : ℝ} (h1 : -c ≤ b) (h2 : b ≤ c) : b ^ 4 ≤ c ^ 2 * b ^ 2 := by
  nlinarith [mul_nonneg (sq_nonneg b) (by nlinarith : (0:ℝ) ≤ c ^ 2 - b ^ 2)]

/-! ## §2  Summed forms -/

/-- `p₅`, the fifth power sum. -/
noncomputable def pFive (B : Matrix (Fin n) (Fin n) ℝ) : ℝ := ∑ i, ∑ j, B i j ^ 5

/-- `Γ_c = ∑ᵢ qᵢ f₃(i)` with `f₃(i) = ∑ⱼ b_ij³`. -/
noncomputable def gammaC (B : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ∑ i, (∑ j, B i j ^ 2) * (∑ j, B i j ^ 3)

/-- `Γ'_c = ∑ⱼ q'ⱼ g₃(j)` with `g₃(j) = ∑ᵢ b_ij³`. -/
noncomputable def gammaC' (B : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ∑ j, (∑ i, B i j ^ 2) * (∑ i, B i j ^ 3)

/-- **Lemma 4(b)**, summed: `p₅ ≥ −c³Q` when every entry is `≥ −c`. -/
theorem sum_quintic_ge {B : Matrix (Fin n) (Fin n) ℝ} {c : ℝ} (hB : ∀ i j, -c ≤ B i j) :
    -(c ^ 3 * SigmaFour.frobQ B) ≤ pFive B := by
  have key : (0:ℝ) ≤ ∑ i, ∑ j, (B i j ^ 5 + c ^ 3 * B i j ^ 2) :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by
      have := quintic_ge (hB i j); linarith
  have hsplit : (∑ i, ∑ j, (B i j ^ 5 + c ^ 3 * B i j ^ 2))
      = pFive B + c ^ 3 * SigmaFour.frobQ B := by
    rw [pFive, SigmaFour.frobQ]
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [hsplit] at key
  linarith

/-- **Lemma 4(c)**, summed: `p₄ ≤ c²Q` when every entry lies in `[−c, c]`. -/
theorem sum_quartic_le {B : Matrix (Fin n) (Fin n) ℝ} {c : ℝ}
    (h1 : ∀ i j, -c ≤ B i j) (h2 : ∀ i j, B i j ≤ c) :
    SigmaFour.pFour B ≤ c ^ 2 * SigmaFour.frobQ B := by
  rw [SigmaFour.pFour, SigmaFour.frobQ, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun j _ => quartic_le (h1 i j) (h2 i j)

/-! ## §3  The doubly stochastic instances

`entry_lower` and `entry_upper` are `StabilityK3`'s (F1); `1/n ≤ β` for `n ≥ 2` is what makes
the two-sided bound `|b| ≤ β` available from the asymmetric range. -/

/-- **Lemma 4(b)** at `c = 1/n`: `p₅ ≥ −Q/n³`. -/
theorem pFive_ge {A : Matrix (Fin n) (Fin n) ℝ} (hA : A ∈ doublyStochastic ℝ (Fin n)) :
    -((1 / (n : ℝ)) ^ 3 * SigmaFour.frobQ (StabilityK3.centre A))
      ≤ pFive (StabilityK3.centre A) :=
  sum_quintic_ge (fun i j => StabilityK3.entry_lower hA i j)

/-- `1/n ≤ 1 − 1/n` for `n ≥ 2`: the asymmetric range of (F1) is contained in `[−β, β]`. -/
theorem inv_le_beta (hn : 2 ≤ n) : 1 / (n : ℝ) ≤ 1 - 1 / (n : ℝ) := by
  have hN : (2:ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h0 : (0:ℝ) < (n : ℝ) := by linarith
  rw [le_sub_iff_add_le, ← two_mul, mul_one_div, div_le_one h0]
  exact hN

/-- **Lemma 4(c)** at `c = β`: `p₄ ≤ β²Q`. -/
theorem pFour_le {A : Matrix (Fin n) (Fin n) ℝ} (hn : 2 ≤ n)
    (hA : A ∈ doublyStochastic ℝ (Fin n)) :
    SigmaFour.pFour (StabilityK3.centre A)
      ≤ (1 - 1 / (n : ℝ)) ^ 2 * SigmaFour.frobQ (StabilityK3.centre A) := by
  refine sum_quartic_le (fun i j => ?_) (fun i j => StabilityK3.entry_upper hA i j)
  rw [StabilityK3.centre_apply]
  have h1 := StabilityK3.entry_lower (n := n) hA i j
  have h2 := inv_le_beta (n := n) hn
  linarith

/-- **Lemma 3 (F3):** `Q ≤ n − 1`, by summing (F2) over the rows.  Attained at every
permutation matrix. -/
theorem frobQ_le {A : Matrix (Fin n) (Fin n) ℝ} (hn : 1 ≤ n)
    (hA : A ∈ doublyStochastic ℝ (Fin n)) :
    SigmaFour.frobQ (StabilityK3.centre A) ≤ (n : ℝ) - 1 := by
  have h0 : (0:ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hrow : ∀ i : Fin n, (∑ j, StabilityK3.centre A i j ^ 2) ≤ 1 - 1 / (n : ℝ) :=
    fun i => StabilityK4.row_sq_le hA i
  have hsum : SigmaFour.frobQ (StabilityK3.centre A)
      ≤ ∑ _i : Fin n, (1 - 1 / (n : ℝ)) :=
    Finset.sum_le_sum fun i _ => hrow i
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have hid : (n : ℝ) * (1 - 1 / (n : ℝ)) = (n : ℝ) - 1 := by field_simp
  linarith [hsum, hid]

/-- **Lemma 4(h):** `Q·p₃ ≥ −βQ`.  This is (a) multiplied by `Q ≥ 0` and then (F3). -/
theorem frobQ_pThree_ge {A : Matrix (Fin n) (Fin n) ℝ} (hn : 2 ≤ n)
    (hA : A ∈ doublyStochastic ℝ (Fin n)) :
    -((1 - 1 / (n : ℝ)) * SigmaFour.frobQ (StabilityK3.centre A))
      ≤ SigmaFour.frobQ (StabilityK3.centre A)
        * ∑ i, ∑ j, StabilityK3.centre A i j ^ 3 := by
  have hN : (2:ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h0 : (0:ℝ) < (n : ℝ) := by linarith
  have hQ0 : (0:ℝ) ≤ SigmaFour.frobQ (StabilityK3.centre A) :=
    StabilityK4.frobQ_nonneg _
  have hp3 : -(1 / (n : ℝ) * SigmaFour.frobQ (StabilityK3.centre A))
      ≤ ∑ i, ∑ j, StabilityK3.centre A i j ^ 3 :=
    StabilityK3.sum_cube_ge (B := StabilityK3.centre A)
      (fun i j => StabilityK3.entry_lower hA i j)
  have hQle := frobQ_le (by omega) hA
  -- Q·p₃ ≥ −Q²/n, and Q²/n ≤ (n−1)Q/n = βQ by (F3)
  have step : SigmaFour.frobQ (StabilityK3.centre A)
      * -(1 / (n : ℝ) * SigmaFour.frobQ (StabilityK3.centre A))
      ≤ SigmaFour.frobQ (StabilityK3.centre A)
        * ∑ i, ∑ j, StabilityK3.centre A i j ^ 3 :=
    mul_le_mul_of_nonneg_left hp3 hQ0
  have hstep : -(SigmaFour.frobQ (StabilityK3.centre A) ^ 2 / (n : ℝ))
      ≤ SigmaFour.frobQ (StabilityK3.centre A)
        * ∑ i, ∑ j, StabilityK3.centre A i j ^ 3 := by
    have hid : SigmaFour.frobQ (StabilityK3.centre A)
        * -(1 / (n : ℝ) * SigmaFour.frobQ (StabilityK3.centre A))
        = -(SigmaFour.frobQ (StabilityK3.centre A) ^ 2 / (n : ℝ)) := by ring
    rw [← hid]; exact step
  have hsq : SigmaFour.frobQ (StabilityK3.centre A) ^ 2
      ≤ ((n : ℝ) - 1) * SigmaFour.frobQ (StabilityK3.centre A) := by
    nlinarith [hQle, hQ0]
  have hnb : (n : ℝ) * (1 - 1 / (n : ℝ)) = (n : ℝ) - 1 := by field_simp
  have hfin : SigmaFour.frobQ (StabilityK3.centre A) ^ 2 / (n : ℝ)
      ≤ (1 - 1 / (n : ℝ)) * SigmaFour.frobQ (StabilityK3.centre A) := by
    rw [div_le_iff₀ h0]
    nlinarith [hsq, hnb]
  linarith [hstep, hfin]

/-- **Lemma 4(e):** `Γ_c ≤ β²Q`.  By (6.1)'s upper side, `f₃(i) ≤ βqᵢ`; then `Γ_c ≤ βY_R` and
`Y_R ≤ βQ` from `StabilityK4.YR_le`. -/
theorem gammaC_le {A : Matrix (Fin n) (Fin n) ℝ} (hA : A ∈ doublyStochastic ℝ (Fin n)) :
    gammaC (StabilityK3.centre A)
      ≤ (1 - 1 / (n : ℝ)) ^ 2 * SigmaFour.frobQ (StabilityK3.centre A) := by
  have hf3 : ∀ i : Fin n, (∑ j, StabilityK3.centre A i j ^ 3)
      ≤ (1 - 1 / (n : ℝ)) * ∑ j, StabilityK3.centre A i j ^ 2 := by
    intro i
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ => cube_le (StabilityK3.entry_upper hA i j)
  have hq0 : ∀ i : Fin n, (0:ℝ) ≤ ∑ j, StabilityK3.centre A i j ^ 2 :=
    fun i => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hstep : gammaC (StabilityK3.centre A)
      ≤ (1 - 1 / (n : ℝ)) * SigmaFour.YR (StabilityK3.centre A) := by
    rw [gammaC, SigmaFour.YR, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    calc (∑ j, StabilityK3.centre A i j ^ 2) * (∑ j, StabilityK3.centre A i j ^ 3)
        ≤ (∑ j, StabilityK3.centre A i j ^ 2)
            * ((1 - 1 / (n : ℝ)) * ∑ j, StabilityK3.centre A i j ^ 2) :=
          mul_le_mul_of_nonneg_left (hf3 i) (hq0 i)
      _ = (1 - 1 / (n : ℝ)) * (∑ j, StabilityK3.centre A i j ^ 2) ^ 2 := by ring
  have hYR := StabilityK4.YR_le hA
  have hbeta0 : (0:ℝ) ≤ 1 - 1 / (n : ℝ) := by
    rcases Nat.eq_zero_or_pos n with rfl | hp
    · norm_num
    · have h0 : (1:ℝ) ≤ (n : ℝ) := by exact_mod_cast hp
      have : (0:ℝ) < (n : ℝ) := by linarith
      rw [sub_nonneg, div_le_one this]
      linarith
  nlinarith [mul_le_mul_of_nonneg_left hYR hbeta0]

/-- **Lemma 4(e)** for columns. -/
theorem gammaC'_le {A : Matrix (Fin n) (Fin n) ℝ} (hA : A ∈ doublyStochastic ℝ (Fin n)) :
    gammaC' (StabilityK3.centre A)
      ≤ (1 - 1 / (n : ℝ)) ^ 2 * SigmaFour.frobQ (StabilityK3.centre A) := by
  have hf3 : ∀ j : Fin n, (∑ i, StabilityK3.centre A i j ^ 3)
      ≤ (1 - 1 / (n : ℝ)) * ∑ i, StabilityK3.centre A i j ^ 2 := by
    intro j
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => cube_le (StabilityK3.entry_upper hA i j)
  have hq0 : ∀ j : Fin n, (0:ℝ) ≤ ∑ i, StabilityK3.centre A i j ^ 2 :=
    fun j => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hstep : gammaC' (StabilityK3.centre A)
      ≤ (1 - 1 / (n : ℝ)) * SigmaFour.YC (StabilityK3.centre A) := by
    rw [gammaC', SigmaFour.YC, Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    calc (∑ i, StabilityK3.centre A i j ^ 2) * (∑ i, StabilityK3.centre A i j ^ 3)
        ≤ (∑ i, StabilityK3.centre A i j ^ 2)
            * ((1 - 1 / (n : ℝ)) * ∑ i, StabilityK3.centre A i j ^ 2) :=
          mul_le_mul_of_nonneg_left (hf3 j) (hq0 j)
      _ = (1 - 1 / (n : ℝ)) * (∑ i, StabilityK3.centre A i j ^ 2) ^ 2 := by ring
  have hYC := StabilityK4.YC_le hA
  have hbeta0 : (0:ℝ) ≤ 1 - 1 / (n : ℝ) := by
    rcases Nat.eq_zero_or_pos n with rfl | hp
    · norm_num
    · have h0 : (1:ℝ) ≤ (n : ℝ) := by exact_mod_cast hp
      have : (0:ℝ) < (n : ℝ) := by linarith
      rw [sub_nonneg, div_le_one this]
      linarith
  nlinarith [mul_le_mul_of_nonneg_left hYC hbeta0]

/-! ## §4  Axiom audit

**Every declaration in this file depends only on axioms among `propext,
Classical.choice, Quot.sound`.**  No `native_decide`, no `sorry`. -/

section AxiomAudit

#print axioms quintic_ge
#print axioms cube_le
#print axioms quartic_le
#print axioms pFive
#print axioms gammaC
#print axioms gammaC'
#print axioms sum_quintic_ge
#print axioms sum_quartic_le
#print axioms pFive_ge
#print axioms inv_le_beta
#print axioms pFour_le
#print axioms frobQ_le
#print axioms frobQ_pThree_ge
#print axioms gammaC_le
#print axioms gammaC'_le

end AxiomAudit

end StabilityK5Atoms
