/-
# A stability form of Tverberg–Friedland at `k = 4`

Target: `graded_stability_lemma.md` Theorem 1 at `k = 4`, every `n ≥ 8`, discharging
`TverbergStability.StabilityAt 4 n`.

Unlike the `k ≤ 3` cells of `StabilityK3`, this one goes through the general layer identity:
`LayerIdentity.layer_identity_mul` at `k = 4` supplies

    σ₄(A) = C(n,4)² ( 4!/n⁴ + t₂σ₂(B) + t₃σ₃(B) + t₄σ₄(B) ),

and the three layers are then bounded below one at a time — `σ₂(B) = Q/2` exactly,
`σ₃(B) = (2/3)p₃ ≥ −(2/3n)Q` by the one-sided entry bound, and `σ₄(B) ≥ −(3/2)βQ` from (4.3)
by discarding its three nonnegative terms.

## The binding atom

Section 7 of the source records that `Y_R` (with `Y_C`) is what binds at `k = 4` for every `n`,
and that its estimate `Y_R ≤ MQ` is ATTAINED at the permutation matrices.  So the threshold `8`
cannot be lowered by sharpening anything here; it moves only by retaining the three nonnegative
terms of (4.3) that this assembly throws away.  Nothing below pretends otherwise.

## Correspondence to the source

| here | source |
|---|---|
| `row_sq_le`, `col_sq_le` | Lemma 3 (F2), `M ≤ 1 − 1/n` |
| `YR_le`, `YC_le` | Lemma 4(d), `Y_R ≤ MQ` and `Y_C ≤ MQ`, composed with (F2) |
| `pFour_nonneg`, `Zinv_nonneg` | Lemma 4(j) |
| `sigma_four_ge` | `C₄(n) = (3/2)β` of (7.1) |
| `stabilityAt_four` | Theorem 1 at `k = 4` |

`Φ(n,4) < 1` is consumed as the committed `TverbergStability.Phi4_lt_one`, whose statement is
(7.4) verbatim; `layer_ratio_lt` is the one bridge, checking that `Φ` rebuilt from
`tVal 4 n {2,3,4}` is exactly (7.4).
-/

import Mathlib.Tactic
import Mathlib.Data.Matrix.DoublyStochastic
import RookSum
import LayerIdentity
import SigmaFour
import StabilityK3
import GradedInequalities
import TverbergStability

open Finset

namespace StabilityK4

variable {n : ℕ}

/-! ## §1  Lemma 4(j): the three discarded terms are nonnegative -/

theorem pFour_nonneg (B : Matrix (Fin n) (Fin n) ℝ) : (0:ℝ) ≤ SigmaFour.pFour B :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity

theorem frobQ_nonneg (B : Matrix (Fin n) (Fin n) ℝ) : (0:ℝ) ≤ SigmaFour.frobQ B :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem Zinv_nonneg (B : Matrix (Fin n) (Fin n) ℝ) : (0:ℝ) ≤ SigmaFour.Zinv B :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- `Q` read down the columns. -/
theorem frobQ_cols (B : Matrix (Fin n) (Fin n) ℝ) :
    SigmaFour.frobQ B = ∑ j, ∑ i, B i j ^ 2 := Finset.sum_comm

/-! ## §2  Lemma 3 (F2) and Lemma 4(d)

`row_sq_le` is `GradedInequalities.centred_row_sq_le`, which needs only that the row is
nonnegative and sums to `1`; `col_sq_le` is the same lemma applied to a column. -/

theorem row_sq_le {A : Matrix (Fin n) (Fin n) ℝ} (hA : A ∈ doublyStochastic ℝ (Fin n))
    (i : Fin n) :
    (∑ j, StabilityK3.centre A i j ^ 2) ≤ 1 - 1 / (n : ℝ) :=
  GradedInequalities.centred_row_sq_le (fun j => A i j)
    (fun _ => nonneg_of_mem_doublyStochastic hA) (sum_row_of_mem_doublyStochastic hA i)

theorem col_sq_le {A : Matrix (Fin n) (Fin n) ℝ} (hA : A ∈ doublyStochastic ℝ (Fin n))
    (j : Fin n) :
    (∑ i, StabilityK3.centre A i j ^ 2) ≤ 1 - 1 / (n : ℝ) :=
  GradedInequalities.centred_row_sq_le (fun i => A i j)
    (fun _ => nonneg_of_mem_doublyStochastic hA) (sum_col_of_mem_doublyStochastic hA j)

/-- **Lemma 4(d) with (F2):** `Y_R ≤ βQ`.  Attained at the permutation matrices, so the
threshold cannot be lowered by improving this. -/
theorem YR_le {A : Matrix (Fin n) (Fin n) ℝ} (hA : A ∈ doublyStochastic ℝ (Fin n)) :
    SigmaFour.YR (StabilityK3.centre A)
      ≤ (1 - 1 / (n : ℝ)) * SigmaFour.frobQ (StabilityK3.centre A) :=
  GradedInequalities.sum_sq_le_max_mul_sum univ
    (fun i => ∑ j, StabilityK3.centre A i j ^ 2) (1 - 1 / (n : ℝ))
    (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (fun i _ => row_sq_le hA i)

theorem YC_le {A : Matrix (Fin n) (Fin n) ℝ} (hA : A ∈ doublyStochastic ℝ (Fin n)) :
    SigmaFour.YC (StabilityK3.centre A)
      ≤ (1 - 1 / (n : ℝ)) * SigmaFour.frobQ (StabilityK3.centre A) := by
  rw [frobQ_cols]
  exact GradedInequalities.sum_sq_le_max_mul_sum univ
    (fun j => ∑ i, StabilityK3.centre A i j ^ 2) (1 - 1 / (n : ℝ))
    (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (fun j _ => col_sq_le hA j)

/-! ## §3  `C₄(n) = (3/2)β`

The only negative terms of (4.3) are `−(3/4)(Y_R + Y_C)`; the other three are discarded by
Lemma 4(j).  This is (7.1)'s `C₄`. -/

theorem sigma_four_ge {A : Matrix (Fin n) (Fin n) ℝ} (hn : (n : ℝ) ≠ 0)
    (hA : A ∈ doublyStochastic ℝ (Fin n)) :
    -(3 / 2 * (1 - 1 / (n : ℝ)) * SigmaFour.frobQ (StabilityK3.centre A))
      ≤ RookSum.sigP 4 (StabilityK3.centre A) := by
  rw [SigmaFour.sigma_four_centred _
    (StabilityK3.centre_rows hn (sum_row_of_mem_doublyStochastic hA))
    (StabilityK3.centre_cols hn (sum_col_of_mem_doublyStochastic hA))]
  have h1 := pFour_nonneg (StabilityK3.centre A)
  have h2 := sq_nonneg (SigmaFour.frobQ (StabilityK3.centre A))
  have h3 := Zinv_nonneg (StabilityK3.centre A)
  have h4 := YR_le hA
  have h5 := YC_le hA
  linarith

/-! ## §4  The layer ratios at `k = 4`, and (7.4)

`layer_ratio_lt` is the single arithmetic bridge between the layer coefficients and the
committed threshold layer: it says that `t₃·C₃ + t₄·C₄ < t₂/4`, which is (7.2) at `k = 4`, and
it proves it by exhibiting the left side as `(t₂/4)·Φ(n,4)` with `Φ(n,4)` literally (7.4).

The ratio law (2.2) at symbolic `m` is NOT used: the three coefficients are evaluated directly
from `tVal`, as at `k = 3`. -/

theorem tVal_four_two {n : ℕ} (hn : 4 ≤ n) :
    TverbergStability.tVal 4 n 2 = 288 / ((n : ℝ) ^ 4 * ((n : ℝ) - 1) ^ 2) := by
  have hN : (4:ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h0 : (n : ℝ) ≠ 0 := by intro h; rw [h] at hN; norm_num at hN
  have h1 : (n : ℝ) - 1 ≠ 0 := by intro h; nlinarith
  rw [TverbergStability.tVal, TverbergStability.sVal,
    show Nat.descFactorial 4 2 = 12 from by norm_num [Nat.descFactorial],
    Nat.cast_descFactorial_two]
  norm_num [Nat.factorial]
  field_simp
  ring

theorem tVal_four_three {n : ℕ} (hn : 4 ≤ n) :
    TverbergStability.tVal 4 n 3
      = 576 / ((n : ℝ) ^ 3 * ((n : ℝ) - 1) ^ 2 * ((n : ℝ) - 2) ^ 2) := by
  have hN : (4:ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h0 : (n : ℝ) ≠ 0 := by intro h; rw [h] at hN; norm_num at hN
  have h1 : (n : ℝ) - 1 ≠ 0 := by intro h; nlinarith
  have h2 : (n : ℝ) - 2 ≠ 0 := by intro h; nlinarith
  rw [TverbergStability.tVal, TverbergStability.sVal,
    show Nat.descFactorial 4 3 = 24 from by norm_num [Nat.descFactorial],
    StabilityK3.cast_descFactorial_three (by omega)]
  norm_num [Nat.factorial]
  field_simp
  ring

theorem tVal_four_four {n : ℕ} (hn : 4 ≤ n) :
    TverbergStability.tVal 4 n 4
      = 576 / ((n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2) * ((n : ℝ) - 3)) ^ 2 := by
  have hN : (4:ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h0 : (n : ℝ) ≠ 0 := by intro h; rw [h] at hN; norm_num at hN
  have h1 : (n : ℝ) - 1 ≠ 0 := by intro h; nlinarith
  have h2 : (n : ℝ) - 2 ≠ 0 := by intro h; nlinarith
  have h3 : (n : ℝ) - 3 ≠ 0 := by intro h; nlinarith
  have hdf : ((n.descFactorial 4 : ℕ) : ℝ)
      = (n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2) * ((n : ℝ) - 3) := by
    obtain ⟨i, rfl⟩ : ∃ i, n = i + 4 := ⟨n - 4, by omega⟩
    simp [Nat.descFactorial_succ]
    ring
  rw [TverbergStability.tVal, TverbergStability.sVal,
    show Nat.descFactorial 4 4 = 24 from by norm_num [Nat.descFactorial], hdf]
  norm_num [Nat.factorial]
  field_simp
  ring

/-- **(7.2) at `k = 4`.**  `t₃C₃ + t₄C₄ < t₂/4`, by exhibiting the left side as `(t₂/4)Φ(n,4)`
with `Φ(n,4)` exactly (7.4), and appealing to the committed `Phi4_lt_one`. -/
theorem layer_ratio_lt {n : ℕ} (hn : 8 ≤ n) :
    TverbergStability.tVal 4 n 3 * (2 / (3 * (n : ℝ)))
        + TverbergStability.tVal 4 n 4 * (3 / 2 * (1 - 1 / (n : ℝ)))
      < TverbergStability.tVal 4 n 2 / 4 := by
  have hN : (8:ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h0 : (n : ℝ) ≠ 0 := by intro h; rw [h] at hN; norm_num at hN
  have h1 : (n : ℝ) - 1 ≠ 0 := by intro h; nlinarith
  have h2 : (n : ℝ) - 2 ≠ 0 := by intro h; nlinarith
  have h3 : (n : ℝ) - 3 ≠ 0 := by intro h; nlinarith
  have hfac : (0:ℝ) < 72 / ((n : ℝ) ^ 4 * ((n : ℝ) - 1) ^ 2) := by
    apply div_pos (by norm_num)
    have : (0:ℝ) < (n : ℝ) := by linarith
    positivity
  have hPhi := TverbergStability.Phi4_lt_one (n := (n : ℝ)) hN
  have hid : TverbergStability.tVal 4 n 3 * (2 / (3 * (n : ℝ)))
        + TverbergStability.tVal 4 n 4 * (3 / 2 * (1 - 1 / (n : ℝ)))
      = (72 / ((n : ℝ) ^ 4 * ((n : ℝ) - 1) ^ 2))
        * (16 / (3 * ((n : ℝ) - 2) ^ 2)
            + 12 * (n : ℝ) * ((n : ℝ) - 1) / (((n : ℝ) - 2) ^ 2 * ((n : ℝ) - 3) ^ 2)) := by
    rw [tVal_four_three (by omega), tVal_four_four (by omega)]
    field_simp
    ring
  have hrhs : TverbergStability.tVal 4 n 2 / 4
      = (72 / ((n : ℝ) ^ 4 * ((n : ℝ) - 1) ^ 2)) * 1 := by
    rw [tVal_four_two (by omega)]
    field_simp
    ring
  rw [hid, hrhs]
  exact mul_lt_mul_of_pos_left hPhi hfac

/-! ## §5  Theorem 1 at `k = 4`, every `n ≥ 8` -/

/-- **Theorem 1 at `k = 4`, every `n ≥ 8`.** -/
theorem stabilityAt_four {n : ℕ} (hn : 8 ≤ n) : TverbergStability.StabilityAt 4 n := by
  intro A hA
  have hN : (8:ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h0 : (n : ℝ) ≠ 0 := by intro h; rw [h] at hN; norm_num at hN
  have hnpos : (0:ℝ) < (n : ℝ) := by linarith
  have hr := StabilityK3.centre_rows h0 (sum_row_of_mem_doublyStochastic hA)
  have hc := StabilityK3.centre_cols h0 (sum_col_of_mem_doublyStochastic hA)
  have hB : ∑ i, ∑ j, StabilityK3.centre A i j = 0 := by
    rw [Finset.sum_congr rfl fun i _ => hr i]; simp
  -- Lemma 2 at k = 4
  have hL := LayerIdentity.layer_identity_mul (n := n) (k := 4) (by omega) (by omega)
    A (StabilityK3.centre A) (fun i j => by rw [StabilityK3.centre_apply]; ring) hB
  have hIcc : (Finset.Icc 2 4 : Finset ℕ) = {2, 3, 4} := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]; omega
  rw [hIcc, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton] at hL
  -- the three layers
  have hs2 : RookSum.sigP 2 (StabilityK3.centre A)
      = SigmaFour.frobQ (StabilityK3.centre A) / 2 := StabilityK3.sigma_two_centred hr hc
  have hs3 : RookSum.sigP 3 (StabilityK3.centre A)
      = 2 / 3 * ∑ i, ∑ j, StabilityK3.centre A i j ^ 3 :=
    StabilityK3.sigma_three_centred hr hc
  have hp3 : -(1 / (n : ℝ) * SigmaFour.frobQ (StabilityK3.centre A))
      ≤ ∑ i, ∑ j, StabilityK3.centre A i j ^ 3 :=
    StabilityK3.sum_cube_ge (B := StabilityK3.centre A)
      (fun i j => StabilityK3.entry_lower hA i j)
  have hs4 := sigma_four_ge h0 hA
  have hQ0 : (0:ℝ) ≤ SigmaFour.frobQ (StabilityK3.centre A) :=
    frobQ_nonneg (StabilityK3.centre A)
  -- the coefficient identity and the threshold
  have hcv : TverbergStability.cVal 4 n = TverbergStability.tVal 4 n 2 / 4 :=
    TverbergStability.cVal_eq_tVal_div_four (by omega) (by omega)
  have ht2pos : (0:ℝ) < TverbergStability.tVal 4 n 2 := by
    rw [tVal_four_two (by omega)]
    have h1 : (n : ℝ) - 1 ≠ 0 := by intro h; nlinarith
    apply div_pos (by norm_num)
    positivity
  have ht3pos : (0:ℝ) < TverbergStability.tVal 4 n 3 := by
    rw [tVal_four_three (by omega)]
    have h1 : (0:ℝ) < ((n : ℝ) - 1) ^ 2 := by nlinarith
    have h2 : (0:ℝ) < ((n : ℝ) - 2) ^ 2 := by nlinarith
    apply div_pos (by norm_num)
    positivity
  have ht4pos : (0:ℝ) < TverbergStability.tVal 4 n 4 := by
    rw [tVal_four_four (by omega)]
    have q1 : (0:ℝ) < (n : ℝ) := by linarith
    have q2 : (0:ℝ) < (n : ℝ) - 1 := by linarith
    have q3 : (0:ℝ) < (n : ℝ) - 2 := by linarith
    have q4 : (0:ℝ) < (n : ℝ) - 3 := by linarith
    have : (0:ℝ) < (n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2) * ((n : ℝ) - 3) :=
      mul_pos (mul_pos (mul_pos q1 q2) q3) q4
    exact div_pos (by norm_num) (by positivity)
  have hratio := layer_ratio_lt (n := n) hn
  have hcpos : (0:ℝ) < ((n.choose 4 : ℕ) : ℝ) ^ 2 := by
    have hpos := Nat.choose_pos (show 4 ≤ n from by omega)
    have hne : ((n.choose 4 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    positivity
  -- the three layer bounds, each a scalar multiple of a committed inequality
  have A1 : -(TverbergStability.tVal 4 n 3 * (2 / (3 * (n : ℝ)))
        * SigmaFour.frobQ (StabilityK3.centre A))
      ≤ TverbergStability.tVal 4 n 3 * (2 / 3 * ∑ i, ∑ j, StabilityK3.centre A i j ^ 3) := by
    have h := mul_le_mul_of_nonneg_left hp3 (le_of_lt ht3pos)
    have hrw : TverbergStability.tVal 4 n 3 * (2 / (3 * (n : ℝ)))
        = 2 / 3 * (TverbergStability.tVal 4 n 3 * (1 / (n : ℝ))) := by
      field_simp; ring
    rw [hrw]
    linarith [h]
  have A2 : -(TverbergStability.tVal 4 n 4 * (3 / 2 * (1 - 1 / (n : ℝ)))
        * SigmaFour.frobQ (StabilityK3.centre A))
      ≤ TverbergStability.tVal 4 n 4 * RookSum.sigP 4 (StabilityK3.centre A) := by
    have h := mul_le_mul_of_nonneg_left hs4 (le_of_lt ht4pos)
    linarith [h]
  have A3 : (TverbergStability.tVal 4 n 3 * (2 / (3 * (n : ℝ)))
        + TverbergStability.tVal 4 n 4 * (3 / 2 * (1 - 1 / (n : ℝ))))
        * SigmaFour.frobQ (StabilityK3.centre A)
      ≤ TverbergStability.tVal 4 n 2 / 4 * SigmaFour.frobQ (StabilityK3.centre A) :=
    mul_le_mul_of_nonneg_right (le_of_lt hratio) hQ0
  have hlayer :
      TverbergStability.tVal 4 n 2 / 4 * SigmaFour.frobQ (StabilityK3.centre A)
        ≤ TverbergStability.tVal 4 n 2 * (SigmaFour.frobQ (StabilityK3.centre A) / 2)
          + (TverbergStability.tVal 4 n 3
                * (2 / 3 * ∑ i, ∑ j, StabilityK3.centre A i j ^ 3)
            + TverbergStability.tVal 4 n 4 * RookSum.sigP 4 (StabilityK3.centre A)) := by
    linarith [A1, A2, A3]
  -- isolate the cancellation of the `m = 0` term
  have hQeq : (∑ i, ∑ j, (A i j - 1 / (n : ℝ)) ^ 2)
      = SigmaFour.frobQ (StabilityK3.centre A) := rfl
  have key : RookSum.sigP 4 A
        - ((n.choose 4 : ℕ) : ℝ) ^ 2 * ((Nat.factorial 4 : ℕ) : ℝ) / (n : ℝ) ^ 4
      = ((n.choose 4 : ℕ) : ℝ) ^ 2
        * (TverbergStability.tVal 4 n 2 * RookSum.sigP 2 (StabilityK3.centre A)
          + (TverbergStability.tVal 4 n 3 * RookSum.sigP 3 (StabilityK3.centre A)
            + TverbergStability.tVal 4 n 4 * RookSum.sigP 4 (StabilityK3.centre A))) := by
    rw [hL]; ring
  rw [key, hcv, hQeq, hs2, hs3]
  linarith [mul_le_mul_of_nonneg_left hlayer (le_of_lt hcpos)]

/-! ## §6  Axiom audit

**Every declaration in this file depends only on axioms among `propext,
Classical.choice, Quot.sound`.**  No `native_decide`, no `sorry`. -/

section AxiomAudit

#print axioms pFour_nonneg
#print axioms frobQ_nonneg
#print axioms Zinv_nonneg
#print axioms frobQ_cols
#print axioms row_sq_le
#print axioms col_sq_le
#print axioms YR_le
#print axioms YC_le
#print axioms sigma_four_ge
#print axioms tVal_four_two
#print axioms tVal_four_three
#print axioms tVal_four_four
#print axioms layer_ratio_lt
#print axioms stabilityAt_four

end AxiomAudit

end StabilityK4
