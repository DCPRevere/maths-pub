/-
# Lemma B6, the entropy witness — `LEAN-ROADMAP.md` stone 6 (inventory A3)

`LIFT.md` §B.10.1:

> **Lemma B6.**  Let `M >= 0` be `N x N` and `W` doubly stochastic with `supp W ⊆ supp M`.
> Then `cap(M) >= prod_{i,j} (M_ij / W_ij)^{W_ij}`.

This is the lower-bound half of the capacity machinery, and — as `LEAN-ROADMAP.md` A3 records —
it is OURS and elementary: it needs weighted AM–GM (A2) and nothing else.  Only the easy half of
the scaling duality is used, so no Sinkhorn theory is load-bearing anywhere.

It is stone 6 on the keystone path `2 → 3 → 6 → 7 → 11 → 12 → 13 → 14 → 15 → 20 → 23`, and it
is the ★ stone that stones 7 (the witness `W` of §B.11.2) and 16 (Egorychev–Falikman) both
consume.

## The proof, in one line per step

At `x > 0`, row `i` of `Mx` is `∑_j W_ij · (M_ij x_j / W_ij)`, an average with weights `W_ij`
summing to `1`.  Weighted AM–GM drops it to `∏_j (M_ij x_j/W_ij)^{W_ij}`.  Multiplying over `i`
and using that the COLUMN sums of `W` are `1` collects `∏_i ∏_j x_j^{W_ij} = ∏_j x_j`, which is
exactly the capacity denominator; what is left over is the witness.

## Two conventions that carry the degenerate entries, and are not accidents

* `W_ij = 0`.  Lean reads `M_ij x_j / 0` as `0` and `t ^ (0:ℝ)` as `1`, so such a `j` contributes
  `1` to the product and `0` to the sum — and `0 ≤ M_ij x_j` closes the gap.  The support
  hypothesis `supp W ⊆ supp M` of `LIFT.md` is therefore **not needed for the inequality**, and
  is omitted below.  What it buys is non-vacuity: without it a `W_ij > 0` sitting on `M_ij = 0`
  makes the witness `0` and the bound empty.
* `M_ij = W_ij = 0`.  Then `(M_ij/W_ij)^{W_ij} = (0/0)^0 = 0^0 = 1`, the right value — which is
  why `entropyWitness_self` below is `1` on the nose, with no support side condition.

## The corollary that closes half of Lemma K1

`LIFT.md` §B.14.2 proves `cap(A) = 1` on `Ω_n` from Lemma B6 with `W = A`.  That direction lands
here as `one_le_cap_rowProd_of_doublyStochastic`, and together with `Capacity.cap_rowProd_le_one`
it gives `cap_rowProd_eq_one_of_doublyStochastic` — the `⇐` half of Lemma K1's equality
characterisation, which `Capacity.lean` had recorded as deferred.  The `⇒` half still needs
`cap(A) = cap(Aᵀ)` and is still owed.
-/

import Mathlib.Tactic
import Mathlib.Analysis.MeanInequalities
import Capacity

open Finset

namespace LemmaB6

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The entropy witness `∏_{i,j} (M_ij / W_ij)^{W_ij}` of `LIFT.md` §B.10.1. -/
noncomputable def entropyWitness (M W : Matrix ι κ ℝ) : ℝ :=
  ∏ i, ∏ j, (M i j / W i j) ^ (W i j)

theorem entropyWitness_nonneg (M W : Matrix ι κ ℝ) (hM : ∀ i j, 0 ≤ M i j)
    (hW : ∀ i j, 0 ≤ W i j) : 0 ≤ entropyWitness M W :=
  Finset.prod_nonneg fun i _ =>
    Finset.prod_nonneg fun j _ => Real.rpow_nonneg (div_nonneg (hM i j) (hW i j)) _

/-- **`LIFT.md` §B.14.2's `∏_{i,j} (A_ij/A_ij)^{A_ij} = 1`.**  True with no support hypothesis:
the vanishing entries give `(0/0)^0 = 0^0 = 1`, which is the value the identity needs. -/
@[simp] theorem entropyWitness_self (A : Matrix ι κ ℝ) : entropyWitness A A = 1 := by
  refine Finset.prod_eq_one fun i _ => Finset.prod_eq_one fun j _ => ?_
  rcases eq_or_ne (A i j) 0 with h | h
  · rw [h]
    simp
  · rw [div_self h, Real.one_rpow]

/-! ## §1  The row estimate

One application of weighted AM–GM per row of `M`, with the row of `W` as the weight vector. -/

omit [Fintype ι] in
/-- Row `i`, with the two conventions of the header carried explicitly. -/
theorem row_bound (M W : Matrix ι κ ℝ) (hM : ∀ i j, 0 ≤ M i j) (hW : ∀ i j, 0 ≤ W i j)
    (hrow : ∀ i, ∑ j, W i j = 1) {x : κ → ℝ} (hx : ∀ j, 0 < x j) (i : ι) :
    (∏ j, (M i j / W i j) ^ (W i j)) * (∏ j, (x j) ^ (W i j)) ≤ ∑ j, M i j * x j := by
  have hz : ∀ j : κ, (0 : ℝ) ≤ M i j * x j / W i j :=
    fun j => div_nonneg (mul_nonneg (hM i j) (hx j).le) (hW i j)
  have hAM := Real.geom_mean_le_arith_mean_weighted (univ : Finset κ) (fun j => W i j)
    (fun j => M i j * x j / W i j) (fun j _ => hW i j) (hrow i) (fun j _ => hz j)
  have hsplit : ∏ j, (M i j * x j / W i j) ^ (W i j)
      = (∏ j, (M i j / W i j) ^ (W i j)) * (∏ j, (x j) ^ (W i j)) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [← Real.mul_rpow (div_nonneg (hM i j) (hW i j)) (hx j).le]
    congr 1
    rw [div_mul_eq_mul_div]
  have hdrop : ∑ j, W i j * (M i j * x j / W i j) ≤ ∑ j, M i j * x j := by
    refine Finset.sum_le_sum fun j _ => ?_
    rcases eq_or_lt_of_le (hW i j) with h | h
    · rw [← h]
      simp only [zero_mul]
      exact mul_nonneg (hM i j) (hx j).le
    · rw [mul_div_cancel₀ _ h.ne']
  rw [← hsplit]
  exact hAM.trans hdrop

/-! ## §2  Lemma B6 -/

/-- **LEMMA B6** (`LIFT.md` §B.10.1, roadmap inventory A3).  For `M ≥ 0` and `W` doubly
stochastic,

    cap(p_M)  ≥  ∏_{i,j} (M_ij / W_ij)^{W_ij} .

Weighted AM–GM per row, then the column sums of `W` collect the capacity denominator.  No
support hypothesis is needed for the inequality (see the header); no scaling duality is used. -/
theorem lemmaB6 (M W : Matrix ι κ ℝ) (hM : ∀ i j, 0 ≤ M i j) (hW : ∀ i j, 0 ≤ W i j)
    (hrow : ∀ i, ∑ j, W i j = 1) (hcol : ∀ j, ∑ i, W i j = 1) :
    entropyWitness M W ≤ Capacity.cap (fun _ => (1 : ℝ)) (Capacity.rowProd M) := by
  refine Capacity.le_cap fun x hx => ?_
  have hxprod : (0 : ℝ) < ∏ j, x j := Finset.prod_pos fun j _ => hx j
  rw [Capacity.monom_one_exp, le_div_iff₀ hxprod]
  -- The witness times the capacity denominator is a product of the row estimates' left sides.
  have hcollect : ∏ i, ∏ j, (x j) ^ (W i j) = ∏ j, x j := by
    rw [Finset.prod_comm]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [← Real.rpow_sum_of_pos (hx j), hcol j, Real.rpow_one]
  have hkey : entropyWitness M W * (∏ j, x j)
      = ∏ i, ((∏ j, (M i j / W i j) ^ (W i j)) * (∏ j, (x j) ^ (W i j))) := by
    rw [Finset.prod_mul_distrib, hcollect, entropyWitness]
  rw [hkey, Capacity.rowProd]
  refine Finset.prod_le_prod (fun i _ => ?_) (fun i _ => row_bound M W hM hW hrow hx i)
  exact mul_nonneg
    (Finset.prod_nonneg fun j _ => Real.rpow_nonneg (div_nonneg (hM i j) (hW i j)) _)
    (Finset.prod_nonneg fun j _ => Real.rpow_nonneg (hx j).le _)

/-! ## §3  The corollary on the doubly stochastic face

`LIFT.md` §B.14.2: "Conversely Lemma B6 with `W = A` gives `cap >= prod_ij (A_ij/A_ij)^{A_ij}
= 1`."  With `Capacity.cap_rowProd_le_one` this is `cap = 1` on `Ω_n`. -/

/-- Lemma B6 at `W = A`: the capacity of a doubly stochastic matrix is at least `1`. -/
theorem one_le_cap_rowProd_of_doublyStochastic (A : Matrix ι κ ℝ) (hA : ∀ i j, 0 ≤ A i j)
    (hrow : ∀ i, ∑ j, A i j = 1) (hcol : ∀ j, ∑ i, A i j = 1) :
    1 ≤ Capacity.cap (fun _ => (1 : ℝ)) (Capacity.rowProd A) := by
  have h := lemmaB6 A A hA hA hrow hcol
  rwa [entropyWitness_self] at h

/-- **Half of Lemma K1's equality characterisation.**  `A ∈ Ω_n ⟹ cap(p_A) = 1`.  The converse
still needs `cap(A) = cap(Aᵀ)` and is still owed (`Capacity.lean` header). -/
theorem cap_rowProd_eq_one_of_doublyStochastic (A : Matrix ι ι ℝ) (hA : ∀ i j, 0 ≤ A i j)
    (hrow : ∀ i, ∑ j, A i j = 1) (hcol : ∀ j, ∑ i, A i j = 1) :
    Capacity.cap (fun _ => (1 : ℝ)) (Capacity.rowProd A) = 1 := by
  refine le_antisymm ?_ (one_le_cap_rowProd_of_doublyStochastic A hA hrow hcol)
  refine Capacity.cap_rowProd_le_one A hA ?_
  calc ∑ i, ∑ j, A i j = ∑ _i : ι, (1 : ℝ) := Finset.sum_congr rfl fun i _ => hrow i
    _ = (Fintype.card ι : ℝ) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]

section AxiomAudit

#print axioms entropyWitness
#print axioms entropyWitness_nonneg
#print axioms entropyWitness_self
#print axioms row_bound
#print axioms lemmaB6
#print axioms one_le_cap_rowProd_of_doublyStochastic
#print axioms cap_rowProd_eq_one_of_doublyStochastic

end AxiomAudit

end LemmaB6
