/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.Tactic

/-!
# Cofactor expansion for the permanent

`Matrix.permanent` currently ships without any cofactor (Laplace) expansion,
although `Matrix.det` provides four: `det_succ_column_zero`, `det_succ_row_zero`,
`det_succ_row` and `det_succ_column`. This file supplies the four permanent
analogues.

The absence is not cosmetic: without an expansion the permanent does not compute.
`decide` stalls on `permsOfList` for `Equiv.Perm (Fin 3)`, and `simp` has no route
into a sum over `Equiv.Perm (Fin n)`.

## Main results

* `Matrix.permanent_succ_column_zero`: expansion along column `0`
* `Matrix.permanent_succ_row_zero`: expansion along row `0`
* `Matrix.permanent_succ_column`: expansion along an arbitrary column
* `Matrix.permanent_succ_row`: expansion along an arbitrary row

## Implementation notes

The proofs are markedly shorter than the determinant analogues, for a structural
reason: with no alternating signs, the entire `Equiv.Perm.sign` bookkeeping that
dominates `det_succ_column_zero` disappears. The permanent, usually the harder of
the two to evaluate, is the easier to expand.

The row versions are obtained from the column versions by transposing, using
`Matrix.permanent_transpose`.
-/

namespace Matrix

open Finset

variable {R : Type*} [CommRing R] {n : ℕ}

/-- **Cofactor expansion of the permanent along column `0`.**

`per A = ∑ i, A i 0 * per (A(i|0))`. -/
theorem permanent_succ_column_zero (A : Matrix (Fin n.succ) (Fin n.succ) R) :
    permanent A = ∑ i : Fin n.succ, A i 0 * permanent (A.submatrix i.succAbove Fin.succ) := by
  rw [Matrix.permanent, Finset.univ_perm_fin_succ, ← Finset.univ_product_univ]
  simp only [Finset.sum_map, Equiv.toEmbedding_apply, Finset.sum_product, Matrix.submatrix]
  refine Finset.sum_congr rfl fun i _ => Fin.cases ?_ (fun i => ?_) i
  · rw [Matrix.permanent, Finset.mul_sum]
    exact Finset.sum_congr rfl fun σ _ => by simp [Fin.prod_univ_succ]
  · rw [Matrix.permanent, Finset.mul_sum]
    exact Fintype.sum_equiv (Equiv.mulLeft i.cycleRange) _ _ (fun σ => by
      simp [Fin.prod_univ_succ, Fin.succAbove_cycleRange])

/-- **Cofactor expansion of the permanent along an arbitrary column `j`.** -/
theorem permanent_succ_column (A : Matrix (Fin n.succ) (Fin n.succ) R) (j : Fin n.succ) :
    permanent A =
      ∑ i : Fin n.succ, A i j * permanent (A.submatrix i.succAbove j.succAbove) := by
  rw [← Matrix.permanent_permute_rows j.cycleRange.symm A, permanent_succ_column_zero]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Matrix.submatrix, Matrix.of_apply, id, Fin.cycleRange_symm_zero,
    Fin.cycleRange_symm_succ]

/-- **Cofactor expansion of the permanent along row `0`.**

`per A = ∑ j, A 0 j * per (A(0|j))`. -/
theorem permanent_succ_row_zero (A : Matrix (Fin n.succ) (Fin n.succ) R) :
    permanent A = ∑ j : Fin n.succ, A 0 j * permanent (A.submatrix Fin.succ j.succAbove) := by
  rw [← permanent_transpose A, permanent_succ_column_zero]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Matrix.transpose_submatrix, permanent_transpose]
  rfl

/-- **Cofactor expansion of the permanent along an arbitrary row `i`.** -/
theorem permanent_succ_row (A : Matrix (Fin n.succ) (Fin n.succ) R) (i : Fin n.succ) :
    permanent A =
      ∑ j : Fin n.succ, A i j * permanent (A.submatrix i.succAbove j.succAbove) := by
  rw [← permanent_transpose A, permanent_succ_column _ i]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Matrix.transpose_submatrix, permanent_transpose]
  rfl

/-! ## Sanity checks -/

example (A : Matrix (Fin 1) (Fin 1) R) : permanent A = A 0 0 := by
  simp [permanent_succ_column_zero, Matrix.permanent_isEmpty]

example (A : Matrix (Fin 2) (Fin 2) R) :
    permanent A = A 0 0 * A 1 1 + A 1 0 * A 0 1 := by
  simp [permanent_succ_column_zero, Fin.sum_univ_succ, Matrix.permanent_isEmpty,
    Matrix.submatrix_apply]

/-- The permanent of the all-ones `3 x 3` matrix is `3! = 6`. -/
example : permanent (fun _ _ => (1 : ℚ) : Matrix (Fin 3) (Fin 3) ℚ) = 6 := by
  simp only [permanent_succ_column_zero, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Matrix.submatrix_apply, Matrix.permanent_isEmpty]
  norm_num

#print axioms permanent_succ_column_zero
#print axioms permanent_succ_column
#print axioms permanent_succ_row_zero
#print axioms permanent_succ_row

end Matrix
