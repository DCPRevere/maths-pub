/-
# Support inequalities for a graded layer decomposition

**This file is library material, not application material.**  It mentions no permanent and
nothing from the sub-Dittert development; it imports only Mathlib, and it must stay that way.
Everything below is a statement about real vectors and real matrices, and each one is a
candidate for upstreaming.

## What is proved

* §1 **`sum_cube_sq_le`** — `(∑ b³)² ≤ (∑ b²)(∑ b⁴)`, Cauchy–Schwarz with the pair
  `(b, b²)`, plus the double-sum form used for matrix entries.
* §2 **`ratio_le_two`** — `(k−2)(n−3)² ≤ 2(k−3)(n−2)²` for `4 ≤ k ≤ n`, and the corollary
  **`ratio_le_27_8`** in the `8 : 27` form.  Stated over `ℝ`, never over `ℕ`: with truncated
  natural subtraction `k − 3` is `0` at `k = 3` and the inequality would degenerate silently.
* §3 the four mixed quadratic bounds: **`sum_weighted_col_sq_le`**,
  **`sum_weighted_row_sq_le`**, **`sq_bilinear_le`**, **`sq_bilinear_sq_left_le`**,
  **`sq_bilinear_sq_right_le`**, each with a corollary specialised to the row and column
  sums so that the correspondence to the source inequality is checked by the kernel rather
  than asserted in a comment.
* §4 **`sum_sq_le_max_mul_sum`** (`∑ q² ≤ M ∑ q` when `0 ≤ q ≤ M`) and the centred row
  bound **`centred_row_sq_le`**, with the exact identity **`centred_row_sq_eq`** that
  relates it to the uncentred row, and **`centred_row_sq_eq_of_indicator`** showing the
  bound is attained.
* §5 **`sq_le_of_polygon`** (the polygon bound, with `zero_sum_sq_le` as its zero-sum
  corollary and **`row_sq_le_of_colSum_zero`** as its row-norm corollary — the two uses that
  look alike and are not), then **`zero_sum_cube_le`** and **`zero_sum_cube_abs_le`** — the sharp zero-sum cubic
  inequality `|∑ x³| ≤ κ(n) (∑ x²)^{3/2}` with `κ(n) = (n−2)/√(n(n−1))`, together with the
  square-free form **`zero_sum_cube_sq_le`** for callers who would rather not meet `rpow`.

## The proof of §5, and why no two-value reduction appears

The usual argument maximises `∑ x³` on the sphere intersected with the zero-sum hyperplane
by a Lagrange condition, finds the extremiser takes two values, and evaluates.  That route
needs analysis.  It is replaced here by a tangent-cubic argument that is entirely algebraic:

1. `sq_le_of_polygon`, and its zero-sum corollary `zero_sum_sq_le`: `n xᵢ² ≤ (n−1) ∑ x²`, by
   Chebyshev's `sq_sum_le_card_mul_sum_sq` applied to the complement of `i`.  So every
   coordinate is at most `u := (n−1)·s/D` with `s := √(∑ x²)` and `D := √(n(n−1))`.
2. `sum_cube_le_of_le`: for any `u` dominating every coordinate and **any** `v`, the
   factorisation `(xᵢ − u)(xᵢ − v)² ≤ 0` gives a pointwise cubic bound, and summing it
   annihilates the linear term because `∑ x = 0`.
3. Choosing `v := −s/D` — the small value of the two-value extremiser — makes the resulting
   bound collapse to exactly `κ(n)·s³`, using only `D² = n(n−1)`.

So the two-value extremiser still governs the constant, but it enters as the choice of the
tangency point `v` in step 3, where it costs one `linear_combination`, instead of as the
conclusion of an optimisation.  Sharpness is not claimed inside Lean; it is witnessed
externally by the vector `(n−1, −1, …, −1)`.

The same inequality, with the same constant, also has an independent proof by the Lagrange
two-value reduction.  Of the two routes only the elementary one above formalises directly,
which is why it is the one here; the agreement of two unrelated derivations is the reason to
trust the constant rather than merely the proof.  Step 1 is of independent use, and is stated
in its general form for that reason: `sq_le_of_polygon` assumes only `0 ≤ xᵢ` and the polygon
condition `xᵢ ≤ ∑_{j ≠ i} xⱼ`, which covers both a vector of **norms** — nonnegative, not
zero-sum, polygon condition from the triangle inequality — and the **zero-sum** case, which
meets the hypothesis only after passing to absolute values.  The two are not the same
hypothesis, and reading one as the other is a mistake this file is arranged to prevent.
Both corollaries are proved here, from the one general lemma: `zero_sum_sq_le` for the
zero-sum case and `row_sq_le_of_colSum_zero` for the row-norm case, the latter with
`rowNorm_polygon` discharging the polygon hypothesis from vanishing column sums alone.

## Correspondence to the source inequalities

Symbols: `b` a real matrix, `R i = ∑ j, b i j` the row sums, `C j = ∑ i, b i j` the column
sums, and

    Q = ∑ᵢⱼ bᵢⱼ²      p2R = ∑ᵢ Rᵢ²      p2C = ∑ⱼ Cⱼ²      p3b = ∑ᵢⱼ bᵢⱼ³      p4b = ∑ᵢⱼ bᵢⱼ⁴

| here | source inequality |
|---|---|
| `sum_cube_sq_le_matrix` | `p3b² ≤ Q · p4b` |
| `ratio_le_27_8` | `8(k−2)(n−3)² ≤ 27(k−3)(n−2)²` |
| `sum_weighted_col_sq_le_rowSum` | `∑ⱼ (∑ᵢ Rᵢbᵢⱼ)² ≤ Q · p2R` |
| `sum_weighted_row_sq_le_colSum` | `∑ᵢ (∑ⱼ Cⱼbᵢⱼ)² ≤ Q · p2C` |
| `sq_bilinear_le_lineSum` | `W² ≤ p2R · p2C · Q`, for `W = ∑ᵢⱼ RᵢbᵢⱼCⱼ` |
| `sq_bilinear_sq_left_le_lineSum` | `W4R² ≤ p2R² · p2C · Q`, for `W4R = ∑ᵢⱼ Rᵢ²bᵢⱼCⱼ` |
| `sq_bilinear_sq_right_le_lineSum` | `W4C² ≤ p2C² · p2R · Q`, for `W4C = ∑ᵢⱼ RᵢbᵢⱼCⱼ²` |
| `sum_sq_le_max_mul_sum` | `YR = ∑ᵢ qᵢ² ≤ M · Q`, for `qᵢ = ∑ⱼ bᵢⱼ²`, `M = maxᵢ qᵢ` |
| `centred_row_sq_le` | `M ≤ 1 − 1/n` for `b = A − J/n`, `A` on the Birkhoff slice |
| `zero_sum_cube_abs_le` | `|∑ x³| ≤ κ(n) (∑ x²)^{3/2}`, `κ(n) = (n−2)/√(n(n−1))` |

Two of these deserve a note, because in each case the shortest reading of the source is the
wrong one.

**`centred_row_sq_le` is a statement about the CENTRED matrix.**  The quantity bounded by
`1 − 1/n` is `qᵢ = ∑ⱼ (Aᵢⱼ − 1/n)²`, not `∑ⱼ Aᵢⱼ²`.  The uncentred reading is false: a
permutation row gives `∑ⱼ Aᵢⱼ² = 1 > 1 − 1/n`.  `centred_row_sq_eq` is the one-line identity
`∑ⱼ (Aᵢⱼ − 1/n)² = ∑ⱼ Aᵢⱼ² − 1/n` that separates the two, and it shows what the bound really
asks for, namely `∑ⱼ Aᵢⱼ² ≤ 1`.  Only row `i`'s stochasticity is used, so double
stochasticity is not needed for this piece.  `centred_row_sq_eq_of_indicator` records that
`1 − 1/n` is attained, at every permutation row, so the constant cannot be improved.

**`sq_bilinear_sq_left_le` does not go through a maximum.**  The source chain for `W4R`
(`results/graded_mixed.log` line 363) passes through `|W4R| ≤ maxᵢ|Rᵢ| · |W|`, and **that step
is false as written** — `W` is a signed sum, so a factor cannot be pulled through it by a
maximum; the worst measured margin is `−7.4·10²`, so it is not a borderline failure.  That
line must never be transcribed.  The endpoint `W4R² ≤ p2R² · p2C · Q` is nevertheless true,
and is proved here by a
shorter route that needs no maximum at all: bound `|W4R| ≤ ∑ᵢⱼ Rᵢ²|bᵢⱼ||Cⱼ|`, apply
Cauchy–Schwarz once on the pair index `(i, j)`, then use `∑ᵢ Rᵢ⁴ ≤ (∑ᵢ Rᵢ²)²`.  One
Cauchy–Schwarz replaces two, and the intermediate quantity that made the original chain
unsound never appears.
-/

import Mathlib.Tactic
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Finset

namespace GradedInequalities

/-! ## §1  The cube Cauchy–Schwarz -/

/-- `(∑ b³)² ≤ (∑ b²)(∑ b⁴)`: Cauchy–Schwarz applied to the pair `(b, b²)`. -/
theorem sum_cube_sq_le {ι : Type*} (s : Finset ι) (b : ι → ℝ) :
    (∑ i ∈ s, b i ^ 3) ^ 2 ≤ (∑ i ∈ s, b i ^ 2) * ∑ i ∈ s, b i ^ 4 := by
  calc (∑ i ∈ s, b i ^ 3) ^ 2 = (∑ i ∈ s, b i * b i ^ 2) ^ 2 := by
        congr 1
        exact Finset.sum_congr rfl fun i _ => by ring
    _ ≤ (∑ i ∈ s, b i ^ 2) * ∑ i ∈ s, (b i ^ 2) ^ 2 :=
        Finset.sum_mul_sq_le_sq_mul_sq s _ _
    _ = (∑ i ∈ s, b i ^ 2) * ∑ i ∈ s, b i ^ 4 := by
        congr 1
        exact Finset.sum_congr rfl fun i _ => by ring

/-- The double-sum form: `p3b² ≤ Q · p4b` for the entries of a matrix. -/
theorem sum_cube_sq_le_matrix {ι κ : Type*} [Fintype ι] [Fintype κ] (b : ι → κ → ℝ) :
    (∑ i, ∑ j, b i j ^ 3) ^ 2 ≤ (∑ i, ∑ j, b i j ^ 2) * ∑ i, ∑ j, b i j ^ 4 := by
  have h := sum_cube_sq_le (Finset.univ : Finset (ι × κ)) fun p => b p.1 p.2
  simpa [Fintype.sum_prod_type] using h

/-! ## §2  The layer-coefficient ratio -/

/-- For `4 ≤ k ≤ n`, `(k−2)(n−3)² ≤ 2(k−3)(n−2)²`.  The factor `2` is the supremum of
`(k−2)(n−3)²/((k−3)(n−2)²)` on that range, approached as `n → ∞` at `k = 4`, so it cannot be
lowered. -/
theorem ratio_le_two {k n : ℝ} (hk : 4 ≤ k) (hkn : k ≤ n) :
    (k - 2) * (n - 3) ^ 2 ≤ 2 * ((k - 3) * (n - 2) ^ 2) := by
  have hn : (4:ℝ) ≤ n := le_trans hk hkn
  have h1 : (k - 2) * (n - 3) ^ 2 ≤ (2 * (k - 3)) * (n - 3) ^ 2 :=
    mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
  have h2 : (2 * (k - 3)) * (n - 3) ^ 2 ≤ (2 * (k - 3)) * (n - 2) ^ 2 :=
    mul_le_mul_of_nonneg_left (by nlinarith) (by linarith)
  linarith

/-- The form in which the ratio is used: `8(k−2)(n−3)² ≤ 27(k−3)(n−2)²` for `4 ≤ k ≤ n`.
The margin is `27/16`, uniform in `(n, k)`. -/
theorem ratio_le_27_8 {k n : ℝ} (hk : 4 ≤ k) (hkn : k ≤ n) :
    8 * ((k - 2) * (n - 3) ^ 2) ≤ 27 * ((k - 3) * (n - 2) ^ 2) := by
  have h := ratio_le_two hk hkn
  have hnn : (0:ℝ) ≤ (k - 3) * (n - 2) ^ 2 :=
    mul_nonneg (by linarith) (sq_nonneg _)
  linarith

/-! ## §3  The mixed quadratic bounds

`rowSum` and `colSum` name the two line-sum vectors, so that the specialised corollaries can
state the source inequalities literally. -/

/-- The vector of row sums. -/
def rowSum {ι κ : Type*} [Fintype κ] (b : ι → κ → ℝ) (i : ι) : ℝ := ∑ j, b i j

/-- The vector of column sums. -/
def colSum {ι κ : Type*} [Fintype ι] (b : ι → κ → ℝ) (j : κ) : ℝ := ∑ i, b i j

section Mixed

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- `∑ⱼ (∑ᵢ rᵢ bᵢⱼ)² ≤ Q · ∑ᵢ rᵢ²`: Cauchy–Schwarz in each column, then summed. -/
theorem sum_weighted_col_sq_le (b : ι → κ → ℝ) (r : ι → ℝ) :
    ∑ j, (∑ i, r i * b i j) ^ 2 ≤ (∑ i, ∑ j, b i j ^ 2) * ∑ i, r i ^ 2 := by
  calc ∑ j, (∑ i, r i * b i j) ^ 2
      ≤ ∑ j, (∑ i, r i ^ 2) * ∑ i, b i j ^ 2 :=
        Finset.sum_le_sum fun j _ => Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    _ = (∑ i, r i ^ 2) * ∑ j, ∑ i, b i j ^ 2 := by rw [Finset.mul_sum]
    _ = (∑ i, ∑ j, b i j ^ 2) * ∑ i, r i ^ 2 := by
        rw [Finset.sum_comm]; ring

/-- `∑ᵢ (∑ⱼ cⱼ bᵢⱼ)² ≤ Q · ∑ⱼ cⱼ²`, the transpose twin. -/
theorem sum_weighted_row_sq_le (b : ι → κ → ℝ) (c : κ → ℝ) :
    ∑ i, (∑ j, c j * b i j) ^ 2 ≤ (∑ i, ∑ j, b i j ^ 2) * ∑ j, c j ^ 2 := by
  calc ∑ i, (∑ j, c j * b i j) ^ 2
      ≤ ∑ i, (∑ j, c j ^ 2) * ∑ j, b i j ^ 2 :=
        Finset.sum_le_sum fun i _ => Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    _ = (∑ j, c j ^ 2) * ∑ i, ∑ j, b i j ^ 2 := by rw [Finset.mul_sum]
    _ = (∑ i, ∑ j, b i j ^ 2) * ∑ j, c j ^ 2 := by ring

/-- `(∑ᵢⱼ rᵢ bᵢⱼ cⱼ)² ≤ (∑ rᵢ²)(∑ cⱼ²) Q`: one Cauchy–Schwarz on the pair index `(i, j)`,
with `f (i,j) = rᵢcⱼ` and `g (i,j) = bᵢⱼ`. -/
theorem sq_bilinear_le (b : ι → κ → ℝ) (r : ι → ℝ) (c : κ → ℝ) :
    (∑ i, ∑ j, r i * b i j * c j) ^ 2
      ≤ (∑ i, r i ^ 2) * (∑ j, c j ^ 2) * ∑ i, ∑ j, b i j ^ 2 := by
  have e1 : ∑ p : ι × κ, r p.1 * c p.2 * b p.1 p.2 = ∑ i, ∑ j, r i * b i j * c j := by
    rw [Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have e2 : ∑ p : ι × κ, (r p.1 * c p.2) ^ 2 = (∑ i, r i ^ 2) * ∑ j, c j ^ 2 := by
    rw [Fintype.sum_prod_type, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have e3 : ∑ p : ι × κ, b p.1 p.2 ^ 2 = ∑ i, ∑ j, b i j ^ 2 := by
    rw [Fintype.sum_prod_type]
  calc (∑ i, ∑ j, r i * b i j * c j) ^ 2
      = (∑ p : ι × κ, r p.1 * c p.2 * b p.1 p.2) ^ 2 := by rw [e1]
    _ ≤ (∑ p : ι × κ, (r p.1 * c p.2) ^ 2) * ∑ p : ι × κ, b p.1 p.2 ^ 2 :=
        Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    _ = (∑ i, r i ^ 2) * (∑ j, c j ^ 2) * ∑ i, ∑ j, b i j ^ 2 := by rw [e2, e3]

/-- `(∑ᵢⱼ rᵢ² bᵢⱼ cⱼ)² ≤ (∑ rᵢ²)² (∑ cⱼ²) Q`.  This is `sq_bilinear_le` at the weight `r²`
followed by `∑ rᵢ⁴ ≤ (∑ rᵢ²)²`; no maximum over `i` is used. -/
theorem sq_bilinear_sq_left_le (b : ι → κ → ℝ) (r : ι → ℝ) (c : κ → ℝ) :
    (∑ i, ∑ j, r i ^ 2 * b i j * c j) ^ 2
      ≤ (∑ i, r i ^ 2) ^ 2 * (∑ j, c j ^ 2) * ∑ i, ∑ j, b i j ^ 2 := by
  have h := sq_bilinear_le b (fun i => r i ^ 2) c
  have h4 : ∑ i, (r i ^ 2) ^ 2 ≤ (∑ i, r i ^ 2) ^ 2 :=
    Finset.sum_sq_le_sq_sum_of_nonneg fun i _ => sq_nonneg _
  have hc : (0:ℝ) ≤ ∑ j, c j ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hQ : (0:ℝ) ≤ ∑ i, ∑ j, b i j ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  refine h.trans ?_
  gcongr

/-- `(∑ᵢⱼ rᵢ bᵢⱼ cⱼ²)² ≤ (∑ cⱼ²)² (∑ rᵢ²) Q`, the twin of `sq_bilinear_sq_left_le`. -/
theorem sq_bilinear_sq_right_le (b : ι → κ → ℝ) (r : ι → ℝ) (c : κ → ℝ) :
    (∑ i, ∑ j, r i * b i j * c j ^ 2) ^ 2
      ≤ (∑ j, c j ^ 2) ^ 2 * (∑ i, r i ^ 2) * ∑ i, ∑ j, b i j ^ 2 := by
  have h := sq_bilinear_le b r (fun j => c j ^ 2)
  have h4 : ∑ j, (c j ^ 2) ^ 2 ≤ (∑ j, c j ^ 2) ^ 2 :=
    Finset.sum_sq_le_sq_sum_of_nonneg fun j _ => sq_nonneg _
  have hr : (0:ℝ) ≤ ∑ i, r i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hQ : (0:ℝ) ≤ ∑ i, ∑ j, b i j ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  refine h.trans ?_
  calc (∑ i, r i ^ 2) * (∑ j, (c j ^ 2) ^ 2) * ∑ i, ∑ j, b i j ^ 2
      = (∑ j, (c j ^ 2) ^ 2) * (∑ i, r i ^ 2) * ∑ i, ∑ j, b i j ^ 2 := by ring
    _ ≤ (∑ j, c j ^ 2) ^ 2 * (∑ i, r i ^ 2) * ∑ i, ∑ j, b i j ^ 2 := by gcongr

/-! The same five bounds with the weights specialised to the line sums.  These are the
statements the source inequalities make; proving them from the general forms is what checks
that the generalisation was faithful. -/

theorem sum_weighted_col_sq_le_rowSum (b : ι → κ → ℝ) :
    ∑ j, (∑ i, rowSum b i * b i j) ^ 2
      ≤ (∑ i, ∑ j, b i j ^ 2) * ∑ i, rowSum b i ^ 2 :=
  sum_weighted_col_sq_le b (rowSum b)

theorem sum_weighted_row_sq_le_colSum (b : ι → κ → ℝ) :
    ∑ i, (∑ j, colSum b j * b i j) ^ 2
      ≤ (∑ i, ∑ j, b i j ^ 2) * ∑ j, colSum b j ^ 2 :=
  sum_weighted_row_sq_le b (colSum b)

theorem sq_bilinear_le_lineSum (b : ι → κ → ℝ) :
    (∑ i, ∑ j, rowSum b i * b i j * colSum b j) ^ 2
      ≤ (∑ i, rowSum b i ^ 2) * (∑ j, colSum b j ^ 2) * ∑ i, ∑ j, b i j ^ 2 :=
  sq_bilinear_le b (rowSum b) (colSum b)

theorem sq_bilinear_sq_left_le_lineSum (b : ι → κ → ℝ) :
    (∑ i, ∑ j, rowSum b i ^ 2 * b i j * colSum b j) ^ 2
      ≤ (∑ i, rowSum b i ^ 2) ^ 2 * (∑ j, colSum b j ^ 2) * ∑ i, ∑ j, b i j ^ 2 :=
  sq_bilinear_sq_left_le b (rowSum b) (colSum b)

theorem sq_bilinear_sq_right_le_lineSum (b : ι → κ → ℝ) :
    (∑ i, ∑ j, rowSum b i * b i j * colSum b j ^ 2) ^ 2
      ≤ (∑ j, colSum b j ^ 2) ^ 2 * (∑ i, rowSum b i ^ 2) * ∑ i, ∑ j, b i j ^ 2 :=
  sq_bilinear_sq_right_le b (rowSum b) (colSum b)

end Mixed

/-! ## §4  The row-maximum bounds -/

/-- `∑ q² ≤ M ∑ q` whenever `0 ≤ qᵢ ≤ M`.  Applied with `qᵢ = ∑ⱼ bᵢⱼ²` and `M = maxᵢ qᵢ`
this is `YR ≤ M · Q`; the maximum is left as a hypothesis rather than a `Finset.sup'`, which
is both weaker to satisfy and easier to use. -/
theorem sum_sq_le_max_mul_sum {ι : Type*} (s : Finset ι) (q : ι → ℝ) (M : ℝ)
    (hq : ∀ i ∈ s, 0 ≤ q i) (hM : ∀ i ∈ s, q i ≤ M) :
    ∑ i ∈ s, q i ^ 2 ≤ M * ∑ i ∈ s, q i := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i hi => ?_
  rw [sq]
  exact mul_le_mul_of_nonneg_right (hM i hi) (hq i hi)

/-- Centring a row of sum `1` costs exactly `1/n`:
`∑ⱼ (aⱼ − 1/n)² = ∑ⱼ aⱼ² − 1/n`.
This identity is the whole content of the distinction between the centred and the uncentred
row bound. -/
theorem centred_row_sq_eq {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (h : ∑ j, a j = 1) :
    ∑ j, (a j - 1 / (n:ℝ)) ^ 2 = (∑ j, a j ^ 2) - 1 / (n:ℝ) := by
  have hn' : ((n:ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have expand : ∀ j : Fin n,
      (a j - 1 / (n:ℝ)) ^ 2 = a j ^ 2 - (2 / (n:ℝ)) * a j + (1 / (n:ℝ)) ^ 2 :=
    fun j => by ring
  rw [Finset.sum_congr rfl fun j _ => expand j, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, ← Finset.mul_sum, h, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

/-- The centred row bound: for a nonnegative row of sum `1`,
`∑ⱼ (aⱼ − 1/n)² ≤ 1 − 1/n`.
Only this row's stochasticity is used.  The uncentred statement `∑ⱼ aⱼ² ≤ 1 − 1/n` is FALSE
— see `centred_row_sq_eq_of_indicator`, where `∑ⱼ aⱼ² = 1`. -/
theorem centred_row_sq_le {n : ℕ} (a : Fin n → ℝ) (h0 : ∀ j, 0 ≤ a j) (h : ∑ j, a j = 1) :
    ∑ j, (a j - 1 / (n:ℝ)) ^ 2 ≤ 1 - 1 / (n:ℝ) := by
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | hp
    · simp at h
    · exact hp
  have hle : ∀ j ∈ (Finset.univ : Finset (Fin n)), a j ≤ 1 := by
    intro j _
    rw [← h]
    exact Finset.single_le_sum (fun i _ => h0 i) (Finset.mem_univ j)
  have h1 : ∑ j, a j ^ 2 ≤ 1 := by
    have := sum_sq_le_max_mul_sum Finset.univ a 1 (fun j _ => h0 j) hle
    rwa [one_mul, h] at this
  rw [centred_row_sq_eq hn a h]
  linarith

/-- The centred row bound is attained: at a permutation row — a `0/1` indicator —
`∑ⱼ (aⱼ − 1/n)² = 1 − 1/n` exactly, so the constant `1 − 1/n` cannot be lowered.  Note that
the same row has `∑ⱼ aⱼ² = 1`, which is what makes the uncentred reading false. -/
theorem centred_row_sq_eq_of_indicator {n : ℕ} (hn : 0 < n) (j₀ : Fin n) :
    ∑ j, ((if j = j₀ then (1:ℝ) else 0) - 1 / (n:ℝ)) ^ 2 = 1 - 1 / (n:ℝ) := by
  have h : ∑ j, (if j = j₀ then (1:ℝ) else 0) = 1 := by simp
  rw [centred_row_sq_eq hn _ h]
  congr 1
  have : ∀ j : Fin n, (if j = j₀ then (1:ℝ) else 0) ^ 2 = if j = j₀ then (1:ℝ) else 0 := by
    intro j; split <;> norm_num
  rw [Finset.sum_congr rfl fun j _ => this j, h]

/-! ## §5  The sharp zero-sum cubic inequality -/

/-- **The polygon bound.**  If `0 ≤ xᵢ` and `xᵢ` is at most the sum of the other coordinates —
the polygon condition — then `n xᵢ² ≤ (n−1) ∑ x²`.  Chebyshev on the complement of `i`, with
the polygon inequality squared.

Only the single entry `xᵢ` is required to be nonnegative; the other coordinates may have
either sign.  Both hypotheses are load-bearing: dropping the polygon condition, or dropping
`0 ≤ xᵢ`, each admits counterexamples.

This is the common generalisation of two uses that look alike but are not: a vector of **norms**
(nonnegative, not zero-sum, polygon condition from the triangle inequality) and a **zero-sum**
vector, which satisfies the hypothesis only after passing to absolute values — see
`zero_sum_sq_le`. -/
theorem sq_le_of_polygon {n : ℕ} (x : Fin n → ℝ) (i : Fin n) (hi : 0 ≤ x i)
    (hpoly : x i ≤ ∑ j ∈ Finset.univ.erase i, x j) :
    (n:ℝ) * x i ^ 2 ≤ ((n:ℝ) - 1) * ∑ j, x j ^ 2 := by
  have hn1 : 1 ≤ n := Fin.pos i
  have hmem : i ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ i
  have hcard : ((Finset.univ.erase i).card : ℝ) = (n:ℝ) - 1 := by
    rw [Finset.card_erase_of_mem hmem, Finset.card_univ, Fintype.card_fin]
    rw [Nat.cast_sub hn1, Nat.cast_one]
  have hsum2 : ∑ j ∈ Finset.univ.erase i, x j ^ 2 = (∑ j, x j ^ 2) - x i ^ 2 := by
    rw [Finset.sum_erase_eq_sub hmem]
  have hcs : (∑ j ∈ Finset.univ.erase i, x j) ^ 2
      ≤ ((Finset.univ.erase i).card : ℝ) * ∑ j ∈ Finset.univ.erase i, x j ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  rw [hcard, hsum2] at hcs
  -- `0 ≤ x i ≤ ∑_{j ≠ i} x j` is what lets the polygon inequality be squared.
  have hsq : x i ^ 2 ≤ (∑ j ∈ Finset.univ.erase i, x j) ^ 2 :=
    pow_le_pow_left₀ hi hpoly 2
  nlinarith [hcs, hsq]

/-- On the zero-sum hyperplane every coordinate is small: `n xᵢ² ≤ (n−1) ∑ x²`.  A corollary
of `sq_le_of_polygon` applied to `|x|`, since `∑ x = 0` gives
`|xᵢ| = |∑_{j ≠ i} xⱼ| ≤ ∑_{j ≠ i} |xⱼ|`. -/
theorem zero_sum_sq_le {n : ℕ} (x : Fin n → ℝ) (hx : ∑ i, x i = 0) (i : Fin n) :
    (n:ℝ) * x i ^ 2 ≤ ((n:ℝ) - 1) * ∑ j, x j ^ 2 := by
  have hmem : i ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ i
  have hsplit : x i + ∑ j ∈ Finset.univ.erase i, x j = 0 := by
    rw [Finset.add_sum_erase _ x hmem]; exact hx
  have hpoly : |x i| ≤ ∑ j ∈ Finset.univ.erase i, |x j| := by
    have hneg : x i = -∑ j ∈ Finset.univ.erase i, x j := by linarith
    rw [hneg, abs_neg]
    exact Finset.abs_sum_le_sum_abs _ _
  have h := sq_le_of_polygon (fun j => |x j|) i (abs_nonneg _) hpoly
  simpa [sq_abs] using h

/-- Cauchy–Schwarz in the form the polygon condition needs: `|∑ ab| ≤ √(∑a²)·√(∑b²)`. -/
theorem abs_sum_mul_le_sqrt_mul_sqrt {ι : Type*} (s : Finset ι) (a b : ι → ℝ) :
    |∑ i ∈ s, a i * b i| ≤ Real.sqrt (∑ i ∈ s, a i ^ 2) * Real.sqrt (∑ i ∈ s, b i ^ 2) := by
  have hA : (0:ℝ) ≤ ∑ i ∈ s, a i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  calc |∑ i ∈ s, a i * b i| = Real.sqrt ((∑ i ∈ s, a i * b i) ^ 2) :=
        (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt ((∑ i ∈ s, a i ^ 2) * ∑ i ∈ s, b i ^ 2) :=
        Real.sqrt_le_sqrt (Finset.sum_mul_sq_le_sq_mul_sq s a b)
    _ = Real.sqrt (∑ i ∈ s, a i ^ 2) * Real.sqrt (∑ i ∈ s, b i ^ 2) := Real.sqrt_mul hA _

/-- The Euclidean norm of row `i`. -/
noncomputable def rowNorm {m n : ℕ} (z : Matrix (Fin m) (Fin n) ℝ) (i : Fin m) : ℝ :=
  Real.sqrt (∑ j, (z i j) ^ 2)

lemma rowNorm_nonneg {m n : ℕ} (z : Matrix (Fin m) (Fin n) ℝ) (i : Fin m) :
    0 ≤ rowNorm z i := Real.sqrt_nonneg _

lemma rowNorm_sq {m n : ℕ} (z : Matrix (Fin m) (Fin n) ℝ) (i : Fin m) :
    rowNorm z i ^ 2 = ∑ j, (z i j) ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)

/-- **Row norms satisfy the polygon condition when the column sums vanish.**  Then
`∑ᵢ (row i) = 0` as a vector, so `row i = −∑_{i' ≠ i} row i'`, and the triangle inequality
gives `ρᵢ ≤ ∑_{i' ≠ i} ρ_{i'}`.

The proof here avoids `EuclideanSpace` — and so avoids the triangle inequality for a finite
sum of vectors — by squaring first: `ρᵢ² = −∑_{i' ≠ i} ⟨row i, row i'⟩ ≤ ρᵢ ∑_{i' ≠ i} ρ_{i'}`
by Cauchy–Schwarz per pair of rows, and then cancelling one `ρᵢ`.

Only the **column** sums are required.  The row sums may be arbitrary, which is weaker than
the doubly centred hypothesis the application supplies. -/
theorem rowNorm_polygon {m n : ℕ} (z : Matrix (Fin m) (Fin n) ℝ)
    (hcol : ∀ j, ∑ i, z i j = 0) (i : Fin m) :
    rowNorm z i ≤ ∑ i' ∈ Finset.univ.erase i, rowNorm z i' := by
  have hSnn : (0:ℝ) ≤ ∑ i' ∈ Finset.univ.erase i, rowNorm z i' :=
    Finset.sum_nonneg fun _ _ => rowNorm_nonneg z _
  -- Row `i` is minus the sum of the others, entry by entry.
  have hpt : ∀ j, z i j = -∑ i' ∈ Finset.univ.erase i, z i' j := by
    intro j
    have h := hcol j
    rw [← Finset.add_sum_erase _ (fun i' => z i' j) (Finset.mem_univ i)] at h
    linarith
  -- Expand `qᵢ` as minus a sum of inner products with the other rows.
  have expand : ∑ j, (z i j) ^ 2
      = -∑ i' ∈ Finset.univ.erase i, ∑ j, z i j * z i' j := by
    have h1 : ∀ j : Fin n, (z i j) ^ 2 = -∑ i' ∈ Finset.univ.erase i, z i j * z i' j := by
      intro j
      calc (z i j) ^ 2 = z i j * z i j := sq _
        _ = z i j * -∑ i' ∈ Finset.univ.erase i, z i' j := by rw [← hpt j]
        _ = -(z i j * ∑ i' ∈ Finset.univ.erase i, z i' j) := by rw [mul_neg]
        _ = -∑ i' ∈ Finset.univ.erase i, z i j * z i' j := by rw [Finset.mul_sum]
    rw [Finset.sum_congr rfl fun j _ => h1 j, Finset.sum_neg_distrib, Finset.sum_comm]
  -- Cauchy–Schwarz on each pair of rows.
  have hbound : ∑ j, (z i j) ^ 2 ≤ rowNorm z i * ∑ i' ∈ Finset.univ.erase i, rowNorm z i' := by
    rw [expand, ← Finset.sum_neg_distrib, Finset.mul_sum]
    refine Finset.sum_le_sum fun i' _ => ?_
    calc -∑ j, z i j * z i' j ≤ |∑ j, z i j * z i' j| := neg_le_abs _
      _ ≤ rowNorm z i * rowNorm z i' := abs_sum_mul_le_sqrt_mul_sqrt _ _ _
  -- Cancel one factor of `ρᵢ`, treating `ρᵢ = 0` separately.
  rcases eq_or_lt_of_le (rowNorm_nonneg z i) with h0 | hpos
  · rw [← h0]; exact hSnn
  · rw [← rowNorm_sq z i] at hbound
    exact le_of_mul_le_mul_left (by nlinarith [hbound]) hpos

/-- **pincer's polygon constraint, complete.**  If the column sums of `z` vanish then for every
row `i`, `m qᵢ ≤ (m−1) Q` where `qᵢ = ∑ⱼ zᵢⱼ²` and `Q = ∑ᵢⱼ zᵢⱼ²` — equivalently
`maxᵢ qᵢ ≤ ((m−1)/m) Q`.  The hypothesis of `sq_le_of_polygon` is discharged by
`rowNorm_polygon`, so nothing is assumed about the row sums. -/
theorem row_sq_le_of_colSum_zero {m n : ℕ} (z : Matrix (Fin m) (Fin n) ℝ)
    (hcol : ∀ j, ∑ i, z i j = 0) (i : Fin m) :
    (m:ℝ) * (∑ j, (z i j) ^ 2) ≤ ((m:ℝ) - 1) * ∑ i', ∑ j, (z i' j) ^ 2 := by
  have h := sq_le_of_polygon (rowNorm z) i (rowNorm_nonneg z i) (rowNorm_polygon z hcol i)
  rw [rowNorm_sq z i] at h
  refine h.trans (le_of_eq ?_)
  congr 1
  exact Finset.sum_congr rfl fun i' _ => rowNorm_sq z i'

/-- The pointwise cubic bound, summed.  For **any** `u` dominating every coordinate and
**any** `v`, the factorisation `(xᵢ − u)(xᵢ − v)² ≤ 0` gives
`xᵢ³ ≤ (u + 2v)xᵢ² − (2uv + v²)xᵢ + uv²`, and `∑ x = 0` deletes the linear term.  All the
sharpness of §5 sits in the later choice of `u` and `v`. -/
theorem sum_cube_le_of_le {n : ℕ} (x : Fin n → ℝ) (hx : ∑ i, x i = 0) (u v : ℝ)
    (hxu : ∀ i, x i ≤ u) :
    ∑ i, x i ^ 3 ≤ (u + 2 * v) * (∑ i, x i ^ 2) + (n:ℝ) * (u * v ^ 2) := by
  have hpt : ∀ i : Fin n,
      x i ^ 3 ≤ (u + 2 * v) * x i ^ 2 - (2 * u * v + v ^ 2) * x i + u * v ^ 2 := by
    intro i
    have h1 : (x i - u) * (x i - v) ^ 2 ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith [hxu i]) (sq_nonneg _)
    nlinarith [h1]
  calc ∑ i, x i ^ 3
      ≤ ∑ i, ((u + 2 * v) * x i ^ 2 - (2 * u * v + v ^ 2) * x i + u * v ^ 2) :=
        Finset.sum_le_sum fun i _ => hpt i
    _ = (u + 2 * v) * (∑ i, x i ^ 2) - (2 * u * v + v ^ 2) * (∑ i, x i)
          + (n:ℝ) * (u * v ^ 2) := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
          Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = (u + 2 * v) * (∑ i, x i ^ 2) + (n:ℝ) * (u * v ^ 2) := by rw [hx]; ring

/-- The sharp zero-sum cubic inequality, one-sided:
for `∑ x = 0` and `2 ≤ n`, `∑ x³ ≤ κ(n) · (√(∑ x²))³` with `κ(n) = (n−2)/√(n(n−1))`.
The constant is attained at `(n−1, −1, …, −1)`. -/
theorem zero_sum_cube_le {n : ℕ} (hn : 2 ≤ n) (x : Fin n → ℝ) (hx : ∑ i, x i = 0) :
    ∑ i, x i ^ 3
      ≤ ((n:ℝ) - 2) / Real.sqrt ((n:ℝ) * ((n:ℝ) - 1)) * Real.sqrt (∑ i, x i ^ 2) ^ 3 := by
  have hnn : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hp2 : (0:ℝ) ≤ ∑ i, x i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hE : (0:ℝ) < (n:ℝ) * ((n:ℝ) - 1) := by nlinarith
  set s := Real.sqrt (∑ i, x i ^ 2) with hsdef
  set D := Real.sqrt ((n:ℝ) * ((n:ℝ) - 1)) with hDdef
  have hs0 : (0:ℝ) ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = ∑ i, x i ^ 2 := Real.sq_sqrt hp2
  have hDpos : (0:ℝ) < D := Real.sqrt_pos.mpr hE
  have hD2 : D ^ 2 = (n:ℝ) * ((n:ℝ) - 1) := Real.sq_sqrt hE.le
  have hDne : D ≠ 0 := hDpos.ne'
  -- the key relation, which is all that the two square roots contribute
  have hw2 : ((n:ℝ) * ((n:ℝ) - 1)) * (s / D) ^ 2 = s ^ 2 := by
    field_simp
    rw [hD2]
    ring
  -- step 1: every coordinate is at most u
  have hxu : ∀ i, x i ≤ ((n:ℝ) - 1) * (s / D) := by
    intro i
    have h1 : (n:ℝ) * x i ^ 2 ≤ ((n:ℝ) - 1) * ∑ j, x j ^ 2 := zero_sum_sq_le x hx i
    have hu0 : (0:ℝ) ≤ ((n:ℝ) - 1) * (s / D) :=
      mul_nonneg (by linarith) (div_nonneg hs0 hDpos.le)
    have hu2 : (((n:ℝ) - 1) * (s / D)) ^ 2 * (n:ℝ) = ((n:ℝ) - 1) * s ^ 2 := by
      field_simp
      rw [hD2]
      ring
    have hxi2 : x i ^ 2 ≤ (((n:ℝ) - 1) * (s / D)) ^ 2 := by
      rw [hs2] at hu2
      nlinarith [h1, hu2]
    calc x i ≤ |x i| := le_abs_self _
      _ = Real.sqrt (x i ^ 2) := (Real.sqrt_sq_eq_abs _).symm
      _ ≤ Real.sqrt ((((n:ℝ) - 1) * (s / D)) ^ 2) := Real.sqrt_le_sqrt hxi2
      _ = ((n:ℝ) - 1) * (s / D) := Real.sqrt_sq hu0
  -- steps 2 and 3
  have hbound := sum_cube_le_of_le x hx (((n:ℝ) - 1) * (s / D)) (-(s / D)) hxu
  refine hbound.trans (le_of_eq ?_)
  rw [← hs2]
  linear_combination (s / D) * hw2

/-- The two-sided form. -/
theorem zero_sum_cube_abs_le {n : ℕ} (hn : 2 ≤ n) (x : Fin n → ℝ) (hx : ∑ i, x i = 0) :
    |∑ i, x i ^ 3|
      ≤ ((n:ℝ) - 2) / Real.sqrt ((n:ℝ) * ((n:ℝ) - 1)) * Real.sqrt (∑ i, x i ^ 2) ^ 3 := by
  refine abs_le.mpr ⟨?_, zero_sum_cube_le hn x hx⟩
  have hneg : ∑ i, (-x i) = 0 := by
    rw [Finset.sum_neg_distrib, hx, neg_zero]
  have h := zero_sum_cube_le hn (fun i => -x i) hneg
  have e1 : ∑ i, (-x i) ^ 3 = -∑ i, x i ^ 3 := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have e2 : ∑ i, (-x i) ^ 2 = ∑ i, x i ^ 2 :=
    Finset.sum_congr rfl fun i _ => by ring
  rw [e1, e2] at h
  linarith

/-- `√p ^ 3 = p ^ (3/2)` for `0 ≤ p`, the bridge to the fractional-power form. -/
theorem sqrt_pow_three {p : ℝ} (hp : 0 ≤ p) : Real.sqrt p ^ 3 = p ^ ((3:ℝ)/2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast (p ^ (1 / (2:ℝ))) 3, ← Real.rpow_mul hp]
  norm_num

/-- The sharp zero-sum cubic inequality in fractional-power form:
`|∑ x³| ≤ ((n−2)/√(n(n−1))) · (∑ x²)^{3/2}`. -/
theorem zero_sum_cube_abs_le_rpow {n : ℕ} (hn : 2 ≤ n) (x : Fin n → ℝ)
    (hx : ∑ i, x i = 0) :
    |∑ i, x i ^ 3|
      ≤ ((n:ℝ) - 2) / Real.sqrt ((n:ℝ) * ((n:ℝ) - 1)) * (∑ i, x i ^ 2) ^ ((3:ℝ)/2) := by
  have hp2 : (0:ℝ) ≤ ∑ i, x i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  rw [← sqrt_pow_three hp2]
  exact zero_sum_cube_abs_le hn x hx

/-- The square-free form, for callers who would rather not meet `Real.sqrt` or `rpow`:
`n(n−1)(∑ x³)² ≤ (n−2)²(∑ x²)³` on the zero-sum hyperplane. -/
theorem zero_sum_cube_sq_le {n : ℕ} (hn : 2 ≤ n) (x : Fin n → ℝ) (hx : ∑ i, x i = 0) :
    (n:ℝ) * ((n:ℝ) - 1) * (∑ i, x i ^ 3) ^ 2 ≤ ((n:ℝ) - 2) ^ 2 * (∑ i, x i ^ 2) ^ 3 := by
  have hnn : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hp2 : (0:ℝ) ≤ ∑ i, x i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hE : (0:ℝ) < (n:ℝ) * ((n:ℝ) - 1) := by nlinarith
  have hD2 : Real.sqrt ((n:ℝ) * ((n:ℝ) - 1)) ^ 2 = (n:ℝ) * ((n:ℝ) - 1) :=
    Real.sq_sqrt hE.le
  have hDpos : (0:ℝ) < Real.sqrt ((n:ℝ) * ((n:ℝ) - 1)) := Real.sqrt_pos.mpr hE
  have hs2 : Real.sqrt (∑ i, x i ^ 2) ^ 2 = ∑ i, x i ^ 2 := Real.sq_sqrt hp2
  have h := zero_sum_cube_abs_le hn x hx
  have habs : (∑ i, x i ^ 3) ^ 2 = |∑ i, x i ^ 3| ^ 2 := (sq_abs _).symm
  have hrhs : (0:ℝ) ≤ ((n:ℝ) - 2) / Real.sqrt ((n:ℝ) * ((n:ℝ) - 1))
      * Real.sqrt (∑ i, x i ^ 2) ^ 3 := by
    apply mul_nonneg (div_nonneg (by linarith) hDpos.le)
    exact pow_nonneg (Real.sqrt_nonneg _) 3
  have hsq : (∑ i, x i ^ 3) ^ 2
      ≤ (((n:ℝ) - 2) / Real.sqrt ((n:ℝ) * ((n:ℝ) - 1)) * Real.sqrt (∑ i, x i ^ 2) ^ 3) ^ 2 := by
    rw [habs]
    exact pow_le_pow_left₀ (abs_nonneg _) h 2
  have hexp : (((n:ℝ) - 2) / Real.sqrt ((n:ℝ) * ((n:ℝ) - 1))
      * Real.sqrt (∑ i, x i ^ 2) ^ 3) ^ 2
      = ((n:ℝ) - 2) ^ 2 / ((n:ℝ) * ((n:ℝ) - 1)) * (∑ i, x i ^ 2) ^ 3 := by
    rw [mul_pow, div_pow, hD2, ← pow_mul, show 3 * 2 = 2 * 3 from by norm_num, pow_mul, hs2]
  rw [hexp] at hsq
  calc (n:ℝ) * ((n:ℝ) - 1) * (∑ i, x i ^ 3) ^ 2
      ≤ (n:ℝ) * ((n:ℝ) - 1)
          * (((n:ℝ) - 2) ^ 2 / ((n:ℝ) * ((n:ℝ) - 1)) * (∑ i, x i ^ 2) ^ 3) :=
        mul_le_mul_of_nonneg_left hsq hE.le
    _ = ((n:ℝ) - 2) ^ 2 * (∑ i, x i ^ 2) ^ 3 := by
        field_simp

/-! ## §6  Axiom audit

**Every declaration in this file depends only on axioms among `propext,
Classical.choice, Quot.sound`.**  No `native_decide`, no `sorry`, and no `decide` on a
large search space appears anywhere in this file. -/

section AxiomAudit

#print axioms rowSum
#print axioms colSum
#print axioms sum_cube_sq_le
#print axioms sum_cube_sq_le_matrix
#print axioms ratio_le_two
#print axioms ratio_le_27_8
#print axioms sum_weighted_col_sq_le
#print axioms sum_weighted_row_sq_le
#print axioms sq_bilinear_le
#print axioms sq_bilinear_sq_left_le
#print axioms sq_bilinear_sq_right_le
#print axioms sum_weighted_col_sq_le_rowSum
#print axioms sum_weighted_row_sq_le_colSum
#print axioms sq_bilinear_le_lineSum
#print axioms sq_bilinear_sq_left_le_lineSum
#print axioms sq_bilinear_sq_right_le_lineSum
#print axioms sum_sq_le_max_mul_sum
#print axioms centred_row_sq_eq
#print axioms centred_row_sq_le
#print axioms centred_row_sq_eq_of_indicator
#print axioms sq_le_of_polygon
#print axioms zero_sum_sq_le
#print axioms abs_sum_mul_le_sqrt_mul_sqrt
#print axioms rowNorm
#print axioms rowNorm_nonneg
#print axioms rowNorm_sq
#print axioms rowNorm_polygon
#print axioms row_sq_le_of_colSum_zero
#print axioms sum_cube_le_of_le
#print axioms zero_sum_cube_le
#print axioms zero_sum_cube_abs_le
#print axioms sqrt_pow_three
#print axioms zero_sum_cube_abs_le_rpow
#print axioms zero_sum_cube_sq_le

end AxiomAudit

end GradedInequalities
