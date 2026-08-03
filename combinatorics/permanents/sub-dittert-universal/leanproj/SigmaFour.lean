/-
# The `σ₄` core expansion on the centred slice

Target: `graded_stability_lemma.md` (4.3),

    σ₄(B) = (3/2)p₄ + (1/8)Q² + (1/4)Z − (3/4)Y_R − (3/4)Y_C

for `B` with vanishing row and column sums.

## The route, and why it is neither the 225-term double sieve nor a 15-term one

§4 of the source expands `σ_m` by Möbius inversion over ORDERED PAIRS of set partitions of
`[m]`.  At `m = 4` that is `15 × 15 = 225` pairs, of which `16` survive — the pairs whose
bipartite multigraph has minimum degree two, i.e. both partitions singleton-free.  Writing 225
terms out and killing 209 is not the cheap way to reach the 16.

Nor is the 15-term partition sieve on one index at a time.  §1 instead PEELS the fourth index:
for `a, b, c` distinct the innermost sum runs over the complement of `{a,b,c}`, so it is the
full marginal minus three values, and the marginal is zero.  What is left is a THREE-index
distinct sum, which `RookSum.sum_distinct_three` already evaluates.  So the four-index sieve
costs one peel, one appeal to the existing `k = 3` sieve, and six vanishing marginals — no
fifteen-term identity is ever written, and the 64-case pointwise check is avoided entirely.

The result, `sum_distinct_four_of_marginals_zero`, is the four-set Möbius statement with the
killing already built in: only the four singleton-free partitions survive, with weights
`+1, +1, +1, −6`.  It is then applied TWICE — once to the columns, once to the rows.

## Where the two hypotheses go

A singleton block on the COLUMN side contributes a factor `∑ⱼ B i j`, a row sum.  A singleton
block on the ROW side contributes `∑ᵢ B i j`, a column sum.  So (4.3) needs both to vanish,
unlike Lemma 2 of `LayerIdentity`, which needs only the total.

## Why the four surviving terms are grouped two ways below

`Y_R` and `Y_C` enter (4.3) with the SAME coefficient, so an error that exchanges them cancels
in the total and leaves the final identity true.  A draft of `e1` accordingly wrote the third
surviving row pattern as `P x y * P y x` where `W₄` at `(x,x,y,y)` gives `P x y * P x y` — equal
by `P_symm`, so (4.3) was unaffected, but the intermediate step was false as stated.

It was caught by computing the total twice: once by the four row patterns of `W₄` (which yields
`Y_C` from the pairings and `Y_R` from the block) and once by splitting `W₄` into its `P`-part
and its `P₄`-part (which yields them the other way round).  The two groupings agree only
because the pair is symmetric, so disagreeing on WHICH invariant a given pattern produces is
exactly the discrepancy that exposes the slip.  Anyone extending this to `σ₅` should expect the
same trap and use the same control: derive the total by two groupings, not one.
-/

import Mathlib.Tactic
import RookSum
import LayerIdentity

open Finset

namespace SigmaFour

variable {n : ℕ}

/-! ## §1  The four-index sieve with vanishing marginals -/

/-- `![a,b,c,d]` is injective exactly when the four entries are pairwise distinct. -/
theorem injective_four {a b c d : Fin n} :
    Function.Injective ![a, b, c, d]
      ↔ a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d := by
  constructor
  · intro h
    refine ⟨fun hab => ?_, fun hac => ?_, fun had => ?_, fun hbc => ?_, fun hbd => ?_,
      fun hcd => ?_⟩
    · exact absurd (h (show ![a,b,c,d] 0 = ![a,b,c,d] 1 by simp [hab])) (by decide)
    · exact absurd (h (show ![a,b,c,d] 0 = ![a,b,c,d] 2 by simp [hac])) (by decide)
    · exact absurd (h (show ![a,b,c,d] 0 = ![a,b,c,d] 3 by simp [had])) (by decide)
    · exact absurd (h (show ![a,b,c,d] 1 = ![a,b,c,d] 2 by simp [hbc])) (by decide)
    · exact absurd (h (show ![a,b,c,d] 1 = ![a,b,c,d] 3 by simp [hbd])) (by decide)
    · exact absurd (h (show ![a,b,c,d] 2 = ![a,b,c,d] 3 by simp [hcd])) (by decide)
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩ i j hij
    fin_cases i <;> fin_cases j <;> simp_all

/-- A sum over functions `Fin 4 → Fin n` as an iterated fourfold sum. -/
theorem sum_fun_four {M : Type*} [AddCommMonoid M] (G : (Fin 4 → Fin n) → M) :
    ∑ f : Fin 4 → Fin n, G f = ∑ a, ∑ b, ∑ c, ∑ d, G ![a, b, c, d] := by
  let e : (Fin n × Fin n × Fin n × Fin n) ≃ (Fin 4 → Fin n) :=
    { toFun := fun p => ![p.1, p.2.1, p.2.2.1, p.2.2.2]
      invFun := fun f => (f 0, f 1, f 2, f 3)
      left_inv := by intro p; rfl
      right_inv := by intro f; funext i; fin_cases i <;> rfl }
  rw [← Equiv.sum_comp e G, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => rfl

/-- **The `k = 4` injection sum as a fourfold sum against the distinctness indicator.** -/
theorem sum_emb_four {M : Type*} [AddCommMonoid M] (F : (Fin 4 → Fin n) → M) :
    ∑ f : Fin 4 ↪ Fin n, F f
      = ∑ a, ∑ b, ∑ c, ∑ d,
          (if a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d then F ![a, b, c, d] else 0) := by
  have h1 : ∑ f : Fin 4 ↪ Fin n, F f
      = ∑ f ∈ (univ : Finset (Fin 4 → Fin n)).filter Function.Injective, F f := by
    rw [Finset.sum_subtype (p := fun f : Fin 4 → Fin n => Function.Injective f)
      ((univ : Finset (Fin 4 → Fin n)).filter Function.Injective) (fun x => by simp) F]
    exact (Fintype.sum_equiv (Equiv.subtypeInjectiveEquivEmbedding (Fin 4) (Fin n))
      _ _ (fun p => rfl)).symm
  rw [h1, Finset.sum_filter, sum_fun_four]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  by_cases h : a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d
  · rw [if_pos (injective_four.mpr h), if_pos h]
  · rw [if_neg (fun hc => h (injective_four.mp hc)), if_neg h]

/-! ### Distributing a negation and a threefold sum through nested sums

The six helpers below are the only sum bookkeeping §1 needs; each is `simp only` over the
matching `Finset` distribution lemma at every level. -/

section Distrib

private theorem sum1_neg (X : Fin n → ℝ) : (∑ a, -(X a)) = -∑ a, X a := by
  simp only [Finset.sum_neg_distrib]

private theorem sum2_neg (X : Fin n → Fin n → ℝ) :
    (∑ a, ∑ b, -(X a b)) = -∑ a, ∑ b, X a b := by
  simp only [Finset.sum_neg_distrib]

private theorem sum3_neg (X : Fin n → Fin n → Fin n → ℝ) :
    (∑ a, ∑ b, ∑ c, -(X a b c)) = -∑ a, ∑ b, ∑ c, X a b c := by
  simp only [Finset.sum_neg_distrib]

private theorem sum1_add3 (X Y Z : Fin n → ℝ) :
    (∑ a, (X a + Y a + Z a)) = (∑ a, X a) + (∑ a, Y a) + ∑ a, Z a := by
  simp only [Finset.sum_add_distrib]

private theorem sum2_add3 (X Y Z : Fin n → Fin n → ℝ) :
    (∑ a, ∑ b, (X a b + Y a b + Z a b))
      = (∑ a, ∑ b, X a b) + (∑ a, ∑ b, Y a b) + ∑ a, ∑ b, Z a b := by
  simp only [Finset.sum_add_distrib]

private theorem sum3_add3 (X Y Z : Fin n → Fin n → Fin n → ℝ) :
    (∑ a, ∑ b, ∑ c, (X a b c + Y a b c + Z a b c))
      = (∑ a, ∑ b, ∑ c, X a b c) + (∑ a, ∑ b, ∑ c, Y a b c) + ∑ a, ∑ b, ∑ c, Z a b c := by
  simp only [Finset.sum_add_distrib]

end Distrib

/-- The sum of a function over the complement of `{a,b,c}`, for `a, b, c` distinct. -/
private theorem sum_compl_triple (G : Fin n → ℝ) {a b c : Fin n}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (∑ d, (if a ≠ d ∧ b ≠ d ∧ c ≠ d then G d else 0))
      = (∑ d, G d) - (G a + G b + G c) := by
  classical
  have hmem : ∀ d : Fin n,
      (a ≠ d ∧ b ≠ d ∧ c ≠ d) ↔ d ∉ ({a, b, c} : Finset (Fin n)) := by
    intro d
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨fun ⟨h1, h2, h3⟩ => ⟨fun h => h1 h.symm, fun h => h2 h.symm, fun h => h3 h.symm⟩,
      fun ⟨h1, h2, h3⟩ => ⟨fun h => h1 h.symm, fun h => h2 h.symm, fun h => h3 h.symm⟩⟩
  rw [Finset.sum_congr rfl fun d _ => by rw [if_congr (hmem d) rfl rfl]]
  rw [← Finset.sum_filter]
  have hfil : (univ : Finset (Fin n)).filter (fun d => d ∉ ({a, b, c} : Finset (Fin n)))
      = ({a, b, c} : Finset (Fin n))ᶜ := by
    ext d; simp
  rw [hfil]
  have htriple : ∑ d ∈ ({a, b, c} : Finset (Fin n)), G d = G a + G b + G c := by
    rw [Finset.sum_insert (by simp [hab, hac]), Finset.sum_insert (by simp [hbc]),
      Finset.sum_singleton]
    ring
  rw [eq_sub_iff_add_eq, ← htriple, Finset.sum_compl_add_sum]

/-- **The four-index sieve, with the eleven singleton partitions already killed.**  If every
one-index marginal of `F` vanishes, then

    ∑_{a,b,c,d distinct} F = ∑ₓᵥ F x x y y + ∑ₓᵥ F x y x y + ∑ₓᵥ F x y y x − 6 ∑ₓ F x x x x,

the four singleton-free partitions of a four-set with Möbius weights `+1, +1, +1, −6`. -/
theorem sum_distinct_four_of_marginals_zero (F : Fin n → Fin n → Fin n → Fin n → ℝ)
    (h0 : ∀ b c d, ∑ a, F a b c d = 0) (h1 : ∀ a c d, ∑ b, F a b c d = 0)
    (h2 : ∀ a b d, ∑ c, F a b c d = 0) (h3 : ∀ a b c, ∑ d, F a b c d = 0) :
    (∑ a, ∑ b, ∑ c, ∑ d,
        (if a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d then F a b c d else 0))
      = (∑ x, ∑ y, F x x y y) + (∑ x, ∑ y, F x y x y) + (∑ x, ∑ y, F x y y x)
        - 6 * ∑ x, F x x x x := by
  -- STEP 1.  Peel `d`: for `a, b, c` distinct the inner sum is the marginal minus three values.
  have peel : ∀ a b c : Fin n,
      (∑ d, (if a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d then F a b c d else 0))
        = (if a ≠ b ∧ a ≠ c ∧ b ≠ c then
            -(F a b c a + F a b c b + F a b c c) else 0) := by
    intro a b c
    by_cases hd : a ≠ b ∧ a ≠ c ∧ b ≠ c
    · obtain ⟨hab, hac, hbc⟩ := hd
      rw [if_pos ⟨hab, hac, hbc⟩]
      rw [show (∑ d, (if a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d then F a b c d else 0))
          = ∑ d, (if a ≠ d ∧ b ≠ d ∧ c ≠ d then F a b c d else 0) from
        Finset.sum_congr rfl fun d _ => by
          by_cases h : a ≠ d ∧ b ≠ d ∧ c ≠ d
          · rw [if_pos ⟨hab, hac, h.1, hbc, h.2.1, h.2.2⟩, if_pos h]
          · rw [if_neg (by tauto), if_neg h]]
      rw [sum_compl_triple (fun d => F a b c d) hab hac hbc, h3 a b c]
      ring
    · rw [if_neg hd]
      refine Finset.sum_eq_zero fun d _ => ?_
      rw [if_neg (by tauto)]
  rw [Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun c _ => peel a b c]
  -- STEP 2.  What is left is a three-index distinct sum: use the committed `k = 3` sieve.
  rw [RookSum.sum_distinct_three (fun a b c => -(F a b c a + F a b c b + F a b c c))]
  -- STEP 3.  Six of the resulting sums vanish, each by one marginal after commuting.
  have V1 : (∑ a, ∑ b, ∑ c, F a b c a) = 0 := by
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_eq_zero fun c _ => h1 a c a
  have V2 : (∑ a, ∑ b, ∑ c, F a b c b) = 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_eq_zero fun c _ => h0 b c b
  have V3 : (∑ a, ∑ b, ∑ c, F a b c c) = 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_eq_zero fun c _ => h0 b c c
  have V4 : (∑ a, ∑ c, F a a c a) = 0 := Finset.sum_eq_zero fun a _ => h2 a a a
  have V5 : (∑ a, ∑ b, F a b a a) = 0 := Finset.sum_eq_zero fun a _ => h1 a a a
  have V6 : (∑ a, ∑ b, F a b b b) = 0 := by
    rw [Finset.sum_comm]
    exact Finset.sum_eq_zero fun b _ => h0 b b b
  -- STEP 4.  Split each of the five sums into its `F`-pieces and substitute.
  have S1 : (∑ a, ∑ b, ∑ c, -(F a b c a + F a b c b + F a b c c)) = 0 := by
    rw [sum3_neg (fun a b c => F a b c a + F a b c b + F a b c c),
      sum3_add3 (fun a b c => F a b c a) (fun a b c => F a b c b) (fun a b c => F a b c c),
      V1, V2, V3]
    ring
  have S2 : (∑ a, ∑ c, -(F a a c a + F a a c a + F a a c c)) = -∑ a, ∑ c, F a a c c := by
    rw [sum2_neg (fun a c => F a a c a + F a a c a + F a a c c),
      sum2_add3 (fun a c => F a a c a) (fun a c => F a a c a) (fun a c => F a a c c), V4]
    ring
  have S3 : (∑ a, ∑ b, -(F a b a a + F a b a b + F a b a a)) = -∑ a, ∑ b, F a b a b := by
    rw [sum2_neg (fun a b => F a b a a + F a b a b + F a b a a),
      sum2_add3 (fun a b => F a b a a) (fun a b => F a b a b) (fun a b => F a b a a), V5]
    ring
  have S4 : (∑ a, ∑ b, -(F a b b a + F a b b b + F a b b b)) = -∑ a, ∑ b, F a b b a := by
    rw [sum2_neg (fun a b => F a b b a + F a b b b + F a b b b),
      sum2_add3 (fun a b => F a b b a) (fun a b => F a b b b) (fun a b => F a b b b), V6]
    ring
  have S5 : (∑ a, -(F a a a a + F a a a a + F a a a a)) = -(3 * ∑ a, F a a a a) := by
    rw [sum1_neg (fun a => F a a a a + F a a a a + F a a a a),
      sum1_add3 (fun a => F a a a a) (fun a => F a a a a) (fun a => F a a a a)]
    ring
  rw [S1, S2, S3, S4, S5]
  ring

/-! ## §2  The invariants of the centred slice

`Q`, `p₄`, `Y_R`, `Y_C`, `Z` in the notation of the source's §2. -/

/-- `P x y = ∑ⱼ B x j B y j`, the `(x,y)` entry of `B Bᵀ`: the column inner product of two
rows. -/
noncomputable def P (B : Matrix (Fin n) (Fin n) ℝ) (x y : Fin n) : ℝ := ∑ j, B x j * B y j

/-- `P₄ a b c d = ∑ⱼ B a j B b j B c j B d j`. -/
noncomputable def P4 (B : Matrix (Fin n) (Fin n) ℝ) (a b c d : Fin n) : ℝ :=
  ∑ j, B a j * B b j * B c j * B d j

/-- `Q = ‖B‖²_F`. -/
noncomputable def frobQ (B : Matrix (Fin n) (Fin n) ℝ) : ℝ := ∑ i, ∑ j, B i j ^ 2

/-- `p₄ = ∑ b_ij⁴`. -/
noncomputable def pFour (B : Matrix (Fin n) (Fin n) ℝ) : ℝ := ∑ i, ∑ j, B i j ^ 4

/-- `Y_R = ∑ᵢ qᵢ²` with `qᵢ = ∑ⱼ b_ij²`. -/
noncomputable def YR (B : Matrix (Fin n) (Fin n) ℝ) : ℝ := ∑ i, (∑ j, B i j ^ 2) ^ 2

/-- `Y_C = ∑ⱼ q'ⱼ²` with `q'ⱼ = ∑ᵢ b_ij²`. -/
noncomputable def YC (B : Matrix (Fin n) (Fin n) ℝ) : ℝ := ∑ j, (∑ i, B i j ^ 2) ^ 2

/-- `Z = ‖BᵀB‖²_F`, exactly as the source defines it. -/
noncomputable def Zinv (B : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ∑ i, ∑ j, (∑ k, B k i * B k j) ^ 2

section Bridges

variable (B : Matrix (Fin n) (Fin n) ℝ)

private theorem pair_factor (u v : Fin n → ℝ) :
    (∑ x, ∑ y, u x * v y) = (∑ x, u x) * (∑ y, v y) :=
  (Finset.sum_mul_sum _ _ _ _).symm

theorem P_apply (x y : Fin n) : P B x y = ∑ j, B x j * B y j := rfl

theorem P4_apply (a b c d : Fin n) :
    P4 B a b c d = ∑ j, B a j * B b j * B c j * B d j := rfl

theorem P_symm (x y : Fin n) : P B x y = P B y x :=
  Finset.sum_congr rfl fun _ _ => mul_comm _ _

theorem P_diag (x : Fin n) : P B x x = ∑ j, B x j ^ 2 :=
  Finset.sum_congr rfl fun j _ => (sq (B x j)).symm

theorem sum_P_diag : (∑ x, P B x x) = frobQ B :=
  Finset.sum_congr rfl fun x _ => P_diag B x

theorem sum_P_diag_sq : (∑ x, (P B x x) ^ 2) = YR B :=
  Finset.sum_congr rfl fun x _ => by rw [P_diag]

/-- Interchanging the outer index pair with the inner one in a fourfold sum. -/
private theorem swap_pairs (T : Fin n → Fin n → Fin n → Fin n → ℝ) :
    (∑ i, ∑ j, ∑ k, ∑ l, T i j k l) = ∑ k, ∑ l, ∑ i, ∑ j, T i j k l := by
  rw [Finset.sum_congr rfl fun i (_ : i ∈ univ) => Finset.sum_comm, Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_congr rfl fun i (_ : i ∈ univ) => Finset.sum_comm, Finset.sum_comm]

/-- `‖BᵀB‖²_F = ‖BBᵀ‖²_F`: expand both squares and interchange the index pairs.  The source
writes `Z` the first way; the row sieve of §3 produces the second. -/
theorem Zinv_eq_rows : Zinv B = ∑ x, ∑ y, (P B x y) ^ 2 := by
  have expand : ∀ i j : Fin n, (∑ k, B k i * B k j) ^ 2
      = ∑ k, ∑ l, (B k i * B l i) * (B k j * B l j) := by
    intro i j
    rw [sq, ← pair_factor (fun k => B k i * B k j) (fun l => B l i * B l j)]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
  have expand' : ∀ x y : Fin n, (P B x y) ^ 2
      = ∑ i, ∑ j, (B x i * B y i) * (B x j * B y j) := by
    intro x y
    rw [P_apply, sq, ← pair_factor (fun i => B x i * B y i) (fun j => B x j * B y j)]
  rw [Zinv, Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => expand i j,
    Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => expand' x y,
    swap_pairs (fun i j k l => (B k i * B l i) * (B k j * B l j))]

theorem sum_P_sq : (∑ x, ∑ y, (P B x y) ^ 2) = Zinv B := (Zinv_eq_rows B).symm

theorem sum_P4_pair : (∑ x, ∑ y, P4 B x x y y) = YC B := by
  have hterm : ∀ x y : Fin n, P4 B x x y y = ∑ j, (B x j ^ 2) * (B y j ^ 2) := by
    intro x y
    rw [P4_apply]
    exact Finset.sum_congr rfl fun j _ => by ring
  have swapj : (∑ x, ∑ y, ∑ j, (B x j ^ 2) * (B y j ^ 2))
      = ∑ j, ∑ x, ∑ y, (B x j ^ 2) * (B y j ^ 2) := by
    rw [Finset.sum_congr rfl fun x (_ : x ∈ univ) => Finset.sum_comm]
    exact Finset.sum_comm
  rw [Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => hterm x y, swapj, YC]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [pair_factor (fun x => B x j ^ 2) (fun y => B y j ^ 2), sq]

theorem sum_P4_diag : (∑ x, P4 B x x x x) = pFour B := by
  rw [pFour]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [P4_apply]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem sum_P4_cross : (∑ x, ∑ y, P4 B x y x y) = YC B := by
  rw [show (∑ x, ∑ y, P4 B x y x y) = ∑ x, ∑ y, P4 B x x y y from
    Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by
      rw [P4_apply, P4_apply]
      exact Finset.sum_congr rfl fun j _ => by ring]
  exact sum_P4_pair B

theorem sum_P4_swap : (∑ x, ∑ y, P4 B x y y x) = YC B := by
  rw [show (∑ x, ∑ y, P4 B x y y x) = ∑ x, ∑ y, P4 B x x y y from
    Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by
      rw [P4_apply, P4_apply]
      exact Finset.sum_congr rfl fun j _ => by ring]
  exact sum_P4_pair B

/-- With the COLUMN sums vanishing, `P` has vanishing marginals in each slot. -/
theorem sum_P_col_zero (hc : ∀ j, ∑ i, B i j = 0) (y : Fin n) : (∑ x, P B x y) = 0 := by
  rw [show (∑ x, P B x y) = ∑ x, ∑ j, B x j * B y j from rfl, Finset.sum_comm]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [← Finset.sum_mul, hc j, zero_mul]

theorem sum_P_row_zero (hc : ∀ j, ∑ i, B i j = 0) (x : Fin n) : (∑ y, P B x y) = 0 := by
  rw [Finset.sum_congr rfl fun y _ => P_symm B x y]
  exact sum_P_col_zero B hc x

/-- With the COLUMN sums vanishing, `P₄` has vanishing marginals in each slot. -/
theorem sum_P4_zero (hc : ∀ j, ∑ i, B i j = 0) (b c d : Fin n) :
    (∑ a, P4 B a b c d) = 0 := by
  rw [show (∑ a, P4 B a b c d) = ∑ a, ∑ j, B a j * B b j * B c j * B d j from rfl,
    Finset.sum_comm]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [Finset.sum_congr rfl fun a (_ : a ∈ univ) =>
      (by ring : B a j * B b j * B c j * B d j = B a j * (B b j * B c j * B d j)),
    ← Finset.sum_mul, hc j, zero_mul]

theorem P4_perm1 (a b c d : Fin n) : P4 B a b c d = P4 B b a c d :=
  Finset.sum_congr rfl fun _ _ => by ring

theorem P4_perm2 (a b c d : Fin n) : P4 B a b c d = P4 B c b a d :=
  Finset.sum_congr rfl fun _ _ => by ring

theorem P4_perm3 (a b c d : Fin n) : P4 B a b c d = P4 B d b c a :=
  Finset.sum_congr rfl fun _ _ => by ring

theorem sum_P4_zero1 (hc : ∀ j, ∑ i, B i j = 0) (a c d : Fin n) :
    (∑ b, P4 B a b c d) = 0 := by
  rw [Finset.sum_congr rfl fun b _ => P4_perm1 B a b c d]
  exact sum_P4_zero B hc a c d

theorem sum_P4_zero2 (hc : ∀ j, ∑ i, B i j = 0) (a b d : Fin n) :
    (∑ c, P4 B a b c d) = 0 := by
  rw [Finset.sum_congr rfl fun c _ => P4_perm2 B a b c d]
  exact sum_P4_zero B hc b a d

theorem sum_P4_zero3 (hc : ∀ j, ∑ i, B i j = 0) (a b c : Fin n) :
    (∑ d, P4 B a b c d) = 0 := by
  rw [Finset.sum_congr rfl fun d _ => P4_perm3 B a b c d]
  exact sum_P4_zero B hc b c a

end Bridges

/-! ## §3  The two sieve applications, and (4.3) -/

/-- `W₄`, the value of the inner column sieve: the three column pairings and the column block. -/
noncomputable def W4 (B : Matrix (Fin n) (Fin n) ℝ) (a b c d : Fin n) : ℝ :=
  P B a b * P B c d + P B a c * P B b d + P B a d * P B b c - 6 * P4 B a b c d

/-- **The column sieve.**  With the ROW sums of `B` vanishing, the inner sum over distinct
columns collapses to the four singleton-free column partitions. -/
theorem inner_sieve_four (B : Matrix (Fin n) (Fin n) ℝ) (hr : ∀ i, ∑ j, B i j = 0)
    (a b c d : Fin n) :
    (∑ e, ∑ f, ∑ g, ∑ h,
        (if e ≠ f ∧ e ≠ g ∧ e ≠ h ∧ f ≠ g ∧ f ≠ h ∧ g ≠ h then
          B a e * B b f * B c g * B d h else 0))
      = W4 B a b c d := by
  have E1 : (∑ x, ∑ y, B a x * B b x * B c y * B d y) = P B a b * P B c d := by
    rw [show (∑ x, ∑ y, B a x * B b x * B c y * B d y)
        = ∑ x, ∑ y, (B a x * B b x) * (B c y * B d y) from
      Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring]
    exact pair_factor (fun x => B a x * B b x) (fun y => B c y * B d y)
  have E2 : (∑ x, ∑ y, B a x * B b y * B c x * B d y) = P B a c * P B b d := by
    rw [show (∑ x, ∑ y, B a x * B b y * B c x * B d y)
        = ∑ x, ∑ y, (B a x * B c x) * (B b y * B d y) from
      Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring]
    exact pair_factor (fun x => B a x * B c x) (fun y => B b y * B d y)
  have E3 : (∑ x, ∑ y, B a x * B b y * B c y * B d x) = P B a d * P B b c := by
    rw [show (∑ x, ∑ y, B a x * B b y * B c y * B d x)
        = ∑ x, ∑ y, (B a x * B d x) * (B b y * B c y) from
      Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring]
    exact pair_factor (fun x => B a x * B d x) (fun y => B b y * B c y)
  have E4 : (∑ x, B a x * B b x * B c x * B d x) = P4 B a b c d := rfl
  rw [sum_distinct_four_of_marginals_zero (fun e f g h => B a e * B b f * B c g * B d h)
    (fun f g h => by
      rw [Finset.sum_congr rfl fun e (_ : e ∈ univ) =>
          (by ring : B a e * B b f * B c g * B d h = B a e * (B b f * B c g * B d h)),
        ← Finset.sum_mul, hr a, zero_mul])
    (fun e g h => by
      rw [Finset.sum_congr rfl fun f (_ : f ∈ univ) =>
          (by ring : B a e * B b f * B c g * B d h = B b f * (B a e * B c g * B d h)),
        ← Finset.sum_mul, hr b, zero_mul])
    (fun e f h => by
      rw [Finset.sum_congr rfl fun g (_ : g ∈ univ) =>
          (by ring : B a e * B b f * B c g * B d h = B c g * (B a e * B b f * B d h)),
        ← Finset.sum_mul, hr c, zero_mul])
    (fun e f g => by
      rw [Finset.sum_congr rfl fun h (_ : h ∈ univ) =>
          (by ring : B a e * B b f * B c g * B d h = B d h * (B a e * B b f * B c g)),
        ← Finset.sum_mul, hr d, zero_mul])]
  show (∑ x, ∑ y, B a x * B b x * B c y * B d y)
      + (∑ x, ∑ y, B a x * B b y * B c x * B d y)
      + (∑ x, ∑ y, B a x * B b y * B c y * B d x)
      - 6 * ∑ x, B a x * B b x * B c x * B d x = W4 B a b c d
  rw [E1, E2, E3, E4, W4]

/-- **The row sieve.**  With the COLUMN sums of `B` vanishing, `W₄` has vanishing marginals, so
the outer sum over distinct rows collapses to the four singleton-free row partitions. -/
theorem outer_sieve_four (B : Matrix (Fin n) (Fin n) ℝ) (hc : ∀ j, ∑ i, B i j = 0) :
    (∑ a, ∑ b, ∑ c, ∑ d,
        (if a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d then W4 B a b c d else 0))
      = 3 * (frobQ B ^ 2 + 2 * Zinv B - 6 * YC B) - 6 * (3 * YR B - 6 * pFour B) := by
  -- the four marginals of `W₄`, each a sum of four vanishing pieces
  have split : ∀ (u : Fin n → ℝ) (F1 F2 F3 F4 : Fin n → ℝ),
      (∀ x, u x = F1 x + F2 x + F3 x - 6 * F4 x) →
      (∑ x, u x) = (∑ x, F1 x) + (∑ x, F2 x) + (∑ x, F3 x) - 6 * ∑ x, F4 x := by
    intro u F1 F2 F3 F4 h
    rw [Finset.sum_congr rfl fun x _ => h x]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  have m0 : ∀ b c d : Fin n, (∑ a, W4 B a b c d) = 0 := by
    intro b c d
    rw [split _ (fun a => P B a b * P B c d) (fun a => P B a c * P B b d)
      (fun a => P B a d * P B b c) (fun a => P4 B a b c d) (fun _ => by simp only [W4]),
      ← Finset.sum_mul, ← Finset.sum_mul, ← Finset.sum_mul,
      sum_P_col_zero B hc b, sum_P_col_zero B hc c, sum_P_col_zero B hc d,
      sum_P4_zero B hc b c d]
    ring
  have m1 : ∀ a c d : Fin n, (∑ b, W4 B a b c d) = 0 := by
    intro a c d
    rw [split _ (fun b => P B a b * P B c d) (fun b => P B a c * P B b d)
      (fun b => P B a d * P B b c) (fun b => P4 B a b c d) (fun _ => by simp only [W4]),
      ← Finset.sum_mul, sum_P_row_zero B hc a, ← Finset.mul_sum, sum_P_col_zero B hc d,
      ← Finset.mul_sum, sum_P_col_zero B hc c, sum_P4_zero1 B hc a c d]
    ring
  have m2 : ∀ a b d : Fin n, (∑ c, W4 B a b c d) = 0 := by
    intro a b d
    rw [split _ (fun c => P B a b * P B c d) (fun c => P B a c * P B b d)
      (fun c => P B a d * P B b c) (fun c => P4 B a b c d) (fun _ => by simp only [W4]),
      ← Finset.mul_sum, sum_P_col_zero B hc d, ← Finset.sum_mul, sum_P_row_zero B hc a,
      ← Finset.mul_sum, sum_P_row_zero B hc b, sum_P4_zero2 B hc a b d]
    ring
  have m3 : ∀ a b c : Fin n, (∑ d, W4 B a b c d) = 0 := by
    intro a b c
    rw [split _ (fun d => P B a b * P B c d) (fun d => P B a c * P B b d)
      (fun d => P B a d * P B b c) (fun d => P4 B a b c d) (fun _ => by simp only [W4]),
      ← Finset.mul_sum, sum_P_row_zero B hc c, ← Finset.mul_sum, sum_P_row_zero B hc b,
      ← Finset.sum_mul, sum_P_row_zero B hc a, sum_P4_zero3 B hc a b c]
    ring
  -- the shared evaluations
  have hQ2 : (∑ x, ∑ y, P B x x * P B y y) = frobQ B ^ 2 := by
    rw [pair_factor (fun x => P B x x) (fun y => P B y y), sum_P_diag, sq]
  have hZ1 : (∑ x, ∑ y, P B x y * P B x y) = Zinv B := by
    rw [show (∑ x, ∑ y, P B x y * P B x y) = ∑ x, ∑ y, (P B x y) ^ 2 from
      Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => (sq _).symm]
    exact sum_P_sq B
  have hZ2 : (∑ x, ∑ y, P B x y * P B y x) = Zinv B := by
    rw [show (∑ x, ∑ y, P B x y * P B y x) = ∑ x, ∑ y, (P B x y) ^ 2 from
      Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by
        rw [← P_symm]; exact (sq _).symm]
    exact sum_P_sq B
  have hYR : (∑ x, P B x x * P B x x) = YR B := by
    rw [show (∑ x, P B x x * P B x x) = ∑ x, (P B x x) ^ 2 from
      Finset.sum_congr rfl fun x _ => (sq _).symm]
    exact sum_P_diag_sq B
  rw [sum_distinct_four_of_marginals_zero (W4 B) m0 m1 m2 m3]
  have e1 : (∑ x, ∑ y, W4 B x x y y) = frobQ B ^ 2 + 2 * Zinv B - 6 * YC B := by
    rw [Finset.sum_congr rfl fun x _ =>
      split _ (fun y => P B x x * P B y y) (fun y => P B x y * P B x y)
        (fun y => P B x y * P B x y) (fun y => P4 B x x y y) (fun _ => by simp only [W4])]
    rw [split _ (fun x => ∑ y, P B x x * P B y y) (fun x => ∑ y, P B x y * P B x y)
      (fun x => ∑ y, P B x y * P B x y) (fun x => ∑ y, P4 B x x y y)
      (fun _ => by simp only []),
      hQ2, hZ1, sum_P4_pair]
    ring
  have e2 : (∑ x, ∑ y, W4 B x y x y) = frobQ B ^ 2 + 2 * Zinv B - 6 * YC B := by
    rw [Finset.sum_congr rfl fun x _ =>
      split _ (fun y => P B x y * P B x y) (fun y => P B x x * P B y y)
        (fun y => P B x y * P B y x) (fun y => P4 B x y x y) (fun _ => by simp only [W4])]
    rw [split _ (fun x => ∑ y, P B x y * P B x y) (fun x => ∑ y, P B x x * P B y y)
      (fun x => ∑ y, P B x y * P B y x) (fun x => ∑ y, P4 B x y x y) (fun _ => by simp only []),
      hQ2, hZ1, hZ2, sum_P4_cross]
    ring
  have e3 : (∑ x, ∑ y, W4 B x y y x) = frobQ B ^ 2 + 2 * Zinv B - 6 * YC B := by
    rw [Finset.sum_congr rfl fun x _ =>
      split _ (fun y => P B x y * P B y x) (fun y => P B x y * P B y x)
        (fun y => P B x x * P B y y) (fun y => P4 B x y y x) (fun _ => by simp only [W4])]
    rw [split _ (fun x => ∑ y, P B x y * P B y x) (fun x => ∑ y, P B x y * P B y x)
      (fun x => ∑ y, P B x x * P B y y) (fun x => ∑ y, P4 B x y y x) (fun _ => by simp only []),
      hQ2, hZ2, sum_P4_swap]
    ring
  have e4 : (∑ x, W4 B x x x x) = 3 * YR B - 6 * pFour B := by
    rw [split _ (fun x => P B x x * P B x x) (fun x => P B x x * P B x x)
      (fun x => P B x x * P B x x) (fun x => P4 B x x x x) (fun _ => by simp only [W4]),
      hYR, sum_P4_diag]
    ring
  rw [e1, e2, e3, e4]
  ring

/-- **The rook sum at `k = 4` as a plain eightfold sum against the two indicators.** -/
theorem rook_four_quad (B : Matrix (Fin n) (Fin n) ℝ) :
    (∑ f : Fin 4 ↪ Fin n, ∑ g : Fin 4 ↪ Fin n, ∏ a, B (f a) (g a))
      = ∑ a, ∑ b, ∑ c, ∑ d,
          (if a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d then
            (∑ e, ∑ f, ∑ g, ∑ h,
              (if e ≠ f ∧ e ≠ g ∧ e ≠ h ∧ f ≠ g ∧ f ≠ h ∧ g ≠ h then
                B a e * B b f * B c g * B d h else 0))
            else 0) := by
  rw [sum_emb_four (fun f : Fin 4 → Fin n => ∑ g : Fin 4 ↪ Fin n, ∏ a, B (f a) (g a))]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  by_cases h : a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d
  · rw [if_pos h, if_pos h,
      sum_emb_four (fun g : Fin 4 → Fin n => ∏ x, B (![a, b, c, d] x) (g x))]
    refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun f _ =>
      Finset.sum_congr rfl fun g _ => Finset.sum_congr rfl fun h _ => ?_
    by_cases h2 : e ≠ f ∧ e ≠ g ∧ e ≠ h ∧ f ≠ g ∧ f ≠ h ∧ g ≠ h
    · rw [if_pos h2, if_pos h2, Fin.prod_univ_four]
      simp
    · rw [if_neg h2, if_neg h2]
  · rw [if_neg h, if_neg h]

/-- **(4.3).**  `σ₄(B) = (3/2)p₄ + (1/8)Q² + (1/4)Z − (3/4)Y_R − (3/4)Y_C` for `B` with
vanishing row and column sums.  Both hypotheses are used: the row sums kill the column
singletons, the column sums the row singletons. -/
theorem sigma_four_centred (B : Matrix (Fin n) (Fin n) ℝ)
    (hr : ∀ i, ∑ j, B i j = 0) (hc : ∀ j, ∑ i, B i j = 0) :
    RookSum.sigP 4 B
      = 3 / 2 * pFour B + 1 / 8 * frobQ B ^ 2 + 1 / 4 * Zinv B
        - 3 / 4 * YR B - 3 / 4 * YC B := by
  have hemb := LayerIdentity.sigma_emb (k := 4) B
  rw [show ((Nat.factorial 4 : ℕ) : ℝ) = 24 from by norm_num [Nat.factorial]] at hemb
  rw [rook_four_quad B] at hemb
  have hsub : ∀ a b c d : Fin n,
      (if a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d then
        (∑ e, ∑ f, ∑ g, ∑ h,
          (if e ≠ f ∧ e ≠ g ∧ e ≠ h ∧ f ≠ g ∧ f ≠ h ∧ g ≠ h then
            B a e * B b f * B c g * B d h else 0)) else 0)
        = (if a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d then W4 B a b c d else 0) := by
    intro a b c d
    by_cases h : a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d
    · rw [if_pos h, if_pos h, inner_sieve_four B hr a b c d]
    · rw [if_neg h, if_neg h]
  rw [Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => hsub a b c d] at hemb
  rw [outer_sieve_four B hc] at hemb
  linarith [hemb]

/-! ## §4  Axiom audit

**Every declaration in this file depends only on axioms among `propext,
Classical.choice, Quot.sound`.**  No `native_decide`, no `sorry`. -/

section AxiomAudit

#print axioms injective_four
#print axioms sum_fun_four
#print axioms sum_emb_four
#print axioms sum1_neg
#print axioms sum2_neg
#print axioms sum3_neg
#print axioms sum1_add3
#print axioms sum2_add3
#print axioms sum3_add3
#print axioms sum_compl_triple
#print axioms sum_distinct_four_of_marginals_zero
#print axioms P
#print axioms P4
#print axioms frobQ
#print axioms pFour
#print axioms YR
#print axioms YC
#print axioms Zinv
#print axioms pair_factor
#print axioms P_apply
#print axioms P4_apply
#print axioms P_symm
#print axioms P_diag
#print axioms sum_P_diag
#print axioms sum_P_diag_sq
#print axioms swap_pairs
#print axioms Zinv_eq_rows
#print axioms sum_P_sq
#print axioms sum_P4_pair
#print axioms sum_P4_diag
#print axioms sum_P4_cross
#print axioms sum_P4_swap
#print axioms sum_P_col_zero
#print axioms sum_P_row_zero
#print axioms sum_P4_zero
#print axioms P4_perm1
#print axioms P4_perm2
#print axioms P4_perm3
#print axioms sum_P4_zero1
#print axioms sum_P4_zero2
#print axioms sum_P4_zero3
#print axioms W4
#print axioms inner_sieve_four
#print axioms outer_sieve_four
#print axioms rook_four_quad
#print axioms sigma_four_centred

end AxiomAudit

end SigmaFour
