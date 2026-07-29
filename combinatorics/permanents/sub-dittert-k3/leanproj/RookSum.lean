/-
# Rook sums

`sigma_k(A)` is defined as a sum over pairs of `k`-subsets of the permanents of the
corresponding submatrices.  Every algebraic manipulation of it instead wants a sum
over *tuples* of indices.  This file is the bridge, proved once for all `k`:

* `sum_emb_eq_sum_powersetCard` — summing a function of an injection `Fin k → Fin n`
  over all injections is the same as summing over `k`-subsets and then over the
  `k!` orderings of each;
* `sum_emb_three` — at `k = 3`, that sum written as an ordinary triple sum against
  the distinctness indicator;
* `sum_distinct_three` — the inclusion–exclusion that removes the indicator.

Nothing here mentions permanents; the content is the bijection

    (k-subset, permutation of Fin k)  ↔  injection Fin k → Fin n

together with the three-index sieve.
-/
import Mathlib.Tactic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Powerset
import Mathlib.Logic.Embedding.Basic
import Mathlib.LinearAlgebra.Matrix.Permanent

open Finset

namespace RookSum

variable {n k : ℕ} {M : Type*} [AddCommMonoid M]

/-! ## 1.  Injections versus subsets -/

/-- The reorderings of the increasing enumeration of `T`, summed.  Kept total in `T`
by a `dite`, so that it is an ordinary summand over `Finset.powersetCard`. -/
def embSum (k : ℕ) (F : (Fin k → Fin n) → M) (T : Finset (Fin n)) : M :=
  if hT : T.card = k then
    ∑ σ : Equiv.Perm (Fin k), F (fun a => T.orderEmbOfFin hT (σ a))
  else 0

theorem embSum_of_card {F : (Fin k → Fin n) → M} {T : Finset (Fin n)} (hT : T.card = k) :
    embSum k F T = ∑ σ : Equiv.Perm (Fin k), F (fun a => T.orderEmbOfFin hT (σ a)) :=
  dif_pos hT

/-- The injection obtained by reordering the increasing enumeration of `T` by `σ`. -/
def permEmb {T : Finset (Fin n)} (hT : T.card = k) (σ : Equiv.Perm (Fin k)) : Fin k ↪ Fin n :=
  ⟨fun a => T.orderEmbOfFin hT (σ a),
    Function.Injective.comp (T.orderEmbOfFin hT).injective σ.injective⟩

@[simp] theorem permEmb_apply {T : Finset (Fin n)} (hT : T.card = k) (σ : Equiv.Perm (Fin k))
    (a : Fin k) : permEmb hT σ a = T.orderEmbOfFin hT (σ a) := rfl

theorem map_permEmb {T : Finset (Fin n)} (hT : T.card = k) (σ : Equiv.Perm (Fin k)) :
    Finset.map (permEmb hT σ) univ = T := by
  refine Finset.eq_of_subset_of_card_le ?_ ?_
  · intro x hx
    simp only [Finset.mem_map, Finset.mem_univ, true_and] at hx
    obtain ⟨a, rfl⟩ := hx
    exact T.orderEmbOfFin_mem hT _
  · rw [Finset.card_map, Finset.card_univ, Fintype.card_fin]
    exact hT.le

/-- **Every injection factors through the increasing enumeration of its image.**
This is the surjectivity half of the subset/injection bijection. -/
theorem exists_perm_eq {T : Finset (Fin n)} (hT : T.card = k) (f : Fin k → Fin n)
    (hinj : Function.Injective f) (hmem : ∀ a, f a ∈ T) :
    ∃ σ : Equiv.Perm (Fin k), ∀ a, T.orderEmbOfFin hT (σ a) = f a := by
  set e := T.orderIsoOfFin hT with he
  have hg : Function.Injective (fun a => e.symm ⟨f a, hmem a⟩) := by
    intro a b hab
    have h1 : (⟨f a, hmem a⟩ : {x // x ∈ T}) = ⟨f b, hmem b⟩ := e.symm.injective hab
    exact hinj (Subtype.ext_iff.mp h1)
  refine ⟨Equiv.ofBijective _ (Finite.injective_iff_bijective.mp hg), fun a => ?_⟩
  have happ : e (e.symm ⟨f a, hmem a⟩) = ⟨f a, hmem a⟩ := e.apply_symm_apply _
  have hcoe : T.orderEmbOfFin hT (e.symm ⟨f a, hmem a⟩)
      = ((e (e.symm ⟨f a, hmem a⟩) : {x // x ∈ T}) : Fin n) :=
    (Finset.coe_orderIsoOfFin_apply T hT _).symm
  rw [show (Equiv.ofBijective _ (Finite.injective_iff_bijective.mp hg)) a
        = e.symm ⟨f a, hmem a⟩ from rfl, hcoe, happ]

/-- The injections with image `T` are exactly the reorderings of its increasing
enumeration. -/
theorem sum_fiber (F : (Fin k → Fin n) → M) {T : Finset (Fin n)} (hT : T.card = k) :
    embSum k F T
      = ∑ f ∈ (univ : Finset (Fin k ↪ Fin n)).filter (fun f => Finset.map f univ = T), F f := by
  rw [embSum_of_card hT]
  refine Finset.sum_bij (fun σ _ => permEmb hT σ) ?_ ?_ ?_ ?_
  · intro σ _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact map_permEmb hT σ
  · intro σ₁ _ σ₂ _ h
    refine Equiv.ext fun a => ?_
    have : T.orderEmbOfFin hT (σ₁ a) = T.orderEmbOfFin hT (σ₂ a) := by
      simpa using congrArg (fun g : Fin k ↪ Fin n => g a) h
    exact (T.orderEmbOfFin hT).injective this
  · intro f hf
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf
    have hmem : ∀ a, f a ∈ T := by
      intro a
      rw [← hf]
      simp
    obtain ⟨σ, hσ⟩ := exists_perm_eq hT f f.injective hmem
    exact ⟨σ, Finset.mem_univ σ, Function.Embedding.ext (fun a => hσ a)⟩
  · intro σ _
    rfl

/-- **Injections versus subsets.**  A sum over all injections `Fin k → Fin n` breaks
up as a sum over the `k`-subsets of the `k!` reorderings of each. -/
theorem sum_emb_eq_sum_powersetCard (F : (Fin k → Fin n) → M) :
    ∑ f : Fin k ↪ Fin n, F f
      = ∑ T ∈ Finset.powersetCard k (univ : Finset (Fin n)), embSum k F T := by
  have hmaps : ∀ f ∈ (univ : Finset (Fin k ↪ Fin n)),
      Finset.map f univ ∈ Finset.powersetCard k (univ : Finset (Fin n)) := by
    intro f _
    rw [Finset.mem_powersetCard_univ, Finset.card_map, Finset.card_univ, Fintype.card_fin]
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun f : Fin k ↪ Fin n => F f)]
  exact Finset.sum_congr rfl fun T hT => (sum_fiber F (Finset.mem_powersetCard_univ.mp hT)).symm

/-! ## 2.  The case `k = 3` as a triple sum -/

/-- `![a, b, c]` is injective exactly when the three entries are pairwise distinct. -/
theorem injective_three {a b c : Fin n} :
    Function.Injective ![a, b, c] ↔ a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  constructor
  · intro h
    refine ⟨fun hab => ?_, fun hac => ?_, fun hbc => ?_⟩
    · have h01 : ![a, b, c] 0 = ![a, b, c] 1 := by simp [hab]
      exact absurd (h h01) (by decide)
    · have h02 : ![a, b, c] 0 = ![a, b, c] 2 := by simp [hac]
      exact absurd (h h02) (by decide)
    · have h12 : ![a, b, c] 1 = ![a, b, c] 2 := by simp [hbc]
      exact absurd (h h12) (by decide)
  · rintro ⟨h1, h2, h3⟩ i j hij
    fin_cases i <;> fin_cases j <;> simp_all

/-- A sum over functions `Fin 3 → Fin n` as an iterated triple sum. -/
theorem sum_fun_three (G : (Fin 3 → Fin n) → M) :
    ∑ f : Fin 3 → Fin n, G f = ∑ a, ∑ b, ∑ c, G ![a, b, c] := by
  let e : (Fin n × Fin n × Fin n) ≃ (Fin 3 → Fin n) :=
    { toFun := fun p => ![p.1, p.2.1, p.2.2]
      invFun := fun f => (f 0, f 1, f 2)
      left_inv := by intro p; rfl
      right_inv := by intro f; funext i; fin_cases i <;> rfl }
  rw [← Equiv.sum_comp e G, Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun a _ => by rw [Fintype.sum_prod_type]; rfl

/-- **The `k = 3` injection sum as a triple sum.** -/
theorem sum_emb_three (F : (Fin 3 → Fin n) → M) :
    ∑ f : Fin 3 ↪ Fin n, F f
      = ∑ a, ∑ b, ∑ c, (if a ≠ b ∧ a ≠ c ∧ b ≠ c then F ![a, b, c] else 0) := by
  have h1 : ∑ f : Fin 3 ↪ Fin n, F f
      = ∑ f ∈ (univ : Finset (Fin 3 → Fin n)).filter Function.Injective, F f := by
    rw [Finset.sum_subtype (p := fun f : Fin 3 → Fin n => Function.Injective f)
      ((univ : Finset (Fin 3 → Fin n)).filter Function.Injective)
      (fun x => by simp) F]
    exact (Fintype.sum_equiv (Equiv.subtypeInjectiveEquivEmbedding (Fin 3) (Fin n))
      _ _ (fun p => rfl)).symm
  rw [h1, Finset.sum_filter, sum_fun_three]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun c _ => ?_
  by_cases h : a ≠ b ∧ a ≠ c ∧ b ≠ c
  · rw [if_pos (injective_three.mpr h), if_pos h]
  · rw [if_neg (fun hc => h (injective_three.mp hc)), if_neg h]

/-! ## 3.  The three-index sieve -/

/-- **Inclusion–exclusion on three indices.**  The pointwise identity behind it is

    [a,b,c distinct] = 1 − [a=b] − [a=c] − [b=c] + 2·[a=b=c],

checked case by case; the five classes of the partition of `(a,b,c)` by coincidence
pattern make it true. -/
theorem sum_distinct_three (F : Fin n → Fin n → Fin n → ℝ) :
    ∑ a, ∑ b, ∑ c, (if a ≠ b ∧ a ≠ c ∧ b ≠ c then F a b c else 0)
      = (∑ a, ∑ b, ∑ c, F a b c) - (∑ a, ∑ c, F a a c) - (∑ a, ∑ b, F a b a)
        - (∑ a, ∑ b, F a b b) + 2 * ∑ a, F a a a := by
  have key : ∀ a b c : Fin n,
      (if a ≠ b ∧ a ≠ c ∧ b ≠ c then F a b c else 0)
        = F a b c - (if a = b then F a b c else 0) - (if a = c then F a b c else 0)
          - (if b = c then F a b c else 0) + 2 * (if a = b ∧ b = c then F a b c else 0) := by
    intro a b c
    by_cases hab : a = b <;> by_cases hac : a = c <;> by_cases hbc : b = c <;>
      simp_all <;> ring
  have e1 : ∑ a, ∑ b, ∑ c, (if a = b then F a b c else 0) = ∑ a, ∑ c, F a a c := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun c _ => by simp
  have e2 : ∑ a, ∑ b, ∑ c, (if a = c then F a b c else 0) = ∑ a, ∑ b, F a b a :=
    Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by simp
  have e3 : ∑ a, ∑ b, ∑ c, (if b = c then F a b c else 0) = ∑ a, ∑ b, F a b b :=
    Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by simp
  have e4 : ∑ a, ∑ b, ∑ c, (if a = b ∧ b = c then F a b c else 0) = ∑ a, F a a a := by
    refine Finset.sum_congr rfl fun a _ => ?_
    have : ∀ b : Fin n, (∑ c, if a = b ∧ b = c then F a b c else 0)
        = if a = b then F a b b else 0 := by
      intro b
      simp only [ite_and]
      by_cases hab : a = b
      · simp [hab]
      · simp [hab]
    rw [Finset.sum_congr rfl fun b _ => this b]
    simp
  calc ∑ a, ∑ b, ∑ c, (if a ≠ b ∧ a ≠ c ∧ b ≠ c then F a b c else 0)
      = ∑ a, ∑ b, ∑ c, (F a b c - (if a = b then F a b c else 0)
          - (if a = c then F a b c else 0) - (if b = c then F a b c else 0)
          + 2 * (if a = b ∧ b = c then F a b c else 0)) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
          Finset.sum_congr rfl fun c _ => key a b c
    _ = _ := by
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
        rw [e1, e2, e3, e4]

/-! ## 4.  Factorisation and swap helpers

`simp only [← Finset.mul_sum, ← Finset.sum_mul]` pulls out of a sum every factor
that does not depend on the summation variable; higher-order matching refuses the
step when the factor does depend on it, so the normal form is well defined.  The
swap lemmas below are the only places where the order of summation changes, and
they are exactly where a column quantity replaces a row quantity. -/

section Helpers

variable {n : ℕ}

private theorem sum_pair (u v : Fin n → ℝ) :
    (∑ a, ∑ c, u a * v c) = (∑ a, u a) * (∑ c, v c) :=
  (Finset.sum_mul_sum _ _ _ _).symm

private theorem prod_three_sums (u v w : Fin n → ℝ) :
    (∑ a, u a) * (∑ b, v b) * (∑ c, w c) = ∑ a, ∑ b, ∑ c, u a * v b * w c := by
  rw [Finset.sum_mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun b _ => Finset.mul_sum _ _ _

private theorem swap_of_three (f : Fin n → Fin n → Fin n → ℝ) :
    (∑ a, ∑ b, ∑ d, f a b d) = ∑ d, ∑ a, ∑ b, f a b d := by
  rw [Finset.sum_congr rfl fun a (_ : a ∈ univ) => Finset.sum_comm, Finset.sum_comm]

private theorem swap_of_four (f : Fin n → Fin n → Fin n → Fin n → ℝ) :
    (∑ a, ∑ b, ∑ c, ∑ d, f a b c d) = ∑ d, ∑ a, ∑ b, ∑ c, f a b c d := by
  rw [Finset.sum_congr rfl fun a (_ : a ∈ univ) =>
        Finset.sum_congr rfl fun b (_ : b ∈ univ) => Finset.sum_comm,
      Finset.sum_congr rfl fun a (_ : a ∈ univ) => Finset.sum_comm, Finset.sum_comm]

end Helpers

/-! ## 5.  `sigma_3` of a matrix

`subP` and `sigP` are written exactly as `SubDittertK3.subPerm` and
`SubDittertK3.sigmaK`, so that the two are definitionally equal and the bridge
theorem there is `rfl`.  If either definition ever drifts, that bridge fails to
compile — which is the point of stating it. -/

section Sigma3

variable {n : ℕ}

/-- The permanent of the `k × k` submatrix of `A` on rows `S` and columns `T`. -/
def subP (k : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (S T : Finset (Fin n)) : ℝ :=
  if hS : S.card = k then
    if hT : T.card = k then
      (A.submatrix (⇑(S.orderEmbOfFin hS)) (⇑(T.orderEmbOfFin hT))).permanent
    else 0
  else 0

/-- `σ_k(A)`, the sum of the permanents of all `C(n,k)²` submatrices of size `k`. -/
def sigP (k : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ∑ S ∈ Finset.powersetCard k (univ : Finset (Fin n)),
    ∑ T ∈ Finset.powersetCard k (univ : Finset (Fin n)), subP k A S T

theorem subP_apply {k : ℕ} {S T : Finset (Fin n)} (hS : S.card = k) (hT : T.card = k)
    (A : Matrix (Fin n) (Fin n) ℝ) :
    subP k A S T
      = ∑ σ : Equiv.Perm (Fin k), ∏ a, A (S.orderEmbOfFin hS (σ a)) (T.orderEmbOfFin hT a) := by
  unfold subP
  rw [dif_pos hS, dif_pos hT]
  rfl

/-- Reordering the rows of a subpermanent by a fixed permutation, and summing over
the column permutation, is `k!` copies of the subpermanent. -/
private theorem perm_double (A : Matrix (Fin n) (Fin n) ℝ) {S T : Finset (Fin n)}
    (hS : S.card = 3) (hT : T.card = 3) :
    (∑ τ : Equiv.Perm (Fin 3), ∑ σ : Equiv.Perm (Fin 3),
        ∏ a, A (S.orderEmbOfFin hS (τ a)) (T.orderEmbOfFin hT (σ a)))
      = 6 * ∑ ρ : Equiv.Perm (Fin 3),
          ∏ a, A (S.orderEmbOfFin hS (ρ a)) (T.orderEmbOfFin hT a) := by
  have inner : ∀ τ : Equiv.Perm (Fin 3),
      (∑ σ : Equiv.Perm (Fin 3), ∏ a, A (S.orderEmbOfFin hS (τ a)) (T.orderEmbOfFin hT (σ a)))
        = ∑ ρ : Equiv.Perm (Fin 3),
            ∏ a, A (S.orderEmbOfFin hS (ρ a)) (T.orderEmbOfFin hT a) := by
    intro τ
    let E : Equiv.Perm (Fin 3) ≃ Equiv.Perm (Fin 3) :=
      { toFun := fun σ => τ * σ⁻¹
        invFun := fun ρ => (τ⁻¹ * ρ)⁻¹
        left_inv := by intro σ; simp [mul_assoc]
        right_inv := by intro ρ; simp [mul_assoc] }
    rw [← Equiv.sum_comp E
        (fun ρ : Equiv.Perm (Fin 3) =>
          ∏ a, A (S.orderEmbOfFin hS (ρ a)) (T.orderEmbOfFin hT a))]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [show E σ = τ * σ⁻¹ from rfl]
    rw [← Equiv.prod_comp σ (fun x => A (S.orderEmbOfFin hS ((τ * σ⁻¹) x))
          (T.orderEmbOfFin hT x))]
    exact Finset.prod_congr rfl fun a _ => by simp
  rw [Finset.sum_congr rfl fun τ (_ : τ ∈ univ) => inner τ, Finset.sum_const, Finset.card_univ,
    Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
  norm_num [Nat.factorial]

/-- **`6 σ_3` as a doubly ordered rook sum.**  The two `Finset.powersetCard` layers
of the definition become two sums over injections `Fin 3 → Fin n`. -/
theorem sigma_three_emb (A : Matrix (Fin n) (Fin n) ℝ) :
    (∑ f : Fin 3 ↪ Fin n, ∑ g : Fin 3 ↪ Fin n, ∏ a, A (f a) (g a)) = 6 * sigP 3 A := by
  rw [sum_emb_eq_sum_powersetCard
    (fun f : Fin 3 → Fin n => ∑ g : Fin 3 ↪ Fin n, ∏ a, A (f a) (g a))]
  unfold sigP
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun S hS => ?_
  have hS3 : S.card = 3 := Finset.mem_powersetCard_univ.mp hS
  rw [embSum_of_card hS3]
  have step : ∀ τ : Equiv.Perm (Fin 3),
      (∑ g : Fin 3 ↪ Fin n, ∏ a, A (S.orderEmbOfFin hS3 (τ a)) (g a))
        = ∑ T ∈ Finset.powersetCard 3 (univ : Finset (Fin n)),
            embSum 3 (fun g : Fin 3 → Fin n =>
              ∏ a, A (S.orderEmbOfFin hS3 (τ a)) (g a)) T :=
    fun τ => sum_emb_eq_sum_powersetCard
      (fun g : Fin 3 → Fin n => ∏ a, A (S.orderEmbOfFin hS3 (τ a)) (g a))
  rw [Finset.sum_congr rfl fun τ (_ : τ ∈ univ) => step τ, Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun T hT => ?_
  have hT3 : T.card = 3 := Finset.mem_powersetCard_univ.mp hT
  rw [Finset.sum_congr rfl fun τ (_ : τ ∈ univ) =>
      embSum_of_card (F := fun g : Fin 3 → Fin n =>
        ∏ a, A (S.orderEmbOfFin hS3 (τ a)) (g a)) hT3]
  rw [perm_double A hS3 hT3, subP_apply hS3 hT3]

/-- **The rook sum as a plain six-fold sum against the two distinctness indicators.** -/
theorem rook_three_triple (A : Matrix (Fin n) (Fin n) ℝ) :
    (∑ f : Fin 3 ↪ Fin n, ∑ g : Fin 3 ↪ Fin n, ∏ a, A (f a) (g a))
      = ∑ a, ∑ b, ∑ c, (if a ≠ b ∧ a ≠ c ∧ b ≠ c then
          (∑ d, ∑ e, ∑ f, (if d ≠ e ∧ d ≠ f ∧ e ≠ f then A a d * A b e * A c f else 0))
          else 0) := by
  rw [sum_emb_three (fun f : Fin 3 → Fin n => ∑ g : Fin 3 ↪ Fin n, ∏ a, A (f a) (g a))]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun c _ => ?_
  by_cases h : a ≠ b ∧ a ≠ c ∧ b ≠ c
  · rw [if_pos h, if_pos h,
      sum_emb_three (fun g : Fin 3 → Fin n => ∏ x, A (![a, b, c] x) (g x))]
    refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun e _ =>
      Finset.sum_congr rfl fun f _ => ?_
    by_cases h2 : d ≠ e ∧ d ≠ f ∧ e ≠ f
    · rw [if_pos h2, if_pos h2, Fin.prod_univ_three]
      simp
    · rw [if_neg h2, if_neg h2]
  · rw [if_neg h, if_neg h]

/-! ### The column sieve -/

/-- The inner sieve of `6 σ_3`: for fixed rows `a, b, c`, the sum over triples of
*distinct* columns.  `P2` and `P3` below are the column inner products. -/
private def W (A : Matrix (Fin n) (Fin n) ℝ) (a b c : Fin n) : ℝ :=
  (∑ d, A a d) * (∑ d, A b d) * (∑ d, A c d)
  - (∑ d, A a d * A b d) * (∑ d, A c d)
  - (∑ d, A a d * A c d) * (∑ d, A b d)
  - (∑ d, A b d * A c d) * (∑ d, A a d)
  + 2 * ∑ d, A a d * A b d * A c d

private theorem inner_sieve (A : Matrix (Fin n) (Fin n) ℝ) (a b c : Fin n) :
    (∑ d, ∑ e, ∑ f, (if d ≠ e ∧ d ≠ f ∧ e ≠ f then A a d * A b e * A c f else 0))
      = W A a b c := by
  have h1 : (∑ d, ∑ e, ∑ f, A a d * A b e * A c f)
      = (∑ d, A a d) * (∑ d, A b d) * (∑ d, A c d) := (prod_three_sums _ _ _).symm
  have h2 : (∑ d, ∑ f, A a d * A b d * A c f)
      = (∑ d, A a d * A b d) * (∑ d, A c d) := sum_pair _ _
  have h3 : (∑ d, ∑ e, A a d * A b e * A c d)
      = (∑ d, A a d * A c d) * (∑ d, A b d) := by
    rw [← sum_pair (fun d => A a d * A c d) (fun e => A b e)]
    exact Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun e _ => by ring
  have h4 : (∑ d, ∑ e, A a d * A b e * A c e)
      = (∑ d, A b d * A c d) * (∑ d, A a d) := by
    rw [← sum_pair (fun d => A b d * A c d) (fun e => A a e), Finset.sum_comm]
    exact Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun e _ => by ring
  rw [sum_distinct_three (fun d e f => A a d * A b e * A c f), h1, h2, h3, h4]
  unfold W
  ring

/-! ### Ten bridging identities

Each one moves a row-indexed quantity to a column-indexed one, or reassociates a
product inside a sum.  They are exactly the places where the order of summation
changes; everything else in the assembly is `ring`. -/

private theorem colProd (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n) :
    (∑ i, ∑ d, A x d * A i d) = ∑ d, A x d * (∑ i, A i d) := by
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun d _ => (Finset.mul_sum _ _ _).symm

private theorem l1 (A : Matrix (Fin n) (Fin n) ℝ) :
    (∑ i, ∑ j, ∑ d, A i d * A j d) = ∑ j, (∑ i, A i j) * (∑ i, A i j) := by
  rw [swap_of_three]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Finset.sum_mul_sum]

private theorem l2 (A : Matrix (Fin n) (Fin n) ℝ) :
    (∑ i, ∑ j, ∑ k, ∑ d, A i d * A j d * A k d)
      = ∑ j, ((∑ i, A i j) * (∑ i, A i j)) * (∑ i, A i j) := by
  rw [swap_of_four]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [prod_three_sums]

private theorem l3 (A : Matrix (Fin n) (Fin n) ℝ) :
    (∑ x, (∑ i, ∑ d, A x d * A i d) * (∑ d, A x d))
      = ∑ i, ∑ j, A i j * (∑ l, A i l) * (∑ l, A l j) := by
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [colProd, Finset.sum_mul]
  exact Finset.sum_congr rfl fun d _ => by ring

private theorem l4 (A : Matrix (Fin n) (Fin n) ℝ) :
    (∑ x, (∑ i, ∑ d, A i d * A x d) * (∑ d, A x d))
      = ∑ i, ∑ j, A i j * (∑ l, A i l) * (∑ l, A l j) := by
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [show (∑ i, ∑ d, A i d * A x d) = ∑ i, ∑ d, A x d * A i d from
      Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun d _ => mul_comm _ _,
    colProd, Finset.sum_mul]
  exact Finset.sum_congr rfl fun d _ => by ring

private theorem l5 (A : Matrix (Fin n) (Fin n) ℝ) :
    (∑ i, ∑ j, ∑ d, A i d * A i d * A j d)
      = ∑ i, ∑ j, A i j * A i j * (∑ l, A l j) := by
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun d _ => (Finset.mul_sum _ _ _).symm

private theorem l6 (A : Matrix (Fin n) (Fin n) ℝ) :
    (∑ i, ∑ j, ∑ d, A i d * A j d * A i d)
      = ∑ i, ∑ j, A i j * A i j * (∑ l, A l j) := by
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [show (∑ j, A i d * A j d * A i d) = ∑ j, (A i d * A i d) * A j d from
      Finset.sum_congr rfl fun j _ => by ring, ← Finset.mul_sum]

private theorem l7 (A : Matrix (Fin n) (Fin n) ℝ) :
    (∑ i, ∑ j, ∑ d, A i d * A j d * A j d)
      = ∑ i, ∑ j, A i j * A i j * (∑ l, A l j) := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [show (∑ i, A i d * A j d * A j d) = ∑ i, (A j d * A j d) * A i d from
      Finset.sum_congr rfl fun i _ => by ring, ← Finset.mul_sum]

private theorem l8 (A : Matrix (Fin n) (Fin n) ℝ) :
    (∑ x, ∑ y, ((∑ d, A x d) * (∑ d, A y d)) * (∑ d, A y d))
      = (∑ i, ∑ j, A i j) * (∑ i, (∑ j, A i j) * (∑ j, A i j)) := by
  rw [← sum_pair (fun x => ∑ d, A x d) (fun y => (∑ d, A y d) * (∑ d, A y d))]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring

private theorem l9 (A : Matrix (Fin n) (Fin n) ℝ) :
    (∑ x, ∑ y, (∑ d, A x d * A y d) * (∑ d, A y d))
      = ∑ i, ∑ j, A i j * (∑ l, A i l) * (∑ l, A l j) := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [← Finset.sum_mul,
    show (∑ x, ∑ d, A x d * A y d) = ∑ d, A y d * (∑ x, A x d) from by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun d _ => by
        rw [← Finset.sum_mul]; ring,
    Finset.sum_mul]
  exact Finset.sum_congr rfl fun d _ => by ring

private theorem l10 (A : Matrix (Fin n) (Fin n) ℝ) :
    (∑ x, ((∑ d, A x d) * (∑ i, ∑ d, A i d)) * (∑ d, A x d))
      = (∑ i, ∑ j, A i j) * (∑ i, (∑ j, A i j) * (∑ j, A i j)) := by
  rw [show (∑ x, ((∑ d, A x d) * (∑ i, ∑ d, A i d)) * (∑ d, A x d))
      = ∑ x, (∑ i, ∑ d, A i d) * ((∑ d, A x d) * (∑ d, A x d)) from
      Finset.sum_congr rfl fun x _ => by ring, ← Finset.mul_sum]

/-- **The closed form of `σ_3`.**  Valid for every `n` and every real matrix, and
proved from the definition of `σ_3` as a sum of subpermanents — no closed form is
assumed anywhere.  The right-hand side is a polynomial in the entries, the row
sums and the column sums, which is what every later manipulation needs.

⚠ The identity was first checked numerically in Python against the definition at
`n = 3, 4, 5, 6`.  That was **scaffolding, used to design the statement, and it is
superseded by this proof**: the theorem below is quantified over every `n` and is
kernel-checked.  Nothing here rests on four samples, and no reader should take the
sample check as evidence for the identity. -/
theorem sigma_three_closed (A : Matrix (Fin n) (Fin n) ℝ) :
    6 * sigP 3 A
      = (∑ i, ∑ j, A i j) ^ 3
        - 3 * (∑ i, ∑ j, A i j) * ((∑ i, (∑ j, A i j) ^ 2) + (∑ j, (∑ i, A i j) ^ 2))
        + 3 * (∑ i, ∑ j, A i j ^ 2) * (∑ i, ∑ j, A i j)
        + 6 * (∑ i, ∑ j, A i j * (∑ l, A i l) * (∑ l, A l j))
        + 2 * (∑ i, (∑ j, A i j) ^ 3) + 2 * (∑ j, (∑ i, A i j) ^ 3)
        - 6 * (∑ i, ∑ j, A i j ^ 2 * (∑ l, A i l))
        - 6 * (∑ i, ∑ j, A i j ^ 2 * (∑ l, A l j))
        + 4 * (∑ i, ∑ j, A i j ^ 3) := by
  rw [← sigma_three_emb, rook_three_triple]
  simp only [inner_sieve]
  rw [sum_distinct_three (fun a b c => W A a b c)]
  unfold W
  simp only [pow_succ, pow_zero, one_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.sum_mul]
  rw [l1, l2, l3, l4, l5, l6, l7, l8, l9, l10]
  ring

/-! ### The matching closed form for `e_3` -/

/-- A product along the increasing enumeration of `S` is a product over `S`. -/
theorem prod_orderEmbOfFin {k : ℕ} {S : Finset (Fin n)} (hS : S.card = k) (x : Fin n → ℝ) :
    ∏ i : Fin k, x (S.orderEmbOfFin hS i) = ∏ i ∈ S, x i := by
  rw [← Finset.prod_coe_sort S x]
  exact Fintype.prod_equiv (S.orderIsoOfFin hS).toEquiv _ _ fun _ => rfl

/-- **The closed form of `e_3`**, by the same sieve.  This is Newton's identity for
`k = 3`, proved here directly so that it shares the machinery with `sigma_three_closed`
and needs no `MvPolynomial` detour.  Quantified over every `n`; no sampling anywhere. -/
theorem esym_three_closed (v : Fin n → ℝ) :
    6 * ∑ S ∈ Finset.powersetCard 3 (univ : Finset (Fin n)), ∏ i ∈ S, v i
      = (∑ i, v i) ^ 3 - 3 * (∑ i, v i) * (∑ i, v i ^ 2) + 2 * ∑ i, v i ^ 3 := by
  have key : (∑ f : Fin 3 ↪ Fin n, ∏ a, v (f a))
      = 6 * ∑ S ∈ Finset.powersetCard 3 (univ : Finset (Fin n)), ∏ i ∈ S, v i := by
    rw [sum_emb_eq_sum_powersetCard (fun f : Fin 3 → Fin n => ∏ a, v (f a)), Finset.mul_sum]
    refine Finset.sum_congr rfl fun S hS => ?_
    have hS3 : S.card = 3 := Finset.mem_powersetCard_univ.mp hS
    rw [embSum_of_card hS3]
    have hcst : ∀ σ : Equiv.Perm (Fin 3),
        (∏ a, v (S.orderEmbOfFin hS3 (σ a))) = ∏ i ∈ S, v i := by
      intro σ
      rw [Equiv.prod_comp σ (fun x => v (S.orderEmbOfFin hS3 x)), prod_orderEmbOfFin]
    rw [Finset.sum_congr rfl fun σ (_ : σ ∈ univ) => hcst σ, Finset.sum_const, Finset.card_univ,
      Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
    norm_num [Nat.factorial]
  rw [← key, sum_emb_three (fun f : Fin 3 → Fin n => ∏ a, v (f a))]
  have hprod : ∀ a b c : Fin n, (∏ x : Fin 3, v (![a, b, c] x)) = v a * v b * v c := by
    intro a b c
    rw [Fin.prod_univ_three]
    simp
  simp only [hprod]
  rw [sum_distinct_three (fun a b c => v a * v b * v c)]
  have m1 : (∑ a, (v a * (∑ i, v i)) * v a) = (∑ i, v i) * ∑ a, v a * v a := by
    rw [show (∑ a, (v a * (∑ i, v i)) * v a) = ∑ a, (∑ i, v i) * (v a * v a) from
      Finset.sum_congr rfl fun a _ => by ring, ← Finset.mul_sum]
  have m2 : (∑ a, ∑ b, v a * v b * v b) = (∑ i, v i) * ∑ b, v b * v b := by
    rw [← sum_pair (fun a => v a) (fun b => v b * v b)]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  simp only [pow_succ, pow_zero, one_mul, ← Finset.mul_sum, ← Finset.sum_mul]
  rw [m1, m2]
  ring

end Sigma3

/-! ## 6.  Axiom audit -/

section AxiomAudit

#print axioms sum_emb_eq_sum_powersetCard
#print axioms sum_emb_three
#print axioms sum_distinct_three
#print axioms sigma_three_emb
#print axioms rook_three_triple
#print axioms sigma_three_closed
#print axioms esym_three_closed

end AxiomAudit

end RookSum
