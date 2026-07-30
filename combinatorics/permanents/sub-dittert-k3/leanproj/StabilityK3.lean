/-
# A stability form of Tverberg–Friedland at `k ≤ 3`

Target: `graded_stability_lemma.md` Theorem 1 at `k = 2` (every `n ≥ 2`) and `k = 3`
(every `n ≥ 4`), discharging `TverbergStability.StabilityAt` at those cells.

## Why this file does not use the general-`k` layer identity

`graded_stability_lemma.md` proves Theorem 1 through Lemma 2 (§3), the layer identity at
every `k`, whose proof is a fibre count over restrictions of injections.  At `k ≤ 3` that
detour is unnecessary: `RookSum.sigma_three_closed` is a committed general-`n` closed form
for `σ₃` of an arbitrary real matrix, and §1 below proves the matching form for `σ₂`.
Evaluating both on a doubly stochastic `A` and substituting `A = Jₙ/n + B` yields the
`k ≤ 3` instances of Lemma 2 by `ring`, with no counting argument anywhere.  The general-`k`
identity remains worth having — it is what `k = 4, 5` will consume — but it is not on the
critical path to these two cells, and nothing here depends on it.

## Correspondence to the source

| here | source |
|---|---|
| `sigma_two_closed` | the `k = 2` case of §4's expansion, before centring |
| `sigma_two_ds` | Lemma 2 at `k = 2`, in the form `2σ₂(A) = (n−1)² + Q` |
| `sigma_three_ds` | Lemma 2 at `k = 3`, in the form `6σ₃(A) = … + 4p₃` |
| `layer_two`, `layer_three` | Lemma 2 (§3) at `k = 2, 3`, in the source's own shape |
| `entry_lower`, `entry_upper` | Lemma 3 (F1) |
| `cube_ge`, `p_three_ge` | (6.1) and Lemma 4(a) |
| `stabilityAt_two`, `stabilityAt_three` | Theorem 1 at `k = 2` and `k = 3` |

`σ₂(B) = Q/2` and `σ₃(B) = (2/3)p₃` — (4.1) and (4.2) — appear as `sigma_two_centred` and
`sigma_three_centred`; each is the same closed form evaluated at a matrix with vanishing
line sums, so they are substitutions rather than fresh derivations.
-/

import Mathlib.Tactic
import Mathlib.Data.Matrix.DoublyStochastic
import RookSum
import LayerIdentity
import TverbergStability

open Finset

namespace StabilityK3

variable {n : ℕ}

/-! ## §1  `σ₂` by the two-index sieve

The `k = 3` sieve of `RookSum` §2–§3 at `k = 2`.  `LayerIdentity.sigma_emb` already supplies
the bridge from `σ_k` to a double sum over injections at every `k`, so only the two-index
sieve itself is new. -/

/-- `![a, b]` is injective exactly when `a ≠ b`. -/
theorem injective_two {a b : Fin n} : Function.Injective ![a, b] ↔ a ≠ b := by
  constructor
  · intro h hab
    have h01 : ![a, b] 0 = ![a, b] 1 := by simp [hab]
    exact absurd (h h01) (by decide)
  · rintro h1 i j hij
    fin_cases i <;> fin_cases j <;> simp_all

/-- A sum over functions `Fin 2 → Fin n` as an iterated double sum. -/
theorem sum_fun_two {M : Type*} [AddCommMonoid M] (G : (Fin 2 → Fin n) → M) :
    ∑ f : Fin 2 → Fin n, G f = ∑ a, ∑ b, G ![a, b] := by
  let e : (Fin n × Fin n) ≃ (Fin 2 → Fin n) :=
    { toFun := fun p => ![p.1, p.2]
      invFun := fun f => (f 0, f 1)
      left_inv := by intro p; rfl
      right_inv := by intro f; funext i; fin_cases i <;> rfl }
  rw [← Equiv.sum_comp e G, Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => rfl

/-- **The `k = 2` injection sum as a double sum.** -/
theorem sum_emb_two {M : Type*} [AddCommMonoid M] (F : (Fin 2 → Fin n) → M) :
    ∑ f : Fin 2 ↪ Fin n, F f = ∑ a, ∑ b, (if a ≠ b then F ![a, b] else 0) := by
  have h1 : ∑ f : Fin 2 ↪ Fin n, F f
      = ∑ f ∈ (univ : Finset (Fin 2 → Fin n)).filter Function.Injective, F f := by
    rw [Finset.sum_subtype (p := fun f : Fin 2 → Fin n => Function.Injective f)
      ((univ : Finset (Fin 2 → Fin n)).filter Function.Injective)
      (fun x => by simp) F]
    exact (Fintype.sum_equiv (Equiv.subtypeInjectiveEquivEmbedding (Fin 2) (Fin n))
      _ _ (fun p => rfl)).symm
  rw [h1, Finset.sum_filter, sum_fun_two]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  by_cases h : a ≠ b
  · rw [if_pos (injective_two.mpr h), if_pos h]
  · rw [if_neg (fun hc => h (injective_two.mp hc)), if_neg h]

/-- **Inclusion–exclusion on two indices.** -/
theorem sum_distinct_two (F : Fin n → Fin n → ℝ) :
    ∑ a, ∑ b, (if a ≠ b then F a b else 0) = (∑ a, ∑ b, F a b) - ∑ a, F a a := by
  have key : ∀ a b : Fin n,
      (if a ≠ b then F a b else 0) = F a b - (if a = b then F a b else 0) := by
    intro a b
    by_cases hab : a = b <;> simp_all
  have e1 : ∀ a : Fin n,
      (∑ b, (F a b - if a = b then F a b else 0)) = (∑ b, F a b) - F a a := by
    intro a
    rw [Finset.sum_sub_distrib]
    congr 1
    simp
  rw [Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => key a b,
    Finset.sum_congr rfl fun a _ => e1 a, Finset.sum_sub_distrib]

section Helpers

private theorem pair_sum (u v : Fin n → ℝ) :
    (∑ a, ∑ b, u a * v b) = (∑ a, u a) * (∑ b, v b) :=
  (Finset.sum_mul_sum _ _ _ _).symm

/-- The one place the order of summation changes: a row quantity becomes a column one. -/
private theorem col_sq (A : Matrix (Fin n) (Fin n) ℝ) :
    (∑ a, ∑ b, ∑ c, A a c * A b c) = ∑ j, (∑ i, A i j) ^ 2 := by
  rw [Finset.sum_congr rfl fun a (_ : a ∈ univ) => Finset.sum_comm, Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [sq, ← pair_sum (fun i => A i c) (fun i => A i c)]

end Helpers

/-- **The closed form of `σ₂`.**  Valid for every `n` and every real matrix, proved from the
definition of `σ₂` as a sum of subpermanents.  The `k = 2` companion to
`RookSum.sigma_three_closed`. -/
theorem sigma_two_closed (A : Matrix (Fin n) (Fin n) ℝ) :
    2 * RookSum.sigP 2 A
      = (∑ i, ∑ j, A i j) ^ 2 - (∑ i, (∑ j, A i j) ^ 2) - (∑ j, (∑ i, A i j) ^ 2)
        + ∑ i, ∑ j, A i j ^ 2 := by
  have hemb := LayerIdentity.sigma_emb (k := 2) A
  rw [show ((Nat.factorial 2 : ℕ) : ℝ) = 2 from by norm_num [Nat.factorial]] at hemb
  rw [← hemb]
  -- the outer sieve
  rw [sum_emb_two (fun f : Fin 2 → Fin n => ∑ g : Fin 2 ↪ Fin n, ∏ a, A (f a) (g a))]
  have inner : ∀ a b : Fin n,
      (∑ g : Fin 2 ↪ Fin n, ∏ x, A (![a, b] x) (g x))
        = (∑ c, A a c) * (∑ d, A b d) - ∑ c, A a c * A b c := by
    intro a b
    rw [sum_emb_two (fun g : Fin 2 → Fin n => ∏ x, A (![a, b] x) (g x))]
    have step : ∀ c d : Fin n,
        (if c ≠ d then (∏ x : Fin 2, A (![a, b] x) (![c, d] x)) else 0)
          = (if c ≠ d then A a c * A b d else 0) := by
      intro c d
      have hprod : (∏ x : Fin 2, A (![a, b] x) (![c, d] x)) = A a c * A b d := by
        rw [Fin.prod_univ_two]; simp
      by_cases h : c ≠ d
      · rw [if_pos h, if_pos h, hprod]
      · rw [if_neg h, if_neg h]
    rw [Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => step c d,
      sum_distinct_two (fun c d => A a c * A b d), pair_sum]
  have outer : ∀ a b : Fin n,
      (if a ≠ b then (∑ g : Fin 2 ↪ Fin n, ∏ x, A (![a, b] x) (g x)) else 0)
        = (if a ≠ b then (∑ c, A a c) * (∑ d, A b d) - ∑ c, A a c * A b c else 0) := by
    intro a b
    by_cases h : a ≠ b
    · rw [if_pos h, if_pos h, inner a b]
    · rw [if_neg h, if_neg h]
  rw [Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => outer a b,
    sum_distinct_two (fun a b => (∑ c, A a c) * (∑ d, A b d) - ∑ c, A a c * A b c)]
  have hsplit : (∑ a, ∑ b, ((∑ c, A a c) * (∑ d, A b d) - ∑ c, A a c * A b c))
      = (∑ a, ∑ b, (∑ c, A a c) * (∑ d, A b d)) - ∑ a, ∑ b, ∑ c, A a c * A b c := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_sub_distrib
  have hdiag : (∑ a, ((∑ c, A a c) * (∑ d, A a d) - ∑ c, A a c * A a c))
      = (∑ a, (∑ c, A a c) * (∑ d, A a d)) - ∑ a, ∑ c, A a c * A a c :=
    Finset.sum_sub_distrib
  have hrow : (∑ a, (∑ c, A a c) * (∑ d, A a d)) = ∑ i, (∑ j, A i j) ^ 2 :=
    Finset.sum_congr rfl fun a _ => (sq _).symm
  have hsq : (∑ a, ∑ c, A a c * A a c) = ∑ i, ∑ j, A i j ^ 2 :=
    Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => (sq (A a c)).symm
  rw [hsplit, hdiag, pair_sum, col_sq, hrow, hsq]
  ring

/-! ## §2  Double sums, and the shift to the centred slice

The three lemmas of this block are the only sum manipulation the rest of the file needs; the
shift identities (§2.2) are then pure algebra on the aggregates `∑∑A²` and `∑∑A³`. -/

section DoubleSums

private theorem dsum_add (f g : Fin n → Fin n → ℝ) :
    (∑ i, ∑ j, (f i j + g i j)) = (∑ i, ∑ j, f i j) + ∑ i, ∑ j, g i j := by
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_add_distrib

private theorem dsum_smul (c : ℝ) (f : Fin n → Fin n → ℝ) :
    (∑ i, ∑ j, c * f i j) = c * ∑ i, ∑ j, f i j := by
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => (Finset.mul_sum _ _ _).symm

private theorem dsum_const (c : ℝ) : (∑ _i : Fin n, ∑ _j : Fin n, c) = (n : ℝ) ^ 2 * c := by
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

end DoubleSums

/-- `∑∑A = n` from the row sums alone. -/
theorem total_of_rows {A : Matrix (Fin n) (Fin n) ℝ} (hr : ∀ i, ∑ j, A i j = 1) :
    ∑ i, ∑ j, A i j = (n : ℝ) := by
  rw [Finset.sum_congr rfl fun i _ => hr i]
  simp

/-- **The degree-two shift.**  `Q = ∑∑A² − 1` when the line sums are `1`; equivalently
`∑∑A² = Q + 1`.  Only the total `∑∑A = n` is used. -/
theorem sum_sq_shift {A : Matrix (Fin n) (Fin n) ℝ} (hn : (n : ℝ) ≠ 0)
    (h : ∑ i, ∑ j, A i j = (n : ℝ)) :
    (∑ i, ∑ j, (A i j - 1 / (n : ℝ)) ^ 2) = (∑ i, ∑ j, A i j ^ 2) - 1 := by
  have hterm : ∀ i j, (A i j - 1 / (n : ℝ)) ^ 2
      = A i j ^ 2 + ((-2 / (n : ℝ)) * A i j + 1 / (n : ℝ) ^ 2) := fun i j => by
    field_simp; ring
  rw [Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hterm i j,
    dsum_add, dsum_add, dsum_smul, dsum_const, h]
  field_simp
  ring

/-- **The degree-three shift.**  `p₃ = ∑∑A³ − 3(∑∑A²)/n + 2/n` when the line sums are `1`. -/
theorem sum_cube_shift {A : Matrix (Fin n) (Fin n) ℝ} (hn : (n : ℝ) ≠ 0)
    (h : ∑ i, ∑ j, A i j = (n : ℝ)) :
    (∑ i, ∑ j, (A i j - 1 / (n : ℝ)) ^ 3)
      = (∑ i, ∑ j, A i j ^ 3) - 3 / (n : ℝ) * (∑ i, ∑ j, A i j ^ 2) + 2 / (n : ℝ) := by
  have hterm : ∀ i j, (A i j - 1 / (n : ℝ)) ^ 3
      = A i j ^ 3 + ((-3 / (n : ℝ)) * A i j ^ 2
          + ((3 / (n : ℝ) ^ 2) * A i j + (-1) / (n : ℝ) ^ 3)) := fun i j => by
    field_simp; ring
  rw [Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hterm i j,
    dsum_add, dsum_add, dsum_add, dsum_smul, dsum_smul, dsum_const, h]
  field_simp
  ring

/-! ## §3  `σ₂` and `σ₃` under the line-sum hypothesis

Lemma 2 of the source at `k = 2, 3`.  The hypotheses are the line sums ONLY — every row and
every column of `A` sums to `1` — with no nonnegativity and no membership in `Ω_n`.  That is
the honest hypothesis set: Lemma 2's proof uses double stochasticity only through
`σ₁(B) = 0`, which is the vanishing of the line sums of `B = A − Jₙ/n`. -/

/-- **Lemma 2 at `k = 2`:** `2σ₂(A) = (n−1)² + Q`. -/
theorem sigma_two_lines {A : Matrix (Fin n) (Fin n) ℝ} (hn : (n : ℝ) ≠ 0)
    (hr : ∀ i, ∑ j, A i j = 1) (hc : ∀ j, ∑ i, A i j = 1) :
    2 * RookSum.sigP 2 A
      = ((n : ℝ) - 1) ^ 2 + ∑ i, ∑ j, (A i j - 1 / (n : ℝ)) ^ 2 := by
  have h := sigma_two_closed A
  simp only [hr, hc, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one] at h
  rw [h, sum_sq_shift hn (total_of_rows hr)]
  ring

/-- **Lemma 2 at `k = 3`:** `6σ₃(A) = (n−1)²(n−2)²/n + 3(n−2)²Q/n + 4p₃`.  Stated in the
expanded form the assembly consumes. -/
theorem sigma_three_lines {A : Matrix (Fin n) (Fin n) ℝ} (hn : (n : ℝ) ≠ 0)
    (hr : ∀ i, ∑ j, A i j = 1) (hc : ∀ j, ∑ i, A i j = 1) :
    6 * RookSum.sigP 3 A
      = (n : ℝ) ^ 3 - 6 * (n : ℝ) ^ 2 + 13 * (n : ℝ) - 12 + 4 / (n : ℝ)
        + 3 * ((n : ℝ) - 2) ^ 2 / (n : ℝ) * (∑ i, ∑ j, (A i j - 1 / (n : ℝ)) ^ 2)
        + 4 * ∑ i, ∑ j, (A i j - 1 / (n : ℝ)) ^ 3 := by
  have h := RookSum.sigma_three_closed A
  simp only [hr, hc, one_pow, mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at h
  have h2 := sum_sq_shift hn (total_of_rows hr)
  have h3 := sum_cube_shift hn (total_of_rows hr)
  rw [h]
  rw [show (∑ i, ∑ j, A i j ^ 2) = (∑ i, ∑ j, (A i j - 1 / (n : ℝ)) ^ 2) + 1 from by
    linarith [h2]]
  rw [show (∑ i, ∑ j, A i j ^ 3)
      = (∑ i, ∑ j, (A i j - 1 / (n : ℝ)) ^ 3)
        + 3 / (n : ℝ) * ((∑ i, ∑ j, (A i j - 1 / (n : ℝ)) ^ 2) + 1) - 2 / (n : ℝ) from by
    rw [← show (∑ i, ∑ j, A i j ^ 2) = (∑ i, ∑ j, (A i j - 1 / (n : ℝ)) ^ 2) + 1 from by
      linarith [h2]]
    linarith [h3]]
  field_simp
  ring

/-! ## §4  The centred slice: (4.1) and (4.2)

These are the source's core expansions at degrees two and three.  Each is the closed form of
§1 (resp. `RookSum.sigma_three_closed`) evaluated at a matrix whose row and column sums all
vanish; nine of the ten terms of the `σ₃` form die, leaving `4p₃`. -/

/-- **(4.1)** `σ₂(B) = Q/2` for `B` with vanishing line sums. -/
theorem sigma_two_centred {B : Matrix (Fin n) (Fin n) ℝ}
    (hr : ∀ i, ∑ j, B i j = 0) (hc : ∀ j, ∑ i, B i j = 0) :
    RookSum.sigP 2 B = (∑ i, ∑ j, B i j ^ 2) / 2 := by
  have h := sigma_two_closed B
  simp only [hr, hc, Finset.sum_const_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow] at h
  linarith

/-- **(4.2)** `σ₃(B) = (2/3)p₃` for `B` with vanishing line sums. -/
theorem sigma_three_centred {B : Matrix (Fin n) (Fin n) ℝ}
    (hr : ∀ i, ∑ j, B i j = 0) (hc : ∀ j, ∑ i, B i j = 0) :
    RookSum.sigP 3 B = 2 / 3 * ∑ i, ∑ j, B i j ^ 3 := by
  have h := RookSum.sigma_three_closed B
  simp only [hr, hc, Finset.sum_const_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, mul_zero, zero_mul, mul_one, sub_zero, add_zero, zero_add] at h
  linarith

/-! ## §4b  Lemma 2 in the source's own shape

§3 states Lemma 2 in the expanded form the assembly consumes.  This block states it as the
source writes it — `σ_k(A)/C(n,k)² − k!/nᵏ = ∑_{m=2}^{k} t_m σ_m(B)` — against
`TverbergStability.tVal`, so that the coefficient layer proved there is what appears here and
the two files cannot drift apart. -/

/-- `B = A − Jₙ/n`. -/
noncomputable def centre (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => A i j - 1 / (n : ℝ)

@[simp] theorem centre_apply (A : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    centre A i j = A i j - 1 / (n : ℝ) := rfl

/-- The line sums of `B` vanish: this is `σ₁(B) = 0`, the only way double stochasticity
enters Lemma 2. -/
theorem centre_rows {A : Matrix (Fin n) (Fin n) ℝ} (hn : (n : ℝ) ≠ 0)
    (hr : ∀ i, ∑ j, A i j = 1) (i : Fin n) : ∑ j, centre A i j = 0 := by
  simp only [centre_apply, Finset.sum_sub_distrib, hr i, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  field_simp

theorem centre_cols {A : Matrix (Fin n) (Fin n) ℝ} (hn : (n : ℝ) ≠ 0)
    (hc : ∀ j, ∑ i, A i j = 1) (j : Fin n) : ∑ i, centre A i j = 0 := by
  simp only [centre_apply, Finset.sum_sub_distrib, hc j, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-- `n(n−1)(n−2)` over `ℝ`, with no truncated subtraction. -/
theorem cast_descFactorial_three {n : ℕ} (hn : 3 ≤ n) :
    ((n.descFactorial 3 : ℕ) : ℝ) = (n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2) := by
  obtain ⟨i, rfl⟩ : ∃ i, n = i + 3 := ⟨n - 3, by omega⟩
  have hd : (((i + 3).descFactorial 3 : ℕ) : ℝ)
      = ((i : ℝ) + 3) * ((i : ℝ) + 2) * ((i : ℝ) + 1) := by
    simp [Nat.descFactorial_succ]
    ring
  rw [hd]
  push_cast
  ring

/-- `6·C(n,3) = n(n−1)(n−2)` over `ℝ`, with no truncated subtraction. -/
theorem choose_three_cast {n : ℕ} (hn : 3 ≤ n) :
    ((n.choose 3 : ℕ) : ℝ) * 6 = (n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2) := by
  have hd := cast_descFactorial_three hn
  rw [Nat.descFactorial_eq_factorial_mul_choose,
    show Nat.factorial 3 = 6 from by norm_num [Nat.factorial]] at hd
  push_cast at hd
  linarith

/-- **Lemma 2 at `k = 2`, verbatim:** `σ₂(A)/C(n,2)² − 2!/n² = t₂ σ₂(B)`. -/
theorem layer_two {A : Matrix (Fin n) (Fin n) ℝ} (hn : 2 ≤ n)
    (hr : ∀ i, ∑ j, A i j = 1) (hc : ∀ j, ∑ i, A i j = 1) :
    RookSum.sigP 2 A / ((n.choose 2 : ℕ) : ℝ) ^ 2 - ((Nat.factorial 2 : ℕ) : ℝ) / (n : ℝ) ^ 2
      = TverbergStability.tVal 2 n 2 * RookSum.sigP 2 (centre A) := by
  have hN : (2:ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by intro h; rw [h] at hN; norm_num at hN
  have hn1 : (n : ℝ) - 1 ≠ 0 := by intro h; nlinarith
  have hsig := sigma_two_lines hn0 hr hc
  have hB := sigma_two_centred (centre_rows hn0 hr) (centre_cols hn0 hc)
  have hQ : (∑ i, ∑ j, centre A i j ^ 2) = ∑ i, ∑ j, (A i j - 1 / (n : ℝ)) ^ 2 := rfl
  rw [hB, hQ]
  have hC : ((n.choose 2 : ℕ) : ℝ) = (n : ℝ) * ((n : ℝ) - 1) / 2 := Nat.cast_choose_two ℝ n
  have ht : TverbergStability.tVal 2 n 2 = 4 / ((n : ℝ) ^ 2 * ((n : ℝ) - 1) ^ 2) := by
    rw [TverbergStability.tVal, TverbergStability.sVal,
      show Nat.descFactorial 2 2 = 2 from by norm_num [Nat.descFactorial],
      Nat.cast_descFactorial_two]
    norm_num
    field_simp
    ring
  rw [hC, ht, show ((Nat.factorial 2 : ℕ) : ℝ) = 2 from by norm_num [Nat.factorial],
    show RookSum.sigP 2 A = (((n : ℝ) - 1) ^ 2 + ∑ i, ∑ j, (A i j - 1 / (n : ℝ)) ^ 2) / 2 from by
      linarith]
  field_simp
  ring

/-- **Lemma 2 at `k = 3`, verbatim:** `σ₃(A)/C(n,3)² − 3!/n³ = t₂ σ₂(B) + t₃ σ₃(B)`. -/
theorem layer_three {A : Matrix (Fin n) (Fin n) ℝ} (hn : 3 ≤ n)
    (hr : ∀ i, ∑ j, A i j = 1) (hc : ∀ j, ∑ i, A i j = 1) :
    RookSum.sigP 3 A / ((n.choose 3 : ℕ) : ℝ) ^ 2 - ((Nat.factorial 3 : ℕ) : ℝ) / (n : ℝ) ^ 3
      = TverbergStability.tVal 3 n 2 * RookSum.sigP 2 (centre A)
        + TverbergStability.tVal 3 n 3 * RookSum.sigP 3 (centre A) := by
  have hN : (3:ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by intro h; rw [h] at hN; norm_num at hN
  have hn1 : (n : ℝ) - 1 ≠ 0 := by intro h; nlinarith
  have hn2 : (n : ℝ) - 2 ≠ 0 := by intro h; nlinarith
  have hsig := sigma_three_lines hn0 hr hc
  have hB2 := sigma_two_centred (centre_rows hn0 hr) (centre_cols hn0 hc)
  have hB3 := sigma_three_centred (centre_rows hn0 hr) (centre_cols hn0 hc)
  have hQ : (∑ i, ∑ j, centre A i j ^ 2) = ∑ i, ∑ j, (A i j - 1 / (n : ℝ)) ^ 2 := rfl
  have hP : (∑ i, ∑ j, centre A i j ^ 3) = ∑ i, ∑ j, (A i j - 1 / (n : ℝ)) ^ 3 := rfl
  rw [hB2, hB3, hQ, hP]
  have hC : ((n.choose 3 : ℕ) : ℝ) = (n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2) / 6 := by
    have := choose_three_cast hn
    linarith
  have ht2 : TverbergStability.tVal 3 n 2
      = 36 / ((n : ℝ) ^ 3 * ((n : ℝ) - 1) ^ 2) := by
    rw [TverbergStability.tVal, TverbergStability.sVal,
      show Nat.descFactorial 3 2 = 6 from by norm_num [Nat.descFactorial],
      Nat.cast_descFactorial_two]
    norm_num [Nat.factorial]
    field_simp
    ring
  have ht3 : TverbergStability.tVal 3 n 3
      = 36 / ((n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2)) ^ 2 := by
    rw [TverbergStability.tVal, TverbergStability.sVal,
      show Nat.descFactorial 3 3 = 6 from by norm_num [Nat.descFactorial],
      cast_descFactorial_three hn]
    norm_num
    field_simp
    ring
  rw [hC, ht2, ht3, show ((Nat.factorial 3 : ℕ) : ℝ) = 6 from by norm_num [Nat.factorial],
    show RookSum.sigP 3 A
        = ((n : ℝ) ^ 3 - 6 * (n : ℝ) ^ 2 + 13 * (n : ℝ) - 12 + 4 / (n : ℝ)
            + 3 * ((n : ℝ) - 2) ^ 2 / (n : ℝ) * (∑ i, ∑ j, (A i j - 1 / (n : ℝ)) ^ 2)
            + 4 * ∑ i, ∑ j, (A i j - 1 / (n : ℝ)) ^ 3) / 6 from by linarith]
  field_simp
  ring

/-! ## §5  Lemma 3 (F1) and Lemma 4(a)

Only the LOWER half of (F1) is used, and it needs only nonnegativity of the entries of `A`.
That is the point of the source's §6: the estimates are one-sided by design, and the side the
sign of the coefficient requires is the cheap one. -/

/-- **(6.1), the cheap side.**  `b³ ≥ −c·b²` whenever `b ≥ −c`; the proof is `b²(b + c) ≥ 0`.

`0 < c` is deliberately NOT assumed.  The source states (6.1) inside the entry range, where
`c = 1/n > 0`, but the inequality needs only `b + c ≥ 0`: sign information about `c` never
enters.  Assuming it would advertise a hypothesis the proof does not consume. -/
theorem cube_ge {b c : ℝ} (h : -c ≤ b) : -(c * b ^ 2) ≤ b ^ 3 := by
  nlinarith [mul_nonneg (sq_nonneg b) (by linarith : (0:ℝ) ≤ b + c)]

/-- **Lemma 4(a)** in the form the assembly uses: `p₃ ≥ −cQ` when every entry is `≥ −c`.
Summing (6.1); a factor `n` stronger than the two-sided bound `|p₃| ≤ βQ`. -/
theorem sum_cube_ge {B : Matrix (Fin n) (Fin n) ℝ} {c : ℝ} (hB : ∀ i j, -c ≤ B i j) :
    -(c * ∑ i, ∑ j, B i j ^ 2) ≤ ∑ i, ∑ j, B i j ^ 3 := by
  have key : (0:ℝ) ≤ ∑ i, ∑ j, (B i j ^ 3 + c * B i j ^ 2) :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by
      have := cube_ge (hB i j); linarith
  rw [dsum_add, dsum_smul] at key
  linarith

/-- `Q ≥ 0`. -/
theorem frob_nonneg (A : Matrix (Fin n) (Fin n) ℝ) :
    (0:ℝ) ≤ ∑ i, ∑ j, (A i j - 1 / (n : ℝ)) ^ 2 :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- **(F1), lower half.**  Needs only `0 ≤ A i j`. -/
theorem entry_lower {A : Matrix (Fin n) (Fin n) ℝ} (hA : A ∈ doublyStochastic ℝ (Fin n))
    (i j : Fin n) : -(1 / (n : ℝ)) ≤ A i j - 1 / (n : ℝ) := by
  have := nonneg_of_mem_doublyStochastic hA (i := i) (j := j)
  linarith

/-- **(F1), upper half.**  Recorded for fidelity to Lemma 3; the `k ≤ 3` assembly does not
use it, since the only invariant appearing at `k ≤ 3` with a negative coefficient is `p₃`. -/
theorem entry_upper {A : Matrix (Fin n) (Fin n) ℝ} (hA : A ∈ doublyStochastic ℝ (Fin n))
    (i j : Fin n) : A i j - 1 / (n : ℝ) ≤ 1 - 1 / (n : ℝ) := by
  have := le_one_of_mem_doublyStochastic hA (i := i) (j := j)
  linarith

/-! ## §6  Theorem 1 at `k = 2` and `k = 3` -/

/-- **Theorem 1 at `k = 2`, every `n ≥ 2`.**  The deficit is exactly `Q/2` and the claim is
`Q/4`, so the cell needs no threshold: `Φ(n,2) = 0`, the empty sum of (7.2). -/
theorem stabilityAt_two {n : ℕ} (hn : 2 ≤ n) : TverbergStability.StabilityAt 2 n := by
  intro A hA
  have hN : (2:ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by intro h; rw [h] at hN; norm_num at hN
  have hn1 : (n : ℝ) - 1 ≠ 0 := by intro h; nlinarith
  have hQ := frob_nonneg (n := n) A
  have hsig := sigma_two_lines hn0 (sum_row_of_mem_doublyStochastic hA)
    (sum_col_of_mem_doublyStochastic hA)
  have hC : ((n.choose 2 : ℕ) : ℝ) = (n : ℝ) * ((n : ℝ) - 1) / 2 := Nat.cast_choose_two ℝ n
  have hcoef : ((n.choose 2 : ℕ) : ℝ) ^ 2 * TverbergStability.cVal 2 n = 1 / 4 := by
    rw [TverbergStability.cVal, hC,
      show ((Nat.factorial 2 : ℕ) : ℝ) = 2 from by norm_num [Nat.factorial]]
    field_simp
    ring
  have hconst : ((n.choose 2 : ℕ) : ℝ) ^ 2 * ((Nat.factorial 2 : ℕ) : ℝ) / (n : ℝ) ^ 2
      = ((n : ℝ) - 1) ^ 2 / 2 := by
    rw [hC, show ((Nat.factorial 2 : ℕ) : ℝ) = 2 from by norm_num [Nat.factorial]]
    field_simp
    ring
  rw [hcoef, hconst]
  linarith

/-- **Theorem 1 at `k = 3`, every `n ≥ 4`.**  The threshold enters as `TverbergStability`'s
`phiPoly3_pos`: `3(n−2)² − 8 > 0` is exactly `Φ(n,3) < 1` of (7.3), cleared. -/
theorem stabilityAt_three {n : ℕ} (hn : 4 ≤ n) : TverbergStability.StabilityAt 3 n := by
  intro A hA
  have hN : (4:ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by intro h; rw [h] at hN; norm_num at hN
  have hnpos : (0:ℝ) < (n : ℝ) := by linarith
  have hn1 : (n : ℝ) - 1 ≠ 0 := by intro h; nlinarith
  -- the two invariants
  set Q := ∑ i, ∑ j, (A i j - 1 / (n : ℝ)) ^ 2 with hQdef
  set P := ∑ i, ∑ j, (A i j - 1 / (n : ℝ)) ^ 3 with hPdef
  have hQ : (0:ℝ) ≤ Q := frob_nonneg (n := n) A
  -- Lemma 4(a) at c = 1/n
  have hP : -(1 / (n : ℝ) * Q) ≤ P := by
    rw [hQdef, hPdef]
    exact sum_cube_ge (B := fun i j => A i j - 1 / (n : ℝ))
      (fun i j => entry_lower hA i j)
  -- Lemma 2 at k = 3
  have hsig := sigma_three_lines hn0 (sum_row_of_mem_doublyStochastic hA)
    (sum_col_of_mem_doublyStochastic hA)
  rw [← hQdef, ← hPdef] at hsig
  -- the two coefficient evaluations
  have hC : ((n.choose 3 : ℕ) : ℝ) = (n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2) / 6 := by
    have := choose_three_cast (by omega : 3 ≤ n)
    linarith
  have hcoef : ((n.choose 3 : ℕ) : ℝ) ^ 2 * TverbergStability.cVal 3 n
      = ((n : ℝ) - 2) ^ 2 / (4 * (n : ℝ)) := by
    rw [TverbergStability.cVal, hC,
      show ((Nat.factorial 3 : ℕ) : ℝ) = 6 from by norm_num [Nat.factorial]]
    field_simp
    ring
  have hconst : ((n.choose 3 : ℕ) : ℝ) ^ 2 * ((Nat.factorial 3 : ℕ) : ℝ) / (n : ℝ) ^ 3
      = ((n : ℝ) - 1) ^ 2 * ((n : ℝ) - 2) ^ 2 / (6 * (n : ℝ)) := by
    rw [hC, show ((Nat.factorial 3 : ℕ) : ℝ) = 6 from by norm_num [Nat.factorial]]
    field_simp
    ring
  -- the threshold, consumed from the committed layer
  have hthr : (0:ℝ) < 3 * (n : ℝ) ^ 2 - 12 * (n : ℝ) + 4 := by
    have := TverbergStability.phiPoly3_pos (n := (n : ℝ)) hN
    rwa [TverbergStability.phiPoly3] at this
  rw [hcoef, hconst]
  -- the deficit, split into the two nonnegative pieces
  have hsigval : RookSum.sigP 3 A
      = ((n : ℝ) ^ 3 - 6 * (n : ℝ) ^ 2 + 13 * (n : ℝ) - 12 + 4 / (n : ℝ)
          + 3 * ((n : ℝ) - 2) ^ 2 / (n : ℝ) * Q + 4 * P) / 6 := by linarith
  have key : (RookSum.sigP 3 A - ((n : ℝ) - 1) ^ 2 * ((n : ℝ) - 2) ^ 2 / (6 * (n : ℝ)))
      - ((n : ℝ) - 2) ^ 2 / (4 * (n : ℝ)) * Q
      = Q * (3 * (n : ℝ) ^ 2 - 12 * (n : ℝ) + 4) / (12 * (n : ℝ))
        + 2 / 3 * (P + 1 / (n : ℝ) * Q) := by
    rw [hsigval]
    field_simp
    ring
  have h1 : (0:ℝ) ≤ Q * (3 * (n : ℝ) ^ 2 - 12 * (n : ℝ) + 4) / (12 * (n : ℝ)) := by
    apply div_nonneg (mul_nonneg hQ (le_of_lt hthr))
    linarith
  have h2 : (0:ℝ) ≤ 2 / 3 * (P + 1 / (n : ℝ) * Q) := by
    have : (0:ℝ) ≤ P + 1 / (n : ℝ) * Q := by linarith
    linarith
  linarith

/-! ## §7  The threshold at `k = 3` is not slack

`stabilityAt_three` requires `n ≥ 4`, and `TverbergStability.not_stabilityAt_three_three`
refutes the cell `(3,3)`.  The two are jointly consistent only because the threshold is `4`:
weakening the hypothesis to `n ≥ 3` is refutable, and the theorem below is that refutation.
It is stated as an implication so that the kernel checks it rather than a comment asserting
it. -/

/-- **The `k = 3` hypothesis `4 ≤ n` cannot be weakened to `3 ≤ n`.**  Proposition 5 is the
obstruction, so no proof of the `n ≥ 3` form can exist. -/
theorem three_threshold_not_slack
    (h : ∀ m : ℕ, 3 ≤ m → TverbergStability.StabilityAt 3 m) : False :=
  TverbergStability.not_stabilityAt_three_three (h 3 le_rfl)

/-! ## §8  Axiom audit

**Every declaration in this file depends only on axioms among `propext, Classical.choice,
Quot.sound`.**  No `native_decide`, no `sorry`. -/

section AxiomAudit

#print axioms injective_two
#print axioms sum_fun_two
#print axioms sum_emb_two
#print axioms sum_distinct_two
#print axioms pair_sum
#print axioms col_sq
#print axioms sigma_two_closed
#print axioms dsum_add
#print axioms dsum_smul
#print axioms dsum_const
#print axioms total_of_rows
#print axioms sum_sq_shift
#print axioms sum_cube_shift
#print axioms sigma_two_lines
#print axioms sigma_three_lines
#print axioms sigma_two_centred
#print axioms sigma_three_centred
#print axioms centre
#print axioms centre_apply
#print axioms centre_rows
#print axioms centre_cols
#print axioms cast_descFactorial_three
#print axioms choose_three_cast
#print axioms layer_two
#print axioms layer_three
#print axioms cube_ge
#print axioms sum_cube_ge
#print axioms frob_nonneg
#print axioms entry_lower
#print axioms entry_upper
#print axioms stabilityAt_two
#print axioms stabilityAt_three
#print axioms three_threshold_not_slack

end AxiomAudit

end StabilityK3
