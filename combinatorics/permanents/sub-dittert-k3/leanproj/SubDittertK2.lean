/-
# The Cheon–Hwang sub-Dittert conjecture at `k = 2`, for every `n ≥ 2`

The other member of band one.  `SubDittertK3.lean` closes `k = 3` for `n ≥ 4` with a
symmetry-reduced SOS certificate and nineteen rational functions of `n`; `k = 2` needs
none of that.  Read through the universal identity of `SubDittertUniversal.lean`, the
objective at `k = 2` is *already* a sum of squares with explicit rational coefficients:
on `∑ b = 0`,

    F_{n,2}(b) = ½ [ κ² |b|² + κ(1 − κ)(|R|² + |C|²) ],    κ = 2/(n(n−1)) ≤ 1,

with `R`, `C` the row and column sums of the increment `b`.  Both coefficients are
non-negative for `n ≥ 2`, so the bound follows with no Cauchy–Schwarz, no Maclaurin
inequality, and no Gram matrix.

**`k = 2` is historically known**, so nothing here is new mathematics.  Its value is as a
positive control: it is the one case where the band-one machinery of
`SubDittertUniversal.lean` can be run end to end and checked against an answer that is
independently known, and it makes band one complete in Lean.

## Route

1. §1–§2: the `k = 2` sieve, in `RookSum.lean`'s idiom, and the closed form
   `2 σ₂(A) = (∑A)² − ∑ᵢrᵢ² − ∑ⱼcⱼ² + ∑ aᵢⱼ²`.  This is the `k = 2` analogue of
   `SubDittertK3.sigmaK_three_closed`, and it is much shorter because the sieve has one
   exclusion rather than three.  The `k`-general `SubDittertUniversal.sigmaK_emb` does the
   work that `RookSum.sigma_three_emb` did at `k = 3`.
2. §3: `e₁` and `e₂` in closed form.
3. §4: the identity above, out of `SubDittertUniversal.universal_identity` at `k = 2`.
4. §5: the bound, through `Certificate.nonneg_of_certificate`.

## Provenance of the shape

The SOS form is `sub-dittert/NOTES-ALLK.md` §10.10 recommendation 2.  It was re-derived
here from `universal_identity` before that note was read, and the two agreed; the form
was then checked against the objective built from the 1992 definition in exact rational
arithmetic at `n = 2..6`, four random `b` per `n` on the hyperplane, with no mismatches.
Note that the *route C* criterion elsewhere in that file —
`(n−2)(n+1)(|r|²−n) + 2|A|² − 2|c|²/n ≥ 0`, which does need two applications of
Cauchy–Schwarz — is a different statement about a different (and, at `k ≥ 3`, dead) proof
route, and is not the `k = 2` case of the conjecture.  It is asymmetric in rows and
columns, which the objective cannot be.
-/
import SubDittertUniversal

open Finset

namespace SubDittertK2

open SubDittertK3 SubDittertLinear SubDittertUniversal

variable {n : ℕ} {M : Type*} [AddCommMonoid M]

/-! ## 1.  The `k = 2` sieve

`RookSum.lean` §2–§3 at `k = 3`, with two indices instead of three. -/

/-- `![a, b]` is injective exactly when `a ≠ b`. -/
theorem injective_two {a b : Fin n} : Function.Injective ![a, b] ↔ a ≠ b := by
  constructor
  · intro h hab
    have h01 : ![a, b] 0 = ![a, b] 1 := by simp [hab]
    exact absurd (h h01) (by decide)
  · rintro h i j hij
    fin_cases i <;> fin_cases j <;> simp_all

/-- A sum over functions `Fin 2 → Fin n` as an iterated double sum. -/
theorem sum_fun_two (G : (Fin 2 → Fin n) → M) :
    ∑ f : Fin 2 → Fin n, G f = ∑ a, ∑ b, G ![a, b] := by
  let e : (Fin n × Fin n) ≃ (Fin 2 → Fin n) :=
    { toFun := fun p => ![p.1, p.2]
      invFun := fun f => (f 0, f 1)
      left_inv := by intro p; rfl
      right_inv := by intro f; funext i; fin_cases i <;> rfl }
  rw [← Equiv.sum_comp e G, Fintype.sum_prod_type]
  rfl

/-- **The `k = 2` injection sum as a double sum.** -/
theorem sum_emb_two (F : (Fin 2 → Fin n) → M) :
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

/-- **Inclusion–exclusion on two indices**: `[a ≠ b] = 1 − [a = b]`. -/
theorem sum_distinct_two (F : Fin n → Fin n → ℝ) :
    ∑ a, ∑ b, (if a ≠ b then F a b else 0) = (∑ a, ∑ b, F a b) - ∑ a, F a a := by
  have key : ∀ a b : Fin n,
      (if a ≠ b then F a b else 0) = F a b - (if a = b then F a b else 0) := by
    intro a b
    by_cases hab : a = b <;> simp_all
  have e1 : ∑ a, ∑ b, (if a = b then F a b else 0) = ∑ a, F a a :=
    Finset.sum_congr rfl fun a _ => by simp
  calc ∑ a, ∑ b, (if a ≠ b then F a b else 0)
      = ∑ a, ∑ b, (F a b - (if a = b then F a b else 0)) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => key a b
    _ = _ := by
        simp only [Finset.sum_sub_distrib]
        rw [e1]

/-! ## 2.  `σ₂` in closed form -/

/-- **`σ₂` in closed form**, for every `n`, from the definition:

    2 σ₂(A) = (∑ A)² − ∑ᵢ rᵢ² − ∑ⱼ cⱼ² + ∑ᵢⱼ aᵢⱼ².

The `k = 2` counterpart of `SubDittertK3.sigmaK_three_closed`. -/
theorem sigmaK_two_closed (A : Matrix (Fin n) (Fin n) ℝ) :
    2 * sigmaK 2 A
      = (∑ i, ∑ j, A i j) ^ 2
        - (∑ i, (∑ j, A i j) ^ 2) - (∑ j, (∑ i, A i j) ^ 2)
        + ∑ i, ∑ j, A i j ^ 2 := by
  have hemb := sigmaK_emb 2 A
  have hfac : ((Nat.factorial 2 : ℕ) : ℝ) = 2 := by norm_num [Nat.factorial]
  rw [hfac] at hemb
  rw [← hemb]
  -- outer sieve on the row injection
  rw [sum_emb_two (fun f : Fin 2 → Fin n =>
    ∑ g : Fin 2 ↪ Fin n, ∏ x, A (f x) (g x))]
  have hinner : ∀ a b : Fin n,
      (∑ g : Fin 2 ↪ Fin n, ∏ x, A (![a, b] x) (g x))
        = (∑ c, A a c) * (∑ d, A b d) - ∑ c, A a c * A b c := by
    intro a b
    rw [sum_emb_two (fun g : Fin 2 → Fin n => ∏ x, A (![a, b] x) (g x))]
    have hstep : ∀ c d : Fin n,
        (if c ≠ d then (∏ x, A (![a, b] x) (![c, d] x)) else 0)
          = (if c ≠ d then A a c * A b d else 0) := by
      intro c d
      by_cases h : c ≠ d
      · rw [if_pos h, if_pos h]
        simp [Fin.prod_univ_two]
      · rw [if_neg h, if_neg h]
    rw [Finset.sum_congr rfl fun c (_ : c ∈ univ) =>
      Finset.sum_congr rfl fun d (_ : d ∈ univ) => hstep c d,
      sum_distinct_two (fun c d => A a c * A b d)]
    congr 1
    exact (Finset.sum_mul_sum _ _ _ _).symm
  have houter : ∀ a b : Fin n,
      (if a ≠ b then (∑ g : Fin 2 ↪ Fin n, ∏ x, A (![a, b] x) (g x)) else 0)
        = (if a ≠ b then ((∑ c, A a c) * (∑ d, A b d) - ∑ c, A a c * A b c) else 0) := by
    intro a b
    by_cases h : a ≠ b
    · rw [if_pos h, if_pos h, hinner a b]
    · rw [if_neg h, if_neg h]
  rw [Finset.sum_congr rfl fun a (_ : a ∈ univ) =>
    Finset.sum_congr rfl fun b (_ : b ∈ univ) => houter a b]
  rw [sum_distinct_two (fun a b => (∑ c, A a c) * (∑ d, A b d) - ∑ c, A a c * A b c)]
  have h1 : (∑ a, ∑ b, ((∑ c, A a c) * (∑ d, A b d) - ∑ c, A a c * A b c))
      = (∑ i, ∑ j, A i j) ^ 2 - ∑ j, (∑ i, A i j) ^ 2 := by
    simp only [Finset.sum_sub_distrib]
    congr 1
    · rw [sq]
      exact (Finset.sum_mul_sum _ _ _ _).symm
    · have hswap : ∀ a : Fin n, (∑ b, ∑ c, A a c * A b c) = ∑ c, ∑ b, A a c * A b c :=
        fun a => Finset.sum_comm
      rw [Finset.sum_congr rfl fun a (_ : a ∈ univ) => hswap a, Finset.sum_comm]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [sq]
      exact (Finset.sum_mul_sum _ _ _ _).symm
  have h2 : (∑ a, ((∑ c, A a c) * (∑ d, A a d) - ∑ c, A a c * A a c))
      = (∑ i, (∑ j, A i j) ^ 2) - ∑ i, ∑ j, A i j ^ 2 := by
    simp only [Finset.sum_sub_distrib]
    congr 1
    · exact Finset.sum_congr rfl fun a _ => (sq _).symm
    · exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => (sq _).symm
  rw [h1, h2]
  ring

/-! ## 3.  `σ₁`, `e₁` and `e₂` in closed form -/

/-- `σ₁` is the sum of all entries. -/
theorem sigmaK_one_closed (A : Matrix (Fin n) (Fin n) ℝ) :
    sigmaK 1 A = ∑ i, ∑ j, A i j := by
  have hemb := sigmaK_emb 1 A
  have hfac : ((Nat.factorial 1 : ℕ) : ℝ) = 1 := by norm_num [Nat.factorial]
  rw [hfac, one_mul] at hemb
  rw [← hemb]
  have hone : ∀ F : (Fin 1 ↪ Fin n) → ℝ,
      (∑ i : Fin n, F (Equiv.uniqueEmbeddingEquivResult.symm i)) = ∑ f : Fin 1 ↪ Fin n, F f :=
    fun F => Equiv.sum_comp (Equiv.uniqueEmbeddingEquivResult (α := Fin 1) (β := Fin n)).symm F
  rw [← hone]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← hone]
  exact Finset.sum_congr rfl fun j _ => by rw [Fin.prod_univ_one]; rfl

/-- `e₁` is the sum. -/
theorem esym_one_closed (v : Fin n → ℝ) : esym 1 v = ∑ i, v i := by
  unfold esym
  rw [Finset.powersetCard_one, Finset.sum_map]
  exact Finset.sum_congr rfl fun i _ => by simp

/-- `e₂` in closed form: `2 e₂(v) = (∑ v)² − ∑ v²`. -/
theorem esym_two_closed (v : Fin n → ℝ) :
    2 * esym 2 v = (∑ i, v i) ^ 2 - ∑ i, v i ^ 2 := by
  have hL : (∑ f : Fin 2 ↪ Fin n, ∏ a, v (f a)) = 2 * esym 2 v := by
    rw [RookSum.sum_emb_eq_sum_powersetCard (fun f : Fin 2 → Fin n => ∏ a, v (f a))]
    unfold esym
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun T hT => ?_
    have hT2 : T.card = 2 := Finset.mem_powersetCard_univ.mp hT
    rw [RookSum.embSum_of_card hT2]
    have hcong : ∀ σ : Equiv.Perm (Fin 2),
        (∏ a, v (T.orderEmbOfFin hT2 (σ a))) = ∏ i ∈ T, v i := by
      intro σ
      rw [Equiv.prod_comp σ (fun a => v (T.orderEmbOfFin hT2 a))]
      exact SubDittertK3.prod_orderEmbOfFin hT2 v
    rw [Finset.sum_congr rfl fun σ (_ : σ ∈ univ) => hcong σ, Finset.sum_const,
      Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
    norm_num [Nat.factorial]
  rw [← hL, sum_emb_two (fun f : Fin 2 → Fin n => ∏ a, v (f a))]
  have hstep : ∀ a b : Fin n,
      (if a ≠ b then (∏ x, v (![a, b] x)) else 0) = (if a ≠ b then v a * v b else 0) := by
    intro a b
    by_cases h : a ≠ b
    · rw [if_pos h, if_pos h]
      simp [Fin.prod_univ_two]
    · rw [if_neg h, if_neg h]
  rw [Finset.sum_congr rfl fun a (_ : a ∈ univ) =>
    Finset.sum_congr rfl fun b (_ : b ∈ univ) => hstep a b,
    sum_distinct_two (fun a b => v a * v b)]
  congr 1
  · rw [sq]
    exact (Finset.sum_mul_sum _ _ _ _).symm
  · exact Finset.sum_congr rfl fun a _ => (sq _).symm

/-! ## 4.  The `k = 2` identity

`SubDittertUniversal.universal_identity` at `k = 2`, with the four coefficients evaluated
and the closed forms of §2–§3 substituted.  On `∑ b = 0` the `d = 1` slice dies outright:
`σ₁(b)`, `e₁(R)` and `e₁(C)` are all the sum of the entries. -/

private theorem cast_desc_two (n : ℕ) (hn : 1 ≤ n) :
    ((n.descFactorial 2 : ℕ) : ℝ) = ((n : ℝ) - 1) * (n : ℝ) := by
  have h : n.descFactorial 2 = (n - 1) * n := by simp [Nat.descFactorial]
  rw [h, Nat.cast_mul, Nat.cast_sub hn, Nat.cast_one]

theorem sCoef_two_one (n : ℕ) : sCoef 2 n 1 = 2 / (n : ℝ) := by
  rw [sCoef]
  norm_num [Nat.descFactorial]

theorem sCoef_two_two (n : ℕ) (hn : 1 ≤ n) :
    sCoef 2 n 2 = 2 / (((n : ℝ) - 1) * (n : ℝ)) := by
  rw [sCoef, cast_desc_two n hn]
  norm_num [Nat.descFactorial]

theorem tCoef_two_one (n : ℕ) : tCoef 2 n 1 = (2 / (n : ℝ)) ^ 2 / (n : ℝ) := by
  rw [tCoef, sCoef_two_one]
  norm_num [Nat.factorial]

theorem tCoef_two_two (n : ℕ) (hn : 1 ≤ n) :
    tCoef 2 n 2 = (2 / (((n : ℝ) - 1) * (n : ℝ))) ^ 2 := by
  rw [tCoef, sCoef_two_two n hn]
  norm_num [Nat.factorial]

/-- **The `k = 2` identity.**  On the hyperplane `∑ b = 0`,

    F_{n,2}(b) · n²(n−1)² = 2|b|² + (n−2)(n+1)(|R|² + |C|²).

Both coefficients on the right are non-negative for `n ≥ 2`, which is §5. -/
theorem Fcent_two_closed (n : ℕ) (hn : 2 ≤ n) (b : Fin n × Fin n → ℝ)
    (hb : (∑ i, ∑ j, incr n b i j) = 0) :
    Fcent 2 n b
      = (2 * (∑ i, ∑ j, incr n b i j ^ 2)
          + ((n : ℝ) - 2) * ((n : ℝ) + 1)
            * ((∑ i, (∑ j, incr n b i j) ^ 2) + ∑ j, (∑ i, incr n b i j) ^ 2))
        / ((n : ℝ) ^ 2 * ((n : ℝ) - 1) ^ 2) := by
  have hn0 : (n : ℝ) ≠ 0 := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    intro h; rw [h] at this; linarith
  have hn1 : ((n : ℝ) - 1) ≠ 0 := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    intro h; apply absurd this; linarith [h]
  set M := incr n b with hM
  -- the column sum of the increment also vanishes
  have hbc : (∑ j, ∑ i, M i j) = 0 := by rw [Finset.sum_comm]; exact hb
  -- the two `d = 1` quantities
  have hs1 : sigmaK 1 M = 0 := by rw [sigmaK_one_closed]; exact hb
  have he1r : esym 1 (rowSum M) = 0 := by rw [esym_one_closed]; exact hb
  have he1c : esym 1 (colSum M) = 0 := by rw [esym_one_closed]; exact hbc
  -- the two `d = 2` quantities
  have he2r : esym 2 (rowSum M) = -(∑ i, (∑ j, M i j) ^ 2) / 2 := by
    have h := esym_two_closed (rowSum M)
    have hr : (∑ i, rowSum M i) = 0 := hb
    rw [hr] at h
    have : (∑ i, rowSum M i ^ 2) = ∑ i, (∑ j, M i j) ^ 2 := rfl
    rw [this] at h
    linarith
  have he2c : esym 2 (colSum M) = -(∑ j, (∑ i, M i j) ^ 2) / 2 := by
    have h := esym_two_closed (colSum M)
    have hc : (∑ j, colSum M j) = 0 := hbc
    rw [hc] at h
    have : (∑ j, colSum M j ^ 2) = ∑ j, (∑ i, M i j) ^ 2 := rfl
    rw [this] at h
    linarith
  have hs2 : sigmaK 2 M
      = ((∑ i, ∑ j, M i j ^ 2) - (∑ i, (∑ j, M i j) ^ 2) - ∑ j, (∑ i, M i j) ^ 2) / 2 := by
    have h := sigmaK_two_closed M
    rw [hb] at h
    linarith
  rw [universal_identity 2 n hn (by omega) b]
  have hIcc : (Finset.Icc 1 2 : Finset ℕ) = {1, 2} := rfl
  rw [hIcc, Finset.sum_pair (by norm_num : (1 : ℕ) ≠ 2), ← hM,
    sCoef_two_one, sCoef_two_two n (by omega), tCoef_two_one, tCoef_two_two n (by omega),
    hs1, he1r, he1c, hs2, he2r, he2c]
  field_simp
  ring

/-! ## 5.  The bound -/

/-- The increment of a point of `K_n` has vanishing entry sum. -/
theorem sum_incr_centre (n : ℕ) (hn : 2 ≤ n) (A : Matrix (Fin n) (Fin n) ℝ) (hA : A ∈ Kn n) :
    (∑ i, ∑ j, incr n (centre n A) i j) = 0 := by
  have hn0 : (n : ℝ) ≠ 0 := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    intro h; rw [h] at this; linarith
  have hstep : ∀ i j, incr n (centre n A) i j = A i j - 1 / (n : ℝ) := fun i j => rfl
  rw [Finset.sum_congr rfl fun i (_ : i ∈ univ) =>
    Finset.sum_congr rfl fun j (_ : j ∈ univ) => hstep i j]
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  rw [hA.2]
  field_simp

/-- **The sub-Dittert conjecture at `k = 2`, for every `n ≥ 2`.**  No certificate, no
Gram matrix, no Cauchy–Schwarz: the objective is a sum of squares with non-negative
rational coefficients, by §4. -/
theorem subDittert_k2 (n : ℕ) (hn : 2 ≤ n) :
    ∀ A ∈ Kn n, Phi 2 A ≤ 2 - 2 / (n : ℝ) ^ 2 := by
  intro A hA
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by intro h; rw [h] at hnR; linarith
  have hn1 : ((n : ℝ) - 1) ≠ 0 := by intro h; apply absurd hnR; linarith [h]
  have hid := Fcent_two_closed n hn (centre n A) (sum_incr_centre n hn A hA)
  have hnonneg : 0 ≤ Fcent 2 n (centre n A) := by
    rw [hid]
    apply div_nonneg
    · have h1 : (0 : ℝ) ≤ ∑ i, ∑ j, incr n (centre n A) i j ^ 2 :=
        Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
      have h2 : (0 : ℝ) ≤ ∑ i, (∑ j, incr n (centre n A) i j) ^ 2 :=
        Finset.sum_nonneg fun i _ => sq_nonneg _
      have h3 : (0 : ℝ) ≤ ∑ j, (∑ i, incr n (centre n A) i j) ^ 2 :=
        Finset.sum_nonneg fun j _ => sq_nonneg _
      have h4 : (0 : ℝ) ≤ ((n : ℝ) - 2) * ((n : ℝ) + 1) := by nlinarith
      nlinarith
    · positivity
  rw [Fcent, uncentre_centre] at hnonneg
  have hfac : ((Nat.factorial 2 : ℕ) : ℝ) = 2 := by norm_num [Nat.factorial]
  rw [hfac] at hnonneg
  linarith

/-- The same in the notation of Cheon–Hwang 1992. -/
theorem subDittert_k2' (n : ℕ) (hn : 2 ≤ n) (A : Matrix (Fin n) (Fin n) ℝ)
    (hpos : ∀ i j, 0 ≤ A i j) (hsum : ∑ i, ∑ j, A i j = (n : ℝ)) :
    E 2 (rowSum A) + E 2 (colSum A) - P 2 A ≤ 2 - 2 / (n : ℝ) ^ 2 :=
  subDittert_k2 n hn A ⟨hpos, hsum⟩

/-! ## 6.  `E₂` in closed form — the base of the quantitative Maclaurin step

`NOTES-ALLK.md` §10.9's Theorem M rests on

    1 − E_k(r)  ≥  |r − 1|² / (n(n−1)),        for `r ≥ 0` with `∑ r = n`, `2 ≤ k ≤ n`,

and the `k = 2` case of that is an *identity*, not an inequality.  It is recorded here
because it needs nothing beyond `esym_two_closed` above, and because it isolates exactly
what Maclaurin is for: the general `k` follows from this identity together with
`E_k(r) ≤ E_2(r)`, which is Newton's inequalities telescoped.  Note that the telescoped
form is free of fractional powers — the `E_k^{1/k} ≤ E_2^{1/2}` shape in the notes is not
needed, and would not be formalisable without real powers. -/

/-- **`E₂` in closed form on the simplex**: `E₂(r) = 1 − |r − 1|²/(n(n−1))`, exactly.
This is the `k = 2` case of the quantitative Maclaurin step, with equality. -/
theorem E_two_eq (n : ℕ) (hn : 2 ≤ n) (r : Fin n → ℝ) (hr : (∑ i, r i) = (n : ℝ)) :
    E 2 r = 1 - (∑ i, (r i - 1) ^ 2) / ((n : ℝ) * ((n : ℝ) - 1)) := by
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by intro h; rw [h] at hnR; linarith
  have hn1 : ((n : ℝ) - 1) ≠ 0 := by intro h; apply absurd hnR; linarith [h]
  -- `C(n,2)` as a real, from the falling factorial
  have hchoose : 2 * ((n.choose 2 : ℕ) : ℝ) = ((n : ℝ) - 1) * (n : ℝ) := by
    have h := cast_desc_two n (by omega)
    rw [Nat.descFactorial_eq_factorial_mul_choose] at h
    rw [← h]
    norm_num [Nat.factorial]
  -- expand the squared distance to the all-ones vector
  have hdist : (∑ i, (r i - 1) ^ 2) = (∑ i, r i ^ 2) - (n : ℝ) := by
    have hexp : ∀ i : Fin n, (r i - 1) ^ 2 = r i ^ 2 - 2 * r i + 1 := fun i => by ring
    rw [Finset.sum_congr rfl fun i (_ : i ∈ univ) => hexp i]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    rw [hr]
    ring
  have he2 := esym_two_closed r
  rw [hr] at he2
  have hval : esym 2 r = ((n : ℝ) ^ 2 - (∑ i, r i ^ 2)) / 2 := by linarith
  have hc2 : ((n.choose 2 : ℕ) : ℝ) = ((n : ℝ) - 1) * (n : ℝ) / 2 := by linarith
  rw [E, hdist, hval, hc2]
  field_simp
  ring

/-! ## 7.  Axiom audit

**Every declaration in this file depends only on `propext, Classical.choice,
Quot.sound`.**  Build success is not an axiom audit, so the list is explicit.  No
`native_decide` appears anywhere in this file. -/

section AxiomAudit

#print axioms injective_two
#print axioms sum_fun_two
#print axioms sum_emb_two
#print axioms sum_distinct_two
#print axioms sigmaK_two_closed
#print axioms sigmaK_one_closed
#print axioms esym_one_closed
#print axioms esym_two_closed
#print axioms sCoef_two_one
#print axioms sCoef_two_two
#print axioms tCoef_two_one
#print axioms tCoef_two_two
#print axioms Fcent_two_closed
#print axioms sum_incr_centre
#print axioms subDittert_k2
#print axioms subDittert_k2'
#print axioms E_two_eq

end AxiomAudit

end SubDittertK2
