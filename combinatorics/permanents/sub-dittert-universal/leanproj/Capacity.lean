/-
# Polynomial capacity, and Lemma K1

`CAPACITY.md` §2.3 fixes the object the whole Gurvits route of `LIFT.md` §B.12–§B.14 runs on:

    cap(p) = inf_{x > 0} p(x) / prod_j x_j ,

and its graded form, used at §B.12.2 in the shape `Cap*(P) = inf_{x,S>0} P/(S^m prod_j x_j)`,
replaces the denominator by an arbitrary monomial `x^alpha`.  This file is that definition and
its elementary API — the layer everything above it quotes without proof.

## What is here

| § | content |
|---|---|
| 1 | `monom`, the grading monomial `x^alpha = prod_j x_j ^ alpha_j`, and its `rpow` algebra |
| 2 | `cap`, the two workhorse lemmas `cap_le` / `le_cap`, and nothing else touches the `iInf` |
| 3 | monotonicity, scaling `p ↦ c·p`, `x`-dilation, super-multiplicativity, capacity of a monomial |
| 4 | AM–GM: `prod r_i ≤ 1` when `sum r_i = card` |
| 5 | **Lemma K1**, inequality half: `cap(p_A) ≤ prod_i r_i ≤ 1` for `A ∈ K_n` |

## Design notes

* The exponent vector `alpha` is **real**, not natural, so the product grading of §3 is plain
  addition of exponents (`monom_add`) and the border-variable bookkeeping of `LIFT.md` §B.12.2
  is available without a cast.  The price is `Real.rpow`, which is harmless on `x > 0`.
* `p` is an arbitrary function `(ι → ℝ) → ℝ`, not an `MvPolynomial`.  Every lemma below needs
  exactly one property of a polynomial with non-negative coefficients — that it is non-negative
  on the open positive orthant — and that is carried explicitly as `NonnegOn`.  Specialising to
  `MvPolynomial.eval` is then a one-line composition at the call site, and no lemma here has to
  reason about coefficients.  This is what keeps `cap_mul_ge` and `cap_dilate` short.
* The infimum is `⨅` over the subtype `PosVec ι`.  `BddBelow` comes from `NonnegOn` alone
  (`bddBelow_ratio`), so `cap` is a genuine greatest lower bound whenever `NonnegOn p` holds and
  is `0` by junk-value convention otherwise.

## What is NOT here

**The equality case of Lemma K1** — `cap(A) = 1` iff `A ∈ Ω_n` — is deferred.  Its forward half
needs `cap(A) = cap(Aᵀ)` (Sinkhorn scalings transpose) and its converse needs Lemma B6.
`LIFT.md` §B.14.2 uses only the inequality half in the direction that kills `(S3)` at `k = n`,
so the inequality half is the load-bearing part.  **Update:** the converse half —
`A ∈ Ω_n ⟹ cap(p_A) = 1` — now lands in `LemmaB6.lean` as
`cap_rowProd_eq_one_of_doublyStochastic`, so what remains owed here is only the forward
direction, which is the one that needs `cap(A) = cap(Aᵀ)`.
-/

import Mathlib.Tactic
import Mathlib.Analysis.MeanInequalities

open Finset

namespace Capacity

/-! ## §1  The positive orthant and the grading monomial -/

/-- The strictly positive orthant `{x : ι → ℝ | ∀ j, 0 < x j}`, as a subtype.  This is the
domain of the infimum defining `cap`. -/
abbrev PosVec (ι : Type*) : Type _ := {x : ι → ℝ // ∀ j, 0 < x j}

instance instNonemptyPosVec (ι : Type*) : Nonempty (PosVec ι) :=
  ⟨⟨fun _ => 1, fun _ => one_pos⟩⟩

variable {ι : Type*} [Fintype ι]

/-- The grading monomial `x^alpha = ∏_j x_j ^ alpha_j`, with real exponents. -/
noncomputable def monom (α : ι → ℝ) (x : ι → ℝ) : ℝ := ∏ j, x j ^ α j

theorem monom_pos (α : ι → ℝ) {x : ι → ℝ} (hx : ∀ j, 0 < x j) : 0 < monom α x :=
  Finset.prod_pos fun j _ => Real.rpow_pos_of_pos (hx j) _

theorem monom_nonneg (α : ι → ℝ) {x : ι → ℝ} (hx : ∀ j, 0 ≤ x j) : 0 ≤ monom α x :=
  Finset.prod_nonneg fun j _ => Real.rpow_nonneg (hx j) _

@[simp] theorem monom_one (α : ι → ℝ) : monom α (fun _ => (1 : ℝ)) = 1 := by
  simp [monom]

/-- The grading is additive in the exponent: this is the "product grading" of `cap_mul_ge`. -/
theorem monom_add (α β : ι → ℝ) {x : ι → ℝ} (hx : ∀ j, 0 < x j) :
    monom (α + β) x = monom α x * monom β x := by
  simp only [monom, Pi.add_apply, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun j _ => Real.rpow_add (hx j) _ _

theorem monom_mul (α : ι → ℝ) {t x : ι → ℝ} (ht : ∀ j, 0 ≤ t j) (hx : ∀ j, 0 ≤ x j) :
    monom α (fun j => t j * x j) = monom α t * monom α x := by
  simp only [monom, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun j _ => Real.mul_rpow (ht j) (hx j)

theorem monom_inv (α : ι → ℝ) {t : ι → ℝ} (ht : ∀ j, 0 < t j) :
    monom α (fun j => (t j)⁻¹) = (monom α t)⁻¹ := by
  simp only [monom, ← Finset.prod_inv_distrib]
  exact Finset.prod_congr rfl fun j _ => Real.inv_rpow (ht j).le _

/-- With every exponent `1` the grading is the plain product `∏_j x_j` of `CAPACITY.md` §2.3. -/
theorem monom_one_exp (x : ι → ℝ) : monom (fun _ => (1 : ℝ)) x = ∏ j, x j := by
  simp [monom]

/-! ## §2  Capacity

The definition, and the only two lemmas that unfold it.  Everything in §3–§5 goes through
`cap_le` and `le_cap`. -/

/-- `p` is non-negative on the open positive orthant.  Every polynomial with non-negative
coefficients has this property, and it is all that the capacity API needs. -/
def NonnegOn (p : (ι → ℝ) → ℝ) : Prop := ∀ x : ι → ℝ, (∀ j, 0 < x j) → 0 ≤ p x

/-- **`CAPACITY.md` §2.3, graded form.**  `cap_alpha(p) = inf_{x>0} p(x) / x^alpha`. -/
noncomputable def cap (α : ι → ℝ) (p : (ι → ℝ) → ℝ) : ℝ :=
  ⨅ x : PosVec ι, p x.1 / monom α x.1

theorem bddBelow_ratio (α : ι → ℝ) {p : (ι → ℝ) → ℝ} (hp : NonnegOn p) :
    BddBelow (Set.range fun x : PosVec ι => p x.1 / monom α x.1) := by
  refine ⟨0, ?_⟩
  rintro y ⟨x, rfl⟩
  exact div_nonneg (hp x.1 x.2) (monom_pos α x.2).le

/-- The infimum is below every evaluation. -/
theorem cap_le (α : ι → ℝ) {p : (ι → ℝ) → ℝ} (hp : NonnegOn p) {x : ι → ℝ}
    (hx : ∀ j, 0 < x j) : cap α p ≤ p x / monom α x :=
  ciInf_le (bddBelow_ratio α hp) (⟨x, hx⟩ : PosVec ι)

/-- The infimum is the greatest lower bound. -/
theorem le_cap {α : ι → ℝ} {p : (ι → ℝ) → ℝ} {c : ℝ}
    (h : ∀ x : ι → ℝ, (∀ j, 0 < x j) → c ≤ p x / monom α x) : c ≤ cap α p :=
  le_ciInf fun x => h x.1 x.2

theorem cap_nonneg {α : ι → ℝ} {p : (ι → ℝ) → ℝ} (hp : NonnegOn p) : 0 ≤ cap α p :=
  le_cap fun x hx => div_nonneg (hp x hx) (monom_pos α hx).le

/-! ## §3  The basic API -/

omit [Fintype ι] in
theorem nonnegOn_zero : NonnegOn (fun _ : ι → ℝ => (0 : ℝ)) := fun _ _ => le_rfl

@[simp] theorem cap_zero (α : ι → ℝ) : cap α (fun _ : ι → ℝ => (0 : ℝ)) = 0 := by
  refine le_antisymm ?_ (cap_nonneg nonnegOn_zero)
  have h := cap_le α nonnegOn_zero (x := fun _ => (1 : ℝ)) (fun _ => one_pos)
  simpa using h

/-- Monotonicity in `p`. -/
theorem cap_mono {α : ι → ℝ} {p q : (ι → ℝ) → ℝ} (hp : NonnegOn p)
    (h : ∀ x : ι → ℝ, (∀ j, 0 < x j) → p x ≤ q x) : cap α p ≤ cap α q := by
  refine le_cap fun x hx => ?_
  refine (cap_le α hp hx).trans ?_
  exact (div_le_div_iff_of_pos_right (monom_pos α hx)).mpr (h x hx)

/-- Scaling, one-sided half.  This direction needs only `c ≥ 0`. -/
theorem le_cap_smul {α : ι → ℝ} {p : (ι → ℝ) → ℝ} (hp : NonnegOn p) {c : ℝ}
    (hc : 0 ≤ c) : c * cap α p ≤ cap α (fun x => c * p x) := by
  refine le_cap fun x hx => ?_
  calc c * cap α p ≤ c * (p x / monom α x) := mul_le_mul_of_nonneg_left (cap_le α hp hx) hc
    _ = c * p x / monom α x := by ring

/-- Scaling of the polynomial: `cap(c·p) = c·cap(p)` for `c ≥ 0`. -/
theorem cap_smul {α : ι → ℝ} {p : (ι → ℝ) → ℝ} (hp : NonnegOn p) {c : ℝ} (hc : 0 ≤ c) :
    cap α (fun x => c * p x) = c * cap α p := by
  rcases eq_or_lt_of_le hc with rfl | hc'
  · simp
  · refine le_antisymm ?_ (le_cap_smul hp hc)
    have hq : NonnegOn (fun x : ι → ℝ => c * p x) := fun x hx => mul_nonneg hc (hp x hx)
    have h := le_cap_smul (α := α) hq (c := c⁻¹) (inv_nonneg.mpr hc)
    have heq : (fun x : ι → ℝ => c⁻¹ * (c * p x)) = p := by
      funext x
      field_simp
    rw [heq] at h
    have h2 := mul_le_mul_of_nonneg_left h hc'.le
    rwa [← mul_assoc, mul_inv_cancel₀ hc'.ne', one_mul] at h2

/-- Dilation, one-sided half. -/
theorem le_cap_dilate (α : ι → ℝ) {p : (ι → ℝ) → ℝ} (hp : NonnegOn p) {t : ι → ℝ}
    (ht : ∀ j, 0 < t j) : monom α t * cap α p ≤ cap α (fun x => p fun j => t j * x j) := by
  refine le_cap fun x hx => ?_
  have htx : ∀ j, 0 < t j * x j := fun j => mul_pos (ht j) (hx j)
  have h1 : cap α p ≤ p (fun j => t j * x j) / monom α (fun j => t j * x j) := cap_le α hp htx
  rw [monom_mul α (fun j => (ht j).le) (fun j => (hx j).le)] at h1
  have hmt := monom_pos α ht
  have hmx := monom_pos α hx
  calc monom α t * cap α p
      ≤ monom α t * (p (fun j => t j * x j) / (monom α t * monom α x)) :=
        mul_le_mul_of_nonneg_left h1 hmt.le
    _ = p (fun j => t j * x j) / monom α x := by
        field_simp
        ring

/-- `x`-dilation: replacing `x` by `t·x` multiplies the capacity by `t^alpha`. -/
theorem cap_dilate (α : ι → ℝ) {p : (ι → ℝ) → ℝ} (hp : NonnegOn p) {t : ι → ℝ}
    (ht : ∀ j, 0 < t j) :
    cap α (fun x => p fun j => t j * x j) = monom α t * cap α p := by
  refine le_antisymm ?_ (le_cap_dilate α hp ht)
  have hq : NonnegOn (fun x : ι → ℝ => p fun j => t j * x j) :=
    fun x hx => hp _ fun j => mul_pos (ht j) (hx j)
  have ht' : ∀ j, 0 < (t j)⁻¹ := fun j => inv_pos.mpr (ht j)
  have h := le_cap_dilate α hq ht'
  have heq :
      (fun x : ι → ℝ => (fun y : ι → ℝ => p fun j => t j * y j) fun j => (t j)⁻¹ * x j) = p := by
    funext x
    have : (fun j => t j * ((t j)⁻¹ * x j)) = x := by
      funext j
      rw [← mul_assoc, mul_inv_cancel₀ (ht j).ne', one_mul]
    simp only [this]
  rw [heq, monom_inv α ht] at h
  have hmt := monom_pos α ht
  have h2 := mul_le_mul_of_nonneg_left h hmt.le
  rwa [← mul_assoc, mul_inv_cancel₀ hmt.ne', one_mul] at h2

/-- **Super-multiplicativity for the product grading.**  The exponent vectors add, and the
capacities multiply up.  This is the step that lets `LIFT.md` §B.12.2 multiply by `L(x)^{n-k}`
without losing capacity. -/
theorem cap_mul_ge {α β : ι → ℝ} {p q : (ι → ℝ) → ℝ} (hp : NonnegOn p) (hq : NonnegOn q) :
    cap α p * cap β q ≤ cap (α + β) (fun x => p x * q x) := by
  refine le_cap fun x hx => ?_
  have hmα := monom_pos α hx
  have hmβ := monom_pos β hx
  have h1 : cap α p ≤ p x / monom α x := cap_le α hp hx
  have h2 : cap β q ≤ q x / monom β x := cap_le β hq hx
  have hstep : cap α p * cap β q ≤ (p x / monom α x) * (q x / monom β x) :=
    mul_le_mul h1 h2 (cap_nonneg hq) (div_nonneg (hp x hx) hmα.le)
  refine hstep.trans_eq ?_
  rw [monom_add α β hx]
  field_simp

/-- The capacity of the grading monomial itself is `1`. -/
@[simp] theorem cap_monom_self (α : ι → ℝ) : cap α (monom α) = 1 := by
  have hp : NonnegOn (monom α : (ι → ℝ) → ℝ) := fun x hx => (monom_pos α hx).le
  refine le_antisymm ?_ ?_
  · have h := cap_le α hp (x := fun _ => (1 : ℝ)) (fun _ => one_pos)
    simpa using h
  · exact le_cap fun x hx => by rw [div_self (monom_pos α hx).ne']

/-- The capacity of a monomial `c · x^alpha`, at its own grading, is its coefficient. -/
theorem cap_monomial (α : ι → ℝ) {c : ℝ} (hc : 0 ≤ c) :
    cap α (fun x => c * monom α x) = c := by
  have hp : NonnegOn (monom α : (ι → ℝ) → ℝ) := fun x hx => (monom_pos α hx).le
  rw [cap_smul hp hc, cap_monom_self, mul_one]

/-! ## §4  AM–GM

The second half of Lemma K1.  `Real.geom_mean_le_arith_mean_weighted` with uniform weights,
then the `n`-th power. -/

/-- **AM–GM, product form.**  If `r ≥ 0` has `∑ r_i = card ι`, then `∏ r_i ≤ 1`. -/
theorem prod_le_one_of_sum_eq_card (r : ι → ℝ) (hr : ∀ i, 0 ≤ r i)
    (hsum : ∑ i, r i = (Fintype.card ι : ℝ)) : ∏ i, r i ≤ 1 := by
  rcases isEmpty_or_nonempty ι with _ | _
  · simp
  have hn : 0 < Fintype.card ι := Fintype.card_pos
  have hnR : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast hn
  have hw : ∀ i ∈ (univ : Finset ι), (0 : ℝ) ≤ ((Fintype.card ι : ℝ))⁻¹ :=
    fun _ _ => by positivity
  have hw' : ∑ _i : ι, ((Fintype.card ι : ℝ))⁻¹ = 1 := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
  have key := Real.geom_mean_le_arith_mean_weighted univ
    (fun _ => ((Fintype.card ι : ℝ))⁻¹) r hw hw' (fun i _ => hr i)
  have hrhs : ∑ i, ((Fintype.card ι : ℝ))⁻¹ * r i = 1 := by
    rw [← Finset.mul_sum, hsum]
    field_simp
  rw [hrhs] at key
  have hgm : (0 : ℝ) ≤ ∏ i, r i ^ ((Fintype.card ι : ℝ))⁻¹ :=
    Finset.prod_nonneg fun i _ => Real.rpow_nonneg (hr i) _
  have hpow : (∏ i, r i ^ ((Fintype.card ι : ℝ))⁻¹) ^ (Fintype.card ι) = ∏ i, r i := by
    rw [← Finset.prod_pow]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← Real.rpow_natCast (r i ^ ((Fintype.card ι : ℝ))⁻¹) (Fintype.card ι),
      ← Real.rpow_mul (hr i), inv_mul_cancel₀ hnR.ne', Real.rpow_one]
  calc ∏ i, r i = (∏ i, r i ^ ((Fintype.card ι : ℝ))⁻¹) ^ (Fintype.card ι) := hpow.symm
    _ ≤ 1 ^ (Fintype.card ι) := by
        exact pow_le_pow_left₀ hgm key _
    _ = 1 := one_pow _

/-! ## §5  Lemma K1

`LIFT.md` §B.14.2, inequality half:

> **Lemma K1.**  For every `A ∈ K_n`, `cap(A) ≤ ∏_i r_i ≤ 1`, and `cap(A) = 1` **iff**
> `A ∈ Ω_n`.

The first inequality is the evaluation at `x = (1,…,1)` — nothing more.  The second is §4.
The equality characterisation is deferred (see the header). -/

variable {κ : Type*} [Fintype κ]

/-- The multilinear row-product polynomial `p_A(x) = ∏_i (Ax)_i` of `CAPACITY.md` §2.1. -/
noncomputable def rowProd (A : Matrix ι κ ℝ) (x : κ → ℝ) : ℝ := ∏ i, ∑ j, A i j * x j

/-- The row sums `r_i = ∑_j A_ij`. -/
def rowSum (A : Matrix ι κ ℝ) (i : ι) : ℝ := ∑ j, A i j

theorem rowProd_one (A : Matrix ι κ ℝ) :
    rowProd A (fun _ => (1 : ℝ)) = ∏ i, rowSum A i := by
  simp [rowProd, rowSum]

theorem nonnegOn_rowProd {A : Matrix ι κ ℝ} (hA : ∀ i j, 0 ≤ A i j) :
    NonnegOn (rowProd A) := by
  intro x hx
  exact Finset.prod_nonneg fun i _ =>
    Finset.sum_nonneg fun j _ => mul_nonneg (hA i j) (hx j).le

/-- **Lemma K1, first inequality.**  `cap(p_A) ≤ ∏_i r_i`, by evaluating at `x = (1,…,1)`. -/
theorem cap_rowProd_le_prod_rowSum (A : Matrix ι κ ℝ) (hA : ∀ i j, 0 ≤ A i j) :
    cap (fun _ => (1 : ℝ)) (rowProd A) ≤ ∏ i, rowSum A i := by
  have h := cap_le (fun _ => (1 : ℝ)) (nonnegOn_rowProd hA) (x := fun _ => (1 : ℝ))
    (fun _ => one_pos)
  rwa [rowProd_one, monom_one, div_one] at h

/-- **Lemma K1, second inequality.**  On `K_n` the row sums have product at most `1`. -/
theorem prod_rowSum_le_one (A : Matrix ι κ ℝ) (hA : ∀ i j, 0 ≤ A i j)
    (hK : ∑ i, ∑ j, A i j = (Fintype.card ι : ℝ)) : ∏ i, rowSum A i ≤ 1 :=
  prod_le_one_of_sum_eq_card (rowSum A) (fun i => Finset.sum_nonneg fun j _ => hA i j) hK

/-- **Lemma K1** (inequality half), assembled: for `A ∈ K_n`, `cap(p_A) ≤ ∏_i r_i ≤ 1`. -/
theorem cap_rowProd_le_one (A : Matrix ι κ ℝ) (hA : ∀ i j, 0 ≤ A i j)
    (hK : ∑ i, ∑ j, A i j = (Fintype.card ι : ℝ)) :
    cap (fun _ => (1 : ℝ)) (rowProd A) ≤ 1 :=
  (cap_rowProd_le_prod_rowSum A hA).trans (prod_rowSum_le_one A hA hK)

section AxiomAudit

#print axioms PosVec
#print axioms instNonemptyPosVec
#print axioms monom
#print axioms monom_pos
#print axioms monom_nonneg
#print axioms monom_one
#print axioms monom_add
#print axioms monom_mul
#print axioms monom_inv
#print axioms monom_one_exp
#print axioms NonnegOn
#print axioms cap
#print axioms bddBelow_ratio
#print axioms cap_le
#print axioms le_cap
#print axioms cap_nonneg
#print axioms nonnegOn_zero
#print axioms cap_zero
#print axioms cap_mono
#print axioms le_cap_smul
#print axioms cap_smul
#print axioms le_cap_dilate
#print axioms cap_dilate
#print axioms cap_mul_ge
#print axioms cap_monom_self
#print axioms cap_monomial
#print axioms prod_le_one_of_sum_eq_card
#print axioms rowProd
#print axioms rowSum
#print axioms rowProd_one
#print axioms nonnegOn_rowProd
#print axioms cap_rowProd_le_prod_rowSum
#print axioms prod_rowSum_le_one
#print axioms cap_rowProd_le_one

end AxiomAudit

end Capacity
