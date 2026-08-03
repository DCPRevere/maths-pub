/-
# Gurvits' Main Theorem as a NAMED HYPOTHESIS — `LEAN-ROADMAP.md` stone 13

`LEAN-ROADMAP.md` §3 names stones 11–12 (a stability predicate closed under `∂` at zero, and
the one-variable capacity lemma) as the single biggest risk in the whole plan, and prescribes
the mitigation **on day one**:

> state stone 13 as a named hypothesis in the `SubDittertM.MaclaurinBound` shape, so that
> stones 14–23 land unconditionally-modulo-one-named-hypothesis and can be audited, published
> and relied on while 11 and 12 are in progress.

This file is that hypothesis, and nothing else.  It is `GurvitsBound` below, at **exactly** the
strength the chain consumes (roadmap A11, finding 1): ONE use, a homogeneous polynomial of
degree `N` in `N` variables, and the **plain** van der Waerden constant `N!/N^N`.  The
degree-refined constant `∏ g(C_i)` and the optimal-labelling analysis of `CAPACITY.md` §2.4 are
off the critical path — `LIFT.md` §B.12's Lemma U replaces them — and are deliberately NOT
stated here.

## What is here

| § | content |
|---|---|
| 1 | `topIdx`, the all-ones multi-index: `coeff (topIdx N) p` **is** `∂^N p/∂x_1⋯∂x_N (0)` |
| 2 | `HStable`, the Hurwitz-stability predicate, and `GurvitsBound`, the named hypothesis |
| 3 | the control: **the stability hypothesis is load-bearing, not decorative** |

## §3 in words, because it is the reason this file is more than a `def`

`LEAN-ROADMAP.md` §2.2 item 2 asks whether the stability side-condition can be dropped — whether
non-negative coefficients alone would do, which would delete stones 11–12 outright — and answers
NO with a two-line counterexample.  `not_gurvitsBound_without_stability` is that counterexample,
machine-checked: at `p = x₀² + x₁²` (homogeneous of degree `2` in `2` variables, coefficients
non-negative) the capacity is `2` while `∂²p/∂x₀∂x₁(0) = 0`, so the de-stabilised statement
would assert `1 ≤ 0`.  The hypothesis below therefore cannot be weakened to something Mathlib
already supports, and stones 11–12 are unavoidable rather than merely unattempted.

## Discharging it

`GurvitsBound` is an ordinary `Prop` and appears as an explicit argument of every theorem that
uses it — it is **not** an axiom, and the `#print axioms` bar stays at
`[propext, Classical.choice, Quot.sound]` throughout.  Stones 11–12 will discharge it; the
pattern is proved out in this tree twice already (`SubDittertM.MaclaurinBound`, discharged one
file later by `SubDittertMaclaurin`; and `TverbergStability.StabilityAt`, discharged cell by
cell).

Source: L. Gurvits, *Van der Waerden/Schrijver-Valiant like Conjectures and Stable (aka
Hyperbolic) Homogeneous Polynomials: One Theorem for all*, Electron. J. Combin. **15** (2008)
#R66, arXiv:0711.3496.
-/

import Mathlib.Tactic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Capacity

open Finset

namespace Gurvits

/-! ## §1  The top square-free coefficient

For a polynomial in `N` variables the mixed derivative `∂^N/∂x_1⋯∂x_N` taken once in each
variable and evaluated at `0` is exactly the coefficient of the square-free top monomial
`x_1⋯x_N`.  Working with the coefficient keeps the statement algebraic — no `deriv`, no
`fderiv` — which is what makes it cheap to consume downstream. -/

/-- The all-ones multi-index of `Fin N`, i.e. the exponent vector of `x_1 ⋯ x_N`. -/
noncomputable def topIdx (N : ℕ) : Fin N →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun _ => 1)

@[simp] theorem topIdx_apply {N : ℕ} (i : Fin N) : topIdx N i = 1 := rfl

/-- `x_1 ⋯ x_N` really has total degree `N`, so `topIdx` is a legitimate multi-index for a
form of degree `N`. -/
theorem topIdx_degree (N : ℕ) : (topIdx N).degree = N := by
  classical
  rw [Finsupp.degree]
  have hsupp : (topIdx N).support = Finset.univ := by
    ext i
    simp [topIdx]
  rw [hsupp]
  simp

/-! ## §2  The hypothesis -/

/-- **H-stability.**  `p` has no zero in the open right half-space: `p(z) ≠ 0` whenever every
`Re z_i > 0`.  This is a bare `Prop` — no theory about it is developed here, and none is needed
to *state* `GurvitsBound`.  The closure properties (roadmap A12) belong to stones 11–12. -/
def HStable {N : ℕ} (p : MvPolynomial (Fin N) ℝ) : Prop :=
  ∀ z : Fin N → ℂ, (∀ i, 0 < (z i).re) → MvPolynomial.aeval z p ≠ 0

/-- **ROADMAP A11 / STONE 13 — Gurvits' Main Theorem, as a named hypothesis.**

> Let `p(x_1..x_N)` be homogeneous of degree `N` in `N` variables, with non-negative
> coefficients, and H-stable.  Then
> `∂^N p/∂x_1⋯∂x_N (0) ≥ (N!/N^N) · Cap(p)`,
> `Cap(p) = inf_{x>0} p(x)/(x_1⋯x_N)`.

Stated at exactly the generality consumed and no more: the plain van der Waerden constant, one
polynomial, degree `N` in `N` variables.  Every theorem downstream takes this as an explicit
argument. -/
def GurvitsBound : Prop :=
  ∀ (N : ℕ) (p : MvPolynomial (Fin N) ℝ), p.IsHomogeneous N →
    (∀ d, 0 ≤ MvPolynomial.coeff d p) → HStable p →
      ((N.factorial : ℝ) / (N : ℝ) ^ N) *
          Capacity.cap (fun _ => (1 : ℝ)) (fun x => MvPolynomial.eval x p)
        ≤ MvPolynomial.coeff (topIdx N) p

/-! ## §3  The control: stability is load-bearing

`LEAN-ROADMAP.md` §2.2 item 2.  Dropping `HStable` from `GurvitsBound` makes it FALSE, so the
side condition cannot be traded for anything Mathlib already has, and stones 11–12 are on the
critical path by necessity rather than by choice. -/

/-- The witness of `LEAN-ROADMAP.md` §2.2 item 2: `p(x₀,x₁) = x₀² + x₁²`. -/
noncomputable def sqSum : MvPolynomial (Fin 2) ℝ := MvPolynomial.X 0 ^ 2 + MvPolynomial.X 1 ^ 2

theorem sqSum_isHomogeneous : sqSum.IsHomogeneous 2 :=
  (MvPolynomial.isHomogeneous_X_pow (R := ℝ) 0 2).add (MvPolynomial.isHomogeneous_X_pow 1 2)

theorem sqSum_coeff_nonneg (d : Fin 2 →₀ ℕ) : 0 ≤ MvPolynomial.coeff d sqSum := by
  classical
  rw [sqSum, MvPolynomial.coeff_add, MvPolynomial.X_pow_eq_monomial,
    MvPolynomial.X_pow_eq_monomial, MvPolynomial.coeff_monomial, MvPolynomial.coeff_monomial]
  split_ifs <;> norm_num

/-- The mixed derivative vanishes: `∂²p/∂x₀∂x₁(0) = 0`. -/
theorem sqSum_topCoeff : MvPolynomial.coeff (topIdx 2) sqSum = 0 := by
  classical
  have h0 : (Finsupp.single (0 : Fin 2) 2) ≠ topIdx 2 := by
    intro h
    have := congrArg (fun f => f (1 : Fin 2)) h
    simp [Finsupp.single_apply] at this
  have h1 : (Finsupp.single (1 : Fin 2) 2) ≠ topIdx 2 := by
    intro h
    have := congrArg (fun f => f (0 : Fin 2)) h
    simp [Finsupp.single_apply] at this
  rw [sqSum, MvPolynomial.coeff_add, MvPolynomial.X_pow_eq_monomial,
    MvPolynomial.X_pow_eq_monomial, MvPolynomial.coeff_monomial, MvPolynomial.coeff_monomial,
    if_neg h0, if_neg h1, add_zero]

theorem sqSum_eval (x : Fin 2 → ℝ) : MvPolynomial.eval x sqSum = x 0 ^ 2 + x 1 ^ 2 := by
  simp [sqSum]

/-- `Cap(x₀² + x₁²) = 2`, the AM–GM value, attained at `x = (1,1)`. -/
theorem cap_sqSum : Capacity.cap (fun _ => (1 : ℝ)) (fun x => MvPolynomial.eval x sqSum) = 2 := by
  have hp : Capacity.NonnegOn (fun x : Fin 2 → ℝ => MvPolynomial.eval x sqSum) := by
    intro x _
    show (0:ℝ) ≤ MvPolynomial.eval x sqSum
    rw [sqSum_eval]
    positivity
  refine le_antisymm ?_ ?_
  · have h := Capacity.cap_le (fun _ => (1 : ℝ)) hp (x := fun _ => (1 : ℝ)) (fun _ => one_pos)
    rw [Capacity.monom_one, div_one, sqSum_eval] at h
    norm_num at h
    exact h
  · refine Capacity.le_cap fun x hx => ?_
    have hx0 := hx 0
    have hx1 := hx 1
    rw [Capacity.monom_one_exp, Fin.prod_univ_two, sqSum_eval, le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (x 0 - x 1)]

/-- **`LEAN-ROADMAP.md` §2.2 item 2, machine-checked.**  `GurvitsBound` with the `HStable`
hypothesis DELETED is false: at `p = x₀² + x₁²` it asserts `(2!/2²)·2 = 1 ≤ 0`.  So
non-negative coefficients alone are not enough, the stability side condition is load-bearing,
and stones 11–12 cannot be avoided. -/
theorem not_gurvitsBound_without_stability :
    ¬ (∀ (N : ℕ) (p : MvPolynomial (Fin N) ℝ), p.IsHomogeneous N →
        (∀ d, 0 ≤ MvPolynomial.coeff d p) →
          ((N.factorial : ℝ) / (N : ℝ) ^ N) *
              Capacity.cap (fun _ => (1 : ℝ)) (fun x => MvPolynomial.eval x p)
            ≤ MvPolynomial.coeff (topIdx N) p) := by
  intro h
  have hbad := h 2 sqSum sqSum_isHomogeneous sqSum_coeff_nonneg
  rw [cap_sqSum, sqSum_topCoeff] at hbad
  norm_num [Nat.factorial] at hbad

/-! ## §4  A consistency control at the tight point

The constant `N!/N^N` is not too large at the natural test point: at `p = x_1⋯x_N` — the
extreme case of a product of non-negative linear forms, and the `A = I` point of the van der
Waerden problem — `Cap(p) = 1` and the top coefficient is `1`, so `GurvitsBound`'s conclusion
reads `N!/N^N ≤ 1`, which is true.  This does not prove the hypothesis; it rules out the
cheapest way for it to be wrong. -/

theorem factorial_div_pow_le_one (N : ℕ) : ((N.factorial : ℝ) / (N : ℝ) ^ N) ≤ 1 := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · norm_num
  · have hpos : (0 : ℝ) < (N : ℝ) ^ N := by
      have : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
      positivity
    rw [div_le_one hpos]
    exact_mod_cast Nat.factorial_le_pow N

section AxiomAudit

#print axioms topIdx
#print axioms topIdx_apply
#print axioms topIdx_degree
#print axioms HStable
#print axioms GurvitsBound
#print axioms sqSum
#print axioms sqSum_isHomogeneous
#print axioms sqSum_coeff_nonneg
#print axioms sqSum_topCoeff
#print axioms sqSum_eval
#print axioms cap_sqSum
#print axioms not_gurvitsBound_without_stability
#print axioms factorial_div_pow_le_one

end AxiomAudit

end Gurvits
