/-
The logical core of a Positivstellensatz certificate, formalised.

MOTIVATION.  A referee's objection to computer-assisted bounds of this kind is
never really "is the arithmetic right" -- that can be re-run -- but "does the
arithmetic actually entail the theorem".  The step that converts a polynomial
identity into a statement about a constrained maximum, and in particular into
UNIQUENESS of the maximiser, is where a human error can hide.  That step is
short, it is completely independent of the size of the numbers, and it is
reusable across every case and every problem in this family.  So it is worth
having machine-checked once and for all.

WHAT IS PROVED HERE.  Suppose on a set `S` we have an identity

    F b = sigma0 b + sum_j sigma j b * g j b,

where every `sigma` is nonnegative (in practice: a sum of squares, presented as
a quadratic form in monomials with a positive semidefinite Gram matrix) and each
`g j` is nonnegative on `S` (in practice: the facet-defining linear forms of a
polytope).  Then:

  * `nonneg_of_certificate`  : `F` is nonnegative on `S`;
  * `eq_zero_of_certificate` : if moreover `sigma0` vanishes only at `0`, then
    `F` vanishes on `S` only at `0`.

The second is the uniqueness half, and it is the one that is easy to get wrong.
Note what it needs: `sigma0` must vanish ONLY at the extremiser.  A merely
positive SEMIdefinite Gram matrix does not give that; a positive DEFINITE one
does, provided the monomial vector separates points from `0`.  That is
`vanish_of_posDef_quadForm` below.

The intended application: `F b = M - phi(A_0 + b)` with `M` the conjectured
maximum, `g j b` the entries of `A_0 + b`, and `S` the affine slice on which the
remaining linear constraint holds.  Then `F >= 0` on `S` is the inequality, and
`F b = 0 -> b = 0` is uniqueness of the maximiser.

Nothing here is specific to permanents; `F`, `sigma` and `g` are arbitrary real
valued functions.
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef

open Finset Matrix

namespace Certificate

variable {α : Type*} {ι : Type*} [Fintype ι] {S : Set α}

/-- **The bound.**  If `F` decomposes as a nonnegative term plus a sum of
products of nonnegative terms with constraint functions that are nonnegative on
`S`, then `F` is nonnegative on `S`. -/
theorem nonneg_of_certificate
    (F sigma0 : α → ℝ) (sigma g : ι → α → ℝ)
    (hid : ∀ b ∈ S, F b = sigma0 b + ∑ j, sigma j b * g j b)
    (hs0 : ∀ b ∈ S, 0 ≤ sigma0 b)
    (hs : ∀ (j : ι), ∀ b ∈ S, 0 ≤ sigma j b)
    (hg : ∀ (j : ι), ∀ b ∈ S, 0 ≤ g j b) :
    ∀ b ∈ S, 0 ≤ F b := by
  intro b hb
  rw [hid b hb]
  have : 0 ≤ ∑ j, sigma j b * g j b :=
    Finset.sum_nonneg fun j _ => mul_nonneg (hs j b hb) (hg j b hb)
  linarith [hs0 b hb]

/-- **Uniqueness.**  Under the same hypotheses, if `F` vanishes at a point of
`S` then so does `sigma0`.  This is the step that upgrades an inequality to a
statement about the extremal set. -/
theorem sigma0_eq_zero_of_certificate
    (F sigma0 : α → ℝ) (sigma g : ι → α → ℝ)
    (hid : ∀ b ∈ S, F b = sigma0 b + ∑ j, sigma j b * g j b)
    (hs0 : ∀ b ∈ S, 0 ≤ sigma0 b)
    (hs : ∀ (j : ι), ∀ b ∈ S, 0 ≤ sigma j b)
    (hg : ∀ (j : ι), ∀ b ∈ S, 0 ≤ g j b) :
    ∀ b ∈ S, F b = 0 → sigma0 b = 0 := by
  intro b hb hF
  have hsum : 0 ≤ ∑ j, sigma j b * g j b :=
    Finset.sum_nonneg fun j _ => mul_nonneg (hs j b hb) (hg j b hb)
  have := hid b hb
  linarith [hs0 b hb]

/-- **The uniqueness conclusion.**  If in addition `sigma0` vanishes only at a
distinguished point `b₀`, then `b₀` is the only zero of `F` on `S`. -/
theorem eq_of_certificate
    (F sigma0 : α → ℝ) (sigma g : ι → α → ℝ) (b₀ : α)
    (hid : ∀ b ∈ S, F b = sigma0 b + ∑ j, sigma j b * g j b)
    (hs0 : ∀ b ∈ S, 0 ≤ sigma0 b)
    (hs : ∀ (j : ι), ∀ b ∈ S, 0 ≤ sigma j b)
    (hg : ∀ (j : ι), ∀ b ∈ S, 0 ≤ g j b)
    (hstrict : ∀ b ∈ S, sigma0 b = 0 → b = b₀) :
    ∀ b ∈ S, F b = 0 → b = b₀ := fun b hb hF =>
  hstrict b hb (sigma0_eq_zero_of_certificate F sigma0 sigma g hid hs0 hs hg b hb hF)

section QuadraticForm

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- The quadratic form `v ↦ vᵀ G v` attached to a matrix. -/
def quadForm (G : Matrix κ κ ℝ) (v : κ → ℝ) : ℝ := dotProduct v (G.mulVec v)

/-- A positive semidefinite Gram matrix makes the quadratic form nonnegative.
This supplies the hypotheses `hs0`/`hs` above from the semidefinite program. -/
theorem quadForm_nonneg {G : Matrix κ κ ℝ} (hG : G.PosSemidef) (v : κ → ℝ) :
    0 ≤ quadForm G v := by
  have h := hG.2 v
  simpa [quadForm] using h

/-- A positive DEFINITE Gram matrix makes the quadratic form vanish only at the
zero vector.  This is what separates "the bound holds" from "the maximiser is
unique": semidefiniteness is not enough. -/
theorem quadForm_eq_zero_iff {G : Matrix κ κ ℝ} (hG : G.PosDef) (v : κ → ℝ) :
    quadForm G v = 0 ↔ v = 0 := by
  constructor
  · intro h
    by_contra hv
    have hpos := hG.2 v hv
    simp only [star_trivial] at hpos
    exact absurd h (ne_of_gt hpos)
  · rintro rfl
    simp [quadForm]

/-- **The bridge actually used.**  If `sigma0` is the quadratic form of a
positive definite Gram matrix in a vector of "monomials" `m`, and `m` separates
`b₀` from every other point of `S`, then `sigma0` vanishes on `S` only at `b₀`.

In the application `m` is the vector of monomials of degree 1 and 2 in centred
coordinates, so `m b = 0` forces every coordinate of `b` to vanish -- the
constant monomial is deliberately excluded from the basis, which is also exactly
what makes the Gram matrix strictly feasible at a tight bound. -/
theorem vanish_of_posDef_quadForm
    {G : Matrix κ κ ℝ} (hG : G.PosDef) (m : α → κ → ℝ) (b₀ : α)
    (hsep : ∀ b ∈ S, m b = 0 → b = b₀) :
    ∀ b ∈ S, quadForm G (m b) = 0 → b = b₀ := by
  intro b hb h
  exact hsep b hb ((quadForm_eq_zero_iff hG (m b)).mp h)

end QuadraticForm

/-- **The packaged statement.**  Everything the numerical work has to supply, and
exactly what it entails.  The hypotheses are: the identity, positive
definiteness of the leading Gram matrix, nonnegativity of the remaining
multipliers, nonnegativity of the constraints on `S`, and injectivity of the
monomial map at `b₀`.  The conclusion is the bound together with uniqueness. -/
theorem certificate_bound_and_uniqueness
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (F : α → ℝ) (sigma g : ι → α → ℝ) (m : α → κ → ℝ)
    (G : Matrix κ κ ℝ) (b₀ : α)
    (hG : G.PosDef)
    (hid : ∀ b ∈ S, F b = quadForm G (m b) + ∑ j, sigma j b * g j b)
    (hs : ∀ (j : ι), ∀ b ∈ S, 0 ≤ sigma j b)
    (hg : ∀ (j : ι), ∀ b ∈ S, 0 ≤ g j b)
    (hsep : ∀ b ∈ S, m b = 0 → b = b₀) :
    (∀ b ∈ S, 0 ≤ F b) ∧ (∀ b ∈ S, F b = 0 → b = b₀) := by
  have hs0 : ∀ b ∈ S, 0 ≤ quadForm G (m b) := fun b _ =>
    quadForm_nonneg hG.posSemidef (m b)
  refine ⟨nonneg_of_certificate F (fun b => quadForm G (m b)) sigma g hid hs0 hs hg,
          ?_⟩
  intro b hb hF
  have := sigma0_eq_zero_of_certificate F (fun b => quadForm G (m b)) sigma g
            hid hs0 hs hg b hb hF
  exact vanish_of_posDef_quadForm hG m b₀ hsep b hb this

end Certificate
