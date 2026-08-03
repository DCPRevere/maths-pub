/-
# Shifted-coefficient positivity certificates

`PARAMETRIC.md` §7.2 records the certificate the campaign's positivity verifiers actually emit:
to prove `p(x) > 0` for every `x ≥ n₁`, substitute `x = m + n₁` and check that every coefficient
of `p(m + n₁)` is non-negative and the constant one is positive.  `param_psd.py:snc` returns
exactly that — the shift `n₁` and the shifted coefficients as an **ascending** exact-rational
list, e.g.

    P_4  SNC threshold 8   shifted coefficients   [284, 1280, 491, 66, 3]

`PARAMETRIC.md` §7.5 lists this file's content as the one missing Lean piece ("missing, and it
is one lemma"), and names the statement.  `pos_of_shifted_coeffs` is that statement verbatim;
everything else here is the plumbing that lets a verifier's output be pasted in as data.

## What is here

* `pos_of_shifted_coeffs` — the `Fin (N+1)`-indexed form named in `PARAMETRIC.md` §7.5.
* `pos_of_shift` — the same, moved along the ray: `p x = ∑ cᵢ (x − n₁)ⁱ` gives `p > 0` on
  `[n₁, ∞)`.
* `evalAsc` and `pos_of_shifted_coeffs_list` — the **ascending list** form, which is the shape
  `param_psd.py` emits, so a certificate goes in as a literal `[284, 1280, 491, 66, 3]` with no
  reindexing.  `evalAsc` is Horner, so the `ring` step that identifies it with the polynomial is
  cheap at any degree.
* §3, the control: the three thresholds of the written Theorem G, re-proved from the campaign's
  own certificate lists rather than by hand.  `TverbergStability.phiPoly{3,4,5}_pos` were each
  proved by a bespoke `ring`-then-`linarith`; here the same three facts come out of one lemma
  plus the verifier's data, which is the point of the exercise — the same route works at any
  degree and for any of the ten Branch-S quantities of `PARAMETRIC.md` §6a.6.

Nothing here is specific to sub-Dittert: `pos_of_shifted_coeffs` is a statement about
non-negative coefficient lists.
-/

import Mathlib.Tactic
import TverbergStability

open Finset

namespace ShiftedCoeffs

/-! ## §1  The certificate, indexed and as a list -/

/-- **`PARAMETRIC.md` §7.5, step 3, verbatim.**  A polynomial whose coefficients are all
non-negative with a positive constant term is positive on `[0, ∞)`. -/
theorem pos_of_shifted_coeffs {N : ℕ} {c : Fin (N + 1) → ℝ} (hc : ∀ i, 0 ≤ c i) (h0 : 0 < c 0)
    {m : ℝ} (hm : 0 ≤ m) : 0 < ∑ i, c i * m ^ (i : ℕ) := by
  have hrest : (0:ℝ) ≤ ∑ i ∈ Finset.univ.erase (0 : Fin (N + 1)), c i * m ^ (i : ℕ) :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hc i) (pow_nonneg hm _)
  have hsplit : c (0 : Fin (N + 1)) * m ^ ((0 : Fin (N + 1)) : ℕ)
      + ∑ i ∈ Finset.univ.erase (0 : Fin (N + 1)), c i * m ^ (i : ℕ)
      = ∑ i, c i * m ^ (i : ℕ) :=
    Finset.add_sum_erase Finset.univ (fun i : Fin (N + 1) => c i * m ^ (i : ℕ))
      (Finset.mem_univ (0 : Fin (N + 1)))
  have hzero : ((0 : Fin (N + 1)) : ℕ) = 0 := rfl
  rw [← hsplit, hzero, pow_zero, mul_one]
  linarith

/-- **The certificate along a ray.**  `p x = ∑ cᵢ (x − n₁)ⁱ` with the `cᵢ` non-negative and
`c₀ > 0` gives `p > 0` on `[n₁, ∞)`. -/
theorem pos_of_shift {N : ℕ} {c : Fin (N + 1) → ℝ} {p : ℝ → ℝ} {n₁ : ℝ}
    (hp : ∀ x, p x = ∑ i, c i * (x - n₁) ^ (i : ℕ)) (hc : ∀ i, 0 ≤ c i) (h0 : 0 < c 0)
    {x : ℝ} (hx : n₁ ≤ x) : 0 < p x := by
  rw [hp x]
  exact pos_of_shifted_coeffs hc h0 (by linarith)

/-- Horner evaluation of an **ascending** coefficient list: `evalAsc [a₀, a₁, a₂] m` is
`a₀ + m(a₁ + m a₂)`.  This is the order `param_psd.py:shift` returns. -/
def evalAsc : List ℝ → ℝ → ℝ
  | [], _ => 0
  | a :: l, m => a + m * evalAsc l m

@[simp] theorem evalAsc_nil (m : ℝ) : evalAsc [] m = 0 := rfl

@[simp] theorem evalAsc_cons (a : ℝ) (l : List ℝ) (m : ℝ) :
    evalAsc (a :: l) m = a + m * evalAsc l m := rfl

theorem evalAsc_nonneg {l : List ℝ} (hc : ∀ a ∈ l, 0 ≤ a) {m : ℝ} (hm : 0 ≤ m) :
    0 ≤ evalAsc l m := by
  induction l with
  | nil => simp
  | cons a t ih =>
    have ha : 0 ≤ a := hc a (List.mem_cons_self a t)
    have ht : 0 ≤ evalAsc t m := ih fun b hb => hc b (List.mem_cons_of_mem a hb)
    have : 0 ≤ m * evalAsc t m := mul_nonneg hm ht
    simpa using by linarith

/-- **The list form of the certificate.**  Head positive, tail non-negative, `m ≥ 0`. -/
theorem pos_of_shifted_coeffs_list {a : ℝ} {l : List ℝ} (h0 : 0 < a) (hc : ∀ b ∈ l, 0 ≤ b)
    {m : ℝ} (hm : 0 ≤ m) : 0 < evalAsc (a :: l) m := by
  have ht : 0 ≤ evalAsc l m := evalAsc_nonneg hc hm
  have : 0 ≤ m * evalAsc l m := mul_nonneg hm ht
  simpa using by linarith

/-- **The list form along a ray.**  This is the shape a verifier's output is pasted into: the
threshold `n₁` and one ascending list of rationals. -/
theorem pos_of_shift_list {p : ℝ → ℝ} {n₁ a : ℝ} {l : List ℝ}
    (hp : ∀ x, p x = evalAsc (a :: l) (x - n₁)) (h0 : 0 < a) (hc : ∀ b ∈ l, 0 ≤ b)
    {x : ℝ} (hx : n₁ ≤ x) : 0 < p x := by
  rw [hp x]
  exact pos_of_shifted_coeffs_list h0 hc (by linarith)

/-! ## §2  Control: Theorem G's own thresholds, from the verifier's certificates

`param_psd.py`'s control run (`PARAMETRIC.md` §7.2) reports SNC thresholds `4, 8, 14` for
`P₃, P₄, P₅`, matching the written proof, with the shifted lists below.  Each theorem here is
the corresponding `TverbergStability.phiPolyₘ_pos`, re-derived from the list alone. -/

/-- `P₃(m+4) = 4 + 12m + 3m²`. -/
theorem phiPoly3_pos_of_cert {x : ℝ} (hx : 4 ≤ x) : 0 < TverbergStability.phiPoly3 x := by
  refine pos_of_shift_list (a := 4) (l := [12, 3]) (fun y => ?_) (by norm_num) ?_ hx
  · simp only [evalAsc_cons, evalAsc_nil, TverbergStability.phiPoly3]; ring
  · intro b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl <;> norm_num

/-- `P₄(m+8) = 284 + 1280m + 491m² + 66m³ + 3m⁴`, the list printed by the control run. -/
theorem phiPoly4_pos_of_cert {x : ℝ} (hx : 8 ≤ x) : 0 < TverbergStability.phiPoly4 x := by
  refine pos_of_shift_list (a := 284) (l := [1280, 491, 66, 3]) (fun y => ?_) (by norm_num) ?_ hx
  · simp only [evalAsc_cons, evalAsc_nil, TverbergStability.phiPoly4]; ring
  · intro b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl <;> norm_num

/-- `P₅(m+14) = 1660864 + 2716720m + 861620m² + 121160m³ + 8845m⁴ + 330m⁵ + 5m⁶`. -/
theorem phiPoly5_pos_of_cert {x : ℝ} (hx : 14 ≤ x) : 0 < TverbergStability.phiPoly5 x := by
  refine pos_of_shift_list (a := 1660864) (l := [2716720, 861620, 121160, 8845, 330, 5])
    (fun y => ?_) (by norm_num) ?_ hx
  · simp only [evalAsc_cons, evalAsc_nil, TverbergStability.phiPoly5]; ring
  · intro b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

/-! ## §3  Axiom audit

**Every declaration in this file depends only on axioms among `propext, Classical.choice,
Quot.sound`.**  No `native_decide`, no `sorry`.  Every named declaration carries a line, so the
orphan diff is empty in both directions. -/

section AxiomAudit

#print axioms pos_of_shifted_coeffs
#print axioms pos_of_shift
#print axioms evalAsc
#print axioms evalAsc_nil
#print axioms evalAsc_cons
#print axioms evalAsc_nonneg
#print axioms pos_of_shifted_coeffs_list
#print axioms pos_of_shift_list
#print axioms phiPoly3_pos_of_cert
#print axioms phiPoly4_pos_of_cert
#print axioms phiPoly5_pos_of_cert

end AxiomAudit

end ShiftedCoeffs
