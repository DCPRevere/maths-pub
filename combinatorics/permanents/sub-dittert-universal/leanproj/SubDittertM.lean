/-
# The Maclaurin confinement, uniformly in `k`

A counterexample to the Cheon–Hwang bound must have row and column sums close to `1`.
Quantitatively, for `A ∈ K_n` and `2 ≤ k ≤ n`,

    (2 − k!/n^k) − Φ_k(A)  ≥  (|r − 1|² + |c − 1|²) / (n(n−1))  −  k!/n^k,

so if `Φ_k(A) ≥ 2 − k!/n^k` then `|r − 1|² + |c − 1|² ≤ n(n−1)·k!/n^k`, which is the
threshold `(n−1)k!/n^(k−1)`.

## ATTRIBUTION — this is a formalisation of a known reduction

**Nothing in this file is new mathematics, and none of it should be presented as new.**
At `k = n` the statement is *Cheon & Wanless 2012*, Linear Algebra Appl. **436**, 791–801,
**Theorem 2.1**, in contrapositive form — with subset sums in place of the `ℓ²` norm and
the same scale of threshold.  That paper describes its own result as significantly
extending a result of Hwang, so the idea predates it.  *Pang 2026*
(`arXiv:2606.01531`; preprint, unrefereed — the standing rule that an arXiv abstract is
not a published claim applies) runs the same argument at `k = n`, refining the
quantitative step without changing its shape.

The only content here not found in the literature checked is the transfer from the
Dittert functional to the whole Cheon–Hwang family uniformly in `2 ≤ k ≤ n`, **and that
is a routine transfer of a known method**.  In any write-up this must appear as a
*recalled and generalised* lemma with Cheon–Wanless Theorem 2.1 cited, never as a new
theorem.  The retraction of the original novelty claim is recorded in
`sub-dittert/NOTES-ALLK.md` §10.8; this docstring exists so the retraction travels with
the code.

It is formalised here for two reasons that have nothing to do with novelty: it is
elementary enough to check, and it is uniform in `k`.

## What is proved, and what is assumed

Everything except one named hypothesis is proved:

* `permanent_nonneg`, `sigmaK_nonneg`, `P_nonneg` — the subpermanent sum of a
  non-negative matrix is non-negative.  Elementary.
* `theoremM` — the bound above, from the split
  `F = [1 − E_k(r)] + [1 − E_k(c)] + [P_k(A) − k!/n^k]`, which needs no expansion.
* `confinement` — the contrapositive, which is the form the statement is used in.
* `maclaurinBound_two` — the hypothesis **holds at `k = 2`**, with equality, from
  `SubDittertK2.E_two_eq`.  So `theoremM_two` below is unconditional, and the hypothesis
  is not vacuous.

The single hypothesis is `MaclaurinBound`, which says `1 − E_k(r) ≥ |r − 1|²/(n(n−1))`.
It is the consequence `E_k ≤ E_2` of Newton's inequalities, telescoped, together with the
exact identity `E_2(r) = 1 − |r − 1|²/(n(n−1))` — note that the telescoped form needs no
fractional powers, unlike the `E_k^{1/k} ≤ E_2^{1/2}` shape.  **Neither Newton's
inequalities nor Maclaurin's inequality is in Mathlib v4.14.0**: `NewtonIdentities.lean`
carries Newton's *identities* only, and the sole occurrence of "Maclaurin" in the library
is the Maclaurin *series* of `arctan`.  Discharging the hypothesis is therefore a
library-gap contribution, tracked separately; when it lands, nothing here is rewritten.
-/
import SubDittertK2

open Finset

namespace SubDittertM

open SubDittertK3 SubDittertLinear SubDittertUniversal SubDittertK2

variable {n : ℕ}

/-! ## 1.  Non-negativity of the subpermanent sum -/

/-- The permanent of a non-negative matrix is non-negative: it is a sum of products of
entries. -/
theorem permanent_nonneg {m : ℕ} (M : Matrix (Fin m) (Fin m) ℝ) (h : ∀ i j, 0 ≤ M i j) :
    0 ≤ M.permanent :=
  Finset.sum_nonneg fun _ _ => Finset.prod_nonneg fun _ _ => h _ _

theorem subPerm_nonneg (k : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (hA : ∀ i j, 0 ≤ A i j)
    (S T : Finset (Fin n)) : 0 ≤ subPerm k A S T := by
  unfold subPerm
  split_ifs with hS hT
  · exact permanent_nonneg _ fun i j => hA _ _
  · exact le_refl 0
  · exact le_refl 0

theorem sigmaK_nonneg (k : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (hA : ∀ i j, 0 ≤ A i j) :
    0 ≤ sigmaK k A :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => subPerm_nonneg k A hA _ _

theorem P_nonneg (k : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (hA : ∀ i j, 0 ≤ A i j) :
    0 ≤ P k A :=
  div_nonneg (sigmaK_nonneg k A hA) (sq_nonneg _)

/-! ## 2.  The line sums of a point of `K_n` -/

theorem rowSum_nonneg {A : Matrix (Fin n) (Fin n) ℝ} (hA : A ∈ Kn n) (i : Fin n) :
    0 ≤ rowSum A i :=
  Finset.sum_nonneg fun j _ => hA.1 i j

theorem colSum_nonneg {A : Matrix (Fin n) (Fin n) ℝ} (hA : A ∈ Kn n) (j : Fin n) :
    0 ≤ colSum A j :=
  Finset.sum_nonneg fun i _ => hA.1 i j

theorem sum_rowSum {A : Matrix (Fin n) (Fin n) ℝ} (hA : A ∈ Kn n) :
    (∑ i, rowSum A i) = (n : ℝ) := hA.2

theorem sum_colSum {A : Matrix (Fin n) (Fin n) ℝ} (hA : A ∈ Kn n) :
    (∑ j, colSum A j) = (n : ℝ) := by
  rw [show (∑ j, colSum A j) = ∑ j, ∑ i, A i j from rfl, Finset.sum_comm]
  exact hA.2

/-! ## 3.  The Maclaurin step, as a named hypothesis

This is the one thing not proved.  It is `E_k(r) ≤ E_2(r)` — Newton's inequalities
telescoped — combined with the exact identity `E_2(r) = 1 − |r − 1|²/(n(n−1))` of
`SubDittertK2.E_two_eq`. -/

/-- **The Maclaurin step**: on the simplex, the deficit of `E_k` below `1` is at least the
squared distance to the all-ones vector, scaled by `n(n−1)`.  At `k = 2` this holds with
equality (`maclaurinBound_two`). -/
def MaclaurinBound (n k : ℕ) : Prop :=
  ∀ r : Fin n → ℝ, (∀ i, 0 ≤ r i) → (∑ i, r i) = (n : ℝ) →
    (∑ i, (r i - 1) ^ 2) / ((n : ℝ) * ((n : ℝ) - 1)) ≤ 1 - E k r

/-- **The hypothesis holds at `k = 2`, with equality.**  So it is not vacuous, and
`theoremM_two` below is unconditional. -/
theorem maclaurinBound_two (n : ℕ) (hn : 2 ≤ n) : MaclaurinBound n 2 := by
  intro r _ hr
  rw [E_two_eq n hn r hr]
  linarith

/-! ## 4.  Theorem M -/

/-- **The split**, straight from the definition of `Φ_k` and with no expansion:

    (2 − k!/n^k) − Φ_k(A) = [1 − E_k(r)] + [1 − E_k(c)] + [P_k(A) − k!/n^k]. -/
theorem obj_split (k : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) :
    (2 - ((k.factorial : ℕ) : ℝ) / (n : ℝ) ^ k) - Phi k A
      = (1 - E k (rowSum A)) + (1 - E k (colSum A))
        + (P k A - ((k.factorial : ℕ) : ℝ) / (n : ℝ) ^ k) := by
  unfold Phi
  ring

/-- **THEOREM M**, given the Maclaurin step.  A recalled and generalised lemma — see the
attribution in the file header; at `k = n` this is Cheon–Wanless 2012 Theorem 2.1 in
contrapositive form. -/
theorem theoremM (n k : ℕ) (_hn : 2 ≤ n) (hM : MaclaurinBound n k)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A ∈ Kn n) :
    ((∑ i, (rowSum A i - 1) ^ 2) + ∑ j, (colSum A j - 1) ^ 2) / ((n : ℝ) * ((n : ℝ) - 1))
        - ((k.factorial : ℕ) : ℝ) / (n : ℝ) ^ k
      ≤ (2 - ((k.factorial : ℕ) : ℝ) / (n : ℝ) ^ k) - Phi k A := by
  have hr := hM (rowSum A) (rowSum_nonneg hA) (sum_rowSum hA)
  have hc := hM (colSum A) (colSum_nonneg hA) (sum_colSum hA)
  have hP := P_nonneg k A hA.1
  have hsplit := obj_split (n := n) k A
  have hadd : ((∑ i, (rowSum A i - 1) ^ 2) + ∑ j, (colSum A j - 1) ^ 2)
        / ((n : ℝ) * ((n : ℝ) - 1))
      = (∑ i, (rowSum A i - 1) ^ 2) / ((n : ℝ) * ((n : ℝ) - 1))
        + (∑ j, (colSum A j - 1) ^ 2) / ((n : ℝ) * ((n : ℝ) - 1)) := by
    rw [add_div]
  rw [hsplit, hadd]
  linarith

/-- **The confinement**, which is the form the statement is used in: any violator of the
Cheon–Hwang bound has its line sums within `n(n−1)·k!/n^k = (n−1)k!/n^(k−1)` of the
all-ones vector, in squared `ℓ²` distance. -/
theorem confinement (n k : ℕ) (hn : 2 ≤ n) (hM : MaclaurinBound n k)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A ∈ Kn n)
    (hviol : 2 - ((k.factorial : ℕ) : ℝ) / (n : ℝ) ^ k ≤ Phi k A) :
    (∑ i, (rowSum A i - 1) ^ 2) + ∑ j, (colSum A j - 1) ^ 2
      ≤ (n : ℝ) * ((n : ℝ) - 1) * (((k.factorial : ℕ) : ℝ) / (n : ℝ) ^ k) := by
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hpos : (0 : ℝ) < (n : ℝ) * ((n : ℝ) - 1) := by nlinarith
  have hM' := theoremM n k hn hM A hA
  have hstep : ((∑ i, (rowSum A i - 1) ^ 2) + ∑ j, (colSum A j - 1) ^ 2)
        / ((n : ℝ) * ((n : ℝ) - 1))
      ≤ ((k.factorial : ℕ) : ℝ) / (n : ℝ) ^ k := by linarith
  rw [div_le_iff₀ hpos] at hstep
  linarith [hstep,
    mul_comm (((k.factorial : ℕ) : ℝ) / (n : ℝ) ^ k) ((n : ℝ) * ((n : ℝ) - 1))]

/-- **Theorem M at `k = 2`, unconditional.**  The hypothesis is discharged by
`maclaurinBound_two`, so this carries no assumption beyond `n ≥ 2`. -/
theorem theoremM_two (n : ℕ) (hn : 2 ≤ n) (A : Matrix (Fin n) (Fin n) ℝ) (hA : A ∈ Kn n) :
    ((∑ i, (rowSum A i - 1) ^ 2) + ∑ j, (colSum A j - 1) ^ 2) / ((n : ℝ) * ((n : ℝ) - 1))
        - (((Nat.factorial 2 : ℕ) : ℝ)) / (n : ℝ) ^ 2
      ≤ (2 - (((Nat.factorial 2 : ℕ) : ℝ)) / (n : ℝ) ^ 2) - Phi 2 A :=
  theoremM n 2 hn (maclaurinBound_two n hn) A hA

/-! ## 5.  Axiom audit

**Every declaration in this file depends only on `propext, Classical.choice,
Quot.sound`.**  `theoremM` and `confinement` take `MaclaurinBound` as a hypothesis rather
than assuming it as an axiom, so they are honest theorems about an implication; nothing
here is `sorry`.  No `native_decide` appears anywhere in this file. -/

section AxiomAudit

#print axioms permanent_nonneg
#print axioms subPerm_nonneg
#print axioms sigmaK_nonneg
#print axioms P_nonneg
#print axioms rowSum_nonneg
#print axioms colSum_nonneg
#print axioms sum_rowSum
#print axioms sum_colSum
#print axioms maclaurinBound_two
#print axioms obj_split
#print axioms theoremM
#print axioms confinement
#print axioms theoremM_two

end AxiomAudit

end SubDittertM
