/-
# The bridge between the two forms of the Maclaurin step

`SubDittertM.MaclaurinBound` is stated quantitatively — `|r−1|²/(n(n−1)) ≤ 1 − E_k(r)` —
because that is what `SubDittertM.theoremM` consumes directly.  Newton's inequalities,
telescoped, will instead produce `E_k(r) ≤ E_2(r)`.  The two are the same statement, but
not the same `Prop`, so something has to sit between them; this file is that something,
and it exists so that neither side has to be reshaped when the other lands.

The equivalence is exact and needs only `n ≥ 2` and `∑ r = n` — **no positivity** — because
`SubDittertK2.E_two_eq` gives `E_2(r) = 1 − |r−1|²/(n(n−1))` as an identity.  The
positivity hypothesis is carried through only because `MaclaurinBound` quantifies over it.

**This file is application material.**  The library half — real-rooted polynomials,
Newton, Maclaurin — is `NewtonInequalities.lean`, which imports only Mathlib and mentions
nothing from this programme.  Keeping the two apart is deliberate: that half is a Mathlib
PR candidate, since neither Newton's inequalities nor Maclaurin's inequality is in
Mathlib v4.14.0.

`maclaurinBound_holds` below DISCHARGES `MaclaurinBound`, using Newton's inequalities
telescoped from `NewtonInequalities.lean`, so `SubDittertM.theoremM` and
`SubDittertM.confinement` become unconditional for `2 ≤ k ≤ n`.
-/
import SubDittertM
import NewtonInequalities

open Finset

namespace SubDittertMaclaurin

open SubDittertK3 SubDittertK2 SubDittertM

/-- **The two forms of the Maclaurin step coincide.**  The quantitative form that
`theoremM` consumes is equivalent to the ratio form `E_k ≤ E_2` that Newton's inequalities
produce, exactly, on the simplex. -/
theorem maclaurinBound_iff (n k : ℕ) (hn : 2 ≤ n) :
    MaclaurinBound n k
      ↔ ∀ r : Fin n → ℝ, (∀ i, 0 ≤ r i) → (∑ i, r i) = (n : ℝ) → E k r ≤ E 2 r := by
  constructor
  · intro h r hpos hsum
    have h1 := h r hpos hsum
    rw [E_two_eq n hn r hsum]
    linarith
  · intro h r hpos hsum
    have h1 := h r hpos hsum
    rw [E_two_eq n hn r hsum] at h1
    linarith

/-- The direction Newton will be used in: `E_k ≤ E_2` on the simplex discharges
`MaclaurinBound`, with no reshaping at the point of use. -/
theorem maclaurinBound_of_le (n k : ℕ) (hn : 2 ≤ n)
    (h : ∀ r : Fin n → ℝ, (∀ i, 0 ≤ r i) → (∑ i, r i) = (n : ℝ) → E k r ≤ E 2 r) :
    MaclaurinBound n k :=
  (maclaurinBound_iff n k hn).mpr h

/-- Consistency check: at `k = 2` the ratio form is reflexivity, and it recovers
`SubDittertM.maclaurinBound_two`. -/
theorem maclaurinBound_two' (n : ℕ) (hn : 2 ≤ n) : MaclaurinBound n 2 :=
  maclaurinBound_of_le n 2 hn fun _ _ _ => le_refl _

example (n : ℕ) (hn : 2 ≤ n) : maclaurinBound_two' n hn = maclaurinBound_two n hn := rfl

/-! ## Discharging the hypothesis

Newton's inequalities, telescoped, give `p_k ≤ p_2` on the simplex, and `p_j` is
`SubDittertK3.E j` — the two are definitionally the same, which is why the bridge below is
`exact` and not a rewriting exercise. -/

/-- **`MaclaurinBound` holds**, for every `2 ≤ k ≤ n`.  The hypothesis of Theorem M is no
longer a hypothesis. -/
theorem maclaurinBound_holds (n k : ℕ) (hn : 2 ≤ n) (hk2 : 2 ≤ k) (hkn : k ≤ n) :
    MaclaurinBound n k :=
  maclaurinBound_of_le n k hn fun _r hpos hsum =>
    NewtonIneq.pnorm_le_two hpos hsum k hk2 hkn

/-- **Theorem M, unconditional.** -/
theorem theoremM' (n k : ℕ) (hn : 2 ≤ n) (hk2 : 2 ≤ k) (hkn : k ≤ n)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A ∈ Kn n) :
    ((∑ i, (rowSum A i - 1) ^ 2) + ∑ j, (colSum A j - 1) ^ 2) / ((n : ℝ) * ((n : ℝ) - 1))
        - ((k.factorial : ℕ) : ℝ) / (n : ℝ) ^ k
      ≤ (2 - ((k.factorial : ℕ) : ℝ) / (n : ℝ) ^ k) - Phi k A :=
  theoremM n k hn (maclaurinBound_holds n k hn hk2 hkn) A hA

/-- **The confinement, unconditional.**  Any violator of the Cheon–Hwang bound has its
line sums within `n(n−1)·k!/n^k` of the all-ones vector, in squared `ℓ²` distance. -/
theorem confinement' (n k : ℕ) (hn : 2 ≤ n) (hk2 : 2 ≤ k) (hkn : k ≤ n)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A ∈ Kn n)
    (hviol : 2 - ((k.factorial : ℕ) : ℝ) / (n : ℝ) ^ k ≤ Phi k A) :
    (∑ i, (rowSum A i - 1) ^ 2) + ∑ j, (colSum A j - 1) ^ 2
      ≤ (n : ℝ) * ((n : ℝ) - 1) * (((k.factorial : ℕ) : ℝ) / (n : ℝ) ^ k) :=
  confinement n k hn (maclaurinBound_holds n k hn hk2 hkn) A hA hviol

/-! ## Axiom audit

**Every declaration in this file depends only on `propext, Classical.choice,
Quot.sound`.**  No `native_decide` appears anywhere in this file. -/

section AxiomAudit

#print axioms maclaurinBound_iff
#print axioms maclaurinBound_of_le
#print axioms maclaurinBound_two'
#print axioms maclaurinBound_holds
#print axioms theoremM'
#print axioms confinement'

end AxiomAudit

end SubDittertMaclaurin
