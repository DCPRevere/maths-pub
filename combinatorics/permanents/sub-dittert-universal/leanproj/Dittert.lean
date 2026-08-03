/-
# Dittert's conjecture as the `k = n` cell, and the cell `n = 2` in closed form

Dittert's conjecture is the diagonal `k = n` of the Cheon–Hwang family that
`SubDittertK3.lean` sets up: for `A` in `K_n` (nonnegative, entry sum `n`),

    phi(A)  =  prod_i r_i  +  prod_j c_j  -  per(A)   <=   2 - n!/n^n ,

with equality only at `A = J_n/n`.  This file does three things.

**1.  The identification, at every `n`, from the definitions.**  `E_top`,
`sigmaK_top`, `P_top` and `Phi_top` prove that the family's `Phi n` *is* the
Dittert functional: `E_n` of a vector is its product because `C(n,n) = 1` and
`powersetCard n univ = {univ}`, and `P_n` of a matrix is its permanent for the
same reason.  Outside Lean this identification is the content of
`sub-dittert/results/dittert_kn_identification.log`; here it is a theorem.
Nothing about it is `n = 4` or `n = 5` specific, so it is proved once.

**2.  `n = 2`, complete and sharp.**  `phi_two_identity` is an *identity*, not an
inequality:

    2 - 2!/2^2 - phi(A)  =  (1/2) * sum_ij (a_ij - 1/2)^2      whenever sum = 2 .

The inequality, the equality case, and a stability rate with the sharp constant
`1/2` all fall out of it, and none of the three uses nonnegativity of the
entries — so `dittert_two_of_sum` is strictly stronger than Dittert at `n = 2`.
Refereed source for the cell: Sinkhorn, *Linear and Multilinear Algebra* **16**
(1984) 167–173.  This file does not import it; it proves it.

**3.  The certificate schema for the whole diagonal.**  `dittert_of_certificate`
reduces `DittertConj n` to a Positivstellensatz certificate on `K_n`: an
identity `bound - phi = sigma0 + sum_p sigma_p * a_p` with every `sigma`
nonnegative and `sigma0` vanishing only at `J_n/n`.  That is the acceptance
layer for the `n = 4` and `n = 5` anchor certificates of
`sub-dittert/D45.md`; with it in place the outstanding obligation at those two
cells is the transcription of the two Gram matrices and one `ring` identity, and
nothing else.  `dittert_of_posDef_certificate` packages the common case where
`sigma0` is a quadratic form with a positive definite Gram.

## What is deliberately NOT here

`n = 3`.  The `k = 3` line of this tree (`subDittert_k3_full`) is stated for
`n >= 4` and that hypothesis is not slack: the ten rational functions of
`CertPositive` are the certificate's own positivity conditions, and at `n = 3`
three of the twelve go negative —

    theta1  (3) = -25/324 ,  minorC2 (3) = -457607/1062882 ,
    c0Line  (3) = -379/5832 .

So the general-`n` `k = 3` certificate does not reach the diagonal cell `(3,3)`,
and `(3,3)` needs a certificate of its own.  `not_certPositive_three` records
that as a theorem rather than a comment, so the gap cannot be forgotten.

There are no `sorry`s and no `native_decide` in this file.
-/

import SubDittertK2

namespace Dittert

open Finset Matrix SubDittertK3

variable {n : ℕ}

/-! ## 1.  The identification `k = n`

Everything here is an unfolding of the definitions in `SubDittertK3`, using only
that `univ` is the unique `n`-subset of `Fin n` and that `C(n,n) = 1`. -/

/-- The only `n`-element subset of `Fin n` is `univ`. -/
theorem powersetCard_top : Finset.powersetCard n (univ : Finset (Fin n)) = {univ} := by
  have hcard : (univ : Finset (Fin n)).card = n := by simp
  have h := Finset.powersetCard_self (univ : Finset (Fin n))
  rwa [hcard] at h

/-- **`e_n(v) = ∏ v i`.**  The top elementary symmetric function is the product. -/
theorem esym_top (v : Fin n → ℝ) : esym n v = ∏ i, v i := by
  unfold esym
  rw [powersetCard_top, Finset.sum_singleton]

/-- **`E_n(v) = ∏ v i`**, since `C(n,n) = 1`. -/
theorem E_top (v : Fin n → ℝ) : E n v = ∏ i, v i := by
  unfold E
  rw [esym_top, Nat.choose_self]
  norm_num

/-- The single `n × n` subpermanent of `A` is its permanent. -/
theorem subPerm_top (A : Matrix (Fin n) (Fin n) ℝ) :
    subPerm n A univ univ = A.permanent := by
  have hcard : (univ : Finset (Fin n)).card = n := by simp
  have hid : (id : Fin n → Fin n) = ⇑((univ : Finset (Fin n)).orderEmbOfFin hcard) :=
    Finset.orderEmbOfFin_unique hcard (fun x => mem_univ x) strictMono_id
  unfold subPerm
  rw [dif_pos hcard, dif_pos hcard, ← hid, Matrix.submatrix_id_id]

/-- **`σ_n(A) = per(A)`.**  There is exactly one `n`-subset of rows and one of
columns, so the subpermanent sum collapses. -/
theorem sigmaK_top (A : Matrix (Fin n) (Fin n) ℝ) : sigmaK n A = A.permanent := by
  unfold sigmaK
  rw [powersetCard_top]
  simp only [Finset.sum_singleton]
  exact subPerm_top A

/-- **`P_n(A) = per(A)`**, since `C(n,n)² = 1`. -/
theorem P_top (A : Matrix (Fin n) (Fin n) ℝ) : P n A = A.permanent := by
  unfold P
  rw [sigmaK_top, Nat.choose_self]
  norm_num

/-- **Dittert's functional** `φ(A) = ∏ r_i + ∏ c_j − per(A)`. -/
noncomputable def phi (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  (∏ i, rowSum A i) + (∏ j, colSum A j) - A.permanent

/-- **The `k = n` cell of the Cheon–Hwang family IS Dittert's functional.**  This
is the identification that makes the whole `k = n` tier a special case of the
family rather than a separate problem. -/
theorem Phi_top (A : Matrix (Fin n) (Fin n) ℝ) : Phi n A = phi A := by
  unfold Phi phi
  rw [E_top, E_top, P_top]

/-- **Dittert's bound** `2 − n!/n^n`. -/
noncomputable def bound (n : ℕ) : ℝ := 2 - (Nat.factorial n : ℝ) / (n : ℝ) ^ n

/-- The bound is attained at `J_n/n`, from the family's own boundary check. -/
theorem phi_uniform (hn : n ≠ 0) : phi (uniform n) = bound n := by
  rw [← Phi_top, bound]
  exact Phi_uniform n le_rfl hn

/-- **Dittert's conjecture at dimension `n`**, inequality and equality case. -/
def DittertConj (n : ℕ) : Prop :=
  ∀ A ∈ Kn n, phi A ≤ bound n ∧ (phi A = bound n ↔ A = uniform n)

/-! ## 2.  `n = 2`, in closed form

The whole cell is one polynomial identity.  Note that `hsum` alone is assumed:
the nonnegativity half of `A ∈ K_2` is never used, so this is stronger than
Dittert at `n = 2`. -/

/-- The permanent of a `2 × 2` matrix, from the column-zero expansion. -/
theorem permanent_two (A : Matrix (Fin 2) (Fin 2) ℝ) :
    A.permanent = A 0 0 * A 1 1 + A 1 0 * A 0 1 := by
  simp [Matrix.permanent_succ_column_zero, Fin.sum_univ_succ, Matrix.permanent_isEmpty,
    Matrix.submatrix_apply]

theorem bound_two : bound 2 = 3 / 2 := by
  norm_num [bound, Nat.factorial]

/-- **The `n = 2` identity.**  For every real `2 × 2` matrix of entry sum `2`,

    2 − 2!/2² − φ(A)  =  (1/2) · ∑_{i,j} (a_ij − 1/2)² .

Everything about the cell follows from this line. -/
theorem phi_two_identity (A : Matrix (Fin 2) (Fin 2) ℝ)
    (hsum : ∑ i, ∑ j, A i j = (2 : ℝ)) :
    bound 2 - phi A = (1 / 2) * ∑ i, ∑ j, (A i j - 1 / 2) ^ 2 := by
  rw [bound_two]
  simp only [phi, rowSum, colSum, permanent_two, Fin.prod_univ_two, Fin.sum_univ_two] at *
  linear_combination (-1 / 2 - (A 0 0 + A 0 1 + A 1 0 + A 1 1) / 2) * hsum

/-- **Dittert at `n = 2`, in full, without nonnegativity**: the inequality, the
equality case, and the sharp stability rate. -/
theorem dittert_two_of_sum (A : Matrix (Fin 2) (Fin 2) ℝ)
    (hsum : ∑ i, ∑ j, A i j = (2 : ℝ)) :
    phi A ≤ bound 2
      ∧ (phi A = bound 2 ↔ A = uniform 2)
      ∧ bound 2 - phi A = (1 / 2) * ∑ i, ∑ j, (A i j - 1 / 2) ^ 2 := by
  have hid := phi_two_identity A hsum
  have hQ : 0 ≤ (1 / 2) * ∑ i, ∑ j, (A i j - 1 / 2) ^ 2 := by
    have : 0 ≤ ∑ i, ∑ j, (A i j - 1 / 2) ^ 2 :=
      Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
    linarith
  refine ⟨by linarith, ⟨fun h => ?_, fun h => ?_⟩, hid⟩
  · -- equality forces every entry to be `1/2`
    have hzero : ∑ i, ∑ j, (A i j - 1 / 2) ^ 2 = 0 := by linarith
    have hrow : ∀ i ∈ (univ : Finset (Fin 2)), ∑ j, (A i j - 1 / 2) ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _)).mp hzero
    ext i j
    have hij : (A i j - 1 / 2) ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (A i j - 1 / 2))).mp
        (hrow i (mem_univ i)) j (mem_univ j)
    have := pow_eq_zero_iff two_ne_zero |>.mp hij
    show A i j = uniform 2 i j
    unfold uniform
    norm_num
    linarith
  · rw [h, phi_uniform (by norm_num)]

/-- **Dittert's conjecture at `n = 2`.**  Sinkhorn 1984 proved this cell; the
proof here is this repository's own and needs no import. -/
theorem dittert_two : DittertConj 2 := by
  intro A hA
  obtain ⟨hle, heq, _⟩ := dittert_two_of_sum A hA.2
  exact ⟨hle, heq⟩

/-! ## 3.  The certificate schema on the diagonal

The acceptance layer for the `n = 4` and `n = 5` anchor certificates.  `S` is
`K_n`; the constraint functions `g` are the `n²` entries, which are exactly the
facets of `K_n` that the certificate cone uses; and the affine constraint
`∑∑ A = n` is carried by membership in `K_n` rather than by a multiplier, so the
`λ(b)·(∑ b)` term of the outside-Lean certificate is absorbed into `hid`. -/

/-- **The certificate schema at `k = n`.**  Given the identity on `K_n`, the
nonnegativity of every `sigma`, and the fact that `sigma0` vanishes only at
`J_n/n`, Dittert's conjecture at dimension `n` follows. -/
theorem dittert_of_certificate (n : ℕ)
    (sigma0 : Matrix (Fin n) (Fin n) ℝ → ℝ)
    (sigma : Fin n × Fin n → Matrix (Fin n) (Fin n) ℝ → ℝ)
    (hn : n ≠ 0)
    (hid : ∀ A ∈ Kn n, bound n - phi A = sigma0 A + ∑ p, sigma p A * A p.1 p.2)
    (hs0 : ∀ A ∈ Kn n, 0 ≤ sigma0 A)
    (hs : ∀ p, ∀ A ∈ Kn n, 0 ≤ sigma p A)
    (hstrict : ∀ A ∈ Kn n, sigma0 A = 0 → A = uniform n) :
    DittertConj n := by
  set F : Matrix (Fin n) (Fin n) ℝ → ℝ := fun A => bound n - phi A with hF
  have hg : ∀ p : Fin n × Fin n, ∀ A ∈ Kn n, 0 ≤ A p.1 p.2 := fun p A hA => hA.1 p.1 p.2
  have hnn : ∀ A ∈ Kn n, 0 ≤ F A :=
    Certificate.nonneg_of_certificate F sigma0 sigma (fun p A => A p.1 p.2) hid hs0 hs hg
  have hzero : ∀ A ∈ Kn n, F A = 0 → A = uniform n :=
    Certificate.eq_of_certificate F sigma0 sigma (fun p A => A p.1 p.2) (uniform n)
      hid hs0 hs hg hstrict
  intro A hA
  refine ⟨by have := hnn A hA; simp only [hF] at this; linarith, ⟨fun h => ?_, fun h => ?_⟩⟩
  · exact hzero A hA (by simp only [hF]; linarith)
  · rw [h, phi_uniform hn]

/-- **The schema in the shape the anchor certificates take**: `sigma0` is the
quadratic form of a positive DEFINITE Gram matrix in a monomial vector `z` that
vanishes only at `J_n/n`.  Positive semidefiniteness would give the inequality
but not the equality case — that is the whole point of check `[4]` of
`sub-dittert/D45.md` insisting on definiteness. -/
theorem dittert_of_posDef_certificate {κ : Type*} [Fintype κ] [DecidableEq κ] (n : ℕ)
    (G : Matrix κ κ ℝ) (z : Matrix (Fin n) (Fin n) ℝ → κ → ℝ)
    (sigma : Fin n × Fin n → Matrix (Fin n) (Fin n) ℝ → ℝ)
    (hn : n ≠ 0)
    (hG : G.PosDef)
    (hid : ∀ A ∈ Kn n,
      bound n - phi A = Certificate.quadForm G (z A) + ∑ p, sigma p A * A p.1 p.2)
    (hs : ∀ p, ∀ A ∈ Kn n, 0 ≤ sigma p A)
    (hz : ∀ A ∈ Kn n, z A = 0 → A = uniform n) :
    DittertConj n :=
  dittert_of_certificate n (fun A => Certificate.quadForm G (z A)) sigma hn hid
    (fun A _ => Certificate.quadForm_nonneg hG.posSemidef (z A))
    hs
    (fun A hA h => hz A hA ((Certificate.quadForm_eq_zero_iff hG (z A)).mp h))

/-! ## 4.  Why `(3,3)` is not a corollary of the `k = 3` line

`subDittert_k3_full` carries the hypothesis `4 ≤ n`.  That hypothesis is not an
artefact of the proof: it is where the certificate's own positivity conditions
stop holding.  `CertPositive n` is the conjunction of the ten rational functions
of `SubDittertK3` §3, and the `σ₀` Gram additionally needs `c0Total` and
`c0Line` positive.  Three of those twelve are negative at `n = 3`. -/

/-- **The `k = 3` certificate fails at `n = 3`.**  So the general-`n` `k = 3`
certificate cannot be specialised to Dittert's diagonal cell `(3,3)`, and the
`4 ≤ n` in `subDittert_k3_full` is sharp for this certificate. -/
theorem not_certPositive_three : ¬ CertPositive (3 : ℝ) := by
  intro h
  have := h.2.1
  rw [theta1, theta1Num, theta1Den] at this
  norm_num at this

/-- The other two failures, recorded exactly. -/
theorem minorC2_three_neg : minorC2 (3 : ℝ) < 0 := by
  rw [minorC2, minorC2Num, minorC2Den]
  norm_num

theorem c0Line_three_neg : c0Line (3 : ℝ) < 0 := by
  rw [c0Line, c0LineNum, c0LineDen]
  norm_num

/-! ## 5.  Axiom audit

Build success is not an axiom audit: a file with no `sorry` in its source can
still rest on `sorryAx`.  Every theorem this file claims is listed. -/

section AxiomAudit

#print axioms esym_top
#print axioms E_top
#print axioms subPerm_top
#print axioms sigmaK_top
#print axioms P_top
#print axioms Phi_top
#print axioms phi_uniform
#print axioms permanent_two
#print axioms phi_two_identity
#print axioms dittert_two_of_sum
#print axioms dittert_two
#print axioms dittert_of_certificate
#print axioms dittert_of_posDef_certificate
#print axioms not_certPositive_three
#print axioms minorC2_three_neg
#print axioms c0Line_three_neg

end AxiomAudit

end Dittert
