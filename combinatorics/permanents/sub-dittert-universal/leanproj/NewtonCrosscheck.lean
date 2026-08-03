/-
# INDEPENDENT CROSS-CHECK of NewtonInequalities.lean — NOT part of the build

A second, independent proof of Newton's inequalities and the telescoped Maclaurin
consequence, written by a different agent with no sight of the in-repo proofs, by a
different route: Mathlib's coeff_eq_esymm_roots_of_card with the sign powers cancelled,
and an induction on the degree through a normalised Qc — against the in-repo induction
on the index through NewtonAt.  The statements agree with the in-repo versions, which
is the point: agreement of two independent proofs is evidence the statements are right.

This file is deliberately NOT in the lakefile.  It duplicates results that
NewtonInequalities.lean already proves; merging it would be maintenance cost with no
mathematical gain.  It is stored as evidence, renamed into its own namespace so it
elaborates alongside the completed file (verified: 12 audit lines, all standard, zero
errors, against commit a94bfcd).  Its own four mutation controls failed correctly when
run by its author.  Elaborate with: lake env lean NewtonCrosscheck.lean
-/
import NewtonInequalities

open Finset Polynomial

namespace NewtonCrosscheck
open NewtonIneq

variable {n : ℕ}

/-! ## A.  From a multiset of roots to a vector -/

theorem map_get_univ_val (l : List ℝ) :
    Multiset.map (fun i : Fin l.length => l.get i) (univ : Finset (Fin l.length)).val = ↑l := by
  rw [Fin.univ_val_map, List.ofFn_get]

theorem esymm_index_one (s : Multiset ℝ) (hs : 2 ≤ Multiset.card s) :
    2 * (Multiset.card s : ℝ) * s.esymm (Multiset.card s) * s.esymm (Multiset.card s - 2)
      ≤ ((Multiset.card s : ℝ) - 1) * (s.esymm (Multiset.card s - 1)) ^ 2 := by
  obtain ⟨l, rfl⟩ : ∃ l : List ℝ, (↑l : Multiset ℝ) = s := ⟨s.toList, Multiset.coe_toList s⟩
  rw [Multiset.coe_card] at hs ⊢
  have hbridge : ∀ k, (↑l : Multiset ℝ).esymm k = esymF k (fun i : Fin l.length => l.get i) := by
    intro k
    rw [esymF_eq_esymm, map_get_univ_val]
  simp only [hbridge]
  exact newton_index_one hs _

/-! ## B.  Newton's inequalities -/

/-- The normalised coefficients `Q_j = a_{m-j} / C(m,j)`. -/
noncomputable def Qc (p : ℝ[X]) (j : ℕ) : ℝ :=
  p.coeff (p.natDegree - j) / (p.natDegree.choose j : ℝ)

theorem Qc_derivative {p : ℝ[X]} (hp : RealRooted p) (hm : 1 ≤ p.natDegree) {j : ℕ}
    (hj : j ≤ p.natDegree - 1) :
    Qc (derivative p) j = (p.natDegree : ℝ) * Qc p j := by
  have hjm : j ≤ p.natDegree := by omega
  have hc1 : (0 : ℝ) < (p.natDegree.choose j : ℝ) := by exact_mod_cast Nat.choose_pos hjm
  have hc2 : (0 : ℝ) < ((p.natDegree - 1).choose j : ℝ) := by exact_mod_cast Nat.choose_pos hj
  have hkey : (p.natDegree.choose j : ℝ) * ((p.natDegree : ℝ) - (j : ℝ))
      = (p.natDegree : ℝ) * ((p.natDegree - 1).choose j : ℝ) := by
    have h := choose_mul_sub p.natDegree j hm
    have h' : ((p.natDegree.choose j * (p.natDegree - j) : ℕ) : ℝ)
        = ((p.natDegree * (p.natDegree - 1).choose j : ℕ) : ℝ) := by exact_mod_cast h
    push_cast [Nat.cast_sub hjm] at h'
    linarith
  unfold Qc
  rw [natDegree_derivative_of_realRooted hp, coeff_derivative_shift p p.natDegree j hm hj]
  field_simp
  linear_combination (p.coeff (p.natDegree - j)) * hkey

/-- The bottom of the induction: the index the derivative never reaches.  This is where
real-rootedness is consumed, through the roots. -/
theorem newton_bottom {p : ℝ[X]} (hp : RealRooted p) {j : ℕ} (hd : p.natDegree = j + 2) :
    Qc p j * Qc p (j + 2) ≤ Qc p (j + 1) ^ 2 := by
  have hcard : Multiset.card p.roots = j + 2 := Eq.trans hp hd
  -- the three coefficients, by Vieta on the roots
  have hcf0 : p.coeff 0 = p.leadingCoeff * (-1) ^ (j + 2) * p.roots.esymm (j + 2) := by
    have h := Polynomial.coeff_eq_esymm_roots_of_card hp (k := 0) (by omega)
    rw [hd] at h
    simpa using h
  have hcf1 : p.coeff 1 = p.leadingCoeff * (-1) ^ (j + 1) * p.roots.esymm (j + 1) := by
    have h := Polynomial.coeff_eq_esymm_roots_of_card hp (k := 1) (by omega)
    rw [hd] at h
    rw [show j + 2 - 1 = j + 1 by omega] at h
    exact h
  have hcf2 : p.coeff 2 = p.leadingCoeff * (-1) ^ j * p.roots.esymm j := by
    have h := Polynomial.coeff_eq_esymm_roots_of_card hp (k := 2) (by omega)
    rw [hd] at h
    rw [show j + 2 - 2 = j by omega] at h
    exact h
  -- the signs cancel
  have hs1 : ((-1 : ℝ)) ^ j * (-1 : ℝ) ^ (j + 2) = 1 := by
    rw [← pow_add, show j + (j + 2) = 2 * (j + 1) by ring, pow_mul]
    norm_num
  have hs2 : (((-1 : ℝ)) ^ (j + 1)) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul]
    norm_num
  have hprod : p.coeff 2 * p.coeff 0
      = p.leadingCoeff ^ 2 * (p.roots.esymm j * p.roots.esymm (j + 2)) := by
    rw [hcf2, hcf0]
    linear_combination (p.leadingCoeff ^ 2 * (p.roots.esymm j * p.roots.esymm (j + 2))) * hs1
  have hsq : p.coeff 1 ^ 2 = p.leadingCoeff ^ 2 * (p.roots.esymm (j + 1)) ^ 2 := by
    rw [hcf1]
    linear_combination (p.leadingCoeff ^ 2 * (p.roots.esymm (j + 1)) ^ 2) * hs2
  -- the binomial coefficients
  have hb0 : (j + 2).choose j = (j + 2).choose 2 := by
    simpa using Nat.choose_symm (show 2 ≤ j + 2 by omega)
  have hb1 : (j + 2).choose (j + 1) = j + 2 := by simp
  have hb2 : (j + 2).choose (j + 2) = 1 := Nat.choose_self _
  have hC2 : (((j + 2).choose 2 : ℕ) : ℝ) = ((j : ℝ) + 2) * ((j : ℝ) + 1) / 2 := by
    have h : (j + 2) * (j + 1) = (j + 2).choose 2 * 2 := by
      simpa using Nat.succ_mul_choose_eq (j + 1) 1
    have h' : (((j + 2) * (j + 1) : ℕ) : ℝ) = (((j + 2).choose 2 * 2 : ℕ) : ℝ) := by
      exact_mod_cast h
    push_cast at h'
    linarith
  -- the index-1 inequality for the root multiset
  have hbot : 2 * ((j : ℝ) + 2) * p.roots.esymm (j + 2) * p.roots.esymm j
      ≤ ((j : ℝ) + 1) * (p.roots.esymm (j + 1)) ^ 2 := by
    have h := esymm_index_one p.roots (by rw [hcard]; omega)
    rw [hcard, show j + 2 - 2 = j by omega, show j + 2 - 1 = j + 1 by omega] at h
    push_cast at h
    linarith
  -- assemble
  have hQ0 : Qc p j = p.coeff 2 / (((j + 2).choose 2 : ℕ) : ℝ) := by
    unfold Qc
    rw [hd, show j + 2 - j = 2 by omega, hb0]
  have hQ1 : Qc p (j + 1) = p.coeff 1 / (((j : ℝ) + 2)) := by
    unfold Qc
    rw [hd, show j + 2 - (j + 1) = 1 by omega, hb1]
    push_cast
    ring
  have hQ2 : Qc p (j + 2) = p.coeff 0 := by
    unfold Qc
    rw [hd, show j + 2 - (j + 2) = 0 by omega, hb2]
    simp
  have hjpos : (0 : ℝ) < (j : ℝ) + 2 := by positivity
  rw [hQ0, hQ1, hQ2, hC2, div_mul_eq_mul_div, div_pow,
    div_le_div_iff₀ (by positivity) (by positivity)]
  rw [hprod, hsq]
  nlinarith [mul_le_mul_of_nonneg_left hbot
    (mul_nonneg (sq_nonneg p.leadingCoeff) hjpos.le)]

private theorem newton_aux : ∀ (m : ℕ) (p : ℝ[X]), RealRooted p → p.natDegree = m →
    ∀ j : ℕ, j + 2 ≤ m → Qc p j * Qc p (j + 2) ≤ Qc p (j + 1) ^ 2 := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m IH =>
    intro p hp hdeg j hj
    rcases eq_or_lt_of_le hj with heq | hlt
    · exact newton_bottom hp (by omega)
    · have hq : RealRooted (derivative p) := realRooted_derivative hp
      have hqdeg : (derivative p).natDegree = m - 1 := by
        rw [natDegree_derivative_of_realRooted hp, hdeg]
      have hIH := IH (m - 1) (by omega) (derivative p) hq hqdeg j (by omega)
      have hm1 : 1 ≤ p.natDegree := by omega
      rw [Qc_derivative (j := j) hp hm1 (by omega),
        Qc_derivative (j := j + 2) hp hm1 (by omega),
        Qc_derivative (j := j + 1) hp hm1 (by omega)] at hIH
      have hdpos : (0 : ℝ) < (p.natDegree : ℝ) := by
        have : 0 < p.natDegree := by omega
        exact_mod_cast this
      refine le_of_mul_le_mul_left ?_ (pow_pos hdpos 2)
      calc (p.natDegree : ℝ) ^ 2 * (Qc p j * Qc p (j + 2))
          = ((p.natDegree : ℝ) * Qc p j) * ((p.natDegree : ℝ) * Qc p (j + 2)) := by ring
        _ ≤ ((p.natDegree : ℝ) * Qc p (j + 1)) ^ 2 := hIH
        _ = (p.natDegree : ℝ) ^ 2 * (Qc p (j + 1) ^ 2) := by ring

/-- **Newton's inequalities** for a real-rooted polynomial. -/
theorem newton_Qc {p : ℝ[X]} (hp : RealRooted p) {j : ℕ} (hj : j + 2 ≤ p.natDegree) :
    Qc p j * Qc p (j + 2) ≤ Qc p (j + 1) ^ 2 :=
  newton_aux p.natDegree p hp rfl j hj

theorem realRooted_polyOf (v : Fin n → ℝ) : RealRooted (polyOf v) := by
  refine Polynomial.splits_iff_card_roots.mp ?_
  unfold polyOf
  refine Polynomial.splits_prod _ fun i _ => ?_
  have h : (X + C (v i) : ℝ[X]) = X - C (-(v i)) := by
    rw [map_neg]; ring
  rw [h]
  exact Polynomial.splits_X_sub_C _

theorem Qc_polyOf (v : Fin n → ℝ) {j : ℕ} (hj : j ≤ n) :
    Qc (polyOf v) j = esymF j v / (n.choose j : ℝ) := by
  unfold Qc
  rw [polyOf_natDegree, polyOf_coeff v hj]

/-- **Newton's inequalities** for the elementary symmetric functions of a real vector. -/
theorem newton_esymF (v : Fin n → ℝ) {j : ℕ} (hj : j + 2 ≤ n) :
    (esymF j v / (n.choose j : ℝ)) * (esymF (j + 2) v / (n.choose (j + 2) : ℝ))
      ≤ (esymF (j + 1) v / (n.choose (j + 1) : ℝ)) ^ 2 := by
  have h := newton_Qc (realRooted_polyOf v) (j := j) (by rw [polyOf_natDegree]; exact hj)
  rwa [Qc_polyOf v (show j ≤ n by omega), Qc_polyOf v (show j + 2 ≤ n by omega),
    Qc_polyOf v (show j + 1 ≤ n by omega)] at h

/-! ## C.  Maclaurin, telescoped -/

theorem esymF_zero (v : Fin n → ℝ) : esymF 0 v = 1 := by
  unfold esymF
  simp

theorem esymF_nonneg {v : Fin n → ℝ} (hv : ∀ i, 0 ≤ v i) (k : ℕ) : 0 ≤ esymF k v :=
  Finset.sum_nonneg fun _ _ => Finset.prod_nonneg fun i _ => hv i

/-- For a non-negative vector, the elementary symmetric functions vanish from the first
zero onwards: `e_k = 0` forces fewer than `k` non-zero entries. -/
theorem esymF_succ_eq_zero {v : Fin n → ℝ} (hv : ∀ i, 0 ≤ v i) {k : ℕ}
    (hk : esymF k v = 0) : esymF (k + 1) v = 0 := by
  classical
  set T := (univ : Finset (Fin n)).filter (fun i => v i ≠ 0) with hT
  have hcard : T.card < k := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨S, hST, hScard⟩ := Finset.exists_subset_card_eq hcon
    have hpos : 0 < esymF k v := by
      refine Finset.sum_pos' (fun _ _ => Finset.prod_nonneg fun i _ => hv i) ⟨S, ?_, ?_⟩
      · exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ S, hScard⟩
      · refine Finset.prod_pos fun i hi => ?_
        have hiT := hST hi
        rw [hT, Finset.mem_filter] at hiT
        exact lt_of_le_of_ne (hv i) (Ne.symm hiT.2)
    rw [hk] at hpos
    exact lt_irrefl 0 hpos
  refine Finset.sum_eq_zero fun S hS => ?_
  have hScard := (Finset.mem_powersetCard.mp hS).2
  have hnsub : ¬ S ⊆ T := fun h => by
    have := Finset.card_le_card h
    omega
  obtain ⟨i, hiS, hiT⟩ := Finset.not_subset.mp hnsub
  refine Finset.prod_eq_zero hiS ?_
  by_contra hvi
  exact hiT (by rw [hT, Finset.mem_filter]; exact ⟨Finset.mem_univ i, hvi⟩)

/-- **Maclaurin's inequality, telescoped.**  On the simplex `∑ v = n` with `v ≥ 0`, the
normalised elementary symmetric functions decrease from index 1 onwards, so `E_k ≤ E_2`
for every `2 ≤ k ≤ n`.  No fractional powers appear. -/
theorem maclaurin_le_two (hn : 2 ≤ n) (v : Fin n → ℝ) (hv : ∀ i, 0 ≤ v i)
    (hsum : (∑ i, v i) = (n : ℝ)) {k : ℕ} (hk : 2 ≤ k) (hkn : k ≤ n) :
    esymF k v / (n.choose k : ℝ) ≤ esymF 2 v / (n.choose 2 : ℝ) := by
  have hnR : (0 : ℝ) < (n : ℝ) := by
    have : 0 < n := by omega
    exact_mod_cast this
  have hchoose : ∀ j : ℕ, j ≤ n → (0 : ℝ) < (n.choose j : ℝ) := by
    intro j hj
    exact_mod_cast Nat.choose_pos hj
  have hFnonneg : ∀ j : ℕ, 0 ≤ esymF j v / (n.choose j : ℝ) := fun j =>
    div_nonneg (esymF_nonneg hv j) (by positivity)
  have hF0 : esymF 0 v / (n.choose 0 : ℝ) = 1 := by
    rw [esymF_zero, Nat.choose_zero_right]
    norm_num
  have hF1 : esymF 1 v / (n.choose 1 : ℝ) = 1 := by
    rw [esymF_one, hsum, Nat.choose_one_right]
    exact div_self hnR.ne'
  have hzero : ∀ j : ℕ, j ≤ n → esymF j v / (n.choose j : ℝ) = 0 →
      esymF (j + 1) v / (n.choose (j + 1) : ℝ) = 0 := by
    intro j hjn hj
    have h1 : esymF j v = 0 := by
      rcases div_eq_zero_iff.mp hj with h | h
      · exact h
      · exact absurd h (hchoose j hjn).ne'
    rw [esymF_succ_eq_zero hv h1, zero_div]
  have descent : ∀ j : ℕ, 1 ≤ j → j + 1 ≤ n →
      esymF (j + 1) v / (n.choose (j + 1) : ℝ) ≤ esymF j v / (n.choose j : ℝ) := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base =>
        intro _
        have hnewt : (esymF 0 v / (n.choose 0 : ℝ)) * (esymF 2 v / (n.choose 2 : ℝ))
            ≤ (esymF 1 v / (n.choose 1 : ℝ)) ^ 2 := newton_esymF v (by omega)
        rw [hF0, hF1] at hnewt
        show esymF 2 v / (n.choose 2 : ℝ) ≤ esymF 1 v / (n.choose 1 : ℝ)
        rw [hF1]
        linarith
    | succ j hj ih =>
        intro hjn
        have hnewt : (esymF j v / (n.choose j : ℝ)) * (esymF (j + 2) v / (n.choose (j + 2) : ℝ))
            ≤ (esymF (j + 1) v / (n.choose (j + 1) : ℝ)) ^ 2 := newton_esymF v (by omega)
        show esymF (j + 2) v / (n.choose (j + 2) : ℝ) ≤ esymF (j + 1) v / (n.choose (j + 1) : ℝ)
        rcases eq_or_lt_of_le (hFnonneg j) with hzj | hpj
        · have h1 := hzero j (by omega) hzj.symm
          have h2 := hzero (j + 1) (by omega) h1
          rw [show j + 1 + 1 = j + 2 by omega] at h2
          rw [h2]
          exact hFnonneg (j + 1)
        · have hih := ih (by omega)
          refine le_of_mul_le_mul_left ?_ hpj
          nlinarith [hFnonneg (j + 1), hih, hnewt]
  have chain : ∀ m : ℕ, 2 ≤ m → m ≤ n →
      esymF m v / (n.choose m : ℝ) ≤ esymF 2 v / (n.choose 2 : ℝ) := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => intro _; exact le_refl _
    | succ m hm ih =>
        intro hmn
        have h1 := ih (by omega)
        have h2 := descent m (by omega) (by omega)
        linarith
  exact chain k hk hkn

section AxiomAudit

#print axioms map_get_univ_val
#print axioms esymm_index_one
#print axioms Qc_derivative
#print axioms newton_bottom
#print axioms newton_Qc
#print axioms realRooted_polyOf
#print axioms Qc_polyOf
#print axioms newton_esymF
#print axioms esymF_zero
#print axioms esymF_nonneg
#print axioms esymF_succ_eq_zero
#print axioms maclaurin_le_two

end AxiomAudit

end NewtonCrosscheck
