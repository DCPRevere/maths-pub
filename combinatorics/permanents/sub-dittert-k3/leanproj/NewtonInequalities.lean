/-
# Newton's inequalities and Maclaurin's inequality

**This file is library material, not application material.**  It mentions no permanent,
no `K_n`, and nothing from the sub-Dittert programme; it imports only Mathlib.  The
boundary is deliberate: Newton's inequalities and Maclaurin's inequality are **absent from
Mathlib v4.14.0** — `RingTheory/MvPolynomial/Symmetric/NewtonIdentities.lean` carries
Newton's *identities* only, and the sole occurrence of "Maclaurin" in the library is the
Maclaurin *series* of `arctan` — so this half is a candidate for upstreaming, and it must
stay separable from the use made of it.

The application, which will discharge `SubDittertM.MaclaurinBound`, lives in its own file.

## What is proved

All of it is kernel-checked with no `sorry`.

* §1 `esymF`, the elementary symmetric function of a vector, written to match
  `SubDittertK3.esym` definitionally; the bridge to Mathlib's `Multiset.esymm`; and
  `esymF_compl`, the reciprocal identity `e_{n-j}(v) = (∏ v) · e_j(v⁻¹)`.
* §2 `RealRooted`, closure under products, and **Rolle for real-rooted polynomials**.
* §3 the bookkeeping: `polyOf v = ∏ (X + v i)`, **Vieta**, the derivative's coefficients,
  the binomial shift `C(m,j)(m−j) = m·C(m−1,j)`, and the derivative's exact degree.
* §4 **Newton at index 1**, at every degree, together with `esymS_two`
  (`2 e₂ = (∑v)² − ∑v²`, by induction on the Finset, because Mathlib carries that identity
  only inside `MvPolynomial`).
* §5 the root vector of a real-rooted polynomial, which is what lets §4 be applied to a
  derivative.
* §6 **`newtonAt_all` — Newton's inequality for every real-rooted real polynomial**, at
  every position, by induction on the index.
* §7 **`newton_esymF` — Newton in vector form**: `e_{j−1} e_{j+1} C(n,j)² ≤ e_j² C(n,j−1)
  C(n,j+1)`.  No positivity is needed.
* §8 **`pnorm_le_two` — Maclaurin, telescoped**: for `v ≥ 0` on the simplex `∑ v = n`,
  `p_k ≤ p_2` for `2 ≤ k ≤ n`, where `p_j = e_j / C(n,j)`.  **No fractional powers
  appear**, unlike the usual `p_k^{1/k} ≤ p_2^{1/2}` form; that is what makes this the
  formalisable statement, and it is the one the application needs.

## The route, and why there is no `Polynomial.reverse` in it

`Q'_i = m · Q_{i+1}` for `Q_i = coeff i / C(m,i)` (§3), so Newton at index `i` for `p` is
Newton at index `i−1` for `p'`, and `p'` is real-rooted by §2.  That reduces every index
`i ≥ 2` to a lower degree.  **Differentiation shifts the index up, so `i = 1` is never
reached by the induction**: it is not a base case at one degree but must be proved
directly at every degree, and it is where real-rootedness is consumed.  §4 does that,
through `esymF_compl` and Chebyshev's `sq_sum_le_card_mul_sum_sq`, with the vanishing case
`e_m = 0` handled separately in two lines.

The reversal of polynomials, which the textbook proof uses and whose root theory Mathlib
does not carry, appears nowhere.

## Working note: a stale olean can shadow a rebuild, silently

`SubDittertUniversal.lean`'s header describes importing an uncommitted sibling by
compiling a private olean into a scratch directory and putting it on `LEAN_PATH`.  That
note is right but incomplete, and the omission cost time here: the directory must be
PREPENDED, not appended.

    lake env sh -c 'LEAN_PATH=/scratch:$LEAN_PATH lean Downstream.lean'   -- correct
    lake env sh -c 'LEAN_PATH=$LEAN_PATH:/scratch lean Downstream.lean'   -- wrong

Once anyone runs `lake build`, `.lake/build/lib` holds an olean for this file, and with
the appended form that stale copy wins.  The symptom is `unknown identifier` for
declarations that are visibly present in the source and that elaborate without error —
which reads like a namespace bug and is not one.  Check `.lake/build/lib/*.olean`
timestamps against the sources before believing any such error.  An earlier draft of this header said `esymF_compl` might
end up unused; §4 consumes it.
-/
import Mathlib.Tactic
import Mathlib.Analysis.Calculus.LocalExtr.Polynomial
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.Algebra.Order.Chebyshev

open Finset Polynomial

namespace NewtonIneq

variable {n : ℕ}

/-! ## 1.  Elementary symmetric functions

`esymF` is written exactly as `SubDittertK3.esym`, so that the bridge in the application
file is `rfl`.  Keeping the definition here rather than importing it is what makes this
file Mathlib-only. -/

/-- The `k`-th elementary symmetric function of a vector. -/
def esymF (k : ℕ) (v : Fin n → ℝ) : ℝ :=
  ∑ S ∈ Finset.powersetCard k (univ : Finset (Fin n)), ∏ i ∈ S, v i

theorem esymF_eq_esymm (k : ℕ) (v : Fin n → ℝ) :
    esymF k v = (Multiset.map v (univ : Finset (Fin n)).val).esymm k :=
  (Finset.esymm_map_val v univ k).symm

/-- **The reciprocal identity.**  `e_{n-j}(v) = (∏ v) · e_j(1/v)` when no entry vanishes.
This is what replaces the reversal of polynomials in the top case of Newton. -/
theorem esymF_compl (v : Fin n → ℝ) (hv : ∀ i, v i ≠ 0) (j : ℕ) (hj : j ≤ n) :
    esymF (n - j) v = (∏ i, v i) * esymF j (fun i => (v i)⁻¹) := by
  classical
  unfold esymF
  rw [Finset.mul_sum]
  refine Finset.sum_bij' (fun T _ => Tᶜ) (fun S _ => Sᶜ) ?_ ?_ ?_ ?_ ?_
  · intro T hT
    rw [Finset.mem_powersetCard_univ] at hT ⊢
    rw [Finset.card_compl, Fintype.card_fin, hT]
    omega
  · intro S hS
    rw [Finset.mem_powersetCard_univ] at hS ⊢
    rw [Finset.card_compl, Fintype.card_fin, hS]
  · intro T _
    exact compl_compl T
  · intro S _
    exact compl_compl S
  · intro T _
    have hne : (∏ i ∈ Tᶜ, v i) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => hv i
    rw [Finset.prod_inv_distrib, ← Finset.prod_mul_prod_compl T v, mul_assoc,
      mul_inv_cancel₀ hne, mul_one]

/-! ## 2.  Real-rooted polynomials -/

/-- A real polynomial is *real-rooted* when it has as many real roots, with multiplicity,
as its degree. -/
def RealRooted (p : ℝ[X]) : Prop := Multiset.card p.roots = p.natDegree

theorem realRooted_mul {p q : ℝ[X]} (hp0 : p ≠ 0) (hq0 : q ≠ 0)
    (hp : RealRooted p) (hq : RealRooted q) : RealRooted (p * q) := by
  unfold RealRooted at *
  rw [Polynomial.roots_mul (mul_ne_zero hp0 hq0), Multiset.card_add, hp, hq,
    Polynomial.natDegree_mul hp0 hq0]

/-- **Rolle for real-rooted polynomials.**  The derivative of a real-rooted real
polynomial is real-rooted.  Mathlib's `card_roots_le_derivative` supplies the only
analytic input; the exact degree of the derivative is not needed, because the count is
pinned by a squeeze. -/
theorem realRooted_derivative {p : ℝ[X]} (hp : RealRooted p) : RealRooted (derivative p) := by
  unfold RealRooted at *
  rcases eq_or_ne p.natDegree 0 with h0 | h0
  · have hd : derivative p = 0 := by
      rw [Polynomial.eq_C_of_natDegree_eq_zero h0, Polynomial.derivative_C]
    rw [hd]
    simp
  · have h1 := Polynomial.card_roots_le_derivative p
    have h2 := Polynomial.card_roots' (derivative p)
    have h3 := Polynomial.natDegree_derivative_le p
    omega

/-! ## 3.  The bookkeeping: Vieta, and what differentiation does to the coefficients -/

/-- `∏ (X + v i)`, the polynomial whose coefficients are the elementary symmetric
functions of `v`. -/
noncomputable def polyOf (v : Fin n → ℝ) : ℝ[X] := ∏ i, (X + C (v i))

theorem polyOf_ne_zero (v : Fin n → ℝ) : polyOf v ≠ 0 := by
  unfold polyOf
  refine Finset.prod_ne_zero_iff.mpr fun i _ => ?_
  intro h
  have := congrArg (fun q : ℝ[X] => q.coeff 1) h
  simp at this

theorem polyOf_monic (v : Fin n → ℝ) : (polyOf v).Monic := by
  unfold polyOf
  exact monic_prod_of_monic _ _ fun i _ => monic_X_add_C (v i)

@[simp] theorem polyOf_natDegree (v : Fin n → ℝ) : (polyOf v).natDegree = n := by
  unfold polyOf
  rw [Polynomial.natDegree_prod _ _ fun i _ => X_add_C_ne_zero (v i)]
  simp

/-- **Vieta.**  The coefficient of `X^(n-j)` in `∏ (X + v i)` is `e_j(v)`. -/
theorem polyOf_coeff (v : Fin n → ℝ) {j : ℕ} (hj : j ≤ n) :
    (polyOf v).coeff (n - j) = esymF j v := by
  have hcard : Multiset.card (Multiset.map v (univ : Finset (Fin n)).val) = n := by simp
  have hprod : polyOf v
      = (Multiset.map (fun r => X + C r) (Multiset.map v (univ : Finset (Fin n)).val)).prod := by
    unfold polyOf
    rw [Multiset.map_map]
    rfl
  rw [hprod, Multiset.prod_X_add_C_coeff _ (by omega : n - j ≤ _), hcard,
    show n - (n - j) = j by omega, esymF_eq_esymm]

/-- **The derivative's coefficients**, in the indexing Newton uses. -/
theorem coeff_derivative_shift (p : ℝ[X]) (m j : ℕ) (hm : 1 ≤ m) (hj : j ≤ m - 1) :
    (derivative p).coeff (m - 1 - j) = p.coeff (m - j) * ((m : ℝ) - (j : ℝ)) := by
  rw [Polynomial.coeff_derivative]
  congr 1
  · congr 1
    omega
  · have : ((m - 1 - j : ℕ) : ℝ) = (m : ℝ) - (j : ℝ) - 1 := by
      have h1 : ((m - 1 - j : ℕ) : ℝ) = ((m - 1 - j : ℕ) : ℝ) := rfl
      rw [show m - 1 - j = m - (j + 1) by omega, Nat.cast_sub (by omega)]
      push_cast
      ring
    rw [this]
    ring

/-- **The binomial shift**: `C(m,j)·(m−j) = m·C(m−1,j)`.  This is what makes the
normalised coefficients scale by exactly the degree under differentiation. -/
theorem choose_mul_sub (m j : ℕ) (hm : 1 ≤ m) :
    m.choose j * (m - j) = m * (m - 1).choose j := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  calc (m' + 1).choose j * (m' + 1 - j)
      = (m' + 1).choose (j + 1) * (j + 1) := (Nat.choose_succ_right_eq (m' + 1) j).symm
    _ = (m' + 1) * m'.choose j := (Nat.succ_mul_choose_eq m' j).symm

/-- The exact degree of the derivative, for a real-rooted polynomial.  Mathlib carries no
char-zero `natDegree_derivative_eq`; the same squeeze that proves `realRooted_derivative`
pins it, so none is needed. -/
theorem natDegree_derivative_of_realRooted {p : ℝ[X]} (hp : RealRooted p) :
    (derivative p).natDegree = p.natDegree - 1 := by
  unfold RealRooted at hp
  have h1 := Polynomial.card_roots_le_derivative p
  have h2 := Polynomial.card_roots' (derivative p)
  have h3 := Polynomial.natDegree_derivative_le p
  omega

variable {ι : Type*} [DecidableEq ι]


/-- Elementary symmetric function over an arbitrary Finset, for the induction. -/
def esymS (k : ℕ) (s : Finset ι) (v : ι → ℝ) : ℝ :=
  ∑ S ∈ Finset.powersetCard k s, ∏ i ∈ S, v i

omit [DecidableEq ι] in
theorem esymS_one (s : Finset ι) (v : ι → ℝ) : esymS 1 s v = ∑ i ∈ s, v i := by
  unfold esymS
  rw [Finset.powersetCard_one, Finset.sum_map]
  exact Finset.sum_congr rfl fun i _ => by simp

/-- `2 e₂ = (∑ v)² − ∑ v²`, by induction on the Finset. -/
theorem esymS_two (s : Finset ι) (v : ι → ℝ) :
    2 * esymS 2 s v = (∑ i ∈ s, v i) ^ 2 - ∑ i ∈ s, v i ^ 2 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      unfold esymS
      rw [Finset.powersetCard_eq_empty.mpr (by simp)]
      simp
  | @insert a s ha ih =>
      have hdisj : Disjoint (Finset.powersetCard 2 s)
          ((Finset.powersetCard 1 s).image (insert a)) := by
        rw [Finset.disjoint_right]
        rintro T hT hT2
        simp only [Finset.mem_image] at hT
        obtain ⟨U, hU, rfl⟩ := hT
        have : a ∈ insert a U := Finset.mem_insert_self a U
        have hsub := (Finset.mem_powersetCard.mp hT2).1
        exact ha (hsub this)
      have hinj : Set.InjOn (insert a) (Finset.powersetCard 1 s : Set (Finset ι)) := by
        intro U hU V hV huv
        have hUs := (Finset.mem_powersetCard.mp (by simpa using hU)).1
        have hVs := (Finset.mem_powersetCard.mp (by simpa using hV)).1
        have hUa : a ∉ U := fun h => ha (hUs h)
        have hVa : a ∉ V := fun h => ha (hVs h)
        rw [← Finset.erase_insert hUa, ← Finset.erase_insert hVa, huv]
      have hkey : esymS 2 (insert a s) v = esymS 2 s v + v a * ∑ i ∈ s, v i := by
        unfold esymS
        rw [Finset.powersetCard_succ_insert ha, Finset.sum_union hdisj,
          Finset.sum_image hinj]
        congr 1
        rw [← esymS_one s v]
        unfold esymS
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun U hU => ?_
        have hUa : a ∉ U := fun h => ha ((Finset.mem_powersetCard.mp hU).1 h)
        rw [Finset.prod_insert hUa]
      rw [hkey, Finset.sum_insert ha, Finset.sum_insert ha]
      have := ih
      ring_nf
      ring_nf at this
      linarith

/-! ## 4.  Newton at index 1

The induction of the intended route reduces every index `i ≥ 2` to a lower degree, but
never reaches `i = 1`: differentiation shifts the index up.  So index 1 must be proved
directly, at every degree, and it is where real-rootedness is consumed.  Everything here
is vector-based; no multiset appears. -/


theorem esymF_one {m : ℕ} (v : Fin m → ℝ) : esymF 1 v = ∑ i, v i := esymS_one univ v

theorem esymF_two {m : ℕ} (v : Fin m → ℝ) :
    2 * esymF 2 v = (∑ i, v i) ^ 2 - ∑ i, v i ^ 2 := esymS_two univ v

theorem esymF_card {m : ℕ} (v : Fin m → ℝ) : esymF m v = ∏ i, v i := by
  unfold esymF
  have h : Finset.powersetCard m (univ : Finset (Fin m)) = {univ} := by
    simpa using Finset.powersetCard_self (univ : Finset (Fin m))
  rw [h, Finset.sum_singleton]

/-- **Newton at index 1**, at every degree: `2m·e_m·e_{m-2} ≤ (m-1)·e_{m-1}²`. -/
theorem newton_index_one {m : ℕ} (hm : 2 ≤ m) (v : Fin m → ℝ) :
    2 * (m : ℝ) * esymF m v * esymF (m - 2) v ≤ ((m : ℝ) - 1) * (esymF (m - 1) v) ^ 2 := by
  have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  by_cases hz : ∃ i, v i = 0
  · obtain ⟨i, hi⟩ := hz
    have h0 : esymF m v = 0 := by
      rw [esymF_card]
      exact Finset.prod_eq_zero (mem_univ i) hi
    rw [h0]
    nlinarith [sq_nonneg (esymF (m - 1) v)]
  · push_neg at hz
    set y : Fin m → ℝ := fun i => (v i)⁻¹ with hy
    have h0 : esymF m v = ∏ i, v i := esymF_card v
    have h1 : esymF (m - 1) v = (∏ i, v i) * esymF 1 y := esymF_compl v hz 1 (by omega)
    have h2 : esymF (m - 2) v = (∏ i, v i) * esymF 2 y := esymF_compl v hz 2 (by omega)
    have hcheb : (∑ i, y i) ^ 2 ≤ (m : ℝ) * ∑ i, y i ^ 2 := by
      have h := sq_sum_le_card_mul_sum_sq (s := (univ : Finset (Fin m))) (f := y)
      simpa using h
    have he1 : esymF 1 y = ∑ i, y i := esymF_one y
    have he2 : 2 * esymF 2 y = (∑ i, y i) ^ 2 - ∑ i, y i ^ 2 := esymF_two y
    have hkey : 2 * (m : ℝ) * esymF 2 y ≤ ((m : ℝ) - 1) * (esymF 1 y) ^ 2 := by
      rw [he1]
      nlinarith [hcheb, he2]
    rw [h0, h1, h2]
    nlinarith [hkey, sq_nonneg (∏ i, v i)]

/-! ## 5.  From a real-rooted polynomial to a root vector

The induction of §6 bottoms out at index 1 of a DERIVATIVE, so §4 must be available for an
arbitrary real-rooted polynomial, whose roots are a `Multiset`.  This section presents
them as a vector. -/

section Roots

theorem exists_vector_of_card {d : ℕ} (s : Multiset ℝ) (h : Multiset.card s = d) :
    ∃ v : Fin d → ℝ, Multiset.map v (univ : Finset (Fin d)).val = s := by
  have hlist : Multiset.map s.toList.get (univ : Finset (Fin s.toList.length)).val = s := by
    have : Multiset.map s.toList.get (univ : Finset (Fin s.toList.length)).val
        = ((s.toList : Multiset ℝ)) := by
      rw [show (univ : Finset (Fin s.toList.length)).val
            = ↑(List.finRange s.toList.length) from rfl,
        Multiset.map_coe, List.finRange_map_get]
    rw [this, Multiset.coe_toList]
  have hlen : s.toList.length = d := by rw [Multiset.length_toList, h]
  subst hlen
  exact ⟨_, hlist⟩

theorem exists_root_vector {p : ℝ[X]} (hp : RealRooted p) :
    ∃ w : Fin p.natDegree → ℝ, p = C p.leadingCoeff * polyOf w := by
  have hcard : Multiset.card (Multiset.map (fun a : ℝ => -a) p.roots) = p.natDegree := by
    rw [Multiset.card_map]; exact hp
  obtain ⟨w, hw⟩ := exists_vector_of_card _ hcard
  refine ⟨w, ?_⟩
  have hfac := Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C hp
  have hkey : (Multiset.map (fun a : ℝ => X - C a) p.roots).prod = polyOf w := by
    unfold polyOf
    have h1 : (∏ i, (X + C (w i)))
        = (Multiset.map (fun r : ℝ => X + C r)
            (Multiset.map w (univ : Finset (Fin p.natDegree)).val)).prod := by
      rw [Multiset.map_map]
      rfl
    rw [h1, hw, Multiset.map_map]
    congr 1
    exact Multiset.map_congr rfl fun a _ => by
      simp only [Function.comp_apply, Polynomial.C_neg, sub_eq_add_neg]
  calc p = C p.leadingCoeff * (Multiset.map (fun a : ℝ => X - C a) p.roots).prod := hfac.symm
    _ = C p.leadingCoeff * polyOf w := by rw [hkey]

/-! ## 6.  Newton for real-rooted polynomials, by induction on the index -/

/-- Newton's inequality at position `i`, multiplicative form. -/
def NewtonAt (p : ℝ[X]) (i : ℕ) : Prop :=
  p.coeff i * p.coeff (i + 2) * ((p.natDegree.choose (i + 1) : ℕ) : ℝ) ^ 2
    ≤ (p.coeff (i + 1)) ^ 2
        * ((p.natDegree.choose i : ℕ) : ℝ) * ((p.natDegree.choose (i + 2) : ℕ) : ℝ)

private theorem cast_choose_two (m : ℕ) (hm : 1 ≤ m) :
    2 * ((m.choose 2 : ℕ) : ℝ) = ((m : ℝ) - 1) * (m : ℝ) := by
  have h : m.descFactorial 2 = (m - 1) * m := by simp [Nat.descFactorial]
  have h2 : m.descFactorial 2 = 2 * m.choose 2 := by
    rw [Nat.descFactorial_eq_factorial_mul_choose]
    norm_num [Nat.factorial]
  have h3 : ((m - 1) * m : ℕ) = ((m.descFactorial 2 : ℕ)) := h.symm
  have : ((2 * m.choose 2 : ℕ) : ℝ) = (((m - 1) * m : ℕ) : ℝ) := by
    rw [← h2, h]
  push_cast [Nat.cast_sub hm] at this
  linarith

/-- **Newton at `i = 0`**, for any real-rooted polynomial: the case the induction bottoms
out at, transported from the vector statement through the root vector. -/
theorem newtonAt_zero {p : ℝ[X]} (hp : RealRooted p) (hm : 2 ≤ p.natDegree) :
    NewtonAt p 0 := by
  obtain ⟨w, hw⟩ := exists_root_vector hp
  have hmR : (2 : ℝ) ≤ (p.natDegree : ℝ) := by exact_mod_cast hm
  have hc : ∀ j : ℕ, j ≤ p.natDegree →
      p.coeff (p.natDegree - j) = p.leadingCoeff * esymF j w := by
    intro j hj
    have hrw : p.coeff (p.natDegree - j)
        = (C p.leadingCoeff * polyOf w).coeff (p.natDegree - j) := by rw [← hw]
    rw [hrw, Polynomial.coeff_C_mul, polyOf_coeff w hj]
  have h0 : p.coeff 0 = p.leadingCoeff * esymF p.natDegree w := by
    have h := hc p.natDegree (le_refl _)
    simpa using h
  have h1 : p.coeff 1 = p.leadingCoeff * esymF (p.natDegree - 1) w := by
    have h := hc (p.natDegree - 1) (by omega)
    rwa [show p.natDegree - (p.natDegree - 1) = 1 by omega] at h
  have h2 : p.coeff 2 = p.leadingCoeff * esymF (p.natDegree - 2) w := by
    have h := hc (p.natDegree - 2) (by omega)
    rwa [show p.natDegree - (p.natDegree - 2) = 2 by omega] at h
  have hidx := newton_index_one hm w
  have hch2 := cast_choose_two p.natDegree (by omega)
  have hch2' : ((p.natDegree.choose 2 : ℕ) : ℝ)
      = ((p.natDegree : ℝ) - 1) * (p.natDegree : ℝ) / 2 := by linarith
  unfold NewtonAt
  rw [h0, h1, h2]
  simp only [zero_add, Nat.choose_zero_right, Nat.choose_one_right, Nat.cast_one,
    one_mul, mul_one, hch2']
  nlinarith [mul_le_mul_of_nonneg_left hidx
      (by positivity : (0:ℝ) ≤ p.leadingCoeff ^ 2 * (p.natDegree : ℝ) / 2)]

/-- **The induction step.**  `Q'_i = m · Q_{i+1}` in multiplicative form. -/
theorem newtonAt_succ {p : ℝ[X]} (hp : RealRooted p) (i : ℕ) (hi : i + 3 ≤ p.natDegree)
    (H : NewtonAt (derivative p) i) : NewtonAt p (i + 1) := by
  have hdeg : (derivative p).natDegree = p.natDegree - 1 :=
    natDegree_derivative_of_realRooted hp
  have hrel : ∀ k : ℕ, (p.natDegree : ℝ) * (((p.natDegree - 1).choose k : ℕ) : ℝ)
      = ((k : ℝ) + 1) * ((p.natDegree.choose (k + 1) : ℕ) : ℝ) := by
    intro k
    have hn : (p.natDegree - 1).succ = p.natDegree := by omega
    have h := Nat.succ_mul_choose_eq (p.natDegree - 1) k
    rw [hn] at h
    have h2 := congrArg (fun t : ℕ => (t : ℝ)) h
    push_cast at h2
    linarith
  unfold NewtonAt at H ⊢
  rw [hdeg] at H
  simp only [Polynomial.coeff_derivative] at H
  set A := p.coeff (i + 1) with hA
  set B := p.coeff (i + 2) with hB
  set Cc := p.coeff (i + 3) with hCc
  set X1 := ((p.natDegree.choose (i + 1) : ℕ) : ℝ) with hX1
  set X2 := ((p.natDegree.choose (i + 2) : ℕ) : ℝ) with hX2
  set X3 := ((p.natDegree.choose (i + 3) : ℕ) : ℝ) with hX3
  set P0 := (((p.natDegree - 1).choose i : ℕ) : ℝ) with hP0
  set P1 := (((p.natDegree - 1).choose (i + 1) : ℕ) : ℝ) with hP1
  set P2 := (((p.natDegree - 1).choose (i + 2) : ℕ) : ℝ) with hP2
  have h0 : (p.natDegree : ℝ) * P0 = ((i : ℝ) + 1) * X1 := hrel i
  have h1 : (p.natDegree : ℝ) * P1 = ((i : ℝ) + 2) * X2 := by
    have := hrel (i + 1); push_cast at this ⊢; linarith
  have h2 : (p.natDegree : ℝ) * P2 = ((i : ℝ) + 3) * X3 := by
    have := hrel (i + 2); push_cast at this ⊢; linarith
  have hc : (0 : ℝ) < ((i : ℝ) + 1) * ((i : ℝ) + 3) * ((i : ℝ) + 2) ^ 2 := by positivity
  refine le_of_mul_le_mul_left ?_ hc
  have Hs := mul_le_mul_of_nonneg_left H (sq_nonneg (p.natDegree : ℝ))
  calc ((i : ℝ) + 1) * ((i : ℝ) + 3) * ((i : ℝ) + 2) ^ 2 * (A * Cc * X2 ^ 2)
      = (p.natDegree : ℝ) ^ 2
          * (A * ((i : ℝ) + 1) * (Cc * ((i : ℝ) + 1 + 2)) * P1 ^ 2) := by
        linear_combination
          (-(A * Cc * ((i : ℝ) + 1) * ((i : ℝ) + 3)
            * ((p.natDegree : ℝ) * P1 + ((i : ℝ) + 2) * X2))) * h1
    _ ≤ (p.natDegree : ℝ) ^ 2 * ((B * ((i : ℝ) + 1 + 1)) ^ 2 * P0 * P2) := by
        push_cast at Hs ⊢
        linarith [Hs]
    _ = ((i : ℝ) + 1) * ((i : ℝ) + 3) * ((i : ℝ) + 2) ^ 2 * (B ^ 2 * X1 * X3) := by
        linear_combination
          (B ^ 2 * ((i : ℝ) + 2) ^ 2 * ((i : ℝ) + 3) * X3) * h0
          + (B ^ 2 * ((i : ℝ) + 2) ^ 2 * (p.natDegree : ℝ) * P0) * h2

/-- **Newton's inequality for real-rooted polynomials**, at every position. -/
theorem newtonAt_all : ∀ (i : ℕ) {p : ℝ[X]}, RealRooted p → i + 2 ≤ p.natDegree →
    NewtonAt p i := by
  intro i
  induction i with
  | zero => intro p hp hi; exact newtonAt_zero hp (by omega)
  | succ i ih =>
      intro p hp hi
      refine newtonAt_succ hp i (by omega) (ih (realRooted_derivative hp) ?_)
      rw [natDegree_derivative_of_realRooted hp]
      omega

theorem realRooted_polyOf {n : ℕ} (v : Fin n → ℝ) : RealRooted (polyOf v) := by
  unfold RealRooted
  have h : polyOf v
      = (Multiset.map (fun a : ℝ => X - C a)
          (Multiset.map (fun i => -v i) (univ : Finset (Fin n)).val)).prod := by
    unfold polyOf
    rw [Multiset.map_map]
    show (Multiset.map (fun i => X + C (v i)) (univ : Finset (Fin n)).val).prod = _
    congr 1
    exact Multiset.map_congr rfl fun i _ => by
      simp only [Function.comp_apply, Polynomial.C_neg, sub_neg_eq_add]
  rw [h, Polynomial.roots_multiset_prod_X_sub_C, Multiset.card_map]
  rw [← h, polyOf_natDegree]
  simp

/-! ## 7.  Newton in vector form -/

theorem esymF_zero {n : ℕ} (v : Fin n → ℝ) : esymF 0 v = 1 := by
  unfold esymF
  rw [Finset.powersetCard_zero]
  simp

theorem newton_esymF {n : ℕ} (v : Fin n → ℝ) (j : ℕ) (hj1 : 1 ≤ j) (hj2 : j + 1 ≤ n) :
    esymF (j - 1) v * esymF (j + 1) v * ((n.choose j : ℕ) : ℝ) ^ 2
      ≤ (esymF j v) ^ 2 * ((n.choose (j - 1) : ℕ) : ℝ) * ((n.choose (j + 1) : ℕ) : ℝ) := by
  have hdeg := polyOf_natDegree v
  have hN := newtonAt_all (n - j - 1) (realRooted_polyOf v) (by rw [hdeg]; omega)
  unfold NewtonAt at hN
  rw [hdeg] at hN
  have e0 : (polyOf v).coeff (n - j - 1) = esymF (j + 1) v := by
    have h := polyOf_coeff v (show j + 1 ≤ n from hj2)
    rwa [show n - (j + 1) = n - j - 1 by omega] at h
  have e1 : (polyOf v).coeff (n - j - 1 + 1) = esymF j v := by
    have h := polyOf_coeff v (show j ≤ n by omega)
    rwa [show n - j = n - j - 1 + 1 by omega] at h
  have e2 : (polyOf v).coeff (n - j - 1 + 2) = esymF (j - 1) v := by
    have h := polyOf_coeff v (show j - 1 ≤ n by omega)
    rwa [show n - (j - 1) = n - j - 1 + 2 by omega] at h
  have c0 : n.choose (n - j - 1) = n.choose (j + 1) := by
    rw [show n - j - 1 = n - (j + 1) by omega]; exact Nat.choose_symm hj2
  have c1 : n.choose (n - j - 1 + 1) = n.choose j := by
    rw [show n - j - 1 + 1 = n - j by omega]; exact Nat.choose_symm (by omega)
  have c2 : n.choose (n - j - 1 + 2) = n.choose (j - 1) := by
    rw [show n - j - 1 + 2 = n - (j - 1) by omega]; exact Nat.choose_symm (by omega)
  rw [e0, e1, e2, c0, c1, c2] at hN
  convert hN using 1 <;> ring

/-- The normalised elementary symmetric function `p_j = e_j / C(n,j)`. -/
noncomputable def pnorm {n : ℕ} (v : Fin n → ℝ) (j : ℕ) : ℝ :=
  esymF j v / ((n.choose j : ℕ) : ℝ)

theorem pnorm_nonneg {n : ℕ} {v : Fin n → ℝ} (hv : ∀ i, 0 ≤ v i) (j : ℕ) :
    0 ≤ pnorm v j := by
  unfold pnorm esymF
  exact div_nonneg (Finset.sum_nonneg fun S _ => Finset.prod_nonneg fun i _ => hv i)
    (Nat.cast_nonneg _)

theorem pnorm_zero {n : ℕ} (v : Fin n → ℝ) : pnorm v 0 = 1 := by
  unfold pnorm
  rw [esymF_zero, Nat.choose_zero_right]
  norm_num

theorem pnorm_one {n : ℕ} (v : Fin n → ℝ) (hn : 1 ≤ n) (h : (∑ i, v i) = (n : ℝ)) :
    pnorm v 1 = 1 := by
  have hn0 : (n : ℝ) ≠ 0 := by
    have : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
    linarith
  unfold pnorm
  rw [esymF_one, h, Nat.choose_one_right]
  field_simp

theorem pnorm_newton {n : ℕ} (v : Fin n → ℝ) (j : ℕ) (hj1 : 1 ≤ j) (hj2 : j + 1 ≤ n) :
    pnorm v (j - 1) * pnorm v (j + 1) ≤ (pnorm v j) ^ 2 := by
  have h := newton_esymF v j hj1 hj2
  have c0 : (0:ℝ) < ((n.choose (j - 1) : ℕ) : ℝ) := by
    exact_mod_cast Nat.choose_pos (show j - 1 ≤ n by omega)
  have c1 : (0:ℝ) < ((n.choose j : ℕ) : ℝ) := by
    exact_mod_cast Nat.choose_pos (show j ≤ n by omega)
  have c2 : (0:ℝ) < ((n.choose (j + 1) : ℕ) : ℝ) := by exact_mod_cast Nat.choose_pos hj2
  unfold pnorm
  rw [div_mul_div_comm, div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
  convert h using 1
  ring

/-! ## 8.  Maclaurin, telescoped -/

theorem esymF_succ_eq_zero {n : ℕ} {v : Fin n → ℝ} (hv : ∀ i, 0 ≤ v i) {j : ℕ}
    (hj : esymF j v = 0) : esymF (j + 1) v = 0 := by
  unfold esymF at hj ⊢
  have hnn : ∀ S ∈ Finset.powersetCard j (univ : Finset (Fin n)), (0:ℝ) ≤ ∏ i ∈ S, v i :=
    fun S _ => Finset.prod_nonneg fun i _ => hv i
  have hall := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hj
  refine Finset.sum_eq_zero fun T hT => ?_
  have hTcard : T.card = j + 1 := Finset.mem_powersetCard_univ.mp hT
  obtain ⟨t, ht⟩ : ∃ t, t ∈ T := Finset.card_pos.mp (by omega)
  have hS : T.erase t ∈ Finset.powersetCard j (univ : Finset (Fin n)) := by
    rw [Finset.mem_powersetCard_univ, Finset.card_erase_of_mem ht, hTcard]
    omega
  rw [← Finset.prod_erase_mul T v ht, hall _ hS, zero_mul]

theorem pnorm_eq_zero_succ {n : ℕ} {v : Fin n → ℝ} (hv : ∀ i, 0 ≤ v i) {j : ℕ}
    (hj : pnorm v j = 0) (hjn : j ≤ n) : pnorm v (j + 1) = 0 := by
  have hcpos : (0:ℝ) < ((n.choose j : ℕ) : ℝ) := by exact_mod_cast Nat.choose_pos hjn
  have he : esymF j v = 0 := by
    unfold pnorm at hj
    exact (div_eq_zero_iff.mp hj).resolve_right (ne_of_gt hcpos)
  unfold pnorm
  rw [esymF_succ_eq_zero hv he, zero_div]

/-- **Maclaurin, telescoped**: on the simplex the normalised symmetric functions are
non-increasing from index 1 on.  No fractional powers appear. -/
theorem pnorm_antitone {n : ℕ} {v : Fin n → ℝ} (hv : ∀ i, 0 ≤ v i)
    (h1 : (∑ i, v i) = (n : ℝ)) :
    ∀ j : ℕ, 1 ≤ j → j + 1 ≤ n → pnorm v (j + 1) ≤ pnorm v j := by
  intro j
  induction j with
  | zero => intro h; exact absurd h (by omega)
  | succ j ih =>
      intro _ hjn
      rcases Nat.eq_zero_or_pos j with hj0 | hjpos
      · subst hj0
        have hN := pnorm_newton v 1 (le_refl 1) (by omega)
        rw [show (1:ℕ) - 1 = 0 from rfl, pnorm_zero] at hN
        have h1' : pnorm v 1 = 1 := pnorm_one v (by omega) h1
        rw [h1'] at hN ⊢
        nlinarith [hN]
      · have hprev := ih hjpos (by omega)
        have hN := pnorm_newton v (j + 1) (by omega) (by omega)
        rw [show j + 1 - 1 = j from rfl] at hN
        rcases eq_or_lt_of_le (pnorm_nonneg hv j) with hz | hpos
        · have h1z : pnorm v (j + 1) = 0 := pnorm_eq_zero_succ hv hz.symm (by omega)
          have h2z : pnorm v (j + 1 + 1) = 0 := pnorm_eq_zero_succ hv h1z (by omega)
          rw [h1z, h2z]
        · nlinarith [hN, hprev, pnorm_nonneg hv (j + 1)]

/-- **`p_k ≤ p_2` for `2 ≤ k ≤ n`** — the form Theorem M's hypothesis needs. -/
theorem pnorm_le_two {n : ℕ} {v : Fin n → ℝ} (hv : ∀ i, 0 ≤ v i)
    (h1 : (∑ i, v i) = (n : ℝ)) : ∀ k : ℕ, 2 ≤ k → k ≤ n → pnorm v k ≤ pnorm v 2 := by
  intro k
  induction k with
  | zero => intro h; exact absurd h (by omega)
  | succ k ih =>
      intro hk2 hkn
      rcases Nat.lt_or_ge k 2 with hk | hk
      · have he : k + 1 = 2 := by omega
        rw [he]
      · exact le_trans (pnorm_antitone hv h1 k (by omega) (by omega)) (ih hk (by omega))

end Roots

/-! ## 9.  Axiom audit

**Every declaration in this file depends only on axioms among `propext,
Classical.choice, Quot.sound`.**  `choose_mul_sub` is pure arithmetic and uses only two
of the three; everything else uses all three.  No `native_decide` appears anywhere in
this file. -/

section AxiomAudit

#print axioms esymF_eq_esymm
#print axioms esymF_compl
#print axioms realRooted_mul
#print axioms realRooted_derivative
#print axioms polyOf_ne_zero
#print axioms polyOf_monic
#print axioms polyOf_natDegree
#print axioms polyOf_coeff
#print axioms coeff_derivative_shift
#print axioms choose_mul_sub
#print axioms natDegree_derivative_of_realRooted
#print axioms esymS_one
#print axioms esymS_two
#print axioms esymF_one
#print axioms esymF_two
#print axioms esymF_card
#print axioms newton_index_one
#print axioms exists_vector_of_card
#print axioms exists_root_vector
#print axioms newtonAt_zero
#print axioms newtonAt_succ
#print axioms newtonAt_all
#print axioms realRooted_polyOf
#print axioms esymF_zero
#print axioms newton_esymF
#print axioms pnorm_nonneg
#print axioms pnorm_zero
#print axioms pnorm_one
#print axioms pnorm_newton
#print axioms esymF_succ_eq_zero
#print axioms pnorm_eq_zero_succ
#print axioms pnorm_antitone
#print axioms pnorm_le_two

end AxiomAudit

end NewtonIneq
