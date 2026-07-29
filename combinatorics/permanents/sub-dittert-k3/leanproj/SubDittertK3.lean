/-
# The Cheon–Hwang sub-Dittert conjecture at `k = 3`, for every `n ≥ 4`

Source of the statement `[R]`: G.-S. Cheon and S.-G. Hwang, *Maximization of a
matrix function related to the Dittert conjecture*, Linear Algebra Appl. **165**
(1992) 153–165.  For `A` in `K_n = { A ≥ 0 : ∑ a_ij = n }`, with row sums `r` and
column sums `c`,

    E_k(r) + E_k(c) − P_k(A)  ≤  2 − k!/n^k,        1 ≤ k ≤ n,

where `E_k(v) = e_k(v)/C(n,k)` and `P_k(A) = σ_k(A)/C(n,k)²`, and `σ_k(A)` is the
sum of the permanents of all `k × k` submatrices of `A`.  This file is about
`k = 3`.

## What is proved here, and what is not

**Proved, kernel-checked, no `sorry`:**

* the definitions, and their validation at the equality case — `Phi_uniform`
  shows `Φ_k(J_n/n) = 2 − k!/n^k` *for every `k ≤ n`*, so the functional as
  defined here is tight at `J_n/n` exactly where the conjecture says it is;
* `sigmaK_three_eq_permanent`, and a concrete `σ_3 = 450` against a hand value;
* `esym_three_closed` and `sigmaK_three_closed` — **closed forms for `e_3` and
  `σ_3`, for every `n`, derived from the definitions**.  `σ_3` is defined as a sum
  over pairs of 3-subsets of subpermanents; the closed form is a polynomial in the
  entries, the row sums and the column sums.  The bridge is `RookSum.lean`: the
  bijection between `k`-subsets paired with permutations of `Fin k` and injections
  `Fin k → Fin n`, then a three-index inclusion–exclusion sieve.  Nothing about
  these is specific to `k = 3` except the sieve;
* `obj_eq_objPoly` — the objective `(2 − 6/n³) − Φ₃(A)` equals the explicit
  polynomial `objPoly n A`, for every `n ≥ 3`;
* `certPositive_of_four_le` — the **ten** rational functions of `n` whose
  positivity is, by the closed-form block-diagonalisation, equivalent to positive
  definiteness of the two Gram matrices of the certificate.  Positive for every
  *real* `n ≥ 4`.  These were decided outside Lean by Sturm sequences; inside
  Lean they are proved outright, because after the substitution `n = m + 4` all
  twenty polynomials involved turn out to have non-negative coefficients and a
  positive constant term;
* `subDittert_k3_of_certificate` — the deduction of the bound from the existence
  of the certificate, by the Positivstellensatz bridge of `Certificate.lean`;
* `certificate_exists` — proved from `certificate_identity` and `Hm_posSemidef`;
* `G0_posSemidef` and `Hm_posSemidef` — **both Gram families are explicit, and both
  are proved positive semidefinite for every `n ≥ 4`**, with no spectral theorem.
  `G0`'s quadratic form splits into four manifestly non-negative pieces (§3c);
  `Hm p`'s splits, after the centring of §3h, into the four isotypic blocks, each
  bounded by the pivot theorems of §3d through the completions of squares of §3f;
* `certificate_identity` — **the Positivstellensatz identity itself**, for every
  `n ≥ 4` and every `A ∈ K_n`.  Both sums over corners are expanded in the ten
  global invariants of the centred coordinates (§3i);
* `subDittert_k3` and `subDittert_k3_of_certificate` — the conjecture at `k = 3`
  for every `n ≥ 4`.

**Nothing is left open.**  There is no `sorry` in this file and no
`native_decide` anywhere; every theorem listed in the audit of §5 depends on
exactly `propext, Classical.choice, Quot.sound`.

The chain is: the combinatorial half (`esym_three_closed`, `sigmaK_three_closed`,
`obj_eq_objPoly`) removes every permanent, subpermanent, elementary symmetric
function and sum over `Finset.powersetCard` from the frontier; what is left is real
algebra — a cubic identity in `n²` variables with coefficients rational in `n`, plus
semidefiniteness of two structured `n² × n²` matrices — and that is what §3c–§3i
prove.

Cross-checks outside Lean, none of which the proof depends on but all of which had
to agree before the transcriptions were written: `sub-dittert/verify_general.py`
re-derives the objective from the 1992 definition and uses none of the closed
forms — exact `ℚ` at `n = 4, 5, 6, 7` and `n = 12`, and `F_p` at three primes near
`2²⁰` at `n = 25`, with positive definiteness decided by exact rational `LDLᵀ` on the
full `n² × n²` matrices.  `verify_modp.py` supplies the negative controls;
`leanproj/verify_objPoly.py` checks `objPoly` against that verifier;
`leanproj/verify_H_identity.py` checks the local-to-global dictionary of §3i against
the assembled Gram and derives the identity symbolically in `n` by full coefficient
comparison; `leanproj/verify_H_decomp.py` checks the centring of §3h and the seven
bridge constants of §3e.  Every one of those scripts carries a mutation control.
-/

import PermanentExpansion
import Certificate
import RookSum

namespace SubDittertK3

open Finset Matrix

noncomputable section

variable {n : ℕ}

/-! ## 1.  The statement

Everything is over `ℝ`.  `K_n` is a set rather than a subtype so that it can be
handed straight to `Certificate.nonneg_of_certificate`, whose `S` is a `Set`. -/

/-- `K_n = { A ≥ 0 : ∑_{i,j} a_ij = n }`, the domain of the conjecture. -/
def Kn (n : ℕ) : Set (Matrix (Fin n) (Fin n) ℝ) :=
  {A | (∀ i j, 0 ≤ A i j) ∧ ∑ i, ∑ j, A i j = (n : ℝ)}

/-- The vector of row sums. -/
def rowSum (A : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) : ℝ := ∑ j, A i j

/-- The vector of column sums. -/
def colSum (A : Matrix (Fin n) (Fin n) ℝ) (j : Fin n) : ℝ := ∑ i, A i j

/-- `e_k(v)`, the `k`-th elementary symmetric function of a vector. -/
def esym (k : ℕ) (v : Fin n → ℝ) : ℝ :=
  ∑ S ∈ Finset.powersetCard k (univ : Finset (Fin n)), ∏ i ∈ S, v i

/-- The permanent of the `k × k` submatrix of `A` on rows `S` and columns `T`,
both listed in increasing order; junk value `0` unless both have `k` elements.
The `dite` keeps the definition total, so that `sigmaK` is an ordinary sum over
`Finset.powersetCard` with no dependent bookkeeping. -/
def subPerm (k : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (S T : Finset (Fin n)) : ℝ :=
  if hS : S.card = k then
    if hT : T.card = k then
      (A.submatrix (⇑(S.orderEmbOfFin hS)) (⇑(T.orderEmbOfFin hT))).permanent
    else 0
  else 0

/-- `σ_k(A)`, the sum of the permanents of all `C(n,k)²` submatrices of size `k`. -/
def sigmaK (k : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ∑ S ∈ Finset.powersetCard k (univ : Finset (Fin n)),
    ∑ T ∈ Finset.powersetCard k (univ : Finset (Fin n)), subPerm k A S T

/-- `E_k(v) = e_k(v) / C(n,k)`. -/
def E (k : ℕ) (v : Fin n → ℝ) : ℝ := esym k v / (n.choose k : ℝ)

/-- `P_k(A) = σ_k(A) / C(n,k)²`. -/
def P (k : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) : ℝ := sigmaK k A / (n.choose k : ℝ) ^ 2

/-- The Cheon–Hwang functional `Φ_k(A) = E_k(r) + E_k(c) − P_k(A)`. -/
def Phi (k : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  E k (rowSum A) + E k (colSum A) - P k A

/-! ## 2.  Validation of the definitions

A definition that is wrong at the boundary proves nothing and compiles anyway.
The check that matters is the conjectured equality case: `Φ_k` must equal
`2 − k!/n^k` at `J_n/n`, and it must do so for the right structural reasons —
`e_k` of the all-ones vector, and `C(n,k)²` constant subpermanents. -/

/-- The permanent of a constant `k × k` matrix is `k! c^k`. -/
theorem permanent_const (k : ℕ) (c : ℝ) :
    Matrix.permanent (Matrix.of fun _ _ : Fin k => c) = (Nat.factorial k : ℝ) * c ^ k := by
  simp only [Matrix.permanent, Matrix.of_apply, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, Finset.sum_const, Fintype.card_perm, nsmul_eq_mul]

/-- `J_n / n`, the conjectured maximiser. -/
def uniform (n : ℕ) : Matrix (Fin n) (Fin n) ℝ := fun _ _ => 1 / (n : ℝ)

theorem uniform_mem_Kn (hn : n ≠ 0) : uniform n ∈ Kn n := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  refine ⟨fun i j => by show (0 : ℝ) ≤ 1 / (n : ℝ); positivity, ?_⟩
  simp only [uniform, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

theorem rowSum_uniform (hn : n ≠ 0) (i : Fin n) : rowSum (uniform n) i = 1 := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  simp only [rowSum, uniform, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

theorem colSum_uniform (hn : n ≠ 0) (j : Fin n) : colSum (uniform n) j = 1 := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  simp only [colSum, uniform, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-- `e_k` of the all-ones vector counts the `k`-subsets. -/
theorem esym_one (k : ℕ) : esym k (fun _ : Fin n => (1 : ℝ)) = (n.choose k : ℝ) := by
  simp [esym, Finset.card_powersetCard, Finset.card_univ]

/-- Every `k × k` submatrix of `J_n/n` is constant, so has permanent `k!/n^k`. -/
theorem subPerm_uniform {k : ℕ} {S T : Finset (Fin n)} (hS : S.card = k) (hT : T.card = k) :
    subPerm k (uniform n) S T = (Nat.factorial k : ℝ) * (1 / (n : ℝ)) ^ k := by
  unfold subPerm
  rw [dif_pos hS, dif_pos hT]
  exact permanent_const k (1 / (n : ℝ))

theorem sigmaK_uniform (k : ℕ) :
    sigmaK k (uniform n) =
      (n.choose k : ℝ) ^ 2 * ((Nat.factorial k : ℝ) * (1 / (n : ℝ)) ^ k) := by
  unfold sigmaK
  rw [Finset.sum_congr rfl fun S hS => Finset.sum_congr rfl fun T hT =>
    subPerm_uniform (Finset.mem_powersetCard.mp hS).2 (Finset.mem_powersetCard.mp hT).2]
  simp only [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  ring

/-- A product along the increasing enumeration of `S` is a product over `S`. -/
theorem prod_orderEmbOfFin {k : ℕ} {S : Finset (Fin n)} (hS : S.card = k) (x : Fin n → ℝ) :
    ∏ i : Fin k, x (S.orderEmbOfFin hS i) = ∏ i ∈ S, x i := by
  rw [← Finset.prod_coe_sort S x]
  exact Fintype.prod_equiv (S.orderIsoOfFin hS).toEquiv _ _ fun _ => rfl

theorem subPerm_rankOne {k : ℕ} {S T : Finset (Fin n)} (hS : S.card = k) (hT : T.card = k)
    (x y : Fin n → ℝ) :
    subPerm k (Matrix.of fun i j => x i * y j) S T
      = (Nat.factorial k : ℝ) * (∏ i ∈ S, x i) * (∏ j ∈ T, y j) := by
  unfold subPerm
  rw [dif_pos hS, dif_pos hT]
  simp only [Matrix.permanent, Matrix.submatrix_apply, Matrix.of_apply, Finset.prod_mul_distrib]
  rw [Finset.sum_congr rfl fun σ _ =>
    congrArg (· * ∏ i : Fin k, y (T.orderEmbOfFin hT i))
      (Equiv.prod_comp σ fun i => x (S.orderEmbOfFin hS i))]
  rw [prod_orderEmbOfFin, prod_orderEmbOfFin, Finset.sum_const, Finset.card_univ,
    Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul, mul_assoc]

/-- **The row/column validation.**  For the rank-one matrix `a_ij = x_i y_j`,

    σ_k(A) = k! · e_k(x) · e_k(y).

This is the check that `subPerm` takes its rows from `S` and its columns from
`T`.  A definition that read both indices off the same subset would give
`k! · C(n,k) · ∑_S (∏_S x)(∏_S y)` instead, and the two differ for every
non-constant `x`, `y` — so unlike a symmetric test matrix this cannot pass by
accident. -/
theorem sigmaK_rankOne (k : ℕ) (x y : Fin n → ℝ) :
    sigmaK k (Matrix.of fun i j => x i * y j)
      = (Nat.factorial k : ℝ) * esym k x * esym k y := by
  unfold sigmaK esym
  rw [Finset.sum_congr rfl fun S hS => Finset.sum_congr rfl fun T hT =>
    subPerm_rankOne (Finset.mem_powersetCard.mp hS).2 (Finset.mem_powersetCard.mp hT).2 x y]
  simp only [← Finset.mul_sum, ← Finset.sum_mul, mul_assoc]

/-- **The boundary validation.**  At `J_n/n` the functional equals `2 − k!/n^k`
exactly, for every `k ≤ n`.  This is `γ(n,k) = k!/n^k` of the 1992 paper, so the
definitions above meet the conjectured bound with equality at the conjectured
maximiser — the one place a mis-transcribed definition would show up. -/
theorem Phi_uniform (k : ℕ) (hkn : k ≤ n) (hn : n ≠ 0) :
    Phi k (uniform n) = 2 - (Nat.factorial k : ℝ) / (n : ℝ) ^ k := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hc : (n.choose k : ℝ) ≠ 0 := by
    exact_mod_cast Nat.choose_pos hkn |>.ne'
  have hr : rowSum (uniform n) = fun _ => (1 : ℝ) := funext (rowSum_uniform hn)
  have hcol : colSum (uniform n) = fun _ => (1 : ℝ) := funext (colSum_uniform hn)
  simp only [Phi, E, P, hr, hcol, esym_one, sigmaK_uniform]
  field_simp
  ring

/-! ### The equality case at `n = 3, 4, 5`

Instances of `Phi_uniform` at `k = 3`, with `3! = 6`. -/

theorem Phi_uniform_three : Phi 3 (uniform 3) = 2 - 6 / (3 : ℝ) ^ 3 := by
  rw [Phi_uniform 3 (by norm_num) (by norm_num)]; norm_num [Nat.factorial]

theorem Phi_uniform_four : Phi 3 (uniform 4) = 2 - 6 / (4 : ℝ) ^ 3 := by
  rw [Phi_uniform 3 (by norm_num) (by norm_num)]; norm_num [Nat.factorial]

theorem Phi_uniform_five : Phi 3 (uniform 5) = 2 - 6 / (5 : ℝ) ^ 3 := by
  rw [Phi_uniform 3 (by norm_num) (by norm_num)]; norm_num [Nat.factorial]

/-! ### `σ_3` against a hand value

At `n = 3` there is exactly one `3`-subset, so `σ_3` collapses to the permanent.
That pins down the `powersetCard`/`orderEmbOfFin` plumbing, which the constant
matrix of `Phi_uniform` cannot see. -/

theorem sigmaK_three_eq_permanent (A : Matrix (Fin 3) (Fin 3) ℝ) :
    sigmaK 3 A = A.permanent := by
  have hcard : (univ : Finset (Fin 3)).card = 3 := by simp
  have hset : Finset.powersetCard 3 (univ : Finset (Fin 3)) = {univ} := by
    rw [← hcard]; exact Finset.powersetCard_self _
  have hid : (id : Fin 3 → Fin 3) = ⇑((univ : Finset (Fin 3)).orderEmbOfFin hcard) :=
    Finset.orderEmbOfFin_unique hcard (fun x => mem_univ x) strictMono_id
  unfold sigmaK
  rw [hset]
  simp only [Finset.sum_singleton]
  unfold subPerm
  rw [dif_pos hcard, dif_pos hcard, ← hid, Matrix.submatrix_id_id]

/-- A test matrix with no symmetry, so that a wrong row/column pairing shows up. -/
def M3 : Matrix (Fin 3) (Fin 3) ℝ := !![1, 2, 3; 4, 5, 6; 7, 8, 9]

/-- Hand value: `σ_3(M3) = per M3
= 1·5·9 + 1·6·8 + 2·4·9 + 2·6·7 + 3·4·8 + 3·5·7 = 45 + 48 + 72 + 84 + 96 + 105 = 450`. -/
theorem sigmaK_three_M3 : sigmaK 3 M3 = 450 := by
  rw [sigmaK_three_eq_permanent]
  simp only [Matrix.permanent_succ_column_zero, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Matrix.submatrix_apply, Matrix.permanent_isEmpty]
  norm_num [M3, Fin.succAbove, Fin.lt_def, Matrix.vecHead, Matrix.vecTail,
    Fin.castSucc, Fin.castAdd, Fin.castLE, Fin.succ, Matrix.cons_val_fin_one]

/-! ## 2b.  Closed forms for `e_3` and `sigma_3`

Both are defined above as sums over subsets.  `RookSum` turns each into a polynomial
in the entries, the row sums and the column sums — for every `n`, from the
definitions, with no `sorry` and no closed form assumed.  The two bridge lemmas are
`rfl`: they stop compiling the moment a definition here drifts from its counterpart
there, which is what makes the reuse safe. -/

theorem sigmaK_eq_sigP (k : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) :
    sigmaK k A = RookSum.sigP k A := rfl

theorem esym_eq_sum (k : ℕ) (v : Fin n → ℝ) :
    esym k v = ∑ S ∈ Finset.powersetCard k (univ : Finset (Fin n)), ∏ i ∈ S, v i := rfl

/-- **`e_3` in closed form.**  Newton's identity at `k = 3`. -/
theorem esym_three_closed (v : Fin n → ℝ) :
    6 * esym 3 v = (∑ i, v i) ^ 3 - 3 * (∑ i, v i) * (∑ i, v i ^ 2) + 2 * ∑ i, v i ^ 3 := by
  rw [esym_eq_sum]
  exact RookSum.esym_three_closed v

/-- **`sigma_3` in closed form.**  Proved from the subpermanent definition through the
subset/injection bijection and the three-index sieve. -/
theorem sigmaK_three_closed (A : Matrix (Fin n) (Fin n) ℝ) :
    6 * sigmaK 3 A
      = (∑ i, ∑ j, A i j) ^ 3
        - 3 * (∑ i, ∑ j, A i j) * ((∑ i, (∑ j, A i j) ^ 2) + (∑ j, (∑ i, A i j) ^ 2))
        + 3 * (∑ i, ∑ j, A i j ^ 2) * (∑ i, ∑ j, A i j)
        + 6 * (∑ i, ∑ j, A i j * (∑ l, A i l) * (∑ l, A l j))
        + 2 * (∑ i, (∑ j, A i j) ^ 3) + 2 * (∑ j, (∑ i, A i j) ^ 3)
        - 6 * (∑ i, ∑ j, A i j ^ 2 * (∑ l, A i l))
        - 6 * (∑ i, ∑ j, A i j ^ 2 * (∑ l, A l j))
        + 4 * (∑ i, ∑ j, A i j ^ 3) := by
  rw [sigmaK_eq_sigP]
  exact RookSum.sigma_three_closed A

/-! ## 3.  The ten positivity theorems

Generated from `sub-dittert/results/general_k3_certificate.txt` via `sturm.py`'s
`quantities_rf_from`; the polynomials are transcribed mechanically, not
re-derived.  Outside Lean each was decided by a Sturm sequence on `n = m + 4`.
Inside Lean every one of the twenty polynomials turns out to have non-negative
coefficients in `m` with a positive constant term, so the Sturm machinery is not
needed and the proofs are `ring` plus `linarith` — Strategy A throughout, no
sums-of-squares fallback used.

**Normalisation, stated exactly.**  Each numerator and each denominator is
separately cleared to primitive integer coefficients, and the pair is
sign-flipped together when the denominator is negative on `n ≥ 4`.  Both
operations scale by a positive rational, so `theta1 n` and the rest are each a
constant *positive* rational multiple of the corresponding certificate quantity
— the multiples are `1` except `minorA2` and `blockB` (`1/2`) and `minorC2`
(`4`) — and positivity of one is positivity of the other.  Nothing here depends
on the multiple; it is recorded so that the definitions can be compared against
`sturm.py`'s output without surprise. -/

/-- `n ≥ 4` in the form the positivity proofs consume. -/
private theorem exists_shift {n : ℝ} (hn : 4 ≤ n) : ∃ m : ℝ, 0 ≤ m ∧ n = m + 4 :=
  ⟨n - 4, by linarith, by ring⟩

/-! ### `G0.theta0` -/

/-- Numerator of `G0.theta0`, cleared to integer coefficients. -/
def theta0Num (_n : ℝ) : ℝ := 1

theorem theta0Num_pos {n : ℝ} (_hn : 4 ≤ n) : 0 < theta0Num n := by
  norm_num [theta0Num]

/-- Denominator of `G0.theta0` (sign-normalised positive on `n ≥ 4`). -/
def theta0Den (n : ℝ) : ℝ := n

theorem theta0Den_pos {n : ℝ} (hn : 4 ≤ n) : 0 < theta0Den n := by
  obtain ⟨m, hm, rfl⟩ := exists_shift hn
  have h : theta0Den (m + 4) = m + 4 := by
    unfold theta0Den; ring
  rw [h]
  linarith [hm]

/-- theta_0 eigenvalue of the sigma_0 Gram (multiplicity 1). -/
noncomputable def theta0 (n : ℝ) : ℝ := theta0Num n / theta0Den n

theorem theta0_pos {n : ℝ} (hn : 4 ≤ n) : 0 < theta0 n :=
  div_pos (theta0Num_pos hn) (theta0Den_pos hn)

/-! ### `G0.theta1` -/

/-- Numerator of `G0.theta1`, cleared to integer coefficients. -/
def theta1Num (n : ℝ) : ℝ := n ^ 6 - 51 * n ^ 4 + 205 * n ^ 3 - 294 * n ^ 2 + 176 * n - 40

theorem theta1Num_pos {n : ℝ} (hn : 4 ≤ n) : 0 < theta1Num n := by
  obtain ⟨m, hm, rfl⟩ := exists_shift hn
  have h : theta1Num (m + 4) = m ^ 6 + 24 * m ^ 5 + 189 * m ^ 4 + 669 * m ^ 3 + 1110 * m ^ 2 + 752 * m + 120 := by
    unfold theta1Num; ring
  rw [h]
  linarith [hm, pow_nonneg hm 2, pow_nonneg hm 3, pow_nonneg hm 4, pow_nonneg hm 5, pow_nonneg hm 6]

/-- Denominator of `G0.theta1` (sign-normalised positive on `n ≥ 4`). -/
def theta1Den (n : ℝ) : ℝ := n ^ 8 - 6 * n ^ 7 + 13 * n ^ 6 - 12 * n ^ 5 + 4 * n ^ 4

theorem theta1Den_pos {n : ℝ} (hn : 4 ≤ n) : 0 < theta1Den n := by
  obtain ⟨m, hm, rfl⟩ := exists_shift hn
  have h : theta1Den (m + 4) = m ^ 8 + 26 * m ^ 7 + 293 * m ^ 6 + 1868 * m ^ 5 + 7364 * m ^ 4 + 18368 * m ^ 3 + 28288 * m ^ 2 + 24576 * m + 9216 := by
    unfold theta1Den; ring
  rw [h]
  linarith [hm, pow_nonneg hm 2, pow_nonneg hm 3, pow_nonneg hm 4, pow_nonneg hm 5, pow_nonneg hm 6, pow_nonneg hm 7, pow_nonneg hm 8]

/-- theta_1 eigenvalue of the sigma_0 Gram (multiplicity 2(n-1)). -/
noncomputable def theta1 (n : ℝ) : ℝ := theta1Num n / theta1Den n

theorem theta1_pos {n : ℝ} (hn : 4 ≤ n) : 0 < theta1 n :=
  div_pos (theta1Num_pos hn) (theta1Den_pos hn)

/-! ### `G0.theta2` -/

/-- Numerator of `G0.theta2`, cleared to integer coefficients. -/
def theta2Num (n : ℝ) : ℝ := n ^ 4 + 40 * n ^ 2 - 84 * n + 40

theorem theta2Num_pos {n : ℝ} (hn : 4 ≤ n) : 0 < theta2Num n := by
  obtain ⟨m, hm, rfl⟩ := exists_shift hn
  have h : theta2Num (m + 4) = m ^ 4 + 16 * m ^ 3 + 136 * m ^ 2 + 492 * m + 600 := by
    unfold theta2Num; ring
  rw [h]
  linarith [hm, pow_nonneg hm 2, pow_nonneg hm 3, pow_nonneg hm 4]

/-- Denominator of `G0.theta2` (sign-normalised positive on `n ≥ 4`). -/
def theta2Den (n : ℝ) : ℝ := n ^ 9 - 5 * n ^ 8 + 9 * n ^ 7 - 7 * n ^ 6 + 2 * n ^ 5

theorem theta2Den_pos {n : ℝ} (hn : 4 ≤ n) : 0 < theta2Den n := by
  obtain ⟨m, hm, rfl⟩ := exists_shift hn
  have h : theta2Den (m + 4) = m ^ 9 + 31 * m ^ 8 + 425 * m ^ 7 + 3381 * m ^ 6 + 17194 * m ^ 5 + 57944 * m ^ 4 + 129344 * m ^ 3 + 184320 * m ^ 2 + 152064 * m + 55296 := by
    unfold theta2Den; ring
  rw [h]
  linarith [hm, pow_nonneg hm 2, pow_nonneg hm 3, pow_nonneg hm 4, pow_nonneg hm 5, pow_nonneg hm 6, pow_nonneg hm 7, pow_nonneg hm 8, pow_nonneg hm 9]

/-- theta_2 eigenvalue of the sigma_0 Gram (multiplicity (n-1)^2). -/
noncomputable def theta2 (n : ℝ) : ℝ := theta2Num n / theta2Den n

theorem theta2_pos {n : ℝ} (hn : 4 ≤ n) : 0 < theta2 n :=
  div_pos (theta2Num_pos hn) (theta2Den_pos hn)

/-! ### `H.A minor1` -/

/-- Numerator of `H.A minor1`, cleared to integer coefficients. -/
def minorA1Num (_n : ℝ) : ℝ := 1

theorem minorA1Num_pos {n : ℝ} (_hn : 4 ≤ n) : 0 < minorA1Num n := by
  norm_num [minorA1Num]

/-- Denominator of `H.A minor1` (sign-normalised positive on `n ≥ 4`). -/
def minorA1Den (n : ℝ) : ℝ := n ^ 3

theorem minorA1Den_pos {n : ℝ} (hn : 4 ≤ n) : 0 < minorA1Den n := by
  obtain ⟨m, hm, rfl⟩ := exists_shift hn
  have h : minorA1Den (m + 4) = m ^ 3 + 12 * m ^ 2 + 48 * m + 64 := by
    unfold minorA1Den; ring
  rw [h]
  linarith [hm, pow_nonneg hm 2, pow_nonneg hm 3]

/-- leading 1x1 minor of the 3x3 trivial block A of the sigma_11 Gram. -/
noncomputable def minorA1 (n : ℝ) : ℝ := minorA1Num n / minorA1Den n

theorem minorA1_pos {n : ℝ} (hn : 4 ≤ n) : 0 < minorA1 n :=
  div_pos (minorA1Num_pos hn) (minorA1Den_pos hn)

/-! ### `H.A minor2` -/

/-- Numerator of `H.A minor2`, cleared to integer coefficients. -/
def minorA2Num (n : ℝ) : ℝ := n ^ 5 - 2 * n ^ 4 + 16 * n ^ 3 + 16 * n ^ 2 - 52 * n + 20

theorem minorA2Num_pos {n : ℝ} (hn : 4 ≤ n) : 0 < minorA2Num n := by
  obtain ⟨m, hm, rfl⟩ := exists_shift hn
  have h : minorA2Num (m + 4) = m ^ 5 + 18 * m ^ 4 + 144 * m ^ 3 + 656 * m ^ 2 + 1612 * m + 1604 := by
    unfold minorA2Num; ring
  rw [h]
  linarith [hm, pow_nonneg hm 2, pow_nonneg hm 3, pow_nonneg hm 4, pow_nonneg hm 5]

/-- Denominator of `H.A minor2` (sign-normalised positive on `n ≥ 4`). -/
def minorA2Den (n : ℝ) : ℝ := n ^ 9

theorem minorA2Den_pos {n : ℝ} (hn : 4 ≤ n) : 0 < minorA2Den n := by
  obtain ⟨m, hm, rfl⟩ := exists_shift hn
  have h : minorA2Den (m + 4) = m ^ 9 + 36 * m ^ 8 + 576 * m ^ 7 + 5376 * m ^ 6 + 32256 * m ^ 5 + 129024 * m ^ 4 + 344064 * m ^ 3 + 589824 * m ^ 2 + 589824 * m + 262144 := by
    unfold minorA2Den; ring
  rw [h]
  linarith [hm, pow_nonneg hm 2, pow_nonneg hm 3, pow_nonneg hm 4, pow_nonneg hm 5, pow_nonneg hm 6, pow_nonneg hm 7, pow_nonneg hm 8, pow_nonneg hm 9]

/-- leading 2x2 minor of the 3x3 trivial block A. -/
noncomputable def minorA2 (n : ℝ) : ℝ := minorA2Num n / minorA2Den n

theorem minorA2_pos {n : ℝ} (hn : 4 ≤ n) : 0 < minorA2 n :=
  div_pos (minorA2Num_pos hn) (minorA2Den_pos hn)

/-! ### `H.A minor3` -/

/-- Numerator of `H.A minor3`, cleared to integer coefficients. -/
def minorA3Num (n : ℝ) : ℝ := 31 * n ^ 13 - 279 * n ^ 12 + 503 * n ^ 11 + 4281 * n ^ 10 - 27723 * n ^ 9 + 64281 * n ^ 8 - 30296 * n ^ 7 - 172276 * n ^ 6 + 423952 * n ^ 5 - 428368 * n ^ 4 + 161856 * n ^ 3 + 59072 * n ^ 2 - 74240 * n + 19200

theorem minorA3Num_pos {n : ℝ} (hn : 4 ≤ n) : 0 < minorA3Num n := by
  obtain ⟨m, hm, rfl⟩ := exists_shift hn
  have h : minorA3Num (m + 4) = 31 * m ^ 13 + 1333 * m ^ 12 + 25799 * m ^ 11 + 299213 * m ^ 10 + 2332077 * m ^ 9 + 12959901 * m ^ 8 + 53049352 * m ^ 7 + 162479148 * m ^ 6 + 373166512 * m ^ 5 + 635322160 * m ^ 4 + 779043136 * m ^ 3 + 650495936 * m ^ 2 + 330645504 * m + 77000448 := by
    unfold minorA3Num; ring
  rw [h]
  linarith [hm, pow_nonneg hm 2, pow_nonneg hm 3, pow_nonneg hm 4, pow_nonneg hm 5, pow_nonneg hm 6, pow_nonneg hm 7, pow_nonneg hm 8, pow_nonneg hm 9, pow_nonneg hm 10, pow_nonneg hm 11, pow_nonneg hm 12, pow_nonneg hm 13]

/-- Denominator of `H.A minor3` (sign-normalised positive on `n ≥ 4`). -/
def minorA3Den (n : ℝ) : ℝ := n ^ 18 - 9 * n ^ 17 + 32 * n ^ 16 - 56 * n ^ 15 + 48 * n ^ 14 - 16 * n ^ 13

theorem minorA3Den_pos {n : ℝ} (hn : 4 ≤ n) : 0 < minorA3Den n := by
  obtain ⟨m, hm, rfl⟩ := exists_shift hn
  have h : minorA3Den (m + 4) = m ^ 18 + 63 * m ^ 17 + 1868 * m ^ 16 + 34632 * m ^ 15 + 449808 * m ^ 14 + 4345584 * m ^ 13 + 32357312 * m ^ 12 + 189835776 * m ^ 11 + 889427968 * m ^ 10 + 3352121344 * m ^ 9 + 10184638464 * m ^ 8 + 24880873472 * m ^ 7 + 48500834304 * m ^ 6 + 74399612928 * m ^ 5 + 87816142848 * m ^ 4 + 76940312576 * m ^ 3 + 47110422528 * m ^ 2 + 17985175552 * m + 3221225472 := by
    unfold minorA3Den; ring
  rw [h]
  linarith [hm, pow_nonneg hm 2, pow_nonneg hm 3, pow_nonneg hm 4, pow_nonneg hm 5, pow_nonneg hm 6, pow_nonneg hm 7, pow_nonneg hm 8, pow_nonneg hm 9, pow_nonneg hm 10, pow_nonneg hm 11, pow_nonneg hm 12, pow_nonneg hm 13, pow_nonneg hm 14, pow_nonneg hm 15, pow_nonneg hm 16, pow_nonneg hm 17, pow_nonneg hm 18]

/-- determinant of the 3x3 trivial block A. -/
noncomputable def minorA3 (n : ℝ) : ℝ := minorA3Num n / minorA3Den n

theorem minorA3_pos {n : ℝ} (hn : 4 ≤ n) : 0 < minorA3 n :=
  div_pos (minorA3Num_pos hn) (minorA3Den_pos hn)

/-! ### `H.B` -/

/-- Numerator of `H.B`, cleared to integer coefficients. -/
def blockBNum (n : ℝ) : ℝ := n ^ 5 - 2 * n ^ 4 + 8 * n ^ 2 + 12 * n - 20

theorem blockBNum_pos {n : ℝ} (hn : 4 ≤ n) : 0 < blockBNum n := by
  obtain ⟨m, hm, rfl⟩ := exists_shift hn
  have h : blockBNum (m + 4) = m ^ 5 + 18 * m ^ 4 + 128 * m ^ 3 + 456 * m ^ 2 + 844 * m + 668 := by
    unfold blockBNum; ring
  rw [h]
  linarith [hm, pow_nonneg hm 2, pow_nonneg hm 3, pow_nonneg hm 4, pow_nonneg hm 5]

/-- Denominator of `H.B` (sign-normalised positive on `n ≥ 4`). -/
def blockBDen (n : ℝ) : ℝ := n ^ 6

theorem blockBDen_pos {n : ℝ} (hn : 4 ≤ n) : 0 < blockBDen n := by
  obtain ⟨m, hm, rfl⟩ := exists_shift hn
  have h : blockBDen (m + 4) = m ^ 6 + 24 * m ^ 5 + 240 * m ^ 4 + 1280 * m ^ 3 + 3840 * m ^ 2 + 6144 * m + 4096 := by
    unfold blockBDen; ring
  rw [h]
  linarith [hm, pow_nonneg hm 2, pow_nonneg hm 3, pow_nonneg hm 4, pow_nonneg hm 5, pow_nonneg hm 6]

/-- the 1x1 sign block B of the sigma_11 Gram. -/
noncomputable def blockB (n : ℝ) : ℝ := blockBNum n / blockBDen n

theorem blockB_pos {n : ℝ} (hn : 4 ≤ n) : 0 < blockB n :=
  div_pos (blockBNum_pos hn) (blockBDen_pos hn)

/-! ### `H.C minor1` -/

/-- Numerator of `H.C minor1`, cleared to integer coefficients. -/
def minorC1Num (n : ℝ) : ℝ := 3 * n ^ 5 - 6 * n ^ 4 + 12 * n ^ 3 - 4 * n ^ 2 - 44 * n + 40

theorem minorC1Num_pos {n : ℝ} (hn : 4 ≤ n) : 0 < minorC1Num n := by
  obtain ⟨m, hm, rfl⟩ := exists_shift hn
  have h : minorC1Num (m + 4) = 3 * m ^ 5 + 54 * m ^ 4 + 396 * m ^ 3 + 1484 * m ^ 2 + 2804 * m + 2104 := by
    unfold minorC1Num; ring
  rw [h]
  linarith [hm, pow_nonneg hm 2, pow_nonneg hm 3, pow_nonneg hm 4, pow_nonneg hm 5]

/-- Denominator of `H.C minor1` (sign-normalised positive on `n ≥ 4`). -/
def minorC1Den (n : ℝ) : ℝ := n ^ 8 - 3 * n ^ 7 + 2 * n ^ 6

theorem minorC1Den_pos {n : ℝ} (hn : 4 ≤ n) : 0 < minorC1Den n := by
  obtain ⟨m, hm, rfl⟩ := exists_shift hn
  have h : minorC1Den (m + 4) = m ^ 8 + 29 * m ^ 7 + 366 * m ^ 6 + 2624 * m ^ 5 + 11680 * m ^ 4 + 33024 * m ^ 3 + 57856 * m ^ 2 + 57344 * m + 24576 := by
    unfold minorC1Den; ring
  rw [h]
  linarith [hm, pow_nonneg hm 2, pow_nonneg hm 3, pow_nonneg hm 4, pow_nonneg hm 5, pow_nonneg hm 6, pow_nonneg hm 7, pow_nonneg hm 8]

/-- leading 1x1 minor of the 2x2 induced block C. -/
noncomputable def minorC1 (n : ℝ) : ℝ := minorC1Num n / minorC1Den n

theorem minorC1_pos {n : ℝ} (hn : 4 ≤ n) : 0 < minorC1 n :=
  div_pos (minorC1Num_pos hn) (minorC1Den_pos hn)

/-! ### `H.C minor2` -/

/-- Numerator of `H.C minor2`, cleared to integer coefficients. -/
def minorC2Num (n : ℝ) : ℝ := 95 * n ^ 12 - 743 * n ^ 11 + 1535 * n ^ 10 + 2451 * n ^ 9 - 17746 * n ^ 8 + 33092 * n ^ 7 - 10820 * n ^ 6 - 60308 * n ^ 5 + 107640 * n ^ 4 - 58736 * n ^ 3 - 24608 * n ^ 2 + 40960 * n - 12800

theorem minorC2Num_pos {n : ℝ} (hn : 4 ≤ n) : 0 < minorC2Num n := by
  obtain ⟨m, hm, rfl⟩ := exists_shift hn
  have h : minorC2Num (m + 4) = 95 * m ^ 12 + 3817 * m ^ 11 + 69163 * m ^ 10 + 747611 * m ^ 9 + 5368010 * m ^ 8 + 26942916 * m ^ 7 + 96706220 * m ^ 6 + 249075020 * m ^ 5 + 453643304 * m ^ 4 + 562699664 * m ^ 3 + 440429984 * m ^ 2 + 184782336 * m + 26204160 := by
    unfold minorC2Num; ring
  rw [h]
  linarith [hm, pow_nonneg hm 2, pow_nonneg hm 3, pow_nonneg hm 4, pow_nonneg hm 5, pow_nonneg hm 6, pow_nonneg hm 7, pow_nonneg hm 8, pow_nonneg hm 9, pow_nonneg hm 10, pow_nonneg hm 11, pow_nonneg hm 12]

/-- Denominator of `H.C minor2` (sign-normalised positive on `n ≥ 4`). -/
def minorC2Den (n : ℝ) : ℝ := n ^ 18 - 9 * n ^ 17 + 33 * n ^ 16 - 63 * n ^ 15 + 66 * n ^ 14 - 36 * n ^ 13 + 8 * n ^ 12

theorem minorC2Den_pos {n : ℝ} (hn : 4 ≤ n) : 0 < minorC2Den n := by
  obtain ⟨m, hm, rfl⟩ := exists_shift hn
  have h : minorC2Den (m + 4) = m ^ 18 + 63 * m ^ 17 + 1869 * m ^ 16 + 34689 * m ^ 15 + 451326 * m ^ 14 + 4370652 * m ^ 13 + 32644568 * m ^ 12 + 192257280 * m ^ 11 + 904958208 * m ^ 10 + 3429403648 * m ^ 9 + 10486130688 * m ^ 8 + 25805783040 * m ^ 7 + 50724077568 * m ^ 6 + 78541750272 * m ^ 5 + 93678206976 * m ^ 4 + 83030441984 * m ^ 3 + 51489275904 * m ^ 2 + 19931332608 * m + 3623878656 := by
    unfold minorC2Den; ring
  rw [h]
  linarith [hm, pow_nonneg hm 2, pow_nonneg hm 3, pow_nonneg hm 4, pow_nonneg hm 5, pow_nonneg hm 6, pow_nonneg hm 7, pow_nonneg hm 8, pow_nonneg hm 9, pow_nonneg hm 10, pow_nonneg hm 11, pow_nonneg hm 12, pow_nonneg hm 13, pow_nonneg hm 14, pow_nonneg hm 15, pow_nonneg hm 16, pow_nonneg hm 17, pow_nonneg hm 18]

/-- determinant of the 2x2 induced block C. -/
noncomputable def minorC2 (n : ℝ) : ℝ := minorC2Num n / minorC2Den n

theorem minorC2_pos {n : ℝ} (hn : 4 ≤ n) : 0 < minorC2 n :=
  div_pos (minorC2Num_pos hn) (minorC2Den_pos hn)

/-! ### `H.D` -/

/-- Numerator of `H.D`, cleared to integer coefficients. -/
def blockDNum (n : ℝ) : ℝ := n ^ 4 + 40 * n ^ 2 - 84 * n + 40

theorem blockDNum_pos {n : ℝ} (hn : 4 ≤ n) : 0 < blockDNum n := by
  obtain ⟨m, hm, rfl⟩ := exists_shift hn
  have h : blockDNum (m + 4) = m ^ 4 + 16 * m ^ 3 + 136 * m ^ 2 + 492 * m + 600 := by
    unfold blockDNum; ring
  rw [h]
  linarith [hm, pow_nonneg hm 2, pow_nonneg hm 3, pow_nonneg hm 4]

/-- Denominator of `H.D` (sign-normalised positive on `n ≥ 4`). -/
def blockDDen (n : ℝ) : ℝ := n ^ 10 - 5 * n ^ 9 + 9 * n ^ 8 - 7 * n ^ 7 + 2 * n ^ 6

theorem blockDDen_pos {n : ℝ} (hn : 4 ≤ n) : 0 < blockDDen n := by
  obtain ⟨m, hm, rfl⟩ := exists_shift hn
  have h : blockDDen (m + 4) = m ^ 10 + 35 * m ^ 9 + 549 * m ^ 8 + 5081 * m ^ 7 + 30718 * m ^ 6 + 126720 * m ^ 5 + 361120 * m ^ 4 + 701696 * m ^ 3 + 889344 * m ^ 2 + 663552 * m + 221184 := by
    unfold blockDDen; ring
  rw [h]
  linarith [hm, pow_nonneg hm 2, pow_nonneg hm 3, pow_nonneg hm 4, pow_nonneg hm 5, pow_nonneg hm 6, pow_nonneg hm 7, pow_nonneg hm 8, pow_nonneg hm 9, pow_nonneg hm 10]

/-- the 1x1 (V'|V') block D, multiplicity (n-2)^2. -/
noncomputable def blockD (n : ℝ) : ℝ := blockDNum n / blockDDen n

theorem blockD_pos {n : ℝ} (hn : 4 ≤ n) : 0 < blockD n :=
  div_pos (blockDNum_pos hn) (blockDDen_pos hn)

/-! ## The ten positivity facts, packaged -/

/-- **The certificate's positivity hypothesis.**  Positive definiteness of the two
Gram matrices is, by the closed-form block-diagonalisation of `blocks.py`,
*exactly* the positivity of these ten rational functions of `n`: the three
eigenvalues of the `sigma_0` Gram in the Bose-Mesner algebra of the rook's graph,
and the leading principal minors of the four blocks of the `sigma_11` Gram. -/
def CertPositive (n : ℝ) : Prop :=
  0 < theta0 n ∧
  0 < theta1 n ∧
  0 < theta2 n ∧
  0 < minorA1 n ∧
  0 < minorA2 n ∧
  0 < minorA3 n ∧
  0 < blockB n ∧
  0 < minorC1 n ∧
  0 < minorC2 n ∧
  0 < blockD n

/-- **All ten hold for every real `n ≥ 4`.**  Kernel-checked; no certificate is
carried here.  Each of the twenty polynomials involved has non-negative
coefficients after the substitution `n = m + 4`, with positive constant term. -/
theorem certPositive_of_four_le {n : ℝ} (hn : 4 ≤ n) : CertPositive n :=
  ⟨theta0_pos hn, theta1_pos hn, theta2_pos hn, minorA1_pos hn, minorA2_pos hn, minorA3_pos hn, blockB_pos hn, minorC1_pos hn, minorC2_pos hn, blockD_pos hn⟩

/-! ## 3c.  The `sigma_0` Gram, explicitly, and its positive semidefiniteness

The Gram of `sigma_0` lies in the Bose–Mesner algebra of the rook's graph: its entry
depends only on whether two cells coincide, share a line, or share neither.  Writing
`[same line] = [same row] + [same column] − [same cell]` turns that into

    G0 u v  =  c0Total  +  c0Line · ([u.1 = v.1] + [u.2 = v.2])  +  theta2 · [u = v],

and then the quadratic form is `c0Total · S² + c0Line · (∑ R² + ∑ C²) + theta2 · ∑ b²`
with no case analysis left — a positive combination of four manifestly non-negative
quantities.  So positive semidefiniteness needs no spectral theory, only two further
positivity facts of exactly the shape of the ten above.  (The eigenvalues are
`theta0`, `theta1`, `theta2` with multiplicities `1`, `2(n−1)`, `(n−1)²`; that is where
these coefficients come from, but the proof below does not need it.)

**Transcription, checked before this was written.**  `c0Total`, `c0Line` and `theta2`
are `sigma0[2]`, `sigma0[1] − sigma0[2]` and `sigma0[0] − 2·sigma0[1] + sigma0[2]` of
`sub-dittert/results/general_k3_certificate.txt`.  That the three orbit values so
recovered are the certificate's own was checked symbolically as an identity of
rational functions of `n`, and the assembled Gram of `verify_general.py` was compared
entrywise against the display above at `n = 4, 5, 6` with zero mismatches.  A wrong
transcription here would make `certificate_exists_poly` FALSE rather than merely
unproved, which is why it was checked outside Lean first. -/

/-- Numerator of the `S²` coefficient (`= sigma0[2]`), cleared to integer coefficients. -/
def c0TotalNum (n : ℝ) : ℝ :=
  n ^ 9 - 9 * n ^ 8 + 21 * n ^ 7 + 77 * n ^ 6 - 495 * n ^ 5 + 992 * n ^ 4 - 900 * n ^ 3
    + 268 * n ^ 2 + 128 * n - 80

theorem c0TotalNum_pos {n : ℝ} (hn : 4 ≤ n) : 0 < c0TotalNum n := by
  obtain ⟨m, hm, rfl⟩ := exists_shift hn
  have h : c0TotalNum (m + 4) = m ^ 9 + 27 * m ^ 8 + 309 * m ^ 7 + 2009 * m ^ 6
      + 8409 * m ^ 5 + 24356 * m ^ 4 + 50460 * m ^ 3 + 72796 * m ^ 2 + 64800 * m + 25968 := by
    unfold c0TotalNum; ring
  rw [h]
  linarith [hm, pow_nonneg hm 2, pow_nonneg hm 3, pow_nonneg hm 4, pow_nonneg hm 5, pow_nonneg hm 6, pow_nonneg hm 7, pow_nonneg hm 8, pow_nonneg hm 9]

/-- Denominator of the `S²` coefficient (sign-normalised positive on `n ≥ 4`). -/
def c0TotalDen (n : ℝ) : ℝ :=
  n ^ 12 - 7 * n ^ 11 + 19 * n ^ 10 - 25 * n ^ 9 + 16 * n ^ 8 - 4 * n ^ 7

theorem c0TotalDen_pos {n : ℝ} (hn : 4 ≤ n) : 0 < c0TotalDen n := by
  obtain ⟨m, hm, rfl⟩ := exists_shift hn
  have h : c0TotalDen (m + 4) = m ^ 12 + 41 * m ^ 11 + 767 * m ^ 10 + 8655 * m ^ 9
      + 65596 * m ^ 8 + 351676 * m ^ 7 + 1367184 * m ^ 6 + 3882176 * m ^ 5
      + 7988480 * m ^ 4 + 11613184 * m ^ 3 + 11317248 * m ^ 2 + 6635520 * m + 1769472 := by
    unfold c0TotalDen; ring
  rw [h]
  linarith [hm, pow_nonneg hm 2, pow_nonneg hm 3, pow_nonneg hm 4, pow_nonneg hm 5, pow_nonneg hm 6, pow_nonneg hm 7, pow_nonneg hm 8, pow_nonneg hm 9, pow_nonneg hm 10, pow_nonneg hm 11, pow_nonneg hm 12]

/-- The coefficient of `S²` in the `sigma_0` quadratic form. -/
noncomputable def c0Total (n : ℝ) : ℝ := c0TotalNum n / c0TotalDen n

theorem c0Total_pos {n : ℝ} (hn : 4 ≤ n) : 0 < c0Total n :=
  div_pos (c0TotalNum_pos hn) (c0TotalDen_pos hn)

/-- Numerator of the line coefficient (`= sigma0[1] − sigma0[2]`), cleared. -/
def c0LineNum (n : ℝ) : ℝ :=
  n ^ 8 - n ^ 7 - 51 * n ^ 6 + 255 * n ^ 5 - 497 * n ^ 4 + 430 * n ^ 3 - 52 * n ^ 2
    - 168 * n + 80

theorem c0LineNum_pos {n : ℝ} (hn : 4 ≤ n) : 0 < c0LineNum n := by
  obtain ⟨m, hm, rfl⟩ := exists_shift hn
  have h : c0LineNum (m + 4) = m ^ 8 + 31 * m ^ 7 + 369 * m ^ 6 + 2279 * m ^ 5
      + 8043 * m ^ 4 + 16382 * m ^ 3 + 17940 * m ^ 2 + 8280 * m + 240 := by
    unfold c0LineNum; ring
  rw [h]
  linarith [hm, pow_nonneg hm 2, pow_nonneg hm 3, pow_nonneg hm 4, pow_nonneg hm 5, pow_nonneg hm 6, pow_nonneg hm 7, pow_nonneg hm 8]

/-- Denominator of the line coefficient (sign-normalised positive on `n ≥ 4`). -/
def c0LineDen (n : ℝ) : ℝ :=
  n ^ 11 - 7 * n ^ 10 + 19 * n ^ 9 - 25 * n ^ 8 + 16 * n ^ 7 - 4 * n ^ 6

theorem c0LineDen_pos {n : ℝ} (hn : 4 ≤ n) : 0 < c0LineDen n := by
  obtain ⟨m, hm, rfl⟩ := exists_shift hn
  have h : c0LineDen (m + 4) = m ^ 11 + 37 * m ^ 10 + 619 * m ^ 9 + 6179 * m ^ 8
      + 40880 * m ^ 7 + 188156 * m ^ 6 + 614560 * m ^ 5 + 1423936 * m ^ 4
      + 2292736 * m ^ 3 + 2442240 * m ^ 2 + 1548288 * m + 442368 := by
    unfold c0LineDen; ring
  rw [h]
  linarith [hm, pow_nonneg hm 2, pow_nonneg hm 3, pow_nonneg hm 4, pow_nonneg hm 5, pow_nonneg hm 6, pow_nonneg hm 7, pow_nonneg hm 8, pow_nonneg hm 9, pow_nonneg hm 10, pow_nonneg hm 11]

/-- The coefficient of `∑ R² + ∑ C²` in the `sigma_0` quadratic form. -/
noncomputable def c0Line (n : ℝ) : ℝ := c0LineNum n / c0LineDen n

theorem c0Line_pos {n : ℝ} (hn : 4 ≤ n) : 0 < c0Line n :=
  div_pos (c0LineNum_pos hn) (c0LineDen_pos hn)

/-- **The `sigma_0` Gram matrix of the certificate, explicitly.** -/
noncomputable def G0 (n : ℕ) : Matrix (Fin n × Fin n) (Fin n × Fin n) ℝ := fun u v =>
  c0Total (n : ℝ)
    + c0Line (n : ℝ) * ((if u.1 = v.1 then 1 else 0) + (if u.2 = v.2 then 1 else 0))
    + theta2 (n : ℝ) * (if u = v then 1 else 0)

theorem G0_symm (n : ℕ) (u v : Fin n × Fin n) : G0 n u v = G0 n v u := by
  unfold G0
  rw [if_congr (eq_comm (a := u.1) (b := v.1)) rfl rfl,
    if_congr (eq_comm (a := u.2) (b := v.2)) rfl rfl,
    if_congr (eq_comm (a := u) (b := v)) rfl rfl]

/-- Summing an indicator of "same row" against `b` twice gives the row power sum. -/
private theorem sum_row_ind (n : ℕ) (b : Fin n × Fin n → ℝ) :
    (∑ u : Fin n × Fin n, ∑ v : Fin n × Fin n,
        (if u.1 = v.1 then (1 : ℝ) else 0) * (b u * b v))
      = ∑ i, (∑ j, b (i, j)) ^ 2 := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sq, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Fintype.sum_prod_type]
  have hcollapse : ∀ k : Fin n,
      (∑ l, (if (i, j).1 = ((k, l) : Fin n × Fin n).1 then (1 : ℝ) else 0)
          * (b (i, j) * b (k, l)))
        = (if i = k then (1 : ℝ) else 0) * ∑ l, b (i, j) * b (k, l) := by
    intro k
    rw [Finset.mul_sum]
  rw [Finset.sum_congr rfl fun k (_ : k ∈ univ) => hcollapse k]
  simp only [boole_mul]
  rw [Finset.sum_ite_eq univ i (fun k => ∑ l, b (i, j) * b (k, l))]
  simp

/-- The same for columns. -/
private theorem sum_col_ind (n : ℕ) (b : Fin n × Fin n → ℝ) :
    (∑ u : Fin n × Fin n, ∑ v : Fin n × Fin n,
        (if u.2 = v.2 then (1 : ℝ) else 0) * (b u * b v))
      = ∑ j, (∑ i, b (i, j)) ^ 2 := by
  have inner : ∀ u : Fin n × Fin n,
      (∑ v : Fin n × Fin n, (if u.2 = v.2 then (1 : ℝ) else 0) * (b u * b v))
        = b u * ∑ k, b (k, u.2) := by
    intro u
    rw [Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [boole_mul]
    rw [Finset.sum_ite_eq univ u.2 (fun l => b u * b (k, l))]
    simp
  rw [Finset.sum_congr rfl fun u (_ : u ∈ univ) => inner u, Fintype.sum_prod_type,
    Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  dsimp only
  rw [sq, ← Finset.sum_mul]

/-- **The `sigma_0` quadratic form, in row, column and entry power sums.** -/
theorem quadForm_G0 (n : ℕ) (b : Fin n × Fin n → ℝ) :
    Certificate.quadForm (G0 n) b
      = c0Total (n : ℝ) * (∑ u, b u) ^ 2
        + c0Line (n : ℝ) * ((∑ i, (∑ j, b (i, j)) ^ 2) + (∑ j, (∑ i, b (i, j)) ^ 2))
        + theta2 (n : ℝ) * ∑ u, b u ^ 2 := by
  have hq : Certificate.quadForm (G0 n) b
      = ∑ u : Fin n × Fin n, ∑ v : Fin n × Fin n, G0 n u v * (b u * b v) := by
    unfold Certificate.quadForm Matrix.mulVec dotProduct
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun v _ => by ring
  have hS : (∑ u : Fin n × Fin n, ∑ v : Fin n × Fin n, b u * b v) = (∑ u, b u) ^ 2 := by
    rw [sq, Finset.sum_mul_sum]
  have hE : (∑ u : Fin n × Fin n, ∑ v : Fin n × Fin n,
      (if u = v then (1 : ℝ) else 0) * (b u * b v)) = ∑ u, b u ^ 2 := by
    refine Finset.sum_congr rfl fun u _ => ?_
    simp only [boole_mul]
    rw [Finset.sum_ite_eq univ u (fun v => b u * b v)]
    simp [sq]
  have expand : (∑ u : Fin n × Fin n, ∑ v : Fin n × Fin n, G0 n u v * (b u * b v))
      = c0Total (n : ℝ) * (∑ u : Fin n × Fin n, ∑ v : Fin n × Fin n, b u * b v)
        + c0Line (n : ℝ) * (∑ u : Fin n × Fin n, ∑ v : Fin n × Fin n,
            (if u.1 = v.1 then (1 : ℝ) else 0) * (b u * b v))
        + c0Line (n : ℝ) * (∑ u : Fin n × Fin n, ∑ v : Fin n × Fin n,
            (if u.2 = v.2 then (1 : ℝ) else 0) * (b u * b v))
        + theta2 (n : ℝ) * (∑ u : Fin n × Fin n, ∑ v : Fin n × Fin n,
            (if u = v then (1 : ℝ) else 0) * (b u * b v)) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun u _ =>
      Finset.sum_congr rfl fun v _ => by unfold G0; ring
  rw [hq, expand, hS, sum_row_ind, sum_col_ind, hE]
  ring

theorem quadForm_G0_nonneg (n : ℕ) (hn : 4 ≤ n) (b : Fin n × Fin n → ℝ) :
    0 ≤ Certificate.quadForm (G0 n) b := by
  have hn' : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  rw [quadForm_G0]
  have h1 := (c0Total_pos hn').le
  have h2 := (c0Line_pos hn').le
  have h3 := (theta2_pos hn').le
  have s1 : (0 : ℝ) ≤ (∑ u, b u) ^ 2 := sq_nonneg _
  have s2 : (0 : ℝ) ≤ ∑ i, (∑ j, b (i, j)) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have s3 : (0 : ℝ) ≤ ∑ j, (∑ i, b (i, j)) ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  have s4 : (0 : ℝ) ≤ ∑ u, b u ^ 2 := Finset.sum_nonneg fun u _ => sq_nonneg _
  have p1 := mul_nonneg h1 s1
  have p2 := mul_nonneg h2 (add_nonneg s2 s3)
  have p3 := mul_nonneg h3 s4
  linarith

/-- **`G0` is positive semidefinite for every `n ≥ 4`.**  Kernel-checked; this
discharges the `sigma_0` half of the certificate's semidefiniteness outright. -/
theorem G0_posSemidef (n : ℕ) (hn : 4 ≤ n) : (G0 n).PosSemidef := by
  constructor
  · ext u v
    simpa [Matrix.conjTranspose_apply] using (G0_symm n v u)
  · intro x
    simpa [Certificate.quadForm] using quadForm_G0_nonneg n hn x

/-! ## 3d.  The seven pivots of the `sigma_11` block decomposition

`quadForm (H p)` decomposes, in the isotypic coordinates of the point stabiliser, as

    Q_A(P, s, τ)  +  Q_B · d²  +  Σ_i Q_C(ê_i, r̂_i)  +  Σ_j Q_C(f̂_j, ĉ_j)  +  Q_D · Σ w²,

where `P` is the value at the corner, `s` and `d` the sum and difference of the row
and column tails, `τ` the body total, the hatted quantities the centred residuals, and
`w` the doubly centred body.  Positive semidefiniteness of `H p` therefore reduces to
positivity of the seven `LDLᵀ` pivots below: the three leading principal minors of the
`3 × 3` block `A`, the `1 × 1` block `B`, the two leading principal minors of the
`2 × 2` block `C`, and the `1 × 1` block `D`.

**All seven are proved positive here, for every real `n ≥ 4`** — so all the
definiteness arithmetic of the `sigma_11` half is done, and what remains for
`(H p).PosSemidef` is the change of coordinates alone.

⚠ These are NOT the `minorA*`, `blockB`, `minorC*`, `blockD` of §3: those are the
same seven quantities in `blocks.py`'s normalisation, and these are in the
coordinates the decomposition above actually uses.  The two sets differ by positive
but `n`-DEPENDENT factors (measured: 1, 1/18, 1/2916, 1/18, 1, 1/36, 1 at `n = 4`, and
not constant in `n`), so neither set can be substituted for the other.  Both are
positive on `n ≥ 4`, which is all either is for.

The coefficients below were emitted by sympy from the 11 orbit values, never typed;
the orbit values themselves, and the expansion of `quadForm (H p)` that produces these
pivots, are checked against the real Gram in `verify_H_blocks.py`. -/

/-- Numerator of the first leading minor of the 3x3 trivial block A of the sigma_11 form, cleared to integer coefficients. -/
def pivotA1Num (n : ℝ) : ℝ := 1

theorem pivotA1Num_pos {n : ℝ} (hn : 4 ≤ n) : 0 < pivotA1Num n := by
  obtain ⟨m, hm, rfl⟩ := exists_shift hn
  have h : pivotA1Num (m + 4) = 1 := by
    unfold pivotA1Num; ring
  rw [h]
  linarith [hm]

/-- Denominator of the first leading minor of the 3x3 trivial block A of the sigma_11 form (sign-normalised positive on `n ≥ 4`). -/
def pivotA1Den (n : ℝ) : ℝ := n ^ 3

theorem pivotA1Den_pos {n : ℝ} (hn : 4 ≤ n) : 0 < pivotA1Den n := by
  obtain ⟨m, hm, rfl⟩ := exists_shift hn
  have h : pivotA1Den (m + 4) = m ^ 3 + 12 * m ^ 2 + 48 * m + 64 := by
    unfold pivotA1Den; ring
  rw [h]
  linarith [hm, pow_nonneg hm 2, pow_nonneg hm 3]

/-- first leading minor of the 3x3 trivial block A of the sigma_11 form. -/
noncomputable def pivotA1 (n : ℝ) : ℝ := pivotA1Num n / pivotA1Den n

theorem pivotA1_pos {n : ℝ} (hn : 4 ≤ n) : 0 < pivotA1 n :=
  div_pos (pivotA1Num_pos hn) (pivotA1Den_pos hn)

/-- Numerator of the second leading minor of A, cleared to integer coefficients. -/
def pivotA2Num (n : ℝ) : ℝ := n ^ 5 - 2 * n ^ 4 + 16 * n ^ 3 + 16 * n ^ 2 - 52 * n + 20

theorem pivotA2Num_pos {n : ℝ} (hn : 4 ≤ n) : 0 < pivotA2Num n := by
  obtain ⟨m, hm, rfl⟩ := exists_shift hn
  have h : pivotA2Num (m + 4) = m ^ 5 + 18 * m ^ 4 + 144 * m ^ 3 + 656 * m ^ 2 + 1612 * m + 1604 := by
    unfold pivotA2Num; ring
  rw [h]
  linarith [hm, pow_nonneg hm 2, pow_nonneg hm 3, pow_nonneg hm 4, pow_nonneg hm 5]

/-- Denominator of the second leading minor of A (sign-normalised positive on `n ≥ 4`). -/
def pivotA2Den (n : ℝ) : ℝ := n ^ 11 - 2 * n ^ 10 + n ^ 9

theorem pivotA2Den_pos {n : ℝ} (hn : 4 ≤ n) : 0 < pivotA2Den n := by
  obtain ⟨m, hm, rfl⟩ := exists_shift hn
  have h : pivotA2Den (m + 4) = m ^ 11 + 42 * m ^ 10 + 801 * m ^ 9 + 9156 * m ^ 8 + 69696 * m ^ 7 + 370944 * m ^ 6 + 1408512 * m ^ 5 + 3815424 * m ^ 4 + 7225344 * m ^ 3 + 9109504 * m ^ 2 + 6881280 * m + 2359296 := by
    unfold pivotA2Den; ring
  rw [h]
  linarith [hm, pow_nonneg hm 2, pow_nonneg hm 3, pow_nonneg hm 4, pow_nonneg hm 5, pow_nonneg hm 6, pow_nonneg hm 7, pow_nonneg hm 8, pow_nonneg hm 9, pow_nonneg hm 10, pow_nonneg hm 11]

/-- second leading minor of A. -/
noncomputable def pivotA2 (n : ℝ) : ℝ := pivotA2Num n / pivotA2Den n

theorem pivotA2_pos {n : ℝ} (hn : 4 ≤ n) : 0 < pivotA2 n :=
  div_pos (pivotA2Num_pos hn) (pivotA2Den_pos hn)

/-- Numerator of the determinant of A, cleared to integer coefficients. -/
def pivotA3Num (n : ℝ) : ℝ := 31 * n ^ 13 - 279 * n ^ 12 + 503 * n ^ 11 + 4281 * n ^ 10 - 27723 * n ^ 9 + 64281 * n ^ 8 - 30296 * n ^ 7 - 172276 * n ^ 6 + 423952 * n ^ 5 - 428368 * n ^ 4 + 161856 * n ^ 3 + 59072 * n ^ 2 - 74240 * n + 19200

theorem pivotA3Num_pos {n : ℝ} (hn : 4 ≤ n) : 0 < pivotA3Num n := by
  obtain ⟨m, hm, rfl⟩ := exists_shift hn
  have h : pivotA3Num (m + 4) = 31 * m ^ 13 + 1333 * m ^ 12 + 25799 * m ^ 11 + 299213 * m ^ 10 + 2332077 * m ^ 9 + 12959901 * m ^ 8 + 53049352 * m ^ 7 + 162479148 * m ^ 6 + 373166512 * m ^ 5 + 635322160 * m ^ 4 + 779043136 * m ^ 3 + 650495936 * m ^ 2 + 330645504 * m + 77000448 := by
    unfold pivotA3Num; ring
  rw [h]
  linarith [hm, pow_nonneg hm 2, pow_nonneg hm 3, pow_nonneg hm 4, pow_nonneg hm 5, pow_nonneg hm 6, pow_nonneg hm 7, pow_nonneg hm 8, pow_nonneg hm 9, pow_nonneg hm 10, pow_nonneg hm 11, pow_nonneg hm 12, pow_nonneg hm 13]

/-- Denominator of the determinant of A (sign-normalised positive on `n ≥ 4`). -/
def pivotA3Den (n : ℝ) : ℝ := n ^ 24 - 15 * n ^ 23 + 101 * n ^ 22 - 403 * n ^ 21 + 1059 * n ^ 20 - 1925 * n ^ 19 + 2471 * n ^ 18 - 2241 * n ^ 17 + 1408 * n ^ 16 - 584 * n ^ 15 + 144 * n ^ 14 - 16 * n ^ 13

theorem pivotA3Den_pos {n : ℝ} (hn : 4 ≤ n) : 0 < pivotA3Den n := by
  obtain ⟨m, hm, rfl⟩ := exists_shift hn
  have h : pivotA3Den (m + 4) = m ^ 24 + 81 * m ^ 23 + 3137 * m ^ 22 + 77301 * m ^ 21 + 1360599 * m ^ 20 + 18204171 * m ^ 19 + 192365387 * m ^ 18 + 1646664903 * m ^ 17 + 11619696364 * m ^ 16 + 68423554360 * m ^ 15 + 339084822960 * m ^ 14 + 1422027209456 * m ^ 13 + 5062452298176 * m ^ 12 + 15314041010688 * m ^ 11 + 39320415123456 * m ^ 10 + 85415189762048 * m ^ 9 + 156092434956288 * m ^ 8 + 237921535000576 * m ^ 7 + 298762987634688 * m ^ 6 + 303681342799872 * m ^ 5 + 243582967480320 * m ^ 4 + 148367933964288 * m ^ 3 + 64479672926208 * m ^ 2 + 17807739715584 * m + 2348273369088 := by
    unfold pivotA3Den; ring
  rw [h]
  linarith [hm, pow_nonneg hm 2, pow_nonneg hm 3, pow_nonneg hm 4, pow_nonneg hm 5, pow_nonneg hm 6, pow_nonneg hm 7, pow_nonneg hm 8, pow_nonneg hm 9, pow_nonneg hm 10, pow_nonneg hm 11, pow_nonneg hm 12, pow_nonneg hm 13, pow_nonneg hm 14, pow_nonneg hm 15, pow_nonneg hm 16, pow_nonneg hm 17, pow_nonneg hm 18, pow_nonneg hm 19, pow_nonneg hm 20, pow_nonneg hm 21, pow_nonneg hm 22, pow_nonneg hm 23, pow_nonneg hm 24]

/-- determinant of A. -/
noncomputable def pivotA3 (n : ℝ) : ℝ := pivotA3Num n / pivotA3Den n

theorem pivotA3_pos {n : ℝ} (hn : 4 ≤ n) : 0 < pivotA3 n :=
  div_pos (pivotA3Num_pos hn) (pivotA3Den_pos hn)

/-- Numerator of the the 1x1 sign block B (the row-minus-column direction), cleared to integer coefficients. -/
def pivotBNum (n : ℝ) : ℝ := n ^ 5 - 2 * n ^ 4 + 8 * n ^ 2 + 12 * n - 20

theorem pivotBNum_pos {n : ℝ} (hn : 4 ≤ n) : 0 < pivotBNum n := by
  obtain ⟨m, hm, rfl⟩ := exists_shift hn
  have h : pivotBNum (m + 4) = m ^ 5 + 18 * m ^ 4 + 128 * m ^ 3 + 456 * m ^ 2 + 844 * m + 668 := by
    unfold pivotBNum; ring
  rw [h]
  linarith [hm, pow_nonneg hm 2, pow_nonneg hm 3, pow_nonneg hm 4, pow_nonneg hm 5]

/-- Denominator of the the 1x1 sign block B (the row-minus-column direction) (sign-normalised positive on `n ≥ 4`). -/
def pivotBDen (n : ℝ) : ℝ := n ^ 8 - 2 * n ^ 7 + n ^ 6

theorem pivotBDen_pos {n : ℝ} (hn : 4 ≤ n) : 0 < pivotBDen n := by
  obtain ⟨m, hm, rfl⟩ := exists_shift hn
  have h : pivotBDen (m + 4) = m ^ 8 + 30 * m ^ 7 + 393 * m ^ 6 + 2936 * m ^ 5 + 13680 * m ^ 4 + 40704 * m ^ 3 + 75520 * m ^ 2 + 79872 * m + 36864 := by
    unfold pivotBDen; ring
  rw [h]
  linarith [hm, pow_nonneg hm 2, pow_nonneg hm 3, pow_nonneg hm 4, pow_nonneg hm 5, pow_nonneg hm 6, pow_nonneg hm 7, pow_nonneg hm 8]

/-- the 1x1 sign block B (the row-minus-column direction). -/
noncomputable def pivotB (n : ℝ) : ℝ := pivotBNum n / pivotBDen n

theorem pivotB_pos {n : ℝ} (hn : 4 ≤ n) : 0 < pivotB n :=
  div_pos (pivotBNum_pos hn) (pivotBDen_pos hn)

/-- Numerator of the first leading minor of the 2x2 induced block C, cleared to integer coefficients. -/
def pivotC1Num (n : ℝ) : ℝ := 3 * n ^ 5 - 6 * n ^ 4 + 12 * n ^ 3 - 4 * n ^ 2 - 44 * n + 40

theorem pivotC1Num_pos {n : ℝ} (hn : 4 ≤ n) : 0 < pivotC1Num n := by
  obtain ⟨m, hm, rfl⟩ := exists_shift hn
  have h : pivotC1Num (m + 4) = 3 * m ^ 5 + 54 * m ^ 4 + 396 * m ^ 3 + 1484 * m ^ 2 + 2804 * m + 2104 := by
    unfold pivotC1Num; ring
  rw [h]
  linarith [hm, pow_nonneg hm 2, pow_nonneg hm 3, pow_nonneg hm 4, pow_nonneg hm 5]

/-- Denominator of the first leading minor of the 2x2 induced block C (sign-normalised positive on `n ≥ 4`). -/
def pivotC1Den (n : ℝ) : ℝ := n ^ 8 - 3 * n ^ 7 + 2 * n ^ 6

theorem pivotC1Den_pos {n : ℝ} (hn : 4 ≤ n) : 0 < pivotC1Den n := by
  obtain ⟨m, hm, rfl⟩ := exists_shift hn
  have h : pivotC1Den (m + 4) = m ^ 8 + 29 * m ^ 7 + 366 * m ^ 6 + 2624 * m ^ 5 + 11680 * m ^ 4 + 33024 * m ^ 3 + 57856 * m ^ 2 + 57344 * m + 24576 := by
    unfold pivotC1Den; ring
  rw [h]
  linarith [hm, pow_nonneg hm 2, pow_nonneg hm 3, pow_nonneg hm 4, pow_nonneg hm 5, pow_nonneg hm 6, pow_nonneg hm 7, pow_nonneg hm 8]

/-- first leading minor of the 2x2 induced block C. -/
noncomputable def pivotC1 (n : ℝ) : ℝ := pivotC1Num n / pivotC1Den n

theorem pivotC1_pos {n : ℝ} (hn : 4 ≤ n) : 0 < pivotC1 n :=
  div_pos (pivotC1Num_pos hn) (pivotC1Den_pos hn)

/-- Numerator of the determinant of C, cleared to integer coefficients. -/
def pivotC2Num (n : ℝ) : ℝ := 95 * n ^ 12 - 743 * n ^ 11 + 1535 * n ^ 10 + 2451 * n ^ 9 - 17746 * n ^ 8 + 33092 * n ^ 7 - 10820 * n ^ 6 - 60308 * n ^ 5 + 107640 * n ^ 4 - 58736 * n ^ 3 - 24608 * n ^ 2 + 40960 * n - 12800

theorem pivotC2Num_pos {n : ℝ} (hn : 4 ≤ n) : 0 < pivotC2Num n := by
  obtain ⟨m, hm, rfl⟩ := exists_shift hn
  have h : pivotC2Num (m + 4) = 95 * m ^ 12 + 3817 * m ^ 11 + 69163 * m ^ 10 + 747611 * m ^ 9 + 5368010 * m ^ 8 + 26942916 * m ^ 7 + 96706220 * m ^ 6 + 249075020 * m ^ 5 + 453643304 * m ^ 4 + 562699664 * m ^ 3 + 440429984 * m ^ 2 + 184782336 * m + 26204160 := by
    unfold pivotC2Num; ring
  rw [h]
  linarith [hm, pow_nonneg hm 2, pow_nonneg hm 3, pow_nonneg hm 4, pow_nonneg hm 5, pow_nonneg hm 6, pow_nonneg hm 7, pow_nonneg hm 8, pow_nonneg hm 9, pow_nonneg hm 10, pow_nonneg hm 11, pow_nonneg hm 12]

/-- Denominator of the determinant of C (sign-normalised positive on `n ≥ 4`). -/
def pivotC2Den (n : ℝ) : ℝ := n ^ 20 - 11 * n ^ 19 + 52 * n ^ 18 - 138 * n ^ 17 + 225 * n ^ 16 - 231 * n ^ 15 + 146 * n ^ 14 - 52 * n ^ 13 + 8 * n ^ 12

theorem pivotC2Den_pos {n : ℝ} (hn : 4 ≤ n) : 0 < pivotC2Den n := by
  obtain ⟨m, hm, rfl⟩ := exists_shift hn
  have h : pivotC2Den (m + 4) = m ^ 20 + 69 * m ^ 19 + 2256 * m ^ 18 + 46470 * m ^ 17 + 676281 * m ^ 16 + 7390809 * m ^ 15 + 62930414 * m ^ 14 + 427460556 * m ^ 13 + 2352303000 * m ^ 12 + 10589468416 * m ^ 11 + 39207176448 * m ^ 10 + 119587200000 * m ^ 9 + 299933952000 * m ^ 8 + 615138263040 * m ^ 7 + 1021445406720 * m ^ 6 + 1351975436288 * m ^ 5 + 1392775790592 * m ^ 4 + 1076140965888 * m ^ 3 + 586615357440 * m ^ 2 + 201125265408 * m + 32614907904 := by
    unfold pivotC2Den; ring
  rw [h]
  linarith [hm, pow_nonneg hm 2, pow_nonneg hm 3, pow_nonneg hm 4, pow_nonneg hm 5, pow_nonneg hm 6, pow_nonneg hm 7, pow_nonneg hm 8, pow_nonneg hm 9, pow_nonneg hm 10, pow_nonneg hm 11, pow_nonneg hm 12, pow_nonneg hm 13, pow_nonneg hm 14, pow_nonneg hm 15, pow_nonneg hm 16, pow_nonneg hm 17, pow_nonneg hm 18, pow_nonneg hm 19, pow_nonneg hm 20]

/-- determinant of C. -/
noncomputable def pivotC2 (n : ℝ) : ℝ := pivotC2Num n / pivotC2Den n

theorem pivotC2_pos {n : ℝ} (hn : 4 ≤ n) : 0 < pivotC2 n :=
  div_pos (pivotC2Num_pos hn) (pivotC2Den_pos hn)

/-- Numerator of the the 1x1 block D on the doubly centred body, multiplicity (n-2)^2, cleared to integer coefficients. -/
def pivotDNum (n : ℝ) : ℝ := n ^ 4 + 40 * n ^ 2 - 84 * n + 40

theorem pivotDNum_pos {n : ℝ} (hn : 4 ≤ n) : 0 < pivotDNum n := by
  obtain ⟨m, hm, rfl⟩ := exists_shift hn
  have h : pivotDNum (m + 4) = m ^ 4 + 16 * m ^ 3 + 136 * m ^ 2 + 492 * m + 600 := by
    unfold pivotDNum; ring
  rw [h]
  linarith [hm, pow_nonneg hm 2, pow_nonneg hm 3, pow_nonneg hm 4]

/-- Denominator of the the 1x1 block D on the doubly centred body, multiplicity (n-2)^2 (sign-normalised positive on `n ≥ 4`). -/
def pivotDDen (n : ℝ) : ℝ := n ^ 10 - 5 * n ^ 9 + 9 * n ^ 8 - 7 * n ^ 7 + 2 * n ^ 6

theorem pivotDDen_pos {n : ℝ} (hn : 4 ≤ n) : 0 < pivotDDen n := by
  obtain ⟨m, hm, rfl⟩ := exists_shift hn
  have h : pivotDDen (m + 4) = m ^ 10 + 35 * m ^ 9 + 549 * m ^ 8 + 5081 * m ^ 7 + 30718 * m ^ 6 + 126720 * m ^ 5 + 361120 * m ^ 4 + 701696 * m ^ 3 + 889344 * m ^ 2 + 663552 * m + 221184 := by
    unfold pivotDDen; ring
  rw [h]
  linarith [hm, pow_nonneg hm 2, pow_nonneg hm 3, pow_nonneg hm 4, pow_nonneg hm 5, pow_nonneg hm 6, pow_nonneg hm 7, pow_nonneg hm 8, pow_nonneg hm 9, pow_nonneg hm 10]

/-- the 1x1 block D on the doubly centred body, multiplicity (n-2)^2. -/
noncomputable def pivotD (n : ℝ) : ℝ := pivotDNum n / pivotDDen n

theorem pivotD_pos {n : ℝ} (hn : 4 ≤ n) : 0 < pivotD n :=
  div_pos (pivotDNum_pos hn) (pivotDDen_pos hn)

/-- **The `sigma_11` positivity hypothesis, packaged.**  Exactly the seven pivots that
the isotypic decomposition of `quadForm (H p)` produces. -/
def CertPositiveH (n : ℝ) : Prop :=
  0 < pivotA1 n ∧ 0 < pivotA2 n ∧ 0 < pivotA3 n ∧ 0 < pivotB n ∧
  0 < pivotC1 n ∧ 0 < pivotC2 n ∧ 0 < pivotD n

/-- **All seven hold for every real `n ≥ 4`.**  Kernel-checked; no certificate is
carried here.  As with the ten of §3, every polynomial involved has non-negative
coefficients after the substitution `n = m + 4`, with a positive constant term. -/
theorem certPositiveH_of_four_le {n : ℝ} (hn : 4 ≤ n) : CertPositiveH n :=
  ⟨pivotA1_pos hn, pivotA2_pos hn, pivotA3_pos hn, pivotB_pos hn,
   pivotC1_pos hn, pivotC2_pos hn, pivotD_pos hn⟩

/-! ## 3e.  The eleven orbit values, and the four blocks of the decomposition

The `pivot*` of §3d are proved positive but are stated as bare rational functions of
`n`.  To use them the blocks themselves are needed, so they are written out here from
the eleven orbit values of `sub-dittert/results/general_k3_certificate.txt` and tied
to the pivots by the seven bridge lemmas below.

⚠ **The bridges carry constants.**  `pivotA1 = A11` and `pivotC1 = aq` and
`pivotD = g` exactly, but `pivotA2 = 2·(minor 2 of A)`, `pivotA3 = 4·(det A)`,
`pivotB = 2·Bb` and `pivotC2 = 4·(minor 2 of C)`.  The constants are `1, 2, 4, 2, 1,
4, 1`, independent of `n`, and are checked as identities of rational functions by
`verify_H_decomp.py`.  They are harmless — positivity is equivalent either way — but
a bridge stated without them is FALSE, and the earlier note claiming the `pivot*` were
themselves the minors of this decomposition was wrong on exactly this point. -/

def hh0 (n : ℝ) : ℝ := 1 / n ^ 3
def hh3 (n : ℝ) : ℝ := (5 * n ^ 3 + 16 * n + 40) / n ^ 6
def hh4 (n : ℝ) : ℝ :=
  (2 * n ^ 5 - 9 * n ^ 4 + 14 * n ^ 3 - 4 * n ^ 2 - 44 * n + 40) /
    (n ^ 6 * (n - 1) * (n - 2))
def hh5 (n : ℝ) : ℝ := (n ^ 3 + 8 * n + 20) / n ^ 6
def hh6 (n : ℝ) : ℝ :=
  (10 * n ^ 8 - 68 * n ^ 7 + 178 * n ^ 6 - 181 * n ^ 5 - 136 * n ^ 4 + 624 * n ^ 3
      - 840 * n ^ 2 + 576 * n - 160) / (2 * n ^ 6 * (n - 1) ^ 3 * (n - 2) ^ 2)
def hh7 (n : ℝ) : ℝ :=
  (4 * n ^ 8 - 33 * n ^ 7 + 102 * n ^ 6 - 132 * n ^ 5 - 44 * n ^ 4 + 418 * n ^ 3
      - 688 * n ^ 2 + 536 * n - 160) / (2 * n ^ 6 * (n - 1) ^ 3 * (n - 2) ^ 2)
def hh8 (n : ℝ) : ℝ :=
  (9 * n ^ 8 - 59 * n ^ 7 + 131 * n ^ 6 - 15 * n ^ 5 - 472 * n ^ 4 + 932 * n ^ 3
      - 936 * n ^ 2 + 576 * n - 160) / (n ^ 6 * (n - 1) ^ 3 * (n - 2) ^ 2)
def hh9 (n : ℝ) : ℝ :=
  (6 * n ^ 8 - 42 * n ^ 7 + 98 * n ^ 6 - 13 * n ^ 5 - 352 * n ^ 4 + 678 * n ^ 3
      - 620 * n ^ 2 + 328 * n - 80) / (n ^ 6 * (n - 1) ^ 3 * (n - 2) ^ 2)
def hh10 (n : ℝ) : ℝ :=
  (3 * n ^ 7 - 19 * n ^ 6 + 27 * n ^ 5 + 44 * n ^ 4 - 146 * n ^ 3 + 172 * n ^ 2
      - 124 * n + 40) / (n ^ 6 * (n - 1) ^ 3 * (n - 2))

def hAq (n : ℝ) : ℝ := hh3 n - hh4 n
def hBq (n : ℝ) : ℝ := hh6 n - hh7 n
def hCq (n : ℝ) : ℝ := hh9 n - hh10 n
def hGg (n : ℝ) : ℝ := hh8 n - 2 * hh9 n + hh10 n

def hA22 (n : ℝ) : ℝ := (hh4 n + hh5 n) / 2 + hAq n / (2 * (n - 1))
def hA23 (n : ℝ) : ℝ := hh7 n + hBq n / (n - 1)
def hA33 (n : ℝ) : ℝ := hh10 n + 2 * hCq n / (n - 1) + hGg n / (n - 1) ^ 2
def hBb (n : ℝ) : ℝ := (hh4 n - hh5 n) / 2 + hAq n / (2 * (n - 1))
def hQ22 (n : ℝ) : ℝ := hCq n + hGg n / (n - 1)

/-- determinant of the 3x3 block A. -/
def hDet3 (n : ℝ) : ℝ :=
  hh0 n * (hA22 n * hA33 n - hA23 n ^ 2)
    - hh0 n * (hh0 n * hA33 n - hA23 n * hh0 n)
    + hh0 n * (hh0 n * hA23 n - hA22 n * hh0 n)

section Bridges

variable {n : ℝ}

private theorem ne0 (hn : 4 ≤ n) : n ≠ 0 := by intro h; rw [h] at hn; linarith
private theorem ne1 (hn : 4 ≤ n) : n - 1 ≠ 0 := by intro h; apply absurd hn; linarith [h]
private theorem ne2 (hn : 4 ≤ n) : n - 2 ≠ 0 := by intro h; apply absurd hn; linarith [h]

theorem bridgeA1 (hn : 4 ≤ n) : hh0 n = pivotA1 n := by
  have h0 := ne0 hn
  unfold hh0 pivotA1 pivotA1Num pivotA1Den
  field_simp

theorem bridgeA2 (hn : 4 ≤ n) :
    2 * (hh0 n * hA22 n - hh0 n ^ 2) = pivotA2 n := by
  have h0 := ne0 hn; have h1 := ne1 hn; have h2 := ne2 hn
  unfold pivotA2
  rw [eq_div_iff (pivotA2Den_pos hn).ne']
  unfold pivotA2Num pivotA2Den hh0 hA22 hAq hh3 hh4 hh5
  field_simp
  ring

theorem bridgeB (hn : 4 ≤ n) : 2 * hBb n = pivotB n := by
  have h0 := ne0 hn; have h1 := ne1 hn; have h2 := ne2 hn
  unfold pivotB
  rw [eq_div_iff (pivotBDen_pos hn).ne']
  unfold pivotBNum pivotBDen hBb hAq hh3 hh4 hh5
  field_simp
  ring

theorem bridgeC1 (hn : 4 ≤ n) : hAq n = pivotC1 n := by
  have h0 := ne0 hn; have h1 := ne1 hn; have h2 := ne2 hn
  unfold pivotC1
  rw [eq_div_iff (pivotC1Den_pos hn).ne']
  unfold pivotC1Num pivotC1Den hAq hh3 hh4
  field_simp
  ring

theorem bridgeD (hn : 4 ≤ n) : hGg n = pivotD n := by
  have h0 := ne0 hn; have h1 := ne1 hn; have h2 := ne2 hn
  unfold pivotD
  rw [eq_div_iff (pivotDDen_pos hn).ne']
  unfold pivotDNum pivotDDen hGg hh8 hh9 hh10
  field_simp
  ring

theorem bridgeC2 (hn : 4 ≤ n) :
    4 * (hAq n * hQ22 n - hBq n ^ 2) = pivotC2 n := by
  have h0 := ne0 hn; have h1 := ne1 hn; have h2 := ne2 hn
  unfold pivotC2
  rw [eq_div_iff (pivotC2Den_pos hn).ne']
  unfold pivotC2Num pivotC2Den hAq hQ22 hBq hCq hGg hh3 hh4 hh6 hh7 hh8 hh9 hh10
  field_simp
  ring

theorem bridgeA3 (hn : 4 ≤ n) : 4 * hDet3 n = pivotA3 n := by
  have h0 := ne0 hn; have h1 := ne1 hn; have h2 := ne2 hn
  unfold pivotA3
  rw [eq_div_iff (pivotA3Den_pos hn).ne']
  unfold pivotA3Num pivotA3Den hDet3 hA22 hA23 hA33 hAq hBq hCq hGg
    hh0 hh3 hh4 hh5 hh6 hh7 hh8 hh9 hh10
  field_simp
  ring

end Bridges

/-! ## 3f.  Positive leading minors make a quadratic form nonnegative -/

/-- A binary quadratic form with positive leading minors is nonnegative.  The
witness is Lagrange's identity `a (a x² + 2b xy + c y²) = (a x + b y)² + (ac − b²) y²`,
so no spectral theory is used. -/
theorem quad2_nonneg {a b c x y : ℝ} (h1 : 0 < a) (h2 : 0 < a * c - b ^ 2) :
    0 ≤ a * x ^ 2 + 2 * b * x * y + c * y ^ 2 := by
  have key : a * (a * x ^ 2 + 2 * b * x * y + c * y ^ 2)
      = (a * x + b * y) ^ 2 + (a * c - b ^ 2) * y ^ 2 := by ring
  have t1 : (0 : ℝ) ≤ (a * x + b * y) ^ 2 := sq_nonneg _
  have t2 : (0 : ℝ) ≤ (a * c - b ^ 2) * y ^ 2 := mul_nonneg h2.le (sq_nonneg _)
  nlinarith [key, t1, t2, h1]

/-- The same in three variables: two rounds of the same completion of squares, the
second using Sylvester's identity `d₂ (a₁₁a₃₃ − a₁₃²) − e² = a₁₁ · det`. -/
theorem quad3_nonneg {a11 a12 a13 a22 a23 a33 x y z : ℝ}
    (h1 : 0 < a11)
    (h2 : 0 < a11 * a22 - a12 ^ 2)
    (h3 : 0 < a11 * (a22 * a33 - a23 ^ 2) - a12 * (a12 * a33 - a23 * a13)
              + a13 * (a12 * a23 - a22 * a13)) :
    0 ≤ a11 * x ^ 2 + 2 * a12 * x * y + 2 * a13 * x * z
        + a22 * y ^ 2 + 2 * a23 * y * z + a33 * z ^ 2 := by
  have key : (a11 * (a11 * a22 - a12 ^ 2))
        * (a11 * x ^ 2 + 2 * a12 * x * y + 2 * a13 * x * z
            + a22 * y ^ 2 + 2 * a23 * y * z + a33 * z ^ 2)
      = (a11 * a22 - a12 ^ 2) * (a11 * x + a12 * y + a13 * z) ^ 2
        + ((a11 * a22 - a12 ^ 2) * y + (a11 * a23 - a12 * a13) * z) ^ 2
        + a11 * (a11 * (a22 * a33 - a23 ^ 2) - a12 * (a12 * a33 - a23 * a13)
                  + a13 * (a12 * a23 - a22 * a13)) * z ^ 2 := by ring
  have t1 : (0 : ℝ) ≤ (a11 * a22 - a12 ^ 2) * (a11 * x + a12 * y + a13 * z) ^ 2 :=
    mul_nonneg h2.le (sq_nonneg _)
  have t2 : (0 : ℝ)
      ≤ ((a11 * a22 - a12 ^ 2) * y + (a11 * a23 - a12 * a13) * z) ^ 2 := sq_nonneg _
  have t3 : (0 : ℝ) ≤ a11 * (a11 * (a22 * a33 - a23 ^ 2) - a12 * (a12 * a33 - a23 * a13)
                  + a13 * (a12 * a23 - a22 * a13)) * z ^ 2 :=
    mul_nonneg (mul_nonneg h1.le h3.le) (sq_nonneg _)
  nlinarith [key, t1, t2, t3, mul_pos h1 h2]

/-! ### The four blocks are positive, from the seven pivot theorems -/

section BlockPos

variable {n : ℝ}

theorem hh0_pos (hn : 4 ≤ n) : 0 < hh0 n := by
  rw [bridgeA1 hn]; exact pivotA1_pos hn

theorem hA_minor2_pos (hn : 4 ≤ n) : 0 < hh0 n * hA22 n - hh0 n ^ 2 := by
  have h := pivotA2_pos hn
  rw [← bridgeA2 hn] at h
  linarith

theorem hA_minor3_pos (hn : 4 ≤ n) : 0 < hDet3 n := by
  have h := pivotA3_pos hn
  rw [← bridgeA3 hn] at h
  linarith

theorem hBb_pos (hn : 4 ≤ n) : 0 < hBb n := by
  have h := pivotB_pos hn
  rw [← bridgeB hn] at h
  linarith

theorem hAq_pos (hn : 4 ≤ n) : 0 < hAq n := by
  rw [bridgeC1 hn]; exact pivotC1_pos hn

theorem hC_minor2_pos (hn : 4 ≤ n) : 0 < hAq n * hQ22 n - hBq n ^ 2 := by
  have h := pivotC2_pos hn
  rw [← bridgeC2 hn] at h
  linarith

theorem hGg_pos (hn : 4 ≤ n) : 0 < hGg n := by
  rw [bridgeD hn]; exact pivotD_pos hn

/-- **The `A` block is nonnegative**, from the three `A` pivots. -/
theorem quadA_nonneg (hn : 4 ≤ n) (x y z : ℝ) :
    0 ≤ hh0 n * x ^ 2 + 2 * hh0 n * x * y + 2 * hh0 n * x * z
        + hA22 n * y ^ 2 + 2 * hA23 n * y * z + hA33 n * z ^ 2 :=
  quad3_nonneg (hh0_pos hn) (hA_minor2_pos hn) (hA_minor3_pos hn)

/-- **The `C` block is nonnegative**, from the two `C` pivots. -/
theorem quadC_nonneg (hn : 4 ≤ n) (x y : ℝ) :
    0 ≤ hAq n * x ^ 2 + 2 * hBq n * x * y + hQ22 n * y ^ 2 :=
  quad2_nonneg (hAq_pos hn) (hC_minor2_pos hn)

end BlockPos

/-! ## 3g.  The `sigma_11` Gram at a corner, and its quadratic form

The cells split into four classes relative to the corner `p`: the corner itself, the
rest of `p`'s row, the rest of `p`'s column, and the body.  `iP`, `iR`, `iC`, `iB`
are their indicators, written as products so that `ring` can handle them as atoms. -/

section Gram

variable {n : ℕ}

def iP (p u : Fin n × Fin n) : ℝ :=
  (if u.1 = p.1 then (1 : ℝ) else 0) * (if u.2 = p.2 then (1 : ℝ) else 0)

def iC (p u : Fin n × Fin n) : ℝ :=
  (1 - (if u.1 = p.1 then (1 : ℝ) else 0)) * (if u.2 = p.2 then (1 : ℝ) else 0)

def iR (p u : Fin n × Fin n) : ℝ :=
  (if u.1 = p.1 then (1 : ℝ) else 0) * (1 - (if u.2 = p.2 then (1 : ℝ) else 0))

def iB (p u : Fin n × Fin n) : ℝ :=
  (1 - (if u.1 = p.1 then (1 : ℝ) else 0)) * (1 - (if u.2 = p.2 then (1 : ℝ) else 0))

/-- **The `sigma_11` Gram at the corner `p`.**  Eleven orbit values, each attached to
the indicator pattern that produces its term of the quadratic form. -/
def Hm (n : ℕ) (p : Fin n × Fin n) : Matrix (Fin n × Fin n) (Fin n × Fin n) ℝ :=
  fun u v =>
    hh0 (n : ℝ) * (iP p u * iP p v)
    + hh0 (n : ℝ) * (iP p u * (iC p v + iR p v) + (iC p u + iR p u) * iP p v)
    + hh0 (n : ℝ) * (iP p u * iB p v + iB p u * iP p v)
    + hh4 (n : ℝ) * (iC p u * iC p v + iR p u * iR p v)
    + hh5 (n : ℝ) * (iC p u * iR p v + iR p u * iC p v)
    + hh7 (n : ℝ) * ((iC p u + iR p u) * iB p v + iB p u * (iC p v + iR p v))
    + hh10 (n : ℝ) * (iB p u * iB p v)
    + hAq (n : ℝ) * ((if u = v then (1 : ℝ) else 0) * (iC p u + iR p u))
    + hBq (n : ℝ) * ((if u.1 = v.1 then (1 : ℝ) else 0)
                        * (iC p u * iB p v + iB p u * iC p v)
                      + (if u.2 = v.2 then (1 : ℝ) else 0)
                        * (iR p u * iB p v + iB p u * iR p v))
    + hCq (n : ℝ) * ((if u.1 = v.1 then (1 : ℝ) else 0) * (iB p u * iB p v)
                      + (if u.2 = v.2 then (1 : ℝ) else 0) * (iB p u * iB p v))
    + hGg (n : ℝ) * ((if u = v then (1 : ℝ) else 0) * iB p u)

theorem Hm_symm (n : ℕ) (p u v : Fin n × Fin n) : Hm n p u v = Hm n p v u := by
  unfold Hm
  rcases eq_or_ne u v with h | h
  · rw [h]
  · rw [if_neg h, if_neg (Ne.symm h),
      if_congr (eq_comm (a := u.1) (b := v.1)) rfl rfl,
      if_congr (eq_comm (a := u.2) (b := v.2)) rfl rfl]
    ring

/-! ### The four ways a double sum collapses -/

private theorem sum_free_pair (F G : Fin n × Fin n → ℝ) :
    (∑ u : Fin n × Fin n, ∑ v : Fin n × Fin n, F u * G v)
      = (∑ u, F u) * (∑ v, G v) := by
  rw [Finset.sum_mul_sum]

private theorem sum_diag_pair (F G : Fin n × Fin n → ℝ) :
    (∑ u : Fin n × Fin n, ∑ v : Fin n × Fin n,
        (if u = v then (1 : ℝ) else 0) * (F u * G v))
      = ∑ u, F u * G u := by
  refine Finset.sum_congr rfl fun u _ => ?_
  simp only [boole_mul]
  rw [Finset.sum_ite_eq univ u (fun v => F u * G v)]
  simp

private theorem sum_row_pair (F G : Fin n × Fin n → ℝ) :
    (∑ u : Fin n × Fin n, ∑ v : Fin n × Fin n,
        (if u.1 = v.1 then (1 : ℝ) else 0) * (F u * G v))
      = ∑ i, (∑ j, F (i, j)) * (∑ l, G (i, l)) := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Fintype.sum_prod_type]
  have hcollapse : ∀ k : Fin n,
      (∑ l, (if ((i, j) : Fin n × Fin n).1 = ((k, l) : Fin n × Fin n).1 then (1 : ℝ) else 0)
          * (F (i, j) * G (k, l)))
        = (if i = k then (1 : ℝ) else 0) * ∑ l, F (i, j) * G (k, l) := by
    intro k
    rw [Finset.mul_sum]
  rw [Finset.sum_congr rfl fun k (_ : k ∈ univ) => hcollapse k]
  simp only [boole_mul]
  rw [Finset.sum_ite_eq univ i (fun k => ∑ l, F (i, j) * G (k, l))]
  simp [Finset.mul_sum]

private theorem sum_col_pair (F G : Fin n × Fin n → ℝ) :
    (∑ u : Fin n × Fin n, ∑ v : Fin n × Fin n,
        (if u.2 = v.2 then (1 : ℝ) else 0) * (F u * G v))
      = ∑ j, (∑ i, F (i, j)) * (∑ k, G (k, j)) := by
  have inner : ∀ u : Fin n × Fin n,
      (∑ v : Fin n × Fin n, (if u.2 = v.2 then (1 : ℝ) else 0) * (F u * G v))
        = F u * ∑ k, G (k, u.2) := by
    intro u
    rw [Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [boole_mul]
    rw [Finset.sum_ite_eq univ u.2 (fun l => F u * G (k, l))]
    simp
  rw [Finset.sum_congr rfl fun u (_ : u ∈ univ) => inner u, Fintype.sum_prod_type,
    Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  dsimp only
  rw [← Finset.sum_mul]

/-! ### The local coordinates at the corner -/

def lKap (p : Fin n × Fin n) (b : Fin n × Fin n → ℝ) : ℝ := ∑ u, iC p u * b u
def lRho (p : Fin n × Fin n) (b : Fin n × Fin n → ℝ) : ℝ := ∑ u, iR p u * b u
def lTau (p : Fin n × Fin n) (b : Fin n × Fin n → ℝ) : ℝ := ∑ u, iB p u * b u
def lE2 (p : Fin n × Fin n) (b : Fin n × Fin n → ℝ) : ℝ := ∑ u, iC p u * b u ^ 2
def lF2 (p : Fin n × Fin n) (b : Fin n × Fin n → ℝ) : ℝ := ∑ u, iR p u * b u ^ 2
def lB2 (p : Fin n × Fin n) (b : Fin n × Fin n → ℝ) : ℝ := ∑ u, iB p u * b u ^ 2

/-- `e_i` : the entry of `p`'s column in row `i`, zero in `p`'s own row. -/
def lE (p : Fin n × Fin n) (b : Fin n × Fin n → ℝ) (i : Fin n) : ℝ :=
  ∑ j, iC p (i, j) * b (i, j)
/-- `r_i` : the body row sum in row `i`. -/
def lR (p : Fin n × Fin n) (b : Fin n × Fin n → ℝ) (i : Fin n) : ℝ :=
  ∑ j, iB p (i, j) * b (i, j)
/-- `f_j` : the entry of `p`'s row in column `j`. -/
def lF (p : Fin n × Fin n) (b : Fin n × Fin n → ℝ) (j : Fin n) : ℝ :=
  ∑ i, iR p (i, j) * b (i, j)
/-- `c_j` : the body column sum in column `j`. -/
def lC (p : Fin n × Fin n) (b : Fin n × Fin n → ℝ) (j : Fin n) : ℝ :=
  ∑ i, iB p (i, j) * b (i, j)

theorem sum_iP (p : Fin n × Fin n) (b : Fin n × Fin n → ℝ) :
    (∑ u, iP p u * b u) = b p := by
  have : ∀ u : Fin n × Fin n, iP p u * b u = (if u = p then (1 : ℝ) else 0) * b u := by
    intro u
    unfold iP
    rcases eq_or_ne u p with h | h
    · rw [h]; simp
    · rw [if_neg h]
      rcases eq_or_ne u.1 p.1 with h1 | h1
      · rw [if_neg (fun h2 : u.2 = p.2 => h (Prod.ext h1 h2))]; ring
      · rw [if_neg h1]; ring
  rw [Finset.sum_congr rfl fun u (_ : u ∈ univ) => this u]
  simp only [boole_mul]
  rw [Finset.sum_ite_eq' univ p b]
  simp

/-- **The quadratic form of the corner Gram, in the local coordinates.**  This is the
orbit expansion checked against the assembled Gram by `verify_H_identity.py`. -/
theorem quadForm_Hm (n : ℕ) (p : Fin n × Fin n) (b : Fin n × Fin n → ℝ) :
    Certificate.quadForm (Hm n p) b
      = hh0 (n : ℝ) * b p ^ 2
        + 2 * hh0 (n : ℝ) * b p * (lKap p b + lRho p b)
        + 2 * hh0 (n : ℝ) * b p * lTau p b
        + hh4 (n : ℝ) * (lKap p b ^ 2 + lRho p b ^ 2)
        + 2 * hh5 (n : ℝ) * (lKap p b * lRho p b)
        + 2 * hh7 (n : ℝ) * ((lKap p b + lRho p b) * lTau p b)
        + hh10 (n : ℝ) * lTau p b ^ 2
        + hAq (n : ℝ) * (lE2 p b + lF2 p b)
        + 2 * hBq (n : ℝ) * ((∑ i, lE p b i * lR p b i) + ∑ j, lF p b j * lC p b j)
        + hCq (n : ℝ) * ((∑ i, lR p b i ^ 2) + ∑ j, lC p b j ^ 2)
        + hGg (n : ℝ) * lB2 p b := by
  have hq : Certificate.quadForm (Hm n p) b
      = ∑ u : Fin n × Fin n, ∑ v : Fin n × Fin n, Hm n p u v * (b u * b v) := by
    unfold Certificate.quadForm Matrix.mulVec dotProduct
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun v _ => by ring
  have expand : (∑ u : Fin n × Fin n, ∑ v : Fin n × Fin n, Hm n p u v * (b u * b v))
      = hh0 (n : ℝ) * (∑ u : Fin n × Fin n, ∑ v : Fin n × Fin n,
            (iP p u * b u) * (iP p v * b v))
        + hh0 (n : ℝ) * (∑ u : Fin n × Fin n, ∑ v : Fin n × Fin n,
            (iP p u * b u) * ((iC p v + iR p v) * b v))
        + hh0 (n : ℝ) * (∑ u : Fin n × Fin n, ∑ v : Fin n × Fin n,
            ((iC p u + iR p u) * b u) * (iP p v * b v))
        + hh0 (n : ℝ) * (∑ u : Fin n × Fin n, ∑ v : Fin n × Fin n,
            (iP p u * b u) * (iB p v * b v))
        + hh0 (n : ℝ) * (∑ u : Fin n × Fin n, ∑ v : Fin n × Fin n,
            (iB p u * b u) * (iP p v * b v))
        + hh4 (n : ℝ) * (∑ u : Fin n × Fin n, ∑ v : Fin n × Fin n,
            (iC p u * b u) * (iC p v * b v))
        + hh4 (n : ℝ) * (∑ u : Fin n × Fin n, ∑ v : Fin n × Fin n,
            (iR p u * b u) * (iR p v * b v))
        + hh5 (n : ℝ) * (∑ u : Fin n × Fin n, ∑ v : Fin n × Fin n,
            (iC p u * b u) * (iR p v * b v))
        + hh5 (n : ℝ) * (∑ u : Fin n × Fin n, ∑ v : Fin n × Fin n,
            (iR p u * b u) * (iC p v * b v))
        + hh7 (n : ℝ) * (∑ u : Fin n × Fin n, ∑ v : Fin n × Fin n,
            ((iC p u + iR p u) * b u) * (iB p v * b v))
        + hh7 (n : ℝ) * (∑ u : Fin n × Fin n, ∑ v : Fin n × Fin n,
            (iB p u * b u) * ((iC p v + iR p v) * b v))
        + hh10 (n : ℝ) * (∑ u : Fin n × Fin n, ∑ v : Fin n × Fin n,
            (iB p u * b u) * (iB p v * b v))
        + hAq (n : ℝ) * (∑ u : Fin n × Fin n, ∑ v : Fin n × Fin n,
            (if u = v then (1 : ℝ) else 0) * (((iC p u + iR p u) * b u) * b v))
        + hBq (n : ℝ) * (∑ u : Fin n × Fin n, ∑ v : Fin n × Fin n,
            (if u.1 = v.1 then (1 : ℝ) else 0) * ((iC p u * b u) * (iB p v * b v)))
        + hBq (n : ℝ) * (∑ u : Fin n × Fin n, ∑ v : Fin n × Fin n,
            (if u.1 = v.1 then (1 : ℝ) else 0) * ((iB p u * b u) * (iC p v * b v)))
        + hBq (n : ℝ) * (∑ u : Fin n × Fin n, ∑ v : Fin n × Fin n,
            (if u.2 = v.2 then (1 : ℝ) else 0) * ((iR p u * b u) * (iB p v * b v)))
        + hBq (n : ℝ) * (∑ u : Fin n × Fin n, ∑ v : Fin n × Fin n,
            (if u.2 = v.2 then (1 : ℝ) else 0) * ((iB p u * b u) * (iR p v * b v)))
        + hCq (n : ℝ) * (∑ u : Fin n × Fin n, ∑ v : Fin n × Fin n,
            (if u.1 = v.1 then (1 : ℝ) else 0) * ((iB p u * b u) * (iB p v * b v)))
        + hCq (n : ℝ) * (∑ u : Fin n × Fin n, ∑ v : Fin n × Fin n,
            (if u.2 = v.2 then (1 : ℝ) else 0) * ((iB p u * b u) * (iB p v * b v)))
        + hGg (n : ℝ) * (∑ u : Fin n × Fin n, ∑ v : Fin n × Fin n,
            (if u = v then (1 : ℝ) else 0) * ((iB p u * b u) * b v)) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun u _ =>
      Finset.sum_congr rfl fun v _ => by unfold Hm; ring
  rw [hq, expand, sum_free_pair, sum_free_pair, sum_free_pair, sum_free_pair,
    sum_free_pair, sum_free_pair, sum_free_pair, sum_free_pair, sum_free_pair,
    sum_free_pair, sum_free_pair, sum_free_pair, sum_diag_pair, sum_row_pair,
    sum_row_pair, sum_col_pair, sum_col_pair, sum_row_pair, sum_col_pair,
    sum_diag_pair, sum_iP]
  unfold lKap lRho lTau lE2 lF2 lB2 lE lR lF lC
  have hsplit : ∀ φ ψ : Fin n × Fin n → ℝ,
      (∑ u : Fin n × Fin n, (φ u + ψ u) * b u)
        = (∑ u, φ u * b u) + ∑ u, ψ u * b u := by
    intro φ ψ
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun u _ => by ring
  rw [hsplit]
  have hE2 : (∑ u : Fin n × Fin n, ((iC p u + iR p u) * b u) * b u)
      = (∑ u, iC p u * b u ^ 2) + ∑ u, iR p u * b u ^ 2 := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun u _ => by ring
  have hB2 : (∑ u : Fin n × Fin n, (iB p u * b u) * b u) = ∑ u, iB p u * b u ^ 2 :=
    Finset.sum_congr rfl fun u _ => by ring
  rw [hE2, hB2]
  have hsq : ∀ f : Fin n → ℝ, (∑ i, f i * f i) = ∑ i, f i ^ 2 :=
    fun f => Finset.sum_congr rfl fun i _ => by ring
  have hswapR : (∑ i, (∑ j, iB p (i, j) * b (i, j)) * ∑ l, iC p (i, l) * b (i, l))
      = ∑ i, (∑ j, iC p (i, j) * b (i, j)) * ∑ l, iB p (i, l) * b (i, l) :=
    Finset.sum_congr rfl fun i _ => by ring
  have hswapC : (∑ j, (∑ i, iB p (i, j) * b (i, j)) * ∑ k, iR p (k, j) * b (k, j))
      = ∑ j, (∑ i, iR p (i, j) * b (i, j)) * ∑ k, iB p (k, j) * b (k, j) :=
    Finset.sum_congr rfl fun j _ => by ring
  rw [hsq, hsq, hswapR, hswapC]
  ring

end Gram

/-! ## 3h.  The centred decomposition, and `PosSemidef`

The isotypic coordinates are the residuals `ê_i = e_i − κ/m`, `r̂_i = r_i − τ/m`
(`m = n − 1`), and the doubly centred body.  Those live on the index sets `i ≠ p.1`,
`j ≠ p.2`, which would force `Finset.erase` everywhere.  Instead the centring
constants are multiplied by the idempotent weights `zR = 1 − [i = p.1]`, which makes
the excluded term vanish identically; every sum then runs over `univ`. -/

section Decomp

variable {n : ℕ}

/-- `1` off the corner's row, `0` on it. -/
def zR (p : Fin n × Fin n) (i : Fin n) : ℝ := 1 - (if i = p.1 then (1 : ℝ) else 0)
/-- `1` off the corner's column, `0` on it. -/
def zC (p : Fin n × Fin n) (j : Fin n) : ℝ := 1 - (if j = p.2 then (1 : ℝ) else 0)

theorem zR_idem (p : Fin n × Fin n) (i : Fin n) : zR p i * zR p i = zR p i := by
  unfold zR; by_cases h : i = p.1 <;> simp [h]

theorem zC_idem (p : Fin n × Fin n) (j : Fin n) : zC p j * zC p j = zC p j := by
  unfold zC; by_cases h : j = p.2 <;> simp [h]

theorem sum_zR (p : Fin n × Fin n) : (∑ i, zR p i) = (n : ℝ) - 1 := by
  unfold zR
  rw [Finset.sum_sub_distrib]
  simp

theorem sum_zC (p : Fin n × Fin n) : (∑ j, zC p j) = (n : ℝ) - 1 := by
  unfold zC
  rw [Finset.sum_sub_distrib]
  simp

theorem iB_eq (p u : Fin n × Fin n) : iB p u = zR p u.1 * zC p u.2 := rfl
theorem iC_eq (p u : Fin n × Fin n) :
    iC p u = zR p u.1 * (if u.2 = p.2 then (1 : ℝ) else 0) := rfl
theorem iR_eq (p u : Fin n × Fin n) :
    iR p u = (if u.1 = p.1 then (1 : ℝ) else 0) * zC p u.2 := rfl

/-! ### Closed forms for the local coordinates -/

variable (p : Fin n × Fin n) (b : Fin n × Fin n → ℝ)

theorem lE_apply (i : Fin n) : lE p b i = zR p i * b (i, p.2) := by
  unfold lE
  have step : ∀ j : Fin n, iC p (i, j) * b (i, j)
      = zR p i * ((if j = p.2 then (1 : ℝ) else 0) * b (i, j)) := by
    intro j; simp only [iC, zR]; ring
  rw [Finset.sum_congr rfl fun j (_ : j ∈ univ) => step j, ← Finset.mul_sum]
  congr 1
  simp only [boole_mul]
  rw [Finset.sum_ite_eq' univ p.2 fun j => b (i, j)]
  simp

theorem lR_apply (i : Fin n) :
    lR p b i = zR p i * ((∑ j, b (i, j)) - b (i, p.2)) := by
  unfold lR
  have step : ∀ j : Fin n, iB p (i, j) * b (i, j)
      = zR p i * (b (i, j) - (if j = p.2 then (1 : ℝ) else 0) * b (i, j)) := by
    intro j; simp only [iB, zR]; ring
  rw [Finset.sum_congr rfl fun j (_ : j ∈ univ) => step j, ← Finset.mul_sum]
  congr 1
  rw [Finset.sum_sub_distrib]
  congr 1
  simp only [boole_mul]
  rw [Finset.sum_ite_eq' univ p.2 fun j => b (i, j)]
  simp

theorem lF_apply (j : Fin n) : lF p b j = zC p j * b (p.1, j) := by
  unfold lF
  have step : ∀ i : Fin n, iR p (i, j) * b (i, j)
      = zC p j * ((if i = p.1 then (1 : ℝ) else 0) * b (i, j)) := by
    intro i; simp only [iR, zC]; ring
  rw [Finset.sum_congr rfl fun i (_ : i ∈ univ) => step i, ← Finset.mul_sum]
  congr 1
  simp only [boole_mul]
  rw [Finset.sum_ite_eq' univ p.1 fun i => b (i, j)]
  simp

theorem lC_apply (j : Fin n) :
    lC p b j = zC p j * ((∑ i, b (i, j)) - b (p.1, j)) := by
  unfold lC
  have step : ∀ i : Fin n, iB p (i, j) * b (i, j)
      = zC p j * (b (i, j) - (if i = p.1 then (1 : ℝ) else 0) * b (i, j)) := by
    intro i; simp only [iB, zC]; ring
  rw [Finset.sum_congr rfl fun i (_ : i ∈ univ) => step i, ← Finset.mul_sum]
  congr 1
  rw [Finset.sum_sub_distrib]
  congr 1
  simp only [boole_mul]
  rw [Finset.sum_ite_eq' univ p.1 fun i => b (i, j)]
  simp

theorem zR_lE (i : Fin n) : zR p i * lE p b i = lE p b i := by
  rw [lE_apply, ← mul_assoc, zR_idem]

theorem zR_lR (i : Fin n) : zR p i * lR p b i = lR p b i := by
  rw [lR_apply, ← mul_assoc, zR_idem]

theorem zC_lF (j : Fin n) : zC p j * lF p b j = lF p b j := by
  rw [lF_apply, ← mul_assoc, zC_idem]

theorem zC_lC (j : Fin n) : zC p j * lC p b j = lC p b j := by
  rw [lC_apply, ← mul_assoc, zC_idem]

/-! ### The local sums -/

theorem sum_lE : (∑ i, lE p b i) = lKap p b := by
  unfold lKap
  rw [Fintype.sum_prod_type]
  rfl

theorem sum_lR : (∑ i, lR p b i) = lTau p b := by
  unfold lTau
  rw [Fintype.sum_prod_type]
  rfl

theorem sum_lF : (∑ j, lF p b j) = lRho p b := by
  unfold lRho
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  rfl

theorem sum_lC : (∑ j, lC p b j) = lTau p b := by
  unfold lTau
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  rfl

theorem sum_lE_sq : (∑ i, lE p b i ^ 2) = lE2 p b := by
  unfold lE2
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  have step : ∀ j : Fin n, iC p (i, j) * b (i, j) ^ 2
      = zR p i * ((if j = p.2 then (1 : ℝ) else 0) * b (i, j) ^ 2) := by
    intro j; simp only [iC, zR]; ring
  rw [Finset.sum_congr rfl fun j (_ : j ∈ univ) => step j, ← Finset.mul_sum]
  simp only [boole_mul]
  rw [Finset.sum_ite_eq' univ p.2 fun j => b (i, j) ^ 2]
  simp only [Finset.mem_univ, if_true]
  rw [lE_apply]
  linear_combination (b (i, p.2) ^ 2) * zR_idem p i

theorem sum_lF_sq : (∑ j, lF p b j ^ 2) = lF2 p b := by
  unfold lF2
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  have step : ∀ i : Fin n, iR p (i, j) * b (i, j) ^ 2
      = zC p j * ((if i = p.1 then (1 : ℝ) else 0) * b (i, j) ^ 2) := by
    intro i; simp only [iR, zC]; ring
  rw [Finset.sum_congr rfl fun i (_ : i ∈ univ) => step i, ← Finset.mul_sum]
  simp only [boole_mul]
  rw [Finset.sum_ite_eq' univ p.1 fun i => b (i, j) ^ 2]
  simp only [Finset.mem_univ, if_true]
  rw [lF_apply]
  linear_combination (b (p.1, j) ^ 2) * zC_idem p j

/-- The body entries, as a function of the two indices. -/
def bodyX (p : Fin n × Fin n) (b : Fin n × Fin n → ℝ) (i j : Fin n) : ℝ :=
  iB p (i, j) * b (i, j)

theorem sum_bodyX_row (i : Fin n) : (∑ j, bodyX p b i j) = lR p b i := rfl
theorem sum_bodyX_col (j : Fin n) : (∑ i, bodyX p b i j) = lC p b j := rfl

theorem zR_bodyX (i j : Fin n) : zR p i * bodyX p b i j = bodyX p b i j := by
  unfold bodyX
  rw [iB_eq]
  linear_combination (zC p j * b (i, j)) * zR_idem p i

theorem zC_bodyX (i j : Fin n) : zC p j * bodyX p b i j = bodyX p b i j := by
  unfold bodyX
  rw [iB_eq]
  linear_combination (zR p i * b (i, j)) * zC_idem p j

theorem sum_bodyX_sq : (∑ i, ∑ j, bodyX p b i j ^ 2) = lB2 p b := by
  unfold lB2 bodyX
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [iB_eq]
  linear_combination (zC p j ^ 2 * b (i, j) ^ 2) * zR_idem p i
    + (zR p i * b (i, j) ^ 2) * zC_idem p j

/-! ### Centring, in one and two directions -/

theorem sum_centred_sq {ι : Type*} [Fintype ι] (e z : ι → ℝ) (m S : ℝ)
    (hz : ∀ i, z i * z i = z i) (hze : ∀ i, z i * e i = e i)
    (hm : (∑ i, z i) = m) (hS : (∑ i, e i) = S) (hm0 : m ≠ 0) :
    (∑ i, (e i - z i * (S / m)) ^ 2) = (∑ i, e i ^ 2) - S ^ 2 / m := by
  have step : ∀ i : ι, (e i - z i * (S / m)) ^ 2
      = e i ^ 2 - 2 * (S / m) * e i + (S / m) ^ 2 * z i := by
    intro i
    linear_combination (-2 * (S / m)) * hze i + (S / m) ^ 2 * hz i
  rw [Finset.sum_congr rfl fun i (_ : i ∈ univ) => step i]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    hm, hS]
  field_simp
  ring

theorem sum_centred_quad {ι : Type*} [Fintype ι] (α β γ : ℝ) (e r z : ι → ℝ)
    (m Sk St : ℝ) (hz : ∀ i, z i * z i = z i) (hze : ∀ i, z i * e i = e i)
    (hzr : ∀ i, z i * r i = r i) (hm : (∑ i, z i) = m) (hSk : (∑ i, e i) = Sk)
    (hSt : (∑ i, r i) = St) (hm0 : m ≠ 0) :
    (∑ i, (α * (e i - z i * (Sk / m)) ^ 2
        + 2 * β * (e i - z i * (Sk / m)) * (r i - z i * (St / m))
        + γ * (r i - z i * (St / m)) ^ 2))
      = α * ((∑ i, e i ^ 2) - Sk ^ 2 / m)
        + 2 * β * ((∑ i, e i * r i) - Sk * St / m)
        + γ * ((∑ i, r i ^ 2) - St ^ 2 / m) := by
  have step : ∀ i : ι, α * (e i - z i * (Sk / m)) ^ 2
        + 2 * β * (e i - z i * (Sk / m)) * (r i - z i * (St / m))
        + γ * (r i - z i * (St / m)) ^ 2
      = (α * e i ^ 2 + 2 * β * (e i * r i) + γ * r i ^ 2)
        - (2 * α * (Sk / m) + 2 * β * (St / m)) * e i
        - (2 * β * (Sk / m) + 2 * γ * (St / m)) * r i
        + (α * (Sk / m) ^ 2 + 2 * β * (Sk / m) * (St / m) + γ * (St / m) ^ 2) * z i := by
    intro i
    linear_combination (-2 * α * (Sk / m) - 2 * β * (St / m)) * hze i
      + (-2 * β * (Sk / m) - 2 * γ * (St / m)) * hzr i
      + (α * (Sk / m) ^ 2 + 2 * β * (Sk / m) * (St / m) + γ * (St / m) ^ 2) * hz i
  rw [Finset.sum_congr rfl fun i (_ : i ∈ univ) => step i]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, hm, hSk, hSt]
  have hsplit : (∑ i : ι, (α * e i ^ 2 + 2 * β * (e i * r i) + γ * r i ^ 2))
      = α * (∑ i, e i ^ 2) + 2 * β * (∑ i, e i * r i) + γ * ∑ i, r i ^ 2 := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum, ← Finset.mul_sum]
  rw [hsplit]
  field_simp
  ring

/-- **The doubly centred body is a sum of squares.**  Two applications of the centring
identity: once along the rows, once along the columns of what is left.  This is the
`D` block, and it needs no pivot beyond `hGg`. -/
theorem body_nonneg (hn0 : ((n : ℝ) - 1) ≠ 0) (hm : (0 : ℝ) < (n : ℝ) - 1) :
    0 ≤ lB2 p b - (∑ i, lR p b i ^ 2) / ((n : ℝ) - 1)
        - (∑ j, lC p b j ^ 2) / ((n : ℝ) - 1)
        + lTau p b ^ 2 / ((n : ℝ) - 1) ^ 2 := by
  have hrow : ∀ i : Fin n,
      (∑ j, (bodyX p b i j - zC p j * (lR p b i / ((n : ℝ) - 1))) ^ 2)
        = (∑ j, bodyX p b i j ^ 2) - lR p b i ^ 2 / ((n : ℝ) - 1) := by
    intro i
    exact sum_centred_sq (fun j => bodyX p b i j) (zC p) _ (lR p b i)
      (zC_idem p) (fun j => zC_bodyX p b i j) (sum_zC p) (sum_bodyX_row p b i) hn0
  have hYsum : (∑ i, ∑ j, (bodyX p b i j - zC p j * (lR p b i / ((n : ℝ) - 1))) ^ 2)
      = lB2 p b - (∑ i, lR p b i ^ 2) / ((n : ℝ) - 1) := by
    rw [Finset.sum_congr rfl fun i (_ : i ∈ univ) => hrow i, Finset.sum_sub_distrib,
      ← Finset.sum_div, sum_bodyX_sq]
  have hzY : ∀ j i : Fin n,
      zR p i * (bodyX p b i j - zC p j * (lR p b i / ((n : ℝ) - 1)))
        = bodyX p b i j - zC p j * (lR p b i / ((n : ℝ) - 1)) := by
    intro j i
    linear_combination zR_bodyX p b i j - (zC p j / ((n : ℝ) - 1)) * zR_lR p b i
  have hSY : ∀ j : Fin n,
      (∑ i, (bodyX p b i j - zC p j * (lR p b i / ((n : ℝ) - 1))))
        = lC p b j - zC p j * (lTau p b / ((n : ℝ) - 1)) := by
    intro j
    rw [Finset.sum_sub_distrib, sum_bodyX_col, ← Finset.mul_sum, ← Finset.sum_div,
      sum_lR]
  have hcol : ∀ j : Fin n,
      0 ≤ (∑ i, (bodyX p b i j - zC p j * (lR p b i / ((n : ℝ) - 1))) ^ 2)
          - (lC p b j - zC p j * (lTau p b / ((n : ℝ) - 1))) ^ 2 / ((n : ℝ) - 1) := by
    intro j
    rw [← sum_centred_sq (fun i => bodyX p b i j - zC p j * (lR p b i / ((n : ℝ) - 1)))
      (zR p) _ (lC p b j - zC p j * (lTau p b / ((n : ℝ) - 1))) (zR_idem p) (hzY j)
      (sum_zR p) (hSY j) hn0]
    exact Finset.sum_nonneg fun i _ => sq_nonneg _
  have htot : 0 ≤ (∑ j, ∑ i,
        (bodyX p b i j - zC p j * (lR p b i / ((n : ℝ) - 1))) ^ 2)
      - (∑ j, (lC p b j - zC p j * (lTau p b / ((n : ℝ) - 1))) ^ 2) / ((n : ℝ) - 1) := by
    rw [Finset.sum_div, ← Finset.sum_sub_distrib]
    exact Finset.sum_nonneg fun j _ => hcol j
  have hcolsum : (∑ j, (lC p b j - zC p j * (lTau p b / ((n : ℝ) - 1))) ^ 2)
      = (∑ j, lC p b j ^ 2) - lTau p b ^ 2 / ((n : ℝ) - 1) :=
    sum_centred_sq (lC p b) (zC p) _ (lTau p b) (zC_idem p) (zC_lC p b) (sum_zC p)
      (sum_lC p b) hn0
  rw [Finset.sum_comm, hYsum, hcolsum] at htot
  have hexp : lB2 p b - (∑ i, lR p b i ^ 2) / ((n : ℝ) - 1)
      - ((∑ j, lC p b j ^ 2) - lTau p b ^ 2 / ((n : ℝ) - 1)) / ((n : ℝ) - 1)
      = lB2 p b - (∑ i, lR p b i ^ 2) / ((n : ℝ) - 1)
        - (∑ j, lC p b j ^ 2) / ((n : ℝ) - 1)
        + lTau p b ^ 2 / ((n : ℝ) - 1) ^ 2 := by
    field_simp
    ring
  rw [hexp] at htot
  exact htot

/-- **`quadForm (H p)` is nonnegative for every `n ≥ 4`.**  The centred decomposition,
then the three block bounds: `A` from the three `A` pivots, `B` from `pivotB`, `C` from
the two `C` pivots at every row and every column, `D` from `pivotD`. -/
theorem quadForm_Hm_nonneg (hn : 4 ≤ n) :
    0 ≤ Certificate.quadForm (Hm n p) b := by
  have hn' : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hm : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hn0 : ((n : ℝ) - 1) ≠ 0 := ne_of_gt hm
  have key : Certificate.quadForm (Hm n p) b
      = (hh0 (n : ℝ) * b p ^ 2
          + 2 * hh0 (n : ℝ) * b p * (lKap p b + lRho p b)
          + 2 * hh0 (n : ℝ) * b p * lTau p b
          + hA22 (n : ℝ) * (lKap p b + lRho p b) ^ 2
          + 2 * hA23 (n : ℝ) * (lKap p b + lRho p b) * lTau p b
          + hA33 (n : ℝ) * lTau p b ^ 2)
        + hBb (n : ℝ) * (lKap p b - lRho p b) ^ 2
        + (hAq (n : ℝ) * ((∑ i, lE p b i ^ 2) - lKap p b ^ 2 / ((n : ℝ) - 1))
            + 2 * hBq (n : ℝ) * ((∑ i, lE p b i * lR p b i)
                - lKap p b * lTau p b / ((n : ℝ) - 1))
            + hQ22 (n : ℝ) * ((∑ i, lR p b i ^ 2) - lTau p b ^ 2 / ((n : ℝ) - 1)))
        + (hAq (n : ℝ) * ((∑ j, lF p b j ^ 2) - lRho p b ^ 2 / ((n : ℝ) - 1))
            + 2 * hBq (n : ℝ) * ((∑ j, lF p b j * lC p b j)
                - lRho p b * lTau p b / ((n : ℝ) - 1))
            + hQ22 (n : ℝ) * ((∑ j, lC p b j ^ 2) - lTau p b ^ 2 / ((n : ℝ) - 1)))
        + hGg (n : ℝ) * (lB2 p b - (∑ i, lR p b i ^ 2) / ((n : ℝ) - 1)
            - (∑ j, lC p b j ^ 2) / ((n : ℝ) - 1)
            + lTau p b ^ 2 / ((n : ℝ) - 1) ^ 2) := by
    rw [quadForm_Hm, ← sum_lE_sq, ← sum_lF_sq]
    unfold hA22 hA23 hA33 hBb hQ22 hAq hBq hCq hGg
    field_simp
    ring
  rw [key]
  have hA : 0 ≤ hh0 (n : ℝ) * b p ^ 2
      + 2 * hh0 (n : ℝ) * b p * (lKap p b + lRho p b)
      + 2 * hh0 (n : ℝ) * b p * lTau p b
      + hA22 (n : ℝ) * (lKap p b + lRho p b) ^ 2
      + 2 * hA23 (n : ℝ) * (lKap p b + lRho p b) * lTau p b
      + hA33 (n : ℝ) * lTau p b ^ 2 := quadA_nonneg hn' _ _ _
  have hB : 0 ≤ hBb (n : ℝ) * (lKap p b - lRho p b) ^ 2 :=
    mul_nonneg (hBb_pos hn').le (sq_nonneg _)
  have hCrow : 0 ≤ hAq (n : ℝ) * ((∑ i, lE p b i ^ 2) - lKap p b ^ 2 / ((n : ℝ) - 1))
      + 2 * hBq (n : ℝ) * ((∑ i, lE p b i * lR p b i)
          - lKap p b * lTau p b / ((n : ℝ) - 1))
      + hQ22 (n : ℝ) * ((∑ i, lR p b i ^ 2) - lTau p b ^ 2 / ((n : ℝ) - 1)) := by
    rw [← sum_centred_quad (hAq (n : ℝ)) (hBq (n : ℝ)) (hQ22 (n : ℝ)) (lE p b) (lR p b)
      (zR p) _ (lKap p b) (lTau p b) (zR_idem p) (zR_lE p b) (zR_lR p b) (sum_zR p)
      (sum_lE p b) (sum_lR p b) hn0]
    exact Finset.sum_nonneg fun i _ => quadC_nonneg hn' _ _
  have hCcol : 0 ≤ hAq (n : ℝ) * ((∑ j, lF p b j ^ 2) - lRho p b ^ 2 / ((n : ℝ) - 1))
      + 2 * hBq (n : ℝ) * ((∑ j, lF p b j * lC p b j)
          - lRho p b * lTau p b / ((n : ℝ) - 1))
      + hQ22 (n : ℝ) * ((∑ j, lC p b j ^ 2) - lTau p b ^ 2 / ((n : ℝ) - 1)) := by
    rw [← sum_centred_quad (hAq (n : ℝ)) (hBq (n : ℝ)) (hQ22 (n : ℝ)) (lF p b) (lC p b)
      (zC p) _ (lRho p b) (lTau p b) (zC_idem p) (zC_lF p b) (zC_lC p b) (sum_zC p)
      (sum_lF p b) (sum_lC p b) hn0]
    exact Finset.sum_nonneg fun j _ => quadC_nonneg hn' _ _
  have hD : 0 ≤ hGg (n : ℝ) * (lB2 p b - (∑ i, lR p b i ^ 2) / ((n : ℝ) - 1)
      - (∑ j, lC p b j ^ 2) / ((n : ℝ) - 1)
      + lTau p b ^ 2 / ((n : ℝ) - 1) ^ 2) :=
    mul_nonneg (hGg_pos hn').le (body_nonneg p b hn0 hm)
  linarith

/-- **The `sigma_11` Gram at every corner is positive semidefinite, for every
`n ≥ 4`.**  No spectral theorem, no `native_decide`: the four blocks are bounded by
the seven pivot theorems through the completions of squares of Stage B. -/
theorem Hm_posSemidef (hn : 4 ≤ n) : (Hm n p).PosSemidef := by
  constructor
  · ext u v
    simpa [Matrix.conjTranspose_apply] using Hm_symm n p v u
  · intro x
    simpa [Certificate.quadForm] using quadForm_Hm_nonneg p x hn

end Decomp


/-! ## 4.  The assembly -/

/-- Centred coordinates `b = A − J_n/n`, indexed by matrix positions. -/
def centre (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) : Fin n × Fin n → ℝ :=
  fun p => A p.1 p.2 - 1 / (n : ℝ)

/-- **The objective, written out.**  This is `(2 − 6/n³) − Φ₃(A)` with `e_3` and
`σ_3` replaced by their proved closed forms, the binomial denominators kept
explicit.  Every sum is over the entries of `A`: no permanent, no subpermanent, no
sum over subsets survives here. -/
noncomputable def objPoly (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  2 - 6 / (n : ℝ) ^ 3
    - (2 * (∑ i, ∑ j, A i j) ^ 3
        - 3 * (∑ i, ∑ j, A i j) * ((∑ i, (∑ j, A i j) ^ 2) + (∑ j, (∑ i, A i j) ^ 2))
        + 2 * (∑ i, (∑ j, A i j) ^ 3) + 2 * (∑ j, (∑ i, A i j) ^ 3))
      / (6 * (n.choose 3 : ℝ))
    + ((∑ i, ∑ j, A i j) ^ 3
        - 3 * (∑ i, ∑ j, A i j) * ((∑ i, (∑ j, A i j) ^ 2) + (∑ j, (∑ i, A i j) ^ 2))
        + 3 * (∑ i, ∑ j, A i j ^ 2) * (∑ i, ∑ j, A i j)
        + 6 * (∑ i, ∑ j, A i j * (∑ l, A i l) * (∑ l, A l j))
        + 2 * (∑ i, (∑ j, A i j) ^ 3) + 2 * (∑ j, (∑ i, A i j) ^ 3)
        - 6 * (∑ i, ∑ j, A i j ^ 2 * (∑ l, A i l))
        - 6 * (∑ i, ∑ j, A i j ^ 2 * (∑ l, A l j))
        + 4 * (∑ i, ∑ j, A i j ^ 3))
      / (6 * (n.choose 3 : ℝ) ^ 2)

/-- **The objective equals its written-out form.**  Kernel-checked; this is where the
two closed forms are cashed in, and it is the step that removes the combinatorial
definitions from everything downstream. -/
theorem obj_eq_objPoly {n : ℕ} (hn : 3 ≤ n) (A : Matrix (Fin n) (Fin n) ℝ) :
    (2 - 6 / (n : ℝ) ^ 3) - Phi 3 A = objPoly n A := by
  have hn0 : (n : ℝ) ≠ 0 := by
    have : 0 < n := lt_of_lt_of_le (by norm_num) hn
    exact_mod_cast this.ne'
  have hC : (n.choose 3 : ℝ) ≠ 0 := by
    have h := Nat.choose_pos hn
    exact_mod_cast h.ne'
  have hTr : (∑ i, rowSum A i) = ∑ i, ∑ j, A i j := rfl
  have hTc : (∑ j, colSum A j) = ∑ i, ∑ j, A i j := Finset.sum_comm
  have hr := esym_three_closed (rowSum A)
  have hc := esym_three_closed (colSum A)
  have hs := sigmaK_three_closed A
  rw [hTr] at hr
  rw [hTc] at hc
  have hr' : esym 3 (rowSum A)
      = ((∑ i, ∑ j, A i j) ^ 3 - 3 * (∑ i, ∑ j, A i j) * (∑ i, rowSum A i ^ 2)
          + 2 * ∑ i, rowSum A i ^ 3) / 6 := by linarith
  have hc' : esym 3 (colSum A)
      = ((∑ i, ∑ j, A i j) ^ 3 - 3 * (∑ i, ∑ j, A i j) * (∑ j, colSum A j ^ 2)
          + 2 * ∑ j, colSum A j ^ 3) / 6 := by linarith
  have hs' : sigmaK 3 A
      = ((∑ i, ∑ j, A i j) ^ 3
        - 3 * (∑ i, ∑ j, A i j) * ((∑ i, (∑ j, A i j) ^ 2) + (∑ j, (∑ i, A i j) ^ 2))
        + 3 * (∑ i, ∑ j, A i j ^ 2) * (∑ i, ∑ j, A i j)
        + 6 * (∑ i, ∑ j, A i j * (∑ l, A i l) * (∑ l, A l j))
        + 2 * (∑ i, (∑ j, A i j) ^ 3) + 2 * (∑ j, (∑ i, A i j) ^ 3)
        - 6 * (∑ i, ∑ j, A i j ^ 2 * (∑ l, A i l))
        - 6 * (∑ i, ∑ j, A i j ^ 2 * (∑ l, A l j))
        + 4 * (∑ i, ∑ j, A i j ^ 3)) / 6 := by linarith
  unfold Phi E P objPoly
  rw [hr', hc', hs']
  simp only [rowSum, colSum]
  field_simp
  ring

/-! ## 3i.  The identity

The two halves of the certificate identity, in the ten global invariants of the
centred coordinates.  Every coefficient here was emitted by
`leanproj/verify_H_identity.py` and checked there symbolically in `n` by full
coefficient comparison, never by sampling; `verify_H_identity.py` part 1 also checks
the local-to-global dictionary against the assembled Gram at `n = 4, 5, 6` at three
corners, with a mutation control. -/


/-! ## Stage E.  The identity

The ten global invariants of the centred coordinates, the local-to-global dictionary
at a corner, and the sum over corners.  Coefficients emitted by
`leanproj/verify_H_identity.py`. -/

section Globals

variable {n : ℕ} (b : Fin n × Fin n → ℝ)

def gRow (i : Fin n) : ℝ := ∑ j, b (i, j)
def gCol (j : Fin n) : ℝ := ∑ i, b (i, j)
def gRowSq (i : Fin n) : ℝ := ∑ j, b (i, j) ^ 2
def gColSq (j : Fin n) : ℝ := ∑ i, b (i, j) ^ 2
def gRowDot (i : Fin n) : ℝ := ∑ j, b (i, j) * gCol b j
def gColDot (j : Fin n) : ℝ := ∑ i, b (i, j) * gRow b i

def gS : ℝ := ∑ u, b u
def gT2 : ℝ := ∑ u, b u ^ 2
def gT3 : ℝ := ∑ u, b u ^ 3
def gSR2 : ℝ := ∑ i, gRow b i ^ 2
def gSC2 : ℝ := ∑ j, gCol b j ^ 2
def gSR3 : ℝ := ∑ i, gRow b i ^ 3
def gSC3 : ℝ := ∑ j, gCol b j ^ 3
def gM1 : ℝ := ∑ i, ∑ j, b (i, j) * gRow b i * gCol b j
def gM2 : ℝ := ∑ i, ∑ j, b (i, j) ^ 2 * gRow b i
def gM3 : ℝ := ∑ i, ∑ j, b (i, j) ^ 2 * gCol b j

theorem sum_gRow : (∑ i, gRow b i) = gS b := by
  unfold gS gRow; rw [Fintype.sum_prod_type]

theorem sum_gCol : (∑ j, gCol b j) = gS b := by
  unfold gS gCol; rw [Fintype.sum_prod_type, Finset.sum_comm]

theorem sum_gRowSq : (∑ i, gRowSq b i) = gT2 b := by
  unfold gT2 gRowSq; rw [Fintype.sum_prod_type]

theorem sum_gColSq : (∑ j, gColSq b j) = gT2 b := by
  unfold gT2 gColSq; rw [Fintype.sum_prod_type, Finset.sum_comm]

theorem sum_gRowDot : (∑ i, gRowDot b i) = gSC2 b := by
  unfold gRowDot gSC2
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_mul]
  unfold gCol
  ring

theorem sum_gColDot : (∑ j, gColDot b j) = gSR2 b := by
  unfold gColDot gSR2
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_mul]
  unfold gRow
  ring

/-! ### The twenty-three ways a sum over corners closes

A sum over corners `p = (a, c)` of any monomial in the corner's own value, in its row
and column sums, and in its row and column profiles, is one of the ten global
invariants.  The list is closed: `verify_H_identity.py` raises rather than silently
dropping a monomial outside it. -/

private theorem const_row (x : ℝ) : (∑ _c : Fin n, x) = (n : ℝ) * x := by
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

theorem sumP_b : (∑ a, ∑ c, b (a, c)) = gS b := by
  unfold gS; rw [Fintype.sum_prod_type]

theorem sumP_b2 : (∑ a, ∑ c, b (a, c) ^ 2) = gT2 b := by
  unfold gT2; rw [Fintype.sum_prod_type]

theorem sumP_b3 : (∑ a, ∑ c, b (a, c) ^ 3) = gT3 b := by
  unfold gT3; rw [Fintype.sum_prod_type]

theorem sumP_bRow : (∑ a, ∑ c, b (a, c) * gRow b a) = gSR2 b := by
  unfold gSR2
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_mul]
  unfold gRow
  ring

theorem sumP_bCol : (∑ a, ∑ c, b (a, c) * gCol b c) = gSC2 b := by
  rw [Finset.sum_comm]
  unfold gSC2
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← Finset.sum_mul]
  unfold gCol
  ring

theorem sumP_Row : (∑ a : Fin n, ∑ _c : Fin n, gRow b a) = (n : ℝ) * gS b := by
  rw [← sum_gRow b, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => const_row _

theorem sumP_Col : (∑ _a : Fin n, ∑ c : Fin n, gCol b c) = (n : ℝ) * gS b := by
  rw [Finset.sum_comm, ← sum_gCol b, Finset.mul_sum]
  exact Finset.sum_congr rfl fun c _ => const_row _

theorem sumP_Row2 : (∑ a : Fin n, ∑ _c : Fin n, gRow b a ^ 2) = (n : ℝ) * gSR2 b := by
  unfold gSR2
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => const_row _

theorem sumP_Col2 : (∑ _a : Fin n, ∑ c : Fin n, gCol b c ^ 2) = (n : ℝ) * gSC2 b := by
  rw [Finset.sum_comm]
  unfold gSC2
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun c _ => const_row _

theorem sumP_Row3 : (∑ a : Fin n, ∑ _c : Fin n, gRow b a ^ 3) = (n : ℝ) * gSR3 b := by
  unfold gSR3
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => const_row _

theorem sumP_Col3 : (∑ _a : Fin n, ∑ c : Fin n, gCol b c ^ 3) = (n : ℝ) * gSC3 b := by
  rw [Finset.sum_comm]
  unfold gSC3
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun c _ => const_row _

theorem sumP_RowCol :
    (∑ a : Fin n, ∑ c : Fin n, gRow b a * gCol b c) = gS b ^ 2 := by
  have h : gS b ^ 2 = (∑ a, gRow b a) * ∑ c, gCol b c := by
    rw [sum_gRow, sum_gCol, sq]
  rw [h, Finset.sum_mul_sum]

theorem sumP_RowSq : (∑ a : Fin n, ∑ _c : Fin n, gRowSq b a) = (n : ℝ) * gT2 b := by
  rw [← sum_gRowSq b, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => const_row _

theorem sumP_ColSq : (∑ _a : Fin n, ∑ c : Fin n, gColSq b c) = (n : ℝ) * gT2 b := by
  rw [Finset.sum_comm, ← sum_gColSq b, Finset.mul_sum]
  exact Finset.sum_congr rfl fun c _ => const_row _

theorem sumP_RowDot :
    (∑ a : Fin n, ∑ _c : Fin n, gRowDot b a) = (n : ℝ) * gSC2 b := by
  rw [← sum_gRowDot b, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => const_row _

theorem sumP_ColDot :
    (∑ _a : Fin n, ∑ c : Fin n, gColDot b c) = (n : ℝ) * gSR2 b := by
  rw [Finset.sum_comm, ← sum_gColDot b, Finset.mul_sum]
  exact Finset.sum_congr rfl fun c _ => const_row _

theorem sumP_b2Row : (∑ a, ∑ c, b (a, c) ^ 2 * gRow b a) = gM2 b := rfl

theorem sumP_b2Col : (∑ a, ∑ c, b (a, c) ^ 2 * gCol b c) = gM3 b := rfl

theorem sumP_bRowCol : (∑ a, ∑ c, b (a, c) * gRow b a * gCol b c) = gM1 b := rfl

theorem sumP_bRow2 : (∑ a, ∑ c, b (a, c) * gRow b a ^ 2) = gSR3 b := by
  unfold gSR3
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_mul]
  unfold gRow
  ring

theorem sumP_bCol2 : (∑ a, ∑ c, b (a, c) * gCol b c ^ 2) = gSC3 b := by
  rw [Finset.sum_comm]
  unfold gSC3
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← Finset.sum_mul]
  unfold gCol
  ring

theorem sumP_bRowSq : (∑ a, ∑ c, b (a, c) * gRowSq b a) = gM2 b := by
  unfold gM2
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [← Finset.sum_mul]
  unfold gRowSq gRow
  ring

theorem sumP_bColSq : (∑ a, ∑ c, b (a, c) * gColSq b c) = gM3 b := by
  have hR : gM3 b = ∑ c, ∑ a, b (a, c) ^ 2 * gCol b c := Finset.sum_comm
  rw [hR, Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [← Finset.sum_mul]
  unfold gColSq gCol
  ring

theorem sumP_bRowDot : (∑ a, ∑ c, b (a, c) * gRowDot b a) = gM1 b := by
  unfold gM1
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_mul]
  unfold gRowDot gRow
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem sumP_bColDot : (∑ a, ∑ c, b (a, c) * gColDot b c) = gM1 b := by
  have hR : gM1 b = ∑ c, ∑ a, b (a, c) * gRow b a * gCol b c := Finset.sum_comm
  rw [hR, Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← Finset.sum_mul]
  unfold gColDot gCol
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

end Globals

/-! ### The local-to-global dictionary at a corner

Every local coordinate of §3g is a global invariant corrected at the corner's own row
and column.  This is the shape `verify_H_identity.py` part 1 checks against the
assembled Gram at `n = 4, 5, 6`, at three corners, with a mutation control. -/

section Dictionary

variable {n : ℕ} (p : Fin n × Fin n) (b : Fin n × Fin n → ℝ)

theorem sum_zR_mul (X : Fin n → ℝ) : (∑ i, zR p i * X i) = (∑ i, X i) - X p.1 := by
  have step : ∀ i : Fin n, zR p i * X i
      = X i - (if i = p.1 then (1 : ℝ) else 0) * X i := by
    intro i; unfold zR; ring
  rw [Finset.sum_congr rfl fun i (_ : i ∈ univ) => step i, Finset.sum_sub_distrib]
  congr 1
  simp only [boole_mul]
  rw [Finset.sum_ite_eq' univ p.1 X]
  simp

theorem sum_zC_mul (Y : Fin n → ℝ) : (∑ j, zC p j * Y j) = (∑ j, Y j) - Y p.2 := by
  have step : ∀ j : Fin n, zC p j * Y j
      = Y j - (if j = p.2 then (1 : ℝ) else 0) * Y j := by
    intro j; unfold zC; ring
  rw [Finset.sum_congr rfl fun j (_ : j ∈ univ) => step j, Finset.sum_sub_distrib]
  congr 1
  simp only [boole_mul]
  rw [Finset.sum_ite_eq' univ p.2 Y]
  simp

theorem lKap_global : lKap p b = gCol b p.2 - b p := by
  rw [← sum_lE p b, Finset.sum_congr rfl fun i (_ : i ∈ univ) => lE_apply p b i,
    sum_zR_mul p (fun i => b (i, p.2))]
  rfl

theorem lRho_global : lRho p b = gRow b p.1 - b p := by
  rw [← sum_lF p b, Finset.sum_congr rfl fun j (_ : j ∈ univ) => lF_apply p b j,
    sum_zC_mul p (fun j => b (p.1, j))]
  rfl

theorem lTau_global : lTau p b = gS b - gRow b p.1 - gCol b p.2 + b p := by
  rw [← sum_lR p b, Finset.sum_congr rfl fun i (_ : i ∈ univ) => lR_apply p b i,
    sum_zR_mul p (fun i => (∑ j, b (i, j)) - b (i, p.2)), Finset.sum_sub_distrib]
  unfold gS gRow gCol
  rw [Fintype.sum_prod_type]
  ring

theorem sum_lE_sq_global : (∑ i, lE p b i ^ 2) = gColSq b p.2 - b p ^ 2 := by
  have step : ∀ i : Fin n, lE p b i ^ 2 = zR p i * b (i, p.2) ^ 2 := by
    intro i
    rw [lE_apply]
    linear_combination (b (i, p.2) ^ 2) * zR_idem p i
  rw [Finset.sum_congr rfl fun i (_ : i ∈ univ) => step i,
    sum_zR_mul p (fun i => b (i, p.2) ^ 2)]
  rfl

theorem sum_lF_sq_global : (∑ j, lF p b j ^ 2) = gRowSq b p.1 - b p ^ 2 := by
  have step : ∀ j : Fin n, lF p b j ^ 2 = zC p j * b (p.1, j) ^ 2 := by
    intro j
    rw [lF_apply]
    linear_combination (b (p.1, j) ^ 2) * zC_idem p j
  rw [Finset.sum_congr rfl fun j (_ : j ∈ univ) => step j,
    sum_zC_mul p (fun j => b (p.1, j) ^ 2)]
  rfl

theorem sum_lElR_global : (∑ i, lE p b i * lR p b i)
    = gColDot b p.2 - gColSq b p.2 - b p * gRow b p.1 + b p ^ 2 := by
  have step : ∀ i : Fin n, lE p b i * lR p b i
      = zR p i * (b (i, p.2) * gRow b i - b (i, p.2) ^ 2) := by
    intro i
    rw [lE_apply, lR_apply]
    have : gRow b i = ∑ j, b (i, j) := rfl
    rw [this]
    linear_combination (b (i, p.2) * ((∑ j, b (i, j)) - b (i, p.2))) * zR_idem p i
  rw [Finset.sum_congr rfl fun i (_ : i ∈ univ) => step i,
    sum_zR_mul p (fun i => b (i, p.2) * gRow b i - b (i, p.2) ^ 2),
    Finset.sum_sub_distrib]
  show gColDot b p.2 - gColSq b p.2 - (b (p.1, p.2) * gRow b p.1 - b (p.1, p.2) ^ 2)
      = _
  ring

theorem sum_lFlC_global : (∑ j, lF p b j * lC p b j)
    = gRowDot b p.1 - gRowSq b p.1 - b p * gCol b p.2 + b p ^ 2 := by
  have step : ∀ j : Fin n, lF p b j * lC p b j
      = zC p j * (b (p.1, j) * gCol b j - b (p.1, j) ^ 2) := by
    intro j
    rw [lF_apply, lC_apply]
    have : gCol b j = ∑ i, b (i, j) := rfl
    rw [this]
    linear_combination (b (p.1, j) * ((∑ i, b (i, j)) - b (p.1, j))) * zC_idem p j
  rw [Finset.sum_congr rfl fun j (_ : j ∈ univ) => step j,
    sum_zC_mul p (fun j => b (p.1, j) * gCol b j - b (p.1, j) ^ 2),
    Finset.sum_sub_distrib]
  show gRowDot b p.1 - gRowSq b p.1 - (b (p.1, p.2) * gCol b p.2 - b (p.1, p.2) ^ 2)
      = _
  ring

theorem sum_lR_sq_global : (∑ i, lR p b i ^ 2)
    = gSR2 b - 2 * gColDot b p.2 + gColSq b p.2 - (gRow b p.1 - b p) ^ 2 := by
  have step : ∀ i : Fin n, lR p b i ^ 2
      = zR p i * (gRow b i ^ 2 - 2 * (b (i, p.2) * gRow b i) + b (i, p.2) ^ 2) := by
    intro i
    rw [lR_apply]
    have : gRow b i = ∑ j, b (i, j) := rfl
    rw [this]
    linear_combination (((∑ j, b (i, j)) - b (i, p.2)) ^ 2) * zR_idem p i
  rw [Finset.sum_congr rfl fun i (_ : i ∈ univ) => step i,
    sum_zR_mul p (fun i => gRow b i ^ 2 - 2 * (b (i, p.2) * gRow b i) + b (i, p.2) ^ 2),
    Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  show gSR2 b - 2 * gColDot b p.2 + gColSq b p.2
      - (gRow b p.1 ^ 2 - 2 * (b (p.1, p.2) * gRow b p.1) + b (p.1, p.2) ^ 2) = _
  ring

theorem sum_lC_sq_global : (∑ j, lC p b j ^ 2)
    = gSC2 b - 2 * gRowDot b p.1 + gRowSq b p.1 - (gCol b p.2 - b p) ^ 2 := by
  have step : ∀ j : Fin n, lC p b j ^ 2
      = zC p j * (gCol b j ^ 2 - 2 * (b (p.1, j) * gCol b j) + b (p.1, j) ^ 2) := by
    intro j
    rw [lC_apply]
    have : gCol b j = ∑ i, b (i, j) := rfl
    rw [this]
    linear_combination (((∑ i, b (i, j)) - b (p.1, j)) ^ 2) * zC_idem p j
  rw [Finset.sum_congr rfl fun j (_ : j ∈ univ) => step j,
    sum_zC_mul p (fun j => gCol b j ^ 2 - 2 * (b (p.1, j) * gCol b j) + b (p.1, j) ^ 2),
    Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  show gSC2 b - 2 * gRowDot b p.1 + gRowSq b p.1
      - (gCol b p.2 ^ 2 - 2 * (b (p.1, p.2) * gCol b p.2) + b (p.1, p.2) ^ 2) = _
  ring

theorem lB2_global :
    lB2 p b = gT2 b - gRowSq b p.1 - gColSq b p.2 + b p ^ 2 := by
  rw [← sum_bodyX_sq p b]
  have inner : ∀ i : Fin n, (∑ j, bodyX p b i j ^ 2)
      = zR p i * (gRowSq b i - b (i, p.2) ^ 2) := by
    intro i
    have step : ∀ j : Fin n, bodyX p b i j ^ 2 = zR p i * (zC p j * b (i, j) ^ 2) := by
      intro j
      unfold bodyX
      rw [iB_eq]
      linear_combination (zC p j ^ 2 * b (i, j) ^ 2) * zR_idem p i
        + (zR p i * b (i, j) ^ 2) * zC_idem p j
    rw [Finset.sum_congr rfl fun j (_ : j ∈ univ) => step j, ← Finset.mul_sum,
      sum_zC_mul p (fun j => b (i, j) ^ 2)]
    rfl
  rw [Finset.sum_congr rfl fun i (_ : i ∈ univ) => inner i,
    sum_zR_mul p (fun i => gRowSq b i - b (i, p.2) ^ 2), Finset.sum_sub_distrib,
    sum_gRowSq b]
  show gT2 b - gColSq b p.2 - (gRowSq b p.1 - b (p.1, p.2) ^ 2) = _
  ring

/-- **The quadratic form at a corner, entirely in global invariants.**  Nothing local
survives: every term is one of `b p`, the corner's row and column sums, its row and
column profiles, and the constants `gS`, `gT2`, `gSR2`, `gSC2`. -/
theorem quadForm_Hm_global :
    Certificate.quadForm (Hm n p) b
      = hh0 (n : ℝ) * b p ^ 2
        + 2 * hh0 (n : ℝ) * b p * ((gCol b p.2 - b p) + (gRow b p.1 - b p))
        + 2 * hh0 (n : ℝ) * b p * (gS b - gRow b p.1 - gCol b p.2 + b p)
        + hh4 (n : ℝ) * ((gCol b p.2 - b p) ^ 2 + (gRow b p.1 - b p) ^ 2)
        + 2 * hh5 (n : ℝ) * ((gCol b p.2 - b p) * (gRow b p.1 - b p))
        + 2 * hh7 (n : ℝ) * (((gCol b p.2 - b p) + (gRow b p.1 - b p))
            * (gS b - gRow b p.1 - gCol b p.2 + b p))
        + hh10 (n : ℝ) * (gS b - gRow b p.1 - gCol b p.2 + b p) ^ 2
        + hAq (n : ℝ) * ((gColSq b p.2 - b p ^ 2) + (gRowSq b p.1 - b p ^ 2))
        + 2 * hBq (n : ℝ)
            * ((gColDot b p.2 - gColSq b p.2 - b p * gRow b p.1 + b p ^ 2)
              + (gRowDot b p.1 - gRowSq b p.1 - b p * gCol b p.2 + b p ^ 2))
        + hCq (n : ℝ)
            * ((gSR2 b - 2 * gColDot b p.2 + gColSq b p.2 - (gRow b p.1 - b p) ^ 2)
              + (gSC2 b - 2 * gRowDot b p.1 + gRowSq b p.1 - (gCol b p.2 - b p) ^ 2))
        + hGg (n : ℝ) * (gT2 b - gRowSq b p.1 - gColSq b p.2 + b p ^ 2) := by
  rw [quadForm_Hm, lKap_global, lRho_global, lTau_global, ← sum_lE_sq, ← sum_lF_sq,
    sum_lE_sq_global, sum_lF_sq_global, sum_lElR_global, sum_lFlC_global,
    sum_lR_sq_global, sum_lC_sq_global, lB2_global]

end Dictionary


/-! ### The seven coefficients, and the sum over corners

Expanded in the monomials of the corner, `sigma_p` has only seven distinct
coefficients, and `sigma_p * b_p` has the same seven: the cubic is the quadratic times
`b_p` monomial by monomial.  Emitted by `verify_H_identity.py`. -/

section SumOverCorners

variable {n : ℕ} (b : Fin n × Fin n → ℝ)

def kB2 (x : ℝ) : ℝ :=
  -2 * hAq x + 4 * hBq x - 2 * hCq x + hGg x - hh0 x + hh10 x + 2 * hh4 x + 2 * hh5 x
    - 4 * hh7 x
def kBL (x : ℝ) : ℝ :=
  -2 * (hBq x - hCq x + hh10 x + hh4 x + hh5 x - 3 * hh7 x)
def kL2 (x : ℝ) : ℝ := -hCq x + hh10 x + hh4 x - 2 * hh7 x
def kRC (x : ℝ) : ℝ := 2 * (hh10 x + hh5 x - 2 * hh7 x)
def kSq (x : ℝ) : ℝ := hAq x - 2 * hBq x + hCq x - hGg x
def kDot (x : ℝ) : ℝ := 2 * (hBq x - hCq x)

/-- The constant term: the only place `gT2`, `gSR2`, `gSC2` enter a single corner. -/
def kC (x : ℝ) (b : Fin n × Fin n → ℝ) : ℝ :=
  hCq x * (gSC2 b + gSR2 b) + hGg x * gT2 b

theorem sumP_const (x : ℝ) : (∑ _a : Fin n, ∑ _c : Fin n, x) = (n : ℝ) ^ 2 * x := by
  rw [Finset.sum_congr rfl fun a (_ : a ∈ univ) => const_row x, const_row ((n : ℝ) * x)]
  ring

theorem sumP_one : (∑ _a : Fin n, ∑ _c : Fin n, (1 : ℝ)) = (n : ℝ) ^ 2 := by
  rw [sumP_const]; ring

/-- **The quadratic form at a corner, as a combination of the twenty-four monomials.**
Valid on `K_n`, where `∑ b = 0`. -/
theorem quadForm_Hm_mono (a c : Fin n) (hS : gS b = 0) :
    Certificate.quadForm (Hm n (a, c)) b
      = kB2 (n : ℝ) * b (a, c) ^ 2
        + kBL (n : ℝ) * (b (a, c) * gRow b a)
        + kBL (n : ℝ) * (b (a, c) * gCol b c)
        + kL2 (n : ℝ) * gRow b a ^ 2
        + kL2 (n : ℝ) * gCol b c ^ 2
        + kRC (n : ℝ) * (gRow b a * gCol b c)
        + kSq (n : ℝ) * gColSq b c
        + kSq (n : ℝ) * gRowSq b a
        + kDot (n : ℝ) * gColDot b c
        + kDot (n : ℝ) * gRowDot b a
        + kC (n : ℝ) b := by
  rw [quadForm_Hm_global (a, c) b, hS]
  unfold kB2 kBL kL2 kRC kSq kDot kC hAq hBq hCq hGg
  ring

theorem quadForm_Hm_mono_mul (a c : Fin n) (hS : gS b = 0) :
    Certificate.quadForm (Hm n (a, c)) b * b (a, c)
      = kB2 (n : ℝ) * b (a, c) ^ 3
        + kBL (n : ℝ) * (b (a, c) ^ 2 * gRow b a)
        + kBL (n : ℝ) * (b (a, c) ^ 2 * gCol b c)
        + kL2 (n : ℝ) * (b (a, c) * gRow b a ^ 2)
        + kL2 (n : ℝ) * (b (a, c) * gCol b c ^ 2)
        + kRC (n : ℝ) * (b (a, c) * gRow b a * gCol b c)
        + kSq (n : ℝ) * (b (a, c) * gColSq b c)
        + kSq (n : ℝ) * (b (a, c) * gRowSq b a)
        + kDot (n : ℝ) * (b (a, c) * gColDot b c)
        + kDot (n : ℝ) * (b (a, c) * gRowDot b a)
        + kC (n : ℝ) b * b (a, c) := by
  rw [quadForm_Hm_mono b a c hS]
  ring

/-- **`∑_p sigma_p(b)`**, in the global invariants. -/
theorem sumP_quadForm_lin (hS : gS b = 0) :
    (∑ p : Fin n × Fin n, Certificate.quadForm (Hm n p) b)
      = kB2 (n : ℝ) * gT2 b
        + kBL (n : ℝ) * gSR2 b + kBL (n : ℝ) * gSC2 b
        + kL2 (n : ℝ) * ((n : ℝ) * gSR2 b) + kL2 (n : ℝ) * ((n : ℝ) * gSC2 b)
        + kRC (n : ℝ) * gS b ^ 2
        + kSq (n : ℝ) * ((n : ℝ) * gT2 b) + kSq (n : ℝ) * ((n : ℝ) * gT2 b)
        + kDot (n : ℝ) * ((n : ℝ) * gSR2 b) + kDot (n : ℝ) * ((n : ℝ) * gSC2 b)
        + (n : ℝ) ^ 2 * kC (n : ℝ) b := by
  rw [Fintype.sum_prod_type,
    Finset.sum_congr rfl fun a (_ : a ∈ univ) =>
      Finset.sum_congr rfl fun c (_ : c ∈ univ) => quadForm_Hm_mono b a c hS]
  have hRC : (∑ a : Fin n, gRow b a * ∑ c : Fin n, gCol b c) = gS b ^ 2 := by
    rw [← Finset.sum_mul, sum_gRow, sum_gCol, sq]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [sumP_b2, sumP_bRow, sumP_bCol, sumP_Row2, sumP_Col2, hRC, sumP_ColSq,
    sumP_RowSq, sumP_ColDot, sumP_RowDot, sumP_const]

/-- **`∑_p sigma_p(b)·b_p`**, in the global invariants. -/
theorem sumP_quadForm_cub (hS : gS b = 0) :
    (∑ p : Fin n × Fin n, Certificate.quadForm (Hm n p) b * b p)
      = kB2 (n : ℝ) * gT3 b
        + kBL (n : ℝ) * gM2 b + kBL (n : ℝ) * gM3 b
        + kL2 (n : ℝ) * gSR3 b + kL2 (n : ℝ) * gSC3 b
        + kRC (n : ℝ) * gM1 b
        + kSq (n : ℝ) * gM3 b + kSq (n : ℝ) * gM2 b
        + kDot (n : ℝ) * gM1 b + kDot (n : ℝ) * gM1 b
        + kC (n : ℝ) b * gS b := by
  rw [Fintype.sum_prod_type,
    Finset.sum_congr rfl fun a (_ : a ∈ univ) =>
      Finset.sum_congr rfl fun c (_ : c ∈ univ) => quadForm_Hm_mono_mul b a c hS]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [sumP_b3, sumP_b2Row, sumP_b2Col, sumP_bRow2, sumP_bCol2, sumP_bRowCol,
    sumP_bColSq, sumP_bRowSq, sumP_bColDot, sumP_bRowDot, sumP_b]

end SumOverCorners


/-! ### The objective in the same invariants -/

section ObjSide

variable {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)

theorem centre_add (i j : Fin n) : A i j = centre n A (i, j) + 1 / (n : ℝ) := by
  unfold centre; ring

theorem hrow (hn0 : (n : ℝ) ≠ 0) (i : Fin n) :
    (∑ j, A i j) = gRow (centre n A) i + 1 := by
  rw [Finset.sum_congr rfl fun j (_ : j ∈ univ) => centre_add A i j,
    Finset.sum_add_distrib, const_row]
  unfold gRow
  field_simp

theorem hcol (hn0 : (n : ℝ) ≠ 0) (j : Fin n) :
    (∑ i, A i j) = gCol (centre n A) j + 1 := by
  rw [Finset.sum_congr rfl fun i (_ : i ∈ univ) => centre_add A i j,
    Finset.sum_add_distrib, const_row]
  unfold gCol
  field_simp

theorem objS1 (hn0 : (n : ℝ) ≠ 0) :
    (∑ i, ∑ j, A i j) = gS (centre n A) + (n : ℝ) := by
  rw [Finset.sum_congr rfl fun i (_ : i ∈ univ) => hrow A hn0 i, Finset.sum_add_distrib,
    sum_gRow, const_row]
  ring

theorem objS2r (hn0 : (n : ℝ) ≠ 0) :
    (∑ i, (∑ j, A i j) ^ 2)
      = gSR2 (centre n A) + 2 * gS (centre n A) + (n : ℝ) := by
  have step : ∀ i : Fin n, (∑ j, A i j) ^ 2
      = gRow (centre n A) i ^ 2 + 2 * gRow (centre n A) i + 1 := by
    intro i; rw [hrow A hn0 i]; ring
  rw [Finset.sum_congr rfl fun i (_ : i ∈ univ) => step i]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [sum_gRow, const_row]
  unfold gSR2
  ring

theorem objS2c (hn0 : (n : ℝ) ≠ 0) :
    (∑ j, (∑ i, A i j) ^ 2)
      = gSC2 (centre n A) + 2 * gS (centre n A) + (n : ℝ) := by
  have step : ∀ j : Fin n, (∑ i, A i j) ^ 2
      = gCol (centre n A) j ^ 2 + 2 * gCol (centre n A) j + 1 := by
    intro j; rw [hcol A hn0 j]; ring
  rw [Finset.sum_congr rfl fun j (_ : j ∈ univ) => step j]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [sum_gCol, const_row]
  unfold gSC2
  ring

theorem objS3r (hn0 : (n : ℝ) ≠ 0) :
    (∑ i, (∑ j, A i j) ^ 3)
      = gSR3 (centre n A) + 3 * gSR2 (centre n A) + 3 * gS (centre n A) + (n : ℝ) := by
  have step : ∀ i : Fin n, (∑ j, A i j) ^ 3
      = gRow (centre n A) i ^ 3 + 3 * gRow (centre n A) i ^ 2
        + 3 * gRow (centre n A) i + 1 := by
    intro i; rw [hrow A hn0 i]; ring
  rw [Finset.sum_congr rfl fun i (_ : i ∈ univ) => step i]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [sum_gRow, const_row]
  unfold gSR3 gSR2
  ring

theorem objS3c (hn0 : (n : ℝ) ≠ 0) :
    (∑ j, (∑ i, A i j) ^ 3)
      = gSC3 (centre n A) + 3 * gSC2 (centre n A) + 3 * gS (centre n A) + (n : ℝ) := by
  have step : ∀ j : Fin n, (∑ i, A i j) ^ 3
      = gCol (centre n A) j ^ 3 + 3 * gCol (centre n A) j ^ 2
        + 3 * gCol (centre n A) j + 1 := by
    intro j; rw [hcol A hn0 j]; ring
  rw [Finset.sum_congr rfl fun j (_ : j ∈ univ) => step j]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [sum_gCol, const_row]
  unfold gSC3 gSC2
  ring

theorem objA2 (hn0 : (n : ℝ) ≠ 0) :
    (∑ i, ∑ j, A i j ^ 2)
      = gT2 (centre n A) + 2 / (n : ℝ) * gS (centre n A) + 1 := by
  have step : ∀ i j : Fin n, A i j ^ 2
      = centre n A (i, j) ^ 2 + 2 / (n : ℝ) * centre n A (i, j) + 1 / (n : ℝ) ^ 2 := by
    intro i j; rw [centre_add A i j]; field_simp; ring
  rw [Finset.sum_congr rfl fun i (_ : i ∈ univ) =>
    Finset.sum_congr rfl fun j (_ : j ∈ univ) => step i j]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [sumP_b2, sumP_b, sumP_const]
  field_simp

theorem objA3 (hn0 : (n : ℝ) ≠ 0) :
    (∑ i, ∑ j, A i j ^ 3)
      = gT3 (centre n A) + 3 / (n : ℝ) * gT2 (centre n A)
        + 3 / (n : ℝ) ^ 2 * gS (centre n A) + 1 / (n : ℝ) := by
  have step : ∀ i j : Fin n, A i j ^ 3
      = centre n A (i, j) ^ 3 + 3 / (n : ℝ) * centre n A (i, j) ^ 2
        + 3 / (n : ℝ) ^ 2 * centre n A (i, j) + 1 / (n : ℝ) ^ 3 := by
    intro i j; rw [centre_add A i j]; field_simp; ring
  rw [Finset.sum_congr rfl fun i (_ : i ∈ univ) =>
    Finset.sum_congr rfl fun j (_ : j ∈ univ) => step i j]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [sumP_b3, sumP_b2, sumP_b, sumP_const]
  field_simp
  ring

theorem objA2r (hn0 : (n : ℝ) ≠ 0) :
    (∑ i, ∑ j, A i j ^ 2 * (∑ l, A i l))
      = gM2 (centre n A) + gT2 (centre n A) + 2 / (n : ℝ) * gSR2 (centre n A)
        + 3 / (n : ℝ) * gS (centre n A) + 1 := by
  have step : ∀ i j : Fin n, A i j ^ 2 * (∑ l, A i l)
      = centre n A (i, j) ^ 2 * gRow (centre n A) i + centre n A (i, j) ^ 2
        + 2 / (n : ℝ) * (centre n A (i, j) * gRow (centre n A) i)
        + 2 / (n : ℝ) * centre n A (i, j)
        + 1 / (n : ℝ) ^ 2 * gRow (centre n A) i + 1 / (n : ℝ) ^ 2 := by
    intro i j; rw [centre_add A i j, hrow A hn0 i]; field_simp; ring
  rw [Finset.sum_congr rfl fun i (_ : i ∈ univ) =>
    Finset.sum_congr rfl fun j (_ : j ∈ univ) => step i j]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [sumP_b2Row, sumP_b2, sumP_bRow, sumP_b, sumP_Row, sumP_const]
  field_simp
  ring

theorem objA2c (hn0 : (n : ℝ) ≠ 0) :
    (∑ i, ∑ j, A i j ^ 2 * (∑ l, A l j))
      = gM3 (centre n A) + gT2 (centre n A) + 2 / (n : ℝ) * gSC2 (centre n A)
        + 3 / (n : ℝ) * gS (centre n A) + 1 := by
  have step : ∀ i j : Fin n, A i j ^ 2 * (∑ l, A l j)
      = centre n A (i, j) ^ 2 * gCol (centre n A) j + centre n A (i, j) ^ 2
        + 2 / (n : ℝ) * (centre n A (i, j) * gCol (centre n A) j)
        + 2 / (n : ℝ) * centre n A (i, j)
        + 1 / (n : ℝ) ^ 2 * gCol (centre n A) j + 1 / (n : ℝ) ^ 2 := by
    intro i j; rw [centre_add A i j, hcol A hn0 j]; field_simp; ring
  rw [Finset.sum_congr rfl fun i (_ : i ∈ univ) =>
    Finset.sum_congr rfl fun j (_ : j ∈ univ) => step i j]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [sumP_b2Col, sumP_b2, sumP_bCol, sumP_b, sumP_Col, sumP_const]
  field_simp
  ring

theorem objArc (hn0 : (n : ℝ) ≠ 0) :
    (∑ i, ∑ j, A i j * (∑ l, A i l) * (∑ l, A l j))
      = gM1 (centre n A) + gSR2 (centre n A) + gSC2 (centre n A)
        + 3 * gS (centre n A) + 1 / (n : ℝ) * gS (centre n A) ^ 2 + (n : ℝ) := by
  have step : ∀ i j : Fin n, A i j * (∑ l, A i l) * (∑ l, A l j)
      = centre n A (i, j) * gRow (centre n A) i * gCol (centre n A) j
        + centre n A (i, j) * gRow (centre n A) i
        + centre n A (i, j) * gCol (centre n A) j
        + centre n A (i, j)
        + 1 / (n : ℝ) * (gRow (centre n A) i * gCol (centre n A) j)
        + 1 / (n : ℝ) * gRow (centre n A) i
        + 1 / (n : ℝ) * gCol (centre n A) j
        + 1 / (n : ℝ) := by
    intro i j; rw [centre_add A i j, hrow A hn0 i, hcol A hn0 j]; field_simp; ring
  have hRC : (∑ a : Fin n, gRow (centre n A) a * ∑ c : Fin n, gCol (centre n A) c)
      = gS (centre n A) ^ 2 := by
    rw [← Finset.sum_mul, sum_gRow, sum_gCol, sq]
  rw [Finset.sum_congr rfl fun i (_ : i ∈ univ) =>
    Finset.sum_congr rfl fun j (_ : j ∈ univ) => step i j]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [sumP_bRowCol, sumP_bRow, sumP_bCol, sumP_b, hRC, sumP_Row, sumP_Col, sumP_const]
  field_simp
  ring

theorem choose3_cast {n : ℕ} (hn : 3 ≤ n) :
    (6 : ℝ) * (n.choose 3 : ℝ) = (n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  have hd := Nat.descFactorial_eq_factorial_mul_choose (m + 3) 3
  have h : (m + 1) * ((m + 2) * ((m + 3) * 1)) = 6 * (m + 3).choose 3 := by
    simpa [Nat.descFactorial, Nat.factorial] using hd
  have h' : ((m + 1 : ℕ) : ℝ) * (((m + 2 : ℕ) : ℝ) * (((m + 3 : ℕ) : ℝ) * 1))
      = 6 * ((m + 3).choose 3 : ℝ) := by exact_mod_cast congrArg (fun t : ℕ => (t : ℝ)) h
  push_cast at h'
  push_cast
  linarith

theorem gS_centre (hn0 : (n : ℝ) ≠ 0) (hA : A ∈ Kn n) : gS (centre n A) = 0 := by
  have h : (∑ i, ∑ j, A i j) = (n : ℝ) := hA.2
  unfold gS
  rw [Fintype.sum_prod_type]
  have step : ∀ i : Fin n, (∑ j, centre n A (i, j)) = (∑ j, A i j) - 1 := by
    intro i
    unfold centre
    rw [Finset.sum_sub_distrib, const_row]
    field_simp
  rw [Finset.sum_congr rfl fun i (_ : i ∈ univ) => step i, Finset.sum_sub_distrib,
    const_row, h]
  ring

/-- **The objective, in the ten global invariants of the centred coordinates.** -/
theorem objPoly_global (hn0 : (n : ℝ) ≠ 0) (hS : gS (centre n A) = 0) :
    objPoly n A
      = 2 - 6 / (n : ℝ) ^ 3
        - (2 * (n : ℝ) ^ 3
            - 3 * (n : ℝ) * ((gSR2 (centre n A) + (n : ℝ)) + (gSC2 (centre n A) + (n : ℝ)))
            + 2 * (gSR3 (centre n A) + 3 * gSR2 (centre n A) + (n : ℝ))
            + 2 * (gSC3 (centre n A) + 3 * gSC2 (centre n A) + (n : ℝ)))
          / (6 * (n.choose 3 : ℝ))
        + ((n : ℝ) ^ 3
            - 3 * (n : ℝ) * ((gSR2 (centre n A) + (n : ℝ)) + (gSC2 (centre n A) + (n : ℝ)))
            + 3 * (gT2 (centre n A) + 1) * (n : ℝ)
            + 6 * (gM1 (centre n A) + gSR2 (centre n A) + gSC2 (centre n A) + (n : ℝ))
            + 2 * (gSR3 (centre n A) + 3 * gSR2 (centre n A) + (n : ℝ))
            + 2 * (gSC3 (centre n A) + 3 * gSC2 (centre n A) + (n : ℝ))
            - 6 * (gM2 (centre n A) + gT2 (centre n A)
                + 2 / (n : ℝ) * gSR2 (centre n A) + 1)
            - 6 * (gM3 (centre n A) + gT2 (centre n A)
                + 2 / (n : ℝ) * gSC2 (centre n A) + 1)
            + 4 * (gT3 (centre n A) + 3 / (n : ℝ) * gT2 (centre n A) + 1 / (n : ℝ)))
          / (6 * (n.choose 3 : ℝ) ^ 2) := by
  unfold objPoly
  rw [objS1 A hn0, objS2r A hn0, objS2c A hn0, objS3r A hn0, objS3c A hn0,
    objA2 A hn0, objArc A hn0, objA2r A hn0, objA2c A hn0, objA3 A hn0, hS]
  ring

/-! ### The reduced coefficients

The one giant `field_simp` over all nine orbit values at once needs 13 GB, so the
cancellation is done one variable at a time instead: each coefficient of the final
identity is reduced on its own, and the identity is then assembled by
`linear_combination`.  Groupings verified in `verify_H_identity.py`. -/

section Coefficients

variable {x : ℝ}

/-- The common denominator of the cubic coefficients. -/
def cD (x : ℝ) : ℝ := x ^ 2 * (x - 2) ^ 2 * (x - 1) ^ 2

def cT2 (x : ℝ) : ℝ :=
  (17 * x ^ 4 - 54 * x ^ 3 - 4 * x ^ 2 + 84 * x - 40) / (x ^ 4 * (x - 2) * (x - 1) ^ 3)

def cSR (x : ℝ) : ℝ :=
  (3 * x ^ 9 - 19 * x ^ 8 + 40 * x ^ 7 - 3 * x ^ 6 - 153 * x ^ 5 + 353 * x ^ 4
      - 358 * x ^ 3 + 52 * x ^ 2 + 168 * x - 80) / (x ^ 5 * (x - 2) ^ 2 * (x - 1) ^ 3)

theorem coefT3 (h0 : x ≠ 0) (h1 : x - 1 ≠ 0) (h2 : x - 2 ≠ 0) :
    kB2 x = 24 / cD x := by
  unfold kB2 cD hAq hBq hCq hGg hh0 hh3 hh4 hh5 hh6 hh7 hh8 hh9 hh10
  field_simp
  ring

theorem coefM23 (h0 : x ≠ 0) (h1 : x - 1 ≠ 0) (h2 : x - 2 ≠ 0) :
    kBL x + kSq x = -36 / cD x := by
  unfold kBL kSq cD hAq hBq hCq hGg hh3 hh4 hh5 hh6 hh7 hh8 hh9 hh10
  field_simp
  ring

theorem coefR3 (h0 : x ≠ 0) (h1 : x - 1 ≠ 0) (h2 : x - 2 ≠ 0) :
    kL2 x = (-2 * x ^ 3 + 6 * x ^ 2 - 4 * x + 12) / cD x := by
  unfold kL2 cD hCq hh4 hh7 hh9 hh10
  field_simp
  ring

theorem coefM1 (h0 : x ≠ 0) (h1 : x - 1 ≠ 0) (h2 : x - 2 ≠ 0) :
    kRC x + 2 * kDot x = 36 / cD x := by
  unfold kRC kDot cD hBq hCq hh5 hh6 hh7 hh9 hh10
  field_simp
  ring

theorem coefT2 (h0 : x ≠ 0) (h1 : x - 1 ≠ 0) (h2 : x - 2 ≠ 0) :
    kB2 x + 2 * x * kSq x + x ^ 2 * hGg x = cT2 x := by
  unfold kB2 kSq cT2 hAq hBq hCq hGg hh0 hh3 hh4 hh5 hh6 hh7 hh8 hh9 hh10
  field_simp
  ring

theorem coefSR2 (h0 : x ≠ 0) (h1 : x - 1 ≠ 0) (h2 : x - 2 ≠ 0) :
    kBL x + x * kL2 x + x * kDot x + x ^ 2 * hCq x = cSR x := by
  unfold kBL kL2 kDot cSR hBq hCq hh4 hh5 hh6 hh7 hh9 hh10
  field_simp
  ring

end Coefficients

/-! ### The two sums over corners, reduced -/

section Reduced

variable {n : ℕ} (b : Fin n × Fin n → ℝ)

theorem sumP_lin_reduced (hS : gS b = 0) (h0 : (n : ℝ) ≠ 0) (h1 : (n : ℝ) - 1 ≠ 0)
    (h2 : (n : ℝ) - 2 ≠ 0) :
    (∑ p : Fin n × Fin n, Certificate.quadForm (Hm n p) b)
      = cT2 (n : ℝ) * gT2 b + cSR (n : ℝ) * (gSR2 b + gSC2 b) := by
  rw [sumP_quadForm_lin b hS, hS]
  unfold kC
  linear_combination gT2 b * coefT2 h0 h1 h2 + (gSR2 b + gSC2 b) * coefSR2 h0 h1 h2

theorem sumP_cub_reduced (hS : gS b = 0) (h0 : (n : ℝ) ≠ 0) (h1 : (n : ℝ) - 1 ≠ 0)
    (h2 : (n : ℝ) - 2 ≠ 0) :
    (∑ p : Fin n × Fin n, Certificate.quadForm (Hm n p) b * b p)
      = (24 * gT3 b
          + (-2 * (n : ℝ) ^ 3 + 6 * (n : ℝ) ^ 2 - 4 * (n : ℝ) + 12) * (gSR3 b + gSC3 b)
          + 36 * gM1 b - 36 * (gM2 b + gM3 b)) / cD (n : ℝ) := by
  rw [sumP_quadForm_cub b hS, hS]
  linear_combination gT3 b * coefT3 h0 h1 h2 + (gM2 b + gM3 b) * coefM23 h0 h1 h2
    + (gSR3 b + gSC3 b) * coefR3 h0 h1 h2 + gM1 b * coefM1 h0 h1 h2

end Reduced

/-! ### The identity -/

set_option maxHeartbeats 2000000 in
/-- **The certificate identity, proved.** -/
theorem certificate_identity_proved (hn : 4 ≤ n) (hA : A ∈ Kn n) :
    objPoly n A
      = Certificate.quadForm (G0 n) (centre n A)
        + ∑ p : Fin n × Fin n,
            Certificate.quadForm (Hm n p) (centre n A) * A p.1 p.2 := by
  have hnR : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by intro h; rw [h] at hnR; linarith
  have hn1 : ((n : ℝ) - 1) ≠ 0 := by intro h; apply absurd hnR; linarith [h]
  have hn2 : ((n : ℝ) - 2) ≠ 0 := by intro h; apply absurd hnR; linarith [h]
  have hS := gS_centre A hn0 hA
  have hAp : ∀ p : Fin n × Fin n, A p.1 p.2 = centre n A p + 1 / (n : ℝ) := by
    intro p; unfold centre; ring
  have hsplit :
      (∑ p : Fin n × Fin n, Certificate.quadForm (Hm n p) (centre n A) * A p.1 p.2)
        = (∑ p : Fin n × Fin n,
            Certificate.quadForm (Hm n p) (centre n A) * centre n A p)
          + 1 / (n : ℝ)
            * ∑ p : Fin n × Fin n, Certificate.quadForm (Hm n p) (centre n A) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun p _ => by rw [hAp p]; ring
  have hG0 : Certificate.quadForm (G0 n) (centre n A)
      = c0Total (n : ℝ) * gS (centre n A) ^ 2
        + c0Line (n : ℝ) * (gSR2 (centre n A) + gSC2 (centre n A))
        + theta2 (n : ℝ) * gT2 (centre n A) := quadForm_G0 n (centre n A)
  have hc : (n.choose 3 : ℝ) = (n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2) / 6 := by
    have := choose3_cast (le_trans (by norm_num) hn)
    linarith
  have hcl : c0Line (n : ℝ)
      = ((n : ℝ) ^ 8 - (n : ℝ) ^ 7 - 51 * (n : ℝ) ^ 6 + 255 * (n : ℝ) ^ 5
          - 497 * (n : ℝ) ^ 4 + 430 * (n : ℝ) ^ 3 - 52 * (n : ℝ) ^ 2 - 168 * (n : ℝ) + 80)
        / ((n : ℝ) ^ 6 * ((n : ℝ) - 1) ^ 3 * ((n : ℝ) - 2) ^ 2) := by
    unfold c0Line c0LineNum c0LineDen
    congr 1
    ring
  have hth : theta2 (n : ℝ)
      = ((n : ℝ) ^ 4 + 40 * (n : ℝ) ^ 2 - 84 * (n : ℝ) + 40)
        / ((n : ℝ) ^ 5 * ((n : ℝ) - 1) ^ 3 * ((n : ℝ) - 2)) := by
    unfold theta2 theta2Num theta2Den
    congr 1
    ring
  rw [hsplit, hG0, sumP_cub_reduced (centre n A) hS hn0 hn1 hn2,
    sumP_lin_reduced (centre n A) hS hn0 hn1 hn2, objPoly_global A hn0 hS, hS, hc,
    hcl, hth]
  unfold cD cT2 cSR
  field_simp
  ring

end ObjSide
/-- **The Positivstellensatz identity of the certificate, proved.**

    objPoly n A  =  quadForm (G0 n) b  +  ∑_p a_p · σ_p(b)          on `K_n`,

with `b = A − J_n/n` the centred coordinates, `σ_p = quadForm (Hm n p)`, and `a_p` the
entries of `A`.  The multiplier `λ(b)·(∑_q b_q)` of the full certificate does not
appear because `∑_q b_q = 0` on `K_n`, which is what `gS_centre` supplies.

**How it is proved.**  Both sides are cubic in `n²` variables with coefficients
rational in `n`, so no instance of `ring` sees the statement whole.  §3i expands each
side in the ten global invariants of `b` — `gT2, gT3, gSR2, gSC2, gSR3, gSC3, gM1,
gM2, gM3` and `gS` — and compares coefficients:

* `quadForm_Hm_global` rewrites `σ_p` at a single corner with every local quantity
  replaced by a global invariant corrected at that corner's own row and column;
* the twenty-three `sumP_*` lemmas close the list of monomials in the corner: a sum
  over corners of any one of them is one of the ten invariants;
* `sumP_lin_reduced` and `sumP_cub_reduced` give, with `∑ b = 0`,

      ∑_p σ_p(b)      = cT2·gT2 + cSR·(gSR2 + gSC2),
      ∑_p σ_p(b)·b_p  = (24·gT3 − (2n³−6n²+4n−12)(gSR3 + gSC3)
                          + 36·gM1 − 36·(gM2 + gM3)) / (n²(n−2)²(n−1)²);

* `objPoly_global` expands the objective in the same invariants.

**Why the algebra is staged.**  Reducing all nine orbit values at once needs 13 GB of
elaborator memory.  The six coefficient identities of §3i are one-variable rational
identities, reduced separately, and the assembly is a `linear_combination` of them;
that route peaks near 3.7 GB.  Note also that `c0Line` and `theta2` must be rewritten
into FACTORED denominators before `field_simp`: their stored denominators are expanded
polynomials, which `field_simp` cannot prove non-zero from `n ≠ 0, n−1 ≠ 0, n−2 ≠ 0`,
and the cancellation then silently fails to complete.

Cross-checked outside Lean by `leanproj/verify_H_identity.py` (part 1 against the
assembled Gram at `n = 4, 5, 6` at three corners; part 3 the whole identity as an
identity of rational functions of `n`, by full coefficient comparison, never
sampling), and by `sub-dittert/verify_general.py` from the 1992 definition. -/
theorem certificate_identity (n : ℕ) (hn : 4 ≤ n) :
    ∀ A ∈ Kn n, objPoly n A
      = Certificate.quadForm (G0 n) (centre n A)
        + ∑ p : Fin n × Fin n,
            Certificate.quadForm (Hm n p) (centre n A) * A p.1 p.2 :=
  fun A hA => certificate_identity_proved A hn hA

/-- **The certificate exists.**  Now only `certificate_identity` is open: the witness
is the explicit `Hm`, and its positive semidefiniteness is proved. -/
theorem certificate_exists_poly (n : ℕ) (hn : 4 ≤ n) (hcert : CertPositive (n : ℝ)) :
    ∃ (H : Fin n × Fin n → Matrix (Fin n × Fin n) (Fin n × Fin n) ℝ),
      (∀ p, (H p).PosSemidef) ∧
        ∀ A ∈ Kn n, objPoly n A
          = Certificate.quadForm (G0 n) (centre n A)
            + ∑ p : Fin n × Fin n, Certificate.quadForm (H p) (centre n A) * A p.1 p.2 :=
  ⟨Hm n, fun p => Hm_posSemidef p hn, certificate_identity n hn⟩

/-- The same statement in the original notation.  **Proved** from
`certificate_exists_poly` and `obj_eq_objPoly`; it carries no `sorry` of its own. -/
theorem certificate_exists (n : ℕ) (hn : 4 ≤ n) (hcert : CertPositive (n : ℝ)) :
    ∃ (G : Matrix (Fin n × Fin n) (Fin n × Fin n) ℝ)
      (H : Fin n × Fin n → Matrix (Fin n × Fin n) (Fin n × Fin n) ℝ),
      G.PosSemidef ∧ (∀ p, (H p).PosSemidef) ∧
        ∀ A ∈ Kn n, (2 - 6 / (n : ℝ) ^ 3) - Phi 3 A
          = Certificate.quadForm G (centre n A)
            + ∑ p : Fin n × Fin n, Certificate.quadForm (H p) (centre n A) * A p.1 p.2 := by
  obtain ⟨H, hH, hid⟩ := certificate_exists_poly n hn hcert
  refine ⟨G0 n, H, G0_posSemidef n hn, hH, fun A hA => ?_⟩
  rw [obj_eq_objPoly (le_trans (by norm_num) hn) A]
  exact hid A hA

/-- **The sub-Dittert conjecture at `k = 3`, for every `n ≥ 4`.**

The deduction from the certificate is Lean-proved: it is
`Certificate.nonneg_of_certificate` applied to the identity, the semidefiniteness
of the Grams, and non-negativity of the entries of `A` on `K_n`.  The ten
positivity facts enter through `certPositive_of_four_le`, which is proved. -/
theorem subDittert_k3_of_certificate (n : ℕ) (hn : 4 ≤ n) :
    ∀ A ∈ Kn n, Phi 3 A ≤ 2 - 6 / (n : ℝ) ^ 3 := by
  have hn' : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  obtain ⟨G, H, hG, hH, hid⟩ := certificate_exists n hn (certPositive_of_four_le hn')
  have key := Certificate.nonneg_of_certificate (S := Kn n)
    (F := fun A => (2 - 6 / (n : ℝ) ^ 3) - Phi 3 A)
    (sigma0 := fun A => Certificate.quadForm G (centre n A))
    (sigma := fun p A => Certificate.quadForm (H p) (centre n A))
    (g := fun p A => A p.1 p.2)
    hid
    (fun A _ => Certificate.quadForm_nonneg hG _)
    (fun p A _ => Certificate.quadForm_nonneg (hH p) _)
    (fun p A hA => hA.1 p.1 p.2)
  intro A hA
  have := key A hA
  simp only at this
  linarith

/-- The same, written out in the notation of Cheon–Hwang 1992. -/
theorem subDittert_k3 (n : ℕ) (hn : 4 ≤ n) (A : Matrix (Fin n) (Fin n) ℝ)
    (hpos : ∀ i j, 0 ≤ A i j) (hsum : ∑ i, ∑ j, A i j = (n : ℝ)) :
    E 3 (rowSum A) + E 3 (colSum A) - P 3 A ≤ 2 - 6 / (n : ℝ) ^ 3 :=
  subDittert_k3_of_certificate n hn A ⟨hpos, hsum⟩

/-! ## 4b.  The full statement: equality only at `J_n/n`, and stability

The conjecture of 1992 asserts the inequality *and* that equality holds only at
`J_n/n`.  Everything needed for the second half is already above, and one term of
`quadForm_G0` was being thrown away.

`quadForm_G0` says, for every `n` and every `b`,

    quadForm (G0 n) b  =  c0Total·(∑ b)²  +  c0Line·(∑ R² + ∑ C²)  +  theta2·∑ b²,

and `c0Total_pos`, `c0Line_pos`, `theta2_pos` hold for every real `n ≥ 4`.  The
first two terms are non-negative; the third is *strictly* positive unless every
`b u` vanishes.  So `G0` is positive DEFINITE, not merely semidefinite, and it is
definite for the cheapest possible reason — no spectral theory, no eigenvalue
multiplicities, no block-diagonalisation, nothing beyond the three positivity
facts already proved.  `Certificate.certificate_bound_and_uniqueness` then turns
the identity into bound *plus* uniqueness, its separation hypothesis discharged by
`eq_uniform_of_centre_eq_zero`: the centred coordinates are `b_p = A p − 1/n`
entrywise, so `centre n A = 0` says exactly `A = J_n/n`.

Keeping the `theta2` term instead of discarding it gives more than the conjecture
asks.  Dropping only the manifestly non-negative pieces leaves

    (2 − 6/n³) − [E₃(r) + E₃(c) − P₃(A)]  ≥  theta_2(n) · ‖A − J_n/n‖_F²

for every `n ≥ 4` and every `A ∈ K_n`, with

    theta_2(n) = (n⁴ + 40n² − 84n + 40) / (n⁵(n−1)³(n−2))

and `‖·‖_F²` the plain sum of squared entry deviations, `∑_{i,j} (A_ij − 1/n)²`,
with no normalising factor.  That is a quantitative stability statement: the
functional falls away from its maximum at least quadratically in the distance to
the maximiser, at an explicit rate.  It implies the equality case immediately,
which is proved separately as `eq_uniform_of_Phi_eq_of_stability` — a second route
to uniqueness that does not go through the positive-definite bridge at all.

The constant is valid but not optimal: `sub-dittert/stability_check.py` measures
the slack ratio exactly over `ℚ` at `n = 4, 5, 6` and finds it constant in the
doubly centred directions — where the `c0Total` and `c0Line` terms vanish
identically, so only the multiplier half of the certificate is discarded — with
values `2.88`, `4.34`, `5.70`. -/

/-- The `sigma_0` form is strictly positive off the origin: the `theta2` term
alone forces it, since `∑ b²` vanishes only when `b` does. -/
theorem quadForm_G0_pos (n : ℕ) (hn : 4 ≤ n) (b : Fin n × Fin n → ℝ) (hb : b ≠ 0) :
    0 < Certificate.quadForm (G0 n) b := by
  have hn' : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  obtain ⟨u0, hu0⟩ := Function.ne_iff.mp hb
  have hu0' : b u0 ≠ 0 := by simpa using hu0
  have hsq : 0 < ∑ u, b u ^ 2 :=
    Finset.sum_pos' (fun v _ => sq_nonneg _)
      ⟨u0, Finset.mem_univ u0, lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hu0'))⟩
  rw [quadForm_G0]
  have p1 : 0 ≤ c0Total (n : ℝ) * (∑ u, b u) ^ 2 :=
    mul_nonneg (c0Total_pos hn').le (sq_nonneg _)
  have p2 : 0 ≤ c0Line (n : ℝ)
      * ((∑ i, (∑ j, b (i, j)) ^ 2) + (∑ j, (∑ i, b (i, j)) ^ 2)) :=
    mul_nonneg (c0Line_pos hn').le
      (add_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _)
        (Finset.sum_nonneg fun _ _ => sq_nonneg _))
  have p3 : 0 < theta2 (n : ℝ) * ∑ u, b u ^ 2 := mul_pos (theta2_pos hn') hsq
  linarith

/-- **`G0` is positive DEFINITE for every `n ≥ 4`.**  This is the step that the
paper's earlier draft had to leave to the unformalised block-diagonalisation; it
needs neither. -/
theorem G0_posDef (n : ℕ) (hn : 4 ≤ n) : (G0 n).PosDef := by
  constructor
  · ext u v
    simpa [Matrix.conjTranspose_apply] using (G0_symm n v u)
  · intro x hx
    simpa [Certificate.quadForm] using quadForm_G0_pos n hn x hx

/-- **The separation lemma.**  The monomial map of the certificate is `centre`,
whose vanishing pins every entry to `1/n`.  This is the hypothesis `hsep` of
`Certificate.certificate_bound_and_uniqueness`. -/
theorem eq_uniform_of_centre_eq_zero (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ)
    (h : centre n A = 0) : A = uniform n := by
  ext i j
  have hij := congrFun h (i, j)
  unfold centre at hij
  simp only [Pi.zero_apply] at hij
  unfold uniform
  linarith

theorem centre_uniform_eq_zero (n : ℕ) : centre n (uniform n) = 0 := by
  funext p
  show uniform n p.1 p.2 - 1 / (n : ℝ) = 0
  unfold uniform
  ring

/-- `centre` vanishes exactly at `J_n/n`. -/
theorem centre_eq_zero_iff (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) :
    centre n A = 0 ↔ A = uniform n :=
  ⟨eq_uniform_of_centre_eq_zero n A, fun h => by rw [h]; exact centre_uniform_eq_zero n⟩

/-- The squared Frobenius distance to `J_n/n`, in the two shapes used below. -/
theorem sum_centre_sq (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) :
    (∑ u : Fin n × Fin n, centre n A u ^ 2) = ∑ i, ∑ j, (A i j - 1 / (n : ℝ)) ^ 2 := by
  rw [Fintype.sum_prod_type]
  rfl

/-- `theta2` with its denominator factored.  The stored denominator is the
expanded polynomial `n⁹ − 5n⁸ + 9n⁷ − 7n⁶ + 2n⁵`, which is `n⁵(n−1)³(n−2)`. -/
theorem theta2_factored (n : ℝ) :
    theta2 n = (n ^ 4 + 40 * n ^ 2 - 84 * n + 40) / (n ^ 5 * (n - 1) ^ 3 * (n - 2)) := by
  unfold theta2 theta2Num theta2Den
  congr 1
  ring

/-- `Phi_uniform` at `k = 3`, for every `n ≥ 3`: the equality case is attained. -/
theorem Phi_uniform_k3 (n : ℕ) (hn : 3 ≤ n) : Phi 3 (uniform n) = 2 - 6 / (n : ℝ) ^ 3 := by
  have h0 : n ≠ 0 := by omega
  rw [Phi_uniform 3 hn h0]
  norm_num [Nat.factorial]

/-- The certificate identity in the original notation, with the explicit `G0` kept
in the statement — `certificate_exists` hides it behind an existential, and the
uniqueness argument needs the witness. -/
theorem obj_identity (n : ℕ) (hn : 4 ≤ n) :
    ∀ A ∈ Kn n, (2 - 6 / (n : ℝ) ^ 3) - Phi 3 A
      = Certificate.quadForm (G0 n) (centre n A)
        + ∑ p : Fin n × Fin n,
            Certificate.quadForm (Hm n p) (centre n A) * A p.1 p.2 := by
  intro A hA
  rw [obj_eq_objPoly (le_trans (by norm_num) hn) A]
  exact certificate_identity n hn A hA

/-- **Bound and uniqueness together, through the formalised bridge.**  This is
`Certificate.certificate_bound_and_uniqueness` at the certificate's own data:
`G0` positive definite, the identity, semidefiniteness of every multiplier Gram,
non-negativity of the entries on `K_n`, and the separation lemma. -/
theorem subDittert_k3_bound_and_uniqueness (n : ℕ) (hn : 4 ≤ n) :
    (∀ A ∈ Kn n, Phi 3 A ≤ 2 - 6 / (n : ℝ) ^ 3) ∧
      (∀ A ∈ Kn n, Phi 3 A = 2 - 6 / (n : ℝ) ^ 3 → A = uniform n) := by
  obtain ⟨hbnd, huniq⟩ :=
    Certificate.certificate_bound_and_uniqueness (S := Kn n) (ι := Fin n × Fin n)
      (fun A => (2 - 6 / (n : ℝ) ^ 3) - Phi 3 A)
      (fun p A => Certificate.quadForm (Hm n p) (centre n A))
      (fun p A => A p.1 p.2)
      (centre n) (G0 n) (uniform n)
      (G0_posDef n hn)
      (obj_identity n hn)
      (fun p A _ => Certificate.quadForm_nonneg (Hm_posSemidef p hn) _)
      (fun p A hA => hA.1 p.1 p.2)
      (fun A _ h => eq_uniform_of_centre_eq_zero n A h)
  refine ⟨fun A hA => ?_, fun A hA hEq => ?_⟩
  · have := hbnd A hA
    simp only at this
    linarith
  · refine huniq A hA ?_
    show (2 - 6 / (n : ℝ) ^ 3) - Phi 3 A = 0
    linarith

/-- **The quantitative form, stronger than the conjecture.**  The objective
exceeds `theta_2(n)` times the squared Frobenius distance to `J_n/n`.  Only
manifestly non-negative terms are discarded: the `(∑ b)²` and line terms of
`quadForm_G0`, and the whole multiplier half. -/
theorem subDittert_k3_stability (n : ℕ) (hn : 4 ≤ n) :
    ∀ A ∈ Kn n, theta2 (n : ℝ) * (∑ i, ∑ j, (A i j - 1 / (n : ℝ)) ^ 2)
      ≤ (2 - 6 / (n : ℝ) ^ 3) - Phi 3 A := by
  intro A hA
  have hn' : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hid := obj_identity n hn A hA
  have hG0 := quadForm_G0 n (centre n A)
  have hmul : 0 ≤ ∑ p : Fin n × Fin n,
      Certificate.quadForm (Hm n p) (centre n A) * A p.1 p.2 :=
    Finset.sum_nonneg fun p _ =>
      mul_nonneg (Certificate.quadForm_nonneg (Hm_posSemidef p hn) _) (hA.1 p.1 p.2)
  have p1 : 0 ≤ c0Total (n : ℝ) * (∑ u, centre n A u) ^ 2 :=
    mul_nonneg (c0Total_pos hn').le (sq_nonneg _)
  have p2 : 0 ≤ c0Line (n : ℝ)
      * ((∑ i, (∑ j, centre n A (i, j)) ^ 2) + (∑ j, (∑ i, centre n A (i, j)) ^ 2)) :=
    mul_nonneg (c0Line_pos hn').le
      (add_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _)
        (Finset.sum_nonneg fun _ _ => sq_nonneg _))
  rw [← sum_centre_sq n A]
  linarith

/-- The same with the constant written out. -/
theorem subDittert_k3_stability_explicit (n : ℕ) (hn : 4 ≤ n) :
    ∀ A ∈ Kn n,
      ((n : ℝ) ^ 4 + 40 * (n : ℝ) ^ 2 - 84 * (n : ℝ) + 40)
          / ((n : ℝ) ^ 5 * ((n : ℝ) - 1) ^ 3 * ((n : ℝ) - 2))
          * (∑ i, ∑ j, (A i j - 1 / (n : ℝ)) ^ 2)
        ≤ (2 - 6 / (n : ℝ) ^ 3) - Phi 3 A := by
  intro A hA
  have := subDittert_k3_stability n hn A hA
  rwa [theta2_factored] at this

/-- **Uniqueness again, from stability alone.**  Independent of
`Certificate.certificate_bound_and_uniqueness` and of `G0_posDef`: if the
objective vanishes then so does a positive multiple of the squared distance, hence
every entry equals `1/n`.  Two routes to the same conclusion. -/
theorem eq_uniform_of_Phi_eq_of_stability (n : ℕ) (hn : 4 ≤ n) :
    ∀ A ∈ Kn n, Phi 3 A = 2 - 6 / (n : ℝ) ^ 3 → A = uniform n := by
  intro A hA hEq
  have hn' : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hst := subDittert_k3_stability n hn A hA
  rw [hEq] at hst
  have hge : 0 ≤ ∑ i, ∑ j, (A i j - 1 / (n : ℝ)) ^ 2 :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  have hzero : (∑ i, ∑ j, (A i j - 1 / (n : ℝ)) ^ 2) = 0 := by
    rcases eq_or_lt_of_le hge with h | h
    · exact h.symm
    · exact absurd hst (not_le.mpr (by nlinarith [theta2_pos hn']))
  have hrow := (Finset.sum_eq_zero_iff_of_nonneg
    (fun i (_ : i ∈ univ) => Finset.sum_nonneg fun j _ => sq_nonneg _)).mp hzero
  ext i j
  have hij := (Finset.sum_eq_zero_iff_of_nonneg
    (fun j (_ : j ∈ univ) => sq_nonneg (A i j - 1 / (n : ℝ)))).mp
      (hrow i (Finset.mem_univ i)) j (Finset.mem_univ j)
  have hij' : A i j - 1 / (n : ℝ) = 0 := pow_eq_zero_iff two_ne_zero |>.mp hij
  unfold uniform
  linarith

/-- **The sub-Dittert conjecture at `k = 3`, in full, for every `n ≥ 4`.**  In the
notation of Cheon–Hwang 1992: the inequality; equality if and only if
`A = J_n/n`; and the quantitative form with the explicit rate. -/
theorem subDittert_k3_full (n : ℕ) (hn : 4 ≤ n) (A : Matrix (Fin n) (Fin n) ℝ)
    (hpos : ∀ i j, 0 ≤ A i j) (hsum : ∑ i, ∑ j, A i j = (n : ℝ)) :
    E 3 (rowSum A) + E 3 (colSum A) - P 3 A ≤ 2 - 6 / (n : ℝ) ^ 3
      ∧ (E 3 (rowSum A) + E 3 (colSum A) - P 3 A = 2 - 6 / (n : ℝ) ^ 3
          ↔ A = uniform n)
      ∧ theta2 (n : ℝ) * (∑ i, ∑ j, (A i j - 1 / (n : ℝ)) ^ 2)
          ≤ 2 - 6 / (n : ℝ) ^ 3 - (E 3 (rowSum A) + E 3 (colSum A) - P 3 A) := by
  have hA : A ∈ Kn n := ⟨hpos, hsum⟩
  obtain ⟨hbnd, huniq⟩ := subDittert_k3_bound_and_uniqueness n hn
  refine ⟨hbnd A hA, ⟨fun h => huniq A hA h, fun h => ?_⟩, subDittert_k3_stability n hn A hA⟩
  rw [h]
  exact Phi_uniform_k3 n (le_trans (by norm_num) hn)

/-! ## 5.  Axiom audit

**Everything depends only on `propext, Classical.choice, Quot.sound`.**  Build success
is not an axiom audit: a file with no `sorry` in its source can still rest on
`sorryAx`, so every theorem the paper cites is listed here explicitly. -/

section AxiomAudit

#print axioms permanent_const
#print axioms Phi_uniform
#print axioms Phi_uniform_three
#print axioms Phi_uniform_four
#print axioms Phi_uniform_five
#print axioms sigmaK_three_eq_permanent
#print axioms sigmaK_rankOne
#print axioms sigmaK_three_M3
#print axioms uniform_mem_Kn
#print axioms theta0_pos
#print axioms theta1_pos
#print axioms theta2_pos
#print axioms minorA1_pos
#print axioms minorA2_pos
#print axioms minorA3_pos
#print axioms blockB_pos
#print axioms minorC1_pos
#print axioms minorC2_pos
#print axioms blockD_pos
#print axioms certPositive_of_four_le
#print axioms sigmaK_three_closed
#print axioms esym_three_closed
#print axioms obj_eq_objPoly
#print axioms c0Total_pos
#print axioms c0Line_pos
#print axioms quadForm_G0
#print axioms G0_posSemidef
#print axioms pivotA1_pos
#print axioms pivotA2_pos
#print axioms pivotA3_pos
#print axioms pivotB_pos
#print axioms pivotC1_pos
#print axioms pivotC2_pos
#print axioms pivotD_pos
#print axioms certPositiveH_of_four_le
#print axioms bridgeA3
#print axioms hA_minor3_pos
#print axioms quad3_nonneg
#print axioms quadForm_Hm
#print axioms body_nonneg
#print axioms quadForm_Hm_nonneg
#print axioms Hm_posSemidef
#print axioms quadForm_Hm_global
#print axioms sumP_lin_reduced
#print axioms sumP_cub_reduced
#print axioms objPoly_global
#print axioms certificate_identity_proved
#print axioms certificate_identity
#print axioms certificate_exists_poly
#print axioms certificate_exists
#print axioms subDittert_k3_of_certificate
#print axioms subDittert_k3
#print axioms quadForm_G0_pos
#print axioms G0_posDef
#print axioms eq_uniform_of_centre_eq_zero
#print axioms centre_uniform_eq_zero
#print axioms centre_eq_zero_iff
#print axioms sum_centre_sq
#print axioms theta2_factored
#print axioms Phi_uniform_k3
#print axioms obj_identity
#print axioms subDittert_k3_bound_and_uniqueness
#print axioms subDittert_k3_stability
#print axioms subDittert_k3_stability_explicit
#print axioms eq_uniform_of_Phi_eq_of_stability
#print axioms subDittert_k3_full
#print axioms Kn
#print axioms rowSum
#print axioms colSum
#print axioms esym
#print axioms subPerm
#print axioms sigmaK
#print axioms E
#print axioms P
#print axioms Phi
#print axioms uniform
#print axioms rowSum_uniform
#print axioms colSum_uniform
#print axioms esym_one
#print axioms subPerm_uniform
#print axioms sigmaK_uniform
#print axioms prod_orderEmbOfFin
#print axioms subPerm_rankOne
#print axioms M3
#print axioms sigmaK_eq_sigP
#print axioms esym_eq_sum
#print axioms exists_shift
#print axioms theta0Num
#print axioms theta0Num_pos
#print axioms theta0Den
#print axioms theta0Den_pos
#print axioms theta0
#print axioms theta1Num
#print axioms theta1Num_pos
#print axioms theta1Den
#print axioms theta1Den_pos
#print axioms theta1
#print axioms theta2Num
#print axioms theta2Num_pos
#print axioms theta2Den
#print axioms theta2Den_pos
#print axioms theta2
#print axioms minorA1Num
#print axioms minorA1Num_pos
#print axioms minorA1Den
#print axioms minorA1Den_pos
#print axioms minorA1
#print axioms minorA2Num
#print axioms minorA2Num_pos
#print axioms minorA2Den
#print axioms minorA2Den_pos
#print axioms minorA2
#print axioms minorA3Num
#print axioms minorA3Num_pos
#print axioms minorA3Den
#print axioms minorA3Den_pos
#print axioms minorA3
#print axioms blockBNum
#print axioms blockBNum_pos
#print axioms blockBDen
#print axioms blockBDen_pos
#print axioms blockB
#print axioms minorC1Num
#print axioms minorC1Num_pos
#print axioms minorC1Den
#print axioms minorC1Den_pos
#print axioms minorC1
#print axioms minorC2Num
#print axioms minorC2Num_pos
#print axioms minorC2Den
#print axioms minorC2Den_pos
#print axioms minorC2
#print axioms blockDNum
#print axioms blockDNum_pos
#print axioms blockDDen
#print axioms blockDDen_pos
#print axioms blockD
#print axioms CertPositive
#print axioms c0TotalNum
#print axioms c0TotalNum_pos
#print axioms c0TotalDen
#print axioms c0TotalDen_pos
#print axioms c0Total
#print axioms c0LineNum
#print axioms c0LineNum_pos
#print axioms c0LineDen
#print axioms c0LineDen_pos
#print axioms c0Line
#print axioms G0
#print axioms G0_symm
#print axioms sum_row_ind
#print axioms sum_col_ind
#print axioms quadForm_G0_nonneg
#print axioms pivotA1Num
#print axioms pivotA1Num_pos
#print axioms pivotA1Den
#print axioms pivotA1Den_pos
#print axioms pivotA1
#print axioms pivotA2Num
#print axioms pivotA2Num_pos
#print axioms pivotA2Den
#print axioms pivotA2Den_pos
#print axioms pivotA2
#print axioms pivotA3Num
#print axioms pivotA3Num_pos
#print axioms pivotA3Den
#print axioms pivotA3Den_pos
#print axioms pivotA3
#print axioms pivotBNum
#print axioms pivotBNum_pos
#print axioms pivotBDen
#print axioms pivotBDen_pos
#print axioms pivotB
#print axioms pivotC1Num
#print axioms pivotC1Num_pos
#print axioms pivotC1Den
#print axioms pivotC1Den_pos
#print axioms pivotC1
#print axioms pivotC2Num
#print axioms pivotC2Num_pos
#print axioms pivotC2Den
#print axioms pivotC2Den_pos
#print axioms pivotC2
#print axioms pivotDNum
#print axioms pivotDNum_pos
#print axioms pivotDDen
#print axioms pivotDDen_pos
#print axioms pivotD
#print axioms CertPositiveH
#print axioms hh0
#print axioms hh3
#print axioms hh4
#print axioms hh5
#print axioms hh6
#print axioms hh7
#print axioms hh8
#print axioms hh9
#print axioms hh10
#print axioms hAq
#print axioms hBq
#print axioms hCq
#print axioms hGg
#print axioms hA22
#print axioms hA23
#print axioms hA33
#print axioms hBb
#print axioms hQ22
#print axioms hDet3
#print axioms ne0
#print axioms ne1
#print axioms ne2
#print axioms bridgeA1
#print axioms bridgeA2
#print axioms bridgeB
#print axioms bridgeC1
#print axioms bridgeD
#print axioms bridgeC2
#print axioms quad2_nonneg
#print axioms hh0_pos
#print axioms hA_minor2_pos
#print axioms hBb_pos
#print axioms hAq_pos
#print axioms hC_minor2_pos
#print axioms hGg_pos
#print axioms quadA_nonneg
#print axioms quadC_nonneg
#print axioms iP
#print axioms iC
#print axioms iR
#print axioms iB
#print axioms Hm
#print axioms Hm_symm
#print axioms sum_free_pair
#print axioms sum_diag_pair
#print axioms sum_row_pair
#print axioms sum_col_pair
#print axioms lKap
#print axioms lRho
#print axioms lTau
#print axioms lE2
#print axioms lF2
#print axioms lB2
#print axioms lE
#print axioms lR
#print axioms lF
#print axioms lC
#print axioms sum_iP
#print axioms zR
#print axioms zC
#print axioms zR_idem
#print axioms zC_idem
#print axioms sum_zR
#print axioms sum_zC
#print axioms iB_eq
#print axioms iC_eq
#print axioms iR_eq
#print axioms lE_apply
#print axioms lR_apply
#print axioms lF_apply
#print axioms lC_apply
#print axioms zR_lE
#print axioms zR_lR
#print axioms zC_lF
#print axioms zC_lC
#print axioms sum_lE
#print axioms sum_lR
#print axioms sum_lF
#print axioms sum_lC
#print axioms sum_lE_sq
#print axioms sum_lF_sq
#print axioms bodyX
#print axioms sum_bodyX_row
#print axioms sum_bodyX_col
#print axioms zR_bodyX
#print axioms zC_bodyX
#print axioms sum_bodyX_sq
#print axioms sum_centred_sq
#print axioms sum_centred_quad
#print axioms centre
#print axioms objPoly
#print axioms gRow
#print axioms gCol
#print axioms gRowSq
#print axioms gColSq
#print axioms gRowDot
#print axioms gColDot
#print axioms gS
#print axioms gT2
#print axioms gT3
#print axioms gSR2
#print axioms gSC2
#print axioms gSR3
#print axioms gSC3
#print axioms gM1
#print axioms gM2
#print axioms gM3
#print axioms sum_gRow
#print axioms sum_gCol
#print axioms sum_gRowSq
#print axioms sum_gColSq
#print axioms sum_gRowDot
#print axioms sum_gColDot
#print axioms const_row
#print axioms sumP_b
#print axioms sumP_b2
#print axioms sumP_b3
#print axioms sumP_bRow
#print axioms sumP_bCol
#print axioms sumP_Row
#print axioms sumP_Col
#print axioms sumP_Row2
#print axioms sumP_Col2
#print axioms sumP_Row3
#print axioms sumP_Col3
#print axioms sumP_RowCol
#print axioms sumP_RowSq
#print axioms sumP_ColSq
#print axioms sumP_RowDot
#print axioms sumP_ColDot
#print axioms sumP_b2Row
#print axioms sumP_b2Col
#print axioms sumP_bRowCol
#print axioms sumP_bRow2
#print axioms sumP_bCol2
#print axioms sumP_bRowSq
#print axioms sumP_bColSq
#print axioms sumP_bRowDot
#print axioms sumP_bColDot
#print axioms sum_zR_mul
#print axioms sum_zC_mul
#print axioms lKap_global
#print axioms lRho_global
#print axioms lTau_global
#print axioms sum_lE_sq_global
#print axioms sum_lF_sq_global
#print axioms sum_lElR_global
#print axioms sum_lFlC_global
#print axioms sum_lR_sq_global
#print axioms sum_lC_sq_global
#print axioms lB2_global
#print axioms kB2
#print axioms kBL
#print axioms kL2
#print axioms kRC
#print axioms kSq
#print axioms kDot
#print axioms kC
#print axioms sumP_const
#print axioms sumP_one
#print axioms quadForm_Hm_mono
#print axioms quadForm_Hm_mono_mul
#print axioms sumP_quadForm_lin
#print axioms sumP_quadForm_cub
#print axioms centre_add
#print axioms hrow
#print axioms hcol
#print axioms objS1
#print axioms objS2r
#print axioms objS2c
#print axioms objS3r
#print axioms objS3c
#print axioms objA2
#print axioms objA3
#print axioms objA2r
#print axioms objA2c
#print axioms objArc
#print axioms choose3_cast
#print axioms gS_centre
#print axioms cD
#print axioms cT2
#print axioms cSR
#print axioms coefT3
#print axioms coefM23
#print axioms coefR3
#print axioms coefM1
#print axioms coefT2
#print axioms coefSR2

end AxiomAudit

end

end SubDittertK3
