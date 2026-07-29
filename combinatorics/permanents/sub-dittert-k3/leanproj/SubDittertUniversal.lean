/-
# The universal identity of the sub-Dittert programme, uniformly in `k`

`SubDittertLinear.lean` proves the `e_k` half of the coefficient rules of
`problems/permanents/sub-dittert/NOTES.md` §6a.4 and leaves the `σ_k` half as a `sorry`.
This file discharges that `sorry` and assembles the two halves into the identity the
whole universal route rests on: with `A = J_n/n + b`, and `R`, `C` the row and column
sums of the increment `b`,

    (2 − k!/n^k) − [E_k(r) + E_k(c) − P_k(A)]
      = ∑_{d=1}^{k} [ t_d · σ_d(b) − s_d · (e_d(R) + e_d(C)) ],

identically in `b`, for every `1 ≤ k ≤ n`, where `s_d = [k]_d / [n]_d` and
`t_d = s_d² (k−d)! / n^(k−d)`.  Outside Lean the identity was derived and checked
exactly in `sub-dittert/allk_universal.py`; nothing here uses that check.

## What is proved

* `sigP_emb` — the rook bridge **for every `k`**: summing over pairs of injections
  `Fin k ↪ Fin n` is `k!` times the subpermanent sum.  `RookSum.sigma_three_emb` is the
  `k = 3` case; nothing in its proof was specific to `3`.
* `sum_emb_restrict`, `sum_emb_restrict_subset`, `sum_emb_pair_restrict` — the fibres of
  the restriction map on injections, counted.  The engine is Mathlib's
  `Equiv.sumEmbeddingEquivSigmaEmbeddingRestricted`.
* `sigmaK_one_add` — **the `σ_k` coefficient rule**, §6a.4's rule 2.  This is exactly the
  statement `SubDittertLinear` carried as a `sorry` until commit `2f8f251`; that
  declaration has since been deleted, and `sigmaK_one_add_of_le` below restates it
  verbatim so the discharged statement stays on the record.
* `universal_identity` — the identity above, kernel-checked, uniformly in `k` and `n`.

## What is NOT claimed

Nothing here is about positivity, about the Gram matrices, or about the certificate
existing.  The identity is an algebraic rewriting of the objective; it says what the
objective *is*, not that it is non-negative.  L1(a)–(d) of `paper_l.typ` remain
unformalised, as `SubDittertLinear.lean`'s header already records.

## An independent derivation of the identity, recorded

The identity arrived here as a statement to be formalised, derived and checked exactly
elsewhere (`sub-dittert/allk_universal.py`).  It was re-derived from scratch before being
accepted, out of the two coefficient rules alone, and the derivation agreed term for
term; that confirmation is recorded here because it is independent of both the Python
check and the Lean proof.

The `e_k` rule gives `e_k(1 + R) = ∑_d C(n−d, k−d) e_d(R)`, and
`C(n−d, k−d) / C(n, k) = [k]_d / [n]_d = s_d` — this is `sCoef_eq` below — so
`E_k(r) = 1 + ∑_{d≥1} s_d e_d(R)`, and likewise for the columns.  The `σ_k` rule gives
`P_k(A) = ∑_{d≥0} s_d² (k−d)! n^{−(k−d)} σ_d(b) = ∑_d t_d σ_d(b)`, whose `d = 0` term is
`k!/n^k` because `s_0 = 1` and `σ_0 = 1`.  Subtracting, the two `1`s from the `E`s and the
`k!/n^k` from `P` cancel the constant `2 − k!/n^k` exactly, which is why the sum starts at
`d = 1`.  That cancellation is the centre identity, and `Fcent_zero_of_universal` in §6
turns the observation into a proof.

## Two working notes, for the next session

**Search the library before costing the work.**  The fibre count of §2 was costed at
150+ lines and is 21.  The estimate collapsed for one reason: Mathlib was searched before
anything was built, and it already had the whole construction
(`Equiv.sumEmbeddingEquivSigmaEmbeddingRestricted`), with the step expected to be hardest
— that its first projection is the restriction — true by `rfl`.  The route was chosen on
the same evidence: the injection layer, not the subset layer that was floated first, since
the subset route needs permanents of submatrices-of-submatrices, i.e. `orderEmbOfFin`
composed with itself.

**Importing an uncommitted sibling without touching the shared build tree.**  `lake env
lean` type-checks but emits no `.olean`, so a second file cannot import the first; running
`lake build` was not an option, because the build tree carried other agents' parked work.
The way through is to compile a private olean into a scratch directory and put that
directory on `LEAN_PATH`:

    lake env lean -o /scratch/SubDittertLinear.olean SubDittertLinear.lean
    lake env sh -c 'LEAN_PATH=/scratch:$LEAN_PATH lean SubDittertUniversal.lean'

Nothing is written under `.lake/build`, so concurrent agents are unaffected.  The scratch
directory must be PREPENDED: once anyone runs `lake build`, the build tree holds an olean
for the sibling, and with `$LEAN_PATH:/scratch` that stale copy wins.  The symptom is
`unknown identifier` for a declaration visibly present in the source; see the working
note in `NewtonInequalities.lean`, where this cost time twice.
-/
import SubDittertLinear

open Finset

namespace SubDittertUniversal

open SubDittertK3 SubDittertLinear

variable {n k d : ℕ}

/-! ## 1.  Injections versus subsets, uniformly in `k`

`RookSum.lean` proves the subset/injection bijection for every `k` but cashes it in only
at `k = 3`.  These two are the `k`-general forms; the proofs are `RookSum.perm_double`
and `RookSum.sigma_three_emb` with `3` replaced by `k` throughout, which is possible
because nothing in them was `3`-specific.  `RookSum.perm_double` is `private`, so it is
reproved rather than reused. -/

private theorem perm_double_k (A : Matrix (Fin n) (Fin n) ℝ) {S T : Finset (Fin n)}
    (hS : S.card = k) (hT : T.card = k) :
    (∑ τ : Equiv.Perm (Fin k), ∑ σ : Equiv.Perm (Fin k),
        ∏ a, A (S.orderEmbOfFin hS (τ a)) (T.orderEmbOfFin hT (σ a)))
      = ((k.factorial : ℕ) : ℝ) * ∑ ρ : Equiv.Perm (Fin k),
          ∏ a, A (S.orderEmbOfFin hS (ρ a)) (T.orderEmbOfFin hT a) := by
  have inner : ∀ τ : Equiv.Perm (Fin k),
      (∑ σ : Equiv.Perm (Fin k), ∏ a, A (S.orderEmbOfFin hS (τ a)) (T.orderEmbOfFin hT (σ a)))
        = ∑ ρ : Equiv.Perm (Fin k),
            ∏ a, A (S.orderEmbOfFin hS (ρ a)) (T.orderEmbOfFin hT a) := by
    intro τ
    let E : Equiv.Perm (Fin k) ≃ Equiv.Perm (Fin k) :=
      { toFun := fun σ => τ * σ⁻¹
        invFun := fun ρ => (τ⁻¹ * ρ)⁻¹
        left_inv := by intro σ; simp [mul_assoc]
        right_inv := by intro ρ; simp [mul_assoc] }
    rw [← Equiv.sum_comp E
        (fun ρ : Equiv.Perm (Fin k) =>
          ∏ a, A (S.orderEmbOfFin hS (ρ a)) (T.orderEmbOfFin hT a))]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [show E σ = τ * σ⁻¹ from rfl]
    rw [← Equiv.prod_comp σ (fun x => A (S.orderEmbOfFin hS ((τ * σ⁻¹) x))
          (T.orderEmbOfFin hT x))]
    exact Finset.prod_congr rfl fun a _ => by simp
  rw [Finset.sum_congr rfl fun τ (_ : τ ∈ univ) => inner τ, Finset.sum_const, Finset.card_univ,
    Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]

/-- **The rook bridge, for every `k`.**  The two `powersetCard` layers of the definition
of `σ_k` become two sums over injections, at the cost of a factor `k!`. -/
theorem sigP_emb (k : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) :
    (∑ f : Fin k ↪ Fin n, ∑ g : Fin k ↪ Fin n, ∏ a, A (f a) (g a))
      = ((k.factorial : ℕ) : ℝ) * RookSum.sigP k A := by
  rw [RookSum.sum_emb_eq_sum_powersetCard
    (fun f : Fin k → Fin n => ∑ g : Fin k ↪ Fin n, ∏ a, A (f a) (g a))]
  unfold RookSum.sigP
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun S hS => ?_
  have hSk : S.card = k := Finset.mem_powersetCard_univ.mp hS
  rw [RookSum.embSum_of_card hSk]
  have step : ∀ τ : Equiv.Perm (Fin k),
      (∑ g : Fin k ↪ Fin n, ∏ a, A (S.orderEmbOfFin hSk (τ a)) (g a))
        = ∑ T ∈ Finset.powersetCard k (univ : Finset (Fin n)),
            RookSum.embSum k (fun g : Fin k → Fin n =>
              ∏ a, A (S.orderEmbOfFin hSk (τ a)) (g a)) T :=
    fun τ => RookSum.sum_emb_eq_sum_powersetCard
      (fun g : Fin k → Fin n => ∏ a, A (S.orderEmbOfFin hSk (τ a)) (g a))
  rw [Finset.sum_congr rfl fun τ (_ : τ ∈ univ) => step τ, Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun T hT => ?_
  have hTk : T.card = k := Finset.mem_powersetCard_univ.mp hT
  rw [Finset.sum_congr rfl fun τ (_ : τ ∈ univ) =>
      RookSum.embSum_of_card (F := fun g : Fin k → Fin n =>
        ∏ a, A (S.orderEmbOfFin hSk (τ a)) (g a)) hTk]
  rw [perm_double_k A hSk hTk, RookSum.subP_apply hSk hTk]

/-- The same in `SubDittertK3`'s notation. -/
theorem sigmaK_emb (k : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) :
    (∑ f : Fin k ↪ Fin n, ∑ g : Fin k ↪ Fin n, ∏ a, A (f a) (g a))
      = ((k.factorial : ℕ) : ℝ) * sigmaK k A :=
  sigP_emb k A

/-! ## 2.  The fibres of restriction

The engine of the `σ_k` rule.  Expanding `∏_a (1/n + b_{f a, g a})` over subsets `D` of
`Fin k` leaves a sum over all injections `Fin k ↪ Fin n` of something that depends only on
the restriction to `D`; the restriction map's fibres must therefore be counted.  Mathlib
already has the decomposition — `Equiv.sumEmbeddingEquivSigmaEmbeddingRestricted` says an
embedding out of a sum type is an embedding of the first summand together with an
embedding of the second into the complement of the first's range — and the count follows
from `Fintype.card_embedding_eq`. -/

/-- **The fibre count.**  Summing a function of the restriction over all injections
`Fin d ⊕ Fin m ↪ Fin n` multiplies the sum over injections `Fin d ↪ Fin n` by the number
of ways to extend, which is `(n − d)` falling `m`. -/
theorem sum_emb_restrict {m : ℕ} {M : Type*} [AddCommMonoid M]
    (F : (Fin d → Fin n) → M) :
    ∑ f : (Fin d ⊕ Fin m) ↪ Fin n, F (fun i => f (Sum.inl i))
      = ((n - d).descFactorial m) • ∑ h : Fin d ↪ Fin n, F h := by
  classical
  set e := Equiv.sumEmbeddingEquivSigmaEmbeddingRestricted
    (α := Fin d) (β := Fin m) (γ := Fin n) with he
  rw [← Equiv.sum_comp e.symm (fun f : (Fin d ⊕ Fin m) ↪ Fin n => F (fun i => f (Sum.inl i)))]
  have hproj : ∀ x : (h : Fin d ↪ Fin n) × (Fin m ↪ ↥(Set.range (h : Fin d → Fin n))ᶜ),
      (fun i => (e.symm x) (Sum.inl i)) = (x.1 : Fin d → Fin n) := fun x => rfl
  rw [Finset.sum_congr rfl (fun x (_ : x ∈ Finset.univ) => by rw [hproj x])]
  rw [← Finset.univ_sigma_univ, Finset.sum_sigma, Finset.smul_sum]
  refine Finset.sum_congr rfl fun h _ => ?_
  show (∑ _s : Fin m ↪ ↥(Set.range (h : Fin d → Fin n))ᶜ, F (h : Fin d → Fin n))
      = (n - d).descFactorial m • F (h : Fin d → Fin n)
  rw [Finset.sum_const, Finset.card_univ]
  congr 1
  rw [Fintype.card_embedding_eq, Fintype.card_compl_set, Fintype.card_range,
    Fintype.card_fin, Fintype.card_fin, Fintype.card_fin]

/-- A product along the increasing enumeration of a subset is a product over it.  This is
`SubDittertK3.prod_orderEmbOfFin` with the ambient `Fin n` relaxed to any linear order, so
that it applies to subsets of `Fin k`. -/
private theorem prod_over_orderEmb {α : Type*} [LinearOrder α] {D : Finset α}
    (hD : D.card = d) (x : α → ℝ) :
    ∏ i : Fin d, x (D.orderEmbOfFin hD i) = ∏ a ∈ D, x a := by
  rw [← Finset.prod_coe_sort D x]
  exact Fintype.prod_equiv (D.orderIsoOfFin hD).toEquiv _ _ fun _ => rfl

/-- The splitting of `Fin k` at a subset `D` of size `d`: an equivalence
`Fin d ⊕ Fin (k − d) ≃ Fin k` whose left summand is the increasing enumeration of `D`.
This is what carries an arbitrary `D` to the standard splitting that `sum_emb_restrict`
is stated for. -/
noncomputable def splitAt {D : Finset (Fin k)} (hD : D.card = d) :
    Fin d ⊕ Fin (k - d) ≃ Fin k := by
  classical
  have hDc : (Dᶜ : Finset (Fin k)).card = k - d := by
    rw [Finset.card_compl, hD, Fintype.card_fin]
  exact (Equiv.sumCongr (D.orderIsoOfFin hD).toEquiv
      ((Dᶜ.orderIsoOfFin hDc).toEquiv.trans
        (Equiv.subtypeEquivRight (fun x => Finset.mem_compl)))).trans
    (Equiv.sumCompl (· ∈ D))

theorem splitAt_inl {D : Finset (Fin k)} (hD : D.card = d) (i : Fin d) :
    splitAt hD (Sum.inl i) = D.orderEmbOfFin hD i := rfl

/-- The fibre count at an arbitrary subset of `Fin k`. -/
theorem sum_emb_restrict_subset {D : Finset (Fin k)} (hD : D.card = d) {M : Type*}
    [AddCommMonoid M] (F : (Fin d → Fin n) → M) :
    ∑ f : Fin k ↪ Fin n, F (fun i => f (D.orderEmbOfFin hD i))
      = ((n - d).descFactorial (k - d)) • ∑ h : Fin d ↪ Fin n, F h := by
  classical
  set e := splitAt hD with he
  set ec := Equiv.embeddingCongr e (Equiv.refl (Fin n)) with hec
  rw [← Equiv.sum_comp ec (fun f : Fin k ↪ Fin n => F (fun i => f (D.orderEmbOfFin hD i)))]
  have hstep : ∀ f : (Fin d ⊕ Fin (k - d)) ↪ Fin n,
      F (fun i => (ec f) (D.orderEmbOfFin hD i)) = F (fun i => f (Sum.inl i)) := by
    intro f
    congr 1
    funext i
    rw [← splitAt_inl hD i, hec]
    simp [Equiv.embeddingCongr]
  rw [Finset.sum_congr rfl fun f (_ : f ∈ univ) => hstep f]
  exact sum_emb_restrict F

/-- **Both injections restricted at once.**  The row and column injections are restricted
to the same `D`, so the count appears squared. -/
theorem sum_emb_pair_restrict {D : Finset (Fin k)} (hD : D.card = d) (b : Fin n × Fin n → ℝ) :
    (∑ f : Fin k ↪ Fin n, ∑ g : Fin k ↪ Fin n, ∏ a ∈ D, b (f a, g a))
      = (((n - d).descFactorial (k - d) : ℕ) : ℝ) ^ 2
        * ∑ h : Fin d ↪ Fin n, ∑ h' : Fin d ↪ Fin n, ∏ i, b (h i, h' i) := by
  classical
  have hprod : ∀ f g : Fin k ↪ Fin n, (∏ a ∈ D, b (f a, g a))
      = ∏ i : Fin d, b (f (D.orderEmbOfFin hD i), g (D.orderEmbOfFin hD i)) :=
    fun f g => (prod_over_orderEmb hD (fun a => b (f a, g a))).symm
  rw [Finset.sum_congr rfl fun f (_ : f ∈ univ) =>
    Finset.sum_congr rfl fun g (_ : g ∈ univ) => hprod f g]
  have hg : ∀ f : Fin k ↪ Fin n,
      (∑ g : Fin k ↪ Fin n, ∏ i : Fin d, b (f (D.orderEmbOfFin hD i), g (D.orderEmbOfFin hD i)))
        = ((n - d).descFactorial (k - d)) •
            ∑ h' : Fin d ↪ Fin n, ∏ i : Fin d, b (f (D.orderEmbOfFin hD i), h' i) :=
    fun f => sum_emb_restrict_subset hD
      (fun h' : Fin d → Fin n => ∏ i : Fin d, b (f (D.orderEmbOfFin hD i), h' i))
  rw [Finset.sum_congr rfl fun f (_ : f ∈ univ) => hg f, ← Finset.smul_sum,
    sum_emb_restrict_subset hD
      (fun h : Fin d → Fin n => ∑ h' : Fin d ↪ Fin n, ∏ i : Fin d, b (h i, h' i)),
    smul_smul, nsmul_eq_mul]
  push_cast
  ring

/-! ## 3.  The `σ_k` coefficient rule

`NOTES.md` §6a.4, rule 2.  The `d` cells of a monomial contribute to `σ_k(J_n/n + b)`
exactly when they form a partial permutation, and then with coefficient
`C(n−d, k−d)² (k−d)! n^{−(k−d)}` — the two binomials choosing the remaining rows and
columns, the factorial matching them up, and the power of `1/n` supplying the entries of
`J_n/n` that were not used.  Stated with `σ_d` carrying the "partial permutation" clause,
exactly as `esym_one_add` lets `e_d` carry "distinct rows". -/

/-- The rule with the falling factorial, which is the form the fibre count produces. -/
theorem sigmaK_uncentre (k n : ℕ) (b : Fin n × Fin n → ℝ) :
    ((k.factorial : ℕ) : ℝ) * sigmaK k (uncentre n b)
      = ∑ j ∈ range (k + 1),
          (((k.choose j : ℕ) : ℝ) * (1 / (n : ℝ)) ^ (k - j)
            * (((n - j).descFactorial (k - j) : ℕ) : ℝ) ^ 2 * ((j.factorial : ℕ) : ℝ))
            * sigmaK j (incr n b) := by
  classical
  rw [sigmaK_eq_sigP, ← sigP_emb k (uncentre n b)]
  have hexp : ∀ f g : Fin k ↪ Fin n,
      (∏ a, (uncentre n b) (f a) (g a))
        = ∑ D ∈ (univ : Finset (Fin k)).powerset,
            (∏ a ∈ D, b (f a, g a)) * (1 / (n : ℝ)) ^ (k - D.card) := by
    intro f g
    have hpt : ∀ a : Fin k, (uncentre n b) (f a) (g a) = b (f a, g a) + 1 / (n : ℝ) := by
      intro a
      show 1 / (n : ℝ) + b (f a, g a) = b (f a, g a) + 1 / (n : ℝ)
      ring
    rw [Finset.prod_congr rfl fun a _ => hpt a,
      Finset.prod_add (fun a => b (f a, g a)) (fun _ => 1 / (n : ℝ)) univ]
    refine Finset.sum_congr rfl fun D hD => ?_
    rw [Finset.prod_const, Finset.card_sdiff (Finset.mem_powerset.mp hD),
      Finset.card_univ, Fintype.card_fin]
  rw [Finset.sum_congr rfl fun f (_ : f ∈ univ) =>
        Finset.sum_congr rfl fun g (_ : g ∈ univ) => hexp f g]
  rw [Finset.sum_congr rfl fun f (_ : f ∈ univ) => Finset.sum_comm, Finset.sum_comm]
  have hin : ∀ D : Finset (Fin k),
      (∑ f : Fin k ↪ Fin n, ∑ g : Fin k ↪ Fin n,
          (∏ a ∈ D, b (f a, g a)) * (1 / (n : ℝ)) ^ (k - D.card))
        = (1 / (n : ℝ)) ^ (k - D.card)
            * ((((n - D.card).descFactorial (k - D.card) : ℕ) : ℝ) ^ 2
              * (((D.card).factorial : ℕ) : ℝ) * sigmaK D.card (incr n b)) := by
    intro D
    have h1 : (∑ f : Fin k ↪ Fin n, ∑ g : Fin k ↪ Fin n,
          (∏ a ∈ D, b (f a, g a)) * (1 / (n : ℝ)) ^ (k - D.card))
        = (1 / (n : ℝ)) ^ (k - D.card)
            * ∑ f : Fin k ↪ Fin n, ∑ g : Fin k ↪ Fin n, ∏ a ∈ D, b (f a, g a) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun f _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun g _ => by ring
    have h2 : (∑ h : Fin D.card ↪ Fin n, ∑ h' : Fin D.card ↪ Fin n, ∏ i, b (h i, h' i))
        = (((D.card).factorial : ℕ) : ℝ) * sigmaK D.card (incr n b) := by
      rw [sigmaK_eq_sigP, ← sigP_emb]
      rfl
    rw [h1, sum_emb_pair_restrict rfl b, h2]
    ring
  rw [Finset.sum_congr rfl fun D (_ : D ∈ (univ : Finset (Fin k)).powerset) => hin D]
  rw [Finset.sum_powerset, Finset.card_univ, Fintype.card_fin]
  have hcard : ∀ j : ℕ, ∀ D ∈ powersetCard j (univ : Finset (Fin k)),
      (1 / (n : ℝ)) ^ (k - D.card)
          * ((((n - D.card).descFactorial (k - D.card) : ℕ) : ℝ) ^ 2
            * (((D.card).factorial : ℕ) : ℝ) * sigmaK D.card (incr n b))
        = (1 / (n : ℝ)) ^ (k - j)
          * ((((n - j).descFactorial (k - j) : ℕ) : ℝ) ^ 2
            * ((j.factorial : ℕ) : ℝ) * sigmaK j (incr n b)) := by
    intro j D hD
    rw [Finset.mem_powersetCard_univ.mp hD]
  rw [Finset.sum_congr rfl (fun j (_ : j ∈ range (k + 1)) => Finset.sum_congr rfl (hcard j))]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  ring

/-- **The `σ_k` coefficient rule** (`NOTES.md` §6a.4, rule 2):

    σ_k(J_n/n + b) = ∑_{d ≤ k} C(n−d, k−d)² (k−d)! n^{−(k−d)} · σ_d(b).

Its `d = 0` term is `SubDittertK3.sigmaK_uniform`.  Note that no `k ≤ n` hypothesis is
needed: above `n` both sides vanish, the left because there are no `k`-subsets of an
`n`-set and the right because `C(n − d, k − d) = 0` once `k − d` exceeds `n − d`. -/
theorem sigmaK_one_add (k n : ℕ) (hn : n ≠ 0) (b : Fin n × Fin n → ℝ) :
    sigmaK k (uncentre n b)
      = ∑ d ∈ range (k + 1),
          ((((n - d).choose (k - d) : ℕ) : ℝ) ^ 2 * (((k - d).factorial : ℕ) : ℝ)
              / (n : ℝ) ^ (k - d))
            * sigmaK d (incr n b) := by
  have hfac : ((k.factorial : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero k
  refine mul_left_cancel₀ hfac ?_
  rw [sigmaK_uncentre k n b, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjk : j ≤ k := by
    have := Finset.mem_range.mp hj
    omega
  have hnR : ((n : ℝ)) ^ (k - j) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr hn)
  have hnat : k.choose j * ((n - j).descFactorial (k - j)) ^ 2 * j.factorial
      = k.factorial * ((n - j).choose (k - j)) ^ 2 * (k - j).factorial := by
    rw [Nat.descFactorial_eq_factorial_mul_choose,
      ← Nat.choose_mul_factorial_mul_factorial hjk]
    ring
  have hcast : ((k.choose j : ℕ) : ℝ) * (((n - j).descFactorial (k - j) : ℕ) : ℝ) ^ 2
        * ((j.factorial : ℕ) : ℝ)
      = ((k.factorial : ℕ) : ℝ) * (((n - j).choose (k - j) : ℕ) : ℝ) ^ 2
        * (((k - j).factorial : ℕ) : ℝ) := by
    exact_mod_cast congrArg (fun x : ℕ => (x : ℝ)) hnat
  have hpow : (1 / (n : ℝ)) ^ (k - j) = 1 / (n : ℝ) ^ (k - j) := by
    rw [div_pow, one_pow]
  rw [hpow]
  field_simp
  linear_combination (sigmaK j (incr n b)) * hcast

/-- **The statement `SubDittertLinear` carried as a `sorry`**, restated verbatim —
including the `k ≤ n` hypothesis, which the proof above shows is not needed.

While that `sorry` still stood, the two were checked to be the same proposition by
`example ... : SubDittertLinear.sigmaK_one_add k n hkn hn b = sigmaK_one_add k n hn b :=
rfl`, which type-checks by proof irrelevance only if the statements agree; a mutation
control (changing the exponent `2` to `3` in the coefficient) broke it, so the check was
live.  The `sorry` was then deleted, and this restatement is what remains on the
record. -/
theorem sigmaK_one_add_of_le (k n : ℕ) (_hkn : k ≤ n) (hn : n ≠ 0) (b : Fin n × Fin n → ℝ) :
    sigmaK k (uncentre n b)
      = ∑ d ∈ range (k + 1),
          ((((n - d).choose (k - d) : ℕ) : ℝ) ^ 2 * (((k - d).factorial : ℕ) : ℝ)
              / (n : ℝ) ^ (k - d))
            * sigmaK d (incr n b) :=
  sigmaK_one_add k n hn b

/-! ## 4.  The coefficients `s_d` and `t_d`

`s_d = [k]_d / [n]_d` is the ratio of falling factorials, and it is also the ratio of
binomials `C(n − d, k − d) / C(n, k)` that the two coefficient rules actually produce.
The bridge between the two is the subset-of-a-subset identity
`C(n, k) C(k, d) = C(n, d) C(n − d, k − d)`, which is proved here because Mathlib does not
carry it. -/

/-- `σ_0` is the empty subpermanent sum, which is `1`, not `0`. -/
@[simp] theorem sigmaK_zero (M : Matrix (Fin n) (Fin n) ℝ) : sigmaK 0 M = 1 := by
  unfold sigmaK subPerm
  rw [Finset.powersetCard_zero]
  simp [Matrix.permanent_isEmpty]

/-- **Choosing `k` of `n` then `d` of those is choosing `d` of `n` then `k − d` of the
rest.**  Both sides times `d! (k−d)! (n−k)!` are `n!`. -/
private theorem choose_subset_of_subset {n k d : ℕ} (hdk : d ≤ k) (hkn : k ≤ n) :
    (n - d).choose (k - d) * n.choose d = n.choose k * k.choose d := by
  have hdn : d ≤ n := le_trans hdk hkn
  have hkd : k - d ≤ n - d := Nat.sub_le_sub_right hkn d
  have hsub : (n - d) - (k - d) = n - k := by omega
  have hpos : 0 < d.factorial * ((k - d).factorial * (n - k).factorial) := by
    exact Nat.mul_pos (Nat.factorial_pos _)
      (Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _))
  refine Nat.eq_of_mul_eq_mul_right hpos ?_
  have e1 : (n - d).choose (k - d) * (k - d).factorial * (n - k).factorial = (n - d).factorial := by
    have h := Nat.choose_mul_factorial_mul_factorial hkd
    rw [hsub] at h
    exact h
  have e2 : n.choose d * d.factorial * (n - d).factorial = n.factorial :=
    Nat.choose_mul_factorial_mul_factorial hdn
  have e3 : k.choose d * d.factorial * (k - d).factorial = k.factorial :=
    Nat.choose_mul_factorial_mul_factorial hdk
  have e4 : n.choose k * k.factorial * (n - k).factorial = n.factorial :=
    Nat.choose_mul_factorial_mul_factorial hkn
  calc (n - d).choose (k - d) * n.choose d
        * (d.factorial * ((k - d).factorial * (n - k).factorial))
      = n.choose d * d.factorial
          * ((n - d).choose (k - d) * (k - d).factorial * (n - k).factorial) := by ring
    _ = n.choose d * d.factorial * (n - d).factorial := by rw [e1]
    _ = n.factorial := e2
    _ = n.choose k * k.factorial * (n - k).factorial := e4.symm
    _ = n.choose k * (k.choose d * d.factorial * (k - d).factorial) * (n - k).factorial := by
          rw [e3]
    _ = n.choose k * k.choose d * (d.factorial * ((k - d).factorial * (n - k).factorial)) := by
          ring

/-- `s_d = [k]_d / [n]_d`. -/
noncomputable def sCoef (k n d : ℕ) : ℝ :=
  ((k.descFactorial d : ℕ) : ℝ) / ((n.descFactorial d : ℕ) : ℝ)

/-- `t_d = s_d² (k − d)! / n^(k−d)`. -/
noncomputable def tCoef (k n d : ℕ) : ℝ :=
  sCoef k n d ^ 2 * (((k - d).factorial : ℕ) : ℝ) / (n : ℝ) ^ (k - d)

@[simp] theorem sCoef_zero (k n : ℕ) : sCoef k n 0 = 1 := by
  simp [sCoef, Nat.descFactorial_zero]

/-- **The two forms of `s_d` agree**: the ratio of falling factorials is the ratio of the
binomials the coefficient rules produce. -/
theorem sCoef_eq {k n d : ℕ} (hdk : d ≤ k) (hkn : k ≤ n) :
    sCoef k n d = (((n - d).choose (k - d) : ℕ) : ℝ) / ((n.choose k : ℕ) : ℝ) := by
  have hdn : d ≤ n := le_trans hdk hkn
  have hB : ((n.descFactorial d : ℕ) : ℝ) ≠ 0 := by
    have : n.descFactorial d ≠ 0 := by
      rw [Ne, Nat.descFactorial_eq_zero_iff_lt]
      omega
    exact_mod_cast this
  have hD : ((n.choose k : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hkn).ne'
  rw [sCoef, div_eq_div_iff hB hD]
  have hnat : k.descFactorial d * n.choose k = (n - d).choose (k - d) * n.descFactorial d := by
    rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.descFactorial_eq_factorial_mul_choose]
    calc d.factorial * k.choose d * n.choose k
        = d.factorial * (n.choose k * k.choose d) := by ring
      _ = d.factorial * ((n - d).choose (k - d) * n.choose d) := by
            rw [choose_subset_of_subset hdk hkn]
      _ = (n - d).choose (k - d) * (d.factorial * n.choose d) := by ring
  exact_mod_cast congrArg (fun x : ℕ => (x : ℝ)) hnat

/-! ## 5.  The universal identity -/

private theorem sum_range_succ_split (g : ℕ → ℝ) (k : ℕ) :
    ∑ d ∈ range (k + 1), g d = g 0 + ∑ d ∈ Finset.Icc 1 k, g d := by
  rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (Nat.succ_pos k),
    ← Nat.Ico_succ_right]

theorem rowSum_uncentre (n : ℕ) (hn : n ≠ 0) (b : Fin n × Fin n → ℝ) :
    rowSum (uncentre n b) = fun i => 1 + rowSum (incr n b) i := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  funext i
  show (∑ j, (1 / (n : ℝ) + b (i, j))) = 1 + ∑ j, b (i, j)
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  field_simp

theorem colSum_uncentre (n : ℕ) (hn : n ≠ 0) (b : Fin n × Fin n → ℝ) :
    colSum (uncentre n b) = fun j => 1 + colSum (incr n b) j := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  funext j
  show (∑ i, (1 / (n : ℝ) + b (i, j))) = 1 + ∑ i, b (i, j)
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  field_simp

/-- The `E_k` half, from `SubDittertLinear.esym_one_add`. -/
theorem E_one_add (k n : ℕ) (hkn : k ≤ n) (v : Fin n → ℝ) :
    E k (fun i => 1 + v i) = ∑ d ∈ range (k + 1), sCoef k n d * esym d v := by
  have hD : ((n.choose k : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hkn).ne'
  rw [E, esym_one_add k hkn v, Finset.sum_div]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdk : d ≤ k := by
    have := Finset.mem_range.mp hd
    omega
  rw [sCoef_eq hdk hkn]
  field_simp

/-- The `P_k` half, from the `σ_k` rule of §3. -/
theorem P_one_add (k n : ℕ) (hkn : k ≤ n) (hn : n ≠ 0) (b : Fin n × Fin n → ℝ) :
    P k (uncentre n b) = ∑ d ∈ range (k + 1), tCoef k n d * sigmaK d (incr n b) := by
  have hD : ((n.choose k : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hkn).ne'
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  rw [P, sigmaK_one_add k n hn b, Finset.sum_div]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdk : d ≤ k := by
    have := Finset.mem_range.mp hd
    omega
  rw [tCoef, sCoef_eq hdk hkn, div_pow]
  field_simp
  exact Or.inl (by ring)

/-- **THE UNIVERSAL IDENTITY**, uniformly in `k` and `n`.  With `A = J_n/n + b` and `R`,
`C` the row and column sums of the increment `b`,

    (2 − k!/n^k) − [E_k(r) + E_k(c) − P_k(A)]
      = ∑_{d=1}^{k} [ t_d σ_d(b) − s_d (e_d(R) + e_d(C)) ].

Both halves are the coefficient rules of `NOTES.md` §6a.4: the `e_k` rule
(`SubDittertLinear.esym_one_add`) supplies the `s_d`, the `σ_k` rule (`sigmaK_one_add` of
§3) supplies the `t_d`.  The `d = 0` terms are what the constant `2 − k!/n^k` cancels,
which is why the sum starts at `1` — and that cancellation IS the centre identity
`SubDittertLinear.Fcent_zero`, now visible as the `d = 0` slice rather than as a separate
fact. -/
theorem universal_identity (k n : ℕ) (hkn : k ≤ n) (hn : n ≠ 0) (b : Fin n × Fin n → ℝ) :
    Fcent k n b
      = ∑ d ∈ Finset.Icc 1 k,
          (tCoef k n d * sigmaK d (incr n b)
            - sCoef k n d * (esym d (rowSum (incr n b)) + esym d (colSum (incr n b)))) := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hEr : E k (rowSum (uncentre n b))
      = ∑ d ∈ range (k + 1), sCoef k n d * esym d (rowSum (incr n b)) := by
    rw [rowSum_uncentre n hn b]
    exact E_one_add k n hkn _
  have hEc : E k (colSum (uncentre n b))
      = ∑ d ∈ range (k + 1), sCoef k n d * esym d (colSum (incr n b)) := by
    rw [colSum_uncentre n hn b]
    exact E_one_add k n hkn _
  have hPk := P_one_add k n hkn hn b
  have hcombine : Fcent k n b
      = (2 - ((k.factorial : ℕ) : ℝ) / (n : ℝ) ^ k)
        + ∑ d ∈ range (k + 1),
            (tCoef k n d * sigmaK d (incr n b)
              - sCoef k n d * (esym d (rowSum (incr n b)) + esym d (colSum (incr n b)))) := by
    have hsplit : ∑ d ∈ range (k + 1),
          (tCoef k n d * sigmaK d (incr n b)
            - sCoef k n d * (esym d (rowSum (incr n b)) + esym d (colSum (incr n b))))
        = (∑ d ∈ range (k + 1), tCoef k n d * sigmaK d (incr n b))
          - ((∑ d ∈ range (k + 1), sCoef k n d * esym d (rowSum (incr n b)))
            + ∑ d ∈ range (k + 1), sCoef k n d * esym d (colSum (incr n b))) := by
      rw [Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      congr 1
      exact Finset.sum_congr rfl fun d _ => by ring
    rw [Fcent, Phi, hEr, hEc, hPk, hsplit]
    ring
  rw [hcombine, sum_range_succ_split]
  have hzero : (tCoef k n 0 * sigmaK 0 (incr n b)
      - sCoef k n 0 * (esym 0 (rowSum (incr n b)) + esym 0 (colSum (incr n b))))
      = ((k.factorial : ℕ) : ℝ) / (n : ℝ) ^ k - 2 := by
    rw [tCoef, sCoef_zero, sigmaK_zero, esym_zero, esym_zero]
    norm_num
  rw [hzero]
  ring

/-! ## 6.  Specialisations

Two, in the order that matters.  First the identity is shown to subsume the centre
identity of `SubDittertLinear` — at `b = 0` every term of the sum dies, because every
summand carries a `σ_d` or an `e_d` with `d ≥ 1`.  Then that is read at `k = 3`, where it
is `SubDittertK3.Phi_uniform_k3`.

This is the hard checkpoint for this file: the general statement must come back to
something the `k = 3` development proves independently, and it does. -/

@[simp] theorem incr_zero (n : ℕ) : incr n (0 : Fin n × Fin n → ℝ) = 0 := rfl

/-- `σ_d` of the zero matrix vanishes for `d ≥ 1` — every subpermanent is a permanent of a
zero block.  At `d = 0` it is `1` instead, which is `sigmaK_zero`. -/
theorem sigmaK_zero_of_ne {d : ℕ} (hd : d ≠ 0) :
    sigmaK d (0 : Matrix (Fin n) (Fin n) ℝ) = 0 := by
  haveI : Nonempty (Fin d) := ⟨⟨0, Nat.pos_of_ne_zero hd⟩⟩
  unfold sigmaK subPerm
  refine Finset.sum_eq_zero fun S hS => Finset.sum_eq_zero fun T hT => ?_
  rw [dif_pos (Finset.mem_powersetCard_univ.mp hS),
    dif_pos (Finset.mem_powersetCard_univ.mp hT)]
  simp

/-- **The universal identity subsumes the centre identity.**  Every summand carries a
factor of degree at least `1` in `b`, so the whole right-hand side dies at the centre.
`SubDittertLinear.Fcent_zero` proves this from `Phi_uniform`; here it falls out of the
identity. -/
theorem Fcent_zero_of_universal (k n : ℕ) (hkn : k ≤ n) (hn : n ≠ 0) :
    Fcent k n 0 = 0 := by
  rw [universal_identity k n hkn hn 0]
  refine Finset.sum_eq_zero fun d hd => ?_
  have hd1 : d ≠ 0 := by
    have := Finset.mem_Icc.mp hd
    omega
  have hr : rowSum (0 : Matrix (Fin n) (Fin n) ℝ) = fun _ : Fin n => (0 : ℝ) := by
    funext i; simp [rowSum]
  have hc : colSum (0 : Matrix (Fin n) (Fin n) ℝ) = fun _ : Fin n => (0 : ℝ) := by
    funext j; simp [colSum]
  rw [incr_zero, sigmaK_zero_of_ne hd1, hr, hc, esym_of_zero hd1]
  ring

/-- The statement reached is exactly `SubDittertLinear.Fcent_zero`. -/
example (k n : ℕ) (hkn : k ≤ n) (hn : n ≠ 0) :
    SubDittertLinear.Fcent_zero k n hkn hn = Fcent_zero_of_universal k n hkn hn := rfl

/-- **The `k = 3` checkpoint.**  The universal identity, read at `k = 3` and `b = 0`, is
`SubDittertK3.Phi_uniform_k3`. -/
theorem k3_centre_from_universal (n : ℕ) (hn : 3 ≤ n) :
    Phi 3 (uniform n) = 2 - 6 / (n : ℝ) ^ 3 := by
  have h := Fcent_zero_of_universal 3 n hn (by omega)
  rw [Fcent, uncentre_zero] at h
  have h6 : ((Nat.factorial 3 : ℕ) : ℝ) = 6 := by norm_num [Nat.factorial]
  rw [h6] at h
  linarith

example (n : ℕ) (hn : 3 ≤ n) : k3_centre_from_universal n hn = Phi_uniform_k3 n hn := rfl

/-! ## 7.  Axiom audit

**Every declaration in this file depends only on `propext, Classical.choice,
Quot.sound`.**  In particular `sigmaK_one_add` does, which is what let
`SubDittertLinear`'s `sorry` of the same statement be deleted rather than left standing.
Build success is not an axiom audit, so the list is explicit.

No `native_decide` appears anywhere in this file. -/

section AxiomAudit

#print axioms sigP_emb
#print axioms sigmaK_emb
#print axioms sum_emb_restrict
#print axioms splitAt_inl
#print axioms sum_emb_restrict_subset
#print axioms sum_emb_pair_restrict
#print axioms sigmaK_uncentre
#print axioms sigmaK_one_add
#print axioms sigmaK_one_add_of_le
#print axioms sigmaK_zero
#print axioms sCoef_zero
#print axioms sCoef_eq
#print axioms rowSum_uncentre
#print axioms colSum_uncentre
#print axioms E_one_add
#print axioms P_one_add
#print axioms universal_identity
#print axioms incr_zero
#print axioms sigmaK_zero_of_ne
#print axioms Fcent_zero_of_universal
#print axioms k3_centre_from_universal

end AxiomAudit

end SubDittertUniversal
