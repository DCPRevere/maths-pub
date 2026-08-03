/-
# The layer identity: Stage 1

Target (Lemma 2 of `graded_stability_lemma.md`): for `A` doubly stochastic and `B = A − Jₙ/n`,

    σ_k(A)/C(n,k)² − k!/nᵏ  =  ∑_{m=2}^{k} t_m σ_m(B).

**Lemma 2 is proved here at every `k`,** as `layer_identity` (the source's own shape) and
`layer_identity_mul` (the same without dividing by `C(n,k)²`).

## What Lemma 2 actually needs

The hypotheses are `1 ≤ k ≤ n` and `∑∑ B = 0` — the entries of `B` sum to zero.  Nothing
else: not double stochasticity, not vanishing row and column sums separately, not
nonnegativity of `A`.  The source says as much ("the term `m = 1` vanishes because
`σ₁(B) = ∑ b_ij = 0`"), and `σ₁(B) = 0` is the only place any hypothesis on `B` is used.
Vanishing line sums imply the total vanishes, so the doubly stochastic case is a corollary.

**(2.2), the ratio law, is not used and not needed.**  The source folds the layer coefficients
into `t_m` by way of (2.2); §5 does it instead with `Nat.descFactorial_mul_descFactorial`,
`descFactorial(n−m, k−m) · descFactorial(n, m) = descFactorial(n, k)`, which is the whole
arithmetic content in one library lemma.  So (2.2) remains unformalised and this file does not
depend on it.

## Layout

* §1 the general-`k` rook bridge; §2 the multilinear expansion over subsets of `Fin k`;
* §3a the one-step fibre count, §3b its iteration to `descFactorial`, §3c the transport that
  makes the `B`-part depend only on a cardinality;
* §4 the master identity `k! σ_k(cJ + B) = ∑_m C(k,m) c^{k−m} descFactorial(n−m,k−m)² m! σ_m(B)`,
  which carries NO hypothesis at all — not even `k ≤ n`;
* §5 the two edge layers and the coefficient fold-in, giving Lemma 2.

## §1, the general-`k` rook bridge — DONE

`RookSum` proves `6 σ₃ = ∑_{f,g} ∏ A (f a) (g a)` over pairs of injections `Fin 3 ↪ Fin n`,
and the route to the layer identity needs that for every `k`.  It generalises: the `k = 3`
proof uses `Fin 3` only as a Fintype and `Equiv.Perm (Fin 3)` only as a group, and the sole
specialisation is the closing `3! = 6`.  `sigma_emb` below is the general statement.

`RookSum.perm_double` was `private` and fixed at `k = 3`; it is now public and general, so it
is imported rather than copied.  There is no duplicated proof: a proof living in two files that
cannot see each other is a drift hazard, and generalising in place was the cheaper fix.

## Why this bridge is the right opening move

With `σ_k` written over injections, the multilinear expansion of `per(X+Y)` becomes
`Fintype.prod_add` — `∏ a, (f a + g a) = ∑ t, (∏ a ∈ t, f a) * ∏ a ∈ tᶜ, g a` — applied over
subsets of `Fin k`, which is a *fixed finite* index set, instead of over subsets of `Fin n`
carrying order embeddings.  The remaining work is then a counting statement about injections,
the same shape as `RookSum.sum_fiber`, rather than an identity about submatrix permanents.
-/

import Mathlib.Tactic
import RookSum
import TverbergStability

open Finset

namespace LayerIdentity

variable {n k : ℕ}

/-- **The rook bridge at every `k`:** `∑_{f,g : Fin k ↪ Fin n} ∏ A (f a) (g a) = k! · σ_k(A)`.
This is `RookSum.sigma_three_emb` with `3` replaced by `k`. -/
theorem sigma_emb (A : Matrix (Fin n) (Fin n) ℝ) :
    (∑ f : Fin k ↪ Fin n, ∑ g : Fin k ↪ Fin n, ∏ a, A (f a) (g a))
      = (k.factorial : ℝ) * RookSum.sigP k A := by
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
  rw [RookSum.perm_double A hSk hTk, RookSum.subP_apply hSk hTk]

/-! ## §2  The multilinear expansion over subsets of `Fin k`

With `sigma_emb` in hand, `per` of a sum expands by `Fintype.prod_add` over subsets of the
FIXED index `Fin k`, which is what makes the layer identity tractable. -/

/-- The entrywise multilinear expansion, specialised to a matrix written as a sum.  Each pair
of injections contributes one term per subset `t ⊆ Fin k`, the `X`-part on `t` and the
`Y`-part on `tᶜ`. -/
theorem prod_add_expand (X Y : Matrix (Fin n) (Fin n) ℝ) (f g : Fin k → Fin n) :
    (∏ a, (X (f a) (g a) + Y (f a) (g a)))
      = ∑ t : Finset (Fin k),
          (∏ a ∈ t, X (f a) (g a)) * ∏ a ∈ tᶜ, Y (f a) (g a) :=
  Fintype.prod_add _ _

/-- The same, summed over pairs of injections: the left side is `k! σ_k(X+Y)` by
`sigma_emb`, so this is the first half of the layer identity. -/
theorem sigma_emb_add (X Y : Matrix (Fin n) (Fin n) ℝ) :
    (k.factorial : ℝ) * RookSum.sigP k (X + Y)
      = ∑ f : Fin k ↪ Fin n, ∑ g : Fin k ↪ Fin n,
          ∑ t : Finset (Fin k),
            (∏ a ∈ t, X (f a) (g a)) * ∏ a ∈ tᶜ, Y (f a) (g a) := by
  rw [← sigma_emb (X + Y)]
  refine Finset.sum_congr rfl fun f _ => Finset.sum_congr rfl fun g _ => ?_
  have : ∀ a : Fin k, (X + Y) (f a) (g a) = X (f a) (g a) + Y (f a) (g a) := fun a => rfl
  rw [Finset.prod_congr rfl fun a _ => this a]
  exact prod_add_expand X Y f g

/-- **The constant matrix is eliminated.**  Taking `X` constant — `X = Jₙ/n` is `c = 1/n` —
the `X`-part of every term collapses to `c^|t|`, leaving a sum over subsets of `Fin k` whose
only remaining content is the inner injection sum.  This reduces the layer identity to the
single counting statement recorded below. -/
theorem sigma_emb_const_add (c : ℝ) (B : Matrix (Fin n) (Fin n) ℝ) :
    (k.factorial : ℝ) * RookSum.sigP k (Matrix.of (fun _ _ => c) + B)
      = ∑ t : Finset (Fin k), c ^ t.card *
          ∑ f : Fin k ↪ Fin n, ∑ g : Fin k ↪ Fin n, ∏ a ∈ tᶜ, B (f a) (g a) := by
  rw [sigma_emb_add]
  have inner : ∀ f : Fin k ↪ Fin n,
      (∑ g : Fin k ↪ Fin n, ∑ t : Finset (Fin k),
          (∏ a ∈ t, Matrix.of (fun _ _ => c) (f a) (g a)) * ∏ a ∈ tᶜ, B (f a) (g a))
        = ∑ t : Finset (Fin k), ∑ g : Fin k ↪ Fin n,
            (∏ a ∈ t, Matrix.of (fun _ _ => c) (f a) (g a)) * ∏ a ∈ tᶜ, B (f a) (g a) :=
    fun _ => Finset.sum_comm
  rw [Finset.sum_congr rfl fun f _ => inner f, Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => ?_
  simp only [Matrix.of_apply, Finset.prod_const, ← Finset.mul_sum]

/-! ## §3a  The one-step fibre count

Dropping the first coordinate of an injection `Fin (j+1) ↪ Fin n` has fibres of constant size
`n − j`: the dropped value may be anything outside the range of what remains.

Mathlib supplies the whole construction, so nothing is built here, only applied.
`Equiv.embeddingFinSucc` is the decomposition
`(Fin (j+1) ↪ ι) ≃ Σ e : Fin j ↪ ι, {i // i ∉ Set.range e}`; `embeddingFinSucc_fst` says its
first component is precisely the restriction along `Fin.succ`; and
`coe_embeddingFinSucc_symm` gives the inverse as `Fin.cons`.  The fibre cardinality is
`Fintype.card_subtype_compl` in its PREDICATE form — `card_compl_set`, stated for a coerced set
complement, does not match the subtype the goal presents — followed by `Fintype.card_range`. -/

theorem sum_emb_succ (j : ℕ) (F : (Fin j → Fin n) → ℝ) :
    (∑ e : Fin (j + 1) ↪ Fin n, F (fun a => e a.succ))
      = (n - j) • ∑ e' : Fin j ↪ Fin n, F e' := by
  rw [← Equiv.sum_comp (Equiv.embeddingFinSucc j (Fin n)).symm
      (fun e : Fin (j + 1) ↪ Fin n => F (fun a => e a.succ))]
  have hsummand : ∀ p : Σ e' : Fin j ↪ Fin n, {i // i ∉ Set.range e'},
      F (fun a => ((Equiv.embeddingFinSucc j (Fin n)).symm p) a.succ) = F p.1 := by
    intro p
    have hfun : (fun a => ((Equiv.embeddingFinSucc j (Fin n)).symm p) a.succ)
        = (p.1 : Fin j → Fin n) := by
      funext a
      rw [show ((Equiv.embeddingFinSucc j (Fin n)).symm p : Fin (j + 1) → Fin n)
            = Fin.cons p.2.1 (p.1 : Fin j → Fin n) from Equiv.coe_embeddingFinSucc_symm p]
      simp
    rw [hfun]
  rw [Finset.sum_congr rfl fun p _ => hsummand p]
  rw [← Finset.univ_sigma_univ, Finset.sum_sigma]
  simp only [Finset.sum_const, Finset.card_univ, Finset.smul_sum]
  refine Finset.sum_congr rfl fun e' _ => ?_
  congr 1
  rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_range, Fintype.card_fin]

/-! ## §3b  Iterating the one-step count to `descFactorial`

`sum_emb_succ` drops the FIRST coordinate, so iterating it `d` times restricts an injection
`Fin (m + d) ↪ Fin n` to its LAST `m` coordinates.  `inclLast` is that inclusion, defined by
the recursion the iteration actually performs rather than by a closed form: the two type
equalities it needs, `m + 0 = m` and `m + (d+1) = (m + d) + 1`, both hold by `rfl` because
`Nat.add` recurses on its second argument.  Choosing `Fin (m + d)` over `Fin (d + m)` is what
makes this work; the latter would need a cast at every step.

No hypothesis relating `m`, `d` and `n` is needed here.  Both sides vanish when the injection
type is empty, and `Nat.descFactorial` truncates in step with it. -/

/-- The inclusion of the last `m` coordinates of `Fin (m + d)`, as iterated `Fin.succ`. -/
def inclLast (m : ℕ) : (d : ℕ) → Fin m → Fin (m + d)
  | 0 => id
  | d + 1 => fun a => (inclLast m d a).succ

@[simp] theorem inclLast_zero (m : ℕ) (a : Fin m) : inclLast m 0 a = a := rfl

@[simp] theorem inclLast_succ (m d : ℕ) (a : Fin m) :
    inclLast m (d + 1) a = (inclLast m d a).succ := rfl

theorem inclLast_injective (m d : ℕ) : Function.Injective (inclLast m d) := by
  induction d with
  | zero => exact fun a b h => h
  | succ d ih => exact fun a b h => ih (Fin.succ_injective _ h)

/-- **The fibre count over the last-`m` restriction.**  Iterating `sum_emb_succ`, the fibres
have constant size `descFactorial (n − m) d`. -/
theorem sum_emb_restrict (m d : ℕ) (F : (Fin m → Fin n) → ℝ) :
    (∑ e : Fin (m + d) ↪ Fin n, F (fun a => e (inclLast m d a)))
      = ((n - m).descFactorial d) • ∑ e' : Fin m ↪ Fin n, F e' := by
  induction d with
  | zero => simp
  | succ d ih =>
      have hstep := sum_emb_succ (n := n) (m + d)
        (fun w : Fin (m + d) → Fin n => F (fun a => w (inclLast m d a)))
      rw [show (∑ e : Fin (m + (d + 1)) ↪ Fin n, F (fun a => e (inclLast m (d + 1) a)))
            = ∑ e : Fin ((m + d) + 1) ↪ Fin n,
                (fun w : Fin (m + d) → Fin n => F (fun a => w (inclLast m d a)))
                  (fun b => e b.succ) from rfl, hstep, ih, smul_smul,
        Nat.descFactorial_succ, Nat.sub_sub]

/-! ## §3c  The `B`-part sum depends only on the cardinality

`sigma_emb_const_add` leaves one sum per subset `t ⊆ Fin k`, namely `Ψ(tᶜ)` below.  Two facts
finish it: `Ψ` is invariant under permuting `Fin k`, hence depends on the subset only through
its cardinality (`psi_image`, `psi_card_eq`); and at the canonical last-`m` block the two
injection sums collapse by §3b (`psi_canonical`).

`exists_perm_image` is the transport the route note calls "the perm action".  It needs no
bespoke construction: `Equiv.extendSubtype` extends an equivalence of two subtypes of a
fintype to a permutation of the whole, and builds the complement half itself through
`Equiv.toCompl`. -/

/-- `Ψ(S) = ∑_{f,g : Fin k ↪ Fin n} ∏_{a ∈ S} B (f a) (g a)`, the inner sum left by
`sigma_emb_const_add`. -/
noncomputable def Psi (B : Matrix (Fin n) (Fin n) ℝ) {k : ℕ} (S : Finset (Fin k)) : ℝ :=
  ∑ f : Fin k ↪ Fin n, ∑ g : Fin k ↪ Fin n, ∏ a ∈ S, B (f a) (g a)

theorem Psi_def (B : Matrix (Fin n) (Fin n) ℝ) {k : ℕ} (S : Finset (Fin k)) :
    Psi B S = ∑ f : Fin k ↪ Fin n, ∑ g : Fin k ↪ Fin n, ∏ a ∈ S, B (f a) (g a) := rfl

/-- **`Ψ` is invariant under permuting the index set.**  Precomposition with `σ` is a bijection
of the injections, and it moves the product from `S.image σ` to `S`. -/
theorem psi_image (B : Matrix (Fin n) (Fin n) ℝ) {k : ℕ} (S : Finset (Fin k))
    (σ : Equiv.Perm (Fin k)) : Psi B (S.image σ) = Psi B S := by
  have hprod : ∀ f g : Fin k ↪ Fin n,
      (∏ a ∈ S.image σ, B (f a) (g a)) = ∏ a ∈ S, B (f (σ a)) (g (σ a)) :=
    fun f g => Finset.prod_image (fun x _ y _ h => σ.injective h)
  let E : (Fin k ↪ Fin n) ≃ (Fin k ↪ Fin n) :=
    { toFun := fun f => σ.toEmbedding.trans f
      invFun := fun f => σ.symm.toEmbedding.trans f
      left_inv := by intro f; ext a; simp
      right_inv := by intro f; ext a; simp }
  have hE : ∀ (f : Fin k ↪ Fin n) (a : Fin k), (E f) a = f (σ a) := fun _ _ => rfl
  unfold Psi
  rw [Finset.sum_congr rfl fun f _ => Finset.sum_congr rfl fun g _ => hprod f g]
  have inner : ∀ f : Fin k ↪ Fin n,
      (∑ g : Fin k ↪ Fin n, ∏ a ∈ S, B (f (σ a)) (g (σ a)))
        = ∑ g : Fin k ↪ Fin n, ∏ a ∈ S, B (f (σ a)) (g a) :=
    fun f => Equiv.sum_comp E (fun g : Fin k ↪ Fin n => ∏ a ∈ S, B (f (σ a)) (g a))
  rw [Finset.sum_congr rfl fun f _ => inner f]
  exact Equiv.sum_comp E
    (fun f : Fin k ↪ Fin n => ∑ g : Fin k ↪ Fin n, ∏ a ∈ S, B (f a) (g a))

/-- **The transport.**  Any two equal-sized subsets of `Fin k` are related by a permutation. -/
theorem exists_perm_image {k : ℕ} {S T : Finset (Fin k)} (h : S.card = T.card) :
    ∃ σ : Equiv.Perm (Fin k), S.image σ = T := by
  classical
  have hcard : Fintype.card {x : Fin k // x ∈ S} = Fintype.card {x : Fin k // x ∈ T} := by
    simpa [Fintype.card_coe] using h
  refine ⟨(Fintype.equivOfCardEq hcard).extendSubtype,
    Finset.eq_of_subset_of_card_le ?_ ?_⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    exact Equiv.extendSubtype_mem (Fintype.equivOfCardEq hcard) y hy
  · rw [Finset.card_image_of_injective _ (Equiv.injective _), h]

/-- `Ψ` depends on the subset only through its cardinality. -/
theorem psi_card_eq (B : Matrix (Fin n) (Fin n) ℝ) {k : ℕ} {S T : Finset (Fin k)}
    (h : S.card = T.card) : Psi B S = Psi B T := by
  obtain ⟨σ, hσ⟩ := exists_perm_image h
  rw [← hσ, psi_image]

/-- The last `m` coordinates of `Fin (m + d)`. -/
def canonS (m d : ℕ) : Finset (Fin (m + d)) := Finset.univ.image (inclLast m d)

theorem canonS_card (m d : ℕ) : (canonS m d).card = m := by
  rw [canonS, Finset.card_image_of_injective _ (inclLast_injective m d), Finset.card_univ,
    Fintype.card_fin]

/-- **`Ψ` at the canonical block.**  Both injection sums collapse by §3b, and what is left is
`sigma_emb` at `m`. -/
theorem psi_canonical (B : Matrix (Fin n) (Fin n) ℝ) (m d : ℕ) :
    Psi B (canonS m d)
      = (((n - m).descFactorial d : ℕ) : ℝ) ^ 2 * ((m.factorial : ℕ) : ℝ)
        * RookSum.sigP m B := by
  have hprod : ∀ f g : Fin (m + d) ↪ Fin n,
      (∏ a ∈ canonS m d, B (f a) (g a))
        = ∏ x : Fin m, B (f (inclLast m d x)) (g (inclLast m d x)) :=
    fun f g => Finset.prod_image (fun x _ y _ h => inclLast_injective m d h)
  unfold Psi
  rw [Finset.sum_congr rfl fun f _ => Finset.sum_congr rfl fun g _ => hprod f g]
  have inner : ∀ f : Fin (m + d) ↪ Fin n,
      (∑ g : Fin (m + d) ↪ Fin n, ∏ x : Fin m, B (f (inclLast m d x)) (g (inclLast m d x)))
        = ((n - m).descFactorial d) • ∑ v : Fin m ↪ Fin n,
            ∏ x : Fin m, B (f (inclLast m d x)) (v x) :=
    fun f => sum_emb_restrict m d
      (fun w : Fin m → Fin n => ∏ x : Fin m, B (f (inclLast m d x)) (w x))
  rw [Finset.sum_congr rfl fun f _ => inner f, ← Finset.smul_sum,
    sum_emb_restrict m d
      (fun w : Fin m → Fin n => ∑ v : Fin m ↪ Fin n, ∏ x : Fin m, B (w x) (v x)),
    smul_smul, sigma_emb (k := m) B, nsmul_eq_mul]
  push_cast
  ring

/-- **The counting statement of §4, at every subset.**  `Ψ(S) = descFactorial(n−m, k−m)² · m! ·
σ_m(B)` where `m = |S|`. -/
theorem psi_eval (B : Matrix (Fin n) (Fin n) ℝ) {k m : ℕ} (S : Finset (Fin k))
    (hS : S.card = m) :
    Psi B S = (((n - m).descFactorial (k - m) : ℕ) : ℝ) ^ 2 * ((m.factorial : ℕ) : ℝ)
      * RookSum.sigP m B := by
  have hmk : m ≤ k := by
    rw [← hS]; simpa using Finset.card_le_univ S
  obtain ⟨d, rfl⟩ : ∃ d, k = m + d := ⟨k - m, by omega⟩
  rw [psi_card_eq B (T := canonS m d) (by rw [hS, canonS_card]), psi_canonical,
    show m + d - m = d from by omega]

/-! ## §4  Grouping the subsets by cardinality, and the master identity

`sigma_emb_const_add` leaves one term per subset `t ⊆ Fin k`.  By §3c that term depends on `t`
only through `|tᶜ|`, so the `2^k` subsets collapse to `k + 1` layers with multiplicity
`C(k,m)`.  Grouping by `|tᶜ|` rather than `|t|` is what avoids a reflection of the index at
the end: complementation is an involution of `Finset (Fin k)`, so the two groupings are the
same sum read two ways. -/

/-- Subsets of `Fin k` grouped by cardinality. -/
theorem sum_subsets_by_card {k : ℕ} (H : ℕ → ℝ) :
    (∑ t : Finset (Fin k), H t.card) = ∑ m ∈ Finset.range (k + 1), (k.choose m : ℝ) * H m := by
  rw [← Finset.powerset_univ, Finset.powerset_card_disjiUnion, Finset.sum_disjiUnion]
  have hcongr : ∀ (x : ℕ), ∀ t ∈ Finset.powersetCard x (univ : Finset (Fin k)),
      H t.card = H x := fun x t ht => by rw [Finset.mem_powersetCard_univ.1 ht]
  simp_rw [Finset.sum_congr rfl (hcongr _), Finset.sum_const, Finset.card_powersetCard,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- The same, grouped by the cardinality of the COMPLEMENT.  Complementation is an involution
of `Finset (Fin k)`, so this is the previous lemma read through that bijection. -/
theorem sum_subsets_by_compl_card {k : ℕ} (H : ℕ → ℝ) :
    (∑ t : Finset (Fin k), H tᶜ.card) = ∑ m ∈ Finset.range (k + 1), (k.choose m : ℝ) * H m := by
  rw [← sum_subsets_by_card H]
  exact Fintype.sum_equiv
    ⟨fun t => tᶜ, fun t => tᶜ, fun t => by simp, fun t => by simp⟩
    (fun t : Finset (Fin k) => H tᶜ.card) (fun t : Finset (Fin k) => H t.card) (fun _ => rfl)

/-- **The master layer identity.**  For every real `c` and every real `B`,

    k! · σ_k(cJ + B) = ∑_{m=0}^{k} C(k,m) c^{k−m} descFactorial(n−m, k−m)² m! σ_m(B).

This is the whole counting content of Lemma 2, with no hypothesis whatever: not `k ≤ n`, not
double stochasticity, not `c = 1/n`.  Both sides degenerate together outside the interesting
range — for `m > n` the subpermanent sum vanishes, and for `k − m > n − m` the descending
factorial does. -/
theorem sigma_layer_sum (c : ℝ) {k : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) :
    (k.factorial : ℝ) * RookSum.sigP k (Matrix.of (fun _ _ => c) + B)
      = ∑ m ∈ Finset.range (k + 1),
          (k.choose m : ℝ) * (c ^ (k - m)
            * (((n - m).descFactorial (k - m) : ℕ) : ℝ) ^ 2
            * ((m.factorial : ℕ) : ℝ) * RookSum.sigP m B) := by
  rw [sigma_emb_const_add]
  have hterm : ∀ t : Finset (Fin k),
      c ^ t.card * (∑ f : Fin k ↪ Fin n, ∑ g : Fin k ↪ Fin n, ∏ a ∈ tᶜ, B (f a) (g a))
        = c ^ (k - tᶜ.card) * (((n - tᶜ.card).descFactorial (k - tᶜ.card) : ℕ) : ℝ) ^ 2
            * ((tᶜ.card.factorial : ℕ) : ℝ) * RookSum.sigP tᶜ.card B := by
    intro t
    have hcompl : tᶜ.card = k - t.card := by
      rw [Finset.card_compl, Fintype.card_fin]
    have hle : t.card ≤ k := by
      simpa using Finset.card_le_univ t
    have hp := psi_eval B tᶜ (rfl : tᶜ.card = tᶜ.card)
    rw [Psi_def] at hp
    rw [hp, show k - tᶜ.card = t.card from by omega]
    ring
  rw [Finset.sum_congr rfl fun t _ => hterm t]
  exact sum_subsets_by_compl_card (fun m => c ^ (k - m)
    * (((n - m).descFactorial (k - m) : ℕ) : ℝ) ^ 2
    * ((m.factorial : ℕ) : ℝ) * RookSum.sigP m B)

/-! ## §5  The two edge layers, and the coefficient fold-in

Lemma 2 differs from §4's master identity in three bookkeeping steps: the `m = 0` layer is
`k!/nᵏ`, the `m = 1` layer vanishes, and the remaining coefficients are `t_m`.

The third step is where the source consumes the ratio law (2.2).  It is NOT needed: the whole
fold-in is `Nat.descFactorial_mul_descFactorial`, which says
`descFactorial(n−m, k−m) · descFactorial(n, m) = descFactorial(n, k)`.  With
`descFactorial(n,k) = k!·C(n,k)` and `(k−m)!·descFactorial(k,m) = k!` that is the entire
arithmetic content, so (2.2) never appears. -/

/-- `σ₀(X) = 1`: the empty submatrix has permanent `1`. -/
theorem sigP_zero (B : Matrix (Fin n) (Fin n) ℝ) : RookSum.sigP 0 B = 1 := by
  rw [RookSum.sigP]
  simp [RookSum.subP, Matrix.permanent]

/-- `σ₁(X) = ∑∑ X`.  With vanishing total this is the `m = 1` layer of Lemma 2. -/
theorem sigP_one (B : Matrix (Fin n) (Fin n) ℝ) :
    RookSum.sigP 1 B = ∑ i, ∑ j, B i j := by
  rw [RookSum.sigP]
  simp [RookSum.subP, Matrix.permanent, Finset.powersetCard_one]

/-- The `ℕ` identity behind the fold-in.  `C(n,k)·k!` is `descFactorial(n,k)`, which
`Nat.descFactorial_mul_descFactorial` splits at `m`. -/
theorem choose_factorial_eq {n k m : ℕ} (hmk : m ≤ k) :
    n.choose k * k.factorial = (n - m).descFactorial (k - m) * n.descFactorial m := by
  rw [mul_comm, ← Nat.descFactorial_eq_factorial_mul_choose]
  exact (Nat.descFactorial_mul_descFactorial (k := m) (m := k) (n := n) hmk).symm

/-- **The coefficient fold-in.**  The `m`-th coefficient of the master identity is
`k!·C(n,k)²·t_m`. -/
theorem tVal_coeff {n k m : ℕ} (hmk : m ≤ k) (hkn : k ≤ n) (hn : 0 < n) :
    ((k.choose m : ℕ) : ℝ) * ((1 / (n : ℝ)) ^ (k - m)
        * (((n - m).descFactorial (k - m) : ℕ) : ℝ) ^ 2 * ((m.factorial : ℕ) : ℝ))
      = ((k.factorial : ℕ) : ℝ) * ((n.choose k : ℕ) : ℝ) ^ 2
          * TverbergStability.tVal k n m := by
  have hnR : ((n : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hdn : ((n.descFactorial m : ℕ) : ℝ) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    intro h
    rw [Nat.descFactorial_eq_zero_iff_lt] at h
    omega
  have hF1 : (((n - m).descFactorial (k - m) : ℕ) : ℝ) * ((n.descFactorial m : ℕ) : ℝ)
      = ((n.choose k : ℕ) : ℝ) * ((k.factorial : ℕ) : ℝ) := by
    rw [← Nat.cast_mul, ← Nat.cast_mul, Nat.cast_inj]
    exact (choose_factorial_eq hmk).symm
  have hF3 : ((k.descFactorial m : ℕ) : ℝ)
      = ((m.factorial : ℕ) : ℝ) * ((k.choose m : ℕ) : ℝ) := by
    rw [← Nat.cast_mul, Nat.cast_inj]
    exact Nat.descFactorial_eq_factorial_mul_choose k m
  have hF2 : (((k - m).factorial : ℕ) : ℝ)
      * (((m.factorial : ℕ) : ℝ) * ((k.choose m : ℕ) : ℝ)) = ((k.factorial : ℕ) : ℝ) := by
    rw [← hF3, ← Nat.cast_mul, Nat.cast_inj]
    exact Nat.factorial_mul_descFactorial hmk
  have hD : (((n - m).descFactorial (k - m) : ℕ) : ℝ)
      = ((n.choose k : ℕ) : ℝ) * ((k.factorial : ℕ) : ℝ) / ((n.descFactorial m : ℕ) : ℝ) := by
    field_simp
    linarith [hF1]
  rw [TverbergStability.tVal, TverbergStability.sVal, hD, hF3, ← hF2]
  field_simp
  ring

/-- **Lemma 2, without division.**  For `1 ≤ k ≤ n` and `B = A − Jₙ/n`,

    σ_k(A) = C(n,k)² ( k!/nᵏ + ∑_{m=2}^{k} t_m σ_m(B) ).

The hypothesis on `B` is that its ENTRIES SUM TO ZERO, nothing more: not double
stochasticity, not vanishing row and column sums separately, not nonnegativity.  That is all
Lemma 2 consumes — through `σ₁(B) = 0` — and the source says as much.  Vanishing line sums
imply it. -/
theorem layer_identity_mul {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n)
    (A B : Matrix (Fin n) (Fin n) ℝ) (hAB : ∀ i j, A i j = 1 / (n : ℝ) + B i j)
    (hB : ∑ i, ∑ j, B i j = 0) :
    RookSum.sigP k A
      = ((n.choose k : ℕ) : ℝ) ^ 2 * (((k.factorial : ℕ) : ℝ) / (n : ℝ) ^ k
          + ∑ m ∈ Finset.Icc 2 k, TverbergStability.tVal k n m * RookSum.sigP m B) := by
  have hn : 0 < n := by omega
  have hnR : ((n : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hkf : ((k.factorial : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
  have hA : A = Matrix.of (fun _ _ => 1 / (n : ℝ)) + B := by
    ext i j; rw [hAB i j]; rfl
  have hmaster := sigma_layer_sum (n := n) (1 / (n : ℝ)) (k := k) B
  rw [← hA] at hmaster
  have hset : Finset.range (k + 1) = insert 0 (insert 1 (Finset.Icc 2 k)) := by
    ext x
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  rw [hset, Finset.sum_insert (by simp), Finset.sum_insert (by simp)] at hmaster
  have hdesc : ((n.descFactorial k : ℕ) : ℝ)
      = ((k.factorial : ℕ) : ℝ) * ((n.choose k : ℕ) : ℝ) := by
    rw [← Nat.cast_mul, Nat.cast_inj]
    exact Nat.descFactorial_eq_factorial_mul_choose n k
  -- the `m = 0` layer is `k!/nᵏ`, scaled
  have h0 : ((k.choose 0 : ℕ) : ℝ) * ((1 / (n : ℝ)) ^ (k - 0)
      * (((n - 0).descFactorial (k - 0) : ℕ) : ℝ) ^ 2 * ((Nat.factorial 0 : ℕ) : ℝ)
      * RookSum.sigP 0 B)
      = ((k.factorial : ℕ) : ℝ) * (((n.choose k : ℕ) : ℝ) ^ 2
          * (((k.factorial : ℕ) : ℝ) / (n : ℝ) ^ k)) := by
    rw [sigP_zero]
    simp only [Nat.choose_zero_right, Nat.sub_zero, Nat.factorial_zero, Nat.cast_one, mul_one,
      one_mul]
    rw [hdesc]
    field_simp
    ring
  -- the `m = 1` layer vanishes
  have h1 : ((k.choose 1 : ℕ) : ℝ) * ((1 / (n : ℝ)) ^ (k - 1)
      * (((n - 1).descFactorial (k - 1) : ℕ) : ℝ) ^ 2 * ((Nat.factorial 1 : ℕ) : ℝ)
      * RookSum.sigP 1 B) = 0 := by
    rw [sigP_one, hB]
    ring
  rw [h0, h1] at hmaster
  -- the remaining coefficients are `t_m`
  have htail : (∑ m ∈ Finset.Icc 2 k, ((k.choose m : ℕ) : ℝ) * ((1 / (n : ℝ)) ^ (k - m)
        * (((n - m).descFactorial (k - m) : ℕ) : ℝ) ^ 2 * ((m.factorial : ℕ) : ℝ)
        * RookSum.sigP m B))
      = ((k.factorial : ℕ) : ℝ) * (((n.choose k : ℕ) : ℝ) ^ 2
          * ∑ m ∈ Finset.Icc 2 k, TverbergStability.tVal k n m * RookSum.sigP m B) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hmk : m ≤ k := (Finset.mem_Icc.mp hm).2
    have := tVal_coeff (n := n) hmk hkn hn
    calc ((k.choose m : ℕ) : ℝ) * ((1 / (n : ℝ)) ^ (k - m)
            * (((n - m).descFactorial (k - m) : ℕ) : ℝ) ^ 2 * ((m.factorial : ℕ) : ℝ)
            * RookSum.sigP m B)
        = (((k.choose m : ℕ) : ℝ) * ((1 / (n : ℝ)) ^ (k - m)
            * (((n - m).descFactorial (k - m) : ℕ) : ℝ) ^ 2 * ((m.factorial : ℕ) : ℝ)))
            * RookSum.sigP m B := by ring
      _ = _ := by rw [this]; ring
  rw [htail] at hmaster
  refine mul_left_cancel₀ hkf ?_
  rw [hmaster]
  ring

/-- **Lemma 2, verbatim.**  `σ_k(A)/C(n,k)² − k!/nᵏ = ∑_{m=2}^{k} t_m σ_m(B)`. -/
theorem layer_identity {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n)
    (A B : Matrix (Fin n) (Fin n) ℝ) (hAB : ∀ i j, A i j = 1 / (n : ℝ) + B i j)
    (hB : ∑ i, ∑ j, B i j = 0) :
    RookSum.sigP k A / ((n.choose k : ℕ) : ℝ) ^ 2 - ((k.factorial : ℕ) : ℝ) / (n : ℝ) ^ k
      = ∑ m ∈ Finset.Icc 2 k, TverbergStability.tVal k n m * RookSum.sigP m B := by
  have hck : ((n.choose k : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.choose_pos hkn).ne'
  rw [layer_identity_mul hk hkn A B hAB hB]
  field_simp

/-! ## §6  Axiom audit

**Every declaration in this file depends only on axioms among `propext, Classical.choice,
Quot.sound`.**  No `native_decide`, no `sorry`. -/

section AxiomAudit

#print axioms sigma_emb
#print axioms prod_add_expand
#print axioms sigma_emb_add
#print axioms sigma_emb_const_add
#print axioms sum_emb_succ
#print axioms inclLast
#print axioms inclLast_zero
#print axioms inclLast_succ
#print axioms inclLast_injective
#print axioms sum_emb_restrict
#print axioms Psi
#print axioms Psi_def
#print axioms psi_image
#print axioms exists_perm_image
#print axioms psi_card_eq
#print axioms canonS
#print axioms canonS_card
#print axioms psi_canonical
#print axioms psi_eval
#print axioms sum_subsets_by_card
#print axioms sum_subsets_by_compl_card
#print axioms sigma_layer_sum
#print axioms sigP_zero
#print axioms sigP_one
#print axioms choose_factorial_eq
#print axioms tVal_coeff
#print axioms layer_identity_mul
#print axioms layer_identity

end AxiomAudit

end LayerIdentity
