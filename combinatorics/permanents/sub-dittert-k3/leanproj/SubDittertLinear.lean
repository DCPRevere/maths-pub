/-
# The linear side of the sub-Dittert certificate programme, uniformly in `k`

`SubDittertK3.lean` carries one instance of the certificate programme: `k = 3`, every
`n ≥ 4`, with the Gram matrices written out.  This file carries the part of the
programme that does *not* depend on `k`: the centre identity, and the structural
degeneracy of the coefficient-matching system that it is equivalent to.

Sources, both in this repository:

* `problems/permanents/uniform-lemma/results/paper_l.typ`, Lemma L1(e) (§`sec-syzygy`)
  — the degree-`0` row of the coefficient-matching system is identically zero, so the
  corank is at least `1`, and the system is consistent at that row if and only if the
  objective vanishes at the centre;
* `problems/permanents/sub-dittert/NOTES.md` §6a.4 — the coefficient rules in closed
  form in `k`.  Rule 1, the `e_k` rule, is `esym_one_add` below; its degree-`0` term is
  the `e_k` half of the centre identity.

## What is proved here

* `esym_one_add` — **the `e_k` coefficient rule, for every `k ≤ n`**: expanding
  `e_k` at the centre splits by degree with the binomial coefficients
  `C(n − d, k − d)`.  This is §6a.4's rule 1, stated so that no monomial bookkeeping
  is needed: the degree-`d` part is `e_d` of the increment.
* `Fcent_zero` — **the centre identity, for every `k ≤ n`**: the objective
  `(2 − k!/n^k) − Φ_k` vanishes at `J_n/n`.
* `colS0_zero`, `colSP_zero`, `colLam_zero` — every column of the coefficient-matching
  system is a polynomial with zero constant term.  The Gram-basis columns because the
  basis carries no constant monomial; the equality-multiplier columns because the
  equality of `K_n` is affine and vanishes at the centre.  This is derived from the
  monomial shape, not assumed.
* `row0_eq_zero`, `syzygy_vecMul`, `corank_ge_one`, `rows_not_linearIndependent` —
  **the degree-`0` row is identically zero and the syzygy is exhibited**: it is the
  standard basis vector at that row.
* `row0_consistent_iff`, `not_exists_certificate_of_centre_ne_zero` — **L1(e)'s
  equivalence**: the degree-`0` equation holds for one choice of the certificate
  unknowns if and only if it holds for every choice, if and only if the objective
  vanishes at the centre; and if it does not, no certificate of the ansatz shape
  exists at all.
* §6 — the `k = 3` specialisations, each an instance of a general statement above
  reproving something `SubDittertK3.lean` proves independently.

## What is NOT proved here, and is not claimed

L1(a)–(d) of the paper — that the row and column counts are `n`-free, that the entries
lie in `ℚ[n, n⁻¹]` with degree at most `2D`, and that the rank is the generic rank off a
finite set — are statements about orbit counts of a group action and about a matrix over
`ℚ(n)`.  Neither the representation stability nor the function field `ℚ(n)` appears in
this file, and nothing here should be read as evidence for them.  What is formalised is
L1(e) and the centre identity it is equivalent to.

The `σ_k` half of §6a.4's coefficient rules — the analogous expansion for the
subpermanent sum, `σ_k(J_n/n + b) = ∑_d C(n−d, k−d)² (k−d)! n^{−(k−d)} σ_d(b)` — stood
here as a `sorry` until it was proved in `SubDittertUniversal.lean`, which imports this
file; it is `SubDittertUniversal.sigmaK_one_add`.  Only its degree-`0` term is used
below, and that term is `SubDittertK3.sigmaK_uniform`.  **This file now carries no
`sorry`.**
-/
import SubDittertK3

open Finset

namespace SubDittertLinear

open SubDittertK3

variable {n : ℕ}

/-! ## 1.  The `e_k` coefficient rule, uniformly in `k`

`NOTES.md` §6a.4, rule 1.  In centred coordinates the row sums of `J_n/n + b` are
`1 + s_i`, so every coefficient of `e_k` at the centre is a count of the `k`-subsets
containing a fixed set of rows.  That count is the whole rule, and it is stated here
first. -/

/-- The `k`-subsets of `Fin n` containing a fixed `T` are in bijection with the
`(k − |T|)`-subsets of the complement, so there are `C(n − |T|, k − |T|)` of them.
This is the single count behind the `e_k` rule. -/
private theorem card_filter_superset (k : ℕ) (T : Finset (Fin n)) (hT : T.card ≤ k) :
    ((powersetCard k (univ : Finset (Fin n))).filter (fun S => T ⊆ S)).card
      = (n - T.card).choose (k - T.card) := by
  classical
  have hcompl : ((univ : Finset (Fin n)) \ T).card = n - T.card := by
    rw [Finset.card_sdiff (Finset.subset_univ T), Finset.card_univ, Fintype.card_fin]
  have h2 : (powersetCard (k - T.card) ((univ : Finset (Fin n)) \ T)).card
      = (n - T.card).choose (k - T.card) := by
    rw [Finset.card_powersetCard, hcompl]
  rw [← h2]
  refine Finset.card_bij' (fun S _ => S \ T) (fun U _ => U ∪ T) ?_ ?_ ?_ ?_
  · intro S hS
    simp only [Finset.mem_filter, Finset.mem_powersetCard_univ] at hS
    rw [Finset.mem_powersetCard]
    refine ⟨fun x hx => ?_, ?_⟩
    · simp only [Finset.mem_sdiff] at hx ⊢
      exact ⟨Finset.mem_univ x, hx.2⟩
    · rw [Finset.card_sdiff hS.2, hS.1]
  · intro U hU
    rw [Finset.mem_powersetCard] at hU
    have hdisj : Disjoint U T := by
      rw [Finset.disjoint_right]
      intro x hxT hxU
      exact (Finset.mem_sdiff.mp (hU.1 hxU)).2 hxT
    simp only [Finset.mem_filter, Finset.mem_powersetCard_univ]
    refine ⟨?_, Finset.subset_union_right⟩
    rw [Finset.card_union_of_disjoint hdisj, hU.2]
    omega
  · intro S hS
    simp only [Finset.mem_filter] at hS
    exact Finset.sdiff_union_of_subset hS.2
  · intro U hU
    rw [Finset.mem_powersetCard] at hU
    have hdisj : Disjoint U T := by
      rw [Finset.disjoint_right]
      intro x hxT hxU
      exact (Finset.mem_sdiff.mp (hU.1 hxU)).2 hxT
    exact Finset.union_sdiff_cancel_right hdisj

/-- Nothing of size `k` contains something bigger.  This is the clause that makes the
`e_k` rule stop at `d = k`; forgetting it gives `C(n − d, 0) = 1` for `d > k` and a
wrong rule. -/
private theorem filter_superset_eq_empty (k : ℕ) (T : Finset (Fin n)) (hT : k < T.card) :
    (powersetCard k (univ : Finset (Fin n))).filter (fun S => T ⊆ S) = ∅ := by
  classical
  refine Finset.eq_empty_of_forall_not_mem fun S hS => ?_
  simp only [Finset.mem_filter, Finset.mem_powersetCard_univ] at hS
  exact absurd (hS.1 ▸ Finset.card_le_card hS.2) (by omega)

/-- **The `e_k` coefficient rule, uniformly in `k`** (`NOTES.md` §6a.4, rule 1).

    e_k(1 + v)  =  ∑_{d ≤ k} C(n − d, k − d) · e_d(v).

At the centre the row sums of `J_n/n + b` are `1 + s`, so this is the promised
statement that the coefficient of a degree-`d` monomial of `e_k` is `C(n − d, k − d)`
when the `d` cells lie in distinct rows and `0` otherwise — the "distinct rows" clause
being carried here by `e_d`, whose monomials are exactly the squarefree ones. -/
theorem esym_one_add (k : ℕ) (hkn : k ≤ n) (v : Fin n → ℝ) :
    esym k (fun i => 1 + v i)
      = ∑ d ∈ range (k + 1), ((n - d).choose (k - d) : ℝ) * esym d v := by
  classical
  have step1 : esym k (fun i => 1 + v i)
      = ∑ S ∈ powersetCard k (univ : Finset (Fin n)), ∑ T ∈ S.powerset, ∏ i ∈ T, v i := by
    unfold esym
    refine Finset.sum_congr rfl fun S _ => ?_
    have hcomm : (fun i => (1 : ℝ) + v i) = fun i => v i + 1 := by
      funext i; exact add_comm _ _
    rw [hcomm, Finset.prod_add v (fun _ => (1 : ℝ)) S]
    exact Finset.sum_congr rfl fun T _ => by simp
  have step2 : ∀ S : Finset (Fin n), (∑ T ∈ S.powerset, ∏ i ∈ T, v i)
      = ∑ T ∈ (univ : Finset (Fin n)).powerset, (if T ⊆ S then ∏ i ∈ T, v i else 0) := by
    intro S
    rw [← Finset.sum_filter]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext T
    simp
  have step4 : ∀ T : Finset (Fin n),
      (∑ S ∈ powersetCard k (univ : Finset (Fin n)), (if T ⊆ S then ∏ i ∈ T, v i else 0))
        = (if T.card ≤ k then ((n - T.card).choose (k - T.card) : ℝ) else 0)
            * ∏ i ∈ T, v i := by
    intro T
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    by_cases h : T.card ≤ k
    · rw [card_filter_superset k T h, if_pos h]
    · rw [filter_superset_eq_empty k T (by omega), Finset.card_empty, if_neg h]
      simp
  rw [step1]
  simp only [step2]
  rw [Finset.sum_comm]
  simp only [step4]
  rw [Finset.sum_powerset, Finset.card_univ, Fintype.card_fin]
  have inner : ∀ j : ℕ, (∑ T ∈ powersetCard j (univ : Finset (Fin n)),
        (if T.card ≤ k then ((n - T.card).choose (k - T.card) : ℝ) else 0) * ∏ i ∈ T, v i)
      = (if j ≤ k then ((n - j).choose (k - j) : ℝ) else 0) * esym j v := by
    intro j
    unfold esym
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun T hT => ?_
    rw [Finset.mem_powersetCard_univ.mp hT]
  rw [Finset.sum_congr rfl fun j (_ : j ∈ range (n + 1)) => inner j]
  have hsub : range (k + 1) ⊆ range (n + 1) := by
    intro j hj
    simp only [Finset.mem_range] at hj ⊢
    omega
  rw [← Finset.sum_subset hsub (fun j _ hj => by
        simp only [Finset.mem_range] at hj
        rw [if_neg (by omega), zero_mul])]
  exact Finset.sum_congr rfl fun j hj => by
    simp only [Finset.mem_range] at hj
    rw [if_pos (by omega)]

/-! ### The rule at the centre

The degree-`0` term of `esym_one_add` is the `e_k` half of the centre identity: at
`J_n/n` every row sum is `1`, and `e_k` of the all-ones vector counts the `k`-subsets.
`SubDittertK3.esym_one` proves this directly; deriving it from the rule is the check
that the rule's `d = 0` coefficient is the right one. -/

theorem esym_zero (v : Fin n → ℝ) : esym 0 v = 1 := by
  unfold esym
  rw [Finset.powersetCard_zero]
  simp

theorem esym_of_zero {d : ℕ} (hd : d ≠ 0) : esym d (fun _ : Fin n => (0 : ℝ)) = 0 := by
  unfold esym
  refine Finset.sum_eq_zero fun S hS => ?_
  obtain ⟨i, hi⟩ := Finset.card_pos.mp
    (by rw [Finset.mem_powersetCard_univ.mp hS]; omega : 0 < S.card)
  exact Finset.prod_eq_zero hi rfl

/-- **The `e_k` half of the centre identity**, as the `d = 0` term of `esym_one_add`.
The statement is `SubDittertK3.esym_one`, which is proved there from the definition;
here it is read off the rule. -/
theorem esym_one_of_rule (k : ℕ) (hkn : k ≤ n) :
    (esym k fun _ : Fin n => (1 : ℝ)) = (n.choose k : ℝ) := by
  have h := esym_one_add (n := n) k hkn (fun _ => (0 : ℝ))
  simp only [add_zero] at h
  rw [h, Finset.sum_eq_single 0]
  · simp [esym_zero]
  · intro d _ hd
    rw [esym_of_zero hd, mul_zero]
  · intro h0
    exact absurd (Finset.mem_range.mpr (Nat.succ_pos k)) h0

/-! ## 2.  The centre identity, uniformly in `k` and `n`

`SubDittertK3.centre` sends a matrix to its centred coordinates `b = A − J_n/n`.  The
inverse is `uncentre`, and the objective read in those coordinates is `Fcent`.  The
centre identity is that `Fcent` vanishes at `0`.

This is the right-hand side of the degree-`0` row of §4: the conjectured bound is
attained at the centre, so the constant coefficient of the objective is zero. -/

/-- The matrix with centred coordinates `b`; the inverse of `SubDittertK3.centre`. -/
noncomputable def uncentre (n : ℕ) (b : Fin n × Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => 1 / (n : ℝ) + b (i, j)

@[simp] theorem uncentre_zero (n : ℕ) : uncentre n 0 = uniform n := by
  funext i j
  simp [uncentre, uniform]

@[simp] theorem centre_uncentre (n : ℕ) (b : Fin n × Fin n → ℝ) :
    centre n (uncentre n b) = b := by
  funext p
  obtain ⟨i, j⟩ := p
  simp [centre, uncentre]

@[simp] theorem uncentre_centre (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) :
    uncentre n (centre n A) = A := by
  funext i j
  simp [centre, uncentre]

/-- **The objective in centred coordinates**, uniformly in `k`:

    F(b) = (2 − k!/n^k) − Φ_k(J_n/n + b).

At `k = 3` this is `SubDittertK3.objPoly` composed with `uncentre`; see §6. -/
noncomputable def Fcent (k n : ℕ) (b : Fin n × Fin n → ℝ) : ℝ :=
  (2 - (k.factorial : ℝ) / (n : ℝ) ^ k) - Phi k (uncentre n b)

theorem Fcent_centre (k n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) :
    Fcent k n (centre n A) = (2 - (k.factorial : ℝ) / (n : ℝ) ^ k) - Phi k A := by
  unfold Fcent
  rw [uncentre_centre]

/-- **The centre identity, for every `k ≤ n`.**  The objective vanishes at the centre:
the conjectured bound `2 − k!/n^k` is exactly the value of `Φ_k` at `J_n/n`.

This is an identity in `k` and `n` and nothing else — no certificate, no `n ≥ 4`, no
positivity.  It is the right-hand side of the degree-`0` row of the coefficient-matching
system, and by `row0_consistent_iff` of §5 it is *equivalent* to that row being
solvable. -/
theorem Fcent_zero (k n : ℕ) (hkn : k ≤ n) (hn : n ≠ 0) : Fcent k n 0 = 0 := by
  unfold Fcent
  rw [uncentre_zero, Phi_uniform k hkn hn]
  ring

/-- The centre identity in the notation of Cheon–Hwang 1992. -/
theorem Phi_uniform_eq (k n : ℕ) (hkn : k ≤ n) (hn : n ≠ 0) :
    E k (rowSum (uniform n)) + E k (colSum (uniform n)) - P k (uniform n)
      = 2 - (k.factorial : ℝ) / (n : ℝ) ^ k :=
  Phi_uniform k hkn hn

/-! ## 3.  The certificate ansatz, and its columns

Hypothesis (H4) of the paper: the certificate is

    F  =  σ₀  +  ∑_p g_p · σ_p  +  ∑_m λ_m · h_m,

with `g_p(b) = 1/n + b_p` the facets of `K_n` in centred coordinates, `h(b) = ∑_q b_q`
its equality, and Gram bases of degree `e` *carrying no constant monomial*.  Writing the
identity out against the certificate unknowns, the polynomial each unknown multiplies is
one of three shapes.  Those are the columns of the coefficient-matching system, and the
whole of L1(e) is a statement about them.

Nothing here fixes `k`.  The only thing `k` controls is the degree `e` of the Gram
basis, and the statements below are indifferent to it: what they use is that each basis
element is a monomial of degree at least `1`. -/

/-- A monomial in the centred coordinates, given by the list of positions it multiplies,
with multiplicity.  Its degree is `L.length`; the empty list is the constant `1`.

Using a list rather than a `Finset` is deliberate: a Gram basis element at `k ≥ 4` has
degree `e ≥ 2` and may repeat a position, as in `b_p²`. -/
def mono (L : List (Fin n × Fin n)) (b : Fin n × Fin n → ℝ) : ℝ := (L.map b).prod

@[simp] theorem mono_nil (b : Fin n × Fin n → ℝ) : mono ([] : List (Fin n × Fin n)) b = 1 := rfl

@[simp] theorem mono_cons (q : Fin n × Fin n) (L : List (Fin n × Fin n))
    (b : Fin n × Fin n → ℝ) : mono (q :: L) b = b q * mono L b := rfl

/-- **"No constant monomial" is a property of the list, not an assumption.**  A monomial
of degree at least `1` vanishes at the centre. -/
theorem mono_zero {L : List (Fin n × Fin n)} (hL : L ≠ []) :
    mono L (0 : Fin n × Fin n → ℝ) = 0 := by
  obtain ⟨q, L', rfl⟩ := List.exists_cons_of_ne_nil hL
  simp

/-- The `σ₀` column at the Gram entry `(u, v)`: the polynomial the unknown `G₀[u,v]`
multiplies in the certificate identity. -/
def colS0 (Lu Lv : List (Fin n × Fin n)) (b : Fin n × Fin n → ℝ) : ℝ :=
  mono Lu b * mono Lv b

/-- The multiplier column at the facet `p` and the Gram entry `(u, v)`:
`g_p · m_u · m_v`, where `g_p(b) = 1/n + b_p` is the facet `a_p ≥ 0` of `K_n` read in
centred coordinates.  The `1/n` is the `n`-dependent offset of hypothesis (H2). -/
noncomputable def colSP (n : ℕ) (p : Fin n × Fin n) (Lu Lv : List (Fin n × Fin n))
    (b : Fin n × Fin n → ℝ) : ℝ :=
  (1 / (n : ℝ) + b p) * (mono Lu b * mono Lv b)

/-- The equality-multiplier column at the `λ`-monomial `L`: `m_L · h`, where
`h(b) = ∑_q b_q` is the equality `∑ a_ij = n` of `K_n` read in centred coordinates. -/
def colLam (L : List (Fin n × Fin n)) (b : Fin n × Fin n → ℝ) : ℝ :=
  mono L b * ∑ q, b q

/-- **The facet does not vanish at the centre.**  Stated so that the source of the
vanishing below is not mistaken: `g_p(0) = 1/n ≠ 0`, so `colSP` owes its zero constant
term entirely to the Gram basis, which is hypothesis (H4). -/
theorem facet_centre (n : ℕ) (hn : n ≠ 0) (p : Fin n × Fin n) :
    (1 / (n : ℝ) + (0 : Fin n × Fin n → ℝ) p) = 1 / (n : ℝ) ∧ (1 / (n : ℝ)) ≠ 0 := by
  refine ⟨by simp, ?_⟩
  have : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  positivity

theorem colS0_zero {Lu Lv : List (Fin n × Fin n)} (hu : Lu ≠ []) :
    colS0 Lu Lv (0 : Fin n × Fin n → ℝ) = 0 := by
  simp [colS0, mono_zero hu]

theorem colSP_zero (n : ℕ) (p : Fin n × Fin n) {Lu Lv : List (Fin n × Fin n)} (hu : Lu ≠ []) :
    colSP n p Lu Lv (0 : Fin n × Fin n → ℝ) = 0 := by
  simp [colSP, mono_zero hu]

/-- **The equality-multiplier columns need no hypothesis.**  They vanish at the centre
because `h` is affine with `h(0) = 0`, whatever the `λ`-monomial — including the constant
one.  This is the clause of L1(e) that is about the polytope and not about the Gram
basis. -/
@[simp] theorem colLam_zero (L : List (Fin n × Fin n)) :
    colLam L (0 : Fin n × Fin n → ℝ) = 0 := by
  simp [colLam]

/-- The columns of the coefficient-matching system: one per `σ₀` Gram entry, one per
(facet, multiplier Gram entry), one per `λ`-monomial. -/
abbrev AnsatzCols (n : ℕ) (ι κ μ : Type*) : Type _ :=
  (ι × ι) ⊕ ((Fin n × Fin n) × κ × κ) ⊕ μ

/-- The column polynomials of the ansatz (H4), indexed by `AnsatzCols`.  `m0`, `mP` and
`mL` are the `σ₀` Gram basis, the multiplier Gram basis and the `λ`-monomials, each given
as a monomial in the centred coordinates. -/
noncomputable def ansatzCol (n : ℕ) {ι κ μ : Type*}
    (m0 : ι → List (Fin n × Fin n)) (mP : κ → List (Fin n × Fin n))
    (mL : μ → List (Fin n × Fin n)) :
    AnsatzCols n ι κ μ → (Fin n × Fin n → ℝ) → ℝ
  | .inl (u, v) => colS0 (m0 u) (m0 v)
  | .inr (.inl (p, u, v)) => colSP n p (mP u) (mP v)
  | .inr (.inr t) => colLam (mL t)

/-- (H4) read off the columns: every column of the coefficient-matching system is a
polynomial in the centred coordinates with zero constant term. -/
def NoConstantColumns {Col : Type*} (P : Col → (Fin n × Fin n → ℝ) → ℝ) : Prop :=
  ∀ c, P c (0 : Fin n × Fin n → ℝ) = 0

/-- **The ansatz has no-constant columns.**  The hypothesis is exactly (H4)'s "Gram
bases carrying no constant monomial", and it is needed only for the two Gram families;
the `λ` family is exempt. -/
theorem ansatzCol_no_constant (n : ℕ) {ι κ μ : Type*}
    {m0 : ι → List (Fin n × Fin n)} {mP : κ → List (Fin n × Fin n)}
    (mL : μ → List (Fin n × Fin n))
    (h0 : ∀ u, m0 u ≠ []) (hP : ∀ u, mP u ≠ []) :
    NoConstantColumns (ansatzCol n m0 mP mL) := by
  rintro (⟨u, v⟩ | ⟨p, u, v⟩ | t)
  · exact colS0_zero (h0 u)
  · exact colSP_zero n p (hP u)
  · exact colLam_zero _

/-! ### The degree-`1` row is not degenerate

The natural over-reading of L1(e) — that the gradient of the objective also vanishes at
the centre, so a second syzygy should be free — is wrong, and the paper flags it.  The
reason is visible in the columns: along the ray `t · e_q` the Gram columns are `O(t²)`,
because each of their two monomial factors carries a `t`, but the equality-multiplier
column with constant `λ`-monomial is `h` itself, which is exactly `t`. -/

private theorem mono_ray {L : List (Fin n × Fin n)} (hL : L ≠ []) (q : Fin n × Fin n) (t : ℝ) :
    ∃ c : ℝ, mono L (fun r => if r = q then t else 0) = t * c := by
  obtain ⟨a, L', rfl⟩ := List.exists_cons_of_ne_nil hL
  by_cases h : a = q
  · refine ⟨mono L' (fun r => if r = q then t else 0), ?_⟩
    rw [mono_cons, if_pos h]
  · refine ⟨0, ?_⟩
    rw [mono_cons, if_neg h, zero_mul, mul_zero]

/-- Along the ray `t · e_q` a `σ₀` column is divisible by `t²`. -/
theorem colS0_ray {Lu Lv : List (Fin n × Fin n)} (hu : Lu ≠ []) (hv : Lv ≠ [])
    (q : Fin n × Fin n) (t : ℝ) :
    ∃ c : ℝ, colS0 Lu Lv (fun r => if r = q then t else 0) = t ^ 2 * c := by
  obtain ⟨cu, hcu⟩ := mono_ray hu q t
  obtain ⟨cv, hcv⟩ := mono_ray hv q t
  exact ⟨cu * cv, by rw [colS0, hcu, hcv]; ring⟩

/-- **The `λ` column with constant monomial is exactly `t` along the ray.**  So the
degree-`1` row of the system has a nonzero entry, and the vanishing of the gradient of
the objective at the centre produces no second syzygy. -/
theorem colLam_nil_ray (q : Fin n × Fin n) (t : ℝ) :
    colLam ([] : List (Fin n × Fin n)) (fun r => if r = q then t else 0) = t := by
  simp [colLam]

/-! ## 4.  The degree-`0` row, and the syzygy

The coefficient-matching system is indexed by orbits of monomials (rows) and by
certificate unknowns (columns); the entry is the coefficient of the row's orbit in the
column's polynomial.  Only one row is used below, and only one property of it: matching
the coefficient of the empty monomial is the linear functional "constant term", which on
a polynomial function of the centred coordinates is evaluation at the centre.  So the
system is carried here abstractly, with `ev` the family of coefficient functionals, and
the degree-`0` row identified by `ev r₀ = ev0`. -/

variable {Row Col : Type*}

/-- The coefficient functional of the degree-`0` row: the constant term, which on a
polynomial function is the value at the centre. -/
def ev0 (Q : (Fin n × Fin n → ℝ) → ℝ) : ℝ := Q (0 : Fin n × Fin n → ℝ)

/-- The coefficient-matching matrix: `ev r` applied to the column's polynomial. -/
def sysMat (ev : Row → ((Fin n × Fin n → ℝ) → ℝ) → ℝ)
    (P : Col → (Fin n × Fin n → ℝ) → ℝ) : Matrix Row Col ℝ :=
  fun r c => ev r (P c)

/-- The right-hand side of the coefficient-matching system: `ev r` applied to the
objective. -/
def sysRhs (ev : Row → ((Fin n × Fin n → ℝ) → ℝ) → ℝ) (F : (Fin n × Fin n → ℝ) → ℝ) :
    Row → ℝ :=
  fun r => ev r F

@[simp] theorem sysRhs_row0 {ev : Row → ((Fin n × Fin n → ℝ) → ℝ) → ℝ} {r0 : Row}
    (hev : ev r0 = ev0) (F : (Fin n × Fin n → ℝ) → ℝ) :
    sysRhs ev F r0 = F (0 : Fin n × Fin n → ℝ) := by
  rw [sysRhs, hev]; rfl

/-- **L1(e), first half: the degree-`0` row is identically zero.**  Every column is a
polynomial with zero constant term, so every entry of that row is zero. -/
theorem row0_eq_zero {ev : Row → ((Fin n × Fin n → ℝ) → ℝ) → ℝ}
    {P : Col → (Fin n × Fin n → ℝ) → ℝ} {r0 : Row}
    (hev : ev r0 = ev0) (hP : NoConstantColumns P) (c : Col) :
    sysMat ev P r0 c = 0 := by
  rw [sysMat, hev]
  exact hP c

/-- **The syzygy, exhibited.**  The left-null vector is the standard basis vector at the
degree-`0` row: no cancellation between rows is involved, the row is zero on its own. -/
theorem syzygy_vecMul [Fintype Row] [DecidableEq Row] [Fintype Col]
    {ev : Row → ((Fin n × Fin n → ℝ) → ℝ) → ℝ} {P : Col → (Fin n × Fin n → ℝ) → ℝ}
    {r0 : Row} (hev : ev r0 = ev0) (hP : NoConstantColumns P) :
    Matrix.vecMul (Pi.single r0 (1 : ℝ)) (sysMat ev P) = 0 := by
  rw [Matrix.single_vecMul]
  funext c
  rw [one_mul, row0_eq_zero hev hP c]
  rfl

/-- **L1(e): the corank is at least `1`.**  There is a nonzero vector annihilating every
column, so the rows of the coefficient-matching system are dependent — before any
question about the objective, and for every `k`. -/
theorem corank_ge_one [Fintype Row] [DecidableEq Row] [Fintype Col] [Nonempty Row]
    {ev : Row → ((Fin n × Fin n → ℝ) → ℝ) → ℝ} {P : Col → (Fin n × Fin n → ℝ) → ℝ}
    {r0 : Row} (hev : ev r0 = ev0) (hP : NoConstantColumns P) :
    ∃ y : Row → ℝ, y ≠ 0 ∧ Matrix.vecMul y (sysMat ev P) = 0 := by
  refine ⟨Pi.single r0 (1 : ℝ), ?_, syzygy_vecMul hev hP⟩
  intro h
  have h1 : (Pi.single r0 (1 : ℝ) : Row → ℝ) r0 = (0 : Row → ℝ) r0 := by rw [h]
  rw [Pi.single_eq_same] at h1
  exact one_ne_zero h1

/-- The same, as linear dependence of the rows. -/
theorem rows_not_linearIndependent [Fintype Row] [DecidableEq Row] [Fintype Col]
    {ev : Row → ((Fin n × Fin n → ℝ) → ℝ) → ℝ} {P : Col → (Fin n × Fin n → ℝ) → ℝ}
    {r0 : Row} (hev : ev r0 = ev0) (hP : NoConstantColumns P) :
    ¬ LinearIndependent ℝ (sysMat ev P) := by
  rw [Fintype.not_linearIndependent_iff]
  refine ⟨Pi.single r0 (1 : ℝ), ?_, r0, ?_⟩
  · funext c
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    rw [Finset.sum_eq_single r0]
    · rw [Pi.single_eq_same, one_mul]
      exact row0_eq_zero hev hP c
    · intro r _ hr
      rw [Pi.single_eq_of_ne hr, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ r0) h
  · rw [Pi.single_eq_same]
    exact one_ne_zero

/-- **The syzygy is not vacuous.**  A concrete row indexing: the degree-`0` row together
with any finite family of further coefficient functionals, whatever they are.  The
theorems above constrain only the degree-`0` row, which is the whole point — the syzygy
is one row on its own and needs no cancellation against the others. -/
theorem corank_ge_one_option {ρ : Type*} [Fintype ρ] [DecidableEq ρ]
    {Col : Type*} [Fintype Col]
    (evRest : ρ → ((Fin n × Fin n → ℝ) → ℝ) → ℝ)
    {P : Col → (Fin n × Fin n → ℝ) → ℝ} (hP : NoConstantColumns P) :
    ∃ y : Option ρ → ℝ, y ≠ 0 ∧
      Matrix.vecMul y (sysMat (fun r => Option.elim r ev0 evRest) P) = 0 :=
  corank_ge_one (r0 := none) rfl hP

/-! ## 5.  L1(e): the syzygy is the centre identity

The degree-`0` row reads `0 = F(centre)`.  Its left-hand side is zero for every choice of
the certificate unknowns, by §4; so the row is solvable exactly when its right-hand side
is zero, and that is the centre identity of §2.  This is the equivalence the paper puts
first: the single structural obstruction to solvability is identified, and it is a fact
known in advance. -/

/-- **L1(e), the equivalence.**  For any choice `x` of the certificate unknowns, the
degree-`0` equation of the system holds if and only if the objective vanishes at the
centre.  The choice does not enter — which is the content. -/
theorem row0_consistent_iff [Fintype Col]
    {ev : Row → ((Fin n × Fin n → ℝ) → ℝ) → ℝ} {P : Col → (Fin n × Fin n → ℝ) → ℝ}
    {r0 : Row} (hev : ev r0 = ev0) (hP : NoConstantColumns P)
    (F : (Fin n × Fin n → ℝ) → ℝ) (x : Col → ℝ) :
    (∑ c, sysMat ev P r0 c * x c = sysRhs ev F r0)
      ↔ F (0 : Fin n × Fin n → ℝ) = 0 := by
  have hzero : (∑ c, sysMat ev P r0 c * x c) = 0 :=
    Finset.sum_eq_zero fun c _ => by rw [row0_eq_zero hev hP c, zero_mul]
  rw [hzero, sysRhs_row0 hev]
  exact eq_comm

/-- **L1(e), the obstruction.**  If the objective does not vanish at the centre then no
certificate of the ansatz shape represents it — for any Gram matrices whatever, definite
or not.  The failure is structural and is not a failure of positivity. -/
theorem not_exists_certificate_of_centre_ne_zero [Fintype Col]
    {P : Col → (Fin n × Fin n → ℝ) → ℝ} (hP : NoConstantColumns P)
    {F : (Fin n × Fin n → ℝ) → ℝ} (hF : F (0 : Fin n × Fin n → ℝ) ≠ 0) :
    ¬ ∃ x : Col → ℝ, ∀ b, F b = ∑ c, x c * P c b := by
  rintro ⟨x, hx⟩
  refine hF ?_
  rw [hx 0]
  exact Finset.sum_eq_zero fun c _ => by rw [hP c, mul_zero]

/-- The same for the ansatz of §3, with (H4) spelled out: whatever `k`, whatever the
Gram matrices, the shape can only represent objectives that vanish at the centre. -/
theorem ansatz_forces_centre_zero (n : ℕ) {ι κ μ : Type*} [Fintype ι] [Fintype κ] [Fintype μ]
    {m0 : ι → List (Fin n × Fin n)} {mP : κ → List (Fin n × Fin n)}
    (mL : μ → List (Fin n × Fin n))
    (h0 : ∀ u, m0 u ≠ []) (hP : ∀ u, mP u ≠ [])
    {F : (Fin n × Fin n → ℝ) → ℝ}
    (hrep : ∃ x : AnsatzCols n ι κ μ → ℝ, ∀ b, F b = ∑ c, x c * ansatzCol n m0 mP mL c b) :
    F (0 : Fin n × Fin n → ℝ) = 0 := by
  by_contra hF
  exact not_exists_certificate_of_centre_ne_zero (ansatzCol_no_constant n mL h0 hP) hF hrep

/-- **The sub-Dittert system clears it, at every `k ≤ n`.**  The degree-`0` row is zero
by §4 and its right-hand side is zero by the centre identity of §2, so the row is
satisfied by every choice of the certificate unknowns. -/
theorem subDittert_row0_consistent (k : ℕ) (n : ℕ) (hkn : k ≤ n) (hn : n ≠ 0)
    {Row Col : Type*} [Fintype Col]
    {ev : Row → ((Fin n × Fin n → ℝ) → ℝ) → ℝ} {P : Col → (Fin n × Fin n → ℝ) → ℝ}
    {r0 : Row} (hev : ev r0 = ev0) (hP : NoConstantColumns P) (x : Col → ℝ) :
    ∑ c, sysMat ev P r0 c * x c = sysRhs ev (Fcent k n) r0 :=
  (row0_consistent_iff hev hP (Fcent k n) x).mpr (Fcent_zero k n hkn hn)

/-! ## 6.  The `k = 3` specialisation

The hard checkpoint: every general statement above must, at `k = 3`, come back to a fact
`SubDittertK3.lean` proves independently.  Two do.

* §2's centre identity at `k = 3` is `SubDittertK3.Phi_uniform_k3`, and the `example`
  below checks that the two statements are the same proposition.
* §4's syzygy, applied to `SubDittertK3`'s own certificate written in §3's columns, says
  the right-hand side of `SubDittertK3.certificate_identity` vanishes at the centre.
  With the identity itself that *reproves* `Phi_uniform_k3`, by a route that goes through
  the general machinery and not through `Phi_uniform`.

The `k = 3` Gram basis is the linear monomials `[u]`; that is the only place `k` enters,
and it enters as `m0 u ≠ []`. -/

section K3

/-- A quadratic form in §3's `σ₀` columns, with the Gram basis the linear monomials. -/
theorem quadForm_eq_sum_colS0 (G : Matrix (Fin n × Fin n) (Fin n × Fin n) ℝ)
    (b : Fin n × Fin n → ℝ) :
    Certificate.quadForm G b = ∑ u, ∑ v, G u v * colS0 [u] [v] b := by
  rw [Certificate.quadForm, Matrix.dotProduct]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Matrix.mulVec, Matrix.dotProduct, Finset.mul_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp only [colS0, mono_cons, mono_nil, mul_one]
  ring

/-- A quadratic form times a facet, in §3's multiplier columns. -/
theorem quadForm_mul_facet_eq_sum_colSP (n : ℕ)
    (H : Matrix (Fin n × Fin n) (Fin n × Fin n) ℝ) (p : Fin n × Fin n)
    (b : Fin n × Fin n → ℝ) :
    Certificate.quadForm H b * (1 / (n : ℝ) + b p)
      = ∑ u, ∑ v, H u v * colSP n p [u] [v] b := by
  rw [quadForm_eq_sum_colS0, Finset.sum_mul]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp only [colS0, colSP]
  ring

/-- **`SubDittertK3`'s certificate is an instance of §3's ansatz.**  Its right-hand side,
rewritten in the columns of §3: `G0` supplies the `σ₀` columns and `Hm p` the multiplier
columns at the facet `p`.  The `λ` family does not appear because `certificate_identity`
is stated on `K_n`, where `∑ b = 0` kills it. -/
theorem k3_rhs_eq_columns (n : ℕ) (b : Fin n × Fin n → ℝ) :
    Certificate.quadForm (G0 n) b
        + ∑ p : Fin n × Fin n, Certificate.quadForm (Hm n p) b * (1 / (n : ℝ) + b p)
      = (∑ u, ∑ v, G0 n u v * colS0 [u] [v] b)
        + ∑ p : Fin n × Fin n, ∑ u, ∑ v, Hm n p u v * colSP n p [u] [v] b := by
  rw [quadForm_eq_sum_colS0]
  exact congrArg _ (Finset.sum_congr rfl fun p _ =>
    quadForm_mul_facet_eq_sum_colSP n (Hm n p) p b)

/-- **The `k = 3` certificate's right-hand side vanishes at the centre**, by §3's
column-vanishing lemmas and not by unfolding `G0` or `Hm`. -/
theorem k3_rhs_centre_zero (n : ℕ) :
    Certificate.quadForm (G0 n) (0 : Fin n × Fin n → ℝ)
        + ∑ p : Fin n × Fin n,
            Certificate.quadForm (Hm n p) (0 : Fin n × Fin n → ℝ)
              * (1 / (n : ℝ) + (0 : Fin n × Fin n → ℝ) p)
      = 0 := by
  have hne : ∀ u : Fin n × Fin n, ([u] : List (Fin n × Fin n)) ≠ [] :=
    fun u => List.cons_ne_nil u []
  have h1 : (∑ u, ∑ v, G0 n u v * colS0 [u] [v] (0 : Fin n × Fin n → ℝ)) = 0 :=
    Finset.sum_eq_zero fun u _ => Finset.sum_eq_zero fun v _ => by
      rw [colS0_zero (hne u), mul_zero]
  have h2 : (∑ p : Fin n × Fin n, ∑ u, ∑ v,
      Hm n p u v * colSP n p [u] [v] (0 : Fin n × Fin n → ℝ)) = 0 :=
    Finset.sum_eq_zero fun p _ => Finset.sum_eq_zero fun u _ => Finset.sum_eq_zero fun v _ => by
      rw [colSP_zero n p (hne u), mul_zero]
  rw [k3_rhs_eq_columns, h1, h2, add_zero]

/-- **The `k = 3` checkpoint, through the syzygy.**  `SubDittertK3.obj_identity` says the
objective equals the certificate's right-hand side on `K_n`; `k3_rhs_centre_zero` says
that right-hand side vanishes at the centre; `J_n/n` is in `K_n` and is the centre.  The
conclusion is `SubDittertK3.Phi_uniform_k3`, reached without `Phi_uniform`. -/
theorem k3_centre_from_syzygy (n : ℕ) (hn : 4 ≤ n) :
    Phi 3 (uniform n) = 2 - 6 / (n : ℝ) ^ 3 := by
  have hmem : uniform n ∈ Kn n := uniform_mem_Kn (by omega)
  have hid := obj_identity n hn (uniform n) hmem
  rw [centre_uniform_eq_zero] at hid
  have hsum : (∑ p : Fin n × Fin n,
      Certificate.quadForm (Hm n p) (0 : Fin n × Fin n → ℝ) * uniform n p.1 p.2)
      = ∑ p : Fin n × Fin n, Certificate.quadForm (Hm n p) (0 : Fin n × Fin n → ℝ)
          * (1 / (n : ℝ) + (0 : Fin n × Fin n → ℝ) p) :=
    Finset.sum_congr rfl fun p _ => by simp [uniform]
  rw [hsum, k3_rhs_centre_zero n] at hid
  linarith

/-- The statement reached above is exactly `SubDittertK3.Phi_uniform_k3`.  That this
`example` type-checks is the check; proof irrelevance makes the equality `rfl` only when
the two propositions are the same. -/
example (n : ℕ) (hn : 4 ≤ n) :
    k3_centre_from_syzygy n hn = Phi_uniform_k3 n (le_trans (by norm_num) hn) := rfl

/-- **The `k = 3` checkpoint, through the centre identity.**  §2's `Fcent_zero` read at
`k = 3`, with `3! = 6`. -/
theorem k3_centre_from_Fcent (n : ℕ) (hn : 3 ≤ n) :
    Phi 3 (uniform n) = 2 - 6 / (n : ℝ) ^ 3 := by
  have h := Fcent_zero 3 n hn (by omega)
  rw [Fcent, uncentre_zero] at h
  have h6 : ((Nat.factorial 3 : ℕ) : ℝ) = 6 := by norm_num [Nat.factorial]
  rw [h6] at h
  linarith

example (n : ℕ) (hn : 3 ≤ n) : k3_centre_from_Fcent n hn = Phi_uniform_k3 n hn := rfl

/-- The `k = 3` ansatz satisfies (H4): the Gram basis is the linear monomials, which are
nonempty lists, so `ansatzCol_no_constant` applies with the `λ`-monomials left
unrestricted. -/
theorem k3_noConstantColumns (n : ℕ) :
    NoConstantColumns (ansatzCol n (fun u : Fin n × Fin n => [u]) (fun u : Fin n × Fin n => [u])
      (fun L : List (Fin n × Fin n) => L)) :=
  ansatzCol_no_constant n _ (fun u => List.cons_ne_nil u []) (fun u => List.cons_ne_nil u [])

end K3

/-! ## 7.  The centred increment

The `σ_k` half of §6a.4's coefficient rules used to stand here as a `sorry`.  It is
proved, as `SubDittertUniversal.sigmaK_one_add` in the file that imports this one, and
the declaration has been deleted rather than left standing — a `sorry` whose statement is
a theorem elsewhere is a false signpost.  What remains here is the definition the rule is
stated with, which §6 of `SubDittertUniversal` also uses. -/

/-- The centred increment as a matrix. -/
noncomputable def incr (n : ℕ) (b : Fin n × Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => b (i, j)

/-! ## 8.  Axiom audit

**Every declaration depends only on `propext, Classical.choice, Quot.sound`.**  Build
success is not an axiom audit — a `sorry` anywhere can leak `sorryAx` into declarations
that never mention it — so every theorem is listed rather than the file's lack of a
`sorry` being taken as evidence.

No `native_decide` appears anywhere in this file. -/

section AxiomAudit

#print axioms esym_one_add
#print axioms esym_zero
#print axioms esym_of_zero
#print axioms esym_one_of_rule
#print axioms uncentre_zero
#print axioms centre_uncentre
#print axioms uncentre_centre
#print axioms Fcent_centre
#print axioms Fcent_zero
#print axioms Phi_uniform_eq
#print axioms mono_nil
#print axioms mono_cons
#print axioms mono_zero
#print axioms facet_centre
#print axioms colS0_zero
#print axioms colSP_zero
#print axioms colLam_zero
#print axioms ansatzCol_no_constant
#print axioms colS0_ray
#print axioms colLam_nil_ray
#print axioms sysRhs_row0
#print axioms row0_eq_zero
#print axioms syzygy_vecMul
#print axioms corank_ge_one
#print axioms rows_not_linearIndependent
#print axioms corank_ge_one_option
#print axioms row0_consistent_iff
#print axioms not_exists_certificate_of_centre_ne_zero
#print axioms ansatz_forces_centre_zero
#print axioms subDittert_row0_consistent
#print axioms quadForm_eq_sum_colS0
#print axioms quadForm_mul_facet_eq_sum_colSP
#print axioms k3_rhs_eq_columns
#print axioms k3_rhs_centre_zero
#print axioms k3_centre_from_syzygy
#print axioms k3_centre_from_Fcent
#print axioms k3_noConstantColumns

end AxiomAudit

end SubDittertLinear
