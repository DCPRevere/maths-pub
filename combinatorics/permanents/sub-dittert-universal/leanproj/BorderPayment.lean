/-
# The border-row refinement: the exact payment, and the constant `G(n,m)`

`LIFT.md` §B.12 replaces Gurvits' per-variable charge `g(n)^m` by the single-coefficient charge
`G(n,m)`, and Theorem H′ records that the refined constant collapses the frontier at **every**
`k`.  Its proof is one line of factorial arithmetic:

> *Proof.*  Both sides reduce to `n! m! C(n,m) = (m!)^2 C(n,k)^2 k!`, which is
> `C(n,m) = C(n,k)` together with `C(n,k) = n!/(k! m!)`. ∎

That identity is `exact_payment` below, with `m = n - k`.  It is the same identity that
`graded_verify_borderrows.py` block [1] checks (`ok_alg`), and both sides equal `(n!)^2 / k!` —
recorded here in the cleared form `exact_payment_mul` so that no division appears.

## What is here

| § | content |
|---|---|
| 1 | `exact_payment`, `exact_payment_mul` — pure `ℕ`, from `Nat.choose_mul_factorial_mul_factorial` |
| 2 | `G`, the Lemma U constant, over `ℚ`, with `G(n,0) = G(n,n) = 1` and `G(n,1) = ((n-1)/n)^(n-1)` |

`G(n,1) = g(n)` and `G(n,0) = G(n,n) = 1` are exactly the degeneration recorded in §B.12.1 —
"the refinement reduces to `CAPACITY.md` §2.4 exactly at `m = 0, 1`" — and are the two lines
where the old labelling was already sharp.  `graded_verify_borderrows.py` block [3] is the
numerical form of §2 below.

Nothing here imports Lemma U itself, which is `[R]` (Csikvári–Schweitzer Lemma 2.8 /
Brändén–Leake–Pak Cor. 5.9); only its constant and the bookkeeping that consumes it.

## STONE 14 (Lemma U) IS NOW LANDED — see `LemmaU.lean`

The resistance recorded here earlier is discharged.  Both blockers turned out smaller than
flagged:

1. **The Vieta bridge** needed no new general `Finset` lemma.  Mathlib already carries the
   coefficient form as `Finset.prod_X_add_C_coeff`, and it is the tree's `esymF` on the nose.
2. **The window** splits cleanly once `d_t/d_m <= rho^{t-m}` is carried in the cleared form
   `d_t rho^m <= d_m rho^t`: two monotone ratio inductions, one degenerate branch between them,
   and `rho = d_{m+1}/d_m` discharges the window hypothesis outright.

`LemmaU.lemmaU_of_pos` is the statement, at `0 < m < n` with `c_m > 0` — exactly the live range
of `R_new` (`m = n-k`, `1 <= m <= n-3`).  Its header records why the excluded ends need a limit
argument rather than a certificate.

Consequence for stone 15, unchanged: `theoremHprime` below is unconditional, but Theorem G'
still is not stated, because it needs the H-stability closure A12 (stones 11-12, out of scope by
instruction) on top of stone 14 and `Gurvits.GurvitsBound`.
`graded_verify_borderrows.py` block [4] remains unmirrored in Lean; block [2] is now half
mirrored (`LemmaU.G_sharp`).
-/

import Mathlib.Tactic

open Nat

namespace BorderPayment

/-! ## §1  The exact payment

`LIFT.md` §B.12.2, Theorem H′: `n! m! C(n,m) = (m!)^2 C(n,k)^2 k!` at `m = n - k`. -/

/-- **Theorem H′, the arithmetic core.**  With `m = n - k` and `k ≤ n`,

    n! · m! · C(n,m)  =  (m!)^2 · C(n,k)^2 · k! .

Both sides are `(n!)^2 / k!`; see `exact_payment_mul` for the division-free form. -/
theorem exact_payment {n k : ℕ} (hk : k ≤ n) :
    n ! * (n - k)! * n.choose (n - k) = ((n - k)!) ^ 2 * (n.choose k) ^ 2 * k ! := by
  have hfact : n.choose k * k ! * (n - k)! = n ! :=
    Nat.choose_mul_factorial_mul_factorial hk
  rw [Nat.choose_symm hk, ← hfact]
  ring

/-- Both sides of `exact_payment` are `(n!)^2 / k!`, in cleared form. -/
theorem exact_payment_mul {n k : ℕ} (hk : k ≤ n) :
    k ! * (n ! * (n - k)! * n.choose (n - k)) = n ! * n ! := by
  have hfact : n.choose k * k ! * (n - k)! = n ! :=
    Nat.choose_mul_factorial_mul_factorial hk
  calc k ! * (n ! * (n - k)! * n.choose (n - k))
      = n ! * (n.choose k * k ! * (n - k)!) := by rw [Nat.choose_symm hk]; ring
    _ = n ! * n ! := by rw [hfact]

/-- The right-hand side of `exact_payment` is `(n!)^2 / k!` too — immediate, but stated so the
"both sides are `(n!)^2/k!`" reading of §B.12.2 is available directly. -/
theorem exact_payment_mul' {n k : ℕ} (hk : k ≤ n) :
    k ! * (((n - k)!) ^ 2 * (n.choose k) ^ 2 * k !) = n ! * n ! := by
  rw [← exact_payment hk]
  exact exact_payment_mul hk

/-! ## §2  The Lemma U constant `G(n,m)`

`LIFT.md` §B.12.1:

    G(n,m) = C(n,m) · m^m · (n-m)^(n-m) / n^n .

Lean's `0 ^ 0 = 1` is exactly the convention the formula needs at `m = 0` and `m = n`. -/

/-- **`LIFT.md` §B.12.1.**  `G(n,m) = C(n,m) m^m (n-m)^(n-m) / n^n`, the sharp constant of
Lemma U (Csikvári–Schweitzer Lemma 2.8 / Brändén–Leake–Pak Cor. 5.9). -/
def G (n m : ℕ) : ℚ :=
  (n.choose m : ℚ) * (m : ℚ) ^ m * ((n - m : ℕ) : ℚ) ^ (n - m) / (n : ℚ) ^ n

theorem G_nonneg (n m : ℕ) : 0 ≤ G n m := by
  unfold G
  positivity

/-- `G(n,0) = 1`: the refinement is a no-op at `m = 0`, `LIFT.md` §B.14.1. -/
@[simp] theorem G_zero (n : ℕ) : G n 0 = 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · norm_num [G]
  · have hn' : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
    simp [G, div_self (pow_ne_zero n hn')]

/-- `G(n,n) = 1`. -/
@[simp] theorem G_self (n : ℕ) : G n n = 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · norm_num [G]
  · have hn' : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
    simp [G, div_self (pow_ne_zero n hn')]

/-- `G(n,1) = ((n-1)/n)^(n-1) = g(n)`, Gurvits' classical single-variable factor.  The
refinement degenerates to `CAPACITY.md` §2.4 exactly here. -/
theorem G_one {n : ℕ} (hn : 1 ≤ n) : G n 1 = (((n : ℚ) - 1) / (n : ℚ)) ^ (n - 1) := by
  have hn0 : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hcast : ((n - 1 : ℕ) : ℚ) = (n : ℚ) - 1 := by
    push_cast [Nat.cast_sub hn]
    ring
  have hsplit : (n : ℚ) ^ n = (n : ℚ) ^ (n - 1) * (n : ℚ) := by
    rw [← pow_succ]
    congr 1
    omega
  rw [G, Nat.choose_one_right, hcast, hsplit, div_pow]
  have hne : ((n : ℚ) ^ (n - 1)) ≠ 0 := pow_ne_zero _ hn0
  field_simp
  ring

/-! ## §3  Theorem H′ — the collapse, `LEAN-ROADMAP.md` stone 15 (second half)

`LIFT.md` §B.12.2:

> **Theorem H′ (the collapse).**  `C_new(n,k) cap_0 = (m!)^2 C(n,k)^2 gamma` **exactly**, i.e.
> `rho_new(n,k) = 1` at **every** `k`.

The constants are transcribed from `graded_verify_borderrows.py` (`gamma`, `cap0`, `C_ref`,
`C_new`, `rho_of`), and block [1] is what `rho_new_eq_one` reproduces in the kernel.

**Only the H′ half of stone 15 lands here.**  Theorem G′ itself —
`per(M_k(A)) ≥ C_new(n,k) cap(M_k(A))` — consumes `Gurvits.GurvitsBound` (stone 13, stated),
Lemma U (stone 14, owed) and the H-stability closure A12 (stones 11–12, deliberately deferred),
so it is not stated here.  What H′ says is that once G′ is available the constant is EXACTLY
right — no slack anywhere on the `(k,n)` plane — and that is a fact about factorials alone. -/

/-- `gamma = k!/n^k`. -/
def gammaC (n k : ℕ) : ℚ := (k.factorial : ℚ) / (n : ℚ) ^ k

/-- `cap_0 = n^(2n-k)/k^k`, the capacity on the doubly stochastic face (`CAPACITY.md`
Lemma C).  Only its value enters H′; the convex-analysis proof that locates the minimiser is
NOT load-bearing anywhere on the chain (`LEAN-ROADMAP.md` A4). -/
def cap0 (n k : ℕ) : ℚ := (n : ℚ) ^ (2 * n - k) / (k : ℚ) ^ k

/-- `C_ref(n,k) = (n!/n^n) ((n-1)/n)^((n-1)(n-k))`, the old per-border-variable charge of
`CAPACITY.md` §2.4. -/
def C_ref (n k : ℕ) : ℚ :=
  ((n.factorial : ℚ) / (n : ℚ) ^ n) * (((n : ℚ) - 1) / (n : ℚ)) ^ ((n - 1) * (n - k))

/-- `C_new(n,k) = (n!/n^n) m! G(n,m)/m^m`, the refined constant of Theorem G′. -/
def C_new (n k : ℕ) : ℚ :=
  ((n.factorial : ℚ) / (n : ℚ) ^ n) * (((n - k).factorial : ℚ)) * G n (n - k)
    / ((n - k : ℕ) : ℚ) ^ (n - k)

/-- `m^m ≠ 0` at every `m`, including `m = 0` where Lean's `0^0 = 1`. -/
theorem pow_self_ne_zero (m : ℕ) : ((m : ℚ)) ^ m ≠ 0 := by
  rcases Nat.eq_zero_or_pos m with rfl | h
  · norm_num
  · exact pow_ne_zero _ (Nat.cast_ne_zero.mpr h.ne')

/-- The refined constant in cleared form: every power of `m` cancels, and `C_new` is a
factorial expression over `n^n · n^n`. -/
theorem C_new_mul {n k : ℕ} (hkn : k ≤ n) :
    C_new n k * (n : ℚ) ^ n * (n : ℚ) ^ n
      = (n.factorial : ℚ) * ((n - k).factorial : ℚ) * (n.choose (n - k) : ℚ) * (k : ℚ) ^ k := by
  have hnz : (n : ℚ) ≠ 0 ∨ n = 0 := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · exact Or.inr rfl
    · exact Or.inl (Nat.cast_ne_zero.mpr h.ne')
  have hmm := pow_self_ne_zero (n - k)
  have hsub : n - (n - k) = k := Nat.sub_sub_self hkn
  have hG : G n (n - k)
      = (n.choose (n - k) : ℚ) * ((n - k : ℕ) : ℚ) ^ (n - k) * (k : ℚ) ^ k / (n : ℚ) ^ n := by
    rw [G, hsub]
  rcases hnz with hnz | rfl
  · obtain ⟨P, hP, hPne⟩ : ∃ P : ℚ, ((n - k : ℕ) : ℚ) ^ (n - k) = P ∧ P ≠ 0 := ⟨_, rfl, hmm⟩
    rw [C_new, hG, hP]
    field_simp
    ring
  · interval_cases k
    norm_num [C_new, G]

/-- `C_new` as a single fraction. -/
theorem C_new_eq {n k : ℕ} (hkn : k ≤ n) (hn : 1 ≤ n) :
    C_new n k
      = (n.factorial : ℚ) * ((n - k).factorial : ℚ) * (n.choose (n - k) : ℚ) * (k : ℚ) ^ k
          / ((n : ℚ) ^ n * (n : ℚ) ^ n) := by
  have hnz : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [eq_div_iff (by positivity), ← mul_assoc]
  exact C_new_mul hkn

/-- **THEOREM H′** (`LIFT.md` §B.12.2).  `C_new(n,k) · cap_0 = (m!)^2 C(n,k)^2 gamma`, exactly,
at every `1 ≤ k ≤ n`.  Both sides reduce to `exact_payment`. -/
theorem theoremHprime {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) :
    C_new n k * cap0 n k
      = ((n - k).factorial : ℚ) ^ 2 * (n.choose k : ℚ) ^ 2 * gammaC n k := by
  have hn : 1 ≤ n := le_trans hk hkn
  have hnz : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hkz : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have key : (n.factorial : ℚ) * ((n - k).factorial : ℚ) * (n.choose (n - k) : ℚ)
      = ((n - k).factorial : ℚ) ^ 2 * (n.choose k : ℚ) ^ 2 * (k.factorial : ℚ) := by
    exact_mod_cast exact_payment hkn
  have hpow : (n : ℚ) ^ n * (n : ℚ) ^ n = (n : ℚ) ^ (2 * n - k) * (n : ℚ) ^ k := by
    rw [← pow_add, ← pow_add]
    congr 1
    omega
  rw [C_new_eq hkn hn, key, cap0, gammaC, hpow]
  have h1 : (n : ℚ) ^ (2 * n - k) ≠ 0 := pow_ne_zero _ hnz
  have h2 : (k : ℚ) ^ k ≠ 0 := pow_ne_zero _ hkz
  field_simp
  ring

/-- `rho_new(n,k)`, `graded_verify_borderrows.py`'s `rho_of` at `C = C_new`. -/
def rho_new (n k : ℕ) : ℚ :=
  C_new n k * cap0 n k / (((n - k).factorial : ℚ) ^ 2 * (n.choose k : ℚ) ^ 2 * gammaC n k)

/-- **Block [1], in the kernel.**  `rho_new = 1` at every `1 ≤ k ≤ n` — the frontier collapses
at every cell, not asymptotically and not approximately. -/
theorem rho_new_eq_one {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) : rho_new n k = 1 := by
  have hnz : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hden : ((n - k).factorial : ℚ) ^ 2 * (n.choose k : ℚ) ^ 2 * gammaC n k ≠ 0 := by
    have h1 : ((n - k).factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (n - k).factorial_ne_zero
    have h2 : (n.choose k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.choose_pos hkn).ne'
    have h3 : gammaC n k ≠ 0 := by
      unfold gammaC
      have : (k.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
      exact div_ne_zero this (pow_ne_zero _ hnz)
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ h1) (pow_ne_zero _ h2)) h3
  rw [rho_new, theoremHprime hk hkn, div_self hden]

/-! ### The degeneration at `m = 0, 1`

`LIFT.md` §B.12.1: "`G(n,1) = ((n-1)/n)^(n-1) = g(n)` and `G(n,0) = G(n,n) = 1`, so the
refinement reduces to `CAPACITY.md` §2.4 exactly at `m = 0, 1` — the two lines where §B.11
showed that labelling was already sharp.  Nothing is claimed where nothing was owed."
`graded_verify_borderrows.py` block [3]. -/

/-- At `m = 0` (`k = n`) the refinement is a no-op: `C_new = C_ref`. -/
theorem C_new_eq_C_ref_of_m_zero (n : ℕ) : C_new n n = C_ref n n := by
  unfold C_new C_ref
  simp

/-- At `m = 1` (`k = n-1`) the refinement is again a no-op, because `G(n,1)` is exactly
Gurvits' single-variable factor `g(n)`. -/
theorem C_new_eq_C_ref_of_m_one {n : ℕ} (hn : 1 ≤ n) : C_new n (n - 1) = C_ref n (n - 1) := by
  have h1 : n - (n - 1) = 1 := by omega
  unfold C_new C_ref
  rw [h1, G_one hn]
  norm_num

section AxiomAudit

#print axioms exact_payment
#print axioms exact_payment_mul
#print axioms exact_payment_mul'
#print axioms G
#print axioms G_nonneg
#print axioms G_zero
#print axioms G_self
#print axioms G_one
#print axioms gammaC
#print axioms cap0
#print axioms C_ref
#print axioms C_new
#print axioms pow_self_ne_zero
#print axioms C_new_mul
#print axioms C_new_eq
#print axioms theoremHprime
#print axioms rho_new
#print axioms rho_new_eq_one
#print axioms C_new_eq_C_ref_of_m_zero
#print axioms C_new_eq_C_ref_of_m_one

end AxiomAudit

end BorderPayment
