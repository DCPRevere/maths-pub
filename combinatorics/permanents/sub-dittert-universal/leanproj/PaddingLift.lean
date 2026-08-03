/-
# The padding lift cannot transfer the sub-Dittert bound between cells

**This file is arithmetic, not application material.**  It mentions no permanent and no
`K_n`; it is the exact algebraic core of one *kill*, recorded so that the kill is
kernel-checked rather than trusted to a rational-arithmetic script.

## What is being killed

Write `K_n = { A ≥ 0 : ∑ aᵢⱼ = n }`, `Φ_k(A) = E_k(r) + E_k(c) − P_k(A)` and
`F_{n,k}(A) = (2 − k!/nᵏ) − Φ_k(A)`, so the Cheon–Hwang conjecture is `F_{n,k} ≥ 0`
on `K_n` with equality only at `J_n/n`.  A lift `L : K_n → K_{n+1}` transfers truth
downwards in `n`, i.e. gives `(k, n+1) ⟹ (k, n)`, exactly when

    (T1)   ∃ c > 0,  F_{n,k}(A) ≥ c · F_{n+1,k}(L A)   for every A ∈ K_n,

because then `F_{n+1,k} ≥ 0` forces `F_{n,k} ≥ 0`.  The first candidate lift is padding,
`L A = A ⊕ [1]`, which does land in `K_{n+1}`.  Two elementary structure facts —
`e_k(r, 1) = e_k(r) + e_{k−1}(r)` and `σ_k(A ⊕ [1]) = σ_k(A) + σ_{k−1}(A)` — give the
exact identity (`TRANSFER.md`, Lemma T1)

    Φ_k(A ⊕ [1]) = λ Φ_k(A) + (1−λ) Φ_{k−1}(A) + λ(1−λ)(P_k(A) + P_{k−1}(A)),
    λ = (n+1−k)/(n+1),

and at the equality point `A = J_n/n` that identity evaluates to a **strictly positive**
defect

    PadLoss(n,k) := F_{n+1,k}(J_n/n ⊕ [1])
                  = λ² γ(n,k) + (1−λ)² γ(n,k−1) − γ(n+1,k),     γ(n,k) = k!/nᵏ,

which is `padLoss` below.  Since `F_{n,k}(J_n/n) = 0`, (T1) at `A = J_n/n` reads
`0 ≥ c · PadLoss(n,k)`, impossible for `c > 0`.  **That is the kill, and `J_n/n` is the
witness.**  So the whole content to be checked is `0 < PadLoss(n,k)` for `k ≥ 2`, which
after clearing denominators is the integer inequality `crit` of §2.

## Route

Clearing `PadLoss(n, k) > 0` of denominators leaves, with `k = j + 2`,

    (*)   nᵏ  <  [ (n+1)² − k(n+2) + k² ] (n+1)ʲ .

Write `k = j+2` and `x = 1/(n+1)`.  Then (*) is the second-order Bonferroni bound
`(1−x)ᵏ ≤ 1 − kx + C(k,2)x²` with one unit of room to spare, and the room is exactly
`C(k,2)x²`, which is what makes (*) *strict* for `k ≥ 2` and an *equality* at `k ≤ 1`
(where the conjecture's `k = 1` case is an identity, so no defect can appear there).

§1 carries Bonferroni over `ℤ` in cleared form as `T`, whose whole proof is the
one-line recursion `T(j+1) = n·T(j) + (j+2)(j+1)(n+1)ʲ` off the base `T(0) = 0`.  This is
why the file is short: no real analysis, no binomial series, one induction.

Everything is kernel-checked with no `sorry`; the audits are at the end.
-/
import Mathlib.Tactic

namespace PaddingLift

/-! ## §1 The Bonferroni core, cleared of denominators

`T n j` is `2 (n+1)^{j+2} · u_{j+2}` where `u_k = 1 − kx + C(k,2)x² − (1−x)ᵏ` at
`x = 1/(n+1)`.  Bonferroni is `u_k ≥ 0`; here that is `0 ≤ T n j`. -/

/-- The cleared Bonferroni quantity. -/
def T (n : ℤ) (j : ℕ) : ℤ :=
  2 * (n + 1) ^ (j + 2) + ((j : ℤ) + 2) * ((j : ℤ) + 1) * (n + 1) ^ j
    - 2 * ((j : ℤ) + 2) * (n + 1) ^ (j + 1) - 2 * n ^ (j + 2)

/-- Bonferroni is an equality at `k = 2`. -/
theorem T_zero (n : ℤ) : T n 0 = 0 := by
  simp only [T, pow_zero, pow_one, Nat.cast_zero]
  ring

/-- The whole proof: one recursion, with a manifestly non-negative increment. -/
theorem T_succ (n : ℤ) (j : ℕ) :
    T n (j + 1) = n * T n j + ((j : ℤ) + 2) * ((j : ℤ) + 1) * (n + 1) ^ j := by
  simp only [T, pow_succ, Nat.cast_add, Nat.cast_one]
  ring

/-- **Bonferroni, cleared.**  For every `n ≥ 0` and every `j`, `0 ≤ T n j`. -/
theorem T_nonneg {n : ℤ} (hn : 0 ≤ n) (j : ℕ) : 0 ≤ T n j := by
  induction j with
  | zero => rw [T_zero]
  | succ j ih =>
    have hp : (0 : ℤ) ≤ (n + 1) ^ j := pow_nonneg (by linarith) j
    have h2 : (0 : ℤ) ≤ ((j : ℤ) + 2) * ((j : ℤ) + 1) * (n + 1) ^ j := by
      have hj : (0 : ℤ) ≤ (j : ℤ) := Int.ofNat_nonneg j
      have : (0 : ℤ) ≤ ((j : ℤ) + 2) * ((j : ℤ) + 1) := by nlinarith
      exact mul_nonneg this hp
    have h1 : (0 : ℤ) ≤ n * T n j := mul_nonneg hn ih
    rw [T_succ]
    linarith

/-! ## §2 The sign criterion `(*)` -/

/-- **`(*)`, the integer form of the padding defect.**  For `n ≥ 1` and `k = j + 2`,

    nᵏ  <  [ (n+1)² − k(n+2) + k² ] (n+1)ʲ .

The gap is `T n j / 2 + C(k,2)(n+1)ʲ`, and it is the second summand — present only
because `k ≥ 2` — that makes the inequality strict. -/
theorem crit (n : ℤ) (hn : 1 ≤ n) (j : ℕ) :
    n ^ (j + 2)
      < ((n + 1) ^ 2 - ((j : ℤ) + 2) * (n + 2) + ((j : ℤ) + 2) ^ 2) * (n + 1) ^ j := by
  have hT : 0 ≤ T n j := T_nonneg (by linarith) j
  have hp : (0 : ℤ) < (n + 1) ^ j := pow_pos (by linarith) j
  have hj : (0 : ℤ) ≤ (j : ℤ) := Int.ofNat_nonneg j
  have hgap : (0 : ℤ) < ((j : ℤ) + 2) * ((j : ℤ) + 1) * (n + 1) ^ j := by
    have : (0 : ℤ) < ((j : ℤ) + 2) * ((j : ℤ) + 1) := by nlinarith
    exact mul_pos this hp
  have key :
      2 * (((n + 1) ^ 2 - ((j : ℤ) + 2) * (n + 2) + ((j : ℤ) + 2) ^ 2) * (n + 1) ^ j)
        = 2 * n ^ (j + 2) + T n j + ((j : ℤ) + 2) * ((j : ℤ) + 1) * (n + 1) ^ j := by
    simp only [T, pow_succ]
    ring
  linarith

/-! ## §3 `PadLoss(n,k) > 0`, and the kill -/

/-- `PadLoss(n,k) = F_{n+1,k}(J_n/n ⊕ [1])`, the defect the padding lift opens at the
equality point, in the closed form of `TRANSFER.md`:

    k! [ ((n+1−k)² + kn) / ((n+1)² nᵏ) − 1/(n+1)ᵏ ]. -/
def padLoss (n k : ℕ) : ℚ :=
  (Nat.factorial k : ℚ) *
    ((((n : ℚ) + 1 - (k : ℚ)) ^ 2 + (k : ℚ) * (n : ℚ)) / (((n : ℚ) + 1) ^ 2 * (n : ℚ) ^ k)
      - 1 / ((n : ℚ) + 1) ^ k)

/-- **The padding lift strictly loses at the equality point**, for every `n ≥ 1` and
every `k ≥ 2`. -/
theorem padLoss_pos (n j : ℕ) (hn : 1 ≤ n) : 0 < padLoss n (j + 2) := by
  have hn' : (1 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn
  have hnpos : (0 : ℚ) < (n : ℚ) := by linarith
  have hm : (0 : ℚ) < (n : ℚ) + 1 := by linarith
  have hnk : (0 : ℚ) < (n : ℚ) ^ (j + 2) := pow_pos hnpos _
  have hmk : (0 : ℚ) < ((n : ℚ) + 1) ^ (j + 2) := pow_pos hm _
  have hmj : (0 : ℚ) < ((n : ℚ) + 1) ^ j := pow_pos hm _
  have hm2 : (0 : ℚ) < ((n : ℚ) + 1) ^ 2 := pow_pos hm 2
  -- the integer criterion, pushed to ℚ
  have hcrit := crit (n : ℤ) (by exact_mod_cast hn) j
  have hQ : (n : ℚ) ^ (j + 2)
      < (((n : ℚ) + 1) ^ 2 - ((j : ℚ) + 2) * ((n : ℚ) + 2) + ((j : ℚ) + 2) ^ 2)
          * ((n : ℚ) + 1) ^ j := by exact_mod_cast hcrit
  -- the numerator of padLoss is that bracket
  have hnum : (((n : ℚ) + 1 - ((j : ℕ) + 2 : ℕ)) ^ 2 + (((j : ℕ) + 2 : ℕ) : ℚ) * (n : ℚ))
      = ((n : ℚ) + 1) ^ 2 - ((j : ℚ) + 2) * ((n : ℚ) + 2) + ((j : ℚ) + 2) ^ 2 := by
    push_cast
    ring
  have hfac : (0 : ℚ) < (Nat.factorial (j + 2) : ℚ) := by
    exact_mod_cast Nat.factorial_pos (j + 2)
  rw [padLoss, hnum]
  refine mul_pos hfac ?_
  rw [sub_pos, div_lt_div_iff₀ hmk (by positivity)]
  have hsplit : ((n : ℚ) + 1) ^ (j + 2) = ((n : ℚ) + 1) ^ 2 * ((n : ℚ) + 1) ^ j := by
    rw [← pow_add]; ring_nf
  calc 1 * (((n : ℚ) + 1) ^ 2 * (n : ℚ) ^ (j + 2))
      = ((n : ℚ) + 1) ^ 2 * (n : ℚ) ^ (j + 2) := by ring
    _ < ((n : ℚ) + 1) ^ 2
          * ((((n : ℚ) + 1) ^ 2 - ((j : ℚ) + 2) * ((n : ℚ) + 2) + ((j : ℚ) + 2) ^ 2)
             * ((n : ℚ) + 1) ^ j) := by
        exact (mul_lt_mul_left hm2).mpr hQ
    _ = (((n : ℚ) + 1) ^ 2 - ((j : ℚ) + 2) * ((n : ℚ) + 2) + ((j : ℚ) + 2) ^ 2)
          * ((n : ℚ) + 1) ^ (j + 2) := by rw [hsplit]; ring

/-- **The kill.**  `F_{n,k}(J_n/n) = 0` while `F_{n+1,k}((J_n/n) ⊕ [1]) = PadLoss(n,k)`,
so no positive transfer constant can exist for the padding lift: (T1) at `A = J_n/n`
would say `0 ≥ c · PadLoss(n,k)`. -/
theorem padding_no_transfer_constant (n j : ℕ) (hn : 1 ≤ n) {c : ℚ} (hc : 0 < c) :
    ¬ (0 ≥ c * padLoss n (j + 2)) :=
  not_le.mpr (mul_pos hc (padLoss_pos n j hn))

/-- The `k ≤ 1` boundary, recorded because it is the reason `k ≥ 2` is not cosmetic:
Bonferroni is an equality there, `PadLoss(n,1) = 0`, and the conjecture's `k = 1` case
is an identity on `K_n`. -/
theorem padLoss_one (n : ℕ) (hn : 1 ≤ n) : padLoss n 1 = 0 := by
  have hnpos : (0 : ℚ) < (n : ℚ) := by
    have : (1 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn
    linarith
  have hm : ((n : ℚ) + 1) ≠ 0 := by positivity
  have hz : (n : ℚ) ≠ 0 := ne_of_gt hnpos
  rw [padLoss]
  field_simp
  ring

#print axioms T_zero
#print axioms T_succ
#print axioms T_nonneg
#print axioms crit
#print axioms padLoss_pos
#print axioms padding_no_transfer_constant
#print axioms padLoss_one

end PaddingLift
