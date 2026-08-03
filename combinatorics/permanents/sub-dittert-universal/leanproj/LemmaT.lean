/-
# Lemma T — the three conditions at EVERY cell — `LEAN-ROADMAP.md` stone 9

`LIFT.md` §B.13.3.  `R_new` is infinite and §B.13.2's support was a finite sweep, so the tail
was owed.  Lemma T closes it:

> **Lemma T (tail).**  For every `n >= 10` and every `3 <= k <= n-1`, `(C1)`, `(C2)` and `(C3)`
> all hold and `theta(n,k) <= 144/955 < 1`.

Together with the 21 exact cells `4 <= n <= 9` this pins `R_new` exactly.

The roadmap sizes stone 9 at L because it expected a reach-every-`n` argument to be invented.
Lemma T supplies one, in five exact rational steps, so what is left is transcription:

| step | content |
|---|---|
| (T0) | `gamma` is non-increasing in `k`, since `gamma(n,k+1)/gamma(n,k) = (k+1)/n <= 1` |
| (T1) | `(k-1)^2 - 4(k-2) = (k-3)^2 >= 0`, so `kappa <= (3/4) gamma (n-1) <= 9/(2n^2)` |
| (T2) | `k <= n/2`: `m >= n/2` and `k-1 >= k/2` give `Lambda <= 12/n^2`, `Xi <= 27 gamma` |
| (T3) | `k > n/2`: `gamma <= h!/n^h` with `h = n/2 + 1` gives `Lambda <= B(n)`, `Xi <= 6B(n)` |
| (T4) | `B(n+2) <= B(n)` for `n >= 8`, and `B(10) = 18/125`, so `B <= 18/125` for `n >= 10` |

Everything is `ℚ`, so the whole file is kernel arithmetic: no `decide` on rationals, no
`native_decide`, and the finite part is spelled cell by cell.

Constants pinned to `graded_verify_strict.py` (`gamma`, `theta`, `condsK`) through `Theta.lean`.
-/

import Mathlib.Tactic
import Theta

namespace LemmaT

open Theta

/-! ## §1  (T0) — `gamma` is non-increasing in `k` -/

theorem gamma_pos {n : ℕ} (hn : 0 < n) (k : ℕ) : 0 < gamma n k := by
  unfold gamma
  have h1 : (0 : ℚ) < (k.factorial : ℚ) := by exact_mod_cast k.factorial_pos
  have h2 : (0 : ℚ) < (n : ℚ) := by exact_mod_cast hn
  positivity

theorem gamma_succ {n : ℕ} (hn : 0 < n) (k : ℕ) :
    gamma n (k + 1) = gamma n k * (((k : ℚ) + 1) / (n : ℚ)) := by
  have h2 : (n : ℚ) ≠ 0 := by
    have : (0 : ℚ) < (n : ℚ) := by exact_mod_cast hn
    linarith
  unfold gamma
  rw [Nat.factorial_succ, pow_succ]
  push_cast
  field_simp
  ring

/-- **(T0).**  `gamma(n,·)` is non-increasing on `[0, n]`. -/
theorem gamma_antitone {n : ℕ} (hn : 0 < n) :
    ∀ j k : ℕ, j ≤ k → k ≤ n → gamma n k ≤ gamma n j := by
  intro j k hjk
  induction k, hjk using Nat.le_induction with
  | base => intro _; exact le_rfl
  | succ i hji ih =>
      intro hin
      have hgi := gamma_pos hn i
      have h2 : ((i : ℚ) + 1) / (n : ℚ) ≤ 1 := by
        have hnq : (0 : ℚ) < (n : ℚ) := by exact_mod_cast hn
        rw [div_le_one hnq]
        have : (i : ℚ) + 1 ≤ (n : ℚ) := by exact_mod_cast hin
        linarith
      have h3 : gamma n (i + 1) ≤ gamma n i := by
        rw [gamma_succ hn i]
        nlinarith
      exact h3.trans (ih (by omega))

theorem gamma_three (n : ℕ) : gamma n 3 = 6 / (n : ℚ) ^ 3 := by
  unfold gamma
  norm_num [Nat.factorial]

/-- `gamma <= 6/n^3` on the whole strip `3 ≤ k ≤ n`. -/
theorem gamma_le_six {n k : ℕ} (h3 : 3 ≤ k) (hkn : k ≤ n) : gamma n k ≤ 6 / (n : ℚ) ^ 3 := by
  have hn : 0 < n := by omega
  have h := gamma_antitone hn 3 k h3 hkn
  rwa [gamma_three] at h

/-! ## §2  (T1) — `kappa` is small -/

/-- The `(k-3)^2` identity: `(k-2)/(k-1)^2 ≤ 1/4`, with equality exactly at `k = 3`. -/
theorem kappa_le_gamma {n k : ℕ} (h3 : 3 ≤ k) (hkn : k ≤ n) :
    kappa n k ≤ 3 / 4 * gamma n k * ((n : ℚ) - 1) := by
  have hn : 0 < n := by omega
  have hkq : (3 : ℚ) ≤ (k : ℚ) := by exact_mod_cast h3
  have hk1 : (0 : ℚ) < ((k : ℚ) - 1) ^ 2 := by nlinarith
  have hsq : ((k : ℚ) - 2) * 4 ≤ ((k : ℚ) - 1) ^ 2 := by nlinarith [sq_nonneg ((k : ℚ) - 3)]
  have hgpos := gamma_pos hn k
  have hn1 : (0 : ℚ) ≤ (n : ℚ) - 1 := by
    have : (3 : ℚ) ≤ (n : ℚ) := le_trans hkq (by exact_mod_cast hkn)
    linarith
  unfold kappa
  rw [div_le_iff₀ hk1]
  nlinarith [mul_nonneg (mul_nonneg hgpos.le hn1) (sub_nonneg.mpr hsq)]

/-- **(T1) numerically.**  At `n ≥ 10`, `kappa ≤ 9/200`, hence `1 - kappa ≥ 191/200 > 0`. -/
theorem kappa_le_num {n k : ℕ} (h3 : 3 ≤ k) (hkn : k ≤ n) (hn10 : 10 ≤ n) :
    kappa n k ≤ 9 / 200 := by
  have hnq : (10 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn10
  have h1 := kappa_le_gamma h3 hkn
  have h2 := gamma_le_six h3 hkn
  have hn1 : (0 : ℚ) ≤ (n : ℚ) - 1 := by linarith
  have h3' : 3 / 4 * gamma n k * ((n : ℚ) - 1) ≤ 3 / 4 * (6 / (n : ℚ) ^ 3) * ((n : ℚ) - 1) := by
    nlinarith
  have h4 : 3 / 4 * (6 / (n : ℚ) ^ 3) * ((n : ℚ) - 1) ≤ 9 / 200 := by
    have hnp : (0 : ℚ) < (n : ℚ) := by linarith
    have h100 : (100 : ℚ) * (n : ℚ) ≤ (n : ℚ) ^ 3 := by
      nlinarith [mul_nonneg (mul_nonneg hnp.le (by linarith : (0:ℚ) ≤ (n:ℚ) - 10))
        (by linarith : (0:ℚ) ≤ (n:ℚ) + 10)]
    rw [show (3 : ℚ) / 4 * (6 / (n : ℚ) ^ 3) * ((n : ℚ) - 1)
        = (9 * ((n : ℚ) - 1)) / (2 * (n : ℚ) ^ 3) by field_simp; ring]
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  linarith

theorem one_sub_kappa_ge {n k : ℕ} (h3 : 3 ≤ k) (hkn : k ≤ n) (hn10 : 10 ≤ n) :
    (191 : ℚ) / 200 ≤ 1 - kappa n k := by
  have := kappa_le_num h3 hkn hn10
  linarith

/-! ## §3  (T2) — the small-`k` side, `3 ≤ k ≤ n/2`

`m = n-k ≥ n/2`, `k-1 ≥ k/2` and `k-1 ≥ 2k/3`, so the denominators are big enough that the
`6/n^3` cap on `gamma` alone closes both conditions. -/

theorem C2_small {n k : ℕ} (h3 : 3 ≤ k) (h2k : 2 * k ≤ n) (hn10 : 10 ≤ n) : C2 n k := by
  have hkn : k ≤ n := by omega
  have hK : (3 : ℚ) ≤ (k : ℚ) := by exact_mod_cast h3
  have hN : (10 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn10
  have h2K : 2 * (k : ℚ) ≤ (n : ℚ) := by exact_mod_cast h2k
  have hg := gamma_le_six h3 hkn
  have hgpos := gamma_pos (show 0 < n by omega) k
  have hNp : (0 : ℚ) < (n : ℚ) := by linarith
  -- `(n-k)(k-1) ≥ nk/3`
  have hmk : (n : ℚ) * (k : ℚ) / 3 ≤ ((n : ℚ) - (k : ℚ)) * ((k : ℚ) - 1) := by
    have ha : (n : ℚ) / 2 ≤ (n : ℚ) - (k : ℚ) := by linarith
    have hb : 2 * (k : ℚ) / 3 ≤ (k : ℚ) - 1 := by linarith
    nlinarith
  have hsq : ((n : ℚ) * (k : ℚ) / 3) ^ 2 ≤ (((n : ℚ) - (k : ℚ)) * ((k : ℚ) - 1)) ^ 2 := by
    have h0 : (0 : ℚ) ≤ (n : ℚ) * (k : ℚ) / 3 := by positivity
    nlinarith
  -- `27 gamma ≤ 1`
  have h27 : 27 * gamma n k ≤ 1 := by
    have hcube : (162 : ℚ) ≤ (n : ℚ) ^ 3 := by
      have hsq2 : (100 : ℚ) ≤ (n : ℚ) ^ 2 := by nlinarith
      have hprod : (10 : ℚ) * 100 ≤ (n : ℚ) * (n : ℚ) ^ 2 :=
        mul_le_mul hN hsq2 (by norm_num) (by linarith)
      nlinarith [hprod]
    have : 27 * gamma n k ≤ 27 * (6 / (n : ℚ) ^ 3) := by linarith
    have h2 : 27 * (6 / (n : ℚ) ^ 3) ≤ 1 := by
      rw [show (27 : ℚ) * (6 / (n : ℚ) ^ 3) = 162 / (n : ℚ) ^ 3 by ring,
        div_le_one (by positivity)]
      linarith
    linarith
  unfold C2
  have hstep : 3 * gamma n k * (k : ℚ) ^ 2 * ((n : ℚ) - 1) ^ 2
      ≤ ((n : ℚ) * (k : ℚ) / 3) ^ 2 := by
    have hn1 : ((n : ℚ) - 1) ^ 2 ≤ (n : ℚ) ^ 2 := by nlinarith
    have hA : 3 * gamma n k * (k : ℚ) ^ 2 * ((n : ℚ) - 1) ^ 2
        ≤ 3 * gamma n k * (k : ℚ) ^ 2 * (n : ℚ) ^ 2 :=
      mul_le_mul_of_nonneg_left hn1 (by positivity)
    nlinarith
  linarith

theorem C3_small {n k : ℕ} (h3 : 3 ≤ k) (h2k : 2 * k ≤ n) (hn10 : 10 ≤ n) : C3 n k := by
  have hkn : k ≤ n := by omega
  have hK : (3 : ℚ) ≤ (k : ℚ) := by exact_mod_cast h3
  have hN : (10 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn10
  have h2K : 2 * (k : ℚ) ≤ (n : ℚ) := by exact_mod_cast h2k
  have hg := gamma_le_six h3 hkn
  have hgpos := gamma_pos (show 0 < n by omega) k
  have hκ := one_sub_kappa_ge h3 hkn hn10
  have hNp : (0 : ℚ) < (n : ℚ) := by linarith
  -- `(n-k)(k-1) ≥ nk/4`
  have hmk : (n : ℚ) * (k : ℚ) / 4 ≤ ((n : ℚ) - (k : ℚ)) * ((k : ℚ) - 1) := by
    have ha : (n : ℚ) / 2 ≤ (n : ℚ) - (k : ℚ) := by linarith
    have hb : (k : ℚ) / 2 ≤ (k : ℚ) - 1 := by linarith
    nlinarith
  -- `gamma k^2 (n-1) ≤ 6k^2/n^2 ≤ (191/800) n k`
  have hL : gamma n k * (k : ℚ) ^ 2 * ((n : ℚ) - 1) ≤ 6 * (k : ℚ) ^ 2 / (n : ℚ) ^ 2 := by
    have h1 : gamma n k * (k : ℚ) ^ 2 * ((n : ℚ) - 1)
        ≤ (6 / (n : ℚ) ^ 3) * (k : ℚ) ^ 2 * (n : ℚ) := by
      have hA : gamma n k * (k : ℚ) ^ 2 * ((n : ℚ) - 1) ≤ gamma n k * (k : ℚ) ^ 2 * (n : ℚ) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      have hB : gamma n k * ((k : ℚ) ^ 2 * (n : ℚ)) ≤ (6 / (n : ℚ) ^ 3) * ((k : ℚ) ^ 2 * (n : ℚ)) :=
        mul_le_mul_of_nonneg_right hg (by positivity)
      nlinarith [hA, hB]
    have h2 : (6 / (n : ℚ) ^ 3) * (k : ℚ) ^ 2 * (n : ℚ) = 6 * (k : ℚ) ^ 2 / (n : ℚ) ^ 2 := by
      field_simp
      ring
    linarith
  have hR : 6 * (k : ℚ) ^ 2 / (n : ℚ) ^ 2 ≤ 191 / 800 * ((n : ℚ) * (k : ℚ)) := by
    rw [div_le_iff₀ (by positivity)]
    have h1 : 4800 * (k : ℚ) ≤ 191 * (n : ℚ) ^ 3 := by nlinarith
    nlinarith
  unfold C3 thetaNum thetaDen
  calc gamma n k * (k : ℚ) ^ 2 * ((n : ℚ) - 1)
      ≤ 191 / 800 * ((n : ℚ) * (k : ℚ)) := le_trans hL hR
    _ = 191 / 200 * ((n : ℚ) * (k : ℚ) / 4) := by ring
    _ ≤ (1 - kappa n k) * (((n : ℚ) - (k : ℚ)) * ((k : ℚ) - 1)) := by
        have h0 : (0 : ℚ) ≤ (n : ℚ) * (k : ℚ) / 4 := by positivity
        nlinarith
    _ = ((n : ℚ) - (k : ℚ)) * ((k : ℚ) - 1) * (1 - kappa n k) := by ring

/-! ## §4  (T3)/(T4) — the large-`k` side, `n/2 < k ≤ n-1`

Here `m` may be `1`, so the denominator gives nothing and the super-exponential decay of
`gamma` has to carry the bound.  `h = ⌊n/2⌋ + 1 ≤ k`, so `gamma ≤ h!/n^h` and both `Lambda`
and `Xi` are controlled by `B(n) = 2 n^2 h!/n^h`. -/

/-- `h = ⌊n/2⌋ + 1`, the exponent at which `gamma` is capped on the large-`k` side. -/
def hh (n : ℕ) : ℕ := n / 2 + 1

/-- `B(n) = 2 n^2 h!/n^h`. -/
def B (n : ℕ) : ℚ := 2 * (n : ℚ) ^ 2 * ((hh n).factorial : ℚ) / (n : ℚ) ^ (hh n)

theorem B_pos {n : ℕ} (hn : 0 < n) : 0 < B n := by
  have h1 : (0 : ℚ) < ((hh n).factorial : ℚ) := by exact_mod_cast (hh n).factorial_pos
  have h2 : (0 : ℚ) < (n : ℚ) := by exact_mod_cast hn
  unfold B
  positivity

/-- **(T4).**  `B(n+2) ≤ B(n)` for `n ≥ 8`. -/
theorem B_step {n : ℕ} (hn : 8 ≤ n) : B (n + 2) ≤ B n := by
  have hN : (8 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn
  have hNpos : (0 : ℚ) < (n : ℚ) := by linarith
  have hhs : hh (n + 2) = hh n + 1 := by unfold hh; omega
  set h := hh n with hdef
  have hfact : (0 : ℚ) < (h.factorial : ℚ) := by exact_mod_cast h.factorial_pos
  have hhq : (h : ℚ) ≤ (n : ℚ) / 2 + 1 := by
    have h1 : (n / 2 : ℕ) * 2 ≤ n := Nat.div_mul_le_self n 2
    have h2 : ((n / 2 : ℕ) : ℚ) * 2 ≤ (n : ℚ) := by exact_mod_cast h1
    rw [hdef, hh]
    push_cast
    linarith
  have hkey : ((h : ℚ) + 1) * ((n : ℚ) + 2) ≤ (n : ℚ) ^ 2 := by nlinarith
  have hpow : (n : ℚ) ^ h ≤ ((n : ℚ) + 2) ^ h :=
    pow_le_pow_left₀ hNpos.le (by linarith) h
  have hstep : ((h : ℚ) + 1) * ((n : ℚ) + 2) * (n : ℚ) ^ h ≤ (n : ℚ) ^ 2 * ((n : ℚ) + 2) ^ h := by
    calc ((h : ℚ) + 1) * ((n : ℚ) + 2) * (n : ℚ) ^ h ≤ (n : ℚ) ^ 2 * (n : ℚ) ^ h :=
          mul_le_mul_of_nonneg_right hkey (by positivity)
      _ ≤ (n : ℚ) ^ 2 * ((n : ℚ) + 2) ^ h := mul_le_mul_of_nonneg_left hpow (by positivity)
  have hB2 : B (n + 2)
      = 2 * ((n : ℚ) + 2) ^ 2 * (((h + 1).factorial : ℕ) : ℚ) / ((n : ℚ) + 2) ^ (h + 1) := by
    unfold B
    rw [hhs]
    push_cast
    ring
  rw [hB2, B, ← hdef, div_le_div_iff₀ (by positivity) (by positivity), Nat.factorial_succ]
  push_cast
  rw [pow_succ ((n : ℚ) + 2) h]
  nlinarith [mul_le_mul_of_nonneg_left hstep
    (by positivity : (0 : ℚ) ≤ 2 * (h.factorial : ℚ) * ((n : ℚ) + 2))]

/-- `B(n) ≤ 18/125` for every `n ≥ 10`, by induction along each parity class from
`B(10) = 18/125` and `B(11) = 1440/14641`. -/
theorem B_le {n : ℕ} (hn : 10 ≤ n) : B n ≤ 18 / 125 := by
  have key : ∀ j : ℕ, B (10 + 2 * j) ≤ 18 / 125 ∧ B (11 + 2 * j) ≤ 18 / 125 := by
    intro j
    induction j with
    | zero => constructor <;> norm_num [B, hh, Nat.factorial]
    | succ i ih =>
        constructor
        · rw [show 10 + 2 * (i + 1) = (10 + 2 * i) + 2 by ring]
          exact le_trans (B_step (by omega)) ih.1
        · rw [show 11 + 2 * (i + 1) = (11 + 2 * i) + 2 by ring]
          exact le_trans (B_step (by omega)) ih.2
  obtain ⟨j, hj⟩ : ∃ j, n = 10 + 2 * j ∨ n = 11 + 2 * j := ⟨(n - 10) / 2, by omega⟩
  rcases hj with hj | hj
  · rw [hj]; exact (key j).1
  · rw [hj]; exact (key j).2

/-- `2 gamma n^2 ≤ B(n)` on the large-`k` side. -/
theorem two_gamma_sq_le_B {n k : ℕ} (hhk : hh n ≤ k) (hkn : k ≤ n) :
    2 * gamma n k * (n : ℚ) ^ 2 ≤ B n := by
  have hn : 0 < n := by
    have := (hh n).succ_pos
    unfold hh at hhk
    omega
  have hg : gamma n k ≤ gamma n (hh n) := gamma_antitone hn (hh n) k hhk hkn
  have hNpos : (0 : ℚ) < (n : ℚ) := by exact_mod_cast hn
  have hB : B n = 2 * gamma n (hh n) * (n : ℚ) ^ 2 := by
    unfold B gamma
    field_simp
    ring
  rw [hB]
  nlinarith [sq_nonneg ((n : ℚ))]

/-! ## §5  (T3) assembly on the large-`k` side, and (T5) -/

theorem C2_large {n k : ℕ} (h3 : 3 ≤ k) (hlk : n < 2 * k) (hkn : k < n) (hn10 : 10 ≤ n) :
    C2 n k := by
  have hhk : hh n ≤ k := by unfold hh; omega
  have hB := two_gamma_sq_le_B hhk hkn.le
  have hBle := B_le hn10
  have hK : (3 : ℚ) ≤ (k : ℚ) := by exact_mod_cast h3
  have hN : (10 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn10
  have hKN : (k : ℚ) + 1 ≤ (n : ℚ) := by exact_mod_cast hkn
  have hlkq : (n : ℚ) + 1 ≤ 2 * (k : ℚ) := by exact_mod_cast hlk
  have hgpos := gamma_pos (show 0 < n by omega) k
  have h12 : 12 * gamma n k * (n : ℚ) ^ 2 ≤ 1 := by linarith
  -- `(n-k)(k-1) ≥ (n-1)/2`
  have hmk : ((n : ℚ) - 1) / 2 ≤ ((n : ℚ) - (k : ℚ)) * ((k : ℚ) - 1) := by
    have ha : (1 : ℚ) ≤ (n : ℚ) - (k : ℚ) := by linarith
    have hb : ((n : ℚ) - 1) / 2 ≤ (k : ℚ) - 1 := by linarith
    nlinarith
  have hsq : (((n : ℚ) - 1) / 2) ^ 2 ≤ (((n : ℚ) - (k : ℚ)) * ((k : ℚ) - 1)) ^ 2 :=
    pow_le_pow_left₀ (by linarith) hmk 2
  unfold C2
  have hL : 3 * gamma n k * (k : ℚ) ^ 2 * ((n : ℚ) - 1) ^ 2
      ≤ 3 * gamma n k * (n : ℚ) ^ 2 * ((n : ℚ) - 1) ^ 2 := by
    have hk2 : (k : ℚ) ^ 2 ≤ (n : ℚ) ^ 2 := by nlinarith
    have hA : 3 * gamma n k * (k : ℚ) ^ 2 ≤ 3 * gamma n k * (n : ℚ) ^ 2 :=
      mul_le_mul_of_nonneg_left hk2 (by positivity)
    exact mul_le_mul_of_nonneg_right hA (sq_nonneg _)
  have hR : 3 * gamma n k * (n : ℚ) ^ 2 * ((n : ℚ) - 1) ^ 2 ≤ (((n : ℚ) - 1) / 2) ^ 2 := by
    have h0 : (0 : ℚ) ≤ ((n : ℚ) - 1) ^ 2 := sq_nonneg _
    nlinarith
  linarith

theorem C3_large {n k : ℕ} (h3 : 3 ≤ k) (hlk : n < 2 * k) (hkn : k < n) (hn10 : 10 ≤ n) :
    C3 n k := by
  have hhk : hh n ≤ k := by unfold hh; omega
  have hB := two_gamma_sq_le_B hhk hkn.le
  have hBle := B_le hn10
  have hκ := one_sub_kappa_ge h3 hkn.le hn10
  have hK : (3 : ℚ) ≤ (k : ℚ) := by exact_mod_cast h3
  have hN : (10 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn10
  have hKN : (k : ℚ) + 1 ≤ (n : ℚ) := by exact_mod_cast hkn
  have hlkq : (n : ℚ) + 1 ≤ 2 * (k : ℚ) := by exact_mod_cast hlk
  have hgpos := gamma_pos (show 0 < n by omega) k
  have hmk : ((n : ℚ) - 1) / 2 ≤ ((n : ℚ) - (k : ℚ)) * ((k : ℚ) - 1) := by
    have ha : (1 : ℚ) ≤ (n : ℚ) - (k : ℚ) := by linarith
    have hb : ((n : ℚ) - 1) / 2 ≤ (k : ℚ) - 1 := by linarith
    nlinarith
  unfold C3 thetaNum thetaDen
  have hL : gamma n k * (k : ℚ) ^ 2 * ((n : ℚ) - 1)
      ≤ gamma n k * (n : ℚ) ^ 2 * ((n : ℚ) - 1) := by
    have hk2 : (k : ℚ) ^ 2 ≤ (n : ℚ) ^ 2 := by nlinarith
    have hA : gamma n k * (k : ℚ) ^ 2 ≤ gamma n k * (n : ℚ) ^ 2 :=
      mul_le_mul_of_nonneg_left hk2 (by positivity)
    exact mul_le_mul_of_nonneg_right hA (by linarith)
  have hR : gamma n k * (n : ℚ) ^ 2 * ((n : ℚ) - 1)
      ≤ ((n : ℚ) - (k : ℚ)) * ((k : ℚ) - 1) * (1 - kappa n k) := by
    have h1 : gamma n k * (n : ℚ) ^ 2 * ((n : ℚ) - 1) ≤ 9 / 125 * ((n : ℚ) - 1) := by
      nlinarith
    have h2 : 9 / 125 * ((n : ℚ) - 1) ≤ 191 / 200 * (((n : ℚ) - 1) / 2) := by linarith
    have h3' : 191 / 200 * (((n : ℚ) - 1) / 2)
        ≤ (1 - kappa n k) * (((n : ℚ) - (k : ℚ)) * ((k : ℚ) - 1)) := by
      nlinarith
    nlinarith
  linarith

theorem C1_tail {n k : ℕ} (h3 : 3 ≤ k) (hkn : k ≤ n) (hn10 : 10 ≤ n) : C1 n k := by
  have hN : (10 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn10
  have hg := gamma_le_six h3 hkn
  have hcube : (1000 : ℚ) ≤ (n : ℚ) ^ 3 := by
    have hsq2 : (100 : ℚ) ≤ (n : ℚ) ^ 2 := by nlinarith
    have hprod : (10 : ℚ) * 100 ≤ (n : ℚ) * (n : ℚ) ^ 2 :=
      mul_le_mul hN hsq2 (by norm_num) (by linarith)
    nlinarith [hprod]
  unfold C1
  have : (6 : ℚ) / (n : ℚ) ^ 3 ≤ 1 / 12 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  linarith

/-- **LEMMA T, the tail.**  All three conditions hold at every `n ≥ 10`, `3 ≤ k ≤ n-1`. -/
theorem condsT {n k : ℕ} (hn10 : 10 ≤ n) (h3 : 3 ≤ k) (hkn : k < n) : Conds n k := by
  refine ⟨h3, hkn, C1_tail h3 hkn.le hn10, ?_, ?_⟩
  · rcases le_or_lt (2 * k) n with h | h
    · exact C2_small h3 h hn10
    · exact C2_large h3 h hkn hn10
  · rcases le_or_lt (2 * k) n with h | h
    · exact C3_small h3 h hn10
    · exact C3_large h3 h hkn hn10

/-- **(T5).**  `Lambda ≤ 18/125` on the whole tail — the uniform slope bound. -/
theorem Lambda_le {n k : ℕ} (hn10 : 10 ≤ n) (h3 : 3 ≤ k) (hkn : k < n) :
    thetaNum n k ≤ 18 / 125 * (((n : ℚ) - (k : ℚ)) * ((k : ℚ) - 1)) := by
  have hK : (3 : ℚ) ≤ (k : ℚ) := by exact_mod_cast h3
  have hN : (10 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn10
  have hKN : (k : ℚ) + 1 ≤ (n : ℚ) := by exact_mod_cast hkn
  have hgpos := gamma_pos (show 0 < n by omega) k
  have hg := gamma_le_six h3 hkn.le
  unfold thetaNum
  rcases le_or_lt (2 * k) n with h | h
  · have h2K : 2 * (k : ℚ) ≤ (n : ℚ) := by exact_mod_cast h
    have hmk : (n : ℚ) * (k : ℚ) / 4 ≤ ((n : ℚ) - (k : ℚ)) * ((k : ℚ) - 1) := by
      have ha : (n : ℚ) / 2 ≤ (n : ℚ) - (k : ℚ) := by linarith
      have hb : (k : ℚ) / 2 ≤ (k : ℚ) - 1 := by linarith
      nlinarith
    have hL : gamma n k * (k : ℚ) ^ 2 * ((n : ℚ) - 1) ≤ 6 * (k : ℚ) ^ 2 / (n : ℚ) ^ 2 := by
      have hA : gamma n k * (k : ℚ) ^ 2 * ((n : ℚ) - 1) ≤ gamma n k * (k : ℚ) ^ 2 * (n : ℚ) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      have hB2 : gamma n k * ((k : ℚ) ^ 2 * (n : ℚ))
          ≤ (6 / (n : ℚ) ^ 3) * ((k : ℚ) ^ 2 * (n : ℚ)) :=
        mul_le_mul_of_nonneg_right hg (by positivity)
      have hE : (6 / (n : ℚ) ^ 3) * ((k : ℚ) ^ 2 * (n : ℚ)) = 6 * (k : ℚ) ^ 2 / (n : ℚ) ^ 2 := by
        field_simp; ring
      nlinarith [hA, hB2]
    have hR : 6 * (k : ℚ) ^ 2 / (n : ℚ) ^ 2 ≤ 18 / 125 * ((n : ℚ) * (k : ℚ) / 4) := by
      rw [div_le_iff₀ (by positivity)]
      have hn2 : (100 : ℚ) ≤ (n : ℚ) ^ 2 := by nlinarith
      have h300 : (300 : ℚ) * (n : ℚ) ≤ 3 * (n : ℚ) ^ 3 := by
        nlinarith [mul_le_mul_of_nonneg_left hn2 (show (0 : ℚ) ≤ 3 * (n : ℚ) by linarith)]
      have h500 : (500 : ℚ) * (k : ℚ) ≤ 3 * (n : ℚ) ^ 3 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_right h500 (show (0 : ℚ) ≤ (k : ℚ) by linarith)]
    nlinarith [hmk, hL, hR]
  · have hhk : hh n ≤ k := by unfold hh; omega
    have hB := two_gamma_sq_le_B hhk hkn.le
    have hBle := B_le hn10
    have hlkq : (n : ℚ) + 1 ≤ 2 * (k : ℚ) := by exact_mod_cast h
    have hmk : ((n : ℚ) - 1) / 2 ≤ ((n : ℚ) - (k : ℚ)) * ((k : ℚ) - 1) := by
      have ha : (1 : ℚ) ≤ (n : ℚ) - (k : ℚ) := by linarith
      have hb : ((n : ℚ) - 1) / 2 ≤ (k : ℚ) - 1 := by linarith
      nlinarith
    have hL : gamma n k * (k : ℚ) ^ 2 * ((n : ℚ) - 1)
        ≤ 9 / 125 * ((n : ℚ) - 1) := by
      have hk2 : (k : ℚ) ^ 2 ≤ (n : ℚ) ^ 2 := by nlinarith
      have hA : gamma n k * (k : ℚ) ^ 2 ≤ gamma n k * (n : ℚ) ^ 2 :=
        mul_le_mul_of_nonneg_left hk2 (by positivity)
      have hB3 : gamma n k * (n : ℚ) ^ 2 ≤ 9 / 125 := by linarith
      exact mul_le_mul_of_nonneg_right (le_trans hA hB3) (by linarith)
    have hRHS : 18 / 125 * (((n : ℚ) - 1) / 2)
        ≤ 18 / 125 * (((n : ℚ) - (k : ℚ)) * ((k : ℚ) - 1)) :=
      mul_le_mul_of_nonneg_left hmk (by norm_num)
    calc gamma n k * (k : ℚ) ^ 2 * ((n : ℚ) - 1)
        ≤ 9 / 125 * ((n : ℚ) - 1) := hL
      _ = 18 / 125 * (((n : ℚ) - 1) / 2) := by ring
      _ ≤ 18 / 125 * (((n : ℚ) - (k : ℚ)) * ((k : ℚ) - 1)) := hRHS

theorem thetaDen_pos {n k : ℕ} (hn10 : 10 ≤ n) (h3 : 3 ≤ k) (hkn : k < n) :
    0 < thetaDen n k := by
  have hκ := one_sub_kappa_ge h3 hkn.le hn10
  have hK : (3 : ℚ) ≤ (k : ℚ) := by exact_mod_cast h3
  have hKN : (k : ℚ) + 1 ≤ (n : ℚ) := by exact_mod_cast hkn
  unfold thetaDen
  have h1 : (0 : ℚ) < (n : ℚ) - (k : ℚ) := by linarith
  have h2 : (0 : ℚ) < (k : ℚ) - 1 := by linarith
  have h3' : (0 : ℚ) < 1 - kappa n k := by linarith
  exact mul_pos (mul_pos h1 h2) h3' 

/-- **LEMMA T, the ceiling.**  `theta ≤ 144/955` on the whole tail. -/
theorem thetaT {n k : ℕ} (hn10 : 10 ≤ n) (h3 : 3 ≤ k) (hkn : k < n) :
    theta n k ≤ 144 / 955 := by
  have hden := thetaDen_pos hn10 h3 hkn
  have hκ := one_sub_kappa_ge h3 hkn.le hn10
  have hΛ := Lambda_le hn10 h3 hkn
  have hK : (3 : ℚ) ≤ (k : ℚ) := by exact_mod_cast h3
  have hKN : (k : ℚ) + 1 ≤ (n : ℚ) := by exact_mod_cast hkn
  have hP : (0 : ℚ) ≤ ((n : ℚ) - (k : ℚ)) * ((k : ℚ) - 1) := by nlinarith
  unfold theta
  rw [div_le_iff₀ hden]
  unfold thetaDen
  nlinarith [hΛ, hP, hκ]

/-! ## §6  The finite part — the 21 cells `4 ≤ n ≤ 9`

Spelled cell by cell, each by `norm_num` over `ℚ`.  Exactly four fail, and they are exactly the
four `R_new` already excludes: `Theta.not_C1_three_four` / `not_C3_three_four` /
`not_C2_three_four` at `(3,4)`, and `Theta.not_C2_{three_five, four_five, five_six}` — the
three that fail `(C2)` ONLY. -/

theorem conds_three_six : Conds 6 3 := by
  refine ⟨by norm_num, by norm_num, ?_, ?_, ?_⟩ <;>
    norm_num [C1, C2, C3, thetaNum, thetaDen, kappa, gamma, Nat.factorial]

theorem conds_four_six : Conds 6 4 := by
  refine ⟨by norm_num, by norm_num, ?_, ?_, ?_⟩ <;>
    norm_num [C1, C2, C3, thetaNum, thetaDen, kappa, gamma, Nat.factorial]

theorem conds_three_seven : Conds 7 3 := by
  refine ⟨by norm_num, by norm_num, ?_, ?_, ?_⟩ <;>
    norm_num [C1, C2, C3, thetaNum, thetaDen, kappa, gamma, Nat.factorial]

theorem conds_four_seven : Conds 7 4 := by
  refine ⟨by norm_num, by norm_num, ?_, ?_, ?_⟩ <;>
    norm_num [C1, C2, C3, thetaNum, thetaDen, kappa, gamma, Nat.factorial]

theorem conds_five_seven : Conds 7 5 := by
  refine ⟨by norm_num, by norm_num, ?_, ?_, ?_⟩ <;>
    norm_num [C1, C2, C3, thetaNum, thetaDen, kappa, gamma, Nat.factorial]

theorem conds_three_eight : Conds 8 3 := by
  refine ⟨by norm_num, by norm_num, ?_, ?_, ?_⟩ <;>
    norm_num [C1, C2, C3, thetaNum, thetaDen, kappa, gamma, Nat.factorial]

theorem conds_four_eight : Conds 8 4 := by
  refine ⟨by norm_num, by norm_num, ?_, ?_, ?_⟩ <;>
    norm_num [C1, C2, C3, thetaNum, thetaDen, kappa, gamma, Nat.factorial]

theorem conds_five_eight : Conds 8 5 := by
  refine ⟨by norm_num, by norm_num, ?_, ?_, ?_⟩ <;>
    norm_num [C1, C2, C3, thetaNum, thetaDen, kappa, gamma, Nat.factorial]

theorem conds_six_eight : Conds 8 6 := by
  refine ⟨by norm_num, by norm_num, ?_, ?_, ?_⟩ <;>
    norm_num [C1, C2, C3, thetaNum, thetaDen, kappa, gamma, Nat.factorial]

theorem conds_seven_eight : Conds 8 7 := by
  refine ⟨by norm_num, by norm_num, ?_, ?_, ?_⟩ <;>
    norm_num [C1, C2, C3, thetaNum, thetaDen, kappa, gamma, Nat.factorial]

theorem conds_three_nine : Conds 9 3 := by
  refine ⟨by norm_num, by norm_num, ?_, ?_, ?_⟩ <;>
    norm_num [C1, C2, C3, thetaNum, thetaDen, kappa, gamma, Nat.factorial]

theorem conds_four_nine : Conds 9 4 := by
  refine ⟨by norm_num, by norm_num, ?_, ?_, ?_⟩ <;>
    norm_num [C1, C2, C3, thetaNum, thetaDen, kappa, gamma, Nat.factorial]

theorem conds_five_nine : Conds 9 5 := by
  refine ⟨by norm_num, by norm_num, ?_, ?_, ?_⟩ <;>
    norm_num [C1, C2, C3, thetaNum, thetaDen, kappa, gamma, Nat.factorial]

theorem conds_six_nine : Conds 9 6 := by
  refine ⟨by norm_num, by norm_num, ?_, ?_, ?_⟩ <;>
    norm_num [C1, C2, C3, thetaNum, thetaDen, kappa, gamma, Nat.factorial]

theorem conds_seven_nine : Conds 9 7 := by
  refine ⟨by norm_num, by norm_num, ?_, ?_, ?_⟩ <;>
    norm_num [C1, C2, C3, thetaNum, thetaDen, kappa, gamma, Nat.factorial]

theorem conds_eight_nine : Conds 9 8 := by
  refine ⟨by norm_num, by norm_num, ?_, ?_, ?_⟩ <;>
    norm_num [C1, C2, C3, thetaNum, thetaDen, kappa, gamma, Nat.factorial]

/-- **`R_new` exactly** (`LIFT.md` §B.13.3).  For `3 ≤ k ≤ n-1` the three conditions hold
unless `(k,n)` is one of the four known exclusions. -/
theorem conds_of_not_excluded {n k : ℕ} (h3 : 3 ≤ k) (hkn : k < n)
    (e1 : ¬(n = 4 ∧ k = 3)) (e2 : ¬(n = 5 ∧ k = 3)) (e3 : ¬(n = 5 ∧ k = 4))
    (e4 : ¬(n = 6 ∧ k = 5)) : Conds n k := by
  rcases le_or_lt 10 n with hn | hn
  · exact condsT hn h3 hkn
  · interval_cases n <;> interval_cases k <;>
      simp_all <;>
      first
        | exact conds_three_six | exact conds_four_six
        | exact conds_three_seven | exact conds_four_seven | exact conds_five_seven
        | exact conds_six_seven
        | exact conds_three_eight | exact conds_four_eight | exact conds_five_eight
        | exact conds_six_eight | exact conds_seven_eight
        | exact conds_three_nine | exact conds_four_nine | exact conds_five_nine
        | exact conds_six_nine | exact conds_seven_nine | exact conds_eight_nine

section AxiomAudit

#print axioms gamma_pos
#print axioms gamma_succ
#print axioms gamma_antitone
#print axioms gamma_three
#print axioms gamma_le_six
#print axioms kappa_le_gamma
#print axioms kappa_le_num
#print axioms one_sub_kappa_ge
#print axioms C2_small
#print axioms C3_small
#print axioms hh
#print axioms B
#print axioms B_pos
#print axioms B_step
#print axioms B_le
#print axioms two_gamma_sq_le_B
#print axioms C2_large
#print axioms C3_large
#print axioms C1_tail
#print axioms condsT
#print axioms Lambda_le
#print axioms thetaDen_pos
#print axioms thetaT
#print axioms conds_three_six
#print axioms conds_four_six
#print axioms conds_three_seven
#print axioms conds_four_seven
#print axioms conds_five_seven
#print axioms conds_three_eight
#print axioms conds_four_eight
#print axioms conds_five_eight
#print axioms conds_six_eight
#print axioms conds_seven_eight
#print axioms conds_three_nine
#print axioms conds_four_nine
#print axioms conds_five_nine
#print axioms conds_six_nine
#print axioms conds_seven_nine
#print axioms conds_eight_nine
#print axioms conds_of_not_excluded

end AxiomAudit

end LemmaT
