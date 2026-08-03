/-
# Lemma U — `LEAN-ROADMAP.md` stone 14

`LIFT.md` §B.12.1:

> **Lemma U (univariate extraction, sharp) `[R]`.**  Let `a_1..a_n >= 0` and
> `f(S) = prod_i (a_i + S) = sum_t c_t S^t`.  Then for `0 <= m <= n`
>
>     c_m  >=  G(n,m) * inf_{S>0} f(S)/S^m ,
>     G(n,m) = C(n,m) m^m (n-m)^{n-m} / n^n ,
>
> with equality at `a = (1,...,1)`.

`[R]` Csikvári–Schweitzer arXiv:2006.16847 Lemma 2.8 (after Gurvits) and Brändén–Leake–Pak
arXiv:2008.05907 Cor. 5.9.  The roadmap records that this is NOT an irreducible import for Lean:
`LIFT.md`'s own proof uses only Newton's inequalities — formalised in this tree as
`NewtonIneq.pnorm_newton` — and one explicit certificate `S_0 = m/(rho(n-m))`.  This file is
that proof.

## The route, and where the work is

| § | content | the difficulty |
|---|---|---|
| 1 | the Vieta bridge `c_t = e_{n-t}(a)` | none — Mathlib has `Finset.prod_X_add_C_coeff` |
| 2 | `d_t = c_t/C(n,t) = pnorm a (n-t)`, log-concave, with its zero propagation | bookkeeping |
| 3 | the two-sided window `d_t rho^m <= d_m rho^t` | the load-bearing induction |
| 4 | the sum bound `f(S) <= (d_m/rho^m)(1 + rho S)^n` | binomial theorem |
| 5 | the certificate `S_0 = m/(rho(n-m))`, and Lemma U | rational algebra |

**The cleared form is what makes §3 tractable.**  The paper writes `d_t/d_m <= rho^{t-m}`, whose
exponent is a difference of naturals and changes sign at `t = m`.  Written as
`d_t * rho^m <= d_m * rho^t` it is one statement for all `t`, no subtraction anywhere, and it
splits into exactly two monotone inductions on the ratio — upward from `m` and downward from `m`
— each with one degenerate branch, rather than one induction with four.

## What lands, and the exact scope

`lemmaU_of_pos` is the theorem: for `a >= 0`, `0 < m < n` and `c_m = e_{n-m}(a) > 0`,

    G(n,m) * inf_{S>0} f(S)/S^m  <=  c_m ,

with `G` the very constant of `BorderPayment.G`, so this layer and
`graded_verify_borderrows.py` pin the same number.  `rho` is NOT a hypothesis: the window
witness `rho = d_{m+1}/d_m` is always admissible — `hup` holds with equality and `hdn` IS
Newton at `m` — so the only side condition is `c_m > 0`.

**`0 < m < n` is exactly the live range, not a convenience.**  §B.12.2 applies Lemma U at
`m = n - k`, and `R_new = {3 <= k <= n-1}` gives `1 <= m <= n-3`.  The excluded ends are the
ones the campaign has already ruled out: `m = 0` is `k = n`, where `LIFT.md` §B.14 shows the
capacity route is PROVABLY dead, and `m = n` is `k = 0`.  Both would additionally need a
limit argument rather than a certificate — at `m = 0` the infimum `inf_{S>0} prod_i (a_i + S)`
is approached as `S -> 0+` and is not attained — so nothing is lost by scoping them out and
something real would have to be built to include them.

**`c_m > 0` is a genuine side condition, and it is a positivity one.**  If `c_m = 0` then
`a` has more than `m` vanishing entries, `f(S)/S^m -> 0` as `S -> 0+`, and the bound is true
but again by a limit and not by any certificate: the `S_0` route cannot reach it, since
`f(S_0) > 0` at every `S_0 > 0`.  It is left as a hypothesis rather than papered over.
-/

import Mathlib.Tactic
import Mathlib.RingTheory.Polynomial.Vieta
import NewtonInequalities
import BorderPayment
import Capacity

open Finset

namespace LemmaU

open NewtonIneq

variable {n : ℕ}

/-! ## §1  The Vieta bridge

`f(S) = ∏_i (a_i + S)` expanded in `S`.  Mathlib's `Finset.prod_X_add_C_coeff` is exactly the
coefficient statement; all that is added here is the evaluation and the degree bound. -/

/-- `f_a(S) = ∏_i (a_i + S)`, the polynomial of Lemma U as a function of `S`. -/
noncomputable def fVal (a : Fin n → ℝ) (S : ℝ) : ℝ := ∏ i, (a i + S)

/-- **The Vieta bridge.**  `[S^t] ∏_i (a_i + S) = e_{n-t}(a)`. -/
theorem coeff_prod_X_add_C (a : Fin n → ℝ) {t : ℕ} (ht : t ≤ n) :
    (∏ i, (Polynomial.X + Polynomial.C (a i)) : Polynomial ℝ).coeff t = esymF (n - t) a := by
  have hcard : (univ : Finset (Fin n)).card = n := by simp
  have h := Finset.prod_X_add_C_coeff (univ : Finset (Fin n)) a (k := t)
    (by rw [hcard]; exact ht)
  rw [hcard] at h
  rw [h, esymF]

theorem natDegree_prod_X_add_C (a : Fin n → ℝ) :
    (∏ i, (Polynomial.X + Polynomial.C (a i)) : Polynomial ℝ).natDegree < n + 1 := by
  have h := Polynomial.natDegree_prod_le (univ : Finset (Fin n))
    (fun i => (Polynomial.X + Polynomial.C (a i) : Polynomial ℝ))
  have h2 : ∑ i : Fin n, (Polynomial.X + Polynomial.C (a i) : Polynomial ℝ).natDegree = n := by
    simp [Polynomial.natDegree_X_add_C]
  omega

/-- **`f` as its coefficient sum**, with the Vieta coefficients already substituted. -/
theorem fVal_eq_sum (a : Fin n → ℝ) (S : ℝ) :
    fVal a S = ∑ t ∈ range (n + 1), esymF (n - t) a * S ^ t := by
  have heval : Polynomial.eval S (∏ i, (Polynomial.X + Polynomial.C (a i)) : Polynomial ℝ)
      = fVal a S := by
    rw [Polynomial.eval_prod, fVal]
    exact Finset.prod_congr rfl fun i _ => by simp [add_comm]
  rw [← heval, Polynomial.eval_eq_sum_range' (natDegree_prod_X_add_C a)]
  exact Finset.sum_congr rfl fun t ht =>
    by rw [coeff_prod_X_add_C a (Nat.lt_succ_iff.mp (Finset.mem_range.mp ht))]

/-! ## §2  The normalised coefficient sequence

`d_t = c_t / C(n,t)`.  Since `C(n,t) = C(n,n-t)` this is exactly `NewtonIneq.pnorm a (n-t)`, so
Newton's inequality transfers with no work beyond reindexing. -/

/-- `d_t = c_t/C(n,t) = pnorm a (n-t)`. -/
noncomputable def dseq (a : Fin n → ℝ) (t : ℕ) : ℝ := pnorm a (n - t)

theorem dseq_nonneg {a : Fin n → ℝ} (ha : ∀ i, 0 ≤ a i) (t : ℕ) : 0 ≤ dseq a t :=
  pnorm_nonneg ha _

/-- The coefficient in terms of `d`: `c_t = C(n,t) d_t`. -/
theorem esymF_eq_choose_mul_dseq (a : Fin n → ℝ) {t : ℕ} (ht : t ≤ n) :
    esymF (n - t) a = (n.choose t : ℝ) * dseq a t := by
  have hc : n.choose (n - t) = n.choose t := Nat.choose_symm ht
  have hpos : ((n.choose t : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.choose_pos ht).ne'
  rw [dseq, pnorm, hc]
  field_simp

/-- `d_n = 1`. -/
@[simp] theorem dseq_top (a : Fin n → ℝ) : dseq a n = 1 := by
  rw [dseq, Nat.sub_self, pnorm_zero]

/-- **Newton, reindexed.**  `d` is log-concave. -/
theorem dseq_newton (a : Fin n → ℝ) {t : ℕ} (h1 : 1 ≤ t) (h2 : t + 1 ≤ n) :
    dseq a (t - 1) * dseq a (t + 1) ≤ (dseq a t) ^ 2 := by
  have hj1 : 1 ≤ n - t := by omega
  have hj2 : (n - t) + 1 ≤ n := by omega
  have h := pnorm_newton a (n - t) hj1 hj2
  have e1 : n - t - 1 = n - (t + 1) := by omega
  have e2 : n - t + 1 = n - (t - 1) := by omega
  rw [e1, e2] at h
  rw [dseq, dseq, dseq]
  linarith [h]

/-- **Zero propagation, downward in `t`.**  `d_t = 0` forces `d_{t-1} = 0`: for a non-negative
vector, once an elementary symmetric function vanishes so does every later one. -/
theorem dseq_eq_zero_of_succ {a : Fin n → ℝ} (ha : ∀ i, 0 ≤ a i) {t : ℕ} (ht : t ≤ n)
    (h1 : 1 ≤ t) (h : dseq a t = 0) : dseq a (t - 1) = 0 := by
  have hchoose : ((n.choose (n - t) : ℕ) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.choose_pos (Nat.sub_le n t)).ne'
  have he : esymF (n - t) a = 0 := by
    rw [dseq, pnorm, div_eq_zero_iff] at h
    rcases h with h | h
    · exact h
    · exact absurd h hchoose
  have he' : esymF (n - t + 1) a = 0 := esymF_succ_eq_zero ha he
  have e2 : n - t + 1 = n - (t - 1) := by omega
  rw [e2] at he'
  rw [dseq, pnorm, he']
  simp

/-- Contrapositive, packaged: positivity spreads upward from any positive `d_m`. -/
theorem dseq_pos_of_le {a : Fin n → ℝ} (ha : ∀ i, 0 ≤ a i) {m : ℕ} (hm : 0 < dseq a m) :
    ∀ t, m ≤ t → t ≤ n → 0 < dseq a t := by
  intro t hmt
  induction t, hmt using Nat.le_induction with
  | base => intro _; exact hm
  | succ s _ ih =>
      intro hsn
      have hs : 0 < dseq a s := ih (by omega)
      rcases eq_or_lt_of_le (dseq_nonneg ha (s + 1)) with h0 | h0
      · exfalso
        have := dseq_eq_zero_of_succ ha hsn (by omega) h0.symm
        simp only [Nat.add_sub_cancel] at this
        exact absurd this hs.ne'
      · exact h0

/-! ## §3  The two-sided window

`LIFT.md` §B.12.1 picks `rho` in the window `[d_{m+1}/d_m, d_m/d_{m-1}]` and propagates
`d_t/d_m <= rho^{t-m}` to every `t`.  Here the conclusion is carried in the CLEARED form

    d_t * rho^m  <=  d_m * rho^t ,

which has no natural subtraction and is a single statement on both sides of `m`.  It comes out
of two monotone ratio lemmas, each with exactly one degenerate branch:

* `dseq_ratio_up`   — `d_{t+1} <= rho d_t` for `m <= t < n`.  No degeneracy: `dseq_pos_of_le`
  makes every `d_t` positive above `m`, so the Newton division is always legal.
* `dseq_ratio_down` — `rho d_j <= d_{j+1}` for `j + 1 <= m`.  One degeneracy: `d_{j+1} = 0`,
  where `dseq_eq_zero_of_succ` forces `d_j = 0` and the inequality is `0 <= 0`.

The window hypotheses are ARGUMENTS, not derived: `hup` is asked for only when `m + 1 <= n` and
`hdn` is vacuous at `m = 0`, so the two degenerate ends of Lemma U cost nothing here. -/

variable {ρ : ℝ}

/-- **Upward ratio.**  Above `m` the sequence decays by at least `rho` each step. -/
theorem dseq_ratio_up {a : Fin n → ℝ} (ha : ∀ i, 0 ≤ a i) {m : ℕ} (hm : 0 < dseq a m)
    (hup : m + 1 ≤ n → dseq a (m + 1) ≤ ρ * dseq a m) :
    ∀ t, m ≤ t → t + 1 ≤ n → dseq a (t + 1) ≤ ρ * dseq a t := by
  intro t hmt
  induction t, hmt using Nat.le_induction with
  | base => exact hup
  | succ s hms ih =>
      intro hsn
      have ihs := ih (by omega)
      have hds : 0 < dseq a s := dseq_pos_of_le ha hm s hms (by omega)
      have hnewton := dseq_newton a (t := s + 1) (by omega) (by omega)
      simp only [Nat.add_sub_cancel] at hnewton
      have h2 : dseq a (s + 1) * dseq a (s + 1) ≤ dseq a (s + 1) * (ρ * dseq a s) :=
        mul_le_mul_of_nonneg_left ihs (dseq_nonneg ha (s + 1))
      nlinarith [hnewton, h2, hds]

/-- **Downward ratio.**  Below `m` the sequence grows by at least `rho` each step.  The single
degenerate branch is `d_{j+1} = 0`, and `dseq_eq_zero_of_succ` closes it. -/
theorem dseq_ratio_down {a : Fin n → ℝ} (ha : ∀ i, 0 ≤ a i) {m : ℕ} (hmn : m ≤ n)
    (hdn : ∀ p : ℕ, p + 1 = m → ρ * dseq a p ≤ dseq a m) :
    ∀ u j : ℕ, j + u + 1 = m → ρ * dseq a j ≤ dseq a (j + 1) := by
  intro u
  induction u with
  | zero =>
      intro j hj
      have hjm : j + 1 = m := by omega
      rw [hjm]
      exact hdn j hjm
  | succ v ih =>
      intro j hj
      have ihj : ρ * dseq a (j + 1) ≤ dseq a (j + 1 + 1) := ih (j + 1) (by omega)
      rcases eq_or_lt_of_le (dseq_nonneg ha (j + 1)) with h0 | h0
      · have hz : dseq a (j + 1) = 0 := h0.symm
        have hzj := dseq_eq_zero_of_succ ha (show j + 1 ≤ n by omega) (by omega) hz
        simp only [Nat.add_sub_cancel] at hzj
        rw [hzj, hz, mul_zero]
      · have hnewton := dseq_newton a (t := j + 1) (by omega) (by omega)
        simp only [Nat.add_sub_cancel] at hnewton
        have h2 : dseq a j * (ρ * dseq a (j + 1)) ≤ dseq a j * dseq a (j + 1 + 1) :=
          mul_le_mul_of_nonneg_left ihj (dseq_nonneg ha j)
        nlinarith [hnewton, h2, h0]

/-- **THE WINDOW, cleared.**  `d_t · rho^m ≤ d_m · rho^t` at every `t ≤ n`, on both sides of
`m` at once. -/
theorem window {a : Fin n → ℝ} (ha : ∀ i, 0 ≤ a i) {m : ℕ} (hmn : m ≤ n) (hm : 0 < dseq a m)
    (hρ : 0 < ρ) (hup : m + 1 ≤ n → dseq a (m + 1) ≤ ρ * dseq a m)
    (hdn : ∀ p : ℕ, p + 1 = m → ρ * dseq a p ≤ dseq a m) :
    ∀ t, t ≤ n → dseq a t * ρ ^ m ≤ dseq a m * ρ ^ t := by
  have hupward : ∀ t, m ≤ t → t ≤ n → dseq a t * ρ ^ m ≤ dseq a m * ρ ^ t := by
    intro t hmt
    induction t, hmt using Nat.le_induction with
    | base => intro _; exact le_rfl
    | succ s hms ih =>
        intro hsn
        have ihs := ih (by omega)
        have hstep := dseq_ratio_up ha hm hup s hms hsn
        calc dseq a (s + 1) * ρ ^ m ≤ (ρ * dseq a s) * ρ ^ m :=
              mul_le_mul_of_nonneg_right hstep (by positivity)
          _ = ρ * (dseq a s * ρ ^ m) := by ring
          _ ≤ ρ * (dseq a m * ρ ^ s) := by
              exact mul_le_mul_of_nonneg_left ihs hρ.le
          _ = dseq a m * ρ ^ (s + 1) := by ring
  have hdownward : ∀ u t, t + u = m → dseq a t * ρ ^ m ≤ dseq a m * ρ ^ t := by
    intro u
    induction u with
    | zero => intro t ht; rw [show t = m by omega]
    | succ v ih =>
        intro t ht
        have ihs : dseq a (t + 1) * ρ ^ m ≤ dseq a m * ρ ^ (t + 1) := ih (t + 1) (by omega)
        have hstep : ρ * dseq a t ≤ dseq a (t + 1) := dseq_ratio_down ha hmn hdn v t (by omega)
        have hmul : (ρ * dseq a t) * ρ ^ m ≤ dseq a (t + 1) * ρ ^ m :=
          mul_le_mul_of_nonneg_right hstep (by positivity)
        have hchain : ρ * (dseq a t * ρ ^ m) ≤ ρ * (dseq a m * ρ ^ t) := by
          calc ρ * (dseq a t * ρ ^ m) = (ρ * dseq a t) * ρ ^ m := by ring
            _ ≤ dseq a (t + 1) * ρ ^ m := hmul
            _ ≤ dseq a m * ρ ^ (t + 1) := ihs
            _ = ρ * (dseq a m * ρ ^ t) := by ring
        exact le_of_mul_le_mul_left hchain hρ
  intro t htn
  rcases le_or_lt m t with h | h
  · exact hupward t h htn
  · exact hdownward (m - t) t (by omega)

/-! ## §4  The sum bound

The window, summed against the binomial coefficients:

    f(S) rho^m  =  sum_t C(n,t) (d_t rho^m) S^t
                <=  sum_t C(n,t) d_m (rho S)^t  =  d_m (1 + rho S)^n . -/

theorem fVal_nonneg {a : Fin n → ℝ} (ha : ∀ i, 0 ≤ a i) {S : ℝ} (hS : 0 ≤ S) :
    0 ≤ fVal a S :=
  Finset.prod_nonneg fun i _ => add_nonneg (ha i) hS

/-- **The sum bound.**  `f(S) rho^m ≤ d_m (1 + rho S)^n` for every `S ≥ 0`. -/
theorem sum_bound {a : Fin n → ℝ} (ha : ∀ i, 0 ≤ a i) {m : ℕ} (hmn : m ≤ n) (hm : 0 < dseq a m)
    (hρ : 0 < ρ) (hup : m + 1 ≤ n → dseq a (m + 1) ≤ ρ * dseq a m)
    (hdn : ∀ p : ℕ, p + 1 = m → ρ * dseq a p ≤ dseq a m) {S : ℝ} (hS : 0 ≤ S) :
    fVal a S * ρ ^ m ≤ dseq a m * (1 + ρ * S) ^ n := by
  have hbin : (1 + ρ * S) ^ n = ∑ t ∈ range (n + 1), (n.choose t : ℝ) * (ρ * S) ^ t := by
    rw [add_comm, add_pow]
    exact Finset.sum_congr rfl fun t _ => by ring
  rw [fVal_eq_sum, Finset.sum_mul, hbin, Finset.mul_sum]
  refine Finset.sum_le_sum fun t ht => ?_
  have htn : t ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp ht)
  have hw := window ha hmn hm hρ hup hdn t htn
  rw [esymF_eq_choose_mul_dseq a htn]
  calc (n.choose t : ℝ) * dseq a t * S ^ t * ρ ^ m
      = ((n.choose t : ℝ) * S ^ t) * (dseq a t * ρ ^ m) := by ring
    _ ≤ ((n.choose t : ℝ) * S ^ t) * (dseq a m * ρ ^ t) :=
        mul_le_mul_of_nonneg_left hw (by positivity)
    _ = dseq a m * ((n.choose t : ℝ) * (ρ * S) ^ t) := by rw [mul_pow]; ring

/-! ## §5  The certificate, and Lemma U

`S_0 = m/(rho(n-m))` makes `rho S_0 = m/(n-m)` and `1 + rho S_0 = n/(n-m)`, and then the sum
bound's right-hand side is **exactly** `c_m / G(n,m)` — no slack, which is the sharpness clause
of Lemma U. -/

/-- The Lemma U certificate `S_0 = m/(rho(n-m))`. -/
noncomputable def S0 (ρ : ℝ) (n m : ℕ) : ℝ := (m : ℝ) / (ρ * ((n - m : ℕ) : ℝ))

/-- `BorderPayment.G` over `ℝ`. -/
theorem G_cast (n m : ℕ) :
    ((BorderPayment.G n m : ℚ) : ℝ)
      = (n.choose m : ℝ) * (m : ℝ) ^ m * ((n - m : ℕ) : ℝ) ^ (n - m) / (n : ℝ) ^ n := by
  rw [BorderPayment.G]
  push_cast
  ring

/-- **The certificate evaluated.**  At `S_0` the sum bound is exactly `c_m/G(n,m)`. -/
theorem certificate {a : Fin n → ℝ} (ha : ∀ i, 0 ≤ a i) {m : ℕ} (h0 : 0 < m) (hmn : m < n)
    (hm : 0 < dseq a m) (hρ : 0 < ρ)
    (hup : m + 1 ≤ n → dseq a (m + 1) ≤ ρ * dseq a m)
    (hdn : ∀ p : ℕ, p + 1 = m → ρ * dseq a p ≤ dseq a m) :
    ((BorderPayment.G n m : ℚ) : ℝ) * (fVal a (S0 ρ n m) / (S0 ρ n m) ^ m)
      ≤ esymF (n - m) a := by
  have hK : ((n - m : ℕ) : ℝ) = (n : ℝ) - (m : ℝ) := by
    push_cast [Nat.cast_sub hmn.le]
    ring
  have hKpos : (0 : ℝ) < ((n - m : ℕ) : ℝ) := by
    rw [hK]
    have : (m : ℝ) < (n : ℝ) := by exact_mod_cast hmn
    linarith
  have hMpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast h0
  have hNpos : (0 : ℝ) < (n : ℝ) := by
    have : (0 : ℕ) < n := by omega
    exact_mod_cast this
  have hS0 : 0 < S0 ρ n m := by
    rw [S0]
    positivity
  -- `rho S_0 = m/(n-m)` and `1 + rho S_0 = n/(n-m)`
  have hρS : ρ * S0 ρ n m = (m : ℝ) / ((n - m : ℕ) : ℝ) := by
    rw [S0]
    field_simp
    ring
  have hKne : ((n - m : ℕ) : ℝ) ≠ 0 := hKpos.ne'
  have hKM : ((n - m : ℕ) : ℝ) + (m : ℝ) = (n : ℝ) := by
    rw [hK]; ring
  have hone : 1 + ρ * S0 ρ n m = (n : ℝ) / ((n - m : ℕ) : ℝ) := by
    rw [hρS, ← hKM]
    field_simp
  have hsum := sum_bound ha hmn.le hm hρ hup hdn (S := S0 ρ n m) hS0.le
  rw [hone] at hsum
  have hKpow : ((n - m : ℕ) : ℝ) ^ (n - m) * ((n - m : ℕ) : ℝ) ^ m = ((n - m : ℕ) : ℝ) ^ n := by
    rw [← pow_add]
    congr 1
    omega
  -- The certificate is EXACT: `G · d_m · (n/(n-m))^n = c_m · (m/(n-m))^m`.
  have hGeq : ((BorderPayment.G n m : ℚ) : ℝ) * (dseq a m * ((n : ℝ) / ((n - m : ℕ) : ℝ)) ^ n)
      = ((n.choose m : ℝ) * dseq a m) * ((m : ℝ) / ((n - m : ℕ) : ℝ)) ^ m := by
    rw [G_cast, div_pow, div_pow, ← hKpow]
    field_simp
    ring
  have hGnn : (0 : ℝ) ≤ ((BorderPayment.G n m : ℚ) : ℝ) := by
    have h := BorderPayment.G_nonneg n m
    exact_mod_cast h
  rw [esymF_eq_choose_mul_dseq a hmn.le, ← mul_div_assoc, div_le_iff₀ (pow_pos hS0 m)]
  refine le_of_mul_le_mul_right ?_ (pow_pos hρ m)
  calc ((BorderPayment.G n m : ℚ) : ℝ) * fVal a (S0 ρ n m) * ρ ^ m
      = ((BorderPayment.G n m : ℚ) : ℝ) * (fVal a (S0 ρ n m) * ρ ^ m) := by ring
    _ ≤ ((BorderPayment.G n m : ℚ) : ℝ) * (dseq a m * ((n : ℝ) / ((n - m : ℕ) : ℝ)) ^ n) :=
        mul_le_mul_of_nonneg_left hsum hGnn
    _ = ((n.choose m : ℝ) * dseq a m) * ((m : ℝ) / ((n - m : ℕ) : ℝ)) ^ m := hGeq
    _ = ((n.choose m : ℝ) * dseq a m) * (ρ * S0 ρ n m) ^ m := by rw [hρS]
    _ = (n.choose m : ℝ) * dseq a m * S0 ρ n m ^ m * ρ ^ m := by rw [mul_pow]; ring

/-! ### The capacity form

`inf_{S>0} f(S)/S^m` is the `Fin 1` case of `Capacity.cap`, so the audited two-lemma interface
of `Capacity.lean` carries it and nothing new is defined. -/

/-- `cap_m(f) = inf_{S>0} f(S)/S^m`, as the one-variable case of `Capacity.cap`. -/
noncomputable def capU (m : ℕ) (f : ℝ → ℝ) : ℝ :=
  Capacity.cap (fun _ : Fin 1 => (m : ℝ)) (fun x => f (x 0))

theorem capU_le {m : ℕ} {f : ℝ → ℝ} (hf : ∀ S : ℝ, 0 < S → 0 ≤ f S) {S : ℝ} (hS : 0 < S) :
    capU m f ≤ f S / S ^ m := by
  have hp : Capacity.NonnegOn (fun x : Fin 1 → ℝ => f (x 0)) := fun x hx => hf _ (hx 0)
  have h := Capacity.cap_le (fun _ : Fin 1 => (m : ℝ)) hp (x := fun _ => S) (fun _ => hS)
  have hmon : Capacity.monom (fun _ : Fin 1 => (m : ℝ)) (fun _ => S) = S ^ m := by
    rw [Capacity.monom, Fin.prod_univ_one, Real.rpow_natCast]
  rwa [hmon] at h

/-- **LEMMA U** (`LIFT.md` §B.12.1, roadmap stone 14 / inventory A10).  For `a ≥ 0` and
`0 < m < n`, with `rho` in the Newton window at `m`,

    c_m  ≥  G(n,m) · inf_{S>0} f(S)/S^m ,       c_m = e_{n-m}(a) .

`G` is `BorderPayment.G`, the constant of `graded_verify_borderrows.py`, so the two layers pin
the same number. -/
theorem lemmaU {a : Fin n → ℝ} (ha : ∀ i, 0 ≤ a i) {m : ℕ} (h0 : 0 < m) (hmn : m < n)
    (hm : 0 < dseq a m) (hρ : 0 < ρ)
    (hup : m + 1 ≤ n → dseq a (m + 1) ≤ ρ * dseq a m)
    (hdn : ∀ p : ℕ, p + 1 = m → ρ * dseq a p ≤ dseq a m) :
    ((BorderPayment.G n m : ℚ) : ℝ) * capU m (fVal a) ≤ esymF (n - m) a := by
  have hK : ((n - m : ℕ) : ℝ) = (n : ℝ) - (m : ℝ) := by
    push_cast [Nat.cast_sub hmn.le]
    ring
  have hKpos : (0 : ℝ) < ((n - m : ℕ) : ℝ) := by
    rw [hK]
    have : (m : ℝ) < (n : ℝ) := by exact_mod_cast hmn
    linarith
  have hMpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast h0
  have hS0 : 0 < S0 ρ n m := by
    rw [S0]
    positivity
  have hGnn : (0 : ℝ) ≤ ((BorderPayment.G n m : ℚ) : ℝ) := by
    have h := BorderPayment.G_nonneg n m
    exact_mod_cast h
  refine le_trans ?_ (certificate ha h0 hmn hm hρ hup hdn)
  exact mul_le_mul_of_nonneg_left
    (capU_le (fun S hS => fVal_nonneg ha hS.le) hS0) hGnn

/-- **Sharpness at `a = (1,…,1)`**, the equality clause of Lemma U: `c_m = C(n,m)` there, and
`G(n,m) · n^n/(m^m (n-m)^{n-m}) = C(n,m)` exactly.  This is the arithmetic half of
`graded_verify_borderrows.py` block [2]'s "SHARPNESS" check. -/
theorem G_sharp {n m : ℕ} (h0 : 0 < m) (hmn : m < n) :
    ((BorderPayment.G n m : ℚ) : ℝ)
        * ((n : ℝ) ^ n / ((m : ℝ) ^ m * ((n - m : ℕ) : ℝ) ^ (n - m)))
      = (n.choose m : ℝ) := by
  have hMpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast h0
  have hKpos : (0 : ℝ) < ((n - m : ℕ) : ℝ) := by
    have : (0 : ℕ) < n - m := by omega
    exact_mod_cast this
  have hNpos : (0 : ℝ) < (n : ℝ) := by
    have : (0 : ℕ) < n := by omega
    exact_mod_cast this
  rw [G_cast]
  field_simp
  ring

/-! ### The window is non-empty, so `rho` is not a real hypothesis

`rho = d_{m+1}/d_m` is always admissible: `hup` holds with EQUALITY, and `hdn` is exactly
Newton's inequality at `m`.  So Lemma U needs no supplied `rho` on its live range. -/

theorem dseq_pos_iff {a : Fin n → ℝ} {m : ℕ} (hmn : m ≤ n) :
    0 < dseq a m ↔ 0 < esymF (n - m) a := by
  have hc : (0 : ℝ) < (n.choose m : ℝ) := by exact_mod_cast Nat.choose_pos hmn
  rw [esymF_eq_choose_mul_dseq a hmn]
  constructor <;> intro h <;> nlinarith

/-- **LEMMA U, with `rho` discharged.**  For `a ≥ 0`, `0 < m < n` and `c_m = e_{n-m}(a) > 0`,

    G(n,m) · inf_{S>0} f(S)/S^m  ≤  c_m .

The window witness is `rho = d_{m+1}/d_m`: `hup` holds with equality and `hdn` IS Newton at `m`,
so nothing is assumed beyond `c_m > 0`. -/
theorem lemmaU_of_pos {a : Fin n → ℝ} (ha : ∀ i, 0 ≤ a i) {m : ℕ} (h0 : 0 < m) (hmn : m < n)
    (hc : 0 < esymF (n - m) a) :
    ((BorderPayment.G n m : ℚ) : ℝ) * capU m (fVal a) ≤ esymF (n - m) a := by
  have hm : 0 < dseq a m := (dseq_pos_iff hmn.le).mpr hc
  have hm1 : 0 < dseq a (m + 1) := dseq_pos_of_le ha hm (m + 1) (by omega) (by omega)
  have hρ : 0 < dseq a (m + 1) / dseq a m := div_pos hm1 hm
  have hup : m + 1 ≤ n → dseq a (m + 1) ≤ (dseq a (m + 1) / dseq a m) * dseq a m := by
    intro _
    rw [div_mul_cancel₀ _ hm.ne']
  have hdn : ∀ p : ℕ, p + 1 = m → (dseq a (m + 1) / dseq a m) * dseq a p ≤ dseq a m := by
    intro p hp
    have hnewton := dseq_newton a (t := m) (by omega) (by omega)
    rw [show m - 1 = p by omega] at hnewton
    rw [div_mul_eq_mul_div, div_le_iff₀ hm]
    nlinarith [hnewton]
  exact lemmaU ha h0 hmn hm hρ hup hdn

section AxiomAudit

#print axioms fVal
#print axioms coeff_prod_X_add_C
#print axioms natDegree_prod_X_add_C
#print axioms fVal_eq_sum
#print axioms dseq
#print axioms dseq_nonneg
#print axioms esymF_eq_choose_mul_dseq
#print axioms dseq_top
#print axioms dseq_newton
#print axioms dseq_eq_zero_of_succ
#print axioms dseq_pos_of_le
#print axioms dseq_ratio_up
#print axioms dseq_ratio_down
#print axioms window
#print axioms fVal_nonneg
#print axioms sum_bound
#print axioms S0
#print axioms G_cast
#print axioms certificate
#print axioms capU
#print axioms capU_le
#print axioms lemmaU
#print axioms G_sharp
#print axioms dseq_pos_iff
#print axioms lemmaU_of_pos

end AxiomAudit

end LemmaU
