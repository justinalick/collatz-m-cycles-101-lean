import Collatz.HercherVertex
import Collatz.HercherChain91

/-!
# No Collatz 91-cycle, from the verification bound and the Simons–de Weger ceiling

`HercherChain91.lean` runs the `m = 91` bootstrap up to `K ≥ K₅ = 77 692 117 359 936 589 403`
with the vertex-free Theorem 21. The last two steps need the vertex-type bound of the corrigendum;
`HercherVertex.lean` proves the variant `f(v) + (m₂ − 1) f(τ)` (`theorem21_two`), and it suffices:

| step | premise `K ≥` | `m₂` | `N ≤ v` | `M ≤ τ` | `ε` | consequence `K ≥` |
|---|---|---|---|---|---|---|
| 6 | 77 692 117 359 936 589 403 | 89 | 70 | 111 | `621 · 10⁻⁴³` | 205 632 218 873 398 596 256 |
| 7 | 205 632 218 873 398 596 256 | 91 | 75 | 119 | `186 · 10⁻⁴⁵` | 7 941 964 418 702 608 664 581 |

(the Farey certificates are those of `bootstrap_core`, steps 6 and 7). Hence

* `K_ge_of_91_cycle'`: if every `0 < n ≤ X₀ = 695 · 2⁶⁰` reaches 1, every nontrivial positive
  `T`-cycle with 91 local minima has `K ≥ 7 941 964 418 702 608 664 581`;
* `no_91_cycle`: with, in addition, the Simons–de Weger ceiling `K < 1.4784 · 91 · δ⁹¹`
  (Lemma 16 of their paper; their Lemma 14 bound `K < K₁(91) ≈ 2.6 · 10²¹` would do as well),
  no nontrivial positive `T`-cycle has 91 local minima.

The two hypotheses are a computation (Bařina's verification to `2⁷¹ > 695 · 2⁶⁰`) and the one
transcendence input (Rhin's measure for `log 3/log 2`, through Simons–de Weger); all of Hercher's
analysis is proved.
-/

namespace Collatz

open Finset

/-- **A chain step from Theorem 21 with the two-element bound.** Side conditions over `ℚ`:
`N ≤ v` and `M ≤ τ` through `δ ≤ deltaUp`, and
`(m − m₂)/X₀ + 1/(2^N − 1) + (m₂ − 1)/(2^M − 1) ≤ ε K₀ · 0.6931471803`. -/
theorem ratioIn_of_window_two {x p : ℕ} (hx : 0 < x) (hp : 0 < p) (hcyc : T^[p] x = x)
    {m m₂ N M Kp X₀ : ℕ} (hm : numLocalMin x p = m) (hm₂ : 1 ≤ m₂) (hm₂m : m₂ ≤ m)
    (hX₀ : 0 < X₀) (hlow : ∀ j, X₀ ≤ T^[j] x) (hKp : 0 < Kp) (hK : Kp ≤ oddCount T x p)
    {ε : ℚ} (hε0 : 0 < ε) (hN1 : 1 ≤ N) (hM1 : 1 ≤ M)
    (hN : (N : ℚ) * m * geomQ deltaUp m₂ ≤ m₂ * Kp)
    (hM : (M : ℚ) * m * (1 + geomQ deltaUp (m₂ - 1)) ≤ m₂ * Kp)
    (hε : ((m - m₂ : ℕ) : ℚ) / X₀ + 1 / (2 ^ N - 1) + ((m₂ - 1 : ℕ) : ℚ) / (2 ^ M - 1) ≤
      ε * Kp * (6931471803 / 10 ^ 10)) :
    RatioIn p (oddCount T x p) ε := by
  have h21 := theorem21_two hx hp hcyc hm₂ (by rw [hm]; exact hm₂m) (X₀ := (X₀ : ℝ))
    (by exact_mod_cast hX₀) (fun j => by exact_mod_cast hlow j)
  rw [hm] at h21
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hGpos := geomSum_delta_pos hm₂
  have hδ0 : (0 : ℝ) ≤ Real.logb 2 3 := by linarith [one_le_logb_two_three]
  have hKR : (Kp : ℝ) ≤ oddCount T x p := by exact_mod_cast hK
  have hm₂R : (0 : ℝ) ≤ m₂ := Nat.cast_nonneg _
  -- `N ≤ v`
  have hG : ∑ d ∈ range m₂, Real.logb 2 3 ^ d ≤ ∑ d ∈ range m₂, (deltaUp : ℝ) ^ d :=
    sum_le_sum (fun d _ => pow_le_pow_left₀ hδ0 logb_le_deltaUp d)
  have hNR : (N : ℝ) * m * ∑ d ∈ range m₂, (deltaUp : ℝ) ^ d ≤ m₂ * Kp := by
    rw [geomQ_eq] at hN
    have := (Rat.cast_le (K := ℝ)).mpr hN
    push_cast at this
    linarith [this]
  have hv : (N : ℝ) ≤ windowExp m m₂ (oddCount T x p) := by
    rw [windowExp, le_div_iff₀ (mul_pos hmpos hGpos)]
    have a1 : (N : ℝ) * ((m : ℝ) * ∑ d ∈ range m₂, Real.logb 2 3 ^ d) ≤
        (N : ℝ) * ((m : ℝ) * ∑ d ∈ range m₂, (deltaUp : ℝ) ^ d) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hG hmpos.le) (Nat.cast_nonneg _)
    have a2 : (m₂ : ℝ) * Kp ≤ m₂ * oddCount T x p := mul_le_mul_of_nonneg_left hKR hm₂R
    linarith
  -- `M ≤ τ`
  have hG' : 1 + ∑ d ∈ range (m₂ - 1), Real.logb 2 3 ^ d ≤
      1 + ∑ d ∈ range (m₂ - 1), (deltaUp : ℝ) ^ d := by
    have := sum_le_sum (fun d (_ : d ∈ range (m₂ - 1)) =>
      pow_le_pow_left₀ hδ0 logb_le_deltaUp d)
    linarith
  have hG'pos : (0 : ℝ) < 1 + ∑ d ∈ range (m₂ - 1), Real.logb 2 3 ^ d := by
    have : (0 : ℝ) ≤ ∑ d ∈ range (m₂ - 1), Real.logb 2 3 ^ d :=
      sum_nonneg (fun d _ => pow_nonneg hδ0 d)
    linarith
  have hMR : (M : ℝ) * m * (1 + ∑ d ∈ range (m₂ - 1), (deltaUp : ℝ) ^ d) ≤ m₂ * Kp := by
    rw [geomQ_eq] at hM
    have := (Rat.cast_le (K := ℝ)).mpr hM
    push_cast at this
    linarith [this]
  have hτ : (M : ℝ) ≤ windowExp2 m m₂ (oddCount T x p) := by
    rw [windowExp2, le_div_iff₀ (mul_pos hmpos hG'pos)]
    have a1 : (M : ℝ) * ((m : ℝ) * (1 + ∑ d ∈ range (m₂ - 1), Real.logb 2 3 ^ d)) ≤
        (M : ℝ) * ((m : ℝ) * (1 + ∑ d ∈ range (m₂ - 1), (deltaUp : ℝ) ^ d)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hG' hmpos.le) (Nat.cast_nonneg _)
    have a2 : (m₂ : ℝ) * Kp ≤ m₂ * oddCount T x p := mul_le_mul_of_nonneg_left hKR hm₂R
    linarith
  -- the powers of two
  have h2N : (2 : ℝ) ^ N ≤ (2 : ℝ) ^ windowExp m m₂ (oddCount T x p) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hv
  have h2M : (2 : ℝ) ^ M ≤ (2 : ℝ) ^ windowExp2 m m₂ (oddCount T x p) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hτ
  have h2N1 : (2 : ℝ) ≤ 2 ^ N := by
    calc (2 : ℝ) = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ N := pow_le_pow_right₀ (by norm_num) hN1
  have h2M1 : (2 : ℝ) ≤ 2 ^ M := by
    calc (2 : ℝ) = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ M := pow_le_pow_right₀ (by norm_num) hM1
  have t1 : 3 / ((2 : ℝ) ^ windowExp m m₂ (oddCount T x p) - 1) ≤ 3 / ((2 : ℝ) ^ N - 1) :=
    div_le_div_of_nonneg_left (by norm_num) (by linarith) (by linarith)
  have t2 : 3 * ((m₂ - 1 : ℕ) : ℝ) / ((2 : ℝ) ^ windowExp2 m m₂ (oddCount T x p) - 1) ≤
      3 * ((m₂ - 1 : ℕ) : ℝ) / ((2 : ℝ) ^ M - 1) :=
    div_le_div_of_nonneg_left (by positivity) (by linarith) (by linarith)
  have hεR := (Rat.cast_le (K := ℝ)).mpr hε
  push_cast at hεR
  have e1 : 3 / ((2 : ℝ) ^ N - 1) = 3 * (1 / ((2 : ℝ) ^ N - 1)) := by ring
  have e2 : 3 * ((m - m₂ : ℕ) : ℝ) / (X₀ : ℝ) = 3 * (((m - m₂ : ℕ) : ℝ) / (X₀ : ℝ)) := by ring
  have e3 : 3 * ((m₂ - 1 : ℕ) : ℝ) / ((2 : ℝ) ^ M - 1) =
      3 * (((m₂ - 1 : ℕ) : ℝ) / ((2 : ℝ) ^ M - 1)) := by ring
  exact ratioIn_of_lambda_lt hx hp hcyc hKp hK hε0
    (B := ((m - m₂ : ℕ) : ℝ) / X₀ + 1 / ((2 : ℝ) ^ N - 1) + ((m₂ - 1 : ℕ) : ℝ) / (2 ^ M - 1))
    (by linarith) (by linarith [hεR])

/-- **Every nontrivial cycle with 91 local minima has `K ≥ 7 941 964 418 702 608 664 581`**, if
every `0 < n ≤ 695 · 2⁶⁰` reaches 1. -/
theorem K_ge_of_91_cycle' (hX₀ : ∀ n, 0 < n → n ≤ 695 * 2 ^ 60 → Reaches T n 1)
    {x p : ℕ} (hx : 0 < x) (hp : 0 < p) (hcyc : T^[p] x = x) (hx1 : x ≠ 1) (hx2 : x ≠ 2)
    (h91 : numLocalMin x p = 91) : 7941964418702608664581 ≤ oddCount T x p := by
  have hlow : ∀ j, 695 * 2 ^ 60 ≤ T^[j] x := by
    intro j
    by_contra hlt
    push_neg at hlt
    exact cycle_not_reaches_one hp hcyc hx1 hx2 j (hX₀ _ (iterate_T_pos hx j) hlt.le)
  have k5 := K_ge_of_numLocalMin_91 hx hp hcyc h91 hlow
  have hK : 0 < oddCount T x p := by omega
  have hX : 0 < 695 * 2 ^ 60 := by norm_num
  -- step 6, `m₂ = 89`
  have k6 : 205632218873398596256 ≤ oddCount T x p := by
    have r := ratioIn_of_window_two hx hp hcyc h91 (m₂ := 89) (N := 70) (M := 111)
      (by norm_num) (by norm_num) hX hlow (by norm_num) k5 (ε := 621 / 10 ^ 43) (by norm_num)
      (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    have h := chain_step hK r (a := 202780263237295321099) (b := 127940101513462006853)
      (c := 123139092617126647266) (d := 77692117359936589403) (by norm_num) (by norm_num)
      (by norm_num) (by decide +kernel) (by decide +kernel)
    omega
  -- step 7, `m₂ = 91`
  have r := ratioIn_of_window_two hx hp hcyc h91 (m₂ := 91) (N := 75) (M := 119)
    (by norm_num) (by norm_num) hX hlow (by norm_num) k6 (ε := 186 / 10 ^ 45) (by norm_num)
    (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have h := chain_step hK r (a := 12261796429850908150604) (b := 7736332199829210068325)
    (c := 325919355854421968365) (d := 205632218873398596256) (by norm_num) (by norm_num)
    (by norm_num) (by decide +kernel) (by decide +kernel)
  omega

/-- **Hercher's Theorem 23 for `m = 91`.** If every `0 < n ≤ 695 · 2⁶⁰` reaches 1 (Bařina's
verification) and every nontrivial 91-cycle satisfies the Simons–de Weger ceiling
`K < 1.4784 · 91 · δ⁹¹`, then no nontrivial positive `T`-cycle has exactly 91 local minima. -/
theorem no_91_cycle (hX₀ : ∀ n, 0 < n → n ≤ 695 * 2 ^ 60 → Reaches T n 1)
    (hceil : ∀ x p, 0 < x → 0 < p → T^[p] x = x → x ≠ 1 → x ≠ 2 → numLocalMin x p = 91 →
      (oddCount T x p : ℝ) < 14784 / 10000 * 91 * Real.logb 2 3 ^ 91) :
    ∀ x p, 0 < x → 0 < p → T^[p] x = x → x ≠ 1 → x ≠ 2 → numLocalMin x p ≠ 91 := by
  intro x p hx hp hcyc hx1 hx2 h91
  have k7 := K_ge_of_91_cycle' hX₀ hx hp hcyc hx1 hx2 h91
  have hc := hceil x p hx hp hcyc hx1 hx2 h91
  have hδ : Real.logb 2 3 ≤ 8 / 5 := by
    have h : (deltaHi : ℝ) ≤ 8 / 5 := by
      have hq : deltaHi ≤ (8 : ℚ) / 5 := by decide +kernel
      have hR := (Rat.cast_le (K := ℝ)).mpr hq
      push_cast at hR
      exact hR
    exact le_trans logb_lt_deltaHi.le h
  have h0 : (0 : ℝ) ≤ Real.logb 2 3 := Real.logb_nonneg (by norm_num) (by norm_num)
  have h91' : Real.logb 2 3 ^ 91 ≤ (8 / 5 : ℝ) ^ 91 := pow_le_pow_left₀ h0 hδ 91
  have hB : (14784 / 10000 : ℝ) * 91 * (8 / 5) ^ 91 < 7941964418702608664581 := by norm_num
  have hm := mul_le_mul_of_nonneg_left h91' (by norm_num : (0 : ℝ) ≤ 14784 / 10000 * 91)
  have hKR : (oddCount T x p : ℝ) < 7941964418702608664581 := by linarith
  have hKN : oddCount T x p < 7941964418702608664581 := by exact_mod_cast hKR
  omega

end Collatz
