import Collatz.HercherNo91

/-!
# The ceiling from Rhin's transcendence measure (Simons–de Weger, Lemmas 7, 12, 14)

`no_91_cycle` (`HercherNo91.lean`) takes the Simons–de Weger ceiling `K < 1.4784 · 91 · δ⁹¹` as a
hypothesis; that ceiling is their Lemma 16, which rests on Rhin's transcendence measure *and* on
their computation of the continued fraction of `δ` (the champion table). This file replaces it by
the transcendence measure alone, in the form of their Lemma 12 (`RhinBound`):

  `Λ = p log 2 − K log 3 > exp(−13.3 (0.46057 + log K))`

for every nontrivial positive cycle (Rhin's proposition with `H = K + L`, and their Lemma 8 for
`log H ≤ 0.46057 + log K`). No part of this is proved here; it is the one input from
transcendence theory.

The other half of their Lemma 14 argument is their Lemma 7, `Λ < m c 2^{−(δ−1) K/(δ^m − 1)}`,
which is Theorem 21 (vertex-free) with `m₂ = m`: every minimum satisfies `n ≥ 2^v − 1` with
`v = K/G_m`, so `Λ < m/(2^v − 1)` (`theorem21_vertexFree`). For `m = 91` and
`K ≥ K₇ = 7 941 964 418 702 608 664 581` one has `v ≥ 2000`, and then
`exp(−13.3 (0.46057 + log K)) < 182 · 2^{−v}` is impossible, since `log K = log v + log G_91`,
`G_91 ≤ 2⁶²` and `log v ≤ 12 log 2 + v/4096 − 1` (tangent line of `log` at `4096 = 2¹²`)
(`K_lt_of_rhin`). With `K_ge_of_91_cycle'` this gives `no_91_cycle_of_rhin`: **no nontrivial
positive `T`-cycle has 91 local minima**, from the verification bound `X₀ = 695 · 2⁶⁰` and
`RhinBound`.
-/

namespace Collatz

open Finset

/-- Simons and de Weger, Lemma 12 (from Rhin's transcendence measure for `log 3/log 2` and their
Lemma 8): for every nontrivial positive cycle with `K ≥ 1` odd elements,
`p log 2 − K log 3 > exp(−13.3 (0.46057 + log K))`. A hypothesis, not proved here. -/
def RhinBound : Prop :=
  ∀ x p : ℕ, 0 < x → 0 < p → T^[p] x = x → x ≠ 1 → x ≠ 2 → 1 ≤ oddCount T x p →
    Real.exp (-(133 / 10 * (46057 / 100000 + Real.log (oddCount T x p)))) <
      (p : ℝ) * Real.log 2 - (oddCount T x p : ℝ) * Real.log 3

/-- **The Lemma 14 ceiling for `m = 91`.** Under `RhinBound`, a nontrivial cycle with 91 local
minima has `K < 7 941 964 418 702 608 664 581`. -/
theorem K_lt_of_rhin (hR : RhinBound) {x p : ℕ} (hx : 0 < x) (hp : 0 < p) (hcyc : T^[p] x = x)
    (hx1 : x ≠ 1) (hx2 : x ≠ 2) (h91 : numLocalMin x p = 91) :
    oddCount T x p < 7941964418702608664581 := by
  by_contra hge
  push_neg at hge
  have hK1 : 1 ≤ oddCount T x p := by omega
  have hrh := hR x p hx hp hcyc hx1 hx2 hK1
  -- Lemma 7: Theorem 21 (vertex-free) with `m₂ = m = 91`
  have h21 := theorem21_vertexFree hx hp hcyc (m₂ := 91) (by norm_num) (by omega)
    (X₀ := 1) one_pos (fun j => by exact_mod_cast Nat.succ_le_of_lt (iterate_T_pos hx j))
  rw [h91] at h21
  obtain ⟨v, hv⟩ : ∃ v, v = windowExp 91 91 (oddCount T x p) := ⟨_, rfl⟩
  rw [← hv] at h21
  set Λ := (p : ℝ) * Real.log 2 - (oddCount T x p : ℝ) * Real.log 3 with hΛ
  have z : ((91 - 91 : ℕ) : ℝ) = 0 := by norm_num
  have e : 3 * ((91 : ℕ) : ℝ) / ((2 : ℝ) ^ v - 1) = 3 * (91 / ((2 : ℝ) ^ v - 1)) := by
    push_cast; ring
  have hΛlt : Λ < 91 / ((2 : ℝ) ^ v - 1) := by
    rw [z] at h21
    linarith
  -- `G = G_91` and `v = K/G ≥ 2000`
  obtain ⟨G, hG⟩ : ∃ G, G = ∑ d ∈ range 91, Real.logb 2 3 ^ d := ⟨_, rfl⟩
  have hGpos : 0 < G := by rw [hG]; exact geomSum_delta_pos (by norm_num)
  have hδ0 : (0 : ℝ) ≤ Real.logb 2 3 := by linarith [one_le_logb_two_three]
  have hGhi : G ≤ ((geomQ deltaUp 91 : ℚ) : ℝ) := by
    rw [hG, geomQ_eq]
    push_cast
    exact sum_le_sum (fun d _ => pow_le_pow_left₀ hδ0 logb_le_deltaUp d)
  have hKR : (7941964418702608664581 : ℝ) ≤ oddCount T x p := by exact_mod_cast hge
  have hq1 : ((2000 * geomQ deltaUp 91 : ℚ) : ℝ) ≤ ((7941964418702608664581 : ℚ) : ℝ) := by
    have : 2000 * geomQ deltaUp 91 ≤ (7941964418702608664581 : ℚ) := by decide +kernel
    exact_mod_cast this
  have hq2 : ((geomQ deltaUp 91 : ℚ) : ℝ) ≤ ((2 ^ 62 : ℚ) : ℝ) := by
    have : geomQ deltaUp 91 ≤ (2 ^ 62 : ℚ) := by decide +kernel
    exact_mod_cast this
  push_cast at hq1 hq2
  have hvK : v * G = oddCount T x p := by
    rw [hv, windowExp, ← hG, div_mul_eq_mul_div,
      div_eq_iff (mul_pos (by norm_num) hGpos).ne']
    ring
  have hv2000 : 2000 ≤ v := by
    have h1 : 2000 * G ≤ v * G := by
      rw [hvK]
      have := mul_le_mul_of_nonneg_left hGhi (by norm_num : (0 : ℝ) ≤ 2000)
      linarith
    exact le_of_mul_le_mul_right h1 hGpos
  -- `2^v − 1 ≥ 2^v/2`, so `Λ < 182 · exp(−v log 2)`
  have h2v : (2 : ℝ) ^ v = Real.exp (Real.log 2 * v) := Real.rpow_def_of_pos (by norm_num) v
  have h2v2 : (2 : ℝ) ≤ (2 : ℝ) ^ v := by
    have := Real.rpow_le_rpow_of_exponent_le (x := (2 : ℝ)) (by norm_num)
      (show (1 : ℝ) ≤ v by linarith)
    rwa [Real.rpow_one] at this
  have hΛ2 : Λ < 182 / (2 : ℝ) ^ v := by
    have h1 : 91 / ((2 : ℝ) ^ v - 1) ≤ 182 / (2 : ℝ) ^ v := by
      rw [div_le_div_iff₀ (by linarith) (by linarith)]
      linarith
    linarith
  -- take logarithms
  have hexp : Real.exp (-(133 / 10 * (46057 / 100000 + Real.log (oddCount T x p))) +
      Real.log 2 * v) < 182 := by
    rw [Real.exp_add, ← h2v]
    have h2pos : (0 : ℝ) < (2 : ℝ) ^ v := by linarith
    have := lt_trans hrh hΛ2
    rwa [lt_div_iff₀ h2pos] at this
  have hlog := (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 182)).mpr hexp
  -- the estimates for the logarithms
  have hl2 : (6931471803 / 10 ^ 10 : ℝ) < Real.log 2 := log_two_gt'
  have hl2' : Real.log 2 < 6931471808 / 10 ^ 10 := by
    have h := Real.log_two_lt_d9
    have e : (0.6931471808 : ℝ) = 6931471808 / 10 ^ 10 := by norm_num
    linarith
  have h182 : Real.log 182 ≤ 8 * Real.log 2 := by
    have : Real.log 182 ≤ Real.log ((2 : ℝ) ^ 8) := Real.log_le_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at this
    push_cast at this
    linarith
  have hvpos : 0 < v := by linarith
  have hlogK : Real.log (oddCount T x p) = Real.log v + Real.log G := by
    rw [← hvK, Real.log_mul hvpos.ne' hGpos.ne']
  have hlogG : Real.log G ≤ 62 * Real.log 2 := by
    have : Real.log G ≤ Real.log ((2 : ℝ) ^ 62) := Real.log_le_log hGpos (by linarith)
    rw [Real.log_pow] at this
    push_cast at this
    linarith
  have hlogv : Real.log v ≤ 12 * Real.log 2 + v / 4096 - 1 := by
    have h1 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < v / 4096 by positivity)
    rw [Real.log_div hvpos.ne' (by norm_num)] at h1
    have h4096 : Real.log (4096 : ℝ) = 12 * Real.log 2 := by
      rw [show (4096 : ℝ) = 2 ^ 12 by norm_num, Real.log_pow]; norm_num
    linarith
  have hvl : 6931471803 / 10 ^ 10 * v ≤ Real.log 2 * v := by
    have := mul_le_mul_of_nonneg_right hl2.le hvpos.le
    linarith
  rw [hlogK] at hlog
  linarith

/-- **Hercher's Theorem 23 for `m = 91`, from the verification bound and Rhin's measure.** If
every `0 < n ≤ 695 · 2⁶⁰` reaches 1 and `RhinBound` holds, no nontrivial positive `T`-cycle has
exactly 91 local minima. -/
theorem no_91_cycle_of_rhin (hX₀ : ∀ n, 0 < n → n ≤ 695 * 2 ^ 60 → Reaches T n 1)
    (hR : RhinBound) :
    ∀ x p, 0 < x → 0 < p → T^[p] x = x → x ≠ 1 → x ≠ 2 → numLocalMin x p ≠ 91 := by
  intro x p hx hp hcyc hx1 hx2 h91
  have h1 := K_ge_of_91_cycle' hX₀ hx hp hcyc hx1 hx2 h91
  have h2 := K_lt_of_rhin hR hx hp hcyc hx1 hx2 h91
  omega

end Collatz
