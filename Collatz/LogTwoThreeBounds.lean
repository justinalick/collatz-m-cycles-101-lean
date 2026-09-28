import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic

/-!
# A rational enclosure of `δ = log₂ 3` of width `10⁻⁵⁰`

Hercher's bootstrap (Theorem 23 of J. Integer Seq. 26 (2023), Art. 23.3.5) needs to know which
fractions lie in `(δ, δ + ε)` for `ε` as small as `1.2 · 10⁻⁴³`. This file proves

  `deltaLo < Real.logb 2 3 < deltaHi`,   `deltaHi − deltaLo = 10⁻⁵⁰`,

with `deltaLo = 1.58496250072115618145373894394781650875981440769248` and
`deltaHi = deltaLo + 10⁻⁵⁰` (`logb_two_three_bounds`, `deltaHi_sub_deltaLo`).

## Method

Mathlib's tail bound for the logarithm series,

  `|∑_{i<n} x^(i+1)/(i+1) + log (1 − x)| ≤ |x|^(n+1) / (1 − |x|)`   (`Real.abs_log_sub_add_sum_range_le`),

gives `log 2` from `x = 1/2` (`log (1 − 1/2) = −log 2`, remainder `≤ 2⁻ⁿ`) and `log 3 − log 2` from
`x = 1/3` (`log (1 − 1/3) = log 2 − log 3`, remainder `≤ 1/(2 · 3ⁿ)`). With `n = 175` and `n = 110` both
remainders are below `2.1 · 10⁻⁵³`. The partial sums are the computable rationals `logSum x n`
(`logSum_eq` identifies them with the `Finset` sums, `logSum_cast` with their real images), and the
two inequalities that pin `δ` down,

  `deltaLo · (S₂ + 2⁻¹⁷⁵) < S₂ + S₃ − 2⁻¹⁷⁵ − 1/(2 · 3¹¹⁰)`   and
  `S₂ + S₃ + 2⁻¹⁷⁵ + 1/(2 · 3¹¹⁰) < deltaHi · (S₂ − 2⁻¹⁷⁵)`,

are evaluated by the kernel over `ℚ` (`decide +kernel`; the rationals involved have about 130-digit
denominators, and the whole evaluation takes about a second). Since `log 2 ≤ S₂ + 2⁻¹⁷⁵` and
`log 3 ≥ S₂ + S₃ − 2⁻¹⁷⁵ − 1/(2 · 3¹¹⁰)`, the first inequality gives `deltaLo · log 2 < log 3`, i.e.
`deltaLo < log 3 / log 2 = logb 2 3`; the second gives the upper bound in the same way.

The constants were produced by `research/scripts/hercher_certificates.py`, which also cross-checks
the enclosure against a 90-digit evaluation of `log 3 / log 2`.
-/

namespace Collatz

open Finset

/-- `logSum x n = ∑_{i<n} x^(i+1)/(i+1)`, as a computable rational so that the kernel can
evaluate it. -/
def logSum (x : ℚ) : ℕ → ℚ
  | 0 => 0
  | n + 1 => logSum x n + x ^ (n + 1) / (n + 1)

theorem logSum_eq (x : ℚ) : ∀ n : ℕ, logSum x n = ∑ i ∈ range n, x ^ (i + 1) / ((i : ℚ) + 1)
  | 0 => by simp [logSum]
  | n + 1 => by simp only [logSum, sum_range_succ, logSum_eq x n]

theorem logSum_cast (x : ℚ) (n : ℕ) :
    ((logSum x n : ℚ) : ℝ) = ∑ i ∈ range n, (x : ℝ) ^ (i + 1) / ((i : ℝ) + 1) := by
  rw [logSum_eq]
  norm_cast

/-- `|log 2 − logSum (1/2) n| ≤ 2⁻ⁿ`, from Mathlib's tail bound with `x = 1/2`. -/
theorem abs_log_two_sub_logSum (n : ℕ) :
    |Real.log 2 - ((logSum (1 / 2) n : ℚ) : ℝ)| ≤ 1 / 2 ^ n := by
  have hpos : (0 : ℝ) < 1 / 2 := by norm_num
  have hx : |(1 / 2 : ℝ)| < 1 := by rw [abs_of_pos hpos]; norm_num
  have z := Real.abs_log_sub_add_sum_range_le hx n
  have hS : ((logSum (1 / 2) n : ℚ) : ℝ) =
      ∑ i ∈ range n, (1 / 2 : ℝ) ^ (i + 1) / ((i : ℝ) + 1) := by
    rw [logSum_cast]
    norm_num
  have h1 : Real.log (1 - 1 / 2 : ℝ) = -Real.log 2 := by
    rw [show (1 - 1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.log_inv]
  have h2 : |(1 / 2 : ℝ)| ^ (n + 1) / (1 - |(1 / 2 : ℝ)|) = 1 / 2 ^ n := by
    rw [abs_of_pos hpos, one_div_pow, div_div]
    congr 1
    ring
  rw [h1, h2] at z
  rw [hS]
  set S : ℝ := ∑ i ∈ range n, (1 / 2 : ℝ) ^ (i + 1) / ((i : ℝ) + 1) with hSdef
  have e : Real.log 2 - S = -(S + -Real.log 2) := by ring
  rw [e, abs_neg]
  exact z

/-- `|log 3 − log 2 − logSum (1/3) n| ≤ 1/(2 · 3ⁿ)`, from Mathlib's tail bound with `x = 1/3`. -/
theorem abs_log_three_sub_two_sub_logSum (n : ℕ) :
    |Real.log 3 - Real.log 2 - ((logSum (1 / 3) n : ℚ) : ℝ)| ≤ 1 / (2 * 3 ^ n) := by
  have hpos : (0 : ℝ) < 1 / 3 := by norm_num
  have hx : |(1 / 3 : ℝ)| < 1 := by rw [abs_of_pos hpos]; norm_num
  have z := Real.abs_log_sub_add_sum_range_le hx n
  have hS : ((logSum (1 / 3) n : ℚ) : ℝ) =
      ∑ i ∈ range n, (1 / 3 : ℝ) ^ (i + 1) / ((i : ℝ) + 1) := by
    rw [logSum_cast]
    norm_num
  have h1 : Real.log (1 - 1 / 3 : ℝ) = Real.log 2 - Real.log 3 := by
    rw [show (1 - 1 / 3 : ℝ) = 2 / 3 by norm_num, Real.log_div (by norm_num) (by norm_num)]
  have h2 : |(1 / 3 : ℝ)| ^ (n + 1) / (1 - |(1 / 3 : ℝ)|) = 1 / (2 * 3 ^ n) := by
    rw [abs_of_pos hpos, one_div_pow, div_div]
    congr 1
    ring
  rw [h1, h2] at z
  rw [hS]
  set S : ℝ := ∑ i ∈ range n, (1 / 3 : ℝ) ^ (i + 1) / ((i : ℝ) + 1) with hSdef
  have e : Real.log 3 - Real.log 2 - S = -(S + (Real.log 2 - Real.log 3)) := by ring
  rw [e, abs_neg]
  exact z

/-- `log 2` to within `2⁻¹⁷⁵` of `logSum (1/2) 175`. -/
theorem log_two_bounds :
    ((logSum (1 / 2) 175 : ℚ) : ℝ) - 1 / 2 ^ 175 ≤ Real.log 2 ∧
      Real.log 2 ≤ ((logSum (1 / 2) 175 : ℚ) : ℝ) + 1 / 2 ^ 175 := by
  have h := abs_log_two_sub_logSum 175
  rw [abs_le] at h
  constructor <;> linarith [h.1, h.2]

/-- `log 3` to within `2⁻¹⁷⁵ + 1/(2 · 3¹¹⁰)` of `logSum (1/2) 175 + logSum (1/3) 110`. -/
theorem log_three_bounds :
    ((logSum (1 / 2) 175 : ℚ) : ℝ) + ((logSum (1 / 3) 110 : ℚ) : ℝ) - 1 / 2 ^ 175 -
        1 / (2 * 3 ^ 110) ≤ Real.log 3 ∧
      Real.log 3 ≤ ((logSum (1 / 2) 175 : ℚ) : ℝ) + ((logSum (1 / 3) 110 : ℚ) : ℝ) + 1 / 2 ^ 175 +
        1 / (2 * 3 ^ 110) := by
  have h2 := log_two_bounds
  have h3 := abs_log_three_sub_two_sub_logSum 110
  rw [abs_le] at h3
  constructor <;> linarith [h2.1, h2.2, h3.1, h3.2]

/-- Lower end of the enclosure of `δ = log₂ 3`: `⌊10⁵⁰ · l₃/u₂⌋ / 10⁵⁰`, where `l₃ < log 3` and
`u₂ > log 2` are the series bounds above. -/
def deltaLo : ℚ := 158496250072115618145373894394781650875981440769248 / 10 ^ 50

/-- Upper end of the enclosure of `δ = log₂ 3`: `⌈10⁵⁰ · u₃/l₂⌉ / 10⁵⁰`. -/
def deltaHi : ℚ := 158496250072115618145373894394781650875981440769249 / 10 ^ 50

theorem deltaHi_sub_deltaLo : deltaHi - deltaLo = 1 / 10 ^ 50 := by decide +kernel

theorem deltaLo_nonneg : (0 : ℚ) ≤ deltaLo := by decide +kernel

theorem deltaHi_nonneg : (0 : ℚ) ≤ deltaHi := by decide +kernel

/-- Kernel evaluation over `ℚ`: `deltaLo · u₂ < l₃`. -/
theorem deltaLo_mul_lt :
    deltaLo * (logSum (1 / 2) 175 + 1 / 2 ^ 175) <
      logSum (1 / 2) 175 + logSum (1 / 3) 110 - 1 / 2 ^ 175 - 1 / (2 * 3 ^ 110) := by
  decide +kernel

/-- Kernel evaluation over `ℚ`: `u₃ < deltaHi · l₂`. -/
theorem lt_deltaHi_mul :
    logSum (1 / 2) 175 + logSum (1 / 3) 110 + 1 / 2 ^ 175 + 1 / (2 * 3 ^ 110) <
      deltaHi * (logSum (1 / 2) 175 - 1 / 2 ^ 175) := by
  decide +kernel

theorem deltaLo_lt_log_div_log : (deltaLo : ℝ) < Real.log 3 / Real.log 2 := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [lt_div_iff₀ hlog]
  have hu2 := log_two_bounds.2
  have hl3 := log_three_bounds.1
  have hkey : ((deltaLo * (logSum (1 / 2) 175 + 1 / 2 ^ 175) : ℚ) : ℝ) <
      ((logSum (1 / 2) 175 + logSum (1 / 3) 110 - 1 / 2 ^ 175 - 1 / (2 * 3 ^ 110) : ℚ) : ℝ) := by
    exact_mod_cast deltaLo_mul_lt
  push_cast at hkey
  have hnn : (0 : ℝ) ≤ (deltaLo : ℝ) := by exact_mod_cast deltaLo_nonneg
  have hm := mul_le_mul_of_nonneg_left hu2 hnn
  linarith

theorem log_div_log_lt_deltaHi : Real.log 3 / Real.log 2 < (deltaHi : ℝ) := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [div_lt_iff₀ hlog]
  have hl2 := log_two_bounds.1
  have hu3 := log_three_bounds.2
  have hkey : ((logSum (1 / 2) 175 + logSum (1 / 3) 110 + 1 / 2 ^ 175 + 1 / (2 * 3 ^ 110) : ℚ) : ℝ) <
      ((deltaHi * (logSum (1 / 2) 175 - 1 / 2 ^ 175) : ℚ) : ℝ) := by
    exact_mod_cast lt_deltaHi_mul
  push_cast at hkey
  have hnn : (0 : ℝ) ≤ (deltaHi : ℝ) := by exact_mod_cast deltaHi_nonneg
  have hm := mul_le_mul_of_nonneg_left hl2 hnn
  linarith

/-- `deltaLo < log₂ 3`. -/
theorem deltaLo_lt_logb : (deltaLo : ℝ) < Real.logb 2 3 := by
  rw [← Real.log_div_log]
  exact deltaLo_lt_log_div_log

/-- `log₂ 3 < deltaHi`. -/
theorem logb_lt_deltaHi : Real.logb 2 3 < (deltaHi : ℝ) := by
  rw [← Real.log_div_log]
  exact log_div_log_lt_deltaHi

/-- **The enclosure**: `deltaLo < log₂ 3 < deltaHi` with `deltaHi − deltaLo = 10⁻⁵⁰`. -/
theorem logb_two_three_bounds : (deltaLo : ℝ) < Real.logb 2 3 ∧ Real.logb 2 3 < (deltaHi : ℝ) :=
  ⟨deltaLo_lt_logb, logb_lt_deltaHi⟩

end Collatz
