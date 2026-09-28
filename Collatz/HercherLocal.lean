import Collatz.SharpCycleBound
import Collatz.InverseTree
import Collatz.Cycles
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Hercher's local lemmas: Remark 7, Lemma 8, Lemma 9, Lemma 20

C. Hercher, *There are no Collatz m-cycles with m ≤ 91*, J. Integer Seq. 26 (2023), Art. 23.3.5,
Section 2. Hercher's map `C` is the repository's `T`. A *rise* of length `k` at `n` is a run of `k`
odd iterates `n, T n, …, T^{k-1} n`; `riseSum n k = ∑_{t<k} 1/T^t n` is Hercher's `T(nᵢ)` when `n`
is a local minimum and `k` its exact number of odd steps.

* `odd_run_form` (Lemma 8 with its proof): a rise of length `k` at `n` means `n + 1 = 2^k a` with
  `a ≥ 1`, and then `T^k n = 3^k a − 1`; `two_pow_dvd_of_odd_run`, `two_pow_le_of_odd_run`.
* `riseSum_le`, `riseSum_lt` (Remark 7): `riseSum n k ≤ 3 (1 − (2/3)^k)/n < 3/n`.
* `merge_of_two_even` (Lemma 9): if the rise of length `k ≥ 1` is followed by two even steps, then
  `T^{k+2} n = T^{k+1} ((n − 1)/2)`; `two_mul_lt_of_two_even` turns this into `2 X₀ < n` for an
  element of a nontrivial cycle when every `0 < n ≤ X₀` reaches 1.
* `succ_iterate_lt_rpow` (Lemma 20, `x = log₂(n+1)` form, as used in Theorem 21):
  `T^{k+1} n + 1 < (n + 1)^δ`, `δ = log₂ 3`; `iterate_lt_rpow` (Lemma 20 as stated):
  `T^{k+1} n < n^δ` for `n ≥ 3`. The next local minimum is at most `T^{k+1} n`
  (`iterate_le_of_even_run`).
-/

namespace Collatz

open Finset

/-- **Lemma 8 (with its proof).** A run of `k` odd iterates at `n` means `n + 1 = 2^k a` for some
`a ≥ 1`, and then `T^k n = 3^k a − 1`. -/
theorem odd_run_form : ∀ (k n : ℕ), (∀ t < k, T^[t] n % 2 = 1) →
    ∃ a, 1 ≤ a ∧ n + 1 = 2 ^ k * a ∧ T^[k] n = 3 ^ k * a - 1
  | 0, n, _ => ⟨n + 1, by omega, by simp, by simp⟩
  | k + 1, n, h => by
    obtain ⟨a, ha, hn, hk⟩ := odd_run_form k n (fun t ht => h t (by omega))
    have hodd : T^[k] n % 2 = 1 := h k (by omega)
    rw [hk] at hodd
    have h3 : 3 ^ k % 2 = 1 := by rw [Nat.pow_mod]; norm_num
    have heven : a % 2 = 0 := by
      have hm : (3 ^ k * a) % 2 = (3 ^ k % 2) * (a % 2) % 2 := Nat.mul_mod _ _ _
      rw [h3, one_mul, Nat.mod_mod] at hm
      have hpos : 1 ≤ 3 ^ k * a := Nat.mul_pos (pow_pos (by norm_num) k) ha
      omega
    obtain ⟨b, rfl⟩ : ∃ b, a = 2 * b := ⟨a / 2, by omega⟩
    have hb : 1 ≤ b := by omega
    have hn' : n = 2 ^ (k + 1) * b - 1 := by
      have : 2 ^ k * (2 * b) = 2 ^ (k + 1) * b := by ring
      omega
    refine ⟨b, hb, ?_, ?_⟩
    · have : 2 ^ k * (2 * b) = 2 ^ (k + 1) * b := by ring
      omega
    · rw [hn', barina_identity (k + 1) hb]

theorem two_pow_dvd_of_odd_run {k n : ℕ} (h : ∀ t < k, T^[t] n % 2 = 1) : 2 ^ k ∣ n + 1 := by
  obtain ⟨a, _, hn, _⟩ := odd_run_form k n h
  exact ⟨a, hn⟩

/-- Lemma 8, "in particular": `n ≥ 2^k − 1`. -/
theorem two_pow_le_of_odd_run {k n : ℕ} (h : ∀ t < k, T^[t] n % 2 = 1) : 2 ^ k ≤ n + 1 := by
  obtain ⟨a, ha, hn, _⟩ := odd_run_form k n h
  rw [hn]
  exact Nat.le_mul_of_pos_right _ ha

/-! ### Remark 7 -/

/-- Hercher's `T(n)` for a rise of length `k` at `n`: `∑_{t<k} 1/T^t n`. -/
noncomputable def riseSum (n k : ℕ) : ℝ := ∑ t ∈ range k, 1 / ((T^[t] n : ℕ) : ℝ)

/-- Along a rise the iterates grow at least by the factor `3/2`. -/
theorem iterate_ge_of_odd_run {k n : ℕ} (h : ∀ t < k, T^[t] n % 2 = 1) :
    ∀ t ≤ k, (3 / 2 : ℝ) ^ t * (n : ℝ) ≤ ((T^[t] n : ℕ) : ℝ) := by
  intro t
  induction t with
  | zero => intro _; simp
  | succ t ih =>
    intro ht
    have h1 := ih (by omega)
    have hodd := h t (by omega)
    rw [Function.iterate_succ_apply', T_cast_odd hodd, pow_succ]
    have hy : (0 : ℝ) ≤ ((T^[t] n : ℕ) : ℝ) := Nat.cast_nonneg _
    nlinarith

/-- **Remark 7**, quantitative form: `T(n) ≤ 3 (1 − (2/3)^k)/n`. -/
theorem riseSum_le {k n : ℕ} (hn : 0 < n) (h : ∀ t < k, T^[t] n % 2 = 1) :
    riseSum n k ≤ 3 * (1 - (2 / 3 : ℝ) ^ k) / n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hge := iterate_ge_of_odd_run h
  have key : ∀ j ≤ k, riseSum n j ≤ 3 * (1 - (2 / 3 : ℝ) ^ j) / n := by
    intro j
    induction j with
    | zero => intro _; simp [riseSum]
    | succ j ih =>
      intro hj
      have h1 := ih (by omega)
      have h2 := hge j (by omega)
      have hpos : (0 : ℝ) < (3 / 2 : ℝ) ^ j * (n : ℝ) := by positivity
      have h3 : 1 / ((T^[j] n : ℕ) : ℝ) ≤ 1 / ((3 / 2 : ℝ) ^ j * (n : ℝ)) :=
        one_div_le_one_div_of_le hpos h2
      have h4 : 1 / ((3 / 2 : ℝ) ^ j * (n : ℝ)) = (2 / 3 : ℝ) ^ j / n := by
        rw [show (2 / 3 : ℝ) = (3 / 2)⁻¹ by norm_num, inv_pow, one_div, mul_inv]
        ring
      have hsplit : riseSum n (j + 1) = riseSum n j + 1 / ((T^[j] n : ℕ) : ℝ) := by
        simp [riseSum, sum_range_succ]
      rw [hsplit]
      have h5 : 3 * (1 - (2 / 3 : ℝ) ^ j) / n + (2 / 3 : ℝ) ^ j / n =
          3 * (1 - (2 / 3 : ℝ) ^ (j + 1)) / n := by
        ring
      linarith
  exact key k le_rfl

/-- **Remark 7.** `T(n) < 3/n`. -/
theorem riseSum_lt {k n : ℕ} (hn : 0 < n) (h : ∀ t < k, T^[t] n % 2 = 1) :
    riseSum n k < 3 / n := by
  have h1 := riseSum_le hn h
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hp : (0 : ℝ) < (2 / 3 : ℝ) ^ k := by positivity
  have h2 : 3 * (1 - (2 / 3 : ℝ) ^ k) / n = 3 / n - 3 * (2 / 3 : ℝ) ^ k / n := by ring
  have h3 : (0 : ℝ) < 3 * (2 / 3 : ℝ) ^ k / n := by positivity
  linarith

/-! ### Lemma 9 -/

/-- **Lemma 9.** If the rise of length `k ≥ 1` at `n` is followed by (at least) two even steps,
the orbits of `n` and `(n − 1)/2` merge: `T^{k+2} n = T^{k+1} ((n − 1)/2)`. -/
theorem merge_of_two_even {k n : ℕ} (hk : 1 ≤ k) (h : ∀ t < k, T^[t] n % 2 = 1)
    (he1 : T^[k] n % 2 = 0) (he2 : T^[k + 1] n % 2 = 0) :
    T^[k + 2] n = T^[k + 1] ((n - 1) / 2) := by
  obtain ⟨a, ha, hn, hk'⟩ := odd_run_form k n h
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hX : 2 ^ (j + 1) * a = 2 * (2 ^ j * a) := by ring
  have hXpos : 1 ≤ 2 ^ j * a := Nat.mul_pos (Nat.two_pow_pos j) ha
  have hn' : (n - 1) / 2 = 2 ^ j * a - 1 := by omega
  have hM : 3 ^ (j + 1) * a = 3 * (3 ^ j * a) := by ring
  have hMpos : 1 ≤ 3 ^ j * a := Nat.mul_pos (pow_pos (by norm_num) j) ha
  have hk2 : T^[j + 1] n = 3 * (3 ^ j * a) - 1 := by rw [hk', hM]
  have hj : T^[j] ((n - 1) / 2) = 3 ^ j * a - 1 := by rw [hn', barina_identity j ha]
  generalize 3 ^ j * a = M at hk2 hj hMpos
  have he1' : (3 * M - 1) % 2 = 0 := by rw [← hk2]; exact he1
  have hstep1 : T^[j + 1 + 1] n = (3 * M - 1) / 2 := by
    rw [Function.iterate_succ_apply', hk2, T_even he1']
  have he2' : ((3 * M - 1) / 2) % 2 = 0 := by rw [← hstep1]; exact he2
  have hL : T^[j + 1 + 2] n = ((3 * M - 1) / 2) / 2 := by
    rw [show j + 1 + 2 = (j + 1 + 1) + 1 by omega, Function.iterate_succ_apply', hstep1,
      T_even he2']
  have hme : (M - 1) % 2 = 0 := by omega
  have hmo : ((M - 1) / 2) % 2 = 1 := by omega
  have hR : T^[j + 1 + 1] ((n - 1) / 2) = (3 * ((M - 1) / 2) + 1) / 2 := by
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hj, T_even hme, T_odd hmo]
  rw [hL, hR]
  omega

theorem reaches_one_iterate {y : ℕ} (h : Reaches T y 1) (s : ℕ) : Reaches T (T^[s] y) 1 := by
  obtain ⟨j, hj⟩ := h
  rcases le_or_gt s j with hsj | hsj
  · refine ⟨j - s, ?_⟩
    rw [← Function.iterate_add_apply, Nat.sub_add_cancel hsj, hj]
  · have e : T^[s] y = T^[s - j] 1 := by
      rw [← hj, ← Function.iterate_add_apply, Nat.sub_add_cancel hsj.le]
    rw [e]
    rcases iterate_T_one (s - j) with h1 | h1
    · exact ⟨0, h1⟩
    · exact ⟨1, by rw [Function.iterate_one, h1]; decide⟩

theorem reaches_one_of_iterate {y s : ℕ} (h : Reaches T (T^[s] y) 1) : Reaches T y 1 := by
  obtain ⟨j, hj⟩ := h
  exact ⟨j + s, by rw [Function.iterate_add_apply, hj]⟩

/-- **Lemma 9, consequence.** On a nontrivial positive cycle, when every `0 < n ≤ X₀` reaches 1,
an element whose rise of length `k ≥ 1` is followed by two even steps exceeds `2 X₀`. -/
theorem two_mul_lt_of_two_even {x p X₀ i k : ℕ} (hp : 0 < p) (hcyc : T^[p] x = x)
    (hx1 : x ≠ 1) (hx2 : x ≠ 2)
    (hX₀ : ∀ n, 0 < n → n ≤ X₀ → Reaches T n 1)
    (hk : 1 ≤ k) (h : ∀ t < k, T^[t] (T^[i] x) % 2 = 1)
    (he1 : T^[k] (T^[i] x) % 2 = 0) (he2 : T^[k + 1] (T^[i] x) % 2 = 0) :
    2 * X₀ < T^[i] x := by
  have hnr := cycle_not_reaches_one hp hcyc hx1 hx2 i
  by_contra hle
  push_neg at hle
  set n := T^[i] x with hn
  rcases Nat.lt_or_ge ((n - 1) / 2) 1 with h0 | h0
  · -- `n ≤ 2`; `n` is odd, so `n = 1`
    have hodd : n % 2 = 1 := by simpa using h 0 (by omega)
    have h1 : n = 1 := by omega
    exact hnr ⟨0, h1⟩
  · have hr := hX₀ ((n - 1) / 2) (by omega) (by omega)
    have hr2 := reaches_one_iterate hr (k + 1)
    rw [← merge_of_two_even hk h he1 he2] at hr2
    exact hnr (reaches_one_of_iterate hr2)

/-! ### Lemma 20 -/

/-- After the rise, the even steps only decrease: `T^{k+ℓ} n ≤ T^{k+1} n` for `ℓ ≥ 1` when
`T^k n, …, T^{k+ℓ−1} n` are even. -/
theorem iterate_le_of_even_run {n k ℓ : ℕ} (hℓ : 1 ≤ ℓ)
    (h : ∀ s < ℓ, T^[k + s] n % 2 = 0) : T^[k + ℓ] n ≤ T^[k + 1] n := by
  induction ℓ with
  | zero => omega
  | succ ℓ ih =>
    rcases Nat.eq_zero_or_pos ℓ with h0 | hpos
    · subst h0; simp
    · have h1 := ih hpos (fun s hs => h s (by omega))
      have he := h ℓ (by omega)
      rw [show k + (ℓ + 1) = (k + ℓ) + 1 by omega, Function.iterate_succ_apply' T (k + ℓ) n,
        T_even he]
      omega

theorem two_rpow_logb_three : (2 : ℝ) ^ Real.logb 2 3 = 3 :=
  Real.rpow_logb (by norm_num) (by norm_num) (by norm_num)

theorem one_le_logb_two_three : 1 ≤ Real.logb 2 3 := by
  rw [Real.le_logb_iff_rpow_le (by norm_num) (by norm_num)]
  norm_num

theorem logb_two_three_lt_two : Real.logb 2 3 < 2 := by
  rw [Real.logb_lt_iff_lt_rpow (by norm_num) (by norm_num), Real.rpow_two]
  norm_num

/-- `(2^k)^δ = 3^k`. -/
theorem two_pow_rpow_logb (k : ℕ) : ((2 : ℝ) ^ k) ^ Real.logb 2 3 = 3 ^ k := by
  calc ((2 : ℝ) ^ k) ^ Real.logb 2 3 = ((2 : ℝ) ^ (k : ℝ)) ^ Real.logb 2 3 := by
        rw [Real.rpow_natCast]
    _ = (2 : ℝ) ^ ((k : ℝ) * Real.logb 2 3) := by rw [← Real.rpow_mul (by norm_num)]
    _ = ((2 : ℝ) ^ Real.logb 2 3) ^ (k : ℝ) := by
        rw [mul_comm, Real.rpow_mul (by norm_num)]
    _ = 3 ^ k := by rw [two_rpow_logb_three, Real.rpow_natCast]

/-- `3^k a ≤ (2^k a)^δ` for `a ≥ 1`. -/
theorem three_pow_mul_le_rpow (k a : ℕ) (ha : 1 ≤ a) :
    (3 : ℝ) ^ k * a ≤ ((2 : ℝ) ^ k * a) ^ Real.logb 2 3 := by
  have ha' : (1 : ℝ) ≤ a := by exact_mod_cast ha
  rw [Real.mul_rpow (by positivity) (by positivity), two_pow_rpow_logb]
  have h := Real.self_le_rpow_of_one_le ha' one_le_logb_two_three
  have h3 : (0 : ℝ) ≤ 3 ^ k := by positivity
  exact mul_le_mul_of_nonneg_left h h3

/-- **Lemma 20, `log₂(n + 1)` form.** After a rise of length `k ≥ 1` at `n` ending in an even
number, `T^{k+1} n + 1 < (n + 1)^δ`. -/
theorem succ_iterate_lt_rpow {k n : ℕ} (hk : 1 ≤ k) (h : ∀ t < k, T^[t] n % 2 = 1)
    (he : T^[k] n % 2 = 0) :
    ((T^[k + 1] n : ℕ) : ℝ) + 1 < ((n : ℝ) + 1) ^ Real.logb 2 3 := by
  obtain ⟨a, ha, hn, hk'⟩ := odd_run_form k n h
  have h3 : 3 ≤ 3 ^ k * a := by
    have : 3 ≤ 3 ^ k := by
      calc 3 = 3 ^ 1 := by norm_num
        _ ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    exact le_trans this (Nat.le_mul_of_pos_right _ ha)
  have hstep : T^[k + 1] n = (3 ^ k * a - 1) / 2 := by
    rw [Function.iterate_succ_apply', T_even he, hk']
  have hnat : T^[k + 1] n + 1 < 3 ^ k * a := by rw [hstep]; omega
  have hreal : ((T^[k + 1] n : ℕ) : ℝ) + 1 < (3 : ℝ) ^ k * a := by exact_mod_cast hnat
  have hn' : (n : ℝ) + 1 = (2 : ℝ) ^ k * a := by exact_mod_cast hn
  rw [hn']
  exact lt_of_lt_of_le hreal (three_pow_mul_le_rpow k a ha)

/-- **Lemma 20.** After a rise of length `k` at `n ≥ 3` ending in an even number,
`T^{k+1} n < n^δ`; the next local minimum is at most `T^{k+1} n` (`iterate_le_of_even_run`). -/
theorem iterate_lt_rpow {k n : ℕ} (hn3 : 3 ≤ n) (h : ∀ t < k, T^[t] n % 2 = 1)
    (he : T^[k] n % 2 = 0) :
    ((T^[k + 1] n : ℕ) : ℝ) < (n : ℝ) ^ Real.logb 2 3 := by
  obtain ⟨a, ha, hn, hk'⟩ := odd_run_form k n h
  have hstep : T^[k + 1] n = (3 ^ k * a - 1) / 2 := by
    rw [Function.iterate_succ_apply', T_even he, hk']
  have hnat : 2 * T^[k + 1] n < 3 ^ k * a := by
    rw [hstep]
    have : 1 ≤ 3 ^ k * a := Nat.mul_pos (pow_pos (by norm_num) k) ha
    omega
  have hreal : 2 * ((T^[k + 1] n : ℕ) : ℝ) < (3 : ℝ) ^ k * a := by exact_mod_cast hnat
  have hn' : (n : ℝ) + 1 = (2 : ℝ) ^ k * a := by exact_mod_cast hn
  have h1 : (3 : ℝ) ^ k * a ≤ ((n : ℝ) + 1) ^ Real.logb 2 3 := by
    rw [hn']; exact three_pow_mul_le_rpow k a ha
  -- `(n + 1)^δ ≤ (4/3)^δ n^δ ≤ (4/3)^2 n^δ < 2 n^δ`
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn3
  have hnpos : (0 : ℝ) < n := by linarith
  have h2 : (n : ℝ) + 1 ≤ (4 / 3 : ℝ) * n := by linarith
  have h3 : ((n : ℝ) + 1) ^ Real.logb 2 3 ≤ ((4 / 3 : ℝ) * n) ^ Real.logb 2 3 :=
    Real.rpow_le_rpow (by positivity) h2 (by linarith [one_le_logb_two_three])
  have h4 : ((4 / 3 : ℝ) * n) ^ Real.logb 2 3 =
      (4 / 3 : ℝ) ^ Real.logb 2 3 * (n : ℝ) ^ Real.logb 2 3 :=
    Real.mul_rpow (by norm_num) hnpos.le
  have h5 : (4 / 3 : ℝ) ^ Real.logb 2 3 ≤ (4 / 3 : ℝ) ^ (2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) logb_two_three_lt_two.le
  have h6 : (4 / 3 : ℝ) ^ (2 : ℝ) = 16 / 9 := by rw [Real.rpow_two]; norm_num
  have hpow : (0 : ℝ) < (n : ℝ) ^ Real.logb 2 3 := Real.rpow_pos_of_pos hnpos _
  have h7 : (4 / 3 : ℝ) ^ Real.logb 2 3 * (n : ℝ) ^ Real.logb 2 3 ≤
      16 / 9 * (n : ℝ) ^ Real.logb 2 3 := by
    rw [← h6]; exact mul_le_mul_of_nonneg_right h5 hpow.le
  linarith

end Collatz
