import Collatz.HercherAll
import Collatz.TwoRiseCheck

/-!
# The two-rise bound, two consecutive steps of the chain of minima, the least element

Ingredients of Theorem 8 of `research_notes/Collatz disproof routes/m92_obstruction.md` (the
chain bound that excludes `m`-cycles for `92 ≤ m ≤ 101` at `X₀ = 2⁷¹`):

* `TwoRiseBound N B`: the first two rises from an odd `n < 2^N` have total length at most `B`
  (`orun n + orun (nextMin n) ≤ B`); `twoRiseBound_of_allPairs` derives it from the kernel-checked
  arithmetic statement `TwoRise.AllPairs N B` (`TwoRiseCheck.lean`, Proposition B′ of the note);
* `block_eq`: the block of a local minimum, `n + 1 = 2^k a` (`a` odd), `3^k a = 2^ℓ n' + 1`
  (Lemma 8 of Hercher and the proof of Lemma 1 of the note);
* `logb_two_step` (Lemma 1 twice): for `x = log₂(n + 1)` and the second next minimum `n''`,
  `x'' ≤ x + (δ − 1)(k + k') − 2 + 6/(n + 1)`, from the integer inequality
  `4 · 2^{k+k'} (n'' + 1) ≤ 3^{k+k'} (n + 4)` (`TwoRise.two_step_core`);
* `exists_least_rotation`: the least element of a cycle is a local minimum;
* `lambda_lt_two`: Theorem 21 (two-element form) with the rational side conditions, for an
  arbitrary real lower bound `X₀` of the cycle elements (used with `X₀` the least element).
-/

namespace Collatz

open Finset

/-- **The two-rise bound below `2^N`**: the first two rises of every odd `n < 2^N` have total
length at most `B`. -/
def TwoRiseBound (N B : ℕ) : Prop :=
  ∀ n, n % 2 = 1 → n < 2 ^ N → orun n + orun (nextMin n) ≤ B

/-- The block of a local minimum `n` (odd): `n + 1 = 2^k a` with `a` odd, and
`3^k a = 2^ℓ n' + 1`, where `k = orun n`, `ℓ = erun n`, `n' = nextMin n`. -/
theorem block_eq {n : ℕ} (hn : n % 2 = 1) :
    ∃ a, a % 2 = 1 ∧ n + 1 = 2 ^ orun n * a ∧ 3 ^ orun n * a = 2 ^ erun n * nextMin n + 1 := by
  have hn0 : 0 < n := by omega
  obtain ⟨a, ha, hna, hk⟩ := odd_run_form (orun n) n (fun t ht => odd_of_lt_orun ht)
  have hrun := iterate_even_run (n := n) (k := orun n) (erun n)
    (fun s hs => even_of_lt_erun hn0 hs)
  have hnm : T^[orun n + erun n] n = nextMin n := rfl
  rw [hnm, hk] at hrun
  have hev : T^[orun n] n % 2 = 0 := orun_spec n
  rw [hk] at hev
  have h3pos : 1 ≤ 3 ^ orun n * a := Nat.mul_pos (by positivity) ha
  have hodd : (3 ^ orun n * a) % 2 = 1 := by omega
  refine ⟨a, ?_, hna, by omega⟩
  rcases Nat.mod_two_eq_zero_or_one a with h | h
  · exfalso
    have hd : 2 ∣ 3 ^ orun n * a := Dvd.dvd.mul_left (Nat.dvd_of_mod_eq_zero h) _
    omega
  · exact h

/-- **The two-rise bound from the kernel-checked arithmetic.** -/
theorem twoRiseBound_of_allPairs {N B : ℕ} (h : TwoRise.AllPairs N B) : TwoRiseBound N B := by
  intro n hn hN
  obtain ⟨a, ha, hna, h1⟩ := block_eq hn
  have hn' : nextMin n % 2 = 1 := nextMin_odd (by omega)
  obtain ⟨a', _, hna', _⟩ := block_eq hn'
  have hk1 : 1 ≤ orun n := orun_pos hn
  have hl : 1 ≤ erun n := erun_pos n
  have hle : 2 ^ orun n * a ≤ 2 ^ N := by rw [← hna]; omega
  have hkN : orun n ≤ N := by
    have h2 : 2 ^ orun n ≤ 2 ^ N := le_trans (Nat.le_mul_of_pos_right _ (by omega)) hle
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h2
  apply h (orun n) hk1 hkN a (erun n) (orun (nextMin n)) a' ha hle hl
  rw [pow_add, mul_assoc, ← hna', h1]
  ring

theorem logb_one_add_le {u : ℝ} (hu : 0 ≤ u) : Real.logb 2 (1 + u) ≤ 2 * u := by
  have hl := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + u by linarith)
  have hl2 : (1 / 2 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hpos : (0 : ℝ) < Real.log 2 := by linarith
  rw [Real.logb, div_le_iff₀ hpos]
  nlinarith [mul_nonneg hu (le_of_lt (sub_pos.mpr hl2))]

/-- **Two consecutive steps of the chain of minima** (Lemma 1 of the note, twice): with
`x = log₂(n + 1)`, `x'' ≤ x + (δ − 1)(k + k') − 2 + 6/(n + 1)` for the second next minimum. -/
theorem logb_two_step {n : ℕ} (hn : n % 2 = 1) :
    Real.logb 2 ((nextMin (nextMin n) : ℝ) + 1) ≤ Real.logb 2 ((n : ℝ) + 1) +
      (Real.logb 2 3 - 1) * ((orun n + orun (nextMin n) : ℕ) : ℝ) - 2 + 6 / ((n : ℝ) + 1) := by
  obtain ⟨a, _, hna, h1⟩ := block_eq hn
  have hn' : nextMin n % 2 = 1 := nextMin_odd (by omega)
  obtain ⟨a', _, hna', h2⟩ := block_eq hn'
  have hint := TwoRise.two_step_core hna h1 (erun_pos n) hna' h2 (erun_pos _)
  obtain ⟨s, hs⟩ : ∃ s, s = orun n + orun (nextMin n) := ⟨_, rfl⟩
  rw [← hs] at hint ⊢
  have hR : (4 : ℝ) * 2 ^ s * ((nextMin (nextMin n) : ℝ) + 1) ≤ (3 : ℝ) ^ s * ((n : ℝ) + 4) := by
    exact_mod_cast hint
  have hpos1 : (0 : ℝ) < (nextMin (nextMin n) : ℝ) + 1 := by positivity
  have hpos2 : (0 : ℝ) < (n : ℝ) + 4 := by positivity
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hlog := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by positivity) hR
  have e1 : Real.logb 2 ((4 : ℝ) * 2 ^ s * ((nextMin (nextMin n) : ℝ) + 1)) =
      2 + s + Real.logb 2 ((nextMin (nextMin n) : ℝ) + 1) := by
    rw [Real.logb_mul (by positivity) hpos1.ne', Real.logb_mul (by norm_num) (by positivity),
      Real.logb_pow, Real.logb_self_eq_one (by norm_num),
      show (4 : ℝ) = 2 ^ 2 by norm_num, Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
    push_cast
    ring
  have e2 : Real.logb 2 ((3 : ℝ) ^ s * ((n : ℝ) + 4)) =
      s * Real.logb 2 3 + Real.logb 2 ((n : ℝ) + 4) := by
    rw [Real.logb_mul (by positivity) hpos2.ne', Real.logb_pow]
  rw [e1, e2] at hlog
  have hq : Real.logb 2 ((n : ℝ) + 4) ≤ Real.logb 2 ((n : ℝ) + 1) + 6 / ((n : ℝ) + 1) := by
    have hn1' : (n : ℝ) + 1 ≠ 0 := hn1.ne'
    have e : (n : ℝ) + 4 = ((n : ℝ) + 1) * (1 + 3 / ((n : ℝ) + 1)) := by
      field_simp <;> ring
    rw [e, Real.logb_mul hn1.ne' (by positivity)]
    have := logb_one_add_le (show (0 : ℝ) ≤ 3 / ((n : ℝ) + 1) by positivity)
    have e3 : 2 * (3 / ((n : ℝ) + 1)) = 6 / ((n : ℝ) + 1) := by ring
    linarith
  linarith

/-- **The least element of a cycle is a local minimum.** -/
theorem exists_least_rotation {x p : ℕ} (hx : 0 < x) (hp : 0 < p) (hcyc : T^[p] x = x) :
    ∃ i, IsMinOf (T^[i] x) p ∧ ∀ j, T^[i] x ≤ T^[j] x := by
  obtain ⟨i, _, hmin⟩ := Finset.exists_min_image (Finset.range p) (fun j => T^[j] x)
    ⟨0, Finset.mem_range.mpr hp⟩
  have hall : ∀ j, T^[i] x ≤ T^[j] x := by
    intro j
    have hj : T^[j] x = T^[j % p] x :=
      periodic_mod (f := fun j => T^[j] x) (fun r => iterate_add_period hcyc r) j
    rw [hj]
    exact hmin _ (Finset.mem_range.mpr (Nat.mod_lt _ hp))
  refine ⟨i, ⟨?_, ?_⟩, hall⟩
  · by_contra hev
    have hev' : T^[i] x % 2 = 0 := by omega
    have h1 := hall (i + 1)
    rw [Function.iterate_succ_apply', T_even hev'] at h1
    have hpos := iterate_T_pos hx i
    omega
  · by_contra hodd
    have hodd' : T^[p - 1] (T^[i] x) % 2 = 1 := by omega
    have e : T^[p - 1] (T^[i] x) = T^[i + (p - 1)] x := by
      rw [← Function.iterate_add_apply, Nat.add_comm]
    have h1 := hall (i + (p - 1))
    rw [← e] at h1
    have h2 : T (T^[p - 1] (T^[i] x)) = T^[i] x := by
      rw [← Function.iterate_succ_apply' T]
      simp only [Nat.succ_eq_add_one, Nat.sub_add_cancel (show 1 ≤ p by omega)]
      exact cycle_rotate hcyc i
    rw [T_odd hodd'] at h2
    have := iterate_T_pos hx i
    omega

/-- **Theorem 21, two-element form, with its rational side conditions**, for a real lower bound
`X₀` of the cycle elements: `Λ < (m − m₂)/X₀ + 1/(2^N − 1) + (m₂ − 1)/(2^M − 1)`. -/
theorem lambda_lt_two {x p : ℕ} (hx : 0 < x) (hp : 0 < p) (hcyc : T^[p] x = x)
    {m m₂ N M Kp : ℕ} (hm : numLocalMin x p = m) (hm₂ : 1 ≤ m₂) (hm₂m : m₂ ≤ m)
    {X₀ : ℝ} (hX₀ : 0 < X₀) (hlow : ∀ j, X₀ ≤ ((T^[j] x : ℕ) : ℝ)) (hK : Kp ≤ oddCount T x p)
    (hN1 : 1 ≤ N) (hM1 : 1 ≤ M)
    (hN : (N : ℚ) * m * geomQ deltaUp m₂ ≤ m₂ * Kp)
    (hM : (M : ℚ) * m * (1 + geomQ deltaUp (m₂ - 1)) ≤ m₂ * Kp) :
    (p : ℝ) * Real.log 2 - (oddCount T x p : ℝ) * Real.log 3 <
      ((m - m₂ : ℕ) : ℝ) / X₀ + 1 / ((2 : ℝ) ^ N - 1) + ((m₂ - 1 : ℕ) : ℝ) / ((2 : ℝ) ^ M - 1) := by
  have h21 := theorem21_two hx hp hcyc hm₂ (by rw [hm]; exact hm₂m) hX₀ hlow
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
  have e1 : 3 / ((2 : ℝ) ^ N - 1) = 3 * (1 / ((2 : ℝ) ^ N - 1)) := by ring
  have e2 : 3 * ((m - m₂ : ℕ) : ℝ) / X₀ = 3 * (((m - m₂ : ℕ) : ℝ) / X₀) := by ring
  have e3 : 3 * ((m₂ - 1 : ℕ) : ℝ) / ((2 : ℝ) ^ M - 1) =
      3 * (((m₂ - 1 : ℕ) : ℝ) / ((2 : ℝ) ^ M - 1)) := by ring
  linarith

end Collatz
