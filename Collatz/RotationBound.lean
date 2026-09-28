import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic

/-!
# Rotation sums of `2^{-fract t}` (research note `sharp_size_bound.md`, Lemmas 3–4)

If `p/q` is a rational approximation of `θ` with `gcd(p, q) = 1` and `|qθ − p| ≤ 1/q`, then the
`q` points `fract (s + jθ)`, `j < q`, fall one into each of the `q` cells of a lattice of mesh
`1/q`, so `∑_{j<q} 2^{-fract(s + jθ)} ≤ q/(2 log 2) + 3/2` (`block_sum_le`). Splitting an orbit of
length `K` into such blocks gives `orbit_sum_le`: `∑_{k<K} 2^{-fract(s + kθ)} ≤ K/(2 log 2) +
3K/(2q) + q`. This is the elementary form of the Denjoy–Koksma inequality used in the note; the
constant `1/(2 log 2) = ∫₀¹ 2^{-t} dt` is what replaces Hercher's `3/4`.
-/

namespace Collatz

open Finset

/-- `∑_{i<q} 2^{-i/q} ≤ q/(2 log 2) + 1/2` (geometric sum and `1 + x ≤ eˣ`). -/
theorem two_rpow_geom_sum_le (q : ℕ) (hq : 0 < q) :
    ∑ i ∈ range q, (2 : ℝ) ^ (-((i : ℝ) / q)) ≤ q / (2 * Real.log 2) + 1 / 2 := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hq'' : (q : ℝ) ≠ 0 := hq'.ne'
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog' : Real.log 2 ≠ 0 := hlog.ne'
  set y : ℝ := Real.log 2 / q with hy
  have hy_pos : 0 < y := by positivity
  set E : ℝ := Real.exp y with hE
  have hE_pos : 0 < E := Real.exp_pos y
  have hyE : y + 1 ≤ E := Real.add_one_le_exp y
  set r : ℝ := (2 : ℝ) ^ (-(1 / (q : ℝ))) with hr
  have hr_exp : r = E⁻¹ := by
    rw [hr, hE, Real.rpow_def_of_pos (by norm_num), ← Real.exp_neg, hy]
    congr 1; ring
  have hr_pos : 0 < r := by rw [hr_exp]; positivity
  have hr_lt : r < 1 := by
    rw [hr_exp]
    have h1 : E⁻¹ * E = 1 := inv_mul_cancel₀ hE_pos.ne'
    have h2 : 0 < E⁻¹ := inv_pos.mpr hE_pos
    nlinarith
  have hterm : ∀ i : ℕ, (2 : ℝ) ^ (-((i : ℝ) / q)) = r ^ i := by
    intro i
    rw [hr, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    congr 1; ring
  have hrq : r ^ q = 1 / 2 := by
    rw [hr, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have : -(1 / (q : ℝ)) * (q : ℝ) = -1 := by
      rw [neg_mul, one_div, inv_mul_cancel₀ hq'']
    rw [this, Real.rpow_neg_one]; norm_num
  rw [Finset.sum_congr rfl (fun i _ => hterm i), geom_sum_eq hr_lt.ne q, hrq]
  have h1r : 0 < 1 - r := by linarith
  have h1r' : 1 - r ≠ 0 := h1r.ne'
  have hr1' : r - 1 ≠ 0 := sub_ne_zero.mpr hr_lt.ne
  have hS : ((1 : ℝ) / 2 - 1) / (r - 1) = 1 / (2 * (1 - r)) := by
    field_simp <;> ring
  rw [hS]
  -- `1 - r ≥ y/(1+y)` since `r = 1/E` and `E ≥ 1 + y`
  have hkey : y / (1 + y) ≤ 1 - r := by
    rw [hr_exp, div_le_iff₀ (by positivity)]
    have h1 : E⁻¹ * (1 + y) ≤ E⁻¹ * E :=
      mul_le_mul_of_nonneg_left (by linarith) (inv_nonneg.mpr hE_pos.le)
    rw [inv_mul_cancel₀ hE_pos.ne'] at h1
    have h2 : (1 - E⁻¹) * (1 + y) = 1 + y - E⁻¹ * (1 + y) := by ring
    linarith
  have hkey' : 2 * (y / (1 + y)) ≤ 2 * (1 - r) := by linarith
  have h1y : (1 : ℝ) + Real.log 2 / q ≠ 0 := ne_of_gt (by linarith)
  calc 1 / (2 * (1 - r)) ≤ 1 / (2 * (y / (1 + y))) :=
        one_div_le_one_div_of_le (by positivity) hkey'
    _ = q / (2 * Real.log 2) + 1 / 2 := by
        rw [hy]; field_simp <;> ring

/-- The index of the lattice cell containing the `j`-th rotation point. -/
def cellIdx (n : ℤ) (p : ℤ) (q j : ℕ) : ℕ := ((n + (j : ℤ) * p) % (q : ℤ)).toNat

theorem cellIdx_spec (n p : ℤ) (q j : ℕ) (hq : 0 < q) :
    ((cellIdx n p q j : ℕ) : ℤ) = (n + (j : ℤ) * p) % (q : ℤ) ∧ cellIdx n p q j < q := by
  have hq' : (0 : ℤ) < q := by exact_mod_cast hq
  have h0 : 0 ≤ (n + (j : ℤ) * p) % (q : ℤ) := Int.emod_nonneg _ hq'.ne'
  have h1 : (n + (j : ℤ) * p) % (q : ℤ) < q := Int.emod_lt_of_pos _ hq'
  refine ⟨Int.toNat_of_nonneg h0, ?_⟩
  have : ((cellIdx n p q j : ℕ) : ℤ) < q := by rw [cellIdx, Int.toNat_of_nonneg h0]; exact h1
  exact_mod_cast this

/-- `cellIdx` is injective on `range q` when `gcd(p, q) = 1`. -/
theorem cellIdx_injOn (n p : ℤ) (q : ℕ) (hq : 0 < q) (hcop : Int.gcd (q : ℤ) p = 1) :
    Set.InjOn (cellIdx n p q) (range q : Set ℕ) := by
  intro j hj j' hj' h
  simp only [coe_range, Set.mem_Iio] at hj hj'
  have hq' : (0 : ℤ) < q := by exact_mod_cast hq
  have e : (n + (j : ℤ) * p) % (q : ℤ) = (n + (j' : ℤ) * p) % (q : ℤ) := by
    rw [← (cellIdx_spec n p q j hq).1, ← (cellIdx_spec n p q j' hq).1, h]
  have hmod : Int.ModEq (q : ℤ) (n + (j : ℤ) * p) (n + (j' : ℤ) * p) := e
  have hdvd : (q : ℤ) ∣ ((j' : ℤ) - j) * p := by
    have := Int.modEq_iff_dvd.mp hmod
    have e2 : (n + (j' : ℤ) * p) - (n + (j : ℤ) * p) = ((j' : ℤ) - j) * p := by ring
    rwa [e2] at this
  have hdvd' : (q : ℤ) ∣ (j' : ℤ) - j := Int.dvd_of_dvd_mul_left_of_gcd_one hdvd hcop
  obtain ⟨k, hk⟩ := hdvd'
  have hj1 : (j : ℤ) < q := by exact_mod_cast hj
  have hj2 : (j' : ℤ) < q := by exact_mod_cast hj'
  have hk0 : k = 0 := by
    rcases lt_trichotomy k 0 with hk' | hk' | hk'
    · exfalso
      have : (q : ℤ) * k ≤ (q : ℤ) * (-1) := by
        apply mul_le_mul_of_nonneg_left _ hq'.le; omega
      omega
    · exact hk'
    · exfalso
      have : (q : ℤ) * 1 ≤ (q : ℤ) * k := by
        apply mul_le_mul_of_nonneg_left _ hq'.le; omega
      omega
  rw [hk0, mul_zero, sub_eq_zero] at hk
  exact_mod_cast hk.symm

/-- The image of `range q` under `cellIdx` is all of `range q`. -/
theorem cellIdx_image (n p : ℤ) (q : ℕ) (hq : 0 < q) (hcop : Int.gcd (q : ℤ) p = 1) :
    (range q).image (cellIdx n p q) = range q := by
  apply Finset.eq_of_subset_of_card_le
  · intro i hi
    rw [Finset.mem_image] at hi
    obtain ⟨j, _, rfl⟩ := hi
    exact Finset.mem_range.mpr (cellIdx_spec n p q j hq).2
  · rw [Finset.card_image_of_injOn (cellIdx_injOn n p q hq hcop)]

/-- One block: the `q` points `fract (s + jθ)` fall one per cell, so the sum is at most
`q/(2 log 2) + 3/2`. Approximation from below: `0 ≤ qθ − p ≤ 1/q`. -/
theorem block_sum_le (θ s : ℝ) (q : ℕ) (hq : 0 < q) (p : ℤ) (hcop : Int.gcd (q : ℤ) p = 1)
    (hlo : 0 ≤ (q : ℝ) * θ - p) (hhi : (q : ℝ) * θ - p ≤ 1 / q) :
    ∑ j ∈ range q, (2 : ℝ) ^ (-Int.fract (s + j * θ)) ≤ q / (2 * Real.log 2) + 3 / 2 := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  obtain ⟨n, hn⟩ : ∃ n : ℤ, n = ⌊(q : ℝ) * s⌋ := ⟨_, rfl⟩
  have hfl1 : (n : ℝ) ≤ q * s := by rw [hn]; exact Int.floor_le _
  have hfl2 : (q : ℝ) * s < n + 1 := by rw [hn]; exact Int.lt_floor_add_one _
  -- termwise bound by the value at the cell's left endpoint (plus 1 for the wrapping cell)
  have hterm : ∀ j ∈ range q, (2 : ℝ) ^ (-Int.fract (s + j * θ)) ≤
      (2 : ℝ) ^ (-((cellIdx n p q j : ℝ) / q)) + if cellIdx n p q j = q - 1 then 1 else 0 := by
    intro j hj
    rw [Finset.mem_range] at hj
    obtain ⟨hm, hmlt⟩ := cellIdx_spec n p q j hq
    obtain ⟨m, hmdef⟩ : ∃ m : ℕ, m = cellIdx n p q j := ⟨_, rfl⟩
    rw [← hmdef] at hm hmlt ⊢
    obtain ⟨t, ht⟩ : ∃ t : ℤ, t = (n + (j : ℤ) * p) / (q : ℤ) := ⟨_, rfl⟩
    have hdiv : ((n + (j : ℤ) * p) % (q : ℤ)) + (q : ℤ) * t = n + (j : ℤ) * p := by
      rw [ht, Int.emod_def]; ring
    rw [← hm] at hdiv
    have hcast : (m : ℝ) + (q : ℝ) * (t : ℝ) = n + (j : ℝ) * p := by
      have := congrArg (fun z : ℤ => (z : ℝ)) hdiv
      push_cast at this
      linarith
    -- `w = s + jθ − t`, with `q w = m + (qs − n) + j (qθ − p)`
    obtain ⟨w, hw⟩ : ∃ w : ℝ, w = s + j * θ - t := ⟨_, rfl⟩
    have hfr : Int.fract (s + j * θ) = Int.fract w := by rw [hw, Int.fract_sub_intCast]
    have hqw : (q : ℝ) * w = m + ((q : ℝ) * s - n) + (j : ℝ) * ((q : ℝ) * θ - p) := by
      rw [hw]
      linear_combination (-1 : ℝ) * hcast
    have hj' : (j : ℝ) < q := by exact_mod_cast hj
    have hprod0 : 0 ≤ (j : ℝ) * ((q : ℝ) * θ - p) := mul_nonneg (Nat.cast_nonneg j) hlo
    have hprod1 : (j : ℝ) * ((q : ℝ) * θ - p) < 1 := by
      calc (j : ℝ) * ((q : ℝ) * θ - p) ≤ (j : ℝ) * (1 / q) :=
            mul_le_mul_of_nonneg_left hhi (Nat.cast_nonneg j)
        _ = j / q := by ring
        _ < 1 := (div_lt_one hq').mpr hj'
    have hlow : (m : ℝ) ≤ (q : ℝ) * w := by linarith
    have hupp : (q : ℝ) * w < m + 2 := by linarith
    rw [hfr]
    by_cases hlast : m = q - 1
    · rw [ite_eq_left hlast]
      have h1 : (2 : ℝ) ^ (-Int.fract w) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith [Int.fract_nonneg w])
      have h2 : (0 : ℝ) ≤ (2 : ℝ) ^ (-((m : ℝ) / q)) := Real.rpow_nonneg (by norm_num) _
      linarith
    · rw [ite_eq_right hlast, add_zero]
      have hm2 : m + 2 ≤ q := by omega
      have hm2' : (m : ℝ) + 2 ≤ q := by exact_mod_cast hm2
      have hw1 : w < 1 := lt_of_mul_lt_mul_left (by linarith : (q : ℝ) * w < q * 1) hq'.le
      have hw0 : (m : ℝ) / q ≤ w := by rw [div_le_iff₀ hq']; linarith
      have hw0' : 0 ≤ w := le_trans (by positivity) hw0
      rw [Int.fract_eq_self.mpr ⟨hw0', hw1⟩]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  calc ∑ j ∈ range q, (2 : ℝ) ^ (-Int.fract (s + j * θ))
      ≤ ∑ j ∈ range q, ((2 : ℝ) ^ (-((cellIdx n p q j : ℝ) / q)) +
          if cellIdx n p q j = q - 1 then 1 else 0) := Finset.sum_le_sum hterm
    _ = ∑ i ∈ (range q).image (cellIdx n p q),
          ((2 : ℝ) ^ (-((i : ℝ) / q)) + if i = q - 1 then 1 else 0) :=
        (Finset.sum_image (f := fun i : ℕ => (2 : ℝ) ^ (-((i : ℝ) / q)) + if i = q - 1 then 1 else 0)
          (cellIdx_injOn n p q hq hcop)).symm
    _ = ∑ i ∈ range q, ((2 : ℝ) ^ (-((i : ℝ) / q)) + if i = q - 1 then 1 else 0) := by
        rw [cellIdx_image n p q hq hcop]
    _ = ∑ i ∈ range q, (2 : ℝ) ^ (-((i : ℝ) / q)) + ∑ i ∈ range q, (if i = q - 1 then (1 : ℝ) else 0) := by
        rw [Finset.sum_add_distrib]
    _ ≤ q / (2 * Real.log 2) + 3 / 2 := by
        have h1 := two_rpow_geom_sum_le q hq
        have h2 : ∑ i ∈ range q, (if i = q - 1 then (1 : ℝ) else 0) = 1 := by
          rw [Finset.sum_ite_eq' (range q) (q - 1) (fun _ => (1 : ℝ)),
            ite_eq_left (Finset.mem_range.mpr (show q - 1 < q by omega))]
        linarith

/-- The block bound for either sign of `qθ − p`, by reflecting the block. -/
theorem block_sum_le' (θ s : ℝ) (q : ℕ) (hq : 0 < q) (p : ℤ) (hcop : Int.gcd (q : ℤ) p = 1)
    (happ : |(q : ℝ) * θ - p| ≤ 1 / q) :
    ∑ j ∈ range q, (2 : ℝ) ^ (-Int.fract (s + j * θ)) ≤ q / (2 * Real.log 2) + 3 / 2 := by
  rcases le_or_gt 0 ((q : ℝ) * θ - p) with hlo | hneg
  · exact block_sum_le θ s q hq p hcop hlo (le_trans (le_abs_self _) happ)
  · -- reflect: `j ↦ q − 1 − j` turns the block into a block of `-θ` starting at `s + (q−1)θ`
    have hcop' : Int.gcd (q : ℤ) (-p) = 1 := by
      unfold Int.gcd at hcop ⊢; rwa [Int.natAbs_neg]
    have hlo' : 0 ≤ (q : ℝ) * (-θ) - (-p : ℤ) := by push_cast; linarith
    have hhi' : (q : ℝ) * (-θ) - (-p : ℤ) ≤ 1 / q := by
      push_cast
      have := neg_abs_le ((q : ℝ) * θ - p)
      have h2 := abs_le.mp happ
      linarith [h2.1]
    have hrefl := block_sum_le (-θ) (s + ((q : ℝ) - 1) * θ) q hq (-p) hcop' hlo' hhi'
    rw [← Finset.sum_range_reflect] at hrefl
    refine le_trans (le_of_eq ?_) hrefl
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_range] at hj
    have hcast : ((q - 1 - j : ℕ) : ℝ) = (q : ℝ) - 1 - j := by
      have h1 : 1 ≤ q := hq
      have h2 : j ≤ q - 1 := by omega
      rw [Nat.cast_sub h2, Nat.cast_sub h1]; push_cast; ring
    have e : (s + ((q : ℝ) - 1) * θ) + ((q : ℝ) - 1 - j) * (-θ) = s + j * θ := by ring
    rw [hcast, e]

/-- Orbit sums: `∑_{k<K} 2^{-fract(s + kθ)} ≤ K/(2 log 2) + 3K/(2q) + q`. -/
theorem orbit_sum_le (θ : ℝ) (q : ℕ) (hq : 0 < q) (p : ℤ) (hcop : Int.gcd (q : ℤ) p = 1)
    (happ : |(q : ℝ) * θ - p| ≤ 1 / q) (K : ℕ) (s : ℝ) :
    ∑ k ∈ range K, (2 : ℝ) ^ (-Int.fract (s + k * θ)) ≤
      K / (2 * Real.log 2) + 3 * K / (2 * q) + q := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hq'' : (q : ℝ) ≠ 0 := hq'.ne'
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog' : Real.log 2 ≠ 0 := hlog.ne'
  induction K using Nat.strong_induction_on generalizing s with
  | _ K ih =>
    rcases lt_or_ge K q with hK | hK
    · -- fewer than `q` terms, each at most 1
      have h1 : ∑ k ∈ range K, (2 : ℝ) ^ (-Int.fract (s + k * θ)) ≤ ∑ k ∈ range K, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro k _
        exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
          (by linarith [Int.fract_nonneg (s + k * θ)])
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at h1
      have hK' : (K : ℝ) < q := by exact_mod_cast hK
      have : (0 : ℝ) ≤ K / (2 * Real.log 2) + 3 * K / (2 * q) := by positivity
      linarith
    · -- split off one block of length `q`
      obtain ⟨K', rfl⟩ : ∃ K', K = q + K' := ⟨K - q, by omega⟩
      rw [Finset.sum_range_add]
      have hblock := block_sum_le' θ s q hq p hcop happ
      have hrest := ih K' (by omega) (s + q * θ)
      have hshift : ∀ x ∈ range K', (2 : ℝ) ^ (-Int.fract (s + ((q + x : ℕ) : ℝ) * θ)) =
          (2 : ℝ) ^ (-Int.fract (s + q * θ + x * θ)) := by
        intro x _
        rw [show (s + ((q + x : ℕ) : ℝ) * θ) = s + q * θ + x * θ by push_cast; ring]
      rw [Finset.sum_congr rfl hshift]
      have hK'' : (((q + K' : ℕ) : ℝ)) = q + K' := by norm_cast
      rw [hK'']
      have e : ((q : ℝ) + K') / (2 * Real.log 2) + 3 * ((q : ℝ) + K') / (2 * q) + q =
          (q / (2 * Real.log 2) + 3 / 2) +
            (K' / (2 * Real.log 2) + 3 * K' / (2 * q) + q) := by
        field_simp <;> ring
      rw [e]
      linarith

end Collatz
