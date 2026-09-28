import Collatz.Reductions
import Collatz.RotationBound

/-!
# The sharp size-only cycle inequality (research note `sharp_size_bound.md`, Theorem A)

Along a `T`-orbit, `log₂` of the iterate changes by `−1` at an even step and by `log₂ 3 − 1 +
log₂(1 + 1/(3y))` at an odd step (`logb_iterate`). Around a cycle the corrections add up to
exactly `Λ / log 2` with `Λ = p log 2 − K log 3` (`Esum_cycle`), and the fractional parts of the
running `log₂` at the odd steps form an orbit of the circle rotation by `θ = log₂ 3`. Combining
the block bound `orbit_sum_le` with `Λ = ∑ log(1 + 1/(3y)) ≤ ∑ 1/(3y)` gives

  `Λ ≤ e^Λ (K/(2 log 2) + 3K/(2q) + q) / (3 X₀)`

for every cycle whose elements are all `≥ X₀` and every rational `p'/q` with `gcd(p', q) = 1`
and `|q log₂ 3 − p'| ≤ 1/q` (`sharp_cycle_bound`). With `p'/q = 1054/665`, certified by the kernel
(`approx_665`), the constant is `1/(2 log 2) + 3/1330 = 0.7236…`, against `3/4` in Hercher's
Theorem 27 (`sharp_cycle_bound_665`).
-/

namespace Collatz

open Finset

/-- The `log₂` correction of the `i`-th step when it is odd: `log₂(1 + 1/(3 T^i x))`. -/
noncomputable def eps (x i : ℕ) : ℝ := Real.logb 2 (1 + 1 / (3 * ((T^[i] x : ℕ) : ℝ)))

/-- Sum of the corrections over the odd steps among the first `k`. -/
noncomputable def Esum (x k : ℕ) : ℝ :=
  ∑ i ∈ range k, if T^[i] x % 2 = 1 then eps x i else 0

theorem T_cast_even {y : ℕ} (h : y % 2 = 0) : ((T y : ℕ) : ℝ) = (y : ℝ) / 2 := by
  have h2 : T y * 2 = y := by rw [T_even h]; exact Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero h)
  have h3 : ((T y : ℕ) : ℝ) * 2 = y := by exact_mod_cast h2
  linarith

theorem T_cast_odd {y : ℕ} (h : y % 2 = 1) : ((T y : ℕ) : ℝ) = (3 * (y : ℝ) + 1) / 2 := by
  have h2 : T y * 2 = 3 * y + 1 := by rw [T_odd h]; exact Nat.div_mul_cancel (by omega)
  have h3 : ((T y : ℕ) : ℝ) * 2 = 3 * (y : ℝ) + 1 := by exact_mod_cast h2
  linarith

theorem logb_T_even {y : ℕ} (hy : 0 < y) (h : y % 2 = 0) :
    Real.logb 2 ((T y : ℕ) : ℝ) = Real.logb 2 y - 1 := by
  have hy' : (y : ℝ) ≠ 0 := by exact_mod_cast hy.ne'
  rw [T_cast_even h, Real.logb_div hy' (by norm_num), Real.logb_self_eq_one (by norm_num)]

theorem logb_T_odd {y : ℕ} (hy : 0 < y) (h : y % 2 = 1) :
    Real.logb 2 ((T y : ℕ) : ℝ) =
      Real.logb 2 y + Real.logb 2 3 - 1 + Real.logb 2 (1 + 1 / (3 * (y : ℝ))) := by
  have hy' : (0 : ℝ) < y := by exact_mod_cast hy
  have h3y : (3 : ℝ) * y ≠ 0 := by positivity
  have hB : (0 : ℝ) < 1 + 1 / (3 * (y : ℝ)) := by positivity
  have e : (3 * (y : ℝ) * (1 + 1 / (3 * (y : ℝ)))) / 2 = (3 * (y : ℝ) + 1) / 2 := by
    rw [mul_add, mul_one, mul_one_div_cancel h3y]
  rw [T_cast_odd h, ← e, Real.logb_div (by positivity) (by norm_num),
    Real.logb_mul h3y hB.ne', Real.logb_mul (by norm_num) hy'.ne',
    Real.logb_self_eq_one (by norm_num)]
  ring

/-- `log₂ T^k(x) = log₂ x + a_k log₂ 3 − k + E_k`, with `a_k` the odd steps and `E_k` the
corrections. -/
theorem logb_iterate (x : ℕ) (hx : 0 < x) (k : ℕ) :
    Real.logb 2 ((T^[k] x : ℕ) : ℝ) =
      Real.logb 2 x + (oddCount T x k : ℝ) * Real.logb 2 3 - k + Esum x k := by
  induction k with
  | zero => simp [Esum, oddCount]
  | succ k ih =>
    rw [Function.iterate_succ_apply', oddCount_succ, Esum, Finset.sum_range_succ, ← Esum]
    have hpos : 0 < T^[k] x := iterate_pos (fun _ => T_pos) hx k
    rcases Nat.mod_two_eq_zero_or_one (T^[k] x) with h | h
    · rw [logb_T_even hpos h, ih, h, ite_eq_right (by norm_num : ¬ ((0 : ℕ) = 1))]
      push_cast
      ring
    · rw [logb_T_odd hpos h, ih, h, ite_eq_left (rfl : (1 : ℕ) = 1), eps]
      push_cast
      ring

theorem eps_nonneg (x i : ℕ) (hx : 0 < x) : 0 ≤ eps x i := by
  unfold eps
  apply Real.logb_nonneg (by norm_num)
  have hy : (0 : ℝ) < ((T^[i] x : ℕ) : ℝ) := by
    exact_mod_cast iterate_pos (fun _ => T_pos) hx i
  have : (0 : ℝ) ≤ 1 / (3 * ((T^[i] x : ℕ) : ℝ)) := by positivity
  linarith

theorem Esum_nonneg (x k : ℕ) (hx : 0 < x) : 0 ≤ Esum x k :=
  Finset.sum_nonneg fun i _ => by
    split_ifs
    · exact eps_nonneg x i hx
    · exact le_rfl

theorem Esum_mono {x i p : ℕ} (hx : 0 < x) (h : i ≤ p) : Esum x i ≤ Esum x p :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono h) fun j _ _ => by
    split_ifs
    · exact eps_nonneg x j hx
    · exact le_rfl

/-- Around a cycle the corrections add up to `p − K log₂ 3 = Λ / log 2`. -/
theorem Esum_cycle {x p : ℕ} (hx : 0 < x) (hcyc : T^[p] x = x) :
    Esum x p = p - (oddCount T x p : ℝ) * Real.logb 2 3 := by
  have := logb_iterate x hx p
  rw [hcyc] at this
  linarith

/-- Reindexing a sum over the odd steps by the odd-step counter. -/
theorem sum_odd_reindex (x : ℕ) (G : ℕ → ℝ) (p : ℕ) :
    ∑ i ∈ range p, (if T^[i] x % 2 = 1 then G (oddCount T x i) else 0) =
      ∑ k ∈ range (oddCount T x p), G k := by
  induction p with
  | zero => simp [oddCount]
  | succ p ih =>
    rw [Finset.sum_range_succ, ih, oddCount_succ]
    rcases Nat.mod_two_eq_zero_or_one (T^[p] x) with h | h
    · rw [h, ite_eq_right (by norm_num : ¬ ((0 : ℕ) = 1)), add_zero, add_zero]
    · rw [h, ite_eq_left (rfl : (1 : ℕ) = 1), Finset.sum_range_succ]

/-- The odd element `y_i` satisfies `X₀ / y_i ≤ 2^E · 2^{-fract(S₀ + a_i θ)}`. -/
theorem odd_term_le {x p : ℕ} (hx : 0 < x) {X₀ : ℝ} (hX₀ : 0 < X₀)
    (hmin : ∀ i < p, X₀ ≤ ((T^[i] x : ℕ) : ℝ)) (i : ℕ) (hi : i < p) :
    X₀ / ((T^[i] x : ℕ) : ℝ) ≤ (2 : ℝ) ^ Esum x p *
      (2 : ℝ) ^ (-Int.fract ((Real.logb 2 x - Real.logb 2 X₀ + Esum x p) +
        (oddCount T x i : ℝ) * Real.logb 2 3)) := by
  have hy : (0 : ℝ) < ((T^[i] x : ℕ) : ℝ) := by
    exact_mod_cast iterate_pos (fun _ => T_pos) hx i
  have hyX : X₀ ≤ ((T^[i] x : ℕ) : ℝ) := hmin i hi
  have hEi : 0 ≤ Esum x i := Esum_nonneg x i hx
  have hEE : Esum x i ≤ Esum x p := Esum_mono hx hi.le
  have hlogy := logb_iterate x hx i
  have ht : Real.logb 2 X₀ ≤ Real.logb 2 ((T^[i] x : ℕ) : ℝ) :=
    Real.logb_le_logb_of_le (by norm_num) hX₀ hyX
  set S : ℝ := (Real.logb 2 x - Real.logb 2 X₀ + Esum x p) +
    (oddCount T x i : ℝ) * Real.logb 2 3 - i with hS
  have hSfr : Int.fract ((Real.logb 2 x - Real.logb 2 X₀ + Esum x p) +
      (oddCount T x i : ℝ) * Real.logb 2 3) = Int.fract S := by
    rw [hS, Int.fract_sub_natCast]
  have hS_nonneg : 0 ≤ S := by rw [hS]; linarith
  have hfrS : Int.fract S ≤ S := by
    have h0 : (0 : ℝ) ≤ ⌊S⌋ := by exact_mod_cast Int.floor_nonneg.mpr hS_nonneg
    rw [← Int.self_sub_floor]
    linarith
  have hXy : X₀ / ((T^[i] x : ℕ) : ℝ) =
      (2 : ℝ) ^ (Real.logb 2 X₀ - Real.logb 2 ((T^[i] x : ℕ) : ℝ)) := by
    rw [Real.rpow_sub (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) hX₀,
      Real.rpow_logb (by norm_num) (by norm_num) hy]
  rw [hXy, hSfr]
  have hexp : Real.logb 2 X₀ - Real.logb 2 ((T^[i] x : ℕ) : ℝ) ≤ Esum x p + (-S) := by
    rw [hS]; linarith
  calc (2 : ℝ) ^ (Real.logb 2 X₀ - Real.logb 2 ((T^[i] x : ℕ) : ℝ))
      ≤ (2 : ℝ) ^ (Esum x p + (-S)) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
    _ = (2 : ℝ) ^ Esum x p * (2 : ℝ) ^ (-S) := Real.rpow_add (by norm_num) _ _
    _ ≤ (2 : ℝ) ^ Esum x p * (2 : ℝ) ^ (-Int.fract S) := by
        apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (by norm_num) _)
        exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)

/-- **Theorem A.** For a positive `T`-cycle `T^p x = x` with `K` odd elements, all elements
`≥ X₀`, and a rational `p'/q` with `gcd(p', q) = 1`, `|q log₂ 3 − p'| ≤ 1/q`:
`Λ ≤ e^Λ (K/(2 log 2) + 3K/(2q) + q) / (3X₀)`, where `Λ = p log 2 − K log 3`. -/
theorem sharp_cycle_bound {x p : ℕ} (hx : 0 < x) (hcyc : T^[p] x = x) {X₀ : ℝ} (hX₀ : 0 < X₀)
    (hmin : ∀ i < p, X₀ ≤ ((T^[i] x : ℕ) : ℝ)) {q : ℕ} (hq : 0 < q) {p' : ℤ}
    (hcop : Int.gcd (q : ℤ) p' = 1) (happ : |(q : ℝ) * Real.logb 2 3 - p'| ≤ 1 / q) :
    (p : ℝ) * Real.log 2 - (oddCount T x p : ℝ) * Real.log 3 ≤
      Real.exp ((p : ℝ) * Real.log 2 - (oddCount T x p : ℝ) * Real.log 3) *
        ((oddCount T x p : ℝ) / (2 * Real.log 2) + 3 * (oddCount T x p : ℝ) / (2 * q) + q) /
          (3 * X₀) := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set K : ℝ := (oddCount T x p : ℝ) with hK
  set θ : ℝ := Real.logb 2 3 with hθ
  set E : ℝ := Esum x p with hE
  set Λ : ℝ := (p : ℝ) * Real.log 2 - K * Real.log 3 with hΛ
  have hEc : E = p - K * θ := by rw [hE, hK, hθ]; exact Esum_cycle hx hcyc
  have hlog' : Real.log 2 ≠ 0 := hlog.ne'
  have hθlog : θ * Real.log 2 = Real.log 3 := by
    rw [hθ, Real.logb]; field_simp
  have hΛE : Λ = E * Real.log 2 := by
    rw [hΛ, hEc, sub_mul, mul_assoc, hθlog]
  have hexp : (2 : ℝ) ^ E = Real.exp Λ := by
    rw [Real.rpow_def_of_pos (by norm_num), hΛE, mul_comm]
  have hΛsum : Λ = ∑ i ∈ range p,
      (if T^[i] x % 2 = 1 then Real.log (1 + 1 / (3 * ((T^[i] x : ℕ) : ℝ))) else 0) := by
    rw [hΛE, hE, Esum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs
    · rw [eps, Real.logb]; field_simp
    · rw [zero_mul]
  set S₀ : ℝ := Real.logb 2 x - Real.logb 2 X₀ + E with hS₀
  set c : ℝ := (2 : ℝ) ^ E / (3 * X₀) with hc
  have hc0 : 0 ≤ c := by rw [hc]; positivity
  have hterm : ∀ i ∈ range p,
      (if T^[i] x % 2 = 1 then Real.log (1 + 1 / (3 * ((T^[i] x : ℕ) : ℝ))) else 0) ≤
      c * (if T^[i] x % 2 = 1 then
        (2 : ℝ) ^ (-Int.fract (S₀ + (oddCount T x i : ℝ) * θ)) else 0) := by
    intro i hi
    rw [Finset.mem_range] at hi
    split_ifs with h
    · have hy : (0 : ℝ) < ((T^[i] x : ℕ) : ℝ) := by
        exact_mod_cast iterate_pos (fun _ => T_pos) hx i
      have hu : (0 : ℝ) < 1 / (3 * ((T^[i] x : ℕ) : ℝ)) := by positivity
      have h1 : Real.log (1 + 1 / (3 * ((T^[i] x : ℕ) : ℝ))) ≤
          1 / (3 * ((T^[i] x : ℕ) : ℝ)) := by
        have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < 1 + 1 / (3 * ((T^[i] x : ℕ) : ℝ)))
        linarith
      have h2 := odd_term_le hx hX₀ hmin i hi
      rw [← hE, ← hθ, ← hS₀] at h2
      have hy' : ((T^[i] x : ℕ) : ℝ) ≠ 0 := hy.ne'
      have hX₀' : X₀ ≠ 0 := hX₀.ne'
      have h3 : 1 / (3 * ((T^[i] x : ℕ) : ℝ)) = (1 / (3 * X₀)) * (X₀ / ((T^[i] x : ℕ) : ℝ)) := by
        field_simp <;> ring
      calc Real.log (1 + 1 / (3 * ((T^[i] x : ℕ) : ℝ))) ≤ 1 / (3 * ((T^[i] x : ℕ) : ℝ)) := h1
        _ = (1 / (3 * X₀)) * (X₀ / ((T^[i] x : ℕ) : ℝ)) := h3
        _ ≤ (1 / (3 * X₀)) * ((2 : ℝ) ^ E *
              (2 : ℝ) ^ (-Int.fract (S₀ + (oddCount T x i : ℝ) * θ))) :=
            mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = c * (2 : ℝ) ^ (-Int.fract (S₀ + (oddCount T x i : ℝ) * θ)) := by
            rw [hc]; ring
    · rw [mul_zero]
  have hre := sum_odd_reindex x (fun k => (2 : ℝ) ^ (-Int.fract (S₀ + k * θ))) p
  have horbit := orbit_sum_le θ q hq p' hcop happ (oddCount T x p) S₀
  rw [← hK] at horbit
  calc Λ ≤ ∑ i ∈ range p, c * (if T^[i] x % 2 = 1 then
          (2 : ℝ) ^ (-Int.fract (S₀ + (oddCount T x i : ℝ) * θ)) else 0) := by
        rw [hΛsum]; exact Finset.sum_le_sum hterm
    _ = c * ∑ i ∈ range p, (if T^[i] x % 2 = 1 then
          (2 : ℝ) ^ (-Int.fract (S₀ + (oddCount T x i : ℝ) * θ)) else 0) := by
        rw [Finset.mul_sum]
    _ = c * ∑ k ∈ range (oddCount T x p), (2 : ℝ) ^ (-Int.fract (S₀ + k * θ)) := by
        rw [hre]
    _ ≤ c * (K / (2 * Real.log 2) + 3 * K / (2 * q) + q) :=
        mul_le_mul_of_nonneg_left horbit hc0
    _ = Real.exp Λ * (K / (2 * Real.log 2) + 3 * K / (2 * q) + q) / (3 * X₀) := by
        rw [hc, hexp]; ring

/-- `|665 log₂ 3 − 1054| ≤ 1/665`, from `2^1054 ≤ 3^665` and `(3^665)^665 ≤ 2 (2^1054)^665`,
both evaluated by the kernel. -/
theorem approx_665 : |(665 : ℝ) * Real.logb 2 3 - ((1054 : ℤ) : ℝ)| ≤ 1 / 665 := by
  have hA : (2 : ℕ) ^ 1054 ≤ 3 ^ 665 := by decide +kernel
  have hB : ((3 : ℕ) ^ 665) ^ 665 ≤ 2 * ((2 : ℕ) ^ 1054) ^ 665 := by decide +kernel
  set a : ℝ := ((3 ^ 665 : ℕ) : ℝ) with ha
  set b : ℝ := ((2 ^ 1054 : ℕ) : ℝ) with hb
  have ha_pos : 0 < a := by rw [ha]; exact Nat.cast_pos.mpr (pow_pos (by norm_num) 665)
  have hb_pos : 0 < b := by rw [hb]; exact Nat.cast_pos.mpr (pow_pos (by norm_num) 1054)
  set y : ℝ := a / b with hy
  have hy_pos : 0 < y := div_pos ha_pos hb_pos
  have hy1 : 1 ≤ y := by
    rw [hy, le_div_iff₀ hb_pos, one_mul, ha, hb]
    exact Nat.cast_le.mpr hA
  have hypow : y ^ 665 ≤ 2 := by
    rw [hy, div_pow, div_le_iff₀ (pow_pos hb_pos 665), ha, hb, ← Nat.cast_pow, ← Nat.cast_pow]
    have h2 : (2 : ℝ) = ((2 : ℕ) : ℝ) := by norm_num
    rw [h2, ← Nat.cast_mul]
    exact Nat.cast_le.mpr hB
  have hlogb : (665 : ℝ) * Real.logb 2 3 - ((1054 : ℤ) : ℝ) = Real.logb 2 y := by
    rw [hy, Real.logb_div ha_pos.ne' hb_pos.ne', ha, hb, Nat.cast_pow, Nat.cast_pow,
      Nat.cast_ofNat, Nat.cast_ofNat, Real.logb_pow, Real.logb_pow,
      Real.logb_self_eq_one (by norm_num)]
    push_cast
    ring
  rw [hlogb, abs_le]
  constructor
  · have h0 : 0 ≤ Real.logb 2 y := Real.logb_nonneg (by norm_num) hy1
    have : (0 : ℝ) ≤ 1 / 665 := by norm_num
    linarith
  · rw [Real.logb_le_iff_le_rpow (by norm_num) hy_pos]
    have h665 : ((665 : ℕ) : ℝ)⁻¹ = 1 / 665 := by norm_num
    calc y = (y ^ 665) ^ ((665 : ℕ) : ℝ)⁻¹ :=
          (Real.pow_rpow_inv_natCast hy_pos.le (by norm_num)).symm
      _ ≤ (2 : ℝ) ^ ((665 : ℕ) : ℝ)⁻¹ := Real.rpow_le_rpow (by positivity) hypow (by positivity)
      _ = (2 : ℝ) ^ (1 / 665 : ℝ) := by rw [h665]

/-- Theorem A with `p'/q = 1054/665`: `Λ ≤ e^Λ (K/(2 log 2) + 3K/1330 + 665) / (3X₀)`. -/
theorem sharp_cycle_bound_665 {x p : ℕ} (hx : 0 < x) (hcyc : T^[p] x = x) {X₀ : ℝ}
    (hX₀ : 0 < X₀) (hmin : ∀ i < p, X₀ ≤ ((T^[i] x : ℕ) : ℝ)) :
    (p : ℝ) * Real.log 2 - (oddCount T x p : ℝ) * Real.log 3 ≤
      Real.exp ((p : ℝ) * Real.log 2 - (oddCount T x p : ℝ) * Real.log 3) *
        ((oddCount T x p : ℝ) / (2 * Real.log 2) + 3 * (oddCount T x p : ℝ) / (2 * 665) + 665) /
          (3 * X₀) :=
  sharp_cycle_bound hx hcyc hX₀ hmin (q := 665) (by norm_num) (by norm_num) approx_665

end Collatz
