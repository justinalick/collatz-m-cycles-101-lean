import Collatz.ParityVector
import Collatz.InverseTree
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.LinearCombination

/-!
# Cycles (brief, Section 5 "Cycle results")

* `cycle_equation` (Böhm and Sontacchi 1978): a `T`-periodic `x` with `p` steps and `a` odd steps
  satisfies `x (2^p − 3^a) = ρ_v`.
* `cycle_product`: `2^p = Π (3 + 1/x_i)` over the odd elements of a positive `T`-cycle.
* `cycle_bounds`: hence `3^K < 2^p ≤ (3 + 1/m)^K`, with `K` odd elements all `≥ m`.
* `cycle_bounds_of_verified`: if every `0 < n < M` reaches 1, a nontrivial positive cycle has
  `2^p ≤ (3 + 1/M)^K`: the input to the cycle-length bounds of Section 5.
-/

namespace Collatz

open Finset

/-- Böhm–Sontacchi: `x (2^p − 3^a) = ρ_v` for `T^p(x) = x`. -/
theorem cycle_equation {x p : ℕ} (h : T^[p] x = x) :
    (x : ℤ) * (2 ^ p - 3 ^ oddCount T x p) = rho (fun j => T^[j] x % 2) p := by
  have := affine_form x p
  rw [h] at this
  push_cast [mul_sub]
  have hz : ((2 ^ p * x : ℕ) : ℤ) = ((3 ^ oddCount T x p * x + rho (fun j => T^[j] x % 2) p : ℕ) : ℤ) :=
    congrArg _ this
  push_cast at hz
  linarith

/-- The factor contributed by the `i`-th step: `3 + 1/y` after an odd `y`, else `1`. -/
noncomputable def stepFactor (x i : ℕ) : ℚ :=
  if T^[i] x % 2 = 1 then 3 + 1 / (T^[i] x : ℚ) else 1

/-- `2^k T^k(x) = x Π_{i<k} f_i`. -/
theorem two_pow_mul_iterate (x k : ℕ) :
    (2 : ℚ) ^ k * (T^[k] x : ℚ) = x * ∏ i ∈ range k, stepFactor x i := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [prod_range_succ, ← mul_assoc, ← ih, Function.iterate_succ_apply', stepFactor, pow_succ]
    set y := T^[k] x
    rcases Nat.mod_two_eq_zero_or_one y with h | h
    · rw [T_even h, ite_eq_right (by omega)]
      have : ((y / 2 : ℕ) : ℚ) * 2 = y := by
        exact_mod_cast Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero h)
      linear_combination (2 : ℚ) ^ k * this
    · rw [T_odd h, ite_eq_left h]
      have hy : (y : ℚ) ≠ 0 := by exact_mod_cast (show y ≠ 0 by omega)
      have : (((3 * y + 1) / 2 : ℕ) : ℚ) * 2 = 3 * y + 1 := by
        exact_mod_cast Nat.div_mul_cancel (show 2 ∣ 3 * y + 1 by omega)
      have e : (y : ℚ) * (3 + 1 / y) = 3 * y + 1 := by rw [mul_add, mul_one_div_cancel hy]; ring
      linear_combination (2 : ℚ) ^ k * this - (2 : ℚ) ^ k * e

/-- `2^p = Π (3 + 1/x_i)` over the odd elements of a positive cycle. -/
theorem cycle_product {x p : ℕ} (hx : 0 < x) (h : T^[p] x = x) :
    (2 : ℚ) ^ p = ∏ i ∈ range p, stepFactor x i := by
  have := two_pow_mul_iterate x p
  rw [h] at this
  have hx' : (x : ℚ) ≠ 0 := by exact_mod_cast hx.ne'
  exact mul_right_cancel₀ hx' (by linarith)

/-- Lower bound on the partial products: `3^{a_k} ≤ Π f_i`, strict once an odd step occurred. -/
theorem three_pow_le_prod (x k : ℕ) :
    (3 : ℚ) ^ oddCount T x k ≤ ∏ i ∈ range k, stepFactor x i ∧
      (0 < oddCount T x k → (3 : ℚ) ^ oddCount T x k < ∏ i ∈ range k, stepFactor x i) := by
  induction k with
  | zero => simp [oddCount]
  | succ k ih =>
    obtain ⟨ih1, ih2⟩ := ih
    rw [oddCount_succ, prod_range_succ, stepFactor]
    have h3 : (0 : ℚ) < 3 ^ oddCount T x k := by positivity
    rcases Nat.mod_two_eq_zero_or_one (T^[k] x) with h | h
    · rw [ite_eq_right (by omega), h, mul_one]; simp only [Nat.add_zero]; exact ⟨ih1, ih2⟩
    · rw [ite_eq_left h, h, pow_succ]
      have hinv : (0 : ℚ) < 1 / (T^[k] x : ℚ) := by
        have : (0 : ℚ) < T^[k] x := by exact_mod_cast (show 0 < T^[k] x by omega)
        exact one_div_pos.mpr this
      refine ⟨by nlinarith, fun _ => by nlinarith⟩

/-- Upper bound: if every odd element among the first `k` is `≥ m > 0`, `Π f_i ≤ (3 + 1/m)^{a_k}`. -/
theorem prod_le_pow {x k m : ℕ} (hm : 0 < m)
    (hmin : ∀ i < k, T^[i] x % 2 = 1 → m ≤ T^[i] x) :
    ∏ i ∈ range k, stepFactor x i ≤ (3 + 1 / (m : ℚ)) ^ oddCount T x k := by
  induction k with
  | zero => simp [oddCount]
  | succ k ih =>
    have ih := ih fun i hi => hmin i (by omega)
    rw [oddCount_succ, prod_range_succ, stepFactor]
    have hprod : 0 ≤ ∏ i ∈ range k, stepFactor x i :=
      prod_nonneg fun i _ => by unfold stepFactor; split_ifs <;> positivity
    rcases Nat.mod_two_eq_zero_or_one (T^[k] x) with h | h
    · rw [ite_eq_right (by omega), h, mul_one]; simp only [Nat.add_zero]; exact ih
    · rw [ite_eq_left h, h, pow_succ]
      have hm' : (0 : ℚ) < m := by exact_mod_cast hm
      have hle : 1 / (T^[k] x : ℚ) ≤ 1 / m :=
        one_div_le_one_div_of_le hm' (by exact_mod_cast hmin k (by omega) h)
      exact mul_le_mul ih (by linarith) (by positivity) (by positivity)

/-- Positive cycles: `3^K < 2^p ≤ (3 + 1/m)^K`, `K` the odd elements, all `≥ m`. -/
theorem cycle_bounds {x p m : ℕ} (hx : 0 < x) (hp : 0 < p) (h : T^[p] x = x) (hm : 0 < m)
    (hmin : ∀ i < p, T^[i] x % 2 = 1 → m ≤ T^[i] x) :
    (3 : ℚ) ^ oddCount T x p < 2 ^ p ∧ (2 : ℚ) ^ p ≤ (3 + 1 / (m : ℚ)) ^ oddCount T x p := by
  rw [cycle_product hx h]
  refine ⟨(three_pow_le_prod x p).2 (Nat.pos_of_ne_zero fun hK => ?_), prod_le_pow hm hmin⟩
  -- With no odd step the product is 1, forcing `2^p = 1`.
  have hprod : ∏ i ∈ range p, stepFactor x i = 1 := prod_eq_one fun i hi => by
    have : T^[i] x % 2 = 0 := by
      by_contra hne
      have := oddCount_pos_of_odd (mem_range.mp hi) (by omega)
      omega
    simp [stepFactor, this]
  have := cycle_product hx h
  rw [hprod] at this
  have : (2 : ℚ) ^ p ≠ 1 := (one_lt_pow₀ (by norm_num) hp.ne').ne'
  contradiction
where
  oddCount_pos_of_odd {i : ℕ} (hi : i < p) (hodd : T^[i] x % 2 = 1) : 0 < oddCount T x p := by
    have hmono := oddCount_mono T x (show i + 1 ≤ p by omega)
    rw [oddCount_succ, hodd] at hmono; omega

/-- `T` keeps positive numbers positive. -/
theorem T_pos {n : ℕ} (hn : 0 < n) : 0 < T n := by unfold T; split_ifs <;> omega

theorem iterate_T_pos {n : ℕ} (hn : 0 < n) (k : ℕ) : 0 < T^[k] n := by
  induction k with
  | zero => exact hn
  | succ k ih => rw [Function.iterate_succ_apply']; exact T_pos ih

/-- Once at 1, the `T`-orbit alternates `1, 2`. -/
theorem iterate_T_one (k : ℕ) : T^[k] 1 = 1 ∨ T^[k] 1 = 2 := by
  induction k with
  | zero => exact Or.inl rfl
  | succ k ih => rw [Function.iterate_succ_apply']; rcases ih with h | h <;> rw [h] <;> decide

/-- Every element of a positive `T`-cycle through `x ∉ {1, 2}` avoids 1 forever. -/
theorem cycle_not_reaches_one {x p : ℕ} (hp : 0 < p) (h : T^[p] x = x) (hx1 : x ≠ 1) (hx2 : x ≠ 2)
    (i : ℕ) : ¬ Reaches T (T^[i] x) 1 := by
  rintro ⟨j, hj⟩
  have hper : ∀ t, T^[p * t] x = x := fun t => by
    induction t with
    | zero => rfl
    | succ t ih => rw [Nat.mul_succ, Function.iterate_add_apply, h, ih]
  obtain ⟨t, ht⟩ : ∃ t, j + i ≤ p * t := ⟨j + i, Nat.le_mul_of_pos_left _ hp⟩
  have := hper t
  rw [show p * t = (p * t - (j + i)) + (j + i) by omega, Function.iterate_add_apply,
    Function.iterate_add_apply, hj] at this
  rcases iterate_T_one (p * t - (j + i)) with h1 | h1 <;> omega

/-- If every `0 < n < M` reaches 1, a nontrivial positive cycle has `2^p ≤ (3 + 1/M)^K`. -/
theorem cycle_bounds_of_verified {x p M : ℕ} (hM : 0 < M)
    (hver : ∀ n, 0 < n → n < M → Reaches T n 1)
    (hx : 0 < x) (hp : 0 < p) (h : T^[p] x = x) (hx1 : x ≠ 1) (hx2 : x ≠ 2) :
    (3 : ℚ) ^ oddCount T x p < 2 ^ p ∧ (2 : ℚ) ^ p ≤ (3 + 1 / (M : ℚ)) ^ oddCount T x p :=
  cycle_bounds hx hp h hM fun i _ _ => by
    by_contra hlt
    exact cycle_not_reaches_one hp h hx1 hx2 i
      (hver _ (iterate_T_pos hx i) (by omega))

end Collatz
