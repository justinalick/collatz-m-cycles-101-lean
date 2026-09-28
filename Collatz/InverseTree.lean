import Collatz.Defs
import Mathlib.Tactic.NormNum

/-!
# Inverse tree, mod-3 facts and Bařina's identity (brief, Sections 4, 7 and 8)

* `T_eq_iff`: `T⁻¹(m) = {2m} ∪ {(2m − 1)/3 : m ≡ 2 (mod 3)}`.
* `T_mod_three`: `T x ≡ 0 (mod 3)` forces `x ≡ 0 (mod 3)` and `x` even; hence orbits never
  re-enter the multiples of 3 (`iterate_T_mod_three`, and `iterate_C_mod_three` for `C`).
* The misstatement "if `C^j(n) ≡ 0 (mod 3)` then `j = 0`" is refuted by `12 → 6`.
* `sieve_mod_three`: `n ≡ 2 (mod 3)` has the smaller preimage `(2n − 1)/3`.
* `barina_identity`: `T^a(2^a m − 1) = 3^a m − 1`.
-/

namespace Collatz

theorem T_eq_iff (x m : ℕ) : T x = m ↔ x = 2 * m ∨ (m % 3 = 2 ∧ x = (2 * m - 1) / 3) := by
  unfold T
  split_ifs with h <;> omega

theorem T_mod_three {x : ℕ} (h : T x % 3 = 0) : x % 3 = 0 ∧ x % 2 = 0 := by
  unfold T at h
  split_ifs at h with hx <;> omega

theorem C_mod_three {x : ℕ} (h : C x % 3 = 0) : x % 3 = 0 := by
  unfold C at h
  split_ifs at h with hx <;> omega

theorem iterate_T_mod_three {x : ℕ} (hx : x % 3 ≠ 0) (k : ℕ) : T^[k] x % 3 ≠ 0 := by
  induction k with
  | zero => exact hx
  | succ k ih => rw [Function.iterate_succ_apply']; exact fun h => ih (T_mod_three h).1

theorem iterate_C_mod_three {x : ℕ} (hx : x % 3 ≠ 0) (k : ℕ) : C^[k] x % 3 ≠ 0 := by
  induction k with
  | zero => exact hx
  | succ k ih => rw [Function.iterate_succ_apply']; exact fun h => ih (C_mod_three h)

/-- Section 8: "if `C^j(n) ≡ 0 (mod 3)` then `j = 0`" is false. -/
theorem not_mod_three_only_at_start : ¬ ∀ n j, C^[j] n % 3 = 0 → j = 0 :=
  fun h => absurd (h 12 1 (by decide)) (by decide)

/-- The 3-adic sieve: `n ≡ 2 (mod 3)` is `T` of the smaller number `(2n − 1)/3`. -/
theorem sieve_mod_three {n : ℕ} (h : n % 3 = 2) : T ((2 * n - 1) / 3) = n ∧ (2 * n - 1) / 3 < n :=
  ⟨(T_eq_iff _ _).mpr (Or.inr ⟨h, rfl⟩), by omega⟩

/-- Bařina's identity `T^a(2^a m − 1) = 3^a m − 1` for `m ≥ 1`. -/
theorem barina_identity (a : ℕ) {m : ℕ} (hm : 1 ≤ m) : T^[a] (2 ^ a * m - 1) = 3 ^ a * m - 1 := by
  induction a generalizing m with
  | zero => simp
  | succ a ih =>
    have hX : 2 ^ (a + 1) * m = 2 * (2 ^ a * m) := by ring
    have hpos : 1 ≤ 2 ^ a * m := Nat.mul_pos (Nat.two_pow_pos a) hm
    have hodd : (2 ^ (a + 1) * m - 1) % 2 = 1 := by rw [hX]; omega
    rw [Function.iterate_succ_apply, T_odd hodd]
    have h3 : 2 ^ a * (3 * m) = 3 * (2 ^ a * m) := by ring
    have : (3 * (2 ^ (a + 1) * m - 1) + 1) / 2 = 2 ^ a * (3 * m) - 1 := by rw [hX, h3]; omega
    rw [this, ih (by omega), pow_succ, Nat.mul_assoc]

/-- The `a` consecutive odd `T`-steps of `2^a m − 1`. -/
theorem barina_odd {a j : ℕ} (hj : j < a) {m : ℕ} (hm : 1 ≤ m) :
    T^[j] (2 ^ a * m - 1) % 2 = 1 := by
  obtain ⟨e, rfl⟩ : ∃ e, a = j + (e + 1) := ⟨a - j - 1, by omega⟩
  have h1 : 2 ^ (j + (e + 1)) * m = 2 ^ j * (2 ^ (e + 1) * m) := by ring
  have hm' : 1 ≤ 2 ^ (e + 1) * m := Nat.mul_pos (Nat.two_pow_pos _) hm
  rw [h1, barina_identity j hm']
  have h2 : 3 ^ j * (2 ^ (e + 1) * m) = 2 * (3 ^ j * 2 ^ e * m) := by ring
  have h3 : 1 ≤ 3 ^ j * 2 ^ e * m :=
    Nat.mul_pos (Nat.mul_pos (pow_pos (by norm_num) j) (Nat.two_pow_pos e)) hm
  rw [h2]; omega

end Collatz
