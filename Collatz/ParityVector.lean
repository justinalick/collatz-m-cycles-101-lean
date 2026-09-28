import Collatz.Defs
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators

/-!
# The parity-vector theorem (Terras 1976, Everett 1977; brief, Section 5 item 1)

* `parities_eq_iff_modEq`: `n` and `m` share their first `k` `T`-parities iff
  `n ≡ m [MOD 2^k]`.
* `parityVector_bijective`: residues mod `2^k` biject with `{0,1}^k` (as `Fin k → Bool`).
* `affine_form`: `2^k T^k(n) = 3^{a_k} n + ρ_k`, where `ρ_k` depends only on the parities.
-/

namespace Collatz

/-- `T (2^(k+1) q + r)` splits into a multiple of `2^k` and `T r`. -/
theorem T_two_pow_mul_add (k q r : ℕ) :
    T (2 ^ (k + 1) * q + r) = 2 ^ k * (if r % 2 = 0 then q else 3 * q) + T r := by
  have e1 : 2 ^ (k + 1) * q + r = 2 * (2 ^ k * q) + r := by ring
  have e3 : 2 ^ k * (3 * q) = 3 * (2 ^ k * q) := by ring
  rw [e1]
  split_ifs with h
  · generalize 2 ^ k * q = s
    unfold T; split_ifs <;> omega
  · rw [e3]
    generalize 2 ^ k * q = s
    unfold T; split_ifs <;> omega

/-- The first `j ≤ k` iterates of `2^k q + r` and of `r` differ by a multiple of `2^(k-j)`. -/
theorem iterate_two_pow_mul_add {k j : ℕ} (hj : j ≤ k) (q r : ℕ) :
    ∃ q', T^[j] (2 ^ k * q + r) = 2 ^ (k - j) * q' + T^[j] r := by
  induction j with
  | zero => exact ⟨q, rfl⟩
  | succ j ih =>
    obtain ⟨q', hq'⟩ := ih (by omega)
    obtain ⟨e, he⟩ : ∃ e, k - j = e + 1 := ⟨k - j - 1, by omega⟩
    refine ⟨if T^[j] r % 2 = 0 then q' else 3 * q', ?_⟩
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hq', he, T_two_pow_mul_add,
      show k - (j + 1) = e by omega]

/-- `(2^(e+1) q + x) % 2 = x % 2`. -/
theorem two_pow_succ_mul_add_mod (e q x : ℕ) : (2 ^ (e + 1) * q + x) % 2 = x % 2 := by
  have : 2 ^ (e + 1) * q = 2 * (2 ^ e * q) := by ring
  rw [this]; omega

/-- The first `k` parities of `n` are those of `n % 2^k`. -/
theorem parity_iterate_mod {n k j : ℕ} (hj : j < k) :
    T^[j] n % 2 = T^[j] (n % 2 ^ k) % 2 := by
  obtain ⟨q', hq'⟩ := iterate_two_pow_mul_add hj.le (n / 2 ^ k) (n % 2 ^ k)
  rw [Nat.div_add_mod] at hq'
  rw [hq']
  obtain ⟨e, he⟩ : ∃ e, k - j = e + 1 := ⟨k - j - 1, by omega⟩
  rw [he, two_pow_succ_mul_add_mod]

/-- Terras/Everett: `n` and `m` have the same first `k` `T`-parities iff `n ≡ m [MOD 2^k]`. -/
theorem parities_eq_iff_modEq {n m k : ℕ} :
    (∀ j < k, T^[j] n % 2 = T^[j] m % 2) ↔ n ≡ m [MOD 2 ^ k] := by
  constructor
  · intro h
    induction k generalizing n m with
    | zero => simp [Nat.ModEq, Nat.mod_one]
    | succ k ih =>
      have h0 := h 0 k.succ_pos
      have hT : T n ≡ T m [MOD 2 ^ k] := ih fun j hj => by
        simpa [Function.iterate_succ_apply] using h (j + 1) (by omega)
      simp only [Function.iterate_zero, id_eq] at h0
      rcases Nat.mod_two_eq_zero_or_one n with hn | hn
      · have hm : m % 2 = 0 := h0 ▸ hn
        rw [T_even hn, T_even hm] at hT
        have := hT.mul_left' 2
        rw [Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hn),
          Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hm), ← pow_succ'] at this
        exact this
      · have hm : m % 2 = 1 := h0 ▸ hn
        rw [T_odd hn, T_odd hm] at hT
        have h2 := hT.mul_left' 2
        rw [Nat.mul_div_cancel' (by omega), Nat.mul_div_cancel' (by omega), ← pow_succ'] at h2
        have h3 : 3 * n ≡ 3 * m [MOD 2 ^ (k + 1)] := Nat.ModEq.add_right_cancel' 1 h2
        exact Nat.ModEq.cancel_left_of_coprime (Nat.Coprime.pow_left _ (by decide)) h3
  · intro h j hj
    rw [parity_iterate_mod (n := n) hj, parity_iterate_mod (n := m) hj, h]

/-- The parity vector of a residue class mod `2^k`. -/
def parityVector (k : ℕ) (r : Fin (2 ^ k)) : Fin k → Bool :=
  fun j => T^[j] r.val % 2 == 1

/-- Residues mod `2^k` biject with the parity vectors `{0,1}^k`. -/
theorem parityVector_bijective (k : ℕ) : Function.Bijective (parityVector k) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨fun r s hrs => ?_, by
    rw [Fintype.card_fin, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]⟩
  have hpar : ∀ j < k, T^[j] r.val % 2 = T^[j] s.val % 2 := by
    intro j hj
    have := congrFun hrs ⟨j, hj⟩
    simp only [parityVector] at this
    rcases Nat.mod_two_eq_zero_or_one (T^[j] r.val) with h | h <;>
      rcases Nat.mod_two_eq_zero_or_one (T^[j] s.val) with h' | h' <;> simp_all
  exact Fin.ext (Nat.ModEq.eq_of_lt_of_lt (parities_eq_iff_modEq.mp hpar) r.isLt s.isLt)

/-- `ρ_k` from a parity sequence `v`: `ρ_0 = 0`, `ρ_{k+1} = 3 ρ_k + 2^k` after an odd step. -/
def rho (v : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => if v k = 1 then 3 * rho v k + 2 ^ k else rho v k

/-- Affine form: `2^k T^k(n) = 3^{a_k} n + ρ_k`, with `ρ_k` a function of the parities only. -/
theorem affine_form (n k : ℕ) :
    2 ^ k * T^[k] n = 3 ^ oddCount T n k * n + rho (fun j => T^[j] n % 2) k := by
  induction k with
  | zero => simp [oddCount, rho]
  | succ k ih =>
    rw [Function.iterate_succ_apply', oddCount_succ, rho]
    rcases Nat.mod_two_eq_zero_or_one (T^[k] n) with h | h
    · have hd : T^[k] n / 2 * 2 = T^[k] n := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero h)
      rw [T_even h, h, ite_eq_right (by omega)]
      simp only [Nat.add_zero]
      calc 2 ^ (k + 1) * (T^[k] n / 2) = 2 ^ k * (T^[k] n / 2 * 2) := by ring
        _ = _ := by rw [hd, ih]
    · rw [T_odd h, h, ite_eq_left rfl, pow_succ, pow_succ]
      have h2 : (3 * T^[k] n + 1) / 2 * 2 = 3 * T^[k] n + 1 := Nat.div_mul_cancel (by omega)
      calc 2 ^ k * 2 * ((3 * T^[k] n + 1) / 2) = 2 ^ k * (3 * T^[k] n + 1) := by
            rw [Nat.mul_assoc, Nat.mul_comm 2, h2]
        _ = 3 * (2 ^ k * T^[k] n) + 2 ^ k := by ring
        _ = _ := by rw [ih]; ring

/-- The affine form's lower bound `3^{a_k} n ≤ 2^k T^k(n)`. -/
theorem three_pow_mul_le (n k : ℕ) : 3 ^ oddCount T n k * n ≤ 2 ^ k * T^[k] n := by
  rw [affine_form]; exact Nat.le_add_right _ _

end Collatz
