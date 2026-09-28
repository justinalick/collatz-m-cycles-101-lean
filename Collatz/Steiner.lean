import Collatz.ParityVector
import Collatz.InverseTree

/-!
# Steiner's circuits (brief, Section 5 "Cycle results", item 3)

A circuit is a `T`-cycle made of `k` odd steps followed by `l` even steps. Steiner (1977) showed
the only one is `{1, 2}`. Proved here:

* `circuit_equation`: a circuit through `x` has `x + 1 = 2^k h` and
  `(2^{k+l} − 3^k) h = 2^l − 1` (stated without subtraction).
* `steiner_search`: for `k, l < 80` the only solution is `(k, l, h) = (1, 1, 1)`, checked by the
  kernel; hence every circuit with `k, l < 80` passes through 1.

Steiner's full theorem (all `k, l`) needs a Baker-type bound and is stated, not proved, in
`Statements.lean`.
-/

namespace Collatz

/-- `x` starts a circuit: `k ≥ 1` odd steps, then `l ≥ 1` even steps, back to `x`. -/
def IsCircuit (x k l : ℕ) : Prop :=
  0 < k ∧ 0 < l ∧ (∀ j < k, T^[j] x % 2 = 1) ∧ (∀ j < l, T^[j + k] x % 2 = 0) ∧
    T^[l + k] x = x

/-- `l` even steps divide by `2^l`. -/
theorem two_pow_mul_iterate_of_even {y l : ℕ} (h : ∀ j < l, T^[j] y % 2 = 0) :
    2 ^ l * T^[l] y = y := by
  induction l with
  | zero => simp
  | succ l ih =>
    have hl := h l (by omega)
    rw [Function.iterate_succ_apply', T_even hl, pow_succ, Nat.mul_assoc,
      Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hl), ih fun j hj => h j (by omega)]

theorem circuit_equation {x k l : ℕ} (hc : IsCircuit x k l) :
    ∃ h, 0 < h ∧ x + 1 = 2 ^ k * h ∧ 2 ^ (k + l) * h + 1 = 3 ^ k * h + 2 ^ l := by
  obtain ⟨hk, hl, hodd, heven, hcyc⟩ := hc
  -- `x` shares its first `k` parities with `2^k − 1`, so `x ≡ −1 (mod 2^k)`.
  have hmod : x ≡ 2 ^ k * 1 - 1 [MOD 2 ^ k] :=
    parities_eq_iff_modEq.mp fun j hj => by rw [hodd j hj, barina_odd hj le_rfl]
  have hpos : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have hx : x % 2 ^ k = 2 ^ k - 1 := by
    have := hmod; unfold Nat.ModEq at this
    rw [this, Nat.mul_one, Nat.mod_eq_of_lt (by omega)]
  obtain ⟨h, hh⟩ : ∃ h, h = x / 2 ^ k + 1 := ⟨_, rfl⟩
  have hxh : x + 1 = 2 ^ k * h := by
    have hd := Nat.div_add_mod x (2 ^ k)
    rw [hx] at hd
    rw [hh, Nat.mul_add, Nat.mul_one]
    generalize 2 ^ k = P at hd hpos ⊢
    omega
  have hh1 : 1 ≤ h := by rw [hh]; exact Nat.succ_pos _
  refine ⟨h, hh1, hxh, ?_⟩
  -- `k` odd steps take `2^k h − 1` to `3^k h − 1`; `l` halvings bring it back to `x`.
  have hk' : T^[k] x = 3 ^ k * h - 1 := by
    rw [show x = 2 ^ k * h - 1 by omega, barina_identity k hh1]
  have hback := two_pow_mul_iterate_of_even (y := T^[k] x) (l := l)
    fun j hj => by rw [← Function.iterate_add_apply]; exact heven j hj
  rw [← Function.iterate_add_apply, hcyc, hk'] at hback
  have h3 : 1 ≤ 3 ^ k * h := Nat.mul_pos (pow_pos (by norm_num) k) hh1
  have hA : 2 ^ (k + l) * h = 2 ^ l * (2 ^ k * h) := by ring
  have hB : 2 ^ l * (2 ^ k * h) = 2 ^ l * x + 2 ^ l := by rw [← hxh]; ring
  omega

/-- Kernel-checkable form of the Steiner search for one `(k, l)`. -/
def steinerOK (k l : ℕ) : Bool :=
  k == 0 || l == 0 ||
    if 3 ^ k < 2 ^ (k + l) then (2 ^ l - 1) % (2 ^ (k + l) - 3 ^ k) != 0 || (k == 1 && l == 1)
    else true

theorem steiner_of_ok {k l h : ℕ} (hk : 0 < k) (hl : 0 < l) (hok : steinerOK k l = true)
    (heq : 2 ^ (k + l) * h + 1 = 3 ^ k * h + 2 ^ l) : k = 1 ∧ l = 1 ∧ h = 1 := by
  unfold steinerOK at hok
  simp only [Bool.or_eq_true, beq_iff_eq, show k ≠ 0 by omega, show l ≠ 0 by omega,
    false_or] at hok
  have h2l : 2 ≤ 2 ^ l := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ l := Nat.pow_le_pow_right (by norm_num) hl
  split_ifs at hok with hlt
  · have hle : 3 ^ k * h ≤ 2 ^ (k + l) * h := Nat.mul_le_mul_right _ hlt.le
    have hd : (2 ^ (k + l) - 3 ^ k) * h = 2 ^ l - 1 := by rw [Nat.sub_mul]; omega
    have hdiv : (2 ^ l - 1) % (2 ^ (k + l) - 3 ^ k) = 0 := by
      rw [← hd]; exact Nat.mul_mod_right _ _
    simp only [hdiv, bne_self_eq_false, Bool.false_or, Bool.and_eq_true, beq_iff_eq] at hok
    obtain ⟨rfl, rfl⟩ := hok
    norm_num at heq
    exact ⟨rfl, rfl, by omega⟩
  · have hge : 2 ^ (k + l) * h ≤ 3 ^ k * h := Nat.mul_le_mul_right _ (by omega)
    omega

/-- Steiner's search: for `k, l < 80` the circuit equation forces `(k, l, h) = (1, 1, 1)`. -/
theorem steiner_search : ∀ k < 80, ∀ l < 80, 0 < k → 0 < l → ∀ h,
    2 ^ (k + l) * h + 1 = 3 ^ k * h + 2 ^ l → k = 1 ∧ l = 1 ∧ h = 1 := by
  have hall : ∀ k < 80, ∀ l < 80, steinerOK k l = true := by decide +kernel
  exact fun k hk l hl hk0 hl0 h heq => steiner_of_ok hk0 hl0 (hall k hk l hl) heq

/-- Every circuit with `k, l < 80` passes through 1 (it is the trivial cycle `{1, 2}`). -/
theorem circuit_trivial {x k l : ℕ} (hc : IsCircuit x k l) (hk : k < 80) (hl : l < 80) :
    x = 1 := by
  obtain ⟨h, -, hxh, heq⟩ := circuit_equation hc
  obtain ⟨rfl, -, rfl⟩ := steiner_search k hk l hl hc.1 hc.2.1 h heq
  omega

end Collatz
