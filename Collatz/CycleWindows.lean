import Collatz.Defs
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic

/-!
# Parity windows of an integer cycle are pairwise distinct (research note
`near_christoffel_cycles.md`, Theorem 4)

Terras (1976): the first `ℓ` parities of the `T`-orbit of `n` determine `n` modulo `2^ℓ`
(`modEq_of_parity_window`). Hence on a cycle of minimal period `p` all of whose elements are
below `2^ℓ`, two distinct positions have distinct parity windows of length `ℓ`
(`cycle_window_ne`), and the window map is injective on `range p` (`card_windows_eq`). This is
the injectivity half of the factor-complexity obstruction for cycles.
-/

namespace Collatz

/-- Terras' theorem, injectivity direction: equal parity windows of length `ℓ` force
congruence modulo `2^ℓ`. -/
theorem modEq_of_parity_window (ℓ : ℕ) : ∀ n n' : ℕ,
    (∀ t, t < ℓ → T^[t] n % 2 = T^[t] n' % 2) → n ≡ n' [MOD 2 ^ ℓ] := by
  induction ℓ with
  | zero =>
    intro n n' _
    show n % 2 ^ 0 = n' % 2 ^ 0
    simp [Nat.mod_one]
  | succ ℓ ih =>
    intro n n' h
    have h0 : n % 2 = n' % 2 := by simpa using h 0 (Nat.succ_pos ℓ)
    have h1 : ∀ t, t < ℓ → T^[t] (T n) % 2 = T^[t] (T n') % 2 := by
      intro t ht
      have := h (t + 1) (by omega)
      simpa [Function.iterate_succ_apply] using this
    have hT : T n ≡ T n' [MOD 2 ^ ℓ] := ih _ _ h1
    rw [pow_succ']
    rcases Nat.mod_two_eq_zero_or_one n with he | ho
    · have he' : n' % 2 = 0 := by omega
      rw [T_even he, T_even he'] at hT
      have hm : 2 * (n / 2) ≡ 2 * (n' / 2) [MOD 2 * 2 ^ ℓ] := Nat.ModEq.mul_left' 2 hT
      calc n = 2 * (n / 2) := by omega
        _ ≡ 2 * (n' / 2) [MOD 2 * 2 ^ ℓ] := hm
        _ = n' := by omega
    · have ho' : n' % 2 = 1 := by omega
      rw [T_odd ho, T_odd ho'] at hT
      have hn : (3 * n + 1) / 2 = 3 * (n / 2) + 2 := by omega
      have hn' : (3 * n' + 1) / 2 = 3 * (n' / 2) + 2 := by omega
      rw [hn, hn'] at hT
      have h3 : 3 * (n / 2) ≡ 3 * (n' / 2) [MOD 2 ^ ℓ] := Nat.ModEq.add_right_cancel' 2 hT
      have hcop : Nat.gcd (2 ^ ℓ) 3 = 1 :=
        Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_left ℓ (by norm_num))
      have hh : n / 2 ≡ n' / 2 [MOD 2 ^ ℓ] := Nat.ModEq.cancel_left_of_coprime hcop h3
      have hm : 2 * (n / 2) ≡ 2 * (n' / 2) [MOD 2 * 2 ^ ℓ] := Nat.ModEq.mul_left' 2 hh
      have hm1 : 2 * (n / 2) + 1 ≡ 2 * (n' / 2) + 1 [MOD 2 * 2 ^ ℓ] := Nat.ModEq.add_right 1 hm
      calc n = 2 * (n / 2) + 1 := by omega
        _ ≡ 2 * (n' / 2) + 1 [MOD 2 * 2 ^ ℓ] := hm1
        _ = n' := by omega

/-- Two coinciding elements of a `p`-cycle at positions `i < i'` give a return after `i' - i`
steps. -/
theorem iterate_sub_eq_self_of_eq {x p i i' : ℕ} (hcyc : T^[p] x = x) (hi' : i' < p)
    (hlt : i < i') (heq : T^[i] x = T^[i'] x) : T^[i' - i] x = x := by
  have hx : x = T^[p - i' + i] x := by
    calc x = T^[p] x := hcyc.symm
      _ = T^[(p - i') + i'] x := by rw [Nat.sub_add_cancel hi'.le]
      _ = T^[p - i'] (T^[i'] x) := Function.iterate_add_apply _ _ _ _
      _ = T^[p - i'] (T^[i] x) := by rw [heq]
      _ = T^[p - i' + i] x := (Function.iterate_add_apply _ _ _ _).symm
  have hsum : (i' - i) + (p - i' + i) = p := by omega
  calc T^[i' - i] x = T^[i' - i] (T^[p - i' + i] x) := by rw [← hx]
    _ = T^[(i' - i) + (p - i' + i)] x := (Function.iterate_add_apply _ _ _ _).symm
    _ = T^[p] x := by rw [hsum]
    _ = x := hcyc

/-- **Theorem 4 of the note.** On a cycle of minimal period `p` whose elements are all `< 2^ℓ`,
distinct positions `i ≠ i'` have distinct parity windows of length `ℓ`. -/
theorem cycle_window_ne {x p ℓ : ℕ} (hcyc : T^[p] x = x)
    (hmin : ∀ j, 0 < j → j < p → T^[j] x ≠ x)
    (hbound : ∀ i, i < p → T^[i] x < 2 ^ ℓ)
    {i i' : ℕ} (hi : i < p) (hi' : i' < p) (hne : i ≠ i') :
    ∃ t, t < ℓ ∧ T^[i + t] x % 2 ≠ T^[i' + t] x % 2 := by
  by_contra hcon
  push_neg at hcon
  have hw : ∀ t, t < ℓ → T^[t] (T^[i] x) % 2 = T^[t] (T^[i'] x) % 2 := by
    intro t ht
    have := hcon t ht
    rwa [Nat.add_comm i t, Nat.add_comm i' t, Function.iterate_add_apply,
      Function.iterate_add_apply] at this
  have hmod := modEq_of_parity_window ℓ _ _ hw
  have heq : T^[i] x = T^[i'] x := by
    have h1 := hbound i hi
    have h2 := hbound i' hi'
    unfold Nat.ModEq at hmod
    rwa [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at hmod
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · exact hmin (i' - i) (by omega) (by omega) (iterate_sub_eq_self_of_eq hcyc hi' hlt heq)
  · exact hmin (i - i') (by omega) (by omega) (iterate_sub_eq_self_of_eq hcyc hi hgt heq.symm)

/-- The parity window of length `ℓ` starting at position `i` of the orbit of `x`. -/
def window (x ℓ i : ℕ) : Fin ℓ → ℕ := fun t => T^[i + t] x % 2

/-- The window map is injective on the positions of the cycle, so the cycle word has exactly
`p` distinct windows of length `ℓ`. -/
theorem card_windows_eq {x p ℓ : ℕ} (hcyc : T^[p] x = x)
    (hmin : ∀ j, 0 < j → j < p → T^[j] x ≠ x)
    (hbound : ∀ i, i < p → T^[i] x < 2 ^ ℓ) :
    ((Finset.range p).image (window x ℓ)).card = p := by
  rw [Finset.card_image_of_injOn, Finset.card_range]
  intro i hi i' hi' h
  have hi₀ : i < p := by simpa using hi
  have hi'₀ : i' < p := by simpa using hi'
  by_contra hne
  obtain ⟨t, ht, hdiff⟩ := cycle_window_ne hcyc hmin hbound hi₀ hi'₀ hne
  apply hdiff
  have := congrFun h ⟨t, ht⟩
  simpa [window] using this

end Collatz
