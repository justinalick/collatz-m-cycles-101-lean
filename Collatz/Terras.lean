import Collatz.ParityVector
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Tactic.NormNum

/-!
# Stopping times and Terras densities (brief, Sections 4 and 5)

* `coeff_le_stoppingTime`: κ(n) ≤ σ(n) (the coefficient stopping time exists and is at most σ).
* `FCount k` counts residues `r < 2^k` whose coefficient stopping time is `≤ k`, i.e.
  `3^{a_j(r)} < 2^j` for some `j ≤ k`; the Terras density is `F(k) = FCount k / 2^k`.
* Exact values `F(1), …, F(11)` and the `2^16` sieve count (2114 survivors), kernel-checked
  through the linear scanner `stopsWithin` and its soundness lemma.

The sieve survivors mod `2^k` are the residues whose first `k` parities do not force a drop
below the start, i.e. `2^k − FCount k`.
-/

namespace Collatz

/-- κ ≤ σ: if `T^k(n) < n` then `3^{a_j} < 2^j` for some `j ≤ k`, and the least such `j` is the
coefficient stopping time. -/
theorem coeff_le_stoppingTime {n k : ℕ} (h : IsFirst T (· < n) n k) :
    ∃ j ≤ k, IsFirstCoeff n j := by
  have hk : 3 ^ oddCount T n k < 2 ^ k := by
    have h1 := three_pow_mul_le n k
    have h2 : 2 ^ k * T^[k] n < 2 ^ k * n := Nat.mul_lt_mul_of_pos_left h.1 (by positivity)
    have hn : 0 < n := by have := h.1; simp only at this; omega
    exact Nat.lt_of_mul_lt_mul_right (a := n) (by linarith)
  have hex : ∃ j, 3 ^ oddCount T n j < 2 ^ j := ⟨k, hk⟩
  classical
  exact ⟨Nat.find hex, Nat.find_min' hex hk, Nat.find_spec hex,
    fun j hj => Nat.find_min hex hj⟩

/-- `stopsWithin f x a j`: scanning from index `j` with odd count `a` at value `x`, does
`3^a < 2^j` hold within `f` more steps? -/
def stopsWithin : ℕ → ℕ → ℕ → ℕ → Bool
  | 0, _, a, j => decide (3 ^ a < 2 ^ j)
  | f + 1, x, a, j => decide (3 ^ a < 2 ^ j) || stopsWithin f (T x) (a + x % 2) (j + 1)

theorem stopsWithin_iff (n f j : ℕ) :
    stopsWithin f (T^[j] n) (oddCount T n j) j = true ↔
      ∃ i, j ≤ i ∧ i ≤ j + f ∧ 3 ^ oddCount T n i < 2 ^ i := by
  induction f generalizing j with
  | zero =>
    simp only [stopsWithin, decide_eq_true_eq]
    exact ⟨fun h => ⟨j, le_rfl, le_rfl, h⟩, fun ⟨i, h1, h2, h⟩ => by
      rwa [show i = j by omega] at h⟩
  | succ f ih =>
    have step : stopsWithin f (T (T^[j] n)) (oddCount T n j + T^[j] n % 2) (j + 1) =
        stopsWithin f (T^[j + 1] n) (oddCount T n (j + 1)) (j + 1) := by
      rw [Function.iterate_succ_apply', oddCount_succ]
    simp only [stopsWithin, Bool.or_eq_true, decide_eq_true_eq, step, ih]
    constructor
    · rintro (h | ⟨i, h1, h2, h⟩)
      · exact ⟨j, le_rfl, by omega, h⟩
      · exact ⟨i, by omega, by omega, h⟩
    · rintro ⟨i, h1, h2, h⟩
      rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
      · exact Or.inl h
      · exact Or.inr ⟨i, by omega, by omega, h⟩

open Classical in
/-- The number of residues mod `2^k` with coefficient stopping time `≤ k`. -/
noncomputable def FCount (k : ℕ) : ℕ :=
  ((Finset.range (2 ^ k)).filter (fun r => ∃ j ≤ k, 3 ^ oddCount T r j < 2 ^ j)).card

theorem FCount_eq_scan (k : ℕ) :
    FCount k = ((Finset.range (2 ^ k)).filter (fun r => stopsWithin k r 0 0 = true)).card := by
  unfold FCount
  congr 1
  apply Finset.filter_congr
  intro r _
  have := stopsWithin_iff r k 0
  constructor
  · rintro ⟨i, hi, h⟩; exact this.mpr ⟨i, Nat.zero_le _, by omega, h⟩
  · intro hs; obtain ⟨i, -, hi, h⟩ := this.mp hs; exact ⟨i, by omega, h⟩

/-- The Terras density `F(k)`: the fraction of residues mod `2^k` with `κ ≤ k`. -/
noncomputable def F (k : ℕ) : ℚ := FCount k / 2 ^ k

set_option maxRecDepth 100000 in
/-- Exact Terras densities `F(1), …, F(11)`. The brief's Section 8 refutes the misquoted
`F(5) = 15/16` and `F(7) = 123/128`. -/
theorem F_values :
    F 1 = 1 / 2 ∧ F 2 = 3 / 4 ∧ F 3 = 3 / 4 ∧ F 4 = 13 / 16 ∧ F 5 = 7 / 8 ∧ F 6 = 7 / 8 ∧
      F 7 = 115 / 128 ∧ F 8 = 237 / 256 ∧ F 9 = 237 / 256 ∧ F 10 = 15 / 16 ∧
      F 11 = 15 / 16 := by
  have h : [FCount 1, FCount 2, FCount 3, FCount 4, FCount 5, FCount 6, FCount 7, FCount 8,
      FCount 9, FCount 10, FCount 11] = [1, 3, 6, 13, 28, 56, 115, 237, 474, 960, 1920] := by
    simp only [FCount_eq_scan]; decide +kernel
  simp only [List.cons.injEq, and_true] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  simp only [F, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
  norm_num

set_option maxRecDepth 100000 in
/-- The `2^16` sieve keeps 2114 residues (3.23 %): the strict-drop criterion gives 2114, not the
1720 quoted in the source material (brief, Section 10 item 2). -/
theorem sieve_2_16 : 2 ^ 16 - FCount 16 = 2114 := by
  rw [FCount_eq_scan]; decide +kernel

end Collatz
