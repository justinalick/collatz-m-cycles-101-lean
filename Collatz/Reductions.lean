import Collatz.Records
import Collatz.Cycles
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.Cofinite

/-!
# Reductions (brief, Sections 3 and 4)

* `verified_iff`: "every `1 < n < N` has an iterate below `n`" (convergence verification) is
  equivalent to "every `0 < n < N` reaches 1", for any positivity-preserving map. Instances for
  `C` and `T` follow.
* `conjecture_iff`: the conjecture holds iff no positive orbit tends to infinity and every
  positive `C`-cycle lies in `{1, 2, 4}`.
-/

namespace Collatz

open Filter

theorem C_pos {n : ℕ} (hn : 0 < n) : 0 < C n := by unfold C; split_ifs <;> omega

theorem iterate_pos {f : ℕ → ℕ} (hf : ∀ n, 0 < n → 0 < f n) {n : ℕ} (hn : 0 < n) (k : ℕ) :
    0 < f^[k] n := by
  induction k with
  | zero => exact hn
  | succ k ih => rw [Function.iterate_succ_apply']; exact hf _ ih

/-- Convergence verification to `N` is equivalent to "every `0 < n < N` reaches 1". -/
theorem verified_iff {f : ℕ → ℕ} (hf : ∀ n, 0 < n → 0 < f n) (N : ℕ) :
    (∀ n, 1 < n → n < N → ∃ k, f^[k] n < n) ↔ (∀ n, 0 < n → n < N → Reaches f n 1) := by
  constructor
  · intro h n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro hn hnN
      rcases Nat.lt_or_ge 1 n with h1 | h1
      · obtain ⟨k, hk⟩ := h n h1 hnN
        obtain ⟨j, hj⟩ := ih _ hk (iterate_pos hf hn k) (by omega)
        exact ⟨j + k, by rw [Function.iterate_add_apply, hj]⟩
      · exact ⟨0, by simp; omega⟩
  · intro h n h1 hnN
    obtain ⟨k, hk⟩ := h n (by omega) hnN
    exact ⟨k, by omega⟩

theorem verified_iff_C (N : ℕ) :
    (∀ n, 1 < n → n < N → ∃ k, C^[k] n < n) ↔ (∀ n, 0 < n → n < N → Reaches C n 1) :=
  verified_iff (fun _ => C_pos) N

theorem verified_iff_T (N : ℕ) :
    (∀ n, 1 < n → n < N → ∃ k, T^[k] n < n) ↔ (∀ n, 0 < n → n < N → Reaches T n 1) :=
  verified_iff (fun _ => T_pos) N

theorem C_iterate_one_mem (j : ℕ) : C^[j] 1 = 1 ∨ C^[j] 1 = 2 ∨ C^[j] 1 = 4 := by
  have := C_iterate_one_le_four j; omega

/-- A start that reaches 1 stays at most 4 from then on. -/
theorem iterate_le_four_of_reaches {n k j : ℕ} (hk : C^[k] n = 1) (hj : k ≤ j) : C^[j] n ≤ 4 := by
  obtain ⟨t, rfl⟩ : ∃ t, j = t + k := ⟨j - k, by omega⟩
  rw [Function.iterate_add_apply, hk]; exact (C_iterate_one_le_four t).1

/-- A periodic point is reached again after any number of steps, rounded up to the period. -/
theorem periodic_reached {f : ℕ → ℕ} {x p : ℕ} (hp : 0 < p) (h : f^[p] x = x) (i : ℕ) :
    ∃ t, i ≤ t ∧ f^[t] x = x := by
  refine ⟨p * i, Nat.le_mul_of_pos_left _ hp, ?_⟩
  induction i with
  | zero => rfl
  | succ i ih => rw [Nat.mul_succ, Function.iterate_add_apply, h, ih]

/-- The conjecture holds iff there is no divergent orbit and no nontrivial positive cycle. -/
theorem conjecture_iff :
    CollatzConjecture ↔
      (∀ n, 0 < n → ¬ Tendsto (fun k => C^[k] n) atTop atTop) ∧
        (∀ x p, 0 < x → 0 < p → C^[p] x = x → x = 1 ∨ x = 2 ∨ x = 4) := by
  constructor
  · intro hc
    refine ⟨fun n hn hdiv => ?_, fun x p hx hp hcyc => ?_⟩
    · obtain ⟨k, hk⟩ := hc n hn
      obtain ⟨K, hK⟩ := eventually_atTop.mp (tendsto_atTop.mp hdiv 5)
      have := hK (max K k) (le_max_left _ _)
      have := iterate_le_four_of_reaches hk (le_max_right K k)
      omega
    · obtain ⟨k, hk⟩ := hc x hx
      obtain ⟨t, hkt, ht⟩ := periodic_reached hp hcyc k
      obtain ⟨s, rfl⟩ : ∃ s, t = s + k := ⟨t - k, by omega⟩
      rw [Function.iterate_add_apply, hk] at ht
      rw [← ht]; exact C_iterate_one_mem s
  · rintro ⟨hdiv, hcyc⟩ n hn
    by_contra hne
    by_cases hinj : Function.Injective (fun k => C^[k] n)
    · exact hdiv n hn hinj.nat_tendsto_atTop
    · simp only [Function.Injective, not_forall] at hinj
      obtain ⟨i, j, hij, hne'⟩ := hinj
      wlog hlt : i < j generalizing i j
      · exact this j i hij.symm (Ne.symm hne') (by omega)
      have hy := iterate_pos (fun _ => C_pos) hn i
      have hper : C^[j - i] (C^[i] n) = C^[i] n := by
        rw [← Function.iterate_add_apply, Nat.sub_add_cancel hlt.le]; exact hij.symm
      apply hne
      rcases hcyc _ _ hy (by omega) hper with h1 | h2 | h4
      · exact ⟨i, h1⟩
      · exact ⟨1 + i, by rw [Function.iterate_add_apply, h2]; rfl⟩
      · exact ⟨2 + i, by rw [Function.iterate_add_apply, h4]; rfl⟩

end Collatz
