import Collatz.Defs

/-!
# Reflective checkers for orbit facts

`orbit f n k` is the list `[n, f n, …, f^[k-1] n]`, built in one pass. The lemmas below turn
`List.all` checks over it into the `IsFirst` / `IsPeak` / `oddCount` statements of `Defs`, so
`decide +kernel` evaluates each numeric claim in linear time inside the kernel. No
`native_decide` is used anywhere.
-/

namespace Collatz

/-- The first `k` terms of the `f`-orbit of `n`. -/
def orbit (f : ℕ → ℕ) : ℕ → ℕ → List ℕ
  | _, 0 => []
  | n, k + 1 => n :: orbit f (f n) k

theorem length_orbit (f : ℕ → ℕ) (n k : ℕ) : (orbit f n k).length = k := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih => simp [orbit, ih]

theorem mem_orbit {f : ℕ → ℕ} {n k x : ℕ} : x ∈ orbit f n k ↔ ∃ j < k, f^[j] n = x := by
  induction k generalizing n with
  | zero => simp [orbit]
  | succ k ih =>
    simp only [orbit, List.mem_cons, ih]
    constructor
    · rintro (rfl | ⟨j, hj, rfl⟩)
      · exact ⟨0, k.succ_pos, rfl⟩
      · exact ⟨j + 1, by omega, by rw [Function.iterate_succ_apply]⟩
    · rintro ⟨_ | j, hj, rfl⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨j, by omega, by rw [Function.iterate_succ_apply]⟩

theorem orbit_succ_eq_append (f : ℕ → ℕ) (n k : ℕ) :
    orbit f n (k + 1) = orbit f n k ++ [f^[k] n] := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih =>
    rw [orbit, ih, orbit, Function.iterate_succ_apply]; rfl

theorem forall_lt_of_all_orbit {f : ℕ → ℕ} {p : ℕ → Prop} [DecidablePred p] {n k : ℕ}
    (h : (orbit f n k).all (fun x => decide (p x)) = true) : ∀ j < k, p (f^[j] n) := by
  intro j hj
  rw [List.all_eq_true] at h
  simpa using h _ (mem_orbit.mpr ⟨j, hj, rfl⟩)

/-- Certificate for `IsFirst`: the predicate holds at `k` and fails on the first `k` terms. -/
theorem isFirst_of_check {f : ℕ → ℕ} {p : ℕ → Prop} [DecidablePred p] {n k : ℕ}
    (hk : p (f^[k] n)) (h : (orbit f n k).all (fun x => decide ¬ p x) = true) :
    IsFirst f p n k :=
  ⟨hk, forall_lt_of_all_orbit h⟩

/-- Certificate for `IsPeak`. -/
theorem isPeak_of_check {f : ℕ → ℕ} {n k m i : ℕ} (hi : i ≤ k) (hm : f^[i] n = m)
    (h : (orbit f n (k + 1)).all (fun x => decide (x ≤ m)) = true) : IsPeak f n k m i :=
  ⟨hi, hm, fun j hj => forall_lt_of_all_orbit h j (by omega)⟩

theorem oddCount_eq_sum (f : ℕ → ℕ) (n k : ℕ) :
    oddCount f n k = ((orbit f n k).map (· % 2)).sum := by
  induction k with
  | zero => rfl
  | succ k ih => rw [oddCount_succ, orbit_succ_eq_append, List.map_append, List.sum_append, ih]; simp

/-- Certificate for "the `f`-orbit of `n` avoids `x` in its first `k` terms". -/
theorem not_mem_of_check {f : ℕ → ℕ} {n k x : ℕ}
    (h : (orbit f n k).all (fun y => decide (y ≠ x)) = true) : ∀ j < k, f^[j] n ≠ x :=
  forall_lt_of_all_orbit h

end Collatz
