import Collatz.Checker

/-!
# Records (brief, Section 4)

A delay, path or glide record is a start whose statistic beats every smaller positive start.
Each definition quantifies over whole orbits; `Oracles*.lean` discharges instances by kernel
computation through the certificates below.
-/

namespace Collatz

/-- `n` is a delay record with delay `d`. -/
def IsDelayRecord (n d : ℕ) : Prop :=
  IsFirst C (· = 1) n d ∧ ∀ m, 0 < m → m < n → ∃ j < d, C^[j] m = 1

/-- `n` is a path record with peak `p`: `p` is the maximum of the whole `C`-orbit of `n` and
exceeds every value in the orbit of every smaller positive start. -/
def IsPathRecord (n p : ℕ) : Prop :=
  (∃ j, C^[j] n = p) ∧ (∀ j, C^[j] n ≤ p) ∧ ∀ m, 0 < m → m < n → ∀ j, C^[j] m < p

/-- `n` is a glide record with glide `g`. -/
def IsGlideRecord (n g : ℕ) : Prop :=
  IsFirst C (· < n) n g ∧ ∀ m, 1 < m → m < n → ∃ j < g, C^[j] m < m

/-- Once at 1, the `C`-orbit stays in the trivial cycle `{1, 4, 2}`. -/
theorem C_iterate_one_le_four (j : ℕ) : C^[j] 1 ≤ 4 ∧ 0 < C^[j] 1 ∧ C^[j] 1 ≠ 3 := by
  induction j with
  | zero => decide
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    obtain ⟨h4, h0, h3⟩ := ih
    interval_cases h : C^[j] 1 <;> first | decide | exact absurd rfl h3

/-- If the orbit of `m` hits 1 within `F` steps and its first `F` terms are `< p` with `4 < p`,
the whole orbit is `< p`. -/
theorem forall_lt_of_orbit {m F p : ℕ} (hp : 4 < p)
    (h : 1 ∈ orbit C m F ∧ (orbit C m F).all (fun x => decide (x < p)) = true) :
    ∀ j, C^[j] m < p := by
  obtain ⟨h1, hall⟩ := h
  obtain ⟨i, hi, hCi⟩ := mem_orbit.mp h1
  intro j
  rcases lt_or_ge j F with hj | hj
  · exact forall_lt_of_all_orbit hall j hj
  · obtain ⟨t, rfl⟩ : ∃ t, j = t + i := ⟨j - i, by omega⟩
    rw [Function.iterate_add_apply, hCi]
    have := (C_iterate_one_le_four t).1; omega

/-- Kernel-checkable certificate for the "all smaller starts" half of a path record. -/
theorem path_smaller_of_check {n F p : ℕ} (hp : 4 < p)
    (h : (List.range n).all
      (fun m => decide (m = 0 ∨ (1 ∈ orbit C m F ∧ (orbit C m F).all (fun x => decide (x < p)))))
      = true) :
    ∀ m, 0 < m → m < n → ∀ j, C^[j] m < p := by
  intro m hm hmn
  rw [List.all_eq_true] at h
  have := h m (List.mem_range.mpr hmn)
  simp only [decide_eq_true_eq] at this
  exact forall_lt_of_orbit hp (this.resolve_left (by omega))

/-- Kernel-checkable certificate for the "all smaller starts" half of a delay record. -/
theorem delay_smaller_of_check {n d : ℕ}
    (h : (List.range n).all (fun m => decide (m = 0 ∨ 1 ∈ orbit C m d)) = true) :
    ∀ m, 0 < m → m < n → ∃ j < d, C^[j] m = 1 := by
  intro m hm hmn
  rw [List.all_eq_true] at h
  have := h m (List.mem_range.mpr hmn)
  simp only [decide_eq_true_eq] at this
  exact mem_orbit.mp (this.resolve_left (by omega))

/-- Kernel-checkable certificate for the "all smaller starts" half of a glide record. -/
theorem glide_smaller_of_check {n g : ℕ}
    (h : (List.range n).all
      (fun m => decide (m ≤ 1 ∨ (orbit C m g).any (fun x => decide (x < m)))) = true) :
    ∀ m, 1 < m → m < n → ∃ j < g, C^[j] m < m := by
  intro m hm hmn
  rw [List.all_eq_true] at h
  have := h m (List.mem_range.mpr hmn)
  simp only [decide_eq_true_eq, List.any_eq_true] at this
  obtain ⟨x, hx, hxm⟩ := this.resolve_left (by omega)
  obtain ⟨j, hj, rfl⟩ := mem_orbit.mp hx
  exact ⟨j, hj, hxm⟩

/-- The peak of a start that reaches 1 bounds its whole orbit. -/
theorem forall_le_of_peak {n D p i : ℕ} (hD : C^[D] n = 1) (hp : IsPeak C n D p i) (h4 : 4 ≤ p) :
    ∀ j, C^[j] n ≤ p := by
  intro j
  rcases le_or_gt j D with hj | hj
  · exact hp.2.2 j hj
  · obtain ⟨t, rfl⟩ : ∃ t, j = t + D := ⟨j - D, by omega⟩
    rw [Function.iterate_add_apply, hD]
    have := (C_iterate_one_le_four t).1; omega

end Collatz
