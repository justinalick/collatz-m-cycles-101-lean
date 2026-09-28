import Collatz.CycleWindows
import Collatz.SharpCycleBound
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Data.Finset.Sort
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.Jensen

/-!
# The harmonic-residue bound (research note `near_christoffel_cycles.md`, Section 9, Theorem 10)

For a `T`-cycle of minimal period `p` with `K` odd elements, the product identity gives
`3 Λ = 3 (p log 2 − K log 3) = 3 ∑ log(1 + 1/(3y)) ≤ ∑ 1/y`, the sums over the odd elements `y`
(`three_lambda_le_sum_inv`, from `Esum_cycle`). Terras' theorem (`modEq_of_parity_window`) makes
the odd elements that share a parity window of length `ℓ` pairwise congruent modulo `2^ℓ`; they are
pairwise distinct because the period is minimal, so in increasing order they are at least `2^ℓ`
apart and the `j`-th one is at least `m₀ + j 2^ℓ`, where `m₀` is a lower bound for the cycle.
A class of `N` such elements therefore contributes at most `1/m₀ + H_{N−1}/2^ℓ ≤
1/m₀ + (1 + log N)/2^ℓ` to `∑ 1/y` (`sum_inv_le_of_pairwise_modEq`, via Mathlib's
`harmonic_le_one_add_log`). Summing over the `C` window classes at odd positions,

  `3 Λ ≤ C/m₀ + ∑_c (1 + log N_c)/2^ℓ ≤ C/m₀ + C (1 + log K)/2^ℓ`

(`harmonic_residue_bound`, `harmonic_residue_bound_crude`). No upper bound on the cycle elements
is assumed anywhere.
-/

namespace Collatz

open Finset

/-- The odd positions among the first `p` steps of the orbit of `x`. -/
def oddPos (x p : ℕ) : Finset ℕ := (range p).filter (fun i => T^[i] x % 2 = 1)

/-- The parity windows of length `ℓ` that start at odd positions. -/
def oddWindows (x p ℓ : ℕ) : Finset (Fin ℓ → ℕ) := (oddPos x p).image (window x ℓ)

theorem oddCount_eq_sum_range (f : ℕ → ℕ) (n k : ℕ) :
    oddCount f n k = ∑ i ∈ range k, f^[i] n % 2 := by
  induction k with
  | zero => simp [oddCount]
  | succ k ih => rw [oddCount_succ, sum_range_succ, ih]

theorem card_oddPos (x p : ℕ) : (oddPos x p).card = oddCount T x p := by
  rw [oddPos, card_filter, oddCount_eq_sum_range]
  refine sum_congr rfl (fun i _ => ?_)
  rcases Nat.mod_two_eq_zero_or_one (T^[i] x) with h | h <;> simp [h]

/-- The size identity in reciprocal form: `3 Λ ≤ ∑ 1/y` over the odd elements of a cycle. -/
theorem three_lambda_le_sum_inv {x p : ℕ} (hx : 0 < x) (hcyc : T^[p] x = x) :
    3 * ((p : ℝ) * Real.log 2 - (oddCount T x p : ℝ) * Real.log 3) ≤
      ∑ i ∈ oddPos x p, (1 : ℝ) / ((T^[i] x : ℕ) : ℝ) := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog' : Real.log 2 ≠ 0 := hlog.ne'
  have hθlog : Real.logb 2 3 * Real.log 2 = Real.log 3 := by
    rw [Real.logb]; field_simp
  have hΛE : (p : ℝ) * Real.log 2 - (oddCount T x p : ℝ) * Real.log 3 =
      Esum x p * Real.log 2 := by
    rw [Esum_cycle hx hcyc, sub_mul, mul_assoc, hθlog]
  have hEs : Esum x p * Real.log 2 = ∑ i ∈ oddPos x p, eps x i * Real.log 2 := by
    rw [Esum, oddPos, sum_filter, sum_mul]
    refine sum_congr rfl (fun i _ => ?_)
    split_ifs <;> simp
  have hterm : ∀ i ∈ oddPos x p,
      3 * (eps x i * Real.log 2) ≤ (1 : ℝ) / ((T^[i] x : ℕ) : ℝ) := by
    intro i _
    have h1 : eps x i * Real.log 2 = Real.log (1 + 1 / (3 * ((T^[i] x : ℕ) : ℝ))) := by
      rw [eps, Real.logb]; field_simp
    have hu : (0 : ℝ) ≤ 1 / (3 * ((T^[i] x : ℕ) : ℝ)) := by positivity
    have h2 := Real.log_le_sub_one_of_pos
      (by linarith : (0 : ℝ) < 1 + 1 / (3 * ((T^[i] x : ℕ) : ℝ)))
    have h3 : 3 * (1 / (3 * ((T^[i] x : ℕ) : ℝ))) = (1 : ℝ) / ((T^[i] x : ℕ) : ℝ) := by ring
    rw [h1]
    linarith
  have hsum : 3 * (Esum x p * Real.log 2) ≤ ∑ i ∈ oddPos x p, (1 : ℝ) / ((T^[i] x : ℕ) : ℝ) := by
    rw [hEs, mul_sum]
    exact sum_le_sum hterm
  rw [hΛE]
  exact hsum

/-- Naturals that are pairwise congruent modulo `M > 0` and at least `m₀ > 0`: in increasing
order they are at least `M` apart, so the sum of their reciprocals is at most
`1/m₀ + H_{N−1}/M ≤ 1/m₀ + (1 + log N)/M`. -/
theorem sum_inv_le_of_pairwise_modEq {S : Finset ℕ} {M m₀ : ℕ} (hM : 0 < M) (hm₀ : 0 < m₀)
    (hlow : ∀ y ∈ S, m₀ ≤ y) (hcong : ∀ y ∈ S, ∀ y' ∈ S, y ≡ y' [MOD M]) :
    ∑ y ∈ S, (1 : ℝ) / (y : ℝ) ≤ 1 / (m₀ : ℝ) + (1 + Real.log (S.card : ℝ)) / (M : ℝ) := by
  obtain ⟨n, hn⟩ : ∃ n, S.card = n := ⟨_, rfl⟩
  have hm₀' : (0 : ℝ) < m₀ := by exact_mod_cast hm₀
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  -- the increasing enumeration of `S`
  have hmem : ∀ j : Fin n, S.orderEmbOfFin hn j ∈ S := fun j => orderEmbOfFin_mem S hn j
  have hgap : ∀ k (hk : k < n), m₀ + k * M ≤ S.orderEmbOfFin hn ⟨k, hk⟩ := by
    intro k
    induction k with
    | zero =>
      intro hk
      simpa using hlow _ (hmem ⟨0, hk⟩)
    | succ k ih =>
      intro hk
      have hk' : k < n := by omega
      have h1 := ih hk'
      have hlt : S.orderEmbOfFin hn ⟨k, hk'⟩ < S.orderEmbOfFin hn ⟨k + 1, hk⟩ :=
        (S.orderEmbOfFin hn).strictMono (Fin.mk_lt_mk.mpr (by omega))
      have hc : S.orderEmbOfFin hn ⟨k, hk'⟩ ≡ S.orderEmbOfFin hn ⟨k + 1, hk⟩ [MOD M] :=
        hcong _ (hmem ⟨k, hk'⟩) _ (hmem ⟨k + 1, hk⟩)
      have hdvd : M ∣ S.orderEmbOfFin hn ⟨k + 1, hk⟩ - S.orderEmbOfFin hn ⟨k, hk'⟩ :=
        (Nat.modEq_iff_dvd' hlt.le).mp hc
      have hge : M ≤ S.orderEmbOfFin hn ⟨k + 1, hk⟩ - S.orderEmbOfFin hn ⟨k, hk'⟩ :=
        Nat.le_of_dvd (by omega) hdvd
      have hmul : m₀ + (k + 1) * M = m₀ + k * M + M := by ring
      omega
  have hgap' : ∀ j : Fin n, m₀ + (j : ℕ) * M ≤ S.orderEmbOfFin hn j := fun j => hgap j.1 j.2
  -- reindex the sum by the enumeration
  have hbij : ∑ y ∈ S, (1 : ℝ) / (y : ℝ) =
      ∑ j : Fin n, (1 : ℝ) / ((S.orderEmbOfFin hn j : ℕ) : ℝ) := by
    symm
    refine sum_bij (fun j _ => S.orderEmbOfFin hn j) (fun j _ => hmem j) ?_ ?_ (fun j _ => rfl)
    · intro j₁ _ j₂ _ h
      exact (S.orderEmbOfFin hn).strictMono.injective h
    · intro y hy
      have hy' : y ∈ Set.range (S.orderEmbOfFin hn) := by
        rw [range_orderEmbOfFin]; exact hy
      obtain ⟨j, hj⟩ := hy'
      exact ⟨j, mem_univ _, hj⟩
  have hterm : ∀ j : Fin n, (1 : ℝ) / ((S.orderEmbOfFin hn j : ℕ) : ℝ) ≤
      1 / ((m₀ : ℝ) + ((j : ℕ) : ℝ) * (M : ℝ)) := by
    intro j
    have hpos : (0 : ℝ) < (m₀ : ℝ) + ((j : ℕ) : ℝ) * (M : ℝ) :=
      add_pos_of_pos_of_nonneg hm₀' (by positivity)
    apply one_div_le_one_div_of_le hpos
    exact_mod_cast hgap' j
  have hsum1 : ∑ j : Fin n, (1 : ℝ) / ((S.orderEmbOfFin hn j : ℕ) : ℝ) ≤
      ∑ j : Fin n, 1 / ((m₀ : ℝ) + ((j : ℕ) : ℝ) * (M : ℝ)) :=
    sum_le_sum (fun j _ => hterm j)
  have hsum2 : ∑ j : Fin n, 1 / ((m₀ : ℝ) + ((j : ℕ) : ℝ) * (M : ℝ)) =
      ∑ j ∈ range n, 1 / ((m₀ : ℝ) + (j : ℝ) * (M : ℝ)) :=
    Fin.sum_univ_eq_sum_range (fun j : ℕ => 1 / ((m₀ : ℝ) + (j : ℝ) * (M : ℝ))) n
  -- the arithmetic-progression sum against the harmonic numbers
  have hrange : ∑ j ∈ range n, 1 / ((m₀ : ℝ) + (j : ℝ) * (M : ℝ)) ≤
      1 / (m₀ : ℝ) + (1 + Real.log (n : ℝ)) / (M : ℝ) := by
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0
      simp only [range_zero, sum_empty, Nat.cast_zero, Real.log_zero, add_zero]
      positivity
    · obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      rw [sum_range_succ']
      have hzero : 1 / ((m₀ : ℝ) + ((0 : ℕ) : ℝ) * (M : ℝ)) = 1 / (m₀ : ℝ) := by simp
      have hterm2 : ∀ j ∈ range n', 1 / ((m₀ : ℝ) + ((j + 1 : ℕ) : ℝ) * (M : ℝ)) ≤
          (1 / (M : ℝ)) * (1 / ((j : ℝ) + 1)) := by
        intro j _
        have hj : (0 : ℝ) < ((j + 1 : ℕ) : ℝ) * (M : ℝ) :=
          mul_pos (by exact_mod_cast Nat.succ_pos j) hM'
        have h1 : 1 / ((m₀ : ℝ) + ((j + 1 : ℕ) : ℝ) * (M : ℝ)) ≤
            1 / (((j + 1 : ℕ) : ℝ) * (M : ℝ)) :=
          one_div_le_one_div_of_le hj (le_add_of_nonneg_left hm₀'.le)
        have h2 : 1 / (((j + 1 : ℕ) : ℝ) * (M : ℝ)) = (1 / (M : ℝ)) * (1 / ((j : ℝ) + 1)) := by
          rw [one_div_mul_one_div]
          congr 1
          push_cast
          try ring
        rw [← h2]; exact h1
      have hsum3 : ∑ j ∈ range n', 1 / ((m₀ : ℝ) + ((j + 1 : ℕ) : ℝ) * (M : ℝ)) ≤
          (1 / (M : ℝ)) * ∑ j ∈ range n', 1 / ((j : ℝ) + 1) := by
        rw [mul_sum]; exact sum_le_sum hterm2
      have hharm : ∑ j ∈ range n', 1 / ((j : ℝ) + 1) = (harmonic n' : ℝ) := by
        simp [harmonic, one_div]
      have hbound : (harmonic n' : ℝ) ≤ 1 + Real.log (n' : ℝ) := harmonic_le_one_add_log n'
      have hlogmono : Real.log (n' : ℝ) ≤ Real.log ((n' + 1 : ℕ) : ℝ) := by
        rcases Nat.eq_zero_or_pos n' with h0 | hpos'
        · subst h0; simp
        · exact Real.log_le_log (by exact_mod_cast hpos') (by exact_mod_cast Nat.le_succ n')
      have hfinal : (1 / (M : ℝ)) * ∑ j ∈ range n', 1 / ((j : ℝ) + 1) ≤
          (1 + Real.log ((n' + 1 : ℕ) : ℝ)) / (M : ℝ) := by
        rw [hharm]
        have hM1 : (0 : ℝ) ≤ 1 / (M : ℝ) := by positivity
        calc (1 / (M : ℝ)) * (harmonic n' : ℝ)
            ≤ (1 / (M : ℝ)) * (1 + Real.log ((n' + 1 : ℕ) : ℝ)) :=
              mul_le_mul_of_nonneg_left (by linarith) hM1
          _ = (1 + Real.log ((n' + 1 : ℕ) : ℝ)) / (M : ℝ) := by ring
      rw [hzero]
      linarith [hsum3, hfinal]
  rw [hn]
  calc ∑ y ∈ S, (1 : ℝ) / (y : ℝ)
      = ∑ j : Fin n, (1 : ℝ) / ((S.orderEmbOfFin hn j : ℕ) : ℝ) := hbij
    _ ≤ ∑ j : Fin n, 1 / ((m₀ : ℝ) + ((j : ℕ) : ℝ) * (M : ℝ)) := hsum1
    _ = ∑ j ∈ range n, 1 / ((m₀ : ℝ) + (j : ℝ) * (M : ℝ)) := hsum2
    _ ≤ 1 / (m₀ : ℝ) + (1 + Real.log (n : ℝ)) / (M : ℝ) := hrange

/-- One window class of a cycle: positions `F ⊆ [0, p)` with a common parity window of length `ℓ`.
The elements there are pairwise distinct (minimal period) and pairwise congruent modulo `2^ℓ`
(Terras), so their reciprocals sum to at most `1/m₀ + (1 + log |F|)/2^ℓ`. -/
theorem class_sum_le {x p ℓ m₀ : ℕ} (hcyc : T^[p] x = x)
    (hmin : ∀ j, 0 < j → j < p → T^[j] x ≠ x)
    (hm₀ : 0 < m₀) (hlow : ∀ i, i < p → m₀ ≤ T^[i] x)
    (F : Finset ℕ) (hFp : ∀ i ∈ F, i < p)
    (hFw : ∀ i ∈ F, ∀ i' ∈ F, window x ℓ i = window x ℓ i') :
    ∑ i ∈ F, (1 : ℝ) / ((T^[i] x : ℕ) : ℝ) ≤
      1 / (m₀ : ℝ) + (1 + Real.log (F.card : ℝ)) / 2 ^ ℓ := by
  have hinj : Set.InjOn (fun i => T^[i] x) (F : Set ℕ) := by
    intro i hi i' hi' heq
    have hi₀ : i < p := hFp i hi
    have hi'₀ : i' < p := hFp i' hi'
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · exact hmin (i' - i) (by omega) (by omega) (iterate_sub_eq_self_of_eq hcyc hi'₀ hlt heq)
    · exact hmin (i - i') (by omega) (by omega) (iterate_sub_eq_self_of_eq hcyc hi₀ hgt heq.symm)
  have hsumY : ∑ i ∈ F, (1 : ℝ) / ((T^[i] x : ℕ) : ℝ) =
      ∑ y ∈ F.image (fun i => T^[i] x), (1 : ℝ) / (y : ℝ) := by
    rw [sum_image hinj]
  have hcongY : ∀ y ∈ F.image (fun i => T^[i] x), ∀ y' ∈ F.image (fun i => T^[i] x),
      y ≡ y' [MOD 2 ^ ℓ] := by
    intro y hy y' hy'
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hy
    obtain ⟨i', hi', rfl⟩ := mem_image.mp hy'
    have hw := hFw i hi i' hi'
    apply modEq_of_parity_window ℓ
    intro t ht
    have := congrFun hw ⟨t, ht⟩
    simp only [window] at this
    rwa [Nat.add_comm i t, Nat.add_comm i' t, Function.iterate_add_apply,
      Function.iterate_add_apply] at this
  have hlowY : ∀ y ∈ F.image (fun i => T^[i] x), m₀ ≤ y := by
    intro y hy
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hy
    exact hlow i (hFp i hi)
  have hcard : (F.image (fun i => T^[i] x)).card = F.card := card_image_of_injOn hinj
  have hM : 0 < 2 ^ ℓ := by positivity
  have h := sum_inv_le_of_pairwise_modEq hM hm₀ hlowY hcongY
  rw [hcard] at h
  rw [hsumY]
  push_cast at h
  exact h

/-- **Theorem 10 (harmonic-residue bound).** For a cycle of minimal period `p` whose elements are
all at least `m₀ > 0`, with `C` distinct parity windows of length `ℓ` at the odd positions and
class sizes `N_w`,  `3 (p log 2 − K log 3) ≤ C/m₀ + ∑_w (1 + log N_w)/2^ℓ`. -/
theorem harmonic_residue_bound {x p ℓ m₀ : ℕ} (hx : 0 < x) (hcyc : T^[p] x = x)
    (hmin : ∀ j, 0 < j → j < p → T^[j] x ≠ x)
    (hm₀ : 0 < m₀) (hlow : ∀ i, i < p → m₀ ≤ T^[i] x) :
    3 * ((p : ℝ) * Real.log 2 - (oddCount T x p : ℝ) * Real.log 3) ≤
      ((oddWindows x p ℓ).card : ℝ) / m₀ +
        ∑ w ∈ oddWindows x p ℓ,
          (1 + Real.log ((((oddPos x p).filter (fun i => window x ℓ i = w)).card : ℕ) : ℝ)) /
            2 ^ ℓ := by
  have h1 := three_lambda_le_sum_inv hx hcyc
  have hmaps : ∀ i ∈ oddPos x p, window x ℓ i ∈ oddWindows x p ℓ :=
    fun i hi => mem_image_of_mem _ hi
  have h2 : ∑ i ∈ oddPos x p, (1 : ℝ) / ((T^[i] x : ℕ) : ℝ) =
      ∑ w ∈ oddWindows x p ℓ, ∑ i ∈ (oddPos x p).filter (fun i => window x ℓ i = w),
        (1 : ℝ) / ((T^[i] x : ℕ) : ℝ) :=
    (sum_fiberwise_of_maps_to hmaps _).symm
  have h3 : ∀ w ∈ oddWindows x p ℓ,
      ∑ i ∈ (oddPos x p).filter (fun i => window x ℓ i = w), (1 : ℝ) / ((T^[i] x : ℕ) : ℝ) ≤
        1 / (m₀ : ℝ) +
          (1 + Real.log ((((oddPos x p).filter (fun i => window x ℓ i = w)).card : ℕ) : ℝ)) /
            2 ^ ℓ := by
    intro w _
    refine class_sum_le hcyc hmin hm₀ hlow _ ?_ ?_
    · intro i hi
      rw [mem_filter, oddPos, mem_filter, mem_range] at hi
      exact hi.1.1
    · intro i hi i' hi'
      rw [mem_filter] at hi hi'
      rw [hi.2, hi'.2]
  calc 3 * ((p : ℝ) * Real.log 2 - (oddCount T x p : ℝ) * Real.log 3)
      ≤ ∑ i ∈ oddPos x p, (1 : ℝ) / ((T^[i] x : ℕ) : ℝ) := h1
    _ = ∑ w ∈ oddWindows x p ℓ, ∑ i ∈ (oddPos x p).filter (fun i => window x ℓ i = w),
          (1 : ℝ) / ((T^[i] x : ℕ) : ℝ) := h2
    _ ≤ ∑ w ∈ oddWindows x p ℓ, (1 / (m₀ : ℝ) +
          (1 + Real.log ((((oddPos x p).filter (fun i => window x ℓ i = w)).card : ℕ) : ℝ)) /
            2 ^ ℓ) := sum_le_sum h3
    _ = ((oddWindows x p ℓ).card : ℝ) / m₀ + ∑ w ∈ oddWindows x p ℓ,
          (1 + Real.log ((((oddPos x p).filter (fun i => window x ℓ i = w)).card : ℕ) : ℝ)) /
            2 ^ ℓ := by
        rw [sum_add_distrib, sum_const, nsmul_eq_mul]; ring

/-- **Corollary (crude form).** Bounding every class size by `K`:
`3 (p log 2 − K log 3) ≤ C/m₀ + C (1 + log K)/2^ℓ`. -/
theorem harmonic_residue_bound_crude {x p ℓ m₀ : ℕ} (hx : 0 < x) (hcyc : T^[p] x = x)
    (hmin : ∀ j, 0 < j → j < p → T^[j] x ≠ x)
    (hm₀ : 0 < m₀) (hlow : ∀ i, i < p → m₀ ≤ T^[i] x) :
    3 * ((p : ℝ) * Real.log 2 - (oddCount T x p : ℝ) * Real.log 3) ≤
      ((oddWindows x p ℓ).card : ℝ) / m₀ +
        ((oddWindows x p ℓ).card : ℝ) * (1 + Real.log (oddCount T x p : ℝ)) / 2 ^ ℓ := by
  have h := harmonic_residue_bound (ℓ := ℓ) hx hcyc hmin hm₀ hlow
  have hK : ∀ w ∈ oddWindows x p ℓ,
      (1 + Real.log ((((oddPos x p).filter (fun i => window x ℓ i = w)).card : ℕ) : ℝ)) / 2 ^ ℓ ≤
        (1 + Real.log (oddCount T x p : ℝ)) / 2 ^ ℓ := by
    intro w _
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    have hle : ((oddPos x p).filter (fun i => window x ℓ i = w)).card ≤ oddCount T x p := by
      rw [← card_oddPos]; exact card_filter_le _ _
    rcases Nat.eq_zero_or_pos ((oddPos x p).filter (fun i => window x ℓ i = w)).card with
      h0 | hpos
    · rw [h0]
      simp only [Nat.cast_zero, Real.log_zero]
      linarith [Real.log_natCast_nonneg (oddCount T x p)]
    · have := Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast hle :
        ((((oddPos x p).filter (fun i => window x ℓ i = w)).card : ℕ) : ℝ) ≤
          (oddCount T x p : ℝ))
      linarith
  have hsum := sum_le_sum hK
  rw [sum_const, nsmul_eq_mul] at hsum
  calc 3 * ((p : ℝ) * Real.log 2 - (oddCount T x p : ℝ) * Real.log 3) ≤ _ := h
    _ ≤ ((oddWindows x p ℓ).card : ℝ) / m₀ +
          ((oddWindows x p ℓ).card : ℝ) * ((1 + Real.log (oddCount T x p : ℝ)) / 2 ^ ℓ) := by
        linarith
    _ = _ := by ring

/-- Jensen's inequality for `log`: for positive reals `a w` indexed by a nonempty finset `t`,
`∑ log (a w) ≤ |t| log ((∑ a w) / |t|)`. -/
theorem sum_log_le_card_mul_log_avg {ι : Type*} (t : Finset ι) (a : ι → ℝ)
    (hpos : ∀ w ∈ t, 0 < a w) (ht : t.Nonempty) :
    ∑ w ∈ t, Real.log (a w) ≤ (t.card : ℝ) * Real.log ((∑ w ∈ t, a w) / t.card) := by
  have hC : (0 : ℝ) < t.card := by exact_mod_cast card_pos.mpr ht
  have hC' : (t.card : ℝ) ≠ 0 := hC.ne'
  have hJ := strictConcaveOn_log_Ioi.concaveOn.le_map_sum
    (t := t) (w := fun _ => 1 / (t.card : ℝ)) (p := a)
    (fun _ _ => by
      show (0 : ℝ) ≤ 1 / (t.card : ℝ)
      positivity)
    (by
      show ∑ _i ∈ t, (1 / (t.card : ℝ)) = 1
      rw [sum_const, nsmul_eq_mul, mul_one_div_cancel hC'])
    (fun w hw => hpos w hw)
  simp only [smul_eq_mul] at hJ
  rw [← mul_sum, ← mul_sum] at hJ
  have hav : 1 / (t.card : ℝ) * ∑ w ∈ t, a w = (∑ w ∈ t, a w) / t.card := by ring
  rw [hav] at hJ
  have hmul := mul_le_mul_of_nonneg_left hJ hC.le
  calc ∑ w ∈ t, Real.log (a w)
      = (t.card : ℝ) * (1 / (t.card : ℝ) * ∑ w ∈ t, Real.log (a w)) := by
        rw [← mul_assoc, mul_one_div_cancel hC', one_mul]
    _ ≤ (t.card : ℝ) * Real.log ((∑ w ∈ t, a w) / t.card) := hmul

/-- **Theorem 10, Jensen form.** With `C` window classes at the odd positions and `K` odd elements
in total, `∑_w log N_w ≤ C log (K/C)`, hence
`3 (p log 2 − K log 3) ≤ C/m₀ + C (1 + log (K/C))/2^ℓ`. -/
theorem harmonic_residue_bound_jensen {x p ℓ m₀ : ℕ} (hx : 0 < x) (hcyc : T^[p] x = x)
    (hmin : ∀ j, 0 < j → j < p → T^[j] x ≠ x)
    (hm₀ : 0 < m₀) (hlow : ∀ i, i < p → m₀ ≤ T^[i] x) :
    3 * ((p : ℝ) * Real.log 2 - (oddCount T x p : ℝ) * Real.log 3) ≤
      ((oddWindows x p ℓ).card : ℝ) / m₀ +
        ((oddWindows x p ℓ).card : ℝ) *
          (1 + Real.log ((oddCount T x p : ℝ) / (oddWindows x p ℓ).card)) / 2 ^ ℓ := by
  have h := harmonic_residue_bound (ℓ := ℓ) hx hcyc hmin hm₀ hlow
  rcases (oddWindows x p ℓ).eq_empty_or_nonempty with hW | hW
  · rw [hW] at h ⊢
    simpa using h
  · have hNpos : ∀ w ∈ oddWindows x p ℓ,
        (0 : ℝ) < ((((oddPos x p).filter (fun i => window x ℓ i = w)).card : ℕ) : ℝ) := by
      intro w hw
      have hw' : w ∈ (oddPos x p).image (window x ℓ) := hw
      obtain ⟨i, hi, rfl⟩ := mem_image.mp hw'
      have hmem : i ∈ (oddPos x p).filter (fun i' => window x ℓ i' = window x ℓ i) :=
        mem_filter.mpr ⟨hi, rfl⟩
      exact_mod_cast card_pos.mpr ⟨i, hmem⟩
    have hsumN : ∑ w ∈ oddWindows x p ℓ,
        ((((oddPos x p).filter (fun i => window x ℓ i = w)).card : ℕ) : ℝ) =
          (oddCount T x p : ℝ) := by
      have hmaps : Set.MapsTo (window x ℓ) (oddPos x p : Set ℕ)
          (oddWindows x p ℓ : Set (Fin ℓ → ℕ)) := by
        intro i hi
        exact mem_image_of_mem _ hi
      rw [← card_oddPos, card_eq_sum_card_fiberwise hmaps]
      push_cast
      try rfl
    have hJ : ∑ w ∈ oddWindows x p ℓ,
        Real.log ((((oddPos x p).filter (fun i => window x ℓ i = w)).card : ℕ) : ℝ) ≤
          ((oddWindows x p ℓ).card : ℝ) *
            Real.log ((∑ w ∈ oddWindows x p ℓ,
              ((((oddPos x p).filter (fun i => window x ℓ i = w)).card : ℕ) : ℝ)) /
                (oddWindows x p ℓ).card) :=
      sum_log_le_card_mul_log_avg (oddWindows x p ℓ)
        (fun w => ((((oddPos x p).filter (fun i => window x ℓ i = w)).card : ℕ) : ℝ)) hNpos hW
    rw [hsumN] at hJ
    have hsplit : ∑ w ∈ oddWindows x p ℓ,
        (1 + Real.log ((((oddPos x p).filter (fun i => window x ℓ i = w)).card : ℕ) : ℝ)) /
          2 ^ ℓ =
        (((oddWindows x p ℓ).card : ℝ) + ∑ w ∈ oddWindows x p ℓ,
          Real.log ((((oddPos x p).filter (fun i => window x ℓ i = w)).card : ℕ) : ℝ)) /
            2 ^ ℓ := by
      rw [← sum_div, sum_add_distrib, sum_const, nsmul_eq_mul, mul_one]
    have h2ℓ : (0 : ℝ) ≤ 2 ^ ℓ := by positivity
    calc 3 * ((p : ℝ) * Real.log 2 - (oddCount T x p : ℝ) * Real.log 3) ≤ _ := h
      _ = ((oddWindows x p ℓ).card : ℝ) / m₀ +
            (((oddWindows x p ℓ).card : ℝ) + ∑ w ∈ oddWindows x p ℓ,
              Real.log ((((oddPos x p).filter (fun i => window x ℓ i = w)).card : ℕ) : ℝ)) /
                2 ^ ℓ := by
          rw [hsplit]
      _ ≤ ((oddWindows x p ℓ).card : ℝ) / m₀ +
            (((oddWindows x p ℓ).card : ℝ) + ((oddWindows x p ℓ).card : ℝ) *
              Real.log ((oddCount T x p : ℝ) / (oddWindows x p ℓ).card)) / 2 ^ ℓ :=
          add_le_add le_rfl (div_le_div_of_nonneg_right (add_le_add le_rfl hJ) h2ℓ)
      _ = _ := by ring

end Collatz
