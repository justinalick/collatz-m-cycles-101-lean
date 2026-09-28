import Collatz.HercherWindow

/-!
# Theorem 21 with a vertex-type bound, by a two-element argument

The corrigendum to Hercher's Theorem 21 bounds the window sum by the value of `Σ f(x_i)`,
`f(x) = 3/(2^x − 1)`, at a vertex `(v, δv, …, δ^{m₂−1} v)` of a polyhedron, which gives
`f(v) + (m₂ − 1) f(δ v)`. `docs/hercher_formalization_roadmap.md` (Section 5a) proposes a
one-variable convexity argument to avoid polyhedral geometry. This file uses a shorter argument
that gives almost the same bound.

**At most one window minimum is small.** In the maximal window of Theorem 21 (chain
`x_{t+1} ≤ δ x_t`, wrap `x_s ≤ δ x_{s+m₂−1}`), for two positions `a₁ < a₂` of the window, following
the chain from each of them covers the window in two runs of lengths `d = a₂ − a₁` and `m₂ − d`:

  `Σ_window x ≤ G_d x_{s+a₁} + G_{m₂−d} x_{s+a₂} ≤ (1 + G_{m₂−1}) max(x_{s+a₁}, x_{s+a₂})`

(`window_sum_le_two`), where `G_n = Σ_{j<n} δ^j` and `G_d + G_e ≤ 1 + G_{d+e−1}` for `d, e ≥ 1`
(`geom_add_le`: moving a term to the longer run only increases the sum). Since the window sum is at
least `S = m₂ K/m`, at most one window minimum has `x < τ = S/(1 + G_{m₂−1})`; all have `x ≥ v =
S/G_{m₂}` (`exists_window_minima_two`). Hence

  `Σ_window T(n_i) < f(v) + (m₂ − 1) f(τ)`,

and `τ = δ v · (1 + δ G_{m₂−1})/(δ (1 + G_{m₂−1}))` differs from the corrigendum's `δ v` by a relative
`(δ − 1)/(δ(1 + G_{m₂−1}))`, about `10⁻¹⁸` for `m₂ ≥ 88`. With the `m − m₂` minima outside the window
bounded by Remark 7, this is `theorem21_two`:

  `3 (p log 2 − K log 3) < 3 (m − m₂)/X₀ + 3/(2^v − 1) + 3 (m₂ − 1)/(2^τ − 1)`.
-/

namespace Collatz

open Finset

/-- `G_{d+1} + G_{e+1} ≤ 1 + G_{d+e+1}` for `δ ≥ 1`, `G_n = Σ_{j<n} δ^j`. -/
theorem geom_add_le {δ : ℝ} (hδ : 1 ≤ δ) (e d : ℕ) :
    ∑ j ∈ range (d + 1), δ ^ j + ∑ j ∈ range (e + 1), δ ^ j ≤
      1 + ∑ j ∈ range (d + e + 1), δ ^ j := by
  induction d with
  | zero =>
    rw [sum_range_one, pow_zero, Nat.zero_add]
  | succ d ih =>
    rw [sum_range_succ _ (d + 1), show d + 1 + e + 1 = (d + e + 1) + 1 by omega,
      sum_range_succ _ (d + e + 1)]
    have : δ ^ (d + 1) ≤ δ ^ (d + e + 1) := pow_le_pow_right₀ hδ (by omega)
    linarith

/-- **Two elements of a closed-up window bound its sum**:
`Σ_{b<m₂} x_{s+b} ≤ (1 + G_{m₂−1}) τ` when `x_{s+a₁}, x_{s+a₂} ≤ τ`, `a₁ < a₂ < m₂`. -/
theorem window_sum_le_two (xs : ℕ → ℝ) {δ : ℝ} (hδ : 1 ≤ δ)
    (hstep : ∀ t, xs (t + 1) ≤ δ * xs t) (hnn : ∀ t, 0 ≤ xs t)
    {s m₂ : ℕ} (hwrap : xs s ≤ δ * xs (s + m₂ - 1)) {a₁ a₂ : ℕ} (h12 : a₁ < a₂) (h2 : a₂ < m₂)
    {τ : ℝ} (h1τ : xs (s + a₁) ≤ τ) (h2τ : xs (s + a₂) ≤ τ) :
    ∑ b ∈ range m₂, xs (s + b) ≤ (1 + ∑ j ∈ range (m₂ - 1), δ ^ j) * τ := by
  have hδ0 : 0 ≤ δ := by linarith
  have hτ : 0 ≤ τ := le_trans (hnn _) h1τ
  -- split the window at `a₁` and `a₂`
  have e1 := sum_range_add (fun b => xs (s + b)) a₁ (m₂ - a₁)
  rw [show a₁ + (m₂ - a₁) = m₂ by omega] at e1
  have e2 := sum_range_add (fun c => xs (s + (a₁ + c))) (a₂ - a₁) (m₂ - a₂)
  rw [show a₂ - a₁ + (m₂ - a₂) = m₂ - a₁ by omega] at e2
  -- the run from `a₂` to the end of the window
  have hC : ∑ c ∈ range (m₂ - a₂), xs (s + (a₁ + (a₂ - a₁ + c))) ≤
      (∑ c ∈ range (m₂ - a₂), δ ^ c) * τ := by
    rw [sum_mul]
    refine sum_le_sum (fun c _ => ?_)
    rw [show s + (a₁ + (a₂ - a₁ + c)) = s + a₂ + c by omega]
    calc xs (s + a₂ + c) ≤ δ ^ c * xs (s + a₂) := chain_le xs hδ0 hstep _ c
      _ ≤ δ ^ c * τ := mul_le_mul_of_nonneg_left h2τ (pow_nonneg hδ0 c)
  -- the run from `a₁` to `a₂`
  have hB : ∑ c ∈ range (a₂ - a₁), xs (s + (a₁ + c)) ≤ (∑ c ∈ range (a₂ - a₁), δ ^ c) * τ := by
    rw [sum_mul]
    refine sum_le_sum (fun c _ => ?_)
    rw [← Nat.add_assoc]
    calc xs (s + a₁ + c) ≤ δ ^ c * xs (s + a₁) := chain_le xs hδ0 hstep _ c
      _ ≤ δ ^ c * τ := mul_le_mul_of_nonneg_left h1τ (pow_nonneg hδ0 c)
  -- the start of the window, reached from `a₂` through the wrap
  have hlast : xs (s + m₂ - 1) ≤ δ ^ (m₂ - 1 - a₂) * xs (s + a₂) := by
    have := chain_le xs hδ0 hstep (s + a₂) (m₂ - 1 - a₂)
    rwa [show s + a₂ + (m₂ - 1 - a₂) = s + m₂ - 1 by omega] at this
  have hA : ∑ b ∈ range a₁, xs (s + b) ≤ (∑ b ∈ range a₁, δ ^ (m₂ - a₂ + b)) * τ := by
    rw [sum_mul]
    refine sum_le_sum (fun b _ => ?_)
    have hδb : 0 ≤ δ ^ b := pow_nonneg hδ0 b
    calc xs (s + b) ≤ δ ^ b * xs s := chain_le xs hδ0 hstep s b
      _ ≤ δ ^ b * (δ * xs (s + m₂ - 1)) := mul_le_mul_of_nonneg_left hwrap hδb
      _ ≤ δ ^ b * (δ * (δ ^ (m₂ - 1 - a₂) * xs (s + a₂))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlast hδ0) hδb
      _ = δ ^ (m₂ - a₂ + b) * xs (s + a₂) := by
          rw [show m₂ - a₂ + b = b + 1 + (m₂ - 1 - a₂) by omega]
          ring
      _ ≤ δ ^ (m₂ - a₂ + b) * τ := mul_le_mul_of_nonneg_left h2τ (pow_nonneg hδ0 _)
  -- the coefficients
  have hco : ∑ c ∈ range (m₂ - a₂ + a₁), δ ^ c =
      ∑ c ∈ range (m₂ - a₂), δ ^ c + ∑ b ∈ range a₁, δ ^ (m₂ - a₂ + b) :=
    sum_range_add _ _ _
  have hg := geom_add_le (δ := δ) hδ (m₂ - a₂ + a₁ - 1) (a₂ - a₁ - 1)
  rw [show a₂ - a₁ - 1 + (m₂ - a₂ + a₁ - 1) + 1 = m₂ - 1 by omega,
    show a₂ - a₁ - 1 + 1 = a₂ - a₁ by omega,
    show m₂ - a₂ + a₁ - 1 + 1 = m₂ - a₂ + a₁ by omega, hco] at hg
  have hgτ := mul_le_mul_of_nonneg_right hg hτ
  rw [e1, e2]
  simp only [add_mul] at hgτ ⊢
  linarith

/-- The maximal window of Theorem 21, as in `exists_window`: the chain closes up in it, and its
sum is at least the average `(m₂/m) Σ_r x_r`. -/
theorem exists_max_window (xs : ℕ → ℝ) {δ : ℝ} (hδ : 0 ≤ δ) (hstep : ∀ t, xs (t + 1) ≤ δ * xs t)
    {m m₂ : ℕ} (hm : 1 ≤ m) (hm₂ : 1 ≤ m₂) (hper : ∀ t, xs (t + m) = xs t) :
    ∃ s, xs s ≤ δ * xs (s + m₂ - 1) ∧
      (m₂ : ℝ) * ∑ r ∈ range m, xs r ≤ (m : ℝ) * ∑ b ∈ range m₂, xs (s + b) := by
  set W : ℕ → ℝ := fun t => ∑ b ∈ range m₂, xs (t + b) with hW
  have hWper : ∀ t, W (t + m) = W t := by
    intro t
    simp only [hW]
    refine sum_congr rfl (fun b _ => ?_)
    rw [show t + m + b = (t + b) + m by omega, hper]
  obtain ⟨s, hs, hmax⟩ := exists_max_image (range m) W ⟨0, mem_range.mpr (by omega)⟩
  have hmax' : ∀ t, W t ≤ W s := by
    intro t
    rw [periodic_mod hWper t]
    exact hmax _ (mem_range.mpr (Nat.mod_lt _ (by omega)))
  have hshift : ∀ t, W (t + 1) + xs t = W t + xs (t + m₂) := by
    intro t
    have e1 : ∑ b ∈ range (m₂ + 1), xs (t + b) = W t + xs (t + m₂) := sum_range_succ _ _
    have e2 : ∑ b ∈ range (m₂ + 1), xs (t + b) = ∑ b ∈ range m₂, xs (t + (b + 1)) + xs (t + 0) :=
      sum_range_succ' _ _
    have e3 : ∑ b ∈ range m₂, xs (t + (b + 1)) = W (t + 1) := by
      simp only [hW]
      refine sum_congr rfl (fun b _ => ?_)
      rw [show t + (b + 1) = t + 1 + b by omega]
    rw [← e1, e2, e3]
    simp
  have hwrap : xs s ≤ δ * xs (s + m₂ - 1) := by
    have h1 := hshift (s + m - 1)
    rw [show s + m - 1 + 1 = s + m by omega, hWper] at h1
    have h2 := hmax' (s + m - 1)
    have h3 : xs (s + m - 1 + m₂) = xs (s + m₂ - 1) := by
      rw [show s + m - 1 + m₂ = (s + m₂ - 1) + m by omega, hper]
    have h4 : xs (s + m - 1) ≤ xs (s + m₂ - 1) := by linarith
    have h5 := hstep (s + m - 1)
    rw [show s + m - 1 + 1 = s + m by omega, hper] at h5
    calc xs s ≤ δ * xs (s + m - 1) := h5
      _ ≤ δ * xs (s + m₂ - 1) := mul_le_mul_of_nonneg_left h4 hδ
  have havg : ∑ t ∈ range m, W t = (m₂ : ℝ) * ∑ r ∈ range m, xs r := by
    simp only [hW]
    rw [sum_comm]
    have : ∀ b ∈ range m₂, ∑ t ∈ range m, xs (t + b) = ∑ r ∈ range m, xs r := by
      intro b _
      have e : ∑ t ∈ range m, xs (t + b) = ∑ t ∈ range m, xs (b + t) :=
        sum_congr rfl (fun t _ => by rw [Nat.add_comm t b])
      rw [e]
      exact sum_range_rotate xs hper b
    rw [sum_congr rfl this, sum_const, card_range, nsmul_eq_mul]
  have hle : ∑ t ∈ range m, W t ≤ (m : ℝ) * W s := by
    have := sum_le_sum (fun t (_ : t ∈ range m) => hmax' t)
    rwa [sum_const, card_range, nsmul_eq_mul] at this
  refine ⟨s, hwrap, ?_⟩
  simp only [hW] at hle havg
  linarith

/-- The second exponent `τ = m₂ K/(m (1 + G_{m₂−1}))`. -/
noncomputable def windowExp2 (m m₂ K : ℕ) : ℝ :=
  (m₂ : ℝ) * K / ((m : ℝ) * (1 + ∑ d ∈ range (m₂ - 1), Real.logb 2 3 ^ d))

/-- **The window minima.** Some `m₂` consecutive minima all satisfy `n ≥ 2^v − 1`, and of any two
of them one satisfies `n ≥ 2^τ − 1`. -/
theorem exists_window_minima_two {x p : ℕ} (hx : 0 < x) (hp : 0 < p) (hcyc : T^[p] x = x)
    (hmin : IsMinOf x p) {m₂ : ℕ} (hm₂ : 1 ≤ m₂) :
    ∃ s, (∀ a < m₂, (2 : ℝ) ^ windowExp (numLocalMin x p) m₂ (oddCount T x p) ≤
        (nextMin^[s + a] x : ℝ) + 1) ∧
      (∀ a₁ a₂, a₁ < a₂ → a₂ < m₂ →
        (2 : ℝ) ^ windowExp2 (numLocalMin x p) m₂ (oddCount T x p) ≤ (nextMin^[s + a₁] x : ℝ) + 1 ∨
        (2 : ℝ) ^ windowExp2 (numLocalMin x p) m₂ (oddCount T x p) ≤ (nextMin^[s + a₂] x : ℝ) + 1) := by
  have hmN := (numLocalMin_eq_of_isMin hx hp hcyc hmin).2
  have hmR : (0 : ℝ) < numLocalMin x p := by exact_mod_cast hmN
  set xs : ℕ → ℝ := fun r => Real.logb 2 ((nextMin^[r] x : ℝ) + 1) with hxs
  have hδ1 : (1 : ℝ) ≤ Real.logb 2 3 := one_le_logb_two_three
  have hδ : (0 : ℝ) ≤ Real.logb 2 3 := by linarith
  have hstep : ∀ t, xs (t + 1) ≤ Real.logb 2 3 * xs t := by
    intro t
    simp only [hxs]
    rw [Function.iterate_succ_apply']
    exact (logb_nextMin_lt (nextMin_iterate_pos hx t) (nextMin_iterate_odd hx hmin.1 t)).le
  have hper : ∀ t, xs (t + numLocalMin x p) = xs t := by
    intro t
    simp only [hxs]
    rw [nextMin_periodic hx hp hcyc hmin]
  have hnn : ∀ t, 0 ≤ xs t := by
    intro t
    simp only [hxs]
    exact Real.logb_nonneg (by norm_num) (by linarith [Nat.cast_nonneg (α := ℝ) (nextMin^[t] x)])
  obtain ⟨s, hwrap, hwin⟩ := exists_max_window xs hδ hstep hmN hm₂ hper
  have hK : (oddCount T x p : ℝ) ≤ ∑ r ∈ range (numLocalMin x p), xs r := by
    rw [oddCount_eq_sum_orun hx hp hcyc hmin]
    push_cast
    exact sum_le_sum (fun r _ => orun_le_logb _)
  have hm₂R : (0 : ℝ) ≤ m₂ := Nat.cast_nonneg _
  have hSK : (m₂ : ℝ) * oddCount T x p ≤ (numLocalMin x p : ℝ) * ∑ b ∈ range m₂, xs (s + b) := by
    have := mul_le_mul_of_nonneg_left hK hm₂R
    linarith
  have hpos_n : ∀ a, (0 : ℝ) < (nextMin^[s + a] x : ℝ) + 1 := fun a => by positivity
  refine ⟨s, fun a ha => ?_, fun a₁ a₂ h12 h2 => ?_⟩
  · -- every window minimum
    have hwsum := window_sum_le xs hδ hstep hwrap ha
    have hG := geomSum_delta_pos hm₂
    rw [← Real.le_logb_iff_rpow_le (b := 2) (by norm_num) (hpos_n a), windowExp,
      div_le_iff₀ (mul_pos hmR hG)]
    have := mul_le_mul_of_nonneg_left hwsum hmR.le
    simp only [hxs] at this hSK
    linarith
  · -- two window minima
    have hG' : (0 : ℝ) < 1 + ∑ d ∈ range (m₂ - 1), Real.logb 2 3 ^ d := by
      have : (0 : ℝ) ≤ ∑ d ∈ range (m₂ - 1), Real.logb 2 3 ^ d :=
        sum_nonneg (fun d _ => pow_nonneg hδ d)
      linarith
    by_contra hcon
    push_neg at hcon
    obtain ⟨c1, c2⟩ := hcon
    rw [← Real.logb_lt_iff_lt_rpow (b := 2) (by norm_num) (hpos_n a₁), windowExp2,
      lt_div_iff₀ (mul_pos hmR hG')] at c1
    rw [← Real.logb_lt_iff_lt_rpow (b := 2) (by norm_num) (hpos_n a₂), windowExp2,
      lt_div_iff₀ (mul_pos hmR hG')] at c2
    have htwo := window_sum_le_two xs hδ1 hstep hnn hwrap h12 h2
      (le_max_left (xs (s + a₁)) (xs (s + a₂))) (le_max_right _ _)
    have hmax : max (xs (s + a₁)) (xs (s + a₂)) * ((numLocalMin x p : ℝ) *
        (1 + ∑ d ∈ range (m₂ - 1), Real.logb 2 3 ^ d)) < (m₂ : ℝ) * oddCount T x p := by
      simp only [hxs]
      rcases le_total (Real.logb 2 ((nextMin^[s + a₁] x : ℝ) + 1))
          (Real.logb 2 ((nextMin^[s + a₂] x : ℝ) + 1)) with h | h
      · rw [max_eq_right h]; exact c2
      · rw [max_eq_left h]; exact c1
    have h3 := mul_le_mul_of_nonneg_left htwo hmR.le
    have e : (numLocalMin x p : ℝ) * ((1 + ∑ j ∈ range (m₂ - 1), Real.logb 2 3 ^ j) *
        max (xs (s + a₁)) (xs (s + a₂))) = max (xs (s + a₁)) (xs (s + a₂)) *
        ((numLocalMin x p : ℝ) * (1 + ∑ d ∈ range (m₂ - 1), Real.logb 2 3 ^ d)) := by ring
    linarith

/-- **Theorem 21 with the two-element bound, sum form**, for a cycle through a local minimum:
`Σ_r T(n_r) < 3 (m − m₂)/X₀ + 3/(2^v − 1) + 3 (m₂ − 1)/(2^τ − 1)`. -/
theorem sum_riseSum_lt_two {x p : ℕ} (hx : 0 < x) (hp : 0 < p) (hcyc : T^[p] x = x)
    (hmin : IsMinOf x p) {m₂ : ℕ} (hm₂ : 1 ≤ m₂) (hm₂m : m₂ ≤ numLocalMin x p) {X₀ : ℝ}
    (hX₀ : 0 < X₀) (hlow : ∀ j, X₀ ≤ ((T^[j] x : ℕ) : ℝ)) :
    ∑ r ∈ range (numLocalMin x p), riseSum (nextMin^[r] x) (orun (nextMin^[r] x)) <
      3 * ((numLocalMin x p - m₂ : ℕ) : ℝ) / X₀ +
        3 / ((2 : ℝ) ^ windowExp (numLocalMin x p) m₂ (oddCount T x p) - 1) +
        3 * ((m₂ - 1 : ℕ) : ℝ) /
          ((2 : ℝ) ^ windowExp2 (numLocalMin x p) m₂ (oddCount T x p) - 1) := by
  obtain ⟨s, hs1, hs2⟩ := exists_window_minima_two hx hp hcyc hmin hm₂
  have hK := K_pos_of_isMin hx hp hcyc hmin
  have hmpos : 0 < numLocalMin x p := (numLocalMin_eq_of_isMin hx hp hcyc hmin).2
  obtain ⟨v, hv⟩ : ∃ v, v = windowExp (numLocalMin x p) m₂ (oddCount T x p) := ⟨_, rfl⟩
  obtain ⟨τ, hτ⟩ : ∃ τ, τ = windowExp2 (numLocalMin x p) m₂ (oddCount T x p) := ⟨_, rfl⟩
  rw [← hv] at hs1 ⊢
  rw [← hτ] at hs2 ⊢
  have h1 : (0 : ℝ) < numLocalMin x p := by exact_mod_cast hmpos
  have h2 : (0 : ℝ) < m₂ := by exact_mod_cast hm₂
  have h3 : (0 : ℝ) < oddCount T x p := by exact_mod_cast hK
  have hvpos : 0 < v := by
    rw [hv, windowExp]
    exact div_pos (mul_pos h2 h3) (mul_pos h1 (geomSum_delta_pos hm₂))
  have hτpos : 0 < τ := by
    rw [hτ, windowExp2]
    have : (0 : ℝ) ≤ ∑ d ∈ range (m₂ - 1), Real.logb 2 3 ^ d :=
      sum_nonneg (fun d _ => pow_nonneg (by linarith [one_le_logb_two_three]) d)
    exact div_pos (mul_pos h2 h3) (mul_pos h1 (by linarith))
  have h2v : (0 : ℝ) < (2 : ℝ) ^ v - 1 := by
    have : (1 : ℝ) < (2 : ℝ) ^ v := Real.one_lt_rpow (by norm_num) hvpos
    linarith
  have h2τ : (0 : ℝ) < (2 : ℝ) ^ τ - 1 := by
    have : (1 : ℝ) < (2 : ℝ) ^ τ := Real.one_lt_rpow (by norm_num) hτpos
    linarith
  obtain ⟨f, hf⟩ : ∃ f : ℕ → ℝ, f = fun r => riseSum (nextMin^[r] x) (orun (nextMin^[r] x)) :=
    ⟨_, rfl⟩
  have hgoal : ∑ r ∈ range (numLocalMin x p), riseSum (nextMin^[r] x) (orun (nextMin^[r] x)) =
      ∑ r ∈ range (numLocalMin x p), f r := by rw [hf]
  have hfper : ∀ r, f (r + numLocalMin x p) = f r := by
    intro r; simp only [hf, nextMin_periodic hx hp hcyc hmin]
  have hrot : ∑ r ∈ range (numLocalMin x p), f r = ∑ r ∈ range (numLocalMin x p), f (s + r) :=
    (sum_range_rotate f hfper s).symm
  have hsplit := sum_range_add (fun r => f (s + r)) m₂ (numLocalMin x p - m₂)
  rw [show m₂ + (numLocalMin x p - m₂) = numLocalMin x p by omega] at hsplit
  have hmem : ∀ r, X₀ ≤ ((nextMin^[r] x : ℕ) : ℝ) := by
    intro r; rw [← iterate_minPos]; exact hlow _
  have hf_lt : ∀ r, f r < 3 / ((nextMin^[r] x : ℕ) : ℝ) := by
    intro r
    rw [hf]
    exact riseSum_lt (nextMin_iterate_pos hx r) (fun t ht => odd_of_lt_orun ht)
  have hfv : ∀ b < m₂, f (s + b) < 3 / ((2 : ℝ) ^ v - 1) := by
    intro b hb
    have h := hs1 b hb
    have h' : (2 : ℝ) ^ v - 1 ≤ ((nextMin^[s + b] x : ℕ) : ℝ) := by linarith
    exact lt_of_lt_of_le (hf_lt _) (div_le_div_of_nonneg_left (by norm_num) h2v h')
  have hfτ : ∀ b, (2 : ℝ) ^ τ ≤ (nextMin^[s + b] x : ℝ) + 1 →
      f (s + b) < 3 / ((2 : ℝ) ^ τ - 1) := by
    intro b h
    have h' : (2 : ℝ) ^ τ - 1 ≤ ((nextMin^[s + b] x : ℕ) : ℝ) := by linarith
    exact lt_of_lt_of_le (hf_lt _) (div_le_div_of_nonneg_left (by norm_num) h2τ h')
  -- the exceptional window position (if any)
  obtain ⟨b₀, hb₀, hgood⟩ : ∃ b₀, b₀ < m₂ ∧ ∀ b < m₂, b ≠ b₀ →
      (2 : ℝ) ^ τ ≤ (nextMin^[s + b] x : ℝ) + 1 := by
    by_cases hex : ∃ b₀, b₀ < m₂ ∧ ¬ (2 : ℝ) ^ τ ≤ (nextMin^[s + b₀] x : ℝ) + 1
    · obtain ⟨b₀, hb₀, hbad⟩ := hex
      refine ⟨b₀, hb₀, fun b hb hne => ?_⟩
      rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
      · rcases hs2 b b₀ hlt hb₀ with h | h
        · exact h
        · exact absurd h hbad
      · rcases hs2 b₀ b hgt hb with h | h
        · exact absurd h hbad
        · exact h
    · push_neg at hex
      exact ⟨0, by omega, fun b hb _ => hex b hb⟩
  -- the window
  have hwin : ∑ b ∈ range m₂, f (s + b) <
      3 / ((2 : ℝ) ^ v - 1) + ((m₂ - 1 : ℕ) : ℝ) * (3 / ((2 : ℝ) ^ τ - 1)) := by
    rw [← add_sum_erase _ _ (mem_range.mpr hb₀)]
    have herase : ∑ b ∈ (range m₂).erase b₀, f (s + b) ≤
        ∑ b ∈ (range m₂).erase b₀, 3 / ((2 : ℝ) ^ τ - 1) := by
      refine sum_le_sum (fun b hb => ?_)
      rw [mem_erase, mem_range] at hb
      exact (hfτ b (hgood b hb.2 hb.1)).le
    rw [sum_const, card_erase_of_mem (mem_range.mpr hb₀), card_range, nsmul_eq_mul] at herase
    have := hfv b₀ hb₀
    linarith
  -- the minima outside the window
  have hout : ∑ c ∈ range (numLocalMin x p - m₂), f (s + (m₂ + c)) ≤
      ∑ c ∈ range (numLocalMin x p - m₂), 3 / X₀ := by
    refine sum_le_sum (fun c _ => ?_)
    calc f (s + (m₂ + c)) ≤ 3 / ((nextMin^[s + (m₂ + c)] x : ℕ) : ℝ) := (hf_lt _).le
      _ ≤ 3 / X₀ := div_le_div_of_nonneg_left (by norm_num) hX₀ (hmem _)
  rw [sum_const, card_range, nsmul_eq_mul] at hout
  rw [hgoal, hrot, hsplit]
  have e1 : ((m₂ - 1 : ℕ) : ℝ) * (3 / ((2 : ℝ) ^ τ - 1)) =
      3 * ((m₂ - 1 : ℕ) : ℝ) / ((2 : ℝ) ^ τ - 1) := by ring
  have e2 : ((numLocalMin x p - m₂ : ℕ) : ℝ) * (3 / X₀) =
      3 * ((numLocalMin x p - m₂ : ℕ) : ℝ) / X₀ := by ring
  linarith

/-- **Theorem 21 with the two-element bound.** For every positive `T`-cycle of length `p` whose
elements are all `≥ X₀ > 0`, with `m` local minima, `K` odd elements and `1 ≤ m₂ ≤ m`:
`3 (p log 2 − K log 3) < 3 (m − m₂)/X₀ + 3/(2^v − 1) + 3 (m₂ − 1)/(2^τ − 1)`. -/
theorem theorem21_two {x p : ℕ} (hx : 0 < x) (hp : 0 < p) (hcyc : T^[p] x = x)
    {m₂ : ℕ} (hm₂ : 1 ≤ m₂) (hm₂m : m₂ ≤ numLocalMin x p) {X₀ : ℝ}
    (hX₀ : 0 < X₀) (hlow : ∀ j, X₀ ≤ ((T^[j] x : ℕ) : ℝ)) :
    3 * ((p : ℝ) * Real.log 2 - (oddCount T x p : ℝ) * Real.log 3) <
      3 * ((numLocalMin x p - m₂ : ℕ) : ℝ) / X₀ +
        3 / ((2 : ℝ) ^ windowExp (numLocalMin x p) m₂ (oddCount T x p) - 1) +
        3 * ((m₂ - 1 : ℕ) : ℝ) /
          ((2 : ℝ) ^ windowExp2 (numLocalMin x p) m₂ (oddCount T x p) - 1) := by
  obtain ⟨i, _, hmin⟩ := exists_isMin_rotation (x := x) (p := p) (by omega)
  have hx' : 0 < T^[i] x := iterate_T_pos hx i
  have h := lt_of_le_of_lt (theorem16_of_isMin hx' hp (cycle_rotate hcyc i) hmin)
    (sum_riseSum_lt_two hx' hp (cycle_rotate hcyc i) hmin hm₂
      (by rw [numLocalMin_rotate hp hcyc]; exact hm₂m) hX₀
      (fun j => by rw [← Function.iterate_add_apply]; exact hlow _))
  rwa [numLocalMin_rotate hp hcyc, oddCount_rotate hcyc] at h

end Collatz
