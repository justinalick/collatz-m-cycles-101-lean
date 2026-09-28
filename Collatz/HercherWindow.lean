import Collatz.HercherMinima

/-!
# Hercher's Theorem 21 in vertex-free form

Hercher, Theorem 21, as repaired by the corrigendum of 14 June 2026, steps (a)–(e′) of
`docs/hercher_formalization_roadmap.md`, Section 5a. For the minima `n_r` of a cycle put
`x_r = log₂(n_r + 1)`. Then

* (c) `k_r ≤ x_r` (`orun_le_logb`, Lemma 8);
* (d) `x_{r+1} < δ x_r` (`logb_nextMin_lt`, Lemma 20);
* (a), (b), (e): among the `m` cyclic windows of `m₂` consecutive minima take one with the largest
  `Σ x`; its sum is at least the average `(m₂/m) Σ_r x_r ≥ (m₂/m) K`, the chain (d) closes up
  inside it (the wrap `x_first < δ x_last` comes from comparing with the preceding window), so
  `Σ_window x ≤ G · x_i` for each window minimum, `G = Σ_{d<m₂} δ^d = (δ^{m₂} − 1)/(δ − 1)`
  (`exists_window`, a statement about real sequences). Hence every window minimum satisfies
  `x_i ≥ v = m₂ K/(m G)`, i.e. `n_i ≥ 2^v − 1`;
* (e′) with Remark 7, `Σ_window T(n_i) < 3 m₂/(2^v − 1)`; the `m − m₂` minima outside the window
  contribute `< 3/X₀` each (Remark 7 again; Hercher uses Theorem 14 there, which is sharper).

With Theorem 16 this gives `theorem21_vertexFree`:

  `3 (p log 2 − K log 3) < 3 (m − m₂)/X₀ + 3 m₂/(2^v − 1)`

for every positive cycle whose elements are all `≥ X₀ > 0`, every `1 ≤ m₂ ≤ m`, `m` the number of
local minima. No premise on `m₂` is needed for the inequality itself (Hercher's premise only makes
it better than Theorem 14). `theorem14_crude` is the `m₂ = 0` analogue: `3 (p log 2 − K log 3) <
3 m/X₀`.

What is *not* here: the vertex bound (f) of the corrigendum, which replaces `m₂ f(v)` by
`f(v) + (m₂ − 1) f(δ v)` and is needed for the last unit `m = 91`, and Theorem 14 for the minima
outside the window.
-/

namespace Collatz

open Finset

/-! ### Periodic sequences -/

theorem periodic_add_mul {α : Type*} {f : ℕ → α} {m : ℕ} (hf : ∀ r, f (r + m) = f r)
    (r q : ℕ) : f (r + m * q) = f r := by
  induction q with
  | zero => simp
  | succ q ih => rw [Nat.mul_add, Nat.mul_one, ← Nat.add_assoc, hf, ih]

theorem periodic_mod {α : Type*} {f : ℕ → α} {m : ℕ} (hf : ∀ r, f (r + m) = f r) (r : ℕ) :
    f r = f (r % m) := by
  conv_lhs => rw [← Nat.mod_add_div r m]
  exact periodic_add_mul hf _ _

/-- A chain `x_{t+1} ≤ δ x_t` iterates to `x_{t+c} ≤ δ^c x_t`. -/
theorem chain_le (xs : ℕ → ℝ) {δ : ℝ} (hδ : 0 ≤ δ) (hstep : ∀ t, xs (t + 1) ≤ δ * xs t)
    (t c : ℕ) : xs (t + c) ≤ δ ^ c * xs t := by
  induction c with
  | zero => simp
  | succ c ih =>
    calc xs (t + (c + 1)) = xs ((t + c) + 1) := by rw [Nat.add_assoc]
      _ ≤ δ * xs (t + c) := hstep _
      _ ≤ δ * (δ ^ c * xs t) := mul_le_mul_of_nonneg_left ih hδ
      _ = δ ^ (c + 1) * xs t := by rw [pow_succ]; ring

/-- Inside a window whose chain closes up (`x_s ≤ δ x_{s+m₂−1}`), every element bounds the
window sum: `Σ_{b<m₂} x_{s+b} ≤ (Σ_{d<m₂} δ^d) x_{s+a}`. -/
theorem window_sum_le (xs : ℕ → ℝ) {δ : ℝ} (hδ : 0 ≤ δ) (hstep : ∀ t, xs (t + 1) ≤ δ * xs t)
    {s m₂ : ℕ} (hwrap : xs s ≤ δ * xs (s + m₂ - 1)) {a : ℕ} (ha : a < m₂) :
    ∑ b ∈ range m₂, xs (s + b) ≤ (∑ d ∈ range m₂, δ ^ d) * xs (s + a) := by
  have e1 := sum_range_add (fun b => xs (s + b)) a (m₂ - a)
  have e2 := sum_range_add (fun d => δ ^ d) (m₂ - a) a
  rw [show a + (m₂ - a) = m₂ by omega] at e1
  rw [show m₂ - a + a = m₂ by omega] at e2
  rw [e1, e2, add_mul, sum_mul, sum_mul]
  -- the part after `a`
  have h2 : ∑ c ∈ range (m₂ - a), xs (s + (a + c)) ≤ ∑ c ∈ range (m₂ - a), δ ^ c * xs (s + a) := by
    refine sum_le_sum (fun c _ => ?_)
    rw [← Nat.add_assoc]
    exact chain_le xs hδ hstep (s + a) c
  -- the part before `a`, through the wrap
  have hlast : xs (s + m₂ - 1) ≤ δ ^ (m₂ - 1 - a) * xs (s + a) := by
    have := chain_le xs hδ hstep (s + a) (m₂ - 1 - a)
    rwa [show s + a + (m₂ - 1 - a) = s + m₂ - 1 by omega] at this
  have h1 : ∑ b ∈ range a, xs (s + b) ≤ ∑ b ∈ range a, δ ^ (m₂ - a + b) * xs (s + a) := by
    refine sum_le_sum (fun b _ => ?_)
    have hb := chain_le xs hδ hstep s b
    have hδb : 0 ≤ δ ^ b := pow_nonneg hδ b
    calc xs (s + b) ≤ δ ^ b * xs s := hb
      _ ≤ δ ^ b * (δ * xs (s + m₂ - 1)) := mul_le_mul_of_nonneg_left hwrap hδb
      _ ≤ δ ^ b * (δ * (δ ^ (m₂ - 1 - a) * xs (s + a))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlast hδ) hδb
      _ = δ ^ (m₂ - a + b) * xs (s + a) := by
          rw [show m₂ - a + b = b + 1 + (m₂ - 1 - a) by omega]
          ring
  linarith

/-- **Steps (a), (b), (e) of Theorem 21**, for a periodic real sequence with `x_{t+1} ≤ δ x_t`:
some window of `m₂` consecutive terms has every term `x_{s+a}` with
`m₂ Σ_{r<m} x_r ≤ m (Σ_{d<m₂} δ^d) x_{s+a}`. -/
theorem exists_window (xs : ℕ → ℝ) {δ : ℝ} (hδ : 0 ≤ δ) (hstep : ∀ t, xs (t + 1) ≤ δ * xs t)
    {m m₂ : ℕ} (hm : 1 ≤ m) (hm₂ : 1 ≤ m₂) (hper : ∀ t, xs (t + m) = xs t) :
    ∃ s, ∀ a < m₂, (m₂ : ℝ) * ∑ r ∈ range m, xs r ≤
      (m : ℝ) * ((∑ d ∈ range m₂, δ ^ d) * xs (s + a)) := by
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
  -- the shift identity `W (t+1) + x_t = W t + x_{t+m₂}`
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
  -- the wrap `x_s ≤ δ x_{s+m₂-1}`
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
  -- the average of the window sums
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
  refine ⟨s, fun a ha => ?_⟩
  have hwin := window_sum_le xs hδ hstep hwrap ha
  have hm' : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have := mul_le_mul_of_nonneg_left hwin hm'
  simp only [hW] at hle havg
  linarith

/-! ### The minima of a cycle as a chain -/

/-- Lemma 8 for a minimum: `k ≤ log₂(n + 1)`. -/
theorem orun_le_logb (n : ℕ) : (orun n : ℝ) ≤ Real.logb 2 ((n : ℝ) + 1) := by
  have h := two_pow_le_of_odd_run (fun t (ht : t < orun n) => odd_of_lt_orun ht)
  rw [Real.le_logb_iff_rpow_le (by norm_num) (by positivity), Real.rpow_natCast]
  exact_mod_cast h

/-- The next minimum is at most `T^{k+1} n`. -/
theorem nextMin_le {n : ℕ} (hn : 0 < n) : nextMin n ≤ T^[orun n + 1] n := by
  show T^[orun n + erun n] n ≤ _
  exact iterate_le_of_even_run (erun_pos n) (fun s hs => even_of_lt_erun hn hs)

/-- **Lemma 20 for successive minima**, `log₂(n + 1)` form (step (d)):
`log₂(n_{i+1} + 1) < δ log₂(n_i + 1)`. -/
theorem logb_nextMin_lt {n : ℕ} (hn : 0 < n) (hodd : n % 2 = 1) :
    Real.logb 2 ((nextMin n : ℝ) + 1) < Real.logb 2 3 * Real.logb 2 ((n : ℝ) + 1) := by
  have hk := orun_pos hodd
  have hle := nextMin_le hn
  have hlt := succ_iterate_lt_rpow hk (fun t ht => odd_of_lt_orun ht) (orun_spec n)
  have hleR : ((nextMin n : ℕ) : ℝ) ≤ ((T^[orun n + 1] n : ℕ) : ℝ) := by exact_mod_cast hle
  have h1 : ((nextMin n : ℕ) : ℝ) + 1 < ((n : ℝ) + 1) ^ Real.logb 2 3 := by linarith
  rw [← Real.logb_rpow_eq_mul_logb_of_pos (b := 2) (y := Real.logb 2 3)
    (show (0 : ℝ) < (n : ℝ) + 1 by positivity)]
  exact Real.logb_lt_logb (by norm_num) (by positivity) h1

theorem nextMin_iterate_odd {x : ℕ} (hx : 0 < x) (hodd : x % 2 = 1) (r : ℕ) :
    nextMin^[r] x % 2 = 1 := by
  rcases r with _ | r
  · exact hodd
  · rw [Function.iterate_succ_apply']
    exact nextMin_odd (nextMin_iterate_pos hx r)

theorem nextMin_periodic {x p : ℕ} (hx : 0 < x) (hp : 0 < p) (hcyc : T^[p] x = x)
    (hmin : IsMinOf x p) (r : ℕ) : nextMin^[r + numLocalMin x p] x = nextMin^[r] x := by
  rw [Function.iterate_add_apply, nextMin_iterate_numLocalMin hx hp hcyc hmin]

/-- The window of Theorem 21 for a cycle through a local minimum `x`: some `m₂` consecutive
minima all satisfy `m₂ K ≤ m G log₂(n + 1)`. -/
theorem exists_window_minima {x p : ℕ} (hx : 0 < x) (hp : 0 < p) (hcyc : T^[p] x = x)
    (hmin : IsMinOf x p) {m₂ : ℕ} (hm₂ : 1 ≤ m₂) :
    ∃ s, ∀ a < m₂, (m₂ : ℝ) * (oddCount T x p : ℝ) ≤
      (numLocalMin x p : ℝ) * ((∑ d ∈ range m₂, Real.logb 2 3 ^ d) *
        Real.logb 2 ((nextMin^[s + a] x : ℝ) + 1)) := by
  have hm := (numLocalMin_eq_of_isMin hx hp hcyc hmin).2
  set xs : ℕ → ℝ := fun r => Real.logb 2 ((nextMin^[r] x : ℝ) + 1) with hxs
  have hδ : (0 : ℝ) ≤ Real.logb 2 3 := by linarith [one_le_logb_two_three]
  have hstep : ∀ t, xs (t + 1) ≤ Real.logb 2 3 * xs t := by
    intro t
    simp only [hxs]
    rw [Function.iterate_succ_apply']
    exact (logb_nextMin_lt (nextMin_iterate_pos hx t) (nextMin_iterate_odd hx hmin.1 t)).le
  have hper : ∀ t, xs (t + numLocalMin x p) = xs t := by
    intro t
    simp only [hxs]
    rw [nextMin_periodic hx hp hcyc hmin]
  obtain ⟨s, hs⟩ := exists_window xs hδ hstep hm hm₂ hper
  refine ⟨s, fun a ha => ?_⟩
  have h1 := hs a ha
  have hK : (oddCount T x p : ℝ) ≤ ∑ r ∈ range (numLocalMin x p), xs r := by
    rw [oddCount_eq_sum_orun hx hp hcyc hmin]
    push_cast
    exact sum_le_sum (fun r _ => orun_le_logb _)
  have hm₂' : (0 : ℝ) ≤ m₂ := Nat.cast_nonneg _
  have := mul_le_mul_of_nonneg_left hK hm₂'
  simp only [hxs] at h1 this
  linarith

/-! ### Theorem 21, vertex-free -/

/-- The exponent `v = m₂ K/(m G)` of Theorem 21, `G = Σ_{d<m₂} δ^d = (δ^{m₂} − 1)/(δ − 1)`. -/
noncomputable def windowExp (m m₂ K : ℕ) : ℝ :=
  (m₂ : ℝ) * K / ((m : ℝ) * ∑ d ∈ range m₂, Real.logb 2 3 ^ d)

theorem geomSum_delta_pos {m₂ : ℕ} (hm₂ : 1 ≤ m₂) : 0 < ∑ d ∈ range m₂, Real.logb 2 3 ^ d := by
  have hδ : (0 : ℝ) < Real.logb 2 3 := by linarith [one_le_logb_two_three]
  exact sum_pos (fun d _ => pow_pos hδ d) (nonempty_range_iff.mpr (by omega))

theorem K_pos_of_isMin {x p : ℕ} (hx : 0 < x) (hp : 0 < p) (hcyc : T^[p] x = x)
    (hmin : IsMinOf x p) : 1 ≤ oddCount T x p := by
  have h1 : oddCount T x 1 = 1 := by
    show oddCount T x 0 + T^[0] x % 2 = 1
    simp only [Function.iterate_zero, id_eq]
    rw [hmin.1]; rfl
  have := oddCount_mono T x (show 1 ≤ p by omega)
  omega

/-- The minima in the window of Theorem 21 are at least `2^v − 1`. -/
theorem window_minima_ge {x p : ℕ} (hx : 0 < x) (hp : 0 < p) (hcyc : T^[p] x = x)
    (hmin : IsMinOf x p) {m₂ : ℕ} (hm₂ : 1 ≤ m₂) :
    ∃ s, ∀ a < m₂, (2 : ℝ) ^ windowExp (numLocalMin x p) m₂ (oddCount T x p) ≤
      (nextMin^[s + a] x : ℝ) + 1 := by
  obtain ⟨s, hs⟩ := exists_window_minima hx hp hcyc hmin hm₂
  refine ⟨s, fun a ha => ?_⟩
  have hm : (0 : ℝ) < numLocalMin x p := by
    exact_mod_cast (numLocalMin_eq_of_isMin hx hp hcyc hmin).2
  have hG := geomSum_delta_pos hm₂
  have hpos : (0 : ℝ) < (nextMin^[s + a] x : ℝ) + 1 := by positivity
  rw [← Real.le_logb_iff_rpow_le (b := 2) (by norm_num) hpos, windowExp,
    div_le_iff₀ (mul_pos hm hG)]
  have := hs a ha
  linarith

/-- **Theorem 21, vertex-free form, sum form.** For a cycle through a local minimum `x` whose
elements are all `≥ X₀ > 0`, with `m` minima and `1 ≤ m₂ ≤ m`:
`Σ_r T(n_r) < 3 (m − m₂)/X₀ + 3 m₂/(2^v − 1)`. -/
theorem sum_riseSum_lt_window {x p : ℕ} (hx : 0 < x) (hp : 0 < p) (hcyc : T^[p] x = x)
    (hmin : IsMinOf x p) {m₂ : ℕ} (hm₂ : 1 ≤ m₂) (hm₂m : m₂ ≤ numLocalMin x p) {X₀ : ℝ}
    (hX₀ : 0 < X₀) (hlow : ∀ j, X₀ ≤ ((T^[j] x : ℕ) : ℝ)) :
    ∑ r ∈ range (numLocalMin x p), riseSum (nextMin^[r] x) (orun (nextMin^[r] x)) <
      3 * ((numLocalMin x p - m₂ : ℕ) : ℝ) / X₀ +
        3 * m₂ / ((2 : ℝ) ^ windowExp (numLocalMin x p) m₂ (oddCount T x p) - 1) := by
  obtain ⟨s, hs⟩ := window_minima_ge hx hp hcyc hmin hm₂
  have hK := K_pos_of_isMin hx hp hcyc hmin
  have hmpos : 0 < numLocalMin x p := (numLocalMin_eq_of_isMin hx hp hcyc hmin).2
  obtain ⟨v, hv⟩ : ∃ v, v = windowExp (numLocalMin x p) m₂ (oddCount T x p) := ⟨_, rfl⟩
  rw [← hv] at hs ⊢
  have hvpos : 0 < v := by
    rw [hv, windowExp]
    have hG := geomSum_delta_pos hm₂
    have h1 : (0 : ℝ) < numLocalMin x p := by exact_mod_cast hmpos
    have h2 : (0 : ℝ) < m₂ := by exact_mod_cast hm₂
    have h3 : (0 : ℝ) < oddCount T x p := by exact_mod_cast hK
    exact div_pos (mul_pos h2 h3) (mul_pos h1 hG)
  have h2v : (0 : ℝ) < (2 : ℝ) ^ v - 1 := by
    have : (1 : ℝ) < (2 : ℝ) ^ v := Real.one_lt_rpow (by norm_num) hvpos
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
  -- each minimum is a cycle element, hence `≥ X₀`
  have hmem : ∀ r, X₀ ≤ ((nextMin^[r] x : ℕ) : ℝ) := by
    intro r; rw [← iterate_minPos]; exact hlow _
  have hf_lt : ∀ r, f r < 3 / ((nextMin^[r] x : ℕ) : ℝ) := by
    intro r
    rw [hf]
    exact riseSum_lt (nextMin_iterate_pos hx r) (fun t ht => odd_of_lt_orun ht)
  -- the window
  have hwin : ∑ b ∈ range m₂, f (s + b) < ∑ b ∈ range m₂, 3 / ((2 : ℝ) ^ v - 1) := by
    refine sum_lt_sum_of_nonempty (nonempty_range_iff.mpr (by omega)) (fun b hb => ?_)
    have h1 := hs b (mem_range.mp hb)
    have h2 : (2 : ℝ) ^ v - 1 ≤ ((nextMin^[s + b] x : ℕ) : ℝ) := by linarith
    calc f (s + b) < 3 / ((nextMin^[s + b] x : ℕ) : ℝ) := hf_lt _
      _ ≤ 3 / ((2 : ℝ) ^ v - 1) := div_le_div_of_nonneg_left (by norm_num) h2v h2
  -- the minima outside the window
  have hout : ∑ c ∈ range (numLocalMin x p - m₂), f (s + (m₂ + c)) ≤
      ∑ c ∈ range (numLocalMin x p - m₂), 3 / X₀ := by
    refine sum_le_sum (fun c _ => ?_)
    calc f (s + (m₂ + c)) ≤ 3 / ((nextMin^[s + (m₂ + c)] x : ℕ) : ℝ) := (hf_lt _).le
      _ ≤ 3 / X₀ := div_le_div_of_nonneg_left (by norm_num) hX₀ (hmem _)
  rw [sum_const, card_range, nsmul_eq_mul] at hwin
  rw [sum_const, card_range, nsmul_eq_mul] at hout
  rw [hgoal, hrot, hsplit]
  have e1 : (m₂ : ℝ) * (3 / ((2 : ℝ) ^ v - 1)) = 3 * m₂ / ((2 : ℝ) ^ v - 1) := by ring
  have e2 : ((numLocalMin x p - m₂ : ℕ) : ℝ) * (3 / X₀) =
      3 * ((numLocalMin x p - m₂ : ℕ) : ℝ) / X₀ := by ring
  linarith

/-- **Theorem 21, vertex-free form**, for a cycle through a local minimum. -/
theorem theorem21_vertexFree_of_isMin {x p : ℕ} (hx : 0 < x) (hp : 0 < p) (hcyc : T^[p] x = x)
    (hmin : IsMinOf x p) {m₂ : ℕ} (hm₂ : 1 ≤ m₂) (hm₂m : m₂ ≤ numLocalMin x p) {X₀ : ℝ}
    (hX₀ : 0 < X₀) (hlow : ∀ j, X₀ ≤ ((T^[j] x : ℕ) : ℝ)) :
    3 * ((p : ℝ) * Real.log 2 - (oddCount T x p : ℝ) * Real.log 3) <
      3 * ((numLocalMin x p - m₂ : ℕ) : ℝ) / X₀ +
        3 * m₂ / ((2 : ℝ) ^ windowExp (numLocalMin x p) m₂ (oddCount T x p) - 1) :=
  lt_of_le_of_lt (theorem16_of_isMin hx hp hcyc hmin)
    (sum_riseSum_lt_window hx hp hcyc hmin hm₂ hm₂m hX₀ hlow)

/-- **Theorem 21, vertex-free form.** For every positive `T`-cycle of length `p` whose elements
are all `≥ X₀ > 0`, with `m = numLocalMin x p` local minima, `K` odd elements and `1 ≤ m₂ ≤ m`:
`3 (p log 2 − K log 3) < 3 (m − m₂)/X₀ + 3 m₂/(2^v − 1)`, `v = m₂ K (δ − 1)/(m (δ^{m₂} − 1))`. -/
theorem theorem21_vertexFree {x p : ℕ} (hx : 0 < x) (hp : 0 < p) (hcyc : T^[p] x = x)
    {m₂ : ℕ} (hm₂ : 1 ≤ m₂) (hm₂m : m₂ ≤ numLocalMin x p) {X₀ : ℝ}
    (hX₀ : 0 < X₀) (hlow : ∀ j, X₀ ≤ ((T^[j] x : ℕ) : ℝ)) :
    3 * ((p : ℝ) * Real.log 2 - (oddCount T x p : ℝ) * Real.log 3) <
      3 * ((numLocalMin x p - m₂ : ℕ) : ℝ) / X₀ +
        3 * m₂ / ((2 : ℝ) ^ windowExp (numLocalMin x p) m₂ (oddCount T x p) - 1) := by
  obtain ⟨i, _, hmin⟩ := exists_isMin_rotation (x := x) (p := p) (by omega)
  have hx' : 0 < T^[i] x := iterate_T_pos hx i
  have h := theorem21_vertexFree_of_isMin hx' hp (cycle_rotate hcyc i) hmin hm₂
    (by rw [numLocalMin_rotate hp hcyc]; exact hm₂m) hX₀
    (fun j => by rw [← Function.iterate_add_apply]; exact hlow _)
  rwa [numLocalMin_rotate hp hcyc, oddCount_rotate hcyc] at h

/-- **Remark 7 summed over the cycle** (a crude Theorem 14 with `m₁ = m`):
`3 (p log 2 − K log 3) < 3 m/X₀` for a cycle with `m ≥ 1` local minima, all elements `≥ X₀ > 0`. -/
theorem theorem14_crude {x p : ℕ} (hx : 0 < x) (hp : 0 < p) (hcyc : T^[p] x = x)
    (hm : 1 ≤ numLocalMin x p) {X₀ : ℝ} (hX₀ : 0 < X₀)
    (hlow : ∀ j, X₀ ≤ ((T^[j] x : ℕ) : ℝ)) :
    3 * ((p : ℝ) * Real.log 2 - (oddCount T x p : ℝ) * Real.log 3) <
      3 * (numLocalMin x p : ℝ) / X₀ := by
  obtain ⟨i, _, hmin⟩ := exists_isMin_rotation (x := x) (p := p) (by omega)
  set y := T^[i] x with hy
  have hy0 : 0 < y := iterate_T_pos hx i
  have hcy := cycle_rotate hcyc i
  rw [← hy] at hcy
  have hlowy : ∀ j, X₀ ≤ ((T^[j] y : ℕ) : ℝ) := fun j => by
    rw [hy, ← Function.iterate_add_apply]; exact hlow _
  have h16 := theorem16_of_isMin hy0 hp hcy hmin
  have hsum : ∑ r ∈ range (numLocalMin y p), riseSum (nextMin^[r] y) (orun (nextMin^[r] y)) <
      ∑ r ∈ range (numLocalMin y p), 3 / X₀ := by
    refine sum_lt_sum_of_nonempty
      (nonempty_range_iff.mpr (by rw [hy, numLocalMin_rotate hp hcyc]; omega)) (fun r _ => ?_)
    have h1 := riseSum_lt (k := orun (nextMin^[r] y)) (nextMin_iterate_pos hy0 r)
      (fun t ht => odd_of_lt_orun ht)
    have h2 : X₀ ≤ ((nextMin^[r] y : ℕ) : ℝ) := by rw [← iterate_minPos]; exact hlowy _
    exact lt_of_lt_of_le h1 (div_le_div_of_nonneg_left (by norm_num) hX₀ h2)
  rw [sum_const, card_range, nsmul_eq_mul] at hsum
  rw [hy, numLocalMin_rotate hp hcyc, oddCount_rotate hcyc] at h16
  rw [hy, numLocalMin_rotate hp hcyc] at hsum
  have e : (numLocalMin x p : ℝ) * (3 / X₀) = 3 * (numLocalMin x p : ℝ) / X₀ := by ring
  linarith

end Collatz
