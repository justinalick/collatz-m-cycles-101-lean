import Collatz.HercherLocal
import Collatz.HarmonicResidue
import Collatz.Statements

/-!
# The local minima of a cycle, and Hercher's Theorem 16

Hercher (Definition 6) lists the local minima `n₁, …, n_m` of an `m`-cycle in cyclic order, with
`kᵢ` the exact number of odd steps after `nᵢ` and `ℓᵢ` the exact number of even steps after those.
Here this is the orbit of one map on positive integers:

* `orun n` (Hercher's `k`): the least `k` with `T^k n` even;
* `erun n` (Hercher's `ℓ`): the least `ℓ ≥ 1` with `T^{k+ℓ} n` odd (or zero, which does not happen
  for `n > 0`);
* `nextMin n = T^{blen n} n`, `blen n = orun n + erun n`.

For a cycle through a local minimum `x` (`x` odd, `T^{p−1} x` even) the minima are
`nextMin^[r] x`, found at the positions `minPos x r` (`iterate_minPos`), and these are exactly the
local minima of the cycle (`exists_minPos_of_min`, `minPos_isMin`). Consequently
`numLocalMin x p = m` with `minPos x m = p` (`numLocalMin_eq_of_isMin`), the odd elements split
into the rises (`sum_oddPos_eq_sum_riseSum`, `oddCount_minPos`: `K = Σ kᵢ`), and **Theorem 16**
holds in the form `3 (p log 2 − K log 3) ≤ Σ_{r<m} T(n_r)` (`theorem16_of_isMin`). A cycle
with at least one local minimum can be rotated to start at one (`exists_isMin_rotation`), with
`numLocalMin`, `oddCount` and the reciprocal sum unchanged (`numLocalMin_rotate`,
`oddCount_rotate`).
-/

namespace Collatz

open Finset

theorem lt_two_pow_self' (n : ℕ) : n < 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ]; omega

theorem exists_even_iterate (n : ℕ) : ∃ k, T^[k] n % 2 = 0 := by
  by_contra h
  push_neg at h
  have h1 := two_pow_le_of_odd_run (k := n + 1) (n := n) (fun t _ => by have := h t; omega)
  have h2 := lt_two_pow_self' (n + 1)
  omega

/-- Hercher's `k`: the exact number of odd steps at `n`. -/
noncomputable def orun (n : ℕ) : ℕ := Nat.find (exists_even_iterate n)

theorem orun_spec (n : ℕ) : T^[orun n] n % 2 = 0 := Nat.find_spec (exists_even_iterate n)

theorem odd_of_lt_orun {n t : ℕ} (ht : t < orun n) : T^[t] n % 2 = 1 := by
  have : ¬ T^[t] n % 2 = 0 := Nat.find_min (exists_even_iterate n) ht
  omega

theorem orun_pos {n : ℕ} (h : n % 2 = 1) : 0 < orun n := by
  rcases Nat.eq_zero_or_pos (orun n) with h0 | h0
  · have := orun_spec n
    rw [h0] at this
    simp only [Function.iterate_zero, id_eq] at this
    omega
  · exact h0

/-- A run of `ℓ` even steps from position `k` divides by `2^ℓ`. -/
theorem iterate_even_run {n k : ℕ} : ∀ ℓ, (∀ s < ℓ, T^[k + s] n % 2 = 0) →
    T^[k] n = 2 ^ ℓ * T^[k + ℓ] n
  | 0, _ => by simp
  | ℓ + 1, h => by
    have ih := iterate_even_run ℓ (fun s hs => h s (by omega))
    have he := h ℓ (by omega)
    have hstep : T^[k + (ℓ + 1)] n = T^[k + ℓ] n / 2 := by
      rw [show k + (ℓ + 1) = (k + ℓ) + 1 by omega, Function.iterate_succ_apply' T (k + ℓ) n,
        T_even he]
    rw [hstep, ih, pow_succ]
    have : T^[k + ℓ] n = 2 * (T^[k + ℓ] n / 2) := by omega
    rw [Nat.mul_assoc, ← this]

theorem exists_odd_after (n : ℕ) :
    ∃ ℓ, 0 < ℓ ∧ (T^[orun n + ℓ] n % 2 = 1 ∨ T^[orun n + ℓ] n = 0) := by
  by_contra h
  push_neg at h
  set y := T^[orun n] n with hy
  have hev : ∀ s < y + 1, T^[orun n + s] n % 2 = 0 := by
    intro s _
    rcases Nat.eq_zero_or_pos s with h0 | h0
    · subst h0; simpa using orun_spec n
    · have := (h s h0).1
      omega
  have hdiv := iterate_even_run (y + 1) hev
  have hne := (h (y + 1) (by omega)).2
  have h2 := lt_two_pow_self' (y + 1)
  have h3 : 2 ^ (y + 1) ≤ 2 ^ (y + 1) * T^[orun n + (y + 1)] n :=
    Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hne)
  omega

/-- Hercher's `ℓ`: the exact number of even steps after the rise at `n`. -/
noncomputable def erun (n : ℕ) : ℕ := Nat.find (exists_odd_after n)

/-- The length of the block from the local minimum `n` to the next one. -/
noncomputable def blen (n : ℕ) : ℕ := orun n + erun n

/-- The next local minimum after `n`. -/
noncomputable def nextMin (n : ℕ) : ℕ := T^[blen n] n

theorem erun_pos (n : ℕ) : 0 < erun n := (Nat.find_spec (exists_odd_after n)).1

theorem nextMin_odd {n : ℕ} (hn : 0 < n) : nextMin n % 2 = 1 := by
  have h : T^[orun n + erun n] n % 2 = 1 ∨ T^[orun n + erun n] n = 0 :=
    (Nat.find_spec (exists_odd_after n)).2
  have hpos := iterate_T_pos hn (orun n + erun n)
  show T^[orun n + erun n] n % 2 = 1
  omega

theorem nextMin_pos {n : ℕ} (hn : 0 < n) : 0 < nextMin n := iterate_T_pos hn _

theorem even_of_lt_erun {n s : ℕ} (hn : 0 < n) (hs : s < erun n) :
    T^[orun n + s] n % 2 = 0 := by
  rcases Nat.eq_zero_or_pos s with h0 | h0
  · subst h0; simpa using orun_spec n
  · have h : ¬ (0 < s ∧ (T^[orun n + s] n % 2 = 1 ∨ T^[orun n + s] n = 0)) :=
      Nat.find_min (exists_odd_after n) hs
    have hpos := iterate_T_pos hn (orun n + s)
    omega

/-- The parity pattern of a block: odd before `orun n`, even from `orun n` to `blen n − 1`. -/
theorem parity_in_block {n d : ℕ} (hn : 0 < n) (hd : d < blen n) :
    T^[d] n % 2 = if d < orun n then 1 else 0 := by
  split_ifs with h
  · exact odd_of_lt_orun h
  · have := even_of_lt_erun (s := d - orun n) hn (by unfold blen at hd; omega)
    rwa [show orun n + (d - orun n) = d by omega] at this

/-! ### The minima of a cycle -/

/-- The position of the `r`-th local minimum after `x`. -/
noncomputable def minPos (x : ℕ) : ℕ → ℕ
  | 0 => 0
  | r + 1 => minPos x r + blen (nextMin^[r] x)

theorem nextMin_iterate_pos {x : ℕ} (hx : 0 < x) (r : ℕ) : 0 < nextMin^[r] x :=
  iterate_pos (fun _ h => nextMin_pos h) hx r

theorem iterate_minPos {x : ℕ} (r : ℕ) : T^[minPos x r] x = nextMin^[r] x := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [Function.iterate_succ_apply', ← ih]
    show T^[minPos x r + blen (nextMin^[r] x)] x =
      T^[blen (T^[minPos x r] x)] (T^[minPos x r] x)
    rw [ih, Nat.add_comm (minPos x r), Function.iterate_add_apply, ih]

theorem blen_pos (n : ℕ) : 0 < blen n := by unfold blen; have := erun_pos n; omega

theorem minPos_strictMono (x : ℕ) : StrictMono (minPos x) :=
  strictMono_nat_of_lt_succ fun r => by
    show minPos x r < minPos x r + blen (nextMin^[r] x)
    have := blen_pos (nextMin^[r] x); omega

theorem le_minPos (x r : ℕ) : r ≤ minPos x r := by
  induction r with
  | zero => exact Nat.zero_le _
  | succ r ih => have := minPos_strictMono x (show r < r + 1 by omega); omega

/-- Positions inside a block are read from the block's minimum. -/
theorem iterate_minPos_add (x r d : ℕ) : T^[minPos x r + d] x = T^[d] (nextMin^[r] x) := by
  rw [Nat.add_comm, Function.iterate_add_apply, iterate_minPos]

/-- Every local minimum at a position `j > 0` of the orbit of `x` is one of the `minPos x r`. -/
theorem exists_minPos_of_min {x j : ℕ} (hx : 0 < x) (hj : 0 < j) (hodd : T^[j] x % 2 = 1)
    (hev : T^[j - 1] x % 2 = 0) : ∃ r, minPos x r = j := by
  have hex : ∃ r, j ≤ minPos x (r + 1) := ⟨j, le_trans (by omega) (le_minPos x (j + 1))⟩
  set R := Nat.find hex with hR
  have hup : j ≤ minPos x (R + 1) := Nat.find_spec hex
  have hlo : minPos x R < j := by
    rcases Nat.eq_zero_or_pos R with h0 | h0
    · rw [h0]; show 0 < j; exact hj
    · obtain ⟨R', hR'⟩ : ∃ R', R = R' + 1 := ⟨R - 1, by omega⟩
      have : ¬ j ≤ minPos x (R' + 1) := Nat.find_min hex (show R' < Nat.find hex by omega)
      rw [hR']; omega
  rcases Nat.eq_or_lt_of_le hup with heq | hlt
  · exact ⟨R + 1, heq.symm⟩
  · exfalso
    have hlt' : j < minPos x R + blen (nextMin^[R] x) := hlt
    have hnpos : 0 < nextMin^[R] x := nextMin_iterate_pos hx R
    have hd : j - minPos x R < blen (nextMin^[R] x) := by omega
    have hodd' : T^[minPos x R + (j - minPos x R)] x % 2 = 1 := by
      rw [show minPos x R + (j - minPos x R) = j by omega]; exact hodd
    have hev' : T^[minPos x R + (j - minPos x R - 1)] x % 2 = 0 := by
      rw [show minPos x R + (j - minPos x R - 1) = j - 1 by omega]; exact hev
    rw [iterate_minPos_add] at hodd' hev'
    have p1 := parity_in_block hnpos hd
    have p2 := parity_in_block hnpos (show j - minPos x R - 1 < blen (nextMin^[R] x) by omega)
    split_ifs at p1 p2 <;> omega

/-- Each `minPos x (r + 1)` is a local minimum: odd, with an even predecessor. -/
theorem minPos_isMin {x : ℕ} (hx : 0 < x) (r : ℕ) :
    T^[minPos x (r + 1)] x % 2 = 1 ∧ T^[minPos x (r + 1) - 1] x % 2 = 0 := by
  have hnpos := nextMin_iterate_pos hx r
  constructor
  · rw [iterate_minPos, Function.iterate_succ_apply']
    exact nextMin_odd hnpos
  · have hb := blen_pos (nextMin^[r] x)
    rw [show minPos x (r + 1) - 1 = minPos x r + (blen (nextMin^[r] x) - 1) by
      show minPos x r + blen (nextMin^[r] x) - 1 = _; omega, iterate_minPos_add]
    have := parity_in_block hnpos (show blen (nextMin^[r] x) - 1 < blen (nextMin^[r] x) by omega)
    have he := erun_pos (nextMin^[r] x)
    rw [this]
    unfold blen
    split_ifs with h <;> omega

theorem iterate_add_period {x p : ℕ} (hcyc : T^[p] x = x) (j : ℕ) : T^[j + p] x = T^[j] x := by
  rw [Function.iterate_add_apply, hcyc]

/-- `x` is a local minimum of the cycle of length `p` through it. -/
abbrev IsMinOf (x p : ℕ) : Prop := x % 2 = 1 ∧ T^[p - 1] x % 2 = 0

/-- **The minima of a cycle.** For a cycle of length `p` through a local minimum `x`, the
`m = numLocalMin x p` local minima are `nextMin^[r] x`, `r < m`, at the positions `minPos x r`,
and `minPos x m = p`. -/
theorem numLocalMin_eq_of_isMin {x p : ℕ} (hx : 0 < x) (hp : 0 < p) (hcyc : T^[p] x = x)
    (hmin : IsMinOf x p) :
    minPos x (numLocalMin x p) = p ∧ 0 < numLocalMin x p := by
  -- `p` is a local-minimum position
  have hpodd : T^[p] x % 2 = 1 := by rw [hcyc]; exact hmin.1
  obtain ⟨m, hm⟩ := exists_minPos_of_min hx hp hpodd hmin.2
  have hmpos : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · rw [h0] at hm; simp [minPos] at hm; omega
    · exact h0
  have hsm := minPos_strictMono x
  -- the filter of `numLocalMin` is the image of `minPos` on `range m`
  have hset : (range p).filter (fun i => T^[i] x % 2 = 1 ∧ T^[i + p - 1] x % 2 = 0) =
      (range m).image (minPos x) := by
    ext i
    simp only [mem_filter, mem_range, mem_image]
    constructor
    · rintro ⟨hip, hodd, hev⟩
      rcases Nat.eq_zero_or_pos i with h0 | h0
      · exact ⟨0, hmpos, by subst h0; rfl⟩
      · have hev' : T^[i - 1] x % 2 = 0 := by
          rw [show i + p - 1 = (i - 1) + p by omega, iterate_add_period hcyc] at hev
          exact hev
        obtain ⟨r, hr⟩ := exists_minPos_of_min hx h0 hodd hev'
        refine ⟨r, ?_, hr⟩
        rw [← hm, ← hr] at hip
        exact hsm.lt_iff_lt.mp hip
    · rintro ⟨r, hr, rfl⟩
      refine ⟨by rw [← hm]; exact hsm hr, ?_⟩
      rcases r with _ | r
      · refine ⟨hmin.1, ?_⟩
        show T^[0 + p - 1] x % 2 = 0
        rw [Nat.zero_add]; exact hmin.2
      · have h := minPos_isMin hx r
        refine ⟨h.1, ?_⟩
        have hpos : 1 ≤ minPos x (r + 1) := le_trans (by omega) (le_minPos x (r + 1))
        rw [show minPos x (r + 1) + p - 1 = (minPos x (r + 1) - 1) + p by omega,
          iterate_add_period hcyc]
        exact h.2
  have hcard : numLocalMin x p = m := by
    unfold numLocalMin
    rw [hset, card_image_of_injective _ hsm.injective, card_range]
  rw [hcard]
  exact ⟨hm, hmpos⟩

theorem nextMin_iterate_numLocalMin {x p : ℕ} (hx : 0 < x) (hp : 0 < p) (hcyc : T^[p] x = x)
    (hmin : IsMinOf x p) : nextMin^[numLocalMin x p] x = x := by
  rw [← iterate_minPos, (numLocalMin_eq_of_isMin hx hp hcyc hmin).1, hcyc]

/-! ### Regrouping the odd elements by rises -/

/-- The odd positions of one block contribute `T(n)`. -/
theorem block_sum_eq_riseSum {n : ℕ} (hn : 0 < n) :
    ∑ d ∈ range (blen n), (if T^[d] n % 2 = 1 then 1 / ((T^[d] n : ℕ) : ℝ) else 0) =
      riseSum n (orun n) := by
  unfold blen
  rw [sum_range_add]
  have h1 : ∑ d ∈ range (orun n), (if T^[d] n % 2 = 1 then 1 / ((T^[d] n : ℕ) : ℝ) else 0) =
      riseSum n (orun n) := by
    unfold riseSum
    refine sum_congr rfl (fun d hd => ?_)
    rw [if_pos (odd_of_lt_orun (mem_range.mp hd))]
  have h2 : ∑ s ∈ range (erun n),
      (if T^[orun n + s] n % 2 = 1 then 1 / ((T^[orun n + s] n : ℕ) : ℝ) else 0) = 0 := by
    refine sum_eq_zero (fun s hs => ?_)
    have := even_of_lt_erun hn (mem_range.mp hs)
    rw [if_neg (by omega)]
  rw [h1, h2, add_zero]

theorem block_oddCount {n : ℕ} (hn : 0 < n) :
    ∑ d ∈ range (blen n), T^[d] n % 2 = orun n := by
  unfold blen
  rw [sum_range_add]
  have h1 : ∑ d ∈ range (orun n), T^[d] n % 2 = orun n := by
    rw [sum_congr rfl (fun d hd => odd_of_lt_orun (mem_range.mp hd)), sum_const, card_range,
      smul_eq_mul, mul_one]
  have h2 : ∑ s ∈ range (erun n), T^[orun n + s] n % 2 = 0 :=
    sum_eq_zero (fun s hs => even_of_lt_erun hn (mem_range.mp hs))
  rw [h1, h2, add_zero]

/-- The reciprocal sum over the odd positions before `minPos x R` is the sum of the rise sums of
the first `R` minima. -/
theorem sum_odd_minPos {x : ℕ} (hx : 0 < x) (R : ℕ) :
    ∑ i ∈ range (minPos x R), (if T^[i] x % 2 = 1 then 1 / ((T^[i] x : ℕ) : ℝ) else 0) =
      ∑ r ∈ range R, riseSum (nextMin^[r] x) (orun (nextMin^[r] x)) := by
  induction R with
  | zero => simp [minPos]
  | succ R ih =>
    rw [sum_range_succ, ← ih, ← block_sum_eq_riseSum (nextMin_iterate_pos hx R)]
    show ∑ i ∈ range (minPos x R + blen (nextMin^[R] x)), _ = _
    rw [sum_range_add]
    congr 1
    refine sum_congr rfl (fun d _ => ?_)
    rw [iterate_minPos_add]

/-- `K = Σ kᵢ`: the odd steps before `minPos x R` are the rises of the first `R` minima. -/
theorem oddCount_minPos {x : ℕ} (hx : 0 < x) (R : ℕ) :
    oddCount T x (minPos x R) = ∑ r ∈ range R, orun (nextMin^[r] x) := by
  induction R with
  | zero => simp [minPos, oddCount]
  | succ R ih =>
    rw [sum_range_succ, ← ih, ← block_oddCount (nextMin_iterate_pos hx R)]
    show oddCount T x (minPos x R + blen (nextMin^[R] x)) = _
    rw [oddCount_eq_sum_range, oddCount_eq_sum_range, sum_range_add]
    congr 1
    refine sum_congr rfl (fun d _ => ?_)
    rw [iterate_minPos_add]

theorem sum_oddPos_eq_sum_riseSum {x p : ℕ} (hx : 0 < x) (hp : 0 < p) (hcyc : T^[p] x = x)
    (hmin : IsMinOf x p) :
    ∑ i ∈ oddPos x p, (1 : ℝ) / ((T^[i] x : ℕ) : ℝ) =
      ∑ r ∈ range (numLocalMin x p), riseSum (nextMin^[r] x) (orun (nextMin^[r] x)) := by
  rw [oddPos, sum_filter, ← sum_odd_minPos hx, (numLocalMin_eq_of_isMin hx hp hcyc hmin).1]

theorem oddCount_eq_sum_orun {x p : ℕ} (hx : 0 < x) (hp : 0 < p) (hcyc : T^[p] x = x)
    (hmin : IsMinOf x p) :
    oddCount T x p = ∑ r ∈ range (numLocalMin x p), orun (nextMin^[r] x) := by
  rw [← oddCount_minPos hx, (numLocalMin_eq_of_isMin hx hp hcyc hmin).1]

/-- **Theorem 16** (upper half, in the form used by the chain), for a cycle through a local
minimum `x` with `m = numLocalMin x p` minima `n_r = nextMin^[r] x`:
`3 (p log 2 − K log 3) ≤ Σ_{r<m} T(n_r)`. -/
theorem theorem16_of_isMin {x p : ℕ} (hx : 0 < x) (hp : 0 < p) (hcyc : T^[p] x = x)
    (hmin : IsMinOf x p) :
    3 * ((p : ℝ) * Real.log 2 - (oddCount T x p : ℝ) * Real.log 3) ≤
      ∑ r ∈ range (numLocalMin x p), riseSum (nextMin^[r] x) (orun (nextMin^[r] x)) := by
  rw [← sum_oddPos_eq_sum_riseSum hx hp hcyc hmin]
  exact three_lambda_le_sum_inv hx hcyc

/-! ### Rotating a cycle to a local minimum -/

/-- Sums of a `p`-periodic function over a period do not depend on the starting point. -/
theorem sum_range_rotate {M : Type*} [AddCancelCommMonoid M] {p : ℕ} (g : ℕ → M)
    (hper : ∀ j, g (j + p) = g j) (i : ℕ) :
    ∑ j ∈ range p, g (i + j) = ∑ j ∈ range p, g j := by
  induction i with
  | zero => simp
  | succ i ih =>
    have h1 : ∑ j ∈ range (p + 1), g (i + j) = ∑ j ∈ range p, g (i + j) + g (i + p) :=
      sum_range_succ _ _
    have h2 : ∑ j ∈ range (p + 1), g (i + j) = ∑ j ∈ range p, g (i + (j + 1)) + g (i + 0) :=
      sum_range_succ' _ _
    have h3 : g (i + p) = g (i + 0) := by rw [hper, Nat.add_zero]
    have h4 : ∑ j ∈ range p, g (i + (j + 1)) + g (i + 0) =
        ∑ j ∈ range p, g (i + j) + g (i + 0) := by
      rw [← h2, h1, h3]
    have h5 := add_right_cancel h4
    rw [← ih, ← h5]
    refine sum_congr rfl (fun j _ => ?_)
    congr 1
    omega

theorem numLocalMin_rotate {x p : ℕ} (hp : 0 < p) (hcyc : T^[p] x = x) (i : ℕ) :
    numLocalMin (T^[i] x) p = numLocalMin x p := by
  unfold numLocalMin
  rw [card_filter, card_filter]
  let g : ℕ → ℕ := fun j => if T^[j] x % 2 = 1 ∧ T^[j + p - 1] x % 2 = 0 then 1 else 0
  have hper : ∀ j, g (j + p) = g j := by
    intro j
    simp only [g, iterate_add_period hcyc, show j + p + p - 1 = (j + p - 1) + p by omega]
  have e : ∀ j, (if T^[j] (T^[i] x) % 2 = 1 ∧ T^[j + p - 1] (T^[i] x) % 2 = 0 then 1 else 0) =
      g (i + j) := by
    intro j
    simp only [g, ← Function.iterate_add_apply, show j + i = i + j by omega,
      show j + p - 1 + i = i + j + p - 1 by omega]
  rw [sum_congr rfl (fun j _ => e j)]
  exact sum_range_rotate g hper i

theorem oddCount_rotate {x p : ℕ} (hcyc : T^[p] x = x) (i : ℕ) :
    oddCount T (T^[i] x) p = oddCount T x p := by
  rw [oddCount_eq_sum_range, oddCount_eq_sum_range]
  have e : ∀ j, T^[j] (T^[i] x) % 2 = T^[i + j] x % 2 := by
    intro j; rw [← Function.iterate_add_apply, Nat.add_comm j i]
  rw [sum_congr rfl (fun j _ => e j)]
  exact sum_range_rotate (fun j => T^[j] x % 2)
    (fun j => by show T^[j + p] x % 2 = T^[j] x % 2; rw [iterate_add_period hcyc]) i

theorem cycle_rotate {x p : ℕ} (hcyc : T^[p] x = x) (i : ℕ) : T^[p] (T^[i] x) = T^[i] x := by
  rw [← Function.iterate_add_apply, Nat.add_comm, Function.iterate_add_apply, hcyc]

/-- A cycle with a local minimum can be rotated to start at one. -/
theorem exists_isMin_rotation {x p : ℕ} (h : 0 < numLocalMin x p) :
    ∃ i, i < p ∧ IsMinOf (T^[i] x) p := by
  unfold numLocalMin at h
  obtain ⟨i, hi⟩ := card_pos.mp h
  rw [mem_filter, mem_range] at hi
  refine ⟨i, hi.1, hi.2.1, ?_⟩
  rw [← Function.iterate_add_apply, show p - 1 + i = i + p - 1 by omega]
  exact hi.2.2

end Collatz
