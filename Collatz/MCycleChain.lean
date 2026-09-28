import Collatz.MCycleSteps

/-!
# The chain bound (Theorem 8 of the `m = 92` note) and the exclusion of one cycle shape

For a cycle with `m` local minima, `K` odd elements and period `p`, label the minima cyclically from
the least element `n₀` of the cycle (`exists_least_rotation`) and put `x_t = log₂(n_t + 1)`. Then

* `x_{t+1} ≤ δ x_t` (Lemma 20, `logb_nextMin_lt`);
* `x_{t+2} ≤ x_t + (δ − 1) B − 2 + 2^{−S}` whenever `x_t ≤ N` and `TwoRiseBound N B`
  (`logb_two_step`, with `n_t > 2⁷¹`);
* `Σ_{t<m} x_t ≥ K` (Lemma 8: `k_t ≤ x_t`);
* `n₀ < U_b` from Theorem 21 with the floor `X₀ = n₀` (`lambda_lt_two`) and the lower bound
  `Λ > (p − K δ⁺) · 0.6931471803` for the given `(K, p)`.

The chain `Y₀ ≥ 2^S log₂ U_b`, `Y₁ = ⌈δ⁺ Y₀⌉`, `Y_{t+2} = min(⌈δ⁺ Y_{t+1}⌉, g(Y_t))` (`chainNext`,
integers standing for `y · 2^{−S}`, `δ⁺ = 1.584962501`) dominates `x_t` (`chain_sound`), so
`Σ_{t<m} Y_t < K 2^S` is a contradiction (`shape_false`). `shapeOK` is the Boolean certificate
check; the two-rise bounds are passed in as a list `grid` of pairs `(N, B)` with `TwoRiseBound N B`.
-/

namespace Collatz

open Finset

/-! ### The scaled chain -/

/-- `⌈1.584962501 · Y⌉`: the step `y ↦ δ y` in units of `2^{−S}`. -/
def chainF (Y : ℕ) : ℕ := (Y * 1584962501 + 999999999) / 1000000000

/-- `Y + ⌈0.584962501 · B · 2^S⌉ + 1 − 2 · 2^S`: the double step `y ↦ y + (δ − 1) B − 2 + 2^{−S}`. -/
def chainG (S B Y : ℕ) : ℕ := Y + (584962501 * B * 2 ^ S + 999999999) / 1000000000 + 1 - 2 * 2 ^ S

/-- The two-rise bound usable at `y = Y/2^S`: the first `(N, B)` of the grid with `Y ≤ N 2^S`. -/
def gridB (S Y : ℕ) : List (ℕ × ℕ) → Option ℕ
  | [] => none
  | e :: rest => if Y ≤ e.1 * 2 ^ S then some e.2 else gridB S Y rest

/-- `Y_{t+2}` from `Y_t = Yp` and `Y_{t+1} = Yc`. -/
def chainNext (S : ℕ) (grid : List (ℕ × ℕ)) (Yp Yc : ℕ) : ℕ :=
  match gridB S Yp grid with
  | none => chainF Yc
  | some B => if 2 * 2 ^ S ≤ Yp then min (chainF Yc) (chainG S B Yp) else chainF Yc

/-- The chain as a sequence. -/
def chainSeq (S : ℕ) (grid : List (ℕ × ℕ)) (Y0 : ℕ) : ℕ → ℕ
  | 0 => Y0
  | 1 => chainF Y0
  | t + 2 => chainNext S grid (chainSeq S grid Y0 t) (chainSeq S grid Y0 (t + 1))

theorem chainSeq_zero (S : ℕ) (grid : List (ℕ × ℕ)) (Y0 : ℕ) : chainSeq S grid Y0 0 = Y0 := by
  rw [chainSeq]

theorem chainSeq_one (S : ℕ) (grid : List (ℕ × ℕ)) (Y0 : ℕ) :
    chainSeq S grid Y0 1 = chainF Y0 := by
  rw [chainSeq]

theorem chainSeq_add_two (S : ℕ) (grid : List (ℕ × ℕ)) (Y0 t : ℕ) :
    chainSeq S grid Y0 (t + 2) =
      chainNext S grid (chainSeq S grid Y0 t) (chainSeq S grid Y0 (t + 1)) := by
  rw [chainSeq]

/-- The sum of the chain, by a loop (for the kernel): `chainSum f Y_t Y_{t+1} acc` adds
`Y_{t+1}, …, Y_{t+f}` to `acc`. -/
def chainSum (S : ℕ) (grid : List (ℕ × ℕ)) : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, _, _, acc => acc
  | f + 1, Yp, Yc, acc => chainSum S grid f Yc (chainNext S grid Yp Yc) (acc + Yc)

theorem chainSum_eq (S : ℕ) (grid : List (ℕ × ℕ)) (Y0 : ℕ) : ∀ f t acc,
    chainSum S grid f (chainSeq S grid Y0 t) (chainSeq S grid Y0 (t + 1)) acc =
      acc + ∑ i ∈ range f, chainSeq S grid Y0 (t + (i + 1)) := by
  intro f
  induction f with
  | zero => intro t acc; simp [chainSum]
  | succ f ih =>
    intro t acc
    have e : chainNext S grid (chainSeq S grid Y0 t) (chainSeq S grid Y0 (t + 1)) =
        chainSeq S grid Y0 (t + 1 + 1) := (chainSeq_add_two S grid Y0 t).symm
    rw [chainSum, e, ih (t + 1), sum_range_succ']
    simp only [Nat.zero_add]
    have h2 : ∑ i ∈ range f, chainSeq S grid Y0 (t + 1 + (i + 1)) =
        ∑ i ∈ range f, chainSeq S grid Y0 (t + (i + 1 + 1)) :=
      sum_congr rfl (fun i _ => by congr 1; omega)
    rw [h2]
    ring

/-- `Σ_{t<m} Y_t` is the loop `chainSum (m − 1) Y₀ Y₁ Y₀`. -/
theorem chainSum_start (S : ℕ) (grid : List (ℕ × ℕ)) (Y0 m : ℕ) (hm : 1 ≤ m) :
    chainSum S grid (m - 1) Y0 (chainF Y0) Y0 = ∑ t ∈ range m, chainSeq S grid Y0 t := by
  have h := chainSum_eq S grid Y0 (m - 1) 0 Y0
  have e1 : chainSeq S grid Y0 0 = Y0 := chainSeq_zero S grid Y0
  have e2 : chainSeq S grid Y0 (0 + 1) = chainF Y0 := chainSeq_one S grid Y0
  rw [e1, e2] at h
  rw [h]
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  rw [sum_range_succ', Nat.add_sub_cancel, e1]
  have h2 : ∑ i ∈ range k, chainSeq S grid Y0 (0 + (i + 1)) =
      ∑ i ∈ range k, chainSeq S grid Y0 (i + 1) :=
    sum_congr rfl (fun i _ => by congr 1; omega)
  rw [h2]
  ring

theorem gridB_some {S Y B : ℕ} : ∀ {grid : List (ℕ × ℕ)}, gridB S Y grid = some B →
    ∃ N, (N, B) ∈ grid ∧ Y ≤ N * 2 ^ S
  | [], h => by simp [gridB] at h
  | (N', B') :: rest, h => by
    unfold gridB at h
    split_ifs at h with hle
    · simp only [Option.some.injEq] at h
      subst h
      exact ⟨N', List.mem_cons.mpr (Or.inl rfl), hle⟩
    · obtain ⟨N, hN, hY⟩ := gridB_some h
      exact ⟨N, List.mem_cons.mpr (Or.inr hN), hY⟩

theorem chainF_ge (Y : ℕ) : (Y : ℝ) * (1584962501 / 1000000000) ≤ chainF Y := by
  have h : Y * 1584962501 ≤ chainF Y * 1000000000 := by
    unfold chainF
    have := Nat.div_add_mod (Y * 1584962501 + 999999999) 1000000000
    have := Nat.mod_lt (Y * 1584962501 + 999999999) (show 0 < 1000000000 by norm_num)
    omega
  have hR : ((Y * 1584962501 : ℕ) : ℝ) ≤ ((chainF Y * 1000000000 : ℕ) : ℝ) := by exact_mod_cast h
  push_cast at hR
  linarith

theorem chainG_ge {S B Y : ℕ} (hY : 2 * 2 ^ S ≤ Y) :
    (Y : ℝ) + (584962501 / 1000000000) * B * 2 ^ S + 1 - 2 * 2 ^ S ≤ chainG S B Y := by
  have hc : 584962501 * B * 2 ^ S ≤
      (584962501 * B * 2 ^ S + 999999999) / 1000000000 * 1000000000 := by
    have := Nat.div_add_mod (584962501 * B * 2 ^ S + 999999999) 1000000000
    have := Nat.mod_lt (584962501 * B * 2 ^ S + 999999999) (show 0 < 1000000000 by norm_num)
    omega
  have hcR : ((584962501 * B * 2 ^ S : ℕ) : ℝ) ≤
      (((584962501 * B * 2 ^ S + 999999999) / 1000000000 * 1000000000 : ℕ) : ℝ) := by
    exact_mod_cast hc
  push_cast at hcR
  have hsub : chainG S B Y = Y + (584962501 * B * 2 ^ S + 999999999) / 1000000000 + 1 - 2 * 2 ^ S :=
    rfl
  have hle : 2 * 2 ^ S ≤ Y + (584962501 * B * 2 ^ S + 999999999) / 1000000000 + 1 := by omega
  rw [hsub, Nat.cast_sub hle]
  push_cast
  linarith

/-- **The chain dominates.** For a sequence `x_t ≥ 0` with `x_{t+1} ≤ δ x_t` and the double step
`x_{t+2} ≤ x_t + (δ − 1) B − 2 + 2^{−S}` whenever `x_t ≤ N`, `(N, B)` in the grid, and
`x₀ ≤ Y₀/2^S`: `x_t ≤ Y_t/2^S` for every `t`. -/
theorem chain_sound {S : ℕ} {grid : List (ℕ × ℕ)} {Y0 : ℕ} {xs : ℕ → ℝ} {δ : ℝ}
    (hδ : δ ≤ 1584962501 / 1000000000) (hδ1 : 1 ≤ δ) (hx0 : ∀ t, 0 ≤ xs t)
    (hf : ∀ t, xs (t + 1) ≤ δ * xs t)
    (hg : ∀ t N B, (N, B) ∈ grid → xs t ≤ N →
      xs (t + 2) ≤ xs t + (δ - 1) * B - 2 + 1 / 2 ^ S)
    (h0 : xs 0 ≤ Y0 / 2 ^ S) : ∀ t, xs t ≤ chainSeq S grid Y0 t / 2 ^ S := by
  have hS : (0 : ℝ) < 2 ^ S := by positivity
  -- the single step
  have hF : ∀ t (Y : ℕ), xs t ≤ (Y : ℝ) / 2 ^ S → xs (t + 1) ≤ (chainF Y : ℝ) / 2 ^ S := by
    intro t Y h
    have h3 : δ * xs t ≤ (1584962501 / 1000000000) * ((Y : ℝ) / 2 ^ S) :=
      mul_le_mul hδ h (hx0 t) (by norm_num)
    have h4 : (1584962501 / 1000000000 : ℝ) * ((Y : ℝ) / 2 ^ S) ≤ (chainF Y : ℝ) / 2 ^ S := by
      rw [← mul_div_assoc]
      exact div_le_div_of_nonneg_right (by linarith [chainF_ge Y]) hS.le
    linarith [hf t]
  have key : ∀ t, xs t ≤ chainSeq S grid Y0 t / 2 ^ S ∧
      xs (t + 1) ≤ chainSeq S grid Y0 (t + 1) / 2 ^ S := by
    intro t
    induction t with
    | zero =>
      refine ⟨by rw [chainSeq_zero]; exact h0, ?_⟩
      rw [show (0 : ℕ) + 1 = 1 from rfl, chainSeq_one]
      exact hF 0 Y0 h0
    | succ t ih =>
      refine ⟨ih.2, ?_⟩
      obtain ⟨ih1, ih2⟩ := ih
      have hf2 := hF (t + 1) _ ih2
      have ih1' : xs t * 2 ^ S ≤ chainSeq S grid Y0 t := (le_div_iff₀ hS).mp ih1
      show xs (t + 2) ≤ (chainSeq S grid Y0 (t + 2) : ℝ) / 2 ^ S
      rw [chainSeq_add_two]
      unfold chainNext
      split
      · exact hf2
      · rename_i B hB
        split_ifs with hY
        · rw [Nat.cast_min, ← min_div_div_right hS.le]
          refine le_min hf2 ?_
          obtain ⟨N, hN, hYN⟩ := gridB_some hB
          have hYNR : (chainSeq S grid Y0 t : ℝ) ≤ N * 2 ^ S := by exact_mod_cast hYN
          have hxN : xs t ≤ N := le_of_mul_le_mul_right (by linarith) hS
          have hgt := hg t N B hN hxN
          have hG := chainG_ge (B := B) hY
          rw [le_div_iff₀ hS]
          have hB0 : (0 : ℝ) ≤ B := Nat.cast_nonneg _
          have h1 : (δ - 1) * B ≤ (584962501 / 1000000000) * B :=
            mul_le_mul_of_nonneg_right (by linarith) hB0
          have h1' := mul_le_mul_of_nonneg_right h1 hS.le
          have e : (1 : ℝ) / 2 ^ S * 2 ^ S = 1 := by field_simp
          have h2 : xs (t + 2) * 2 ^ S ≤
              (xs t + (δ - 1) * B - 2 + 1 / 2 ^ S) * 2 ^ S :=
            mul_le_mul_of_nonneg_right hgt hS.le
          have h2' : (xs t + (δ - 1) * B - 2 + 1 / 2 ^ S) * 2 ^ S =
              xs t * 2 ^ S + (δ - 1) * B * 2 ^ S - 2 * 2 ^ S + 1 / 2 ^ S * 2 ^ S := by ring
          rw [h2', e] at h2
          linarith
        · exact hf2
  exact fun t => (key t).1

/-! ### The certificate for one shape -/

/-- A shape `(K, p)` of an `m`-cycle and its exclusion data: Theorem 21 with `m₂`, `N ≤ v`,
`M ≤ τ` gives `n₀ < U_b` for the least element; `U_b^Q ≤ 2^{Pe}` gives `x₀ ≤ Pe/Q`. -/
structure ShapeCert where
  K : ℕ
  P : ℕ
  m₂ : ℕ
  N : ℕ
  M : ℕ
  Ub : ℕ
  Pe : ℕ
  Q : ℕ

/-- The lower bound for `Λ − 1/(2^N − 1) − (m₂ − 1)/(2^M − 1)`. -/
def ShapeCert.room (c : ShapeCert) : ℚ :=
  ((c.P : ℚ) - c.K * deltaHi) * (6931471803 / 10 ^ 10) - 1 / (2 ^ c.N - 1) -
    ((c.m₂ - 1 : ℕ) : ℚ) / (2 ^ c.M - 1)

/-- The rational side conditions of the bound `n₀ < U_b`. -/
def uOK (m : ℕ) (c : ShapeCert) : Bool :=
  decide (1 ≤ c.m₂ ∧ c.m₂ ≤ m ∧ 1 ≤ c.N ∧ 1 ≤ c.M ∧
    (c.N : ℚ) * m * geomQ deltaUp c.m₂ ≤ c.m₂ * c.K ∧
    (c.M : ℚ) * m * (1 + geomQ deltaUp (c.m₂ - 1)) ≤ c.m₂ * c.K ∧
    (c.K : ℚ) * deltaHi ≤ c.P ∧ 0 < c.room ∧ ((m - c.m₂ : ℕ) : ℚ) ≤ c.Ub * c.room)

/-- The start of the chain, `⌈2^S Pe/Q⌉`. -/
def ShapeCert.Y0 (c : ShapeCert) (S : ℕ) : ℕ := (c.Pe * 2 ^ S + c.Q - 1) / c.Q

/-- **The certificate check for one shape**: the bound `n₀ < U_b`, and either `U_b ≤ 2⁷¹ + 1`
(no element exceeds `2⁷¹` then), or `U_b^Q ≤ 2^{Pe}` and the chain sum is below `K 2^S`. -/
def shapeOK (m S : ℕ) (grid : List (ℕ × ℕ)) (c : ShapeCert) : Bool :=
  uOK m c && (decide (c.Ub ≤ 2 ^ 71 + 1) ||
    (decide (1 ≤ c.Q) && decide (c.Ub ^ c.Q ≤ 2 ^ c.Pe) &&
      decide (chainSum S grid (m - 1) (c.Y0 S) (chainF (c.Y0 S)) (c.Y0 S) < c.K * 2 ^ S)))

/-- **`n₀ < U_b`** for the least element `y` of a cycle of the given shape. -/
theorem least_lt_Ub {y p m : ℕ} (hy : 0 < y) (hp : 0 < p) (hcyc : T^[p] y = y)
    (hleast : ∀ j, y ≤ T^[j] y) (c : ShapeCert) (hm : numLocalMin y p = m)
    (hK : oddCount T y p = c.K) (hP : p = c.P) (hok : uOK m c = true) : (y : ℝ) < c.Ub := by
  simp only [uOK, decide_eq_true_eq] at hok
  obtain ⟨hm1, hm2, hN1, hM1, hN, hM, hKP, hroom, hUb⟩ := hok
  have hyR : (0 : ℝ) < y := by exact_mod_cast hy
  have hlam := lambda_lt_two hy hp hcyc hm hm1 hm2 hyR (fun j => by exact_mod_cast hleast j)
    (Kp := c.K) (le_of_eq hK.symm) hN1 hM1 hN hM
  rw [hK, hP] at hlam
  -- `Λ > (p − K δ⁺) · 0.6931471803`
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have h3 : Real.log 3 = Real.logb 2 3 * Real.log 2 := by
    have := hlog2.ne'
    rw [Real.logb]
    field_simp
  have hδ := logb_lt_deltaHi
  have hKP' : (c.K : ℝ) * (deltaHi : ℝ) ≤ c.P := by exact_mod_cast hKP
  have hl2 := log_two_gt'
  have hlam2 : ((c.P : ℝ) - c.K * (deltaHi : ℝ)) * (6931471803 / 10 ^ 10) ≤
      (c.P : ℝ) * Real.log 2 - (c.K : ℝ) * Real.log 3 := by
    rw [h3]
    have hK0 : (0 : ℝ) ≤ c.K := Nat.cast_nonneg _
    have a1 : (c.K : ℝ) * Real.logb 2 3 ≤ c.K * (deltaHi : ℝ) :=
      mul_le_mul_of_nonneg_left hδ.le hK0
    have a2 : ((c.P : ℝ) - c.K * (deltaHi : ℝ)) * (6931471803 / 10 ^ 10) ≤
        ((c.P : ℝ) - c.K * (deltaHi : ℝ)) * Real.log 2 :=
      mul_le_mul_of_nonneg_left hl2.le (by linarith)
    nlinarith
  -- the room
  have hroomR : ((c.room : ℚ) : ℝ) = ((c.P : ℝ) - c.K * (deltaHi : ℝ)) * (6931471803 / 10 ^ 10) -
      1 / ((2 : ℝ) ^ c.N - 1) - ((c.m₂ - 1 : ℕ) : ℝ) / ((2 : ℝ) ^ c.M - 1) := by
    simp only [ShapeCert.room]
    push_cast <;> ring
  have hroomPos : (0 : ℝ) < ((c.room : ℚ) : ℝ) := by exact_mod_cast hroom
  have hUbR : ((m - c.m₂ : ℕ) : ℝ) ≤ (c.Ub : ℝ) * ((c.room : ℚ) : ℝ) := by exact_mod_cast hUb
  -- `(m − m₂)/y > room`
  have hmain : ((c.room : ℚ) : ℝ) < ((m - c.m₂ : ℕ) : ℝ) / y := by
    rw [hroomR]; linarith
  rw [lt_div_iff₀ hyR] at hmain
  by_contra hge
  push_neg at hge
  have : (c.Ub : ℝ) * ((c.room : ℚ) : ℝ) ≤ y * ((c.room : ℚ) : ℝ) :=
    mul_le_mul_of_nonneg_right hge hroomPos.le
  linarith

/-- The sum over the minima: `K ≤ Σ_{t<m} log₂(n_t + 1)`. -/
theorem K_le_sum_logb {y p : ℕ} (hy : 0 < y) (hp : 0 < p) (hcyc : T^[p] y = y)
    (hmin : IsMinOf y p) :
    (oddCount T y p : ℝ) ≤
      ∑ t ∈ range (numLocalMin y p), Real.logb 2 ((nextMin^[t] y : ℕ) + 1 : ℝ) := by
  rw [oddCount_eq_sum_orun hy hp hcyc hmin]
  push_cast
  exact sum_le_sum (fun t _ => orun_le_logb _)

/-- **The exclusion of one shape.** A cycle whose elements all exceed `2⁷¹`, with `m` local
minima, `K` odd elements and period `p` as in a certificate accepted by `shapeOK` (with two-rise
bounds for the grid, `S ≤ 60`), does not exist. -/
theorem shape_false {x p : ℕ} (hx : 0 < x) (hp : 0 < p) (hcyc : T^[p] x = x)
    (hlow : ∀ j, 2 ^ 71 < T^[j] x) {m S : ℕ} {grid : List (ℕ × ℕ)}
    (hgrid : ∀ e ∈ grid, TwoRiseBound e.1 e.2) (hS : S ≤ 60) (c : ShapeCert)
    (hm : numLocalMin x p = m) (hK : oddCount T x p = c.K) (hP : p = c.P)
    (hok : shapeOK m S grid c = true) : False := by
  obtain ⟨i, hmin, hleast⟩ := exists_least_rotation hx hp hcyc
  set y := T^[i] x with hy_def
  have hy : 0 < y := iterate_T_pos hx i
  have hcy : T^[p] y = y := cycle_rotate hcyc i
  have hmy : numLocalMin y p = m := by rw [hy_def, numLocalMin_rotate hp hcyc]; exact hm
  have hKy : oddCount T y p = c.K := by rw [hy_def, oddCount_rotate hcyc]; exact hK
  have hlowy : ∀ j, 2 ^ 71 < T^[j] y := fun j => by
    rw [hy_def, ← Function.iterate_add_apply]; exact hlow _
  have hleasty : ∀ j, y ≤ T^[j] y := fun j => by
    rw [hy_def, ← Function.iterate_add_apply]; exact hleast _
  simp only [shapeOK, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hok
  obtain ⟨hu, hrest⟩ := hok
  have hlt := least_lt_Ub hy hp hcy hleasty c hmy hKy hP hu
  have hy71 : 2 ^ 71 < y := by
    have := hlowy 0
    simpa using this
  have hltN : y < c.Ub := by exact_mod_cast hlt
  rcases hrest with hsmall | ⟨⟨hQ, hUbQ⟩, hsum⟩
  · -- `y < U_b ≤ 2⁷¹ + 1`
    omega
  · -- the chain
    have hm1 : 1 ≤ m := by rw [← hmy]; exact (numLocalMin_eq_of_isMin hy hp hcy hmin).2
    set xs : ℕ → ℝ := fun t => Real.logb 2 ((nextMin^[t] y : ℕ) + 1 : ℝ) with hxs
    have hδ1 := one_le_logb_two_three
    have hδ : Real.logb 2 3 ≤ 1584962501 / 1000000000 := by
      have h := logb_le_deltaUp
      have e : ((deltaUp : ℚ) : ℝ) = 1584962501 / 1000000000 := by norm_num [deltaUp]
      linarith
    have hx0 : ∀ t, 0 ≤ xs t := fun t =>
      Real.logb_nonneg (by norm_num) (by linarith [Nat.cast_nonneg (α := ℝ) (nextMin^[t] y)])
    have hodd : ∀ t, nextMin^[t] y % 2 = 1 := nextMin_iterate_odd hy hmin.1
    have hbig : ∀ t, 2 ^ 71 < nextMin^[t] y := fun t => by
      rw [← iterate_minPos]; exact hlowy _
    have hf : ∀ t, xs (t + 1) ≤ Real.logb 2 3 * xs t := by
      intro t
      simp only [hxs]
      rw [Function.iterate_succ_apply']
      exact (logb_nextMin_lt (nextMin_iterate_pos hy t) (hodd t)).le
    have hg : ∀ t N B, (N, B) ∈ grid → xs t ≤ N →
        xs (t + 2) ≤ xs t + (Real.logb 2 3 - 1) * B - 2 + 1 / 2 ^ S := by
      intro t N B hNB hxN
      have htr : TwoRiseBound N B := hgrid (N, B) hNB
      have hnt : nextMin^[t] y < 2 ^ N := by
        have hpos : (0 : ℝ) < ((nextMin^[t] y : ℕ) : ℝ) + 1 := by positivity
        have h1 : ((nextMin^[t] y : ℕ) : ℝ) + 1 ≤ 2 ^ (N : ℝ) := by
          rw [← Real.logb_le_iff_le_rpow (by norm_num) hpos]
          exact hxN
        rw [Real.rpow_natCast] at h1
        have h2 : nextMin^[t] y + 1 ≤ 2 ^ N := by exact_mod_cast h1
        omega
      have hkk := htr _ (hodd t) hnt
      have h2 := logb_two_step (hodd t)
      have e2 : nextMin (nextMin (nextMin^[t] y)) = nextMin^[t + 2] y := by
        rw [show t + 2 = t + 1 + 1 from rfl, Function.iterate_succ_apply',
          Function.iterate_succ_apply']
      rw [e2] at h2
      have hkR : ((orun (nextMin^[t] y) + orun (nextMin (nextMin^[t] y)) : ℕ) : ℝ) ≤ B := by
        exact_mod_cast hkk
      have hδ0 : (0 : ℝ) ≤ Real.logb 2 3 - 1 := by linarith
      have h3 := mul_le_mul_of_nonneg_left hkR hδ0
      have h6 : 6 / (((nextMin^[t] y : ℕ) : ℝ) + 1) ≤ 1 / 2 ^ S := by
        have hbigR : ((2 ^ 71 : ℕ) : ℝ) < ((nextMin^[t] y : ℕ) : ℝ) := by exact_mod_cast hbig t
        push_cast at hbigR
        have hS2 : (2 : ℝ) ^ S ≤ 2 ^ 60 := pow_le_pow_right₀ (by norm_num) hS
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have h60 : (2 : ℝ) ^ 60 * 6 ≤ 2 ^ 71 := by norm_num
        nlinarith
      simp only [hxs]
      linarith
    have hY0 : xs 0 ≤ (c.Y0 S : ℝ) / 2 ^ S := by
      simp only [hxs, Function.iterate_zero, id_eq]
      -- `log₂(y + 1) ≤ log₂ U_b ≤ Pe/Q ≤ Y₀/2^S`
      have hy1 : ((y : ℕ) : ℝ) + 1 ≤ c.Ub := by
        have h' : y + 1 ≤ c.Ub := hltN
        exact_mod_cast h'
      have hQR : (0 : ℝ) < c.Q := by exact_mod_cast hQ
      have hUbpos : (0 : ℝ) < c.Ub := by linarith [Nat.cast_nonneg (α := ℝ) y]
      have hA : Real.logb 2 (((y : ℕ) : ℝ) + 1) ≤ Real.logb 2 c.Ub :=
        Real.logb_le_logb_of_le (by norm_num) (by positivity) hy1
      have hB : (c.Q : ℝ) * Real.logb 2 c.Ub ≤ c.Pe := by
        have h1 : ((c.Ub ^ c.Q : ℕ) : ℝ) ≤ ((2 ^ c.Pe : ℕ) : ℝ) := by exact_mod_cast hUbQ
        push_cast at h1
        have h2 := Real.logb_le_logb_of_le (b := 2) (by norm_num) (pow_pos hUbpos _) h1
        rw [Real.logb_pow, Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one] at h2
        exact h2
      have hC : (c.Pe : ℝ) * 2 ^ S ≤ (c.Y0 S : ℝ) * c.Q := by
        have h : c.Pe * 2 ^ S ≤ c.Y0 S * c.Q := by
          unfold ShapeCert.Y0
          have := Nat.div_add_mod (c.Pe * 2 ^ S + c.Q - 1) c.Q
          have := Nat.mod_lt (c.Pe * 2 ^ S + c.Q - 1) (show 0 < c.Q by omega)
          have : (c.Pe * 2 ^ S + c.Q - 1) / c.Q * c.Q = c.Q * ((c.Pe * 2 ^ S + c.Q - 1) / c.Q) :=
            Nat.mul_comm _ _
          omega
        exact_mod_cast h
      have hS0 : (0 : ℝ) < 2 ^ S := by positivity
      rw [le_div_iff₀ hS0]
      have hD : Real.logb 2 (((y : ℕ) : ℝ) + 1) * c.Q ≤ c.Pe := by
        have := mul_le_mul_of_nonneg_right hA hQR.le
        linarith
      have hD' := mul_le_mul_of_nonneg_right hD hS0.le
      have hE : Real.logb 2 (((y : ℕ) : ℝ) + 1) * 2 ^ S * c.Q ≤ (c.Y0 S : ℝ) * c.Q := by
        have e : Real.logb 2 (((y : ℕ) : ℝ) + 1) * 2 ^ S * c.Q =
            Real.logb 2 (((y : ℕ) : ℝ) + 1) * c.Q * 2 ^ S := by ring
        rw [e]
        linarith
      exact le_of_mul_le_mul_right hE hQR
    have hdom := chain_sound (grid := grid) hδ hδ1 hx0 hf hg hY0
    have hsumK := K_le_sum_logb hy hp hcy hmin
    rw [hKy, hmy] at hsumK
    have hsumY : ∑ t ∈ range m, xs t ≤ ∑ t ∈ range m, (chainSeq S grid (c.Y0 S) t : ℝ) / 2 ^ S :=
      sum_le_sum (fun t _ => hdom t)
    rw [chainSum_start S grid (c.Y0 S) m hm1] at hsum
    have hsumR : (∑ t ∈ range m, (chainSeq S grid (c.Y0 S) t : ℝ)) < c.K * 2 ^ S := by
      have : ((∑ t ∈ range m, chainSeq S grid (c.Y0 S) t : ℕ) : ℝ) < ((c.K * 2 ^ S : ℕ) : ℝ) := by
        exact_mod_cast hsum
      push_cast at this
      exact this
    rw [← sum_div] at hsumY
    have hS0 : (0 : ℝ) < 2 ^ S := by positivity
    have : (∑ t ∈ range m, (chainSeq S grid (c.Y0 S) t : ℝ)) / 2 ^ S < c.K := by
      rw [div_lt_iff₀ hS0]; exact hsumR
    simp only [hxs] at hsumY
    linarith

end Collatz
