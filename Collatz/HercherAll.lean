import Collatz.HercherRhin

/-!
# Hercher's theorem: every nontrivial cycle has at least 92 local minima

`HercherTheorem` (`Statements.lean`), from two hypotheses: the verification bound (every
`0 < n ≤ X₀ = 695 · 2⁶⁰` reaches 1, Bařina) and `RhinBound` (Simons–de Weger's Lemma 12, from
Rhin's transcendence measure). Everything else is proved: for each `m = 1, …, 91` a bootstrap
chain from `K ≥ 1` (Remark 7 summed, `theorem14_crude`, while no window helps; then Theorem 21
with the two-element bound, `theorem21_two`, with the best `m₂`) raises the lower bound on `K` to
some `K_f(m)`, and Lemma 7 with the Rhin bound (`K_lt_of_rhinOK`, the argument of `K_lt_of_rhin`
for general `m`) shows `K < K_f(m)`; a cycle has at least one local minimum
(`numLocalMin_pos`).

The chains are data (`hercherData`: 234 steps over the 91 values of `m`, at most 8 per `m`), checked
by the kernel, one evaluation per `m` (`hercherData_ok`), of the Boolean checkers `chainOK` and `rhinOK`,
whose soundness is proved (`chainOK_sound`, `K_lt_of_rhinOK`). The certificates were computed with
exact rational arithmetic from the same bounds (Farey neighbours of `(deltaLo, deltaHi + ε)`,
`N ≤ v`, `M ≤ τ` with `δ ≤ 1.584962501`, `log 2 > 0.6931471803`).

Neither Theorem 14 (Hercher's `97/54`) nor the corrigendum's convex-vertex argument is used, and
neither is Simons–de Weger's seed, champion table or lattice reduction.
-/

namespace Collatz

open Finset

/-! ### A cycle has a local minimum -/

/-- A positive cycle has at least one local minimum: otherwise all its elements have the same
parity, and then `3^p < 2^p` (all odd) or `2^p ≤ 1` (all even). -/
theorem numLocalMin_pos {x p : ℕ} (hx : 0 < x) (hp : 0 < p) (hcyc : T^[p] x = x) :
    0 < numLocalMin x p := by
  by_contra h0
  push_neg at h0
  have hnone : ∀ i < p, ¬ (T^[i] x % 2 = 1 ∧ T^[i + p - 1] x % 2 = 0) := by
    intro i hi hc
    have hmem : i ∈ (range p).filter (fun i => T^[i] x % 2 = 1 ∧ T^[i + p - 1] x % 2 = 0) :=
      mem_filter.mpr ⟨mem_range.mpr hi, hc⟩
    have := card_pos.mpr ⟨i, hmem⟩
    unfold numLocalMin at h0
    omega
  have hcb := cycle_bounds hx hp hcyc (m := 1) one_pos (fun i _ _ => iterate_T_pos hx i)
  rcases Nat.mod_two_eq_zero_or_one x with hev | hodd
  · -- all even
    have hall : ∀ i < p, T^[i] x % 2 = 0 := by
      intro i
      induction i with
      | zero => intro _; exact hev
      | succ i ih =>
        intro hi
        have h1 := ih (by omega)
        have h2 := hnone (i + 1) hi
        rw [show i + 1 + p - 1 = i + p by omega, iterate_add_period hcyc] at h2
        omega
    have hK : oddCount T x p = 0 := by
      rw [oddCount_eq_sum_range]
      exact sum_eq_zero (fun i hi => hall i (mem_range.mp hi))
    have h2 := hcb.2
    rw [hK, pow_zero] at h2
    have : (1 : ℚ) < 2 ^ p := one_lt_pow₀ (by norm_num) hp.ne'
    linarith
  · -- all odd
    have hall : ∀ j ≤ p, T^[p - j] x % 2 = 1 := by
      intro j
      induction j with
      | zero => intro _; rw [Nat.sub_zero, hcyc]; exact hodd
      | succ j ih =>
        intro hj
        have h1 := ih (by omega)
        rcases Nat.eq_zero_or_pos j with hj0 | hj0
        · subst hj0
          have h2 := hnone 0 hp
          rw [Function.iterate_zero, id_eq, Nat.zero_add] at h2
          have : T^[p - 1] x % 2 = 1 := by omega
          simpa using this
        · have h2 := hnone (p - j) (by omega)
          rw [show p - j + p - 1 = (p - (j + 1)) + p by omega, iterate_add_period hcyc] at h2
          omega
    have hK : oddCount T x p = p := by
      rw [oddCount_eq_sum_range]
      have : ∀ i ∈ range p, T^[i] x % 2 = 1 := by
        intro i hi
        have := hall (p - i) (by omega)
        rwa [show p - (p - i) = i by have := mem_range.mp hi; omega] at this
      rw [sum_congr rfl this, sum_const, card_range, smul_eq_mul, mul_one]
    have h1 := hcb.1
    rw [hK] at h1
    have : (2 : ℚ) ^ p ≤ 3 ^ p := pow_le_pow_left₀ (by norm_num) (by norm_num) p
    linarith

theorem oddCount_pos_of_numLocalMin_pos {x p : ℕ} (h : 0 < numLocalMin x p) :
    1 ≤ oddCount T x p := by
  unfold numLocalMin at h
  obtain ⟨i, hi⟩ := Finset.card_pos.mp h
  rw [Finset.mem_filter, Finset.mem_range] at hi
  have h1 : oddCount T x (i + 1) = oddCount T x i + 1 := by rw [oddCount_succ, hi.2.1]
  have h2 : oddCount T x (i + 1) ≤ oddCount T x p := oddCount_mono T x (by omega)
  omega

/-! ### Chain certificates -/

/-- One step of a chain: `m₂ = 0` means Remark 7 summed (`ratioIn_of_crude`), otherwise
Theorem 21 with the two-element bound (`ratioIn_of_window_two`) with `N ≤ v`, `M ≤ τ`; `ε` and the
Farey neighbours `a/b < c/d` of `(deltaLo, deltaHi + ε)`. -/
structure ChainStep where
  m₂ : ℕ
  N : ℕ
  M : ℕ
  eps : ℚ
  a : ℤ
  b : ℕ
  c : ℤ
  d : ℕ

/-- The data for one `m`: the chain from `K ≥ 1` to `K ≥ Kf`, and `V ≤ Kf/G_m`,
`G_m ≤ 2^cexp`, `2m ≤ 2^kexp` for the Rhin contradiction. -/
structure Entry where
  steps : List ChainStep
  Kf : ℕ
  V : ℕ
  cexp : ℕ
  kexp : ℕ

/-- `X₀ = 695 · 2⁶⁰`. -/
def hercherX₀ : ℕ := 695 * 2 ^ 60

/-- The rational side conditions of one chain step at the premise `K ≥ Kp`. -/
def stepOK (m Kp : ℕ) (s : ChainStep) : Bool :=
  decide (0 < Kp ∧ 0 < s.eps ∧ 0 < s.b ∧ 0 < s.d ∧ s.c * s.b - s.a * s.d = 1 ∧
    (s.a : ℚ) / s.b ≤ deltaLo ∧ deltaHi + s.eps ≤ (s.c : ℚ) / s.d) &&
  (if s.m₂ = 0 then decide ((m : ℚ) / hercherX₀ ≤ s.eps * Kp * (6931471803 / 10 ^ 10))
   else decide (s.m₂ ≤ m ∧ 1 ≤ s.N ∧ 1 ≤ s.M ∧
     (s.N : ℚ) * m * geomQ deltaUp s.m₂ ≤ s.m₂ * Kp ∧
     (s.M : ℚ) * m * (1 + geomQ deltaUp (s.m₂ - 1)) ≤ s.m₂ * Kp ∧
     ((m - s.m₂ : ℕ) : ℚ) / hercherX₀ + 1 / (2 ^ s.N - 1) + ((s.m₂ - 1 : ℕ) : ℚ) / (2 ^ s.M - 1) ≤
       s.eps * Kp * (6931471803 / 10 ^ 10)))

/-- A chain of steps from `K ≥ Kp` to `K ≥ Kf`. -/
def chainOK (m : ℕ) : ℕ → List ChainStep → ℕ → Bool
  | Kp, [], Kf => decide (Kf ≤ Kp)
  | Kp, s :: rest, Kf => stepOK m Kp s && chainOK m (s.b + s.d) rest Kf

/-- **Soundness of `chainOK`.** -/
theorem chainOK_sound {x p : ℕ} (hx : 0 < x) (hp : 0 < p) (hcyc : T^[p] x = x) {m : ℕ}
    (hm : numLocalMin x p = m) (hm1 : 1 ≤ m) (hlow : ∀ j, hercherX₀ ≤ T^[j] x) :
    ∀ (steps : List ChainStep) (Kp Kf : ℕ), Kp ≤ oddCount T x p →
      chainOK m Kp steps Kf = true → Kf ≤ oddCount T x p
  | [], Kp, Kf, hK, h => by
    simp only [chainOK, decide_eq_true_eq] at h
    omega
  | s :: rest, Kp, Kf, hK, h => by
    simp only [chainOK, Bool.and_eq_true] at h
    obtain ⟨hs, hrest⟩ := h
    refine chainOK_sound hx hp hcyc hm hm1 hlow rest (s.b + s.d) Kf ?_ hrest
    unfold stepOK at hs
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hs
    obtain ⟨⟨hKp, hε0, hb, hd, hF, hc1, hc2⟩, hcase⟩ := hs
    have hX : 0 < hercherX₀ := by unfold hercherX₀; norm_num
    have hKpos : 0 < oddCount T x p := lt_of_lt_of_le hKp hK
    have r : RatioIn p (oddCount T x p) s.eps := by
      by_cases h0 : s.m₂ = 0
      · rw [if_pos h0, decide_eq_true_eq] at hcase
        exact ratioIn_of_crude hx hp hcyc hm hm1 hX hlow hKp hK hε0 hcase
      · rw [if_neg h0, decide_eq_true_eq] at hcase
        obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hcase
        exact ratioIn_of_window_two hx hp hcyc hm (by omega) h1 hX hlow hKp hK hε0 h2 h3 h4 h5 h6
    exact chain_step hKpos r hb hd hF hc1 hc2

/-! ### The Rhin contradiction for general `m` -/

/-- The rational side conditions of the Rhin contradiction for `m` minima above `K ≥ Kf`. -/
def rhinOK (m Kf V c k : ℕ) : Bool :=
  decide (1 ≤ m ∧ 1 ≤ V ∧ (V : ℚ) * geomQ deltaUp m ≤ Kf ∧ geomQ deltaUp m ≤ 2 ^ c ∧
    2 * m ≤ 2 ^ k ∧
    (133 / 10 : ℚ) * (12 + c) * (6931471808 / 10 ^ 10) - 133 / 10 + 133 / 10 * (46057 / 100000) +
        k * (6931471808 / 10 ^ 10) <
      (V : ℚ) * (6931471803 / 10 ^ 10 - 133 / (10 * 4096)))

/-- **Lemma 7 against Lemma 12 (Simons–de Weger), general `m`.** Under `RhinBound`, a
nontrivial cycle with `m` local minima has `K < Kf` whenever `rhinOK m Kf V c k`. -/
theorem K_lt_of_rhinOK (hR : RhinBound) {x p : ℕ} (hx : 0 < x) (hp : 0 < p)
    (hcyc : T^[p] x = x) (hx1 : x ≠ 1) (hx2 : x ≠ 2) {m Kf V c k : ℕ}
    (hm : numLocalMin x p = m) (hok : rhinOK m Kf V c k = true) :
    oddCount T x p < Kf := by
  simp only [rhinOK, decide_eq_true_eq] at hok
  obtain ⟨hm1, hV1, hVG, hGc, hmk, hineq⟩ := hok
  by_contra hge
  push_neg at hge
  have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  -- `G = G_m`, `G ≤ Ghi`
  obtain ⟨G, hG⟩ : ∃ G, G = ∑ d ∈ range m, Real.logb 2 3 ^ d := ⟨_, rfl⟩
  have hGpos : 0 < G := by rw [hG]; exact geomSum_delta_pos hm1
  have hδ0 : (0 : ℝ) ≤ Real.logb 2 3 := by linarith [one_le_logb_two_three]
  have hGhi : G ≤ ((geomQ deltaUp m : ℚ) : ℝ) := by
    rw [hG, geomQ_eq]
    push_cast
    exact sum_le_sum (fun d _ => pow_le_pow_left₀ hδ0 logb_le_deltaUp d)
  have hVGR : ((V * geomQ deltaUp m : ℚ) : ℝ) ≤ ((Kf : ℚ) : ℝ) := by exact_mod_cast hVG
  have hGcR : ((geomQ deltaUp m : ℚ) : ℝ) ≤ ((2 ^ c : ℚ) : ℝ) := by exact_mod_cast hGc
  have hineqR := (Rat.cast_lt (K := ℝ)).mpr hineq
  push_cast at hVGR hGcR hineqR
  have hKR : (Kf : ℝ) ≤ oddCount T x p := by exact_mod_cast hge
  have hK1 : 1 ≤ oddCount T x p := by
    have : (1 : ℝ) ≤ oddCount T x p := by
      have hVR : (1 : ℝ) ≤ V := by exact_mod_cast hV1
      have hG1 : (1 : ℝ) ≤ ((geomQ deltaUp m : ℚ) : ℝ) := by
        have : (1 : ℝ) ≤ G := by
          rw [hG]
          have := single_le_sum (f := fun d => Real.logb 2 3 ^ d)
            (fun d _ => pow_nonneg hδ0 d) (mem_range.mpr (show 0 < m by omega))
          simpa using this
        linarith
      nlinarith
    exact_mod_cast this
  have hrh := hR x p hx hp hcyc hx1 hx2 hK1
  -- Lemma 7: Theorem 21 (vertex-free) with `m₂ = m`
  have h21 := theorem21_vertexFree hx hp hcyc (m₂ := m) hm1 (by omega)
    (X₀ := 1) one_pos (fun j => by exact_mod_cast Nat.succ_le_of_lt (iterate_T_pos hx j))
  rw [hm] at h21
  obtain ⟨v, hv⟩ : ∃ v, v = windowExp m m (oddCount T x p) := ⟨_, rfl⟩
  rw [← hv] at h21
  set Λ := (p : ℝ) * Real.log 2 - (oddCount T x p : ℝ) * Real.log 3 with hΛ
  have z : ((m - m : ℕ) : ℝ) = 0 := by rw [Nat.sub_self, Nat.cast_zero]
  have e : 3 * (m : ℝ) / ((2 : ℝ) ^ v - 1) = 3 * ((m : ℝ) / ((2 : ℝ) ^ v - 1)) := by ring
  have hΛlt : Λ < (m : ℝ) / ((2 : ℝ) ^ v - 1) := by
    rw [z] at h21
    linarith
  have hvK : v * G = oddCount T x p := by
    rw [hv, windowExp, ← hG, div_mul_eq_mul_div, div_eq_iff (mul_pos hmR hGpos).ne']
    ring
  have hVv : (V : ℝ) ≤ v := by
    have h1 : (V : ℝ) * G ≤ v * G := by
      rw [hvK]
      have := mul_le_mul_of_nonneg_left hGhi (Nat.cast_nonneg (α := ℝ) V)
      linarith
    exact le_of_mul_le_mul_right h1 hGpos
  have hV1R : (1 : ℝ) ≤ V := by exact_mod_cast hV1
  have h2v : (2 : ℝ) ^ v = Real.exp (Real.log 2 * v) := Real.rpow_def_of_pos (by norm_num) v
  have h2v2 : (2 : ℝ) ≤ (2 : ℝ) ^ v := by
    have := Real.rpow_le_rpow_of_exponent_le (x := (2 : ℝ)) (by norm_num)
      (show (1 : ℝ) ≤ v by linarith)
    rwa [Real.rpow_one] at this
  have hΛ2 : Λ < 2 * m / (2 : ℝ) ^ v := by
    have h1 : (m : ℝ) / ((2 : ℝ) ^ v - 1) ≤ 2 * m / (2 : ℝ) ^ v := by
      rw [div_le_div_iff₀ (by linarith) (by linarith)]
      have := mul_le_mul_of_nonneg_left h2v2 hmR.le
      linarith
    linarith
  have hexp : Real.exp (-(133 / 10 * (46057 / 100000 + Real.log (oddCount T x p))) +
      Real.log 2 * v) < 2 * m := by
    rw [Real.exp_add, ← h2v]
    have h2pos : (0 : ℝ) < (2 : ℝ) ^ v := by linarith
    have := lt_trans hrh hΛ2
    rwa [lt_div_iff₀ h2pos] at this
  have hlog := (Real.lt_log_iff_exp_lt (by positivity : (0 : ℝ) < 2 * m)).mpr hexp
  have hl2 : (6931471803 / 10 ^ 10 : ℝ) < Real.log 2 := log_two_gt'
  have hl2' : Real.log 2 < 6931471808 / 10 ^ 10 := by
    have h := Real.log_two_lt_d9
    have e : (0.6931471808 : ℝ) = 6931471808 / 10 ^ 10 := by norm_num
    linarith
  have hlog2m : Real.log (2 * m) ≤ k * Real.log 2 := by
    have hmkR : (2 : ℝ) * m ≤ (2 : ℝ) ^ k := by exact_mod_cast hmk
    have : Real.log (2 * m) ≤ Real.log ((2 : ℝ) ^ k) := Real.log_le_log (by positivity) hmkR
    rwa [Real.log_pow] at this
  have hvpos : 0 < v := by linarith
  have hlogK : Real.log (oddCount T x p) = Real.log v + Real.log G := by
    rw [← hvK, Real.log_mul hvpos.ne' hGpos.ne']
  have hlogG : Real.log G ≤ c * Real.log 2 := by
    have : Real.log G ≤ Real.log ((2 : ℝ) ^ c) := Real.log_le_log hGpos (by linarith)
    rwa [Real.log_pow] at this
  have hlogv : Real.log v ≤ 12 * Real.log 2 + v / 4096 - 1 := by
    have h1 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < v / 4096 by positivity)
    rw [Real.log_div hvpos.ne' (by norm_num)] at h1
    have h4096 : Real.log (4096 : ℝ) = 12 * Real.log 2 := by
      rw [show (4096 : ℝ) = 2 ^ 12 by norm_num, Real.log_pow]; norm_num
    linarith
  -- the products with `log 2`
  have hcR : (0 : ℝ) ≤ c := Nat.cast_nonneg _
  have hkR : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have p1 : (c : ℝ) * Real.log 2 ≤ c * (6931471808 / 10 ^ 10) :=
    mul_le_mul_of_nonneg_left hl2'.le hcR
  have p2 : (k : ℝ) * Real.log 2 ≤ k * (6931471808 / 10 ^ 10) :=
    mul_le_mul_of_nonneg_left hl2'.le hkR
  have p3 : (6931471803 / 10 ^ 10 : ℝ) * v ≤ Real.log 2 * v :=
    mul_le_mul_of_nonneg_right hl2.le hvpos.le
  have p4 : (V : ℝ) * (6931471803 / 10 ^ 10 - 133 / (10 * 4096)) ≤
      v * (6931471803 / 10 ^ 10 - 133 / (10 * 4096)) :=
    mul_le_mul_of_nonneg_right hVv (by norm_num)
  rw [hlogK] at hlog
  linarith

/-- Chain certificate for `m = 1`. -/
def hercherData1 : Entry :=
  ⟨[⟨0, 0, 0, 181 / 10 ^ 23, 103768467013, 65470613321, 10439860591, 6586818670⟩],
    72057431991, 72057431991, 0, 1⟩

/-- Chain certificate for `m = 2`. -/
def hercherData2 : Entry :=
  ⟨[⟨0, 0, 0, 361 / 10 ^ 23, 9809721694, 6189245291, 630138897, 397573379⟩],
    6586818670, 2548129292, 2, 2⟩

/-- Chain certificate for `m = 3`. -/
def hercherData3 : Entry :=
  ⟨[⟨0, 0, 0, 541 / 10 ^ 23, 9809721694, 6189245291, 630138897, 397573379⟩],
    6586818670, 1292275844, 3, 3⟩

/-- Chain certificate for `m = 4`. -/
def hercherData4 : Entry :=
  ⟨[⟨0, 0, 0, 721 / 10 ^ 23, 9809721694, 6189245291, 630138897, 397573379⟩],
    6586818670, 725527418, 4, 3⟩

/-- Chain certificate for `m = 5`. -/
def hercherData5 : Entry :=
  ⟨[⟨0, 0, 0, 901 / 10 ^ 23, 9809721694, 6189245291, 630138897, 397573379⟩],
    6586818670, 428011775, 4, 4⟩

/-- Chain certificate for `m = 6`. -/
def hercherData6 : Entry :=
  ⟨[⟨0, 0, 0, 109 / 10 ^ 22, 9809721694, 6189245291, 630138897, 397573379⟩],
    6586818670, 259410108, 5, 4⟩

/-- Chain certificate for `m = 7`. -/
def hercherData7 : Entry :=
  ⟨[⟨0, 0, 0, 127 / 10 ^ 22, 9809721694, 6189245291, 630138897, 397573379⟩],
    6586818670, 159701291, 6, 4⟩

/-- Chain certificate for `m = 8`. -/
def hercherData8 : Entry :=
  ⟨[⟨0, 0, 0, 145 / 10 ^ 22, 9809721694, 6189245291, 630138897, 397573379⟩],
    6586818670, 99242162, 7, 4⟩

/-- Chain certificate for `m = 9`. -/
def hercherData9 : Entry :=
  ⟨[⟨0, 0, 0, 163 / 10 ^ 22, 9809721694, 6189245291, 630138897, 397573379⟩],
    6586818670, 62025216, 7, 5⟩

/-- Chain certificate for `m = 10`. -/
def hercherData10 : Entry :=
  ⟨[⟨0, 0, 0, 181 / 10 ^ 22, 9809721694, 6189245291, 630138897, 397573379⟩],
    6586818670, 38902427, 8, 5⟩

/-- Chain certificate for `m = 11`. -/
def hercherData11 : Entry :=
  ⟨[⟨0, 0, 0, 199 / 10 ^ 22, 9809721694, 6189245291, 630138897, 397573379⟩],
    6586818670, 24453576, 9, 5⟩

/-- Chain certificate for `m = 12`. -/
def hercherData12 : Entry :=
  ⟨[⟨0, 0, 0, 217 / 10 ^ 22, 9809721694, 6189245291, 630138897, 397573379⟩],
    6586818670, 15392435, 9, 5⟩

/-- Chain certificate for `m = 13`. -/
def hercherData13 : Entry :=
  ⟨[⟨0, 0, 0, 235 / 10 ^ 22, 9809721694, 6189245291, 630138897, 397573379⟩],
    6586818670, 9697247, 10, 5⟩

/-- Chain certificate for `m = 14`. -/
def hercherData14 : Entry :=
  ⟨[⟨0, 0, 0, 253 / 10 ^ 22, 9809721694, 6189245291, 630138897, 397573379⟩],
    6586818670, 6112604, 11, 5⟩

/-- Chain certificate for `m = 15`. -/
def hercherData15 : Entry :=
  ⟨[⟨0, 0, 0, 271 / 10 ^ 22, 9809721694, 6189245291, 630138897, 397573379⟩],
    6586818670, 3854367, 11, 5⟩

/-- Chain certificate for `m = 16`. -/
def hercherData16 : Entry :=
  ⟨[⟨0, 0, 0, 289 / 10 ^ 22, 9809721694, 6189245291, 630138897, 397573379⟩],
    6586818670, 2430937, 12, 5⟩

/-- Chain certificate for `m = 17`. -/
def hercherData17 : Entry :=
  ⟨[⟨0, 0, 0, 307 / 10 ^ 22, 9809721694, 6189245291, 630138897, 397573379⟩],
    6586818670, 1533393, 13, 6⟩

/-- Chain certificate for `m = 18`. -/
def hercherData18 : Entry :=
  ⟨[⟨0, 0, 0, 325 / 10 ^ 22, 9809721694, 6189245291, 630138897, 397573379⟩],
    6586818670, 967321, 13, 6⟩

/-- Chain certificate for `m = 19`. -/
def hercherData19 : Entry :=
  ⟨[⟨0, 0, 0, 343 / 10 ^ 22, 9809721694, 6189245291, 630138897, 397573379⟩],
    6586818670, 610255, 14, 6⟩

/-- Chain certificate for `m = 20`. -/
def hercherData20 : Entry :=
  ⟨[⟨0, 0, 0, 361 / 10 ^ 22, 9809721694, 6189245291, 630138897, 397573379⟩],
    6586818670, 385005, 15, 6⟩

/-- Chain certificate for `m = 21`. -/
def hercherData21 : Entry :=
  ⟨[⟨0, 0, 0, 379 / 10 ^ 22, 9809721694, 6189245291, 630138897, 397573379⟩],
    6586818670, 242902, 15, 6⟩

/-- Chain certificate for `m = 22`. -/
def hercherData22 : Entry :=
  ⟨[⟨0, 0, 0, 397 / 10 ^ 22, 9809721694, 6189245291, 630138897, 397573379⟩],
    6586818670, 153250, 16, 6⟩

/-- Chain certificate for `m = 23`. -/
def hercherData23 : Entry :=
  ⟨[⟨0, 0, 0, 415 / 10 ^ 22, 9809721694, 6189245291, 630138897, 397573379⟩],
    6586818670, 96689, 17, 6⟩

/-- Chain certificate for `m = 24`. -/
def hercherData24 : Entry :=
  ⟨[⟨0, 0, 0, 433 / 10 ^ 22, 9809721694, 6189245291, 630138897, 397573379⟩],
    6586818670, 61003, 17, 6⟩

/-- Chain certificate for `m = 25`. -/
def hercherData25 : Entry :=
  ⟨[⟨0, 0, 0, 451 / 10 ^ 22, 9809721694, 6189245291, 630138897, 397573379⟩],
    6586818670, 38488, 18, 6⟩

/-- Chain certificate for `m = 26`. -/
def hercherData26 : Entry :=
  ⟨[⟨0, 0, 0, 469 / 10 ^ 22, 9809721694, 6189245291, 630138897, 397573379⟩],
    6586818670, 24283, 19, 6⟩

/-- Chain certificate for `m = 27`. -/
def hercherData27 : Entry :=
  ⟨[⟨0, 0, 0, 487 / 10 ^ 22, 9809721694, 6189245291, 630138897, 397573379⟩],
    6586818670, 15321, 19, 6⟩

/-- Chain certificate for `m = 28`. -/
def hercherData28 : Entry :=
  ⟨[⟨0, 0, 0, 505 / 10 ^ 22, 9809721694, 6189245291, 630138897, 397573379⟩],
    6586818670, 9666, 20, 6⟩

/-- Chain certificate for `m = 29`. -/
def hercherData29 : Entry :=
  ⟨[⟨0, 0, 0, 523 / 10 ^ 22, 9809721694, 6189245291, 630138897, 397573379⟩],
    6586818670, 6098, 21, 6⟩

/-- Chain certificate for `m = 30`. -/
def hercherData30 : Entry :=
  ⟨[⟨0, 0, 0, 541 / 10 ^ 22, 9809721694, 6189245291, 630138897, 397573379⟩],
    6586818670, 3847, 21, 6⟩

/-- Chain certificate for `m = 31`. -/
def hercherData31 : Entry :=
  ⟨[⟨0, 0, 0, 559 / 10 ^ 22, 9809721694, 6189245291, 630138897, 397573379⟩],
    6586818670, 2427, 22, 6⟩

/-- Chain certificate for `m = 32`. -/
def hercherData32 : Entry :=
  ⟨[⟨0, 0, 0, 577 / 10 ^ 22, 9809721694, 6189245291, 630138897, 397573379⟩],
    6586818670, 1531, 23, 6⟩

/-- Chain certificate for `m = 33`. -/
def hercherData33 : Entry :=
  ⟨[⟨0, 0, 0, 595 / 10 ^ 22, 9809721694, 6189245291, 630138897, 397573379⟩],
    6586818670, 966, 23, 7⟩

/-- Chain certificate for `m = 34`. -/
def hercherData34 : Entry :=
  ⟨[⟨0, 0, 0, 613 / 10 ^ 22, 9809721694, 6189245291, 630138897, 397573379⟩],
    6586818670, 609, 24, 7⟩

/-- Chain certificate for `m = 35`. -/
def hercherData35 : Entry :=
  ⟨[⟨0, 0, 0, 631 / 10 ^ 22, 9809721694, 6189245291, 630138897, 397573379⟩,
    ⟨35, 200, 200, 478 / 10 ^ 71, 5504938256213345873657899, 3473229337418774934657366, 41311723474137723079719633, 26064795511149907129365023⟩],
    29538024848568682064022389, 1725221315847977158, 25, 7⟩

/-- Chain certificate for `m = 36`. -/
def hercherData36 : Entry :=
  ⟨[⟨0, 0, 0, 649 / 10 ^ 22, 9809721694, 6189245291, 630138897, 397573379⟩,
    ⟨36, 200, 200, 491 / 10 ^ 71, 5504938256213345873657899, 3473229337418774934657366, 41311723474137723079719633, 26064795511149907129365023⟩],
    29538024848568682064022389, 1088493419361072225, 25, 7⟩

/-- Chain certificate for `m = 37`. -/
def hercherData37 : Entry :=
  ⟨[⟨0, 0, 0, 667 / 10 ^ 22, 9809721694, 6189245291, 630138897, 397573379⟩,
    ⟨37, 153, 200, 192 / 10 ^ 58, 5504938256213345873657899, 3473229337418774934657366, 41311723474137723079719633, 26064795511149907129365023⟩],
    29538024848568682064022389, 686762868753486379, 26, 7⟩

/-- Chain certificate for `m = 38`. -/
def hercherData38 : Entry :=
  ⟨[⟨0, 0, 0, 685 / 10 ^ 22, 9809721694, 6189245291, 630138897, 397573379⟩,
    ⟨38, 96, 153, 277 / 10 ^ 41, 36143248623210700400, 22803850947114245497, 7354673373747273033, 4640282259296926456⟩],
    27444133206411171953, 402583411009, 27, 7⟩

/-- Chain certificate for `m = 39`. -/
def hercherData39 : Entry :=
  ⟨[⟨0, 0, 0, 703 / 10 ^ 22, 9809721694, 6189245291, 630138897, 397573379⟩,
    ⟨38, 94, 149, 274 / 10 ^ 33, 766512153894657, 483615324366283, 5282454920184382, 3332857981044265⟩],
    3816473305410548, 35322350, 27, 7⟩

/-- Chain certificate for `m = 40`. -/
def hercherData40 : Entry :=
  ⟨[⟨0, 0, 0, 721 / 10 ^ 22, 9809721694, 6189245291, 630138897, 397573379⟩,
    ⟨38, 91, 145, 547 / 10 ^ 33, 766512153894657, 483615324366283, 2982918458500411, 1882012007945416⟩],
    2365627332311699, 13813848, 28, 7⟩

/-- Chain certificate for `m = 41`. -/
def hercherData41 : Entry :=
  ⟨[⟨0, 0, 0, 739 / 10 ^ 22, 9809721694, 6189245291, 630138897, 397573379⟩,
    ⟨38, 89, 141, 821 / 10 ^ 33, 766512153894657, 483615324366283, 2216406304605754, 1398396683579133⟩],
    1882012007945416, 6933807, 29, 7⟩

/-- Chain certificate for `m = 42`. -/
def hercherData42 : Entry :=
  ⟨[⟨0, 0, 0, 757 / 10 ^ 22, 9809721694, 6189245291, 630138897, 397573379⟩,
    ⟨38, 87, 138, 110 / 10 ^ 32, 766512153894657, 483615324366283, 2216406304605754, 1398396683579133⟩],
    1882012007945416, 4374745, 29, 7⟩

/-- Chain certificate for `m = 43`. -/
def hercherData43 : Entry :=
  ⟨[⟨0, 0, 0, 775 / 10 ^ 22, 9809721694, 6189245291, 630138897, 397573379⟩,
    ⟨38, 85, 135, 137 / 10 ^ 32, 766512153894657, 483615324366283, 1449894150711097, 914781359212850⟩],
    1398396683579133, 2050887, 30, 7⟩

/-- Chain certificate for `m = 44`. -/
def hercherData44 : Entry :=
  ⟨[⟨0, 0, 0, 793 / 10 ^ 22, 9809721694, 6189245291, 630138897, 397573379⟩,
    ⟨38, 83, 132, 165 / 10 ^ 32, 766512153894657, 483615324366283, 1449894150711097, 914781359212850⟩],
    1398396683579133, 1293965, 31, 7⟩

/-- Chain certificate for `m = 45`. -/
def hercherData45 : Entry :=
  ⟨[⟨0, 0, 0, 811 / 10 ^ 22, 9809721694, 6189245291, 630138897, 397573379⟩,
    ⟨38, 81, 129, 192 / 10 ^ 32, 766512153894657, 483615324366283, 1449894150711097, 914781359212850⟩],
    1398396683579133, 816401, 31, 7⟩

/-- Chain certificate for `m = 46`. -/
def hercherData46 : Entry :=
  ⟨[⟨0, 0, 0, 829 / 10 ^ 22, 9809721694, 6189245291, 630138897, 397573379⟩,
    ⟨38, 79, 126, 219 / 10 ^ 32, 766512153894657, 483615324366283, 683381996816440, 431166034846567⟩],
    914781359212850, 336954, 32, 7⟩

/-- Chain certificate for `m = 47`. -/
def hercherData47 : Entry :=
  ⟨[⟨0, 0, 0, 847 / 10 ^ 22, 9809721694, 6189245291, 630138897, 397573379⟩,
    ⟨38, 78, 123, 247 / 10 ^ 32, 766512153894657, 483615324366283, 683381996816440, 431166034846567⟩],
    914781359212850, 212594, 33, 7⟩

/-- Chain certificate for `m = 48`. -/
def hercherData48 : Entry :=
  ⟨[⟨0, 0, 0, 865 / 10 ^ 22, 9809721694, 6189245291, 630138897, 397573379⟩,
    ⟨38, 76, 121, 274 / 10 ^ 32, 766512153894657, 483615324366283, 683381996816440, 431166034846567⟩],
    914781359212850, 134132, 33, 7⟩

/-- Chain certificate for `m = 49`. -/
def hercherData49 : Entry :=
  ⟨[⟨0, 0, 0, 883 / 10 ^ 22, 9809721694, 6189245291, 630138897, 397573379⟩,
    ⟨38, 74, 118, 302 / 10 ^ 32, 766512153894657, 483615324366283, 683381996816440, 431166034846567⟩],
    914781359212850, 84628, 34, 7⟩

/-- Chain certificate for `m = 50`. -/
def hercherData50 : Entry :=
  ⟨[⟨0, 0, 0, 901 / 10 ^ 22, 9809721694, 6189245291, 630138897, 397573379⟩,
    ⟨38, 73, 116, 331 / 10 ^ 32, 766512153894657, 483615324366283, 683381996816440, 431166034846567⟩],
    914781359212850, 53394, 34, 7⟩

/-- Chain certificate for `m = 51`. -/
def hercherData51 : Entry :=
  ⟨[⟨0, 0, 0, 919 / 10 ^ 22, 9809721694, 6189245291, 630138897, 397573379⟩,
    ⟨38, 71, 114, 365 / 10 ^ 32, 766512153894657, 483615324366283, 683381996816440, 431166034846567⟩],
    914781359212850, 33688, 35, 7⟩

/-- Chain certificate for `m = 52`. -/
def hercherData52 : Entry :=
  ⟨[⟨0, 0, 0, 937 / 10 ^ 22, 9809721694, 6189245291, 630138897, 397573379⟩,
    ⟨38, 70, 111, 402 / 10 ^ 32, 766512153894657, 483615324366283, 683381996816440, 431166034846567⟩],
    914781359212850, 21254, 36, 7⟩

/-- Chain certificate for `m = 53`. -/
def hercherData53 : Entry :=
  ⟨[⟨0, 0, 0, 955 / 10 ^ 22, 9809721694, 6189245291, 630138897, 397573379⟩,
    ⟨37, 106, 169, 438 / 10 ^ 32, 766512153894657, 483615324366283, 683381996816440, 431166034846567⟩],
    914781359212850, 13410, 36, 7⟩

/-- Chain certificate for `m = 54`. -/
def hercherData54 : Entry :=
  ⟨[⟨0, 0, 0, 973 / 10 ^ 22, 9809721694, 6189245291, 630138897, 397573379⟩,
    ⟨37, 104, 166, 465 / 10 ^ 32, 83130157078217, 52449289519716, 600251839738223, 378716745326851⟩],
    431166034846567, 3987, 37, 7⟩

/-- Chain certificate for `m = 55`. -/
def hercherData55 : Entry :=
  ⟨[⟨0, 0, 0, 991 / 10 ^ 22, 9809721694, 6189245291, 630138897, 397573379⟩,
    ⟨37, 103, 163, 493 / 10 ^ 32, 83130157078217, 52449289519716, 600251839738223, 378716745326851⟩],
    431166034846567, 2516, 38, 7⟩

/-- Chain certificate for `m = 56`. -/
def hercherData56 : Entry :=
  ⟨[⟨0, 0, 0, 101 / 10 ^ 21, 9809721694, 6189245291, 630138897, 397573379⟩,
    ⟨37, 101, 160, 520 / 10 ^ 32, 83130157078217, 52449289519716, 600251839738223, 378716745326851⟩],
    431166034846567, 1587, 38, 7⟩

/-- Chain certificate for `m = 57`. -/
def hercherData57 : Entry :=
  ⟨[⟨0, 0, 0, 103 / 10 ^ 21, 9809721694, 6189245291, 630138897, 397573379⟩,
    ⟨37, 99, 157, 547 / 10 ^ 32, 83130157078217, 52449289519716, 600251839738223, 378716745326851⟩],
    431166034846567, 1001, 39, 7⟩

/-- Chain certificate for `m = 58`. -/
def hercherData58 : Entry :=
  ⟨[⟨0, 0, 0, 105 / 10 ^ 21, 9809721694, 6189245291, 630138897, 397573379⟩,
    ⟨37, 97, 154, 575 / 10 ^ 32, 83130157078217, 52449289519716, 600251839738223, 378716745326851⟩,
    ⟨58, 200, 200, 121 / 10 ^ 75, 5504938256213345873657899, 3473229337418774934657366, 41311723474137723079719633, 26064795511149907129365023⟩],
    29538024848568682064022389, 43292031446197, 40, 7⟩

/-- Chain certificate for `m = 59`. -/
def hercherData59 : Entry :=
  ⟨[⟨0, 0, 0, 107 / 10 ^ 21, 9809721694, 6189245291, 630138897, 397573379⟩,
    ⟨37, 96, 152, 602 / 10 ^ 32, 83130157078217, 52449289519716, 600251839738223, 378716745326851⟩,
    ⟨59, 200, 200, 123 / 10 ^ 75, 5504938256213345873657899, 3473229337418774934657366, 41311723474137723079719633, 26064795511149907129365023⟩],
    29538024848568682064022389, 27314230727126, 40, 7⟩

/-- Chain certificate for `m = 60`. -/
def hercherData60 : Entry :=
  ⟨[⟨0, 0, 0, 109 / 10 ^ 21, 9809721694, 6189245291, 630138897, 397573379⟩,
    ⟨37, 94, 149, 629 / 10 ^ 32, 83130157078217, 52449289519716, 600251839738223, 378716745326851⟩,
    ⟨60, 200, 200, 125 / 10 ^ 75, 5504938256213345873657899, 3473229337418774934657366, 41311723474137723079719633, 26064795511149907129365023⟩],
    29538024848568682064022389, 17233360858617, 41, 7⟩

/-- Chain certificate for `m = 61`. -/
def hercherData61 : Entry :=
  ⟨[⟨0, 0, 0, 110 / 10 ^ 21, 9809721694, 6189245291, 630138897, 397573379⟩,
    ⟨37, 92, 147, 657 / 10 ^ 32, 83130157078217, 52449289519716, 600251839738223, 378716745326851⟩,
    ⟨61, 158, 200, 916 / 10 ^ 65, 5504938256213345873657899, 3473229337418774934657366, 41311723474137723079719633, 26064795511149907129365023⟩],
    29538024848568682064022389, 10873040117818, 42, 7⟩

/-- Chain certificate for `m = 62`. -/
def hercherData62 : Entry :=
  ⟨[⟨0, 0, 0, 112 / 10 ^ 21, 9809721694, 6189245291, 630138897, 397573379⟩,
    ⟨37, 91, 144, 684 / 10 ^ 32, 83130157078217, 52449289519716, 600251839738223, 378716745326851⟩,
    ⟨62, 100, 158, 264 / 10 ^ 47, 12261796429850908150604, 7736332199829210068325, 24849512215556238269573, 15678296618531818732906⟩],
    23414628818361028801231, 5437982740, 42, 7⟩

/-- Chain certificate for `m = 63`. -/
def hercherData63 : Entry :=
  ⟨[⟨0, 0, 0, 114 / 10 ^ 21, 9809721694, 6189245291, 630138897, 397573379⟩,
    ⟨37, 89, 142, 711 / 10 ^ 32, 83130157078217, 52449289519716, 600251839738223, 378716745326851⟩,
    ⟨62, 98, 156, 418 / 10 ^ 38, 423372672964960618, 267118416222671843, 206745572560704147, 130441933147714940⟩],
    397560349370386783, 58255, 43, 7⟩

/-- Chain certificate for `m = 64`. -/
def hercherData64 : Entry :=
  ⟨[⟨0, 0, 0, 116 / 10 ^ 21, 9809721694, 6189245291, 630138897, 397573379⟩,
    ⟨37, 88, 140, 739 / 10 ^ 32, 83130157078217, 52449289519716, 600251839738223, 378716745326851⟩,
    ⟨62, 97, 153, 836 / 10 ^ 38, 423372672964960618, 267118416222671843, 206745572560704147, 130441933147714940⟩],
    397560349370386783, 36754, 44, 7⟩

/-- Chain certificate for `m = 65`. -/
def hercherData65 : Entry :=
  ⟨[⟨0, 0, 0, 118 / 10 ^ 21, 9809721694, 6189245291, 630138897, 397573379⟩,
    ⟨37, 87, 138, 766 / 10 ^ 32, 83130157078217, 52449289519716, 600251839738223, 378716745326851⟩,
    ⟨62, 95, 151, 126 / 10 ^ 37, 423372672964960618, 267118416222671843, 206745572560704147, 130441933147714940⟩],
    397560349370386783, 23189, 44, 8⟩

/-- Chain certificate for `m = 66`. -/
def hercherData66 : Entry :=
  ⟨[⟨0, 0, 0, 119 / 10 ^ 21, 9809721694, 6189245291, 630138897, 397573379⟩,
    ⟨37, 85, 136, 793 / 10 ^ 32, 83130157078217, 52449289519716, 600251839738223, 378716745326851⟩,
    ⟨62, 94, 149, 168 / 10 ^ 37, 423372672964960618, 267118416222671843, 206745572560704147, 130441933147714940⟩],
    397560349370386783, 14631, 45, 8⟩

/-- Chain certificate for `m = 67`. -/
def hercherData67 : Entry :=
  ⟨[⟨0, 0, 0, 121 / 10 ^ 21, 9809721694, 6189245291, 630138897, 397573379⟩,
    ⟨37, 84, 134, 821 / 10 ^ 32, 83130157078217, 52449289519716, 600251839738223, 378716745326851⟩,
    ⟨62, 92, 146, 209 / 10 ^ 37, 9881527843552324, 6234549927241963, 196864044717151823, 124207383220472977⟩],
    130441933147714940, 3028, 46, 8⟩

/-- Chain certificate for `m = 68`. -/
def hercherData68 : Entry :=
  ⟨[⟨0, 0, 0, 123 / 10 ^ 21, 9809721694, 6189245291, 630138897, 397573379⟩,
    ⟨37, 83, 132, 848 / 10 ^ 32, 83130157078217, 52449289519716, 600251839738223, 378716745326851⟩,
    ⟨62, 91, 144, 251 / 10 ^ 37, 9881527843552324, 6234549927241963, 196864044717151823, 124207383220472977⟩],
    130441933147714940, 1910, 46, 8⟩

/-- Chain certificate for `m = 69`. -/
def hercherData69 : Entry :=
  ⟨[⟨0, 0, 0, 125 / 10 ^ 21, 9809721694, 6189245291, 630138897, 397573379⟩,
    ⟨37, 82, 130, 875 / 10 ^ 32, 83130157078217, 52449289519716, 600251839738223, 378716745326851⟩,
    ⟨62, 89, 142, 293 / 10 ^ 37, 9881527843552324, 6234549927241963, 196864044717151823, 124207383220472977⟩],
    130441933147714940, 1205, 47, 8⟩

/-- Chain certificate for `m = 70`. -/
def hercherData70 : Entry :=
  ⟨[⟨0, 0, 0, 127 / 10 ^ 21, 9809721694, 6189245291, 630138897, 397573379⟩,
    ⟨37, 80, 128, 903 / 10 ^ 32, 83130157078217, 52449289519716, 600251839738223, 378716745326851⟩,
    ⟨62, 88, 140, 335 / 10 ^ 37, 9881527843552324, 6234549927241963, 196864044717151823, 124207383220472977⟩,
    ⟨70, 200, 200, 482 / 10 ^ 78, 5504938256213345873657899, 3473229337418774934657366, 41311723474137723079719633, 26064795511149907129365023⟩],
    29538024848568682064022389, 172258263961, 48, 8⟩

/-- Chain certificate for `m = 71`. -/
def hercherData71 : Entry :=
  ⟨[⟨0, 0, 0, 128 / 10 ^ 21, 9809721694, 6189245291, 630138897, 397573379⟩,
    ⟨37, 79, 126, 930 / 10 ^ 32, 83130157078217, 52449289519716, 600251839738223, 378716745326851⟩,
    ⟨62, 87, 138, 376 / 10 ^ 37, 9881527843552324, 6234549927241963, 196864044717151823, 124207383220472977⟩,
    ⟨71, 200, 200, 489 / 10 ^ 78, 5504938256213345873657899, 3473229337418774934657366, 41311723474137723079719633, 26064795511149907129365023⟩],
    29538024848568682064022389, 108682864012, 48, 8⟩

/-- Chain certificate for `m = 72`. -/
def hercherData72 : Entry :=
  ⟨[⟨0, 0, 0, 130 / 10 ^ 21, 9809721694, 6189245291, 630138897, 397573379⟩,
    ⟨37, 78, 124, 957 / 10 ^ 32, 83130157078217, 52449289519716, 600251839738223, 378716745326851⟩,
    ⟨62, 86, 136, 418 / 10 ^ 37, 9881527843552324, 6234549927241963, 196864044717151823, 124207383220472977⟩,
    ⟨72, 200, 200, 496 / 10 ^ 78, 5504938256213345873657899, 3473229337418774934657366, 41311723474137723079719633, 26064795511149907129365023⟩],
    29538024848568682064022389, 68571252596, 49, 8⟩

/-- Chain certificate for `m = 73`. -/
def hercherData73 : Entry :=
  ⟨[⟨0, 0, 0, 132 / 10 ^ 21, 9809721694, 6189245291, 630138897, 397573379⟩,
    ⟨37, 77, 123, 985 / 10 ^ 32, 83130157078217, 52449289519716, 600251839738223, 378716745326851⟩,
    ⟨62, 85, 134, 460 / 10 ^ 37, 9881527843552324, 6234549927241963, 196864044717151823, 124207383220472977⟩,
    ⟨73, 191, 200, 402 / 10 ^ 77, 5504938256213345873657899, 3473229337418774934657366, 41311723474137723079719633, 26064795511149907129365023⟩],
    29538024848568682064022389, 43263643495, 50, 8⟩

/-- Chain certificate for `m = 74`. -/
def hercherData74 : Entry :=
  ⟨[⟨0, 0, 0, 134 / 10 ^ 21, 9809721694, 6189245291, 630138897, 397573379⟩,
    ⟨37, 76, 121, 102 / 10 ^ 31, 83130157078217, 52449289519716, 600251839738223, 378716745326851⟩,
    ⟨62, 83, 132, 502 / 10 ^ 37, 9881527843552324, 6234549927241963, 196864044717151823, 124207383220472977⟩,
    ⟨74, 120, 191, 833 / 10 ^ 56, 5504938256213345873657899, 3473229337418774934657366, 41311723474137723079719633, 26064795511149907129365023⟩],
    29538024848568682064022389, 27296319924, 50, 8⟩

/-- Chain certificate for `m = 75`. -/
def hercherData75 : Entry :=
  ⟨[⟨0, 0, 0, 136 / 10 ^ 21, 9809721694, 6189245291, 630138897, 397573379⟩,
    ⟨37, 75, 119, 104 / 10 ^ 31, 83130157078217, 52449289519716, 600251839738223, 378716745326851⟩,
    ⟨62, 82, 131, 543 / 10 ^ 37, 9881527843552324, 6234549927241963, 196864044717151823, 124207383220472977⟩,
    ⟨75, 76, 120, 147 / 10 ^ 42, 79641170620168673833, 50247984153525417450, 43497921996957973433, 27444133206411171953⟩],
    77692117359936589403, 45298, 51, 8⟩

/-- Chain certificate for `m = 76`. -/
def hercherData76 : Entry :=
  ⟨[⟨0, 0, 0, 137 / 10 ^ 21, 9809721694, 6189245291, 630138897, 397573379⟩,
    ⟨37, 74, 118, 107 / 10 ^ 31, 83130157078217, 52449289519716, 517121682660006, 326267455807135⟩,
    ⟨62, 71, 113, 682 / 10 ^ 37, 9881527843552324, 6234549927241963, 196864044717151823, 124207383220472977⟩,
    ⟨75, 75, 118, 141 / 10 ^ 40, 6724555128221608268, 4242721909926539673, 630118245525664765, 397560349370386783⟩],
    4640282259296926456, 1706, 52, 8⟩

/-- Chain certificate for `m = 77`. -/
def hercherData77 : Entry :=
  ⟨[⟨0, 0, 0, 139 / 10 ^ 21, 9809721694, 6189245291, 630138897, 397573379⟩,
    ⟨37, 73, 116, 110 / 10 ^ 31, 83130157078217, 52449289519716, 517121682660006, 326267455807135⟩,
    ⟨62, 70, 112, 746 / 10 ^ 37, 9881527843552324, 6234549927241963, 196864044717151823, 124207383220472977⟩,
    ⟨75, 74, 117, 282 / 10 ^ 40, 6724555128221608268, 4242721909926539673, 630118245525664765, 397560349370386783⟩],
    4640282259296926456, 1076, 52, 8⟩

/-- Chain certificate for `m = 78`. -/
def hercherData78 : Entry :=
  ⟨[⟨0, 0, 0, 141 / 10 ^ 21, 9809721694, 6189245291, 630138897, 397573379⟩,
    ⟨37, 72, 115, 113 / 10 ^ 31, 83130157078217, 52449289519716, 517121682660006, 326267455807135⟩,
    ⟨61, 109, 172, 809 / 10 ^ 37, 9881527843552324, 6234549927241963, 196864044717151823, 124207383220472977⟩,
    ⟨75, 73, 115, 426 / 10 ^ 40, 6724555128221608268, 4242721909926539673, 630118245525664765, 397560349370386783⟩,
    ⟨78, 200, 200, 151 / 10 ^ 79, 5504938256213345873657899, 3473229337418774934657366, 41311723474137723079719633, 26064795511149907129365023⟩],
    29538024848568682064022389, 4325418498, 53, 8⟩

/-- Chain certificate for `m = 79`. -/
def hercherData79 : Entry :=
  ⟨[⟨0, 0, 0, 143 / 10 ^ 21, 9809721694, 6189245291, 630138897, 397573379⟩,
    ⟨37, 71, 113, 116 / 10 ^ 31, 83130157078217, 52449289519716, 517121682660006, 326267455807135⟩,
    ⟨61, 107, 170, 856 / 10 ^ 37, 9881527843552324, 6234549927241963, 186982516873599499, 117972833293231014⟩,
    ⟨74, 107, 170, 725 / 10 ^ 40, 6724555128221608268, 4242721909926539673, 630118245525664765, 397560349370386783⟩,
    ⟨79, 200, 200, 153 / 10 ^ 79, 5504938256213345873657899, 3473229337418774934657366, 41311723474137723079719633, 26064795511149907129365023⟩],
    29538024848568682064022389, 2729035226, 54, 8⟩

/-- Chain certificate for `m = 80`. -/
def hercherData80 : Entry :=
  ⟨[⟨0, 0, 0, 145 / 10 ^ 21, 9809721694, 6189245291, 630138897, 397573379⟩,
    ⟨37, 70, 112, 120 / 10 ^ 31, 83130157078217, 52449289519716, 517121682660006, 326267455807135⟩,
    ⟨61, 106, 168, 904 / 10 ^ 37, 9881527843552324, 6234549927241963, 186982516873599499, 117972833293231014⟩,
    ⟨74, 106, 168, 870 / 10 ^ 40, 6724555128221608268, 4242721909926539673, 630118245525664765, 397560349370386783⟩,
    ⟨80, 200, 200, 155 / 10 ^ 79, 5504938256213345873657899, 3473229337418774934657366, 41311723474137723079719633, 26064795511149907129365023⟩],
    29538024848568682064022389, 1721829522, 54, 8⟩

/-- Chain certificate for `m = 81`. -/
def hercherData81 : Entry :=
  ⟨[⟨0, 0, 0, 146 / 10 ^ 21, 9809721694, 6189245291, 630138897, 397573379⟩,
    ⟨36, 107, 170, 124 / 10 ^ 31, 83130157078217, 52449289519716, 517121682660006, 326267455807135⟩,
    ⟨61, 104, 166, 951 / 10 ^ 37, 9881527843552324, 6234549927241963, 186982516873599499, 117972833293231014⟩,
    ⟨74, 104, 166, 102 / 10 ^ 39, 6724555128221608268, 4242721909926539673, 630118245525664765, 397560349370386783⟩,
    ⟨81, 170, 200, 208 / 10 ^ 72, 5504938256213345873657899, 3473229337418774934657366, 41311723474137723079719633, 26064795511149907129365023⟩],
    29538024848568682064022389, 1086353476, 55, 8⟩

/-- Chain certificate for `m = 82`. -/
def hercherData82 : Entry :=
  ⟨[⟨0, 0, 0, 148 / 10 ^ 21, 9809721694, 6189245291, 630138897, 397573379⟩,
    ⟨36, 106, 168, 126 / 10 ^ 31, 83130157078217, 52449289519716, 517121682660006, 326267455807135⟩,
    ⟨61, 103, 164, 999 / 10 ^ 37, 9881527843552324, 6234549927241963, 186982516873599499, 117972833293231014⟩,
    ⟨74, 103, 164, 116 / 10 ^ 39, 6724555128221608268, 4242721909926539673, 630118245525664765, 397560349370386783⟩,
    ⟨82, 107, 170, 192 / 10 ^ 53, 5504938256213345873657899, 3473229337418774934657366, 35806785217924377206061734, 22591566173731132194707657⟩],
    26064795511149907129365023, 604818459, 56, 8⟩

/-- Chain certificate for `m = 83`. -/
def hercherData83 : Entry :=
  ⟨[⟨0, 0, 0, 150 / 10 ^ 21, 9809721694, 6189245291, 630138897, 397573379⟩,
    ⟨36, 105, 166, 129 / 10 ^ 31, 83130157078217, 52449289519716, 517121682660006, 326267455807135⟩,
    ⟨61, 102, 162, 105 / 10 ^ 36, 9881527843552324, 6234549927241963, 186982516873599499, 117972833293231014⟩,
    ⟨74, 102, 162, 131 / 10 ^ 39, 6724555128221608268, 4242721909926539673, 630118245525664765, 397560349370386783⟩,
    ⟨82, 106, 168, 389 / 10 ^ 42, 79641170620168673833, 50247984153525417450, 43497921996957973433, 27444133206411171953⟩],
    77692117359936589403, 1137, 56, 8⟩

/-- Chain certificate for `m = 84`. -/
def hercherData84 : Entry :=
  ⟨[⟨0, 0, 0, 152 / 10 ^ 21, 9809721694, 6189245291, 630138897, 397573379⟩,
    ⟨36, 104, 164, 132 / 10 ^ 31, 83130157078217, 52449289519716, 517121682660006, 326267455807135⟩,
    ⟨61, 101, 160, 110 / 10 ^ 36, 9881527843552324, 6234549927241963, 186982516873599499, 117972833293231014⟩,
    ⟨74, 101, 160, 145 / 10 ^ 39, 6724555128221608268, 4242721909926539673, 630118245525664765, 397560349370386783⟩,
    ⟨82, 105, 166, 777 / 10 ^ 42, 36143248623210700400, 22803850947114245497, 7354673373747273033, 4640282259296926456⟩,
    ⟨84, 200, 200, 275 / 10 ^ 80, 5504938256213345873657899, 3473229337418774934657366, 41311723474137723079719633, 26064795511149907129365023⟩],
    29538024848568682064022389, 272843859, 57, 8⟩

/-- Chain certificate for `m = 85`. -/
def hercherData85 : Entry :=
  ⟨[⟨0, 0, 0, 154 / 10 ^ 21, 9809721694, 6189245291, 630138897, 397573379⟩,
    ⟨36, 102, 162, 134 / 10 ^ 31, 83130157078217, 52449289519716, 517121682660006, 326267455807135⟩,
    ⟨61, 100, 158, 115 / 10 ^ 36, 9881527843552324, 6234549927241963, 186982516873599499, 117972833293231014⟩,
    ⟨74, 99, 158, 160 / 10 ^ 39, 6724555128221608268, 4242721909926539673, 630118245525664765, 397560349370386783⟩,
    ⟨82, 103, 164, 117 / 10 ^ 41, 36143248623210700400, 22803850947114245497, 7354673373747273033, 4640282259296926456⟩,
    ⟨85, 159, 200, 720 / 10 ^ 70, 5504938256213345873657899, 3473229337418774934657366, 41311723474137723079719633, 26064795511149907129365023⟩],
    29538024848568682064022389, 172145308, 58, 8⟩

/-- Chain certificate for `m = 86`. -/
def hercherData86 : Entry :=
  ⟨[⟨0, 0, 0, 155 / 10 ^ 21, 9809721694, 6189245291, 630138897, 397573379⟩,
    ⟨36, 101, 161, 137 / 10 ^ 31, 83130157078217, 52449289519716, 517121682660006, 326267455807135⟩,
    ⟨61, 98, 156, 119 / 10 ^ 36, 9881527843552324, 6234549927241963, 186982516873599499, 117972833293231014⟩,
    ⟨74, 98, 156, 174 / 10 ^ 39, 6724555128221608268, 4242721909926539673, 630118245525664765, 397560349370386783⟩,
    ⟨82, 102, 162, 156 / 10 ^ 41, 36143248623210700400, 22803850947114245497, 7354673373747273033, 4640282259296926456⟩,
    ⟨86, 100, 159, 415 / 10 ^ 52, 5504938256213345873657899, 3473229337418774934657366, 8282093936857647837772239, 5225419486637257521420827⟩],
    8698648824056032456078193, 31985014, 58, 8⟩

/-- Chain certificate for `m = 87`. -/
def hercherData87 : Entry :=
  ⟨[⟨0, 0, 0, 157 / 10 ^ 21, 9809721694, 6189245291, 630138897, 397573379⟩,
    ⟨36, 100, 159, 140 / 10 ^ 31, 83130157078217, 52449289519716, 517121682660006, 326267455807135⟩,
    ⟨61, 97, 154, 124 / 10 ^ 36, 9881527843552324, 6234549927241963, 186982516873599499, 117972833293231014⟩,
    ⟨74, 97, 154, 189 / 10 ^ 39, 6724555128221608268, 4242721909926539673, 630118245525664765, 397560349370386783⟩,
    ⟨82, 101, 160, 195 / 10 ^ 41, 36143248623210700400, 22803850947114245497, 7354673373747273033, 4640282259296926456⟩,
    ⟨86, 99, 158, 657 / 10 ^ 43, 79641170620168673833, 50247984153525417450, 43497921996957973433, 27444133206411171953⟩,
    ⟨87, 180, 200, 122 / 10 ^ 76, 5504938256213345873657899, 3473229337418774934657366, 41311723474137723079719633, 26064795511149907129365023⟩],
    29538024848568682064022389, 68526288, 59, 8⟩

/-- Chain certificate for `m = 88`. -/
def hercherData88 : Entry :=
  ⟨[⟨0, 0, 0, 159 / 10 ^ 21, 9809721694, 6189245291, 630138897, 397573379⟩,
    ⟨36, 99, 157, 143 / 10 ^ 31, 83130157078217, 52449289519716, 517121682660006, 326267455807135⟩,
    ⟨61, 96, 153, 129 / 10 ^ 36, 9881527843552324, 6234549927241963, 186982516873599499, 117972833293231014⟩,
    ⟨74, 96, 152, 203 / 10 ^ 39, 6724555128221608268, 4242721909926539673, 630118245525664765, 397560349370386783⟩,
    ⟨82, 100, 159, 233 / 10 ^ 41, 36143248623210700400, 22803850947114245497, 7354673373747273033, 4640282259296926456⟩,
    ⟨86, 98, 156, 132 / 10 ^ 42, 79641170620168673833, 50247984153525417450, 43497921996957973433, 27444133206411171953⟩,
    ⟨88, 113, 180, 179 / 10 ^ 56, 5504938256213345873657899, 3473229337418774934657366, 41311723474137723079719633, 26064795511149907129365023⟩],
    29538024848568682064022389, 43235274, 60, 8⟩

/-- Chain certificate for `m = 89`. -/
def hercherData89 : Entry :=
  ⟨[⟨0, 0, 0, 161 / 10 ^ 21, 9809721694, 6189245291, 630138897, 397573379⟩,
    ⟨36, 98, 155, 145 / 10 ^ 31, 83130157078217, 52449289519716, 517121682660006, 326267455807135⟩,
    ⟨61, 95, 151, 134 / 10 ^ 36, 9881527843552324, 6234549927241963, 186982516873599499, 117972833293231014⟩,
    ⟨74, 95, 151, 218 / 10 ^ 39, 6724555128221608268, 4242721909926539673, 630118245525664765, 397560349370386783⟩,
    ⟨82, 99, 157, 272 / 10 ^ 41, 36143248623210700400, 22803850947114245497, 7354673373747273033, 4640282259296926456⟩,
    ⟨86, 97, 154, 197 / 10 ^ 42, 79641170620168673833, 50247984153525417450, 43497921996957973433, 27444133206411171953⟩,
    ⟨89, 71, 113, 787 / 10 ^ 44, 202780263237295321099, 127940101513462006853, 123139092617126647266, 77692117359936589403⟩,
    ⟨89, 189, 200, 933 / 10 ^ 80, 5504938256213345873657899, 3473229337418774934657366, 41311723474137723079719633, 26064795511149907129365023⟩],
    29538024848568682064022389, 27278420, 60, 8⟩

/-- Chain certificate for `m = 90`. -/
def hercherData90 : Entry :=
  ⟨[⟨0, 0, 0, 163 / 10 ^ 21, 9809721694, 6189245291, 630138897, 397573379⟩,
    ⟨36, 97, 153, 148 / 10 ^ 31, 83130157078217, 52449289519716, 517121682660006, 326267455807135⟩,
    ⟨61, 94, 149, 138 / 10 ^ 36, 9881527843552324, 6234549927241963, 186982516873599499, 117972833293231014⟩,
    ⟨74, 94, 149, 232 / 10 ^ 39, 6724555128221608268, 4242721909926539673, 630118245525664765, 397560349370386783⟩,
    ⟨82, 98, 155, 311 / 10 ^ 41, 36143248623210700400, 22803850947114245497, 7354673373747273033, 4640282259296926456⟩,
    ⟨86, 96, 152, 263 / 10 ^ 42, 79641170620168673833, 50247984153525417450, 43497921996957973433, 27444133206411171953⟩,
    ⟨89, 70, 112, 390 / 10 ^ 43, 202780263237295321099, 127940101513462006853, 123139092617126647266, 77692117359936589403⟩,
    ⟨90, 119, 189, 106 / 10 ^ 58, 5504938256213345873657899, 3473229337418774934657366, 41311723474137723079719633, 26064795511149907129365023⟩],
    29538024848568682064022389, 17210767, 61, 8⟩

/-- Chain certificate for `m = 91`. -/
def hercherData91 : Entry :=
  ⟨[⟨0, 0, 0, 164 / 10 ^ 21, 9809721694, 6189245291, 630138897, 397573379⟩,
    ⟨36, 96, 152, 151 / 10 ^ 31, 83130157078217, 52449289519716, 517121682660006, 326267455807135⟩,
    ⟨61, 93, 148, 143 / 10 ^ 36, 9881527843552324, 6234549927241963, 186982516873599499, 117972833293231014⟩,
    ⟨74, 93, 147, 247 / 10 ^ 39, 6724555128221608268, 4242721909926539673, 630118245525664765, 397560349370386783⟩,
    ⟨82, 97, 153, 350 / 10 ^ 41, 36143248623210700400, 22803850947114245497, 7354673373747273033, 4640282259296926456⟩,
    ⟨86, 95, 151, 329 / 10 ^ 42, 79641170620168673833, 50247984153525417450, 43497921996957973433, 27444133206411171953⟩,
    ⟨89, 70, 111, 621 / 10 ^ 43, 202780263237295321099, 127940101513462006853, 123139092617126647266, 77692117359936589403⟩,
    ⟨91, 75, 119, 186 / 10 ^ 45, 12261796429850908150604, 7736332199829210068325, 325919355854421968365, 205632218873398596256⟩],
    7941964418702608664581, 2919, 62, 8⟩

/-- The chain certificates, entry `i` for `m = i + 1` (generated with exact rational arithmetic). -/
def hercherData : List Entry :=
  [hercherData1, hercherData2, hercherData3, hercherData4, hercherData5, hercherData6,
   hercherData7, hercherData8, hercherData9, hercherData10, hercherData11, hercherData12,
   hercherData13, hercherData14, hercherData15, hercherData16, hercherData17, hercherData18,
   hercherData19, hercherData20, hercherData21, hercherData22, hercherData23, hercherData24,
   hercherData25, hercherData26, hercherData27, hercherData28, hercherData29, hercherData30,
   hercherData31, hercherData32, hercherData33, hercherData34, hercherData35, hercherData36,
   hercherData37, hercherData38, hercherData39, hercherData40, hercherData41, hercherData42,
   hercherData43, hercherData44, hercherData45, hercherData46, hercherData47, hercherData48,
   hercherData49, hercherData50, hercherData51, hercherData52, hercherData53, hercherData54,
   hercherData55, hercherData56, hercherData57, hercherData58, hercherData59, hercherData60,
   hercherData61, hercherData62, hercherData63, hercherData64, hercherData65, hercherData66,
   hercherData67, hercherData68, hercherData69, hercherData70, hercherData71, hercherData72,
   hercherData73, hercherData74, hercherData75, hercherData76, hercherData77, hercherData78,
   hercherData79, hercherData80, hercherData81, hercherData82, hercherData83, hercherData84,
   hercherData85, hercherData86, hercherData87, hercherData88, hercherData89, hercherData90,
   hercherData91]

/-- The empty entry (never used for `1 ≤ m ≤ 91`). -/
def defaultEntry : Entry := ⟨[], 0, 0, 0, 0⟩

/-- One entry: the chain from `K ≥ 1` to `K ≥ Kf` and the Rhin contradiction above `Kf`. -/
def entryOK (m : ℕ) (e : Entry) : Bool :=
  chainOK m 1 e.steps e.Kf && rhinOK m e.Kf e.V e.cexp e.kexp

/-- **The kernel check of all 91 chains and Rhin contradictions**, one `m` at a time. -/
theorem hercherData_ok (m : ℕ) (h1 : 1 ≤ m) (h2 : m ≤ 91) :
    entryOK m (hercherData.getD (m - 1) defaultEntry) = true := by
  interval_cases m <;> decide +kernel

/-- **Hercher's theorem** (`m ≤ 91` excluded): if every `0 < n ≤ 695 · 2⁶⁰` reaches 1 and
Simons–de Weger's Lemma 12 (Rhin's transcendence measure) holds, every nontrivial positive
`T`-cycle has at least 92 local minima. -/
theorem hercher_theorem (hX₀ : ∀ n, 0 < n → n ≤ 695 * 2 ^ 60 → Reaches T n 1)
    (hR : RhinBound) : HercherTheorem := by
  intro x p hx hp hcyc hx1 hx2
  by_contra hlt
  push_neg at hlt
  have hpos := numLocalMin_pos hx hp hcyc
  obtain ⟨m, hm⟩ : ∃ m, numLocalMin x p = m := ⟨_, rfl⟩
  have hK1 : 1 ≤ oddCount T x p := oddCount_pos_of_numLocalMin_pos hpos
  rw [hm] at hlt hpos
  have hlow : ∀ j, hercherX₀ ≤ T^[j] x := by
    intro j
    by_contra h
    push_neg at h
    unfold hercherX₀ at h
    exact cycle_not_reaches_one hp hcyc hx1 hx2 j (hX₀ _ (iterate_T_pos hx j) h.le)
  have he := hercherData_ok m (by omega) (by omega)
  unfold entryOK at he
  rw [Bool.and_eq_true] at he
  have h1 := chainOK_sound hx hp hcyc hm (by omega) hlow _ 1 _ hK1 he.1
  have h2 := K_lt_of_rhinOK hR hx hp hcyc hx1 hx2 hm he.2
  omega

end Collatz
