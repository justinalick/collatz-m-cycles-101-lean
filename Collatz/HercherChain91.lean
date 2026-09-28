import Collatz.HercherWindow
import Collatz.HercherBootstrap
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The first six steps of the `m = 91` bootstrap, proved

`HercherBootstrap.lean` proves the arithmetic of Hercher's Theorem 23 for `m = 91` with the
analytic inputs as hypotheses `H0, H0', H1, …, H7`. This file proves enough of the analysis
(`HercherWindow.lean`: Theorem 16, Theorem 21 in vertex-free form, Remark 7 summed) to run the
chain unconditionally up to `K ≥ K₅ = 77 692 117 359 936 589 403`, the premise of step 6:

| step | premise `K ≥` | bound used | `m₂` | `N ≤ v` | `ε` | consequence `K ≥` |
|---|---|---|---|---|---|---|
| 0 | 1 | `theorem14_crude` | — | — | `1639 · 10⁻²²` | 6 586 818 670 |
| 1 | 6 586 818 670 | `theorem21_vertexFree` | 36 | 96 | `1504 · 10⁻³²` | 378 716 745 326 851 |
| 2 | 378 716 745 326 851 | same | 61 | 93 | `1427 · 10⁻³⁷` | 124 207 383 220 472 977 |
| 3 | 124 207 383 220 472 977 | same | 74 | 93 | `2465 · 10⁻⁴⁰` | 4 640 282 259 296 926 456 |
| 4 | 4 640 282 259 296 926 456 | same | 82 | 97 | `3493 · 10⁻⁴²` | 27 444 133 206 411 171 953 |
| 5 | 27 444 133 206 411 171 953 | same | 86 | 95 | `3281 · 10⁻⁴³` | 77 692 117 359 936 589 403 |

(The chain of `docs/hercher_formalization_roadmap.md` with Theorem 14 replaced by Remark 7 and
the vertex bound (f) dropped, the best `m₂` at each step; the certificates are recomputed from
these bounds, see `docs/formalization.md`. Each `ε` is checked against the bound by the kernel
over `ℚ`, with `log 2 > 0.6931471803` (`Real.log_two_gt_d9`), `δ ≤ 1.584962501` and `2^v ≥ 2^N`.)

`K_ge_of_numLocalMin_91` is the result: every positive `T`-cycle with 91 local minima whose
elements all exceed `X₀ = 695 · 2⁶⁰` has `K ≥ 77 692 117 359 936 589 403` odd elements.
`no_91_cycle_of_H6_H7` then needs only the last two instances of Theorem 21 (with the vertex
bound) and the Simons–de Weger ceiling; unlike `no_91_cycle_of_hypotheses`, all its hypotheses
are quantified over *nontrivial* cycles (`x ≠ 1, 2`): the trivial cycle run 91 times
(`x = 1`, `p = 182`) has 91 local minima and `K = 91`, so hypotheses quantified over every
cycle with 91 local minima are false for it.
-/

namespace Collatz

open Finset

/-- `δ ≤ 1.584962501`. -/
def deltaUp : ℚ := 1584962501 / 10 ^ 9

theorem logb_le_deltaUp : Real.logb 2 3 ≤ (deltaUp : ℝ) := by
  have h : deltaHi ≤ deltaUp := by decide +kernel
  have hR := (Rat.cast_le (K := ℝ)).mpr h
  exact le_trans logb_lt_deltaHi.le hR

/-- `Σ_{d<n} q^d`, computably. -/
def geomQ (q : ℚ) : ℕ → ℚ
  | 0 => 0
  | n + 1 => geomQ q n + q ^ n

theorem geomQ_eq (q : ℚ) (n : ℕ) : geomQ q n = ∑ d ∈ range n, q ^ d := by
  induction n with
  | zero => rfl
  | succ n ih => rw [geomQ, ih, sum_range_succ]

theorem log_two_gt' : (6931471803 / 10 ^ 10 : ℝ) < Real.log 2 := by
  have h := Real.log_two_gt_d9
  have e : (0.6931471803 : ℝ) = 6931471803 / 10 ^ 10 := by norm_num
  linarith

/-- The lower half of Theorem 16: `δ < p/K` for a positive cycle with `K ≥ 1`. -/
theorem logb_lt_ratio {x p : ℕ} (hx : 0 < x) (hp : 0 < p) (hcyc : T^[p] x = x)
    (hK : 0 < oddCount T x p) : Real.logb 2 3 < (p : ℝ) / oddCount T x p := by
  have h := (cycle_bounds hx hp hcyc (m := 1) one_pos
    (fun i _ _ => iterate_T_pos hx i)).1
  have hR := (Rat.cast_lt (K := ℝ)).mpr h
  push_cast at hR
  have hl := Real.log_lt_log (by positivity) hR
  rw [Real.log_pow, Real.log_pow] at hl
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hKR : (0 : ℝ) < oddCount T x p := by exact_mod_cast hK
  rw [Real.logb, div_lt_div_iff₀ hlog2 hKR]
  linarith

/-- From `p log 2 − K log 3 < B ≤ ε K₀ · 0.6931471803` with `K ≥ K₀ > 0` to `RatioIn p K ε`. -/
theorem ratioIn_of_lambda_lt {x p : ℕ} (hx : 0 < x) (hp : 0 < p) (hcyc : T^[p] x = x)
    {Kp : ℕ} (hKp : 0 < Kp) (hK : Kp ≤ oddCount T x p) {ε : ℚ} (hε0 : 0 < ε) {B : ℝ}
    (hΛ : (p : ℝ) * Real.log 2 - (oddCount T x p : ℝ) * Real.log 3 < B)
    (hB : B ≤ (ε : ℝ) * Kp * (6931471803 / 10 ^ 10)) : RatioIn p (oddCount T x p) ε := by
  have hKpos : 0 < oddCount T x p := lt_of_lt_of_le hKp hK
  unfold RatioIn
  refine ⟨logb_lt_ratio hx hp hcyc hKpos, ?_⟩
  have hl2 := log_two_gt'
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hKR : (Kp : ℝ) ≤ oddCount T x p := by exact_mod_cast hK
  have hKR' : (0 : ℝ) < oddCount T x p := by exact_mod_cast hKpos
  have hε' : (0 : ℝ) < ε := by exact_mod_cast hε0
  have a1 : (ε : ℝ) * Kp ≤ ε * oddCount T x p := mul_le_mul_of_nonneg_left hKR hε'.le
  have a2 : (ε : ℝ) * Kp * (6931471803 / 10 ^ 10) ≤ ε * oddCount T x p * (6931471803 / 10 ^ 10) :=
    mul_le_mul_of_nonneg_right a1 (by norm_num)
  have a3 : (ε : ℝ) * oddCount T x p * (6931471803 / 10 ^ 10) ≤
      ε * oddCount T x p * Real.log 2 :=
    mul_le_mul_of_nonneg_left hl2.le (by positivity)
  have hmain : (p : ℝ) * Real.log 2 - (oddCount T x p : ℝ) * Real.log 3 <
      ε * oddCount T x p * Real.log 2 := by linarith
  have e : (p : ℝ) / oddCount T x p = Real.log 3 / Real.log 2 +
      ((p : ℝ) * Real.log 2 - (oddCount T x p : ℝ) * Real.log 3) /
        ((oddCount T x p : ℝ) * Real.log 2) := by
    have hK0 : (oddCount T x p : ℝ) ≠ 0 := hKR'.ne'
    have hl0 : Real.log 2 ≠ 0 := hlog2.ne'
    field_simp
    ring
  have h2 : ((p : ℝ) * Real.log 2 - (oddCount T x p : ℝ) * Real.log 3) /
      ((oddCount T x p : ℝ) * Real.log 2) < ε := by
    rw [div_lt_iff₀ (by positivity)]
    have e' : (ε : ℝ) * oddCount T x p * Real.log 2 = ε * (oddCount T x p * Real.log 2) := by ring
    linarith
  rw [e, Real.logb]
  linarith

/-- **A chain step from Remark 7** (Theorem 14 replaced by `3/X₀` per minimum). -/
theorem ratioIn_of_crude {x p : ℕ} (hx : 0 < x) (hp : 0 < p) (hcyc : T^[p] x = x)
    {m Kp X₀ : ℕ} (hm : numLocalMin x p = m) (hm1 : 1 ≤ m) (hX₀ : 0 < X₀)
    (hlow : ∀ j, X₀ ≤ T^[j] x) (hKp : 0 < Kp) (hK : Kp ≤ oddCount T x p) {ε : ℚ}
    (hε0 : 0 < ε) (hε : (m : ℚ) / X₀ ≤ ε * Kp * (6931471803 / 10 ^ 10)) :
    RatioIn p (oddCount T x p) ε := by
  have h14 := theorem14_crude hx hp hcyc (by rw [hm]; exact hm1) (X₀ := (X₀ : ℝ))
    (by exact_mod_cast hX₀) (fun j => by exact_mod_cast hlow j)
  rw [hm] at h14
  have hεR := (Rat.cast_le (K := ℝ)).mpr hε
  push_cast at hεR
  have e : 3 * (m : ℝ) / (X₀ : ℝ) = 3 * ((m : ℝ) / (X₀ : ℝ)) := by ring
  exact ratioIn_of_lambda_lt hx hp hcyc hKp hK hε0 (B := (m : ℝ) / X₀) (by linarith)
    (by linarith [hεR])

/-- **A chain step from the vertex-free Theorem 21.** The rational side conditions:
`N m Σ_{d<m₂} deltaUp^d ≤ m₂ K₀` (so that `v ≥ N`) and
`(m − m₂)/X₀ + m₂/(2^N − 1) ≤ ε K₀ · 0.6931471803`. -/
theorem ratioIn_of_window {x p : ℕ} (hx : 0 < x) (hp : 0 < p) (hcyc : T^[p] x = x)
    {m m₂ N Kp X₀ : ℕ} (hm : numLocalMin x p = m) (hm₂ : 1 ≤ m₂) (hm₂m : m₂ ≤ m) (hX₀ : 0 < X₀)
    (hlow : ∀ j, X₀ ≤ T^[j] x) (hKp : 0 < Kp) (hK : Kp ≤ oddCount T x p) {ε : ℚ}
    (hε0 : 0 < ε) (hN1 : 1 ≤ N)
    (hN : (N : ℚ) * m * geomQ deltaUp m₂ ≤ m₂ * Kp)
    (hε : ((m - m₂ : ℕ) : ℚ) / X₀ + m₂ / (2 ^ N - 1) ≤ ε * Kp * (6931471803 / 10 ^ 10)) :
    RatioIn p (oddCount T x p) ε := by
  have h21 := theorem21_vertexFree hx hp hcyc hm₂ (by rw [hm]; exact hm₂m) (X₀ := (X₀ : ℝ))
    (by exact_mod_cast hX₀) (fun j => by exact_mod_cast hlow j)
  rw [hm] at h21
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hGpos := geomSum_delta_pos hm₂
  have hδ0 : (0 : ℝ) ≤ Real.logb 2 3 := by linarith [one_le_logb_two_three]
  have hG : ∑ d ∈ range m₂, Real.logb 2 3 ^ d ≤ ∑ d ∈ range m₂, (deltaUp : ℝ) ^ d :=
    sum_le_sum (fun d _ => pow_le_pow_left₀ hδ0 logb_le_deltaUp d)
  have hNR : (N : ℝ) * m * ∑ d ∈ range m₂, (deltaUp : ℝ) ^ d ≤ m₂ * Kp := by
    rw [geomQ_eq] at hN
    have := (Rat.cast_le (K := ℝ)).mpr hN
    push_cast at this
    linarith [this]
  have hKR : (Kp : ℝ) ≤ oddCount T x p := by exact_mod_cast hK
  have hv : (N : ℝ) ≤ windowExp m m₂ (oddCount T x p) := by
    rw [windowExp, le_div_iff₀ (mul_pos hmpos hGpos)]
    have a1 : (N : ℝ) * ((m : ℝ) * ∑ d ∈ range m₂, Real.logb 2 3 ^ d) ≤
        (N : ℝ) * ((m : ℝ) * ∑ d ∈ range m₂, (deltaUp : ℝ) ^ d) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hG hmpos.le) (Nat.cast_nonneg _)
    have a2 : (m₂ : ℝ) * Kp ≤ m₂ * oddCount T x p :=
      mul_le_mul_of_nonneg_left hKR (Nat.cast_nonneg _)
    linarith
  have h2N : (2 : ℝ) ^ N ≤ (2 : ℝ) ^ windowExp m m₂ (oddCount T x p) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hv
  have h2N1 : (2 : ℝ) ≤ 2 ^ N := by
    calc (2 : ℝ) = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ N := pow_le_pow_right₀ (by norm_num) hN1
  have htail : 3 * (m₂ : ℝ) / ((2 : ℝ) ^ windowExp m m₂ (oddCount T x p) - 1) ≤
      3 * m₂ / ((2 : ℝ) ^ N - 1) :=
    div_le_div_of_nonneg_left (by positivity) (by linarith) (by linarith)
  have hεR := (Rat.cast_le (K := ℝ)).mpr hε
  push_cast at hεR
  have e1 : 3 * (m₂ : ℝ) / ((2 : ℝ) ^ N - 1) = 3 * ((m₂ : ℝ) / ((2 : ℝ) ^ N - 1)) := by ring
  have e2 : 3 * ((m - m₂ : ℕ) : ℝ) / (X₀ : ℝ) = 3 * (((m - m₂ : ℕ) : ℝ) / (X₀ : ℝ)) := by ring
  exact ratioIn_of_lambda_lt hx hp hcyc hKp hK hε0
    (B := ((m - m₂ : ℕ) : ℝ) / X₀ + m₂ / (2 ^ N - 1)) (by linarith) (by linarith [hεR])

/-- **Every cycle with 91 local minima above `X₀ = 695 · 2⁶⁰` has `K ≥ K₅`**: the first six
steps of the `m = 91` bootstrap, from Theorems 16 and 21 (vertex-free) and Remark 7. -/
theorem K_ge_of_numLocalMin_91 {x p : ℕ} (hx : 0 < x) (hp : 0 < p) (hcyc : T^[p] x = x)
    (h91 : numLocalMin x p = 91) (hlow : ∀ j, 695 * 2 ^ 60 ≤ T^[j] x) :
    77692117359936589403 ≤ oddCount T x p := by
  have hK1 := oddCount_pos_of_numLocalMin h91
  have hK : 0 < oddCount T x p := by omega
  have hX : 0 < 695 * 2 ^ 60 := by norm_num
  -- step 0 (Remark 7)
  have k0 : 6586818670 ≤ oddCount T x p := by
    have r := ratioIn_of_crude hx hp hcyc h91 (by norm_num) hX hlow (Kp := 1) (by norm_num) hK1
      (ε := 1639 / 10 ^ 22) (by norm_num) (by decide +kernel)
    have h := chain_step hK r (a := 9809721694) (b := 6189245291)
      (c := 630138897) (d := 397573379) (by norm_num) (by norm_num) (by norm_num)
      (by decide +kernel) (by decide +kernel)
    omega
  -- step 1, `m₂ = 36`
  have k1 : 378716745326851 ≤ oddCount T x p := by
    have r := ratioIn_of_window hx hp hcyc h91 (m₂ := 36) (N := 96) (by norm_num) (by norm_num)
      hX hlow (by norm_num) k0 (ε := 1504 / 10 ^ 32) (by norm_num) (by norm_num)
      (by decide +kernel) (by decide +kernel)
    have h := chain_step hK r (a := 83130157078217) (b := 52449289519716)
      (c := 517121682660006) (d := 326267455807135) (by norm_num) (by norm_num) (by norm_num)
      (by decide +kernel) (by decide +kernel)
    omega
  -- step 2, `m₂ = 61`
  have k2 : 124207383220472977 ≤ oddCount T x p := by
    have r := ratioIn_of_window hx hp hcyc h91 (m₂ := 61) (N := 93) (by norm_num) (by norm_num)
      hX hlow (by norm_num) k1 (ε := 1427 / 10 ^ 37) (by norm_num) (by norm_num)
      (by decide +kernel) (by decide +kernel)
    have h := chain_step hK r (a := 9881527843552324) (b := 6234549927241963)
      (c := 186982516873599499) (d := 117972833293231014) (by norm_num) (by norm_num)
      (by norm_num) (by decide +kernel) (by decide +kernel)
    omega
  -- step 3, `m₂ = 74`
  have k3 : 4640282259296926456 ≤ oddCount T x p := by
    have r := ratioIn_of_window hx hp hcyc h91 (m₂ := 74) (N := 93) (by norm_num) (by norm_num)
      hX hlow (by norm_num) k2 (ε := 2465 / 10 ^ 40) (by norm_num) (by norm_num)
      (by decide +kernel) (by decide +kernel)
    have h := chain_step hK r (a := 6724555128221608268) (b := 4242721909926539673)
      (c := 630118245525664765) (d := 397560349370386783) (by norm_num) (by norm_num)
      (by norm_num) (by decide +kernel) (by decide +kernel)
    omega
  -- step 4, `m₂ = 82`
  have k4 : 27444133206411171953 ≤ oddCount T x p := by
    have r := ratioIn_of_window hx hp hcyc h91 (m₂ := 82) (N := 97) (by norm_num) (by norm_num)
      hX hlow (by norm_num) k3 (ε := 3493 / 10 ^ 42) (by norm_num) (by norm_num)
      (by decide +kernel) (by decide +kernel)
    have h := chain_step hK r (a := 36143248623210700400) (b := 22803850947114245497)
      (c := 7354673373747273033) (d := 4640282259296926456) (by norm_num) (by norm_num)
      (by norm_num) (by decide +kernel) (by decide +kernel)
    omega
  -- step 5, `m₂ = 86`
  have r := ratioIn_of_window hx hp hcyc h91 (m₂ := 86) (N := 95) (by norm_num) (by norm_num)
    hX hlow (by norm_num) k4 (ε := 3281 / 10 ^ 43) (by norm_num) (by norm_num)
    (by decide +kernel) (by decide +kernel)
  have h := chain_step hK r (a := 79641170620168673833) (b := 50247984153525417450)
    (c := 43497921996957973433) (d := 27444133206411171953) (by norm_num) (by norm_num)
    (by norm_num) (by decide +kernel) (by decide +kernel)
  omega

/-- The same from the verification bound: if every `0 < n ≤ 695 · 2⁶⁰` reaches 1, every
nontrivial positive cycle with 91 local minima has `K ≥ 77 692 117 359 936 589 403`. -/
theorem K_ge_of_91_cycle (hX₀ : ∀ n, 0 < n → n ≤ 695 * 2 ^ 60 → Reaches T n 1)
    {x p : ℕ} (hx : 0 < x) (hp : 0 < p) (hcyc : T^[p] x = x) (hx1 : x ≠ 1) (hx2 : x ≠ 2)
    (h91 : numLocalMin x p = 91) : 77692117359936589403 ≤ oddCount T x p := by
  refine K_ge_of_numLocalMin_91 hx hp hcyc h91 (fun j => ?_)
  by_contra hlt
  push_neg at hlt
  exact cycle_not_reaches_one hp hcyc hx1 hx2 j (hX₀ _ (iterate_T_pos hx j) hlt.le)

/-- **Theorem 23 for `m = 91` from the last two instances of Theorem 21.** With the verification
bound `X₀ = 695 · 2⁶⁰`, the Simons–de Weger ceiling and Theorem 21 at steps 6 and 7
(`m₂ = 88, 91`, with the vertex bound of the corrigendum), no nontrivial positive `T`-cycle has
91 local minima. The hypotheses `H0, H0', H1, …, H5` of `no_91_cycle_of_hypotheses_selfseeded` are
discharged by `K_ge_of_91_cycle`. -/
theorem no_91_cycle_of_H6_H7 (hX₀ : ∀ n, 0 < n → n ≤ 695 * 2 ^ 60 → Reaches T n 1)
    (hceil : ∀ x p, 0 < x → 0 < p → T^[p] x = x → x ≠ 1 → x ≠ 2 → numLocalMin x p = 91 →
      (oddCount T x p : ℝ) < 14784 / 10000 * 91 * Real.logb 2 3 ^ 91)
    (H6 : ∀ x p, 0 < x → 0 < p → T^[p] x = x → x ≠ 1 → x ≠ 2 → numLocalMin x p = 91 →
      77692117359936589403 ≤ oddCount T x p → RatioIn p (oddCount T x p) eps6)
    (H7 : ∀ x p, 0 < x → 0 < p → T^[p] x = x → x ≠ 1 → x ≠ 2 → numLocalMin x p = 91 →
      205632218873398596256 ≤ oddCount T x p → RatioIn p (oddCount T x p) eps7) :
    ∀ x p, 0 < x → 0 < p → T^[p] x = x → x ≠ 1 → x ≠ 2 → numLocalMin x p ≠ 91 := by
  intro x p hx hp hcyc hx1 hx2 h91
  have k5 := K_ge_of_91_cycle hX₀ hx hp hcyc hx1 hx2 h91
  have hK : 0 < oddCount T x p := by omega
  -- step 6 (the certificate of `bootstrap_core`)
  have k6 : 205632218873398596256 ≤ oddCount T x p := by
    have h := chain_step hK (H6 x p hx hp hcyc hx1 hx2 h91 k5) (a := 202780263237295321099)
      (b := 127940101513462006853) (c := 123139092617126647266) (d := 77692117359936589403)
      (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel)
    omega
  -- step 7
  have k7 : 7941964418702608664581 ≤ oddCount T x p := by
    have h := chain_step hK (H7 x p hx hp hcyc hx1 hx2 h91 k6) (a := 12261796429850908150604)
      (b := 7736332199829210068325) (c := 325919355854421968365) (d := 205632218873398596256)
      (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel)
    omega
  -- the ceiling
  have hc := hceil x p hx hp hcyc hx1 hx2 h91
  have hδ : Real.logb 2 3 ≤ 8 / 5 := by
    have h : (deltaHi : ℝ) ≤ 8 / 5 := by
      have hq : deltaHi ≤ (8 : ℚ) / 5 := by decide +kernel
      have hR := (Rat.cast_le (K := ℝ)).mpr hq
      push_cast at hR
      exact hR
    exact le_trans logb_lt_deltaHi.le h
  have h0 : (0 : ℝ) ≤ Real.logb 2 3 := Real.logb_nonneg (by norm_num) (by norm_num)
  have h91' : Real.logb 2 3 ^ 91 ≤ (8 / 5 : ℝ) ^ 91 := pow_le_pow_left₀ h0 hδ 91
  have hB : (14784 / 10000 : ℝ) * 91 * (8 / 5) ^ 91 < 7941964418702608664581 := by norm_num
  have hm := mul_le_mul_of_nonneg_left h91' (by norm_num : (0 : ℝ) ≤ 14784 / 10000 * 91)
  have hKR : (oddCount T x p : ℝ) < 7941964418702608664581 := by linarith
  have hKN : oddCount T x p < 7941964418702608664581 := by exact_mod_cast hKR
  omega

end Collatz
