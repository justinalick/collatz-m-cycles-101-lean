import Collatz.Statements
import Collatz.FareyCertificate
import Collatz.LogTwoThreeBounds

/-!
# The `m = 91` bootstrap of Hercher's Theorem 23, with the analytic inputs as hypotheses

Hercher (J. Integer Seq. 26 (2023), Art. 23.3.5, Theorem 23, with the corrigendum of 14 June 2026 to
Theorem 21) excludes Collatz `m`-cycles with `m ≤ 91` by a bootstrap. For `m = 91`, `K` odd and `L`
even elements, `X₀ = 695 · 2⁶⁰`, and `δ = log₂ 3`, the chain is (`research/scripts/hercher_thm23_bootstrap.py`,
validated against the paper's printed values):

| step `j` | premise        | `m₂` | `ε_j` (Theorem 21) | consequence `K ≥ K_j` (Lemma 22) |
|---|---|---|---|---|
| 1 | `K ≥ 7.5311 · 10¹¹` (Simons–de Weger, Corollary 11) | 47 | `6.407 · 10⁻³²` | `K ≥ 5 267 319 278 509 397` |
| 2 | `K ≥ K₁` | 67 | `5.067 · 10⁻³⁶` | `K ≥ 397 560 349 370 386 783` |
| 3 | `K ≥ K₂` | 77 | `4.002 · 10⁻³⁸` | `K ≥ 4 640 282 259 296 926 456` |
| 4 | `K ≥ K₃` | 82 | `2.266 · 10⁻³⁹` | `K ≥ 27 444 133 206 411 171 953` |
| 5 | `K ≥ K₄` | 86 | `2.260 · 10⁻⁴⁰` | `K ≥ 77 692 117 359 936 589 403` |
| 6 | `K ≥ K₅` | 88 | `5.208 · 10⁻⁴¹` | `K ≥ 205 632 218 873 398 596 256` |
| 7 | `K ≥ K₆` | 91 | `1.230 · 10⁻⁴³` | `K ≥ 7 941 964 418 702 608 664 581` |

and `K₇ > 1.4784 · 91 · δ⁹¹ ≈ 2.14 · 10²⁰`, the Simons–de Weger ceiling (Lemma 16 / Theorem 3(d)),
so no 91-cycle exists. (The `ε_j` are the values of Theorem 21 at the premise, rounded up to four
significant digits; a larger `ε` only weakens the hypothesis, and the rounding does not change any
`K_j`.)

The Simons–de Weger seed can itself be replaced by two more steps of the same kind, starting from the
trivial `K ≥ 1` (`seed_of_theorem14`): step 0 is Theorem 14 with `m₁ = m` (no window; the bound
`Σ T(nᵢ) < (97·91 + 73)/(54 X₀)` holds for every 91-cycle), step 0′ is Theorem 21 with `m₂ = 36`:

| step | premise | `m₂` | `ε` | consequence |
|---|---|---|---|---|
| 0 | `K ≥ 1` | — (Theorem 14) | `9.892 · 10⁻²⁰` | `K ≥ 6 586 818 670` |
| 0′ | `K ≥ 6 586 818 670` | 36 | `9.126 · 10⁻³⁰` | `K ≥ 431 166 034 846 567 > 7.5311 · 10¹¹` |

## What is proved here, and what is assumed

This file proves the *arithmetic* of the chain: `bootstrap_core` shows that the seed, the ceiling and
the seven instances of Theorem 21 are jointly contradictory, `bootstrap_core_selfseeded` the same with
the seed replaced by steps 0 and 0′, and `no_91_cycle_of_hypotheses` /
`no_91_cycle_of_hypotheses_selfseeded` state this for `T`-cycles with 91 local minima
(`numLocalMin x p = 91`, Hercher's `m`; his `C` is the map `T` of `Defs.lean`). Each step is a Farey
certificate: two Farey neighbours `a/b < c/d` with `a/b ≤ deltaLo` and `deltaHi + ε_j ≤ c/d` (checked
by the kernel over `ℚ`), so that every fraction in `(δ, δ + ε_j) ⊆ (a/b, c/d)`, in particular
`(K+L)/K`, has denominator `≥ b + d = K_j` (`FareyCertificate.lean`), where `deltaLo < δ < deltaHi`
is the enclosure of `LogTwoThreeBounds.lean`. The certificates were computed by
`research/scripts/hercher_certificates.py`.

The following remain **hypotheses** of the theorems (not axioms: nothing in the library depends on
them, and they are discharged by whoever formalizes the analytic part):

* `hseed`: `K > 7.5311 · 10¹¹` for every 91-cycle — Simons and de Weger, Corollary 11 (Theorem 3(d));
  a best-approximation argument with the convergents of `δ`. Not needed in the self-seeded form.
* `hceil`: `K < 1.4784 · 91 · δ⁹¹` for every 91-cycle — Simons and de Weger, Lemma 16, which rests on
  their transcendence bound (Lemma 12, from Rhin's theorem) and their computation of the continued
  fraction of `δ` up to `a₂₀₀ ₀₀₁` (the champion table `A(m)`). Their weaker Lemma 14 bound
  `K < K₁(91) ≈ 2.6 · 10²¹` (Rhin's theorem and Lemma 7 only, no continued fraction table) would also
  suffice, since `K₇ ≈ 7.9 · 10²¹`.
* `H0`, `H0'`, `H1`–`H7`: Theorem 14 (`m₁ = m`) and Theorem 21 (as repaired by the corrigendum) for
  `m = 91`, `X₀ = 695 · 2⁶⁰` and the stated `m₂`, at the nine stages: every 91-cycle with `K ≥ K_{j−1}`
  has `(K+L)/K ∈ (δ, δ + ε_j)`. These are the real-analysis content of Hercher's paper (Theorems 14,
  16, Lemma 20, and the convex vertex argument of the corrigendum); see
  `docs/hercher_formalization_roadmap.md`.

Everything else — the enclosure of `δ`, the Farey certificates, the numerics of the ceiling — is
machine-checked.

**Superseded.** The hypotheses of `no_91_cycle_of_hypotheses` and
`no_91_cycle_of_hypotheses_selfseeded` quantify over *every* cycle with 91 local minima, including
the trivial cycle run 91 times (`x = 1`, `p = 182`, `K = 91`), for which `hseed` and `H0` are false;
they cannot be discharged, and the conclusion is false for that cycle. The analytic inputs are
now proved for nontrivial cycles: see `no_91_cycle` (`HercherNo91.lean`), `no_91_cycle_of_rhin`
(`HercherRhin.lean`) and `hercher_theorem` (`HercherAll.lean`).
-/

namespace Collatz

/-- The conclusion of Hercher's Theorem 21 for a cycle with `p = K + L` steps and `K` odd elements:
`δ < (K+L)/K < δ + ε`. -/
def RatioIn (p K : ℕ) (ε : ℚ) : Prop :=
  Real.logb 2 3 < (p : ℝ) / K ∧ (p : ℝ) / K < Real.logb 2 3 + (ε : ℝ)

/-- One step of the bootstrap: if `(K+L)/K ∈ (δ, δ + ε)` and `a/b < c/d` are Farey neighbours with
`a/b ≤ deltaLo` and `deltaHi + ε ≤ c/d`, then `K ≥ b + d`. -/
theorem chain_step {p K : ℕ} (hK : 0 < K) {ε : ℚ} (h : RatioIn p K ε)
    {a c : ℤ} {b d : ℕ} (hb : 0 < b) (hd : 0 < d) (hF : c * b - a * d = 1)
    (hcert1 : (a : ℚ) / b ≤ deltaLo) (hcert2 : deltaHi + ε ≤ (c : ℚ) / d) : b + d ≤ K := by
  obtain ⟨h1, h2⟩ := h
  have hlo : ((deltaLo : ℚ) : ℝ) < (((p : ℚ) / (K : ℚ) : ℚ) : ℝ) := by
    push_cast
    exact lt_trans deltaLo_lt_logb h1
  have hhi : (((p : ℚ) / (K : ℚ) : ℚ) : ℝ) < ((deltaHi + ε : ℚ) : ℝ) := by
    push_cast
    linarith [logb_lt_deltaHi]
  have hloQ : deltaLo < (p : ℚ) / K := Rat.cast_lt.mp hlo
  have hhiQ : (p : ℚ) / K < deltaHi + ε := Rat.cast_lt.mp hhi
  exact farey_den_bound_div hK hb hd hF (lt_of_le_of_lt hcert1 hloQ) (lt_of_lt_of_le hhiQ hcert2)

/-! ### The values of `ε` (Theorem 14 or Theorem 21 at the premise of each step, rounded up). -/

/-- Step 0, Theorem 14 with `m₁ = m = 91` (no window), premise `K ≥ 1`:
`ε₀ = (97 · 91 + 73)/(54 · X₀ · 3 · log 2)`. -/
def eps0 : ℚ := 9892 / 10 ^ 23
/-- Step 0′, `m₂ = 36`, premise `K ≥ 6 586 818 670`. -/
def eps0' : ℚ := 9126 / 10 ^ 33
/-- Step 1, `m₂ = 47`, premise `K ≥ 753 110 000 000`. -/
def eps1 : ℚ := 6407 / 10 ^ 35
/-- Step 2, `m₂ = 67`, premise `K ≥ 5 267 319 278 509 397`. -/
def eps2 : ℚ := 5067 / 10 ^ 39
/-- Step 3, `m₂ = 77`, premise `K ≥ 397 560 349 370 386 783`. -/
def eps3 : ℚ := 4002 / 10 ^ 41
/-- Step 4, `m₂ = 82`, premise `K ≥ 4 640 282 259 296 926 456`. -/
def eps4 : ℚ := 2266 / 10 ^ 42
/-- Step 5, `m₂ = 86`, premise `K ≥ 27 444 133 206 411 171 953`. -/
def eps5 : ℚ := 2260 / 10 ^ 43
/-- Step 6, `m₂ = 88`, premise `K ≥ 77 692 117 359 936 589 403`. -/
def eps6 : ℚ := 5208 / 10 ^ 44
/-- Step 7, `m₂ = 91`, premise `K ≥ 205 632 218 873 398 596 256`. -/
def eps7 : ℚ := 1230 / 10 ^ 46

/-- **The chain is contradictory.** For naturals `p` (steps) and `K` (odd elements) with the
Simons–de Weger seed `K > 7.5311 · 10¹¹` and ceiling `K < 1.4784 · 91 · δ⁹¹`, the seven instances of
Theorem 21 cannot all hold: each forces `K ≥ K_j` through a Farey certificate, and `K₇` exceeds the
ceiling. -/
theorem bootstrap_core {p K : ℕ} (hseed : 753110000000 < K)
    (hceil : (K : ℝ) < 14784 / 10000 * 91 * Real.logb 2 3 ^ 91)
    (H1 : 753110000000 ≤ K → RatioIn p K eps1)
    (H2 : 5267319278509397 ≤ K → RatioIn p K eps2)
    (H3 : 397560349370386783 ≤ K → RatioIn p K eps3)
    (H4 : 4640282259296926456 ≤ K → RatioIn p K eps4)
    (H5 : 27444133206411171953 ≤ K → RatioIn p K eps5)
    (H6 : 77692117359936589403 ≤ K → RatioIn p K eps6)
    (H7 : 205632218873398596256 ≤ K → RatioIn p K eps7) : False := by
  have hK : 0 < K := by omega
  -- step 1: certificate 766512153894657/483615324366283 < 7581991381868353/4783703954143114
  have k1 : 5267319278509397 ≤ K := by
    have h := chain_step hK (H1 (by omega)) (a := 766512153894657) (b := 483615324366283)
      (c := 7581991381868353) (d := 4783703954143114) (by norm_num) (by norm_num) (by norm_num)
      (by decide +kernel) (by decide +kernel)
    omega
  -- step 2
  have k2 : 397560349370386783 ≤ K := by
    have h := chain_step hK (H2 k1) (a := 423372672964960618) (b := 267118416222671843)
      (c := 206745572560704147) (d := 130441933147714940) (by norm_num) (by norm_num) (by norm_num)
      (by decide +kernel) (by decide +kernel)
    omega
  -- step 3
  have k3 : 4640282259296926456 ≤ K := by
    have h := chain_step hK (H3 k2) (a := 6724555128221608268) (b := 4242721909926539673)
      (c := 630118245525664765) (d := 397560349370386783) (by norm_num) (by norm_num) (by norm_num)
      (by decide +kernel) (by decide +kernel)
    omega
  -- step 4
  have k4 : 27444133206411171953 ≤ K := by
    have h := chain_step hK (H4 k3) (a := 36143248623210700400) (b := 22803850947114245497)
      (c := 7354673373747273033) (d := 4640282259296926456) (by norm_num) (by norm_num) (by norm_num)
      (by decide +kernel) (by decide +kernel)
    omega
  -- step 5
  have k5 : 77692117359936589403 ≤ K := by
    have h := chain_step hK (H5 k4) (a := 79641170620168673833) (b := 50247984153525417450)
      (c := 43497921996957973433) (d := 27444133206411171953) (by norm_num) (by norm_num) (by norm_num)
      (by decide +kernel) (by decide +kernel)
    omega
  -- step 6
  have k6 : 205632218873398596256 ≤ K := by
    have h := chain_step hK (H6 k5) (a := 202780263237295321099) (b := 127940101513462006853)
      (c := 123139092617126647266) (d := 77692117359936589403) (by norm_num) (by norm_num) (by norm_num)
      (by decide +kernel) (by decide +kernel)
    omega
  -- step 7
  have k7 : 7941964418702608664581 ≤ K := by
    have h := chain_step hK (H7 k6) (a := 12261796429850908150604) (b := 7736332199829210068325)
      (c := 325919355854421968365) (d := 205632218873398596256) (by norm_num) (by norm_num) (by norm_num)
      (by decide +kernel) (by decide +kernel)
    omega
  -- the ceiling: `δ < 8/5`, so `1.4784 · 91 · δ⁹¹ < 1.4784 · 91 · (8/5)⁹¹ < K₇`
  have hδ : Real.logb 2 3 ≤ 8 / 5 := by
    have h : (deltaHi : ℝ) ≤ 8 / 5 := by
      have hq : deltaHi ≤ (8 : ℚ) / 5 := by decide +kernel
      have hR := (Rat.cast_le (K := ℝ)).mpr hq
      push_cast at hR
      exact hR
    exact le_trans logb_lt_deltaHi.le h
  have h0 : (0 : ℝ) ≤ Real.logb 2 3 := Real.logb_nonneg (by norm_num) (by norm_num)
  have h91 : Real.logb 2 3 ^ 91 ≤ (8 / 5 : ℝ) ^ 91 := pow_le_pow_left₀ h0 hδ 91
  have hB : (14784 / 10000 : ℝ) * 91 * (8 / 5) ^ 91 < 7941964418702608664581 := by norm_num
  have hm := mul_le_mul_of_nonneg_left h91 (by norm_num : (0 : ℝ) ≤ 14784 / 10000 * 91)
  have hKR : (K : ℝ) < 7941964418702608664581 := by linarith
  have hKN : K < 7941964418702608664581 := by exact_mod_cast hKR
  omega

/-- **The seed from Theorem 14.** Two chain steps starting at the trivial `K ≥ 1` (Theorem 14 with
`m₁ = m`, then Theorem 21 with `m₂ = 36`) already give `K > 7.5311 · 10¹¹`, so the Simons–de Weger
seed is not needed. -/
theorem seed_of_theorem14 {p K : ℕ} (hK : 1 ≤ K)
    (H0 : 1 ≤ K → RatioIn p K eps0) (H0' : 6586818670 ≤ K → RatioIn p K eps0') :
    753110000000 < K := by
  have hK0 : 0 < K := by omega
  -- step 0: certificate 9809721694/6189245291 < 630138897/397573379
  have k0 : 6586818670 ≤ K := by
    have h := chain_step hK0 (H0 hK) (a := 9809721694) (b := 6189245291)
      (c := 630138897) (d := 397573379) (by norm_num) (by norm_num) (by norm_num)
      (by decide +kernel) (by decide +kernel)
    omega
  -- step 0′: certificate 83130157078217/52449289519716 < 600251839738223/378716745326851
  have k0' : 431166034846567 ≤ K := by
    have h := chain_step hK0 (H0' k0) (a := 83130157078217) (b := 52449289519716)
      (c := 600251839738223) (d := 378716745326851) (by norm_num) (by norm_num) (by norm_num)
      (by decide +kernel) (by decide +kernel)
    omega
  omega

/-- `bootstrap_core` with the Simons–de Weger seed replaced by steps 0 and 0′. -/
theorem bootstrap_core_selfseeded {p K : ℕ} (hK : 1 ≤ K)
    (hceil : (K : ℝ) < 14784 / 10000 * 91 * Real.logb 2 3 ^ 91)
    (H0 : 1 ≤ K → RatioIn p K eps0)
    (H0' : 6586818670 ≤ K → RatioIn p K eps0')
    (H1 : 753110000000 ≤ K → RatioIn p K eps1)
    (H2 : 5267319278509397 ≤ K → RatioIn p K eps2)
    (H3 : 397560349370386783 ≤ K → RatioIn p K eps3)
    (H4 : 4640282259296926456 ≤ K → RatioIn p K eps4)
    (H5 : 27444133206411171953 ≤ K → RatioIn p K eps5)
    (H6 : 77692117359936589403 ≤ K → RatioIn p K eps6)
    (H7 : 205632218873398596256 ≤ K → RatioIn p K eps7) : False :=
  bootstrap_core (seed_of_theorem14 hK H0 H0') hceil H1 H2 H3 H4 H5 H6 H7

/-- A cycle with a local minimum has an odd element, so `K ≥ 1`. -/
theorem oddCount_pos_of_numLocalMin {x p : ℕ} (h : numLocalMin x p = 91) :
    1 ≤ oddCount T x p := by
  have hpos : 0 < numLocalMin x p := by omega
  unfold numLocalMin at hpos
  obtain ⟨i, hi⟩ := Finset.card_pos.mp hpos
  rw [Finset.mem_filter, Finset.mem_range] at hi
  have h1 : oddCount T x (i + 1) = oddCount T x i + 1 := by rw [oddCount_succ, hi.2.1]
  have h2 : oddCount T x (i + 1) ≤ oddCount T x p := oddCount_mono T x (by omega)
  omega

/-- **Theorem 23 for `m = 91`, modulo the analytic inputs.** If every `T`-cycle with 91 local minima
satisfies the Simons–de Weger seed and ceiling and the seven instances of Theorem 21 listed in the
module docstring, then no `T`-cycle has exactly 91 local minima. -/
theorem no_91_cycle_of_hypotheses
    (hseed : ∀ x p, 0 < x → 0 < p → T^[p] x = x → numLocalMin x p = 91 →
      753110000000 < oddCount T x p)
    (hceil : ∀ x p, 0 < x → 0 < p → T^[p] x = x → numLocalMin x p = 91 →
      (oddCount T x p : ℝ) < 14784 / 10000 * 91 * Real.logb 2 3 ^ 91)
    (H1 : ∀ x p, 0 < x → 0 < p → T^[p] x = x → numLocalMin x p = 91 →
      753110000000 ≤ oddCount T x p → RatioIn p (oddCount T x p) eps1)
    (H2 : ∀ x p, 0 < x → 0 < p → T^[p] x = x → numLocalMin x p = 91 →
      5267319278509397 ≤ oddCount T x p → RatioIn p (oddCount T x p) eps2)
    (H3 : ∀ x p, 0 < x → 0 < p → T^[p] x = x → numLocalMin x p = 91 →
      397560349370386783 ≤ oddCount T x p → RatioIn p (oddCount T x p) eps3)
    (H4 : ∀ x p, 0 < x → 0 < p → T^[p] x = x → numLocalMin x p = 91 →
      4640282259296926456 ≤ oddCount T x p → RatioIn p (oddCount T x p) eps4)
    (H5 : ∀ x p, 0 < x → 0 < p → T^[p] x = x → numLocalMin x p = 91 →
      27444133206411171953 ≤ oddCount T x p → RatioIn p (oddCount T x p) eps5)
    (H6 : ∀ x p, 0 < x → 0 < p → T^[p] x = x → numLocalMin x p = 91 →
      77692117359936589403 ≤ oddCount T x p → RatioIn p (oddCount T x p) eps6)
    (H7 : ∀ x p, 0 < x → 0 < p → T^[p] x = x → numLocalMin x p = 91 →
      205632218873398596256 ≤ oddCount T x p → RatioIn p (oddCount T x p) eps7) :
    ∀ x p, 0 < x → 0 < p → T^[p] x = x → numLocalMin x p ≠ 91 := by
  intro x p hx hp hcyc h91
  exact bootstrap_core (hseed x p hx hp hcyc h91) (hceil x p hx hp hcyc h91)
    (H1 x p hx hp hcyc h91) (H2 x p hx hp hcyc h91) (H3 x p hx hp hcyc h91)
    (H4 x p hx hp hcyc h91) (H5 x p hx hp hcyc h91) (H6 x p hx hp hcyc h91)
    (H7 x p hx hp hcyc h91)

/-- **Theorem 23 for `m = 91`, self-seeded.** The same with the Simons–de Weger seed replaced by
Theorem 14 (`H0`) and one more instance of Theorem 21 (`H0'`); the only remaining input outside
Hercher's paper is the ceiling `hceil`. -/
theorem no_91_cycle_of_hypotheses_selfseeded
    (hceil : ∀ x p, 0 < x → 0 < p → T^[p] x = x → numLocalMin x p = 91 →
      (oddCount T x p : ℝ) < 14784 / 10000 * 91 * Real.logb 2 3 ^ 91)
    (H0 : ∀ x p, 0 < x → 0 < p → T^[p] x = x → numLocalMin x p = 91 →
      1 ≤ oddCount T x p → RatioIn p (oddCount T x p) eps0)
    (H0' : ∀ x p, 0 < x → 0 < p → T^[p] x = x → numLocalMin x p = 91 →
      6586818670 ≤ oddCount T x p → RatioIn p (oddCount T x p) eps0')
    (H1 : ∀ x p, 0 < x → 0 < p → T^[p] x = x → numLocalMin x p = 91 →
      753110000000 ≤ oddCount T x p → RatioIn p (oddCount T x p) eps1)
    (H2 : ∀ x p, 0 < x → 0 < p → T^[p] x = x → numLocalMin x p = 91 →
      5267319278509397 ≤ oddCount T x p → RatioIn p (oddCount T x p) eps2)
    (H3 : ∀ x p, 0 < x → 0 < p → T^[p] x = x → numLocalMin x p = 91 →
      397560349370386783 ≤ oddCount T x p → RatioIn p (oddCount T x p) eps3)
    (H4 : ∀ x p, 0 < x → 0 < p → T^[p] x = x → numLocalMin x p = 91 →
      4640282259296926456 ≤ oddCount T x p → RatioIn p (oddCount T x p) eps4)
    (H5 : ∀ x p, 0 < x → 0 < p → T^[p] x = x → numLocalMin x p = 91 →
      27444133206411171953 ≤ oddCount T x p → RatioIn p (oddCount T x p) eps5)
    (H6 : ∀ x p, 0 < x → 0 < p → T^[p] x = x → numLocalMin x p = 91 →
      77692117359936589403 ≤ oddCount T x p → RatioIn p (oddCount T x p) eps6)
    (H7 : ∀ x p, 0 < x → 0 < p → T^[p] x = x → numLocalMin x p = 91 →
      205632218873398596256 ≤ oddCount T x p → RatioIn p (oddCount T x p) eps7) :
    ∀ x p, 0 < x → 0 < p → T^[p] x = x → numLocalMin x p ≠ 91 := by
  intro x p hx hp hcyc h91
  exact bootstrap_core_selfseeded (oddCount_pos_of_numLocalMin h91) (hceil x p hx hp hcyc h91)
    (H0 x p hx hp hcyc h91) (H0' x p hx hp hcyc h91)
    (H1 x p hx hp hcyc h91) (H2 x p hx hp hcyc h91) (H3 x p hx hp hcyc h91)
    (H4 x p hx hp hcyc h91) (H5 x p hx hp hcyc h91) (H6 x p hx hp hcyc h91)
    (H7 x p hx hp hcyc h91)

end Collatz
