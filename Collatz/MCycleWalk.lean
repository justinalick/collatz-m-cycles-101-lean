import Collatz.MCycleChain

/-!
# The shapes left by Hercher's bootstrap: the bootstrap at a general floor and a Farey walk

For `m ≥ 92` the bootstrap of Hercher's Theorem 23 (`chainOK` of `HercherAll.lean`, here with a
general floor `X₀`: `stepOKX`, `chainOKX`) stops at the first fraction `q/K` in `(δ, δ + ε)`. The
remaining shapes `(K, p)` below the Rhin ceiling are enumerated by a walk down the Stern–Brocot tree
(`walk`): at a node with Farey neighbours `a/b < c/d` every fraction strictly between has
denominator at least `b + d`, so an `ε` valid for `K ≥ b + d` (a *stair* entry, checked by
`epsOKX`) decides whether the mediant `(a + c)/(b + d)` can be a shape; the in-interval mediants
and their multiples `j (b + d)` below the ceiling (`mults`) are listed. `walk_sound`: every shape
of a cycle below the ceiling is listed (or the walk reports a failure marker `(0, 0)`).
-/

namespace Collatz

open Finset

/-! ### The bootstrap with a general floor -/

/-- `ε` from Remark 7 summed (`m₂ = 0`) or Theorem 21 with the two-element bound, at the premise
`K ≥ Kp` and the floor `X₀` (the Farey fields of the step are not used here). -/
def epsOKX (X₀ m Kp : ℕ) (s : ChainStep) : Bool :=
  decide (0 < Kp ∧ 0 < s.eps) &&
  (if s.m₂ = 0 then decide ((m : ℚ) / X₀ ≤ s.eps * Kp * (6931471803 / 10 ^ 10))
   else decide (s.m₂ ≤ m ∧ 1 ≤ s.N ∧ 1 ≤ s.M ∧
     (s.N : ℚ) * m * geomQ deltaUp s.m₂ ≤ s.m₂ * Kp ∧
     (s.M : ℚ) * m * (1 + geomQ deltaUp (s.m₂ - 1)) ≤ s.m₂ * Kp ∧
     ((m - s.m₂ : ℕ) : ℚ) / X₀ + 1 / (2 ^ s.N - 1) + ((s.m₂ - 1 : ℕ) : ℚ) / (2 ^ s.M - 1) ≤
       s.eps * Kp * (6931471803 / 10 ^ 10)))

/-- **Soundness of `epsOKX`**: `(K + L)/K ∈ (δ, δ + ε)` for `K ≥ Kp`. -/
theorem epsOKX_sound {x p : ℕ} (hx : 0 < x) (hp : 0 < p) (hcyc : T^[p] x = x) {m X₀ : ℕ}
    (hm : numLocalMin x p = m) (hm1 : 1 ≤ m) (hX₀ : 0 < X₀) (hlow : ∀ j, X₀ ≤ T^[j] x)
    {Kp : ℕ} {s : ChainStep} (h : epsOKX X₀ m Kp s = true) (hK : Kp ≤ oddCount T x p) :
    RatioIn p (oddCount T x p) s.eps := by
  unfold epsOKX at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hKp, hε0⟩, hcase⟩ := h
  by_cases h0 : s.m₂ = 0
  · rw [if_pos h0, decide_eq_true_eq] at hcase
    exact ratioIn_of_crude hx hp hcyc hm hm1 hX₀ hlow hKp hK hε0 hcase
  · rw [if_neg h0, decide_eq_true_eq] at hcase
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hcase
    exact ratioIn_of_window_two hx hp hcyc hm (by omega) h1 hX₀ hlow hKp hK hε0 h2 h3 h4 h5 h6

/-- One bootstrap step at the floor `X₀`. -/
def stepOKX (X₀ m Kp : ℕ) (s : ChainStep) : Bool :=
  epsOKX X₀ m Kp s &&
    decide (0 < s.b ∧ 0 < s.d ∧ s.c * s.b - s.a * s.d = 1 ∧
      (s.a : ℚ) / s.b ≤ deltaLo ∧ deltaHi + s.eps ≤ (s.c : ℚ) / s.d)

/-- A bootstrap chain from `K ≥ Kp` to `K ≥ Kf` at the floor `X₀`. -/
def chainOKX (X₀ m : ℕ) : ℕ → List ChainStep → ℕ → Bool
  | Kp, [], Kf => decide (Kf ≤ Kp)
  | Kp, s :: rest, Kf => stepOKX X₀ m Kp s && chainOKX X₀ m (s.b + s.d) rest Kf

/-- **Soundness of `chainOKX`.** -/
theorem chainOKX_sound {x p : ℕ} (hx : 0 < x) (hp : 0 < p) (hcyc : T^[p] x = x) {m X₀ : ℕ}
    (hm : numLocalMin x p = m) (hm1 : 1 ≤ m) (hX₀ : 0 < X₀) (hlow : ∀ j, X₀ ≤ T^[j] x) :
    ∀ (steps : List ChainStep) (Kp Kf : ℕ), Kp ≤ oddCount T x p →
      chainOKX X₀ m Kp steps Kf = true → Kf ≤ oddCount T x p
  | [], Kp, Kf, hK, h => by
    simp only [chainOKX, decide_eq_true_eq] at h
    omega
  | s :: rest, Kp, Kf, hK, h => by
    simp only [chainOKX, Bool.and_eq_true] at h
    obtain ⟨hs, hrest⟩ := h
    refine chainOKX_sound hx hp hcyc hm hm1 hX₀ hlow rest (s.b + s.d) Kf ?_ hrest
    unfold stepOKX at hs
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hs
    obtain ⟨he, hb, hd, hF, hc1, hc2⟩ := hs
    have hr := epsOKX_sound hx hp hcyc hm hm1 hX₀ hlow he hK
    have hKp : 0 < Kp := by
      unfold epsOKX at he
      simp only [Bool.and_eq_true, decide_eq_true_eq] at he
      exact he.1.1
    exact chain_step (lt_of_lt_of_le hKp hK) hr hb hd hF hc1 hc2

/-! ### The Farey walk -/

/-- The first stair entry `(Kp, ε)` with `Kp ≤ K` (stairs are listed by decreasing `Kp`). -/
def epsAt (K : ℕ) : List (ℕ × ℚ) → Option ℚ
  | [] => none
  | e :: rest => if e.1 ≤ K then some e.2 else epsAt K rest

theorem epsAt_some {K : ℕ} {ε : ℚ} : ∀ {stair : List (ℕ × ℚ)}, epsAt K stair = some ε →
    ∃ e ∈ stair, e.1 ≤ K ∧ e.2 = ε
  | [], h => by simp [epsAt] at h
  | e :: rest, h => by
    unfold epsAt at h
    split_ifs at h with hle
    · simp only [Option.some.injEq] at h
      exact ⟨e, List.mem_cons.mpr (Or.inl rfl), hle, h⟩
    · obtain ⟨e', he', h1, h2⟩ := epsAt_some h
      exact ⟨e', List.mem_cons.mpr (Or.inr he'), h1, h2⟩

/-- The multiples `(j f, j e)`, `j = j₀, j₀ + 1, …`, below the ceiling and not excluded by a stair
entry (fuel `fuel`; `(0, 0)` marks exhausted fuel). -/
def mults (stair : List (ℕ × ℚ)) (Kceil Kmin e f : ℕ) : ℕ → ℕ → List (ℕ × ℕ)
  | 0, _ => [(0, 0)]
  | fuel + 1, j =>
    if Kceil ≤ j * f then []
    else match epsAt (max (j * f) Kmin) stair with
      | some ε =>
        if deltaHi + ε ≤ (e : ℚ) / f then [] else (j * f, j * e) :: mults stair Kceil Kmin e f fuel (j + 1)
      | none => (j * f, j * e) :: mults stair Kceil Kmin e f fuel (j + 1)

/-- The walk from the Farey neighbours `a/b < c/d` (fuel `fuel`; `(0, 0)` marks a failure); every
shape has `K ≥ Kmin`, so the premise at a node is `max (b + d) Kmin`. -/
def walk (stair : List (ℕ × ℚ)) (Kceil Kmin : ℕ) : ℕ → ℕ → ℕ → ℕ → ℕ → List (ℕ × ℕ)
  | 0, _, _, _, _ => [(0, 0)]
  | fuel + 1, a, b, c, d =>
    if Kceil ≤ b + d then []
    else match epsAt (max (b + d) Kmin) stair with
      | none => [(0, 0)]
      | some ε =>
        if ((a + c : ℕ) : ℚ) / ((b + d : ℕ) : ℚ) ≤ deltaLo then
          walk stair Kceil Kmin fuel (a + c) (b + d) c d
        else if deltaHi + ε ≤ ((a + c : ℕ) : ℚ) / ((b + d : ℕ) : ℚ) then
          walk stair Kceil Kmin fuel a b (a + c) (b + d)
        else
          mults stair Kceil Kmin (a + c) (b + d) (Kceil / (b + d) + 1) 1 ++
            (walk stair Kceil Kmin fuel a b (a + c) (b + d) ++
              walk stair Kceil Kmin fuel (a + c) (b + d) c d)

/-- **The multiples are listed.** -/
theorem mults_sound {stair : List (ℕ × ℚ)} {Kceil Kmin e f : ℕ} {j : ℕ}
    (hj : j * f < Kceil) (hmin : Kmin ≤ j * f)
    (hex : ∀ s ∈ stair, s.1 ≤ j * f → (e : ℚ) / f < deltaHi + s.2) :
    ∀ fuel j₀, j₀ ≤ j → (j * f, j * e) ∈ mults stair Kceil Kmin e f fuel j₀ ∨
      ((0 : ℕ), (0 : ℕ)) ∈ mults stair Kceil Kmin e f fuel j₀ := by
  intro fuel
  induction fuel with
  | zero => intro j₀ _; right; rw [mults]; exact List.mem_singleton.mpr rfl
  | succ fuel ih =>
    intro j₀ hj₀
    have hjf : j₀ * f ≤ j * f := Nat.mul_le_mul_right f hj₀
    have key : mults stair Kceil Kmin e f (fuel + 1) j₀ =
        (j₀ * f, j₀ * e) :: mults stair Kceil Kmin e f fuel (j₀ + 1) := by
      rw [mults, if_neg (by omega)]
      split
      · rename_i ε hε
        obtain ⟨s, hs, hs1, hs2⟩ := epsAt_some hε
        have hlt := hex s hs (le_trans hs1 (max_le hjf hmin))
        rw [hs2] at hlt
        rw [if_neg (not_le.mpr hlt)]
      · rfl
    rw [key]
    rcases Nat.eq_or_lt_of_le hj₀ with h | h
    · left; subst h; exact List.mem_cons.mpr (Or.inl rfl)
    · rcases ih (j₀ + 1) h with h1 | h1
      · left; exact List.mem_cons.mpr (Or.inr h1)
      · right; exact List.mem_cons.mpr (Or.inr h1)

/-- A fraction equal to the mediant of Farey neighbours is a multiple of it. -/
theorem eq_mediant_mul {a b c d K p : ℕ} (hF : c * b = a * d + 1) (hK : 0 < K)
    (h : (p : ℚ) / K = ((a + c : ℕ) : ℚ) / ((b + d : ℕ) : ℚ)) :
    ∃ j, 0 < j ∧ K = j * (b + d) ∧ p = j * (a + c) := by
  have hbd : 0 < b + d := by
    rcases Nat.eq_zero_or_pos (b + d) with h0 | h0
    · have hb : b = 0 := by omega
      have hd : d = 0 := by omega
      subst hb; subst hd; simp at hF
    · exact h0
  have hKq : (0 : ℚ) < K := by exact_mod_cast hK
  have hbdq : (0 : ℚ) < ((b + d : ℕ) : ℚ) := by exact_mod_cast hbd
  rw [div_eq_div_iff hKq.ne' hbdq.ne'] at h
  have hN : p * (b + d) = (a + c) * K := by exact_mod_cast h
  -- `(a + c) b = a (b + d) + 1`, so `gcd(b + d, a + c) = 1`
  have hF' : (a + c) * b = a * (b + d) + 1 := by rw [Nat.add_mul, Nat.mul_add, hF]; ring
  have hcop : Nat.Coprime (b + d) (a + c) := by
    show Nat.gcd (b + d) (a + c) = 1
    have h1 : Nat.gcd (b + d) (a + c) ∣ (a + c) * b :=
      Dvd.dvd.mul_right (Nat.gcd_dvd_right _ _) _
    have h2 : Nat.gcd (b + d) (a + c) ∣ a * (b + d) := Dvd.dvd.mul_left (Nat.gcd_dvd_left _ _) _
    have h3 : Nat.gcd (b + d) (a + c) ∣ 1 := by
      rw [hF'] at h1
      exact (Nat.dvd_add_right h2).mp h1
    exact Nat.dvd_one.mp h3
  have hdvd : (b + d) ∣ K := by
    have : (b + d) ∣ (a + c) * K := ⟨p, by rw [← hN]; ring⟩
    exact hcop.dvd_of_dvd_mul_left this
  obtain ⟨j, hj⟩ := hdvd
  refine ⟨j, ?_, by rw [hj]; ring, ?_⟩
  · rcases Nat.eq_zero_or_pos j with h0 | h0
    · rw [h0, Nat.mul_zero] at hj; omega
    · exact h0
  · rw [hj] at hN
    have : p * (b + d) = j * (a + c) * (b + d) := by rw [hN]; ring
    exact Nat.eq_of_mul_eq_mul_right hbd this

/-- **Soundness of the walk**: a fraction `p/K` with `K` below the ceiling, strictly between the
Farey neighbours `a/b < c/d`, above `deltaLo` and below `deltaHi + ε` for every stair entry
`(Kp, ε)` with `Kp ≤ K`, is listed (or the walk reports the marker `(0, 0)`). -/
theorem walk_sound {stair : List (ℕ × ℚ)} {Kceil Kmin K p : ℕ} (hK : K < Kceil) (hK0 : 0 < K)
    (hKmin : Kmin ≤ K) (hlo : deltaLo < (p : ℚ) / K)
    (hhi : ∀ s ∈ stair, s.1 ≤ K → (p : ℚ) / K < deltaHi + s.2) :
    ∀ (fuel a b c d : ℕ), 0 < b → 0 < d → c * b = a * d + 1 →
      (a : ℚ) / b < (p : ℚ) / K → (p : ℚ) / K < (c : ℚ) / d →
      (K, p) ∈ walk stair Kceil Kmin fuel a b c d ∨
        ((0 : ℕ), (0 : ℕ)) ∈ walk stair Kceil Kmin fuel a b c d := by
  intro fuel
  induction fuel with
  | zero => intro a b c d _ _ _ _ _; right; rw [walk]; exact List.mem_singleton.mpr rfl
  | succ fuel ih =>
    intro a b c d hb hd hF h1 h2
    -- `b + d ≤ K`
    have hbdK : b + d ≤ K := by
      have hFz : (c : ℤ) * b - (a : ℤ) * d = 1 := by
        have : ((c * b : ℕ) : ℤ) = ((a * d + 1 : ℕ) : ℤ) := by rw [hF]
        push_cast at this
        linarith
      have h1' : ((a : ℤ) : ℚ) / b < (p : ℚ) / K := by push_cast; exact h1
      have h2' : (p : ℚ) / K < ((c : ℤ) : ℚ) / d := by push_cast; exact h2
      exact farey_den_bound_div hK0 hb hd hFz h1' h2'
    rw [walk, if_neg (by omega)]
    split
    · right; exact List.mem_singleton.mpr rfl
    · rename_i ε hε
      obtain ⟨s, hs, hs1, hs2⟩ := epsAt_some hε
      have hlt : (p : ℚ) / K < deltaHi + ε := by
        rw [← hs2]; exact hhi s hs (le_trans hs1 (max_le hbdK hKmin))
      have hbd : 0 < b + d := by omega
      have hFl : (a + c) * b = a * (b + d) + 1 := by rw [Nat.add_mul, Nat.mul_add, hF]; ring
      have hFr : c * (b + d) = (a + c) * d + 1 := by rw [Nat.mul_add, Nat.add_mul, hF]; ring
      split_ifs with hlo' hhi'
      · -- the mediant is at most `deltaLo`: the right half
        exact ih (a + c) (b + d) c d hbd hd hFr (lt_of_le_of_lt hlo' hlo) h2
      · -- the mediant is at least `deltaHi + ε`: the left half
        exact ih a b (a + c) (b + d) hb hbd hFl h1 (lt_of_lt_of_le hlt hhi')
      · -- the mediant is in the interval
        rcases lt_trichotomy ((p : ℚ) / K) (((a + c : ℕ) : ℚ) / ((b + d : ℕ) : ℚ)) with hl | he | hr
        · rcases ih a b (a + c) (b + d) hb hbd hFl h1 hl with h | h
          · left; exact List.mem_append_right _ (List.mem_append_left _ h)
          · right; exact List.mem_append_right _ (List.mem_append_left _ h)
        · obtain ⟨j, hj0, hKj, hpj⟩ := eq_mediant_mul hF hK0 he
          have hm := mults_sound (stair := stair) (Kceil := Kceil) (Kmin := Kmin) (e := a + c)
            (f := b + d) (j := j) (by rw [← hKj]; exact hK) (by rw [← hKj]; exact hKmin)
            (fun s hs hs1 => by
              have := hhi s hs (by rw [hKj]; exact hs1)
              rw [he] at this
              exact this)
            (Kceil / (b + d) + 1) 1 hj0
          rw [← hKj, ← hpj] at hm
          rcases hm with h | h
          · left; exact List.mem_append_left _ h
          · right; exact List.mem_append_left _ h
        · rcases ih (a + c) (b + d) c d hbd hd hFr hr h2 with h | h
          · left; exact List.mem_append_right _ (List.mem_append_right _ h)
          · right; exact List.mem_append_right _ (List.mem_append_right _ h)

/-! ### All data for one `m` -/

/-- The floor: every element of a nontrivial cycle is at least `2⁷¹ + 1` when every
`0 < n ≤ 2⁷¹` reaches 1. -/
def mX₀ : ℕ := 2 ^ 71 + 1

/-- The exclusion data for one `m`: the bootstrap from `K ≥ 1` to `K ≥ Ks`; the root step (its
`ε` at the premise `Ks` and its Farey neighbours `a/b < c/d`, as naturals); the stair `(Kp, step)`
(decreasing `Kp`, the Farey fields of the steps are not used); the Rhin ceiling `Kceil` with its
parameters; the fuel of the walk; one shape certificate per listed shape. -/
structure MData where
  boot : List ChainStep
  Ks : ℕ
  root : ChainStep
  ra : ℕ
  rb : ℕ
  rc : ℕ
  rd : ℕ
  stair : List (ℕ × ChainStep)
  Kceil : ℕ
  V : ℕ
  cexp : ℕ
  kexp : ℕ
  fuel : ℕ
  certs : List ShapeCert

/-- The stair as pairs `(Kp, ε)`, the root entry last. -/
def MData.pairs (D : MData) : List (ℕ × ℚ) :=
  D.stair.map (fun e => (e.1, e.2.eps)) ++ [(D.Ks, D.root.eps)]

/-- The listed shapes. -/
def MData.shapes (D : MData) : List (ℕ × ℕ) :=
  walk D.pairs D.Kceil D.Ks D.fuel D.ra D.rb D.rc D.rd

/-- Every listed shape has an accepted certificate. -/
def certsOK (m S : ℕ) (grid : List (ℕ × ℕ)) (certs : List ShapeCert) (shapes : List (ℕ × ℕ)) :
    Bool :=
  shapes.all (fun s => certs.any (fun c => c.K == s.1 && c.P == s.2 && shapeOK m S grid c))

/-- **The check for one `m`.** -/
def mOK (m S : ℕ) (grid : List (ℕ × ℕ)) (D : MData) : Bool :=
  chainOKX mX₀ m 1 D.boot D.Ks && rhinOK m D.Kceil D.V D.cexp D.kexp &&
    epsOKX mX₀ m D.Ks D.root &&
    decide (0 < D.rb ∧ 0 < D.rd ∧ D.rc * D.rb = D.ra * D.rd + 1 ∧
      (D.ra : ℚ) / D.rb ≤ deltaLo ∧ deltaHi + D.root.eps ≤ (D.rc : ℚ) / D.rd) &&
    D.stair.all (fun e => epsOKX mX₀ m e.1 e.2) &&
    !(D.shapes.contains ((0 : ℕ), (0 : ℕ))) && certsOK m S grid D.certs D.shapes

theorem ratio_lt_of_ratioIn {p K : ℕ} {ε : ℚ} (hK : 0 < K) (h : RatioIn p K ε) :
    deltaLo < (p : ℚ) / K ∧ (p : ℚ) / K < deltaHi + ε := by
  obtain ⟨h1, h2⟩ := h
  have hlo : ((deltaLo : ℚ) : ℝ) < (((p : ℚ) / (K : ℚ) : ℚ) : ℝ) := by
    push_cast
    exact lt_trans deltaLo_lt_logb h1
  have hhi : (((p : ℚ) / (K : ℚ) : ℚ) : ℝ) < ((deltaHi + ε : ℚ) : ℝ) := by
    push_cast
    linarith [logb_lt_deltaHi]
  exact ⟨Rat.cast_lt.mp hlo, Rat.cast_lt.mp hhi⟩

/-- **Soundness of the check for one `m`**: no nontrivial cycle with `m` local minima has all its
elements above `2⁷¹`, given `RhinBound` and the two-rise bounds of the grid. -/
theorem mOK_sound (hR : RhinBound) {m S : ℕ} {grid : List (ℕ × ℕ)}
    (hgrid : ∀ e ∈ grid, TwoRiseBound e.1 e.2) (hS : S ≤ 60) {D : MData}
    (hok : mOK m S grid D = true) {x p : ℕ} (hx : 0 < x) (hp : 0 < p) (hcyc : T^[p] x = x)
    (hx1 : x ≠ 1) (hx2 : x ≠ 2) (hm : numLocalMin x p = m) (hlow : ∀ j, 2 ^ 71 < T^[j] x) :
    False := by
  simp only [mOK, certsOK, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
    List.all_eq_true] at hok
  obtain ⟨⟨⟨⟨⟨⟨hboot, hrhin⟩, hroot⟩, ⟨hrb, hrd, hF, hra, hrc⟩⟩, hstair⟩, hmark⟩, hcerts⟩ := hok
  have hpos := numLocalMin_pos hx hp hcyc
  have hm1 : 1 ≤ m := by rw [← hm]; exact hpos
  have hK1 : 1 ≤ oddCount T x p := oddCount_pos_of_numLocalMin_pos hpos
  have hX : 0 < mX₀ := by unfold mX₀; positivity
  have hlowX : ∀ j, mX₀ ≤ T^[j] x := fun j => by unfold mX₀; have := hlow j; omega
  have hKs := chainOKX_sound hx hp hcyc hm hm1 hX hlowX D.boot 1 D.Ks hK1 hboot
  have hKc := K_lt_of_rhinOK hR hx hp hcyc hx1 hx2 hm hrhin
  have hK0 : 0 < oddCount T x p := by omega
  -- the ratio bounds from the root and the stair
  have hr0 := ratio_lt_of_ratioIn hK0 (epsOKX_sound hx hp hcyc hm hm1 hX hlowX hroot hKs)
  have hhi : ∀ s ∈ D.pairs, s.1 ≤ oddCount T x p →
      (p : ℚ) / (oddCount T x p) < deltaHi + s.2 := by
    intro s hs hsK
    unfold MData.pairs at hs
    rcases List.mem_append.mp hs with h | h
    · obtain ⟨e, he, rfl⟩ := List.mem_map.mp h
      exact (ratio_lt_of_ratioIn hK0 (epsOKX_sound hx hp hcyc hm hm1 hX hlowX
        (hstair e he) hsK)).2
    · rw [List.mem_singleton] at h
      subst h
      exact hr0.2
  have hw := walk_sound (stair := D.pairs) hKc hK0 hKs hr0.1 hhi D.fuel D.ra D.rb D.rc D.rd
    hrb hrd hF (lt_of_le_of_lt hra hr0.1) (lt_of_lt_of_le hr0.2 hrc)
  have hmem : (oddCount T x p, p) ∈ D.shapes := by
    rcases hw with h | h
    · exact h
    · exfalso
      have h' : D.shapes.contains ((0 : ℕ), (0 : ℕ)) = true := List.elem_eq_true_of_mem h
      rw [hmark] at h'
      exact Bool.false_ne_true h'
  obtain ⟨c, _, hc⟩ := List.any_eq_true.mp (hcerts _ hmem)
  simp only [Bool.and_eq_true, beq_iff_eq] at hc
  obtain ⟨⟨hcK, hcP⟩, hshape⟩ := hc
  exact shape_false hx hp hcyc hlow hgrid hS c hm hcK.symm hcP.symm hshape

end Collatz
