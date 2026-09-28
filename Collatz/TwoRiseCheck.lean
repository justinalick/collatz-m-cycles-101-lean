/-!
# Two consecutive rises from a number below `2^N`: the checker and its soundness

For an odd `n < 2^N` write `n + 1 = a · 2^{k₀}` (`a` odd; `k₀` is the first rise), let `ℓ ≥ 1` be the
length of the following descent and `k₁` the next rise. Then

  `3^{k₀} a + 2^ℓ = 2^{ℓ + k₁} a' + 1`   (`a'` odd, the next minimum is `a' 2^{k₁} − 1`),

and `a < 2^A`, `A = N − k₀` (`A = 1` if `k₀ = N`). `PairCond N B k₀` says that every such
configuration has `k₀ + k₁ ≤ B`. With `c = 3^{−k₀} mod 2^W` and `γ = c (1 − 2^ℓ)` one has
`a ≡ γ (mod 2^{min(W, ℓ + k₁)})`; so `k₀ + k₁ > B` forces the bits `A, …, B − k₀ + ℓ` of `γ` to vanish.
`kOK` refutes this for every `ℓ ≥ 1`:

* `ℓ > z`, `z ≥ A` a set bit of `c` (`γ ≡ c mod 2^ℓ`): automatic;
* `A ≤ ℓ ≤ z`, and `ℓ < lmin`: the direct test `directOK`;
* `lmin ≤ ℓ < A`: if the bits `A, …, A + E₁ − 1` of `γ` vanish, the `E₁`-bit window of `c` at
  `A − ℓ` equals the window `P` at `A` or `P − 1` (a borrow), so it agrees with `P` above the lowest
  set bit of `P`; a bit-parallel search (`matchMask`) over all positions at once finds the candidates,
  which get the direct test (`fallbackOK`).

The code is plain `Nat` arithmetic evaluated by the kernel (`decide +kernel`); the operations are
the kernel's GMP-accelerated primitives, called directly, and the loops are `Nat.rec`. (`Nat.log2`
is avoided: the kernel does not accelerate it.) This file imports nothing beyond Lean's core.
-/

namespace Collatz.TwoRise

/-! ### The checker -/

/-- Bit-parallel pattern search: bit `i < L` (`M = 2^L − 1`) of `matchMask M E X P` is set iff
bits `i, …, i + E − 1` of `X` equal bits `0, …, E − 1` of `P`. -/
def matchMask (M E : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ _ => M)
    (fun _ ih X P => Nat.land (Nat.xor X (cond (Nat.beq (Nat.land P 1) 1) 0 M))
      (ih (Nat.shiftRight X 1) (Nat.shiftRight P 1))) E

/-- The direct test of a pair `(k₀, ℓ)`, given `D = 2^{B+1−k₀}`, `A2 = 2^A`, `W2 = 2^W`, `L2 = 2^ℓ`:
with `J = D · L2 = 2^j`, `J ≤ W2` and `c (J + 1 − L2) mod J ≥ A2`, i.e. `γ = c (1 − 2^ℓ)` has a set
bit in `[A, j)`. -/
def directOK (D A2 W2 c L2 : Nat) : Bool :=
  Nat.ble (Nat.mul D L2) W2 &&
    Nat.ble A2 (Nat.mod (Nat.mul c (Nat.sub (Nat.add (Nat.mul D L2) 1) L2)) (Nat.mul D L2))

/-- `directOK` for `L2, 2 L2, …, 2^{cnt−1} L2`. -/
def directRange (D A2 W2 c cnt : Nat) : Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun _ ih L2 => directOK D A2 W2 c L2 && ih (Nat.mul 2 L2)) cnt

/-- Direct tests for every set bit `2^i` of `mm`, at `2^ℓ = A2 / 2^i`; fuel `f`. -/
def fallbackOK (D A2 W2 c f : Nat) : Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Bool) (fun mm => Nat.beq mm 0)
    (fun _ ih mm => cond (Nat.beq mm 0) true
      (let Pt := Nat.land mm (Nat.xor mm (Nat.sub mm 1));
        Nat.beq (Nat.land Pt (Nat.sub Pt 1)) 0 && Nat.ble 1 Pt && Nat.beq (Nat.land mm Pt) Pt &&
          directOK D A2 W2 c (Nat.div A2 Pt) && ih (Nat.xor mm Pt))) f

/-- The first `s' ≥ s` with bit `s'` of `x` set, scanning at most `f` positions (`s + f` if none).
(Only a heuristic: the checker verifies the bit it returns.) -/
def lowScan (x f : Nat) : Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun s => s)
    (fun _ ih s => cond (Nat.beq (Nat.land (Nat.shiftRight x s) 1) 1) s (ih (Nat.add s 1))) f

/-- The pattern test for `ℓ ∈ [lmin, A − 1]`, i.e. positions `i = A − ℓ ∈ [1, L − 1]`, with
`M = 2^L − 1`, `X = c mod 2^{A+E₁}`, `P = (c >>> A) mod 2^{E₁}` and `s` (claimed) the lowest set bit of
`P`: the windows `P` and `P − 1` agree on bits `s + 1, …, E₁ − 1`, which are searched; if `P = 0` both
windows (`0` and `2^{E₁} − 1`) are searched. Every hit gets the direct test. -/
def patternCore (D A2 W2 c E1 L M X P s : Nat) : Bool :=
  cond (Nat.blt s E1)
    (Nat.beq (Nat.land (Nat.shiftRight P s) 1) 1 && Nat.beq (Nat.mod P (Nat.pow 2 s)) 0 &&
      fallbackOK D A2 W2 c L
        (Nat.land (matchMask M (Nat.sub E1 (Nat.add s 1)) (Nat.shiftRight X (Nat.add s 1))
          (Nat.shiftRight P (Nat.add s 1))) (Nat.xor M 1)))
    (Nat.beq P 0 && fallbackOK D A2 W2 c L
      (Nat.land (Nat.lor (matchMask M E1 X 0) (matchMask M E1 X (Nat.sub (Nat.pow 2 E1) 1)))
        (Nat.xor M 1)))

/-- `patternCore` with its intermediate values. -/
def patternOK (D A2 W2 c A E1 lmin : Nat) : Bool :=
  let L := Nat.add (Nat.sub A lmin) 1
  let P := Nat.mod (Nat.shiftRight c A) (Nat.pow 2 E1)
  patternCore D A2 W2 c E1 L (Nat.sub (Nat.pow 2 L) 1) (Nat.mod c (Nat.pow 2 (Nat.add A E1))) P
    (lowScan P E1 0)

/-- All tests for one `k₀` (`c = 3^{−k₀} mod 2^W`), with `A = N − k₀` (`1` if `k₀ = N`),
`D = 2^{B+1−k₀}`, `A2 = 2^A`, `W2 = 2^W`, `y = c >>> A` and `t` (claimed) a set bit of `y`. -/
def kCore (B E1 W k0 c A D A2 W2 y t lmin : Nat) : Bool :=
  Nat.ble k0 (Nat.add B 1) && Nat.beq (Nat.land (Nat.shiftRight y t) 1) 1 &&
    directRange D A2 W2 c (Nat.add t 1) A2 &&
    directRange D A2 W2 c (Nat.sub (Nat.min A lmin) 1) 2 &&
    cond (Nat.ble A lmin) true (Nat.ble (Nat.add A E1) W && patternOK D A2 W2 c A E1 lmin)

/-- `kCore` with its intermediate values. -/
def kOK (N B E1 W k0 c : Nat) : Bool :=
  let A := cond (Nat.blt k0 N) (Nat.sub N k0) 1
  let y := Nat.shiftRight c A
  kCore B E1 W k0 c A (Nat.pow 2 (Nat.sub (Nat.add B 1) k0)) (Nat.pow 2 A) (Nat.pow 2 W) y
    (lowScan y W 0) (Nat.max 1 (Nat.sub (Nat.add N E1) (Nat.add B 1)))

/-- The loop over `k₀ = k, …, k + cnt − 1`; on entry `c = 3^{−(k−1)} mod 2^W`. -/
def loop (N B E1 W i3 cnt : Nat) : Nat → Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => true)
    (fun _ ih k c =>
      let c' := Nat.mod (Nat.mul c i3) (Nat.pow 2 W)
      kOK N B E1 W k c' && ih (Nat.add k 1) c') cnt

/-- The checker for `k₀ ∈ [k, k + cnt)` (`k ≥ 1`): `3 i3 ≡ 1` and `3^{k−1} c₀ ≡ 1` modulo `2^W`, then
the loop. -/
def rangeOK (N B E1 W i3 k c0 cnt : Nat) : Bool :=
  Nat.ble 1 k && Nat.beq (Nat.mod (Nat.mul 3 i3) (Nat.pow 2 W)) 1 &&
    Nat.beq (Nat.mod (Nat.mul (Nat.pow 3 (Nat.sub k 1)) c0) (Nat.pow 2 W)) 1 &&
    loop N B E1 W i3 cnt k c0

/-- `acc · b^e mod m` by repeated squaring with fuel `f` (only produces the start value of a chunk;
`rangeOK` verifies it). -/
def powMod (m : Nat) : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, acc => acc
  | f + 1, b, e, acc => cond (Nat.beq e 0) acc
      (powMod m f (Nat.mod (Nat.mul b b) m) (Nat.div e 2)
        (cond (Nat.beq (Nat.mod e 2) 1) (Nat.mod (Nat.mul acc b) m) acc))

/-! ### Soundness -/

/-- The two-rise condition for first rise `k₀` below `2^N`. -/
def PairCond (N B k0 : Nat) : Prop :=
  ∀ a l k1 a', a % 2 = 1 → 2 ^ k0 * a ≤ 2 ^ N → 1 ≤ l →
    3 ^ k0 * a + 2 ^ l = 2 ^ (l + k1) * a' + 1 → k0 + k1 ≤ B



/-- `a − c (1 − L) = c (x a + L − 1) − a (x c − 1)`. -/
theorem key_dvd {D x a c L : Int} (h1 : D ∣ x * a + L - 1) (h2 : D ∣ x * c - 1) :
    D ∣ a - c * (1 - L) := by
  have e : a - c * (1 - L) = c * (x * a + L - 1) - a * (x * c - 1) := by grind
  rw [e]
  exact Int.dvd_sub (Int.dvd_mul_of_dvd_right h1) (Int.dvd_mul_of_dvd_right h2)

/-- Integer divisibility of a difference gives equal residues. -/
theorem nat_mod_eq_of_int_dvd {x y m : Nat} (h : (m : Int) ∣ (x : Int) - (y : Int)) :
    x % m = y % m := by
  have h1 : ((x : Int) - y) % m = 0 := Int.emod_eq_zero_of_dvd h
  have h2 : (x : Int) % m = (y : Int) % m := Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr h1
  have h3 : ((x % m : Nat) : Int) = ((y % m : Nat) : Int) := h2
  exact Int.ofNat.inj h3

/-- From the rise relation: `2^j ∣ a − c (1 − 2^ℓ)` for `j ≤ W`, `j ≤ ℓ + k₁`. -/

theorem dvd_of_rel {k0 a l k1 a' c W j : Nat} (hc : 3 ^ k0 * c % 2 ^ W = 1)
    (hrel : 3 ^ k0 * a + 2 ^ l = 2 ^ (l + k1) * a' + 1) (hjW : j ≤ W) (hj : j ≤ l + k1) :
    ((2 ^ j : Nat) : Int) ∣ (a : Int) - (c : Int) * (1 - ((2 ^ l : Nat) : Int)) := by
  apply key_dvd (x := ((3 ^ k0 : Nat) : Int))
  · have e : ((3 ^ k0 : Nat) : Int) * a + ((2 ^ l : Nat) : Int) - 1 =
        ((2 ^ (l + k1) * a' : Nat) : Int) := by
      have : ((3 ^ k0 * a + 2 ^ l : Nat) : Int) = ((2 ^ (l + k1) * a' + 1 : Nat) : Int) := by
        rw [hrel]
      simp only [Int.natCast_add, Int.natCast_mul] at this ⊢
      omega
    rw [e]
    exact Int.natCast_dvd_natCast.mpr (Nat.dvd_mul_right_of_dvd (Nat.pow_dvd_pow 2 hj) _)
  · have hq := Nat.div_add_mod (3 ^ k0 * c) (2 ^ W)
    rw [hc] at hq
    have e : ((3 ^ k0 : Nat) : Int) * c - 1 = ((2 ^ W * (3 ^ k0 * c / 2 ^ W) : Nat) : Int) := by
      have : ((2 ^ W * (3 ^ k0 * c / 2 ^ W) + 1 : Nat) : Int) = ((3 ^ k0 * c : Nat) : Int) := by
        rw [hq]
      simp only [Int.natCast_add, Int.natCast_mul] at this ⊢
      omega
    rw [e]
    exact Int.natCast_dvd_natCast.mpr (Nat.dvd_mul_right_of_dvd (Nat.pow_dvd_pow 2 hjW) _)

/-- `a ≡ c (2^j + 1 − 2^ℓ) (mod 2^j)` for `ℓ ≤ j ≤ W`, `j ≤ ℓ + k₁`. -/

theorem mod_eq_of_rel {k0 a l k1 a' c W j : Nat} (hc : 3 ^ k0 * c % 2 ^ W = 1)
    (hrel : 3 ^ k0 * a + 2 ^ l = 2 ^ (l + k1) * a' + 1) (hlj : l ≤ j) (hjW : j ≤ W)
    (hj : j ≤ l + k1) : a % 2 ^ j = c * (2 ^ j + 1 - 2 ^ l) % 2 ^ j := by
  have h := dvd_of_rel hc hrel hjW hj
  have hle : 2 ^ l ≤ 2 ^ j + 1 := Nat.le_succ_of_le (Nat.pow_le_pow_right (by decide) hlj)
  apply nat_mod_eq_of_int_dvd
  have e : ((c * (2 ^ j + 1 - 2 ^ l) : Nat) : Int) =
      (c : Int) * (1 - ((2 ^ l : Nat) : Int)) + (c : Int) * ((2 ^ j : Nat) : Int) := by
    rw [Int.natCast_mul, Int.ofNat_sub hle, Int.natCast_add]
    simp only [Int.natCast_pow, Int.cast_ofNat_Int]
    grind
  rw [e]
  have e2 : (a : Int) - ((c : Int) * (1 - ((2 ^ l : Nat) : Int)) + (c : Int) * ((2 ^ j : Nat) : Int)) =
      ((a : Int) - (c : Int) * (1 - ((2 ^ l : Nat) : Int))) - (c : Int) * ((2 ^ j : Nat) : Int) := by
    grind
  rw [e2]
  exact Int.dvd_sub h (Int.dvd_mul_left _ _)

/-- `a ≡ c (mod 2^j)` for `j ≤ ℓ`, `j ≤ W`. -/

theorem mod_eq_of_rel_low {k0 a l k1 a' c W j : Nat} (hc : 3 ^ k0 * c % 2 ^ W = 1)
    (hrel : 3 ^ k0 * a + 2 ^ l = 2 ^ (l + k1) * a' + 1) (hjl : j ≤ l) (hjW : j ≤ W) :
    a % 2 ^ j = c % 2 ^ j := by
  have h := dvd_of_rel hc hrel hjW (Nat.le_trans hjl (Nat.le_add_right l k1))
  apply nat_mod_eq_of_int_dvd
  have hd : ((2 ^ j : Nat) : Int) ∣ (c : Int) * ((2 ^ l : Nat) : Int) :=
    Int.dvd_mul_of_dvd_right (Int.natCast_dvd_natCast.mpr (Nat.pow_dvd_pow 2 hjl))
  have e : (a : Int) - c = ((a : Int) - (c : Int) * (1 - ((2 ^ l : Nat) : Int))) -
      (c : Int) * ((2 ^ l : Nat) : Int) := by grind
  rw [e]
  exact Int.dvd_sub h hd

theorem pow_eq' (a b : Nat) : Nat.pow a b = a ^ b := rfl

theorem mod_eq' (a b : Nat) : Nat.mod a b = a % b := rfl

theorem div_eq' (a b : Nat) : Nat.div a b = a / b := rfl

theorem shiftRight_eq' (a b : Nat) : Nat.shiftRight a b = a >>> b := rfl

theorem directOK_iff (D A2 W2 c L2 : Nat) :
    directOK D A2 W2 c L2 = true ↔ D * L2 ≤ W2 ∧ A2 ≤ c * (D * L2 + 1 - L2) % (D * L2) := by
  simp only [directOK, Bool.and_eq_true, Nat.ble_eq, Nat.mul_eq, Nat.add_eq, Nat.sub_eq, mod_eq']

/-- The direct test refutes `k₀ + k₁ > B` at `ℓ`. -/

theorem directOK_false {D A2 W2 c L2 k0 a l k1 a' W A B : Nat}
    (h : directOK D A2 W2 c L2 = true) (hc : 3 ^ k0 * c % 2 ^ W = 1)
    (hrel : 3 ^ k0 * a + 2 ^ l = 2 ^ (l + k1) * a' + 1)
    (hD : D = 2 ^ (B + 1 - k0)) (hA2 : A2 = 2 ^ A) (hW2 : W2 = 2 ^ W) (hL2 : L2 = 2 ^ l)
    (hbad : B + 1 ≤ k0 + k1) (ha : a < 2 ^ A) : False := by
  rw [directOK_iff] at h
  obtain ⟨h1, h2⟩ := h
  have hJ : D * L2 = 2 ^ (B + 1 - k0 + l) := by rw [hD, hL2, Nat.pow_add]
  rw [hJ, hW2] at h1
  rw [hJ, hA2, hL2] at h2
  have hjW : B + 1 - k0 + l ≤ W := (Nat.pow_le_pow_iff_right (by decide)).mp h1
  have hm := mod_eq_of_rel hc hrel (j := B + 1 - k0 + l) (by omega) hjW (by omega)
  rw [← hm] at h2
  have : a % 2 ^ (B + 1 - k0 + l) ≤ a := Nat.mod_le _ _
  omega

/-- A set bit `z ≥ A` of `c` below `ℓ` refutes the pair. -/

theorem bit_false {k0 a l k1 a' c W A z : Nat} (hc : 3 ^ k0 * c % 2 ^ W = 1)
    (hrel : 3 ^ k0 * a + 2 ^ l = 2 ^ (l + k1) * a' + 1) (hcW : c < 2 ^ W)
    (hz : c.testBit z = true) (hAz : A ≤ z) (hzl : z < l) (ha : a < 2 ^ A) : False := by
  have hzW : z < W := by
    rcases Nat.lt_or_ge z W with h | h
    · exact h
    · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hcW (Nat.pow_le_pow_right (by decide) h))] at hz
      exact absurd hz (by decide)
  have hm := mod_eq_of_rel_low hc hrel (j := z + 1) hzl hzW
  have h1 : (a % 2 ^ (z + 1)).testBit z = (c % 2 ^ (z + 1)).testBit z := by rw [hm]
  rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow, hz] at h1
  have h2 : a.testBit z = false :=
    Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le ha (Nat.pow_le_pow_right (by decide) hAz))
  simp [h2] at h1

theorem win_of_split {c s g A E : Nat} (hm : c % 2 ^ (A + E) = (s + g * 2 ^ A) % 2 ^ (A + E))
    (hs : s < 2 ^ A) : (c >>> A) % 2 ^ E = g % 2 ^ E := by
  rw [Nat.shiftRight_eq_div_pow, ← Nat.mod_mul_right_div_self, ← Nat.pow_add, hm, Nat.pow_add,
    Nat.mod_mul_right_div_self, Nat.add_mul_div_right _ _ (Nat.two_pow_pos _),
    Nat.div_eq_of_lt hs, Nat.zero_add]

theorem mul_split {c h l A : Nat} (hlA : l ≤ A) (hh : h = c >>> (A - l)) :
    c * 2 ^ l = h * 2 ^ A + c % 2 ^ (A - l) * 2 ^ l := by
  have hdiv : c = 2 ^ (A - l) * h + c % 2 ^ (A - l) := by
    rw [hh, Nat.shiftRight_eq_div_pow]; exact (Nat.div_add_mod c _).symm
  have hpow : 2 ^ (A - l) * 2 ^ l = 2 ^ A := by rw [← Nat.pow_add, Nat.sub_add_cancel hlA]
  conv => lhs; rw [hdiv]
  rw [Nat.add_mul, ← hpow, Nat.mul_comm (2 ^ (A - l)) h, Nat.mul_assoc]

/-- If `c (1 − 2^ℓ) ≡ a < 2^A (mod 2^{A+E})`, the `E`-bit window of `c` at `A − ℓ` equals the window
at `A`, or is one less (a borrow). -/

theorem window_borrow {k0 a l k1 a' c W A E : Nat} (hc : 3 ^ k0 * c % 2 ^ W = 1)
    (hrel : 3 ^ k0 * a + 2 ^ l = 2 ^ (l + k1) * a' + 1) (hlA : l ≤ A) (hjW : A + E ≤ W)
    (hj : A + E ≤ l + k1) (ha : a < 2 ^ A) :
    (c >>> (A - l)) % 2 ^ E = (c >>> A) % 2 ^ E ∨
      ((c >>> (A - l)) % 2 ^ E + 1) % 2 ^ E = (c >>> A) % 2 ^ E := by
  have hd := dvd_of_rel hc hrel hjW hj
  have hm : c % 2 ^ (A + E) = (a + c * 2 ^ l) % 2 ^ (A + E) := by
    apply nat_mod_eq_of_int_dvd
    have e : (c : Int) - ((a + c * 2 ^ l : Nat) : Int) =
        -((a : Int) - (c : Int) * (1 - ((2 ^ l : Nat) : Int))) := by
      simp only [Int.natCast_add, Int.natCast_mul]
      grind
    rw [e]
    exact Int.dvd_neg.mpr hd
  obtain ⟨h, hh⟩ : ∃ h, h = c >>> (A - l) := ⟨_, rfl⟩
  have hsp := mul_split hlA hh
  have hpow : 2 ^ (A - l) * 2 ^ l = 2 ^ A := by rw [← Nat.pow_add, Nat.sub_add_cancel hlA]
  have hr : c % 2 ^ (A - l) * 2 ^ l < 2 ^ A := by
    rw [← hpow]
    exact Nat.mul_lt_mul_of_pos_right (Nat.mod_lt _ (Nat.two_pow_pos _)) (Nat.two_pow_pos _)
  obtain ⟨u, hu⟩ : ∃ u, u = a + c % 2 ^ (A - l) * 2 ^ l := ⟨_, rfl⟩
  have hu2 : u < 2 * 2 ^ A := by omega
  have hdm := Nat.div_add_mod u (2 ^ A)
  have he : u / 2 ^ A < 2 := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]; omega
  have hsum : a + c * 2 ^ l = u % 2 ^ A + (h + u / 2 ^ A) * 2 ^ A := by
    rw [hsp, Nat.add_mul]
    have : 2 ^ A * (u / 2 ^ A) = u / 2 ^ A * 2 ^ A := Nat.mul_comm _ _
    omega
  rw [hsum] at hm
  have hwin := win_of_split hm (Nat.mod_lt _ (Nat.two_pow_pos _))
  rw [← hh, hwin]
  rcases Nat.lt_or_ge (u / 2 ^ A) 1 with h0 | h1
  · left
    rw [Nat.lt_one_iff.mp h0, Nat.add_zero]
  · right
    rw [Nat.le_antisymm (Nat.lt_succ_iff.mp he) h1]
    exact Nat.mod_add_mod h (2 ^ E) 1

theorem matchMask_zero (M X P : Nat) : matchMask M 0 X P = M := rfl

theorem matchMask_succ (M E X P : Nat) : matchMask M (E + 1) X P =
    Nat.land (Nat.xor X (cond (Nat.beq (Nat.land P 1) 1) 0 M))
      (matchMask M E (Nat.shiftRight X 1) (Nat.shiftRight P 1)) := rfl

/-- **The bit-parallel search.** -/
theorem testBit_matchMask {L M : Nat} (hM : M = 2 ^ L - 1) : ∀ (E X P i : Nat),
    (matchMask M E X P).testBit i = true ↔
      i < L ∧ ∀ b < E, X.testBit (i + b) = P.testBit b := by
  subst hM
  intro E
  induction E with
  | zero =>
    intro X P i
    rw [matchMask_zero, Nat.testBit_two_pow_sub_one]
    simp
  | succ E ih =>
    intro X P i
    rw [matchMask_succ, Nat.land_eq, Nat.testBit_and, Bool.and_eq_true, Nat.xor_eq,
      Nat.testBit_xor]
    have ih' := ih (Nat.shiftRight X 1) (Nat.shiftRight P 1) i
    rw [ih']
    have hc : (cond (Nat.beq (Nat.land P 1) 1) 0 (2 ^ L - 1)).testBit i =
        (!P.testBit 0 && decide (i < L)) := by
      rw [Nat.land_eq, Nat.and_one_is_mod, Nat.testBit_zero]
      rcases Nat.mod_two_eq_zero_or_one P with h | h
      · rw [h]; simp [Nat.testBit_two_pow_sub_one]
      · rw [h]; simp
    rw [hc]
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨h2, fun b hb => ?_⟩
      rcases b with _ | b
      · simp only [Nat.add_zero]
        cases hx : X.testBit i <;> cases hp : P.testBit 0 <;> simp_all
      · have := h3 b (by omega)
        simp only [shiftRight_eq', Nat.testBit_shiftRight] at this
        rw [show i + (b + 1) = 1 + (i + b) by omega, this, Nat.add_comm 1 b]
    · rintro ⟨h1, h2⟩
      refine ⟨?_, h1, fun b hb => ?_⟩
      · have := h2 0 (by omega)
        simp only [Nat.add_zero] at this
        rw [this]
        cases P.testBit 0 <;> simp [h1]
      · simp only [shiftRight_eq', Nat.testBit_shiftRight]
        have := h2 (b + 1) (by omega)
        rw [show 1 + (i + b) = i + (b + 1) by omega, this, Nat.add_comm 1 b]

theorem directRange_zero (D A2 W2 c L2 : Nat) : directRange D A2 W2 c 0 L2 = true := rfl

theorem directRange_succ (D A2 W2 c cnt L2 : Nat) : directRange D A2 W2 c (cnt + 1) L2 =
    (directOK D A2 W2 c L2 && directRange D A2 W2 c cnt (Nat.mul 2 L2)) := rfl

/-- `directRange` ran the direct test at `2^q L2`, `q < cnt`. -/
theorem directRange_sound {D A2 W2 c : Nat} : ∀ (cnt L2 : Nat),
    directRange D A2 W2 c cnt L2 = true → ∀ q < cnt, directOK D A2 W2 c (2 ^ q * L2) = true := by
  intro cnt
  induction cnt with
  | zero => intro L2 _ q hq; omega
  | succ cnt ih =>
    intro L2 h q hq
    rw [directRange_succ, Bool.and_eq_true] at h
    rcases q with _ | q
    · rw [Nat.pow_zero, Nat.one_mul]; exact h.1
    · have := ih _ h.2 q (by omega)
      rwa [Nat.mul_eq, ← Nat.mul_assoc, ← Nat.pow_succ] at this

theorem fallbackOK_zero (D A2 W2 c mm : Nat) : fallbackOK D A2 W2 c 0 mm = Nat.beq mm 0 := rfl

theorem fallbackOK_succ (D A2 W2 c f mm : Nat) : fallbackOK D A2 W2 c (f + 1) mm =
    cond (Nat.beq mm 0) true
      (let Pt := Nat.land mm (Nat.xor mm (Nat.sub mm 1));
        Nat.beq (Nat.land Pt (Nat.sub Pt 1)) 0 && Nat.ble 1 Pt && Nat.beq (Nat.land mm Pt) Pt &&
          directOK D A2 W2 c (Nat.div A2 Pt) && fallbackOK D A2 W2 c f (Nat.xor mm Pt)) := rfl

/-- Every set bit of `mm` got the direct test. -/
theorem fallbackOK_sound {D A2 W2 c : Nat} : ∀ (f mm : Nat),
    fallbackOK D A2 W2 c f mm = true →
      ∀ i, mm.testBit i = true → directOK D A2 W2 c (A2 / 2 ^ i) = true := by
  intro f
  induction f with
  | zero =>
    intro mm h i hi
    rw [fallbackOK_zero, Nat.beq_eq] at h
    subst h
    simp at hi
  | succ f ih =>
    intro mm h i hi
    rw [fallbackOK_succ] at h
    by_cases h0 : mm = 0
    · subst h0; simp at hi
    · have hb : Nat.beq mm 0 = false := by
        cases hq : Nat.beq mm 0
        · rfl
        · exact absurd (Nat.eq_of_beq_eq_true hq) h0
      rw [hb] at h
      simp only [Bool.cond_false, Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq] at h
      obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
      generalize hPt : Nat.land mm (Nat.xor mm (Nat.sub mm 1)) = Pt at h1 h2 h3 h4 h5
      have hpow : Pt.isPowerOfTwo :=
        (Nat.and_sub_one_eq_zero_iff_isPowerOfTwo (by omega)).mp h1
      obtain ⟨t, ht⟩ := hpow
      subst ht
      have hmt : mm.testBit t = true := by
        have e := congrArg (fun x => Nat.testBit x t) h3
        simp only [Nat.land_eq, Nat.testBit_and, Nat.testBit_two_pow_self, Bool.and_true] at e
        exact e
      by_cases hit : i = t
      · subst hit; rwa [div_eq'] at h4
      · apply ih _ h5 i
        rw [Nat.xor_eq, Nat.testBit_xor, hi, Nat.testBit_two_pow]
        simp [Ne.symm hit]

/-- A window of `X` equals a pattern iff its bits do. -/

theorem window_eq_iff (X Q i E : Nat) :
    (X >>> i) % 2 ^ E = Q % 2 ^ E ↔ ∀ b < E, X.testBit (i + b) = Q.testBit b := by
  constructor
  · intro h b hb
    have e := congrArg (fun x => Nat.testBit x b) h
    simp only [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight] at e
    simpa [hb] using e
  · intro h
    apply Nat.eq_of_testBit_eq
    intro b
    simp only [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
    by_cases hb : b < E
    · simp [hb, h b hb]
    · simp [hb]

/-- `a < 2^A` with `A = N − k₀` (or `1` when `k₀ = N`). -/

theorem a_lt {N k0 a : Nat} (ha : a % 2 = 1) (hN : 2 ^ k0 * a ≤ 2 ^ N) (hkN : k0 ≤ N) :
    a < 2 ^ (cond (Nat.blt k0 N) (Nat.sub N k0) 1) := by
  have hpow : 2 ^ N = 2 ^ k0 * 2 ^ (N - k0) := by rw [← Nat.pow_add, Nat.add_sub_cancel' hkN]
  rw [hpow] at hN
  have hle : a ≤ 2 ^ (N - k0) := Nat.le_of_mul_le_mul_left hN (Nat.two_pow_pos _)
  rcases Nat.lt_or_ge k0 N with hlt | hge
  · have hb : Nat.blt k0 N = true := by simp [hlt]
    rw [hb]
    simp only [Bool.cond_true, Nat.sub_eq]
    have hev : 2 ^ (N - k0) % 2 = 0 := by
      obtain ⟨m, hm⟩ : ∃ m, N - k0 = m + 1 := ⟨N - k0 - 1, by omega⟩
      rw [hm, Nat.pow_succ, Nat.mul_mod_left]
    have : a ≠ 2 ^ (N - k0) := fun h => by rw [h] at ha; omega
    omega
  · have hb : Nat.blt k0 N = false := by
      rw [Bool.eq_false_iff]; intro h; rw [Nat.blt_eq] at h; omega
    rw [hb]
    simp only [Bool.cond_false]
    rw [show N - k0 = 0 by omega, Nat.pow_zero] at hle
    simp; omega

/-- If `(w + 1) mod 2^E = P` and `s` is the lowest set bit of `P`, then `w` and `P` agree above `s`. -/

theorem high_bits_of_pred {w P s E : Nat} (hw : w < 2 ^ E) (hP : (w + 1) % 2 ^ E = P)
    (hs : P.testBit s = true) (hs0 : P % 2 ^ s = 0) : w >>> (s + 1) = P >>> (s + 1) := by
  have hP1 : P = w + 1 := by
    rcases Nat.lt_or_ge (w + 1) (2 ^ E) with h | h
    · rw [Nat.mod_eq_of_lt h] at hP; exact hP.symm
    · have : w + 1 = 2 ^ E := by omega
      rw [this, Nat.mod_self] at hP
      subst hP
      simp at hs
  subst hP1
  rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
  -- bit `s` of `w + 1` is set, so `(w + 1) mod 2^{s+1} ≥ 1`
  have hbit : ((w + 1) % 2 ^ (s + 1)).testBit s = true := by
    rw [Nat.testBit_mod_two_pow]; simp [hs]
  have hpos : 1 ≤ (w + 1) % 2 ^ (s + 1) := by
    rcases Nat.eq_zero_or_pos ((w + 1) % 2 ^ (s + 1)) with h0 | h0
    · rw [h0] at hbit; simp at hbit
    · exact h0
  have hd := Nat.div_add_mod (w + 1) (2 ^ (s + 1))
  have hlt := Nat.mod_lt (w + 1) (Nat.two_pow_pos (s + 1))
  have e : w = 2 ^ (s + 1) * ((w + 1) / 2 ^ (s + 1)) + ((w + 1) % 2 ^ (s + 1) - 1) := by omega
  have hr : (w + 1) % 2 ^ (s + 1) - 1 < 2 ^ (s + 1) := by omega
  calc w / 2 ^ (s + 1)
      = (2 ^ (s + 1) * ((w + 1) / 2 ^ (s + 1)) + ((w + 1) % 2 ^ (s + 1) - 1)) / 2 ^ (s + 1) := by
        rw [← e]
    _ = (w + 1) / 2 ^ (s + 1) := by
        rw [Nat.mul_add_div (Nat.two_pow_pos _), Nat.div_eq_of_lt hr, Nat.add_zero]

theorem testBit_window {c i E j : Nat} (hj : j < E) :
    ((c >>> i) % 2 ^ E).testBit j = c.testBit (i + j) := by
  rw [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]; simp [hj]

theorem testBit_xor_one_mask {L i : Nat} (h1 : 1 ≤ i) (hL : i < L) :
    (Nat.xor (Nat.sub (Nat.pow 2 L) 1) 1).testBit i = true := by
  rw [Nat.xor_eq, Nat.testBit_xor, Nat.sub_eq, pow_eq', Nat.testBit_two_pow_sub_one]
  have : (1 : Nat).testBit i = false := Nat.testBit_lt_two_pow
    (Nat.lt_of_lt_of_le (by decide : 1 < 2 ^ 1) (Nat.pow_le_pow_right (by decide) h1))
  simp [this, hL]

theorem patternCore_zero_false {D A2 W2 c E1 L M X P s : Nat}
    (h : patternCore D A2 W2 c E1 L M X P s = true) (hs : E1 ≤ s) :
    P = 0 ∧ fallbackOK D A2 W2 c L
      (Nat.land (Nat.lor (matchMask M E1 X 0) (matchMask M E1 X (Nat.sub (Nat.pow 2 E1) 1)))
        (Nat.xor M 1)) = true := by
  have hb : Nat.blt s E1 = false := by
    rw [Bool.eq_false_iff]; intro h'; rw [Nat.blt_eq] at h'; omega
  simp only [patternCore, hb, Bool.cond_false, Bool.and_eq_true, Nat.beq_eq] at h
  exact h

theorem patternCore_lt {D A2 W2 c E1 L M X P s : Nat}
    (h : patternCore D A2 W2 c E1 L M X P s = true) (hs : s < E1) :
    P.testBit s = true ∧ P % 2 ^ s = 0 ∧ fallbackOK D A2 W2 c L
        (Nat.land (matchMask M (Nat.sub E1 (Nat.add s 1)) (Nat.shiftRight X (Nat.add s 1))
          (Nat.shiftRight P (Nat.add s 1))) (Nat.xor M 1)) = true := by
  have hb : Nat.blt s E1 = true := by rw [Nat.blt_eq]; exact hs
  simp only [patternCore, hb, Bool.cond_true, Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨?_, by rw [mod_eq', pow_eq'] at h2; exact h2, h3⟩
  rw [Nat.land_eq, shiftRight_eq', Nat.and_one_is_mod] at h1
  rw [Nat.testBit_eq_decide_div_mod_eq, ← Nat.shiftRight_eq_div_pow]
  simp [h1]

/-- **The pattern test.** If the window of `c` at `i ∈ [1, L − 1]` (`i ≤ A`) is `P` or `P − 1`, the
direct test at `2^A / 2^i` has been run and passed. -/
theorem patternCore_sound {D A2 W2 c E1 L P s A i : Nat}
    (h : patternCore D A2 W2 c E1 L (2 ^ L - 1) (c % 2 ^ (A + E1)) P s = true)
    (hi1 : 1 ≤ i) (hiL : i < L) (hiA : i ≤ A)
    (hw : (c >>> i) % 2 ^ E1 = P ∨ ((c >>> i) % 2 ^ E1 + 1) % 2 ^ E1 = P) :
    directOK D A2 W2 c (A2 / 2 ^ i) = true := by
  have hmask : ((2 ^ L - 1) ^^^ 1).testBit i = true := testBit_xor_one_mask hi1 hiL
  have hX : ∀ j, j < E1 → (c % 2 ^ (A + E1)).testBit (i + j) = c.testBit (i + j) := by
    intro j hj
    rw [Nat.testBit_mod_two_pow]
    have : i + j < A + E1 := by omega
    simp [this]
  have hwlt : (c >>> i) % 2 ^ E1 < 2 ^ E1 := Nat.mod_lt _ (Nat.two_pow_pos _)
  rcases Nat.lt_or_ge s E1 with hs | hs
  · obtain ⟨hPs, hPs0, hf⟩ := patternCore_lt h hs
    simp only [Nat.land_eq, Nat.xor_eq, Nat.sub_eq, Nat.add_eq, shiftRight_eq'] at hf
    apply fallbackOK_sound _ _ hf i
    rw [Nat.testBit_and, hmask, Bool.and_true, testBit_matchMask (L := L) rfl]
    refine ⟨hiL, fun b hb => ?_⟩
    rw [Nat.testBit_shiftRight, Nat.testBit_shiftRight,
      show s + 1 + (i + b) = i + (s + 1 + b) by omega, hX _ (by omega)]
    have hb' : s + 1 + b < E1 := by omega
    rw [← testBit_window (c := c) (i := i) hb']
    rcases hw with hw | hw
    · rw [hw]
    · have hh := high_bits_of_pred hwlt hw hPs hPs0
      have e1 := congrArg (fun x => Nat.testBit x b) hh
      simp only [Nat.testBit_shiftRight] at e1
      exact e1
  · obtain ⟨hP0, hf⟩ := patternCore_zero_false h hs
    subst hP0
    simp only [Nat.land_eq, Nat.lor_eq, Nat.xor_eq, Nat.sub_eq, pow_eq'] at hf
    apply fallbackOK_sound _ _ hf i
    rw [Nat.testBit_and, hmask, Bool.and_true, Nat.testBit_or, Bool.or_eq_true,
      testBit_matchMask (L := L) rfl, testBit_matchMask (L := L) rfl]
    rcases hw with hw | hw
    · left
      refine ⟨hiL, fun b hb => ?_⟩
      rw [hX b hb, ← testBit_window (c := c) (i := i) hb, hw]
    · right
      refine ⟨hiL, fun b hb => ?_⟩
      have hw1 : (c >>> i) % 2 ^ E1 = 2 ^ E1 - 1 := by
        rcases Nat.lt_or_ge ((c >>> i) % 2 ^ E1 + 1) (2 ^ E1) with hh | hh
        · rw [Nat.mod_eq_of_lt hh] at hw; omega
        · omega
      rw [hX b hb, ← testBit_window (c := c) (i := i) hb, hw1]

theorem kCore_facts {B E1 W k0 c A D A2 W2 y t lmin : Nat}
    (h : kCore B E1 W k0 c A D A2 W2 y t lmin = true) :
    k0 ≤ B + 1 ∧ (y >>> t) % 2 = 1 ∧ directRange D A2 W2 c (t + 1) A2 = true ∧
      directRange D A2 W2 c (min A lmin - 1) 2 = true ∧
      (lmin < A → A + E1 ≤ W ∧ patternOK D A2 W2 c A E1 lmin = true) := by
  simp only [kCore, Bool.and_eq_true, Nat.ble_eq, Nat.beq_eq, Nat.add_eq, Nat.sub_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨h1, ?_, h3, ?_, ?_⟩
  · rw [Nat.land_eq, shiftRight_eq', Nat.and_one_is_mod] at h2; exact h2
  · have : Nat.min A lmin = min A lmin := rfl
    rw [this] at h4; exact h4
  · intro hlt
    have hb : Nat.ble A lmin = false := by
      rw [Bool.eq_false_iff]; intro h'; rw [Nat.ble_eq] at h'; omega
    rw [hb, Bool.cond_false, Bool.and_eq_true, Nat.ble_eq] at h5
    exact h5

/-- **Soundness of the test for one `k₀`**: `k₀ + k₁ ≤ B` for every configuration. -/
theorem kCore_sound {N B E1 W k0 c A D A2 W2 y t lmin : Nat}
    (h : kCore B E1 W k0 c A D A2 W2 y t lmin = true)
    (hA : A = cond (Nat.blt k0 N) (Nat.sub N k0) 1) (hD : D = 2 ^ (B + 1 - k0))
    (hA2 : A2 = 2 ^ A) (hW2 : W2 = 2 ^ W) (hy : y = c >>> A)
    (hlmin : lmin = max 1 (N + E1 - (B + 1)))
    (hc : 3 ^ k0 * c % 2 ^ W = 1) (hcW : c < 2 ^ W) (hkN : k0 ≤ N) :
    PairCond N B k0 := by
  intro a l k1 a' ha hN hl hrel
  apply Nat.le_of_not_lt
  intro hbad
  obtain ⟨hkB, hbit, hdr1, hdr2, hpat⟩ := kCore_facts h
  have haA : a < 2 ^ A := by rw [hA]; exact a_lt ha hN hkN
  have hA1 : 1 ≤ A := by
    rw [hA]
    rcases Nat.lt_or_ge k0 N with hlt | hge
    · have hb : Nat.blt k0 N = true := by rw [Nat.blt_eq]; exact hlt
      rw [hb, Bool.cond_true, Nat.sub_eq]; omega
    · have hb : Nat.blt k0 N = false := by
        rw [Bool.eq_false_iff]; intro h'; rw [Nat.blt_eq] at h'; omega
      rw [hb, Bool.cond_false]; exact Nat.le_refl 1
  -- the set bit `A + t` of `c`
  have hz : c.testBit (A + t) = true := by
    have h1 : (c >>> A).testBit t = true := by
      rw [Nat.testBit_eq_decide_div_mod_eq, ← Nat.shiftRight_eq_div_pow, ← hy]; simp [hbit]
    rwa [Nat.testBit_shiftRight] at h1
  have hbad' : B + 1 ≤ k0 + k1 := hbad
  rcases Nat.lt_or_ge (A + t) l with hlt | hge
  · exact bit_false hc hrel hcW hz (Nat.le_add_right A t) hlt haA
  rcases Nat.lt_or_ge l A with hlA | hAl
  · -- `ℓ < A`
    rcases Nat.lt_or_ge l lmin with hll | hll
    · have hq := directRange_sound _ _ hdr2 (l - 1) (by omega)
      have e : 2 ^ (l - 1) * 2 = 2 ^ l := by
        rw [← Nat.pow_succ]; congr 1; omega
      rw [e] at hq
      exact directOK_false hq hc hrel hD hA2 hW2 rfl hbad' haA
    · obtain ⟨hAE, hp⟩ := hpat (by omega)
      have hkN' : k0 < N := by
        rcases Nat.lt_or_ge k0 N with h' | h'
        · exact h'
        · have hb : Nat.blt k0 N = false := by
            rw [Bool.eq_false_iff]; intro h''; rw [Nat.blt_eq] at h''; omega
          rw [hA, hb, Bool.cond_false] at hlA; omega
      have hAv : A = N - k0 := by
        have hb : Nat.blt k0 N = true := by rw [Nat.blt_eq]; exact hkN'
        rw [hA, hb, Bool.cond_true, Nat.sub_eq]
      have hwb := window_borrow (E := E1) hc hrel (Nat.le_of_lt hlA) hAE (by omega) haA
      simp only [patternOK, Nat.add_eq, Nat.sub_eq, pow_eq', mod_eq', shiftRight_eq'] at hp
      have hd := patternCore_sound (A := A) (i := A - l) hp (by omega) (by omega)
        (Nat.sub_le A l) hwb
      have e : A2 / 2 ^ (A - l) = 2 ^ l := by
        rw [hA2, Nat.pow_div (Nat.sub_le A l) (by decide), Nat.sub_sub_self (Nat.le_of_lt hlA)]
      rw [e] at hd
      exact directOK_false hd hc hrel hD hA2 hW2 rfl hbad' haA
  · -- `A ≤ ℓ ≤ A + t`
    have hq := directRange_sound _ _ hdr1 (l - A) (by omega)
    have e : 2 ^ (l - A) * A2 = 2 ^ l := by rw [hA2, ← Nat.pow_add, Nat.sub_add_cancel hAl]
    rw [e] at hq
    exact directOK_false hq hc hrel hD hA2 hW2 rfl hbad' haA

/-- **Soundness of `kOK`.** -/
theorem kOK_sound {N B E1 W k0 c : Nat} (h : kOK N B E1 W k0 c = true)
    (hc : 3 ^ k0 * c % 2 ^ W = 1) (hcW : c < 2 ^ W) (hkN : k0 ≤ N) : PairCond N B k0 := by
  have h' : kCore B E1 W k0 c (cond (Nat.blt k0 N) (Nat.sub N k0) 1)
      (Nat.pow 2 (Nat.sub (Nat.add B 1) k0)) (Nat.pow 2 (cond (Nat.blt k0 N) (Nat.sub N k0) 1))
      (Nat.pow 2 W) (Nat.shiftRight c (cond (Nat.blt k0 N) (Nat.sub N k0) 1))
      (lowScan (Nat.shiftRight c (cond (Nat.blt k0 N) (Nat.sub N k0) 1)) W 0)
      (Nat.max 1 (Nat.sub (Nat.add N E1) (Nat.add B 1))) = true := h
  exact kCore_sound h' rfl rfl rfl rfl rfl rfl hc hcW hkN

theorem loop_succ (N B E1 W i3 cnt k c : Nat) : loop N B E1 W i3 (cnt + 1) k c =
    (kOK N B E1 W k (Nat.mod (Nat.mul c i3) (Nat.pow 2 W)) &&
      loop N B E1 W i3 cnt (Nat.add k 1) (Nat.mod (Nat.mul c i3) (Nat.pow 2 W))) := rfl

theorem inv_step {k c i3 W : Nat} (hc : 3 ^ (k - 1) * c % 2 ^ W = 1) (hi : 3 * i3 % 2 ^ W = 1)
    (hk : 1 ≤ k) : 3 ^ k * (c * i3 % 2 ^ W) % 2 ^ W = 1 := by
  have hm : 1 < 2 ^ W := by
    have := Nat.mod_lt (3 ^ (k - 1) * c) (Nat.two_pow_pos W); omega
  rw [Nat.mul_mod_mod, show 3 ^ k = 3 ^ (k - 1) * 3 by rw [← Nat.pow_succ]; congr 1; omega,
    show 3 ^ (k - 1) * 3 * (c * i3) = (3 ^ (k - 1) * c) * (3 * i3) by
      rw [Nat.mul_assoc, Nat.mul_assoc, Nat.mul_left_comm 3 c i3],
    Nat.mul_mod, hc, hi, Nat.mul_one, Nat.mod_eq_of_lt hm]

/-- `PairCond` for every `k₀ ∈ [lo, hi)` with `k₀ ≤ N`. -/
def RangeCond (N B lo hi : Nat) : Prop :=
  ∀ k0, lo ≤ k0 → k0 < hi → k0 ≤ N → PairCond N B k0

theorem loop_sound {N B E1 W i3 : Nat} (hi : 3 * i3 % 2 ^ W = 1) : ∀ cnt k c,
    loop N B E1 W i3 cnt k c = true → 3 ^ (k - 1) * c % 2 ^ W = 1 → 1 ≤ k →
      RangeCond N B k (k + cnt) := by
  intro cnt
  induction cnt with
  | zero => intro k c _ _ _ k0 h1 h2; omega
  | succ cnt ih =>
    intro k c h hc hk k0 h1 h2 hkN
    rw [loop_succ, Bool.and_eq_true] at h
    have hc' := inv_step hc hi hk
    rcases Nat.eq_or_lt_of_le h1 with he | hlt
    · subst he
      exact kOK_sound h.1 hc' (Nat.mod_lt _ (Nat.two_pow_pos W)) hkN
    · exact ih (k + 1) _ h.2 (by rw [Nat.add_sub_cancel]; exact hc') (by omega) k0 hlt (by omega) hkN

/-- **Soundness of the chunk checker.** -/
theorem rangeOK_sound {N B E1 W i3 k c0 cnt : Nat} (h : rangeOK N B E1 W i3 k c0 cnt = true) :
    RangeCond N B k (k + cnt) := by
  simp only [rangeOK, Bool.and_eq_true, Nat.ble_eq, Nat.beq_eq] at h
  obtain ⟨⟨⟨hk, hi⟩, hc⟩, hl⟩ := h
  exact loop_sound hi cnt k c0 hl hc hk

theorem RangeCond.trans {N B a b c : Nat} (h1 : RangeCond N B a b) (h2 : RangeCond N B b c) :
    RangeCond N B a c := by
  intro k0 ha hc hkN
  rcases Nat.lt_or_ge k0 b with hb | hb
  · exact h1 k0 ha hb hkN
  · exact h2 k0 hb hc hkN

/-- The two-rise bound for all first rises `1 ≤ k₀ ≤ N`. -/
def AllPairs (N B : Nat) : Prop := ∀ k0, 1 ≤ k0 → k0 ≤ N → PairCond N B k0

theorem allPairs_of_range {N B : Nat} (h : RangeCond N B 1 (N + 1)) : AllPairs N B :=
  fun k0 h1 h2 => h k0 h1 (by omega) h2

/-! ### Two blocks, in integers -/

/-- One block: `2 · 2^k (n' + 1) ≤ 3^k (n + 1) + 2^k`. -/
theorem one_step_core {n n' k a l : Nat} (hn : n + 1 = 2 ^ k * a) (h1 : 3 ^ k * a = 2 ^ l * n' + 1)
    (hl : 1 ≤ l) : 2 * 2 ^ k * (n' + 1) ≤ 3 ^ k * (n + 1) + 2 ^ k := by
  have h2l : 2 ≤ 2 ^ l := by
    have := Nat.pow_le_pow_right (show 0 < 2 by decide) hl
    simpa using this
  have hA : 2 * n' + 1 ≤ 3 ^ k * a := by
    have : 2 * n' ≤ 2 ^ l * n' := Nat.mul_le_mul_right n' h2l
    omega
  -- `2 · 2^k (n' + 1) = 2^k (2 n' + 1) + 2^k ≤ 2^k 3^k a + 2^k = 3^k (n + 1) + 2^k`
  have e1 : 2 * 2 ^ k * (n' + 1) = 2 ^ k * (2 * n' + 1) + 2 ^ k := by grind
  have e2 : 3 ^ k * (n + 1) = 2 ^ k * (3 ^ k * a) := by
    rw [hn, Nat.mul_left_comm]
  rw [e1, e2]
  exact Nat.add_le_add_right (Nat.mul_le_mul_left _ hA) _

/-- Two blocks: `4 · 2^{k+k'} (n'' + 1) ≤ 3^{k+k'} (n + 4)`. -/
theorem two_step_core {n n' n'' k k' a a' l l' : Nat} (hn : n + 1 = 2 ^ k * a)
    (h1 : 3 ^ k * a = 2 ^ l * n' + 1) (hl : 1 ≤ l) (hn' : n' + 1 = 2 ^ k' * a')
    (h2 : 3 ^ k' * a' = 2 ^ l' * n'' + 1) (hl' : 1 ≤ l') :
    4 * 2 ^ (k + k') * (n'' + 1) ≤ 3 ^ (k + k') * (n + 4) := by
  have s1 := one_step_core hn h1 hl
  have s2 := one_step_core hn' h2 hl'
  have hk : 2 ^ k ≤ 3 ^ k := Nat.pow_le_pow_left (by decide) k
  have hk' : 2 ^ k' ≤ 3 ^ k' := Nat.pow_le_pow_left (by decide) k'
  -- `4 · 2^k 2^{k'} (n''+1) = 2^k · 2 · (2 · 2^{k'} (n''+1)) ≤ 2^k · 2 · (3^{k'} (n'+1) + 2^{k'})`
  have t1 : 4 * 2 ^ (k + k') * (n'' + 1) = 2 * 2 ^ k * (2 * 2 ^ k' * (n'' + 1)) := by
    rw [Nat.pow_add]; grind
  have t2 : 2 * 2 ^ k * (3 ^ k' * (n' + 1) + 2 ^ k') =
      3 ^ k' * (2 * 2 ^ k * (n' + 1)) + 2 * 2 ^ k * 2 ^ k' := by
    grind
  have t3 : 3 ^ k' * (3 ^ k * (n + 1) + 2 ^ k) = 3 ^ (k + k') * (n + 1) + 3 ^ k' * 2 ^ k := by
    rw [Nat.pow_add]; grind
  have b1 : 3 ^ k' * 2 ^ k ≤ 3 ^ (k + k') := by
    rw [Nat.pow_add, Nat.mul_comm (3 ^ k)]
    exact Nat.mul_le_mul_left _ hk
  have b2 : 2 * 2 ^ k * 2 ^ k' ≤ 2 * 3 ^ (k + k') := by
    rw [Nat.pow_add, Nat.mul_assoc]
    exact Nat.mul_le_mul_left _ (Nat.mul_le_mul hk hk')
  calc 4 * 2 ^ (k + k') * (n'' + 1) = 2 * 2 ^ k * (2 * 2 ^ k' * (n'' + 1)) := t1
    _ ≤ 2 * 2 ^ k * (3 ^ k' * (n' + 1) + 2 ^ k') := Nat.mul_le_mul_left _ s2
    _ = 3 ^ k' * (2 * 2 ^ k * (n' + 1)) + 2 * 2 ^ k * 2 ^ k' := t2
    _ ≤ 3 ^ k' * (3 ^ k * (n + 1) + 2 ^ k) + 2 * 2 ^ k * 2 ^ k' :=
        Nat.add_le_add_right (Nat.mul_le_mul_left _ s1) _
    _ = 3 ^ (k + k') * (n + 1) + 3 ^ k' * 2 ^ k + 2 * 2 ^ k * 2 ^ k' := by rw [t3]
    _ ≤ 3 ^ (k + k') * (n + 1) + 3 ^ (k + k') + 2 * 3 ^ (k + k') :=
        Nat.add_le_add (Nat.add_le_add_left b1 _) b2
    _ = 3 ^ (k + k') * (n + 4) := by
        grind

end Collatz.TwoRise
