import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic

/-!
# Farey certificates for denominator bounds (Eliahou 1993, Lemma 3.1; Hercher 2023, Lemma 22)

Two fractions `a/b < c/d` with `b, d > 0` are *Farey neighbours* when `c b − a d = 1`. Every rational
strictly between them has denominator at least `b + d`: writing the rational as `p/q` with `q > 0`,
the integers `u = p b − a q` and `v = c q − d p` are positive, and

  `q = q (c b − a d) = u d + v b ≥ d + b`.

This is Lemma 3.1 of Eliahou (Discrete Math. 118 (1993) 45–56) and the mechanism behind Lemma 22 of
Hercher (J. Integer Seq. 26 (2023), Art. 23.3.5): the fraction of smallest denominator in an open
interval `(α, β)` is the mediant `(a+c)/(b+d)` of the Farey neighbours `a/b ≤ α < β ≤ c/d` that are
adjacent in the Stern–Brocot tree, and the bound `b + d` is all that the bootstrap of Hercher's
Theorem 23 uses.

* `farey_den_bound`: the integer core, in cross-multiplied form.
* `denom_ge_of_between`: `a/b < x < c/d` implies `b + d ≤ x.den` for `x : ℚ`.
* `denom_ge_of_certificate`: the certificate form used in `HercherBootstrap.lean`; the endpoints are
  replaced by any rationals `α, β` with `a/b ≤ α` and `β ≤ c/d`, and every rational in `(α, β)` has
  denominator `≥ b + d`.
* `farey_den_bound_div`: the same for a fraction `N/K` of naturals, concluding `b + d ≤ K` directly
  (`K` is a multiple of the reduced denominator, so no reduction is needed).
* `mediant_between`: the mediant lies strictly between the neighbours, so the bound is attained.
-/

namespace Collatz

/-- Integer core of the Farey bound: if `c b − a d = 1` with `b, d > 0`, and `a/b < N/K < c/d` in
cross-multiplied form, then `b + d ≤ K`. -/
theorem farey_den_bound {a b c d N K : ℤ} (hb : 0 < b) (hd : 0 < d) (hF : c * b - a * d = 1)
    (h1 : a * K < N * b) (h2 : N * d < c * K) : b + d ≤ K := by
  have e1 : 1 ≤ N * b - a * K := by omega
  have e2 : 1 ≤ c * K - N * d := by omega
  have hK : K = (N * b - a * K) * d + (c * K - N * d) * b := by
    linear_combination (-K) * hF
  nlinarith [mul_le_mul_of_nonneg_right e1 hd.le, mul_le_mul_of_nonneg_right e2 hb.le]

/-- Cross-multiplication: `a/b < p/q` with `b, q > 0` gives `a q < p b` in `ℤ`. -/
theorem div_lt_div_cross {a p : ℤ} {b q : ℕ} (hb : 0 < b) (hq : 0 < q)
    (h : (a : ℚ) / b < (p : ℚ) / q) : a * q < p * b := by
  have hb' : (0 : ℚ) < b := by exact_mod_cast hb
  have hq' : (0 : ℚ) < q := by exact_mod_cast hq
  rw [div_lt_iff₀ hb', div_mul_eq_mul_div, lt_div_iff₀ hq'] at h
  exact_mod_cast h

/-- **Farey bound.** Every rational strictly between the Farey neighbours `a/b < c/d`
(`c b − a d = 1`, `b, d > 0`) has denominator at least `b + d`. -/
theorem denom_ge_of_between {a c : ℤ} {b d : ℕ} (hb : 0 < b) (hd : 0 < d)
    (hF : c * b - a * d = 1) {x : ℚ} (h1 : (a : ℚ) / b < x) (h2 : x < (c : ℚ) / d) :
    b + d ≤ x.den := by
  have hq : 0 < x.den := x.pos
  have hx : ((x.num : ℚ) / (x.den : ℚ)) = x := Rat.num_div_den x
  rw [← hx] at h1 h2
  have h1' := div_lt_div_cross hb hq h1
  have h2' := div_lt_div_cross hq hd h2
  have := farey_den_bound (by exact_mod_cast hb) (by exact_mod_cast hd) hF h1' h2'
  exact_mod_cast this

/-- **Certificate form.** If `a/b ≤ α < β ≤ c/d` with `a/b, c/d` Farey neighbours, every rational in
the open interval `(α, β)` has denominator at least `b + d`. -/
theorem denom_ge_of_certificate {a c : ℤ} {b d : ℕ} (hb : 0 < b) (hd : 0 < d)
    (hF : c * b - a * d = 1) {α β : ℚ} (hα : (a : ℚ) / b ≤ α) (hβ : β ≤ (c : ℚ) / d)
    {x : ℚ} (h1 : α < x) (h2 : x < β) : b + d ≤ x.den :=
  denom_ge_of_between hb hd hF (lt_of_le_of_lt hα h1) (lt_of_lt_of_le h2 hβ)

/-- The Farey bound for a fraction `N/K` of naturals, `K > 0`: `a/b < N/K < c/d` gives `b + d ≤ K`. -/
theorem farey_den_bound_div {N K : ℕ} (hK : 0 < K) {a c : ℤ} {b d : ℕ} (hb : 0 < b) (hd : 0 < d)
    (hF : c * b - a * d = 1) (h1 : (a : ℚ) / b < (N : ℚ) / K) (h2 : (N : ℚ) / K < (c : ℚ) / d) :
    b + d ≤ K := by
  have hN : ((N : ℤ) : ℚ) = (N : ℚ) := Int.cast_natCast N
  have h1' : (a : ℚ) / b < ((N : ℤ) : ℚ) / K := by rw [hN]; exact h1
  have h2' : ((N : ℤ) : ℚ) / K < (c : ℚ) / d := by rw [hN]; exact h2
  have h1'' := div_lt_div_cross hb hK h1'
  have h2'' := div_lt_div_cross hK hd h2'
  have := farey_den_bound (by exact_mod_cast hb) (by exact_mod_cast hd) hF h1'' h2''
  exact_mod_cast this

/-- The mediant of two Farey neighbours lies strictly between them and has denominator `b + d`,
so the bound of `denom_ge_of_between` is attained. -/
theorem mediant_between {a c : ℤ} {b d : ℕ} (hb : 0 < b) (hd : 0 < d) (hF : c * b - a * d = 1) :
    (a : ℚ) / b < ((a + c : ℤ) : ℚ) / ((b + d : ℕ) : ℚ) ∧
      ((a + c : ℤ) : ℚ) / ((b + d : ℕ) : ℚ) < (c : ℚ) / d := by
  have hb' : (0 : ℚ) < b := by exact_mod_cast hb
  have hd' : (0 : ℚ) < d := by exact_mod_cast hd
  have hbd : (0 : ℚ) < ((b + d : ℕ) : ℚ) := by positivity
  have hF' : (c : ℚ) * b - a * d = 1 := by exact_mod_cast hF
  constructor
  · rw [div_lt_div_iff₀ hb' hbd]
    push_cast
    nlinarith
  · rw [div_lt_div_iff₀ hbd hd']
    push_cast
    nlinarith

end Collatz
