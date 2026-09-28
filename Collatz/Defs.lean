import Mathlib.Logic.Function.Iterate
import Mathlib.Order.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.IntervalCases
import Mathlib.Data.Rat.Defs

/-!
# Definitions (brief, Section 2)

The three maps of the brief, the orbit notions built on them, and the conjecture itself.

* `C` is the Collatz function: `3n + 1` if `n` is odd, `n / 2` if `n` is even.
* `T` is the shortcut map: `(3n + 1) / 2` if `n` is odd, `n / 2` if `n` is even.
* `syr` is Tao's Syracuse map on odd numbers: `(3n + 1) / 2 ^ ν₂(3n + 1)`.

Orbit statistics are stated with `IsFirst`: `IsFirst f p n k` says that `k` is the least
index at which the `f`-orbit of `n` satisfies `p`. With it:

| brief term | Lean |
|---|---|
| delay `D(n) = k` | `IsFirst C (· = 1) n k` |
| total stopping time `σ∞(n) = k` | `IsFirst T (· = 1) n k` |
| stopping time `σ(n) = k` | `IsFirst T (· < n) n k` |
| glide `G(n) = k` | `IsFirst C (· < n) n k` |
| coefficient stopping time `κ(n) = k` | `IsFirstCoeff n k` |
-/

namespace Collatz

/-- The Collatz function `C` (Lagarias's "Collatz function"). -/
def C (n : ℕ) : ℕ := if n % 2 = 0 then n / 2 else 3 * n + 1

/-- The shortcut map `T` (Lagarias's "3x+1 function"). -/
def T (n : ℕ) : ℕ := if n % 2 = 0 then n / 2 else (3 * n + 1) / 2

/-- `stripTwosAux fuel n` divides `n` by 2 while it is even and nonzero, at most `fuel` times. -/
def stripTwosAux : ℕ → ℕ → ℕ
  | 0, n => n
  | fuel + 1, n => if n % 2 = 0 ∧ n ≠ 0 then stripTwosAux fuel (n / 2) else n

/-- The odd part of `n` (with `stripTwos 0 = 0`). Fuel `n` suffices because `2 ^ n > n`. -/
def stripTwos (n : ℕ) : ℕ := stripTwosAux n n

/-- Tao's Syracuse map, intended for odd arguments: `(3n + 1) / 2 ^ ν₂(3n + 1)`. -/
def syr (n : ℕ) : ℕ := stripTwos (3 * n + 1)

/-- `k` is the least index at which the `f`-orbit of `n` satisfies `p`. -/
def IsFirst (f : ℕ → ℕ) (p : ℕ → Prop) (n k : ℕ) : Prop :=
  p (f^[k] n) ∧ ∀ j < k, ¬ p (f^[j] n)

/-- The number of odd values among `f^[0] n, …, f^[k-1] n`. For `C` these are the triplings;
for `T` they are the odd steps `a_k` of the parity vector. -/
def oddCount (f : ℕ → ℕ) (n : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => oddCount f n k + f^[k] n % 2

/-- `k` is the coefficient stopping time `κ(n)`: the least `k ≥ 1` with `3 ^ a_k < 2 ^ k`, where
`a_k = oddCount T n k`. (For `k = 0` the inequality `1 < 1` fails, so `k ≥ 1` is automatic.) -/
def IsFirstCoeff (n k : ℕ) : Prop :=
  3 ^ oddCount T n k < 2 ^ k ∧ ∀ j < k, ¬ 3 ^ oddCount T n j < 2 ^ j

/-- The `f`-orbit of `n` reaches `m`. -/
def Reaches (f : ℕ → ℕ) (n m : ℕ) : Prop := ∃ k, f^[k] n = m

/-- The Collatz conjecture: every positive integer reaches 1 under `C`. -/
def CollatzConjecture : Prop := ∀ n, 0 < n → Reaches C n 1

/-- `m` is the peak of the first `k + 1` terms of the `f`-orbit of `n`, attained at index `i`. -/
def IsPeak (f : ℕ → ℕ) (n k m i : ℕ) : Prop :=
  i ≤ k ∧ f^[i] n = m ∧ ∀ j ≤ k, f^[j] n ≤ m

/-- Roosendaal's residue `Res(n) = 2^E / (3^O n)` for a start with delay `D`, where `O` is the
number of triplings and `E = D - O` the number of halvings. -/
def res (n D : ℕ) : ℚ := 2 ^ (D - oddCount C n D) / (3 ^ oddCount C n D * n)

section basic

theorem C_even {n : ℕ} (h : n % 2 = 0) : C n = n / 2 := by simp [C, h]

theorem C_odd {n : ℕ} (h : n % 2 = 1) : C n = 3 * n + 1 := by simp [C, h]

theorem T_even {n : ℕ} (h : n % 2 = 0) : T n = n / 2 := by simp [T, h]

theorem T_odd {n : ℕ} (h : n % 2 = 1) : T n = (3 * n + 1) / 2 := by simp [T, h]

theorem oddCount_succ (f : ℕ → ℕ) (n k : ℕ) :
    oddCount f n (k + 1) = oddCount f n k + f^[k] n % 2 := rfl

theorem oddCount_le (f : ℕ → ℕ) (n k : ℕ) : oddCount f n k ≤ k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [oddCount_succ]; have := Nat.mod_lt (f^[k] n) two_pos; omega

theorem oddCount_mono (f : ℕ → ℕ) (n : ℕ) : Monotone (oddCount f n) :=
  monotone_nat_of_le_succ fun k => by rw [oddCount_succ]; omega

theorem IsFirst.unique {f : ℕ → ℕ} {p : ℕ → Prop} {n k k' : ℕ}
    (h : IsFirst f p n k) (h' : IsFirst f p n k') : k = k' := by
  rcases lt_trichotomy k k' with hlt | heq | hgt
  · exact absurd h.1 (h'.2 k hlt)
  · exact heq
  · exact absurd h'.1 (h.2 k' hgt)

end basic

end Collatz
