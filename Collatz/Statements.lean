import Collatz.Terras
import Collatz.Steiner
import Collatz.Reductions
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Statements of results that are not proved here (brief, Sections 3, 5 and 10)

Each `def … : Prop` below pins down the exact meaning of a published theorem or open conjecture.
None is proved or assumed: nothing in the library depends on them. They exist so that the
brief's Section 8 misstatements are visibly different propositions, e.g. Tao's theorem is about
logarithmic density and a strict inequality, not "almost all orbits reach 1".
-/

namespace Collatz

open Filter Topology Finset

/-- The minimum of the `C`-orbit of `N`. -/
noncomputable def colMin (N : ℕ) : ℕ := sInf (Set.range fun k => C^[k] N)

open Classical in
/-- `A ⊆ ℕ` has logarithmic density 0: `(1 / log x) Σ_{n ≤ x, n ∈ A} 1/n → 0`. -/
def HasLogDensityZero (A : Set ℕ) : Prop :=
  Tendsto (fun x : ℕ => (∑ n ∈ (range (x + 1)).filter (· ∈ A), (1 : ℝ) / n) / Real.log x)
    atTop (𝓝 0)

open Classical in
/-- `A ⊆ ℕ` has natural density 1. -/
def HasNatDensityOne (A : Set ℕ) : Prop :=
  Tendsto (fun x : ℕ => (((range x).filter (· ∈ A)).card : ℝ) / x) atTop (𝓝 1)

/-- Tao (2019/2022), Theorem 1.3: for every `f → ∞`, `Col_min(N) < f(N)` for almost all `N` in
logarithmic density. Not "almost all orbits reach 1", and not natural density. -/
def TaoTheorem : Prop :=
  ∀ f : ℕ → ℝ, Tendsto f atTop atTop → HasLogDensityZero {N | ¬ ((colMin N : ℝ) < f N)}

/-- Terras (1976), Everett (1977): almost every `n` (natural density) has finite stopping time. -/
def TerrasTheorem : Prop := HasNatDensityOne {n | ∃ k, T^[k] n < n}

/-- Korec (1994): for `θ > log 3 / log 4`, almost every `n` has an iterate below `n^θ`. -/
def KorecTheorem : Prop :=
  ∀ θ : ℝ, Real.log 3 / Real.log 4 < θ →
    HasNatDensityOne {n | ∃ k, (C^[k] n : ℝ) < (n : ℝ) ^ θ}

open Classical in
/-- Krasikov and Lagarias (2003): at least `x^0.84` of the integers up to `x` reach 1. -/
def KrasikovLagariasTheorem : Prop :=
  ∀ᶠ x : ℕ in atTop, (x : ℝ) ^ (0.84 : ℝ) ≤ ((range (x + 1)).filter (fun n => Reaches C n 1)).card

/-- The number of local minima of the `T`-cycle through `x` of length `p`: odd elements whose
cyclic predecessor is even. -/
def numLocalMin (x p : ℕ) : ℕ :=
  ((range p).filter (fun i => T^[i] x % 2 = 1 ∧ T^[i + p - 1] x % 2 = 0)).card

/-- Simons and de Weger (2005), extended by Hercher (2023): a nontrivial positive `T`-cycle has
at least 92 local minima. -/
def HercherTheorem : Prop :=
  ∀ x p, 0 < x → 0 < p → T^[p] x = x → x ≠ 1 → x ≠ 2 → 92 ≤ numLocalMin x p

/-- Steiner (1977), all `k, l`: the only circuit is the trivial one. `Steiner.lean` proves the
`k, l < 80` case. -/
def SteinerTheorem : Prop := ∀ x k l, IsCircuit x k l → x = 1

/-- Terras's conjecture κ = σ for `n ≥ 2` (open). -/
def CoefficientStoppingTimeConjecture : Prop :=
  ∀ n k, 2 ≤ n → IsFirst T (· < n) n k → IsFirstCoeff n k

/-- Divergent Trajectories Conjecture: no positive `C`-orbit tends to infinity (open). -/
def NoDivergentTrajectories : Prop :=
  ∀ n, 0 < n → ¬ Tendsto (fun k => C^[k] n) atTop atTop

/-- Nontrivial cycles conjecture: every positive `C`-cycle lies in `{1, 2, 4}` (open). -/
def NoNontrivialCycles : Prop :=
  ∀ x p, 0 < x → 0 < p → C^[p] x = x → x = 1 ∨ x = 2 ∨ x = 4

/-- The conjecture splits into the two open halves (proved in `Reductions.lean`). -/
theorem conjecture_iff_halves :
    CollatzConjecture ↔ NoDivergentTrajectories ∧ NoNontrivialCycles :=
  conjecture_iff

end Collatz
