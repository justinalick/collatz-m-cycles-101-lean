import Collatz.MCycle92
import Collatz.MCycle93
import Collatz.MCycle94
import Collatz.MCycle95
import Collatz.MCycle96
import Collatz.MCycle97
import Collatz.MCycle98
import Collatz.MCycle99
import Collatz.MCycle100
import Collatz.MCycle101Data

/-!
# No Collatz `m`-cycle with `m ≤ 101` when every `n ≤ 2⁷¹` reaches 1

Hercher's theorem (`hercher_theorem`, `m ≤ 91`, verification bound `695 · 2⁶⁰ < 2⁷¹`) extended by
the chain bound of `research_notes/Collatz disproof routes/m92_obstruction.md` (Theorem 8, with the
two-rise lemma, Proposition B′): `MCycle92.lean`, …, `MCycle100.lean` and `MCycle101Data.lean`
exclude one `m` each.

The hypotheses are the verification bound `2⁷¹` (Bařina) and `RhinBound` (Simons–de Weger's
Lemma 12, from Rhin's transcendence measure); nothing else is assumed.
-/

namespace Collatz

/-- Every element of a nontrivial cycle exceeds `2⁷¹` if every `0 < n ≤ 2⁷¹` reaches 1. -/
theorem cycle_gt_of_verified (hX : ∀ n, 0 < n → n ≤ 2 ^ 71 → Reaches T n 1) {x p : ℕ}
    (hx : 0 < x) (hp : 0 < p) (hcyc : T^[p] x = x) (hx1 : x ≠ 1) (hx2 : x ≠ 2) :
    ∀ j, 2 ^ 71 < T^[j] x := by
  intro j
  by_contra h
  exact cycle_not_reaches_one hp hcyc hx1 hx2 j (hX _ (iterate_T_pos hx j) (by omega))

/-- Hercher's theorem at the verification bound `2⁷¹`: at least 92 local minima. -/
theorem hercher_theorem_2_71 (hX : ∀ n, 0 < n → n ≤ 2 ^ 71 → Reaches T n 1) (hR : RhinBound) :
    HercherTheorem :=
  hercher_theorem (fun n hn hle => hX n hn (le_trans hle (by norm_num))) hR

/-- **No Collatz `m`-cycle with `m ≤ 92`** when every `0 < n ≤ 2⁷¹` reaches 1, given
`RhinBound`: every nontrivial positive `T`-cycle has at least 93 local minima. -/
theorem no_92_cycle_2_71 (hX : ∀ n, 0 < n → n ≤ 2 ^ 71 → Reaches T n 1) (hR : RhinBound) :
    ∀ x p, 0 < x → 0 < p → T^[p] x = x → x ≠ 1 → x ≠ 2 → 93 ≤ numLocalMin x p := by
  intro x p hx hp hcyc hx1 hx2
  have h91 := hercher_theorem_2_71 hX hR x p hx hp hcyc hx1 hx2
  have hlow := cycle_gt_of_verified hX hx hp hcyc hx1 hx2
  by_contra h
  exact no_92_cycle_of_floor hR hx hp hcyc hx1 hx2 hlow (by omega)

/-- **No Collatz `m`-cycle with `m ≤ 94`** when every `0 < n ≤ 2⁷¹` reaches 1, given
`RhinBound`: every nontrivial positive `T`-cycle has at least 95 local minima. -/
theorem no_94_cycle_2_71 (hX : ∀ n, 0 < n → n ≤ 2 ^ 71 → Reaches T n 1) (hR : RhinBound) :
    ∀ x p, 0 < x → 0 < p → T^[p] x = x → x ≠ 1 → x ≠ 2 → 95 ≤ numLocalMin x p := by
  intro x p hx hp hcyc hx1 hx2
  have h92 := no_92_cycle_2_71 hX hR x p hx hp hcyc hx1 hx2
  have hlow := cycle_gt_of_verified hX hx hp hcyc hx1 hx2
  have h93 := no_93_cycle_of_floor hR hx hp hcyc hx1 hx2 hlow
  have h94 := no_94_cycle_of_floor hR hx hp hcyc hx1 hx2 hlow
  omega

/-- **No Collatz `m`-cycle with `m ≤ 96`** when every `0 < n ≤ 2⁷¹` reaches 1, given
`RhinBound`: every nontrivial positive `T`-cycle has at least 97 local minima. -/
theorem no_96_cycle_2_71 (hX : ∀ n, 0 < n → n ≤ 2 ^ 71 → Reaches T n 1) (hR : RhinBound) :
    ∀ x p, 0 < x → 0 < p → T^[p] x = x → x ≠ 1 → x ≠ 2 → 97 ≤ numLocalMin x p := by
  intro x p hx hp hcyc hx1 hx2
  have h94 := no_94_cycle_2_71 hX hR x p hx hp hcyc hx1 hx2
  have hlow := cycle_gt_of_verified hX hx hp hcyc hx1 hx2
  have h95 := no_95_cycle_of_floor hR hx hp hcyc hx1 hx2 hlow
  have h96 := no_96_cycle_of_floor hR hx hp hcyc hx1 hx2 hlow
  omega

/-- **No Collatz `m`-cycle with `m ≤ 101`** when every `0 < n ≤ 2⁷¹` reaches 1, given
`RhinBound`: every nontrivial positive `T`-cycle has at least 102 local minima. -/
theorem no_101_cycle_2_71 (hX : ∀ n, 0 < n → n ≤ 2 ^ 71 → Reaches T n 1) (hR : RhinBound) :
    ∀ x p, 0 < x → 0 < p → T^[p] x = x → x ≠ 1 → x ≠ 2 → 102 ≤ numLocalMin x p := by
  intro x p hx hp hcyc hx1 hx2
  have h96 := no_96_cycle_2_71 hX hR x p hx hp hcyc hx1 hx2
  have hlow := cycle_gt_of_verified hX hx hp hcyc hx1 hx2
  have h97 := no_97_cycle_of_floor hR hx hp hcyc hx1 hx2 hlow
  have h98 := no_98_cycle_of_floor hR hx hp hcyc hx1 hx2 hlow
  have h99 := no_99_cycle_of_floor hR hx hp hcyc hx1 hx2 hlow
  have h100 := no_100_cycle_of_floor hR hx hp hcyc hx1 hx2 hlow
  have h101 := no_101_cycle_of_floor hR hx hp hcyc hx1 hx2 hlow
  omega

end Collatz
