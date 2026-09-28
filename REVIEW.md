# Independent review: "no Collatz m-cycle with m ≤ 101"

Reviewer: Claude (AI), session of 2026-09-28, at the request of the repository owner.
Scope: verify that the repository proves what the README claims, identify what the proof
rests on, cross-check the numerical data independently, and find out why the bound stops
at m = 101.

## 1. Verdict

**The claim holds, in exactly the conditional form the README states.** The repository proves,
by a kernel-checked Lean 4 proof with no non-standard axioms, that *if* every `0 < n ≤ 2^71`
reaches 1 and *if* Rhin's measure holds in the Simons–de Weger form (`RhinBound`), then no
positive Collatz cycle other than `1 → 2 → 1` has 101 or fewer local minima, i.e. there is no
Collatz `m`-cycle with `m ≤ 101`. Evidence, in decreasing order of weight:

1. The proof compiles from source on an isolated machine (Mathlib compiled from source,
   84 minutes) and in GitHub CI; every one of the 1173 `Collatz` declarations, and the final
   theorem in particular, depends only on `propext`, `Classical.choice`, `Quot.sound`. A separate
   kernel replay (`leanchecker`) of all 50 modules also passes (§3).
2. The statement means what the README says: every definition it mentions was read (§2), and
   an independent statement-level audit of every definition and hypothesis on the dependency
   path found nothing vacuous, hidden or non-standard (§7).
3. The two hypotheses match the literature as far as I could check without access to the
   papers themselves: Bařina's 2025 verification to `2^71` is confirmed; the constants 13.3 and
   0.46057 are confirmed by four independent secondary quotations, and I checked that the
   `K`-form is equivalent in strength to Rhin's `p^{−13.3}` measure for all integers, so no extra
   assumption is hidden in `RhinBound` (§4).
4. Every number I could recompute independently agrees: 84 of the 97 kernel-checked two-rise
   bounds are exactly the true maxima (the rest were not recomputed only for lack of time), every
   shape certificate and Rhin ceiling passes an independent transcription of the checkers, and
   the README's "80 %" worst case is reproduced (§5).

What is *not* established, and should be said plainly wherever the result is quoted:

* The theorem is conditional. That is the same standard as Simons–de Weger's `m ≤ 68` and
  Hercher's `m ≤ 91`, both of which rest on Rhin's measure and on a numerical verification
  bound, so the comparison "previous record 91" is fair. It is not a proof of the Collatz
  conjecture and says nothing about `m ≥ 102` or divergent orbits (the README says so).
* I could not read Rhin's proposition or Simons–de Weger's Lemma 12 in the original; the lemma
  numbering and any height threshold in Rhin's theorem remain to be checked by someone with
  the papers in hand.
* The Lean kernel (a release-candidate toolchain), Mathlib, and Bařina's computation are trusted,
  not re-verified.
* There is no human-readable proof of the new material yet; the Lean sources are the only
  complete account, and the work is not refereed.

On the value of the result: the two-rise bound and the chain argument are a genuine, correct
improvement, but a modest one. The 101 is the point where the two-rise grid's compute budget
runs out, not a structural barrier (§6): each further `m` needs about 2.6× more kernel time,
so this route buys single-digit increments of `m` at exponentially increasing cost and does not
point toward anything qualitatively new. Present it as "the method extends Hercher's bound to
101 for a known price", not as progress on the conjecture.

## 2. What is proved (checked by reading the statement)

The final theorem is `Collatz.no_101_cycle_2_71` (`Collatz/MCycle101.lean:73`):

```lean
theorem no_101_cycle_2_71 (hX : ∀ n, 0 < n → n ≤ 2 ^ 71 → Reaches T n 1) (hR : RhinBound) :
    ∀ x p, 0 < x → 0 < p → T^[p] x = x → x ≠ 1 → x ≠ 2 → 102 ≤ numLocalMin x p
```

Every definition in this statement was read and matches the README and the standard notions:

* `T n = if n % 2 = 0 then n / 2 else (3 * n + 1) / 2` (`Collatz/Defs.lean:34`): the usual
  shortcut Collatz map on naturals; for odd `n`, `(3n+1)/2` is exact.
* `Reaches f n m := ∃ k, f^[k] n = m` (`Collatz/Defs.lean:70`).
* `oddCount T x p` counts the odd values among `T^[0] x, …, T^[p-1] x` (`Collatz/Defs.lean:56`).
* `numLocalMin x p` counts `i < p` with `T^[i] x` odd and `T^[i+p-1] x` even
  (`Collatz/Statements.lean:57`). Since `T^[p] x = x`, `T^[i+p-1] x` is the cyclic predecessor
  of `T^[i] x`; an odd element whose predecessor is even is exactly a local minimum of the
  cycle, and the number of local minima is the `m` of an `m`-cycle (Simons–de Weger, Hercher).
* `p` is any period, not necessarily the least one. If `p = t·p₀`, the count is `t` times the
  count for `p₀`, so the statement for all `p` is equivalent to the statement for the least period.
* `x ≠ 1, x ≠ 2` excludes exactly the trivial cycle `1 → 2 → 1`: if a positive cycle contains 1
  it is that cycle (`Collatz/Cycles.lean:141`, `cycle_not_reaches_one`).

`scripts/Statement.lean` restates the theorem with the definitions unfolded (`rfl` checks) and
prints its axioms, so the statement can be audited without reading the proof. I agree with the
README's reading of the statement.

## 3. What the proof rests on (trust base)

1. **The Lean 4 kernel**, toolchain `leanprover/lean4:v4.35.0-rc3` (a release candidate, pinned
   with Mathlib commit `c55e6e78…` of 2026-09-24), including the kernel's GMP-accelerated
   `Nat` arithmetic. All large computations are done with `decide +kernel`, i.e. by kernel
   reduction of plain `Nat`/`ℚ` definitions; there is no `native_decide` (which would show up
   as the axiom `Lean.ofReduceBool`).
2. **Mathlib** facts, notably `Real.log_two_gt_d9 : 0.6931471803 < log 2`,
   `Real.log_two_lt_d9 : log 2 < 0.6931471808` and the logarithm series tail bound
   `Real.abs_log_sub_add_sum_range_le` (all present in the pinned Mathlib, checked in the
   local checkout). The enclosure `deltaLo < log₂ 3 < deltaHi` of width `10⁻⁵⁰` is proved from
   the series bound inside the repository (`Collatz/LogTwoThreeBounds.lean`).
3. **Hypothesis `hX`**: every `0 < n ≤ 2^71` reaches 1 (Bařina's distributed computation).
4. **Hypothesis `RhinBound`** (`Collatz/HercherRhin.lean:37`): for every nontrivial positive
   cycle with `K = oddCount T x p ≥ 1`,
   `exp(−13.3·(0.46057 + log K)) < p·log 2 − K·log 3`.

Checks of the trust base:

* `grep` over the sources: no `sorry`, `axiom`, `native_decide`, `unsafe`, `implemented_by`,
  `extern`, `opaque`, `partial`, `macro`, `elab`; the only `set_option`s are `maxRecDepth`
  (twice) and `Elab.async false` (memory control in the generated modules).
* The repository's own CI run on `main` (run 1, 2026-09-28 08:11 UTC) built everything and its
  axiom audit reported `audited 1173 declarations: only propext, Classical.choice, Quot.sound`;
  `#print axioms main_statement` gives the same three axioms.
* Kernel replay with `leanchecker` (the bundled `lean4checker`, added to CI on this review
  branch, runs 2 and 3 on 2026-09-28): all 50 `Collatz.*` modules were re-elaborated
  declaration by declaration through the kernel from their `.olean`s (`replaying Collatz.…`
  for each module, 9 minutes single-threaded) with no error. This guards against environment
  tampering by metaprograms, which a plain `lake build` would not catch. The grep, the axiom
  audit (`1173 declarations`) and `#print axioms main_statement` also passed on this branch.
* Local from-source build (the Mathlib cache hosts are blocked from this container, so Mathlib
  was compiled from source with the pinned toolchain, 4 cores, 09:00–10:22 UTC): `lake build`
  exit 0, 3568 modules, 39 warnings (deprecations, unused variables), 0 errors;
  `lake env lean scripts/AxiomAudit.lean` → `audited 1173 declarations: only propext,
  Classical.choice, Quot.sound`; `scripts/Statement.lean` → the same three axioms; and
  `#print axioms` of `no_101_cycle_2_71`, `hercher_theorem`, `data101_ok`,
  `TwoRise.allPairs23446`, `logb_two_three_bounds` → the same three axioms.

## 4. The two hypotheses against the literature

The original papers (Acta Arith. 117, JIS 26, Rhin's 1987 article, Bařina's 2025 article) are
on hosts that this container's network policy blocks, so the citations were checked only
through search-engine snippets of the papers and of independent secondary sources. Status:

**Hypothesis `hX` (2^71).** Confirmed: D. Bařina, *Improved verification limit for the
convergence of the Collatz conjecture*, J. Supercomput. 81 (2025), art. 810,
doi 10.1007/s11227-025-07337-0; abstract: "pushes the limit for which the conjecture is
verified up to 2^71". Two small gaps between citation and Lean statement:

* `hX` is stated for the shortcut map `T`; Bařina's computation is for the Collatz map `C`
  (`3n+1`, then halvings). `Reaches C n 1 ↔ Reaches T n 1` is elementary but not formalized in
  the repository (`Reductions.lean` only relates "some iterate is smaller" to "reaches 1" for
  each map separately). Worth a five-line lemma so the hypothesis matches the citation verbatim.
* Whether the published bound is `< 2^71` or `≤ 2^71` is not settled by the snippets; immaterial,
  since `2^71` itself reaches 1.

**Hypothesis `RhinBound` (13.3, 0.46057).** The form `|Λ| > exp(−13.3·(0.46057 + log K))` with
`K` the number of odd elements is confirmed by four independent secondary quotations of
Simons–de Weger (a MathOverflow discussion, G. Helms's notes, Sha's arXiv 2112.12962, and
Simons–de Weger's own later paper on generalized Syracuse sequences). Not verified: the exact
lemma number (the repository's scripts cite the 2010 preprint "v1.44" while the README cites the
2005 journal version; the numbering may differ), and whether Rhin's proposition carries a
threshold `H ≥ H₀` (moot under `hX`, where `K` is astronomically large, but it should be stated).

Analysis of the constants (my own, verified to 40 digits): `ln(log₂ 3) = 0.4605607…`, so
`0.46057` is `ln δ` rounded up at the fifth decimal, and `e^{0.46057} = 1.5849772 = δ + 1.47·10⁻⁵`.
Rhin's measure, written for `Λ = p log 2 − K log 3` with height `H = p` (the larger coefficient),
is `Λ > p^{−13.3}`. The `K`-form follows from it for **every** pair of positive integers with
`2^p > 3^K`, by two cases: if `p/K ≤ 1.5849772` then `log p ≤ 0.46057 + log K` and the `K`-form
is weaker than the `p`-form; if `p/K > 1.5849772` then `Λ = K·log 2·(p/K − δ) > 1.016·10⁻⁵·K`,
which exceeds `e^{−13.3·0.46057}·K^{−13.3} = 0.00219·K^{−13.3}` for every `K ≥ 2`, and for
`K = 1` the smallest value `2 log 2 − log 3 = 0.288` exceeds it too. So `RhinBound` is exactly
Rhin's measure in disguise, no cycle-specific estimate is hidden in it, and restricting it to
cycles only weakens the hypothesis. The README's description is accurate. Recommendation
(cosmetic, but it makes the hypothesis checkable line by line against Rhin's paper): state the
pure Diophantine inequality `∀ p K, 1 ≤ K → K·log 3 < p·log 2 → p^{−13.3} < p·log 2 − K·log 3`
as the hypothesis and prove the two-case reduction above in Lean.

**Hercher's paper.** J. Integer Seq. 26 (2023), Article 23.3.5, confirmed; the journal page lists
a corrigendum, confirmed. The date 14 June 2026, the affected result (Theorem 21) and the credit
to Xinjun Wang are confirmed only through a secondary source (a GitHub issue of 27 Sept 2026 on
another formalization repository). The verification bound `695·2^60` used by Hercher is
consistent with snippets of his paper.

**Related work and priority.** The 27 Sept 2026 announcement of an independent m ≤ 91
formalization (azadveersingh) is confirmed; it takes Simons–de Weger's Theorem 3 bounds as
hypotheses, whereas this repository takes Rhin's measure and derives the ceiling, which is the
cleaner assumption. The "m ≤ 82" figure for PhilNorfleet's partial formalization could not be
confirmed. No published or announced bound beyond m ≤ 91 was found anywhere, so "new record"
is consistent with everything visible.

## 5. Independent numerical cross-checks

All of these were computed from scratch (no code shared with the repository's generators).

* **Two-rise bounds.** `TwoRise.AllPairs N B` is kernel-checked for 97 values of `N` (72 to
  23 446). I recomputed the exact maximum `M(N) = max (k₀ + k₁)` over odd `n < 2^N` by an
  independent 2-adic enumeration (`review/scripts/tworise_indep.py`) for every grid value
  `N ≤ 6792` (84 of 97 entries): every `B` equals `M(N)` exactly (e.g. `M(74) = 84`, witness
  `k₀ = 56, ℓ = 1, k₁ = 28`; `M(6792) = 6806`), no violations. The 13 largest entries
  (7471 to 23 446) were not recomputed: the naive enumeration costs about `N^2.3` and the
  largest would take over an hour; they rest on the kernel check alone.
* **Shape certificates and Rhin ceilings.** I transcribed the Boolean checkers `uOK`, `shapeOK`,
  `chainF/G/Next/Sum` and `rhinOK` from the Lean sources into Python
  (`review/scripts/chain_indep.py`) and ran them on the data of `MCycle92`, `MCycle96`, `MCycle97`
  and `MCycle101Data`: every certificate passes, every Rhin ceiling `Kceil` is tight
  (`rhinOK` holds at `Kceil` and fails at `Kceil − 1`), and the worst chain ratio for
  `m = 101` is `0.7980` of `K`, which is the README's "about 80 %".
* **The certificate generator** (`research/scripts/mcycle101_certgen`) reproduces the m = 101
  data (39 shapes, 7629 walk nodes, `K ≥ 77 692 117 359 936 589 403`).

## 6. Why the method stops at m = 101

Running the repository's own generator for `m = 102` and `m = 103` with the committed two-rise
grid (`review/scripts/m102_probe.py`):

| m   | surviving shapes | shapes whose chain fails | worst chain sum / K |
|-----|------------------|--------------------------|---------------------|
| 101 | 39               | 0                        | 0.798               |
| 102 | 63               | 1                        | 1.265               |
| 103 | 99               | 1                        | 2.005               |

The failing shape is always the first one, `K = 77 692 117 359 936 589 403`,
`p = 123 139 092 617 126 647 266` (a convergent of `log₂ 3`; the bootstrap stalls there for
every `m ≥ 92`). The mechanism: while the chain of minima stays below the top of the grid
(`2^23446`), the two-rise bound limits growth to a factor `δ = log₂ 3` per *two* steps; above
the grid the only bound is `δ` per step. Each extra minimum therefore multiplies the tail of
the chain by `δ ≈ 1.585`, and `0.798 · 1.585 = 1.265` is exactly the m = 102 ratio. So m = 101
is where the *compute budget* of this method runs out, not a mathematical wall:

| m   | grid top `N` needed (estimate, `B = N + 16` for new points) | kernel cost proxy `Σ N²` |
|-----|-------------------------------------------------------------|--------------------------|
| 101 | 23 446 (committed)                                          | 3.2 · 10⁹                |
| 102 | ≈ 34 000                                                    | 8.2 · 10⁹                |
| 103 | ≈ 55 000                                                    | 2.1 · 10¹⁰               |
| 104 | ≈ 89 000                                                    | 5.5 · 10¹⁰               |
| 106 | ≈ 231 000                                                   | 3.7 · 10¹¹               |

(`review/scripts/grid_extent.py`; the two-rise check costs about `N²` kernel operations per grid
point, and the cost grows by roughly ×2.6 per additional `m`.)

## 7. Mathematics of the new parts (read, not re-proved; the kernel checks the proofs)

* Two-rise bound (`Collatz/TwoRiseCheck.lean`): for odd `n < 2^N`, `n + 1 = 2^{k₀} a`, the
  next minimum satisfies `3^{k₀} a + 2^ℓ = 2^{ℓ+k₁} a' + 1`, so `a ≡ 3^{−k₀}(1 − 2^ℓ)`
  modulo `2^{ℓ+k₁}`; `k₀ + k₁ > B` would force a run of zero bits of that 2-adic number from bit
  `A = N − k₀` up, which the checker refutes bit-parallel for every `ℓ`. The soundness theorem
  `kCore_sound … : PairCond N B k₀` and `twoRiseBound_of_allPairs` connect this to the orbit
  notions `orun`/`nextMin`. The derivation is correct and my independent enumeration agrees
  with the values.
* Two-step inequality (`TwoRise.two_step_core`): `4·2^{k+k'}(n''+1) ≤ 3^{k+k'}(n+4)`, hence
  `log₂(n''+1) ≤ log₂(n+1) + (δ−1)(k+k') − 2 + 6/(n+1)`. I re-derived this by hand; it uses only
  `ℓ ≥ 1` for each descent.
* Chain (`Collatz/MCycleChain.lean`): integer chain `Y_t` (units of `2^{−20}`) dominating
  `x_t = log₂(n_t + 1)` from the least minimum, with `x_{t+1} ≤ δ x_t` (Lemma 20) and the
  two-step bound when `x_t ≤ N` for a grid point `(N, B)`; `K ≤ Σ x_t` (each rise `k_t ≤ x_t`);
  contradiction when `Σ Y_t < K·2^S`. The least element is bounded by Theorem 21 in the
  two-element form (`lambda_lt_two`) at the floor `X₀ = n₀` itself. Sound as read.
* Farey walk (`Collatz/MCycleWalk.lean`): `walk_sound` shows every `(K, p)` below the Rhin
  ceiling with `p/K` in the admissible interval is listed or a failure marker is emitted, and
  `mOK` rejects the marker. Sound as read.

Statement-level audit of the Hercher files (Theorem 16, 21, bootstrap), done separately from
my reading: `hercher_theorem` has exactly the two hypotheses (`695·2^60` and `RhinBound`);
`RatioIn p K ε` is `δ < p/K < δ + ε`; `windowExp m m₂ K = m₂K/(m·Σ_{d<m₂} δ^d)` (Hercher's
`v`, with the factor `m₂`), `windowExp2` its two-element variant; `theorem21_vertexFree`
proves `3Λ < 3(m−m₂)/X₀ + 3m₂/(2^v − 1)` and `theorem21_two` proves
`3Λ < 3(m−m₂)/X₀ + 3/(2^v − 1) + 3(m₂−1)/(2^τ − 1)`, both from Theorem 16
(`theorem16_of_isMin`), Lemma 8 (`orun_le_logb`), Lemma 20 (`logb_nextMin_lt`) and Remark 7,
so the corrigendum's convex-vertex argument and Theorem 14 (`97/54`) are not used, as the
README says. No `Nat.find`/`sInf`/`Classical` on the main path except inside `orun`/`erun`
(least indices of decidable predicates), no `instance`/`@[simp]`/`abbrev` tricks
(`IsMinOf` is a transparent `abbrev`), `autoImplicit` off. Nothing vacuous.

## 8. Smaller observations

* The README says a CI build takes about 18 minutes; run 1 took 7 minutes (Mathlib cache hit),
  and a full build with Mathlib from source took 84 minutes on 4 cores.
* The toolchain is a release candidate (`v4.35.0-rc3`); a stable release would be preferable
  for a proof meant to be checked by others, but it does not affect correctness.
* Build warnings only (deprecated `push_neg`, `if_pos`/`if_neg`, unused variables).
* The README's "related work": the 27 Sept 2026 announcement of an independent `m ≤ 91`
  formalization is confirmed (it was posted as an issue on the other formalization's
  repository); the "m ≤ 82" figure for the partial formalization could not be confirmed.
* Several docstrings reference notes in a private repository (`research_notes/…`, `docs/…`);
  the human-readable proof is "in preparation". Until it exists, the Lean sources are the only
  complete account of the new argument.
* Dead weight: `HercherBootstrap.lean` keeps superseded theorems
  (`no_91_cycle_of_hypotheses`, `…_selfseeded`) whose hypotheses quantify over *every* cycle
  with 91 local minima and are therefore false for the trivial cycle run 91 times
  (`x = 1`, `p = 182`); `HercherChain91.lean` and `HercherNo91.lean` keep variants with extra
  hypotheses (`hceil`, `H6`, `H7`). None of them is on the path to the main theorem (the audit
  traced the dependency path), but they invite misreading and should be deleted or clearly
  quarantined. Likewise `Terras.lean`, `Steiner.lean`, `Records.lean`, `SharpCycleBound.lean`,
  `RotationBound.lean` are imported only through `Statements.lean` and play no role in the
  result.
* The verification bound enters twice: Hercher's part uses `695·2^60` (`hercherX₀`) and the new
  part uses `2^71 + 1` (`mX₀`); `hercher_theorem_2_71` bridges them. Consistent, but a single
  constant would be cleaner.

## 9. Recommendations

1. Restate `RhinBound` as the pure Diophantine inequality of Rhin's theorem (with whatever
   height threshold the original states) and prove the two-case reduction to the
   `0.46057 + log K` form in Lean (see §4). Cite the exact version of Simons–de Weger whose
   lemma numbering is used.
2. Add the lemma `Reaches C n 1 ↔ Reaches T n 1` so that `hX` matches Bařina's statement.
3. Keep the `leanchecker` replay in CI (added on this branch).
4. Cite Bařina's 2025 paper with its title (*Improved verification limit for the convergence of
   the Collatz conjecture*) and DOI in the README.
5. Publish the human-readable proof of the two-rise and chain arguments; the Lean code is the
   proof, but a referee needs the narrative. Until then, the private notes referenced in the
   docstrings are dangling references.
