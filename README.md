# collatz-m-cycles-101-lean

A Lean 4 proof that **every nontrivial Collatz cycle has at least 102 local minima**, assuming two inputs:
every positive integer up to 2^71 reaches 1 (a published computation), and Rhin's lower bound on |p log 2 − K log 3|.

The previous record was at least 92 local minima, i.e. no m-cycle with m ≤ 91 (C. Hercher, 2023). This is not a proof of
the Collatz conjecture: it rules out cycles with at most 101 local minima and says nothing about cycles with more, or
about divergent orbits.

## Credit

This work stands on C. Hercher's proof that there are no m-cycles with m ≤ 91 (J. Integer Seq. 26 (2023),
Art. 23.3.5, with the corrigendum of June 2026; the error it repairs was found by Xinjun Wang). Everything up to the
list of surviving cycle shapes is his method: the product identity and its AM–GM form (Theorem 16), the bounds on
local minima (Lemmas 8, 9, 11, 20, Corollary 13, Theorem 14), the window bound (Theorem 21), the Farey step
(Lemma 22) and the bootstrap (Theorem 23). What is new here is the two-rise bound and the chain argument that
exclude the shapes his bootstrap leaves for m = 92, …, 101, and the formalization. The m-cycle framework and the use
of Rhin's measure are due to J. Simons and B. de Weger (2005).

## The theorem

```lean
theorem Collatz.no_101_cycle_2_71
    (hX : ∀ n, 0 < n → n ≤ 2 ^ 71 → Reaches T n 1)
    (hR : RhinBound) :
    ∀ x p, 0 < x → 0 < p → T^[p] x = x → x ≠ 1 → x ≠ 2 → 102 ≤ numLocalMin x p
```

In words: if every n with 0 < n ≤ 2^71 reaches 1, and `RhinBound` holds, then every positive cycle of `T` other
than 1 → 2 → 1 has at least 102 local minima.

## The definitions it uses

These are all the definitions the statement depends on (the rest of the code is the proof):

```lean
-- Collatz/Defs.lean
def T (n : ℕ) : ℕ := if n % 2 = 0 then n / 2 else (3 * n + 1) / 2
def Reaches (f : ℕ → ℕ) (n m : ℕ) : Prop := ∃ k, f^[k] n = m
def oddCount (f : ℕ → ℕ) (n : ℕ) : ℕ → ℕ      -- number of odd values among f^[0] n, …, f^[k-1] n
  | 0 => 0
  | k + 1 => oddCount f n k + f^[k] n % 2

-- Collatz/Statements.lean: odd elements whose cyclic predecessor is even
def numLocalMin (x p : ℕ) : ℕ :=
  ((range p).filter (fun i => T^[i] x % 2 = 1 ∧ T^[i + p - 1] x % 2 = 0)).card

-- Collatz/HercherRhin.lean: Simons–de Weger, Lemma 12 (from Rhin's measure), for cycles
def RhinBound : Prop :=
  ∀ x p : ℕ, 0 < x → 0 < p → T^[p] x = x → x ≠ 1 → x ≠ 2 → 1 ≤ oddCount T x p →
    Real.exp (-(133 / 10 * (46057 / 100000 + Real.log (oddCount T x p)))) <
      (p : ℝ) * Real.log 2 - (oddCount T x p : ℝ) * Real.log 3
```

`scripts/Statement.lean` restates the theorem with these definitions unfolded and checks it against the proof, so the
statement can be audited without reading the proof.

Remarks on the statement:
* `p` need not be the least period. Taking `p` minimal gives the number of local minima of the cycle itself; for a
  multiple of the period the count is multiplied accordingly, so the theorem covers the minimal case.
* The hypotheses are parameters of the theorem, not axioms. The axiom audit below shows that nothing else is assumed.
* `hX`: Bařina verified that every n < 2^71 reaches 1 (D. Bařina, J. Supercomput. 81 (2025), art. 810); n = 2^71 is a
  power of 2.
* `RhinBound`: G. Rhin, "Approximants de Padé et mesures effectives d'irrationalité", Progr. Math. 71 (1987) 155–164,
  as used in J. Simons and B. de Weger, Acta Arith. 117 (2005) 51–70, Lemma 12. It is a transcendence-theory input
  that is not in Mathlib.

## How the proof works

1. **Hercher's theorem**, m ≤ 91 (J. Integer Seq. 26 (2023), Art. 23.3.5, with the corrigendum of 14 June 2026), is
   formalized in full from the same two hypotheses (`Collatz.hercher_theorem`, `Collatz/Hercher*.lean`). For each m ≤ 91
   the continued-fraction bootstrap is checked by the kernel; the ceiling on the number of odd steps comes from
   `RhinBound`, not from the Simons–de Weger computations.
2. **The two-rise bound** (new). For an odd n < 2^N, the first two ascending runs of its orbit have total length at most
   M(N), and M(N) is only slightly larger than N (for example M(74) ≤ 84). This is a finite 2-adic computation, checked by
   the kernel for every N used (up to 23 446) by a checker proved sound in `Collatz/TwoRiseCheck.lean`.
3. **The chain bound** (new). Along a cycle, the sizes of consecutive local minima can grow by a factor of at most
   log₂ 3 in the exponent per step, but by the two-rise bound only by about that factor over two steps. Starting from the
   least minimum, whose size Hercher's Theorem 21 bounds (`lambda_lt_two`, `least_lt_Ub`), the minima cannot reach the total size that a cycle with the
   required number of odd steps needs (`Collatz/MCycleChain.lean`, `MCycleWalk.lean`).
4. **Per-m certificates** for m = 92, …, 101 (`Collatz/MCycle92.lean` … `MCycle101Data.lean`): the finitely many cycle
   shapes (numbers of odd steps K) that survive the bootstrap below the Rhin ceiling are listed by a Farey walk and each
   is excluded by the chain bound. The worst case reaches about 80 % of what the cycle needs (m = 101, K = 77 692 117 359 936 589 403).

A paper with the human-readable proof is in preparation.

## Checking it

Requirements: [elan](https://github.com/leanprover/elan) (the toolchain `leanprover/lean4:v4.35.0-rc3` is pinned in
`lean-toolchain`), git, and about 2 GB of memory per Lean process.

```sh
lake exe cache get                          # prebuilt Mathlib
lake build                                  # builds the proof
lake env lean scripts/AxiomAudit.lean       # every Collatz declaration: only propext, Classical.choice, Quot.sound
lake env lean scripts/Statement.lean        # the statement above, with #print axioms
```

The same steps run in GitHub Actions on every push (`.github/workflows/lean.yml`); a build from scratch takes about
18 minutes on a standard GitHub runner, after the Mathlib cache is downloaded. The sources contain no `sorry`, no `native_decide` and no `axiom`; the workflow checks this.

## Layout

| Path | Content |
|---|---|
| `Collatz/Defs.lean`, `Statements.lean` | the map `T`, `Reaches`, `numLocalMin` |
| `Collatz/Hercher*.lean`, `FareyCertificate.lean`, `LogTwoThreeBounds.lean` | Hercher's m ≤ 91 |
| `Collatz/TwoRiseCheck.lean`, `MCycleTwoRise*.lean`, `MCycleGrid*.lean` | the two-rise bound: checker and kernel-checked values |
| `Collatz/MCycleSteps.lean`, `MCycleChain.lean`, `MCycleWalk.lean` | the chain bound and the per-m check |
| `Collatz/MCycle92.lean` … `MCycle101Data.lean`, `MCycle101.lean` | certificates and the main theorem |
| other `Collatz/*.lean` | general lemmas imported by the above (Terras' theorem, cycle identities, …) |
| `research/scripts/mcycle101_certgen/` | generators of the m = 92 … 101 data modules |
| `research/scripts/hercher_*.py` | the Hercher bootstrap and the constants of `LogTwoThreeBounds.lean` |

The data modules are reproduced byte for byte by the commands in the docstring of
`research/scripts/mcycle101_certgen/gen_lean.py`. The generators are not needed to check the proof: the kernel
re-checks every certificate. Some docstrings refer to notes (`research_notes/…`, `docs/…`) of the private development
repository; the mathematics they describe will be in the paper.

## Related work

* C. Hercher, *There are no Collatz m-cycles with m ≤ 91*, J. Integer Seq. 26 (2023); corrigendum 2026.
* J. Simons, B. de Weger, *Theoretical and computational bounds for m-cycles of the 3n+1 problem*, Acta Arith. 117 (2005).
* L. Halbeisen, N. Hungerbühler, *Optimal bounds for the length of rational Collatz cycles*, Acta Arith. 78 (1997).
* A partial formalization of Hercher's paper (m ≤ 82) is in `PhilNorfleet/Hercher2023_lean`; an independent
  formalization of m ≤ 91 from the Simons–de Weger bounds was announced in `azadveersingh/collatz-research`
  (27 September 2026).

## Status, authorship, license

Not yet refereed. Author: Justin Alick. The proofs, the Lean code and this repository were prepared with an AI coding
assistant (Claude Code) under the author's direction; the author is responsible for the content.
License: Apache 2.0 (see `LICENSE`).
