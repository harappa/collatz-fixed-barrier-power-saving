# A power-saving bound, uniform in the endpoint, for Collatz orbits that stay above a fixed barrier

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.22986670.svg)](https://doi.org/10.5281/zenodo.22986670)

This repository contains the Lean 4 formalization accompanying the preprint
*A power-saving bound, uniform in the endpoint, for Collatz orbits that stay above a fixed barrier* by Hiroyuki Nashida
(Zenodo, 2026, doi:10.5281/zenodo.22986670). It formalizes the main theorem of the paper (for all integers $N_0 \ge 1$
and $X \ge 0$, at most $K N_0^{-c'} X$ integers $1 \le N \le X$ have a Collatz orbit that stays above $N_0$, with an
explicit exponent $c'$), the fixed-barrier count on which it rests, and the density corollaries (Corollary 1.2); the
main theorem and Corollary 1.2 are proved without hypotheses, and the Lean kernel checks them with no axioms beyond the
three used throughout Mathlib.

## Paper

- **Author:** Hiroyuki Nashida
- **Title:** A power-saving bound, uniform in the endpoint, for Collatz orbits that stay above a fixed barrier
- **Preprint:** Zenodo, 2026
- **DOI:** [10.5281/zenodo.22986670](https://doi.org/10.5281/zenodo.22986670)
- **Lean code:** this repository

Revision r8 (September 27, 2026). This repository accompanies revision r8 of the paper; the revision number is
incremented with every revision of the paper and of this repository.

## Abstract

Let $\mathrm{col}$ be the Collatz map, $\mathrm{col}(n)=n/2$ for even $n$ and $\mathrm{col}(n)=3n+1$
for odd $n$. We prove that there is a constant $K>0$ such that for all integers $N_0\ge 1$ and $X\ge 0$,

$$\left|\lbrace 1\le N\le X : \mathrm{col}^{m}(N)>N_0 \text{ for all } m\ge 0\rbrace\right| \le K N_0^{-c'} X, \qquad c'=\frac{c_B}{160\ln 2}\approx 3.5\times 10^{-6},$$

where $c_B\approx 3.9\times10^{-4}$ is an explicit entropy rate. The bound is uniform in the endpoint $X$; in
particular the upper natural density of the set of integers whose orbit stays above $N_0$ is at most $KN_0^{-c'}$,
whereas the natural-density bounds available to us decay like a power of $\log N_0$. The proof combines two recent
results that exist as Lean formalizations: a fixed-barrier failure count, which we derive from lemmas of Shaik's
formalization and use only on a base window whose logarithmic scale is exponential in $\log N_0$, and the one-step
recursion of Tao's method in natural density, from Mazur's formalization, which carries the bound to all larger
scales. The whole argument, including the derivation of the fixed-barrier count, is formalized in Lean 4 and checked
by the kernel, with no axioms beyond the three used throughout Mathlib. The exponent $c'$ is explicit, while $K$ is
ineffective because it depends on thresholds obtained from "for all sufficiently large" statements. The Lean code is
available in this repository.

## Main results in Lean

### Main theorem (Theorem 1.1 of the paper)

```lean
def Collatz.col (n : ℕ) : ℕ := if n % 2 = 0 then n / 2 else 3 * n + 1

theorem Collatz.nd_collatz_uniform_explicit :
    ∃ K : ℝ, 0 < K ∧ ∀ N0 : ℕ, 1 ≤ N0 → ∀ X : ℕ,
      (((Finset.Icc 1 X).filter (fun N => ∀ m, N0 < col^[m] N)).card : ℝ) ≤
        K * (N0 : ℝ) ^ (-tstarExponent) * X

theorem Collatz.nd_collatz_uniform :
    ∃ K c' : ℝ, 0 < c' ∧ ∀ N0 : ℕ, 1 ≤ N0 → ∀ X : ℕ,
      (((Finset.Icc 1 X).filter (fun N => ∀ m, N0 < col^[m] N)).card : ℝ) ≤
        K * (N0 : ℝ) ^ (-c') * X

noncomputable def Collatz.tstarExponent : ℝ := cB * min (1 / 80) ((1 / 40 : ℝ) / 2) / (2 * Real.log 2)
noncomputable def Collatz.cB : ℝ := min (FixedBarrier.fbRate / 2) (Real.log 2 / 2)
lemma Collatz.tstarExponent_eq : tstarExponent = cB / (160 * Real.log 2)
lemma Collatz.tstarExponent_pos : 0 < tstarExponent
-- fbRate = log 2 - binEntropy (1/2 + (1/2)(1/16)/log₂ 3)
```

- `Collatz.col` is the Collatz map ($n/2$ for even $n$, $3n+1$ for odd $n$); `col^[m]` is its $m$-fold iterate,
  with $m = 0$ allowed, so the orbit includes $N$ itself.
- `nd_collatz_uniform_explicit` is the main theorem with the exponent displayed ($c' =$ `tstarExponent`) and
  $K > 0$.
- `nd_collatz_uniform` is the same bound with some exponent $c' > 0$.
- `tstarExponent` and `cB` define the exponent and the fixed-barrier rate $c_B$ in closed form; the comment line
  gives the closed form of `fbRate` from Shaik's formalization.
- `tstarExponent_eq` states $c' = c_B/(160 \log 2)$, and `tstarExponent_pos` states $c' > 0$.

In words: for all integers `N0 ≥ 1` and `X ≥ 0`, the number of `1 ≤ N ≤ X` whose Collatz orbit (including `N`
itself) stays strictly above `N0` is at most `K · N0^(-c') · X`, with `c' = cB/(160 log 2) ≈ 3.506e-6`. The exponent
is explicit; `K` is not effective (it depends on thresholds obtained from `Filter.eventually_atTop`). The identifier
`tstarExponent` is named after an internal label of the project; it has no mathematical meaning.

The fixed-barrier count (Theorem A of the paper) is
`FirstPassageLinearTransport.FixedBarrier.fixedBarrier_failure_count_rate` (explicit rate
`fbFixedRate = min (fbRate/2) (log 2/2)`); the existential form `fixedBarrier_failure_count` and the form
`Collatz.fixedBarrier_failure_count_explicit` used in the assembly are corollaries of it.

### Corollary 1.2 (`CollatzND/Core/Density.lean`)

```lean
theorem Collatz.nd_density_one (f : ℕ → ℝ) (hf : Filter.Tendsto f Filter.atTop Filter.atTop) :
    Filter.Tendsto
      (fun X : ℕ => (((Finset.Icc 1 X).filter (fun N => ∃ m, ((col^[m] N : ℕ) : ℝ) < f N)).card : ℝ) / X)
      Filter.atTop (nhds 1)

theorem Collatz.nd_collatz_corollaries :
    ∃ K : ℝ, 0 < K ∧
      (∀ N0 : ℕ, 1 ≤ N0 → ∀ X : ℕ,
        (((Finset.Icc 1 X).filter (fun N => ∀ m, N0 < col^[m] N)).card : ℝ) ≤
          K * (N0 : ℝ) ^ (-tstarExponent) * X) ∧
      (∀ N0 : ℕ, 1 ≤ N0 →
        Filter.IsBoundedUnder (· ≤ ·) Filter.atTop
          (fun X : ℕ => (((Finset.Icc 1 X).filter (fun N => ∀ m, N0 < col^[m] N)).card : ℝ) / X) ∧
        Filter.limsup
          (fun X : ℕ => (((Finset.Icc 1 X).filter (fun N => ∀ m, N0 < col^[m] N)).card : ℝ) / X)
          Filter.atTop ≤ K * (N0 : ℝ) ^ (-tstarExponent)) ∧
      (∀ θ : ℝ, 0 < θ → ∀ X : ℝ, 1 ≤ X →
        (((Finset.Icc 1 ⌊X⌋₊).filter (fun N => ∀ m, X ^ θ < ((col^[m] N : ℕ) : ℝ))).card : ℝ) ≤
          2 ^ tstarExponent * K * X ^ (1 - θ * tstarExponent))

noncomputable def Collatz.colMin (N : ℕ) : ℕ := sInf (Set.range fun m => col^[m] N)
theorem Collatz.lt_colMin_iff (b : ℝ) (N : ℕ) : b < (colMin N : ℝ) ↔ ∀ m, b < ((col^[m] N : ℕ) : ℝ)
theorem Collatz.colMin_lt_iff (y : ℝ) (N : ℕ) : (colMin N : ℝ) < y ↔ ∃ m, ((col^[m] N : ℕ) : ℝ) < y
```

- `nd_density_one` is Corollary 1.2 (ii): if $f(N) \to \infty$, the set of $N$ whose orbit goes below $f(N)$ has
  natural density 1.
- `nd_collatz_corollaries` contains the main theorem (first conjunct) and Corollary 1.2 (i) and (iii) with the same
  constant `K`.
- `colMin` is $\mathrm{Col}_{\min}(N) = \min_{m \ge 0} \mathrm{col}^m(N)$, and `lt_colMin_iff`,
  `colMin_lt_iff` translate the inequalities of the statements into inequalities for `colMin`.

Correspondence with Corollary 1.2 of the paper. $\mathrm{Col}_{\min}(N) > b$ is written `∀ m, b < col^[m] N` and
$\mathrm{Col}_{\min}(N) < y$ is written `∃ m, col^[m] N < y`; `lt_colMin_iff` and `colMin_lt_iff` show that these are
equivalent to the same inequalities for `colMin N` $= \min_{m \ge 0} \mathrm{col}^m(N)$. In
`nd_collatz_corollaries` the first conjunct is the main theorem, so the constant $K$ of (i) and (iii) is the constant
of the main theorem, and $c' =$ `tstarExponent`.

- (i) is the second conjunct: for every $N_0 \ge 1$, the ratio $E(X, N_0)/X$ ($X \in \mathbb{N}$), where $E(X, N_0)$
  is the number of $1 \le N \le X$ with $\mathrm{Col}_{\min}(N) > N_0$, is bounded above and its `limsup` is at most
  $K N_0^{-c'}$.
- (ii) is `nd_density_one`: if $f(N) \to \infty$, then the proportion of $1 \le N \le X$ with
  $\mathrm{Col}_{\min}(N) < f(N)$ tends to 1 as $X \to \infty$ through the integers, i.e. the set of $N \ge 1$ with
  $\mathrm{Col}_{\min}(N) < f(N)$ has natural density 1 (`f : ℕ → ℝ`).
- (iii) is the third conjunct, for every $\theta > 0$ (the paper states $\theta \in (0, 1]$) and every real
  $X \ge 1$, counting $1 \le N \le \lfloor X \rfloor$; for an integer $X$ this is the statement of the paper.

## What is and is not verified

**Checked by the Lean kernel.** The theorems `nd_collatz_uniform_explicit`, `nd_collatz_uniform`,
`tstarExponent_eq`, `tstarExponent_pos`, `nd_collatz_corollaries`, `nd_density_one`, `lt_colMin_iff`,
`colMin_lt_iff`, and the fixed-barrier counts `fixedBarrier_failure_count_rate`, `fixedBarrier_failure_count` and
`fixedBarrier_failure_count_explicit`, together with their whole dependency closure: the files of this repository,
the imported formalizations of Mazur and Shaik (including `FixedBarrier.lean` from the patch), and Mathlib. There is
no `sorry` and no project axiom.

**Hypotheses.** None of these theorems has a hypothesis; the statements above are complete as displayed. The assembly
in `CollatzND/Core/Uniform.lean` is proved under the hypothesis `FixedBarrierHyp` (the fixed-target form of Theorem 5.3
of Shaik's manuscript), and `CollatzND/Core/ShaikBridge.lean` proves that hypothesis (`fixedBarrierHyp_holds`) from
`fixedBarrier_failure_count`; it does not remain in the final theorems.

**Axioms.** `#print axioms` reports only `[propext, Classical.choice, Quot.sound]` (the three axioms used throughout
Mathlib) for `nd_collatz_uniform_explicit`, `nd_collatz_uniform`, `tstarExponent_eq`, `tstarExponent_pos`,
`fixedBarrier_failure_count_explicit`, `fixedBarrier_failure_count` and `fixedBarrier_failure_count_rate`
(see `verify/stmt-2026-09-26.log`), and for the theorems `nd_density_one`, `nd_collatz_corollaries`,
`lt_colMin_iff` and `colMin_lt_iff` of Corollary 1.2 (see `verify/density-2026-09-27.log`). An explicit hypothesis
is not an axiom: `#print axioms` lists axioms only, so a hypothesis would not appear in its output but in the
statement itself; here the statements have none.

**What rests on the written proof or on reading.**

- The correspondence between the Lean statements and the statements of the paper (see the correspondence notes
  above). The specification tests in `CollatzND/Spec.lean` (`decide`/`rfl` only) check on small values that `col`,
  the predicate `∀ m, N0 < col^[m] N` and the counts have the intended meaning.
- No published theorem is transcribed into a hypothesis here; the external results enter as theorems of the imported
  formalizations, which the kernel checks. These formalizations correspond to preprints that have not been refereed:
  the kernel certifies their statements as written, not that they express the intentions of the manuscripts, so the
  attribution of ingredients to the manuscripts (for example Theorem 5.3 of Shaik's manuscript, or Section 3 of Tao's
  paper in Mazur's formalization) rests on reading.
- The explicit constants: the formalization contains the closed forms and $c' > 0$; the decimal values quoted in the
  paper ($t$, $\mathrm{fbRate}$, $c_B$, $c'$, $K_1$) are recomputed by `verify/constants.py` in floating point and
  are not formalized.
- The comments of the Lean sources were translated from Japanese; a script in the source repository confirms that the
  code differs from the checked originals only in comments.

**Review.** This work has not yet been reviewed by independent human experts; no human mathematician has reviewed the
proofs.

## Repository layout

This repository contains exactly the **closure of the main theorem and of Corollary 1.2**: every declaration of this
project in `CollatzProof/Core/` and `CollatzND/Core/` (110 declarations) lies in the dependency closure of the main
theorem, of the two lemmas `tstarExponent_eq`, `tstarExponent_pos` stated in the paper, of the two theorems
`nd_collatz_corollaries`, `nd_density_one` that formalize Corollary 1.2, or of the two lemmas `lt_colMin_iff`,
`colMin_lt_iff` that relate their statements to $\mathrm{Col}_{\min}$ (checked by a script; see
`verify/density-2026-09-27.log`). Earlier results of the same project (other bounds, earlier development paths) are
not included; they remain in the source repository.

| Path | Content |
|---|---|
| `CollatzND/Core/` | Main development. `Bridge.lean` (bridge to Mazur's one-step recursion), `Main.lean` (orbit minima and counts), `Col.lean` (the Collatz map, reduction to odd starting points), `Power.lean` (windows to dyadic blocks, top conversion), `Uniform.lean` (assembly of the uniform power saving from a fixed-barrier hypothesis), `ShaikBridge.lean` (discharging that hypothesis with the fixed-barrier count; `nd_collatz_uniform`), `Explicit.lean` (explicit exponent, `K > 0`; `nd_collatz_uniform_explicit`), `Density.lean` (Corollary 1.2: upper density, natural density one, the barrier `X^θ`; `nd_collatz_corollaries`, `nd_density_one`, and `colMin` with `lt_colMin_iff`, `colMin_lt_iff`). |
| `CollatzProof/Core/` | Supporting library: the shortcut map (`Defs`), orbit-minimum counts (`Recursion`, `Step`), the Syracuse map (`Syr`), logarithmic windows and Tao's recursion in the form used here (`TaoDefs`, `TaoRec`, `TaoFinal`), windows versus dyadic shells (`Conv`). |
| `CollatzND/Spec.lean` | Specification tests of the statement (`decide`/`rfl` only): values of `col`, truncated counts against a brute-force computation, the cases `N0 = 0` and `N0 = 1`. |
| `patches/shaik-v4.30.patch` | Port of Shaik's formalization to Lean v4.30.0-rc2 and the new file `FixedBarrier.lean` (see License and Attribution). |
| `fetch_mazur.py`, `fetch_shaik.py` | Download the external formalizations and check SHA-256 hashes. |
| `lakefile.toml`, `lake-manifest.json`, `lean-toolchain` | Lake configuration; Lean and Mathlib versions (see Versions). |
| `verify/` | `Replay.lean` (independent kernel replay, with a tampered positive control), `Stmt.lean` (statements, definitions and axioms), `constants.py` (decimal values of the constants; the decimals are not formalized), the logs of 2026-09-26, and the logs of 2026-09-27 for Corollary 1.2. |
| `LICENSE`, `NOTICE` | Apache License 2.0 and the attribution notices (see License). |
| `MANIFEST.sha256` | SHA-256 of every file in this repository (except itself). |

## Building and checking

Requirements: [elan](https://github.com/leanprover/elan) (the toolchain in `lean-toolchain`, Lean v4.30.0-rc2, is
installed automatically), `git`, `patch`, Python 3 (standard library only). In the root directory of a clone of this
repository:

```sh
sha256sum -c MANIFEST.sha256    # optional: compare the files with the recorded SHA-256 hashes
python3 fetch_mazur.py          # Mazur's formalization -> vendor/mazur   (ZIP and per-file SHA-256 checked)
python3 fetch_shaik.py          # Shaik's formalization -> vendor/shaik   (commit and 25 patched files checked)
lake exe cache get              # Mathlib v4.30.0-rc2 cache
lake build                      # CollatzND.Core.* and CollatzND.Spec
lake env lean verify/Stmt.lean                          # statements, definitions and axioms
lake env lean --run verify/Replay.lean                  # independent kernel replay (about 1 minute)
lake env lean --run verify/Replay.lean tamper           # positive control: must be rejected
lake env leanchecker --fresh CollatzND.Core.Explicit    # re-check every declaration incl. Mathlib (30+ minutes)
python3 verify/constants.py                             # decimal values of the constants
```

The external formalizations are not redistributed here; the fetch scripts download them from their original
locations and verify them by hash:

- L. Mazur, *Natural-density Collatz descent in logarithmic time*, Lean formalization hosted by ProofAtlas,
  commit `ca3dd0d63920411213403092aecc6946619eb082`, ZIP SHA-256
  `5761e6bdad1284275f3a19aa51d8278a68b19cb569c516c20df956e6fac91864` (Apache-2.0).
- I. A. Shaik, *FirstPassageLinearTransport* (formalization accompanying *Polylogarithmic Descent for Almost All
  Collatz Orbits in Natural Density*), <https://github.com/shaikidris/FirstPassageLinearTransport>, commit
  `7239f88d05d8262d4778f3c46f4560905052872f` (Apache-2.0).

## Versions

Lean v4.30.0-rc2, Mathlib tag v4.30.0-rc2 (pinned by `lake-manifest.json`). This release candidate is the version of
Mazur's formalization; Shaik's formalization (written for Lean v4.15.0) is ported to it by
`patches/shaik-v4.30.patch`. A rebuild on a stable Lean release has not been done.

## Verification records

The records of 2026-09-26 predate `CollatzND/Core/Density.lean` and cover the main theorem; the corollary file is
covered by the records of 2026-09-27 (last two items). In the logs, "bundle" refers to the files of this repository
at the time of the record.

- `verify/replay-2026-09-26.log`: the dependency closure of the main theorem, of `nd_collatz_uniform`,
  `tstarExponent_eq`, `tstarExponent_pos` and of `fixedBarrier_failure_count` has 64,836 constants; the 8,114 constants
  outside Mathlib (7,539 from Mazur's formalization, 401 from Shaik's formalization including `FixedBarrier.lean`,
  81 + 92 from this project, 1 other) are replayed with the kernel into an environment containing only Mathlib; the
  replay succeeds and the replayed statements coincide with the originals.
- `verify/replay-tamper-2026-09-26.log`: positive control. Replacing the proof of
  `fixedBarrier_failure_count_timed_rate` (the substantive proof of Theorem A) by `True.intro` is rejected by the kernel.
- `verify/stmt-2026-09-26.log`: statements (fully elaborated), definitions and axioms.
- `verify/fresh-build-2026-09-26.log`: a fresh copy of this bundle: both fetch scripts verified the external
  formalizations by SHA-256, and `lake build` succeeded (the Mathlib packages were copied from a local build of the
  same Mathlib tag instead of `lake exe cache get`).
- `verify/leanchecker-fresh-2026-09-26.log`: `lake env leanchecker --fresh CollatzND.Core.Explicit`, run in that fresh
  copy, re-checks every declaration of the closure, including Mathlib, in the kernel.
- `verify/density-2026-09-27.log`: Corollary 1.2, in a copy of this bundle. `lake build` rebuilt all 17 modules of
  the bundle (`CollatzND.Core.Density` with no message). The log records the statements of `nd_density_one`,
  `nd_collatz_corollaries`, `lt_colMin_iff`, `colMin_lt_iff` and their axioms (the three above), and a closure check
  (the script is included in the log): every declaration of the project modules loaded with `CollatzND.Core.Density`
  lies in the dependency closure of the main theorem, `nd_collatz_uniform`, `tstarExponent_eq`, `tstarExponent_pos`,
  `fixedBarrier_failure_count`, `nd_collatz_corollaries`, `nd_density_one`, `lt_colMin_iff` and `colMin_lt_iff`,
  apart from the equation lemma `Collatz.A.eq_1`, which `unfold`/`simp` generate on demand.
- `verify/leanchecker-fresh-2026-09-27.log`: `lake env leanchecker --fresh CollatzND.Core.Density`, run in the source
  repository; its closure contains the main theorem and Corollary 1.2, and every declaration of it, including Mathlib
  and the imported formalizations of Mazur and Shaik, is re-checked in the kernel (exit code 0).

## License

The Lean code and scripts in this repository are licensed under the Apache License, Version 2.0 (see `LICENSE`).

Third-party components:

| Component | Use in this repository | Copyright | License |
|---|---|---|---|
| Mathlib (<https://github.com/leanprover-community/mathlib4>, tag v4.30.0-rc2) | Dependency fetched at build time by Lake (not included) | Individual authors (stated per file) | Apache-2.0 |
| Lake dependencies of Mathlib (Batteries, Aesop, Qq, ProofWidgets, Plausible, LeanSearchClient, ImportGraph, lean4-cli), pinned in `lake-manifest.json` | Dependencies fetched at build time by Lake (not included) | Stated in each package | Apache-2.0 (lean4-cli: MIT) |
| L. Mazur, *Natural-density Collatz descent in logarithmic time*, Lean formalization (ProofAtlas, commit `ca3dd0d`) | Dependency fetched at build time by `fetch_mazur.py` (not included), used unchanged | Copyright 2026 Advameg, Inc. | Apache-2.0 |
| Formal Conjectures material contained in Mazur's formalization | Fetched with it by `fetch_mazur.py` (not included), used unchanged | Copyright 2025 The Formal Conjectures Authors | Apache-2.0 |
| I. A. Shaik, *FirstPassageLinearTransport* (<https://github.com/shaikidris/FirstPassageLinearTransport>, commit `7239f88`) | Original files fetched at build time by `fetch_shaik.py` (not included); patch included: `patches/shaik-v4.30.patch` is a derivative work (modified files and the new file `FixedBarrier.lean`) | Copyright (c) 2026 Idris Ali Shaik | Apache-2.0 |

`patches/shaik-v4.30.patch` modifies 19 of the 24 files taken from Shaik's formalization (the port from Lean v4.15.0
to v4.30.0-rc2; no theorem or definition statement is changed, only proofs and notation) and adds the new file
`FixedBarrier.lean`; the patch header states these changes, and the copyright notices in the headers of the original
files are retained. No other file of this repository is derived from third-party code: the Lean files in
`CollatzND/` and `CollatzProof/` use the formalizations of Mazur and Shaik only through `import` and references to
their declarations. The attribution notices are collected in `NOTICE`.

The paper itself is not part of this repository; it is distributed on Zenodo (doi:10.5281/zenodo.22986670) under the
license stated there.

## How to cite

```bibtex
@misc{nashida2026fixedbarrier,
  author    = {Hiroyuki Nashida},
  title     = {A power-saving bound, uniform in the endpoint, for Collatz orbits that stay above a fixed barrier},
  year      = {2026},
  publisher = {Zenodo},
  doi       = {10.5281/zenodo.22986670},
  url       = {https://doi.org/10.5281/zenodo.22986670},
  note      = {Preprint}
}
```

## Attribution and the role of AI

- The one-step recursion (Tao's Section 3 in natural density), the top conversion, and the Rhin-type phase gap
  are theorems of Mazur's formalization, used unchanged.
- The ingredients of the fixed-barrier count (re-certification runs, rank-scaled loss, terminal profile,
  entropy estimates) are theorems of Shaik's formalization, used unchanged apart from the port to Lean v4.30.
- `FixedBarrier.lean` (in the patch) was assembled by this project from those lemmas. It is a fixed-target
  counterpart of the estimate behind Theorem 5.3 of Shaik's manuscript and is **not** a theorem of the manuscript
  or a declaration of Shaik's repository.
- All Lean code of this project (`CollatzND/`, `CollatzProof/`, `FixedBarrier.lean`, the port) was written with
  Anthropic Claude models through Claude Code, directed by the author, and checked by the Lean kernel; the kernel
  check does not depend on how the code was produced. No human mathematician has reviewed the proofs.
- The comments were translated from Japanese; some of them use internal labels and numbering of the project's
  working documents rather than the numbering of the paper, and some refer to files of the source repository that
  are not part of this repository. A script in the source repository confirms that the code differs from the checked
  originals only in comments.
