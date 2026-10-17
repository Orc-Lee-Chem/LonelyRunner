# LonelyRunner

Lean 4 formalization and English manuscript for **Short Integer Relations and
Near-Covering Structure in the Lonely Runner Problem**, by Cheng Li.

## Main result and scope

For every real `κ > 0`, there is a natural number `N ≥ 2` depending only on `κ`
such that every finite set `V` of distinct positive integers with `m = |V| ≥ N`
admits one real time `t ∈ [0,1)` satisfying, simultaneously for every `v ∈ V`
and every integer `k`,

$$|vt-k|\ge\frac{1}{2m}+\frac{1}{2m^{3/2+\kappa}}.$$

There is no velocity-height bound, covering, irreducibility, gcd, dimension,
or model assumption in the final theorem. The threshold is existential and
depends on `κ`. This is an asymptotic improvement at the stated scale;
it is **not a full solution of the Lonely Runner Conjecture**.

- English paper: [PDF](paper/lonely_runner_en.pdf) · [TeX source](paper/lonely_runner_en.tex).
- Circle theorem: [`LonelyRunner.mainTheorem`](LonelyRunner/MainTheorem.lean).
- Ordinary real formulation: [`LonelyRunner.mainTheorem_real`](SemanticCheck.lean).
  Its proof actually selects a representative in `[0,1)` and compares circle
  distance with distance to every integer.

The development proves the weak GCD bound needed here by finite Poisson moments.
It does not formalize the refined Bondarenko–Seip exponential estimate or Bedert's
small-height theorem in its full original height range. The paper also contains
discussion for which no corresponding Lean theorem is claimed. Kernel checking
certifies the formal statements present in the released source.

## Pinned toolchain and building

- Lean: `leanprover/lean4:v4.34.1`.
- Mathlib: `v4.34.1`, exact commit
  `d13f23b723b8a846827a245b89c10fc7d3f11612`.
- All transitive revisions are fixed by [`lake-manifest.json`](lake-manifest.json).

Install elan and Git, clone this repository, then run from its root:

```sh
lake env lean --version
lake exe cache get
lake build
lake env lean SemanticCheck.lean
```

The semantic-check file prints the complete main theorem and real formulation,
then prints the axioms of these and its two semantic-transfer lemmas. Expected:

```text
[propext, Classical.choice, Quot.sound]
```

Large Tablet geometry files can require substantial memory. To limit concurrency,
set `LEAN_NUM_THREADS=1` (PowerShell: `$env:LEAN_NUM_THREADS = '1'`) before building.
No dependency upgrade or `lake update` is needed. Mathlib caches are optional;
the repository contains no `.lake` or compiled Lean artifacts.

To regenerate the English PDF, run twice from `paper/`:

```sh
pdflatex -interaction=nonstopmode -halt-on-error lonely_runner_en.tex
pdflatex -interaction=nonstopmode -halt-on-error lonely_runner_en.tex
```

Rerun if LaTeX requests another reference pass. The published PDF required a third
pass to stabilize references; see [the build record](audit/ManuscriptBuild.md).

## Verification status and provenance

On 2026-10-17, a frozen copy was rebuilt in a newly created directory **on the
original computer**. Only fixed Mathlib/transitive dependency caches were reused;
all 609 Tablet and 71 LonelyRunner source modules were recompiled. With an
audit-only all-module import driver and the root targets, the build completed
successfully with **9608 jobs**, exit code 0. The real semantic check also exited 0.
Actual axiom checks for the main theorem, its real formulation and both semantic
conversion lemmas returned only `propext`, `Classical.choice`, `Quot.sound`.

This is **not third-party independent reproduction or peer review**. It also
does not certify every statement in the manuscript. The original 9608-job count
includes the private audit-only import driver; a normal `lake build` of this
release need not report that same job count.

Current Lean sources/configuration were compared to that snapshot before
publication: all 686 build-input files matched. Publication adds only a comment
notice to the 76 modified upstream Tablet files to identify the compatibility
port; the bytes below each notice match the audited file exactly. No mathematical
proof, theorem statement, definition, toolchain or dependency was changed.

See [`audit/README.md`](audit/README.md) for the distinction between the original
private audit, its explicitly redacted public excerpt, and release-specific hashes.

## Upstream ST formalization and licenses

Tablet comes from [wpegden/crossing-consequences](https://github.com/wpegden/crossing-consequences),
upstream commit `8769d142033fce042f502bf2857afb6b1375b5c3`.
It was ported from Lean `v4.30.0-rc2` to the pinned `v4.34.1` environment.
The final non-weighted ST theorem uses 589 Tablet modules; all 609 upstream-port
modules are included. See [`Tablet/PORTING.md`](Tablet/PORTING.md), the
[per-file porting record](docs/STPortChanges.md), and the original, verbatim
[`Tablet/LICENSE`](Tablet/LICENSE).

Original project code/documentation: [Apache-2.0](LICENSE).
English TeX/PDF: [CC-BY-4.0](LICENSES/CC-BY-4.0.txt), attribution to Cheng Li.
Third-party content retains its own license; see [NOTICE](NOTICE).

## AI assistance

ChatGPT and Codex were used to assist with manuscript drafting
and revision, English translation, Lean proof development, and
verification workflows. The author is responsible for the final
manuscript and code. Lean kernel checking applies to the formal
statements in the released source; it does not by itself certify
every statement in the manuscript.
