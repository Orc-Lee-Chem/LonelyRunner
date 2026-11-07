# Uniform lonely-runner gap: exp(-6888)

**Draft research branch. Final acceptance is pending.**

This independent Lake project contains the fixed-source development and supplied
revised English [paper (PDF)](paper/LonelyRunner_e6888_English.pdf) /
[TeX](paper/LonelyRunner_e6888_English.tex). The original asymptotic result, its
paper and the root Lake entry points remain available unchanged.

For every finite set `V` of distinct positive integers with `n = V.card >= 2`,
there exists one real `t` in `[0,1)` such that, simultaneously for every `v in V`
and every integer `k`,

```text
|v*t-k| > (1 + exp(-6888))/(2*n).
```

The constant is independent of `V` and `n`. This is the stated uniform
improvement, not a proof of the full lonely-runner conjecture.

## Source and frozen specification

Current candidate source-map SHA-256:
`befdb0a4d53dd27f1a62e01f7e9c6ad5be3ae91569fde001bd3cca2040cb4c78`.
The candidate only splits `LCMiddlePrimeData7` into 29 low-memory modules,
with exact reconstruction of all 57 original definition/proof bodies.
The other 233 original inputs and all 16 frozen files are unchanged.
The original [source checkpoint](https://github.com/Orc-Lee-Chem/LonelyRunner/tree/c1bee1c802624725dfeefef8dc9fb22b5ee886f7/uniform-gap)
and [pinned-source-version.json](pinned-source-version.json) are preserved;
see [candidate-source-version.json](candidate-source-version.json) for this version
and [the frozen manifest](validation/frozen-v1.sha256.json).

The four final declarations are `LonelyRunnerNew.lonely_runner_gap`,
`LonelyRunnerNew.frozen_target_proved`, `LonelyRunnerAcceptance.explicit_gap`
and `LonelyRunnerAcceptance.uniform_gap`. The independent direct statement is
[`LonelyRunnerSpec.V1.Statement`](LonelyRunnerSpec/V1.lean).

## Acceptance status (2026-11-07)

All requested machine gates passed in the
[official Linux Actions run](https://github.com/Orc-Lee-Chem/LonelyRunner/actions/runs/42260418491),
on commit `2d0f3ded605f4929e0313fa4edc362064c3a1bd6`.
This documentation update changes no tested proof, specification or CI bytes.

| Check | Actual status and scope |
| --- | --- |
| Source and frozen files | PASS: 263 source/build inputs and all 16 frozen inputs. |
| Clean candidate build | PASS: all 261 source/validation modules, default target and FinalSolution; locked external library cache reused. |
| Official Comparator explicit_gap | PASS. |
| Official Comparator uniform_gap | PASS. |
| Lean and nanoda | Both accept the same Comparator solution export; nanoda checked 60665 declarations. |
| Four negative controls | All rejected after compilation/export for their expected semantic reasons: weaker target, changed definition, sorry dependency and extra premise. |
| Official fresh replay | PASS: full-environment `leanchecker --fresh -v LonelyRunnerValidation.FinalSolution`, exit 0. |
| Final types and axioms | PASS for all four final declarations; only propext, Classical.choice and Quot.sound. |
| Independent human semantic/manuscript review | PENDING; machine acceptance does not replace it. |
| Authorship and new-material licenses | PENDING; existing author field and license files unchanged. |
| Final publication acceptance | PENDING. PR remains draft; no merge or release. |

Actual Linux systemd/Landrun isolation and protected-write/AF_UNIX-denial probes
passed. Runtime TOML resource arguments and the diagnostic-only nanoda CLI are
fully described in the [redacted acceptance summary](audit/PublicationStatus.md)
and [structured status](audit/AcceptanceSummary.json), together with retained
failed-run diagnoses. The checker library and acceptance rules were not relaxed.
The supplied historical [`AUDIT.md`](AUDIT.md) and revised paper are unchanged.
The manuscript correspondence checks retain their stated limited agent/script
scope and are not relabeled as independent human review.

## Build and inspect

Use `leanprover/lean4:v4.34.1` and the exact commits in `lake-manifest.json`.
From `uniform-gap/`, on a machine with sufficient resources:

```sh
lake exe cache get
lake build
lake build +LonelyRunnerValidation.FinalSolution
lake env lean -j1 audit/PrintFinalTypes.lean
```

These are reproduction commands; the actual Linux CI run above records the
completed clean project build. No project build objects or raw logs are published. Matching trusted
external dependency caches may be reused. For limited resources, -j1 is a Lean
compiler option: an external copy of lakefile.toml may add the top-level
`weakLeanArgs = ["-j1"]` without changing the frozen file. Lake itself has no -j1
CLI option in this version. Formal Comparator additionally requires the actual
official Linux isolation flow and its two positives/four negatives.

## Authorship, licenses and draft scope

The new manuscript's author field remains intentionally empty as instructed;
author names, ordering and affiliations remain unconfirmed. No new attribution
is invented. The new code and manuscript licenses are also unconfirmed; the
older material's license grants are not represented as confirmation for the new
materials. Existing license files are unchanged.

The user has explicitly authorized this research-branch push and **draft** PR
with these open items disclosed. This is not final acceptance, permission to
merge, a release, or a declaration that every publication condition is met.
