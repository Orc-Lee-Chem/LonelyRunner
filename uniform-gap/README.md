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

Fixed source-map SHA-256:
`67008acda1805ce8a67e8557e793b7c91e6d016634d72da04dacc50ace443a9a`.
The [source checkpoint](https://github.com/Orc-Lee-Chem/LonelyRunner/tree/c1bee1c802624725dfeefef8dc9fb22b5ee886f7/uniform-gap)
is preserved; this publication update changes documentation only.
See [pinned-source-version.json](pinned-source-version.json) and
[the frozen manifest](validation/frozen-v1.sha256.json).

The four final declarations are `LonelyRunnerNew.lonely_runner_gap`,
`LonelyRunnerNew.frozen_target_proved`, `LonelyRunnerAcceptance.explicit_gap`
and `LonelyRunnerAcceptance.uniform_gap`. The independent direct statement is
[`LonelyRunnerSpec.V1.Statement`](LonelyRunnerSpec/V1.lean).

## Acceptance status (2026-11-05)

| Check | Actual status and scope |
| --- | --- |
| Fixed sources and frozen files | PASS: all 234 source/build inputs and all 16 frozen files match. |
| Manuscript correspondence | Completed statement/appendix checks: six bootstrap rows and 34 small-prime rows; supplied TeX/PDF bytes preserved. This is limited agent/script review, not independent human review of every argument. |
| Historical Lean source rebuild and fresh replay | Passing records exist for the same fixed source version: 228 project modules and official bundled leanchecker fresh replay, exit 0; locked external library cache reused. |
| Historical nanoda | Passing standalone check of 60,675 exported declarations, exit 0, for the same fixed source/export; not a Comparator result. |
| Existing-artifact final types/axioms | Print command exited 0; only propext, Classical.choice and Quot.sound were reported for all four final declarations. |
| Publication-candidate clean rebuild | RESOURCE BLOCKED / INCOMPLETE. A single-compiler -j1 attempt was stopped by its resource guard; FinalSolution and new-output checks were not reached. |
| Formal Comparator explicit_gap and uniform_gap | Both NOT RUN. |
| Four formal Comparator negative controls | All NOT RUN: weaker target, changed definition, sorry dependency and extra premise. No expected rejection has been observed. |
| Final acceptance | PENDING. Historical kernel checks do not replace the outstanding checks. |

The current host lacks a usable Linux systemd/landrun environment. Separate
hash-matched acceptance references have been prepared, but actual Linux
isolation/write protection and pinned-tool compatibility remain untested.
Read the [redacted acceptance summary](audit/PublicationStatus.md) and
[machine-readable status](audit/AcceptanceSummary.json). The supplied historical
[`AUDIT.md`](AUDIT.md) retains its original review scope and bytes.
Earlier source comments and frozen tool-status fields are historical;
the current summary above does not overwrite them.

## Build and inspect

Use `leanprover/lean4:v4.34.1` and the exact commits in `lake-manifest.json`.
From `uniform-gap/`, on a machine with sufficient resources:

```sh
lake exe cache get
lake build
lake build +LonelyRunnerValidation.FinalSolution
lake env lean -j1 audit/PrintFinalTypes.lean
```

These are reproduction commands, not a claim that the current clean rebuild
completed. No project build objects or raw logs are published. Matching trusted
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
