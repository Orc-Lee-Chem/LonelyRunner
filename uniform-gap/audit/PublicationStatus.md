# Redacted publication and acceptance summary

Status as of 2026-11-05: **draft research branch; final acceptance pending**.
The user explicitly authorized a branch push and draft PR with the outstanding
checks disclosed. No merge, release tag or final-acceptance claim is authorized.

## Fixed content and checks

The starting checkpoint is `c1bee1c802624725dfeefef8dc9fb22b5ee886f7`.
The source-map SHA-256 remains
`67008acda1805ce8a67e8557e793b7c91e6d016634d72da04dacc50ace443a9a`.
All 234 source/build inputs and all 16 frozen files match their fixed manifests.
The new publication commit changes documentation only; Lean files, certificates,
frozen goals, version locks, supplied AUDIT.md and revised TeX/PDF are unchanged.
The original asymptotic result, old paper and root build entry points are retained.

The completed manuscript correspondence checks cover positive distinct integer
speeds, n >= 2, a single time in [0,1), every speed and integer, strict >, the
exponent -6888 and denominator 2n. The six bootstrap rows and the prime/tau/
edgeUpper columns of all 34 small-prime rows agree as exact fractions. Two
pdfLaTeX validation passes exited 0 and normalized text matches the supplied PDF.
This is agent/script review, not independent human semantic review or validation
of every manuscript argument. The supplied AUDIT.md's original review inspected
188 of 234 pinned inputs; it is not silently relabeled as a full-source review.

## Historical and current evidence are distinct

| Check | Result |
| --- | --- |
| Historical isolated source rebuild | Passing records for 228 project modules; the same input hashes were rechecked. Locked external library artifacts were reused, not all mathlib rebuilt. |
| Historical official Lean fresh replay | `lake env leanchecker --fresh LonelyRunnerValidation.FinalSolution`, exit 0, recorded for the fixed development. |
| Historical nanoda | Standalone independent-kernel check passed, exit 0, 60,675 declarations; both final acceptance targets printed. Its source/export binding is retained below. |
| Existing-artifact final type/axiom inspection | Exit 0 for all four final declarations; only propext, Classical.choice and Quot.sound. This is not the new clean rebuild. |
| Publication-candidate clean rebuild | Incomplete: resource wrapper stopped a single-compiler -j1 attempt while compiling LCMiddlePrimeData7, exit 1. Commit headroom remained below 1.5 GiB. No Lean native OOM or compilation error was observed before the guard stopped the tree. |
| Publication-candidate FinalSolution and new-output types/axioms | NOT RUN after that block. |
| Formal Comparator: explicit_gap | NOT RUN. |
| Formal Comparator: uniform_gap | NOT RUN. |
| Negative: weakened target | NOT RUN; no actual statement-mismatch rejection recorded. |
| Negative: changed definition | NOT RUN; no actual definition/type-mismatch rejection recorded. |
| Negative: sorry dependency | NOT RUN; no actual illegal-sorryAx rejection recorded. |
| Negative: extra premise | NOT RUN; no actual extra-premise/type-mismatch rejection recorded. |

Historical nanoda commit: `8de7e0c4ed3052745a7f8725164efd9e76d84c56`.
Checked export SHA-256:
`7446f910cc05d34af2df4ef8e01fe1ae6734f4d2909abcd5bf5d7799ac6ed221`.
Its axiom policy was propext, Classical.choice, Quot.sound. This was a standalone
kernel check, not comparison with an independently held challenge.

The current host has no usable Linux systemd/landrun environment. Hash-matched
reference files have been prepared separately and an ordinary readonly write
test was denied. Actual Linux sandbox enforcement, pinned Comparator/exporter
compatibility, both positive targets and the four semantic negative diagnostics
remain outstanding. Environment/startup failures cannot count as expected
negative rejections. Earlier local preflight tests are not these formal controls.

See [AcceptanceSummary.json](AcceptanceSummary.json) for the redacted structured
record. Raw logs, machine paths, usernames, private configuration, build caches
and binaries remain outside this published tree. Historical evidence is retained
privately; its passing records are not a claim of third-party reproduction.

## Authorship and licensing remain open

The new author field remains intentionally empty at the user's request. Final
author/affiliation information is unconfirmed. The new code and manuscript
licenses are unconfirmed. Existing license files and old-material grants are
unchanged; they are not used here as a substitute for new-material confirmation.
The revised manuscript and supplied audit are preserved verbatim. A source
checkpoint link is supplied in the README; no manuscript link/edit or new
attribution/license is invented for this draft.

Technical final acceptance, authorship and license confirmation are still needed
before a final release. This research draft does not assert the full lonely-runner
conjecture or waive any outstanding acceptance requirement.
