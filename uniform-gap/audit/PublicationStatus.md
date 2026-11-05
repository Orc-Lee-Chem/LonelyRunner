# Publication and acceptance status

This branch is a local publication preparation. It has not been pushed and no PR,
merge or release tag has been created by this workflow.

## Scope and identity

The supplied AUDIT.md is preserved verbatim. Its historical review had 188 of
234 pinned inputs and all 16 frozen files; it did not rerun Lean or Comparator.
This attempt verified all 234 source/build inputs and all 16 frozen files.
Source version: `67008acda1805ce8a67e8557e793b7c91e6d016634d72da04dacc50ace443a9a`.
The proof-source checkpoint for this build is local commit `cbdd4634ace19e79a704433173a2686ebfe09b2b`.
Additional publication documentation does not change any pinned mathematical source.
The pre-existing asymptotic result, old paper and original root build entry points
are retained. Only a navigation section is added to the repository root README.

## Actual checks in this attempt

| Check | Actual result |
| --- | --- |
| Source/frozen hashes | PASS: 234 source inputs and 16 frozen files match. |
| Git exact-byte handling | PASS: -text checked; committed source/frozen bytes checked in a clean worktree. |
| Clean Lean build | FAILED OR INCOMPLETE: see private execution receipts; no build success is asserted. |
| Final types and axioms | Cached pinned-project print command exited 0 and reported only propext, Classical.choice and Quot.sound for all four declarations. Clean-publication-build validation remains incomplete. |
| Paper statement review | Quantifier scope, one common time, positive speeds, n >= 2, strict inequality, exponent -6888 and denominator 2n checked against the frozen target. This is agent/script review, not independent human semantic review. |
| Appendix rows | PASS: all six bootstrap rows and the prime/tau/distance columns of all 34 small-prime rows match Lean as exact fractions. |
| Revised manuscript rebuild | PASS: pdfLaTeX pass exits [0, 0]; normalized PDF text matches the supplied PDF: True. Supplied TeX/PDF bytes retained. |
| Export / independent kernel | INCOMPLETE OR FAILED: the new export/kernel condition has not passed. |
| Comparator explicit_gap | NOT RUN: no usable Linux isolation environment. |
| Comparator uniform_gap | NOT RUN: no usable Linux isolation environment. |
| Negative: weakened target | NOT RUN; expected statement mismatch is not observed. |
| Negative: changed definition | NOT RUN; expected statement/dependent-definition mismatch is not observed. |
| Negative: sorry dependency | NOT RUN; expected illegal sorryAx rejection is not observed. |
| Negative: extra premise | NOT RUN; expected statement mismatch is not observed. |

The Windows environment probes found no usable systemd user manager/landrun.
A missing process or build failure is not counted as an expected negative rejection.
Independent acceptance-side frozen inputs still need to be provided, authenticated
and protected on the Linux checker. Bundled references alone are not independent provisioning.
No fake-landrun or unsandboxed Comparator substitute is reported as acceptance.

## Reproduce the local project checks

Use the locked Lean 4.34.1 and exact lake-manifest.json commits, then from uniform-gap:

```sh
lake exe cache get
lake build
lake build +LonelyRunnerValidation.FinalSolution
# Fresh final type/axiom check still required
```

All project build artifacts were generated in this attempt from the committed source;
fixed trusted external dependency caches were reused. This does not claim rebuilding
all of mathlib from source or official adversarial Linux isolation.
Private raw command logs and host paths are retained outside the publication tree.

## Publication conditions still open

Author name: intentionally omitted per the user's instruction; no new attribution is invented.
New code/manuscript license: not confirmed. The old paper's grant is not treated as
confirmation for the new manuscript.
Accessible source-commit link in the paper: pending authorized publication. No local-only
commit is described as a currently accessible GitHub permalink. The supplied paper and
AUDIT.md remain byte-identical; final link insertion and paper recompilation await that step.
Formal Comparator positives and all four negative rejection diagnostics: still required.
These open conditions prevent push/PR/release. Kernel success does not replace them.

The print helper audit/PrintFinalTypes.lean was executed against the existing artifacts
of the original hash-matching pinned project. This records actual final types/axioms,
not a successful source-clean publication rebuild. Root lake build exited 1 after
the 768 MiB free-memory/commit guard stopped its owned process tree. The requested
FinalSolution build in that clean worktree was not reached and has no exit code.
