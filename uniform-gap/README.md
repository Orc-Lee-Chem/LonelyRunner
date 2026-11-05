# Uniform lonely-runner gap with target constant exp(-6888)

This independent Lake project preserves the frozen source version
`67008acda1805ce8a67e8557e793b7c91e6d016634d72da04dacc50ace443a9a`.
The original repository and its asymptotic theorem remain available from the repository root.

For every finite set V of distinct positive integers with n = |V| >= 2, there is
one real t in [0,1) such that, for every v in V and every integer k,
|v*t-k| > (1 + exp(-6888))/(2*n). The constant is independent of V and n.
This is a uniform improvement; it is not the full lonely-runner conjecture.

The final declarations are LonelyRunnerNew.lonely_runner_gap,
LonelyRunnerNew.frozen_target_proved, LonelyRunnerAcceptance.explicit_gap,
and LonelyRunnerAcceptance.uniform_gap. See pinned-source-version.json and
validation/frozen-v1.sha256.json for exact source/frozen hashes.

## Build

Use leanprover/lean4:v4.34.1 and the exact dependency commits in lake-manifest.json.
Run from this directory:

```sh
lake exe cache get
lake build
lake build +LonelyRunnerValidation.FinalSolution
```

Original project build artifacts are not included. Dependency caches may be reused
when their exact locked versions and provenance are checked.

## Publication and acceptance status

See AUDIT.md for the supplied historical review and audit/PublicationStatus.md
for this publication attempt. Existing comments describing earlier prerequisites
are retained to preserve the pinned source bytes; they are not current validation results.
The paper in paper/ is the supplied revised manuscript and PDF, retained verbatim.
No new author or copyright statement has been added. The user requested no author name;
licensing for the new code/manuscript is still pending confirmation. The previous
manuscript's license is not represented here as a confirmed grant for this new manuscript.
Do not publish this local branch until all recorded publication conditions are satisfied.
