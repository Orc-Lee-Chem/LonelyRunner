# Uniform-gap machine acceptance

Status: prepared workflow. No GitHub Actions run or official Comparator
acceptance is claimed by these preparation tests.

The workflow runs on pushes to publication/uniform-gap-e6888. It does not
require merging the draft PR or registering workflow_dispatch on main.
Both positive targets are compared in one official Comparator invocation,
using its Lean kernel and its nanoda integration on the same export.
Each of four negative controls gets a new project directory.

## Inputs and trust

Candidate fingerprint:
befdb0a4d53dd27f1a62e01f7e9c6ad5be3ae91569fde001bd3cca2040cb4c78.
All 263 build inputs and 16 frozen inputs are checked before compilation.
Only hash-listed Lean files enter the execution tree.

The reference payload was extracted from the independently supplied acceptance
ZIP with SHA-256:
68c5304afabf79dcb043ff7c9360dd94de3edb7a05d9565735f58128f5128947.
Its original provenance metadata was excluded from the distributable copy.
The exact 16 frozen file bytes and original manifest bytes are preserved.
The manifest hashes to:
58caccd663f20dc987be5b769f4fd348aeb2f81f28b2b1058645a5b923df91c7.
This reconstructs the supplied specification; it is not a newly authored or
independently human-reviewed specification.

The workflow and runner are operator-side trusted code and require review.
Before executing Python in isolated mode, the workflow checks the runner and
payload manifest. Failed integrity verification cannot execute finalization.
Expected fingerprints are not accepted from a candidate's proposed policy.

## Runtime configuration

Frozen source files remain unchanged in the source snapshot. The temporary
acceptance project derives its TOML from the frozen root configuration, adding
resource arguments -j1 -M12288 -DElab.async=false and libraries for Challenge,
Solution, and AllSource. AllSource imports all 261 source/validation modules.
The derived execution configuration has its own recorded checksum; it is not
described as an unchanged frozen configuration.

The comparison JSON adds only enable_nanoda=true. Theorem names, definition
holes, and the three permitted axioms remain unchanged.

An auditable native Lake launcher sets LEAN_NUM_THREADS=1 and execs the
unchanged official Lake executable. It controls Lake parallelism even when
Comparator filters its child's environment. It does not replace Landrun,
Comparator, Lean, or a proof checker.

## Isolation and sequence

The job requires an unprivileged user, Landlock ABI >=6, a real systemd user
manager and AF_UNIX restriction. It tests protected-file write denial and
AF_UNIX denial. Missing prerequisites mean BLOCKED_NOT_RUN, never an expected
semantic rejection.

Challenge is compiled and exported before candidate Lean code runs in that
project. Compilation/export is sandboxed, with only that project's .lake
writable. Trusted external caches are outside this write tree.
The positive project is not reused for a later comparison. Negative projects
do not import the mathematical core.

After positive and negative gates, all modules are built through AllSource and
the original default target. Bundled leanchecker --fresh is then run read-only
on LonelyRunnerValidation.FinalSolution with a 90-minute limit. Four fully
explicit final types and their axioms are printed.

## Evidence

Every child command records its actual command, exit code, timing, raw log and
checksum. Evidence is uploaded after every major stage. Project caches from
earlier CI runs are not reused; only locked external dependency caches are
downloaded.

Expected negatives require both builds and exports to reach comparison,
nonzero Comparator exit, and the correct semantic diagnostic. A missing
sandbox, compiler failure, timeout, or accepted negative cannot count.
Positive acceptance requires both kernels and the official final message.

Machine completion requires all machine gates. Final acceptance remains false
pending independent human semantic/manuscript review. Author and license
confirmation remain separate.

Protocol: Comparator README at d03acab154d269c06e60e4de7e4cc85deebff94b.
Runner specifications:
https://docs.github.com/en/actions/reference/runners/github-hosted-runners

CI resource correction: run 42174160139 actually reported Lean interpreter memory_exception (exit 134) in LCMiddlePrimeData5 and Data6 at 6144 MiB. Only the execution memory ceiling is raised to 12288 MiB, and the ephemeral VM receives 16 GiB additional swap with raw memory records. Source fingerprint, frozen inputs, isolation, kernels, time limits and semantic rejection rules are unchanged. This is not a new successful acceptance claim.

Nanoda diagnostic correction: official Comparator in run 42180024571 returned 0 after both targets and both kernels accepted, but the strict CI classifier rejected missing declaration-count output. The classifier is NOT relaxed. A separate CLI, derived byte-for-byte from the pinned nanoda main except enabling print_success_message, links the unchanged pinned nanoda_lib. It executes the same check_all_declars flow and prints the real count. The original CLI, generated diagnostic source, dependency-lock subset check and both binary hashes are recorded. No checker logic, axiom policy, source fingerprint or isolation is changed.
