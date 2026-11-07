# Lonely Runner uniform-gap proof and publication audit

## Statement

For every finite set \(V\) of distinct positive integer speeds with \(n=|V|\ge 2\), a single real \(t\in[0,1)\) satisfies \(|vt-k|>(1+e^{-6888})/(2n)\) for all \(v\in V\) and all \(k\in\mathbb Z\). The paper's maximum of the minimum distance to the nearest integer gives the same assertion. The finite minimum and the nearest integer both exist. The existential time in the frozen statement needs no maximum-attainment hypothesis.

| Item | Evidence and scope |
| --- | --- |
| Frozen statement and final proof | The manuscript theorem, `LonelyRunnerSpec.V1.Statement`, `LonelyRunnerNew.lonely_runner_gap`, and the exported `LonelyRunnerAcceptance.explicit_gap` agree. The proof in `SpilloverInputProved.lean` supplies the proved spillover bound to the adapter with rough block and forest already discharged. The corollary `LonelyRunnerAcceptance.uniform_gap` takes the witness `Real.exp (-6888)`. |
| Audit input | The supplied `LonelyRunnerNew(7).lean` is the import entry point. Its SHA-256 is `fdb21e5c0213997a202736fe6d5a506375e220c43bfd931852def8230623b73f`, matching the pinned root module. This review had 188 of 234 pinned build inputs and all 16 frozen files. It did not rerun a clean build or read the missing 46 pinned files. |
| Prior source and kernel checks | The recorded isolated rebuild of 228 project modules and official fresh Lean replay passed on the pinned source version, with locked external library artifacts reused. The separate nanoda run checked 60,675 exported declarations and printed both targets. Its only reported axioms were `propext`, `Classical.choice` and `Quot.sound`. |
| Independent comparison | The latest Comparator report and raw-log archive match their recorded hashes. Both positive checks and all four negative controls have status `BLOCKED_NOT_RUN`. The earlier tool build was a compatibility check. An independent human review of the full manuscript and formal statement is still pending. |

Pinned source identifier: `67008acda1805ce8a67e8557e793b7c91e6d016634d72da04dacc50ace443a9a`. The accompanying manifest lists the exact file hashes. This audit found no final-statement mismatch or evidence of a proof failure within the scope above.

## Manuscript corrections

- Replaced the erroneous declaration prefix `SpilloverInputProved.lonely_runner_gap` with `LonelyRunnerNew.lonely_runner_gap`, and gave its source file separately.
- Matched the certificate in `DyadicKernelCertificate.lean` by using a non-strict upper bound of 2.137859 for the dyadic kernel. The final theorem remains strict.
- In the saturated sum argument, used the same polynomial comparison as `LonelyRunnerNew.Saturated.fourth_power_bound`. The original derivative proof was a separate derivation of the same estimate.
- Made the spillover radius conditions, integer unit-cell inputs of the Green estimate, and common dyadic grid explicit. The paper sums the block estimates directly, while Lean first selects a block using the same weighted sum.
- Compared all six bootstrap rows against `BootstrapChain.lean` and all 34 small-prime rows against `CertificateData.lean` as exact fractions. The rows agree. Rebuilt the revised TeX twice with pdfLaTeX and inspected the resulting PDF.
- Replaced private bibliography links with the pinned source identifier. Add an accessible source-commit link and confirmed author information at publication time.

The old acceptance report correctly describes the difference between an independent kernel check and formal Comparator acceptance. Several historical source comments still describe prerequisites as pending, including `LonelyRunnerValidation/FinalSolution.lean` and `SpilloverEndpointAssembly.lean`. The final proof supplies those results. Preserve the pinned bytes and clarify the status in the release documentation.

## Repository layout

Use a separate `uniform-gap/` Lake project in the existing repository `Orc-Lee-Chem/LonelyRunner`. The public `main` checked for this audit was commit `4f42d5a9d01d468a7e49537850b0b32a3154d259`. The existing `SemanticCheck.lean` proves a gain of \(1/(2n^{3/2+\kappa})\) for all sufficiently large \(n\), for every \(\kappa>0\). The new gain of \(e^{-6888}/(2n)\) is uniform for \(n\ge2\). Preserve both results, their build entry points and their manuscripts.
