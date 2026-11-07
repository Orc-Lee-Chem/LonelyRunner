# Manuscript-to-Lean review, 2026-11-07

## Scope and conclusion

This is a model-assisted textual/interface review, not independent human
refereeing and not another execution of Lean. The reviewed snapshot is commit
2d0f3ded605f4929e0313fa4edc362064c3a1bd6 in Orc-Lee-Chem/LonelyRunner,
specifically the separate uniform-gap project. The repository-root paper and
the older result are outside this manuscript revision and remain untouched.

All 263 candidate source/build inputs and all sixteen frozen files were
rehash-verified against the candidate fingerprint
befdb0a4d53dd27f1a62e01f7e9c6ad5be3ae91569fde001bd3cca2040cb4c78.
The whole 45,098-byte uniform-gap TeX source was read. Main proof interfaces
were inspected and 43 source locations with commit-pinned links were mapped.
This is not a claim to have independently reproved every theorem in all 261
modules or recomputed every large-prime interval-certificate entry.

No new blocking mathematical mismatch was found in the inspected main chain.
Five manuscript edits are proposed below. No Lean proof, frozen input,
certificate value, or final theorem is changed.

## Machine evidence already established

GitHub's public API was inspected directly. Run 42260418491 completed with
conclusion success on the exact tested commit. Every reported acceptance
step has conclusion success, including both positive targets, all four
negative controls, full source build, fresh replay and final reporting.

https://github.com/Orc-Lee-Chem/LonelyRunner/actions/runs/42260418491

The user's actual-result report records Lean and nanoda acceptance, 60,665
checked declarations, an actual export digest, full types and the three
permitted axioms. Its raw artifact ZIPs were not independently downloaded in
this review. The exact successful export SHA-256 recorded there is
c2490a10b8b0dfc536336c1b2a3cd46bac643ea7618806468448c1efe0f87764.
This is distinct from older exports with different declaration counts.

The following documentation-only commit was compared through GitHub's API:
edb9175d174b8e39ccf25534f557c6093a6f282f changes only uniform-gap/README.md,
audit/AcceptanceSummary.json and audit/PublicationStatus.md. It is not a new
mathematical source revision.

## Statement and important interfaces

The paper and the frozen specification quantify over every finite set of
positive natural-number speeds of cardinality at least two. A single real
time in [0,1) is selected before all speed and integer-translate quantifiers.
The standard real absolute value and strict inequality have the radius
(1+exp(-6888))/(2*card V). The uniform corollary selects c before V.

The direct final theorem is in SpilloverInputProved.lean; the final acceptance
adapter imports the full project and applies that theorem. There is no
unproved LC/RC, rough-block, spillover or forest premise in the final type.
Historical comments calling intermediate inputs unproved are not the final
dependency status. Their source bytes are deliberately preserved.

The main inspected junctions agree as follows:

- The pair-overlap expression removes the common-center mass 2r/H. The C1
  and C2 normalizations use ordered off-diagonal pairs and the original set's
  fixed radius during deletion. The singleton remainder is covered.
- The ordinary score uses q=201/50=4(1+sigma), sigma=1/200. Its rectangle
  exponent is exactly 3/4. Fourth-power stability is obtained separately.
- GreenVariation.two_sided_variation treats both sides of a maximum with
  absolute integrals and decay, without a monotonicity premise. GreenKernel
  proves the bound on the finite nonnegative integer-unit-cell class used
  in the paper; KernelInputProved eliminates the analytic input premise.
- The fixed larger scale lambda0 is used only to obtain the initial center.
  The actual prime scale is used for the six subsequent steps at that same
  center. Ordinary and fourth-power distributions keep their own stability.
- Large-prime retention is normalized by the same current stable state's
  edge mass. Small-prime coarea uses the actual symmetrized edge marginal pi.
  Stripping has distortion 2750, leaving separation exponent 4130, and the
  rough image is restabilized rather than assumed stable.
- The physical fourth-power bound and ordinary physical bound stabilize
  their own scores. Labeled repeated product heights are counted with their
  multiplicities in the saturated sum.
- The ordinary global dyadic selection uses all edges before applying the
  independently proved physical-block bound. There is no extra parent-level
  27/50 restriction loss to insert into the paper's ordinary global bound.
  The local physical-block argument already includes its own retention.
- The dyadic kernel upper bound is non-strict. The final strict inequalities
  are obtained from the strict scalar comparisons and positive uncovered
  measure, not by changing that kernel certificate to a strict statement.

## Exact data checks performed

The supplied check_paper_data.py performs 301 exact input/table/scalar checks
on both the old and proposed manuscripts. Most are per-file SHA checks; this
number does not count independent mathematical proofs. In particular:

- All six bootstrap rows match BootstrapChain.lean as rational numbers;
  all six stated power certificates pass exact rational arithmetic.
- All 34 small-prime rows match CertificateData.lean, cover exactly the
  primes at most 142, and have total below 99.984727. The median multiplier
  enclosure gives a cost below 170.685.
- The fixed-scale residual is exactly 629/25000000, and the initial center
  residual is 89199/250000<357/1000.
- The three large-prime budgets sum to 451/1000<23/50, and the core retention
  fraction is exactly 103363/137500.
- The saturated polynomial comparison, Cbar error comparison, the final
  50th-power rational inequality, and the Taylor certificates for exp(8),
  exp(34), and the entropy bound pass.

These checks support transcription and scalar correspondence. They do not
replace the completed machine proof or independent human reading.

## Proposed manuscript edits

1. Clarify in the introduction that Hu and Jing also give explicit constants;
   do not imply that this is the first explicit uniform constant.
2. State positive integer u,v explicitly in the pair-overlap lemma, matching
   its Lean hypotheses.
3. State the median argument for nonnegative integer-valued vertex functions,
   the actual class formally proved by nat_median_coarea and used for prime
   valuations. The old real-valued formulation is a broader elementary
   generalization; it is not itself the existing Lean declaration. Narrowing
   the paper avoids claiming that broader formalization unnecessarily.
4. Use the non-strict diagonal conclusion D>=401/500, exactly as supplied by
   FixedScale.diagonal_lower. This is sufficient for the unchanged seed.
5. Replace the old source-manifest-only bibliography entry with a permanent
   link to the actually tested source commit and its new candidate manifest.

The proof's numerical value exp(-6888), theorem, tables, authors field and
licenses are unchanged. TeX reference/environment structure was checked;
new PDF compilation and visual inspection are delegated to local Codex.

## Sources and attribution

Hu--Jing, arXiv:2610.23790v1, was retrieved from the primary arXiv HTML.
Its Theorem 1.1 states the uniform positive-constant result. Sections 3--4
provide pair intersections and multiplicity dilation; Section 6 develops
valuation concentration; Section 8 closes their argument. The original
paper explicitly says that its constants are explicit and not optimized.
https://arxiv.org/html/2610.23790v1

Green--Walker, Extremal problems for GCDs, arXiv:2012.02078v2, was also
retrieved from the primary arXiv HTML. The manuscript cites its GCD-graph
valuation strategy, not an unproved use of its whole extremal theorem.
https://arxiv.org/html/2012.02078v2

The Green-function energy argument is proved in the current manuscript and
formal modules. No claim that the underlying sharp one-dimensional analytic
inequality is new has been established by this review. Priority, a numerical
comparison with every earlier explicit constant, and a complete literature
review remain separate publication questions.

## Remaining work

Apply the exact-hash manuscript revision and source map, compile the paper
twice and inspect the PDF. Preserve the successful machine evidence; paper
edits alone do not require another long Lean build. Any future mathematical
source change must be separately assessed and verified.

Keep PR #1 as a draft. Independent human semantic/manuscript review, author
attribution, license confirmation, and final publication approval remain
pending. This model-assisted review must not be relabeled independent human
review. No push, merge, tag or release was performed by this review session.
