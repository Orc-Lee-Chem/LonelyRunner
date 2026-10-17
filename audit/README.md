# Publication and audit provenance

## Original local audit (not uploaded)

The original `FinalAudit.log` and `FinalSourceHashes.tsv` are retained unchanged
locally. They contain local paths, archival file names and a Chinese-manuscript
diff, so neither original is included in this public repository.

- Original FinalAudit.log SHA256: `d4914598611d87b3a893052c22767c029d8f478c97dfd1fc6f07c138a5a7ae7b`.
- Original FinalSourceHashes.tsv SHA256: `281eae9938a99acdbae9c6ede451f20a6f620997f9437bbefcf65ed124872e2b`.
- Original frozen inventory: 5024 records, all matching the audited snapshot.
- Independent fresh-source rebuild on the original machine: 609 Tablet modules,
  71 LonelyRunner modules and an audit-only import driver; 9608 jobs; exit 0.
- A later change in the original Chinese manuscript was recorded; it did not
  change any Lean source/configuration and was not copied over the snapshot.

`FinalAudit.public-excerpt.log` is an explicitly labeled, selected and redacted
excerpt, not the complete raw log. It excludes private paths, manuscript diffs
and old warning/retry output; the full theorem/axiom output is preserved.

## Released code and manuscript

`FrozenLeanInputs.tsv` is a derived inventory of the 686 released build-input files,
with both frozen and release SHA256 values. It is not the original 5024-record
inventory. Exactly 76 Tablet files gained a publication-only comment identifying
the upstream compatibility modifications. Their remaining bytes are unchanged;
all other Lean sources/configurations are byte-identical to the frozen inputs.
The audited source bodies were not changed, so the completed full source rebuild
was not repeated solely for these comment notices.

The English manuscript input was selected by the author-specified SHA256:
`21c71e8cb16d001c58e95486579480d4933eb19c1461f1be0396c2fba9ec813c`.
Only the required AI-assistance disclosure was added before its bibliography.
The author approved retention of the manuscript's name, affiliation and contact
email. No Chinese manuscript, reference-paper PDF, old draft or temporary TeX
output is included. The released PDF is newly compiled from the released TeX.

`ReleaseSHA256.tsv` at the repository root is generated after all publication files
are finalized. It covers every published file except itself and Git internals;
it is a **release inventory**, not an assertion that the publication bytes are
the original frozen tree. Licenses, README, disclosure, notices and PDF belong
to this release and were not in the old source rebuild.

To verify this release inventory with Python 3:

```sh
python scripts/check_release_hashes.py
```
