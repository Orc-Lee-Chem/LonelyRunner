# Publication checks

Target repository: https://github.com/Orc-Lee-Chem/LonelyRunner

The author explicitly selected this account/repository and public upload,
Apache-2.0 for original code, CC-BY-4.0 for the English manuscript, and retention
of the manuscript's author, affiliation and contact email.

## Frozen formalization

- 686 current Lean/build inputs matched the audited frozen SHA256 values.
- 609 Tablet sources and 71 LonelyRunner sources are included, plus unchanged
  root imports, Test, SemanticCheck and pinned configuration files.
- The sole publication edits to Lean files are 76 Apache compatibility-port
  comment notices; stripping each notice exactly recovers its audited file.
- No theorem, definition, proof body, hypothesis, toolchain or dependency changed.
- The completed 9608-job source rebuild was reused rather than repeated.
- Original FinalAudit.log and FinalSourceHashes.tsv remain unchanged locally.
- Public audit material is explicitly labeled as a selected/redacted excerpt
  and derived scoped inventory, not the original raw log or inventory.

## Manuscript

- Selected input SHA256: `21c71e8cb16d001c58e95486579480d4933eb19c1461f1be0396c2fba9ec813c`.
- Released TeX SHA256: `e7270aac9ece5c0b29938131a19641da9bd1cfcdf4d9e2836bf0c1ac4fd57972`.
- Released PDF SHA256: `30f7a5d7b3844750b26cabe9bd1ce44a21b3a6f009b7e40cdaf1e937df040d66`.
- Required AI-assistance text appears once before the bibliography, and once
  in README. The paper's mathematical content was not changed for publication.
- pdfLaTeX: 3 successful passes; 34 pages; no unresolved
  cross-references/citations, no rerun requests, no overfull boxes.
- Three minor underfull line-spacing diagnostics were reviewed visually.

## Publication boundaries

Only the final English TeX and its newly compiled PDF are in paper/.
No Chinese manuscript, old draft, reference-paper PDF, .lake directory, compiled
Lean output, TeX intermediate, local credential, private audit log or private
absolute path is part of the release. The approved academic contact information
on the manuscript's title page is intentionally retained.

The release-specific ReleaseSHA256.tsv excludes itself and Git internals.
Git text conversion is disabled by .gitattributes to preserve those exact bytes.
