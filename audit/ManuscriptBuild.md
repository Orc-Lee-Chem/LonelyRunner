# English manuscript build

Engine: `pdfTeX 3.141592653-2.6-1.40.25 (TeX Live 2023)`.

The release PDF was regenerated from `paper/lonely_runner_en.tex`, not copied
from the original project PDF. 3 pdfLaTeX passes exited 0: the requested
two initial passes, plus any rerun required by the cross-reference diagnostics.
Build intermediates were kept outside the release tree.

```sh
cd paper
pdflatex -interaction=nonstopmode -halt-on-error lonely_runner_en.tex
pdflatex -interaction=nonstopmode -halt-on-error lonely_runner_en.tex
```

Final PDF: 34 pages. Final-pass undefined references/citations or rerun diagnostics: 0.
Overfull box diagnostics: 0. Underfull box diagnostics: 3.

PDF text extraction confirms the retained author and the AI-assistance section.

All 34 pages were rendered for a layout overview; the final AI-assistance and
reference page was also inspected at larger scale. No clipped equations, missing
reference text or misplaced disclosure was observed. The three underfull notices
are line-spacing diagnostics; no overfull boxes remain.
