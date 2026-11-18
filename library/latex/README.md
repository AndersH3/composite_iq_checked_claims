# Common XeLaTeX report template

**Author/researcher/requester:** Anders Hellström.

> **AI disclosure:** This template, documentation, and the report front-matter refactor were developed with AI assistance. XeLaTeX compilation validates document construction, not mathematical correctness, independent human review, or empirical suitability.

The canonical styles for all **six** maintained report books live here, based on the supplied `iq_test_differences_report.tex` reference:

- `report_style.tex`: KOMA-Script `scrbook`, A4, narrow margins, Latin Modern OpenType fonts, required XeLaTeX packages, reference-report color palette, result/disclosure boxes, theorem definitions, listings, and consistent front matter.
- `simulation_style.tex`: imports the report style and adds PGFPlots for simulation figures only.

The books in `analyses/{hoeflin-ferguson,towers-multiple-test-admissions,sequential-conditional-means}` **directly import** these library styles. The former `reporting/book_style.tex` and `reporting/simulation_style.tex` names are thin backward-compatible wrappers; they must not duplicate styling.

Each main book retains `\\title`, `\\subtitle`, `\\author` and `\\date` and replaces `\\maketitle` with `\\ProjectReportTitlePage`. Set `\\renewcommand{\\ProjectReportHighlights}{...}` in each book's preamble using its independently supported results. The title page prominently discloses AI assistance; the existing complete, report-specific AI disclosure stays in the **last appendix**. Keep the abstract, table of contents, proofs, labels, citations, simulation manifest, and analytical text in the report-specific files. Do not move mathematical formulas into graphics.

Run XeLaTeX/latexmk from the individual analysis directory (the relative shared-library paths are resolved from the current working directory), e.g.:

```sh
cd analyses/hoeflin-ferguson
latexmk -xelatex -interaction=nonstopmode -halt-on-error -outdir=output/pdf composite_iq_analysis.tex
```

GitHub Actions `.github/workflows/report-books.yml` builds all six reports on changes to `library/latex/**`, the analysis TeX sources, or the reporting proof inputs. A small single-file XeLaTeX smoke test verified the common title-page macros; the CI matrix must verify all six full books and citations before merge.
