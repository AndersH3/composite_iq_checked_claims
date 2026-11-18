# Shared XeLaTeX report templates

**Researcher/requester:** Anders Hellström.

> **AI disclosure:** The common templates and their refactoring have been produced with AI assistance. A successful XeLaTeX build verifies typesetting, not the correctness of the mathematics or any psychometric assumption.

## Canonical library files

- `report_style.tex`: canonical XeLaTeX/KOMA-Script `scrbook` format, A4 narrow margins, Latin Modern fonts, colors, navigation, native math environments and listings, a title page with one short AI notice, and the final AI-appendix command.
- `simulation_style.tex`: the same style plus PGFPlots support for scientific simulation graphics.
- `ai_disclosure.tex`: the only maintained full AI-use disclosure body. Every book includes it once through the shared `\ProjectReportAIAppendix` macro.

The old `reporting/book_style.tex`, `reporting/simulation_style.tex` and `reporting/ai_disclosure.tex` paths remain compatibility aliases with no independent formatting or prose. Do not edit those aliases to change the report presentation.

## Book structure

Each report sets `\title`, `\subtitle`, `\author`, `\date` and its unique `\ProjectReportHighlights`. Mathematical reports set `\ProjectReportRunningTitle` and `\ProjectReportRunningSubtitle` rather than assigning page headers directly. Simulation books inherit shared running heads. Each book follows this order:

1. `\frontmatter` and exactly one `\ProjectReportTitlePage` (the prominent short AI disclosure appears here).
2. Exactly one `abstract` overview, then the existing proof/evidence convention and table of contents. No second AI disclosure follows the abstract.
3. `\mainmatter` with all original derivations, data, citations, results and numerical limitations.
4. `\appendix` with proofs/claim maps, bibliography as appropriate, then exactly one `\ProjectReportAIAppendix` as the final chapter.

The complete AI disclosure is deliberate and distinct from the short title-page notice. It must not be copied into individual book sources, and the layout should not contain a second initial notice. The overview and key-findings box have different purposes and must remain substantively distinct.

## Verification

Run `bash scripts/check_report_template.sh` or `make report-template` for structural checks. The six-book workflow runs the structural audit and then builds all six PDFs, checking unresolved citations and references. The workflow watches changes to `library/latex/**` and the audit script.

Build one book from the individual analysis directory:

```sh
cd analyses/hoeflin-ferguson
latexmk -xelatex -interaction=nonstopmode -halt-on-error -outdir=output/pdf composite_iq_analysis.tex
```

All documents follow the reference supplied as `iq_test_differences_report.tex`, while retaining mathematical conventions and bibliographic compatibility from the original six books.
