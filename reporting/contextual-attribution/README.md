# Contextual attribution

**Author:** Anders Hellström. Revision: 16 November 2026.

All six report title pages now display **Anders Hellström** alone as the author. The shared `\ProjectAuthor` macro expands only to that name; each report uses `\author{\ProjectAuthor}`, and PDF author metadata contains the same name. The combined role line and its `\ProjectRoles` macro have been removed.

Current documentation uses one role where the context calls for it. Ordinary document credits use `Author: Anders Hellström`; prose about specifying the work uses “the requester Anders Hellström.” “Researcher” is reserved for contexts in which that role is relevant, rather than being automatically attached to the name. `AGENTS.md` records this convention. Substantive AI disclosures, original-author citations and verification limits remain accurate.

## Build and verification

The existing Dask workflow rebuilt all six PDFs using XeLaTeX and the canonical KOMA-Script `scrbook` style, with 16 mm margins, all required packages, contents and final AI-disclosure appendices. Its eleven-task graph verifies the retained data, audits native numerical records, builds and renders the reports, and writes [revision.json](revision.json). The builder now checks the name-only author declaration, its visible rendering and exact PDF metadata.

| Report | Pages |
|---|---:|
| [Hoeflin/Ferguson analysis](../../analyses/hoeflin-ferguson/output/pdf/composite_iq_analysis.pdf) | 30 |
| [Hoeflin/Ferguson simulations](../../analyses/hoeflin-ferguson/output/pdf/hoeflin_simulations.pdf) | 32 |
| [Towers analysis](../../analyses/towers-multiple-test-admissions/output/pdf/towers_admissions_analysis.pdf) | 30 |
| [Towers simulations](../../analyses/towers-multiple-test-admissions/output/pdf/towers_simulations.pdf) | 31 |
| [Sequential analysis](../../analyses/sequential-conditional-means/output/pdf/sequential_conditional_means.pdf) | 42 |
| [Sequential simulations](../../analyses/sequential-conditional-means/output/pdf/sequential_simulations.pdf) | 33 |

All 198 pages were rendered for visual review, including enlarged title pages and disclosure text. The build rejects unresolved citations/references, duplicate labels, missing glyphs and overfull/underfull boxes. Build transcripts and current source/PDF hashes are retained beside this record. Reproduce with `make report-books PYTHON=.venv/bin/python` after installing `requirements-dev.txt`.

The final [check.txt](check.txt) records successful `make check PYTHON=.venv/bin/python`: library ownership, repository-wide Python/SPARK contract inventories, static lint with the expected DEL012 negative control, **453 passing tests** and scoped symbolic checks. All current named Python functions retain at least five Deal decorators; CLI contracts remain explicitly enabled. Contract inventories, tests and limited symbolic results have their stated scopes and do not establish universal program or statistical-model correctness.

## Historical records and disclosure

This is a new presentation revision. The original simulation data and recorded proof evidence, and the earlier attribution, book-format, proof-text and dual-simulation records, retain their original bytes and wording. The mathematical arguments and simulation results are preserved; no new random experiment, native SPARK proof or Rocq campaign was run. The retained native results still describe their source-pinned historical snapshots, rather than later refactored Ada bodies.

OpenAI Codex and collaborating AI agents applied and reviewed this wording correction, updated the build checks, rebuilt the reports and inspected their pages at the request of Anders Hellström. Full AI disclosures remain in the final appendix of every report. Independent human peer review is not claimed.
