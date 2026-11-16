# SPARK and Dask simulation reports

**Author, researcher and requester:** Anders Hellström. Revision: 16 November 2026.

All three simulation books now explain both implementations as experiments, with algorithms, case coverage, actual observations, uncertainty, comparisons and verification boundaries. Existing mathematical proofs remain, and the new native-method arguments include the ideal Box–Muller law and the Gaussian scalar-aggregate law. Mathematical consequences, observed records, numerical approximations and statistical assumptions retain distinct evidence classifications.

| Simulation book | Pages | Native coverage | Dask coverage |
|---|---:|---|---|
| [Hoeflin/Ferguson](../../analyses/hoeflin-ferguson/output/pdf/hoeflin_simulations.pdf) | 32 | Eight sizes, one million draws per size; composite moments and three tail counts | Four million per size; also latent-factor MSE |
| [Towers](../../analyses/towers-multiple-test-admissions/output/pdf/towers_simulations.pdf) | 31 | One million shared normal pairs, four original rules, every event cell and conditional denominator | Four million shared pairs, five rules including calibrated OR |
| [Sequential](../../analyses/sequential-conditional-means/output/pdf/sequential_simulations.pdf) | 33 | Forty finite population/conditional batches and six limit batches, 200,000 outputs each | Twenty-four IQ-150 finite/limit laws, four million outputs each |

The sequential report now includes all 22 native batches outside the Dask grid: alternate starting levels, independence, perfect correlation, finite negative correlations and singular covariance endpoints. The six native limit rows are compared directly with Dask. Reports explain why population spread, conditional outcome spread and Monte Carlo uncertainty of an estimated centre answer different questions.

## Reproduction and immutable inputs

Run from the repository root, with `requirements-dev.txt` installed:

```sh
make simulation-reports PYTHON=.venv/bin/python
```

The eight-task Dask graph audits retained inputs, reinterprets each project's native numerical records, builds the three books using XeLaTeX/BibTeX, renders every page with Poppler and records [revision.json](revision.json). It uses KOMA-Script `scrbook`, 16 mm margins, all 19 required packages, a table of contents, Anders Hellström's title-page roles and PDF metadata, and the full AI-disclosure appendix last. PGFPlots is used only for scientific charts. There is no Matplotlib stage. The three analytical PDFs remain at their preceding revision.

The manifest pins 50 original `simulation-data/` files and 24 native campaign/validation/source records. The audit retains all 58 native simulation rows, checks their exact equality to the historical records consumed by the original Dask campaign, recalculates event partitions/conditional denominators/Wilson intervals using the shared statistics library, and derives moment summaries and descriptive comparisons. Additional native table rows are transcribed from these immutable observations; the Dask audit provides their machine-readable numerical counterparts. No native observations and Dask observations are pooled across implementations, and no cross-generator independence is inferred.

Hoeflin and Towers use the final 4 November campaign's source-pinned native runtime and portfolio records. Their simulation CSVs are byte-identical to the original 31 October observations used by Dask. Ghost Check/Ignore runs and deterministic replays do not increase the sample size. Sequential uses `campaign-20261114-current`, including its archived source; the word `current` in that historical directory does not assert identity with later checkouts. Original evidence, original Dask assets and earlier report-revision records remain unchanged.

The retained native portfolios contain 404, 696 and 430 discharged checks respectively. These are facts about their original source snapshots, not new GNATprove runs on the later shared-library refactor. Finite runtime tests, static lint, structural contract inventories, limited symbolic proofs, numerical agreement, ideal sampling laws and psychometric-model validity are separate claims. The report revision generates no new random draws and performs no new native proof campaign.

## Verification and visual review

The final [check.txt](check.txt) records successful `make check PYTHON=.venv/bin/python`: library ownership, repository-wide Python and SPARK contract inventories, static lint with its exact expected DEL012 negative control, **453 passing tests** and scoped symbolic checks. The current inventories contain 43 Python files, 380 named functions and 2,310 Deal decorators, plus 183 SPARK subprograms and 1,183 explicit contract entries; both mandatory five-entry floors pass. The numerical-audit tests check native row counts and denominators, explicitly absent Dask cases, deterministic boundaries, and rejection of changed historical rows or false union/conditional/interval projections. CLI contracts remain enabled under optimization. Structural counts and scoped symbolic results do not prove entire implementations or statistical-model validity.

Earlier attempts are retained transparently. [check-before-lint-refactor.txt](check-before-lint-refactor.txt) stops after the structural gates and is incomplete. [check-during-rebuild.txt](check-during-rebuild.txt) failed because report-preservation fixtures detected PDFs changing while the build was still running; it is not a passing verification result. The final gate runs after all PDF builds finish. No fixture, contract or acceptance threshold was weakened to obtain that result.

All 96 final pages were rendered for visual review. Contact sheets and enlarged algorithm/table/disclosure pages were inspected by AI agents; a chart-only float page and a two-line orphan continuation were corrected before the final build. Compiler logs reject overfull/underfull boxes, missing glyphs, unresolved references/citations and duplicate labels. The build transcripts are retained beside the manifest; temporary rendered PNGs remain under each project's `tmp/pdfs/` directory.

AI disclosure: OpenAI Codex and collaborating AI agents drafted and reviewed these additions, audited the numerical records, implemented the report workflow changes, ran the recorded checks, and inspected the PDFs at Anders Hellström's request. Full disclosures remain in each book. Independent human peer review and empirical validation are not claimed.
