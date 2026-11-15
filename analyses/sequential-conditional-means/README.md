# Sequential Conditional Means of Equicorrelated Scores

A full derivation for the average of `a, e_1, ..., e_k`, including the fixed starting score `a` as the first value. Every test has population mean **0** and standard deviation **1**. Under joint Gaussianity and equal pairwise correlation `c`, every subsequent recursive prediction equals `c a`, so the requested average is **`a (1 + k c) / (k + 1)`**. Here `k` counts subsequent predictions and `k + 1` counts all values in the average.

- [Compiled PDF](output/pdf/sequential_conditional_means.pdf)
- [XeLaTeX source](sequential_conditional_means.tex)
- [Established theorems and their proofs](theorem_foundations.tex)
- [Exact arithmetic and rounding certificates](exact_numeric_certificates.tex)
- [Bibliography](references.bib)
- [Verified source versions and theorem locators](reference_notes.md)

Every derived mathematical claim now has a proof from named, referenced results. The report states the foundational moment, conditional-expectation, spectral, Gaussian-conditioning and induction theorems, then proves the project-specific means, SDs, special cases and endpoint claims. A claim-to-proof map links the conclusions to their proof locations and source foundations. The cited primary references are Durrett, Gallager, Axler, Hammack, and Bertsekas-Tsitsiklis; exact source versions and theorem numbers are recorded in the reference notes.

The population parameters, joint Gaussian assumption, fixed observed scores and IQ reporting transformation are explicit model inputs. The mathematical proofs establish their consequences. Exact rational values and positive-integer rounding certificates justify all displayed numerical approximations.

The report derives the Gaussian regression function using a residual independent of the conditioning scores, solves the recursion by induction and by telescoping partial sums, and distinguishes the deterministic sequence from actual test outcomes. It also gives the formula in terms of the total number of values `N = k + 1`: `a (1 + (N - 1) c) / N`. It covers the admissible finite-battery correlation interval and both singular endpoints. A discrete counterexample shows why correlation alone is insufficient. The tests remain on the specified mean-zero, unit-standard-deviation scale throughout.

The standard deviation of the mean depends on which scores remain random:

| Quantity, including the first value | Standard deviation |
|---|---|
| Actual mean of `k + 1` tests across the population | `sqrt((1 + k c) / (k + 1))` |
| Actual mean after fixing the first test score at `a` (Gaussian model) | `sqrt(k (1 - c) (1 + k c)) / (k + 1)` |
| Recursive mean of the fixed numbers `a, e_1, ..., e_k` | `0` |
| Recursively filled mean across random starting scores | `(1 + k c) / (k + 1)` |

The PDF derives these formulas by counting covariance terms and conditioning Gaussian residuals. It also connects the formulas using the law of total variance. For `N` total tests, the population standard deviation is `sqrt((1 + (N - 1) c) / N)`; this population formula needs the stated variances and covariances but does not require Gaussianity.

## Two or three initial scores equal to `a`

These cases fix two or three distinct initial test scores at the same value `a`, then make `k >= 1` subsequent recursive predictions. All starting scores are included in the average, so the total counts are `k + 2` and `k + 3`.

| Quantity | Two initial scores `a, a` | Three initial scores `a, a, a` |
|---|---|---|
| Every subsequent prediction | `2 c a / (1 + c)` | `3 c a / (1 + 2 c)` |
| Mean including all initial scores | `2 (1 + (k + 1) c) a / ((k + 2) (1 + c))` | `3 (1 + (k + 2) c) a / ((k + 3) (1 + 2 c))` |
| Population SD of the actual mean | `sqrt((1 + (k + 1) c) / (k + 2))` | `sqrt((1 + (k + 2) c) / (k + 3))` |
| Conditional SD of the actual mean, given the initial scores | `sqrt(k (1 - c) (1 + (k + 1) c) / (1 + c)) / (k + 2)` | `sqrt(k (1 - c) (1 + (k + 2) c) / (1 + 2 c)) / (k + 3)` |

The fixed recursive means have SD `0`. The report derives a general case with `r` equal starting scores, proves that the subsequent predictions stay constant, and then specializes it to `r = 2` and `r = 3`. The correlation domains are `-1/(k + 1) <= c <= 1` and `-1/(k + 2) <= c <= 1`, respectively. Every test retains population mean `0` and SD `1`.

For `a = 2`, `c = 0.6` and three subsequent predictions, the inclusive means are `1.7` and `1.818182`; the corresponding conditional SDs of the actual means are `0.319374` and `0.246183`.

## IQ 150 examples, SD 15 and correlation 0.6

Use the reporting scale `IQ = 100 + 15 X`, so an initial IQ of 150 is the standardized starting score `a = (150 - 100) / 15 = 10/3`. The underlying standardized tests retain mean 0 and SD 1. For one, two or three initial IQ-150 scores, every subsequent prediction is respectively **130.00**, **137.50** or **140.91** IQ points.

All initial scores are included in the following means. `k` is the number of subsequent predictions. The SD columns describe the actual test-score mean, in IQ points; the conditional SD fixes every initial score at IQ 150.

| Initial IQ-150 scores | Subsequent predictions k | Total scores | Mean IQ | Population SD | Conditional SD |
|---:|---:|---:|---:|---:|---:|
| 1 | 1 | 2 | 140.00 | 13.42 | 6.00 |
| 1 | 2 | 3 | 136.67 | 12.85 | 6.63 |
| 1 | 10 | 11 | 131.82 | 11.97 | 7.22 |
| 2 | 1 | 3 | 145.83 | 12.85 | 3.71 |
| 2 | 2 | 4 | 143.75 | 12.55 | 4.44 |
| 2 | 10 | 12 | 139.58 | 11.94 | 5.45 |
| 3 | 1 | 4 | 147.73 | 12.55 | 2.68 |
| 3 | 2 | 5 | 146.36 | 12.37 | 3.34 |
| 3 | 10 | 13 | 143.01 | 11.91 | 4.46 |

The PDF derives the scale conversion, mean and SD formulas and works through the two-start, ten-prediction row. Calculations use the exact standardized score `10/3` and exact correlation `3/5`, with rounding applied only to displayed results. The fixed recursive mean has SD 0 in every row; the nonzero SDs describe actual test outcomes.

## Infinite-count limits and SD interpretation

For fixed `r` and `c` in `[0,1]`, each subsequent prediction already equals `r c a / (1+(r-1)c)`. The inclusive mean tends to that same value. Actual-mean population SD tends to `sqrt(c)` and conditional SD tends to `sqrt(c(1-c)/(1+(r-1)c))`. A fixed negative correlation cannot remain admissible as the battery grows without bound.

For the IQ-150 examples at `c=0.6`, the limiting rows are:

| Initial scores | Mean IQ limit | Population SD limit | Conditional SD limit |
|---:|---:|---:|---:|
| 1 | 130.000000 | 11.618950 | 7.348469 |
| 2 | 137.500000 | 11.618950 | 5.809475 |
| 3 | 140.909091 | 11.618950 | 4.954337 |

Population SD describes random whole batteries centred at IQ 100, with the initial scores also random. Conditional SD describes variation of actual outcomes around the conditional mean after fixing the initial scores at IQ 150. Replacing future outcomes by their predictions gives a fixed numerical list whose mean has SD zero. The report proves the general variance decomposition and explains why conditional SD increases with `k` in these selected examples while population SD decreases.

## Calculations, simulations and verification

The [Ada/SPARK implementation](ada/README.md) separates exact coefficient construction, floating evaluation, bounded accumulation, sampling and the trusted command-line/CSV boundary. All eleven new SPARK interfaces have at least five meaningful explicit behavioral/flow contracts; eight have at least ten. The [Python validator](scripts/VALIDATION.md) uses Deal contracts on every named function, including helpers and tests, and reuses Fraction, NumPy and SciPy rather than duplicating their algorithms.

The implementation covers all numerical examples, finite negative and singular endpoints, inverse/eigenvector/recursion identities, analytic limits, total variance, conditional-growth arithmetic and the non-Gaussian counterexample. Foundational probability and linear-algebra theorems remain written proofs with primary references. Simulations and finite calculations do not prove universal mathematical theorems or the empirical IQ model.

Reproduce a fresh build, native proof and numerical campaign from the repository root:

```sh
.venv/bin/python analyses/sequential-conditional-means/scripts/run_spark.py --trials 200000
```

Every run uses a fresh source/object mirror and an unused evidence directory. See [Ada reproduction instructions and trust boundaries](ada/README.md) and [validator schemas](scripts/VALIDATION.md). Run the repository gates with `make check PYTHON=.venv/bin/python`. No historical campaign records are modified.

## Recorded results (14 November 2026)

The [retained campaign and current-source audit](evidence/REPORT.md) record:

- **430 native checks discharged** across six new/reused SPARK units: 124 flow checks and 306 prover checks, zero unproved or justified checks, with no retained assumptions or suppressions. All ten new analyzed subprogram bodies are covered; the checked square-root completion and CLI remain explicit trusted boundaries.
- **20 finite calculations**, 20 independent matrix comparisons, **46 simulation batches of 200,000 observations** each, and 18 algebraic/PMF diagnostics passed. The independent self-check verified all 74 printed rounding-certificate integers.
- `make check PYTHON=.venv/bin/python` passed, including **420 runtime/property tests**, static lint with its expected negative control, contract inventories, and the existing scoped symbolic gate. A final lint/coverage rerun includes the new evidence auditor; its rejection checks reject altered current Ada and changed retained artifacts.
- The **32-page PDF** compiled without unresolved references, missing glyphs or overfull/underfull boxes, and every page was visually reviewed.

The native record is immutable. A later Python-only import/path normalization for the updated Astroid dependency is disclosed in the [current-source audit](evidence/current-source-audit.json); every Ada/project hash still matches, and the current validator rechecks the original CSVs. The audit makes no extra prover-invocation claim.

## Build the report

From this analysis directory, run `make pdf`. Both report volumes use XeLaTeX, BibTeX, `latexmk`, KOMA-Script `scrbook`, A4 paper with 16 mm margins, TeX Gyre Pagella text/mathematics, TeX Gyre Heros and Latin Modern Mono. The [shared preamble](../../reporting/book_style.tex) loads the required package set. Every volume has a table of contents and full AI disclosure as the final appendix after the bibliography. The output is `output/pdf/sequential_conditional_means.pdf`. `make clean` removes auxiliary files while retaining the PDF.

The new sections are [asymptotic limits](asymptotic_limits.tex), [SD interpretation](sd_interpretation.tex) and [computational scope and proofs](computational_verification.tex). The final PDF is rendered and visually inspected after changes. Written mathematical proofs, native SPARK results, runtime Deal tests, static lint, scoped symbolic verification, numerical accuracy and model validity are reported separately.

## AI disclosure and license

The mathematical exposition, documentation, typesetting, Ada/SPARK and Python/Deal software were prepared with OpenAI Codex and collaborating AI agents in response to the requester's problem and verification requirements. The report contains its own disclosure dated 14 November 2026. Independent human peer review and empirical psychometric validation are not claimed. The repository's existing [LICENSE](../../LICENSE) governs its original material, subject to third-party rights.

## Dedicated simulation report

The [simulation report](output/pdf/sequential_simulations.pdf) describes the simulated probability model, experiment design, Dask execution, pooled and replicate results, uncertainty, historical Ada comparison and interpretation limits in detail. Its [XeLaTeX source](sequential_simulations.tex) consumes the generated tables in [simulation-data](simulation-data/). Charts are drawn by XeLaTeX/PGFPlots from Dask-produced CSVs.

From the repository root, regenerate all three experiments, tables, PDFs and rendered review pages with:

```sh
.venv/bin/python -m reporting.simulate --pdf
```

See the [shared Dask workflow](../../reporting/README.md) for seeds, chunk layout, dependency versions, contracts and verification scope. With the generated data already present, `make simulation-pdf` in this directory rebuilds only this volume using XeLaTeX. From the repository root, `make report-books PYTHON=.venv/bin/python` rebuilds all six books and records the presentation revision separately while retaining the original numerical campaign and historical proof evidence.
