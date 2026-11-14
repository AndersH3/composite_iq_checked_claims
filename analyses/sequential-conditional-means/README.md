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

## Build

From this directory, run:

```sh
make pdf
```

The build requires XeLaTeX, BibTeX, `latexmk`, KOMA-Script, the packages loaded by the source, TeX Gyre Pagella text and mathematics, TeX Gyre Heros, and Latin Modern Mono. `latexmk` follows the included theorem/certificate files and runs BibTeX for `references.bib`. The output is `output/pdf/sequential_conditional_means.pdf`. `make clean` removes auxiliary files while retaining the PDF.

The report follows the typography and output layout of the existing [Hoeflin/Ferguson analysis](../hoeflin-ferguson/). It introduces no Python or SPARK implementation and has no additional runtime dependencies.

## Verification and limits

The derivations, theorem attributions and source locators were reviewed by collaborating AI agents. Validation for the referenced-proof revision was completed on 14 November 2026:

- `make pdf` passed; the PDF, including the bibliography and proof certificates, was rendered and visually inspected. The final LaTeX log had no unresolved references, missing glyphs, or overfull/underfull boxes.
- From the repository root, `make check PYTHON=.venv/bin/python` passed using the exact versions in `requirements-dev.txt`. This includes Python contract coverage, the SPARK structural contract audit, static lint with its required negative control, **343 runtime/property tests**, and the existing scoped symbolic acceptance gate.
- The symbolic gate proved its six expected postcondition obligations and found the required negative-control counterexample. Those obligations concern the existing software; they do not formally verify this new analysis.

The report contains written mathematical proofs under its stated assumptions. Build and software checks are separate from those arguments and do not machine-check the new exposition or empirically validate the Gaussian test model. No new SPARK prover campaign was run.

The text explicitly specifies the continuous Gaussian conditional-mean version so that recursive evaluation at probability-zero point histories is well defined. For `k` future tests and one starting test, the correlation domain is `-1/k <= c <= 1`; an arbitrarily long collection requires `0 <= c <= 1`.

## AI disclosure and license

The mathematical exposition, documentation and typesetting were prepared with OpenAI Codex and collaborating AI agents in response to the requester's problem, indexing clarifications and request for proofs with references. Review took place within that workflow; independent human peer review is not claimed. The report includes its own disclosure dated 14 November 2026. Historical verification evidence for other analyses is not evidence of a new formal verification of this report.

The repository's existing [LICENSE](../../LICENSE) governs its original material, subject to third-party rights.
