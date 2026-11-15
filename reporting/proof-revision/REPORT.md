# Six-report proof revision, 15 November 2026

All three main analyses and all three simulation reports contain working proofs of their mathematical deductions, named foundational references, and claim-to-proof/evidence maps. Assumptions, model consequences, numerical approximations, historical observations and recommendations are explicitly distinguished.

| Project | Main report pages | Simulation report pages |
|---|---:|---:|
| Hoeflin/Ferguson | 24 | 22 |
| Towers admissions | 26 | 23 |
| Sequential conditional means | 32 | 22 |

The **149 pages** were rebuilt using XeLaTeX/BibTeX, rendered with Poppler and visually reviewed through all contact sheets and selected full-page images. Final logs contain no overfull/underfull boxes, missing characters, unresolved references/citations or duplicate labels. The final layout correction removed a stranded provenance sentence: 147 final page images are identical to the reviewed baseline, and the two changed sequential main pages were reviewed at full size.

## Mathematical coverage

The shared foundations prove weighted covariance and affine scaling, PSD feasibility and Gaussian construction, Gaussian affine closure and block independence, conditioning by independent residuals including exact continuous histories, normal-marginal insufficiency, event denominators and total variance. Project appendices prove the composite thresholds and limits, latent-factor conditioning and nonidentification, bivariate joint tails and Plackett differentiation, admissions calibration and grid interpretation, and the complete sequential future-vector, recursion, covariance, SD and limiting laws.

The statistical appendix supplies full normal/chi-square sampling proofs and pivotal inversion, binomial moments, Wilson endpoint algebra and its approximate coverage scope, exact Clopper–Pearson coverage, conditional-binomial random denominators, pooled variance, simultaneous diagnostic bounds and rare-event precision. The Towers argument includes an exact elementary bound rejecting the original probabilities independently of the numerical integrator's final digits. Sequential numerical certificates are exact rational/integer arguments. Other numerical-library evaluations remain explicitly approximate; agreement of programs is not described as a proof of their last rounded digits.

Primary foundations include the precisely identified author versions of Durrett, Gallager and Axler, with the sequential report also using Hammack and Bertsekas–Tsitsiklis. Primary Plackett, Wilson and Clopper–Pearson references accompany the relevant results. Each report contains its own bibliography and AI disclosure. Independent human review or empirical IQ-model validation is not claimed.

## Reproduction and preservation

Run from the repository root:

```sh
make proof-reports PYTHON=.venv/bin/python
```

The single Dask graph has eight tasks: retained-input verification, six document builds/renders and a final manifest. [`revision.json`](revision.json) pins the current TeX/Bib sources, rebuild code, instructions and all six PDF hashes. [`artifact-audit.json`](artifact-audit.json) records final hash, text, log, render-count and visual checks. The new rebuild module has four named functions, with five to ten distinct Deal decorators each, explicit I/O boundaries and enabled CLI contracts. Standard XeLaTeX/BibTeX and Poppler tools perform the document operations inside Dask tasks. No Matplotlib is used.

All **50 original simulation-data files** match the retained [`../run.json`](../run.json) hashes, including its old build transcripts. The numerical campaign and historical native evidence were not regenerated or overwritten. That original manifest's document/source hashes describe its original snapshot; this revision has a separate manifest. Build stdout is retained in the six new `*.build.txt` files here.

The repository's concurrent shared-library migration was integrated at base `0773444ddae3eef4bfa9cfd3292c5d08913b4534`. Its library-layout gate and source changes were preserved. Historical GNATprove campaigns are not relabelled as current-source proof of refactored Ada units. No new native SPARK or Rocq campaign was invoked for this document revision.

## Checks actually run

[`check.txt`](check.txt) records `make check PYTHON=.venv/bin/python` after the shared-library integration:

- Canonical source ownership and all three shared-library consumers: passed.
- Python inventory: 41 files, 377 named functions, 2,276 distinct Deal declarations; every function meets the five-contract floor, with 56 at the staged ten-contract target.
- SPARK structural inventory: 102 functions and 81 procedures, 1,183 explicit clauses; all 183 meet the five-clause floor, with 26 at the staged ten-clause target. This is a structural inventory, not a native proof run.
- Static lint: every positive Python file passed; the explicit negative fixture produced precisely its expected failure.
- Runtime/property tests: **446 passed** in 178.71 seconds.
- Scoped symbolic gate: six supported postcondition obligations proved and the intended negative obligation returned a counterexample; no unsupported whole-program claim is made.

After the final temporary-page cleanup improvement, [`rebuild-helper-check.txt`](rebuild-helper-check.txt) records repeated contract inventories and static lint. The complete six-report Dask build exercised that final helper under enabled Deal contracts; it removes stale temporary page images when a report becomes shorter. The retained [`check-before-library-integration.txt`](check-before-library-integration.txt) preserves the earlier full check's distinct source context.

The written mathematical proofs, bounded program contracts, structural audits, runtime tests, numerical accuracy, PRNG assumptions and empirical model validity remain separate claims.
