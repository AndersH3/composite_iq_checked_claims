# Dask simulations and KOMA-Script report books

**Author:** Anders Hellström.

**All-six-volume formalization scan:** [Rocq proof obligations and source-located report claims](../rocq/SIX_REPORT_PROOF_OBLIGATIONS.md) covers all three analytical books and all three simulation books, including the shared statistical appendix. It distinguishes finite algebra already checked from missing Gaussian/sample-distribution/interval-coverage theorems.

Each sub-project has its own detailed XeLaTeX report:

| Sub-project | Report | Pages |
|---|---|---:|
| Hoeflin/Ferguson | [PDF](../analyses/hoeflin-ferguson/output/pdf/hoeflin_simulations.pdf) | See revision manifest |
| Towers admissions | [PDF](../analyses/towers-multiple-test-admissions/output/pdf/towers_simulations.pdf) | See revision manifest |
| Sequential conditional means | [PDF](../analyses/sequential-conditional-means/output/pdf/sequential_simulations.pdf) | See revision manifest |

Each report covers **both SPARK and Dask** as experiments: the native generator and sampling algorithm, estimators, every native case, Dask construction and pooling, observed results, direct comparisons and verification limits. Hoeflin covers all eight native sizes; Towers covers all four native threshold rules and Dask's additional calibrated OR rule; sequential covers all 46 native batches, including the 22 outside Dask's 24-law grid. Native source-pinned proof results, runtime/replay observations, numerical diagnostics and ideal-model statistical laws have separate scopes. A shared appendix derives the Gaussian mean/variance and binomial/Wilson reference calculations from named sources. Every report includes its own AI disclosure and bibliography.

All three main reports and all three simulation reports now contain complete working proofs and claim-to-proof/evidence maps. The common foundations prove covariance and scaling, covariance feasibility, Gaussian closure and block independence, regression with exact continuous histories, event arithmetic and total variance. Project appendices supply the composite, admissions and sequential deductions. The statistical appendix proves the normal/chi-square pivots, interval inversion, Wilson algebra and its approximate scope, exact Clopper–Pearson coverage, conditional-binomial denominators, pooling and multiple-diagnostic bounds. Numerical estimates, historical observations and model assumptions are explicitly distinguished from mathematical consequences.

## Rebuild the six proof-complete reports

With the retained simulation data already present, run from the repository root:

```sh
make report-books PYTHON=.venv/bin/python
```

[`rebuild_proofs.py`](rebuild_proofs.py) executes one Dask graph that verifies the retained campaign inputs, audits native numerical records through [`native_audit.py`](native_audit.py), builds the selected PDFs with XeLaTeX/BibTeX, rejects unresolved references or layout diagnostics, renders every page with Poppler and writes the current [`contextual-attribution/revision.json`](contextual-attribution/revision.json). The builder verifies **Anders Hellström** on each title page and in the exact PDF author metadata, including the diacritic. Every named Python function has at least five distinct Deal decorators. No simulation draws or native prover runs are performed by this document revision. Rendered pages are temporary visual-QA artifacts; current source/PDF hashes and new build transcripts are retained separately from the original experiment. `make proof-reports` remains an alias for the six-volume workflow.

To rebuild only the three simulation reports, use `make simulation-reports PYTHON=.venv/bin/python` (equivalently, `.venv/bin/python -m reporting.rebuild_proofs --simulations-only`). The retained [dual-implementation revision](dual-simulation/revision.json) used this selection and left the three analytical PDFs at their preceding revision. The current manifest records the selected reports, hashes the native campaign files actually discussed, and retains all 58 native simulation rows with derived intervals or moments and descriptive Dask comparisons. The audit rejects changed historical rows and inconsistent event projections; it does not pool the two engines or infer cross-generator independence.

All six volumes use the canonical [`book_style.tex`](book_style.tex): **KOMA-Script `scrbook`, A4, one-sided, 16 mm outer margins**, TeX Gyre Pagella text/math, TeX Gyre Heros headings and Latin Modern Mono. Native front matter contains an overview and table of contents; numbered chapters and mathematical appendices follow. The **full AI disclosure is the final appendix after the bibliography**. A brief opening notice links to it.

The style loads every required package: `fontspec`, `unicode-math`, `tcolorbox`, `tabularray`, `hyperref`, `bookmark`, `mathtools`, `microtype`, `scrlayer-scrpage`, `cleveref`, `amsthm`, `booktabs`, `graphicx`, `float`, `enumitem`, `scrhack`, `listings`, `natbib`, and `xurl`. The build checks actual compiler input files, all four margins in the geometry log, contents entries and the final appendix anchor. The common style uses native text, math and table layout. The simulation wrapper loads PGFPlots only for its scientific charts; Xy-pic is unnecessary for these volumes.

[`run.json`](run.json), the original `simulation-data/` files and the earlier [`proof-revision`](proof-revision/REPORT.md), [`book-format`](book-format/README.md), [`attribution`](attribution/README.md) and [`dual-simulation`](dual-simulation/README.md) records remain unchanged. Their document/source hashes describe their original snapshots; the contextual-attribution manifest describes the current report PDFs. Re-running the original simulation command below is a new experiment campaign and overwrites its generated outputs, so it is unnecessary for rebuilding these reports.

## Reproduce

From the repository root, with the exact development dependencies installed:

```sh
.venv/bin/python -m pip install -r requirements-dev.txt
.venv/bin/python -m reporting.simulate --pdf
```

`make simulations PYTHON=.venv/bin/python` is equivalent. Use the module entry point: `reporting.statistics` is deliberately namespaced and must not be loaded as the standard-library `statistics` module by executing a reporting file directly.

Dask owns random-array generation, transformations, chunk reductions, reference calculations, replicate pooling, statistical diagnostics, CSV/TeX asset production, XeLaTeX/BibTeX builds, Poppler rendering and the final source/output-hash manifest. The three branches share one terminal task graph and one `dask.compute` call. There is no Matplotlib import or direct plotting stage. XeLaTeX/PGFPlots draws charts from Dask-produced CSV files.

The canonical run uses Dask **2026.8.0**, NumPy **2.5.4**, SciPy **1.18.1** and Deal **4.24.6**, four fixed-seed replicates of one million observations per case, chunks of 50,000 and two process workers. Process isolation keeps Deal's runtime side-effect instrumentation local to a worker. The graph contains **31,254 tasks**. Dask's `default_rng` uses the NumPy PCG64 backend in this environment. Seeds and chunk layout are part of the reproducibility specification, not an independence theorem. Changing them can change the individual draws.

Base seeds are 20261114, 20261115, 20261116 and 20261117. Hoeflin uses those directly; Towers adds 1000; sequential cases add `2000 + 100*r`. The actual seed is retained in every replicate record. These integers are identifiers, not dates of the experiments.

Omitting `--pdf` produces data without building reports. `--trials`, `--chunk`, `--replicates` (1–4) and `--workers` (1–8) support development runs. The published reports describe the canonical four-million-observation design. A small development run overwrites the generated data; rerun the canonical command before distributing the reports. To rebuild one PDF from already generated data, use `make simulation-pdf` in its analysis folder. That target sets the shared BibTeX search path and uses XeLaTeX.

## Experiments

- **Hoeflin/Ferguson:** eight sizes, `n=1,2,3,4,5,10,100,1000`, correlation 0.6. An exact Gaussian aggregate representation avoids generating a thousand individual residuals for each observation. The experiment records standardized moments, raw-average SD, latent-factor prediction MSE and nested tail counts at 2, 3 and the one-in-a-million quantile.
- **Towers:** correlated normal pairs with correlation 0.7, four original threshold rules and a fifth OR rule calibrated to 2% combined eligibility. All four disjoint cells, joint/union probabilities, conditional rates with actual random denominators, Wilson/exact intervals and binary phi are retained. The common cutoff is independently recalculated using maintained quadrature and root-finding libraries.
- **Sequential:** all nine IQ-150 cases at correlation 0.6, plus six limiting population/conditional laws. Finite residual vectors and the conditional posterior common factor implement the actual mean, independently of the earlier scalar Ada sampler. The nonzero conditional SD is outcome uncertainty; the fixed prediction list has SD zero.

There are 37 pooled case laws and 148 replicate records. Each pooled law has four million output observations. Shared random inputs within a replicate make case comparisons dependent: these counts cannot be summed as if all rows were independent observations of one event. Four million trials still provide only four expected observations for a probability of one in a million.

The original Ada observations remain immutable, source-hashed inputs. A different generator is not expected to reproduce their counts bit for bit. The new reports compare statistical targets and uncertainty, rather than claiming exact replay or a fresh SPARK proof.

## Implementation and records

- [simulate.py](simulate.py) constructs the lazy array/delayed graphs and schedules all artifact operations.
- [The canonical statistics library](../library/python/statistics.py) reuses SciPy's binomial and chi-square routines, preserves conditional denominators and combines unbiased replicate variances using within/between sums of squares. [statistics.py](statistics.py) is the compatibility import facade after the shared-library migration; the original campaign manifest retains its original source hashes.
- [assets.py](assets.py) writes tables, scalar-only plot CSVs and data-driven numerical discussion. Full metadata remains in each `simulation-data/summary.json`.
- [run.json](run.json) records configuration, versions, graph size, sources and output hashes. It excludes its own hash to avoid circularity.
- Each analysis's `simulation-data/` contains complete pooled and replicate records, the original historical records, input hashes, generated TeX/CSV assets and the actual build log. These are new outputs; older evidence is not overwritten.

Every new named Python function, including tests and helpers, has at least five distinct meaningful Deal decorators. Higher counts specify useful domain, output, frame, exception or I/O properties. The CLI explicitly enables contracts, including optimized Python. Structural counts do not establish adequacy or universal correctness. Statistical diagnostics use a fixed conservative tail of `1e-10` and are separate from the descriptive 95% intervals: some 95% intervals can miss their known model targets. No seed is rerolled to improve the output.

`tests/test_dask_simulations.py` checks independent pooled-variance calculations, weighted MSE, individual-replicate corruption that cancels in aggregate, event partitions, conditional denominators, zero events, lazy seeded graph reproducibility and artifact schemas. Repository gates are `make check PYTHON=.venv/bin/python`. Verification results are retained separately after the final report build.

Numerical-library accuracy, PRNG quality/independence and empirical psychometric-model validity remain distinct from successful runtime checks. No native SPARK or Rocq invocation is claimed for this Python/document addition. The project license and AI disclosure apply.
