# Python/Dask simulation and XeLaTeX report pipeline

**Author/researcher:** Anders Hellström.

> **AI disclosure:** This numerical/reporting code and the accompanying source and documentation received substantial AI assistance. Results are model-based computations, not independent empirical psychometric validation.

The active pipeline is Python/Dask/NumPy/SciPy with Deal contracts. All four analysis projects have a mathematical report and a separate Python/Dask simulation-methods/results report. The former native simulation path is no longer shipped. Older proof, runtime and publication snapshots remain recoverable in Git history but are not current-source evidence.

- `simulate.py`: one shared Dask graph for reference calculations, block tasks, seeded replicates, pooling, output generation and optional PDFs. The default is the block-summary engine; `--engine arrays` retains the older Dask Array implementation as a cross-check for up to one million samples per replicate.
- `block_simulations.py`: vectorized, worker-local NumPy normal draws inside Dask delayed blocks. Every block evaluates all coupled rules/counts, transmits only small sufficient statistics, and combines centered variances with the parallel Chan merge. This avoids shipping full sample matrices across worker boundaries.
- `assets.py`: reproducible numerical tables and CSV/TeX plot data. Report displays round values; the underlying records retain numerical precision.
- `provenance.py`: SHA-256 and JSON source/output manifests.
- `rebuild_proofs.py`: document-only XeLaTeX/KOMA-Script rebuild for eight books from current recorded Dask assets, without generating fresh random draws.
- `../library/latex/report_style.tex` and `../library/latex/simulation_style.tex`: canonical shared book typography and title pages. The `reporting/*_style.tex` files and `reporting/ai_disclosure.tex` are compatibility aliases only. The canonical full AI-use disclosure lives in `library/latex/ai_disclosure.tex` and is included once per report through `\ProjectReportAIAppendix`. Shared mathematical proof inputs remain here.

## Scaled runs and memory model

The prior baseline run used four seeds × 1,000,000 samples per seed (4,000,000 per case), 50,000-row chunks, and 31,254 tasks. The optimized **default configuration** specifies **eight seeds × 5,000,000 samples per seed = 40,000,000 per case** with 500,000-row blocks; its no-execution task graph has **3,303 tasks**. This is 10× the baseline sample budget with about 89% fewer Dask scheduling tasks. The actual executed sample count, engine, seed set and output hashes for the original three-study campaign are recorded in **`reporting/run.json`**, and its six PDFs must be read alongside that manifest. The fourth study has a specialized campaign and separate evidence. A source default alone does not certify that samples were drawn.

### Measured 40-million-sample run

The 16 November 2026 scaled campaign was **executed**, not merely planned: `reporting/run.json` records eight seeds, five million observations per seed, 500,000-row blocks, the Dask delayed block engine and **3,303 graph tasks**. Each of the 37 coupled reported cases has **40 million pooled simulated observations**. The workflow completed successfully; the three model-specific generated CSVs and all replicate summaries were checked before committing the replacement assets.

GNU `/usr/bin/time -v` measured **35.51 seconds wall time** and **192% CPU utilization** on the GitHub runner with two Dask multiprocessing workers, with 59.90 user CPU seconds, 8.51 system CPU seconds, and maximum reported resident set size **241,104 KiB (about 235.5 MiB)**. The RSS measurement is not a sum of simultaneous worker peaks, nor is this a controlled speedup benchmark against the earlier Dask Array graph. Measured logs and the execution plan are preserved at [`reporting/benchmarks/40m-resource-usage.txt`](benchmarks/40m-resource-usage.txt) and [`reporting/benchmarks/40m-plan.json`](benchmarks/40m-plan.json). The previous graph used 31,254 tasks for four million pooled samples per case; this refactor executes ten times the samples with about **89.4% fewer scheduler tasks**.

The default block engine performs random generation and per-case vectorized calculations *inside* independent Dask delayed tasks. It keeps finite score matrices local to individual workers (especially the sequential study), then sends only means, centered sums of squares, tail counts, and MSE sums to reduction tasks. The centered parallel-variance identity preserves between-block and between-replicate variation. All cases for a block reuse shared random draws, so cross-case comparisons remain dependent. Block-indexed NumPy SeedSequence streams make the result independent of worker completion order; **changing the block size, worker engine, or NumPy version changes the seeded realization**, and the resulting output is not identical to older Dask Array runs.

The largest sequential block at default settings creates roughly **96 MB of raw Gaussian inputs** (the 13-column population matrix, 10-column future matrix, and one latent column), plus working arrays and Python/Dask overhead. This is **not a peak-memory bound**: plan memory for multiple concurrent blocks, Dask worker processes, intermediate arrays, and report generation. The `distributed` scheduler supports per-worker memory limits, spill-to-disk, a dashboard and performance-report capture. For large runs on shared hardware, measure peak RSS, wall time and spill behavior before increasing workers or block size.

```sh
python -m pip install -r requirements-dev.txt
make check
# Construct the actual lazy DAG; display task count and memory inputs without execution.
python -m reporting.simulate --plan
# Actual scaled default: 40 million observations per case (8 × 5 million).
python -m reporting.simulate --workers 4 --pdf
# Higher-precision example: 160 million per case; requires sufficient RAM/time.
python -m reporting.simulate --trials 20000000 --chunk 500000 \
    --replicates 8 --workers 4 --scheduler distributed \
    --memory-limit 2GiB --dashboard-address :8787 \
    --performance-report dask-performance.html --pdf
# Rebuild documents from recorded numerical assets, WITHOUT drawing new samples.
python -m reporting.rebuild_proofs
```

For a one-in-a-million event, 40 million Bernoulli trials have **40 expected exceedances** and about **16% Poisson relative standard deviation**; 160 million have 160 expected exceedances, approximately **8%**. The draws remain pseudorandom, and larger counts do not validate the assumed model. Reported tail probabilities still need uncertainty intervals.

A new simulation command **reruns** Monte Carlo experiments and **overwrites** generated assets and the provenance manifest. The document-only rebuild does not. Treat the committed manifest as the authoritative record of the most recent published numerical campaign, not the source defaults; ensure data and report PDFs are reviewed and committed together. The CLI enforces at most 1,024 blocks per replicate and bounds individual worker chunks, preventing silent million-task graphs. The `--plan` switch is suitable for inspecting large hypothetical configurations without allocating their sample arrays.

Reproducibility depends on `requirements-dev.txt`, hypotheses, seeds, block layout, NumPy/Scipy/Dask versions, scheduler selection and `reporting/run.json`. Dask's guidance is to use blocks large enough to amortize per-task scheduling overhead, while retaining multiple blocks per worker and respecting RAM capacity: https://docs.dask.org/en/stable/array-chunks.html and https://docs.dask.org/en/stable/best-practices.html.

The six books explain their Gaussian assumptions, confidence-interval interpretation, finite-sample dependence, numerical method boundaries and limitations of using synthetic simulation to infer human IQ-test statistics. Deal checks and Rocq proofs establish separate, specifically scoped properties; neither constitutes a proof of numerical library internals, random generator independence or psychometric model validity.

**Full AI disclosure:** AI systems contributed formulas, algorithms, source design, Deal contract specifications, Rocq proofs, mathematical prose, numerical presentation and document revisions. Recorded CI is automated rather than independent human review. No experimental participants or empirical IQ-validation study were involved, and no retired compiler proof campaign is attributed to the current Python code.
