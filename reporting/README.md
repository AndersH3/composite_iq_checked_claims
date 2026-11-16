# Python/Dask simulation and XeLaTeX report pipeline

**Author/researcher:** Anders Hellström.

> **AI disclosure:** This numerical/reporting code and the accompanying source and documentation received substantial AI assistance. Results are model-based computations, not independent empirical psychometric validation.

The active pipeline is Python/Dask/NumPy/SciPy with Deal contracts. All three analysis projects have a mathematical report and a separate Python/Dask simulation-methods/results report. The former native simulation path is no longer shipped. Older proof, runtime and publication snapshots remain recoverable in Git history but are not current-source evidence.

- `simulate.py`: one scheduled Dask graph for random array generation, exact-reference calculations, seeded replicates, pooling, output generation and optional PDF builds.
- `assets.py`: reproducible numerical tables and CSV/TeX plot data. Report displays round values; the underlying records retain numerical precision.
- `provenance.py`: SHA-256 and JSON source/output manifests.
- `rebuild_proofs.py`: document-only XeLaTeX/KOMA-Script rebuild for six books from current recorded Dask assets, without generating fresh random draws.
- `simulation_style.tex`, `book_style.tex` and shared proof inputs: common report typography, bibliography and formal/methodological exposition.

Reproducibility begins with `requirements-dev.txt`, the model assumptions, explicit seed list, chunk layout, versions and `reporting/run.json`. A new Dask simulation is not byte-identical across arbitrary library versions or backends just because the human-readable seed matches.

```sh
python -m pip install -r requirements-dev.txt
make check
python -m reporting.simulate --trials 1000000 --chunk 50000 --replicates 4 --workers 2 --pdf
python -m reporting.rebuild_proofs
```

The simulation command **reruns** Monte Carlo experiments and updates computed assets. The report command reuses recorded data and builds the books without a fresh Monte Carlo run. Both require an installed XeLaTeX/latexmk toolchain and Poppler for PDF inspection.

The six books explain their Gaussian assumptions, confidence-interval interpretation, finite-sample dependence, numerical method boundaries and limitations of using synthetic simulation to infer human IQ-test statistics. Deal checks and Rocq proofs establish separate, specifically scoped properties; neither constitutes a proof of numerical library internals, random generator independence or psychometric model validity.

**Full AI disclosure:** AI systems contributed formulas, algorithms, source design, Deal contract specifications, Rocq proofs, mathematical prose, numerical presentation and document revisions. Recorded CI is automated rather than independent human review. No experimental participants or empirical IQ-validation study were involved, and no retired compiler proof campaign is attributed to the current Python code.
