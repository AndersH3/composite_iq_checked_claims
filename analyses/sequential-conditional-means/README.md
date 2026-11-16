# Sequential conditional means and IQ-score averages

**Researcher/requester:** Anders Hellström.

> **AI disclosure:** This documentation, simulation development and mathematical exposition were substantially assisted by OpenAI ChatGPT/Codex. Automated checks do not constitute independent peer review.

The current implementation uses **Python 3.13, NumPy/SciPy, Dask and Deal contracts**. Formal mathematical statements are checked separately in Rocq 9.2. The discontinued Ada/SPARK implementation and its source-pinned native campaigns are available through *earlier Git revisions only*; they are not part of the working implementation or current-source proof evidence.

Each project has a full mathematical XeLaTeX/KOMA-Script analytical book and a separate simulation-methods/results book. The mathematical assumptions and finite Monte Carlo estimates are distinct from claims about real test-taking populations. Run `make check` for Deal/runtime checks and the Rocq Actions workflow for formal proof acceptance.

**Publication caveat:** Checked-in PDF artifacts may still reflect a pre-migration TeX revision until rebuilt with `make report-books` and committed; inspect the TeX sources for this revision's method descriptions.


## Reports

- [Mathematical analysis (XeLaTeX)](sequential_conditional_means.tex); [published PDF](output/pdf/sequential_conditional_means.pdf).
- [Python/Dask simulation report (XeLaTeX)](sequential_simulations.tex); [published PDF](output/pdf/sequential_simulations.pdf).

The mathematical report derives population and conditional means/variances of average standardized scores with one, two or three fixed observed starting scores included in the average. It distinguishes deterministic recursively predicted scores from actual random future outcomes. The [Python/Dask simulator](../../reporting/simulate.py) constructs the reported nonnegative-correlation finite score vectors and selected limiting Gaussian laws, with four seeded replicates, and compares their simulated moments against analytic reference formulas.

The current simulation is not a claim to cover all negative-correlation or singular cases through one common-factor generator; those cases must rely on explicit theoretical derivations or independently justified numerical implementations. A passing finite comparison does not prove exact Gaussian sampling, model validity or a universal floating-point error bound.

Use `python -m reporting.simulate --pdf` to conduct fresh experiments and `python -m reporting.rebuild_proofs` to regenerate the six books from the existing recorded Dask assets. The [formal Rocq modules](rocq/README.md) and the shared proof register explain the mathematical proof scope.

**Full AI disclosure:** The project received extensive AI contributions in source, proof scripting, numeric analysis, simulation explanation and revision. The earlier removed implementation's claims are not recast as Python/Dask results or new evidence of human psychometric parameters.
