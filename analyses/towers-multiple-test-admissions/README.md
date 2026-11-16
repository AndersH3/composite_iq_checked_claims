# Towers multiple-test admissions

**Researcher/requester:** Anders Hellström.

> **AI disclosure:** This documentation, simulation development and mathematical exposition were substantially assisted by OpenAI ChatGPT/Codex. Automated checks do not constitute independent peer review.

The current implementation uses **Python 3.13, NumPy/SciPy, Dask and Deal contracts**. Formal mathematical statements are checked separately in Rocq 9.2. The discontinued discontinued alternate-engine implementation and its source-pinned native campaigns are available through *earlier Git revisions only*; they are not part of the working implementation or current-source proof evidence.

Each project has a full mathematical XeLaTeX/KOMA-Script analytical book and a separate simulation-methods/results book. The mathematical assumptions and finite Monte Carlo estimates are distinct from claims about real test-taking populations. Run `make check` for Deal/runtime checks and the Rocq Actions workflow for formal proof acceptance.

**Publication caveat:** Checked-in PDF artifacts may still reflect a pre-migration TeX revision until rebuilt with `make report-books` and committed; inspect the TeX sources for this revision's method descriptions.


## Reports

- [Mathematical analysis (XeLaTeX)](towers_admissions_analysis.tex); [published PDF](output/pdf/towers_admissions_analysis.pdf).
- [Python/Dask simulation report (XeLaTeX)](towers_simulations.tex); [published PDF](output/pdf/towers_simulations.pdf).

The analysis distinguishes overlapping qualifications, union eligibility, conditional retest qualification and calibrated multiple-test admission rules under an explicitly specified bivariate Gaussian model. The shared Python/Dask campaign generates the same correlated scores per replicate for the tested cutoff rules and preserves the four joint Boolean event cells. The model probabilities use [SciPy-based maintained Python numerical calculations](scripts/verify_calculations.py), with Deal contracts, explicit denominators and interval uncertainty for rare joint events.

To run a new seeded campaign use `python -m reporting.simulate --pdf`. To rebuild the book from *existing* recorded Dask data without new draws use `python -m reporting.rebuild_proofs`. Install the pinned Python requirements and XeLaTeX/Poppler first.

**Full AI disclosure:** AI systems helped develop code, contracts, mathematical proofs and this report. The model is not a measurement of actual association membership or a verified latent-ability distribution. Old removed compiler and native simulation results are not presented as evidence for the current Python code.
