# Hoeflin/Ferguson composite IQ scores

**Researcher/requester:** Anders Hellström.

> **AI disclosure:** This documentation, simulation development and mathematical exposition were substantially assisted by OpenAI ChatGPT/Codex. Automated checks do not constitute independent peer review.

The current implementation uses **Python 3.13, NumPy/SciPy, Dask and Deal contracts**. Formal mathematical statements are checked separately in Rocq 9.2. The discontinued Ada/SPARK implementation and its source-pinned native campaigns are available through *earlier Git revisions only*; they are not part of the working implementation or current-source proof evidence.

Each project has a full mathematical XeLaTeX/KOMA-Script analytical book and a separate simulation-methods/results book. The mathematical assumptions and finite Monte Carlo estimates are distinct from claims about real test-taking populations. Run `make check` for Deal/runtime checks and the Rocq Actions workflow for formal proof acceptance.

**Publication caveat:** Checked-in PDF artifacts may still reflect a pre-migration TeX revision until rebuilt with `make report-books` and committed; inspect the TeX sources for this revision's method descriptions.


## Reports

- [Mathematical analysis (XeLaTeX)](composite_iq_analysis.tex); [published PDF](output/pdf/composite_iq_analysis.pdf).
- [Python/Dask simulation report (XeLaTeX)](hoeflin_simulations.tex); [published PDF](output/pdf/hoeflin_simulations.pdf).

The mathematics compares unstandardized and standardized composite scores, covariance-based variance, correlation constraints, common-factor prediction and rare exceedance rates. The model-dependent Monte Carlo campaign computes per-size sample moments, standardized tail counts and latent-factor prediction error with four seeded Dask replicates and explicit Monte Carlo uncertainty. The numerical reference implementation is [Python](scripts/verify_calculations.py); reusable numeric helpers live in [the canonical library](../../library/python/README.md).

To reproduce current simulations and regenerate the report books from the repository root, use `python -m reporting.simulate --pdf` and `python -m reporting.rebuild_proofs` respectively, after installing `requirements-dev.txt` and an appropriate XeLaTeX toolchain. The latter only rebuilds documents from recorded Dask assets; it does not rerun the experiment.

**Full AI disclosure:** AI systems contributed to software source, contract specifications, formalization and report writing. Earlier removed implementations remain historical, not current verification. Finite simulation checks are not empirical validation of IQ score distributions, independent test results or extraordinary tails; the proof appendix states which formal propositions are established.
