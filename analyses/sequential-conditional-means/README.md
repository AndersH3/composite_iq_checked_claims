# Sequential conditional means and IQ-score averages

**Researcher/requester:** Anders Hellström.

> **AI disclosure:** This documentation, simulation development and mathematical exposition were substantially assisted by OpenAI ChatGPT/Codex. Automated checks do not constitute independent peer review.

The current implementation uses **Python 3.13, NumPy/SciPy, Dask and Deal contracts**. Formal mathematical statements are checked separately in Rocq 9.2. The discontinued alternate-engine implementation and its source-pinned native campaigns are available through *earlier Git revisions only*; they are not part of the working implementation or current-source proof evidence.

Each project has a full mathematical XeLaTeX/KOMA-Script analytical book and a separate simulation-methods/results book. The mathematical assumptions and finite Monte Carlo estimates are distinct from claims about real test-taking populations. Run `make check` for Deal/runtime checks and the Rocq Actions workflow for formal proof acceptance.

**Publication caveat:** Checked-in PDF artifacts may still reflect a pre-migration TeX revision until rebuilt with `make report-books` and committed; inspect the TeX sources for this revision's method descriptions.


## Reports

- [Mathematical analysis (XeLaTeX)](sequential_conditional_means.tex); [published PDF](output/pdf/sequential_conditional_means.pdf).
- [Python/Dask simulation report (XeLaTeX)](sequential_simulations.tex); [published PDF](output/pdf/sequential_simulations.pdf).

The mathematical report proves the **general case of any positive integer `n` initial test results, all equal to a fixed standardized score `a`**, followed by `k` future predictions or actual outcomes, with every initial result retained in the inclusive average. For pairwise correlation `c`, each future prediction is `n*c*a/(1+(n-1)*c)` and the predicted inclusive average is `n*(1+(n+k-1)*c)*a/((n+k)*(1+(n-1)*c))`. The report also gives exact conditional Gaussian variances, admissible negative-correlation endpoints and the limit as `n` increases at fixed `k`. The cases `n=1,2,3` are examples, not a mathematical restriction. It distinguishes deterministic recursively predicted scores from actual random future outcomes. The [Python/Dask simulator](../../reporting/simulate.py) constructs the *recorded* nonnegative-correlation finite score vectors for `n=1,2,3` and selected limiting Gaussian laws, with four seeded replicates, and compares their simulated moments against analytic reference formulas. It does **not** claim Monte Carlo verification of every `n`. The independent exact rational [general-n calculator](../../library/python/sequential.py) accepts any valid positive integer initial and future counts, including singular negative-correlation endpoints; its [tests](../../tests/test_sequential_arbitrary_n.py) compare closed forms with finite covariance Schur complements.

The current simulation is not a claim to cover all negative-correlation or singular cases through one common-factor generator; those cases must rely on explicit theoretical derivations or independently justified numerical implementations. A passing finite comparison does not prove exact Gaussian sampling, model validity or a universal floating-point error bound.


## D053–D056 verified Rocq continuation (November 17, 2026)

The Rocq 9.2 kernel has accepted **105 additional theorem declarations**
on the verified D056 revision (bringing the D050–D056
Gaussian-specific collection to **292**). They directly support the
mathematical report's general initial-`n` predictors, signed covariance
feasibility and dependence on unequal, finite score histories:

- [GaussianInnovationBounds.v](rocq/GaussianInnovationBounds.v):
  43 signed prediction, innovation and full covariance-domain properties,
  including observed-block nonsingularity at singular full endpoints.
- [GaussianBatchBalance.v](rocq/GaussianBatchBalance.v):
  30 exact predicted-total and inclusive-mean score identities,
  strict sign/ordering bounds, and singular-boundary cancellation.
- [GaussianFiniteHistoryPosterior.v](rocq/GaussianFiniteHistoryPosterior.v):
  32 posterior precision, variance-reduction, innovation-update and
  likelihood sufficient-statistic results for arbitrary unequal histories.

The [complete source-ordered proof register](../../rocq/PROOF_REFACTOR_GAUSSIAN.md)
and [successful Rocq D056 workflow](https://github.com/AndersH3/composite_iq_checked_claims/actions/runs/44153123270)
provide reproducible evidence. The statements concern deterministic
covariance and unnormalized Gaussian density algebra, **not** a kernel
proof of the actual measure-theoretic conditional expectation, Gaussian
independence, or empirical IQ distributions.

## Arbitrary-`n` exact calculation

```python
from fractions import Fraction
from library.python.sequential import equal_initial_scores

case = equal_initial_scores(n=5, k=10, a=Fraction(10, 3), c=Fraction(3, 5))
assert case["next_prediction"] == Fraction(50, 17)
assert case["inclusive_mean"] == Fraction(470, 153)
assert case["population_variance"] == Fraction(47, 75)
assert case["conditional_variance"] == Fraction(188, 3825)
```

`a=10/3` is IQ 150 on the reporting scale `IQ = 100 + 15*standardized_score`. This `n=5` case is an exact theoretical calculation, not an additional recorded simulation. The function accepts `int` or `Fraction` values (rather than inexact floating-point inputs), with a positive finite battery of at most one million tests. Underlying Gaussianity and equal correlation remain model assumptions.

Use `python -m reporting.simulate --pdf` to conduct fresh experiments and `python -m reporting.rebuild_proofs` to regenerate the six books from the existing recorded Dask assets. The [formal Rocq modules](rocq/README.md) and the shared proof register explain the mathematical proof scope.

**Full AI disclosure:** The project received extensive AI contributions in source, proof scripting, numeric analysis, simulation explanation and revision. The earlier removed implementation's claims are not recast as Python/Dask results or new evidence of human psychometric parameters.
