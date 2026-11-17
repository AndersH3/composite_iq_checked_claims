# Sequential conditional-means — Rocq formalization

## D050 — 56 checked Gaussian density and signed covariance-domain proofs

**AI disclosure:** These candidate formal proofs, probability model analysis and
documentation were AI-assisted. Kernel acceptance, not source-counting,
establishes any proved statement. The full regular conditional-expectation
theorem remains an explicit open Rocq obligation.

At the exact D050 revision `20801d4a693adb0582133876d1a8d41c2ba48bcf`,
the [pinned Rocq 9.2 kernel](https://github.com/AndersH3/composite_iq_checked_claims/actions/runs/43997860735)
accepted **35 Gaussian kernel/sufficiency proofs and 21 concrete
Schur-covariance proofs**. Five of the kernel proofs factor an arbitrary
unequal-score Gaussian likelihood through its sample mean; four
covariance proofs establish full PSD/PD necessity and sufficiency for
concrete future-score lists of length at least two, plus the one-future-score variance PSD/PD iff and both singular endpoints.

A separate [MathComp normalized posterior measure module](../mathcomp/GaussianPosteriorMeasure.v)
uses the maintained Gaussian conjugacy theorem but remains outside the
Stdlib 9.2 kernel count until its dedicated workflow passes. Neither
step alone proves the full observed-sigma-algebra conditional
expectation of a future Gaussian score.

The new `GaussianConditionalKernel.v` specifies the latent common-factor
Gaussian prior and arbitrary unequal-history likelihood for `0<c<1`,
and uses finite-score sums to complete the posterior normal quadratic.
It identifies the candidate posterior center `c*S_n/d_n(c)`, posterior
variance `c*(1-c)/d_n(c)`, and factors the *unnormalized* joint
density into evidence and posterior-shape kernels.

`GaussianCovarianceDomain.v` extends Schur-complement PSD and PD conditions
to **negative** admissible correlations using the exact eigenvalue
`(1-c)*d_(n+k)(c)/d_n(c)` of the conditional common-score direction.
It deliberately reuses canonical finite-list Cauchy-Schwarz and
equicorrelation spectral lemmas.

The separate [Gaussian conditioning mathematical derivation](../../../rocq/GAUSSIAN_CONDITIONING_THEOREM.md)
distinguishes those kernels from the additional multivariate normal
independence/disintegration and conditional-expectation theorems needed
for complete formalization. Existing Gaussian normal-probability results
in MathComp-Analysis should be reused, rather than made into axioms.


**Researcher:** Anders Hellström.

> **AI disclosure:** OpenAI ChatGPT/Codex materially assisted theorem selection, Rocq proof scripts and commentary. Mathematical proof status depends exclusively on Rocq 9.2 kernel validation of the exact source revision.

## D049x — arbitrary unequal observed-score histories (120 theorem scripts)

The pinned Rocq 9.2 kernel [accepted the 120 proofs](https://github.com/AndersH3/composite_iq_checked_claims/actions/runs/43982923903) at source revision `87227eef93b3`; the full corpus comprises 3,378 proof scripts across 39 modules. The specialized [UnequalHistoryLinearPrediction.v](UnequalHistoryLinearPrediction.v)
module contains 120 newly documented deterministic identities for the candidate
equicorrelation predictor based on the **sum of arbitrarily unequal observed
scores**, predicted future-batch totals, inclusive means, outcome innovations,
and shifts of the baseline/score scale. It reuses the original
`SequentialReport.sequential_d`; no separate finite-sum algorithm, covariance
library or numerical model is implemented. The exact source-order theorem audit
is [PROOF_REFACTOR_UNEQUAL_HISTORY.md](../../../rocq/PROOF_REFACTOR_UNEQUAL_HISTORY.md).

These related linearity and calibration identities are not 106 independent
Gaussian regression laws. In particular, the *probabilistic* assertion that this
candidate is a regular conditional expectation remains unproved, as do
distributional and empirical assumptions. The source must pass the Rocq 9.2
kernel and documentation/source-ownership workflows before any formalized claim
can be considered established.

The report-local Rocq modules (SequentialReport.v, SequentialSensitivity.v, EquicorrelationSpectral.v, EquicorrelationVectors.v, EquicorrelationInverseVectors.v, ReportRounding.v, ReportCounterexample.v, UnequalHistoryLinearPrediction.v) formalize sequential regression algebra, equicorrelation vectors, sensitivity, rounding certificates and finite counterexamples with explicit hypotheses, reusing the [canonical shared mathematical library](../../../library/rocq/README.md). They contain separate explanations of every definition, theorem and proof strategy. The full source-order register and six-volume proof-obligation ledger are maintained in the central Rocq documentation.

Numerical reference calculations are implemented in [Python](../../../reporting/simulate.py) with NumPy/SciPy where appropriate. [Dask](../../../reporting/simulate.py) constructs the maintained Monte Carlo workflow and Deal specifies selected source-level contracts. These numerical computations and Rocq proofs address different propositions.

No formal proof of Gaussian pseudorandom sampling, individual test-taking behavior, tail calibration, external numerical library implementations or empirical IQ validity is implied by checking finite algebraic identities.

**Full AI disclosure:** The project used AI assistance for specification, mathematics, tests, source, formatting and reports. The user-directed research questions and priorities originated with Anders Hellström. Automated checks do not constitute independent human peer review or actual participant data.
