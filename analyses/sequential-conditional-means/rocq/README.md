# Sequential conditional-means — Rocq formalization

**Researcher:** Anders Hellström.

> **AI disclosure:** OpenAI ChatGPT/Codex materially assisted theorem selection, Rocq proof scripts and commentary. Mathematical proof status depends exclusively on Rocq 9.2 kernel validation of the exact source revision.

## D049x — arbitrary unequal observed-score histories (106 theorem scripts)

The specialized [UnequalHistoryLinearPrediction.v](UnequalHistoryLinearPrediction.v)
module contains 106 newly documented deterministic identities for the candidate
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

The report-local Rocq modules (SequentialReport.v, SequentialSensitivity.v, EquicorrelationSpectral.v, EquicorrelationVectors.v, EquicorrelationInverseVectors.v, ReportRounding.v, ReportCounterexample.v) formalize sequential regression algebra, equicorrelation vectors, sensitivity, rounding certificates and finite counterexamples with explicit hypotheses, reusing the [canonical shared mathematical library](../../../library/rocq/README.md). They contain separate explanations of every definition, theorem and proof strategy. The full source-order register and six-volume proof-obligation ledger are maintained in the central Rocq documentation.

Numerical reference calculations are implemented in [Python](../../../reporting/simulate.py) with NumPy/SciPy where appropriate. [Dask](../../../reporting/simulate.py) constructs the maintained Monte Carlo workflow and Deal specifies selected source-level contracts. These numerical computations and Rocq proofs address different propositions.

No formal proof of Gaussian pseudorandom sampling, individual test-taking behavior, tail calibration, external numerical library implementations or empirical IQ validity is implied by checking finite algebraic identities.

**Full AI disclosure:** The project used AI assistance for specification, mathematics, tests, source, formatting and reports. The user-directed research questions and priorities originated with Anders Hellström. Automated checks do not constitute independent human peer review or actual participant data.
