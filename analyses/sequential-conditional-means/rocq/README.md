# Sequential conditional-means — Rocq formalization

**Researcher:** Anders Hellström.

> **AI disclosure:** OpenAI ChatGPT/Codex materially assisted theorem selection, Rocq proof scripts and commentary. Mathematical proof status depends exclusively on Rocq 9.2 kernel validation of the exact source revision.

The report-local Rocq modules (SequentialReport.v, SequentialSensitivity.v, EquicorrelationSpectral.v, EquicorrelationVectors.v, EquicorrelationInverseVectors.v, ReportRounding.v, ReportCounterexample.v) formalize sequential regression algebra, equicorrelation vectors, sensitivity, rounding certificates and finite counterexamples with explicit hypotheses, reusing the [canonical shared mathematical library](../../../library/rocq/README.md). They contain separate explanations of every definition, theorem and proof strategy. The full source-order register and six-volume proof-obligation ledger are maintained in the central Rocq documentation.

Numerical reference calculations are implemented in [Python](../../../reporting/simulate.py) with NumPy/SciPy where appropriate. [Dask](../../../reporting/simulate.py) constructs the maintained Monte Carlo workflow and Deal specifies selected source-level contracts. These numerical computations and Rocq proofs address different propositions.

No formal proof of Gaussian pseudorandom sampling, individual test-taking behavior, tail calibration, external numerical library implementations or empirical IQ validity is implied by checking finite algebraic identities.

**Full AI disclosure:** The project used AI assistance for specification, mathematics, tests, source, formatting and reports. The user-directed research questions and priorities originated with Anders Hellström. Automated checks do not constitute independent human peer review or actual participant data.
