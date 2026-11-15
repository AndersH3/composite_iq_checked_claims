# Sequential conditional-means specialized Rocq proofs

> **AI disclosure:** This source-ownership documentation was AI-assisted.

[`SequentialReport.v`](SequentialReport.v), [`EquicorrelationSpectral.v`](EquicorrelationSpectral.v), [`EquicorrelationVectors.v`](EquicorrelationVectors.v), [`EquicorrelationInverseVectors.v`](EquicorrelationInverseVectors.v), [`ReportRounding.v`](ReportRounding.v) and [`ReportCounterexample.v`](ReportCounterexample.v) formalize the report's sequential regression algebra, exact rounding certificates and finite counterexamples. The three equicorrelation spectral/vector modules remain here because they import the specialized `SequentialReport` proof; only report-neutral finite sums, moments, conditional covariance/projection and Schur algebra are imported from [the central Rocq library](../../../library/rocq/README.md). Domain-specific SPARK implementations and independent Python validation stay alongside the report.

Compile using `sh scripts/compile_rocq.sh` from the repository root. Consult the [report theorem inventory](../../../rocq/REPORT_THEOREM_INVENTORY.md) for the exact scope. The conditional-mean and Gaussian-tail implications beyond finite algebra remain explicit research gaps.

## Complete AI disclosure

OpenAI ChatGPT assisted with classification and source relocation. Pinned kernel checking is confined to the formal statements; no Gaussian conditional-distribution existence or empirical test parameter has been proved by this refactor.
