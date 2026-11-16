# D048x empirical covariance Cauchy–Schwarz proof review register

**Author:** Anders Hellström.

> **AI DISCLOSURE:** OpenAI ChatGPT assisted the theorem design, proof scripts and this register. A source statement only counts as proved if the pinned Rocq 9.2 kernel accepts the exact commit; this register is not an independent proof or a probability model.

The source-ordered register below records every `Proof.` block of the shared `SampleContrastCauchy.v` module. Covariance feasibility inequalities are deterministic necessary constraints on observed finite weighted samples, not evidence of independent sampling, Gaussianity, or interval coverage.

## SampleContrastCauchy.v — 2 proof scripts

| Proof script (kind) | Mathematical scope | Library reuse | Boundaries |
|---|---|---|---|
| `sample_centered_bridge` (theorem) | Equality between canonical finite weighted centered cross-products and arbitrary-batch covariance numerators | FiniteSum, FiniteConditionalCovariance, ListPoolingAlgebra | Deterministic moments only |
| `sample_covariance_cauchy_schwarz` (theorem) | Squared normalized finite sample covariance bounded by product of empirical variances with nonnegative weights and positive total mass | Existing finite_centered_cauchy_schwarz plus previous bridge | Not a distribution or Gaussian sampling law |

## Full AI disclosure

OpenAI ChatGPT specified these propositions, generated candidate proof scripts, documented their assumptions, and orchestrated GitHub validation. Only Rocq-kernel-accepted statements are proven. The deterministic mathematical scope does not establish empirical psychometric assumptions or general measure-theoretic Gaussian conditioning.
