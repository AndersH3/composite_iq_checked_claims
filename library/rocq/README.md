# Shared Rocq mathematical source

> **AI disclosure:** This source-location refactor and accompanying documentation were AI-assisted; only the separately pinned Rocq kernel checks theorems.

All report-neutral mathematical modules are now owned **once**, under this directory: `FiniteSum`, `FiniteUnion`, `FiniteMoments`, `FiniteBridge`, the equicorrelation spectral/vector/inverse modules, finite two-cell and nested projection, finite conditional covariance/residual, and `TwoObservationSchur`. They reuse Rocq's maintained Stdlib List, Reals, Lra, Psatz, and ring/field tactics. No new axioms, alternative summation recursion or Gaussian oracle are introduced.

Report-specific lemmas and models remain with their reports: [Hoeflin/Ferguson](../../analyses/hoeflin-ferguson/rocq/), [Towers admissions](../../analyses/towers-multiple-test-admissions/rocq/), and [Sequential conditional means](../../analyses/sequential-conditional-means/rocq/).

The canonical 18-module dependency order is encoded in [`scripts/compile_rocq.sh`](../../scripts/compile_rocq.sh). It copies each uniquely named source into a clean temporary workspace and runs `rocq compile` in that order. From the repository root:

```sh
bash scripts/check_rocq_documentation.sh
sh scripts/compile_rocq.sh
```

CI pins `rocq/rocq-prover:9.2.0`; an explanatory header and full declaration-specific documentation are enforced. The existing 1,682 proof scripts are relocated **without altering their propositions**. Finite weighted algebra and best linear prediction do not themselves establish Gaussian conditional probabilities, normal-tail integrals, or any empirical psychometric parameter.

## Complete AI disclosure

OpenAI ChatGPT classified and relocated the source and updated the compile scripts. Only Rocq-kernel-checked statements under their actual hypotheses constitute formal results, and these results must not be interpreted as validation of Gaussian or real-world IQ assumptions.
