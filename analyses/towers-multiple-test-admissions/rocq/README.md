# Towers admissions specialized Rocq proofs

> **AI disclosure:** This module-ownership documentation was AI-assisted.

[`Admissions.v`](Admissions.v), [`FourCellBridge.v`](FourCellBridge.v) and [`ThreeTestAdmissions.v`](ThreeTestAdmissions.v) own the report's four-cell event model, union, conditional-admissions, dependence and three-test multiplicity theorems. Shared finite-event summation, moment and covariance operations reside in [the central Rocq library](../../../library/rocq/README.md). Specialized SPARK and Python source remains in the adjacent `ada/src/` and `scripts/` directories, using central exact event arithmetic where applicable.

Build using `sh scripts/compile_rocq.sh`; see the [report theorem inventory](../../../rocq/REPORT_THEOREM_INVENTORY.md). The new 55-theorem module covers eight atomic Boolean admission patterns,
finite three-way inclusion-exclusion, count distribution (zero through three),
three-event Fréchet/Bonferroni inequalities and sharp overlap bounds. The
probabilities all use the central `FiniteUnion.finite_prob` and
`FiniteSum.finite_sum`; no duplicated finite integral/union algorithm is
introduced. These discrete probability identities do not establish a continuous Gaussian joint-tail model.

## Complete AI disclosure

ChatGPT assisted with source placement and documentation. Kernel compilation validates only the declared theorem statements and hypotheses; empirical admissions rates and Gaussian assumptions remain unverified.
