# Towers admissions specialized Rocq proofs

> **AI disclosure:** This module-ownership documentation was AI-assisted.

[`Admissions.v`](Admissions.v), [`FourCellBridge.v`](FourCellBridge.v), [`ThreeTestAdmissions.v`](ThreeTestAdmissions.v), [`ThreeTestPairBridge.v`](ThreeTestPairBridge.v), and [`ThreeTestConditionalStrata.v`](ThreeTestConditionalStrata.v) own the report's four-cell event model, union, conditional-admissions, dependence and three-test multiplicity theorems. Shared finite-event summation, moment and covariance operations reside in [the central Rocq library](../../../library/rocq/README.md). Specialized SPARK and Python source remains in the adjacent `ada/src/` and `scripts/` directories, using central exact event arithmetic where applicable.

Build using `sh scripts/compile_rocq.sh`; see the [report theorem inventory](../../../rocq/REPORT_THEOREM_INVENTORY.md). The new 55-theorem module covers eight atomic Boolean admission patterns,
finite three-way inclusion-exclusion, count distribution (zero through three),
three-event Fréchet/Bonferroni inequalities and sharp overlap bounds. The
probabilities all use the central `FiniteUnion.finite_prob` and
`FiniteSum.finite_sum`; no duplicated finite integral/union algorithm is
introduced. The companion `ThreeTestPairBridge.v` derives three normalized four-cell
projections (AB, AC and BC) and 84 theorems about marginalized overlap,
conditionals, association, binary independence, odds ratios, phi correlation,
Fréchet constraints and normalized union bounds. It reuses the canonical
`Admissions.TwoEventModel` results rather than replicating pairwise proofs
inside the three-test source. These discrete probability identities do not
establish a continuous Gaussian joint-tail model.

## D038x conditional selection and Simpson reversal

`ThreeTestConditionalStrata.v` creates six properly normalized
third-test-conditioned pair tables and proves 126 further results,
including generic conditional association, raw-cell independence,
conditional rates, odds ratios, selection bounds, and explicit
selection-dependent association-sign reversal.

The construction reuses `Admissions.TwoEventModel` and its proven
independence, conditional and Fréchet theorems. The eight-cell
`ThreeTestAdmissions` representation reuses centralized
`FiniteUnion.finite_prob` and `FiniteSum.finite_sum`. Strict positive
conditioning and denominator premises remain explicit.

In a concrete exact eight-outcome model, the pooled AB association is
positive but AB association is negative among both C-passers and
C-nonpassers. This is a finite Simpson paradox witness, not a
Gaussian-tail theorem or real-world IQ/admissions estimate.

## Complete AI disclosure

ChatGPT assisted with source placement and documentation. Kernel compilation validates only the declared theorem statements and hypotheses; empirical admissions rates and Gaussian assumptions remain unverified.
