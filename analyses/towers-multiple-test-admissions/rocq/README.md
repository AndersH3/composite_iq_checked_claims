# Towers admissions specialized Rocq proofs

**Author:** Anders Hellström.

> **AI disclosure:** This module-ownership documentation was AI-assisted.

[`Admissions.v`](Admissions.v), [`FourCellBridge.v`](FourCellBridge.v), [`ThreeTestAdmissions.v`](ThreeTestAdmissions.v), [`ThreeTestPairBridge.v`](ThreeTestPairBridge.v), and [`ThreeTestConditionalStrata.v`](ThreeTestConditionalStrata.v), and [`ThreeTestSelectionDecomposition.v`](ThreeTestSelectionDecomposition.v), and [`ThreeTestReversalCriteria.v`](ThreeTestReversalCriteria.v) own the report's four-cell event model, union, conditional-admissions, dependence and three-test multiplicity theorems. Shared finite-event summation, moment and covariance operations reside in [the central Rocq library](../../../library/rocq/README.md). Specialized SPARK and Python source remains in the adjacent `ada/src/` and `scripts/` directories, using central exact event arithmetic where applicable.

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

## D039x pooled versus conditional association

`ThreeTestSelectionDecomposition.v` proves 60 exact, route-specific
AB/AC/BC results by reusing the 44 common algebraic theorems from
[`TwoStratumAssociation.v`](../../../library/rocq/TwoStratumAssociation.v).
The central identity decomposes the pooled 2×2 association determinant into
an opposite-stratum-weighted within-group contribution and a product
of signed differences in conditional marginal admission rates.
Consequently, test selection can create or reverse pairwise dependence.
All claims rely only on explicitly normalized eight-outcome masses, with
strictly positive selected and nonselected stratum probabilities when
division or sign equivalence is involved.

## D040x exact selection-reversal conditions

`ThreeTestReversalCriteria.v` connects the central 50-theorem
[`TwoStratumReversal.v`](../../../library/rocq/TwoStratumReversal.v)
library to the eight-outcome AB/AC/BC admissions model. Its 75
route-specific theorems specify necessary-and-sufficient pooled sign
thresholds and conditional-independence criteria, together with
necessary signs of selected-versus-unselected admission-rate gaps for
positive or negative Simpson reversal. Selected and other-stratum
probabilities must both be strictly positive where division or
sign-equivalence conditions are used. Every raw determinant corresponds
to a concrete pair of disjoint Boolean event cells.

## Complete AI disclosure

ChatGPT assisted with source placement and documentation. Kernel compilation validates only the declared theorem statements and hypotheses; empirical admissions rates and Gaussian assumptions remain unverified.


## D041x — trivariate covariance algebra

`ThreeTestSchur.v` contains 81 conditional pair-specific theorem scripts
(AB|C, AC|B, BC|A) and imports the canonical 27-theorem
`library/rocq/TrivariateSchur.v`. Each checks exact real Schur-covariance
identities or inequalities and explicitly states any conditioning-variance
hypotheses. It does **not** construct a joint Gaussian law, prove conditional
normal distributions or evaluate any normal tail. The source and comments are
AI-assisted; validity depends on the pinned Rocq 9.2 kernel.
