# Rocq coverage

Researcher/requester: Anders Hellström.

The algebraic module covers variance expansion, domain factors, example mixture and block averages, regression arithmetic, and affine contrast cancellation. It does not establish the Gaussian law, density integrals, Jensen inequality, order statistics, orthant identity or measure-theoretic conditioning. These have written proofs in the companion report; machine formalization and kernel verification remain open. No proof placeholders or new axioms are used. The module is not yet compiler-verified.

The expanded module also reuses `FiniteSum.finite_sum_member_le` for the squared-gap bound and Stdlib absolute-value lemmas for affine invariance. It adds heterogeneous variance nonnegativity, a two-component scale inequality, and exact parallel-variance pooling. All six additional scripts are draft, not kernel-verified. Existing `EquicorrelationSpectral` and `SampleContrastCauchy` supply reusable deterministic algebra; the continuous Gaussian distributional obligations remain open.

The pooling lemma now instantiates `PooledMomentsAlgebra.pooled_between_centered_identity` rather than reproving the variance identity independently. This is a notation bridge, not an additional independently established probability result.
