# Rocq coverage

Researcher/requester: Anders Hellström.

The algebraic module covers variance expansion, domain factors, example mixture and block averages, regression arithmetic, and affine contrast cancellation. It does not establish the Gaussian law, density integrals, Jensen inequality, order statistics, orthant identity or measure-theoretic conditioning. These have written proofs in the companion report; machine formalization and kernel verification remain open. No proof placeholders or new axioms are used. The module has been partially kernel-checked on Rocq 9.3.0; the full compilation is pending.

The expanded module also reuses `FiniteSum.finite_sum_member_le` for the squared-gap bound and Stdlib absolute-value lemmas for affine invariance. It adds heterogeneous variance nonnegativity, a two-component scale inequality, and exact parallel-variance pooling. The first three of the six additional scripts were accepted by the compiler at 6f16773; the final three still require checking. Existing `EquicorrelationSpectral` and `SampleContrastCauchy` supply reusable deterministic algebra; the continuous Gaussian distributional obligations remain open.

The pooling lemma now instantiates `PooledMomentsAlgebra.pooled_between_centered_identity` rather than reproving the variance identity independently. This is a notation bridge, not an additional independently established probability result.

Computer10 kernel compilation on Rocq 9.3.0 reached `iq_range_pair_square_bound` in the prior source revision and failed due to higher-order unification. The earlier declarations in that module were accepted before this error. The corrected application explicitly supplies the existing finite-sum lemma's integrand and requires a new full compilation. Do not treat the remaining three theorem scripts as checked yet.

The second computer10 compilation at `6f167731968e9eca8c9c755dbf18eb0a7dd21629` passed the explicit finite-sum application and stopped at `iq_gap_heterogeneous_variance_nonnegative`, specifically automated difference-square positivity. Thus the first 13 declarations were accepted in this module. This patch uses Stdlib `Rle_0_sqr` explicitly in both remaining square arguments and normalizes the pooling identity to the library's exact notation. A fresh Rocq run is needed; neither the full algebra module nor the continuous probability obligations are declared verified.
