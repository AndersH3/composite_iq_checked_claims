# Rocq coverage

Researcher/requester: Anders Hellström.

The algebraic module covers variance expansion, domain factors, example mixture and block averages, regression arithmetic, and affine contrast cancellation. It does not establish the Gaussian law, density integrals, Jensen inequality, order statistics, orthant identity or measure-theoretic conditioning. These have written proofs in the companion report; their continuous-probability formalization remains open. No proof placeholders or new axioms are used in the IQ algebra module. All 16 algebra scripts compiled on Rocq 9.3.0 at 799af85.

The expanded module also reuses `FiniteSum.finite_sum_member_le` for the squared-gap bound and Stdlib absolute-value lemmas for affine invariance. It adds heterogeneous variance nonnegativity, a two-component scale inequality, and exact parallel-variance pooling. All six additional scripts compiled at 799af85. Existing `EquicorrelationSpectral` and `SampleContrastCauchy` supply reusable deterministic algebra; the continuous Gaussian distributional obligations remain open.

The pooling lemma now instantiates `PooledMomentsAlgebra.pooled_between_centered_identity` rather than reproving the variance identity independently. This is a notation bridge, not an additional independently established probability result.

Computer10 kernel compilation on Rocq 9.3.0 reached `iq_range_pair_square_bound` in the prior source revision and failed due to higher-order unification. The earlier declarations in that module were accepted before this error. The corrected application explicitly supplies the existing finite-sum lemma's integrand; it was accepted in the subsequent compilation.

The second computer10 compilation at `6f167731968e9eca8c9c755dbf18eb0a7dd21629` passed the explicit finite-sum application and stopped at `iq_gap_heterogeneous_variance_nonnegative`, specifically automated difference-square positivity. Thus the first 13 declarations were accepted in this module. This patch uses Stdlib `Rle_0_sqr` explicitly in both remaining square arguments and normalizes the pooling identity to the library's exact notation. The next computer10 run at 799af85 compiled all 45 canonical modules with Rocq 9.3.0, including all 16 IQ algebra scripts. Continuous probability obligations remain separate and open.

See the [canonical verification record](../../../rocq/README.md#computer10-canonical-kernel-verification--november-26-2026) for the scope and revision of the successful run.

Two new weighted-scale Jensen certificates strengthen the finite-mixture non-identification argument. Both compiled at `0b22b3f64c6429d04071b5c5f56028e86a3b8301` on Rocq 9.3.0, bringing the verified IQ algebra inventory to 18 declarations. The MathComp density-factorization candidates and FormalML transfer are separate probability-library modules.
