# Rocq formalization of checked claims

This directory is an additional **Rocq kernel-checked mathematical layer**
for the two reports. **209 theorem, lemma and example declarations** in four
Rocq files have passed Rocq 9.2 compilation (including four internal
quotient-sign helper lemmas). It complements, rather than replaces, the existing Ada/SPARK
verification, Python/Deal contracts, and numerical integration checks.

## Reproduction

With Rocq Prover 9.2 and its standard library:

```sh
rocq compile rocq/Hoeflin.v
rocq compile rocq/Admissions.v
rocq compile rocq/FiniteUnion.v
rocq compile rocq/FiniteMoments.v
```

The GitHub Actions workflow at
[rocq-proofs.yml](../.github/workflows/rocq-proofs.yml) compiles the
whole proof scripts with a pinned `rocq/rocq-prover:9.2.0` image.
Compilation performs kernel checking, not merely parsing or syntax linting.
The workflow also rejects the syntactic use of `Admitted`, `Axiom`,
`Parameter`, `Conjecture` and `Abort` in proof sources.

There are no added logical axioms, admitted lemmas, opaque oracle results,
external SMT certificates, or `native_compute` trust extensions.

## Claims and exact theorem correspondences

| Report claim | Rocq statement(s) | Scope and qualification |
|---|---|---|
| [Hoeflin variance equation](../analyses/hoeflin-ferguson/analysis.md): average of distinct pairwise correlations suffices | `pair_average_variance`, `equicorrelation_variance`, `variance_alternative_form`, `equal_weight_variance_from_finite_covariances` | The last theorem derives the exact arbitrary-n equal-weight identity from finite probability weights, unit component variances, and an average off-diagonal covariance; identical pairwise correlations are unnecessary |
| Equal-weight variance at \(n=1\), \(\rho=0\), \(\rho=1\) | `one_test_variance`, `independent_tests_variance`, `perfectly_correlated_variance` | Exact real identities |
| Positive variance, variance between \(\rho\) and 1, sensitivity to average correlation | `variance_strictly_positive`, `variance_at_least_correlation`, `variance_at_most_one`, `variance_nondecreasing_in_correlation`, `variance_gap_to_limiting_correlation` | Explicit \(n\ge 1\), \(0\le\rho\le1\) or weaker hypotheses; does not validate observed correlations |
| Equal-weight variance sensitivity to battery size and population correlation | `variance_decreases_with_test_count`, `variance_strictly_decreases_with_test_count`, `variance_correlation_sensitivity`, `variance_of_two_equicorrelated_tests`, `variance_of_three_equicorrelated_tests` | These are exact algebraic monotonicity formulas at fixed correlation; they are not a claim that adding real-world tests leaves correlation fixed |
| Common-factor reliability and posterior-variance monotonicity | `latent_variance_denominator_positive`, `latent_variance_decreases_with_test_count`, `latent_reliability_increases_with_test_count` | Algebra conditional on the report's common-factor expressions, not their Gaussian derivation |
| Quantitative variance stabilization and factor decomposition | `doubling_battery_halves_variance_excess`, `nonnegative_correlation_variance_at_least_independent`, `variance_excess_bound_by_inverse_battery_size`, `latent_reliability_times_composite_variance`, `latent_posterior_times_composite_variance` | Exact at fixed average correlation; the latent reliability identities assume the report's specified factor expressions |
| IQ standardization and same-SD composite reporting | `iq_standardization_inversion`, `iq_report_standardization`, `equal_sd_composite_scale`, `standardized_160_sd15`, `standardized_160_sd16` | Exact algebra; standard deviations/divisors assumed nonzero |
| Normalized variance and threshold rescaling | `normalized_variance_is_one`, `threshold_recovered_after_normalization` | Uses an **assumed** variance and its nonzero squared divisor; not a distribution theorem |
| Latent-factor squared correlation and conditional-variance expressions | `latent_reliability_plus_posterior_variance`, `latent_reliability_nonnegative`, `latent_posterior_variance_nonnegative`, `latent_reliability_at_most_one`, and boundary cases | Algebra for the report's *given* expressions; **does not prove the Gaussian conditional-distribution derivation** |
| Finite expectation: linearity, constants, centering, and nonnegative means | `expectation_add`, `expectation_scale`, `expectation_affine`, `centered_score_has_zero_expectation`, `expectation_nonnegative` | Finite sums with explicit masses; normalization and nonnegativity required where stated |
| Finite covariance and variance laws | `covariance_symmetric`, `covariance_add_first`, `covariance_scale_second`, `variance_nonnegative`, `variance_of_two_score_sum` | Derived from definitions, not covariance axioms; variance nonnegativity requires nonnegative normalized weights |
| Weighted two-score variance and variance of the average | `variance_of_two_weighted_scores`, `variance_of_two_score_average`, `variance_of_two_unit_variance_average` | Exact, no normality; the unit-variance result requires unit component variances |
| Arbitrary finite weighted composite: variance is the quadratic form \(\sum_{i,j} w_i w_j\operatorname{Cov}(X_i,X_j)\) | `variance_of_general_weighted_sum`, `covariance_of_general_weighted_sums`, `expectation_of_general_weighted_sum` | Derived for any finite list of component functions on a *normalized finite probability space*; no Gaussian assumption |
| Concrete covariance-matrix representation and bilinear form | `covariance_row_as_vector_dot`, `covariance_double_sum_as_matrix_product`, `covariance_matrix_quadratic_form_identity`, `covariance_cross_matrix_bilinear_identity`, `covariance_matrix_quadratic_form_is_variance`, `covariance_matrix_is_positive_semidefinite` | Covariance entries are computed from finite expectations and expressed as real-valued row lists, proving the matrix-vector representation rather than postulating it |
| Cauchy–Schwarz derived from finite variance nonnegativity | `nonnegative_quadratic_discriminant`, `finite_covariance_cauchy_schwarz_squared`, `zero_variance_implies_zero_covariance_first`, `zero_variance_implies_zero_covariance_second`, `nonzero_covariance_implies_positive_variances` | Proves Cov(X,Y)² ≤ Var(X)Var(Y) by examining Var(X+tY) ≥ 0 for all real t, including the degenerate zero-variance case; normalized nonnegative finite weights are required |
| Fixed score basis and arbitrary real coefficient vectors | `weighted_basis_sum_as_combination`, `coefficients_of_combine`, `basis_of_combine`, `covariance_matrix_uses_only_basis`, `covariance_cross_matrix_uses_only_bases`, `fixed_basis_covariance_matrix_representation`, `fixed_basis_weighted_variance_identity`, `fixed_basis_covariance_matrix_positive_semidefinite` | The covariance matrix is defined **solely by the fixed score basis**, independently of the coefficient vector; proves Var(wᵀX)=wᵀΣw and wᵀΣw≥0 for every **matching-length** real coefficient list |
| Standardized finite-score covariance and perfect-correlation equality | `normalized_covariance_is_between_minus_one_and_one`, `centered_standardized_covariance_in_unit_interval`, `unit_covariance_one_iff_difference_has_zero_variance`, `unit_covariance_minus_one_iff_sum_has_zero_variance` | Correlation is within [−1,1] for provided strictly positive standard deviations whose squares equal the corresponding finite variances; the ±1 equality cases require both variances equal one |
| Finite covariance matrix positive semidefiniteness | `covariance_quadratic_form_nonnegative` | Follows from nonnegative variance for normalized nonnegative weights |
| Finite standardization has mean zero and IQ-style reporting has mean 100 | `mean_of_centered_standardized_score`, `mean_of_iq_reporting_scale` | Means are exact under normalized finite weights and nonzero scale parameters |
| Finite normalized covariance and two-/three-test averages | `covariance_of_centered_standardized_scores`, `self_covariance_of_standardized_score`, `variance_of_three_score_average`, `variance_of_three_standardized_score_average`, `variance_of_two_standardized_score_average` | Derives the two- and three-test variance formulas; the three-test case needs only the sum of pairwise correlations, not equal individual correlations |
| General finite equal-weight variance from unordered pair sums | `covariance_double_sum_second_cons`, `double_sum_diagonal_off_diagonal`, `variance_of_rescaled_unweighted_sum`, `diagonal_variance_sum_of_unit_scores`, `equal_weight_variance_from_finite_covariances` | Any finite battery of at least two unit-variance tests on one normalized finite reference population, with average pairwise covariance rho |
| Unit-variance pairwise covariance bounded by −1 and +1 | `covariance_at_most_half_sum_of_variances`, `covariance_at_least_negative_half_sum_of_variances`, `covariance_of_unit_variance_scores_bounded`, `average_of_two_unit_variance_scores_bounded` | Derived from positivity of the finite variance of score differences and sums; normalized nonnegative sample weights are essential |
| Feasible interval for the **average** pairwise correlation | `feasible_average_pair_correlation_lower_bound`, `covariance_row_sum_bounded_by_count`, `unordered_covariance_sum_bounded_by_pair_count`, `feasible_average_pair_correlation_upper_bound`, `feasible_average_pair_correlation_interval` | For a finite battery of n > 1 unit-variance scores, proves −1/(n−1) ≤ ρ̄ ≤ 1 without equal individual pairwise correlations |
| Standardization and IQ-style reporting variance | `variance_of_standardized_score`, `variance_of_iq_reporting_scale` | Requires nonzero divisor whose square equals the finite-model variance; does not establish norms or psychometric validity |
| [Towers event identity](../analyses/towers-multiple-test-admissions/analysis.md): union \(=p_A+p_B-J\) | `inclusion_exclusion`, `union_complement` | Derived from a four-cell finite probability space |
| Union and joint Fréchet bounds | `union_bound`, `union_at_most_one`, `union_at_least_first`, `union_at_least_second`, `both_at_most_first`, `both_at_most_second`, `frechet_lower_bound` | Any events, without a Gaussian model or independence |
| Distribution-free admission refinements | `exactly_one_nonnegative`, `exactly_one_at_most_either`, `union_equal_marginal_lower_bound`, `union_equal_marginal_upper_bound`, `excess_marginal_mass_forces_overlap`, `independent_equal_marginal_union` | Bounds and special-case identities require only explicit four-cell probabilities, with independence stated when used |
| Independence and conditional probabilities; zero-overlap cases | `independent_either_as_complement_product`, `independent_equal_marginals_as_complement_square`, `independent_conditional_B_equals_marginal`, `independent_conditional_A_equals_marginal`, `independent_exactly_one_formula`, `disjointness_iff_union_is_sum`, `complete_coverage_iff_no_failures`, and marginal/overlap bounds | Independence and nonzero conditioning-event masses are explicit hypotheses; no real-world independence is claimed |
| Exactly one pass versus either pass | `exactly_one_formula`, `exactly_one_vs_union`, `equal_marginal_union`, `equal_marginal_exactly_one` | Exact |
| Conditional denominators and failure complements | `conditional_B_numerator`, `conditional_A_numerator`, `both_conditional_denominators_agree`, `conditional_either_numerator`, `conditional_failure_complement`, and conditional bounds | Require strictly positive conditioning-event masses |
| Distinguish binary phi numerator and continuous Pearson correlation | `binary_indicator_covariance_numerator`, `binary_independence_criterion` | Proves the binary covariance numerator and independence criterion; **not** the numerical continuous/discrete correlation discrepancy |
| Published mixed-case 2.11% figure is impossible from marginals of 2% and 0.1% | `original_mixed_union_impossible` | Exact rational contradiction from the union bound |
| Marginal rates do not determine overlap or OR admission fraction | `same_marginals_different_joint`, `same_marginals_different_union` | Constructive four-cell counterexamples |
| Arbitrary number of admission routes: every marginal <= union <= sum of marginals and union <= 1 | `arbitrary_union_bound`, `arbitrary_union_contains_every_member`, `normalized_arbitrary_union_at_most_one`, and supporting lemmas in `FiniteUnion.v` | Explicit finite sample outcomes with nonnegative weights; no normality or independence |
| Repeated independent-attempt formula \(1-(1-p)^m\) | `independent_union_formula`, `independent_union_one`, `independent_union_two` | Induction on the independent-union recurrence; **not** an assertion that real retests are independent |
| BASIC grid node count, constant factors, quarter-point boundary shift | `grid_node_count`, `grid_scale_factors_cancel`, `half_point_grid_midpoint_shift` | Exact arithmetic only; does **not** certify numerical quadrature error |

## Proof boundaries

**Not formalized or certified** here: Gaussian joint or conditional
distribution properties; the normal CDF or its inverse; numerical bivariate
normal tail integrals and their rigorous enclosures; the stated numerical
one-in-a-million threshold; covariance/variance theorems for general
continuous or abstract measure-theoretic random variables; sample selection
effects; empirical test correlations;
measurement validity, reliability, clinical interpretations, and real-world
society admission policies.

In particular, the latent-factor formulas are only algebraically checked;
their statistical derivation requires a separate probability-theory
formalization. The two finite examples show non-identification of joint
probabilities by marginals; they do not establish any actual IQ-test dependence.

The Hoeflin finite moment model uses explicitly enumerated outcomes and
nonnegative masses summing to one; its universal finite-list weighted
covariance identity is a genuine derived theorem. It does not itself prove
that specific empirical IQ tests have the report's assumed covariance matrix.

The four-cell Towers model is a **constructed finite probability space**, not
a trusted abstract probability axiom. Its nonnegativity and total-mass-equals-one
properties are carried in the record, and examples construct those records
with checked arithmetic proofs. No data are imported into the kernel.

## Research extensions

The next valuable targets are: (1) rigorous finite-battery bounds for
standard deviations and score thresholds at fixed average correlation,
(2) covariance-matrix properties for indexed score bases and rank constraints,
(3) extending finite event and moment identities to abstract probability
measures, (4) theorem-level construction and normalization of bivariate
Gaussian densities and certified tail enclosures, and (5) Gaussian common-factor
conditional-moment theorems. Numerical tables must remain labeled numerical until certified
interval arithmetic is available.

This work is AI-generated and requires independent review of the
**mapping between the English report and the exact formal statements**,
even when the Rocq kernel accepts all proofs.
