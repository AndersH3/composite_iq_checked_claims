# Rocq formalization of checked claims

This directory is an additional **Rocq kernel-checked mathematical layer**
for the two reports. It complements, rather than replaces, the existing Ada/SPARK
verification, Python/Deal contracts, and numerical integration checks.

## Reproduction

With Rocq Prover 9.2 and its standard library:

```sh
rocq compile rocq/Hoeflin.v
rocq compile rocq/Admissions.v
```

The GitHub Actions workflow at
[rocq-proofs.yml](../.github/workflows/rocq-proofs.yml) compiles the
whole proof scripts with a pinned \`rocq/rocq-prover:9.2.0\` image.
Compilation performs kernel checking, not merely parsing or syntax linting.
The workflow also rejects the syntactic use of \`Admitted\`, \`Axiom\`,
\`Parameter\`, \`Conjecture\` and \`Abort\` in proof sources.

There are no added logical axioms, admitted lemmas, opaque oracle results,
external SMT certificates, or \`native_compute\` trust extensions.

## Claims and exact theorem correspondences

| Report claim | Rocq statement(s) | Scope and qualification |
|---|---|---|
| [Hoeflin variance equation](../analyses/hoeflin-ferguson/analysis.md): average of distinct pairwise correlations suffices | \`pair_average_variance\`, \`equicorrelation_variance\`, \`variance_alternative_form\` | Algebra conditional on the stated covariance-sum and pair-average identity; **not** a formal derivation from arbitrary random variables |
| Equal-weight variance at \(n=1\), \(\rho=0\), \(\rho=1\) | \`one_test_variance\`, \`independent_tests_variance\`, \`perfectly_correlated_variance\` | Exact real identities |
| Positive variance, variance between \(\rho\) and 1, sensitivity to average correlation | \`variance_strictly_positive\`, \`variance_at_least_correlation\`, \`variance_at_most_one\`, \`variance_nondecreasing_in_correlation\`, \`variance_gap_to_limiting_correlation\` | Explicit \(n\ge 1\), \(0\le\rho\le1\) or weaker hypotheses; does not validate observed correlations |
| IQ standardization and same-SD composite reporting | \`iq_standardization_inversion\`, \`iq_report_standardization\`, \`equal_sd_composite_scale\`, \`standardized_160_sd15\`, \`standardized_160_sd16\` | Exact algebra; standard deviations/divisors assumed nonzero |
| Normalized variance and threshold rescaling | \`normalized_variance_is_one\`, \`threshold_recovered_after_normalization\` | Uses an **assumed** variance and its nonzero squared divisor; not a distribution theorem |
| Latent-factor squared correlation and conditional-variance expressions | \`latent_reliability_plus_posterior_variance\`, \`latent_reliability_nonnegative\`, \`latent_posterior_variance_nonnegative\`, \`latent_reliability_at_most_one\`, and boundary cases | Algebra for the report's *given* expressions; **does not prove the Gaussian conditional-distribution derivation** |
| [Towers event identity](../analyses/towers-multiple-test-admissions/analysis.md): union \(=p_A+p_B-J\) | \`inclusion_exclusion\`, \`union_complement\` | Derived from a four-cell finite probability space |
| Union and joint Fréchet bounds | \`union_bound\`, \`union_at_most_one\`, \`union_at_least_first\`, \`union_at_least_second\`, \`both_at_most_first\`, \`both_at_most_second\`, \`frechet_lower_bound\` | Any events, without a Gaussian model or independence |
| Exactly one pass versus either pass | \`exactly_one_formula\`, \`exactly_one_vs_union\`, \`equal_marginal_union\`, \`equal_marginal_exactly_one\` | Exact |
| Conditional denominators and failure complements | \`conditional_B_numerator\`, \`conditional_A_numerator\`, \`both_conditional_denominators_agree\`, \`conditional_either_numerator\`, \`conditional_failure_complement\`, and conditional bounds | Require strictly positive conditioning-event masses |
| Distinguish binary phi numerator and continuous Pearson correlation | \`binary_indicator_covariance_numerator\`, \`binary_independence_criterion\` | Proves the binary covariance numerator and independence criterion; **not** the numerical continuous/discrete correlation discrepancy |
| Published mixed-case 2.11% figure is impossible from marginals of 2% and 0.1% | \`original_mixed_union_impossible\` | Exact rational contradiction from the union bound |
| Marginal rates do not determine overlap or OR admission fraction | \`same_marginals_different_joint\`, \`same_marginals_different_union\` | Constructive four-cell counterexamples |
| Repeated independent-attempt formula \(1-(1-p)^m\) | \`independent_union_formula\`, \`independent_union_one\`, \`independent_union_two\` | Induction on the independent-union recurrence; **not** an assertion that real retests are independent |
| BASIC grid node count, constant factors, quarter-point boundary shift | \`grid_node_count\`, \`grid_scale_factors_cancel\`, \`half_point_grid_midpoint_shift\` | Exact arithmetic only; does **not** certify numerical quadrature error |

## Proof boundaries

**Not formalized or certified** here: Gaussian joint or conditional
distribution properties; the normal CDF or its inverse; numerical bivariate
normal tail integrals and their rigorous enclosures; the stated numerical
one-in-a-million threshold; covariance/variance theorems for arbitrary
random variables; sample selection effects; empirical test correlations;
measurement validity, reliability, clinical interpretations, and real-world
society admission policies.

In particular, the latent-factor formulas are only algebraically checked;
their statistical derivation requires a separate probability-theory
formalization. The two finite examples show non-identification of joint
probabilities by marginals; they do not establish any actual IQ-test dependence.

The four-cell Towers model is a **constructed finite probability space**, not
a trusted abstract probability axiom. Its nonnegativity and total-mass-equals-one
properties are carried in the record, and examples construct those records
with checked arithmetic proofs. No data are imported into the kernel.

## Research extensions

The next valuable targets are: (1) finite-space proofs of variance/covariance
of weighted sums; (2) theorem-level construction and normalization of
bivariate Gaussian densities; (3) verified normal-tail numerical bounds;
(4) an inductive arbitrary-number-of-tests union bound with an explicit
finite event-space model; and (5) Gaussian common-factor conditional-moment
theorems. Numerical tables must remain labeled numerical until certified
interval arithmetic is available.

This work is AI-generated and requires independent review of the
**mapping between the English report and the exact formal statements**,
even when the Rocq kernel accepts all proofs.
