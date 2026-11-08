# Rocq formalization of checked claims

This directory is an additional **Rocq kernel-checked mathematical layer**
for the two reports. **329 theorem, lemma and example declarations** in seven
Rocq files have passed Rocq 9.2 compilation (including auxiliary proof lemmas). It complements, rather than replaces, the existing Ada/SPARK
verification, Python/Deal contracts, and numerical integration checks.

## Reproduction

With Rocq Prover 9.2 and its standard library, compile from the
`rocq/` directory so the shared local modules are on the load path:

```sh
cd rocq
rocq compile FiniteSum.v
rocq compile Hoeflin.v
rocq compile Admissions.v
rocq compile FiniteUnion.v
rocq compile FiniteMoments.v
rocq compile FiniteBridge.v
rocq compile FourCellBridge.v
```

The GitHub Actions workflow at
[rocq-proofs.yml](../.github/workflows/rocq-proofs.yml) compiles the
whole proof scripts with a pinned `rocq/rocq-prover:9.2.0` image.
Compilation performs kernel checking, not merely parsing or syntax linting.
The workflow also runs
[`scripts/check_rocq_documentation.sh`](../scripts/check_rocq_documentation.sh)
to require an explanatory header in each module and a declaration-specific
proof comment with mathematical meaning, explicit statement, assumptions,
proof method, library reuse and scope. The checker is a shell CI utility using Python's standard library and can
be run from the repository root without extra dependencies:

```sh
bash scripts/check_rocq_documentation.sh
```

The workflow also rejects the syntactic use of `Admitted`, `Axiom`,
`Parameter`, `Conjecture` and `Abort` in proof sources.

There are no added logical axioms, admitted lemmas, opaque oracle results,
external SMT certificates, or `native_compute` trust extensions.

## Standard-library reuse

For elementary calculations, the proof modules now reuse Rocq 9.2's
**standard library** and a single shared finite real-sum wrapper rather
than maintaining separate recursive or list-fold algebra:

- **`FiniteSum.v` / `Stdlib.List`**: a single transparent `finite_sum`
  implements finite integration with `map` and `fold_right`. Both
  `FiniteUnion.v` and `FiniteMoments.v` reuse its extensionality,
  additivity, scaling, nonnegativity, order, concatenation and
  permutation proofs. Weighted composites, covariance sums, list-vector
  dot products and event marginals use the same fold. `List.combine`
  pairs basis scores and coefficients with explicit equal-length
  hypotheses whenever truncation would affect a theorem.
- **`Stdlib.Reals`**: `sqrt`, `sqrt_pos`, `sqrt_sqrt`,
  `sqrt_lt_R0`, `sqrt_le_1`, `sqrt_lt_1`, and `sqrt_1`
  supply the square-root definition, fundamental properties, and
  order comparisons in the composite standard-deviation results.
- **`Stdlib.Sorting.Permutation`**: `Permutation_in` and
  `Permutation_sym` establish finite union probability invariance under
  reordering; `Stdlib.List.existsb_exists` handles event-family membership.
- **`Stdlib.List`**: `length_map`, `in_map_iff`, `combine_split`, `list_prod`, `in_prod`, and `length_prod` establish covariance-matrix
  dimensions without project-specific list-indexing recursion.
- **`Stdlib.Lra` / `Stdlib.Psatz`** and the standard `ring` /
  `field` tactics handle ordinary real arithmetic.

Report-specific covariance, variance, weighted-component, and event
definitions remain explicit to make their probabilistic assumptions
visible. **`FiniteBridge.v`** proves that finite-event probabilities are
finite expectations of Boolean indicators. It derives Bernoulli
variance, event-indicator covariance and the finite independence
criterion without adding independence or measure axioms.

A module-by-module inventory, migration criteria and deferred library
candidates are documented in [LIBRARY_AUDIT.md](LIBRARY_AUDIT.md). This is
an audited **incremental refactor**, not a claim that every proof was
rewritten or that the finite probability model was replaced. This stage adds **no external dependency** just to reproduce
functionality already in the standard library. More advanced continuous
probability and matrix formalization should evaluate established Rocq
mathematics libraries before introducing new foundational code.

## November 7 continuation: finite bridges and library refactoring

The Rocq 9.2 kernel has checked **289 declarations**, counted directly as
`Theorem`, `Lemma` and `Example` statements in the six current source files
(`Hoeflin` 64, `Admissions` 67, `FiniteUnion` 30,
`FiniteMoments` 102, `FiniteSum` 12, and `FiniteBridge` 14).
This corrects the previous prose count of 65 in `Hoeflin.v`;
the source contains 64 named theorem declarations.

- The shared `FiniteSum` module now proves `finite_sum_map`,
  `finite_sum_neg`, `finite_sum_sub`, and `finite_sum_rev`.
  These reuse `Stdlib.List.map_map`, the previously proved sum
  linearity, and `Stdlib.Sorting.Permutation.Permutation_rev`;
  no independent summation recursion was introduced.
- Three `FiniteUnion` proofs now use the existing shared zero-sum
  identity and `Stdlib.Bool.orb_false_r`, replacing an explicit
  sample-list induction and Boolean case analyses.
- Five new `FiniteBridge` statements prove the universal
  Bernoulli upper variance bound of `1/4`, complement invariance
  of indicator variance under normalized total mass, and the
  covariance sign changes under complementing one or both events.
  The proofs reuse earlier finite covariance extensionality,
  shift invariance, scaling and symmetry rather than recalculating
  the underlying finite sums.

The `1/4` variance upper bound is an algebraic identity for
`p(1-p)`; interpreting this quantity as a nonnegative variance
still requires appropriate sample-weight hypotheses. Complement
covariance and variance formulas explicitly require total mass one.
All previous theorem statements are preserved. No claim is made
about Gaussian conditioning, empirical IQ psychometrics or continuous
probability measures.

## November 8 continuation: concrete four-cell interpretation

At the four-cell bridge milestone, the seven modules contained **311 named theorem, lemma and example
declarations** (64 Hoeflin, 67 Admissions, 38 FiniteUnion,
103 FiniteMoments, 12 FiniteSum, 14 FiniteBridge, 13 FourCellBridge).
These are source-counted declarations, not a count of independent
mathematical insights. Existing theorem statements in the original six
modules were compared against commit `a2f6427` and are unchanged.

- **`FourCellBridge.v` (13 theorems):** represents the four report-specific
  admissions cells as `bool * bool`. Uses the standard
  `Stdlib.List.list_prod` operation to enumerate the outcomes, and
  `in_prod` and `length_prod` to check coverage and cardinality.
  The four weights are exactly the report's joint, A-only, B-only and
  neither masses. Their normalization and nonnegativity come from
  `Admissions.TwoEventModel`, with no added axioms.
- The bridge proves exact equivalence of both marginals, intersection,
  union, and exactly-one admission mass with the original definitions.
  It then reuses `FiniteBridge` to connect the four-cell model with
  finite indicator covariance and both Bernoulli variance identities.
  The resulting covariance-zero condition agrees with the explicit
  four-cell independence criterion.
- **`FiniteUnion.v` (+8 theorems):** derives true/false event masses,
  sample concatenation, sample permutation, union sample permutation,
  event-family marginal-sum permutation, event monotonicity and the
  normalized unit-interval probability bound. These use shared
  `FiniteSum` facts and `Stdlib.Sorting.Permutation` rather than
  custom list algorithms. The empty event-family proof is reduced to
  the established false-event theorem.
- **`FiniteMoments.v` (+1 generic helper):** replaces two duplicated
  `combine` projection inductions with `Stdlib.List.combine_split`
  and a single checked `split`-to-projection lemma. The existing
  expectation-subtraction theorem now uses the shared
  `FiniteSum.finite_sum_sub` directly.

This bridge is an explicit **finite** probabilistic interpretation;
it does not establish continuous distributions, Gaussian tail
integrals, psychometric validity, or statistical calibration. It does
not require a MathComp or measure-theory dependency. The
report-specific four-cell declarations remain separate from the
library-backed Boolean-product interpretation.

## November 8 continuation: support-aware finite sums and general event bounds

At the preceding support-aware milestone, the seven modules contained **320 kernel-checked theorem,
lemma and example declarations**: `Hoeflin` 64, `Admissions` 67,
`FiniteUnion` 43, `FiniteMoments` 103, `FiniteSum` 16,
`FiniteBridge` 14 and `FourCellBridge` 13. This is **nine additional
declarations** compared with the preceding 311-declaration milestone.

**Refactoring to established Rocq library facilities:**

- `finite_sum_ext_in` uses Rocq Stdlib `List.map_ext_in` to establish
  equality of finite sums when integrands agree **only on enumerated
  outcomes**. The old global `finite_sum_ext` remains as a wrapper;
  its original type is unchanged.
- `finite_sum_member_le` proves that a nonnegative supported
  contribution cannot exceed its containing finite sum.
  `finite_sum_nonnegative_zero` derives the termwise zero implication
  from this bound. The corresponding `FiniteMoments` theorem now
  delegates to it rather than duplicating a list induction.
- `finite_sum_swap` is a reusable finite double-sum interchange identity,
  derived from the existing addition/zero laws. The report-specific
  `interchange_finite_sums` now delegates to the generic theorem,
  replacing a separate induction over event routes.

**New distribution-free finite-event consequences:**

- `finite_prob_zero_iff_no_positive_mass_support`: for nonnegative
  outcome weights, an event has mass zero precisely when every
  enumerated outcome satisfying the event has zero weight.
- `finite_prob_positive_of_positive_support`: positive-weight
  support for the event implies positive event mass.
- `finite_intersection_at_most_first`,
  `finite_intersection_at_most_second`, and
  `finite_frechet_lower_bound`: the intersection probability is
  bounded by both marginals, and by the Fréchet lower bound
  `P(A) + P(B) - 1`. These results reuse Boolean conjunction,
  generic monotonicity, inclusion-exclusion and normalized
  unit-interval bounds.

All **311 previously named declarations retain their exact statements**;
their source signatures were compared with the prior milestone commit
`82c2806`. No new axioms or `Admitted` proofs were introduced.
The mathematical scope remains finite weighted samples; only
nonnegative and, where explicitly required, normalized weights
support a probabilistic interpretation. Gaussianity and empirical
IQ-test validity are not claimed.

## November 8 continuation: reusing constant sums and weighted covariance proofs

At the preceding covariance-refactoring milestone, the seven-module source contained **325 kernel-checked declarations**:
`Hoeflin` 64, `Admissions` 67, `FiniteUnion` 43,
`FiniteMoments` 107, `FiniteSum` 17,
`FiniteBridge` 14 and `FourCellBridge` 13.
There are **five new declarations** beyond the earlier 320-result
milestone, and seven existing proofs were refactored without changing
their statements.

- **`FiniteSum.finite_sum_const`:** the sum of a constant over a
  finite list equals its length times the constant. The generic proof
  uses Rocq's list fold, `INR`, `S_INR`, and real ring arithmetic.
  `diagonal_variance_sum_of_unit_scores` now reuses this theorem and
  support-aware `finite_sum_ext_in`, replacing its unit-score induction.
- **Covariance row bound:** `covariance_row_sum_bounded_by_count`
  now follows from `FiniteSum.finite_sum_monotone`,
  `finite_sum_const`, and the already checked pairwise unit-variance
  covariance bound. Its list induction has been removed.
- **Double covariance sum:** `covariance_double_sum_second_cons`
  now uses finite-sum addition and scalar covariance symmetry,
  rather than a list induction. The new
  `covariance_double_sum_symmetric` theorem uses the shared finite
  Fubini law (`finite_sum_swap`) and covariance symmetry.
- **Expectation and both covariance batteries:**
  `expectation_of_general_weighted_sum` now applies
  `finite_sum_swap` and `finite_sum_scale`, without a separate
  weighted-component induction.
  `covariance_of_general_weighted_sums` uses the previously checked
  covariance row theorem and symmetry.
  `covariance_of_sum_scores` similarly reuses the single-battery
  covariance theorem and symmetry.
- **Unweighted–weighted bridge:** two new lemmas,
  `unweighted_scores_as_linear_combination` and
  `unweighted_covariance_row_as_weighted`, use
  `Stdlib.List.map` and `FiniteSum.finite_sum_map`. They show that
  a score battery is the existing weighted-composite model with every
  coefficient equal to one. Thus `covariance_with_sum_scores`
  delegates to `covariance_of_general_weighted_second` instead of
  repeating another induction.
- **Cross-matrix identity:** the new
  `covariance_cross_matrix_bilinear_swap` derives symmetry under
  exchanging the two bases and coefficient vectors from the existing
  cross-matrix correspondence and covariance symmetry. No new
  transpose implementation or matrix axioms are needed.

In total, **seven domain-specific list induction proofs** were replaced
with established shared lemmas and standard list operations. The
existing `unordered_covariance_sum` recursion remains intentional:
its terms depend on the progressively shortened list suffix, so it
does not have the same semantics as a plain map/fold over the
original list.

All **320 previously named theorem, lemma and example statements** are
preserved, with no new `Admitted` placeholders or axioms. These
results establish finite algebraic identities only; they do not imply
Gaussian tail bounds, empirical IQ-score reliability or continuous
measure-theoretic results.

## November 8 continuation: complete theorem documentation and standard list filtering

**At that milestone, the kernel-checked proof inventory was 328 named theorem, lemma and
example declarations** in seven modules (`Hoeflin` 64,
`Admissions` 67, `FiniteUnion` 45, `FiniteMoments` 107,
`FiniteSum` 18, `FiniteBridge` 14, and `FourCellBridge` 13).
One additional `Local Lemma` in `Hoeflin.v` is kernel-checked but
excluded from the conventional top-level inventory, bringing the total
number of proof declarations including that helper to **329**.

**At that milestone, all 385 named declarations** (including definitions, records and
helper declarations) across the seven `.v` files now have
declaration-local Rocq `(** ... *)` comments. Each comment records:

- its mathematical role and the precise statement/construction;
- hypotheses, positivity/normalization/dimension conditions, where used;
- proof or implementation method and reused library facilities;
- the limited mathematical interpretation (finite sums versus unproved
  continuous distributions or empirical validity).

Each proof source starts with a comprehensive module header giving its
purpose, mathematical model, imports, trust boundaries, and reproduction
information. No proof terms or previously declared proposition types were
changed by the documentation-only commits. The separate static
documentation-checking script is enforced in GitHub Actions **before**
Rocq kernel checking. The checker is implemented as a shell utility rather than adding a new
Python source module, preserving the historical source-pinned Python
Deal/SPARK inventory and all existing contract quality gates.

Three small library-backed proof additions precede the documentation
pass: `FiniteSum.finite_sum_filter` proves that summing over
`Stdlib.List.filter p xs` equals summing `if p x then f x else 0`
over the original list. `FiniteUnion.finite_prob_as_filtered_mass`
uses this result to identify event mass with the weight sum over
filtered outcomes, without a nonnegativity or normalization
assumption. `FiniteUnion.finite_prob_event_ext_on_samples` uses
`FiniteSum.finite_sum_ext_in` to show event mass depends only on
event membership at the sampled outcomes. These results add no
recursive filter, measure, axiom, or `Admitted` proof.

All **325** previously named public theorem/lemma/example propositions
remain intact. The previously checked Rocq 9.2 math source was
extended only by the three stated theorems. The current formalization
remains finite and algebraic.

## Complete proof-script refactor review and shared zip/map consolidation

The current seven-module source has **329 public theorem/lemma/example
declarations** (Hoeflin 64; Admissions 67; FiniteUnion 45;
FiniteMoments 107; FiniteSum 19; FiniteBridge 14; FourCellBridge 13).
One existing `Local Lemma` in `Hoeflin.v` is also kernel-checked:
**330 proof declarations**, or **332 actual `Proof.` scripts** when
the two `Admissions.TwoEventModel` record constructors proved with
`Defined.` are included. **All 386 named declarations** have
individual Rocq documentation comments and each `.v` file has a
detailed explanatory header.

The exhaustive [proof-refactor register](PROOF_REFACTOR_REGISTER.md)
accounts for every one of those **332 scripts** across seven modules.
It records the used proof methods, Stdlib and shared-lemma
dependencies, and the disposition of scripts already optimal with
respect to library reuse. It distinguishes proof scripts that have
actually been rewritten from scripts inspected and retained because
they already use appropriate library laws. The CI documentation gate
now checks the register **name by name and in source order**; merely
claiming a complete review does not satisfy that gate.

Additional proof-level consolidations, preserving all previous
proposition types:

- `finite_sum_monotone`: the previous list induction is replaced with
  `finite_sum_nonnegative`, pointwise difference, `finite_sum_sub`
  and `Lra`.
- `finite_sum_zero`: the previous list induction is replaced by
  specializing the general `finite_sum_const` lemma at zero.
- `FiniteSum.finite_sum_zip_map`: one new generic identity
  connects `List.combine (map f xs) (map g xs)` with
  `map (fun x => (f x,g x)) xs` at the level of shared finite sums.
  It is implemented using **Stdlib.List** operations rather than a
  parallel custom recursive zip or score-sum algorithm.
- `covariance_row_as_vector_dot` and
  `covariance_double_sum_as_matrix_product`: both previously had
  separate inductions over weighted-score component lists; they now
  delegate to the generic `finite_sum_zip_map` and the existing
  `covariance_row_as_vector_dot` correspondence, respectively.

After these replacements, only **15 explicitly structural induction
scripts** remain. They implement basic fold algebra in
`FiniteSum.v`, the `Nat.iter` independence recurrence in
`Admissions.v`, and genuinely list/suffix-dependent covariance
arguments in `FiniteMoments.v`. Replacing those with a new bespoke
library would add code rather than reuse established functionality.
The full list is in the refactor register.

A complete *inspection and refactor-decision pass* of every proof
script has been performed, but **this does not mean that every script
was rewritten**: exact `reflexivity` proofs and direct uses of
`Stdlib.Reals`, `Lra`, `Psatz`, `ring`, `field`, and the checked
bridges have been retained deliberately. No new project axiom,
`Admitted`, continuous probability construction, or unpinned package
is involved. Kernel checking remains the decisive verification.

## Claims and exact theorem correspondences

| Report claim | Rocq statement(s) | Scope and qualification |
|---|---|---|
| [Hoeflin variance equation](../analyses/hoeflin-ferguson/analysis.md): average of distinct pairwise correlations suffices | `pair_average_variance`, `equicorrelation_variance`, `variance_alternative_form`, `equal_weight_variance_from_finite_covariances` | The last theorem derives the exact arbitrary-n equal-weight identity from finite probability weights, unit component variances, and an average off-diagonal covariance; identical pairwise correlations are unnecessary |
| Equal-weight variance at \(n=1\), \(\rho=0\), \(\rho=1\) | `one_test_variance`, `independent_tests_variance`, `perfectly_correlated_variance` | Exact real identities |
| Positive variance, variance between \(\rho\) and 1, sensitivity to average correlation | `variance_strictly_positive`, `variance_at_least_correlation`, `variance_at_most_one`, `variance_nondecreasing_in_correlation`, `variance_gap_to_limiting_correlation` | Explicit \(n\ge 1\), \(0\le\rho\le1\) or weaker hypotheses; does not validate observed correlations |
| Equal-weight variance sensitivity to battery size and population correlation | `variance_decreases_with_test_count`, `variance_strictly_decreases_with_test_count`, `variance_correlation_sensitivity`, `variance_of_two_equicorrelated_tests`, `variance_of_three_equicorrelated_tests` | These are exact algebraic monotonicity formulas at fixed correlation; they are not a claim that adding real-world tests leaves correlation fixed |
| Common-factor reliability and posterior-variance monotonicity | `latent_variance_denominator_positive`, `latent_variance_decreases_with_test_count`, `latent_reliability_increases_with_test_count` | Algebra conditional on the report's common-factor expressions, not their Gaussian derivation |
| Positive reporting cutoff response to average correlation | `positive_cutoff_nondecreasing_in_correlation`, `positive_cutoff_strictly_increases_in_correlation` | Follows from the proved SD monotonicity and Stdlib real-order compatibility; assumes fixed test count and nonnegative/positive cutoff multipliers |
| Explicit epsilon threshold for fixed average correlation | `fixed_correlation_variance_epsilon_bound`, `fixed_correlation_variance_epsilon_after_threshold` | If n > (1−rho)/epsilon with rho ≤ 1 and epsilon > 0, proves 0 ≤ V(n,rho)−rho < epsilon; this is a conditional real-arithmetic bound at **fixed** rho, not a claim about changing correlations in observed test batteries |
| Quantitative variance stabilization and factor decomposition | `doubling_battery_halves_variance_excess`, `nonnegative_correlation_variance_at_least_independent`, `variance_excess_bound_by_inverse_battery_size`, `latent_reliability_times_composite_variance`, `latent_posterior_times_composite_variance` | Exact at fixed average correlation; the latent reliability identities assume the report's specified factor expressions |
| Composite standard deviation: standard-library square root and boundaries | `composite_standard_deviation_nonnegative`, `composite_standard_deviation_squared`, `composite_standard_deviation_at_zero_correlation`, `composite_standard_deviation_at_perfect_correlation`, `composite_standard_deviation_positive` | Uses Rocq's `sqrt` and its library lemmas; requires a feasible positive-variance parameter range where stated |
| Composite SD comparison under fixed average correlation | `composite_standard_deviation_nondecreasing_in_correlation`, `composite_standard_deviation_nonincreasing_in_test_count`, `composite_standard_deviation_strictly_decreases_with_test_count`, `composite_standard_deviation_strictly_increases_in_correlation` | Exact algebra followed by monotonicity of `sqrt`; the changes are conditional on keeping the parameter rho fixed as test count changes |
| Reporting-threshold algebra | `standardized_affine_cutoff_round_trip`, `positive_scale_preserves_cutoff_order`, `composite_standardized_cutoff_round_trip`, `positive_cutoff_nonincreasing_with_test_count` | Exact real identities and inequalities only; no Gaussian tail integral or empirical cutoff certified |
| Composite SD bounds against unit and independent-test baselines | `composite_standard_deviation_at_most_one`, `composite_standard_deviation_at_least_sqrt_correlation`, `composite_standard_deviation_at_least_independent_baseline`, `composite_standard_deviation_strictly_below_one` | For n ≥ 1 and 0 ≤ rho ≤ 1 unless stronger hypotheses are stated; no quantile or tail-probability implication is certified |
| Reporting-score monotonicity under positive normalization and nonnegative IQ scale | `standardize_preserves_order`, `iq_report_preserves_order`, `standardized_iq_reporting_preserves_order` | Exact real order preservation for positive standardization divisor and nonnegative reporting scale; no probability or tail assumptions |
| IQ standardization and same-SD composite reporting | `iq_standardization_inversion`, `iq_report_standardization`, `equal_sd_composite_scale`, `standardized_160_sd15`, `standardized_160_sd16` | Exact algebra; standard deviations/divisors assumed nonzero |
| Normalized variance and threshold rescaling | `normalized_variance_is_one`, `threshold_recovered_after_normalization` | Uses an **assumed** variance and its nonzero squared divisor; not a distribution theorem |
| Latent-factor squared correlation and conditional-variance expressions | `latent_reliability_plus_posterior_variance`, `latent_reliability_nonnegative`, `latent_posterior_variance_nonnegative`, `latent_reliability_at_most_one`, and boundary cases | Algebra for the report's *given* expressions; **does not prove the Gaussian conditional-distribution derivation** |
| Shared finite real-sum infrastructure (technical bridge) | `FiniteSum.finite_sum_ext`, `finite_sum_add`, `finite_sum_scale`, `finite_sum_nonnegative`, `finite_sum_monotone`, `finite_sum_zero`, `finite_sum_app`, `finite_sum_permutation` | Exact `Stdlib.List` folds replace repeated finite-sum proofs in both domain models; no probability normalization is assumed by the generic library |
| Four-cell admissions model interpreted as a standard Boolean-product probability space | `four_cell_total_mass`, `four_cell_first_marginal`, `four_cell_second_marginal`, `four_cell_intersection_mass`, `four_cell_union_mass`, `four_cell_exactly_one_mass`, `four_cell_indicator_covariance`, `four_cell_indicator_independence_criterion` | Explicit representation of all four outcomes and their normalized nonnegative weights; exact correspondence with the report's specialized joint, marginal and union expressions, using generic finite-probability and finite-moment library lemmas |
| Constant finite sums and unit-score covariance bounds | `FiniteSum.finite_sum_const`, `diagonal_variance_sum_of_unit_scores`, `covariance_row_sum_bounded_by_count` | Uses the shared real-valued list fold, Rocq `INR`/`S_INR`, support-aware extensionality and finite-sum monotonicity, instead of duplicating unit-variance inductions |
| Symmetric covariance double sums and cross-matrix bilinear forms | `covariance_double_sum_symmetric`, `covariance_double_sum_second_cons`, `covariance_cross_matrix_bilinear_swap` | Uses existing finite Fubini, covariance symmetry, finite sum addition and the proved fixed-basis bilinear identity; no independent matrix transpose implementation |
| Unweighted score batteries as unit-weight composites | `unweighted_scores_as_linear_combination`, `unweighted_covariance_row_as_weighted`, `covariance_with_sum_scores`, `covariance_of_sum_scores` | Uses `Stdlib.List.map` and shared sum-map composition to reuse the already formalized weighted-composite covariance theorems |
| Filtering a finite sample by a Boolean event | `FiniteSum.finite_sum_filter`, `FiniteUnion.finite_prob_as_filtered_mass`, `FiniteUnion.finite_prob_event_ext_on_samples` | Reuses Rocq's standard `List.filter` and shared support-aware sum extensionality to interpret event probability as the sum of selected outcome weights, without new measure or recursion |
| Finite double-sum interchange and termwise zero criterion | `FiniteSum.finite_sum_ext_in`, `FiniteSum.finite_sum_member_le`, `FiniteSum.finite_sum_nonnegative_zero`, `FiniteSum.finite_sum_swap`, `interchange_finite_sums` | Reuses Stdlib `List.map_ext_in` and standard finite-sum linearity to centralize support-sensitive and double-sum proofs; no new finite iterator |
| Event positive support, zero mass and generalized Fréchet bounds | `finite_prob_zero_iff_no_positive_mass_support`, `finite_prob_positive_of_positive_support`, `finite_intersection_at_most_first`, `finite_intersection_at_most_second`, `finite_frechet_lower_bound` | Holds for explicitly enumerated finite outcomes under nonnegative weights, plus normalization for the Fréchet lower bound; no independence or normality premise |
| Finite event sample permutation and monotonicity | `finite_prob_sample_append`, `finite_prob_sample_permutation`, `union_prob_sample_permutation`, `finite_prob_event_monotone`, `normalized_finite_prob_unit_interval` | For finite lists and Boolean events, weighted sample order is irrelevant, monotone events have monotone mass under nonnegative weights, and unit-interval bounds require normalized nonnegative weights |
| Finite Boolean event and moment models agree | `finite_sum_models_agree`, `finite_total_mass_models_agree`, `finite_event_probability_is_indicator_expectation` | Certified equality between the original finite-event sum/probability and finite-moment sum/indicator expectation for arbitrary real weights |
| Event-indicator Bernoulli variance, covariance and independence | `indicator_square`, `indicator_product_and`, `finite_event_indicator_variance`, `finite_event_indicator_covariance`, `finite_event_independence_iff_zero_indicator_covariance`, `finite_event_indicator_zero_variance_iff_extreme_mass` | Algebraically proves Var(1_A)=p_A(1−p_A), Cov(1_A,1_B)=p_(A∩B)−p_A p_B and zero covariance iff the finite product identity; to interpret the masses as probabilities, nonnegative normalized weights are required |
| Finite expectation: linearity, constants, centering, and nonnegative means | `expectation_add`, `expectation_scale`, `expectation_affine`, `centered_score_has_zero_expectation`, `expectation_nonnegative` | Finite sums with explicit masses; normalization and nonnegativity required where stated |
| Zero variance and finite support | `sum_finite_zero_implies_zero_terms`, `zero_variance_is_constant_on_positive_mass`, `null_covariance_direction_constant_on_positive_mass` | The variance-zero implication holds on outcomes of **positive probability weight**, using Stdlib `Rle_0_sqr` and `Rmult_integral`. A zero covariance-matrix quadratic direction makes the weighted score constant on support; no rank theorem is claimed |
| Affine finite-score variance and covariance | `variance_of_affine_score`, `covariance_of_affine_scores` | Reuses already verified shift invariance and covariance bilinearity, requiring a normalized finite probability mass rather than introducing new integration algebra |
| Finite covariance and variance laws | `covariance_symmetric`, `covariance_add_first`, `covariance_scale_second`, `variance_nonnegative`, `variance_of_two_score_sum` | Derived from definitions, not covariance axioms; variance nonnegativity requires nonnegative normalized weights |
| Weighted two-score variance and variance of the average | `variance_of_two_weighted_scores`, `variance_of_two_score_average`, `variance_of_two_unit_variance_average` | Exact, no normality; the unit-variance result requires unit component variances |
| Arbitrary finite weighted composite: variance is the quadratic form \(\sum_{i,j} w_i w_j\operatorname{Cov}(X_i,X_j)\) | `variance_of_general_weighted_sum`, `covariance_of_general_weighted_sums`, `expectation_of_general_weighted_sum` | Derived for any finite list of component functions on a *normalized finite probability space*; no Gaussian assumption |
| Concrete covariance-matrix representation and bilinear form | `covariance_row_as_vector_dot`, `covariance_double_sum_as_matrix_product`, `covariance_matrix_quadratic_form_identity`, `covariance_cross_matrix_bilinear_identity`, `covariance_matrix_quadratic_form_is_variance`, `covariance_matrix_is_positive_semidefinite` | Covariance entries are computed from finite expectations and expressed as real-valued row lists, proving the matrix-vector representation rather than postulating it |
| Cauchy–Schwarz derived from finite variance nonnegativity | `nonnegative_quadratic_discriminant`, `finite_covariance_cauchy_schwarz_squared`, `zero_variance_implies_zero_covariance_first`, `zero_variance_implies_zero_covariance_second`, `nonzero_covariance_implies_positive_variances` | Proves Cov(X,Y)² ≤ Var(X)Var(Y) by examining Var(X+tY) ≥ 0 for all real t, including the degenerate zero-variance case; normalized nonnegative finite weights are required |
| Score-battery order invariance | `sum_scores_permutation_invariant`, `variance_of_permuted_score_sum`, `equal_weight_variance_permutation_invariant` | Uses `Stdlib.Sorting.Permutation` induction and real addition commutativity; a reordering of the tests cannot change the sum or its variance |
| Covariance-matrix shape from the standard library | `basis_covariance_matrix_row_count`, `basis_covariance_matrix_column_count`, `basis_cross_covariance_matrix_row_count`, `basis_cross_covariance_matrix_column_count` | Uses `length_map` and `in_map_iff` to prove square and rectangular list-matrix dimensions |
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
| Positive-marginal independence characterization | `independence_iff_conditional_B_equals_marginal`, `independence_iff_conditional_A_equals_marginal` | Both directions follow from earlier conditional numerator identities; a positive conditioning marginal is required and no empirical independence is asserted |
| Complete conditional probability interval bounds | `conditional_B_given_A_nonnegative`, `conditional_A_given_B_nonnegative`, `conditional_B_given_A_unit_interval`, `conditional_A_given_B_unit_interval`, `overlap_at_most_either`, `conditional_both_given_either_unit_interval`, `conditional_not_A_given_B_unit_interval` | All bounds require positive probability for the conditioning event; follow from four-cell nonnegativity and existing identities, not an independence assumption |
| Independence and conditional probabilities; zero-overlap cases | `independent_either_as_complement_product`, `independent_equal_marginals_as_complement_square`, `independent_conditional_B_equals_marginal`, `independent_conditional_A_equals_marginal`, `independent_exactly_one_formula`, `disjointness_iff_union_is_sum`, `complete_coverage_iff_no_failures`, and marginal/overlap bounds | Independence and nonzero conditioning-event masses are explicit hypotheses; no real-world independence is claimed |
| Exactly one pass versus either pass | `exactly_one_formula`, `exactly_one_vs_union`, `equal_marginal_union`, `equal_marginal_exactly_one` | Exact |
| Conditional denominators and failure complements | `conditional_B_numerator`, `conditional_A_numerator`, `both_conditional_denominators_agree`, `conditional_either_numerator`, `conditional_failure_complement`, and conditional bounds | Require strictly positive conditioning-event masses |
| Distinguish binary phi numerator and continuous Pearson correlation | `binary_indicator_covariance_numerator`, `binary_independence_criterion` | Proves the binary covariance numerator and independence criterion; **not** the numerical continuous/discrete correlation discrepancy |
| Published mixed-case 2.11% figure is impossible from marginals of 2% and 0.1% | `original_mixed_union_impossible` | Exact rational contradiction from the union bound |
| Marginal rates do not determine overlap or OR admission fraction | `same_marginals_different_joint`, `same_marginals_different_union` | Constructive four-cell counterexamples |
| Finite event complementation and inclusion–exclusion | `indicator_complement`, `finite_prob_complement`, `normalized_finite_prob_complement`, `indicator_union_intersection`, `finite_prob_inclusion_exclusion`, `two_event_union_probability`, `two_event_union_inclusion_exclusion` | Exact Bool `negb`, `orb`, `andb` interpretation using list folds; the real-weight identities do **not** require normalization or nonnegativity, only the normalized complement uses mass one |
| Appending event families | `any_event_append`, `union_prob_append`, `sum_marginal_probs_append` | Derived using `Stdlib.List.existsb_app`, `map_app`, `fold_right_app`; no custom event-family concatenation recursion |
| Finite union invariant under route order or repetition | `union_prob_membership_extensional`, `union_prob_permutation_invariant`, `union_prob_duplicate_route` | Proofs reuse `existsb_exists` and `Sorting.Permutation`; probability depends on event membership, not route-list order or duplicate entries |
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

The next valuable targets are: (1) a checked connection from the
four-cell `TwoEventModel` to the now-verified Boolean-event/moment
bridge, (2) certified covariance-matrix rank statements beyond the
zero-quadratic-form support result, (3) using a maintained measure-theory
library with checked finite-to-continuous interpretation lemmas,
(4) bivariate Gaussian density normalization and certified tail
enclosures, and (5) Gaussian common-factor conditional-moment theorems. Numerical tables must remain labeled numerical until certified
interval arithmetic is available.

This work is AI-generated and requires independent review of the
**mapping between the English report and the exact formal statements**,
even when the Rocq kernel accepts all proofs.
