# Complete proof-script refactoring register

This register inventories **every `Proof. ... Qed.` or `Proof. ... Defined.`
script**, including local helpers and two explicit record constructors.
It is a proof-by-proof review of source structure, dependency reuse, and
whether an additional rewrite is justified; it is **not** a replacement for
Rocq 9.2 kernel checking or a claim that all scripts needed modification.

The current branch has 389 public theorem/lemma/example declarations,
one local helper, and two constructed `Admissions.TwoEventModel` values:
**392 proof scripts**, including the generic
`FiniteSum.finite_sum_zip_map` and four newly formalized properties
of event filtering and Boolean sample partitions.
The record was created after the current generic list-fold and covariance
matrix refactoring and counts explicit proof blocks, not definitions lacking
proof obligations.

### Refactor criteria

1. Preserve each existing theorem's exact proposition and every assumption.
2. Prefer `Stdlib.List`, `Stdlib.Sorting.Permutation`, `Stdlib.Bool`,
   `Stdlib.Reals`, `Lra`, `Psatz`, and the shared `FiniteSum` laws.
3. Remove repeated finite-list inductions only when an already-checked
   general theorem expresses the **same** finite list semantics.
4. Retain structural induction for genuinely recursive `fold_right`
   algebra, `Nat.iter`, and the suffix-dependent unordered-pair sum.
5. Do not introduce a new project-specific axiom, `Admitted`, or unpinned
   matrix/measure library. Review all changes with the pinned Rocq 9.2
   kernel check and existing Python/Deal/SPARK workflows.
6. Where the existing proof already delegates to a Stdlib theorem
   or a checked lemma in one or two lines, **retain it**; rewriting
   solely to change its text is not a semantic refactor.

### New generic covariance proof
`covariance_of_general_weighted_second_unconditional` derives component
covariance linearity from the already verified finite expectation/finite
sum laws, with no list induction or normalization premise. The original
`covariance_of_general_weighted_second` theorem remains unchanged and
now delegates to the stronger result. This removes one of the previously
retained component-list inductions without adding a custom recursion.

### Additional Stdlib-backed filtering refactor
The generic `FiniteSum.finite_sum_filter_partition` identity
reuses `Stdlib.List.filter` and the existing signed finite-sum
algebra. The event-specific partition theorem now delegates to it.
The existing finite_prob_complement theorem now also delegates to this
same shared partition theorem instead of redoing indicator algebra.
Two nonnegative-mass monotonicity theorems reuse Boolean conjunction
and the pre-existing `finite_prob_event_monotone` lemma; neither
needs a new list induction or a normalized probability model.

### Further Stdlib.List refactoring: filtered sample concatenation

The three new additivity theorems `union_prob_sample_append`,
`finite_prob_filtered_append` and `union_prob_filtered_append`
are direct applications of the preexisting
`finite_prob_sample_append` and `Stdlib.List.filter_app`.
All sample-list multiplicities and arbitrary real weights are
preserved; no additional recursive proof or list implementation
is needed. No structural induction was introduced.

### Further bridge reuse: selected samples as score moments

Two new `FiniteBridge` theorems express filtered-event mass and
filtered-event-family union mass as an indicator-score expectation
over the original sample. They directly compose already checked
`FiniteUnion.finite_prob_on_filtered_samples` or
`union_prob_on_filtered_samples` with the existing
`finite_event_probability_is_indicator_expectation` bridge.
They introduce no probability-measure object, new expectation
implementation, or induction.

### Stronger covariance and variance algebra without sample normalization

The new `covariance_of_general_weighted_sums_unconditional` and
`variance_of_general_weighted_sum_unconditional` reuse the
already-checked unconditional covariance-in-one-argument lemma,
covariance symmetry and `FiniteSum.finite_sum_ext`.
The existing mass-normalized versions retain **unchanged statements**
and now apply the stronger results directly. No additional induction
or external distribution/matrix library is introduced; a signed
real-weighted list expression is **not** automatically a probability.

### Unconditional matrix and variance identities

Three new covariance-matrix results reuse the unconditional composite
variance/covariance identities: cross-matrix bilinear representation,
cross-matrix swap symmetry, and self-covariance quadratic-form equality.
All three older mass-normalized theorems now delegate to these results
while retaining their original theorem propositions. The resulting
representations are real-weighted finite algebra; positive
semidefiniteness still requires nonnegative normalized sample weights.
No additional structural induction, custom matrix library, or axiom
is introduced.

### Generalized unweighted score-list covariance and variance

Three new lemmas reuse `Stdlib.List.map` to represent unweighted
score sums as unit-coefficient weighted composites. Together with
`covariance_of_general_weighted_second_unconditional`,
`covariance_symmetric` and `FiniteSum.finite_sum_ext`, they prove
covariance of one score against a finite list sum, covariance
between two list sums, and the unweighted score-list variance
identity **without requiring sample mass normalization**.
Their original three mass-one theorem signatures are preserved,
but the proof bodies now directly reuse the stronger laws.
This work adds no structural induction, new finite-sum recursion,
or external matrix library.

### Generic finite conditional-event quotient

A new `FiniteUnion.finite_conditional_prob` definition composes the
existing Boolean intersection and finite event probability laws, rather
than implementing another sum. Two checked generic theorems relate it
to standard List.filter and prove self-conditioning for positive mass.
Two four-cell corollaries reuse the existing B|A and A|B bridge proofs.
All original statements are retained; the new definition has no proof
block and the four new theorems are entered in source order.

### Further FourCellBridge conditional interpretations

Five additional standard-library-backed proofs connect B-only event mass
and the four report-specific conditional ratios to generic Boolean-event
probabilities. The B-only mass uses one fixed Boolean-product calculation;
all conditional ratios reuse already checked marginal/intersection/union
lemmas and make strictly positive denominators explicit.

### Generic conditional-event bounds and standard-library reuse

Three conditional lemmas reuse the existing finite event monotonicity,
Fréchet intersection bounds, finite Boolean sample filtering and
complement identities. No new iterator, measure object, list induction
or probability normalization assumption is introduced. The quotient
bound requires nonnegative weights and positive conditioning mass,
while event extensionality and the complement identity preserve their
exact weaker premises.

### Four-cell generic conditional interpretation completed

Two more conditional correspondences show the report's
`conditional_both_given_either` and `conditional_not_A_given_B`
are special cases of the shared finite conditional operator. The
proofs reuse standard Boolean identities and already checked finite
union, support extensionality, and report-specific ratio theorems;
no second event implementation or matrix recursion is introduced.
All four original conditional report expressions are now covered by
the same general finite conditional model, with positive denominators.

### Stronger conditional support reasoning and reviewed refactor

Four additional generic conditional results establish target-event
extensionality *only on enumerated conditioning support*, event
monotonicity under a fixed positive conditioning marginal, conditional
mass one for the true event, and support extensionality of the
conditioning predicate itself. The existing
`finite_conditional_prob_event_ext_on_samples` proof delegates to
the stronger conditional-support lemma, eliminating a repeated
Boolean-conjunction equality proof. All new results reuse
Stdlib.Bool, finite_prob_event_ext_on_samples,
finite_prob_event_monotone and real inverse order lemmas; none adds
custom list recursion or external probability infrastructure.

### Conditional event algebra and Bayes identities

Four further results reuse existing standard-library Boolean operations,
finite event-mass filtering, inclusion–exclusion and partition identities
instead of implementing a new event algebra: impossible conditional
events, conditional inclusion–exclusion, Bayes balance under two positive
marginals, and the law of total probability under a two-cell positive
partition. All proofs preserve the exact weighted-list and division
semantics, including arbitrary sample multiplicities.

### Conditional chain rule and stronger covariance-matrix null directions

The finite conditional chain rule now reduces directly to Boolean
conjunction associativity and standard field cancellation, without
additional finite sums. The fixed-basis Cauchy–Schwarz extension and
null-direction covariance-orthogonality and positive-support equality
theorems reuse existing matrix/variance bridge lemmas instead of
implementing new indexed matrix operations. Full eigenvalue and
rank-nullity theorems remain outside the current finite-list API.

### Concrete rank-deficiency witness for a duplicate score basis

The standard covariance-with-constant theorem is exposed as a reusable
variance-zero lemma under unit total mass. Applying the existing
fixed-basis variance identity to duplicate score functions `[f; f]`
and the genuinely nonzero coefficient list `[1; -1]` constructs a
kernel-checked zero-quadratic-form witness. The list basis and
combination are the existing Stdlib and FiniteSum constructs; there
is no bespoke determinant, eigenvalue or rank implementation.

### Three new support-aware finite-moment extensionality lemmas

The generic `FiniteSum.finite_sum_ext_in` already relies on
Stdlib.List.map_ext_in, and now establishes on-sample equality of
expectations directly. Covariance and variance support-extensionality
follow using the existing finite-moment definitions, with no second
list recursion. Previously proven global-extensionality statements
are retained for source compatibility.

### Refactored global moment extensionality

The original globally quantified expectation, covariance and variance
extensionality proofs are now direct instances of the stronger
on-sample versions. Their exact original propositions are retained,
while duplicate finite expectation rewrites were removed.

### Full finite covariance null-direction support characterization

The earlier one-way zero-variance and positive-support theorems
now have a converse without imposing strict positivity on every
sample occurrence. Nonnegative weights permit zero-weight scores
to be ignored via the shared FiniteSum.finite_sum_ext_in lemma,
using standard real-order case analysis. An exact equivalence
then identifies zero fixed-basis covariance quadratic form with
weighted scores constant on the positive-weight sample support.
This does not add an unverified matrix rank or determinant routine.

### Generic variance equivalences reused by fixed-basis null proofs

Two general equivalences now characterize zero variance by constancy
on positive-weight sampled support and by vanishing covariance with
all comparison scores. The existing fixed-basis null/constant theorem
is refactored to apply the generic variance equivalence directly.
A further fixed-basis iff theorem characterizes every null direction
by orthogonality to all finite comparison scores. This uses only
previously checked moment and matrix-variance bridge lemmas.

### Current structural-induction inventory

Exactly **14 proof scripts** currently contain an
`induction` tactic. These are implementation-shape arguments or proofs
over `Nat.iter`; their retention is a conscious review outcome, not a
missing documentation comment. Remaining candidates for further
generalization must be judged against preservation of the exact
enumeration and matrix-list semantics.

- `FiniteSum.finite_sum_add`
- `FiniteSum.finite_sum_scale`
- `FiniteSum.finite_sum_nonnegative`
- `FiniteSum.finite_sum_member_le`
- `FiniteSum.finite_sum_const`
- `FiniteSum.finite_sum_zip_map`
- `FiniteSum.finite_sum_swap`
- `FiniteSum.finite_sum_filter`
- `FiniteSum.finite_sum_app`
- `FiniteSum.finite_sum_permutation`
- `Admissions.independent_union_formula`
- `FiniteMoments.double_sum_diagonal_off_diagonal`
- `FiniteMoments.unordered_covariance_sum_bounded_by_pair_count`
- `FiniteMoments.split_as_projection_maps`

### Per-module proof review

This table records the currently used proof method and known library
dependencies. Status **Reviewed** means the script has been inspected
for straightforward library substitutions and intentionally left
unchanged, *not* that every proof term was rewritten. The dependency
column is a tactic-level heuristic; consult the actual source for
full dependencies and the theorem-specific doc comment for hypotheses.

## FiniteSum.v — 20 proof scripts

| Named declaration | Proof strategy | Library reuse | Refactor disposition |
|---|---|---|---|
| `finite_sum_ext_in` (lemma) | Lemma application | Stdlib.List | Reviewed: keep established tactic/library proof |
| `finite_sum_ext` (lemma) | Lemma application | Prior named lemmas | Earlier library refactor retained |
| `finite_sum_add` (lemma) | Structural induction, Rewriting, Ring/field, Computation | Stdlib ring/field | Reviewed: structural induction retained |
| `finite_sum_scale` (lemma) | Structural induction, Rewriting, Ring/field, Computation | Stdlib ring/field | Reviewed: structural induction retained |
| `finite_sum_nonnegative` (lemma) | Structural induction, Lemma application, Lra/Psatz, Computation | Stdlib.Lra/Psatz | Reviewed: structural induction retained |
| `finite_sum_neg` (lemma) | Lemma application, Rewriting, Ring/field | Stdlib ring/field | Reviewed: keep established tactic/library proof |
| `finite_sum_sub` (lemma) | Lemma application, Rewriting, Ring/field | Stdlib ring/field | Reviewed: keep established tactic/library proof |
| `finite_sum_member_le` (lemma) | Structural induction, Finite cases, Lemma application, Lra/Psatz, Computation | Stdlib.Lra/Psatz | Reviewed: structural induction retained |
| `finite_sum_nonnegative_zero` (lemma) | Lemma application, Lra/Psatz | Stdlib.Lra/Psatz | Reviewed: keep established tactic/library proof |
| `finite_sum_monotone` (lemma) | Lemma application, Rewriting, Lra/Psatz | Stdlib.Lra/Psatz | **Rewritten**: duplicated list induction removed |
| `finite_sum_const` (lemma) | Structural induction, Rewriting, Ring/field, Computation | Stdlib ring/field | Reviewed: structural induction retained |
| `finite_sum_zero` (lemma) | Rewriting, Ring/field | Stdlib ring/field | **Rewritten**: duplicated list induction removed |
| `finite_sum_map` (lemma) | Rewriting, Computation | Stdlib.List | Reviewed: keep established tactic/library proof |
| `finite_sum_zip_map` (lemma) | Structural induction, Rewriting, Computation | Stdlib.List | Reviewed: structural induction retained |
| `finite_sum_swap` (lemma) | Structural induction, Lemma application, Rewriting, Computation | Prior named lemmas | Reviewed: structural induction retained |
| `finite_sum_filter` (lemma) | Structural induction, Finite cases, Rewriting, Ring/field, Computation | Stdlib ring/field | Reviewed: structural induction retained |
| `finite_sum_filter_partition` (lemma) | Rewriting, Lemma application, Finite cases, Ring/field | Stdlib.List.filter, Stdlib.Bool.negb, finite_sum_filter/add/ext | **New generic lemma:** additive partition of arbitrary real-weighted finite lists without induction |
| `finite_sum_app` (lemma) | Structural induction, Rewriting, Ring/field, Computation | Stdlib ring/field | Reviewed: structural induction retained |
| `finite_sum_permutation` (lemma) | Structural induction, Rewriting, Ring/field, Computation | Stdlib ring/field | Reviewed: structural induction retained |
| `finite_sum_rev` (lemma) | Lemma application | Stdlib.Permutation | Reviewed: keep established tactic/library proof |

## Hoeflin.v — 65 proof scripts

| Named declaration | Proof strategy | Library reuse | Refactor disposition |
|---|---|---|---|
| `nonnegative_quotient` (lemma) | Lemma application | Prior named lemmas | Reviewed: keep established tactic/library proof |
| `pair_average_variance` (theorem) | Rewriting, Ring/field, Lra/Psatz | Stdlib.Lra/Psatz, Stdlib ring/field | Reviewed: keep established tactic/library proof |
| `equicorrelation_variance` (theorem) | Ring/field, Lra/Psatz | Stdlib.Lra/Psatz, Stdlib ring/field | Reviewed: keep established tactic/library proof |
| `variance_alternative_form` (theorem) | Ring/field, Lra/Psatz | Stdlib.Lra/Psatz, Stdlib ring/field | Reviewed: keep established tactic/library proof |
| `one_test_variance` (theorem) | Ring/field | Stdlib ring/field | Reviewed: keep established tactic/library proof |
| `independent_tests_variance` (theorem) | Ring/field, Lra/Psatz | Stdlib.Lra/Psatz, Stdlib ring/field | Reviewed: keep established tactic/library proof |
| `perfectly_correlated_variance` (theorem) | Ring/field, Lra/Psatz | Stdlib.Lra/Psatz, Stdlib ring/field | Reviewed: keep established tactic/library proof |
| `variance_strictly_positive` (theorem) | Lemma application, Rewriting, Lra/Psatz | Stdlib.Lra/Psatz | Reviewed: keep established tactic/library proof |
| `variance_at_least_correlation` (theorem) | Lemma application, Lra/Psatz | Stdlib.Lra/Psatz | Reviewed: keep established tactic/library proof |
| `variance_at_most_one` (theorem) | Lemma application, Ring/field, Lra/Psatz | Stdlib.Lra/Psatz, Stdlib ring/field | Reviewed: keep established tactic/library proof |
| `variance_nondecreasing_in_correlation` (theorem) | Lemma application, Ring/field, Lra/Psatz | Stdlib.Lra/Psatz, Stdlib ring/field | Reviewed: keep established tactic/library proof |
| `variance_gap_to_limiting_correlation` (theorem) | Ring/field | Stdlib ring/field | Reviewed: keep established tactic/library proof |
| `iq_standardization_inversion` (theorem) | Ring/field, Lra/Psatz | Stdlib.Lra/Psatz, Stdlib ring/field | Reviewed: keep established tactic/library proof |
| `iq_report_standardization` (theorem) | Ring/field, Lra/Psatz | Stdlib.Lra/Psatz, Stdlib ring/field | Reviewed: keep established tactic/library proof |
| `equal_sd_composite_scale` (theorem) | Ring/field, Lra/Psatz | Stdlib.Lra/Psatz, Stdlib ring/field | Reviewed: keep established tactic/library proof |
| `threshold_recovered_after_normalization` (theorem) | Ring/field, Lra/Psatz | Stdlib.Lra/Psatz, Stdlib ring/field | Reviewed: keep established tactic/library proof |
| `normalized_variance_is_one` (theorem) | Ring/field, Lra/Psatz | Stdlib.Lra/Psatz, Stdlib ring/field | Reviewed: keep established tactic/library proof |
| `standardized_160_sd15` (theorem) | Ring/field | Stdlib ring/field | Reviewed: keep established tactic/library proof |
| `standardized_160_sd16` (theorem) | Ring/field | Stdlib ring/field | Reviewed: keep established tactic/library proof |
| `latent_reliability_plus_posterior_variance` (theorem) | Ring/field, Lra/Psatz | Stdlib.Lra/Psatz, Stdlib ring/field | Reviewed: keep established tactic/library proof |
| `latent_reliability_nonnegative` (theorem) | Lemma application, Lra/Psatz | Stdlib.Lra/Psatz | Reviewed: keep established tactic/library proof |
| `latent_posterior_variance_nonnegative` (theorem) | Lemma application, Lra/Psatz | Stdlib.Lra/Psatz | Reviewed: keep established tactic/library proof |
| `latent_reliability_at_most_one` (theorem) | Lemma application, Lra/Psatz | Stdlib.Lra/Psatz | Reviewed: keep established tactic/library proof |
| `latent_reliability_for_one_test` (theorem) | Ring/field | Stdlib ring/field | Reviewed: keep established tactic/library proof |
| `latent_reliability_at_zero` (theorem) | Ring/field | Stdlib ring/field | Reviewed: keep established tactic/library proof |
| `latent_variance_at_zero` (theorem) | Ring/field | Stdlib ring/field | Reviewed: keep established tactic/library proof |
| `latent_variance_at_perfect_correlation` (theorem) | Ring/field, Lra/Psatz | Stdlib.Lra/Psatz, Stdlib ring/field | Reviewed: keep established tactic/library proof |
| `variance_decreases_with_test_count` (theorem) | Lemma application, Ring/field, Lra/Psatz | Stdlib.Lra/Psatz, Stdlib ring/field | Reviewed: keep established tactic/library proof |
| `variance_strictly_decreases_with_test_count` (theorem) | Lemma application, Ring/field, Lra/Psatz | Stdlib.Lra/Psatz, Stdlib ring/field | Reviewed: keep established tactic/library proof |
| `variance_is_affine_in_correlation` (theorem) | Ring/field, Lra/Psatz | Stdlib.Lra/Psatz, Stdlib ring/field | Reviewed: keep established tactic/library proof |
| `variance_correlation_sensitivity` (theorem) | Ring/field, Lra/Psatz | Stdlib.Lra/Psatz, Stdlib ring/field | Reviewed: keep established tactic/library proof |
| `variance_of_two_equicorrelated_tests` (theorem) | Ring/field | Stdlib ring/field | Reviewed: keep established tactic/library proof |
| `variance_of_three_equicorrelated_tests` (theorem) | Ring/field | Stdlib ring/field | Reviewed: keep established tactic/library proof |
| `latent_variance_denominator_positive` (theorem) | Lra/Psatz | Stdlib.Lra/Psatz | Reviewed: keep established tactic/library proof |
| `latent_variance_decreases_with_test_count` (theorem) | Lemma application, Ring/field, Lra/Psatz | Stdlib.Lra/Psatz, Stdlib ring/field | Reviewed: keep established tactic/library proof |
| `latent_reliability_increases_with_test_count` (theorem) | Lemma application, Lra/Psatz | Stdlib.Lra/Psatz | Reviewed: keep established tactic/library proof |
| `doubling_battery_halves_variance_excess` (theorem) | Ring/field, Lra/Psatz | Stdlib.Lra/Psatz, Stdlib ring/field | Reviewed: keep established tactic/library proof |
| `nonnegative_correlation_variance_at_least_independent` (theorem) | Lemma application, Ring/field, Lra/Psatz | Stdlib.Lra/Psatz, Stdlib ring/field | Reviewed: keep established tactic/library proof |
| `variance_excess_bound_by_inverse_battery_size` (theorem) | Lemma application, Rewriting, Ring/field, Lra/Psatz | Stdlib.Lra/Psatz, Stdlib ring/field | Reviewed: keep established tactic/library proof |
| `latent_reliability_times_composite_variance` (theorem) | Lemma application, Ring/field, Lra/Psatz | Stdlib.Lra/Psatz, Stdlib ring/field | Reviewed: keep established tactic/library proof |
| `latent_posterior_times_composite_variance` (theorem) | Lemma application, Ring/field, Lra/Psatz | Stdlib.Lra/Psatz, Stdlib ring/field | Reviewed: keep established tactic/library proof |
| `composite_standard_deviation_nonnegative` (theorem) | Lemma application | Stdlib.sqrt | Reviewed: keep established tactic/library proof |
| `composite_standard_deviation_squared` (theorem) | Lemma application, Lra/Psatz | Stdlib.Lra/Psatz, Stdlib.sqrt | Reviewed: keep established tactic/library proof |
| `composite_standard_deviation_at_zero_correlation` (theorem) | Rewriting, Lra/Psatz, Computation | Stdlib.Lra/Psatz | Reviewed: keep established tactic/library proof |
| `composite_standard_deviation_at_perfect_correlation` (theorem) | Lemma application, Rewriting, Lra/Psatz | Stdlib.Lra/Psatz, Stdlib.sqrt | Reviewed: keep established tactic/library proof |
| `composite_standard_deviation_nondecreasing_in_correlation` (theorem) | Lemma application, Lra/Psatz | Stdlib.Lra/Psatz, Stdlib.sqrt | Reviewed: keep established tactic/library proof |
| `composite_standard_deviation_nonincreasing_in_test_count` (theorem) | Lemma application, Lra/Psatz | Stdlib.Lra/Psatz, Stdlib.sqrt | Reviewed: keep established tactic/library proof |
| `composite_standard_deviation_at_most_one` (theorem) | Lemma application, Rewriting, Lra/Psatz | Stdlib.Lra/Psatz, Stdlib.sqrt | Reviewed: keep established tactic/library proof |
| `composite_standard_deviation_at_least_sqrt_correlation` (theorem) | Lemma application, Lra/Psatz | Stdlib.Lra/Psatz, Stdlib.sqrt | Reviewed: keep established tactic/library proof |
| `composite_standard_deviation_positive` (theorem) | Lemma application | Stdlib.sqrt | Reviewed: keep established tactic/library proof |
| `composite_standard_deviation_strictly_decreases_with_test_count` (theorem) | Lemma application, Lra/Psatz | Stdlib.Lra/Psatz, Stdlib.sqrt | Reviewed: keep established tactic/library proof |
| `composite_standard_deviation_strictly_increases_in_correlation` (theorem) | Lemma application, Rewriting, Lra/Psatz | Stdlib.Lra/Psatz, Stdlib.sqrt | Reviewed: keep established tactic/library proof |
| `composite_standard_deviation_at_least_independent_baseline` (theorem) | Lemma application, Lra/Psatz | Stdlib.Lra/Psatz, Stdlib.sqrt | Reviewed: keep established tactic/library proof |
| `composite_standard_deviation_strictly_below_one` (theorem) | Lemma application, Rewriting, Ring/field, Lra/Psatz | Stdlib.Lra/Psatz, Stdlib ring/field, Stdlib.sqrt | Reviewed: keep established tactic/library proof |
| `standardized_affine_cutoff_round_trip` (theorem) | Ring/field, Lra/Psatz | Stdlib.Lra/Psatz, Stdlib ring/field | Reviewed: keep established tactic/library proof |
| `positive_scale_preserves_cutoff_order` (theorem) | Lemma application, Lra/Psatz | Stdlib.Lra/Psatz | Reviewed: keep established tactic/library proof |
| `composite_standardized_cutoff_round_trip` (theorem) | Lemma application, Lra/Psatz | Stdlib.Lra/Psatz | Reviewed: keep established tactic/library proof |
| `positive_cutoff_nonincreasing_with_test_count` (theorem) | Lemma application | Prior named lemmas | Reviewed: keep established tactic/library proof |
| `standardize_preserves_order` (theorem) | Lemma application, Lra/Psatz | Stdlib.Lra/Psatz | Reviewed: keep established tactic/library proof |
| `iq_report_preserves_order` (theorem) | Lemma application | Prior named lemmas | Reviewed: keep established tactic/library proof |
| `standardized_iq_reporting_preserves_order` (theorem) | Lemma application | Prior named lemmas | Reviewed: keep established tactic/library proof |
| `fixed_correlation_variance_epsilon_bound` (theorem) | Lemma application, Rewriting, Ring/field, Lra/Psatz | Stdlib.Lra/Psatz, Stdlib ring/field | Reviewed: keep established tactic/library proof |
| `fixed_correlation_variance_epsilon_after_threshold` (theorem) | Lemma application, Rewriting, Ring/field, Lra/Psatz | Stdlib.Lra/Psatz, Stdlib ring/field | Reviewed: keep established tactic/library proof |
| `positive_cutoff_nondecreasing_in_correlation` (theorem) | Lemma application | Prior named lemmas | Reviewed: keep established tactic/library proof |
| `positive_cutoff_strictly_increases_in_correlation` (theorem) | Lemma application | Prior named lemmas | Reviewed: keep established tactic/library proof |

## Admissions.v — 69 proof scripts

| Named declaration | Proof strategy | Library reuse | Refactor disposition |
|---|---|---|---|
| `first_marginal_nonnegative` (theorem) | Lemma application | Prior named lemmas | Reviewed: keep established tactic/library proof |
| `second_marginal_nonnegative` (theorem) | Lemma application | Prior named lemmas | Reviewed: keep established tactic/library proof |
| `union_nonnegative` (theorem) | Lemma application | Prior named lemmas | Reviewed: keep established tactic/library proof |
| `union_at_most_one` (theorem) | Lemma application, Lra/Psatz | Stdlib.Lra/Psatz | Reviewed: keep established tactic/library proof |
| `both_at_most_first` (theorem) | Lemma application, Lra/Psatz | Stdlib.Lra/Psatz | Reviewed: keep established tactic/library proof |
| `both_at_most_second` (theorem) | Lemma application, Lra/Psatz | Stdlib.Lra/Psatz | Reviewed: keep established tactic/library proof |
| `union_at_least_first` (theorem) | Lemma application, Lra/Psatz | Stdlib.Lra/Psatz | Reviewed: keep established tactic/library proof |
| `union_at_least_second` (theorem) | Lemma application, Lra/Psatz | Stdlib.Lra/Psatz | Reviewed: keep established tactic/library proof |
| `inclusion_exclusion` (theorem) | Ring/field | Stdlib ring/field | Reviewed: keep established tactic/library proof |
| `union_bound` (theorem) | Lemma application, Rewriting, Lra/Psatz | Stdlib.Lra/Psatz | Reviewed: keep established tactic/library proof |
| `frechet_lower_bound` (theorem) | Lemma application, Lra/Psatz | Stdlib.Lra/Psatz | Reviewed: keep established tactic/library proof |
| `overlap_nonnegative` (theorem) | Lemma application | Prior named lemmas | Reviewed: keep established tactic/library proof |
| `union_complement` (theorem) | Lemma application | Definitional reduction | Reviewed: keep established tactic/library proof |
| `exactly_one_formula` (theorem) | Ring/field | Stdlib ring/field | Reviewed: keep established tactic/library proof |
| `exactly_one_vs_union` (theorem) | Ring/field | Stdlib ring/field | Reviewed: keep established tactic/library proof |
| `equal_marginal_union` (theorem) | Rewriting, Ring/field | Stdlib ring/field | Reviewed: keep established tactic/library proof |
| `equal_marginal_exactly_one` (theorem) | Rewriting, Ring/field | Stdlib ring/field | Reviewed: keep established tactic/library proof |
| `conditional_B_numerator` (theorem) | Ring/field, Lra/Psatz | Stdlib.Lra/Psatz, Stdlib ring/field | Reviewed: keep established tactic/library proof |
| `conditional_A_numerator` (theorem) | Ring/field, Lra/Psatz | Stdlib.Lra/Psatz, Stdlib ring/field | Reviewed: keep established tactic/library proof |
| `conditional_either_numerator` (theorem) | Ring/field, Lra/Psatz | Stdlib.Lra/Psatz, Stdlib ring/field | Reviewed: keep established tactic/library proof |
| `both_conditional_denominators_agree` (theorem) | Rewriting, Computation | Prior named lemmas | Reviewed: keep established tactic/library proof |
| `conditional_failure_complement` (theorem) | Ring/field, Lra/Psatz | Stdlib.Lra/Psatz, Stdlib ring/field | Reviewed: keep established tactic/library proof |
| `conditional_second_le_one` (theorem) | Lemma application, Rewriting, Ring/field, Lra/Psatz | Stdlib.Lra/Psatz, Stdlib ring/field | Reviewed: keep established tactic/library proof |
| `conditional_first_le_one` (theorem) | Lemma application, Rewriting, Ring/field, Lra/Psatz | Stdlib.Lra/Psatz, Stdlib ring/field | Reviewed: keep established tactic/library proof |
| `conditional_failure_nonnegative` (theorem) | Lemma application | Prior named lemmas | Reviewed: keep established tactic/library proof |
| `binary_indicator_covariance_numerator` (theorem) | Lemma application, Rewriting, Ring/field, Lra/Psatz | Stdlib.Lra/Psatz, Stdlib ring/field | Reviewed: keep established tactic/library proof |
| `binary_independence_criterion` (theorem) | Lemma application, Lra/Psatz | Stdlib.Lra/Psatz | Reviewed: keep established tactic/library proof |
| `original_mixed_union_impossible` (theorem) | Lemma application, Rewriting, Lra/Psatz | Stdlib.Lra/Psatz | Reviewed: keep established tactic/library proof |
| `equal_marginal_overlap_from_union` (theorem) | Lemma application, Rewriting, Lra/Psatz | Stdlib.Lra/Psatz | Reviewed: keep established tactic/library proof |
| `independent_union_formula` (theorem) | Structural induction, Rewriting, Ring/field, Computation | Stdlib ring/field | Reviewed: structural induction retained |
| `independent_union_one` (theorem) | Ring/field, Computation | Stdlib ring/field | Reviewed: keep established tactic/library proof |
| `independent_union_two` (theorem) | Ring/field, Computation | Stdlib ring/field | Reviewed: keep established tactic/library proof |
| `identical_half_events` (definition) | Lra/Psatz | Stdlib.Lra/Psatz | Reviewed: keep established tactic/library proof |
| `independent_half_events` (definition) | Lra/Psatz | Stdlib.Lra/Psatz | Reviewed: keep established tactic/library proof |
| `same_marginals_different_joint` (theorem) | Lra/Psatz, Computation | Stdlib.Lra/Psatz | Reviewed: keep established tactic/library proof |
| `same_marginals_different_union` (theorem) | Lra/Psatz, Computation | Stdlib.Lra/Psatz | Reviewed: keep established tactic/library proof |
| `grid_node_count` (example) | Computation | Definitional reduction | Reviewed: minimal definitional proof |
| `grid_scale_factors_cancel` (theorem) | Ring/field, Lra/Psatz | Stdlib.Lra/Psatz, Stdlib ring/field | Reviewed: keep established tactic/library proof |
| `half_point_grid_midpoint_shift` (theorem) | Ring/field | Stdlib ring/field | Reviewed: keep established tactic/library proof |
| `exactly_one_nonnegative` (theorem) | Lemma application, Lra/Psatz | Stdlib.Lra/Psatz | Reviewed: keep established tactic/library proof |
| `exactly_one_at_most_either` (theorem) | Lemma application, Lra/Psatz | Stdlib.Lra/Psatz | Reviewed: keep established tactic/library proof |
| `intersection_at_most_minimum_marginal` (theorem) | Lemma application, Lra/Psatz | Stdlib.Lra/Psatz | Reviewed: keep established tactic/library proof |
| `union_equal_marginal_lower_bound` (theorem) | Lemma application, Lra/Psatz | Stdlib.Lra/Psatz | Reviewed: keep established tactic/library proof |
| `union_equal_marginal_upper_bound` (theorem) | Lemma application, Lra/Psatz | Stdlib.Lra/Psatz | Reviewed: keep established tactic/library proof |
| `disjoint_events_union_is_sum` (theorem) | Rewriting, Ring/field | Stdlib ring/field | Reviewed: keep established tactic/library proof |
| `independent_events_union_formula` (theorem) | Rewriting, Computation | Prior named lemmas | Reviewed: keep established tactic/library proof |
| `independent_equal_marginal_union` (theorem) | Rewriting, Ring/field | Stdlib ring/field | Reviewed: keep established tactic/library proof |
| `all_first_passers_also_second_union` (theorem) | Lemma application, Rewriting, Lra/Psatz | Stdlib.Lra/Psatz | Reviewed: keep established tactic/library proof |
| `excess_marginal_mass_forces_overlap` (theorem) | Lemma application, Lra/Psatz | Stdlib.Lra/Psatz | Reviewed: keep established tactic/library proof |
| `lower_bound_on_overlap_from_union` (theorem) | Lemma application, Lra/Psatz | Stdlib.Lra/Psatz | Reviewed: keep established tactic/library proof |
| `independent_either_as_complement_product` (theorem) | Rewriting, Ring/field | Stdlib ring/field | Reviewed: keep established tactic/library proof |
| `independent_equal_marginals_as_complement_square` (theorem) | Rewriting, Ring/field | Stdlib ring/field | Reviewed: keep established tactic/library proof |
| `independent_conditional_B_equals_marginal` (theorem) | Rewriting, Ring/field, Lra/Psatz | Stdlib.Lra/Psatz, Stdlib ring/field | Reviewed: keep established tactic/library proof |
| `independent_conditional_A_equals_marginal` (theorem) | Rewriting, Ring/field, Lra/Psatz | Stdlib.Lra/Psatz, Stdlib ring/field | Reviewed: keep established tactic/library proof |
| `independent_exactly_one_formula` (theorem) | Rewriting, Ring/field | Stdlib ring/field | Reviewed: keep established tactic/library proof |
| `disjointness_iff_union_is_sum` (theorem) | Lemma application, Lra/Psatz | Stdlib.Lra/Psatz | Reviewed: keep established tactic/library proof |
| `complete_coverage_iff_no_failures` (theorem) | Lemma application, Lra/Psatz | Stdlib.Lra/Psatz | Reviewed: keep established tactic/library proof |
| `equal_marginals_overlap_lower_bound` (theorem) | Lemma application, Lra/Psatz | Stdlib.Lra/Psatz | Reviewed: keep established tactic/library proof |
| `zero_first_marginal_forces_zero_overlap` (theorem) | Lemma application, Lra/Psatz | Stdlib.Lra/Psatz | Reviewed: keep established tactic/library proof |
| `zero_second_marginal_forces_zero_overlap` (theorem) | Lemma application, Lra/Psatz | Stdlib.Lra/Psatz | Reviewed: keep established tactic/library proof |
| `conditional_B_given_A_nonnegative` (theorem) | Lemma application | Prior named lemmas | Reviewed: keep established tactic/library proof |
| `conditional_A_given_B_nonnegative` (theorem) | Lemma application | Prior named lemmas | Reviewed: keep established tactic/library proof |
| `conditional_B_given_A_unit_interval` (theorem) | Lemma application | Prior named lemmas | Reviewed: keep established tactic/library proof |
| `conditional_A_given_B_unit_interval` (theorem) | Lemma application | Prior named lemmas | Reviewed: keep established tactic/library proof |
| `overlap_at_most_either` (theorem) | Lemma application, Rewriting, Lra/Psatz | Stdlib.Lra/Psatz | Reviewed: keep established tactic/library proof |
| `conditional_both_given_either_unit_interval` (theorem) | Lemma application, Rewriting, Ring/field, Lra/Psatz | Stdlib.Lra/Psatz, Stdlib ring/field | Reviewed: keep established tactic/library proof |
| `conditional_not_A_given_B_unit_interval` (theorem) | Lemma application, Lra/Psatz | Stdlib.Lra/Psatz | Reviewed: keep established tactic/library proof |
| `independence_iff_conditional_B_equals_marginal` (theorem) | Lemma application, Rewriting | Prior named lemmas | Reviewed: keep established tactic/library proof |
| `independence_iff_conditional_A_equals_marginal` (theorem) | Lemma application, Rewriting | Prior named lemmas | Reviewed: keep established tactic/library proof |

## FiniteUnion.v — 68 proof scripts

| Named declaration | Proof strategy | Library reuse | Refactor disposition |
|---|---|---|---|
| `indicator_nonnegative` (lemma) | Lra/Psatz | Stdlib.Lra/Psatz | Reviewed: keep established tactic/library proof |
| `indicator_at_most_one` (lemma) | Lra/Psatz | Stdlib.Lra/Psatz | Reviewed: keep established tactic/library proof |
| `sum_indicators_nonnegative` (lemma) | Lemma application | Shared finite sums | Reviewed: keep established tactic/library proof |
| `union_indicator_bound` (lemma) | Finite cases, Lemma application, Rewriting, Computation | Shared finite sums, Stdlib.List | Earlier library refactor retained |
| `event_member_implies_union` (lemma) | Lemma application | Stdlib.List | Reviewed: keep established tactic/library proof |
| `indicator_implication_bound` (lemma) | Lra/Psatz | Stdlib.Lra/Psatz | Reviewed: keep established tactic/library proof |
| `finite_sum_monotone` (lemma) | Lemma application | Shared finite sums | **Rewritten**: duplicated list induction removed |
| `finite_sum_extensional` (lemma) | Lemma application | Shared finite sums | Reviewed: keep established tactic/library proof |
| `finite_sum_addition` (lemma) | Lemma application | Shared finite sums | Reviewed: keep established tactic/library proof |
| `interchange_finite_sums` (lemma) | Lemma application, Rewriting | Shared finite sums | Earlier library refactor retained |
| `arbitrary_union_bound` (theorem) | Lemma application, Rewriting, Lra/Psatz | Stdlib.Lra/Psatz | Reviewed: keep established tactic/library proof |
| `arbitrary_union_contains_every_member` (theorem) | Lemma application, Lra/Psatz | Stdlib.Lra/Psatz | Reviewed: keep established tactic/library proof |
| `arbitrary_union_at_most_total_mass` (theorem) | Lemma application, Lra/Psatz | Stdlib.Lra/Psatz | Reviewed: keep established tactic/library proof |
| `normalized_arbitrary_union_at_most_one` (theorem) | Lemma application, Lra/Psatz | Stdlib.Lra/Psatz | Reviewed: keep established tactic/library proof |
| `arbitrary_union_nonnegative` (theorem) | Lemma application | Shared finite sums | Reviewed: keep established tactic/library proof |
| `finite_prob_true` (theorem) | Lemma application, Ring/field, Computation | Stdlib ring/field | Reviewed: keep established tactic/library proof |
| `finite_prob_false` (theorem) | Lemma application, Rewriting, Ring/field, Computation | Shared finite sums, Stdlib ring/field | Reviewed: keep established tactic/library proof |
| `finite_prob_zero_iff_no_positive_mass_support` (theorem) | Finite cases, Lemma application, Rewriting, Ring/field, Lra/Psatz, Computation | Shared finite sums, Stdlib.Lra/Psatz, Stdlib ring/field | Reviewed: keep established tactic/library proof |
| `finite_prob_positive_of_positive_support` (theorem) | Lemma application, Rewriting, Lra/Psatz, Computation | Shared finite sums, Stdlib.Lra/Psatz | Reviewed: keep established tactic/library proof |
| `finite_prob_as_filtered_mass` (theorem) | Finite cases, Lemma application, Rewriting, Ring/field, Computation | Shared finite sums, Stdlib ring/field | Reviewed: keep established tactic/library proof |
| `finite_prob_event_ext_on_samples` (theorem) | Rewriting, Lemma application, Computation | Stdlib.List.filter_ext_in, finite_prob_as_filtered_mass | **Refactored:** direct library filter extensionality rather than pointwise sum algebra |
| `finite_prob_on_filtered_samples` (theorem) | Finite cases, Lemma application, Rewriting, Ring/field | Stdlib.List.filter, Stdlib.Bool.andb, FiniteSum.finite_sum_filter, finite_sum_ext | **New:** formalized event intersection under filtered samples |
| `union_prob_on_filtered_samples` (theorem) | Lemma application | Prior checked finite_prob_on_filtered_samples, Stdlib.List.existsb | **New:** formalized union of events restricted to filtered outcomes |
| `finite_prob_filtered_partition` (theorem) | Lemma application | FiniteSum.finite_sum_filter_partition | **Refactored:** replaces event-specific Boolean case analysis with shared generic finite-sum partition lemma |
| `union_prob_filtered_partition` (theorem) | Lemma application | finite_prob_filtered_partition, Stdlib.List.existsb | **New:** finite event-family unions partition by sample selection |
| `finite_prob_sample_append` (theorem) | Lemma application | Shared finite sums | Reviewed: keep established tactic/library proof |
| `union_prob_sample_append` (theorem) | Lemma application | finite_prob_sample_append, Stdlib.List.existsb | **New:** union mass additive over concatenated outcome lists, no event-specific list induction |
| `finite_prob_filtered_append` (theorem) | Rewriting, Lemma application | Stdlib.List.filter_app, finite_prob_sample_append | **New:** filtered event mass additive over concatenated outcome lists |
| `union_prob_filtered_append` (theorem) | Rewriting, Lemma application | Stdlib.List.filter_app, union_prob_sample_append | **New:** union mass after filtering distributes over sample concatenation |
| `finite_prob_sample_permutation` (theorem) | Lemma application | Shared finite sums | Reviewed: keep established tactic/library proof |
| `union_prob_sample_permutation` (theorem) | Lemma application | Prior named lemmas | Reviewed: keep established tactic/library proof |
| `sum_marginal_probs_event_permutation` (theorem) | Lemma application | Shared finite sums | Reviewed: keep established tactic/library proof |
| `finite_prob_event_monotone` (theorem) | Lemma application, Lra/Psatz | Stdlib.Lra/Psatz | Reviewed: keep established tactic/library proof |
| `finite_prob_filtered_mass_le` (theorem) | Rewriting, Lemma application | Stdlib.Bool.andb_true_iff, finite_prob_on_filtered_samples, finite_prob_event_monotone | **New:** nonnegative sample mass cannot increase under Boolean sample selection |
| `union_prob_filtered_mass_le` (theorem) | Lemma application | finite_prob_filtered_mass_le and existing union_prob definition | **New:** union-mass counterpart without additional event-list induction |
| `normalized_finite_prob_unit_interval` (theorem) | Lemma application, Lra/Psatz | Shared finite sums, Stdlib.Lra/Psatz | Reviewed: keep established tactic/library proof |
| `empty_family_probability_zero` (theorem) | Lemma application | Prior named lemmas | Earlier library refactor retained |
| `singleton_family_probability` (theorem) | Lemma application, Rewriting, Computation | Prior named lemmas | Reviewed: keep established tactic/library proof |
| `union_prob_membership_extensional` (theorem) | Finite cases, Lemma application, Rewriting, Computation | Stdlib.List | Earlier library refactor retained |
| `union_prob_permutation_invariant` (theorem) | Lemma application | Stdlib.Permutation | Reviewed: keep established tactic/library proof |
| `union_prob_duplicate_route` (theorem) | Lemma application, Computation | Prior named lemmas | Reviewed: keep established tactic/library proof |
| `indicator_complement` (lemma) | Ring/field, Computation | Stdlib ring/field | Reviewed: keep established tactic/library proof |
| `finite_prob_complement` (theorem) | Lemma application, Rewriting | finite_prob_as_filtered_mass, FiniteSum.finite_sum_filter_partition, Stdlib.Reals.Rplus_comm | **Refactored:** replaces event-specific indicator arithmetic with generic Boolean partition of finite samples |
| `normalized_finite_prob_complement` (theorem) | Lemma application, Rewriting, Lra/Psatz | Stdlib.Lra/Psatz | Reviewed: keep established tactic/library proof |
| `indicator_union_intersection` (lemma) | Ring/field, Computation | Stdlib ring/field | Reviewed: keep established tactic/library proof |
| `finite_prob_inclusion_exclusion` (theorem) | Lemma application, Rewriting, Ring/field | Stdlib ring/field | Reviewed: keep established tactic/library proof |
| `two_event_union_probability` (theorem) | Lemma application, Rewriting, Computation | Prior named lemmas | Reviewed: keep established tactic/library proof |
| `two_event_union_inclusion_exclusion` (theorem) | Lemma application, Rewriting | Prior named lemmas | Reviewed: keep established tactic/library proof |
| `any_event_append` (lemma) | Rewriting, Computation | Prior named lemmas | Reviewed: keep established tactic/library proof |
| `union_prob_append` (theorem) | Lemma application | finite_prob_event_ext_on_samples, any_event_append (Stdlib.List.existsb_app) | **Refactored:** reuse established Boolean-event extensionality instead of duplicating finite-sum extensionality |
| `sum_marginal_probs_append` (theorem) | Lemma application | Shared finite sums | Reviewed: keep established tactic/library proof |
| `finite_intersection_at_most_first` (theorem) | Lemma application | Prior named lemmas | Reviewed: keep established tactic/library proof |
| `finite_intersection_at_most_second` (theorem) | Lemma application | Prior named lemmas | Reviewed: keep established tactic/library proof |
| `finite_frechet_lower_bound` (theorem) | Lemma application, Lra/Psatz | Stdlib.Lra/Psatz | Reviewed: keep established tactic/library proof |
| `finite_conditional_prob_filtered` (theorem) | Rewriting, Computation | finite_prob_on_filtered_samples, Stdlib.List.filter | **New:** generic quotient interpretation of selected outcome lists |
| `finite_conditional_prob_self` (theorem) | Finite cases, Rewriting, Lemma application | finite_prob_event_ext_on_samples; Stdlib.Reals field tactic | **New:** positive-mass event conditional on itself equals one |
| `finite_conditional_prob_unit_interval` (theorem) | Lemma application, Rewriting, Real inequalities | finite_prob_event_monotone, finite_intersection_at_most_first, Stdlib.Reals | **New:** nonnegative bounded conditional mass for positive conditioning mass |
| `finite_conditional_prob_event_ext_on_conditioned_samples` (theorem) | Finite cases, Lemma application | finite_prob_event_ext_on_samples, Stdlib.Bool.andb | **New:** weaker event agreement only where conditioning event holds |
| `finite_conditional_prob_event_ext_on_samples` (theorem) | Lemma application | finite_conditional_prob_event_ext_on_conditioned_samples | **Refactored:** delegate to stronger support theorem without duplicated conjunction proof |
| `finite_conditional_prob_complement` (theorem) | Rewriting, Stdlib inverse cancellation | finite_conditional_prob_filtered, finite_prob_complement, finite_prob_as_filtered_mass, Stdlib.Reals.Rinv_r | **New:** conditional complement mass sums to one |
| `finite_conditional_prob_monotone` (theorem) | Lemma application, Boolean conjunction | finite_prob_event_monotone, Stdlib.Bool.andb_true_iff, Stdlib.Reals inverse/order | **New:** conditional event implication monotonicity |
| `finite_conditional_prob_true` (theorem) | Lemma application | finite_conditional_prob_event_ext_on_conditioned_samples, finite_conditional_prob_self | **New:** true target conditionally has mass one |
| `finite_conditional_prob_conditioning_ext_on_samples` (theorem) | Rewriting, Lemma application | finite_prob_event_ext_on_samples | **New:** conditioning event support extensionality |
| `finite_conditional_prob_false` (theorem) | Lemma application, ring algebra | finite_prob_event_ext_on_samples, finite_prob_false, Stdlib.Bool | **New:** conditional false-event mass is zero |
| `finite_conditional_prob_inclusion_exclusion` (theorem) | Rewriting, shared inverse factoring | finite_conditional_prob_filtered, finite_prob_inclusion_exclusion, Stdlib.List.filter | **New:** conditional two-event inclusion-exclusion |
| `finite_conditional_prob_bayes_balance` (theorem) | Rewriting, field algebra | finite_prob_event_ext_on_samples, Stdlib.Bool.andb_comm, Stdlib.Reals | **New:** positive-marginal Bayes balance |
| `finite_conditional_prob_total_probability` (theorem) | Rewriting, field algebra | finite_prob_filtered_partition, finite_conditional_prob_filtered, Stdlib.List.filter | **New:** partition-based law of total probability |
| `finite_conditional_prob_chain_rule` (theorem) | Lemma application, real-field cancellation | Stdlib.Bool.andb_assoc, finite_prob_event_ext_on_samples, Stdlib.Reals | **New:** positive-denominator finite conditional chain rule |

## FiniteMoments.v — 132 proof scripts

| Named declaration | Proof strategy | Library reuse | Refactor disposition |
|---|---|---|---|
| `sum_finite_ext` (lemma) | Lemma application | Shared finite sums | Reviewed: keep established tactic/library proof |
| `sum_finite_add` (lemma) | Lemma application | Shared finite sums | Reviewed: keep established tactic/library proof |
| `sum_finite_scale` (lemma) | Lemma application | Shared finite sums | Reviewed: keep established tactic/library proof |
| `sum_finite_nonnegative` (lemma) | Lemma application | Shared finite sums | Reviewed: keep established tactic/library proof |
| `expectation_extensional_on_samples` (theorem) | Lemma application | FiniteSum.finite_sum_ext_in, Stdlib.List.map_ext_in | **New:** expectation support extensionality |
| `expectation_ext` (theorem) | Lemma application | expectation_extensional_on_samples | **Refactored:** delegate to on-sample equality |
| `expectation_add` (theorem) | Lemma application, Rewriting, Ring/field | Stdlib ring/field | Reviewed: keep established tactic/library proof |
| `expectation_scale` (theorem) | Lemma application, Rewriting, Ring/field | Stdlib ring/field | Reviewed: keep established tactic/library proof |
| `expectation_zero` (theorem) | Lemma application, Rewriting, Ring/field | Shared finite sums, Stdlib ring/field | Reviewed: keep established tactic/library proof |
| `expectation_constant` (theorem) | Lemma application, Rewriting, Ring/field, Computation | Stdlib ring/field | Reviewed: keep established tactic/library proof |
| `expectation_constant_normalized` (theorem) | Rewriting, Ring/field | Stdlib ring/field | Reviewed: keep established tactic/library proof |
| `expectation_sub` (theorem) | Lemma application, Rewriting, Ring/field | Shared finite sums, Stdlib ring/field | Earlier library refactor retained |
| `expectation_affine` (theorem) | Lemma application, Rewriting, Ring/field | Stdlib ring/field | Reviewed: keep established tactic/library proof |
| `expectation_nonnegative` (theorem) | Lemma application, Lra/Psatz | Stdlib.Lra/Psatz | Reviewed: keep established tactic/library proof |
| `covariance_symmetric` (theorem) | Lemma application, Rewriting, Ring/field | Stdlib ring/field | Reviewed: keep established tactic/library proof |
| `covariance_scale_first` (theorem) | Lemma application, Rewriting, Ring/field | Stdlib ring/field | Reviewed: keep established tactic/library proof |
| `covariance_add_first` (theorem) | Lemma application, Rewriting, Ring/field | Stdlib ring/field | Reviewed: keep established tactic/library proof |
| `covariance_scale_second` (theorem) | Rewriting, Computation | Prior named lemmas | Reviewed: keep established tactic/library proof |
| `covariance_add_second` (theorem) | Rewriting, Computation | Prior named lemmas | Reviewed: keep established tactic/library proof |
| `variance_second_moment` (theorem) | Computation | Definitional reduction | Reviewed: keep established tactic/library proof |
| `variance_of_scaled_score` (theorem) | Rewriting, Ring/field | Stdlib ring/field | Reviewed: keep established tactic/library proof |
| `variance_of_two_score_sum` (theorem) | Rewriting, Ring/field | Stdlib ring/field | Reviewed: keep established tactic/library proof |
| `centered_second_moment_identity` (theorem) | Lemma application, Rewriting, Ring/field | Stdlib ring/field | Reviewed: keep established tactic/library proof |
| `variance_nonnegative` (theorem) | Lemma application, Rewriting | Prior named lemmas | Reviewed: keep established tactic/library proof |
| `covariance_with_constant_first` (theorem) | Rewriting, Ring/field, Computation | Stdlib ring/field | Reviewed: keep established tactic/library proof |
| `variance_of_shifted_score` (theorem) | Lemma application, Rewriting, Ring/field | Stdlib ring/field | Reviewed: keep established tactic/library proof |
| `covariance_extensional_on_samples` (theorem) | Rewriting, Lemma application | expectation_extensional_on_samples | **New:** covariance support extensionality |
| `covariance_extensional` (theorem) | Lemma application | covariance_extensional_on_samples | **Refactored:** remove duplicated expectation/product rewrites |
| `variance_extensional_on_samples` (theorem) | Lemma application | covariance_extensional_on_samples | **New:** variance support extensionality |
| `variance_extensional` (theorem) | Lemma application | variance_extensional_on_samples | **Refactored:** direct stronger-lemma reuse |
| `centered_score_has_zero_expectation` (theorem) | Rewriting, Ring/field | Stdlib ring/field | Reviewed: keep established tactic/library proof |
| `covariance_with_constant_second` (theorem) | Lemma application, Rewriting | Prior named lemmas | Reviewed: keep established tactic/library proof |
| `covariance_invariant_under_first_shift` (theorem) | Rewriting, Ring/field | Stdlib ring/field | Reviewed: keep established tactic/library proof |
| `covariance_invariant_under_second_shift` (theorem) | Rewriting, Ring/field | Stdlib ring/field | Reviewed: keep established tactic/library proof |
| `variance_of_two_weighted_scores` (theorem) | Rewriting, Ring/field | Stdlib ring/field | Reviewed: keep established tactic/library proof |
| `covariance_of_two_weighted_pairs` (theorem) | Rewriting, Ring/field | Stdlib ring/field | Reviewed: keep established tactic/library proof |
| `variance_of_two_score_average` (theorem) | Lemma application, Rewriting, Ring/field | Stdlib ring/field | Reviewed: keep established tactic/library proof |
| `variance_of_two_unit_variance_average` (theorem) | Rewriting, Ring/field | Stdlib ring/field | Reviewed: keep established tactic/library proof |
| `variance_of_standardized_score` (theorem) | Lemma application, Rewriting, Ring/field, Lra/Psatz | Stdlib.Lra/Psatz, Stdlib ring/field | Reviewed: keep established tactic/library proof |
| `variance_of_iq_reporting_scale` (theorem) | Lemma application, Rewriting, Ring/field | Stdlib ring/field | Reviewed: keep established tactic/library proof |
| `expectation_of_general_weighted_sum` (lemma) | Lemma application, Rewriting, Ring/field, Computation | Shared finite sums, Stdlib ring/field | Earlier library refactor retained |
| `covariance_of_general_weighted_second_unconditional` (lemma) | Lemma application, Rewriting, Ring/field, Computation | Stdlib.List.map, shared finite_sum_map/scale/sub/ext, expectation_of_general_weighted_sum | **New stronger algebraic lemma:** covariance distributes over weighted finite scores without normalized mass |
| `covariance_of_general_weighted_second` (lemma) | Lemma application | covariance_of_general_weighted_second_unconditional | **Refactored:** removed component-list induction; retain original total_mass premise and proposition |
| `covariance_of_general_weighted_sums_unconditional` (theorem) | Lemma application, Rewriting, Computation | covariance_of_general_weighted_second_unconditional, covariance_symmetric, FiniteSum.finite_sum_ext | **New stronger theorem:** arbitrary finite weighted composite covariance needs no normalization premise |
| `covariance_of_general_weighted_sums` (theorem) | Lemma application | covariance_of_general_weighted_sums_unconditional | **Refactored:** original statement retained, direct reuse of unconditional theorem |
| `variance_of_general_weighted_sum_unconditional` (theorem) | Lemma application | covariance_of_general_weighted_sums_unconditional, existing variance definition | **New stronger theorem:** finite weighted variance quadratic form valid algebraically without unit mass |
| `variance_of_general_weighted_sum` (theorem) | Lemma application | variance_of_general_weighted_sum_unconditional | **Refactored:** original mass-one statement preserved and derived from stronger lemma |
| `covariance_quadratic_form_nonnegative` (theorem) | Lemma application, Rewriting | Prior named lemmas | Reviewed: keep established tactic/library proof |
| `mean_of_centered_standardized_score` (theorem) | Lemma application, Rewriting, Ring/field | Stdlib ring/field | Reviewed: keep established tactic/library proof |
| `mean_of_iq_reporting_scale` (theorem) | Lemma application, Rewriting, Ring/field | Stdlib ring/field | Reviewed: keep established tactic/library proof |
| `covariance_invariant_under_both_shifts` (theorem) | Lemma application, Rewriting | Prior named lemmas | Reviewed: keep established tactic/library proof |
| `covariance_of_centered_standardized_scores` (theorem) | Lemma application, Rewriting, Ring/field, Lra/Psatz | Stdlib.Lra/Psatz, Stdlib ring/field | Reviewed: keep established tactic/library proof |
| `self_covariance_of_standardized_score` (theorem) | Rewriting, Ring/field, Lra/Psatz | Stdlib.Lra/Psatz, Stdlib ring/field | Reviewed: keep established tactic/library proof |
| `variance_of_three_score_average` (theorem) | Lemma application, Rewriting, Ring/field | Stdlib ring/field | Reviewed: keep established tactic/library proof |
| `variance_of_three_standardized_score_average` (theorem) | Rewriting, Ring/field, Lra/Psatz | Stdlib.Lra/Psatz, Stdlib ring/field | Reviewed: keep established tactic/library proof |
| `variance_of_two_standardized_score_average` (theorem) | Rewriting, Computation | Prior named lemmas | Reviewed: keep established tactic/library proof |
| `covariance_double_sum_second_cons` (lemma) | Lemma application, Rewriting | Shared finite sums | Earlier library refactor retained |
| `covariance_double_sum_symmetric` (lemma) | Lemma application, Rewriting | Shared finite sums | Reviewed: keep established tactic/library proof |
| `double_sum_diagonal_off_diagonal` (lemma) | Structural induction, Rewriting, Ring/field | Stdlib ring/field | Reviewed: structural induction retained |
| `unweighted_scores_as_linear_combination` (lemma) | Lemma application, Rewriting, Ring/field, Computation | Shared finite sums, Stdlib ring/field | Reviewed: keep established tactic/library proof |
| `unweighted_covariance_row_as_weighted` (lemma) | Lemma application, Rewriting, Ring/field, Computation | Shared finite sums, Stdlib ring/field | Reviewed: keep established tactic/library proof |
| `covariance_with_sum_scores_unconditional` (lemma) | Lemma application, Rewriting, Computation | Stdlib.List.map, covariance_of_general_weighted_second_unconditional, unweighted_scores_as_linear_combination | **New unconditional score-sum covariance:** avoid mass assumptions without another list induction |
| `covariance_with_sum_scores` (lemma) | Lemma application | covariance_with_sum_scores_unconditional | **Refactored:** retains original mass-one statement but delegates to more general covariance proof |
| `covariance_of_sum_scores_unconditional` (lemma) | Lemma application, Rewriting | covariance_with_sum_scores_unconditional, covariance_symmetric, FiniteSum.finite_sum_ext | **New unconditional double covariance sum:** all sample weights and composite coefficients allowed |
| `covariance_of_sum_scores` (lemma) | Lemma application | covariance_of_sum_scores_unconditional | **Refactored:** original mass-one statement preserved as direct specialization |
| `variance_of_unweighted_sum_unconditional` (theorem) | Lemma application | covariance_of_sum_scores_unconditional | **New unconditional unweighted variance:** finite self-covariance double-sum identity |
| `variance_of_unweighted_sum` (theorem) | Lemma application | variance_of_unweighted_sum_unconditional | **Refactored:** retains original mass normalization premise without duplicate algebra |
| `variance_of_rescaled_unweighted_sum` (theorem) | Lemma application, Rewriting, Ring/field, Lra/Psatz | Stdlib.Lra/Psatz, Stdlib ring/field | Reviewed: keep established tactic/library proof |
| `diagonal_variance_sum_of_unit_scores` (lemma) | Lemma application, Rewriting, Ring/field | Shared finite sums, Stdlib ring/field | Earlier library refactor retained |
| `equal_weight_variance_from_finite_covariances` (theorem) | Rewriting, Ring/field, Lra/Psatz | Stdlib.Lra/Psatz, Stdlib ring/field | Reviewed: keep established tactic/library proof |
| `covariance_row_as_vector_dot` (lemma) | Lemma application, Rewriting, Computation | Shared finite sums | **Rewritten**: duplicated list induction removed |
| `covariance_double_sum_as_matrix_product` (lemma) | Lemma application, Rewriting, Computation | Shared finite sums, Stdlib.List | **Rewritten**: duplicated list induction removed |
| `covariance_matrix_quadratic_form_identity` (theorem) | Lemma application | Prior named lemmas | Reviewed: keep established tactic/library proof |
| `covariance_cross_matrix_bilinear_identity_unconditional` (theorem) | Lemma application, Rewriting | covariance_double_sum_as_matrix_product and unconditional weighted composite covariance | **New unconditional matrix theorem:** no mass normalization, induction, or new matrix implementation |
| `covariance_cross_matrix_bilinear_identity` (theorem) | Lemma application | `covariance_cross_matrix_bilinear_identity_unconditional` | **Refactored:** original theorem and mass-one premise preserved, direct reuse of stronger checked result |
| `covariance_cross_matrix_bilinear_swap_unconditional` (theorem) | Lemma application, Rewriting | covariance_symmetric and unconditional matrix bilinearity | **New unconditional matrix theorem:** no mass normalization, induction, or new matrix implementation |
| `covariance_cross_matrix_bilinear_swap` (theorem) | Lemma application | `covariance_cross_matrix_bilinear_swap_unconditional` | **Refactored:** original theorem and mass-one premise preserved, direct reuse of stronger checked result |
| `covariance_matrix_quadratic_form_is_variance_unconditional` (theorem) | Lemma application, Rewriting | covariance_matrix_quadratic_form_identity and unconditional weighted variance | **New unconditional matrix theorem:** no mass normalization, induction, or new matrix implementation |
| `covariance_matrix_quadratic_form_is_variance` (theorem) | Lemma application | `covariance_matrix_quadratic_form_is_variance_unconditional` | **Refactored:** original theorem and mass-one premise preserved, direct reuse of stronger checked result |
| `covariance_matrix_is_positive_semidefinite` (theorem) | Lemma application, Rewriting | Prior named lemmas | Reviewed: keep established tactic/library proof |
| `covariance_at_most_half_sum_of_variances` (theorem) | Lemma application, Rewriting, Ring/field, Lra/Psatz | Stdlib.Lra/Psatz, Stdlib ring/field | Reviewed: keep established tactic/library proof |
| `covariance_at_least_negative_half_sum_of_variances` (theorem) | Lemma application, Rewriting, Lra/Psatz | Stdlib.Lra/Psatz | Reviewed: keep established tactic/library proof |
| `covariance_of_unit_variance_scores_bounded` (theorem) | Lemma application, Rewriting, Lra/Psatz | Stdlib.Lra/Psatz | Reviewed: keep established tactic/library proof |
| `average_of_two_unit_variance_scores_bounded` (theorem) | Lemma application, Rewriting, Lra/Psatz | Stdlib.Lra/Psatz | Reviewed: keep established tactic/library proof |
| `feasible_average_pair_correlation_lower_bound` (theorem) | Lemma application, Rewriting, Ring/field, Lra/Psatz | Stdlib.Lra/Psatz, Stdlib ring/field | Reviewed: keep established tactic/library proof |
| `covariance_row_sum_bounded_by_count` (lemma) | Lemma application, Rewriting, Ring/field | Shared finite sums, Stdlib ring/field | Earlier library refactor retained |
| `unordered_covariance_sum_bounded_by_pair_count` (lemma) | Structural induction, Lemma application, Rewriting, Lra/Psatz, Computation | Stdlib.Lra/Psatz | Reviewed: structural induction retained |
| `feasible_average_pair_correlation_upper_bound` (theorem) | Lemma application, Rewriting, Lra/Psatz | Stdlib.Lra/Psatz | Reviewed: keep established tactic/library proof |
| `feasible_average_pair_correlation_interval` (theorem) | Lemma application | Prior named lemmas | Reviewed: keep established tactic/library proof |
| `nonnegative_quadratic_discriminant` (lemma) | Finite cases, Lemma application, Rewriting, Ring/field, Lra/Psatz | Stdlib.Lra/Psatz, Stdlib ring/field | Reviewed: keep established tactic/library proof |
| `finite_covariance_cauchy_schwarz_squared` (theorem) | Lemma application, Rewriting, Ring/field | Stdlib ring/field | Reviewed: keep established tactic/library proof |
| `zero_variance_implies_zero_covariance_first` (theorem) | Lemma application, Rewriting, Lra/Psatz | Stdlib.Lra/Psatz | Reviewed: keep established tactic/library proof |
| `zero_variance_implies_zero_covariance_second` (theorem) | Lemma application, Rewriting | Prior named lemmas | Reviewed: keep established tactic/library proof |
| `nonzero_covariance_implies_positive_variances` (theorem) | Finite cases, Lemma application, Lra/Psatz | Stdlib.Lra/Psatz | Reviewed: keep established tactic/library proof |
| `weighted_basis_sum_as_combination` (lemma) | Computation | Definitional reduction | Reviewed: minimal definitional proof |
| `split_as_projection_maps` (lemma) | Structural induction, Rewriting, Computation | Prior named lemmas | Reviewed: structural induction retained |
| `coefficients_of_combine` (lemma) | Lemma application, Rewriting | Prior named lemmas | Earlier library refactor retained |
| `basis_of_combine` (lemma) | Lemma application, Rewriting | Prior named lemmas | Earlier library refactor retained |
| `covariance_matrix_uses_only_basis` (lemma) | Lemma application, Rewriting, Computation | Stdlib.List | Reviewed: keep established tactic/library proof |
| `covariance_cross_matrix_uses_only_bases` (lemma) | Lemma application, Rewriting, Computation | Stdlib.List | Reviewed: keep established tactic/library proof |
| `fixed_basis_covariance_matrix_representation` (theorem) | Rewriting, Computation | Prior named lemmas | Reviewed: keep established tactic/library proof |
| `fixed_basis_weighted_variance_identity` (theorem) | Lemma application, Rewriting | Stdlib.List | Reviewed: keep established tactic/library proof |
| `fixed_basis_covariance_matrix_positive_semidefinite` (theorem) | Lemma application, Rewriting | Prior named lemmas | Reviewed: keep established tactic/library proof |
| `normalized_covariance_is_between_minus_one_and_one` (theorem) | Finite cases, Lemma application, Rewriting, Ring/field, Lra/Psatz | Stdlib.Lra/Psatz, Stdlib ring/field | Reviewed: keep established tactic/library proof |
| `centered_standardized_covariance_in_unit_interval` (theorem) | Lemma application, Rewriting, Lra/Psatz | Stdlib.Lra/Psatz | Reviewed: keep established tactic/library proof |
| `unit_covariance_one_iff_difference_has_zero_variance` (theorem) | Lemma application, Rewriting, Ring/field, Lra/Psatz | Stdlib.Lra/Psatz, Stdlib ring/field | Reviewed: keep established tactic/library proof |
| `unit_covariance_minus_one_iff_sum_has_zero_variance` (theorem) | Rewriting, Lra/Psatz | Stdlib.Lra/Psatz | Reviewed: keep established tactic/library proof |
| `variance_of_affine_score` (theorem) | Lemma application, Rewriting | Prior named lemmas | Reviewed: keep established tactic/library proof |
| `covariance_of_affine_scores` (theorem) | Rewriting, Ring/field | Stdlib ring/field | Reviewed: keep established tactic/library proof |
| `basis_covariance_matrix_row_count` (lemma) | Lemma application | Prior named lemmas | Reviewed: keep established tactic/library proof |
| `basis_covariance_matrix_column_count` (lemma) | Finite cases, Lemma application | Prior named lemmas | Reviewed: keep established tactic/library proof |
| `basis_cross_covariance_matrix_row_count` (lemma) | Lemma application | Prior named lemmas | Reviewed: keep established tactic/library proof |
| `basis_cross_covariance_matrix_column_count` (lemma) | Finite cases, Lemma application | Prior named lemmas | Reviewed: keep established tactic/library proof |
| `sum_finite_zero_implies_zero_terms` (lemma) | Lemma application | Shared finite sums | Earlier library refactor retained |
| `zero_variance_is_constant_on_positive_mass` (theorem) | Finite cases, Lemma application, Rewriting, Lra/Psatz | Stdlib.Lra/Psatz | Reviewed: keep established tactic/library proof |
| `null_covariance_direction_constant_on_positive_mass` (theorem) | Lemma application, Rewriting | Prior named lemmas | Reviewed: keep established tactic/library proof |
| `sum_scores_permutation_invariant` (lemma) | Lemma application | Shared finite sums | Reviewed: keep established tactic/library proof |
| `variance_of_permuted_score_sum` (theorem) | Lemma application | Prior named lemmas | Reviewed: keep established tactic/library proof |
| `equal_weight_variance_permutation_invariant` (theorem) | Lemma application, Rewriting, Computation | Prior named lemmas | Reviewed: keep established tactic/library proof |
| `fixed_basis_covariance_cauchy_schwarz_squared` (theorem) | Rewriting, Lemma application | fixed_basis_weighted_variance_identity, finite_covariance_cauchy_schwarz_squared | **New:** compare basis-matrix quadratic form against covariance with arbitrary score |
| `null_covariance_direction_orthogonal_to_every_score` (theorem) | Rewriting, Lemma application | fixed_basis_weighted_variance_identity, zero_variance_implies_zero_covariance_first | **New:** matrix null direction is covariance-orthogonal to every finite score |
| `null_covariance_direction_pairwise_constant_on_positive_mass` (theorem) | Lemma application, Transitivity | null_covariance_direction_constant_on_positive_mass | **New:** any two positive-support outcomes have equal scores in a null direction |
| `variance_of_constant_score_zero` (theorem) | Lemma application | covariance_with_constant_first | **New:** reusable zero variance for constant score under total mass one |
| `duplicate_basis_nontrivial_null_direction` (theorem) | Rewriting, Lemma application, ring and Lra | fixed_basis_weighted_variance_identity, variance_extensional, variance_of_constant_score_zero, Stdlib.List.combine and FiniteSum.finite_sum | **New:** explicit nonzero null coefficient vector for duplicated score basis |
| `expectation_extensional_on_positive_weight_support` (theorem) | Real-order case split, lemma application | FiniteSum.finite_sum_ext_in, Stdlib.Reals.Rle_lt_dec, Lra | **New:** ignore zero-mass score changes without signed-weight assumptions |
| `covariance_extensional_on_positive_weight_support` (theorem) | Rewriting, lemma application | expectation_extensional_on_positive_weight_support | **New:** covariance invariance under changes off positive support |
| `variance_extensional_on_positive_weight_support` (theorem) | Lemma application | covariance_extensional_on_positive_weight_support | **New:** variance invariance on positive support |
| `variance_zero_of_constant_on_positive_weight_support` (theorem) | Lemma application, equality transitivity | variance_extensional_on_positive_weight_support, variance_of_constant_score_zero | **New:** constant positive support entails zero finite variance |
| `variance_zero_iff_constant_on_positive_weight_support` (theorem) | Lemma application, iff split | zero_variance_is_constant_on_positive_mass, variance_zero_of_constant_on_positive_weight_support | **New:** zero variance iff constant score on positive-mass outcomes |
| `variance_zero_iff_covariance_zero_with_every_score` (theorem) | Lemma application, definitional reduction | zero_variance_implies_zero_covariance_first, variance | **New:** zero variance iff zero covariance with every comparison score |
| `fixed_basis_null_iff_constant_on_positive_weight_support` (theorem) | Rewriting, lemma application | fixed_basis_weighted_variance_identity, variance_zero_iff_constant_on_positive_weight_support | **Refactored:** complete fixed-basis null iff delegates to generic variance equivalence |
| `fixed_basis_null_iff_orthogonal_to_every_score` (theorem) | Rewriting, lemma application | fixed_basis_weighted_variance_identity, variance_zero_iff_covariance_zero_with_every_score | **New:** fixed-basis null directions iff orthogonal to all finite scores |

## FiniteBridge.v — 16 proof scripts

| Named declaration | Proof strategy | Library reuse | Refactor disposition |
|---|---|---|---|
| `finite_sum_models_agree` (theorem) | Computation | Definitional reduction | Earlier library refactor retained |
| `finite_total_mass_models_agree` (theorem) | Computation | Definitional reduction | Reviewed: minimal definitional proof |
| `finite_event_probability_is_indicator_expectation` (theorem) | Computation | Definitional reduction | Reviewed: minimal definitional proof |
| `filtered_event_mass_is_indicator_expectation` (theorem) | Rewriting, Lemma application | FiniteUnion.finite_prob_on_filtered_samples; finite_event_probability_is_indicator_expectation; Stdlib.List.filter | **New:** bridge event mass on filtered samples to the conjunction-indicator moment |
| `filtered_union_mass_is_indicator_expectation` (theorem) | Rewriting, Lemma application | FiniteUnion.union_prob_on_filtered_samples; finite_event_probability_is_indicator_expectation; Stdlib.List.existsb | **New:** bridge filtered family-union mass to a single indicator-score expectation |
| `indicator_square` (lemma) | Ring/field | Stdlib ring/field | Reviewed: keep established tactic/library proof |
| `indicator_product_and` (lemma) | Ring/field, Computation | Stdlib ring/field | Reviewed: keep established tactic/library proof |
| `finite_event_indicator_variance` (theorem) | Lemma application, Rewriting, Ring/field | Stdlib ring/field | Reviewed: keep established tactic/library proof |
| `finite_event_indicator_covariance` (theorem) | Lemma application, Rewriting, Computation | Prior named lemmas | Reviewed: keep established tactic/library proof |
| `finite_event_independence_iff_zero_indicator_covariance` (theorem) | Rewriting, Lra/Psatz | Stdlib.Lra/Psatz | Reviewed: keep established tactic/library proof |
| `finite_event_indicator_zero_variance_iff_extreme_mass` (theorem) | Finite cases, Lemma application, Rewriting, Ring/field, Lra/Psatz | Stdlib.Lra/Psatz, Stdlib ring/field | Reviewed: keep established tactic/library proof |
| `finite_event_indicator_variance_at_most_quarter` (theorem) | Lemma application, Rewriting, Lra/Psatz | Stdlib.Lra/Psatz | Reviewed: keep established tactic/library proof |
| `finite_event_indicator_complement_variance` (theorem) | Rewriting, Ring/field | Stdlib ring/field | Reviewed: keep established tactic/library proof |
| `finite_event_indicator_covariance_complement_second` (theorem) | Finite cases, Lemma application, Rewriting, Ring/field, Computation | Stdlib ring/field | Reviewed: keep established tactic/library proof |
| `finite_event_indicator_covariance_complement_first` (theorem) | Lemma application, Rewriting | Prior named lemmas | Reviewed: keep established tactic/library proof |
| `finite_event_indicator_covariance_complement_both` (theorem) | Rewriting, Ring/field | Stdlib ring/field | Reviewed: keep established tactic/library proof |

## FourCellBridge.v — 22 proof scripts

| Named declaration | Proof strategy | Library reuse | Refactor disposition |
|---|---|---|---|
| `four_cell_samples_complete` (theorem) | Finite cases, Lemma application, Computation | Stdlib.List | Reviewed: keep established tactic/library proof |
| `four_cell_samples_length` (theorem) | Rewriting, Computation | Stdlib.List | Reviewed: keep established tactic/library proof |
| `four_cell_weight_nonnegative` (theorem) | Finite cases, Lemma application, Computation | Prior named lemmas | Reviewed: keep established tactic/library proof |
| `four_cell_total_mass` (theorem) | Lemma application, Lra/Psatz, Computation | Shared finite sums, Stdlib.Lra/Psatz | Reviewed: keep established tactic/library proof |
| `four_cell_first_marginal` (theorem) | Ring/field, Computation | Shared finite sums, Stdlib ring/field | Reviewed: keep established tactic/library proof |
| `four_cell_second_marginal` (theorem) | Ring/field, Computation | Shared finite sums, Stdlib ring/field | Reviewed: keep established tactic/library proof |
| `four_cell_intersection_mass` (theorem) | Ring/field, Computation | Shared finite sums, Stdlib ring/field | Reviewed: keep established tactic/library proof |
| `four_cell_union_mass` (theorem) | Ring/field, Computation | Shared finite sums, Stdlib ring/field | Reviewed: keep established tactic/library proof |
| `four_cell_exactly_one_mass` (theorem) | Ring/field, Computation | Shared finite sums, Stdlib ring/field | Reviewed: keep established tactic/library proof |
| `four_cell_indicator_covariance` (theorem) | Rewriting, Computation | Prior named lemmas | Reviewed: keep established tactic/library proof |
| `four_cell_indicator_independence_criterion` (theorem) | Rewriting, Lra/Psatz | Stdlib.Lra/Psatz | Reviewed: keep established tactic/library proof |
| `four_cell_first_indicator_variance` (theorem) | Rewriting, Computation | Prior named lemmas | Reviewed: keep established tactic/library proof |
| `four_cell_second_indicator_variance` (theorem) | Rewriting, Computation | Prior named lemmas | Reviewed: keep established tactic/library proof |
| `four_cell_second_without_first_mass` (theorem) | Computation, Ring/field | Stdlib.List.list_prod, FiniteUnion.finite_prob, Stdlib.Bool | **New:** Exact B-only event interpretation; reuse of verified event results |
| `four_cell_conditional_B_given_A` (theorem) | Rewriting, Computation | four_cell_intersection_mass; four_cell_first_marginal | **New:** Positive-A conditional bridge; reuse of verified event results |
| `four_cell_conditional_A_given_B` (theorem) | Rewriting, Computation | four_cell_intersection_mass; four_cell_second_marginal | **New:** Positive-B conditional bridge; reuse of verified event results |
| `four_cell_conditional_both_given_either` (theorem) | Rewriting, Computation | four_cell_intersection_mass; four_cell_union_mass | **New:** Positive-union conditional bridge; reuse of verified event results |
| `four_cell_conditional_not_A_given_B` (theorem) | Rewriting, Computation | four_cell_second_without_first_mass; four_cell_second_marginal | **New:** Positive-B failure conditional bridge; reuse of verified event results |
| `four_cell_generic_conditional_B_given_A` (theorem) | Lemma application, Computation | FiniteUnion.finite_conditional_prob; four_cell_conditional_B_given_A | **New:** reuse generic operator for B given A |
| `four_cell_generic_conditional_A_given_B` (theorem) | Lemma application, Computation | FiniteUnion.finite_conditional_prob; four_cell_conditional_A_given_B | **New:** reuse generic operator for A given B |
| `four_cell_generic_conditional_both_given_either` (theorem) | Finite cases, Rewriting, Lemma application | FiniteUnion.finite_prob_event_ext_on_samples, two_event_union_probability, four_cell_conditional_both_given_either | **New:** generic both-given-either bridge |
| `four_cell_generic_conditional_not_A_given_B` (theorem) | Rewriting, Lemma application | Stdlib.Bool.andb_comm, FiniteUnion.finite_prob_event_ext_on_samples, four_cell_conditional_not_A_given_B | **New:** generic B-only conditional bridge |
