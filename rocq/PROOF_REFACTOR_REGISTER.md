# Complete proof-script refactoring register

This register inventories **every `Proof. ... Qed.` or `Proof. ... Defined.`
script**, including local helpers and two explicit record constructors.
It is a proof-by-proof review of source structure, dependency reuse, and
whether an additional rewrite is justified; it is **not** a replacement for
Rocq 9.2 kernel checking or a claim that all scripts needed modification.

The current branch has **976 public theorem/lemma/example claims**, plus
one local helper and two constructed `Admissions.TwoEventModel` values:
**979 proof scripts** across seven Rocq modules. The claims and scripts
are counted separately because helper and record-constructor proof blocks
are included in the latter total.
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

### Sufficient positive-support witnesses for strictly positive variance

Four further finite theorems give explicit witnesses for positive
variance or a positive fixed-basis covariance quadratic form: a
positive-mass outcome whose score deviates from its mean, or two
positive-mass outcomes with distinct score values. The proofs
reuse checked variance nonnegativity, the zero-variance support
result, the fixed-basis variance identity, and Stdlib.Lra;
there is no new quadratic-form or matrix summation algorithm.

### Strict finite covariance positivity and positive-definiteness equivalence

Three new declarations reuse the generic variance_zero_iff support
characterization, variance_nonnegative and the fixed-basis moment
bridge to establish strict variance positivity iff support
nonconstancy, strict fixed-basis quadratic positivity iff support
nonconstancy, and positive definiteness for all nonzero coefficient
lists iff absence of any nonzero constant weighted-score direction.
The zero coefficient list is represented by Stdlib.List.repeat.
Two prior strict-variance proofs now delegate to the new generic
equivalence, eliminating duplicated real-order case splits.
There is no custom rank, determinant or vector indexing routine.

### Verified criteria for finite covariance positive definiteness

Three results reuse the previously checked strict-positive
quadratic-form witnesses and covariance nullity equivalences.
If every compatible nonzero coefficient list separates two
positive-weight outcomes, or deviates from its own expected
score at some positive-weight outcome, then the fixed-basis
covariance matrix is positive definite. A complementary iff
theorem characterizes positive definiteness as the absence
of nonzero coefficient directions having zero covariance
with every comparison score. The zero vector is represented
with Stdlib.List.repeat; no custom rank or matrix algorithm
is needed.

### Stronger finite support covariance and variance reuse

Two general support-constant covariance-zero theorems now reuse
covariance_extensional_on_positive_weight_support and the
already checked covariance_with_constant_first and symmetry laws.
The existing variance_zero_of_constant_on_positive_weight_support
proof is refactored to a one-step self-covariance application.
A further iff theorem characterizes zero variance by the
existence of any real constant on positive-weight sampled support.
No new summation, list induction, or matrix algebra is introduced.

### Existential support constants and concrete duplicate-basis degeneracy

The exact finite variance positive/null results are now stated
without preselecting the expectation as the supported constant:
zero variance iff some constant exists on positive-weight support,
and strict positive variance iff no such constant exists.
Two fixed-basis analogues reuse the established matrix/variance
identity instead of duplicating covariance algebra.
An additional concrete theorem rules out positive definiteness
for the duplicate-score basis [f;f] using the existing
[1;-1] null witness and Stdlib.List.repeat. No custom
determinant, rank, list fold or vector-space implementation.

### Matrix-level affine covariance transformations via Stdlib maps

The existing covariance_of_affine_scores identity is now lifted
to the rectangular basis_cross_covariance_matrix using only
Stdlib.List.map_map and map_ext, and then to the square
basis_covariance_matrix by the definitional cross-matrix bridge.
The transformations require unit total mass but no positivity
of the weights. Both theorem signatures have extensive
mathematical and implementation comments. No new row iterator,
matrix representation, index arithmetic or determinant code
has been added.

### Affine dependency rather than duplicated score-specific proofs

The duplicate-score null witness now delegates to the generic
sampled affine-dependence theorem using only a unit slope and
zero offset, eliminating repeated variance and finite-sum
reductions. A second theorem proves that affine dependence
restricted to positive-weight support produces the same
nonzero covariance null direction, using the existing
fixed_basis_null_iff_exists_constant_on_positive_weight_support.
The corresponding two-score non-positive-definite criterion
then reuses the witness and Stdlib.List.repeat. None of these
introduces a matrix rank or determinant implementation.

### Finite-coordinate covariance nullity and positive definiteness

The new null iff theorem requires zero covariance only against
the finitely enumerated basis functions. Its converse uses
covariance_of_general_weighted_second_unconditional, the existing
fixed-basis variance identity, Stdlib.List.in_map, the checked
basis_of_combine projection, and shared
FiniteSum.finite_sum_ext_in/finite_sum_zero; no matrix-vector
algorithm or list induction is introduced. Finite positive
semidefiniteness plus Stdlib real-order reasoning gives a strict
quadratic criterion, which lifts immediately to a
positive-definiteness iff theorem quantified over all nonzero
compatible coefficient lists. These results are exact finite
moment identities, not a spectral rank implementation.

### Actual covariance-matrix rowwise null characterization

The scalar covariance/weighted-score identity is re-expressed
as the coefficient vector dot the covariance row of each basis
score, via the existing covariance_of_general_weighted_second_unconditional,
covariance_row_as_vector_dot and Stdlib.List.map_map.
Stdlib.List.combine projection lemmas avoid new list recursions.
The rowwise quadratic-null iff then uses
fixed_basis_null_iff_uncorrelated_with_basis,
covariance_symmetric and Stdlib.List.in_map_iff to link every
list-of-lists covariance-matrix row to its originating basis score.
No rank, determinant, matrix multiplication, eigenvector or
nullspace-basis implementation is added.

### Strict covariance row conditions and precision audit

Two results apply existing covariance positive semidefiniteness and
rowwise quadratic-null iff to characterize strictly positive
quadratic values as failure of all-zero covariance row dot
products, then positive definiteness as the absence of a nonzero
compatible vector in that row-dot kernel. Only Stdlib.List.repeat,
Stdlib.Reals.Rle_dec and Lra are needed beyond previous lemmas.
Separately, the comments on vector_dot, basis_covariance_matrix,
basis_cross_covariance_matrix, covariance_row_as_vector_dot,
basis_of_combine and fixed_basis_covariance_matrix_positive_semidefinite
now explicitly explain their list-shape behavior, normalization
and sign assumptions, exact checked statements, the reused list
algebra, and why the positive-semidefinite and positive-definite
notions must not be conflated.

### General quadratic-null obstructions and refactored special cases

A purely algebraic lemma shows that any nonzero compatible
quadratic-null coefficient vector rules out strict positive
definiteness, without assuming nonnegative or unit sample
weights. A positive-support specialization reuses the existing
fixed_basis_null_iff_exists_constant_on_positive_weight_support
to cover any finite basis with a constant composite score.
The duplicated-score and affine-dependent two-score
non-positive-definiteness proofs now delegate to the generic
null-witness contradiction and no longer repeat local
strict-positivity proofs. Only Stdlib.List.repeat, Lra and
previously checked lemmas are used; no rank/determinant solver
or matrix library was reimplemented.

### General finite row-kernel witnesses without new matrix arithmetic

Two results connect the existing positive-support constant-score
characterization to every actual row of the list-based covariance
matrix, and turn a compatible nonzero row-dot kernel vector into
a formal obstruction to strict positive definiteness. Both are
direct compositions of checked nullity iff statements and the
new general non-positive-definiteness witness theorem, using
Stdlib.List.In and repeat. They introduce no new row iteration,
vector-space structure, numerical procedure or proof axiom.

### Exact row-kernel/support equivalence and refined core documentation

A new iff combines the checked quadratic-null iff row-dot-kernel
and quadratic-null iff supported-constant results, characterizing
finite covariance row nullity directly by a composite score
constant on positive-weight support. A second iff characterizes
positive definiteness by excluding any nonzero compatible
coefficient direction with such a supported constant. The proofs
are compositions of previously checked lemmas and Stdlib.List.repeat.
Five foundational declarations were also documented more precisely:
matrix_bilinear_form, matrix_quadratic_form, weighted_basis_sum,
fixed_basis_weighted_variance_identity, and
zero_variance_is_constant_on_positive_mass. Their comments now
specify exact shapes, coefficient lengths, weight normalization
and sign assumptions, proof dependencies and scope limitations.

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

## FiniteSum.v — 29 proof scripts

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
| `finite_sum_nonnegative_zero_iff` (lemma) | Zero-criterion equivalence via extensionality | finite_sum_nonnegative_zero, finite_sum_ext_in, finite_sum_zero | **New:** reversible zero condition on nonnegative finite support, without induction |
| `finite_sum_positive_of_positive_member` (lemma) | **Refactored:** strict positivity from already checked bound on a listed term | finite_sum_member_le, Stdlib.Lra | Removes real-order case split and repeated nonnegative-zero reasoning without changing statement |
| `finite_sum_strict_monotone_at_member` (lemma) | Positive difference sum and linearity | finite_sum_positive_of_positive_member, finite_sum_sub, Stdlib.Lra | **New:** strict monotonicity of sums from one strict coordinate |
| `finite_sum_positive_iff_positive_member` (lemma) | Constructive induction extracting a listed positive real term; converse via generic strict support theorem | finite_sum_positive_of_positive_member, Stdlib.Rlt_dec, Stdlib.List.map/fold_right, Lra | **New:** strict positivity of a nonnegative finite sum iff a positive listed term exists |
| `finite_sum_monotone_equality_iff_pointwise` (lemma) | Generic nonnegative difference zero criterion and linear arithmetic | finite_sum_nonnegative_zero_iff, finite_sum_sub, Stdlib.Lra | **New:** equality of ordered finite sums exactly when all enumerated terms agree; no duplicated induction |
| `finite_sum_strict_monotone_iff_strict_member` (lemma) | Constructive positive-difference support witness plus established strict-order converse | finite_sum_positive_iff_positive_member, finite_sum_strict_monotone_at_member, finite_sum_sub, Stdlib.Lra | **New:** strict inequality iff a listed strict comparison exists; reuses maintained generic theorems |


| `finite_sum_singleton_zero_iff` (lemma) | Singleton-list elimination and linear arithmetic; reusable formerly local argument | Stdlib.List.In/length, Lra, shared finite_sum | **New:** generic singleton zero iff member-zero characterization |
| `finite_sum_pair` (lemma) | Unfold existing map/fold for exactly two values, normalize by ring | Shared finite_sum, Stdlib.List, Stdlib.Reals ring | **New:** two-term finite sum computation |
| `finite_sum_pair_zero_iff_opposite` (lemma) | Rewrite pair fold identity; linear arithmetic | finite_sum_pair, Stdlib.Lra | **New:** zero pair sum iff opposite scores |

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

## FiniteUnion.v — 189 proof scripts

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
| `finite_prob_zero_iff_no_positive_mass_support` (theorem) | Generic nonnegative zero iff, Boolean cases, ring/nra | FiniteSum.finite_sum_nonnegative_zero_iff, Stdlib.Rmult_le_pos | **Refactored:** eliminates custom proof of zero sum; uses the common positive-support criterion |
| `finite_prob_positive_of_positive_support` (theorem) | Generic strict-sum positivity and indicator arithmetic | FiniteSum.finite_sum_positive_of_positive_member, Stdlib.Rmult_le_pos | **Refactored:** delegates strict positivity instead of locally deriving it through the member bound |
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
| `any_event_membership_ext` (lemma) | Transfer existsb witnesses across event-list membership equivalence | Stdlib.List.existsb_exists, Bool | **New:** shared union Boolean extensionality; eliminates duplicate witness analysis |
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
| `finite_conditional_prob_intersection_symmetric` (theorem) | Extensionality, Stdlib Boolean commutativity | finite_conditional_prob_event_ext_on_samples, Stdlib.Bool.andb_comm | **New:** joint conditional mass is invariant under target-event order |
| `finite_conditional_independent_symmetric` (theorem) | Conjunction decomposition, rewriting, real multiplication commutativity | finite_conditional_prob_intersection_symmetric, Stdlib.Reals.Rmult_comm | **New:** conditional independence is symmetric with explicit positive conditioning mass |
| `finite_conditional_independent_event_ext_on_conditioned_samples` (theorem) | Rewrite joint and first conditional marginal via conditioned support extensionality | finite_conditional_prob_event_ext_on_conditioned_samples, Stdlib.Bool.andb | **New:** first-target independence extensionality need only hold within conditioning event |
| `finite_conditional_independent_event_ext_on_samples` (theorem) | Delegate ordinary sample extensionality to stronger conditioned-support theorem | finite_conditional_independent_event_ext_on_conditioned_samples, Stdlib.List.In | **Refactored:** no independence unfolding or repeated conditional-mass rewrite |
| `finite_conditional_independent_conditioning_ext_on_samples` (theorem) | Rewriting both conditioning marginal and quotients | finite_prob_event_ext_on_samples, finite_conditional_prob_conditioning_ext_on_samples | **New:** conditioning-support invariance of the independence predicate |
| `finite_conditional_independent_second_event_ext_on_conditioned_samples` (theorem) | Swap targets, apply stronger support extensionality, swap back | finite_conditional_independent_symmetric, finite_conditional_independent_event_ext_on_conditioned_samples | **New:** second-target independence extensionality on conditioned support |
| `finite_conditional_independent_second_event_ext_on_samples` (theorem) | Iff rewriting and lemma application | finite_conditional_independent_symmetric, finite_conditional_independent_event_ext_on_samples | **New:** second-target support extensionality without duplicating the first-target proof |
| `finite_conditional_independent_sample_permutation` (theorem) | Rewriting finite event masses; no list recursion | finite_prob_sample_permutation, FiniteSum.finite_sum_permutation, Stdlib.Sorting.Permutation | **New:** independence is invariant under reordering all sampled weighted outcomes |
| `finite_conditional_prob_partition_by_event` (theorem) | Conditional inclusion–exclusion, beta normalization, Boolean extensionality and Lra | finite_conditional_prob_inclusion_exclusion, finite_conditional_prob_false, Stdlib.Bool | **New:** conditional event partition into target∧part and target∧¬part |
| `finite_conditional_independent_complement_first` (theorem) | Conditional partition and complement, polynomial equality | finite_conditional_prob_partition_by_event, finite_conditional_prob_complement, finite_conditional_prob_intersection_symmetric, Stdlib.Psatz.nra | **New:** conditional independence preserved under first-target complement |
| `finite_conditional_independent_complement_second` (theorem) | Symmetry and existing complement theorem | finite_conditional_independent_symmetric, finite_conditional_independent_complement_first | **New:** second-target complement without duplicate event algebra |
| `finite_conditional_independent_complement_both` (theorem) | Two theorem applications | finite_conditional_independent_complement_first, finite_conditional_independent_complement_second | **New:** simultaneous complement closure of finite conditional independence |
| `finite_conditional_prob_given_true_normalized` (theorem) | Rewriting by finite mass, unit division | finite_prob_event_ext_on_samples, finite_prob_true, Stdlib.Reals field/Lra | **New:** normalized conditioning on true leaves event mass unchanged |
| `finite_conditional_independent_given_true_iff_marginal_product` (theorem) | Existing theorem rewrites, iff splitting and Lra | finite_conditional_prob_given_true_normalized, finite_prob_true | **New:** unconditioned joint factorization coincides with generic independence under true conditioning |
| `finite_conditional_independent_true_first` (theorem) | Conditional target extensionality, unit product via Stdlib ring | finite_conditional_prob_event_ext_on_samples, finite_conditional_prob_true | **New:** trivial first target gives independence under positive conditioning mass |
| `finite_conditional_independent_true_second` (theorem) | Project symmetry iff, apply existing theorem | finite_conditional_independent_symmetric, finite_conditional_independent_true_first | **New:** certain-event second target via symmetry |
| `finite_conditional_independent_false_first` (theorem) | Extensionality to false, zero product via Stdlib ring | finite_conditional_prob_event_ext_on_samples, finite_conditional_prob_false | **New:** impossible-event first target is independent |
| `finite_conditional_independent_false_second` (theorem) | Project symmetry iff, apply existing theorem | finite_conditional_independent_symmetric, finite_conditional_independent_false_first | **New:** impossible-event second target via symmetry |
| `finite_conditional_independent_iff_cross_product_mass` (theorem) | Positive-denominator cancellation via field and Lra, two-way iff | finite_conditional_independent, finite_conditional_prob, finite_prob, Stdlib.Reals field | **New:** conditional product factorization iff unnormalized four-mass cross product |
| `finite_conditional_independent_conditioning_first` (theorem) | Conditioned-support target extensionality, unit conditional mass, ring | finite_conditional_prob_event_ext_on_conditioned_samples, finite_conditional_prob_self, Stdlib.Reals | **New:** given is independent of any second target conditional on itself |
| `finite_conditional_independent_conditioning_second` (theorem) | Iff symmetry projection and lemma application | finite_conditional_independent_symmetric, finite_conditional_independent_conditioning_first | **New:** other target independent of conditioning event given itself |
| `finite_conditional_independent_union_formula` (theorem) | Conditional inclusion-exclusion and factor rewrite | finite_conditional_prob_inclusion_exclusion, finite_conditional_independent, Stdlib.Lra | **New:** two-event conditional independent union formula |
| `finite_conditional_three_event_product` (theorem) | Boolean associativity, conditioned target extensionality, two independence factorizations | finite_conditional_prob_event_ext_on_samples, Stdlib.Bool.andb_assoc, Stdlib.Reals ring | **New:** triple conditional joint factors given independence of A,B and of A∩B,C (not merely pairwise independence) |
| `finite_conditional_independent_conditioning_complement_first` (theorem) | Reduce complement of conditioning to impossible target on conditioned support | finite_conditional_independent_false_first, finite_conditional_independent_event_ext_on_conditioned_samples | **New:** complementary selector independent of arbitrary target when conditioned on selector |
| `finite_conditional_independent_conditioning_complement_second` (theorem) | Symmetry reuse | finite_conditional_independent_symmetric, finite_conditional_independent_conditioning_complement_first | **New:** complementary selector independent in second position |
| `finite_conditional_prob_as_filtered_true` (theorem) | Simplify true-event intersection and reuse finite filtered mass/denominator identities | finite_prob_event_ext_on_samples, finite_prob_on_filtered_samples, finite_prob_true, finite_prob_as_filtered_mass | **New:** original conditioning equals true-event conditioning after filtering |
| `finite_conditional_independent_iff_filtered_true` (theorem) | Rewrite mass guard and three conditional terms via restriction theorem | finite_conditional_prob_as_filtered_true, finite_prob_true, finite_prob_as_filtered_mass | **New:** generic conditional independence iff certain-event independence on the selected sample list |
| `finite_conditional_independent_iff_filtered_cross_product` (theorem) | Rewrite existing conditioned cross-product criterion onto selected sublist | finite_conditional_independent_iff_cross_product_mass, finite_prob_on_filtered_samples, finite_prob_as_filtered_mass | **New:** denominator-free conditional independence criterion entirely on the filtered list |
| `all_events_append` (lemma) | Shared Boolean conjunction append via maintained forallb_app | Stdlib.List.forallb_app | **New:** reuse one Boolean append helper for both mass models |
| `finite_all_events_append` (theorem) | Lift the shared conjunction append identity under finite mass extensionality | all_events_append, finite_prob_event_ext_on_samples | **New:** unconditional mass of appended conjunction families |
| `finite_all_events_empty` (theorem) | Standard empty forallb and existing full-mass identity | Stdlib.List.forallb, finite_prob_true | **New:** empty required family has total weighted mass |
| `finite_all_events_singleton` (theorem) | Singleton forallb simplification via maintained finite event extensionality | Stdlib.List.forallb, finite_prob_event_ext_on_samples | **New:** singleton required family matches event mass |
| `finite_conditional_all_events_append` (theorem) | Conditional target extensionality using shared conjunction append helper | all_events_append, finite_conditional_prob_event_ext_on_samples | **Refactored:** eliminate repeated forallb_app unfolding |
| `finite_conditional_all_events_singleton` (theorem) | Standard singleton forallb computation under event extensionality | all_events, Stdlib.List.forallb, finite_conditional_prob_event_ext_on_samples | **New:** singleton joint conditional mass equals event mass |
| `finite_conditional_all_events_product` (theorem) | Event-list induction, chain-condition split and two-event factorization reuse | finite_conditional_prefix_independent, finite_conditional_prob_true, Stdlib.List.forallb/map/fold_right | **New:** arbitrary finite joint-event conditional product under stronger-than-pairwise suffix independence |
| `finite_conditional_union_contains_member` (theorem) | Conditional event monotonicity and existing union membership implication | finite_conditional_prob_monotone, event_member_implies_union, Stdlib.List.In | **New:** member conditional mass is at most finite union conditional mass |
| `finite_conditional_union_bound_filtered` (theorem) | Apply arbitrary union bound to conditioned List.filter and multiply by positive inverse | finite_conditional_prob_filtered, arbitrary_union_bound, Stdlib.List.filter_In, Stdlib.Reals.Rinv_0_lt_compat | **New:** distribution-free conditioned finite-family union upper bound |
| `finite_conditional_all_events_at_most_member` (theorem) | Conditional mass monotonicity with universal-list implication | finite_conditional_prob_monotone, Stdlib.List.forallb_forall, all_events | **New:** finite conditioned intersection bounded above by each member |
| `finite_conditional_marginals_sum_filtered` (theorem) | Factor common reciprocal out of standard FiniteSum of conditional marginals | FiniteSum.finite_sum_scale/finite_sum_ext, finite_conditional_prob_filtered, Stdlib.Reals ring | **New:** sum of conditional marginals equals sum on filtered sample divided by conditioning mass |
| `finite_conditional_union_bound` (theorem) | Rewrite marginal-sum identity and reuse conditioned finite union bound | finite_conditional_marginals_sum_filtered, finite_conditional_union_bound_filtered | **New:** standard finite conditional union bound directly in terms of conditional member probabilities |
| `finite_prob_scale_weights` (theorem) | Reuse shared finite_sum_scale, extensionality and ring | FiniteSum.finite_sum_scale, finite_sum_ext, Stdlib.Reals ring | **New:** finite Boolean event mass is homogeneous in the outcome weights |
| `finite_conditional_prob_scale_weights` (theorem) | Common positive numerator/denominator factor cancellation by field | finite_prob_scale_weights, Stdlib.Reals field, Stdlib.Lra | **New:** finite conditional masses invariant under a common positive weight scaling |
| `finite_conditional_independent_scale_weights` (theorem) | Positive-guard iff and conditional quotient rewrites | finite_prob_scale_weights, finite_conditional_prob_scale_weights, Stdlib.Psatz.nra | **New:** conditional-independence predicate iff preserved by common positive weight scaling |
| `all_events_membership_ext` (theorem) | Boolean true/false analysis via Stdlib forallb_forall | Stdlib.List.forallb_forall, all_events | **New:** conjunction predicate depends only on membership set, not ordering or duplicates |
| `all_events_permutation` (theorem) | Bidirectional membership transport through library permutation | all_events_membership_ext, Stdlib.Sorting.Permutation.Permutation_in/Permutation_sym | **New:** conditional event-family intersection invariant under list permutation |
| `finite_conditional_all_events_permutation` (theorem) | Conditional target extensionality using pointwise permutation invariance | finite_conditional_prob_event_ext_on_samples, all_events_permutation | **New:** conditional finite intersection mass invariant under event ordering |
| `all_events_membership_antitone` (lemma) | Shared Boolean inclusion via two maintained forallb_forall equivalences | Stdlib.List.forallb_forall | **Refactor:** centralize conjunction membership reasoning |
| `finite_all_events_subset` (theorem) | Use generic nonnegative event monotonicity and shared conjunction implication | finite_prob_event_monotone, all_events_membership_antitone | **New:** unconditional intersection mass antitone under family inclusion |
| `finite_conditional_all_events_subset` (theorem) | Conditioned mass monotonicity from shared Boolean conjunction implication | finite_conditional_prob_monotone, all_events_membership_antitone | **Refactored:** remove duplicated forallb_forall reasoning |
| `event_append_existing_membership_iff` (lemma) | Factor appended-event membership into one reusable Stdlib.List.in_app_iff proof | Stdlib.List.in_app_iff, Stdlib.List.In | **New:** Generic membership iff for appending an event already in the list |
| `finite_union_append_existing` (theorem) | Reuse generic union-probability membership extensionality and shared append-existing membership iff | union_prob_membership_extensional, event_append_existing_membership_iff | **New:** Appending any already-listed event leaves finite union mass unchanged |
| `finite_conditional_union_duplicate_head` (theorem) | Reuse conditional target extensionality and existing existsb Boolean idempotence | finite_conditional_prob_event_ext_on_samples, any_event, Stdlib.List.existsb | **New:** Conditional union mass invariant under a duplicated head event |
| `finite_intersection_duplicate_head` (theorem) | Generic finite probability extensionality and forallb/andb repeated-head idempotence | finite_prob_event_ext_on_samples, all_events, Stdlib.List.forallb | **New:** Unconditional intersection mass invariant under duplicating a required event |
| `finite_conditional_intersection_duplicate_head` (theorem) | Conditional target extensionality plus Stdlib conjunction predicate repeated-head identity | finite_conditional_prob_event_ext_on_samples, all_events, Stdlib.List.forallb | **New:** Conditional intersection mass invariant under a duplicated head event |
| `finite_intersection_append_existing` (theorem) | Compose finite event-mass extensionality and all_events_membership_ext with shared list-membership helper | finite_prob_event_ext_on_samples, all_events_membership_ext, event_append_existing_membership_iff | **New:** Appending an already-required event preserves unconditional intersection mass |
| `finite_conditional_intersection_append_existing` (theorem) | Conditioned event-target extensionality plus shared list-membership and conjunction laws | finite_conditional_prob_event_ext_on_samples, all_events_membership_ext, event_append_existing_membership_iff | **New:** Appending an already-required event preserves finite conditional intersection mass |

| `finite_conditional_union_membership_extensional` (theorem) | Lift shared pointwise union equivalence to conditional target equality | any_event_membership_ext, finite_conditional_prob_event_ext_on_samples | **New:** includes zero-conditioning-mass case |
| `finite_conditional_union_permutation` (theorem) | Transfer predicate membership under a Stdlib permutation | Permutation_in, finite_conditional_union_membership_extensional | **New:** reordering conditioned union alternatives |
| `finite_conditional_union_append_existing` (theorem) | Reuse already-present append membership equivalence | event_append_existing_membership_iff, finite_conditional_union_membership_extensional | **New:** adding an existing conditional union alternative |
| `any_event_membership_monotone` (lemma) | Transfer existsb witnesses through event membership inclusion | Stdlib.List.existsb_exists | **New:** a single Boolean implication for both probability laws |
| `finite_union_subset` (theorem) | Generic nonnegative event-mass monotonicity via shared Boolean inclusion | finite_prob_event_monotone, any_event_membership_monotone | **New:** distribution-free ordinary union inclusion inequality |
| `finite_conditional_union_subset` (theorem) | Reuse conditioned target monotonicity with shared Boolean inclusion | finite_conditional_prob_monotone, any_event_membership_monotone | **New:** distribution-free conditioned union inclusion inequality |
| `finite_conditional_union_empty` (theorem) | Reduce empty existsb and use established false-event conditional mass | Stdlib.List.existsb, finite_conditional_prob_false | **New:** arbitrary-conditioning empty-family identity |
| `finite_conditional_union_singleton` (theorem) | Lift singleton existsb computation through conditioned event extensionality | finite_conditional_prob_event_ext_on_samples, Stdlib.List.existsb | **New:** singleton conditional union exactly matches event mass |
| `finite_conditional_union_append` (theorem) | Reuse existing any_event_append and conditioned target extensionality | any_event_append, finite_conditional_prob_event_ext_on_samples, Stdlib.List.existsb_app | **New:** conditional append semantics without custom union recursion |
| `finite_conditional_all_events_empty` (theorem) | Reduce empty forallb and apply positive-denominator certain-event law | Stdlib.List.forallb, finite_conditional_prob_true | **New:** conditional unit mass of empty conjunction when conditioning is positive |
| `finite_conditional_all_events_cons` (theorem) | Reduce forallb cons through existing conditional target extensionality | Stdlib.List.forallb, finite_conditional_prob_event_ext_on_samples | **New:** head-tail conjunction semantics under conditioning |
| `finite_union_append_left_monotone` (theorem) | Standard in_or_app inclusion and existing finite family monotonicity | Stdlib.List.in_or_app, finite_union_subset | **New:** appending arbitrary alternatives weakly increases union mass |
| `finite_conditional_union_append_left_monotone` (theorem) | Standard in_or_app inclusion and positive-conditioner family monotonicity | Stdlib.List.in_or_app, finite_conditional_union_subset | **New:** conditional append monotonicity |
| `finite_union_append_right_monotone` (theorem) | Right-membership into app plus original union subset theorem | Stdlib.List.in_or_app, finite_union_subset | **New:** unconditional right-side append monotonicity |
| `finite_conditional_union_append_right_monotone` (theorem) | Right-membership into app plus conditional union subset theorem | Stdlib.List.in_or_app, finite_conditional_union_subset | **New:** conditional right-side append monotonicity |
| `finite_conditional_all_events_append_left_antitone` (theorem) | Left-membership into app plus conditional conjunction subset theorem | Stdlib.List.in_or_app, finite_conditional_all_events_subset | **New:** appending requirements weakly decreases left joint mass |
| `finite_conditional_all_events_append_right_antitone` (theorem) | Right-membership into app plus conditional conjunction subset theorem | Stdlib.List.in_or_app, finite_conditional_all_events_subset | **New:** prepending requirements weakly decreases right joint mass |
| `finite_all_events_append_left_antitone` (theorem) | Left-membership into app plus unconditional conjunction subset theorem | Stdlib.List.in_or_app, finite_all_events_subset | **New:** ordinary left conjunction append antitonicity |
| `finite_all_events_append_right_antitone` (theorem) | Right-membership into app plus unconditional conjunction subset theorem | Stdlib.List.in_or_app, finite_all_events_subset | **New:** ordinary right conjunction append antitonicity |
| `finite_all_events_cons` (theorem) | Lift maintained forallb cons through finite mass event extensionality | Stdlib.List.forallb, finite_prob_event_ext_on_samples | **New:** ordinary head-tail conjunction identity |
| `finite_all_events_membership_extensional` (theorem) | Lift existing pointwise conjunction membership extensionality | all_events_membership_ext, finite_prob_event_ext_on_samples | **New:** unconditional mass invariance under membership equivalence |
| `finite_all_events_permutation` (theorem) | Lift existing pointwise permutation theorem through finite event mass | all_events_permutation, Stdlib.Sorting.Permutation, finite_prob_event_ext_on_samples | **New:** ordinary conjunction mass independent of ordering |
| `finite_all_events_at_most_member` (theorem) | **Refactored:** direct event monotonicity plus extraction of a required member from standard forallb | finite_prob_event_monotone, Stdlib.List.forallb_forall | Same inequality without singleton/list-subset intermediate transformations |
| `finite_all_events_mass_at_most_union` (theorem) | Compose checked intersection/member and member/union inequalities | finite_all_events_at_most_member, arbitrary_union_contains_every_member, Rle_trans | **New:** unconditional intersection mass ≤ union mass under nonempty-family membership |
| `finite_conditional_all_events_mass_at_most_union` (theorem) | Compose existing conditional intersection/member and member/union inequalities | finite_conditional_all_events_at_most_member, finite_conditional_union_contains_member, Rle_trans | **New:** positive-conditioner intersection mass ≤ union mass |
| `all_events_pair` (lemma) | Reduce two-element forallb and use the true identity of Boolean conjunction | Stdlib.List.forallb, Stdlib.Bool.andb_true_r | **New:** shared exact two-event conjunction semantics |
| `any_event_pair` (lemma) | Two-member existsb disjunction via the standard Boolean false unit | Stdlib.List.existsb, Stdlib.Bool.orb_false_r | **New shared helper:** remove duplicated two-member disjunction unfolding |
| `finite_two_event_family_inclusion_exclusion` (theorem) | Transport two-event family conjunction via generic finite mass extensionality, then reuse established inclusion-exclusion | all_events_pair, finite_prob_event_ext_on_samples, two_event_union_inclusion_exclusion | **New:** event-family union plus intersection equals sum of marginals |
| `finite_conditional_two_event_family_inclusion_exclusion` (theorem) | Transport two-event family OR/AND via conditional target extensionality, then reuse generic conditional inclusion-exclusion | all_events_pair, finite_conditional_prob_event_ext_on_samples, finite_conditional_prob_inclusion_exclusion, Stdlib.Bool.orb_false_r | **New:** identical conditional inclusion-exclusion in list semantics |
| `finite_conditional_two_event_family_product` (theorem) | Transport two-event all_events conjunction to generic conditional factorization | finite_conditional_independent, all_events_pair, finite_conditional_prob_event_ext_on_samples | **New:** exact pairwise conditional product expressed in event-family notation |
| `finite_conditional_two_event_family_independent_union` (theorem) | Transport shared any_event_pair and apply the maintained independent union formula | finite_conditional_independent_union_formula, any_event_pair, finite_conditional_prob_event_ext_on_samples | **Refactored:** conditional union sum-minus-product without repeat existsb rewriting |
| `finite_conditional_prob_positive_of_positive_joint_support` (theorem) | Event witness positivity and standard positive quotient | finite_prob_positive_of_positive_support, Stdlib.Rdiv_lt_0_compat | **New:** positive conditional probability from explicit positive joint witness and denominator |
| `finite_conditional_prob_positive_of_joint_support_witness` (theorem) | Derived denominator positivity and preceding conditional result | finite_prob_positive_of_positive_support, finite_conditional_prob_positive_of_positive_joint_support | **New:** supported witness provides denominator and numerator positivity |
| `finite_prob_event_strict_monotone` (theorem) | Strict finite-sum monotonicity from one positively weighted event difference | FiniteSum.finite_sum_strict_monotone_at_member, indicator_implication_bound, Stdlib.Psatz.nra | **New:** strict event inclusion requires one enumerated positive-weight f-only witness |
| `finite_prob_filtered_mass_strict` (theorem) | Filter-to-conjunction rewriting and strict event monotonicity | finite_prob_on_filtered_samples, finite_prob_event_strict_monotone, Stdlib.Bool.andb_true_iff | **New:** discard positive-weight support implies strict filtered-mass reduction |
| `union_prob_filtered_mass_strict` (theorem) | Unfold union as existing event and reuse strict filtering | union_prob, finite_prob_filtered_mass_strict, Stdlib.List.existsb | **New:** identical strict reduction for any finite Boolean-event family |
| `finite_conditional_prob_strict_monotone` (theorem) | Strict numerator comparison and positive common inverse | finite_prob_event_strict_monotone, Stdlib.Bool.andb_true_iff, Stdlib.Rmult_lt_compat_r | **New:** strict inclusion among conditional event targets with an inside-conditioning witness |
| `finite_conditional_prob_strictly_between_zero_one_of_two_witnesses` (theorem) | Positivity of complementary conditioned masses and their sum-to-one identity | finite_conditional_prob_positive_of_joint_support_witness, finite_conditional_prob_complement, Stdlib.Lra | **New:** both conditioned target and conditioned complement supported implies interior mass |
| `union_prob_append_strict_of_fresh_support` (theorem) | Strict event inclusion through standard existsb append | finite_prob_event_strict_monotone, any_event_append, Stdlib.List.existsb_app | **New:** fresh positive-weight right-family witness strictly enlarges unconditional union |
| `finite_conditional_union_append_strict_of_fresh_support` (theorem) | Strict conditional event inclusion through standard existsb append | finite_conditional_prob_strict_monotone, any_event_append, Stdlib.List.existsb_app | **New:** fresh positive-weight right-family witness inside the conditioner strictly enlarges conditional union |
| `all_events_triple` (lemma) | Standard finite Boolean forallb and conjunction associativity | Stdlib.List.forallb, Stdlib.Bool.andb_true_r, Stdlib.Bool.andb_assoc | **New:** three-member conjunction helper with no custom Boolean recursion |
| `finite_conditional_three_event_family_product` (theorem) | **Refactored:** delegate to the pre-existing three-event factorization theorem after Boolean associativity | finite_conditional_three_event_product, finite_conditional_prob_event_ext_on_samples, all_events_triple, Stdlib.Bool.andb_assoc | Reuses one general factorizaton proof rather than repeating two factorization rewrites |
| `finite_conditional_prefix_independent_cons_positive` (theorem) | First chain conjunct projection | finite_conditional_prefix_independent, finite_conditional_independent | **New:** nonempty chain already entails strictly positive conditioning mass |
| `finite_conditional_nonempty_all_events_product` (theorem) | Existing general finite-list product, no duplicate induction | finite_conditional_all_events_product, finite_conditional_prefix_independent_cons_positive, Stdlib.List.map/fold_right | **New:** remove redundant explicitly supplied denominator premise for nonempty chain |
| `all_negated_events_eq_negated_any` (lemma) | List structural induction bridging standard forallb and existsb with Stdlib Boolean De Morgan | Stdlib.List.map/forallb/existsb, Stdlib.Bool.negb_orb | **New:** finite-family De Morgan without custom Boolean operators |
| `finite_union_complement_partition` (theorem) | Event complement extensionality followed by maintained finite-mass partition | all_negated_events_eq_negated_any, finite_prob_event_ext_on_samples, finite_prob_complement | **New:** finite union and universal-negation complement partition total signed weight |
| `finite_conditional_union_complement_partition` (theorem) | Conditional target transport and existing conditional complement identity | all_negated_events_eq_negated_any, finite_conditional_prob_event_ext_on_samples, finite_conditional_prob_complement | **New:** conditional union plus all-failures mass equals one under positive conditioner |
| `finite_conditional_union_complement_chain_product` (theorem) | **Refactored:** general complement-family product and reusable conditional partition, avoiding a second De Morgan transport | finite_conditional_all_events_product, finite_conditional_union_complement_partition, finite_conditional_prob_complement, Stdlib.List.map_map/map_ext_in, Stdlib.Lra | Arbitrary finite conditional union formula with explicit non-pairwise complement chain |
| `finite_conditional_nonempty_union_complement_chain_product` (theorem) | General union formula and first-guard positivity projection | finite_conditional_union_complement_chain_product, finite_conditional_prefix_independent_cons_positive | **New:** positivity is a consequence of the nonempty complement chain, not an extra premise |
| `union_prob_zero_iff_no_positive_support` (theorem) | Immediate union alias application of generic finite-event zero-support criterion | finite_prob_zero_iff_no_positive_mass_support | **New:** zero union iff no sampled positive-weight union support |
| `union_prob_zero_iff_each_member_zero` (theorem) | Support iff in both directions; existsb witness extraction and member inclusion | union_prob_zero_iff_no_positive_support, finite_prob_zero_iff_no_positive_mass_support, Stdlib.List.existsb_exists, event_member_implies_union | **New:** nonnegative union mass vanishes iff every member event mass vanishes |
| `union_prob_positive_of_positive_support` (theorem) | Immediate reuse of single-event positive witness criterion | finite_prob_positive_of_positive_support, any_event | **New:** positive-weight union support implies strictly positive union mass |
| `union_prob_positive_of_positive_member_support` (theorem) | Member-to-union witness then generic union positivity | event_member_implies_union, union_prob_positive_of_positive_support | **New:** any listed event with a positive-weight sampled witness makes union mass positive |
| `finite_conditional_prob_zero_iff_joint_zero` (theorem) | Zero-divisor real algebra with a strictly positive common reciprocal | Stdlib.Reals.Rmult_integral, Rinv_0_lt_compat, Stdlib.Lra, ring | **New:** conditional mass zero iff exact joint numerator zero |
| `finite_conditional_prob_zero_iff_no_positive_joint_support` (theorem) | Reuse generic joint zero and finite-event support iff | finite_conditional_prob_zero_iff_joint_zero, finite_prob_zero_iff_no_positive_mass_support, Stdlib.Bool.andb_true_iff | **New:** conditional mass zero iff no positive-weight sampled given-and-target witness |
| `finite_conditional_union_zero_iff_each_member_zero` (theorem) | Support iff in both directions using standard existsb witness | finite_conditional_prob_zero_iff_no_positive_joint_support, event_member_implies_union, Stdlib.List.existsb_exists | **New:** conditional union zero iff every member conditional mass zero, under common positive conditioner |
| `finite_all_events_zero_of_zero_member` (theorem) | Existing finite-event support iff plus standard forallb member extraction | finite_prob_zero_iff_no_positive_mass_support, Stdlib.List.forallb_forall | **New:** one zero-mass required member forces finite conjunction mass to zero |
| `finite_conditional_all_events_zero_of_zero_member` (theorem) | Existing conditional zero joint-support iff plus standard forallb member extraction | finite_conditional_prob_zero_iff_no_positive_joint_support, Stdlib.List.forallb_forall | **New:** one zero conditional mass required member forces conditional conjunction mass to zero |
| `finite_prob_positive_iff_positive_support` (theorem) | Generic positive finite-sum iff and weighted Boolean indicator simplification | FiniteSum.finite_sum_positive_iff_positive_member, indicator_nonnegative, Rmult_le_pos, nra | **New:** positive event mass iff a positive-weight accepted sample exists |
| `union_prob_positive_iff_positive_member_support` (theorem) | Event positive-support iff and standard list existential witness | finite_prob_positive_iff_positive_support, Stdlib.List.existsb_exists, event_member_implies_union | **New:** positive finite union iff some listed event accepts a positive-weight sample |
| `finite_conditional_prob_positive_iff_joint_support` (theorem) | Positive quotient implies nonzero joint mass; positive-event support iff; converse by existing joint witness theorem | finite_conditional_prob_zero_iff_joint_zero, finite_prob_positive_iff_positive_support, finite_prob_false, finite_prob_event_monotone, finite_conditional_prob_positive_of_positive_joint_support, Stdlib.Lra | **New:** positive finite conditional event iff a positive-weight joint support sample exists |
| `finite_conditional_union_positive_iff_positive_member_joint_support` (theorem) | Conditional support equivalence plus standard Boolean-list witness extraction | finite_conditional_prob_positive_iff_joint_support, Stdlib.List.existsb_exists, event_member_implies_union | **New:** strict conditional union iff a listed target admits a positive-weight jointly satisfying outcome |
| `finite_all_events_positive_implies_member_positive` (theorem) | Earlier finite intersection upper bound and real order | finite_all_events_at_most_member, Stdlib.Lra | **New:** positive conjunction mass implies positivity of each required marginal |
| `finite_conditional_all_events_positive_implies_member_positive` (theorem) | Earlier conditional intersection upper bound and real order | finite_conditional_all_events_at_most_member, Stdlib.Lra | **New:** conditional positive conjunction implies each required conditional marginal positive |











The preexisting `union_prob_membership_extensional` proof now uses the shared
`any_event_membership_ext` lemma instead of repeating both Boolean cases.

## FiniteMoments.v — 572 proof scripts

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
| `affine_dependent_pair_nontrivial_null_on_samples` (theorem) | Sample extensionality, fixed-basis variance identity, ring | variance_extensional_on_samples, variance_of_constant_score_zero, fixed_basis_weighted_variance_identity | **New:** sampled affine dependency produces a nonzero quadratic null witness |
| `duplicate_basis_nontrivial_null_direction` (theorem) | Lemma application, ring | affine_dependent_pair_nontrivial_null_on_samples | **Refactored:** duplicate-score special case of affine dependence |
| `expectation_extensional_on_positive_weight_support` (theorem) | Real-order case split, lemma application | FiniteSum.finite_sum_ext_in, Stdlib.Reals.Rle_lt_dec, Lra | **New:** ignore zero-mass score changes without signed-weight assumptions |
| `covariance_extensional_on_positive_weight_support` (theorem) | Rewriting, lemma application | expectation_extensional_on_positive_weight_support | **New:** covariance invariance under changes off positive support |
| `variance_extensional_on_positive_weight_support` (theorem) | Lemma application | covariance_extensional_on_positive_weight_support | **New:** variance invariance on positive support |
| `covariance_zero_of_constant_on_positive_weight_support_first` (theorem) | Support extensionality, lemma application | covariance_extensional_on_positive_weight_support, covariance_with_constant_first | **New:** constant positive-support first score yields zero covariance |
| `covariance_zero_of_constant_on_positive_weight_support_second` (theorem) | Symmetry, lemma application | covariance_symmetric, covariance_zero_of_constant_on_positive_weight_support_first | **New:** constant positive-support second score yields zero covariance |
| `variance_zero_of_constant_on_positive_weight_support` (theorem) | Definitional reduction, lemma application | covariance_zero_of_constant_on_positive_weight_support_first | **Refactored:** direct self-covariance specialization avoids duplicate expectation algebra |
| `variance_zero_iff_constant_on_positive_weight_support` (theorem) | Lemma application, iff split | zero_variance_is_constant_on_positive_mass, variance_zero_of_constant_on_positive_weight_support | **New:** zero variance iff constant score on positive-mass outcomes |
| `variance_zero_iff_exists_constant_on_positive_weight_support` (theorem) | Iff splitting, existential witness, lemma application | variance_zero_iff_constant_on_positive_weight_support, variance_zero_of_constant_on_positive_weight_support | **New:** zero variance iff a real constant exists on positive support |
| `variance_zero_iff_covariance_zero_with_every_score` (theorem) | Lemma application, definitional reduction | zero_variance_implies_zero_covariance_first, variance | **New:** zero variance iff zero covariance with every comparison score |
| `fixed_basis_null_iff_constant_on_positive_weight_support` (theorem) | Rewriting, lemma application | fixed_basis_weighted_variance_identity, variance_zero_iff_constant_on_positive_weight_support | **Refactored:** complete fixed-basis null iff delegates to generic variance equivalence |
| `fixed_basis_null_iff_orthogonal_to_every_score` (theorem) | Rewriting, lemma application | fixed_basis_weighted_variance_identity, variance_zero_iff_covariance_zero_with_every_score | **New:** fixed-basis null directions iff orthogonal to all finite scores |
| `variance_positive_iff_not_constant_on_positive_weight_support` (theorem) | Real-order case split, lemma application | variance_nonnegative, variance_zero_iff_constant_on_positive_weight_support, Stdlib.Reals.Rle_dec | **New:** strict finite variance iff not constant on positive-mass support |
| `variance_positive_iff_no_constant_on_positive_weight_support` (theorem) | Iff splitting, contradiction, lemma application | variance_zero_of_constant_on_positive_weight_support, variance_positive_iff_not_constant_on_positive_weight_support | **New:** strict variance iff no supported constant exists |
| `fixed_basis_positive_quadratic_iff_not_constant_on_positive_weight_support` (theorem) | Rewriting, lemma application | fixed_basis_weighted_variance_identity, variance_positive_iff_not_constant_on_positive_weight_support | **New:** fixed-basis strict curvature iff support nonconstancy |
| `positive_variance_of_positive_support_deviation` (theorem) | Lemma application, contradiction | variance_positive_iff_not_constant_on_positive_weight_support | **Refactored:** no repeated real-order case analysis |
| `positive_variance_of_two_distinct_positive_support_values` (theorem) | Lemma application, equality transitivity | variance_positive_iff_not_constant_on_positive_weight_support | **Refactored:** reusable strict-variance equivalence instead of case split |
| `positive_fixed_basis_quadratic_of_positive_support_deviation` (theorem) | Rewriting, lemma application | fixed_basis_weighted_variance_identity, positive_variance_of_positive_support_deviation | **New:** positive deviation witnesses strict quadratic curvature |
| `positive_fixed_basis_quadratic_of_two_distinct_support_values` (theorem) | Rewriting, lemma application | fixed_basis_weighted_variance_identity, positive_variance_of_two_distinct_positive_support_values | **New:** two positive outcomes witness a strictly positive quadratic form |
| `fixed_basis_positive_definite_iff_no_nonzero_constant_direction` (theorem) | Iff splitting, contradiction, lemma application | Stdlib.List.repeat, fixed_basis_null_iff_constant_on_positive_weight_support, fixed_basis_positive_quadratic_iff_not_constant_on_positive_weight_support | **New:** positive definiteness iff no nontrivial constant-score direction |
| `fixed_basis_positive_definite_of_separating_positive_support_pairs` (theorem) | Existential witness elimination, lemma application | positive_fixed_basis_quadratic_of_two_distinct_support_values, Stdlib.List.repeat | **New:** positive-weight pair-separation suffices for matrix positive definiteness |
| `fixed_basis_positive_definite_of_positive_support_mean_deviations` (theorem) | Existential witness elimination, lemma application | positive_fixed_basis_quadratic_of_positive_support_deviation, Stdlib.List.repeat | **New:** every nonzero direction has mean-deviation witness implies positive definiteness |
| `fixed_basis_positive_definite_iff_no_nonzero_orthogonal_direction` (theorem) | Iff splitting, contradiction, lemma application | fixed_basis_null_iff_orthogonal_to_every_score, fixed_basis_null_iff_constant_on_positive_weight_support, fixed_basis_positive_quadratic_iff_not_constant_on_positive_weight_support, Stdlib.Lra | **New:** positive definiteness iff no nonzero direction is orthogonal to every finite score |
| `fixed_basis_null_iff_exists_constant_on_positive_weight_support` (theorem) | Rewriting, lemma application | fixed_basis_weighted_variance_identity, variance_zero_iff_exists_constant_on_positive_weight_support | **New:** matrix nullity iff composite score equals some real support constant |
| `fixed_basis_positive_quadratic_iff_no_constant_on_positive_weight_support` (theorem) | Rewriting, lemma application | fixed_basis_weighted_variance_identity, variance_positive_iff_no_constant_on_positive_weight_support | **New:** strictly positive matrix curvature iff no supported constant exists |
| `fixed_basis_not_positive_definite_of_nonzero_null_direction` (theorem) | Witness instantiation and Lra | Stdlib.List.repeat and Lra | **New:** arbitrary nonzero quadratic null witness rules out strict positive definiteness even for signed weights |
| `fixed_basis_not_positive_definite_of_nonzero_constant_support_direction` (theorem) | Lemma application, existential constant | fixed_basis_null_iff_exists_constant_on_positive_weight_support, fixed_basis_not_positive_definite_of_nonzero_null_direction | **New:** any nontrivial positive-support-constant composite direction obstructs positive definiteness |
| `duplicate_basis_covariance_not_positive_definite` (theorem) | Witness simplification and lemma application | duplicate_basis_nontrivial_null_direction, fixed_basis_not_positive_definite_of_nonzero_null_direction, Stdlib.List.repeat | **Refactored:** delegate general strict-positivity contradiction to a shared null-witness lemma |
| `basis_cross_covariance_matrix_affine` (theorem) | Map fusion, extensionality, lemma reuse | Stdlib.List.map_map, Stdlib.List.map_ext, covariance_of_affine_scores | **New:** cross-covariance of affine-transformed bases scales entrywise by the product of slopes |
| `basis_covariance_matrix_affine` (theorem) | Definitional bridge, lemma reuse | basis_cross_covariance_matrix_affine, existing basis covariance definitions | **New:** fixed-basis covariance scales by the square of a common affine slope |
| `affine_dependent_pair_nontrivial_null_on_positive_support` (theorem) | Support constant witness, ring, Lra | fixed_basis_null_iff_exists_constant_on_positive_weight_support, FiniteSum.finite_sum, Stdlib.List.combine | **New:** affine dependency on positive support provides nonzero null direction |
| `affine_dependent_pair_covariance_not_positive_definite` (theorem) | Witness simplification and lemma application | affine_dependent_pair_nontrivial_null_on_positive_support, fixed_basis_not_positive_definite_of_nonzero_null_direction, Stdlib.List.repeat | **Refactored:** use the common nonzero quadratic-null obstruction |
| `fixed_basis_null_iff_uncorrelated_with_basis` (theorem) | Existing covariance linear-combination identity, finite-sum extensionality, null iff | covariance_of_general_weighted_second_unconditional, basis_of_combine, FiniteSum.finite_sum_ext_in, FiniteSum.finite_sum_zero, Stdlib.List.in_map | **New:** quadratic null iff composite score uncorrelated with every basis element |
| `fixed_basis_positive_quadratic_iff_not_uncorrelated_with_basis` (theorem) | Real order cases, null iff, positive semidefiniteness | fixed_basis_covariance_matrix_positive_semidefinite, fixed_basis_null_iff_uncorrelated_with_basis, Stdlib.Reals.Rle_dec and Lra | **New:** strict quadratic positivity iff not orthogonal to the finite basis |
| `fixed_basis_positive_definite_iff_no_nonzero_basis_orthogonal_direction` (theorem) | Iff projection, lemma application | fixed_basis_positive_quadratic_iff_not_uncorrelated_with_basis, Stdlib.List.repeat | **New:** positive definite iff no nonzero vector is covariance-orthogonal to the finite basis |
| `covariance_with_weighted_basis_as_row_dot` (theorem) | Weighted covariance row rewriting, Stdlib list-map fusion | covariance_of_general_weighted_second_unconditional, covariance_row_as_vector_dot, coefficients_of_combine, basis_of_combine, Stdlib.List.map_map | **New:** covariance with a composite score equals a coefficient-dot-covariance-row |
| `fixed_basis_null_iff_zero_dot_with_every_covariance_row` (theorem) | Iff projection, Stdlib.List.in_map_iff, covariance symmetry | fixed_basis_null_iff_uncorrelated_with_basis, covariance_with_weighted_basis_as_row_dot, Stdlib.List.in_map_iff | **New:** zero covariance quadratic iff every actual matrix row is orthogonal to coefficients |
| `fixed_basis_positive_quadratic_iff_nonzero_covariance_row_dot` (theorem) | Iff splitting, real-order comparison, Lra | fixed_basis_covariance_matrix_positive_semidefinite, fixed_basis_null_iff_zero_dot_with_every_covariance_row, Stdlib.Rle_dec | **New:** strictly positive covariance quadratic iff not orthogonal to every row |
| `fixed_basis_positive_definite_iff_no_nonzero_covariance_row_kernel` (theorem) | Iff projection, lemma application | fixed_basis_positive_quadratic_iff_nonzero_covariance_row_dot, Stdlib.List.repeat | **New:** covariance positive definiteness iff row-dot kernel contains no nonzero compatible list |
| `fixed_basis_constant_support_implies_zero_covariance_row_dots` (theorem) | Lemma application, support-constant witness | fixed_basis_null_iff_exists_constant_on_positive_weight_support, fixed_basis_null_iff_zero_dot_with_every_covariance_row | **New:** a supported constant composite score yields zero dot product with every matrix row |
| `fixed_basis_not_positive_definite_of_nonzero_covariance_row_kernel` (theorem) | Lemma application, nullity iff | fixed_basis_null_iff_zero_dot_with_every_covariance_row, fixed_basis_not_positive_definite_of_nonzero_null_direction | **New:** a nonzero row-dot kernel vector disproves covariance positive definiteness |
| `fixed_basis_zero_covariance_row_dots_iff_supported_constant` (theorem) | Iff composition, lemma application | fixed_basis_null_iff_zero_dot_with_every_covariance_row, fixed_basis_null_iff_exists_constant_on_positive_weight_support | **New:** zero dot against every covariance row iff composite score equals some positive-support constant |
| `fixed_basis_positive_definite_iff_no_nonzero_supported_constant` (theorem) | Iff projection, lemma application | fixed_basis_positive_quadratic_iff_no_constant_on_positive_weight_support, Stdlib.List.repeat | **New:** covariance positive definite iff no nonzero coefficient direction yields any supported constant |
| `basis_covariance_matrix_as_cross` (theorem) | Transparent equal-basis specialization of existing rectangular matrix definition | basis_covariance_matrix, basis_cross_covariance_matrix, Stdlib.List.map | **New:** square covariance list is equal-left-right cross covariance list |
| `basis_cross_covariance_matrix_app_left` (theorem) | Stdlib map_app on score row lists | Stdlib.List.map_app, basis_cross_covariance_matrix | **New:** row-basis append law for rectangular covariance list |
| `basis_cross_covariance_matrix_app_right` (theorem) | List induction and map_app for each pair of covariance rows | Stdlib.List.map_app, combine, basis_cross_covariance_matrix | **New:** column-basis append corresponds to elementwise row concatenation |
| `basis_cross_covariance_matrix_nth_error_entry` (theorem) | Two Stdlib nth_error_map rewrites and option inversion | Stdlib.List.nth_error_map, basis_cross_covariance_matrix, covariance | **New:** indexed covariance list cell equals selected scalar covariance with explicit bounds |
| `basis_cross_covariance_matrix_nth_error_swap` (theorem) | Two certified entry rewrites and covariance_symmetric | basis_cross_covariance_matrix_nth_error_entry, covariance_symmetric | **New:** left/right covariance matrices obey componentwise transpose symmetry |
| `basis_cross_covariance_matrix_nth_error_row` (theorem) | Stdlib nth_error_map applies successful source basis index to mapped covariance row | Stdlib.List.nth_error_map, basis_cross_covariance_matrix | **New:** selected matrix row corresponds exactly to selected left-side basis score |
| `basis_cross_covariance_matrix_nth_error_row_length` (theorem) | Indexed row substitution then Stdlib length_map | basis_cross_covariance_matrix_nth_error_row, Stdlib.List.length_map | **New:** every successfully selected rectangular covariance row has the right column count |
| `basis_covariance_matrix_nth_error_entry` (theorem) | Square specialization of existing rectangular entry invariant | basis_covariance_matrix_as_cross, basis_cross_covariance_matrix_nth_error_entry | **New:** square covariance list entry equals covariance of selected score pair |
| `basis_covariance_matrix_nth_error_symmetric` (theorem) | Square specialization of checked rectangular swap entry theorem | basis_covariance_matrix_as_cross, basis_cross_covariance_matrix_nth_error_swap | **New:** covariance square matrix has symmetric indexed entries |
| `vector_of_list_nth_error` (theorem) | Reuse VectorSpec.to_list_nth_order, Fin.of_nat_to_nat_inv and nth_error_nth' | Stdlib.Vectors.VectorSpec, Stdlib.Vectors.Fin, Stdlib.List | **New:** bounded vector index agrees with option-valued list access after of_list |
| `indexed_basis_cross_covariance_matrix_entry` (theorem) | Compose source entry certification and Stdlib list/vector selected score equality | basis_cross_covariance_matrix_nth_error_entry, vector_of_list_nth_error | **New:** dimension-indexed covariance entry exactly equals existing list-matrix cell |
| `indexed_basis_cross_covariance_matrix_swap` (theorem) | Scalar covariance symmetry in type-indexed representation | indexed_basis_cross_covariance_matrix, covariance_symmetric, Stdlib.Vectors.Fin | **New:** dimension-safe rectangular covariance transpose identity |
| `indexed_basis_cross_covariance_matrix_row` (theorem) | Use certified vector/list nth equality then existing row theorem | vector_of_list_nth_error, basis_cross_covariance_matrix_nth_error_row | **New:** every bounded row of the dimension-indexed model exists in the old list matrix |
| `indexed_basis_cross_covariance_matrix_row_length` (theorem) | Reuse established row length lemma with Fin-to-list index bridge | basis_cross_covariance_matrix_nth_error_row_length, vector_of_list_nth_error | **New:** bounded indexed rows retain exact right-basis column dimensions |
| `indexed_basis_cross_covariance_matrix_entry_total` (theorem) | Reuse certified total bounded row theorem and existing cell bridge | indexed_basis_cross_covariance_matrix_row, indexed_basis_cross_covariance_matrix_entry | **New:** every bounded row and column index is successfully realized by the list covariance matrix |
| `indexed_basis_covariance_matrix_symmetric` (theorem) | Equal-basis specialization of dimension-indexed rectangular covariance swap | indexed_basis_cross_covariance_matrix_swap, Stdlib.Vectors.Fin | **New:** total symmetry of the square dimension-indexed covariance representation |
| `indexed_basis_covariance_matrix_diagonal` (theorem) | Definitional reduction of variance to self-covariance | variance, covariance, Stdlib.Vectors.Vector.nth | **New:** each total bounded diagonal cell equals the selected score variance |
| `indexed_basis_covariance_matrix_diagonal_nonnegative` (theorem) | Rewrite diagonal entry to variance, then apply established variance_nonnegative | indexed_basis_covariance_matrix_diagonal, variance_nonnegative | **New:** normalized nonnegative finite weights imply nonnegative indexed covariance diagonal |
| `indexed_basis_cross_covariance_cauchy_schwarz_squared` (theorem) | Specialize scalar finite Cauchy-Schwarz to dimension-indexed rectangular entries | finite_covariance_cauchy_schwarz_squared, Stdlib.Vectors.Fin | **New:** squared rectangular indexed covariance is bounded by selected score variances |
| `indexed_basis_cross_covariance_nonzero_implies_positive_variances` (theorem) | Specialize scalar nonzero-covariance theorem to rectangular indexed cells | nonzero_covariance_implies_positive_variances, Stdlib.Vectors.Vector.nth | **New:** nonzero rectangular covariance forces both variances strictly positive |
| `indexed_basis_cross_covariance_nonzero_implies_nonconstant_scores` (theorem) | Use rectangular positive variances and scalar nonconstant-on-support iff | indexed_basis_cross_covariance_nonzero_implies_positive_variances, variance_positive_iff_no_constant_on_positive_weight_support | **New:** nonzero rectangular covariance requires both scores vary on positive-weight support |
| `indexed_basis_covariance_matrix_cauchy_schwarz_squared` (theorem) | Rewrite diagonal cells as variances and specialize rectangular Cauchy-Schwarz | indexed_basis_covariance_matrix_diagonal, indexed_basis_cross_covariance_cauchy_schwarz_squared | **New:** squared indexed matrix entries are bounded by the product of diagonal cells |
| `indexed_basis_covariance_matrix_diagonal_zero_iff_constant_on_support` (theorem) | Rewrite diagonal entry to variance and apply existing supported-constant iff theorem | indexed_basis_covariance_matrix_diagonal, variance_zero_iff_exists_constant_on_positive_weight_support | **New:** zero indexed diagonal exactly characterizes a constant score on positive-weight support |
| `indexed_basis_cross_covariance_zero_variance_row` (theorem) | Specialize existing scalar null-covariance theorem in rectangular indexed entry | zero_variance_implies_zero_covariance_first, indexed_basis_cross_covariance_matrix | **New:** zero-variance left score annihilates any rectangular covariance row |
| `indexed_basis_cross_covariance_zero_variance_column` (theorem) | Apply rectangular swap and established zero-variance row rule | indexed_basis_cross_covariance_matrix_swap, indexed_basis_cross_covariance_zero_variance_row | **New:** zero-variance right score annihilates any rectangular covariance column |
| `indexed_basis_covariance_matrix_zero_diagonal_implies_zero_row` (theorem) | Rewrite zero diagonal to variance and use rectangular zero-variance row lemma | indexed_basis_covariance_matrix_diagonal, indexed_basis_cross_covariance_zero_variance_row | **New:** zero indexed diagonal forces every cell of that covariance row to vanish |
| `indexed_basis_covariance_matrix_zero_diagonal_implies_zero_column` (theorem) | Rewrite diagonal variance and apply rectangular zero-variance column lemma | indexed_basis_covariance_matrix_diagonal, indexed_basis_cross_covariance_zero_variance_column | **New:** zero indexed diagonal forces all covariance column cells to vanish |
| `indexed_basis_covariance_matrix_zero_row_iff_zero_diagonal` (theorem) | Diagonal specialization and established zero-diagonal-to-zero-row lemma | indexed_basis_covariance_matrix_zero_diagonal_implies_zero_row | **New:** a zero diagonal exactly characterizes a zero indexed row |
| `indexed_basis_covariance_matrix_zero_column_iff_zero_diagonal` (theorem) | Diagonal specialization and established zero-diagonal-to-zero-column lemma | indexed_basis_covariance_matrix_zero_diagonal_implies_zero_column | **New:** a zero diagonal exactly characterizes a zero indexed column |
| `indexed_basis_covariance_matrix_principal_minor_nonnegative` (theorem) | Indexed symmetry and previously proved Cauchy-Schwarz bound, then Lra | indexed_basis_covariance_matrix_symmetric, indexed_basis_covariance_matrix_cauchy_schwarz_squared, Stdlib.Lra | **New:** every two-coordinate principal covariance minor is nonnegative |
| `indexed_basis_covariance_matrix_zero_row_iff_zero_column` (theorem) | Rewrite indexed covariance symmetric cells in both directions | indexed_basis_covariance_matrix_symmetric, Stdlib.Vectors.Fin | **New:** indexed zero rows and columns are equivalent without weight assumptions |
| `indexed_basis_covariance_matrix_zero_row_iff_constant_on_support` (theorem) | Compose zero-row iff zero-diagonal and support constancy iff via tauto | indexed_basis_covariance_matrix_zero_row_iff_zero_diagonal, indexed_basis_covariance_matrix_diagonal_zero_iff_constant_on_support | **New:** a zero row exactly identifies constant positive-support score |
| `indexed_basis_covariance_matrix_zero_column_iff_constant_on_support` (theorem) | Compose unconditional row/column equivalence with support criterion via tauto | indexed_basis_covariance_matrix_zero_row_iff_zero_column, indexed_basis_covariance_matrix_zero_row_iff_constant_on_support | **New:** a zero column exactly identifies constant positive-support score |
| `indexed_basis_covariance_matrix_positive_diagonal_iff_nonconstant_on_support` (theorem) | Rewrite indexed diagonal to scalar variance, apply existing strict positivity iff | indexed_basis_covariance_matrix_diagonal, variance_positive_iff_no_constant_on_positive_weight_support | **New:** positive indexed variance iff selected score is nonconstant on positive-weight support |
| `indexed_basis_covariance_matrix_nonzero_entry_implies_positive_diagonals` (theorem) | Reduce to scalar covariance and apply already verified nonzero-covariance variance theorem | indexed_basis_covariance_matrix_diagonal, nonzero_covariance_implies_positive_variances | **New:** nonzero indexed covariance requires both diagonals strictly positive |
| `indexed_basis_covariance_matrix_nonzero_entry_implies_nonconstant_scores` (theorem) | Two positive diagonal results and existing strict support-nonconstancy equivalence | indexed_basis_covariance_matrix_nonzero_entry_implies_positive_diagonals, indexed_basis_covariance_matrix_positive_diagonal_iff_nonconstant_on_support | **New:** nonzero covariance requires both selected scores to vary on positive-weight support |
| `indexed_basis_covariance_two_coordinate_form_as_variance` (theorem) | Apply scalar two-weighted-score variance formula, unfold indexed entries | variance_of_two_weighted_scores, Stdlib.Vectors.Vector.nth | **New:** Two-coordinate covariance quadratic equals pair-score variance |
| `indexed_basis_covariance_two_coordinate_form_as_list_matrix` (theorem) | Variance extensionality and the existing unconditional finite matrix quadratic identity | indexed_basis_covariance_two_coordinate_form_as_variance, variance_extensional, covariance_matrix_quadratic_form_is_variance_unconditional, Stdlib.List | **New:** bridge indexed two-coordinate covariance form to existing list-based matrix quadratic |
| `indexed_basis_covariance_two_coordinate_form_nonnegative` (theorem) | Rewrite indexed form through checked list-matrix bridge and specialize general fixed-basis PSD | indexed_basis_covariance_two_coordinate_form_as_list_matrix, fixed_basis_covariance_matrix_positive_semidefinite | **Refactored:** reuse maintained general covariance PSD theorem rather than repeating variance nonnegativity |
| `indexed_basis_covariance_two_coordinate_form_zero_iff_constant_on_support` (theorem) | Reduce via pair variance then apply positive-weight support zero-variance characterization | indexed_basis_covariance_two_coordinate_form_as_variance, variance_zero_iff_exists_constant_on_positive_weight_support | **New:** Form nullity iff a supported-constant pair score |
| `indexed_basis_covariance_two_coordinate_form_positive_iff_nonconstant_on_support` (theorem) | Reduce via pair variance then apply strict-variance support iff | indexed_basis_covariance_two_coordinate_form_as_variance, variance_positive_iff_no_constant_on_positive_weight_support | **New:** Positive two-coordinate form iff the pair score varies on support |
| `indexed_basis_covariance_quadratic_as_variance` (theorem) | Apply existing fixed-basis variance identity using Stdlib vector-to-list length | fixed_basis_weighted_variance_identity, VectorSpec.length_to_list | **New:** General dimension-checked covariance quadratic equals composite-score variance under unit mass |
| `indexed_basis_covariance_quadratic_nonnegative` (theorem) | Specialize generic fixed-basis PSD using VectorSpec.length_to_list | fixed_basis_covariance_matrix_positive_semidefinite, VectorSpec.length_to_list | **New:** All dimension-safe coefficient directions have nonnegative finite covariance quadratic |
| `indexed_basis_covariance_quadratic_zero_iff_constant_on_support` (theorem) | Specialize existing positive-support nullity iff using Stdlib vector length | fixed_basis_null_iff_exists_constant_on_positive_weight_support, VectorSpec.length_to_list | **New:** General bounded coefficient nullity iff finite positive-support constancy |
| `indexed_basis_covariance_quadratic_positive_iff_nonconstant_on_support` (theorem) | Apply fixed-basis strict-positivity iff with length_to_list | fixed_basis_positive_quadratic_iff_no_constant_on_positive_weight_support, VectorSpec.length_to_list | **New:** Strictly positive vector-indexed quadratic iff the weighted basis score varies on support |
| `indexed_basis_covariance_quadratic_zero_iff_uncorrelated_with_basis` (theorem) | Apply general zero-covariance basis orthogonality iff with standard vector length | fixed_basis_null_iff_uncorrelated_with_basis, VectorSpec.length_to_list | **New:** Dimension-safe covariance nullity iff uncorrelated with every basis score |
| `indexed_basis_covariance_quadratic_zero_iff_zero_matrix_row_dots` (theorem) | Delegate to general list covariance row kernel iff and stdlib length | fixed_basis_null_iff_zero_dot_with_every_covariance_row, VectorSpec.length_to_list | **New:** All-dimensional coefficient-vector nullity iff zero dot with every covariance row |
| `indexed_basis_covariance_quadratic_zero_iff_uncorrelated_with_every_score` (theorem) | Specialize existing all-scores nullity iff with standard vector length theorem | fixed_basis_null_iff_orthogonal_to_every_score, VectorSpec.length_to_list | **New:** Indexed quadratic zero iff composite score has zero covariance with every comparison score |
| `indexed_basis_covariance_quadratic_positive_iff_not_uncorrelated_with_basis` (theorem) | Specialize existing positive-quadratic iff basis covariance nonorthogonality | fixed_basis_positive_quadratic_iff_not_uncorrelated_with_basis, VectorSpec.length_to_list | **New:** Bounded coefficient quadratic positive iff composite score is not orthogonal to every basis score |
| `indexed_basis_covariance_quadratic_positive_iff_nonzero_matrix_row_dot` (theorem) | Reuse general list PSD strict-positive iff nonzero covariance row dot | fixed_basis_positive_quadratic_iff_nonzero_covariance_row_dot, VectorSpec.length_to_list | **New:** Strictly positive dimension-safe quadratic iff not all covariance row products vanish |
| `indexed_basis_covariance_quadratic_zero_matrix_row_dots_iff_constant_on_support` (theorem) | Use existing row-dot/support-constancy iff and the standard vector-to-list length | fixed_basis_zero_covariance_row_dots_iff_supported_constant, VectorSpec.length_to_list | **New:** Zero row dot products iff the weighted composite score is constant on positive sample support |
| `indexed_basis_covariance_quadratic_nonzero_covariance_implies_positive` (theorem) | Nonzero scalar covariance gives positive composite variance; rewrite indexed quadratic | nonzero_covariance_implies_positive_variances, indexed_basis_covariance_quadratic_as_variance | **New:** A nonzero covariance witness with any score certifies a strictly positive indexed quadratic |
| `indexed_basis_covariance_two_coordinate_form_swap` (theorem) | Unfold two-coordinate form; apply indexed covariance symmetry and ring | indexed_basis_covariance_matrix_symmetric, Stdlib.Reals.ring | **New:** Two-score coefficient and index exchange preserves the covariance quadratic |
| `indexed_basis_covariance_two_coordinate_form_homogeneous` (theorem) | Unfold existing quadratic polynomial and normalize by Stdlib ring | indexed_basis_covariance_two_coordinate_form, Stdlib.Reals.ring | **New:** Two-coordinate covariance form scales quadratically with common coefficient multiplier |
| `indexed_basis_covariance_quadratic_zero_implies_bounded_row_dot_zero` (theorem) | List row nullity followed by bounded row realization and Stdlib nth_error_In | indexed_basis_covariance_quadratic_zero_iff_zero_matrix_row_dots, indexed_basis_cross_covariance_matrix_row, basis_covariance_matrix_as_cross, Stdlib.List.nth_error_In | **New:** Zero quadratic annihilates every total bounded covariance row dot product |
| `indexed_basis_covariance_quadratic_zero_implies_uncorrelated_indexed_score` (theorem) | Specialize stronger all-scores orthogonality to selected Fin.t basis score | indexed_basis_covariance_quadratic_zero_iff_uncorrelated_with_every_score, Stdlib.Vectors.Vector.nth | **New:** Zero arbitrary-dimensional coefficient quadratic implies zero covariance with each indexed basis score |
| `indexed_basis_covariance_quadratic_nonzero_indexed_covariance_implies_positive` (theorem) | Apply general nonzero covariance witness theorem to selected bounded basis score | indexed_basis_covariance_quadratic_nonzero_covariance_implies_positive, Stdlib.Vectors.Vector.nth | **New:** Nonzero covariance with any indexed score certifies positive coefficient-vector quadratic |
| `indexed_basis_covariance_matrix_row_has_bounded_index` (theorem) | Recover list row position via In_nth_error, bound with nth_error_Some, reify Fin.of_nat_lt and use indexed row theorem | Stdlib.List.In_nth_error, nth_error_Some, length_map, Fin.of_nat_lt, Fin.to_nat_of_nat, indexed_basis_cross_covariance_matrix_row | **New:** Every list covariance row is exactly a Fin.t-indexed covariance row |
| `indexed_basis_covariance_quadratic_zero_iff_bounded_row_dots_zero` (theorem) | Compose existing forward bounded-row nullity and new list-row-to-Fin index coverage for converse | indexed_basis_covariance_quadratic_zero_implies_bounded_row_dot_zero, indexed_basis_covariance_quadratic_zero_iff_zero_matrix_row_dots, indexed_basis_covariance_matrix_row_has_bounded_index | **New:** Zero covariance quadratic iff all Fin.t-bounded covariance row dot products vanish |
| `indexed_basis_covariance_quadratic_positive_iff_nonzero_bounded_row_dot` (theorem) | Compose positive/list-row iff and nullity/list-row/indexed-row iff using tauto | indexed_basis_covariance_quadratic_positive_iff_nonzero_matrix_row_dot, indexed_basis_covariance_quadratic_zero_iff_zero_matrix_row_dots, indexed_basis_covariance_quadratic_zero_iff_bounded_row_dots_zero | **New:** Positive indexed covariance quadratic iff not all bounded covariance row dots vanish |
| `indexed_basis_covariance_bounded_row_dots_zero_iff_constant_on_support` (theorem) | Propositional composition of bounded-row zero iff quadratic zero iff supported constancy | indexed_basis_covariance_quadratic_zero_iff_bounded_row_dots_zero, indexed_basis_covariance_quadratic_zero_iff_constant_on_support | **New:** All bounded row dot products vanish iff the weighted score is supported-constant |
| `indexed_basis_covariance_bounded_row_dots_zero_iff_uncorrelated_with_every_score` (theorem) | Propositional composition of bounded-row nullity and universal score orthogonality | indexed_basis_covariance_quadratic_zero_iff_bounded_row_dots_zero, indexed_basis_covariance_quadratic_zero_iff_uncorrelated_with_every_score | **New:** All bounded covariance row dots vanish iff the composite score is orthogonal to every score |
| `indexed_basis_covariance_positive_definite_iff_no_nonzero_supported_constant` (theorem) | Pointwise bidirectional application of existing positive quadratic/support nonconstancy iff | indexed_basis_covariance_quadratic_positive_iff_nonconstant_on_support, indexed_basis_covariance_positive_definite | **New:** Indexed positive definiteness iff no nonzero coefficient vector yields a positive-support constant score |
| `indexed_basis_covariance_positive_definite_iff_no_nonzero_bounded_row_kernel` (theorem) | Pointwise composition of typed positive definiteness and positive iff not bounded row nullity | indexed_basis_covariance_positive_definite, indexed_basis_covariance_quadratic_positive_iff_nonzero_bounded_row_dot | **New:** Indexed positive definiteness iff no nonzero bounded coefficient vector is in the covariance row kernel |
| `indexed_basis_covariance_positive_definite_iff_positive_composite_variances` (theorem) | Rewrite arbitrary typed quadratic as existing finite composite-score variance in both directions | indexed_basis_covariance_quadratic_as_variance, indexed_basis_covariance_positive_definite | **New:** Positive definiteness iff every nonzero bounded coefficient direction has strictly positive composite-score variance |
| `indexed_basis_covariance_positive_definite_iff_no_nonzero_basis_orthogonal_direction` (theorem) | Pointwise specialize indexed quadratic strict positivity iff nonorthogonality to basis scores | indexed_basis_covariance_quadratic_positive_iff_not_uncorrelated_with_basis, indexed_basis_covariance_positive_definite | **New:** Positive definiteness iff no nonzero coefficient direction is uncorrelated with its entire basis |
| `indexed_basis_covariance_positive_definite_iff_no_nonzero_zero_quadratic` (theorem) | Combine existing indexed PSD and absence of quadratic zeros using standard lra | indexed_basis_covariance_quadratic_nonnegative, Stdlib.Lra | **New:** Positive definiteness iff a PSD covariance quadratic has no nonzero null direction |
| `indexed_basis_covariance_quadratic_positive_of_distinct_support_values` (theorem) | Positive-support separation contradicts support constancy through existing positive-quadratic iff | indexed_basis_covariance_quadratic_positive_iff_nonconstant_on_support, weighted_basis_sum | **New:** Distinct composite scores on two positive-weight outcomes certify a strictly positive typed covariance quadratic |
| `indexed_basis_covariance_positive_definite_of_separating_support_pairs` (theorem) | Apply the pairwise positive-support witness theorem pointwise to every nonzero typed coefficient vector | indexed_basis_covariance_quadratic_positive_of_distinct_support_values, indexed_basis_covariance_positive_definite | **New:** Pointwise positive-support sample separation of all nonzero typed composite directions implies positive definiteness |
| `indexed_basis_covariance_quadratic_positive_of_nonzero_bounded_row_dot` (theorem) | Refute the universal bounded covariance-row nullity using one explicitly nonzero row dot witness | indexed_basis_covariance_quadratic_positive_iff_nonzero_bounded_row_dot, Stdlib.Vectors.Fin | **New:** A single nonzero typed covariance row dot product certifies strict positivity of the composite quadratic |
| `indexed_basis_covariance_not_positive_definite_of_nonzero_bounded_row_kernel` (theorem) | Directly contradict the checked positive-definite no-nonzero-bounded-row-kernel criterion | indexed_basis_covariance_positive_definite_iff_no_nonzero_bounded_row_kernel, Stdlib.Vectors.Fin | **New:** An explicit nonzero coefficient vector in every bounded covariance row kernel refutes positive definiteness |
| `indexed_basis_covariance_quadratic_zero_implies_equal_positive_support_scores` (theorem) | Delegate pairwise nullity to existing finite list quadratic theorem and stdlib vector length | null_covariance_direction_pairwise_constant_on_positive_mass, VectorSpec.length_to_list | **New:** A zero vector-typed covariance quadratic forces identical composite scores on all positive-weight sample pairs |
| `indexed_basis_covariance_quadratic_zero_iff_constant_at_positive_support_anchor` (theorem) | Compose pairwise nullity and support-constant iff using the explicit anchor score | indexed_basis_covariance_quadratic_zero_implies_equal_positive_support_scores, indexed_basis_covariance_quadratic_zero_iff_constant_on_support | **New:** Zero typed covariance quadratic iff every positive-weight score equals any chosen positive-weight anchor score |
| `indexed_basis_covariance_not_positive_definite_of_nonzero_supported_constant` (theorem) | Contradict existing indexed positive definiteness iff no supported-constant nonzero direction | indexed_basis_covariance_positive_definite_iff_no_nonzero_supported_constant | **New:** Any nonzero coefficient vector constant on positive-weight support proves the typed covariance matrix is not positive definite |
| `indexed_basis_covariance_not_positive_definite_of_nonzero_zero_quadratic` (theorem) | Use existing positive-definite iff no nonzero quadratic zeros to refute positive definiteness | indexed_basis_covariance_positive_definite_iff_no_nonzero_zero_quadratic | **New:** An explicit nonzero zero-quadratic coefficient vector refutes typed covariance positive definiteness |
| `variance_positive_iff_exists_positive_weight_deviation` (theorem) | Generic constructive positive finite-sum witness applied to weighted squared deviations | centered_second_moment_identity, FiniteSum.finite_sum_positive_iff_positive_member, Stdlib.Reals.Rle_0_sqr/Rmult_lt_0_compat, Lra/Psatz | **New:** strictly positive variance iff a listed positive-weight sample deviates from its expectation |
| `indexed_basis_covariance_quadratic_positive_iff_supported_deviation` (theorem) | Transfer generic positive variance witness through an existing typed quadratic/variance equality | indexed_basis_covariance_quadratic_as_variance, variance_positive_iff_exists_positive_weight_deviation, Stdlib.Vector.to_list | **New:** positive typed covariance quadratic iff a listed positive-weight composite score deviates from its mean |
| `indexed_basis_covariance_positive_definite_iff_all_nonzero_supported_deviations` (theorem) | Pointwise lifting of constructive positive quadratic iff to every nonzero typed vector | indexed_basis_covariance_quadratic_positive_iff_supported_deviation, indexed_basis_covariance_positive_definite, Stdlib.Vector.to_list, Stdlib.List.repeat | **New:** positive definiteness iff every nonzero direction has a real enumerated positive-weight deviation witness |
| `indexed_basis_covariance_quadratic_zero_iff_centered_weighted_score_zero` (theorem) | Reuse indexed quadratic=variance and generic zero-variance support iff; standard real zero-product split | indexed_basis_covariance_quadratic_as_variance, variance_zero_iff_constant_on_positive_weight_support, Rle_lt_dec, Rmult_integral | **New:** covariance quadratic zero iff each observed weighted centered composite score is zero |
| `indexed_basis_covariance_bounded_row_kernel_iff_centered_weighted_score_zero` (theorem) | Compose two previously checked indexed covariance quadratic-nullity iff results | indexed_basis_covariance_quadratic_zero_iff_bounded_row_dots_zero, indexed_basis_covariance_quadratic_zero_iff_centered_weighted_score_zero | **New:** bounded covariance row kernel equals centered sample evaluation kernel |
| `indexed_basis_covariance_positive_definite_iff_no_nonzero_centered_weighted_sample_kernel` (theorem) | Transport positive-definite iff trivial indexed row kernel through the centered evaluation kernel equivalence | indexed_basis_covariance_positive_definite_iff_no_nonzero_bounded_row_kernel, indexed_basis_covariance_bounded_row_kernel_iff_centered_weighted_score_zero | **New:** positive definite iff no nonzero typed coefficient vector annihilates all centered weighted sample evaluations |
| `indexed_basis_centered_weighted_score_sum_zero` (theorem) | Identify centered weighted finite sum as existing centered expectation and apply earlier result | centered_score_has_zero_expectation, FiniteSum.finite_sum | **New:** centered weighted sample evaluation lies in exact zero-sum hyperplane when mass=1 |
| `indexed_basis_centered_weighted_score_nonnegative_implies_quadratic_zero` (theorem) | Generic finite nonnegative-zero sum criterion plus centered kernel equivalence | FiniteSum.finite_sum_nonnegative_zero_iff, indexed_basis_centered_weighted_score_sum_zero, indexed_basis_covariance_quadratic_zero_iff_centered_weighted_score_zero | **New:** all nonnegative centered evaluations force a null covariance direction |
| `indexed_basis_centered_weighted_score_nonpositive_implies_quadratic_zero` (theorem) | Negate sample evaluations using the maintained sum-negation theorem then apply generic nonnegative-zero iff | FiniteSum.finite_sum_neg, FiniteSum.finite_sum_nonnegative_zero_iff, indexed_basis_centered_weighted_score_sum_zero, indexed_basis_covariance_quadratic_zero_iff_centered_weighted_score_zero | **New:** all nonpositive centered evaluations likewise force covariance nullity |
| `indexed_basis_covariance_quadratic_positive_iff_nonzero_centered_sample` (theorem) | Positive-score witness gives nonzero centered product; reverse uses quadratic PSD and zero-kernel iff | indexed_basis_covariance_quadratic_positive_iff_supported_deviation, indexed_basis_covariance_quadratic_nonnegative, indexed_basis_covariance_quadratic_zero_iff_centered_weighted_score_zero, Stdlib.Rmult_integral | **New:** positive quadratic iff some sampled centered weighted evaluation is nonzero |
| `indexed_basis_covariance_positive_definite_iff_every_nonzero_direction_detected` (theorem) | Pointwise lift of the constructive nonzero centered evaluation iff to each nonzero typed vector | indexed_basis_covariance_positive_definite, indexed_basis_covariance_quadratic_positive_iff_nonzero_centered_sample | **New:** positive definite iff every nonzero typed direction has a detecting sampled evaluation |
| `indexed_basis_centered_sample_evaluation_zero_iff_all_sample_scores_zero` (theorem) | Reify In sample positions with stdlib List.nth_error and Fin bounded indices; reuse the existing list-to-vector bridge | vector_of_list_nth_error, Stdlib.List.In_nth_error/nth_error_Some/nth_error_In, Fin.of_nat_lt/to_nat_of_nat | **New:** zero bounded Fin.t sample evaluation iff every enumerated centered score is zero |
| `indexed_basis_covariance_bounded_row_kernel_iff_bounded_sample_kernel` (theorem) | Compose existing covariance-row kernel with new pure sample-indexing equivalence | indexed_basis_covariance_bounded_row_kernel_iff_centered_weighted_score_zero, indexed_basis_centered_sample_evaluation_zero_iff_all_sample_scores_zero | **New:** covariance-row and bounded sample-evaluation kernels coincide |
| `indexed_basis_covariance_positive_definite_iff_no_nonzero_bounded_sample_kernel` (theorem) | Transport existing positive-definiteness vs sampled kernel criterion through exact standard index bridge | indexed_basis_covariance_positive_definite_iff_no_nonzero_centered_weighted_sample_kernel, indexed_basis_centered_sample_evaluation_zero_iff_all_sample_scores_zero | **New:** positive-definite covariance iff bounded sample mapping has no nonzero typed kernel direction |
| `finite_expectation_monotone_equality_iff_positive_support` (theorem) | Instantiate generic finite-sum equality iff at products and distinguish zero from positive sample weight | FiniteSum.finite_sum_monotone_equality_iff_pointwise, Stdlib.Rlt_dec, Stdlib.Psatz | **New:** weighted expectations equal precisely when ordered scores agree on listed positive support |
| `finite_expectation_strict_monotone_iff_positive_support_witness` (theorem) | Reuse constructive strict monotonicity on weighted summands and derive a positive-weight witness | FiniteSum.finite_sum_strict_monotone_iff_strict_member, Stdlib.Psatz | **New:** strict weighted expectation comparison exactly witnesses a positively weighted strict score |
| `finite_expectation_nonnegative_zero_iff_positive_support` (theorem) | Zero-score specialization of existing ordered-expectation equality criterion; symmetry only | finite_expectation_monotone_equality_iff_positive_support, expectation_zero, Stdlib.Logic | **New:** vanishing nonnegative finite expectation iff all positive-weight sample scores vanish |
| `finite_expectation_nonnegative_positive_iff_positive_support_witness` (theorem) | Strict-order specialization at the zero score, no new induction | finite_expectation_strict_monotone_iff_positive_support_witness, expectation_zero | **New:** strict positivity iff a positive-weight positive-score listed witness exists |
| `finite_expectation_square_zero_iff_zero_on_positive_support` (theorem) | Nonnegative expectation zero support, zero-product reduction, no recursion | finite_expectation_nonnegative_zero_iff_positive_support, Stdlib.Reals.Rmult_integral/Rle_0_sqr | **New:** expected square is zero precisely when every positively weighted listed score is zero |
| `finite_expectation_square_positive_iff_nonzero_positive_support` (theorem) | Strict expected-square support witness and standard real square inequalities | finite_expectation_nonnegative_positive_iff_positive_support_witness, Stdlib.Psatz.nra | **New:** positive expected square iff a nonzero positively weighted sample score exists |
| `weighted_basis_sum_coefficients_scale` (theorem) | Small list-combine induction plus established real finite sum and ring arithmetic | weighted_basis_sum, linear_combination, FiniteSum.finite_sum, Stdlib.List.combine/map, Stdlib.Ring | **New:** scalar homogeneity of coefficient-weighted composite scores, including unequal list lengths |
| `indexed_basis_centered_weighted_score_scale` (theorem) | Vector/list mapping transport, composite/expectation scaling, ring normalization | VectorSpec.to_list_map, weighted_basis_sum_coefficients_scale, expectation_scale, expectation_ext, Stdlib.Ring | **New:** typed centered score is homogeneous in its coefficient direction |
| `indexed_basis_centered_sample_evaluation_scale` (theorem) | Direct reuse of established centered score scaling for bounded indices | indexed_basis_centered_weighted_score_scale, Stdlib.Vectors.Fin/Vector | **New:** bounded centered sample evaluation is homogeneous in coefficient vectors |
| `weighted_basis_sum_coefficients_zip_add` (theorem) | Equal-length paired coefficient induction retaining the shared sum tail | Stdlib.List.combine/map, weighted_basis_sum, FiniteSum.finite_sum, Stdlib.Ring | **New:** componentwise coefficient addition distributes over a finite weighted basis |
| `indexed_vector_to_list_map2_add` (lemma) | Standard paired vector induction and list conversion, no vector implementation | Stdlib.Vectors.Vector.rect2/map2/to_list, Stdlib.List.combine/map | **New:** map2 plus corresponds to the paired coefficient list representation |
| `indexed_basis_centered_weighted_score_add` (theorem) | Reuse list addition, vector transport and existing linear expectation | indexed_vector_to_list_map2_add, weighted_basis_sum_coefficients_zip_add, VectorSpec.length_to_list, expectation_add, expectation_ext | **New:** centered weighted score is additive in the typed coefficient direction |
| `indexed_basis_centered_sample_evaluation_add` (theorem) | Unfold bounded wrapper and apply the existing centered-score additivity | indexed_basis_centered_weighted_score_add, Stdlib.Vectors.Vector.map2/nth | **New:** dimension-safe sample evaluation is pointwise additive |
| `weighted_basis_sum_repeat_zero` (theorem) | Explicit empty/cons basis cases; retain shared sum tail and ring normalization | Stdlib.List.repeat/combine, weighted_basis_sum, FiniteSum.finite_sum, Stdlib.Ring | **New:** all-zero coefficient list evaluates to zero |
| `indexed_basis_centered_sample_evaluation_zero_coefficients` (theorem) | Transport canonical zero vector, reuse zero list composite and expectation extensionality | VectorSpec.to_list_const, weighted_basis_sum_repeat_zero, expectation_zero, expectation_ext | **New:** typed zero coefficient vector belongs to every bounded sample kernel |
| `indexed_basis_centered_sample_kernel_closed_under_scale` (theorem) | Rewrite checked pointwise homogeneity and zero premise | indexed_basis_centered_sample_evaluation_scale, Stdlib.Ring | **New:** the bounded evaluation kernel is closed under real scalar multiplication |
| `indexed_basis_centered_sample_kernel_closed_under_add` (theorem) | Rewrite checked pointwise additivity and zero premises | indexed_basis_centered_sample_evaluation_add, Stdlib.Ring | **New:** the bounded evaluation kernel is closed under coefficient-vector addition |
| `indexed_basis_centered_sample_kernel_nonzero_scale_iff` (theorem) | Zero-product lemma and existing scale-closure theorem | indexed_basis_centered_sample_evaluation_scale, indexed_basis_centered_sample_kernel_closed_under_scale, Stdlib.Reals.Rmult_integral | **New:** nonzero coefficient scaling preserves the sample kernel exactly |
| `indexed_basis_bounded_covariance_row_kernel_of_sample_constant` (theorem) | Convert each row dot to covariance by existing unconditional basis identity, then use symmetry, support extensionality and constant covariance zero. | covariance_with_weighted_basis_as_row_dot, VectorSpec.length_to_list, covariance_symmetric, covariance_extensional_on_samples, covariance_with_constant_first. | **New:** Signed-weight normalized sample constancy entails exact bounded covariance row nullity. |
| `indexed_basis_bounded_covariance_row_kernel_iff_sample_kernel` (theorem) | Unfold two transparent kernel predicates, apply checked bounded kernel bridge | indexed_basis_covariance_bounded_row_kernel_iff_bounded_sample_kernel, Stdlib.Vectors.Fin/Vector | **New:** reuse named covariance-row vs. centered-sample kernel equivalence |
| `indexed_basis_bounded_covariance_row_kernel_zero` (theorem) | Transport canonical zero evaluation through named kernel equivalence | indexed_basis_bounded_covariance_row_kernel_iff_sample_kernel, indexed_basis_centered_sample_evaluation_zero_coefficients | **New:** typed zero coefficient vector annihilates bounded covariance rows |
| `indexed_basis_bounded_covariance_row_kernel_closed_under_add` (theorem) | Transport both hypotheses via iff; apply prior sample-kernel addition; transport conclusion | indexed_basis_bounded_covariance_row_kernel_iff_sample_kernel, indexed_basis_centered_sample_kernel_closed_under_add | **New:** covariance-row kernel closed under vector addition |
| `indexed_basis_bounded_covariance_row_kernel_closed_under_scale` (theorem) | Transport via iff and reuse prior sample-kernel scalar closure | indexed_basis_bounded_covariance_row_kernel_iff_sample_kernel, indexed_basis_centered_sample_kernel_closed_under_scale | **New:** covariance-row kernel closed under arbitrary real scaling |
| `indexed_basis_bounded_covariance_row_kernel_nonzero_scale_iff` (theorem) | Compose two named kernel iff bridges with the checked nonzero-scaling sample iff | indexed_basis_bounded_covariance_row_kernel_iff_sample_kernel, indexed_basis_centered_sample_kernel_nonzero_scale_iff, Stdlib.Logic.tauto | **New:** covariance row nullity invariant under nonzero scalar coefficient multiplication |
| `indexed_basis_covariance_positive_definite_iff_named_row_kernel_trivial` (theorem) | Transparent row-kernel predicate unfolding and existing positive-definite criterion | indexed_basis_covariance_positive_definite_iff_no_nonzero_bounded_row_kernel | **Refactored API:** existing typed row nullspace injectivity result expressed using named kernel predicate |
| `indexed_basis_covariance_positive_definite_iff_named_sample_kernel_trivial` (theorem) | Transparent sample-kernel predicate unfolding and existing positive-definite criterion | indexed_basis_covariance_positive_definite_iff_no_nonzero_bounded_sample_kernel | **Refactored API:** existing typed sample nullspace injectivity result expressed using named kernel predicate |
| `indexed_basis_covariance_quadratic_zero_iff_named_sample_kernel` (theorem) | Compose centered-score quadratic nullity with Fin.t sample indexing and named predicate | indexed_basis_covariance_quadratic_zero_iff_centered_weighted_score_zero, indexed_basis_centered_sample_evaluation_zero_iff_all_sample_scores_zero, Stdlib.Logic.tauto | **New:** zero covariance quadratic iff named centered-sample kernel membership |
| `indexed_basis_covariance_quadratic_zero_iff_named_row_kernel` (theorem) | Propositional composition of named quadratic/sample and named row/sample iff | indexed_basis_covariance_quadratic_zero_iff_named_sample_kernel, indexed_basis_bounded_covariance_row_kernel_iff_sample_kernel | **New:** zero covariance quadratic iff named bounded covariance-row nullspace membership |
| `indexed_basis_centered_sample_vector_nth` (theorem) | Unfold maintained vector wrapper; standard nth-of-Vector.map law | Stdlib.Vectors.VectorSpec.nth_map, indexed_basis_centered_sample_evaluation | **New:** full output vector has exactly the established bounded coordinates |
| `indexed_basis_centered_sample_vector_zero_iff_named_sample_kernel` (theorem) | Standard vector coordinate extensionality and constant-vector nth equality | Stdlib.Vectors.VectorSpec.eq_nth_iff/const_nth, indexed_basis_centered_sample_vector_nth | **New:** concrete sample-output vector equals zero iff named sample-kernel membership |
| `indexed_basis_centered_sample_vector_zero_coefficients` (theorem) | Transport indexed zero coordinates through named kernel iff | indexed_basis_centered_sample_evaluation_zero_coefficients, indexed_basis_centered_sample_vector_zero_iff_named_sample_kernel | **New:** zero coefficients produce zero output |
| `indexed_basis_centered_sample_vector_zero_iff_all_sample_scores_zero` (theorem) | Compose bounded-index/list-score and vector/kernel iff lemmas | indexed_basis_centered_sample_evaluation_zero_iff_all_sample_scores_zero, indexed_basis_centered_sample_vector_zero_iff_named_sample_kernel, tauto | **New:** zero vector output iff every listed score zero |
| `indexed_basis_centered_sample_vector_nonzero_scale_zero_iff` (theorem) | Compose two output/kernel iff and pre-existing scale iff | indexed_basis_centered_sample_kernel_nonzero_scale_iff, indexed_basis_centered_sample_vector_zero_iff_named_sample_kernel | **New:** nonzero scaling preserves output nullity |
| `indexed_basis_centered_sample_vector_scale` (theorem) | Vector coordinate equality via standard extensionality/nth-map and prior scalar law | VectorSpec.eq_nth_iff/nth_map, indexed_basis_centered_sample_vector_nth, indexed_basis_centered_sample_evaluation_scale | **New:** typed real output vector respects coefficient scalar multiplication |
| `indexed_basis_centered_sample_vector_add` (theorem) | Vector coordinate equality and standard nth-map2, prior sample coordinate additivity | VectorSpec.eq_nth_iff/nth_map2, indexed_basis_centered_sample_vector_nth, indexed_basis_centered_sample_evaluation_add | **New:** concrete vector-to-vector evaluator is additive |
| `indexed_basis_covariance_quadratic_zero_iff_sample_vector_zero` (theorem) | Compose named quadratic-nullity and typed-output-zero equivalences | indexed_basis_covariance_quadratic_zero_iff_named_sample_kernel, indexed_basis_centered_sample_vector_zero_iff_named_sample_kernel, Stdlib.Logic.tauto | **New:** zero quadratic iff concrete sample output vector is zero |
| `indexed_basis_covariance_positive_definite_iff_sample_vector_detects_nonzero` (theorem) | Transport named kernel triviality through concrete vector zero predicate | indexed_basis_covariance_positive_definite_iff_named_sample_kernel_trivial, indexed_basis_centered_sample_vector_zero_iff_named_sample_kernel | **New:** finite covariance positive-definiteness iff concrete typed evaluation detects every nonzero coefficient vector |
| `indexed_basis_centered_sample_vector_to_list` (theorem) | Standard Vector.to_list/map and of_list inverse laws, no recursion | VectorSpec.to_list_map, VectorSpec.to_list_of_list_opp | **New:** output list is exactly the centered weighted score map over samples |
| `indexed_real_vector_coordinate_sum_zero` (lemma) | Apply VectorSpec.to_list_const, dimension induction over repeated-zero list, and existing FiniteSum sum | VectorSpec.to_list_const, Stdlib.List.repeat, FiniteSum.finite_sum, Stdlib.Ring | **New:** sum of typed zero real vector vanishes in all finite dimensions |
| `indexed_real_vector_coordinate_sum_scale` (lemma) | Rewrite maintained vector-to-list map and reuse finite-sum map/scaling laws | VectorSpec.to_list_map, FiniteSum.finite_sum_map, FiniteSum.finite_sum_scale | **New:** common coordinate sum is homogeneous for arbitrary real scalars |
| `indexed_real_vector_coordinate_sum_add` (lemma) | Standard Vector.rect2 matched-length eliminator and real ring arithmetic over existing shared finite sum | Vector.rect2/map2/to_list, FiniteSum.finite_sum, Stdlib.Ring | **New:** common coordinate sum preserves componentwise addition |
| `indexed_real_vector_zero_sum_closed_under_scale` (lemma) | Rewrite common functional homogeneity and zero sum | indexed_real_vector_coordinate_sum_scale, Stdlib.Ring | **New:** zero-sum vector family is scalar closed |
| `indexed_real_vector_zero_sum_closed_under_add` (lemma) | Rewrite common functional additivity and both input zero sums | indexed_real_vector_coordinate_sum_add, Stdlib.Ring | **New:** zero-sum vector family is addition closed |
| `indexed_real_vector_coordinate_sum_const` (lemma) | Reuse VectorSpec.to_list_const and the existing finite-sum fold on a repeated list; dimensional induction with S_INR and ring | VectorSpec.to_list_const, FiniteSum.finite_sum, Stdlib.List.repeat, Stdlib.Reals.S_INR, Stdlib.Ring | **New:** constant vector coordinate sum equals INR n times its entry |
| `indexed_real_vector_zero_sum_const_nonzero` (lemma) | Apply constant-sum identity, real zero-product and natural INR nonnegativity | indexed_real_vector_coordinate_sum_const, Stdlib.Reals.Rmult_integral/pos_INR/S_INR, Stdlib.Lra | **New:** a nonzero constant vector of positive dimension is outside the zero-sum family |
| `indexed_real_vector_coordinate_sum_cons` (lemma) | Definitional reduction of the standard Vector.cons-to-list conversion and shared fold | Stdlib.Vectors.Vector.cons/to_list, FiniteSum.finite_sum, Stdlib.List.fold_right | **New:** nonempty vector coordinate sum equals head plus tail sum, without custom recursion |
| `indexed_real_vector_zero_sum_cons_iff` (lemma) | Rewrite the shared cons law then use scalar linear arithmetic | indexed_real_vector_coordinate_sum_cons, Stdlib.Lra | **New:** zero sum iff head equals negative coordinate sum of tail |
| `indexed_real_vector_zero_sum_from_tail` (lemma) | Instantiate converse of cons iff with the uniquely determined first coordinate | indexed_real_vector_zero_sum_cons_iff, Stdlib.Vectors.Vector.cons | **New:** any n-coordinate tail extends constructively to an (n+1)-coordinate zero-sum vector |
| `indexed_real_vector_coordinate_sum_surjective` (lemma) | Construct cons target (const zero), then rewrite earlier generic cons and zero-vector sum laws | indexed_real_vector_coordinate_sum_cons, indexed_real_vector_coordinate_sum_zero, Stdlib.Vectors.Vector.const, Stdlib.Ring | **New:** coordinate sum maps every positive vector dimension onto all real scalars, with explicit witness |
| `indexed_real_vector_zero_sum_extension_zero_sum` (lemma) | Unfold wrapper and reuse prior canonical tail-extension theorem | indexed_real_vector_zero_sum_from_tail | **New:** map image belongs to the zero-sum family for every tail |
| `indexed_real_vector_zero_sum_extension_tail` (lemma) | Definitional reduction of standard vector tail destructor after cons | Stdlib.Vectors.Vector.cons/tl | **New:** Vector.tl is an exact left inverse to the zero-sum extension |
| `indexed_real_vector_zero_sum_extension_add` (lemma) | Rewrite shared coordinate-sum additivity, compute standard Vector.map2 on cons, close with ring | indexed_real_vector_coordinate_sum_add, Stdlib.Vectors.Vector.map2, Stdlib.Ring | **New:** additive linearity of canonical zero-sum extension |
| `indexed_real_vector_zero_sum_extension_scale` (lemma) | Rewrite existing coordinate-sum homogeneity, compute Vector.map on cons and normalize with ring | indexed_real_vector_coordinate_sum_scale, Stdlib.Vectors.Vector.map, Stdlib.Ring | **New:** scalar homogeneity of canonical zero-sum extension |
| `indexed_real_vector_zero_sum_extension_injective` (lemma) | Apply f_equal Vector.tl, then rewrite both recovered tails using standard retraction | Stdlib.Logic.f_equal, Stdlib.Vectors.Vector.tl, indexed_real_vector_zero_sum_extension_tail | **New:** distinct original coefficient tails have distinct zero-sum extensions |
| `indexed_real_vector_zero_sum_extension_inverse_on_zero_sum` (lemma) | Apply standard VectorSpec.eta to derive the uniquely determined head from the zero-sum-cons iff and rebuild the vector | Stdlib.Vectors.VectorSpec.eta, Vector.hd/tl, indexed_real_vector_zero_sum_cons_iff | **New:** every positive-dimensional zero-sum vector equals the canonical extension of its tail |
| `indexed_real_vector_zero_sum_extension_surjective_on_zero_sum` (lemma) | Witness arbitrary zero-sum vector by Vector.tl and reuse exact inverse result | Stdlib.Vectors.Vector.tl, indexed_real_vector_zero_sum_extension_inverse_on_zero_sum | **New:** extension surjective onto, but not beyond, the zero-sum target |
| `indexed_real_vector_zero_sum_iff_extension_of_tail` (lemma) | Compose proven inverse with extension target membership under equality | indexed_real_vector_zero_sum_extension_inverse_on_zero_sum, indexed_real_vector_zero_sum_extension_zero_sum | **New:** zero-sum iff canonical re-extension of own tail fixes the vector |
| `indexed_real_vector_zero_sum_extension_zero` (lemma) | Identify standard tl of a positive-length zero vector, reuse the proven extension inverse and zero-coordinate-sum law | Stdlib.Vectors.Vector.tl/const, indexed_real_vector_zero_sum_extension_inverse_on_zero_sum, indexed_real_vector_coordinate_sum_zero | **New:** zero-sum extension preserves the typed additive zero |
| `indexed_real_vector_zero_sum_equal_iff_tails_equal` (lemma) | Use Vector.tl congruence forward and canonical inverse for both zero-sum inputs backward | Stdlib.Vectors.Vector.tl, indexed_real_vector_zero_sum_extension_inverse_on_zero_sum | **New:** positive-length zero-sum vectors agree iff their shorter tails agree |
| `indexed_real_vector_zero_sum_equal_iff_list_tails_equal` (lemma) | Handle n=0 via VectorSpec.eq_nth_iff; for n=S k reuse typed-tail equality and VectorSpec.eta/to_list_inj | indexed_real_vector_zero_sum_equal_iff_tails_equal, VectorSpec.eta/to_list_inj | **New:** zero-sum vectors of every length are equal iff their list tails agree |
| `indexed_real_vector_zero_sum_list_tail_zero_iff` (lemma) | Split the length index before introducing vectors; specialize generalized list-tail equality against zero and simplify repeat | indexed_real_vector_coordinate_sum_zero, VectorSpec.to_list_const, indexed_real_vector_zero_sum_equal_iff_list_tails_equal | **New:** zero-sum vector of any length is zero iff its list tail vanishes |
| `indexed_real_vector_zero_sum_extension_zero_iff_tail_zero` (lemma) | Apply Vector.tl congruence and established left inverse, reverse via zero preservation | indexed_real_vector_zero_sum_extension_tail, indexed_real_vector_zero_sum_extension_zero, Stdlib.Logic.f_equal | **New:** explicit extension is zero exactly for a zero input |
| `indexed_real_vector_zero_sum_projection_zero_sum` (lemma) | Unfold the canonical projection and reuse the zero-sum-extension membership theorem | indexed_real_vector_zero_sum_extension_zero_sum, Stdlib.Vectors.Vector.tl | **New:** projection outputs always belong to the zero-sum family |
| `indexed_real_vector_zero_sum_projection_tail` (lemma) | Unfold only the wrapper and apply standard Vector.tl's established extension retraction | indexed_real_vector_zero_sum_extension_tail, Stdlib.Vectors.Vector.tl | **New:** zero-sum projection preserves every tail coordinate |
| `indexed_real_vector_zero_sum_projection_fixed_iff_zero_sum` (lemma) | Transport target membership through projection equality; reverse via exact inverse on zero-sum vectors | indexed_real_vector_zero_sum_projection_zero_sum, indexed_real_vector_zero_sum_extension_inverse_on_zero_sum | **New:** projection fixes exactly the zero-sum vectors |
| `indexed_real_vector_zero_sum_projection_idempotent` (lemma) | Reuse projection target membership and verified fixed-point iff | indexed_real_vector_zero_sum_projection_fixed_iff_zero_sum, indexed_real_vector_zero_sum_projection_zero_sum | **New:** repeated canonical projection has no further effect |
| `indexed_real_vector_zero_sum_projection_surjective_on_zero_sum` (lemma) | Choose each zero-sum vector as its own preimage by the fixed-point iff | indexed_real_vector_zero_sum_projection_fixed_iff_zero_sum | **New:** projection is onto its zero-sum target |
| `indexed_real_vector_zero_sum_projection_zero_iff_tail_zero` (lemma) | Unfold projection and apply earlier extension-zero/input-zero iff | indexed_real_vector_zero_sum_extension_zero_iff_tail_zero, Stdlib.Vectors.Vector.const/tl | **New:** projection is zero precisely when its input tail vanishes |
| `indexed_real_vector_zero_sum_projection_equal_iff_tails_equal` (lemma) | Congruence of standard Vector.tl and projection-tail retraction forward; rewrite tails in extension backward | Stdlib.Logic.f_equal, indexed_real_vector_zero_sum_projection_tail, Stdlib.Vectors.Vector.tl | **New:** images under projection agree iff input tails agree |
| `indexed_real_vector_zero_sum_projection_zero` (lemma) | Apply projection fixed-point iff to the already verified constant-zero coordinate sum | indexed_real_vector_zero_sum_projection_fixed_iff_zero_sum, indexed_real_vector_coordinate_sum_zero, Stdlib.Vectors.Vector.const | **New:** canonical projection preserves zero |
| `indexed_real_vector_zero_sum_projection_add` (lemma) | Rewrite RHS by existing extension additivity, then expand nonempty vectors via standard VectorSpec.eta to reduce tl/map2 equality | indexed_real_vector_zero_sum_extension_add, Stdlib.Vectors.VectorSpec.eta, Vector.map2/tl | **New:** additive linearity of the canonical projection |
| `indexed_real_vector_zero_sum_projection_scale` (lemma) | Rewrite RHS by extension scalar homogeneity, then use VectorSpec.eta to reduce tl/map equality | indexed_real_vector_zero_sum_extension_scale, Stdlib.Vectors.VectorSpec.eta, Vector.map/tl | **New:** real scalar homogeneity of the projection |
| `indexed_real_vector_zero_sum_projection_extension_fixed` (lemma) | Apply existing fixed-point iff to checked extension zero-sum membership | indexed_real_vector_zero_sum_projection_fixed_iff_zero_sum, indexed_real_vector_zero_sum_extension_zero_sum | **New:** zero-sum extension image is pointwise fixed by canonical projection |
| `indexed_real_vector_zero_sum_projection_ignores_head` (lemma) | Apply established projection equality iff equality of tails; Stdlib Vector.tl/cons reduces reflexively | indexed_real_vector_zero_sum_projection_equal_iff_tails_equal, Stdlib.Vectors.Vector.cons/tl | **New:** projection discards arbitrary initial-coordinate differences |
| `indexed_real_vector_zero_sum_projection_changes_nonzero_constant` (lemma) | Hypothetical fixed point implies zero-sum; contradict checked nonzero-constant exclusion | indexed_real_vector_zero_sum_projection_fixed_iff_zero_sum, indexed_real_vector_zero_sum_const_nonzero | **New:** nonzero constant vectors are never fixed by projection in positive length |
| `indexed_real_vector_zero_sum_projection_kernel_normal_form` (lemma) | Rewrite checked projection-zero iff tail-zero; reconstruct vector from standard head/tail by VectorSpec.eta, with the arbitrary head as explicit witness | indexed_real_vector_zero_sum_projection_zero_iff_tail_zero, Stdlib.Vectors.VectorSpec.eta, Vector.hd/tl/cons/const | **New:** every projection-kernel vector is exactly a head-only vector, with explicit scalar witness |
| `indexed_real_vector_zero_sum_extension_unique_tail` (lemma) | Apply standard Vector.tl congruence and the checked extension retraction; reverse by established inverse on zero-sum targets | Stdlib.Logic.f_equal, Stdlib.Vectors.Vector.tl, indexed_real_vector_zero_sum_extension_tail, indexed_real_vector_zero_sum_extension_inverse_on_zero_sum | **New:** unique shorter tail witness for each zero-sum extended target |
| `indexed_real_vector_zero_sum_projection_fiber_iff` (lemma) | Forward transport target zero-sum membership and preserve tail; reverse use exact extension inverse with equal tails | indexed_real_vector_zero_sum_projection_zero_sum, indexed_real_vector_zero_sum_projection_tail, indexed_real_vector_zero_sum_extension_inverse_on_zero_sum | **New:** exact preimage fibers: target zero-sum and input/output tails agree |
| `indexed_real_vector_zero_sum_projection_image_iff_zero_sum` (lemma) | Combine checked image zero-sum membership with preexisting surjectivity-on-zero-sum theorem | indexed_real_vector_zero_sum_projection_zero_sum, indexed_real_vector_zero_sum_projection_surjective_on_zero_sum | **New:** projection image equals zero-sum family, stated as a constructive existence iff |
| `indexed_real_vector_zero_sum_projection_head` (lemma) | Rewrite input coordinate sum through VectorSpec.eta and existing cons law, unfold projected head and normalize the scalar identity | indexed_real_vector_coordinate_sum_cons, Stdlib.Vectors.VectorSpec.eta/hd/tl, Stdlib.Ring | **New:** projection's head equals original head minus original total coordinate sum |
| `indexed_real_vector_zero_sum_projection_and_sum_injective` (lemma) | Recover tails from projection equality; recover heads from paired total sums and projected-head law using Lra; reconstruct via VectorSpec.eta | indexed_real_vector_zero_sum_projection_equal_iff_tails_equal, indexed_real_vector_zero_sum_projection_head, Stdlib.Logic.f_equal, Stdlib.Vectors.VectorSpec.eta, Stdlib.Lra | **New:** projection plus total sum uniquely determines arbitrary nonempty input vector |
| `indexed_real_vector_zero_sum_projection_and_sum_equal_iff` (lemma) | Apply paired injectivity in forward direction, substitute original equality for reverse reflexivity | indexed_real_vector_zero_sum_projection_and_sum_injective, Stdlib.Logic.eq_ind | **New:** exact iff equality criterion for projection-plus-total representation |
| `indexed_real_vector_projection_sum_reconstruct_tail` (lemma) | Reduce standard Vector.tl on Vector.cons directly | Stdlib.Vectors.Vector.cons/tl | **New:** prescribed tail is recovered by the reconstruction operation |
| `indexed_real_vector_projection_sum_reconstruct_coordinate_sum` (lemma) | Rewrite the checked coordinate-sum-on-cons law and close scalar cancellation using Ring | indexed_real_vector_coordinate_sum_cons, Stdlib.Ring | **New:** reconstructed vector has exactly the supplied total sum |
| `indexed_real_vector_projection_sum_reconstruct_projection` (lemma) | Unfold canonical projection and reconstruction, reduce the standard Vector.tl/cons pair | indexed_real_vector_zero_sum_projection, Stdlib.Vectors.Vector.tl/cons | **New:** reconstruction projects to canonical zero-sum extension of its tail |
| `indexed_real_vector_projection_sum_reconstruct_roundtrip` (lemma) | Apply existing paired projection/sum injectivity with checked reconstruction projection and sum laws | indexed_real_vector_zero_sum_projection_and_sum_injective, indexed_real_vector_projection_sum_reconstruct_projection, indexed_real_vector_projection_sum_reconstruct_coordinate_sum | **New:** vector reconstructed from its own tail and total is exactly the original |
| `indexed_real_vector_projection_sum_reconstruct_unique_fiber` (lemma) | Use paired injectivity and standard extension inverse for the forward direction; converse by substitution and verified projection/sum formulas | indexed_real_vector_zero_sum_projection_and_sum_injective, indexed_real_vector_zero_sum_extension_inverse_on_zero_sum, indexed_real_vector_projection_sum_reconstruct_projection, indexed_real_vector_projection_sum_reconstruct_coordinate_sum | **New:** unique preimage of each (zero-sum target, arbitrary total) pair |
| `indexed_real_vector_tail_total_decode_encode` (lemma) | Reduce standard product encode/decode wrappers and reuse exact reconstruction round-trip | indexed_real_vector_projection_sum_reconstruct_roundtrip, Stdlib.Datatypes.fst/snd | **New:** decoder is a left inverse of the standard tail/total encoding |
| `indexed_real_vector_tail_total_encode_decode` (lemma) | Destruct only the standard pair and reuse checked reconstruction tail and coordinate-sum laws | Stdlib.Datatypes.prod/fst/snd, indexed_real_vector_projection_sum_reconstruct_tail, indexed_real_vector_projection_sum_reconstruct_coordinate_sum | **New:** encoder is a left inverse of decoder for every tail/total pair |
| `indexed_real_vector_tail_total_encode_injective` (lemma) | Apply maintained f_equal to the decoder and rewrite both verified decode/encode identities | Stdlib.Logic.f_equal, indexed_real_vector_tail_total_decode_encode | **New:** standard product encoding is injective |
| `indexed_real_vector_tail_total_decode_injective` (lemma) | Apply maintained f_equal to the encoder and rewrite both verified encode/decode identities | Stdlib.Logic.f_equal, indexed_real_vector_tail_total_encode_decode | **New:** standard product reconstruction is injective |
| `indexed_real_vector_projection_sum_reconstruct_zero` (lemma) | Apply the established zero coordinate-sum theorem and standard cons/const reduction | indexed_real_vector_coordinate_sum_zero, Vector.const/cons, Ring | **New:** zero tail and total reconstruct exactly the zero vector |
| `indexed_real_vector_projection_sum_reconstruct_add` (lemma) | Rewrite finite coordinate-sum additivity and normalize only the reconstructed first entry | indexed_real_vector_coordinate_sum_add, Vector.map2/cons, Ring | **New:** reconstruction preserves tail and total addition |
| `indexed_real_vector_projection_sum_reconstruct_scale` (lemma) | Rewrite sum homogeneity and normalize the first-coordinate scalar distribution | indexed_real_vector_coordinate_sum_scale, Vector.map/cons, Ring | **New:** reconstruction preserves real scaling |
| `indexed_real_vector_tail_total_encode_zero` (lemma) | Use coordinate-sum zero and standard Vector.const/tl reduction | indexed_real_vector_coordinate_sum_zero, Vector.const/tl | **New:** zero vector encodes to zero tail/total product |
| `indexed_real_vector_tail_total_encode_add` (lemma) | Reuse coordinate-sum addition and standard VectorSpec.eta to establish tail addition | indexed_real_vector_coordinate_sum_add, VectorSpec.eta, Vector.map2/tl | **New:** encoding preserves componentwise product addition |
| `indexed_real_vector_tail_total_encode_scale` (lemma) | Reuse sum scaling and standard VectorSpec.eta for tail scaling | indexed_real_vector_coordinate_sum_scale, VectorSpec.eta, Vector.map/tl | **New:** encoding is homogeneous |
| `indexed_real_vector_tail_total_decode_zero` (lemma) | Reduce product projections and delegate to reconstruction zero | indexed_real_vector_projection_sum_reconstruct_zero, Stdlib.Datatypes.fst/snd | **New:** decoder preserves zero |
| `indexed_real_vector_tail_total_decode_add` (lemma) | Reduce product projections and delegate to reconstruction addition | indexed_real_vector_projection_sum_reconstruct_add, Stdlib.Datatypes.fst/snd | **New:** decoder preserves addition |
| `indexed_real_vector_tail_total_decode_scale` (lemma) | Reduce product projections and delegate to reconstruction scaling | indexed_real_vector_projection_sum_reconstruct_scale, Stdlib.Datatypes.fst/snd | **New:** decoder preserves scaling |
| `indexed_real_vector_zero_sum_iff_tail_total_encode_snd_zero` (lemma) | Unfold only the maintained zero-sum predicate and product-encoding definition; standard snd reduction makes both propositions definitionally identical. | Stdlib.Datatypes.snd, indexed_real_vector_tail_total_encode, indexed_real_vector_zero_sum. | **New:** The second component of the existing product encoding detects the exact zero-sum constraint. |
| `indexed_real_vector_zero_sum_iff_tail_total_encode_zero_total` (lemma) | In the forward implication unfold the encoding and rewrite the stored coordinate sum to zero. In the reverse implication take snd of the product equality by the checked preceding iff. | Stdlib.Datatypes.snd, Stdlib.Vectors.Vector.tl, indexed_real_vector_zero_sum_iff_tail_total_encode_snd_zero. | **New:** The zero-sum family is precisely the set of product encodings with second component zero. |
| `indexed_real_vector_tail_total_decode_zero_sum_iff_total_zero` (lemma) | Unfold zero-sum and the standard-product decoder, then rewrite the checked reconstruction-coordinate-sum identity; the remaining equivalence is reflexive. | indexed_real_vector_projection_sum_reconstruct_coordinate_sum, indexed_real_vector_tail_total_decode, Stdlib.Logic. | **New:** Decoding product coordinates gives a zero-sum vector exactly when the supplied real total is zero. |
| `indexed_real_vector_tail_total_decode_zero_total_extension` (lemma) | Unfold the transparent product decoder and both already maintained constructors. Apply congruence to standard Vector.cons and close 0 minus a sum equals the negative sum by Stdlib.Ring. | Stdlib.Vectors.Vector.cons, Stdlib.Ring, indexed_real_vector_projection_sum_reconstruct, indexed_real_vector_zero_sum_extension. | **New:** The existing zero-total product decoder is exactly the canonical zero-sum extension. |
| `indexed_real_vector_tail_total_encode_zero_sum_extension` (lemma) | Expand only the encoding, rewrite the verified extension-tail retraction, then use the previously proved zero-sum membership to rewrite the stored coordinate sum. | indexed_real_vector_zero_sum_extension_tail, indexed_real_vector_zero_sum_extension_zero_sum, Stdlib.Datatypes.prod. | **New:** The canonical zero-sum extension encodes to the original tail paired with real zero. |
| `indexed_real_vector_zero_sum_projection_as_zero_total_decode` (lemma) | Rewrite the decoder at zero total by the preceding constructor-compatibility lemma; unfold the existing projection and conclude by reflexivity. | indexed_real_vector_tail_total_decode_zero_total_extension, indexed_real_vector_zero_sum_projection, Stdlib.Vectors.Vector.tl. | **New:** The canonical zero-sum projection factors through the existing standard-product zero-total decoder. |
| `indexed_real_vector_add_zero_right` (lemma) | Use Stdlib VectorSpec.eq_nth_iff to reduce vector equality to equal indexed entries, then VectorSpec.nth_map2 and const_nth; the scalar identity follows from Stdlib.Ring. No list/vector recursion is added. | Stdlib.Vectors.VectorSpec.eq_nth_iff/nth_map2/const_nth, Stdlib.Ring. | **New:** The maintained componentwise addition leaves a real vector unchanged when the second input is zero. |
| `indexed_real_vector_total_axis_coordinate_sum` (lemma) | Apply the existing coordinate_sum_cons theorem and the checked sum of the standard zero vector, then close by Stdlib.Ring. | indexed_real_vector_coordinate_sum_cons, indexed_real_vector_coordinate_sum_zero, Stdlib.Ring. | **New:** The head-only vector has exactly its prescribed scalar coordinate sum. |
| `indexed_real_vector_total_axis_projection_zero` (lemma) | Unfold projection and head-only vector, reduce standard Vector.tl/cons, and reuse the existing zero-sum-extension-zero identity. | indexed_real_vector_zero_sum_extension_zero, Stdlib.Vectors.Vector.tl/cons/const. | **New:** The canonical zero-sum projection annihilates every head-only total-axis vector. |
| `indexed_real_vector_total_axis_zero_sum_iff_total_zero` (lemma) | Unfold only the verified zero-sum predicate, rewrite total_axis_coordinate_sum, and finish by reflexivity. | indexed_real_vector_total_axis_coordinate_sum, indexed_real_vector_zero_sum, Stdlib.Logic. | **New:** A head-only total-axis vector lies in the zero-sum family only at the zero scalar. |
| `indexed_real_vector_total_axis_injective` (lemma) | Apply Stdlib.Logic.f_equal to the existing coordinate-sum map and rewrite both sides by the preceding head-only coordinate-sum lemma. | Stdlib.Logic.f_equal, indexed_real_vector_total_axis_coordinate_sum. | **New:** The prescribed total uniquely identifies a vector on the head-only axis. |
| `indexed_real_vector_zero_sum_projection_kernel_iff_total_axis` (lemma) | Use the previously proved injectivity of the pair (zero-sum projection, coordinate sum); the head-only candidate has zero projection and the same total. The reverse implication substitutes the candidate. | indexed_real_vector_zero_sum_projection_and_sum_injective, indexed_real_vector_total_axis_coordinate_sum, indexed_real_vector_total_axis_projection_zero. | **New:** The zero-sum projection kernel consists exactly of the unique head-only vector carrying the input total. |
| `indexed_real_vector_zero_sum_axis_sum_coordinates` (lemma) | Use the existing linearity of projection and coordinate sum, the projection fixed-point theorem for zero-sum vectors, total-axis projection/sum identities, and the generic map2-add-zero-right lemma. | indexed_real_vector_zero_sum_projection_add/fixed_iff_zero_sum, indexed_real_vector_coordinate_sum_add, indexed_real_vector_add_zero_right, indexed_real_vector_total_axis_coordinate_sum/projection_zero, Stdlib.Ring. | **New:** Adding a zero-sum vector to a head-only vector recovers that zero-sum projection and the prescribed total. |
| `indexed_real_vector_zero_sum_axis_sum_unique` (lemma) | The reverse implication uses the just proved coordinates of the explicit sum. The forward implication uses the established projection-plus-sum injectivity theorem to prove equality with that explicit sum. | indexed_real_vector_zero_sum_axis_sum_coordinates, indexed_real_vector_zero_sum_projection_and_sum_injective, Stdlib.Logic. | **New:** Every prescribed zero-sum projection and total has one additive representative. |
| `indexed_real_vector_zero_sum_axis_decomposition` (lemma) | Instantiate the previously checked unique additive representative theorem at the input vector's own projection and coordinate sum; zero-sum membership comes from the existing projection-image theorem. | indexed_real_vector_zero_sum_axis_sum_unique, indexed_real_vector_zero_sum_projection_zero_sum, Stdlib.Vectors.Vector.map2. | **New:** Every nonempty real vector equals the sum of its canonical zero-sum projection and a head-only vector containing its coordinate sum. |
| `indexed_real_vector_scale_zero` (lemma) | Use the maintained VectorSpec.eq_nth_iff and VectorSpec.nth_map extensionality tools and VectorSpec.const_nth; finish the scalar multiplication by Stdlib.Ring rather than writing an induction or bespoke map implementation. | VectorSpec.eq_nth_iff, VectorSpec.nth_map, VectorSpec.const_nth, Stdlib.Ring. | **New:** Scaling a standard all-zero finite real vector remains zero in every dimension. |
| `indexed_real_vector_total_axis_zero` (lemma) | Reduce the already-defined head-only axis constructor and the maintained standard constant vector by computation; no custom induction or theorem about matrix coordinates is introduced. | Stdlib.Vectors.Vector.cons and Vector.const, indexed_real_vector_total_axis. | **New:** The total-axis embedding maps the additive identity of real scalars to the standard all-zero vector. |
| `indexed_real_vector_total_axis_add` (lemma) | Prove both sides have equal zero-sum projections using projector additivity, axis annihilation and the existing generic vector addition-with-zero lemma; show both sides have the same coordinate sum using the checked sum-addition law; conclude from the existing projection-plus-sum injectivity theorem. | indexed_real_vector_zero_sum_projection_and_sum_injective, indexed_real_vector_zero_sum_projection_add, indexed_real_vector_total_axis_projection_zero/coordinate_sum, indexed_real_vector_add_zero_right, indexed_real_vector_coordinate_sum_add. | **New:** Adding real totals before the head-only embedding equals componentwise addition of the two embedded vectors. |
| `indexed_real_vector_total_axis_scale` (lemma) | Apply the existing joint projection-and-coordinate-sum injectivity theorem. Projection homogeneity and scalar-axis annihilation reduce to the preceding maintained-vector scale-zero identity; total-sum homogeneity and the axis sum theorem close the scalar condition. | indexed_real_vector_zero_sum_projection_and_sum_injective/scale, indexed_real_vector_coordinate_sum_scale, indexed_real_vector_total_axis_projection_zero/coordinate_sum, indexed_real_vector_scale_zero. | **New:** Embedding a scaled real total is the same as scaling every coordinate of its embedded vector. |
| `indexed_real_vector_total_axis_zero_iff_total_zero` (lemma) | Forward direction uses the already certified injectivity of the head-only axis and the newly proved axis-zero law. Reverse direction rewrites the scalar and uses the axis-zero theorem, so no coordinate-level argument is repeated. | indexed_real_vector_total_axis_injective, indexed_real_vector_total_axis_zero, Stdlib.Logic. | **New:** A real total is zero exactly when its head-only embedded finite vector is the all-zero vector. |
| `indexed_real_vector_zero_sum_projection_kernel_iff_exists_total_axis` (lemma) | For a kernel vector use the previously checked stronger characterization that identifies the unique scalar as coordinate_sum v. Conversely substitute an axis witness and apply the previously proved axis projection-annihilation law. | indexed_real_vector_zero_sum_projection_kernel_iff_total_axis, indexed_real_vector_total_axis_projection_zero, Stdlib.Logic. | **New:** The zero-sum projection kernel consists exactly of the head-only scalar-axis vectors. |
| `indexed_real_vector_zero_sum_axis_shift_projection` (lemma) | Rewrite the projection of the sum with the already established projection additivity, replace the projection of the scalar axis with the zero vector, and eliminate the zero summand using the generic VectorSpec-based add-zero-right lemma. | indexed_real_vector_zero_sum_projection_add, indexed_real_vector_total_axis_projection_zero, indexed_real_vector_add_zero_right. | **New:** Adding any scalar-axis vector to a finite real vector leaves its canonical zero-sum projection unchanged. |
| `indexed_real_vector_zero_sum_axis_shift_coordinate_sum` (lemma) | Reuse the exact coordinate_sum_add theorem and the existing axis coordinate-sum identity; no finite-list fold or vector traversal is repeated. | indexed_real_vector_coordinate_sum_add, indexed_real_vector_total_axis_coordinate_sum. | **New:** Adding a scalar-axis vector changes the full coordinate sum by precisely the embedded scalar. |
| `indexed_real_vector_zero_sum_axis_shift_decomposition` (lemma) | Rewrite the shifted vector by the already proved unique canonical axis decomposition, then reuse the immediately preceding projection-invariance and coordinate-sum-shift lemmas. Do not reassociate or recurse on vector addition. | indexed_real_vector_zero_sum_axis_decomposition, indexed_real_vector_zero_sum_axis_shift_projection, indexed_real_vector_zero_sum_axis_shift_coordinate_sum, Stdlib.Vectors.Vector.map2. | **New:** Translating a real vector along the head-only scalar axis changes only the scalar coordinate in its unique zero-sum plus axis decomposition. |
| `indexed_real_vector_zero_sum_axis_shift_injective` (lemma) | Apply coordinate sums to equal translated vectors, rewrite both shift-sum identities and cancel with Lra. | Stdlib.Logic.f_equal, indexed_real_vector_zero_sum_axis_shift_coordinate_sum, Stdlib.Lra. | **New:** Fixed-vector scalar-axis translation is injective. |
| `indexed_real_vector_zero_sum_projection_equal_iff_axis_shift` (lemma) | Choose the difference of totals and apply projection/sum pair-injectivity; converse follows by shift-invariance. | indexed_real_vector_zero_sum_projection_and_sum_injective, indexed_real_vector_zero_sum_axis_shift_projection/coordinate_sum, Stdlib.Ring. | **New:** Projection fibers are exactly affine head-axis translates. |
| `indexed_real_vector_zero_sum_axis_shift_zero_sum_iff` (lemma) | Unfold zero-sum membership and solve the shift-sum identity with Lra. | indexed_real_vector_zero_sum, indexed_real_vector_zero_sum_axis_shift_coordinate_sum, Stdlib.Lra. | **New:** Unique scalar normalization to a zero-sum vector. |
| `indexed_real_vector_zero_sum_projection_as_axis_normalization` (lemma) | Compare projection and coordinate sum via injectivity, using idempotence, zero-sum membership and shift formulas. | indexed_real_vector_zero_sum_projection_and_sum_injective/idempotent/zero_sum, indexed_real_vector_zero_sum_axis_shift_projection/coordinate_sum, Stdlib.Ring. | **New:** The canonical projection is the minus-total head-axis shift. |
| `indexed_real_vector_zero_sum_axis_shift_scalar_unique` (lemma) | Apply the coordinate-sum functional to a head-axis shift and use the existing exact shift-sum identity; finish scalar cancellation with Lra. | Stdlib.Logic.f_equal, indexed_real_vector_zero_sum_axis_shift_coordinate_sum, Stdlib.Lra. | **New:** The axis shift amount equals the difference of the vector coordinate totals. |
| `indexed_real_vector_zero_sum_projection_equal_iff_exact_axis_shift` (lemma) | Extract the existing affine-fiber witness and specialize it via the preceding scalar-uniqueness identity; converse repackages the explicit witness. | indexed_real_vector_zero_sum_projection_equal_iff_axis_shift, indexed_real_vector_zero_sum_axis_shift_scalar_unique, Stdlib.Logic. | **New:** Equal projection iff one exact signed sum-difference axis shift relates the vectors. |
| `indexed_real_vector_zero_sum_projection_equal_iff_unique_axis_shift` (lemma) | Reuse the existing affine-fiber existence theorem; identify any two scalar witnesses through the coordinate-sum difference using Lra. | indexed_real_vector_zero_sum_projection_equal_iff_axis_shift, indexed_real_vector_zero_sum_axis_shift_scalar_unique, Stdlib.Lra. | **New:** Equal projection iff exactly one axis-shift scalar exists. |
| `indexed_real_vector_zero_sum_projection_iff_unique_normalizing_shift` (lemma) | Rewrite the previously checked projector by the minus-total axis shift and directly apply the maintained axis-shift injectivity equivalence. | indexed_real_vector_zero_sum_projection_as_axis_normalization, indexed_real_vector_zero_sum_axis_shift_injective. | **New:** A head-axis shift equals the projector iff it cancels the coordinate sum. |
| `indexed_real_vector_zero_sum_translation_projection` (lemma) | Use projection additivity and the already proved fixed-point criterion to identify the projection of the zero-sum summand with itself. | indexed_real_vector_zero_sum_projection_add/fixed_iff_zero_sum, Stdlib.Vectors.Vector.map2. | **New:** Zero-sum translations are retained exactly in the projected component. |
| `indexed_real_vector_zero_sum_translation_coordinate_sum` (lemma) | Use shared coordinate-sum additivity and rewrite the zero-sum vector's total to zero; close by Ring. | indexed_real_vector_coordinate_sum_add, indexed_real_vector_zero_sum, Stdlib.Ring. | **New:** Adding a zero-sum direction leaves the scalar total unchanged. |
| `indexed_real_vector_zero_sum_translation_decomposition` (lemma) | Decompose the shifted input using the existing canonical splitting; rewrite the two coordinates by the preceding translation lemmas. | indexed_real_vector_zero_sum_axis_decomposition, indexed_real_vector_zero_sum_translation_projection/coordinate_sum, Stdlib.Vectors.Vector.map2. | **New:** Zero-sum translations modify only the zero-sum component of the direct decomposition. |
| `indexed_real_vector_zero_sum_iff_exists_unique_extension` (lemma) | Forward choose the maintained Vector.tl and apply the existing inverse-on-zero-sum, then extension injectivity for uniqueness. Converse transports extension zero-sum membership along equality. | indexed_real_vector_zero_sum_extension_inverse_on_zero_sum/injective/zero_sum, Stdlib.Logic.exists!, Vector.tl. | **New:** A vector is zero-sum iff it has exactly one tail-coordinate extension witness. |
| `indexed_real_vector_zero_sum_tail_add_linear` (lemma) | Combine existing zero-sum closure under addition with fst congruence of the product encoder's checked additive law; avoid new Vector.map2 recursion. | indexed_real_vector_zero_sum_closed_under_add, indexed_real_vector_tail_total_encode_add, Stdlib.Logic.f_equal, Stdlib.Datatypes.fst. | **New:** The tail inverse preserves addition on zero-sum inputs, with closure. |
| `indexed_real_vector_zero_sum_tail_scale_linear` (lemma) | Combine existing zero-sum closure under scaling with fst congruence of the product encoder's checked homogeneity; avoid new Vector.map induction. | indexed_real_vector_zero_sum_closed_under_scale, indexed_real_vector_tail_total_encode_scale, Stdlib.Logic.f_equal, Stdlib.Datatypes.fst. | **New:** The tail inverse preserves scalar multiplication on zero-sum inputs, with closure. |
| `indexed_real_vector_zero_sum_tail_add_reconstruct` (lemma) | Rewrite by the existing extension-add law and both inverse-on-zero-sum identities. | indexed_real_vector_zero_sum_extension_add/inverse_on_zero_sum, Vector.map2. | **New:** Adding tails then extending reconstructs the sum of two zero-sum vectors. |
| `indexed_real_vector_zero_sum_tail_scale_reconstruct` (lemma) | Rewrite by the existing extension-scale law and inverse-on-zero-sum identity. | indexed_real_vector_zero_sum_extension_scale/inverse_on_zero_sum, Vector.map. | **New:** Scaling a tail then extending reconstructs scaling of its zero-sum vector. |
| `indexed_real_vector_zero_sum_mixed_translation_projection` (lemma) | Compose the established scalar-axis projection invariance with zero-sum translation equivariance, with no vector induction. | indexed_real_vector_zero_sum_axis_shift_projection, indexed_real_vector_zero_sum_translation_projection, Stdlib.Vectors.Vector.map2. | **New:** Projection of a mixed zero-sum/axis translation depends only on the zero-sum shift. |
| `indexed_real_vector_zero_sum_mixed_translation_coordinate_sum` (lemma) | Compose the scalar-axis total-shift identity with zero-sum total invariance, with no fold duplication. | indexed_real_vector_zero_sum_axis_shift_coordinate_sum, indexed_real_vector_zero_sum_translation_coordinate_sum. | **New:** Mixed translation alters the coordinate total by exactly the axis scalar. |
| `indexed_real_vector_zero_sum_mixed_translation_decomposition` (lemma) | Apply canonical projection-plus-axis decomposition to the mixed shift and rewrite the two components by the preceding lemmas. | indexed_real_vector_zero_sum_axis_decomposition, indexed_real_vector_zero_sum_mixed_translation_projection/coordinate_sum. | **New:** An explicit normal form for both independent affine translation coordinates. |
| `indexed_real_vector_zero_sum_mixed_translation_zero_sum_iff` (lemma) | Instantiate the established scalar-axis zero-sum iff on the zero-sum-shifted base and replace its sum using maintained invariance. | indexed_real_vector_zero_sum_axis_shift_zero_sum_iff, indexed_real_vector_zero_sum_translation_coordinate_sum. | **New:** The original negative coordinate total remains the unique normalizing scalar. |
| `indexed_real_vector_zero_sum_mixed_translation_normalization_iff` (lemma) | Rewrite the projected target by existing zero-sum shift equivariance and apply the unique axis normalization iff; simplify totals. | indexed_real_vector_zero_sum_translation_projection, indexed_real_vector_zero_sum_projection_iff_unique_normalizing_shift, indexed_real_vector_zero_sum_translation_coordinate_sum. | **New:** The mixed translate equals its projected component iff the scalar cancels the original total. |
| `indexed_real_vector_zero_sum_axis_pair_unique_components` (lemma) | Apply the maintained axis-sum uniqueness criterion to one representative; rewrite its projected and total coordinates using those of the other, avoiding a separate f_equal/reduction proof. | indexed_real_vector_zero_sum_axis_sum_unique, indexed_real_vector_zero_sum_axis_sum_coordinates, Stdlib.Logic.eq_sym. | **New:** Explicit componentwise uniqueness of zero-sum and scalar-axis coordinates. |
| `indexed_real_vector_zero_sum_axis_unique_decomposition` (lemma) | Choose the canonical projection and coordinate sum; apply existing decomposition and axis-sum inverse to prove uniqueness of any alternative components. | indexed_real_vector_zero_sum_axis_decomposition/axis_sum_unique, indexed_real_vector_zero_sum_projection_zero_sum. | **New:** Every nonempty real vector has a unique zero-sum-plus-axis decomposition. |
| `indexed_real_vector_zero_sum_axis_pair_add_coordinates` (lemma) | Combine projection-add and coordinate-sum-add laws, then substitute the maintained axis-sum coordinates of both summands. | indexed_real_vector_zero_sum_projection_add, indexed_real_vector_coordinate_sum_add, indexed_real_vector_zero_sum_axis_sum_coordinates. | **New:** The two components of a sum are sums of the corresponding components. |
| `indexed_real_vector_zero_sum_axis_pair_scale_coordinates` (lemma) | Apply projection-scale and coordinate-sum-scale laws, then the previously checked axis-sum coordinate facts. | indexed_real_vector_zero_sum_projection_scale, indexed_real_vector_coordinate_sum_scale, indexed_real_vector_zero_sum_axis_sum_coordinates. | **New:** Real scaling acts componentwise on zero-sum and total coordinates. |
| `indexed_real_vector_zero_sum_axis_pair_add_reconstruct` (lemma) | Reuse canonical reconstruction uniqueness on the pair-add coordinate law and zero-sum closure under addition; no vector associativity proof. | indexed_real_vector_zero_sum_axis_sum_unique, indexed_real_vector_zero_sum_axis_pair_add_coordinates, indexed_real_vector_zero_sum_closed_under_add. | **New:** Reconstruction of summed components agrees with vector addition. |
| `indexed_real_vector_zero_sum_axis_pair_scale_reconstruct` (lemma) | Reuse canonical reconstruction uniqueness on the pair-scale coordinate law and zero-sum closure under scaling; no component recursion. | indexed_real_vector_zero_sum_axis_sum_unique, indexed_real_vector_zero_sum_axis_pair_scale_coordinates, indexed_real_vector_zero_sum_closed_under_scale. | **New:** Reconstruction of scaled components agrees with vector scaling. |
| `indexed_basis_centered_sample_vector_sum_zero` (theorem) | Transport generic finite sum of vector entries through standard map theorem to existing centered-score sum | indexed_basis_centered_sample_vector_to_list, FiniteSum.finite_sum_map, indexed_basis_centered_weighted_score_sum_zero | **New:** all normalized typed sample-output vectors have zero coordinate sum |
| `indexed_basis_centered_sample_vector_in_zero_sum` (theorem) | Unfold shared predicate/functional and reuse the existing normalized centered-output coordinate-sum-zero result | indexed_real_vector_zero_sum, indexed_real_vector_coordinate_sum, indexed_basis_centered_sample_vector_sum_zero | **New:** normalized centered sample evaluator maps every direction into typed zero-sum family |
| `indexed_basis_centered_sample_vector_omits_nonzero_constant` (theorem) | Combine already checked zero-sum sample output membership with the generic positive-length nonzero-constant exclusion criterion | indexed_basis_centered_sample_vector_in_zero_sum, indexed_real_vector_zero_sum_const_nonzero, Vector.const | **New:** under unit mass and nonempty sample list, a centered output is never a nonzero constant vector, even for signed weights |
| `normalized_total_mass_implies_samples_nonempty` (lemma) | Expand the existing shared sum only on the empty list and refute mass 0 = 1 by Lra | FiniteSum.finite_sum, Stdlib.List.fold_right/map, Stdlib.Lra | **New:** normalized mass excludes an empty sample enumeration, without sign restrictions |
| `indexed_basis_centered_sample_vector_equal_iff_list_tails_equal` (theorem) | Directly apply all-length zero-sum list-tail iff on normalized centered outputs | indexed_basis_centered_sample_vector_in_zero_sum, indexed_real_vector_zero_sum_equal_iff_list_tails_equal | **New:** full centered outputs agree iff their post-first list coordinates agree |
| `indexed_basis_centered_sample_vector_zero_iff_list_tail_zero` (theorem) | Directly apply generalized list-tail zero iff to normalized centered outputs | indexed_basis_centered_sample_vector_in_zero_sum, indexed_real_vector_zero_sum_list_tail_zero_iff | **New:** centered output vanishes iff shortened list of components is zero |
| `indexed_basis_centered_sample_vector_omits_nonzero_constant_normalized` (theorem) | Derive successor-length witness in a separate proposition by empty/cons cases, preserving dependent vector typing, then reuse the checked exclusion theorem | normalized_total_mass_implies_samples_nonempty, indexed_basis_centered_sample_vector_omits_nonzero_constant, Stdlib.List | **New:** nonzero constant output excluded under unit mass without a redundant length witness |
| `indexed_basis_centered_sample_vector_single_sample_zero` (theorem) | Shared singleton sum-zero iff plus new typed vector/list-score equivalence | FiniteSum.finite_sum_singleton_zero_iff, indexed_basis_centered_sample_vector_zero_iff_all_sample_scores_zero, indexed_basis_centered_weighted_score_sum_zero | **Refactored:** no local singleton sum or dependent vector induction |
| `indexed_basis_centered_weighted_score_two_samples_opposite` (theorem) | Normalize sample-list sum-zero using generic pair iff | indexed_basis_centered_weighted_score_sum_zero, FiniteSum.finite_sum_pair_zero_iff_opposite | **New:** two centered scores are additive opposites |
| `indexed_basis_centered_sample_vector_two_samples_opposite` (theorem) | Vector-to-list map plus prior paired-score cancellation | indexed_basis_centered_sample_vector_to_list, indexed_basis_centered_weighted_score_two_samples_opposite, Stdlib.Lra | **New:** complete two-sample vector output equals [s; -s] |
| `indexed_basis_centered_sample_vector_two_samples_zero_iff_first_score_zero` (theorem) | Two-element list membership plus existing opposite-score and vector-zero equivalences | indexed_basis_centered_sample_vector_zero_iff_all_sample_scores_zero, indexed_basis_centered_weighted_score_two_samples_opposite, Stdlib.List.In, Lra | **New:** first centered score completely tests two-sample output nullity |
| `indexed_basis_covariance_not_positive_definite_single_sample` (theorem) | Nonzero constant-one typed coefficient witness contradicts singleton output zero via positivity/kernel criterion | indexed_basis_covariance_positive_definite_iff_sample_vector_detects_nonzero, indexed_basis_centered_sample_vector_single_sample_zero, VectorSpec.to_list_const, Stdlib.List.hd, Lra | **New:** covariance of normalized singleton cannot be positive definite for nonempty basis |
| `indexed_basis_covariance_positive_definite_two_samples_iff_first_score_detects_nonzero` (theorem) | Compose typed positive-definite/output test with the two-sample first-score kernel iff | indexed_basis_covariance_positive_definite_iff_sample_vector_detects_nonzero, indexed_basis_centered_sample_vector_two_samples_zero_iff_first_score_zero | **New:** two-sample covariance is positive definite iff every nonzero coefficient direction gives a nonzero first centered score |
| `indexed_basis_covariance_quadratic_zero_iff_two_samples_first_score_zero` (theorem) | Compose existing quadratic/output and two-sample first-centered-score equivalences | indexed_basis_covariance_quadratic_zero_iff_sample_vector_zero, indexed_basis_centered_sample_vector_two_samples_zero_iff_first_score_zero, tauto | **New:** zero quadratic iff first centered score zero with two samples |
| `indexed_basis_covariance_quadratic_single_sample_zero` (theorem) | Transport singleton typed output degeneracy via quadratic/output iff | indexed_basis_centered_sample_vector_single_sample_zero, indexed_basis_covariance_quadratic_zero_iff_sample_vector_zero | **New:** single normalized sample has zero covariance quadratic in all directions |
| `indexed_basis_covariance_quadratic_scale` (theorem) | Full quadratic scaling through typed vector/list bridge and preexisting variance scaling | indexed_basis_covariance_quadratic_as_variance, VectorSpec.to_list_map, weighted_basis_sum_coefficients_scale, variance_extensional, variance_of_scaled_score | **New:** exact Q(a*c)=a^2 Q(c) without sign restrictions on sample weights |
| `indexed_basis_covariance_quadratic_nonzero_scale_zero_iff_unit_mass` (theorem) | Simplify exact quadratic homogeneity and use standard real zero-product splitting | indexed_basis_covariance_quadratic_scale, Reals.Rmult_integral, Ring | **New:** nonzero coefficient scaling preserves quadratic nullity even for signed normalized weights |
| `indexed_basis_covariance_quadratic_zero_nonzero_scale_iff` (theorem) | **Refactored:** direct legacy-compatible wrapper of unit-mass-only algebraic scaling equivalence; redundant kernel transports eliminated | indexed_basis_covariance_quadratic_nonzero_scale_zero_iff_unit_mass, indexed_basis_covariance_quadratic_scale | **Simplified:** preserved exact old statement and assumptions while reducing proof to one library-backed theorem application |
| `indexed_basis_covariance_quadratic_add_polarization` (theorem) | Full coefficient-vector additivity through shared weighted-score and variance-of-sum identities | indexed_basis_covariance_quadratic_as_variance, indexed_vector_to_list_map2_add, weighted_basis_sum_coefficients_zip_add, VectorSpec.length_to_list, variance_extensional, variance_of_two_score_sum | **New:** exact covariance quadratic polarization for two typed coefficient directions |
| `indexed_basis_covariance_cross_cauchy_schwarz_squared` (theorem) | Replace typed quadratic by previously verified variance and instantiate the generic finite Cauchy-Schwarz inequality | indexed_basis_covariance_quadratic_as_variance, finite_covariance_cauchy_schwarz_squared | **New:** squared covariance of typed composite scores bounded by the product of their indexed quadratic values |
| `indexed_basis_covariance_bilinear_symmetric` (theorem) | Thin wrapper over covariance symmetry; no score or matrix re-expansion | covariance_symmetric, indexed_basis_covariance_bilinear_form | **New:** typed coefficient pairing is symmetric |
| `indexed_basis_covariance_bilinear_scale_first` (theorem) | Transport coefficient scaling through standard vector-to-list law and score homogeneity, then reuse finite covariance scaling | VectorSpec.to_list_map, weighted_basis_sum_coefficients_scale, covariance_extensional, covariance_scale_first | **New:** first-argument scalar linearity |
| `indexed_basis_covariance_bilinear_add_first` (theorem) | Standard map2/list bridge, shared score zip-add, covariance extensionality and generic covariance additivity | indexed_vector_to_list_map2_add, weighted_basis_sum_coefficients_zip_add, VectorSpec.length_to_list, covariance_extensional, covariance_add_first | **New:** first-argument additive linearity |
| `indexed_basis_covariance_bilinear_scale_second` (theorem) | Symmetry reduces to first-argument homogeneity; no duplicate coefficient transport | indexed_basis_covariance_bilinear_symmetric, indexed_basis_covariance_bilinear_scale_first | **New:** second-argument scalar linearity |
| `indexed_basis_covariance_bilinear_add_second` (theorem) | Symmetry reduces to checked first-argument additivity; no additional list induction | indexed_basis_covariance_bilinear_symmetric, indexed_basis_covariance_bilinear_add_first | **New:** second-argument additive linearity |
| `indexed_basis_covariance_bilinear_diagonal` (theorem) | Identify self-covariance with variance and reuse original indexed quadratic bridge | indexed_basis_covariance_quadratic_as_variance, variance | **New:** B(c,c)=Q(c) under unit mass |
| `indexed_basis_covariance_bilinear_polarization` (theorem) | Thin pairing wrapper of existing typed quadratic polarization theorem | indexed_basis_covariance_quadratic_add_polarization | **New:** Q(u+v)=Q(u)+Q(v)+2 B(u,v) |
| `indexed_basis_covariance_bilinear_cauchy_schwarz_squared` (theorem) | Thin pairing wrapper over checked typed finite covariance Cauchy-Schwarz | indexed_basis_covariance_cross_cauchy_schwarz_squared | **New:** B(u,v)^2<=Q(u)Q(v) with nonnegative normalized weights |
| `indexed_basis_covariance_bilinear_radical_of_sample_constant` (theorem) | Sampled covariance extensionality replaces the composite by a constant, then normalized constant-first covariance vanishes. | covariance_extensional_on_samples, covariance_with_constant_first. | **New:** Signed-weight sample-constant composite lies in covariance radical. |
| `indexed_basis_covariance_bilinear_radical_closed_under_scale` (theorem) | One rewrite by established first-argument scalar homogeneity and zero substitution | indexed_basis_covariance_bilinear_scale_first, Stdlib.Ring | **New:** algebraic radical closed under all scalar multiplication |
| `indexed_basis_covariance_bilinear_radical_closed_under_add` (theorem) | One rewrite by established first-argument additivity and zero substitutions | indexed_basis_covariance_bilinear_add_first, Stdlib.Ring | **New:** algebraic radical closed under coefficient addition |
| `indexed_basis_covariance_quadratic_zero_iff_bilinear_radical` (theorem) | Compose existing orthogonality to arbitrary scores with diagonal self-pairing | indexed_basis_covariance_quadratic_zero_iff_uncorrelated_with_every_score, indexed_basis_covariance_bilinear_diagonal | **New:** finite covariance quadratic nullspace equals the typed bilinear radical |
| `indexed_basis_score_has_typed_coordinate_representation` (lemma) | Induct on basis to construct a typed coordinate selector with Vector.cons 1/0 and Vector.const 0. | Vector.cons/const, VectorSpec.to_list_const, weighted_basis_sum_repeat_zero, ring. | **New:** Each listed basis score has a typed composite representation. |
| `indexed_basis_covariance_bilinear_radical_iff_uncorrelated_with_basis_unconditional` (theorem) | Unit basis selectors prove one direction; unconditional second-slot covariance linearity and finite-sum zero prove the other. | covariance_of_general_weighted_second_unconditional, basis_of_combine, FiniteSum.finite_sum_ext_in/zero. | **New:** Arbitrary-weight radical iff orthogonality to every basis score. |
| `indexed_basis_bounded_covariance_row_kernel_iff_uncorrelated_with_basis_unconditional` (theorem) | Row-dot covariance identity and symmetry; existing bounded-index surjectivity and vector-list nth_error membership. | covariance_with_weighted_basis_as_row_dot, indexed_basis_covariance_matrix_row_has_bounded_index, vector_of_list_nth_error. | **New:** Arbitrary-weight row kernel iff orthogonality to every basis score. |
| `indexed_basis_covariance_bilinear_radical_iff_row_kernel_unconditional` (theorem) | Compose the radical-vs-basis and row-vs-basis equivalences with tauto. | Both new unconditional basis-orthogonality bridges. | **New:** Algebraic radical iff row kernel without sign/mass conditions. |
| `indexed_basis_covariance_bilinear_radical_iff_row_kernel` (theorem) | **Refactored:** Keep original API but delegate to unconditional algebraic radical-row equivalence. | indexed_basis_covariance_bilinear_radical_iff_row_kernel_unconditional. | **Refactored:** Remove unnecessary quadratic-nullity positivity bridge. |
| `indexed_basis_covariance_positive_definite_iff_bilinear_radical_trivial` (theorem) | **Refactored:** Reuse positivity iff trivial named row kernel, but obtain radical/row equality unconditionally. | indexed_basis_covariance_positive_definite_iff_named_row_kernel_trivial, indexed_basis_covariance_bilinear_radical_iff_row_kernel_unconditional. | **Refactored:** Probability assumptions now used only where positivity requires them. |
| `indexed_basis_covariance_bilinear_radical_zero_coefficients` (theorem) | Standard zero-vector list and existing weighted-score zero identity, covariance extensionality and homogeneity | VectorSpec.to_list_const, weighted_basis_sum_repeat_zero, covariance_extensional, covariance_scale_first, Stdlib.Ring | **New:** canonical typed coefficient zero lies in covariance radical even with signed unnormalized weights |
| `indexed_basis_covariance_bilinear_radical_nonzero_scale_iff` (theorem) | First-argument covariance homogeneity and standard real zero-product elimination | indexed_basis_covariance_bilinear_scale_first, Stdlib.Reals.Rmult_integral, Stdlib.Ring | **New:** radical membership invariant under every nonzero scalar, without probability assumptions |
| `indexed_basis_bounded_covariance_row_kernel_zero_unconditional` (theorem) | Zero-vector radical theorem transported by the unconditional radical-to-row kernel iff. | indexed_basis_covariance_bilinear_radical_zero_coefficients, indexed_basis_covariance_bilinear_radical_iff_row_kernel_unconditional. | **New:** Every finite covariance row annihilates the zero vector without mass or sign restrictions. |
| `indexed_basis_bounded_covariance_row_kernel_closed_under_add_unconditional` (theorem) | Convert two row members to radical, apply radical addition closure, convert the sum back. | indexed_basis_covariance_bilinear_radical_closed_under_add, indexed_basis_covariance_bilinear_radical_iff_row_kernel_unconditional. | **New:** Arbitrary-weight row-null addition closure. |
| `indexed_basis_bounded_covariance_row_kernel_closed_under_scale_unconditional` (theorem) | Apply radical scaling closure between two unconditional radical/row transports. | indexed_basis_covariance_bilinear_radical_closed_under_scale, indexed_basis_covariance_bilinear_radical_iff_row_kernel_unconditional. | **New:** Arbitrary-weight row-null scalar closure. |
| `indexed_basis_bounded_covariance_row_kernel_nonzero_scale_iff_unconditional` (theorem) | Compose radical rescaling iff with two unconditional radical/row iff applications using tauto. | indexed_basis_covariance_bilinear_radical_nonzero_scale_iff, indexed_basis_covariance_bilinear_radical_iff_row_kernel_unconditional. | **New:** Nonzero rescaling cannot alter row-kernel membership, without positivity. |
| `indexed_basis_covariance_bilinear_radical_iff_sample_vector_zero` (theorem) | Compose the existing typed zero-quadratic iff radical and zero-quadratic iff sample-output-zero equivalences | indexed_basis_covariance_quadratic_zero_iff_bilinear_radical, indexed_basis_covariance_quadratic_zero_iff_sample_vector_zero, tauto | **New:** radical exactly equals the kernel of the concrete centered-sample output vector under finite probability assumptions |
| `indexed_basis_covariance_bilinear_add_radical_first_invariant` (theorem) | Reuse first-argument additivity and radical orthogonality; ordinary zero-summand ring reduction | indexed_basis_covariance_bilinear_add_first, indexed_basis_covariance_bilinear_radical, Stdlib.Ring | **New:** adding radical coefficients leaves pairing's first argument unchanged |
| `indexed_basis_covariance_bilinear_add_radical_second_invariant` (theorem) | Reduce second argument to previously checked first-argument invariance by symmetry | indexed_basis_covariance_bilinear_symmetric, indexed_basis_covariance_bilinear_add_radical_first_invariant | **New:** radical shifts are invisible in either argument |
| `indexed_basis_covariance_bilinear_add_radicals_both_invariant` (theorem) | Compose the maintained two slotwise radical-shift laws, without expanding the covariance pairing | indexed_basis_covariance_bilinear_add_radical_first_invariant, indexed_basis_covariance_bilinear_add_radical_second_invariant, Stdlib.Vectors.Vector.map2 | **New:** arbitrary-weight B(left+r,right+s)=B(left,right) for independently radical r and s |
| `indexed_basis_covariance_quadratic_add_radical_invariant` (theorem) | **Refactored:** diagonal self-pairing followed by one two-sided radical-shift law instead of two separate rewrites | indexed_basis_covariance_bilinear_diagonal, indexed_basis_covariance_bilinear_add_radicals_both_invariant | **Refactored:** unchanged signed-weight-compatible Q(c+r)=Q(c) statement |
| `indexed_basis_centered_sample_vector_add_radical_invariant` (theorem) | Compose radical/zero-sample-output iff with existing typed output additivity and standard coordinate extensionality | indexed_basis_covariance_bilinear_radical_iff_sample_vector_zero, indexed_basis_centered_sample_vector_add, VectorSpec.eq_nth_iff/nth_map2/const_nth, Ring | **New:** coefficient radical shifts leave the complete typed sample output invariant |
| `indexed_basis_centered_sample_vector_add_radical_iff` (theorem) | **Refactored after Rocq tactic failure:** assert explicit indexed coordinate equality, then cancel; use preceding radical-shift theorem for sufficiency | indexed_basis_centered_sample_vector_nth, indexed_basis_centered_sample_evaluation_add, indexed_basis_covariance_bilinear_radical_iff_sample_vector_zero, indexed_basis_centered_sample_vector_add_radical_invariant, VectorSpec.eq_nth_iff/const_nth, Lra | **New:** full sample-output invariance under a shift iff that shift lies in covariance radical |
| `indexed_basis_covariance_bilinear_first_shift_iff_radical` (theorem) | First-argument additivity and real cancellation give necessity; prior radical-shift invariance gives sufficiency | indexed_basis_covariance_bilinear_add_first, indexed_basis_covariance_bilinear_add_radical_first_invariant, Stdlib.Lra | **New:** arbitrary-weight first-slot universal shift-invariance iff radical |
| `indexed_basis_covariance_bilinear_second_shift_iff_radical` (theorem) | Reduce second-slot universal invariance to first-slot iff through symmetry, reuse second-slot invariance | indexed_basis_covariance_bilinear_symmetric, indexed_basis_covariance_bilinear_first_shift_iff_radical, indexed_basis_covariance_bilinear_add_radical_second_invariant | **New:** arbitrary-weight second-slot universal shift-invariance iff radical |
| `indexed_basis_covariance_bilinear_radical_add_radical_iff` (theorem) | Rewrite both implications using established first-slot covariance radical-shift invariance; avoid vector/list induction | indexed_basis_covariance_bilinear_add_radical_first_invariant, indexed_basis_covariance_bilinear_radical, Stdlib.Vectors.Vector.map2 | **New:** radical(c+r) iff radical(c) whenever radical(r), even for signed unnormalized weights |
| `indexed_basis_bounded_covariance_row_kernel_add_kernel_iff_unconditional` (theorem) | Transport three row predicates to radical, apply its coset-shift iff and tauto. | indexed_basis_covariance_bilinear_radical_add_radical_iff, indexed_basis_covariance_bilinear_radical_iff_row_kernel_unconditional. | **New:** Row-kernel membership invariant under row-kernel shifts, even for signed weights. |
| `indexed_real_vector_equal_iff_signed_difference_zero` (lemma) | Factor out generic equal-length real-vector cancellation by VectorSpec.eq_nth_iff and coordinate nth_map2/nth_map laws | Stdlib.Vectors.VectorSpec.eq_nth_iff/nth_map2/nth_map/const_nth, Stdlib.Ring, Stdlib.Lra | **New reusable helper:** x=y iff x+(-1)*y=0 for all finite real-vector dimensions |
| `indexed_real_vector_zero_iff_to_list_repeat` (lemma) | Reuse Stdlib VectorSpec.to_list_const and to_list_inj; no custom induction or real-vector conversion | Stdlib.Vectors.VectorSpec.to_list_const/to_list_inj, Stdlib.List.repeat | **New reusable helper:** typed real zero vector iff its standard coefficient list is repeat 0 |
| `indexed_real_vector_equality_stable` (lemma) | Use VectorSpec.eq_nth_iff and the maintained Req_dec real equality dichotomy at each bounded coordinate | Stdlib.Reals.Req_dec, Stdlib.Vectors.VectorSpec.eq_nth_iff, Vector.nth | **New reusable helper:** double-negation stability of equality of length-indexed real vectors; no new axiom declarations |
| `indexed_basis_centered_sample_vector_equal_iff_difference_zero` (theorem) | **Refactored:** rewrite full sample evaluator through existing additivity/scaling, then apply generic vector difference-zero iff equality | indexed_basis_centered_sample_vector_add/scale, indexed_real_vector_equal_iff_signed_difference_zero | **Refactored:** theorem statement unchanged; removed duplicated coordinate-extensionality proof |
| `indexed_basis_centered_sample_vector_equal_iff_difference_radical` (theorem) | Compose signed-difference zero-output iff with maintained radical/zero-output equivalence | indexed_basis_centered_sample_vector_equal_iff_difference_zero, indexed_basis_covariance_bilinear_radical_iff_sample_vector_zero, Stdlib.Logic.tauto | **New:** normalized nonnegative finite sample outputs agree iff their signed coefficient difference lies in the covariance radical |
| `indexed_basis_covariance_positive_definite_separates_sample_outputs` (theorem) | **Refactored:** detect the nonzero signed coefficient difference with the preexisting positive-definite sample-vector detection criterion, then use the already checked equal-output iff zero-difference-output law | indexed_basis_covariance_positive_definite_iff_sample_vector_detects_nonzero, indexed_basis_centered_sample_vector_equal_iff_difference_zero | **Refactored:** original separation statement and hypotheses preserved; radical detour removed |
| `indexed_basis_centered_sample_vector_equal_iff_difference_quadratic_zero` (theorem) | Compose existing equality iff zero evaluation of signed difference with quadratic-zero iff sample-vector-zero | indexed_basis_centered_sample_vector_equal_iff_difference_zero, indexed_basis_covariance_quadratic_zero_iff_sample_vector_zero, Stdlib.Logic.tauto | **New:** equal centered outputs iff signed difference has zero covariance quadratic under normalized nonnegative weights |
| `indexed_basis_centered_sample_vector_equal_iff_difference_row_kernel` (theorem) | Compose equality iff radical of signed difference with established radical iff bounded covariance row-kernel | indexed_basis_centered_sample_vector_equal_iff_difference_radical, indexed_basis_covariance_bilinear_radical_iff_row_kernel, Stdlib.Logic.tauto | **New:** coincident centered outputs iff signed difference belongs to the bounded covariance row kernel |
| `indexed_basis_covariance_quadratic_difference_positive_iff_distinct_outputs` (theorem) | Use established quadratic nonnegativity and equality iff zero quadratic, discharge strict positivity with Stdlib.Lra | indexed_basis_covariance_quadratic_nonnegative, indexed_basis_centered_sample_vector_equal_iff_difference_quadratic_zero, Stdlib.Lra | **New:** covariance quadratic of difference is strictly positive iff complete centered outputs differ |
| `indexed_basis_centered_sample_vector_equal_iff_difference_covariance_orthogonal_first` (theorem) | Unfold only the already-checked covariance radical predicate after applying the existing sample-output equality iff signed-difference radical lemma | indexed_basis_centered_sample_vector_equal_iff_difference_radical, indexed_basis_covariance_bilinear_radical | **New:** equal outputs iff the signed difference pairs to zero against every test in the first slot |
| `indexed_basis_centered_sample_vector_equal_iff_difference_covariance_orthogonal_second` (theorem) | Compose the previous first-slot criterion with covariance symmetry in each direction | indexed_basis_centered_sample_vector_equal_iff_difference_covariance_orthogonal_first, indexed_basis_covariance_bilinear_symmetric | **New:** equal outputs iff every test pairs to zero against the signed difference in the second slot |
| `indexed_basis_covariance_bilinear_self_nonnegative` (theorem) | Rewrite diagonal pairing to the established nonnegative indexed quadratic | indexed_basis_covariance_bilinear_diagonal, indexed_basis_covariance_quadratic_nonnegative | **New:** PSD self-pairing for arbitrary same-basis vectors under normalized nonnegative weights |
| `indexed_basis_covariance_bilinear_self_zero_iff_radical` (theorem) | Rewrite bilinear self-pairing to Q and reuse checked quadratic zero iff radical | indexed_basis_covariance_bilinear_diagonal, indexed_basis_covariance_quadratic_zero_iff_bilinear_radical | **New:** zero bilinear self-pairing exactly characterizes radical membership |
| `indexed_basis_covariance_bilinear_self_positive_iff_not_radical` (theorem) | Compose new bilinear PSD and zero-iff-radical laws with Stdlib.Lra | indexed_basis_covariance_bilinear_self_nonnegative, indexed_basis_covariance_bilinear_self_zero_iff_radical, Stdlib.Lra | **New:** strictly positive self-covariance iff direction is outside the radical |
| `indexed_basis_covariance_bilinear_cauchy_schwarz_self_squared` (theorem) | Rewrite both PSD diagonal factors to existing Q and reuse checked Cauchy-Schwarz | indexed_basis_covariance_bilinear_diagonal, indexed_basis_covariance_bilinear_cauchy_schwarz_squared | **New:** B(u,v)^2<=B(u,u)B(v,v) entirely in the bilinear interface |
| `indexed_basis_covariance_positive_definite_iff_strict_bilinear_self` (theorem) | Compose positive definite iff trivial radical with strict self-pairing positivity iff not radical for every typed nonzero direction | indexed_basis_covariance_positive_definite_iff_bilinear_radical_trivial, indexed_basis_covariance_bilinear_self_positive_iff_not_radical | **New:** positive definiteness iff every nonzero coefficient has strictly positive bilinear self-covariance |
| `indexed_basis_covariance_bilinear_difference_positive_iff_distinct_outputs` (theorem) | **Refactored and relocated after generic PSD self-pairing:** compose self-positive iff not radical with equal-output iff difference-radical, then tauto; preserve exact original proposition | indexed_basis_covariance_bilinear_self_positive_iff_not_radical, indexed_basis_centered_sample_vector_equal_iff_difference_radical, Stdlib.Logic.tauto | **Refactored:** same strict self-covariance iff distinct complete centered sample outputs statement, without a redundant quadratic conversion |
| `indexed_basis_covariance_positive_definite_iff_sample_vector_separates_coefficients` (theorem) | Prove a bidirectional nonzero-direction detection vs distinct-coefficient-output separation equivalence using generic signed-difference cancellation, zero list characterization and zero-output preservation | indexed_real_vector_equal_iff_signed_difference_zero, indexed_real_vector_zero_iff_to_list_repeat, indexed_basis_covariance_positive_definite_iff_sample_vector_detects_nonzero, indexed_basis_centered_sample_vector_equal_iff_difference_zero, indexed_basis_centered_sample_vector_zero_coefficients, VectorSpec.to_list_const | **New:** positive definiteness iff the centered sample evaluator distinguishes every pair of unequal typed coefficient vectors, without classical equality axioms |
| `indexed_basis_covariance_positive_definite_iff_sample_vector_injective` (theorem) | Compose the checked separation equivalence with a generic Stdlib-based real-vector equality stability lemma; reverse implication directly contradicts separation failure | indexed_basis_covariance_positive_definite_iff_sample_vector_separates_coefficients, indexed_real_vector_equality_stable, Stdlib.Logic | **New:** positive definiteness iff complete centered sample-vector equality implies coefficient equality for every typed pair |

| `indexed_basis_covariance_positive_definite_iff_sample_list_tail_injective` (theorem) | Compose previous positive-definiteness/full-output-injectivity equivalence and normalized list-tail equality equivalence | indexed_basis_covariance_positive_definite_iff_sample_vector_injective, indexed_basis_centered_sample_vector_equal_iff_list_tails_equal | **New:** finite strict covariance positive definiteness iff the shortened centered evaluator is injective |

| `indexed_basis_covariance_quadratic_zero_iff_sample_list_tail_zero` (theorem) | Obtain the already proven quadratic-form-zero iff complete centered output is zero and the normalized centered-output-zero iff list-tail-zero propositions. Compose the two iff statements with Stdlib.Logic.tauto rather than expanding the quadratic form. | indexed_basis_covariance_quadratic_zero_iff_sample_vector_zero, indexed_basis_centered_sample_vector_zero_iff_list_tail_zero and Stdlib.Logic.tauto. | **New:** Exact covariance quadratic-form nullity from the shortened centered sample output. |
| `indexed_basis_covariance_bilinear_radical_iff_sample_list_tail_zero` (theorem) | Compose the established radical iff full sample-output-zero bridge and the general normalized centered-output list-tail-zero iff by tauto. Avoid recalculating either bilinear covariance entries or centered sample values. | indexed_basis_covariance_bilinear_radical_iff_sample_vector_zero, indexed_basis_centered_sample_vector_zero_iff_list_tail_zero and Stdlib.Logic.tauto. | **New:** Covariance bilinear radical membership from zero shortened centered output. |
| `indexed_basis_bounded_covariance_row_kernel_iff_sample_list_tail_zero` (theorem) | Compose the checked quadratic-form-zero iff named row-kernel bridge with the just established quadratic-form-zero iff shortened centered-output test. This avoids repeating the named sample-kernel or matrix-row expansions. | indexed_basis_covariance_quadratic_zero_iff_named_row_kernel, indexed_basis_covariance_quadratic_zero_iff_sample_list_tail_zero, Stdlib.Logic.tauto. | **New:** Named finite covariance-row kernel membership via shortened sample output. |
| `indexed_basis_centered_sample_vector_equal_iff_difference_list_tail_zero` (theorem) | Combine the established full output equality iff signed-difference output zero proposition with the general normalized centered-output zero iff ordinary list tail zero proposition. Use tauto without any new vector arithmetic. | indexed_basis_centered_sample_vector_equal_iff_difference_zero, indexed_basis_centered_sample_vector_zero_iff_list_tail_zero, Stdlib.Vectors.Vector.map/map2, Stdlib.Logic.tauto. | **New:** Equal finite centered sample outputs via the shortened image of the signed coefficient difference. |
| `indexed_basis_covariance_positive_definite_iff_sample_list_tail_detects_nonzero` (theorem) | Apply the existing positive-definiteness iff complete evaluator detects every nonzero coefficient. Transport each nonvanishing assertion via the checked normalized full-output-zero iff shortened-list-tail-zero statement in both directions. | indexed_basis_covariance_positive_definite_iff_sample_vector_detects_nonzero, indexed_basis_centered_sample_vector_zero_iff_list_tail_zero and Stdlib.Logic. | **New:** Strict covariance positive definiteness as zero-kernel detection by n-1 listed sample components. |
| `indexed_basis_affine_prefix_null_direction_to_list` (lemma) | Unfold only the standard Vector.cons prefix and use maintained VectorSpec.to_list_const for the zero tail. | Vector.to_list, VectorSpec.to_list_const, List.repeat. | **New:** Typed affine-null witness equals its ordinary coefficient list. |
| `indexed_basis_affine_prefix_null_direction_nonzero` (lemma) | Apply List.hd congruence to a hypothetical zero-list equality and refute 1=0 using Lra. | indexed_basis_affine_prefix_null_direction_to_list, Stdlib.List.hd, Stdlib.Logic.f_equal, Lra. | **New:** A null witness remains nonzero for any slope and tail dimension. |
| `indexed_basis_affine_prefix_weighted_score` (lemma) | Rewrite via typed-to-list bridge, expose the two prefix weights and reuse weighted_basis_sum_repeat_zero; finish with Ring. | weighted_basis_sum_repeat_zero, indexed_basis_affine_prefix_null_direction_to_list, Ring. | **New:** Affine dependence f=a*g+c makes the extended weighted score equal c. |
| `indexed_basis_affine_prefix_centered_sample_zero` (theorem) | Apply full centered-output-zero iff sampled-score-zero; use expectation extensionality and normalized constant expectation. | indexed_basis_centered_sample_vector_zero_iff_all_sample_scores_zero, indexed_basis_affine_prefix_weighted_score, expectation_extensional_on_samples, expectation_constant_normalized. | **New:** The affine prefix gives an exact centered sample-output kernel witness. |
| `indexed_basis_affine_prefix_covariance_quadratic_zero` (theorem) | Use indexed quadratic-as-variance, variance_extensional_on_samples and variance_of_constant_score_zero. | indexed_basis_covariance_quadratic_as_variance, indexed_basis_affine_prefix_weighted_score, variance_of_constant_score_zero. | **New:** Affinely dependent prefix yields zero covariance quadratic with arbitrary extra scores, including signed weights. |
| `indexed_basis_affine_prefix_covariance_not_positive_definite` (theorem) | Instantiate the existing positive-definiteness predicate with the nonzero witness and its zero quadratic; finish by Lra. | indexed_basis_covariance_positive_definite, indexed_basis_affine_prefix_null_direction_nonzero, indexed_basis_affine_prefix_covariance_quadratic_zero, Lra. | **New:** Adding other scores cannot restore strict covariance positive definiteness. |
| `indexed_basis_affine_prefix_covariance_radical_signed` (theorem) | Compose established affine-prefix weighted-score equality with the constant-score radical lemma. | indexed_basis_affine_prefix_weighted_score, indexed_basis_covariance_bilinear_radical_of_sample_constant. | **New:** Signed-weight affine-prefix witness is radical. |
| `indexed_basis_affine_prefix_covariance_radical` (theorem) | **Refactored:** Preserve public theorem assumptions, delegate to the signed-weight result. | indexed_basis_affine_prefix_covariance_radical_signed. | **Refactored:** Avoid unnecessary positivity-dependent quadratic bridge. |
| `indexed_basis_affine_prefix_covariance_row_kernel_signed` (theorem) | **Refactored:** Transport signed affine radical witness through unconditional radical-row equivalence. | indexed_basis_affine_prefix_covariance_radical_signed, indexed_basis_covariance_bilinear_radical_iff_row_kernel_unconditional. | **Refactored:** Unify radical and row-kernel proof paths. |
| `indexed_basis_affine_prefix_covariance_row_kernel` (theorem) | **Refactored:** Delegate original nonnegative-weight interface to stronger signed-weight row theorem. | indexed_basis_affine_prefix_covariance_row_kernel_signed. | **Refactored:** Algebraic row-dot proof replaces redundant positivity-dependent nullity bridge. |


| `covariance_two_samples_rank_one_factorization` (theorem) | Evaluate the shared two-sample FiniteSum fold, use unit mass to eliminate one weight, and close by ring. | FiniteSum.finite_sum, Stdlib.Lra/Ring. | **New:** Exact signed-weight two-sample covariance factors through score differences. |
| `covariance_two_samples_all_cross_minors_zero` (theorem) | Rewrite four covariances by the rank-one factorization, finish with ring. | covariance_two_samples_rank_one_factorization, Stdlib.Ring. | **New:** Every two-by-two covariance cross-product minor vanishes. |
| `indexed_basis_covariance_two_samples_all_minors_zero` (theorem) | Instantiate scalar cross-minor theorem at standard Fin-indexed covariance matrix entries. | indexed_basis_cross_covariance_matrix, covariance_two_samples_all_cross_minors_zero, Vector.nth/of_list. | **New:** Dimension-safe all-minors-zero certificate. |
| `indexed_basis_covariance_bilinear_two_samples_factorization` (theorem) | Unfold existing bilinear covariance and instantiate scalar product factorization. | indexed_basis_covariance_bilinear_form, covariance_two_samples_rank_one_factorization. | **New:** Composite covariance pairing factors through a single score contrast. |
| `indexed_basis_two_samples_row_kernel_iff_all_contrast_products_zero` (theorem) | Compose unconditional row/basis-orthogonality iff with rank-one factorization. | indexed_basis_bounded_covariance_row_kernel_iff_uncorrelated_with_basis_unconditional, covariance_two_samples_rank_one_factorization. | **New:** Signed-weight row-kernel criterion for every basis score. |
| `covariance_two_samples_zero_against_separating_score_iff_equal_values` (theorem) | Reuse exact rank-one factorization and standard real zero-product cancellation in one reusable scalar equivalence. | covariance_two_samples_rank_one_factorization, Rmult_integral, Lra. | **New:** Cov(f,pivot)=0 exactly when f has zero two-sample contrast under nondegeneracy. |
| `indexed_basis_two_samples_row_kernel_iff_equal_composite_values` (theorem) | **Refactored:** Reuse scalar zero-covariance iff for a separating basis score and unconditional row-kernel/basis covariance orthogonality. | covariance_two_samples_zero_against_separating_score_iff_equal_values, indexed_basis_bounded_covariance_row_kernel_iff_uncorrelated_with_basis_unconditional, covariance_two_samples_rank_one_factorization. | **Refactored:** Eliminate duplicated Rmult_integral proof tree while keeping the API and hypotheses. |
| `indexed_basis_two_samples_nonzero_diagonal_of_separating_score` (theorem) | Reuse scalar factorization and eliminate possible zero products. | covariance_two_samples_rank_one_factorization, Stdlib.Reals.Rmult_integral. | **New:** Separating basis score provides a nonzero diagonal rank-one certificate. |

| `indexed_basis_two_samples_pivot_cross_identity` (theorem) | Specialize already checked all-minors-zero theorem with a repeated row/column pivot index. | indexed_basis_covariance_two_samples_all_minors_zero, Fin.t. | **New:** Every entry times pivot diagonal equals pivot column times pivot row. |
| `indexed_basis_two_samples_pivot_reconstruction` (theorem) | Rewrite numerator by cross-product identity and cancel a nonzero denominator with standard field normalization. | indexed_basis_two_samples_pivot_cross_identity, Stdlib.Reals/Field. | **New:** Exact reconstruction M(i,j)=M(i,p)M(p,j)/M(p,p) for a nonzero diagonal pivot. |
| `indexed_basis_two_samples_nonzero_pivot_implies_nondegenerate` (theorem) | Expand diagonal by existing scalar two-sample covariance factorization; refute vanishing factors by ring. | covariance_two_samples_rank_one_factorization, Stdlib.Ring. | **New:** Nonzero pivot guarantees nonzero weight product and separating pivot score. |
| `indexed_basis_two_samples_row_kernel_iff_pivot_row_dot_zero` (theorem) | Reuse typed nth_error membership, scalar contrast detection, named row-kernel/contrast equivalence and unconditional covariance row-dot identity. | vector_of_list_nth_error, nth_error_In, covariance_with_weighted_basis_as_row_dot, covariance_symmetric, VectorSpec.length_to_list. | **New:** One nonzero pivot row determines the full two-sample covariance row kernel. |
| `indexed_basis_two_samples_radical_iff_pivot_row_dot_zero` (theorem) | Compose unconditional radical/row-kernel equivalence with the preceding one-row test. | indexed_basis_covariance_bilinear_radical_iff_row_kernel_unconditional, indexed_basis_two_samples_row_kernel_iff_pivot_row_dot_zero, tauto. | **New:** One pivot-row dot product also detects the bilinear radical, including signed weights. |
| `indexed_basis_two_samples_zero_matrix_of_zero_weight_product` (theorem) | Expand every existing indexed entry using scalar rank-one factorization, then simplify the zero weight product. | covariance_two_samples_rank_one_factorization, indexed_basis_cross_covariance_matrix, ring. | **New:** Exact rank-zero degeneracy when either two-sample weight vanishes. |
| `indexed_basis_two_samples_cross_square_equals_diagonal_product` (theorem) | Specialize the established all-minors-zero law at (i,j,j,i); rewrite the reverse entry using covariance symmetry. | indexed_basis_covariance_two_samples_all_minors_zero, covariance_symmetric, Stdlib.Vectors.Fin. | **New:** M(i,j)^2=M(i,i)M(j,j) for normalized two-sample signed covariance. |
| `indexed_basis_two_samples_cross_entry_nonzero_iff_diagonals_nonzero` (theorem) | Apply the shared square-diagonal identity and cancel nonzero real factors, without assuming PSD. | indexed_basis_two_samples_cross_square_equals_diagonal_product, Psatz.nra, Reals.Rmult_integral. | **New:** M(i,j) is nonzero iff both associated diagonals are nonzero. |
| `indexed_basis_two_samples_zero_matrix_iff_all_diagonals_zero` (theorem) | Reduce all entry zeros to all diagonal zeros using the established cross-square law and real square-zero arithmetic. | indexed_basis_two_samples_cross_square_equals_diagonal_product, Psatz.nra, indexed_basis_cross_covariance_matrix. | **New:** Exact two-sample rank-zero certificate, valid for signed weights. |
| `indexed_basis_two_samples_bilinear_all_minors_zero` (theorem) | Rewrite four typed bilinear pairings using the existing two-sample contrast factorization; close by ring. | indexed_basis_covariance_bilinear_two_samples_factorization, Stdlib.Ring. | **New: all rank-one minors vanish for arbitrary typed coefficient directions.** |
| `indexed_basis_two_samples_bilinear_self_nonnegative_of_weight_product` (theorem) | Combine nonnegative sample-weight product with square nonnegativity through the typed rank-one formula. | indexed_basis_covariance_bilinear_two_samples_factorization, Rmult_le_pos, Rle_0_sqr. | **New: signed two-sample PSD sufficiency without separately nonnegative weights.** |
| `indexed_basis_two_samples_bilinear_self_nonpositive_of_weight_product` (theorem) | Use a nonpositive sample-weight product and the standard nonnegative square. | indexed_basis_covariance_bilinear_two_samples_factorization, Rle_0_sqr, nra. | **New: signed two-sample negative semidefinite sufficiency.** |
| `indexed_basis_two_samples_bilinear_negative_self_witness` (theorem) | Reuse a typed standard coordinate representation of a separating score and the squared contrast. | indexed_basis_score_has_typed_coordinate_representation, indexed_basis_covariance_bilinear_two_samples_factorization, nra. | **New: negative-product sign yields a strictly negative self-pairing.** |
| `indexed_basis_two_samples_bilinear_positive_self_witness` (theorem) | Represent a separating score as a typed coefficient vector, and multiply its positive contrast square. | indexed_basis_score_has_typed_coordinate_representation, indexed_basis_covariance_bilinear_two_samples_factorization, nra. | **New: positive-product sign yields a strictly positive self-pairing.** |
| `indexed_basis_two_samples_bilinear_psd_iff_nonnegative_weight_product` (theorem) | Combine PSD sufficiency with negative self-pairing witness to rule out a negative weight product. | indexed_basis_two_samples_bilinear_self_nonnegative_of_weight_product, indexed_basis_two_samples_bilinear_negative_self_witness, Rle_dec, lra. | **New: exact PSD sign classification for separating two-sample bases.** |
| `indexed_basis_two_samples_bilinear_nsd_iff_nonpositive_weight_product` (theorem) | Combine NSD sufficiency with positive self-pairing witness to exclude positive weight product. | indexed_basis_two_samples_bilinear_self_nonpositive_of_weight_product, indexed_basis_two_samples_bilinear_positive_self_witness, Rle_dec, lra. | **New: exact NSD sign classification for separating two-sample bases.** |
| `indexed_basis_two_samples_zero_matrix_of_nonseparating_basis` (theorem) | Use typed indexed-score membership, scalar covariance factorization and vanishing sample contrast. | vector_of_list_nth_error, nth_error_In, covariance_two_samples_rank_one_factorization, ring. | **New: a nonseparating score basis has identically zero covariance, even with signed weights.** |
| `indexed_basis_two_samples_bilinear_self_zero_iff_weight_or_equal_scores` (theorem) | Factor the self-covariance and apply the standard zero-product lemma twice; solve equal-score differences with Lra. | indexed_basis_covariance_bilinear_two_samples_factorization, Rmult_integral, Lra, Ring. | **New: exact signed two-sample self-nullity as weight degeneracy or score constancy.** |
| `indexed_basis_two_samples_bilinear_self_zero_iff_radical_signed` (theorem) | Use the scalar self-zero characterization and exact bilinear factorization; converse tests the same vector. | indexed_basis_two_samples_bilinear_self_zero_iff_weight_or_equal_scores, indexed_basis_covariance_bilinear_two_samples_factorization, Ring. | **New: zero self-covariance iff full radical for signed two-sample weights.** |
| `indexed_basis_two_samples_quadratic_zero_iff_radical_signed` (theorem) | Transport the strengthened signed self-zero/radical equivalence across the existing diagonal identity. | indexed_basis_covariance_bilinear_diagonal, indexed_basis_two_samples_bilinear_self_zero_iff_radical_signed. | **New: typed quadratic nullity iff radical without nonnegative-weight assumptions.** |
| `indexed_basis_two_samples_quadratic_zero_iff_row_kernel_signed` (theorem) | Compose signed quadratic/radical equivalence with the unconditional radical/row-kernel bridge. | indexed_basis_two_samples_quadratic_zero_iff_radical_signed, indexed_basis_covariance_bilinear_radical_iff_row_kernel_unconditional, tauto. | **New: two-sample zero quadratic iff every indexed covariance row dot is zero, signed weights permitted.** |
| `indexed_basis_two_samples_radical_iff_zero_weight_or_equal_scores` (theorem) | Compose self-zero/radical and exact weight-or-contrast self-nullity tests. | indexed_basis_two_samples_bilinear_self_zero_iff_radical_signed, indexed_basis_two_samples_bilinear_self_zero_iff_weight_or_equal_scores, tauto. | **New: full radical characterized by zero weight product or equal sampled composite scores.** |
| `indexed_basis_two_samples_quadratic_zero_iff_weight_or_equal_scores` (theorem) | Compose typed quadratic/radical and explicit radical weight/contrast criteria. | indexed_basis_two_samples_quadratic_zero_iff_radical_signed, indexed_basis_two_samples_radical_iff_zero_weight_or_equal_scores, tauto. | **New: exact signed two-sample quadratic-zero classification.** |
| `indexed_basis_two_samples_bilinear_zero_iff_weight_or_nonseparating_basis` (theorem) | Use Req_EM_T and the existing typed basis coordinate witness for necessity; factorization and the unconditional basis/radical bridge for sufficiency. | Req_EM_T, indexed_basis_score_has_typed_coordinate_representation, indexed_basis_covariance_bilinear_radical_iff_uncorrelated_with_basis_unconditional, covariance_two_samples_rank_one_factorization. | **New: all bilinear pairings vanish iff weight product zero or basis does not separate sampled outcomes.** |
| `indexed_basis_two_samples_all_self_zero_iff_weight_or_nonseparating_basis` (theorem) | Convert every zero self-pairing into radical membership, then reuse exact full-zero-form classification. | indexed_basis_two_samples_bilinear_self_zero_iff_radical_signed, indexed_basis_two_samples_bilinear_zero_iff_weight_or_nonseparating_basis. | **New: all self-nullities characterize full two-sample covariance degeneracy even with signed weights.** |
| `indexed_basis_two_samples_all_quadratics_zero_iff_weight_or_nonseparating_basis` (theorem) | Transport universal zero quadratics through the already verified bilinear diagonal theorem and all-self-nullity classification. | indexed_basis_covariance_bilinear_diagonal, indexed_basis_two_samples_all_self_zero_iff_weight_or_nonseparating_basis. | **New: exact criterion for a globally zero typed covariance quadratic under arbitrary signed two-sample weights.** |
| `indexed_basis_two_samples_bilinear_pivot_cross_identity` (theorem) | Specialize the established all-minors-zero theorem to a repeated typed coefficient pivot. | indexed_basis_two_samples_bilinear_all_minors_zero. | **New: one pivot cross identity for arbitrary typed coefficient covariance pairings.** |
| `indexed_basis_two_samples_bilinear_pivot_reconstruction` (theorem) | Rewrite the typed pivot identity as a quotient and discharge the denominator with the nonzero self-pairing premise. | indexed_basis_two_samples_bilinear_pivot_cross_identity, Stdlib.Field. | **New: reconstruct the full typed covariance pairing from a nonzero pivot.** |
| `indexed_basis_two_samples_bilinear_radical_iff_pivot_orthogonal` (theorem) | Use the pivot cross identity and Rmult_integral to cancel nonzero self-covariance in every test pairing. | indexed_basis_two_samples_bilinear_pivot_cross_identity, indexed_basis_covariance_bilinear_radical, Rmult_integral. | **New: radical membership is equivalent to one pivot covariance equality.** |
| `indexed_basis_two_samples_bilinear_zero_iff_pivot_orthogonality` (theorem) | Factor zero pairings by pivot cross identity, real zero-product and nonzero-pivot cancellation. | indexed_basis_two_samples_bilinear_pivot_cross_identity, Rmult_integral, Stdlib.Ring. | **New: a zero typed cross-pairing iff either pivot-side pairing vanishes.** |
| `indexed_basis_two_samples_bilinear_functional_normal_form` (theorem) | Normalize the previously proved typed pivot reconstruction to a scalar multiple of the pivot functional. | indexed_basis_two_samples_bilinear_pivot_reconstruction, Stdlib.Field. | **New: exact functional normal form for every typed coefficient direction.** |
| `indexed_basis_two_samples_bilinear_functional_unique_scale` (theorem) | Choose the pivot quotient as the scale; use right=pivot and the nonzero denominator to prove uniqueness. | indexed_basis_two_samples_bilinear_functional_normal_form, Stdlib.Logic.ex_unique, Stdlib.Field. | **New: covariance functional image has a unique scalar coordinate against a nonzero pivot.** |
| `indexed_basis_two_samples_bilinear_radical_unique_pivot_subtraction` (theorem) | Subtract the quotient-scaled pivot; use checked bilinear add/scale laws to prove radical membership and field cancellation for uniqueness. | indexed_basis_two_samples_bilinear_functional_normal_form, indexed_basis_covariance_bilinear_add_first, indexed_basis_covariance_bilinear_scale_first, Stdlib.Field. | **New: unique scalar-plus-radical splitting of every typed covariance coefficient direction.** |
| `indexed_basis_two_samples_bilinear_functional_fiber_iff_pivot` (theorem) | Use the normal form in both directions to equate full covariance functionals precisely when one pivot evaluation matches. | indexed_basis_two_samples_bilinear_functional_normal_form, Stdlib.Logic. | **New: single-pivot equality criterion for arbitrary covariance functional fibers.** |
| `indexed_basis_two_samples_covariance_quadratic_pivot_square` (theorem) | Rewrite the typed quadratic as a bilinear diagonal and then a pivot-reconstructed symmetric square. | indexed_basis_covariance_bilinear_diagonal, indexed_basis_two_samples_bilinear_pivot_reconstruction, indexed_basis_covariance_bilinear_symmetric. | **New: exact signed two-sample quadratic square divided by a nonzero pivot pairing.** |
| `indexed_basis_covariance_pivot_coordinate_add` (theorem) | Reuse typed covariance additivity and normalize the quotient under a nonzero pivot. | indexed_basis_covariance_bilinear_add_first, Stdlib.Field. | **New: Coordinate map is additive, even for signed/unnormalized weights.** |
| `indexed_basis_covariance_pivot_coordinate_scale` (theorem) | Use typed covariance scalar homogeneity and field normalization. | indexed_basis_covariance_bilinear_scale_first, Stdlib.Field. | **New: Coordinate map is homogeneous.** |
| `indexed_basis_covariance_pivot_coordinate_pivot_one` (theorem) | Cancel the nonzero pivot self-covariance in the normalized quotient. | Stdlib.Field, indexed_basis_covariance_pivot_coordinate. | **New: Pivot has normalized scalar coordinate one.** |
| `indexed_basis_covariance_pivot_coordinate_section` (theorem) | Apply checked covariance homogeneity to the standard vector-map section then normalize. | indexed_basis_covariance_bilinear_scale_first, Stdlib.Field, Vector.map. | **New: Coordinate composed with scalar section is the identity on R.** |
| `indexed_basis_covariance_pivot_section_injective` (theorem) | Apply the coordinate functional to a section equality and use retraction. | indexed_basis_covariance_pivot_coordinate_section, f_equal. | **New: Scalar section is injective for a nonzero pivot.** |
| `indexed_basis_two_samples_bilinear_pivot_coordinate_factorization` (theorem) | Apply checked two-sample bilinear pivot reconstruction, symmetry and field arithmetic. | indexed_basis_two_samples_bilinear_pivot_reconstruction, indexed_basis_covariance_bilinear_symmetric, Stdlib.Field. | **New: Every pairing factors through two normalized real coordinates.** |
| `indexed_basis_two_samples_radical_iff_pivot_coordinate_zero` (theorem) | Transport one-pivot radical orthogonality across the nonzero scalar denominator. | indexed_basis_two_samples_bilinear_radical_iff_pivot_orthogonal, Stdlib.Field, Psatz.nra. | **New: Radical is the kernel of one normalized real linear functional.** |
| `indexed_basis_covariance_pivot_projection_coordinate` (theorem) | Unfold the composition and invoke coordinate-section retraction. | indexed_basis_covariance_pivot_coordinate_section. | **New: Projection preserves its unique scalar coordinate.** |
| `indexed_basis_covariance_pivot_projection_idempotent` (theorem) | Expand only the outer projection and rewrite its coordinate to the original value. | indexed_basis_covariance_pivot_projection_coordinate. | **New: Pivot-line coefficient projection is idempotent.** |
| `indexed_basis_covariance_pivot_projection_fiber_iff_coordinate` (theorem) | Apply the normalized coordinate to equal projections, and vice versa. | indexed_basis_covariance_pivot_projection_coordinate, f_equal. | **New: Projection equality iff one real coordinate equality.** |
| `indexed_basis_covariance_pivot_projection_image_iff_section` (theorem) | Project to its scalar section; conversely each section is fixed by retraction. | indexed_basis_covariance_pivot_coordinate_section. | **New: Projection image is exactly the one-scalar pivot line.** |
| `indexed_basis_two_samples_projection_radical_iff_zero_section` (theorem) | Reuse the radical iff zero-coordinate criterion and the projection retraction. | indexed_basis_two_samples_radical_iff_pivot_coordinate_zero, indexed_basis_covariance_pivot_projection_coordinate. | **New: Covariance radical equals concrete projection kernel.** |
| `indexed_basis_two_samples_projection_preserves_bilinear` (theorem) | Factor both pairings into normalized coordinates and preserve each projection coordinate. | indexed_basis_two_samples_bilinear_pivot_coordinate_factorization, indexed_basis_covariance_pivot_projection_coordinate. | **New: Projecting both directions leaves covariance unchanged.** |
| `indexed_basis_covariance_pivot_section_add` (theorem) | Prove standard Vector.map scalar-section additivity coordinatewise through VectorSpec equality and map2. | VectorSpec.eq_nth_iff, nth_map, nth_map2, Stdlib.Ring. | **New: The pivot section preserves addition without any probability assumptions.** |
| `indexed_basis_covariance_pivot_section_scale` (theorem) | Apply VectorSpec map extensionality and ring associativity for nested scalar maps. | VectorSpec.eq_nth_iff, nth_map, Stdlib.Ring. | **New: Pivot scalar section preserves real scalar multiplication.** |
| `indexed_basis_covariance_pivot_section_zero` (theorem) | Use standard VectorSpec nth_map and const_nth to identify zero-scaled pivot with Vector.const 0. | VectorSpec.eq_nth_iff, nth_map, const_nth, Stdlib.Ring. | **New: The zero scalar section is exactly the standard zero vector.** |
| `indexed_basis_covariance_pivot_coordinate_surjective` (theorem) | Choose the already established scalar section as a witness and invoke coordinate-section retraction. | indexed_basis_covariance_pivot_coordinate_section. | **New: The normalized covariance pivot coordinate is onto all real numbers.** |
| `indexed_basis_covariance_pivot_projection_add` (theorem) | Compose normalized covariance-coordinate additivity and scalar-section additivity. | indexed_basis_covariance_pivot_coordinate_add, indexed_basis_covariance_pivot_section_add. | **New: The idempotent covariance pivot projection is additive.** |
| `indexed_basis_covariance_pivot_projection_scale` (theorem) | Compose normalized covariance-coordinate homogeneity and scalar-section homogeneity. | indexed_basis_covariance_pivot_coordinate_scale, indexed_basis_covariance_pivot_section_scale. | **New: The pivot projection respects arbitrary real scalar multiplication.** |
| `indexed_basis_two_samples_projection_radical_iff_zero_vector` (theorem) | Rewrite the checked radical/zero-section equivalence using the certified section-zero vector identity. | indexed_basis_two_samples_projection_radical_iff_zero_section, indexed_basis_covariance_pivot_section_zero. | **New: For two signed unit-mass outcomes, the linear projection kernel equals covariance radical.** |

| `indexed_basis_covariance_pivot_projection_remainder_decomposition` (theorem) | Prove the full vector decomposition by VectorSpec pointwise extensionality and ring cancellation. | VectorSpec.eq_nth_iff, nth_map, nth_map2, Stdlib.Ring. | **New: Every coefficient vector decomposes into pivot projection plus explicit remainder.** |
| `indexed_basis_covariance_pivot_remainder_coordinate_zero` (theorem) | Combine coordinate additivity and section retraction to cancel the pivot coordinate. | indexed_basis_covariance_pivot_coordinate_add, indexed_basis_covariance_pivot_coordinate_section. | **New: Remainder has zero normalized pivot coordinate.** |
| `indexed_basis_two_samples_pivot_remainder_in_radical` (theorem) | Use two-sample radical/kernel equivalence and the remainder coordinate-zero proof. | indexed_basis_two_samples_radical_iff_pivot_coordinate_zero. | **New: Signed two-sample remainder is in the full covariance bilinear radical.** |
| `indexed_basis_covariance_pivot_projection_remainder_zero` (theorem) | Substitute the remainder coordinate-zero theorem and the standard zero-section identity. | indexed_basis_covariance_pivot_section_zero, Vector.const. | **New: Concrete remainder lies in the projection kernel without normalization.** |
| `indexed_basis_covariance_pivot_projection_fixes_section` (theorem) | Reuse coordinate-section retraction in the projection's thin composition. | indexed_basis_covariance_pivot_coordinate_section. | **New: Every pivot-line vector is fixed by the projection.** |
| `indexed_basis_two_samples_radical_pivot_line_trivial` (theorem) | Rewrite radical membership via the scalar coordinate and section retraction. | indexed_basis_two_samples_radical_iff_pivot_coordinate_zero. | **New: Radical and nonisotropic pivot line intersect only at zero.** |
| `indexed_basis_two_samples_projection_fiber_iff_radical_difference` (theorem) | Combine projection and radical coordinate-fiber equivalences, then simplify linear differences. | indexed_basis_covariance_pivot_coordinate_add/scale, Stdlib.Ring, Stdlib.Lra. | **New: Projection fibers are exactly covariance-radical cosets.** |
| `finite_signed_three_mass_one` (lemma) | Reduce the concrete signed three-sample sum and normalize arithmetic using ring. | FiniteMoments.total_mass, FiniteSum.finite_sum, Stdlib.Ring. | **New:** (1,1,-1) has unit total mass but is not a nonnegative probability weighting. |
| `finite_signed_three_first_score_variance_zero` (lemma) | Evaluate finite expectations and the shared variance/covariance definition at all three samples. | FiniteMoments.variance, FiniteMoments.covariance, FiniteSum.finite_sum, ring. | **New:** First nonconstant score has zero signed-weight quadratic. |
| `finite_signed_three_scores_cross_covariance_one` (lemma) | Evaluate the same finite moment definitions and normalize the real expression. | FiniteMoments.covariance, FiniteMoments.expect, FiniteSum.finite_sum, ring. | **New:** First and second score have cross-covariance one despite zero first-score variance. |
| `finite_signed_three_direction_selects_first_score` (lemma) | Compute typed Vector.of_list/to_list and existing composite score with List.combine, use ring. | Vector.of_list/to_list, weighted_basis_sum, linear_combination, FiniteSum.finite_sum. | **New:** Explicit first-coordinate typed coefficient exactly selects first score. |
| `finite_signed_three_unit_mass_isotropic_not_radical` (theorem) | Quadratic via unit-mass variance, then refute radical via unconditional orthogonality-to-basis iff and cross-covariance witness. | indexed_basis_covariance_quadratic_as_variance, variance_extensional, covariance_extensional, indexed_basis_covariance_bilinear_radical_iff_uncorrelated_with_basis_unconditional, Lra. | **New:** Kernel-checked signed-weight counterexample to quadratic-zero implies radical, with total mass one. |

## FiniteBridge.v — 37 proof scripts

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
| `finite_normalized_conditional_independence_iff_zero_indicator_covariance` (theorem) | Rewrite existing two iff bridges, reverse equivalence | FiniteUnion.finite_conditional_independent_given_true_iff_marginal_product; finite_event_independence_iff_zero_indicator_covariance | **New:** normalized true-conditioning independence iff zero indicator covariance |
| `conditioned_weights_total_mass_one` (theorem) | Scalar reciprocal factor from filtered FiniteSum, positive denominator field cancellation | FiniteSum.finite_sum_scale, FiniteUnion.finite_prob_as_filtered_mass, Stdlib.Reals field | **New:** filtered sample weights scaled by positive conditioning mass sum to exactly one |
| `conditioned_weights_moment_total_mass_one` (theorem) | Definitional bridge of normalized sample mass to moments | conditioned_weights_total_mass_one, FiniteMoments.total_mass, FiniteUnion.finite_sum | **New:** reusable normalized conditional sample unit-mass bridge for covariance results |
| `conditioned_weights_nonnegative_on_filtered_samples` (theorem) | Filter membership and nonnegative scalar product | Stdlib.List.filter_In, Stdlib.Reals.Rinv_0_lt_compat/Rmult_le_pos | **New:** normalized filtered weights remain nonnegative on retained samples |
| `finite_conditional_independence_iff_conditioned_indicator_covariance_zero` (theorem) | Compose filtered-true iff, positive scaling iff and normalized covariance bridge | FiniteUnion.finite_conditional_independent_iff_filtered_true, finite_conditional_independent_scale_weights, finite_normalized_conditional_independence_iff_zero_indicator_covariance | **New:** general positive-mass conditional independence iff indicator covariance zero on normalized filtered sample |
| `finite_conditioned_event_mass` (theorem) | Positive-denominator cancellation after finite event scaling and filtering | FiniteUnion.finite_prob_scale_weights, finite_prob_on_filtered_samples, Stdlib.Reals field | **New:** exact original conditional probability equals event mass on normalized selected finite sample |
| `finite_conditioned_indicator_variance` (theorem) | Rewrite existing indicator variance with normalized selected mass bridge | finite_event_indicator_variance, finite_conditioned_event_mass | **New:** conditional Bernoulli variance = p(A|G)*(1-p(A|G)) |
| `finite_conditioned_indicator_covariance_residual` (theorem) | Rewrite existing indicator covariance event-mass residual | finite_event_indicator_covariance, finite_conditioned_event_mass | **New:** conditioned indicator covariance equals conditional joint minus marginal product |
| `finite_conditioned_indicator_variance_at_most_quarter` (theorem) | Existing indicator variance upper bound instantiation | finite_event_indicator_variance_at_most_quarter, Stdlib.List.filter | **New:** universal conditional indicator variance upper bound of one quarter |
| `finite_conditioned_indicator_zero_variance_iff_extreme_conditional_mass` (theorem) | Indicator degeneracy iff rewritten through selected event mass | finite_event_indicator_zero_variance_iff_extreme_mass, finite_conditioned_event_mass | **New:** conditional indicator variance zero iff target conditional mass is zero or one |
| `finite_conditioned_indicator_complement_variance` (theorem) | Existing complement variance with reusable selected-sample normalization bridge | conditioned_weights_moment_total_mass_one, finite_event_indicator_complement_variance | **Refactored:** avoids repeated definition expansion of normalized moment total mass |
| `finite_conditioned_indicator_covariance_complement_first` (theorem) | Existing covariance complement-first theorem with shared unit-mass bridge | conditioned_weights_moment_total_mass_one, finite_event_indicator_covariance_complement_first | **New:** complementing first conditional indicator flips covariance sign |
| `finite_conditioned_indicator_covariance_complement_second` (theorem) | Existing covariance complement-second theorem with shared unit-mass bridge | conditioned_weights_moment_total_mass_one, finite_event_indicator_covariance_complement_second | **New:** complementing second conditional indicator flips covariance sign |
| `finite_conditioned_indicator_covariance_complement_both` (theorem) | Existing covariance complement-both theorem with shared unit-mass bridge | conditioned_weights_moment_total_mass_one, finite_event_indicator_covariance_complement_both | **New:** complementing both conditional indicators preserves covariance |
| `finite_conditioned_indicator_cauchy_schwarz_squared` (theorem) | Instantiate finite Cauchy–Schwarz with selected normalized mass and weight positivity | FiniteMoments.finite_covariance_cauchy_schwarz_squared, conditioned_weights_moment_total_mass_one, conditioned_weights_nonnegative_on_filtered_samples | **New:** conditional Boolean indicator covariance obeys squared Cauchy–Schwarz |
| `finite_conditioned_zero_indicator_variance_implies_zero_covariance` (theorem) | Apply established zero-variance covariance lemma to normalized selected sample | FiniteMoments.zero_variance_implies_zero_covariance_first, selected mass/nonnegativity bridges | **New:** zero conditional indicator variance forces zero conditional covariance |
| `finite_conditional_extreme_first_independent` (theorem) | Compose extreme mass iff zero variance, covariance zero, independence iff | finite_conditioned_indicator_zero_variance_iff_extreme_conditional_mass, finite_conditioned_zero_indicator_variance_implies_zero_covariance, finite_conditional_independence_iff_conditioned_indicator_covariance_zero | **New:** conditional event with mass zero or one independent of any second event |
| `finite_conditional_extreme_second_independent` (theorem) | Project original target-symmetry iff and invoke extreme-first theorem | FiniteUnion.finite_conditional_independent_symmetric, finite_conditional_extreme_first_independent | **New:** extreme conditional second target independent of any first event |
| `finite_conditioned_indicator_variance_nonnegative` (theorem) | Apply established finite moment variance positivity with selected normalized mass/nonnegativity | FiniteMoments.variance_nonnegative, conditioned_weights_moment_total_mass_one, conditioned_weights_nonnegative_on_filtered_samples | **New:** nonnegative variance of selected Bernoulli indicators |
| `finite_conditioned_indicator_covariance_squared_at_most_sixteenth` (theorem) | Cauchy–Schwarz with variance between 0 and 1/4, via nra | finite_conditioned_indicator_cauchy_schwarz_squared, finite_conditioned_indicator_variance_nonnegative, finite_conditioned_indicator_variance_at_most_quarter, Stdlib.Psatz.nra | **New:** squared conditional indicator covariance bounded by 1/16 |
| `finite_conditioned_indicator_covariance_between_quarters` (theorem) | Extract signed interval from the squared bound by nra | finite_conditioned_indicator_covariance_squared_at_most_sixteenth, Stdlib.Psatz.nra | **New:** finite conditional Bernoulli covariance lies in [-1/4, 1/4] |

## FourCellBridge.v — 25 proof scripts

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
| `four_cell_generic_independence_iff_marginal_product` (theorem) | Definitional shared sum equality, existing mass bridges and iff rewriting | FiniteUnion.finite_conditional_independent_given_true_iff_marginal_product, four_cell_total_mass, four_cell_intersection_mass, four_cell_first_marginal, four_cell_second_marginal | **New:** generic independence specializes exactly to four-cell joint=marginal product |
| `four_cell_generic_independence_iff_cross_product_cells` (theorem) | Iff rewriting and pre-existing admissions criterion | four_cell_generic_independence_iff_marginal_product, Admissions.binary_independence_criterion | **New:** generic conditional independence iff cross-product of four cell weights |
| `four_cell_generic_independence_iff_zero_indicator_covariance` (theorem) | Convert shared finite mass definitionally, instantiate general bridge | four_cell_total_mass, FiniteBridge.finite_normalized_conditional_independence_iff_zero_indicator_covariance | **New:** four-cell generic independence iff indicator covariance nullity |

## Unconditional covariance radical and row-kernel equivalence (13 November 2026)

Four documented results establish that the covariance bilinear radical
is exactly the bounded covariance row kernel for arbitrary finite signed
or unnormalized weights. A typed coordinate-selector lemma uses existing
Vector.cons/const and the zero-composite theorem. Two other theorems
characterize the radical and the row kernel separately through covariance
orthogonality to every listed basis score, using shared FiniteSum laws,
the unconditional covariance linearity, and existing bounded index bridges.
The original normalized nonnegative theorem now delegates to the stronger
result. The affine signed-weight row theorem likewise delegates to its
already checked radical witness through the new equivalence.

Intended inventory: **903 public claims, 906 proof scripts, 985 documented
declarations** over seven modules, pending pinned Rocq 9.2 and Python
CI. This is a purely algebraic kernel equivalence, not a general
quadratic-nullity equivalence for signed weights, PSD claim or rank
calculation.


## Algebraic covariance-row kernel closure and shift invariance (13 November 2026)

Five documented theorems certify zero membership, addition closure,
scalar closure, nonzero-scaling equivalence, and invariance under
row-kernel shifts **without normalizing sample weights or assuming
their nonnegativity**. All results reuse the unconditional equivalence
between the bilinear covariance radical and the indexed covariance
row kernel, plus existing radical lemmas; no second matrix, vector,
or finite-sum implementation is introduced. The older normalized
row-kernel APIs remain intact as separately defined compatibility
statements (their source-order dependencies precede the radical
interface). The positive-definiteness iff trivial radical theorem
now uses the unconditional bridge in both directions, retaining its
own probability premises because strict positivity requires them.

Inventory: **908 public claims, 911 proof scripts, 990 documented
declarations**, with **497 proof scripts in FiniteMoments.v**, across
seven Rocq modules. Pin to Rocq 9.2 and run existing Python/Deal/SPARK
CI. No signed-weight PSD, covariance rank, abstract nullity or
empirical IQ result follows from these kernel identities.


## A concrete unit-mass signed-weight isotropic counterexample (13 November 2026)

The finite natural-number sample [0,1,2] carries outcome weights
(1,1,-1), totaling exactly one, but the last is negative. The two
indicator-like scores are f=1 only at sample one and g=1 only
at sample two. The checked finite moment calculations give
Var(f)=0 and Cov(f,g)=1. A typed direction selecting f therefore
has zero indexed covariance quadratic but **does not** lie in the
bilinear radical: the unconditional radical/basis-score theorem
detects its nonzero covariance against g. The construction is
deliberately synthetic and disproves the tempting signed-weight
converse of quadratic nullity to radical membership. It does
not challenge positive-semidefinite covariance under
nonnegative normalized probability weights. All computations
use the existing finite-sum, indexed-basis and covariance
interfaces; there is no new numerical matrix implementation.

Inventory after this addition: **913 public claims, 916 proof scripts,
1001 documented declarations** (502 FiniteMoments proofs) across seven
modules, subject to pinned Rocq 9.2 and Python/Deal/SPARK CI.


## Exact two-sample covariance rank-one certificates (13 November 2026)

Seven documented Rocq results prove that every covariance over two
enumerated sample occurrences and unit total mass has the form
w(x)w(y)(f(x)-f(y))(g(x)-g(y)), without nonnegative-weight assumptions.
Every two-by-two covariance minor therefore vanishes for every
four bounded Fin-indexed score coordinates; the same factorization
applies to arbitrary typed coefficient composite scores. The row
kernel is exactly the kernel of the sample contrast functional when
both weights have nonzero product and the basis includes a score
separating the two outcomes. Such a separating score also yields
a nonzero covariance diagonal, completing an explicit rank-one
certificate. Proofs reuse the established finite covariance and
FiniteSum operators, Stdlib.Vectors.Fin/Vector, and standard ring
and zero-product lemmas. No custom matrix or determinant implementation
or general rank-nullity theorem is added.

Expected total: **920 public claims, 923 proof scripts, 1008
documented declarations**, including **509 FiniteMoments proof
scripts**, pending pinned Rocq 9.2 and Python regression CI.
Signed weights can produce negative covariance diagonals, so no
signed-weight positive-semidefiniteness is claimed.


## Pivot reconstruction and exact one-row kernels (13 November 2026)

Seven documented Rocq theorems strengthen the two-sample rank-one
certificate. Under samples=[x;y], total_mass=1, and a nonzero
Fin-indexed diagonal pivot M(p,p), the existing bounded covariance
matrix has exact entrywise reconstruction
M(i,j)=M(i,p)*M(p,j)/M(p,p). That pivot is shown to separate the two
outcomes and requires a nonzero product of their weights. A single
ordinary pivot-row dot product is therefore an exact membership test
for the entire covariance row kernel and, through the previously
checked unconditional radical-row equivalence, for the bilinear
radical. Separately, a zero weight product implies every indexed
matrix entry is exactly zero. A reusable scalar two-sample
zero-covariance iff contrast theorem replaces repeated
zero-product reasoning in the existing two-sample kernel proof.
The construction reuses FiniteSum, Stdlib.Vectors.Fin/Vector,
the maintained indexed covariance matrix and real-field lemmas;
it defines no competing matrix type, determinant or rank routine.
Signed weights are supported but no PSD claim is made.

Expected inventory: **927 public claims, 930 proof scripts and
1015 documented declarations** in seven modules, including
**516 FiniteMoments proof scripts**, subject to pinned Rocq 9.2
kernel verification and existing Python/Deal/SPARK regression gates.
Rank-zero and rank-one here are structural entry certificates,
not an abstract dimension/rank-nullity formalization.


## Diagonal detection of all two-sample covariance entries (13 November 2026)

Three documented and library-reusing Rocq theorems extend the structural
rank-one certificate beyond pivot reconstruction. The checked two-by-two
minor theorem and covariance symmetry imply M(i,j)^2=M(i,i)M(j,j).
Consequently a cross-covariance entry is nonzero exactly when **both**
corresponding diagonal entries are nonzero, regardless of the sign of
the sample weights. The entire Fin-indexed covariance matrix vanishes
exactly when every diagonal vanishes. This includes empty and dependent
score bases, repeated outcomes and signed unit-mass weights. Proofs
reuse the existing Fin-indexed covariance, two-sample minor theorem,
covariance symmetry, Stdlib.Reals.Rmult_integral and Psatz.nra; no
new matrix data type, determinant, rank algorithm or axiom is added.

Expected inventory: **930 public claims, 933 proof scripts, 1018
documented declarations**, with **519 FiniteMoments proof scripts**
in seven modules. Pinned Rocq 9.2 kernel and Python regression checks
must validate the branch head before these counts are reported as
verified. This is an entrywise rank-zero/rank-one certificate, not
a general finite-dimensional rank-nullity theorem or a claim about
empirical IQ covariance.

## Typed two-sample covariance sign and nullity classification (13 November 2026)

Eight carefully documented theorems extend the exact two-outcome rank-one
factorization beyond matrix entries to every typed coefficient direction.
Four-direction bilinear cross minors vanish without signed-weight restrictions.
When the product of the two normalized sampled weights is nonnegative,
all coefficient self-pairings are nonnegative; when nonpositive, they are
nonpositive. An existing typed single-score coordinate representation gives
strictly negative or positive self-pairing witnesses for strictly negative or
positive weight products, provided a listed score separates the outcomes.
Consequently, **in a separating basis**, the covariance bilinear form is
positive semidefinite exactly when the weight product is nonnegative, and
negative semidefinite exactly when it is nonpositive. If every listed score
assigns equal values to the two sampled outcomes, every indexed covariance
matrix entry is zero, independently of the signed weight product.

The proofs reuse the already kernel-checked two-sample factorization,
indexed_basis_score_has_typed_coordinate_representation, established vector
nth_error/membership bridges, Stdlib.Reals square and sign laws, Psatz.nra
and Ring. No additional finite sums, coordinate selectors, matrices, rank
calculators, axioms or admitted proofs are introduced.

Expected inventory: **938 public checked claims, 941 proof scripts,
1026 documented declarations**, including **527 FiniteMoments proof
scripts**, across seven modules. These figures and all proof theorems
require Rocq 9.2 CI verification. This is a signed two-sample
semidefinite classification, not general covariance inertia, an abstract
rank-nullity theorem or empirical IQ inference.

## Signed two-sample covariance isotropy and complete degeneracy (13 November 2026)

Nine new fully documented Rocq theorems strengthen the already checked
two-sample rank-one covariance factorization. The self-pairing of any
typed coefficient direction vanishes exactly when the product of the two
sample weights is zero or the coefficient composite has the same value
on both outcomes. **Even for signed weights**, this is equivalent to
membership in the full bilinear radical and to annihilating every
indexed covariance row. The original typed covariance quadratic has
exactly the same zero set under samples=[x;y] and unit mass, without
requiring individual weights to be nonnegative.

The results also characterize complete covariance degeneracy:
all typed bilinear pairings vanish, all self-pairings vanish, or all
typed quadratics vanish **if and only if** the sample weight product
is zero or no listed score separates the two samples. This distinction
matters because the checked signed *three*-sample counterexample
admits an isotropic direction that is not in the bilinear radical.
The new equivalences are explicitly confined to two outcomes.

The proofs reuse the existing signed two-sample factorization,
indexed-basis covariance/radical/row-kernel interfaces, the maintained
typed basis-coordinate selector lemma, the bilinear diagonal identity,
Stdlib.Reals.Rmult_integral/Req_EM_T, Lra, Ring and tauto.
No competing finite-sum, matrix representation, generic rank algorithm,
axiom or admitted lemma is introduced. No Python, Ada/SPARK or archived
evidence source is modified.

Intended inventory: **947 public checked claims, 950 proof scripts,
1035 documented declarations**, including **536 FiniteMoments proof
scripts** in seven modules. Pinned Rocq 9.2 and Python/Deal/SPARK CI
remain the verification authorities; these counts alone do not imply
generic rank-nullity or empirical IQ-test validity.

## Typed coefficient-pivot covariance reconstruction (13 November 2026)

Four new fully documented theorems extend the already checked
two-sample all-minors-zero theorem to a **single typed coefficient pivot**
with nonzero covariance self-pairing. The first specializes the
four-direction determinant-free cross identity. The second reconstructs
every bilinear covariance pairing from two pivot covariances divided by
the nonzero pivot self-pairing. The third proves that radical membership
is exactly the vanishing of one pivot covariance. The fourth proves that
a zero covariance between two directions occurs exactly when one of
their corresponding pivot covariances vanishes.

The proofs reuse the maintained indexed-basis covariance bilinear form
and radical, its all-minors identity, Stdlib.Reals.Rmult_integral,
Stdlib.Ring and Stdlib.Field. No new matrix operations, coefficient
selectors, finite sums, axioms or admitted proofs have been introduced.
The sign of either individual sample weight is unrestricted under
two-sample unit-mass normalization. The nonzero-pivot premise is
essential for the reconstruction and one-pivot nullity converses.

Intended inventory: **951 public checked claims, 954 proof scripts,
1039 documented declarations**, including **540 FiniteMoments proof
scripts** in seven modules. GitHub Actions Rocq 9.2 kernel checks and
the existing Python/Deal/SPARK workflows are the verification authority.
The result does not yet prove an abstract linear-map rank-nullity theorem
or an empirical covariance inference.

## Typed two-sample covariance functional normal form (14 November 2026)

Five Rocq kernel-checkable and fully documented theorems extend the
two-sample typed pivot reconstruction. Given a nonzero self-pairing of a
typed coefficient pivot, every covariance functional is a scalar multiple
of the pivot functional and that scalar is **unique**. Every coefficient
direction has exactly one pivot multiplier whose subtraction leaves a
coefficient direction in the covariance bilinear radical. Two coefficient
directions induce the same covariance against every test direction if and
only if they agree against the pivot. The original typed covariance
quadratic equals the square of its pivot covariance divided by the
nonzero pivot self-pairing, under the existing unit-mass premise.

All five proofs reuse the already checked bilinear normalizations,
additive/scalar linearity, radical predicate, diagonal identity,
symmetry, and Stdlib.Field/Ring/Psatz. No new finite-sum, custom
matrix algebra, coefficient-selector, axioms or admitted code is added.
Signed weights are permitted because the algebra is specific to
two unit-mass sampled occurrences. The construction supplies a
unique one-scalar/radical normal form, but does not yet supply a
maintained abstract vector-space dimension or rank-nullity theorem.

Expected inventory: **956 public checked claims, 959 proof scripts,
1044 documented declarations**, including **545 FiniteMoments proof
scripts** across seven modules; pinned Rocq 9.2 CI remains mandatory.

## Covariance pivot-coordinate retraction and rank-one projection (14 November 2026)

Three thoroughly commented thin definitions and thirteen documented
theorems organize the previously proved two-sample scalar-plus-radical
normal form as an explicit **coordinate / section / projection** triple
over the existing Stdlib.Vectors.Vector.t representation. The normalized
coordinate is additive and homogeneous and sends the chosen pivot
to one when its self-covariance is nonzero. The standard Vector.map
scalar section is an injective right inverse to the coordinate map.
The covariance pairing for two unit-mass outcomes factors exactly
through the two real normalized coordinates and one pivot self-pairing.

The induced coefficient projection preserves its coordinate, is
idempotent, has fibers classified by one real scalar, and has image
exactly the scalar pivot line. Under two unit-mass sampled outcomes,
its kernel is precisely the existing covariance bilinear radical
and projecting both arguments **preserves every covariance pairing**.
Coordinate/section retraction and linearity, projection idempotence,
image and fiber identities require only a nonzero pivot, independently
of probability mass normalization. The factorization, radical kernel
and covariance-preservation identities additionally state the exact
two-sample unit-mass hypotheses.

The implementation reuses indexed-basis bilinearity, prior typed
pivot reconstruction, the existing radical and Stdlib.Reals,
Stdlib.Field, Stdlib.Psatz, Stdlib.Vectors.Vector.map and f_equal.
No new finite sum, vector recursion, matrix evaluator, determinant,
axiom or admitted proof is introduced. No Python, SPARK or archived
evidence code is changed. The operator is a concrete, certified
rank-one-style retraction, **not yet an abstract dimension/rank-nullity
theorem** over a maintained vector-space theory.

Expected inventory after pinned Rocq 9.2 validation:
**969 public claims, 972 proof scripts, 1060 documented declarations**
across seven modules; **558 FiniteMoments proof scripts**.

## Stdlib-backed linearity and zero-kernel of the covariance pivot projection (14 November 2026)

Seven additional fully documented Rocq theorems complete the linear
retraction interface: the scalar-to-pivot section preserves addition
and scaling and maps zero to the standard Vector.const zero vector.
The normalized pivot-coordinate functional is surjective onto all
real scalars whenever B(p,p) is nonzero. The already certified
idempotent pivot projection itself preserves both vector addition
and scalar multiplication, so it is a concrete linear endomorphism
of the existing fixed-length real Vector.t. In a two-sample model
with unit total mass, its kernel equals the covariance radical
**using the standard typed zero vector**.

The proofs reuse VectorSpec.eq_nth_iff/nth_map/nth_map2/const_nth,
Stdlib.Ring, the existing covariance bilinearity, coordinate and
section retraction lemmas, and the earlier signed two-sample
radical/zero-section theorem. No new vector recursion, finite sums,
matrix code, axioms, admission, Python, SPARK or historical evidence
changes are introduced.

Expected inventory: **976 public checked claims, 979 proof scripts,
1067 documented declarations**, including **565 FiniteMoments proof
scripts** across seven Rocq modules. The linear projection and its
explicit scalar-line image and covariance radical kernel are now
represented with typed standard-library vectors, but an abstract
vector-space dimension and general rank-nullity result remain open.


## Explicit pivot-line / radical complement and quotient fibers (14 November 2026)

The maintained covariance projection now has an explicit **typed complementary
remainder**, using only `Vector.map2 Rplus` and the existing scalar pivot
section. Seven documented Rocq theorems certify: exact vector reconstruction
as projection plus remainder without normalization; zero pivot coordinate
and projection of that remainder under nonzero pivot; full bilinear-radical
membership of the remainder under exactly two unit-mass sample occurrences;
pointwise fixation of every pivot-line vector; trivial intersection of that
line with the covariance radical; and equality of projected vectors exactly
when their difference belongs to the radical.

All theorems work with signed weights where logically allowed. Only the
radical-specific theorems assume two occurrences and unit mass; none claims
an abstract vector-space rank, dimension, or a general PSD statement. The
proofs reuse established `indexed_basis_covariance_pivot_*` interfaces,
`Stdlib.Vectors.VectorSpec.eq_nth_iff/nth_map/nth_map2`,
`Stdlib.Ring` and `Stdlib.Lra`. No new matrix, summation, recursive vector,
axiom, admitted proof, Python/SPARK source or historical evidence was added.

Expected inventory after Rocq CI: **983 public claims**, **986 proof scripts**
and **1075 documented declarations** across seven modules, including
**572 FiniteMoments proof scripts**. The surviving research gap is transport to
maintained abstract linear maps, subspaces and a generic rank-nullity theorem.
