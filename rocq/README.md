# Rocq formalization of checked claims

This directory is an additional **Rocq kernel-checked mathematical layer**
for the two reports. **673 proof scripts** in seven
Rocq files are tracked for Rocq 9.2 kernel compilation (including auxiliary proof lemmas). It complements, rather than replaces, the existing Ada/SPARK
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

## Prior complete proof-script refactor review and shared zip/map consolidation

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

## Previous continuation: filtered-sample event algebra and direct Stdlib reuse

**Current inventory:** 333 public theorem/lemma/example declarations across
seven Rocq modules (64 Hoeflin; 67 Admissions; **49 FiniteUnion**;
107 FiniteMoments; 19 FiniteSum; 14 FiniteBridge; 13 FourCellBridge).
The one existing `Local Lemma` makes **334 checked proof
declarations**; including the two `Admissions.TwoEventModel`
constructors gives **336 `Proof.` scripts**. All **390 named
declarations**, including records and definitions, have an explanatory
`(** ... *)` comment. All seven Rocq files retain their comprehensive
module header comments.

The latest change replaces the project-specific pointwise weighted-sum
argument in `finite_prob_event_ext_on_samples` with the directly
applicable **`Stdlib.List.filter_ext_in`** lemma and the already checked
`finite_prob_as_filtered_mass` identity.

Four new results establish a reusable representation of event restriction
and Boolean sample partition, without axiomatizing probability:

- `finite_prob_on_filtered_samples`: probability mass on
  `filter p samples` equals mass of the conjunction of `p` and
  the event on the original sample. Uses
  `FiniteSum.finite_sum_filter` and the common sum-extensionality law.
- `union_prob_on_filtered_samples`: applies the same property to
  arbitrary event families encoded by `Stdlib.List.existsb`.
- `finite_prob_filtered_partition`: proves that mass in selected
  outcomes plus rejected outcomes equals the original event mass,
  through the shared sum-addition theorem.
- `union_prob_filtered_partition`: extends this exact identity to
  the union of any number of finite admission routes using the
  preceding theorem, without a new induction.

All these equalities hold for arbitrary real weights, including
repeated outcomes. No assumption of independence, positive weights
or normalized total mass is required to establish the identities.
To interpret the resulting masses as genuine probabilities, the
usual nonnegativity and normalization requirements still apply.

The [proof-script register](PROOF_REFACTOR_REGISTER.md) now lists
**336 scripts individually and in source order**, including these
four additions and the refactored extensionality theorem. The
[documentation and inventory checker](../scripts/check_rocq_documentation.sh)
enforces the module headers, declaration-specific comments and
register completeness before Rocq 9.2 compilation. The 15 remaining
structural inductions are unchanged and have an explicit refactoring
disposition.

No previously named theorem statements were modified; this iteration
adds four named propositions and rewrites only the proof body and
adjacent commentary of `finite_prob_event_ext_on_samples`. The report
data, historical evidence and previously verified SPARK/Python sources
are unaffected.

## Previous continuation: remove weighted covariance induction by finite-sum laws

A new theorem, `covariance_of_general_weighted_second_unconditional`,
proves

\[
\operatorname{Cov}\!\left(f,\sum_{i} a_i g_i\right)
=\sum_i a_i\operatorname{Cov}(f,g_i)
\]

for any finite component list, **without requiring total sample
mass to equal one**. It follows from finite-sum interchange and
linearity of the explicitly defined expectation; covariance is
algebraically linear in its second argument even for unnormalized
real weights. This does *not* claim that arbitrary signed weights
define a probability distribution.

The proof reuses the existing
`expectation_of_general_weighted_sum` theorem,
`FiniteSum.finite_sum_map`, `finite_sum_scale`,
`finite_sum_sub`, `finite_sum_ext` and `Stdlib.List.map`.
It introduces no extra recursion or covariance implementation.
The existing theorem `covariance_of_general_weighted_second`
preserves its original `total_mass = 1` hypothesis and its exact
proposition while delegating the proof to the stronger result.
**One domain-specific component-list induction is eliminated.**

The current inventory has **334 public theorem/lemma/example
declarations**, one additional checked local helper, and two proof-bearing
record constructions: **337 proof scripts** across seven modules.
Their source contains **391 named declarations**, all with mathematical
doc comments and comprehensive explanatory module headers.
The [proof-refactor register](PROOF_REFACTOR_REGISTER.md) accounts
for every proof, including the new and replaced proofs.
**14 structural induction scripts** remain, mostly for generic finite
folds, the natural-number recurrence and unordered-pair covariance.

The prior theorem statements and their hypotheses remain unchanged.
As throughout this project, the results concern finite algebraic
moments and do not establish empirical validity or Gaussianity.

### Precise semantics for foundational definitions

In addition to the 394 adjacent declaration comments and the seven
module headers, **19 core definition comments** have been rewritten
from generic template descriptions into declaration-specific
mathematical explanations. The changes cover the generic
`FiniteSum.finite_sum` fold; eight Boolean-event definitions
(including `Event`, `indicator`, `any_event`,
`sum_event_indicators`, `finite_prob`, and `union_prob`);
and ten finite-moment definitions (including `total_mass`,
`expect`, `covariance`, `variance`,
`centered_second_moment`, and weighted-score combinations).

The updated comments spell out how **duplicates contribute by
list position**, why arbitrary **negative or unnormalized real
weights still define algebraic sums**, and exactly which
**nonnegativity and normalization premises** are required
for probability, nonnegative variance or centered-covariance
interpretations. The comments also name the precise Stdlib
`List.map`, `List.fold_right`, `List.existsb`,
`Bool` and shared `FiniteSum` constructions reused.
No declaration statement or executable proof was changed
during this documentation-only improvement.

## Previous continuation: general finite-sum partition and filtered-event bounds

The current source adds one general and two event-specific results.
**There are now 337 publicly named theorem/lemma/example declarations,
one local helper and two explicitly proved record constructors:
340 proof scripts in all**. The seven Rocq modules contain
**394 named declarations**, each with a detailed declaration-specific
`(** ... *)` comment. Every module begins with a substantive
explanatory header. A
[proof-by-proof register](PROOF_REFACTOR_REGISTER.md) records the
source order, standard-library dependencies and proof methods for all
340 scripts. GitHub Actions checks the register for completeness.

The new `FiniteSum.finite_sum_filter_partition` is the reusable
finite-list identity

\[
\sum_{x\in\operatorname{filter}(p,L)} f(x)
+ \sum_{x\in\operatorname{filter}(\neg p,L)} f(x)
= \sum_{x\in L} f(x).
\]

Here summation means the explicit list fold, so any repeated elements
retain their multiplicity and the real-valued integrand may have
either sign. The proof directly invokes the previously checked
`finite_sum_filter`, `finite_sum_add`, `finite_sum_ext`,
`Stdlib.List.filter` and standard Boolean/ring operations, without
introducing another recursive summation implementation.

Two new distribution-free consequences are
`finite_prob_filtered_mass_le` and
`union_prob_filtered_mass_le`. They assert that restricting
enumerated outcomes cannot increase an event's or union's mass
when the original sample weights are nonnegative. They use
`Stdlib.Bool.andb_true_iff`, the existing
`finite_prob_event_monotone` and the checked finite event family
abstraction. **No independence or unit-total-mass premise** is needed
for these inequalities.

Two older proofs were simplified in this continuation:
`finite_prob_filtered_partition` now delegates to the new
generic list-sum theorem; `finite_prob_complement` derives the
event-complement identity from that same theorem and the
established event-mass-as-filtered-sum equivalence instead of
repeating indicator arithmetic. Their exact statements are preserved.

**Structural induction count remains 14**, restricted to basic
generic folds, the recurrence and suffix-dependent covariance.
All theorem hypotheses remain explicit. These identities are
finite list-weight statements, not claims about empirical
psychometrics, continuous distributions or inferred Gaussianity.

### Theorem-by-theorem semantic commentary audit

In addition to full documentation for the five new identities,
this iteration rewrites the descriptions of **eight existing
foundational theorems** whose earlier comments were syntactically
complete but too generic: three in `FiniteBridge`,
three in `FiniteMoments`, and two in `FiniteUnion`.

The revisions specify (a) which identities hold for arbitrary
signed real weights, (b) when nonnegative normalized weights
are required to interpret a mass as probability or assert
variance nonnegativity, (c) why Boolean independence is
equivalent to zero *indicator* covariance but not generally
to zero covariance of arbitrary scores, (d) how the
Cauchy–Schwarz inequality follows from finite variance
nonnegativity, and (e) that the stated finite covariance
matrix nonnegativity result concerns the supplied coefficient
vector, rather than an unstated strict positive-definiteness
claim. They also distinguish **appending sample lists** from
**appending event-family lists**, preserving the meaning of
duplicate elements in each.

These are comment-only changes: the theorem definitions,
parameters, assumptions, proof bodies and kernel-checked
conclusions are unchanged.

## Previous continuation: filtered sample concatenation and indicator-score bridges

**Current Rocq inventory:** 342 public theorem/lemma/example declarations
across seven modules (Hoeflin 64; Admissions 67; FiniteUnion **54**;
FiniteMoments 108; FiniteSum 20; FiniteBridge **16**;
FourCellBridge 13). One existing local lemma and the two explicitly
proved two-event model constructors bring this to **345 complete
`Proof.` scripts**. There are **399 named declarations**, including
records and definitions. All 399 have explanatory adjacent
`(** ... *)` comments; all seven Rocq modules retain substantive
opening explanatory headers.

This continuation establishes five new identities, reusing
existing library and already checked results:

- `FiniteUnion.union_prob_sample_append`: union mass on a
  concatenated sample list equals the sum of the masses on its
  two input lists. Its proof simply specializes
  `finite_prob_sample_append` to the existing `any_event`.
- `FiniteUnion.finite_prob_filtered_append`: filtered event mass
  over concatenated samples is additive. The proof uses the
  **Stdlib.List.filter_app** law and `finite_prob_sample_append`.
- `FiniteUnion.union_prob_filtered_append`: the corresponding
  sample concatenation identity for an arbitrary family of
  Boolean events; it delegates to `filter_app` and
  `union_prob_sample_append` without an event-list induction.
- `FiniteBridge.filtered_event_mass_is_indicator_expectation`:
  mass of an event after sample selection equals the expectation
  on the original sample of the indicator of the selection-event
  conjunction. The proof composes the checked filtered-mass
  correspondence with the existing event-to-moment bridge.
- `FiniteBridge.filtered_union_mass_is_indicator_expectation`:
  similarly expresses selected-sample union mass as the
  indicator-score expectation of selection AND the finite
  Boolean family union, using `Stdlib.List.existsb`.

An existing proof, `FiniteUnion.union_prob_append`, now invokes
`finite_prob_event_ext_on_samples` and `any_event_append`
(which already delegates to **Stdlib.List.existsb_app**) instead
of duplicating finite-sum extensionality.

**Assumption audit:** All five new equalities hold for arbitrary
finite lists, including duplicate occurrences, and arbitrary
real weights, including signed values. They do not silently
assume independence, nonnegative weights, disjoint events or
unit total mass. For probabilistic interpretations those
conditions must be supplied separately as appropriate.
None of the equalities claims a conditional probability,
continuous measure, or empirical psychometric inference.

The full [proof-by-proof register](PROOF_REFACTOR_REGISTER.md)
lists **all 345 scripts**, with exact source-order coverage
enforced by the documentation checker before Rocq 9.2
kernel validation. There are still **14 structural inductions**,
limited to generic fold/list algebra, the `Nat.iter`
recurrence and suffix-sensitive finite covariance properties.
No preexisting theorem statement was changed, no new
recursive filter/sum implementation was added, and historical
Python/SPARK verification evidence remains untouched.

## Previous continuation: unconditional composite and covariance-matrix algebra

This continuation proves five new Rocq theorem statements, all reusing
established finite weighted-sum and covariance laws:

| New theorem | Formal mathematical result | Reused checked theorem(s) |
|---|---|---|
| `covariance_of_general_weighted_sums_unconditional` | Covariance of two finite weighted score composites equals their double weighted component covariance sum, with no total-mass premise | `covariance_of_general_weighted_second_unconditional`, `covariance_symmetric`, `FiniteSum.finite_sum_ext` |
| `variance_of_general_weighted_sum_unconditional` | Self-covariance/variance of a composite equals its coefficient covariance quadratic form | `covariance_of_general_weighted_sums_unconditional` |
| `covariance_cross_matrix_bilinear_identity_unconditional` | Matrix bilinear form for two component lists is their composite covariance | `covariance_double_sum_as_matrix_product` and the unconditional composite covariance theorem |
| `covariance_cross_matrix_bilinear_swap_unconditional` | Swapping both component lists leaves the evaluated cross-covariance bilinear form unchanged | Unconditional cross-matrix bilinear identity, `covariance_symmetric` |
| `covariance_matrix_quadratic_form_is_variance_unconditional` | A composite's covariance-matrix quadratic form equals its variance | `covariance_matrix_quadratic_form_identity` and the unconditional composite variance theorem |

The five existing total-mass-one versions of these identities preserve
their **original propositions, including every premise**, but their
proof bodies now delegate directly to the corresponding stronger
unconditional theorems. Every newly added statement has a detailed
adjacent `(** ... *)` comment explaining the mathematics, exact
proposition, assumptions, proof method, library dependencies and scope.

**Why removing the mass assumption is sound:** The finite algebraic
definition `Cov(f,g) = E[fg] - E[f] E[g]` is bilinear for any real-valued
linear functional `E`. It does not require `E[1]=1`.
The matrix identities in this section are exact identities between
finite real expressions. They do **not** imply nonnegative variance,
matrix positive semidefiniteness or a valid probability distribution
for arbitrary signed or unnormalized sample weights. The separate
positive-semidefiniteness and covariance bounds continue to require
their explicit nonnegative/normalized sample-weight hypotheses.

The current seven Rocq modules have **347 public theorem/lemma/example
declarations** (Hoeflin 64; Admissions 67; FiniteUnion 54;
FiniteMoments **113**; FiniteSum 20; FiniteBridge 16;
FourCellBridge 13), one local helper and two proof-bearing record
constructors, for **350 proof scripts**. All **404 named declarations**
have extensive adjacent documentation; each of the seven modules has
its required explanatory header.

The [complete proof register](PROOF_REFACTOR_REGISTER.md) is checked
by CI for the exact order and names of all 350 scripts.
**Fourteen structural inductions** remain, where the underlying
generic fold, `Nat.iter` recurrence or suffix-dependent covariance
model requires them. No new list fold, matrix construction, axiom,
`Admitted`, external library or modification to historical
Python/Deal/SPARK evidence was introduced.

## Current continuation: normalization-free unweighted score-list algebra

After the matrix and weighted composite refactors, the remaining
unweighted score-list covariance lemmas could also be generalized
**without introducing list induction or a new summation definition**.
The original code already represents a list of unweighted scores
using `Stdlib.List.map (fun g => (1,g))`; this converts each score
to a unit-coefficient weighted composite and permits direct use
of the stronger, already checked covariance theorems.

Three new formal results are now available:

- `covariance_with_sum_scores_unconditional`: for arbitrary score
  `f` and score list `fs`, covariance of `f` against
  `sum_scores fs` is the sum of pairwise covariances.
  Uses `unweighted_scores_as_linear_combination`,
  `unweighted_covariance_row_as_weighted`,
  `covariance_extensional`, `Stdlib.List.map`,
  and `covariance_of_general_weighted_second_unconditional`.
- `covariance_of_sum_scores_unconditional`: covariance of two
  arbitrary finite score-list sums equals the complete double
  covariance sum, by the previous theorem, covariance symmetry
  and `FiniteSum.finite_sum_ext`.
- `variance_of_unweighted_sum_unconditional`: variance of a
  finite score-list sum equals the self-covariance double sum,
  as an immediate specialization of the preceding theorem.

The original `covariance_with_sum_scores`,
`covariance_of_sum_scores` and `variance_of_unweighted_sum`
statements keep the exact `total_mass = 1` hypothesis for
source compatibility; their proof bodies now delegate to the
unconditional versions. Each new declaration has a complete
theorem-level comment explaining meaning, exact type, premises,
library use, proof method and finite-model boundaries.

**Mathematical distinction:** The expressions remain exact real
algebra even if the outcome weights are signed or unnormalized.
Nonnegative variance, stochastic interpretation, or positive
semidefiniteness must not be inferred from this extension.
Those properties require the separately stated nonnegative and
normalized distribution hypotheses. No new real-valued matrix,
event, expectation or list-fold implementation was introduced.

The seven Rocq modules contain **350 public theorem/lemma/example
declarations** (Hoeflin 64; Admissions 67; FiniteUnion 54;
FiniteMoments **116**; FiniteSum 20; FiniteBridge 16;
FourCellBridge 13), one local helper and two explicit record
constructions, for **353 complete proof scripts**. All **407
named declarations** have adjacent detailed doc comments and all
seven modules retain their explanatory file headers.
The [proof-by-proof register](PROOF_REFACTOR_REGISTER.md) inventories
every script in source order, checked by the documentation gate
before Rocq 9.2 compilation. **Fourteen structural inductions**
are retained where required by the underlying generic fold,
`Nat.iter` or suffix-dependent covariance structure.

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

## Four-cell conditional event interpretation (November 8)

Five new declarations in `FourCellBridge.v` equate all four report
conditionals with their finite Boolean event-mass ratios, relying on
existing normalized marginal, intersection and union theorems. The
additional B-only event theorem is a direct Boolean-product calculation.
Each conditional ratio has an explicit positive conditioning-mass premise;
none assumes route independence or claims empirical validity. They add
no new event summation, matrix operation, or mathematical axioms.

Current source totals: **359 public checked claims**, **362 explicit proof
scripts**, **417 named declarations**, with full documentation and an
ordered proof-refactor register.

## Generic finite conditional probability (further November 8 continuation)

`FiniteUnion.finite_conditional_prob` is a thin quotient of existing
finite Boolean-event masses, not a new probability measure. Its
`finite_conditional_prob_filtered` theorem reuses the existing
`finite_prob_on_filtered_samples` result, and
`finite_conditional_prob_self` proves that a positive-mass event has
conditional probability one given itself. Two new FourCellBridge
corollaries connect B-given-A and A-given-B to this shared operator
without altering the earlier four-cell statements.
The complete seven-module declaration inventory is now 417 named
items, 359 public theorem/lemma/example declarations, and 362
proof scripts including the local helper and two record constructors.

## Generic conditional-event bounds (November 8 continuation)

Three new `FiniteUnion.v` theorems prove the conditional [0,1]
interval for nonnegative weights and positive conditioning mass,
insensitivity to changes of the target event outside the enumerated
samples, and the event/complement conditional partition identity.
The proofs reuse existing finite Boolean event laws,
`Stdlib.List.filter`, real order and field lemmas, without adding
any probability-measure implementation or custom recursion.

At this earlier stage: **362 public theorem/lemma/example declarations**,
**365 explicit proof scripts** and **420 fully documented named
declarations**, all within seven original Rocq modules.

## Completion of the generic four-cell conditional bridge

Two further FourCellBridge proofs reuse the exact finite-event support
extensionality, two-event union identity and `Stdlib.Bool.andb_comm` to
identify both-given-either and not-A-given-B as specializations of the
shared `FiniteUnion.finite_conditional_prob` operator. These complement
the two existing A|B and B|A generic conditional results.

That earlier stage contained **364 public claims**,
**367 proof scripts** and **422 fully documented declarations**. All
existing named theorem propositions are unchanged. Nothing here proves
empirical event independence or Gaussian admission tail estimates.

## Stronger conditional-support properties and a proof refactor

Four further generic conditional theorems strengthen target-event
extensionality to the outcomes actually accepted by the conditioning
event, prove monotonicity under Boolean implication, show that a true
target event has conditional mass one when conditioning is positive,
and establish conditioning-event extensionality on the sampled support.
The previous whole-sample target-extensionality proof now delegates
to the stronger result. All use existing `FiniteUnion` identities,
`Stdlib.Bool` and real order lemmas, not new finite sum recursions.

At the previous stage the inventory comprised **368 public claims**,
**371 audited proof scripts**, **426 documented named declarations**.

## Finite conditional-event algebra and total probability

Additional `FiniteUnion.v` theorems show that the impossible event has
zero conditional mass, that conditional Boolean events satisfy the
same inclusion–exclusion identity as their original finite masses,
that conditional probabilities satisfy the symmetric Bayes balance
identity under strictly positive conditioning marginals, and that
partitioning by an event and its complement proves the finite law
of total probability. The proofs are direct applications of already
checked `finite_prob_inclusion_exclusion`,
`finite_prob_filtered_partition` and `finite_prob_event_ext_on_samples`
plus Rocq Stdlib Boolean/real algebra; no new recursions were added.

At the previous stage: **372 public theorem/lemma/example declarations**,
**375 registered proof scripts** and **430 documented named declarations**.

## Conditional chain rule and covariance-matrix null consequences

A generic finite conditional chain rule reduces nested intersections to
the existing `finite_prob` identities, `Stdlib.Bool.andb_assoc`
and real-field cancellation with two strictly positive marginals.

Three `FiniteMoments.v` results extend the already checked fixed-basis
covariance matrix: a Cauchy–Schwarz bound against any comparison score,
zero covariance with every score in a zero-quadratic-form direction,
and equality of the weighted score totals at any pair of positive-mass
sampled outcomes in that direction. These reuse
`fixed_basis_weighted_variance_identity`, finite Cauchy–Schwarz,
and the established zero-variance and support theorems without
reimplementing matrix-vector arithmetic or assuming a spectral basis.

At that preceding stage, the seven-module inventory comprised **376 public claims**,
**379 registered proofs** and **434 documented named declarations**.

## Explicit nonzero null direction for a duplicated score basis

The new `variance_of_constant_score_zero` theorem reuses the
checked covariance-with-constant law. A concrete result,
`duplicate_basis_nontrivial_null_direction`, then proves that
two identical score functions in basis `[f; f]` admit the nonzero
coefficient vector `[1; -1]` with covariance quadratic form zero.
The proof reuses `fixed_basis_weighted_variance_identity`,
`variance_extensional`, `Stdlib.List.combine` and the common
finite-sum implementation. This supplies a concrete degeneracy
witness but does **not** certify an arbitrary rank or eigenvalue.

At that earlier stage: **378 public claims**, **381 proof scripts**,
**436 fully documented named declarations** across seven Rocq files.

## Finite-moment extensionality on enumerated support

New `expectation_extensional_on_samples`,
`covariance_extensional_on_samples`, and
`variance_extensional_on_samples` results replace global
pointwise equality with equality only at sampled outcomes. They
reuse `FiniteSum.finite_sum_ext_in` and Stdlib.List.map_ext_in
rather than building new finite sums, and preserve the original
finite-list multiplicities without extra hypotheses.

At the preceding stage: **381 public claims**, **384 proof scripts**,
and **439 documented named declarations** in seven modules.

## Exact positive-support characterization of covariance null directions

Five `FiniteMoments.v` results prove positive-weight-support
extensionality for expectation, covariance and variance, and
derive zero variance when the score is constant on that support.
The final iff theorem proves that the fixed-basis covariance
quadratic form vanishes **exactly when** the corresponding
weighted score equals its expected value on every sampled
outcome of positive weight. All claims allow zero-weight
outcomes and use Stdlib real order plus FiniteSum extensionality,
the existing variance identity, and prior nullity theorems.

At that preceding stage there were **386 public claims**,
**389 registered proof scripts** and **444 documented declarations**.

## Null-direction equivalences and a proof refactor

Generic finite variance is now proved zero iff the score is constant
on positive-weight sampled outcomes, and also iff it has zero
covariance with every comparison score. The fixed-basis covariance
null/constant iff proof is refactored to reuse the first theorem;
a second fixed-basis iff uses the covariance-orthogonality theorem.
This is a strictly algebraic finite-outcome characterization,
not an arbitrary matrix rank function or spectral algorithm.

At the preceding stage: **389 public theorem/lemma/example
declarations**, **392 proof scripts**, **447 documented names**.

## Strict variance and quadratic-form positivity witnesses

Four new results show strict finite variance positivity from a
positive-weight outcome deviating from the mean, or from a pair
of positive-weight outcomes with unequal score values. Their
fixed-basis covariance-matrix analogues use the checked
fixed_basis_weighted_variance_identity to transfer those
strict inequalities to quadratic forms. No determinant, eigenvalue
or matrix-rank routine was introduced.

At the previous stage there were **393 public claims**, **396 proof scripts**
and **451 fully documented declarations** in seven Rocq modules.

## Positive-definiteness and support-nonconstancy equivalences

Three finite weighted-score results identify strictly positive
variance and fixed-basis quadratic form with the absence of a
constant positive-weight score. Using Stdlib.List.repeat for the
zero coefficient vector, a general equivalence states that all
nonzero compatible coefficient vectors yield strictly positive
covariance quadratic form precisely when none yields a constant
weighted score on positive-weight support. The two previous
positive-variance witness proofs now reuse this generic lemma.
This is a finite-list positive-definiteness characterization;
spectral matrix rank and determinant algorithms are deliberately
not implemented.

At the preceding stage: **396 public claims**, **399 proof scripts**,
**454 documented named declarations** across seven Rocq modules.

## Positive-definiteness witnesses and zero-covariance characterization

The newest `FiniteMoments.v` theorems provide two sufficient
conditions for positive definiteness of a finite fixed-basis
covariance matrix: every nonzero coefficient vector must
separate two positive-weight sampled outcomes, or differ
from its expected score at a positive-weight outcome.
A further iff theorem characterizes strict positive
definiteness as the absence of a nonzero direction
uncorrelated with every finite comparison score. These
are direct applications of existing null/strict-variance
theorems, without new rank, determinant or list recursion.

At the preceding stage: **399 public claims**,
**402 proof scripts**, **457 fully documented named declarations**.

## Finite support-constant covariance and variance equivalences

Three additional `FiniteMoments.v` theorems show that a score
constant on positive-weight sampled support has zero covariance
with any score in either argument, and characterize zero
variance by the existence of a constant supported by all
positive-weight observations. The prior zero-variance
converse proof now delegates to the generic covariance-zero
lemma. These changes reuse Stdlib, existing support-extensional
moment lemmas, and symmetry rather than implementing new sums.

**Earlier inventory: 402 public claims, 405 proof scripts,
460 fully documented named declarations** across seven modules.

## Existential finite covariance nullity and duplicate-score obstruction

Four further `FiniteMoments.v` theorems use the established
support-constant variance criteria and fixed-basis variance
bridge to characterize strict variance positivity and matrix
null/positive quadratic forms through the existence of an
arbitrary common positive-support score value. The concrete
duplicate-basis covariance result rules out positive definiteness
from the existing nonzero [1;-1] null direction using
Stdlib.List.repeat. No new list, matrix, rank or eigenvalue
implementation has been introduced.

**Earlier source totals: 406 public claims, 409 proof scripts,
464 documented named declarations** across seven Rocq modules.

## Affine transformations of finite covariance matrices

Two newly verified finite-moment matrix theorems lift the
pre-existing scalar `covariance_of_affine_scores` law to
rectangular cross-covariance matrices and square fixed-basis
covariance matrices. The former scales entries by the product
of the two affine slopes; the latter scales entries by the
square of a common slope. Additive score offsets cancel
under unit total mass. The proof uses Stdlib.List.map_map
and map_ext at both levels, then reuses the established
cross-matrix representation; there is no new matrix
library, recursive list traversal or custom linear algebra.

**Earlier source totals: 408 public claims, 411 proof scripts,
466 documented named declarations** in seven Rocq files.

## Affine dependence and finite covariance degeneracy

Three new theorems generalize the previous duplicate-score
quadratic nullity result. Affine-dependent scores on all sampled
outcomes yield a nonzero [1;-a] null coefficient vector even for
signed normalized weights. The former duplicate-score proof now
uses this stronger theorem rather than repeating its finite sum.
A positive-weight-support version permits zero-weight exceptions
under nonnegative normalized weights, and yields a concrete
obstruction to covariance positive definiteness. These are exact
two-score statements, not full spectral rank results.

**Earlier source totals: 411 public claims, 414 proof scripts,
469 documented named declarations** in seven Rocq files.

## Covariance nullity from finitely many basis coordinates

Three results in `FiniteMoments.v` characterize quadratic-form
nullity through zero covariance with each member of the finite
score basis, rather than all possible comparison score functions.
The converse folds individual zero covariance values with the
existing `covariance_of_general_weighted_second_unconditional`
and library-backed `FiniteSum.finite_sum_ext_in` and
`finite_sum_zero` lemmas. A strict-positive quadratic iff
and an all-nonzero-directions positive-definiteness iff
follow from the existing positive-semidefinite theorem.
No new matrix rank, nullspace, list sum or eigenvalue library
is implemented.

**Earlier source totals: 414 public claims, 417 proof scripts,
472 fully documented named declarations** across seven modules.

## Covariance row-dot identities and matrix nullity

A new theorem identifies covariance with a coefficient-weighted
basis score as the dot product of that coefficient list with
the comparison score's covariance row. It reuses existing
weighted covariance and covariance-row lemmas, plus
Stdlib.List.map_map and canonical List.combine projections.
A second result proves that covariance quadratic nullity is
equivalent to the coefficient vector having zero dot product
with each actual row of the list-of-lists covariance matrix,
using Stdlib.List.in_map_iff and the existing coordinate-level
nullity result. No new matrix product or rank implementation
is needed.

**Earlier totals: 416 public claims, 419 proof scripts,
474 fully documented named declarations** in seven Rocq files.

## Matrix-row positive-definiteness equivalence and comment audit

Two additional theorems identify strict positive covariance
quadratic curvature with a nonzero dot product against at least
one covariance matrix row, expressed constructively as the
negation of zero for all rows, and identify positive definiteness
with the absence of nonzero vectors in the row-dot kernel.
They reuse the rowwise nullity iff and checked positive
semidefiniteness rather than implementing matrix operations.

Detailed declaration comments were rewritten on the six core
dependencies vector_dot, basis_covariance_matrix,
basis_cross_covariance_matrix, covariance_row_as_vector_dot,
basis_of_combine, and fixed_basis_covariance_matrix_positive_semidefinite,
including exact truncation/length/weight assumptions and the
actual Stdlib/FiniteSum proof dependencies.

**Earlier counts: 418 public claims, 421 proof scripts and
476 documented named declarations** across seven Rocq modules.

## General quadratic-null obstruction to positive definiteness

Two new theorems formalize a finite arbitrary-basis obstruction:
any nonzero compatible coefficient vector whose covariance
quadratic form is zero prevents strict positive definiteness;
no normalization or sign constraint is necessary for this
algebraic contradiction. A stronger model-specific corollary
uses the supported-constant nullity equivalence for normalized
nonnegative sampled weights. The existing duplicate-score
and affine-dependent pair proofs now reuse the general theorem,
eliminating duplicated strict-positivity reasoning.

Earlier source inventory: **420 public claims, 423 proof scripts,
478 documented named declarations** across seven Rocq modules.

## Positive-support constants and covariance row-kernel witnesses

Two additional results use the previously established null
quadratic-form equivalences. A composite score constant on
positive-weight sampled outcomes yields a coefficient vector
whose dot product with every row of its finite covariance
matrix is zero. A compatible nonzero vector with this rowwise
property prevents strict positive definiteness, by direct
reuse of the general quadratic-null obstruction lemma.
The proof introduces no matrix product, kernel basis, rank
or numerical algorithm.

Earlier audited inventory: **422 public claims, 425 proof scripts,
480 documented named declarations** in seven Rocq modules.

## Exact covariance row-kernel and support-constant equivalence

The row-dot kernel of the finite covariance matrix is exactly
the set of compatible coefficient vectors whose composite
scores equal some constant on every positive-weight sampled
outcome, under unit total mass and nonnegative sampled weights.
Positive definiteness is equivalently the absence of such a
nonzero compatible direction. Both iff results use existing
covariance nullity and strict positivity lemmas without a new
matrix operation or rank computation.

Five core declarations were also redocumented with detailed
mathematical definitions and precise Stdlib/FiniteSum reuse:
matrix_bilinear_form, matrix_quadratic_form,
weighted_basis_sum, fixed_basis_weighted_variance_identity,
and zero_variance_is_constant_on_positive_mass.

Current audited totals: **573 public claims, 576 proof scripts,
639 documented declarations** across seven Rocq modules.


## Generic finite conditional-independence interface

The finite Boolean-event model now exposes the transparent
`finite_conditional_independent` predicate: the conditioning event must
have strictly positive mass and the conditional intersection mass must equal
the product of the two conditional marginals. Ten new checked theorems
establish that conditional intersection is symmetric, conditional independence
is symmetric, and that the independence predicate is invariant under changes
to either target event or the conditioning predicate outside the
enumerated finite sample. Reordering the same weighted sample multiset also
preserves the independence predicate by Stdlib permutation invariance.
A conditional event-partition identity further proves independence is
preserved by complementing the first target, the second target, or both,
using only the existing conditional inclusion–exclusion and complement laws.

These results reuse `Stdlib.Bool.andb_comm`, the already checked
conditional-event extensionality lemmas, and real multiplication
commutativity. They add no second conditional-probability implementation,
finite-list traversal, Gaussian assumption, or external measure-theory axiom.
Signed weights remain algebraically meaningful but require nonnegativity for
probability interpretation; no unit-mass normalization is assumed.
The interface is a starting point for future conditional-independence
cross-product factorization and stronger four-cell bridge rules, not a certified stochastic process model.

Current audited totals: **573 public claims, 576 proof scripts,
639 documented declarations** across seven Rocq modules.

## Generic conditional independence specialized to the four-cell model

Two finite-union theorems show that normalizing the underlying outcome
list to total mass one turns conditioning on the universally true event
into ordinary event mass. Under the same normalization, the generic
`finite_conditional_independent` predicate is equivalent to the exact
joint-event product of its two marginal event masses.

Two new `FourCellBridge.v` theorems instantiate that result with the
already verified Boolean-pair enumeration and four-cell model weights:
generic independence of A and B given true is equivalent both to
`p_both m = p_A m * p_B m` and to
`joint m * neither m = only_A m * only_B m`. The latter equivalence
delegates to `Admissions.binary_independence_criterion`; there is
no new four-cell enumeration, cross-product calculation, or assumption
of observed independence. All results retain the existing normalized,
nonnegative four-cell interpretation.

Current audited totals: **573 public claims, 576 proof scripts,
639 documented declarations** in seven Rocq modules.

## Degenerate Boolean-event independence laws

Four new kernel-checkable consequences of the generic finite
conditional-independence interface show that the always-true and
always-false events are each conditionally independent of any other
Boolean event in either target position, whenever the conditioning
event has strictly positive finite mass. The first-target results
reuse conditional event extensionality and the checked unit/zero
conditional-mass laws; their reverse-order partners use only
the already checked symmetry theorem. No new list recursion, event
sum, or conditional quotient is introduced.

Current audited totals: **573 public claims, 576 proof scripts,
639 documented declarations** in seven Rocq files.

## True-conditioning independence and zero indicator covariance

Two new bridge theorems compose previously checked propositions
without expanding event sums or covariance polynomials. In `FiniteBridge`,
unit finite total mass makes conditional independence given the certain
event equivalent to zero finite covariance of the two event-indicator
scores. In `FourCellBridge`, the same equivalence holds for the
normalized, nonnegative four-cell admissions model by direct
instantiation of the general result and `four_cell_total_mass`.
The formalization does not assume that observed admissions are
independent and does not generalize zero covariance to independence
of arbitrary real-valued scores.

Current audited totals: **573 public claims, 576 proof scripts,
639 documented declarations** in seven Rocq modules.

## Finite conditional independence as a cross-product equation

Under strictly positive conditioning mass, a new `FiniteUnion`
theorem equates generic conditional independence with the
denominator-free identity

```text
P(G and A and B) * P(G) = P(G and A) * P(G and B)
```

where `P` is the shared finite weighted Boolean-event mass.
The proof reuses the existing conditional quotient and positive
denominator cancellation by the standard real-field tactic.
The equality needs no unit-mass normalization and remains algebraic
for signed weights; interpreting it probabilistically requires
nonnegative sample weights. No additional conditional probability
operator or finite-sum implementation is introduced.

Current audited totals: **573 public claims, 576 proof scripts,
639 documented declarations** across seven Rocq modules.

## Conditioning-event independence and finite union factorization

Two results show that a strictly positive-mass conditioning event
is conditionally independent of any other Boolean target when
that event itself occupies either target position. The proofs
reuse the existing conditioned-support extensionality and symmetry
results rather than rebuilding the finite event sum.

A third theorem specializes conditional inclusion–exclusion under
the already checked conditional-independence factorization:
`P(A or B | G) = P(A | G) + P(B | G) - P(A | G)*P(B | G)`.
This is a two-event finite algebraic identity, not an extension
to mutually independent families of events.

Current audited totals: **573 public claims, 576 proof scripts,
639 documented declarations** in seven Rocq modules.

## Three-event conditional factorization

A new checked finite Boolean-event theorem proves

```text
P(A and B and C | G) = P(A | G) * P(B | G) * P(C | G)
```

under the **two explicit hypotheses** that A is conditionally
independent of B given G and that (A and B) is conditionally
independent of C given G. Three merely pairwise conditional
independence premises are deliberately **not** treated as sufficient.
The proof delegates to the existing two-event conditional
factorization and Stdlib.Boolean conjunction associativity, without
introducing a new list fold or general mutual-independence axiom.

Current audited totals: **573 public claims, 576 proof scripts,
639 documented declarations** in seven Rocq modules.

## Conditional-support refactoring of the independence interface

The generic conditional-independence API now has checked target
extensionality for **both targets on conditioned sample support**:
two target predicates need agree only at enumerated outcomes for
which the conditioning event is true. This strengthens the older
theorem requiring agreement on every outcome and makes the older
first-target theorem a short corollary rather than a duplicate
conditional quotient calculation.

Two consequences show that the complement of the conditioning
event is conditionally independent of any target under the
original positive-mass conditioning event. They reuse the already
checked impossible-event theorem, stronger support extensionality
and independence symmetry. No additional weighted summation or
probability definition is introduced.

Current audited totals: **573 public claims, 576 proof scripts,
639 documented declarations** in seven Rocq modules.

## Finite conditioning by standard-library list filtering

Three checked representation results identify `P(A|G)` on an
original weighted sample with `P(A|true)` after filtering
the sample by `G`. The generic conditional-independence
predicate is likewise equivalent to the true-conditioned
predicate on the filtered list, including its strict positive
mass guard. A third theorem restates the denominator-free
conditional-independence cross product directly in terms of
the filtered sample's mass and its event marginals.

The proofs reuse `Stdlib.List.filter`, previously checked
`finite_prob_on_filtered_samples` and
`finite_prob_as_filtered_mass`, and the generic
cross-product theorem. No new event sums, conditional quotients,
or probability wrappers are introduced. Zero-denominator cases
remain algebraic and are not interpreted as probabilities.

Current audited totals: **573 public claims, 576 proof scripts,
639 documented declarations** in seven Rocq modules.

## Arbitrary finite conditional event products

The event-intersection operator `all_events` is the standard
`Stdlib.List.forallb` applied to a finite list of Boolean
predicates. The report-specific `finite_conditional_prefix_independent`
predicate records the exact factorization assumptions along
each suffix of that list. Under positive conditioning mass, a
checked induction now proves

```text
P(all events | G) =
  fold_right (*) 1 (map (fun A => P(A | G)) events)
```

when each current event is independent (given G) of the
**conjunction of all remaining events**. This is explicitly
stronger than pairwise independence. Companion theorems
validate event-list concatenation via `Stdlib.List.forallb_app`
and singleton intersection via standard computation.

The proof does not define a new finite sum or probability
quotient: conjunction and product use `forallb`, `map`,
`fold_right` and the existing conditional-independence API.

Current audited totals: **573 public claims, 576 proof scripts,
639 documented declarations** in seven Rocq modules.

## Conditional finite-family union and intersection bounds

Three checked inequalities extend the original report's
distribution-free union/intersection reasoning to a strictly
positive finite conditioning event. Any listed event has no
greater conditional mass than the union of all events;
the union's conditional mass is bounded above by the
original `arbitrary_union_bound` applied to the filtered
sample and divided by the conditioning mass. Dually, the
conditional intersection of the finite event list has
no greater mass than any of its members.

These proofs invoke `finite_conditional_prob_monotone`,
the existing `arbitrary_union_bound`, `List.filter_In`,
and `List.forallb_forall` rather than implementing new
probability sums, event-set recursion, or an independent
conjunction calculus.

Current audited totals: **573 public claims, 576 proof scripts,
639 documented declarations** across seven Rocq modules.

## Direct finite conditional Boole union bound

The conditional upper bound is also checked in its familiar
marginal-sum form:

```text
P(any listed event | G) <=
  fold_right (+) 0 (map (fun A => P(A | G)) events)
```

for nonnegative sampled weights and strictly positive `P(G)`.
A reusable algebraic lemma uses the existing
`FiniteSum.finite_sum_scale` and `finite_sum_ext` lemmas to
factor out the common conditioning denominator from the
finite sum of event marginals. The final union theorem simply
composes that identity with the prior filtered conditional
union bound, without a second union-bound proof or new
finite-sum recursion.

Current audited totals: **573 public claims, 576 proof scripts,
639 documented declarations** across seven Rocq modules.

## Positive common scaling of finite outcome weights

Three checked lemmas establish the exact invariance under
a uniform strictly positive reweighting of the finite
outcome list. The finite event mass is homogeneous in
the weights by `FiniteSum.finite_sum_scale`; conditional
event masses cancel the common numerator/denominator
factor by Rocq's standard real-field tactic. The
explicit positive-conditioning guard and entire
conditional-independence predicate are preserved
in both directions. The original event list and all
multiplicities stay unchanged, and no new summation
or probability quotient is introduced.

Current audited totals: **573 public claims, 576 proof scripts,
639 documented declarations** across seven Rocq modules.

## Set-extensional finite event families and permutation invariance

Four checked results connect the previously defined
`all_events` operator to standard library membership and
permutation reasoning. The conjunction predicate is
determined entirely by event-list membership, independent
of duplicates and order, by `Stdlib.List.forallb_forall`.
`Stdlib.Sorting.Permutation.Permutation_in` then gives
event-list permutation invariance of both pointwise
conjunction and its conditional event mass. Finally,
conditional intersection mass is monotone when more
Boolean-event constraints are added, under the existing
nonnegative sampled-weight and positive conditioning-mass
assumptions.

These theorems reuse `finite_conditional_prob_monotone`,
the shared conditional target-event extensionality theorem
and Stdlib rather than adding more finite-list recursion.

Current audited totals: **573 public claims, 576 proof scripts,
639 documented declarations** across seven Rocq modules.

## Conditional indicator covariance under normalized filtered weights

A new `FiniteBridge` definition represents the normalized
weighted sample obtained by filtering on a strictly
positive-mass Boolean conditioning event and multiplying
each retained original weight by the reciprocal of the
conditioning mass. Two checked theorems establish that
the resulting finite weights sum to exactly one and
preserve nonnegativity of original sampled weights.

A third theorem composes the existing selected-sample
independence bridge, positive scaling invariance and
normalized indicator covariance equivalence to prove

```text
A independent of B given G  iff
  Cov_{filter G, normalized weights}(1_A, 1_B) = 0
```

for any positive-mass G. This is exact for finite
Boolean indicator scores; it makes no claim that
uncorrelated general real-valued scores are independent
or that arbitrary continuous conditional densities exist.

Current audited totals: **573 public claims, 576 proof scripts,
639 documented declarations** across seven Rocq modules.

## Exact conditional Bernoulli moments and covariance residual

Three new `FiniteBridge` results establish that an
original conditional event mass `P(A|G)` equals the
ordinary event mass on the G-filtered sample with
weights scaled by `1/P(G)`. By delegating to the
pre-existing Boolean-indicator variance and covariance
formulas, they also prove the exact finite identities

```text
Var(1_A | G) = P(A|G) * (1 - P(A|G))
Cov(1_A, 1_B | G) =
  P(A and B | G) - P(A|G)*P(B|G)
```

under strictly positive conditioning mass. The
covariance residual gives a second, directly interpretable
form of the general conditional-independence bridge.
Nonnegative original sample weights are still needed
for probability interpretations; none of the proofs
redefines the finite covariance or conditional quotient.

Current audited totals: **573 public claims, 576 proof scripts,
639 documented declarations** across seven Rocq modules.

## Normalized conditional indicator variance bounds

Three additional finite conditional Bernoulli lemmas are
proved solely by reusing the existing checked indicator
variance results on the normalized, filtered outcome list:
variance is at most one quarter; it equals zero exactly
when the conditional event mass is zero or one (under
positive conditioning mass); and complementing the target
preserves its conditional indicator variance (under
positive conditioning mass). The first upper bound is
an algebraic inequality for arbitrary real weights;
a statistical probability interpretation additionally
requires normalized, nonnegative selected weights.

The Python Deal audit is already enforced for **every
named function**, not just five decorators per file:
28 tracked Python files, 292 named functions, 1460 Deal
contracts and no violations on the pinned Python CI
verification for commit `001fdfe`. The minimum observed
number of distinct contracts per named function is five.

Current audited Rocq totals: **573 public claims, 576 proof scripts,
639 documented declarations** across seven Rocq modules.

## Conditional indicator covariance complement laws

A reusable `conditioned_weights_moment_total_mass_one`
bridge connects the normalized Boolean-filtered sample's
unit total mass to the `FiniteMoments.total_mass` API.
The existing conditional complement-variance proof
now uses this bridge rather than repeating the
model conversion.

Three new covariance theorems instantiate the checked
unconditional Bernoulli indicator complement laws on
this same normalized, selected finite sample:
complementing exactly one indicator reverses
conditional covariance sign, whereas complementing
both indicators leaves covariance unchanged.
Each result retains a strictly positive conditioning
mass requirement; nonnegative individual weights
are additionally needed for probabilistic semantics.

Current audited totals: **573 public claims, 576 proof scripts,
639 documented declarations** in seven Rocq modules.

## Cauchy–Schwarz and conditional degenerate-event independence

The existing `FiniteMoments.finite_covariance_cauchy_schwarz_squared`
is instantiated on the normalized conditioning-selected
finite sample to prove the conditional Boolean-indicator
covariance inequality, with positive mass and nonnegative
sample weights explicit. A second theorem imports the
existing zero-variance-implies-zero-covariance result
through the same finite-moment normalization bridge.

Combining the already checked
`zero indicator variance iff conditional mass is zero or one`,
the covariance zero consequence and the
`conditional independence iff zero indicator covariance`
bridge, the new theorems derive that any Boolean target
with **exact conditional mass zero or one** is independent
of any other Boolean event given G, in either target order.
These are real-algebraic, kernel-checked consequences of
existing finite moment results, not a claim that
near-extreme observed frequencies are independent.

Current audited totals: **573 public claims, 576 proof scripts,
639 documented declarations** across seven Rocq modules.

## Quantitative finite conditional Bernoulli covariance bounds

Using the checked selected-weight normalization, three
more theorems establish variance nonnegativity of
conditioned zero-one indicator scores and combine
`FiniteMoments.finite_covariance_cauchy_schwarz_squared`
with the exact indicator variance upper bound of 1/4
to prove `Cov(1_A,1_B | G)^2 <= 1/16` and its
signed consequence `-1/4 <= Cov(1_A,1_B | G) <= 1/4`.

The bounds require strictly positive conditioning mass
and nonnegative original sampled weights; neither event
independence nor whole-list mass normalization is needed.
All proof steps reuse existing finite moments and the
standard Rocq `nra` tactic, without manual covariance
sum expansion.

Current audited totals: **573 public claims, 576 proof scripts,
639 documented declarations** across seven Rocq modules.

## Dimension-preserving groundwork for covariance matrices

Five structural results in `FiniteMoments` prepare the
existing list-based covariance representation for a
checked finite-indexed matrix translation. They
show that the square basis covariance matrix is
the equal-left-right instance of the rectangular
cross-covariance matrix, that splitting a row-side
basis or column-side basis is compatible with
standard list appending, and that positional
matrix access by `Stdlib.List.nth_error` returns
the covariance of the selected score pair.
The latter gives a componentwise transpose law
using the previously proved scalar covariance
symmetry.

These are exact finite-list representation results;
they do not yet claim a dimension-indexed matrix
isomorphism, generic transpose operation, rank or
eigenvalue theorem. The implementation reuses
`Stdlib.List.map_app`, `combine`,
`nth_error_map`, and the existing scalar covariance,
rather than inventing custom matrix traversal.

Current audited totals: **573 public claims, 576 proof scripts,
639 documented declarations** across seven Rocq modules.

## Certified finite covariance rows and square symmetry

The rectangular covariance matrix now has a
`nth_error` row-selection theorem proving a selected
matrix row is exactly the covariance map of its
corresponding left-side basis score. Another theorem
proves every such row has the right-side basis length,
explicitly preserving the rectangular column dimension.

The square-basis covariance representation inherits a
checked selected-cell identity and componentwise
symmetry at every valid pair of basis positions from
the previous rectangular covariance entry/transpose
results. No new indexing algorithm, out-of-bounds
sentinel, matrix transpose operator or covariance
calculation is introduced.

Current audited totals: **573 public claims, 576 proof scripts,
639 documented declarations** across seven Rocq modules.

## First finite-indexed matrix representation with a checked cell bridge

The first dimension-indexed rectangular covariance
matrix is now represented by a function
`Fin.t (length left) -> Fin.t (length right) -> R`,
where bounded `Fin.t` indices select scores from
the standard `Vector.of_list` conversion.
This replaces unbounded lookup and its fallback
value with maintained Rocq `Fin` and `Vector`
types, retaining both rectangular dimensions.

A generic theorem uses `VectorSpec.to_list_nth_order`,
`to_list_of_list_opp`, `Fin.of_nat_to_nat_inv`
and `List.nth_error_nth'` to certify that a bounded
index retrieves the same element from a list
and its vector conversion. Applying the previously
checked list-matrix entry theorem establishes
**exact equality at every valid covariance cell**
between the old and new representations. The
indexed rectangular transpose law follows from
scalar covariance symmetry.

No rank, nullspace or continuous-distribution
conclusion is claimed yet. Those need separate
checked matrix-theory connections.

Current audited totals: **573 public claims, 576 proof scripts,
639 documented declarations** across seven Rocq modules.

## Total source-matrix access for bounded covariance indices

The new `indexed_basis_cross_covariance_matrix_entry_total`
theorem removes the row-existence premise from the
earlier list/vector covariance-entry bridge. For every
pair of `Fin.t` bounded row and column indices,
it constructs the corresponding actual list-matrix
row and proves successful `nth_error` lookups
return the same scalar as the indexed matrix.
This relies only on the certified vector/list
element conversion, existing covariance-row
selection and checked entry equality.

For a square score basis, the indexed matrix
also inherits exact symmetry directly from
the rectangular covariance swap theorem.
The representation is a dimension-safe,
fully checked transport of individual
covariance entries; rank and nullspace
algorithms remain separate unproved work.

Current audited totals: **573 public claims, 576 proof scripts,
639 documented declarations** across seven Rocq modules.

## Bounded covariance rows and diagonal-variance bridge

Four additional Rocq 9.2 source-level proof obligations make the
`Stdlib.Vectors.Fin`/`Vector` interface more directly useful:
`indexed_basis_cross_covariance_matrix_row` establishes that every valid
finite index selects an actual row of the original list matrix;
`indexed_basis_cross_covariance_matrix_row_length` certifies its exact
number of columns; `indexed_basis_covariance_matrix_diagonal` identifies
each diagonal cell with the corresponding score's variance; and
`indexed_basis_covariance_matrix_diagonal_nonnegative` applies the
preexisting variance theorem under explicit unit-mass and nonnegative
weight assumptions. The earlier total cell-bridge proof now reuses
the new row theorem instead of repeating its list/vector conversion.

These are finite algebraic facts, not a rank/nullspace algorithm or
a proof about continuous probability distributions. No new matrix
traversal, library dependency, axiom, Python code or changed source-pinned
verification artifact is introduced.

Current audited totals: **573 public claims, 576 proof scripts,
639 documented declarations** across seven Rocq modules.

## Indexed finite covariance inequalities and zero-variance support

Three direct, fully documented consequences of the checked vector/list
bridge extend the diagonal characterization. Under normalized, nonnegative
finite weights, `indexed_basis_covariance_matrix_cauchy_schwarz_squared`
bounds the square of an off-diagonal entry by the product of its two
diagonal cells. The theorem
`indexed_basis_covariance_matrix_diagonal_zero_iff_constant_on_support`
characterizes a zero diagonal as a selected score constant on every
positive-weight sample occurrence. Finally,
`indexed_basis_covariance_matrix_zero_diagonal_implies_zero_row`
proves that a zero diagonal forces its entire covariance row to vanish.

Each proof is reduced to an existing scalar finite-covariance theorem;
no new induction, custom matrix data structure or Gaussian assumption
is introduced. Rank-nullity remains a separate library-integration task.

Current audited totals: **573 public claims, 576 proof scripts,
639 documented declarations** across seven Rocq modules.

## Rectangular covariance nullity and two-coordinate minors

Six documented theorems extend the indexed `Fin.t` interface. The
rectangular covariance row/column theorems transport zero scalar
variance to arbitrary covariance entries with different left/right
score bases, using the already checked covariance symmetry. The
existing square zero-row proof now reuses the rectangular result.

The next three theorems certify that a zero square diagonal forces
the corresponding column to zero and that an entire zero row or column
is equivalent to its diagonal being zero, under normalized
nonnegative finite sample weights. The sixth theorem verifies the
nonnegative two-coordinate principal-minor expression
`M(i,i)*M(j,j)-M(i,j)*M(j,i)` from existing Cauchy-Schwarz and
indexed symmetry, including repeated indices.

No new list recursion, matrix algorithms, external dependencies,
axioms, Python modules, or historical source-pinned SPARK evidence
have been introduced. Rank-nullity and spectral decompositions
remain separate, unproved extensions.

Current inventory: **573 public claims, 576 proof scripts,
639 documented declarations** across seven Rocq modules.

## Exact coordinate nullity and positive-support constancy

Three further formal results complete a coordinatewise characterization.
`indexed_basis_covariance_matrix_zero_row_iff_zero_column` uses
indexed symmetry to prove that a row is identically zero iff its
corresponding column is identically zero, **without** assuming
normalized or nonnegative weights. Theorems
`indexed_basis_covariance_matrix_zero_row_iff_constant_on_support`
and `indexed_basis_covariance_matrix_zero_column_iff_constant_on_support`
then show, for normalized nonnegative finite sample weights, that
zero rows and columns characterize scores constant on positive-weight
sample support. Both implications reuse previously certified
zero-diagonal and support-constancy iff results and the standard
propositional `tauto` tactic.

The model still lacks a generic matrix rank/kernel dimension theorem;
no such claim is made. The changes introduce no custom matrix
operation, new external dependency, Python code or SPARK modifications.

Current inventory: **573 public claims, 576 proof scripts,
639 documented declarations** in seven Rocq modules.

## Indexed covariance positivity and positive-support variation

Three certified consequences of the prior scalar covariance library
extend the bounded matrix interface. The positive-diagonal theorem
characterizes strict variance by absence of a constant selected score
on positively weighted sample outcomes. A nonzero indexed covariance
entry implies strictly positive variances for both selected scores,
and consequently neither score can be constant on positive-weight
support. The final implication is necessary, not sufficient:
two varying scores may still have zero covariance.

The proofs use only existing scalar covariance/variance theorems
and the prior `Fin.t` diagonal bridge. They introduce no separate
finite-sample recursion, matrix algorithm, Gaussian measure, new
Rocq axiom, Python file, or historical source modification.

Current inventory: **573 public claims, 576 proof scripts,
639 documented declarations** across seven Rocq modules.

## Rectangular indexed covariance bounds and variation

Three documented, library-backed theorems lift scalar finite covariance
laws to rectangular `Fin.t`-indexed matrices. They show the
Cauchy-Schwarz squared bound against the two selected score variances,
strictly positive selected variances when a cross-covariance is nonzero,
and the consequent nonconstancy of both scores on positive-weight
sample support. Bases can have different dimensions and repeated scores.

The existing square indexed Cauchy-Schwarz proof was also refactored:
it now reuses the more general rectangular theorem and the established
diagonal-to-variance identity instead of unfolding scalar covariance
again. No custom matrix traversal, new external dependency, axiom,
Python source change or historical evidence modification was needed.

Current inventory: **573 public claims, 576 proof scripts,
639 documented declarations** in seven Rocq modules.

## Two-coordinate indexed covariance quadratic via scalar variance

The bounded covariance interface now includes
`indexed_basis_covariance_two_coordinate_form`, a purpose-specific
polynomial in already verified dimension-indexed covariance entries.
The `_as_variance` theorem uses the library-backed
`variance_of_two_weighted_scores` identity without requiring
normalized weights. Its `_nonnegative` theorem follows from scalar
finite variance nonnegativity with explicit mass-one/nonnegative
sample weights. Further iff results characterize a zero form and
a strictly positive form exactly by constancy or nonconstancy of
the two-score linear combination on positive-weight sample support.

No list iteration, matrix multiplication, general determinant
algorithm, axiom or external library was added. Full matrix
kernel/rank results and continuous distribution theory remain
separately unproved. No Python source or archived SPARK evidence
was modified.

Current inventory: **573 public claims, 576 proof scripts,
639 documented declarations** across seven Rocq modules.

## Two-coordinate bridge to the established list-matrix quadratic

The `indexed_basis_covariance_two_coordinate_form_as_list_matrix`
theorem connects two bounded covariance cells to the already verified
`matrix_quadratic_form` on a two-score list covariance matrix,
without any normalized-mass assumption. It reuses the existing
two-weighted-score variance theorem, score variance extensionality
and unconditional list-matrix covariance quadratic identity.
No independent generic matrix multiplication or list recursion
was introduced. Later positive-semidefiniteness proofs can use
the existing general fixed-basis matrix theorem through this bridge.

Current inventory: **573 public claims, 576 proof scripts,
639 documented declarations** across seven Rocq modules.

## Generic fixed-basis positive-semidefinite theorem reuse

The two-coordinate form nonnegativity proof was refactored to reuse
`fixed_basis_covariance_matrix_positive_semidefinite` through the
kernel-checked `indexed_basis_covariance_two_coordinate_form_as_list_matrix`
bridge. Its theorem statement and exact normalization/nonnegative-weight
assumptions are unchanged. This removes a duplicated scalar variance
positivity step in favor of the existing general finite matrix theorem.

Current inventory remains **573 public claims, 576 proof scripts,
639 documented declarations** across seven Rocq modules.

## Arbitrary-dimensional vector coefficients and covariance nullity

The new `indexed_basis_covariance_quadratic_form` takes a
`Vector.t R (length basis)` rather than an unconstrained list of
coefficients. It delegates matrix arithmetic to the existing
`matrix_quadratic_form` and `basis_covariance_matrix` functions.
`Stdlib.Vectors.VectorSpec.length_to_list` certifies the exact
dimension equality whenever an established list-matrix theorem is reused.

Six documented proofs lift **existing all-dimensional** finite
covariance theorems: weighted-basis variance equality, PSD,
zero quadratic iff a supported-constant score, strict positivity
iff no positive-support constant, zero quadratic iff the
composite score is uncorrelated with every basis score, and
zero quadratic iff its coefficient list has zero dot product
with every covariance row. All probability statements retain
mass-one/nonnegative sample-weight hypotheses. Empty and
dependent bases are allowed. This is a dimension-safe coefficient
interface, not an independent indexed-matrix multiplication
implementation or a kernel-dimension theorem.

No Python files, new Rocq axioms, external dependencies or
historical source-pinned SPARK verification artifacts were changed.

Current inventory: **573 public claims, 576 proof scripts,
639 documented declarations** across seven Rocq modules.

## Dimension-safe covariance orthogonality and strict positivity

Five additional proofs lift the existing general finite list covariance
results to `Vector.t R (length basis)` coefficients. Zero covariance
quadratic is equivalent to uncorrelatedness with **every** outcome
score, not just the basis. Strictly positive quadratic is equivalent
to non-orthogonality with all basis scores, and also to failure of
every covariance-row dot product to vanish. A separate iff equates
zero covariance row dots with a composite score constant over
positive-weight sampled support. Finally, a nonzero covariance
with any comparison score provides a strictly positive
coefficient-vector quadratic witness.

Every theorem delegates to established scalar or general
fixed-basis results and `VectorSpec.length_to_list` where required.
Theorems preserve the normalized nonnegative-weight assumptions;
none asserts finite matrix rank or continuous probability results.
There are no new Python changes, matrix algorithms, dependencies,
axioms or edits to source-pinned SPARK evidence.

Current inventory: **573 public claims, 576 proof scripts,
639 documented declarations** across seven Rocq modules.

## Two-coordinate algebra and bounded covariance row consequences

Five kernel-checkable consequences extend the indexed interface
without implementing any new matrix or vector algorithm. The
two-coordinate covariance form is invariant under exchanging
its score indices and coefficients; it is homogeneous of degree
two under a common real coefficient scaling. Both identities
reuse the checked covariance symmetry and Stdlib real `ring`.

For arbitrary-dimensional `Vector.t` coefficient vectors,
a vanishing covariance quadratic forces the dot product
against **every Fin.t-selected covariance row** to vanish.
The proof composes the earlier general row-dot kernel iff,
the bounded-row list correspondence and Stdlib.List.nth_error_In.
A null direction is also uncorrelated with every bounded basis
score; conversely a *witnessed nonzero covariance* with one
bounded basis score certifies a strictly positive quadratic.
The row kernel result is one-way at this stage; full indexed
row-kernel equivalence and rank dimensions remain future work.

All theorem comments and the proof inventory were updated;
no Python sources, new axioms, custom finite sums or
source-pinned SPARK evidence were changed.

Current inventory: **573 public claims, 576 proof scripts,
639 documented declarations** across seven Rocq modules.

## Complete Fin.t-indexed covariance-row nullspace criterion

The new `indexed_basis_covariance_matrix_row_has_bounded_index`
theorem establishes that **every** row in the existing list
covariance matrix has a corresponding bounded `Fin.t` index,
even with repeated score functions. It composes the standard
`In_nth_error`, `nth_error_Some`, `length_map`,
`Fin.of_nat_lt`, and `Fin.to_nat_of_nat` lemmas with the
already checked list/Fin row bridge. No custom list induction
or index enumeration is introduced.

This completes the earlier one-way implication:
`indexed_basis_covariance_quadratic_zero_iff_bounded_row_dots_zero`
proves that, under normalized nonnegative sample weights, a
dimension-safe coefficient direction has covariance quadratic
zero **iff all bounded indexed covariance row dot products
vanish**. The converse follows from completeness of the
row-index bridge and the existing general fixed-basis nullity
theorem. The result does not compute rank or nullspace dimension.

Current inventory: **573 public claims, 576 proof scripts,
639 documented declarations** across seven Rocq modules.

## Indexed covariance positive definiteness and bounded row kernel

Five further theorem proofs reuse the complete Fin.t row
kernel iff. Strict positivity of an arbitrary-dimensional
typed coefficient covariance quadratic is now equivalent
to the bounded row dot products not all vanishing. A
vanishing bounded row system is equivalent both to a
positive-support-constant composite score and to a
composite score uncorrelated with every outcome score.
These are propositional compositions of existing checked
results and do not repeat covariance algebra.

The `indexed_basis_covariance_positive_definite` definition
quantifies over all nonzero `Vector.t R (length basis)`
coefficient directions, using the existing `Vector.to_list`
and `List.repeat` representation of a zero vector.
Two further iff theorems characterize positive definiteness
as the absence of any nonzero supported-constant score
direction, equivalently the absence of a nonzero bounded
covariance row-kernel direction, under unit-mass nonnegative
weights. The existing fixed-basis results supply the
substantive mathematics. **No rank dimension, eigenvalue,
spectral theorem or determinant algorithm is claimed.**

Current inventory: **573 public claims, 576 proof scripts,
639 documented declarations** across seven Rocq modules.

## Indexed positive definiteness: composite variance and PSD null directions

Three more extensively commented, library-backed theorems
characterize the typed finite covariance positive-definiteness
predicate. First, positive definiteness is equivalent (under unit
sample mass) to strictly positive variance of every nonzero
vector-coefficient composite score. Second, under normalized
nonnegative weights, it is equivalent to the absence of nonzero
directions orthogonal to all chosen basis scores. Third, combining
the previously checked positive-semidefinite property with
real linear arithmetic, positive definiteness is equivalent to
**no nonzero direction having an exactly zero quadratic form**.

These statements reuse earlier indexed covariance/variance
bridges and Stdlib.Lra. They neither implement matrix
elimination nor claim numerical rank, eigenvalue bounds or
new statistical evidence. All seven Rocq file headers remain
in place and no Python source hashes are altered in this batch.

Current inventory: **573 public claims, 576 proof scripts,
639 documented declarations** across seven Rocq modules.

## Constructive witnesses for typed covariance positivity and degeneracy

Four further checked theorem statements link typed coefficient
directions to concrete finite-support and matrix-row witnesses.
Two distinct composite-score evaluations on positive-weight sampled
outcomes force strictly positive coefficient quadratic form,
reusing the existing strict-positivity iff support nonconstancy.
If every nonzero vector direction admits such a sample pair,
the covariance basis is positive definite. A single nonzero
bounded-index covariance row dot similarly certifies positivity
using the previously checked Fin.t row-kernel equivalence.
Conversely, one explicit nonzero coefficient direction annihilating
all bounded covariance rows refutes positive definiteness.

These arguments compose existing finite variance/covariance lemmas;
they introduce no duplicated finite-sum implementations, new axioms,
rank algorithms or dependence on external matrix libraries.
The boundary is finite, normalized, nonnegative weighted samples.

Current inventory: **573 public claims, 576 proof scripts,
639 documented declarations** across seven Rocq modules.

## Typed covariance nullity through positive-support anchors

Four new Rocq proofs reuse the existing finite coefficient
nullity and positive-definiteness library without new summations
or matrix algorithms. A zero dimension-safe covariance quadratic
forces identical weighted composite-score values on every pair
of positive-weight sampled outcomes, using the general list
quadratic theorem and `VectorSpec.length_to_list`.
With a specified positive-weight sampled anchor, the converse
holds: equality with the anchor on all positive-weight outcomes
is exactly equivalent to a zero coefficient quadratic.
A nonzero bounded coefficient direction constant on positive
sample support refutes positive definiteness, as does an
explicit nonzero zero-quadratic direction; both use previously
checked indexed positive-definiteness iff theorems.

Every new declaration has a complete adjacent mathematical
comment; the proof inventory and library audit are synchronized.
The statements retain finite normalized nonnegative-weight
premises and assert neither Gaussianity nor numerical rank.

Current inventory: **573 public claims, 576 proof scripts,
639 documented declarations** across seven Rocq modules.

## Duplicate Boolean-event invariance for finite union and intersection

Four new extensively documented Rocq proofs establish that
duplicating one event predicate at the head of a required-event
or alternative-event list leaves its finite event mass unchanged.
The identities apply both to unconditional finite event mass
and to conditional probability given an arbitrary conditioning
event. They need no nonnegative/normalized weight hypothesis:
the existing probability target extensionality lemmas also
handle the zero-conditioner-mass branch. The proofs use the
existing `any_event` (`existsb`) and `all_events` (`forallb`)
definitions and the standard Boolean conjunction/disjunction
identities, not duplicate list recursion or weighted summation.

The statements clarify an important distinction: duplicate
constraints do not alter union/intersection truth, but a sum
of separate marginal event probabilities can double-count.
All theorem comments, module headers, proof-register rows
and the library audit remain synchronized.

Current inventory: **573 public claims, 576 proof scripts,
639 documented declarations** across seven Rocq modules.

## Refactored event idempotence and general append-existing laws

A duplicate-head union-mass theorem introduced in the preceding
batch had an equivalent existing checked
`union_prob_duplicate_route` result. It was **replaced rather
than maintained as a redundant proof** by a stronger
`finite_union_append_existing` theorem: appending any event
already in the list preserves its finite union mass.
One `event_append_existing_membership_iff` helper reuses
`Stdlib.List.in_app_iff` and supplies its membership
equivalence to that union theorem and to two new statements:
unconditional and conditioned intersections are invariant
under appending an already-required event. These proofs delegate
to `union_prob_membership_extensional`,
`all_events_membership_ext` and existing finite target
extensionality, rather than reimplementing event Booleans
or sample summations.

The earlier duplicated-intersection head proofs were also
refactored to reuse `all_events_membership_ext` directly.
No event independence, probability normalization or positive
conditioning mass is required. The proof register reflects
each refactor and the complete explanatory comments remain.

Current inventory: **573 public claims, 576 proof scripts,
639 documented declarations** across seven Rocq modules.

## Shared conditional union membership equivalences

The finite union membership proof is factored into a pure event predicate
lemma using `Stdlib.List.existsb_exists`. It now serves the existing
unconditional union theorem and three new conditional union results:
membership-extensional equality, event-list permutation, and appending
an already-present event. The new theorems reuse the existing conditional
target extensionality and permutation and append-membership lemmas.
They retain exact equality even when the conditioning mass is zero.

The new intended inventory is **580 claims, 583 proof scripts, 646
documented declarations** across seven Rocq modules. All new claims
require the Rocq kernel and existing documentation CI gates.

## Reuse generic finite event monotonicity for event-family inclusion

A shared `any_event_membership_monotone` lemma uses the maintained
`existsb_exists` membership bridge rather than Boolean recursion.
Ordinary and positive-conditioner conditional union inclusion inequalities
follow from `finite_prob_event_monotone` and
`finite_conditional_prob_monotone`. Both require only nonnegative sampled
weights; the conditional result also requires positive conditioning mass.

## Conditional union identity base cases and concatenation

Three documented theorems now cover empty-family zero mass, singleton-family
identity and appended event-family Boolean OR under the same conditioning
predicate. The proofs reuse `finite_conditional_prob_false`,
`finite_conditional_prob_event_ext_on_samples` and the existing
`any_event_append` lemma built on `Stdlib.List.existsb_app`.
They are exact equalities even when conditioning mass is zero; that
case has no ordinary statistical conditional-probability interpretation.

Current intended inventory: **583 public claims, 586 proof scripts and
649 documented declarations** across seven Rocq files, subject to the
Rocq 9.2 kernel and documentation CI.

## Conditional conjunction base case and head-tail structure

Two additional documented theorems reduce `all_events []` to true and
`all_events (head :: rest)` to a Boolean conjunction, using the
maintained `Stdlib.List.forallb` and generic conditional extensionality.
The empty conjunction equals conditional probability one only with
explicitly positive conditioning mass. No independence premise is
inferred from the Boolean conjunction representation.

Current intended inventory: **585 public claims, 588 proof scripts and
651 documented declarations** across seven Rocq modules, subject to CI.

## Monotonic append-family admission alternatives

The ordinary and conditioned union append-left corollaries use
`Stdlib.List.in_or_app` and the existing family-inclusion theorems,
without new list recursion or finite-sum algebra. Nonnegative weights
are explicit, and positive conditioning mass is additionally needed
for conditional inequalities.

Current intended inventory: **587 public claims, 590 proof scripts and
653 documented declarations** across seven Rocq modules, pending CI.

## Append-family order for unions and conjunctions

Four documented Rocq theorems derive right-sided union monotonicity
(ordinary and conditional) and both-sided conditional conjunction
antitonicity. All use `Stdlib.List.in_or_app` as a pure membership
bridge and the previously established family-subset probability laws.
Nonnegative sampled weights and strictly positive conditioning mass
remain explicit for conditional inequalities. No event recursion,
custom sum or independence claim was introduced.

Current intended inventory: **591 public claims, 594 proof scripts,
657 documented declarations** across seven Rocq modules, subject to CI.

## Shared conjunction membership and ordinary intersection monotonicity

A documented `all_events_membership_antitone` lemma now centralizes the
maintained `Stdlib.List.forallb_forall` reasoning for Boolean conjunctions.
The existing conditional conjunction family-subset theorem delegates
to this helper rather than duplicating the witness proof. The ordinary
finite-mass counterpart `finite_all_events_subset` combines the helper
with existing `finite_prob_event_monotone`; two unconditional append
corollaries use `Stdlib.List.in_or_app`. No new sums or recursions appear.

Current intended inventory: **595 public claims, 598 proof scripts,
661 documented declarations** across seven Rocq modules, subject to CI.

## Shared append semantics and unconditional conjunction identities

The maintained `Stdlib.List.forallb_app` fact is now used by a
single documented `all_events_append` helper, replacing the
duplicated Boolean reduction in the pre-existing conditional
conjunction-append theorem. Its unconditional counterpart and
empty/singleton conjunction identities are derived from existing
`finite_prob_event_ext_on_samples` and `finite_prob_true`.
No new list recursion, custom finite sum or independence assumption
is introduced.

Current intended inventory: **599 public claims, 602 proof scripts,
665 documented declarations** in seven Rocq modules, subject to CI.

## Unconditional conjunction structure, membership and marginal bounds

Four more well-documented declarations lift standard Boolean-list
semantics to finite weighted mass: head-tail conjunction via
`Stdlib.List.forallb`, membership extensionality via the existing
`all_events_membership_ext`, permutation invariance via
`Stdlib.Sorting.Permutation`, and the upper bound by any required
event via the existing `finite_all_events_subset` and singleton
law. All remain independent of sample normalization and event
independence; only the inequality assumes nonnegative weights.

Current intended inventory: **603 public claims, 606 proof scripts,
669 documented declarations** in seven modules, subject to CI.

## Finite event-family intersection versus union

Two documented theorems bound the mass of an event-family conjunction
by its union, both unconditionally and under positive-mass
conditioning. Both results chain existing `finite_all_events_at_most_member`
(or conditional counterpart) with the previously proved
member-to-union inequality using standard real-order transitivity.
The explicit `In member events` witness avoids the empty-family
counterexample; nonnegative sample weights and positive conditioning
mass are visible wherever needed. No new Boolean recursion or
probability normalization assumption is introduced.

Current intended inventory: **605 public claims, 608 proof scripts,
671 documented declarations** across seven modules, subject to CI.

## Two-event family inclusion-exclusion without duplicated algebra

A shared `all_events_pair` lemma reduces `Stdlib.List.forallb`
on two event predicates to ordinary `andb`. New unconditional
and conditional inclusion-exclusion theorems then lift the maintained
generic indicator-mass identities into the event-family notation.
Both reuse existing target-event extensionality lemmas. The
conditional equality also covers a zero-mass conditioner as an
identity of totalized real quotients; probabilistic interpretation
still requires a strictly positive conditioner and nonnegative
weights. There is no new summation, independence assumption or axiom.

Current intended inventory: **608 public claims, 611 proof scripts,
674 documented declarations** across seven modules, subject to CI.

## Two-member family conditional independence without duplicated algebra

The two-event conditional factorization and sum-minus-product union
identities now have explicit event-family formulations. A new
`finite_conditional_two_event_family_product` theorem projects
the factorization already required by `finite_conditional_independent`
and uses the shared `all_events_pair` Boolean identity.
`finite_conditional_two_event_family_independent_union` delegates to
the existing independent-union theorem after a standard `existsb`
reduction. These are not new independence assumptions or Gaussian
probability theorems; both rely on a strictly positive conditioner
inside the conditional-independence predicate.

Current intended inventory: **610 public claims, 613 proof scripts,
676 documented declarations** across seven modules, subject to CI.

## Shared two-event Boolean disjunction refactor

A documented `any_event_pair` lemma replaces the duplicated
`existsb` unfolding and `orb_false_r` normalization in both the
conditional two-event family inclusion-exclusion proof and the
independent two-event union proof. It parallels the already checked
`all_events_pair` helper and reuses only maintained Rocq 9.2
standard-library operations.

Current intended inventory: **662 public claims, 665 proof scripts,
730 documented declarations** across seven modules, subject to CI.

## Generic positive finite sums and strict monotonicity (9 November 2026)

The shared `FiniteSum.v` layer now proves three more reusable facts:
`finite_sum_nonnegative_zero_iff` characterizes a zero aggregate
by the vanishing of **every** nonnegative listed summand;
`finite_sum_positive_of_positive_member` derives strict positivity
from one positive term; and `finite_sum_strict_monotone_at_member`
lifts pointwise weak comparison plus a single strict comparison
to strict comparison of the two totals.

All three proofs reuse the existing finite sum, its zero and
subtraction laws, Rocq's decidable real order and `Lra`; they
introduce no new finite sum implementation, induction, axioms or
admitted proofs. The new statements require their explicit
support-membership and sign/order hypotheses. Multiplicities of
repeated sample entries are retained.

Inventory after these generic sum additions and strict event bounds: **662 public claims,
665 proof scripts, 730 documented declarations** across seven
Rocq modules; final acceptance depends on the Rocq 9.2 CI kernel
and source-documentation audits.

### Existing event-mass proofs refactored to the shared sum layer

The propositions of `finite_prob_zero_iff_no_positive_mass_support`
and `finite_prob_positive_of_positive_support` are unchanged. Their
proofs now use the generic zero-sum equivalence and positive-member
lemma in `FiniteSum.v`, rather than duplicating the finite-sum
reasoning in `FiniteUnion.v`. They preserve the nonnegative-weight,
Boolean event and sample-membership assumptions. Both theorem comments
now explain the exact witness semantics, proof dependencies, and
limits of probabilistic interpretation.

### Conditional-event positivity from finite joint support

The two new theorems
`finite_conditional_prob_positive_of_positive_joint_support` and
`finite_conditional_prob_positive_of_joint_support_witness` derive a
strictly positive conditional event mass from a sampled outcome where
both Boolean events hold with positive weight. The first makes the
positive conditioning denominator explicit; the second proves that
denominator condition from the same witness. Both reuse the generic
positive support theorem and the standard `Rdiv_lt_0_compat` rule,
without assuming independence or normalized total sample mass.

## Strict event inclusion and filtered-mass comparison

Three new Rocq theorems express strict mass comparisons rather than
only non-strict event bounds:
`finite_prob_event_strict_monotone`,
`finite_prob_filtered_mass_strict`, and
`union_prob_filtered_mass_strict`.

They require a **positively weighted enumerated witness** belonging
to the larger event but not the smaller one (or an outcome discarded
by filtering). All sample weights must be nonnegative. They reuse the
already checked strict finite-sum comparison, event indicator order,
filtered-mass equivalence, and the existing union operator.
No independence, normality, unit normalization, extra axioms,
or custom finite-sum recursion are introduced.

### Strict conditional target comparison and interior conditional mass

Two further finite conditional-event theorems preserve the existing
strict-positive denominator semantics. The first lifts strict target
event inclusion through a **common positive conditioning denominator**,
using `finite_prob_event_strict_monotone` and Rocq's positive-inverse
order laws. The second derives `0 < P(E|G) < 1` when the selected
sample contains positive-weight witnesses for both `E` and its
complement, reusing the already verified conditional positivity and
complement identities. These statements concern the exact enumerated
finite sample; they assert neither independence nor empirical or
continuous probability results.

### Strict event-family extension from a genuinely new sample witness

The pair `union_prob_append_strict_of_fresh_support` and
`finite_conditional_union_append_strict_of_fresh_support`
proves that appending an event family strictly enlarges its
unconditional and (under a positive conditioner) conditional union
mass when a new positively weighted sampled outcome enters the
union. Both are immediate reductions to the maintained strict event
comparison theorems, with `Stdlib.List.existsb_app` supplied via
`any_event_append`. No fresh Boolean-family recursion, enumeration,
or independence premise is introduced.

### Three-event conditional product from hierarchical independence

The new `all_events_triple` helper rewrites the standard
three-member `Stdlib.List.forallb` into a left-associated Boolean
conjunction using `Stdlib.Bool.andb_assoc`. The theorem
`finite_conditional_three_event_family_product` then proves the
three-way conditional product rule by reusing the two-event conditional
product and the explicitly assumed independence between the first
pair's conjunction and the third event.

**Pairwise independence alone is not sufficient** for this conclusion.
The statement is a finite Boolean event identity under two explicit
hierarchical conditional-factorization premises; it does not claim
that the observed report data satisfies these premises.

### Nonempty chain factorization and triple-proof consolidation

`finite_conditional_prefix_independent_cons_positive` projects
positive conditioning-event mass from the **first** independence
assumption of any nonempty suffix-factorization chain.
`finite_conditional_nonempty_all_events_product` thereby removes
the otherwise redundant explicit denominator premise of
`finite_conditional_all_events_product` for nonempty families.
The empty-family theorem intentionally still requires a positive
denominator: an empty chain alone is `True`.

The earlier `finite_conditional_three_event_family_product` now
delegates to the already checked `finite_conditional_three_event_product`
after the standard Boolean associativity rewrite. This removes
duplicated factorization algebra without weakening or changing either
theorem's statement or hierarchical independence requirements.

### Arbitrary finite conditional union from complement-family independence

`all_negated_events_eq_negated_any` proves the pointwise
Boolean De Morgan bridge between `Stdlib.List.forallb` on
pointwise complements and `Stdlib.List.existsb` on the
original family. The proof uses the standard `negb_orb` lemma.

`finite_conditional_union_complement_chain_product` applies
the pre-existing arbitrary-list conditional intersection product
to this complement list, and transports each complement mass via
the already checked conditional complement identity, obtaining

`P(A_1 ∪ ... ∪ A_n | G) = 1 - ∏_(i=1)^n (1 - P(A_i | G))`.

The explicit premise is **suffix conditional factorization of the
complementary events**; pairwise independence alone is not asserted
to suffice. The empty-list case has a separate positive-denominator
premise, while the nonempty corollary derives that premise from
the first independence assertion. No new finite-sum or real-product
implementation is introduced: products use `Stdlib.List.fold_right`.

### Explicit unconditional and conditional union/complement partitions

`finite_union_complement_partition` states that the weighted
mass of a finite union plus the mass of outcomes failing
**every** member equals the full enumerated sample mass, for
arbitrary real weights. Its conditional companion establishes
that these complementary conditional masses sum to one under
a positive conditioning denominator.

Both are direct applications of the existing complement mass
identities after the finite-family De Morgan bridge. The
general union product proof now reuses the new conditional
partition theorem rather than repeating the De Morgan rewrite.
No new independence premise or list-fold implementation is needed.

### Finite union mass determined by event support

The zero-mass law `union_prob_zero_iff_no_positive_support`
is a specialization of the existing finite-event support theorem.
`union_prob_zero_iff_each_member_zero` strengthens it to
an event-family equivalence: under nonnegative sampled weights,
the mass of a union vanishes exactly when the mass of **every
listed member** vanishes. The proof uses
`Stdlib.List.existsb_exists` and the checked
`event_member_implies_union` lemma instead of implementing a
second union search.

The positive counterparts,
`union_prob_positive_of_positive_support` and
`union_prob_positive_of_positive_member_support`,
reuse single-event positivity and show that one positive-weight
sampled witness suffices. These results require no independence
or normalized total mass and remain specific to finite lists.

### Conditional zero mass and union-member support

`finite_conditional_prob_zero_iff_joint_zero` proves that an
exact finite conditional quotient is zero precisely when its
joint numerator is zero, when the conditioning marginal
is strictly positive. It reuses Rocq's real-product
zero-divisor and positive-reciprocal lemmas.

With nonnegative sampled weights,
`finite_conditional_prob_zero_iff_no_positive_joint_support`
then characterizes the same zero conditional mass by the absence
of positively weighted sampled outcomes satisfying both
the condition and the target. Finally,
`finite_conditional_union_zero_iff_each_member_zero`
extends the unconditional union support equivalence to
**conditional** union masses under the same positive conditioner.
Its only event-family witness conversion is
`Stdlib.List.existsb_exists`. No additional
independence, normalized-total-mass assumption, conditional
measure implementation, or custom finite-sum recursion is used.

### Zero mass propagates through finite intersections

The new `finite_all_events_zero_of_zero_member` and
`finite_conditional_all_events_zero_of_zero_member` state
that a finite intersection cannot have positive finite mass
when any listed required event has zero mass, unconditionally
or under a common positive-mass conditioner. Both results
reuse the existing zero-support equivalences and
`Stdlib.List.forallb_forall`, rather than a new
induction on the event family.

The older `finite_all_events_at_most_member` has also been
refactored to use generic event monotonicity and the same
standard forallb membership theorem as its conditional
counterpart. This removes its unnecessary singleton conversion
while retaining the exact statement and side conditions.

### Constructive positive-support witnesses for sums and event probabilities

`FiniteSum.finite_sum_positive_iff_positive_member` now shows
constructively that a sum of nonnegative real contributions
is positive **if and only if** an actual listed contribution
is positive. It uses the previously checked one-witness
sufficiency theorem and only a minimal standard-list induction
for extracting a witness in the reverse direction.

`finite_prob_positive_iff_positive_support` specializes the
generic sum law to existing Boolean-weight indicators.
`union_prob_positive_iff_positive_member_support` uses
`Stdlib.List.existsb_exists` to identify both an actual
event-family member and an actual positively weighted sampled
outcome. The conditional companion
`finite_conditional_prob_positive_iff_joint_support`
requires a positive denominator and nonnegative sampled
weights, and reuses the existing quotient-zero and
conditional-witness results instead of reimplementing the
conditional probability quotient.

### Conditional-union witness and necessary intersection marginals

The new `finite_conditional_union_positive_iff_positive_member_joint_support`
extends the constructive conditional positive-support iff to a
finite union. It identifies both a *listed event* and a *sampled
outcome* satisfying that event and the conditioner with positive
weight. The only family witness conversion is the standard
`Stdlib.List.existsb_exists` lemma.

Theorems `finite_all_events_positive_implies_member_positive`
and `finite_conditional_all_events_positive_implies_member_positive`
then reuse existing intersection-vs-member bounds to show that
positive joint mass forces every required marginal positive,
unconditionally and with a fixed positive conditioner.
The converses are **not** asserted without overlap assumptions.

The generic `FiniteSum.finite_sum_positive_of_positive_member`
proof was also shortened to the existing
`finite_sum_member_le` member bound and `Stdlib.Lra`.
This removes the former redundant real-decision case analysis.

### Constructive positive variance and indexed covariance curvature

`variance_positive_iff_exists_positive_weight_deviation`
uses the generic constructive finite-sum positivity theorem
on nonnegative weighted squared score deviations. Under unit
total mass and nonnegative sampled weights, strictly positive
variance now yields an actual enumerated, positive-weight
sample with score different from its finite mean, rather than
only a negated universal constancy predicate.

`indexed_basis_covariance_quadratic_positive_iff_supported_deviation`
transfers this witness through the maintained dimension-safe
covariance quadratic = composite-score variance identity.
It characterizes strictly positive covariance curvature for
any `Vector.t R (length basis)` coefficient direction by
positive-weight sampled deviation. This is useful evidence
for later kernel and rank reasoning but **does not yet
compute rank or prove a rank-nullity dimension formula**.

### Positive definiteness through constructive support separation

`indexed_basis_covariance_positive_definite_iff_all_nonzero_supported_deviations`
lifts the previous typed quadratic positivity iff pointwise
to **all nonzero coefficient directions**. For normalized
nonnegative weights, a covariance basis is positive definite
precisely when each nonzero typed linear combination deviates
from its finite mean on some *actual positive-weight sampled
outcome*. The proof invokes the already checked quadratic
support-witness iff and does not introduce a matrix implementation,
rank function or classical-existence assumption.

The result is a constructive bridge toward finite covariance
kernel and rank questions. A dimension or numerical eigenvalue
claim would still require a separately checked linear-algebra
formalization with its own explicit assumptions.

### Weighted centered sample evaluation as a covariance-kernel bridge

The new `indexed_basis_centered_weighted_score` is a transparent
function evaluating the weight times the deviation of a
dimension-correct composite basis score from its expectation.
It reuses existing `weighted_basis_sum`, `expect`, and
`Stdlib.Vectors.Vector.to_list` without reimplementing
a matrix, finite sum or linear map.

`indexed_basis_covariance_quadratic_zero_iff_centered_weighted_score_zero`
shows that the indexed covariance quadratic vanishes exactly
when this centered weighted function vanishes at every sampled
outcome, given unit mass and nonnegative sampled weights.
`indexed_basis_covariance_bounded_row_kernel_iff_centered_weighted_score_zero`
identifies this sample evaluation kernel with the existing
Fin.t-indexed covariance row kernel.

`indexed_basis_covariance_positive_definite_iff_no_nonzero_centered_weighted_sample_kernel`
lifts this kernel equivalence to all nonzero typed coefficient
vectors, relating positive definiteness to the triviality of
the centered evaluation kernel. A future finite-dimensional
rank-nullity theorem requires a maintained linear-algebra
library and an explicitly proved linear-map/dimension bridge;
none is assumed here.

### Centered evaluation zero-sum constraint

`indexed_basis_centered_weighted_score_sum_zero` reuses
`centered_score_has_zero_expectation` to prove that the centered
weighted sample evaluations sum to zero whenever the total
sample mass is one. This exact identity holds even for signed
weights and does not assume covariance positive semidefiniteness.

For nonnegative sampled weights, the
`indexed_basis_centered_weighted_score_nonnegative_implies_quadratic_zero`
and
`indexed_basis_centered_weighted_score_nonpositive_implies_quadratic_zero`
theorems show that if every centered sample evaluation
has the same weak sign, all evaluations vanish and the
covariance quadratic is zero. The proofs reuse the generic
`FiniteSum.finite_sum_nonnegative_zero_iff`, `finite_sum_neg`
and previously established sample-evaluation kernel equivalence.

Geometrically, this is the explicit zero-total constraint
needed before constructing a finite-dimensional centered
evaluation linear map. No codomain dimension, covariance
rank bound, or rank-nullity theorem is claimed yet.

### Detecting nonnull covariance directions by sampled evaluations

`indexed_basis_covariance_quadratic_positive_iff_nonzero_centered_sample`
characterizes strictly positive indexed covariance quadratic
curvature by an actual sample where the existing weighted
centered score is nonzero. Its forward direction reuses the
constructive supported-deviation witness, and its backward
direction uses the maintained positive-semidefinite bound
and zero-evaluation kernel iff. Both directions retain
normalized nonnegative sample assumptions.

`indexed_basis_covariance_positive_definite_iff_every_nonzero_direction_detected`
lifts the result to all nonzero typed coefficient vectors.
Together with the zero-sum image and row-kernel bridge,
this supplies a concrete input-to-observation interface
for subsequent dimension/rank work, without treating
the interface itself as a full linear-map/rank theorem.

### Dimension-safe indexed centered sample evaluations

`indexed_basis_centered_sample_evaluation` now gives a
finite coordinate function with input coefficients typed
by `Vector.t R (length basis)` and output sample
coordinates indexed by `Fin.t (length samples)`.
It reuses standard `Vector.of_list`, `Vector.nth` and
the already checked centered weighted sample score.

`indexed_basis_centered_sample_evaluation_zero_iff_all_sample_scores_zero`
proves the output coordinate function vanishes everywhere
precisely when all enumerated sample outcome evaluations
vanish, using the existing `vector_of_list_nth_error` lemma
and maintained list/finite-index conversions. The
`indexed_basis_covariance_bounded_row_kernel_iff_bounded_sample_kernel`
theorem identifies this typed finite sample kernel with the
typed covariance row kernel.

Finally,
`indexed_basis_covariance_positive_definite_iff_no_nonzero_bounded_sample_kernel`
connects positive definiteness to triviality of the
dimension-checked sample evaluation kernel. This explicitly
separates the basis and sample dimensions without asserting
equal length, invertibility, or a rank theorem. A future
linear-map proof and standard algebraic dimension theorem
are still required before a numeric rank claim.

## Ordered finite-sum comparison equivalences (10 November 2026)

Two new finite-sum lemmas strengthen the reusable order interface without
adding recursion or axioms. `finite_sum_monotone_equality_iff_pointwise`
shows that pointwise ordered summands have equal total sums exactly when
they agree on every enumerated item. The complementary
`finite_sum_strict_monotone_iff_strict_member` identifies a concrete
strictly ordered list member precisely when the total sums differ strictly.
Both require pointwise `f x <= g x` on the listed domain and preserve
empty-list and duplicate-entry cases. Their proofs reuse the existing
nonnegative zero/positive member equivalences, sum subtraction, and
Rocq standard-library real linear arithmetic. No matrix rank theorem
or continuous-measure claim is inferred.

Inventory for this preceding sum-only batch: **664 public claims, 667 proof scripts,
732 documented declarations** across seven Rocq modules, pending CI.

## Exact order characterization for finite expectations (10 November 2026)

The new `finite_expectation_monotone_equality_iff_positive_support`
and `finite_expectation_strict_monotone_iff_positive_support_witness`
theorems transport the generic ordered-sum equivalences to weighted
expectations. Under nonnegative weights and a pointwise score order,
equality of expectations means that the scores agree at every listed
**positive-weight** sample. Strict expectation order holds precisely
when some listed positive-weight sample has a strict score order.
No normalized-total-mass premise or separate sample induction is used.
The proofs reuse `FiniteSum` and the standard Rocq real algebra
libraries; they do not establish general measure-theoretic or
empirical-statistical conclusions.

Inventory at the end of this preceding batch: **666 public claims, 669 proof scripts,
734 documented declarations** across seven modules, pending CI.

## Zero and positive finite expectations via support witnesses (10 November 2026)

Two nonnegative-moment corollaries reuse the maintained order-equivalence
theorems with the identically zero score. With nonnegative listed
weights and nonnegative listed scores, an expectation is zero exactly
when every positive-weight sample score is zero; the expectation is
strictly positive exactly when a listed positive-weight sample has a
strictly positive score. Zero-weight entries are irrelevant, repetitions
remain counted, and no total-mass normalization is needed. No new
sum fold, induction, axiom or decidable equality was introduced.

Inventory for the preceding nonnegative expectation batch: **668 public claims, 671 proof scripts,
736 documented declarations** across seven modules, pending Rocq 9.2 CI.

## Finite expected-square nullity and positive witnesses (10 November 2026)

The new `finite_expectation_square_zero_iff_zero_on_positive_support`
identifies the exact positive-weight kernel of a finite expected square:
it is zero if and only if the sampled score is zero at every
positive-weight occurrence. The companion
`finite_expectation_square_positive_iff_nonzero_positive_support`
produces an enumerated nonzero sample score precisely when the
expected square is strictly positive. These are reusable quadratic
support facts, obtained from the preceding expectation sign
characterizations and Rocq standard real-arithmetic libraries.
No fresh sum induction, matrix engine or rank claim is introduced.

Inventory for preceding expected-square batch: **670 public claims, 673 proof scripts,
738 documented declarations** across seven modules, pending Rocq 9.2 CI.

## Homogeneity of dimension-checked finite sample evaluation (10 November 2026)

Three new lemmas connect the coefficient list, typed coefficient
vector, and typed sample index representations: coefficient-wise
scaling of `weighted_basis_sum`, centered weighted-score scaling,
and bounded indexed sample-evaluation scaling. The latter establishes
`E(a*c)[i] = a*E(c)[i]` for every real `a` and bounded sample index
`i`, with no mass normalization or nonnegative-weight condition.
The library bridge `VectorSpec.to_list_map` transfers the
type-indexed vector operation to the existing finite list sum,
while `expectation_scale` and `expectation_ext` avoid new
expectation implementations. Vector additivity and a packaged
rank-nullity theorem remain future targets.

Inventory for preceding scalar-homogeneity batch: **673 public claims, 676 proof scripts,
741 documented declarations** across seven modules, pending Rocq 9.2 CI.

## Pointwise additivity of the bounded sample evaluation (10 November 2026)

The next four checked claims establish componentwise coefficient
addition in the existing `weighted_basis_sum`, the structural
`Vector.map2 Rplus`/list-pair bridge, additivity of the centered
weighted score and additivity at each dimension-safe sample index.
Combined with `indexed_basis_centered_sample_evaluation_scale`, the
final coordinate evaluator now satisfies both pointwise real-linear
identities for the maintained vector operations. The sole new
representation bridge uses `Stdlib.Vectors.Vector.rect2` rather
than a custom vector recursion. Both finite expectation additivity
and composite sums reuse existing library laws, without a new matrix
engine or numerical rank claim.

Inventory for preceding additivity batch: **677 public claims, 680 proof scripts,
745 documented declarations** across seven modules, pending Rocq 9.2 CI.

## Typed bounded sample kernel closure (10 November 2026)

Five small, separately registered lemmas show that the canonical
`Vector.const 0` coefficient direction evaluates to zero; the
sample-evaluation kernel is closed under coefficient-vector addition
and arbitrary real scalar multiplication; and multiplying by a
nonzero real scalar preserves the kernel in both directions.
These results reuse the newly checked additivity/homogeneity
identities, standard `VectorSpec.to_list_const`,
`expectation_zero`/`expectation_ext`, and `Rmult_integral`.
They certify the elementary kernel-subspace laws as explicit
predicates but do not yet package them into a maintained library's
linear-map/subspace abstraction or assert a numeric rank-nullity law.

Inventory for preceding typed sample-kernel batch: **682 public claims, 685 proof scripts,
750 documented declarations** across seven modules, pending Rocq 9.2 CI.

## Typed covariance-row kernel bridge and closure (10 November 2026)

Two extensively commented transparent predicates name the already-checked
bounded sample-evaluation kernel and bounded covariance-row kernel, so new
proofs no longer duplicate long indexed covariance row dot-product
expressions. A direct bridge theorem transports their membership under
unit total mass and nonnegative listed weights. Three corollaries prove
membership of the canonical all-zero coefficient vector and closure of
the covariance-row kernel under componentwise vector addition and all
real scalar multipliers. Every proof reuses the earlier sample-kernel
linearity and closure theorems; no new matrix implementation, generic
vector recursion, Gaussian assumption, or rank calculation is added.

Inventory for preceding named-kernel bridge batch: **686 public claims, 689 proof scripts,
756 documented declarations** across seven modules, pending Rocq 9.2 CI.

## Named covariance kernel scaling and positive definiteness (10 November 2026)

The named bounded covariance-row kernel is now also shown invariant
under all nonzero real coefficient scalings. The proof composes the
checked named row/sample-kernel equivalence with the earlier
nonzero-scaling sample-nullspace equivalence, without opening a
covariance sum. Two additional equivalences state the existing
positive-definite covariance criterion directly using the reusable
named row and sample kernel predicates: positive definiteness holds
precisely when no nonzero, dimension-correct coefficient direction
belongs to either kernel. No false assumption of rank equality,
full column rank or a numerical rank-nullity formula is introduced.

Inventory for preceding positive-definiteness batch: **689 public claims, 692 proof scripts,
759 documented declarations** across seven modules, pending Rocq 9.2 CI.

## Covariance quadratic nullity as named typed kernel membership (10 November 2026)

Two kernel-checked interface equivalences identify exact zero covariance
quadratic values with membership in the named bounded centered-sample
kernel and, equivalently, the named bounded covariance-row kernel.
They are obtained by composing the existing quadratic-zero support
result with the established Fin.t sample-index bridge and row/sample
kernel equivalence. Both require unit total sample mass and
nonnegative listed weights and permit degenerate or repeated score
bases. No additional covariance formula, new real-sum induction or
spectral/rank arithmetic is introduced.

Inventory for preceding covariance-nullity batch: **691 public claims, 694 proof scripts,
761 documented declarations** across seven modules, pending Rocq 9.2 CI.

## Full typed centered sample output vector (11 November 2026)

The `indexed_basis_centered_sample_vector` definition maps each length-typed
coefficient vector into a standard `Vector.t R (length samples)` using the
existing single-outcome centered score and `Vector.map`/`Vector.of_list`.
`indexed_basis_centered_sample_vector_nth` identifies every Fin.t-indexed
coordinate with the previously checked sample evaluator through the
standard `VectorSpec.nth_map` rule. The typed output equals
`Vector.const 0 (length samples)` exactly when the existing named
bounded sample-kernel predicate holds, proved using the standard
`VectorSpec.eq_nth_iff` extensionality theorem and `const_nth`.
This is a concrete dimension-preserving representation bridge and
not yet a library-packaged linear map or rank calculation.

Inventory for preceding typed output-vector bridge: **693 public claims, 696 proof scripts,
764 documented declarations** across seven modules, pending Rocq 9.2 CI.

## Real-linearity and covariance nullity of the full sample vector (11 November 2026)

Two new checked `Vector.t` identities establish full-output real scalar
homogeneity and componentwise additivity of the existing typed
coefficient-to-sample-vector function. Rather than adding a second
summation or vector-recursion implementation, each proof uses Rocq's
standard `VectorSpec.eq_nth_iff` and `nth_map`/`nth_map2` laws,
then delegates to the previously checked coordinate linearity results.
Two further equivalences identify exact zero covariance quadratic form
with an all-zero output vector, and positive definiteness with the
absence of a nonzero coefficient vector mapping to the zero output.
The latter characterizes injectivity through the kernel, but no
finite-dimensional rank, nullity, or library linear-map record is claimed.

Inventory for preceding full-vector linearity batch: **697 public claims, 700 proof scripts,
768 documented declarations** across seven modules, pending Rocq 9.2 CI.

## Normalized sample-vector image has coordinate sum zero (11 November 2026)

The full centered sample-output vector now has a checked `Vector.to_list`
representation equal to mapping the established centered weighted score
across the original samples. Under unit total mass, the sum of all
output coordinates is exactly zero; this proof is delegated to the
existing centered-score sum theorem through the generic
`FiniteSum.finite_sum_map` lemma. A further result proves that a
normalized sample of length one has identically zero centered output
for all coefficient vectors; the proof isolates the singleton scalar sum
and transports it through the checked kernel equivalences to avoid
destructing the dependent sample-vector index. This is a genuine zero-sum image
constraint and concrete one-sample degeneracy, but no numeric
rank bound, image-dimension or rank-nullity identity is asserted.

Current target inventory: **700 public claims, 703 proof scripts,
771 documented declarations** across seven modules, pending Rocq 9.2 CI.

## Research extensions

The next valuable targets are: (1) extending the generic finite conditional-independence interface to
multi-event conditional factorization and conditioning-event transformations, (2) certified covariance-matrix rank statements beyond the
zero-quadratic-form support result, (3) using a maintained measure-theory
library with checked finite-to-continuous interpretation lemmas,
(4) bivariate Gaussian density normalization and certified tail
enclosures, and (5) Gaussian common-factor conditional-moment theorems. Numerical tables must remain labeled numerical until certified
interval arithmetic is available.

This work is AI-generated and requires independent review of the
**mapping between the English report and the exact formal statements**,
even when the Rocq kernel accepts all proofs.
