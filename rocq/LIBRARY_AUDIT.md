# Rocq proof-library audit and refactoring plan

This audit covers all **seven Rocq modules** in the Hoeflin/Ferguson and Towers formalization, including the shared finite-sum, event-to-moment and four-cell interpretation bridge modules.
It distinguishes **library functionality that should be reused** from
**report-specific definitions that must remain explicit**.

## Confirmed standard-library substitutions

| Module | Existing library facilities | Refactoring decision |
|---|---|---|
| `Hoeflin.v` | `Stdlib.Reals`: `Rplus_le_compat_l`, `Rmult_le_compat_l`, `Rdiv_lt_0_compat`, `sqrt_pos`, `sqrt_sqrt`, `sqrt_le_1`, `sqrt_lt_1` | Use the ordered-field and square-root lemmas directly rather than duplicating their proofs. Reuse them for reporting-scale monotonicity. |
| `Admissions.v` | `Stdlib.Reals.Rplus_le_le_0_compat`, `Stdlib.Lra`, `Stdlib.Psatz`, `Stdlib.Arith.PeanoNat` | Nonnegativity of sums uses library sign lemmas. Keep the four-cell model as explicit report evidence; it is not generic probability infrastructure. |
| `FiniteUnion.v` | `Stdlib.List` / `Stdlib.Bool`: `existsb`, `existsb_exists`, `map_ext`, `map`, `fold_right` | Use library Boolean-list membership and extensionality instead of explicit list inductions. Finite integration and marginal aggregation now delegate to `FiniteSum.finite_sum`. |
| `FiniteMoments.v` | `Stdlib.List`: `map_ext`, `map`, `fold_right`, `combine`, `map_map`; `Stdlib.Reals` | Score sums, weighted expectations, covariance rows and matrix-vector products reuse `FiniteSum.finite_sum`; the remaining matrix/basis definitions retain their report-specific meaning. |

The previous library refactoring also replaced recursive `sum_finite`,
`sum_scores`, `vector_dot`, `linear_combination`, and
`weighted_basis_sum` implementations by standard folds and
`List.combine`. Preserve the public names as thin wrappers so downstream
proof statements and report mappings do not change.

## Consolidated finite real sums and verified model bridge

The shared `FiniteSum.v` module implements one definition using
`Stdlib.List.map` and `fold_right`, and proves **nineteen reusable
lemmas**: extensionality, addition, scalar multiplication, positivity,
monotonicity, zero sums, append, permutation invariance, map composition,
negation, subtraction, reversal, support-aware extensionality,
member bounds, termwise-zero characterization, constant sums, filtered list sums, aligned list zip/map sums, and double-sum interchange. In
`FiniteMoments.v` and `FiniteUnion.v`, public `sum_finite` and
`finite_sum` remain transparent aliases. Existing theorem signatures
are preserved, while the previous duplicate inductions now delegate
to this shared module.

The same shared fold is used by **weighted score combinations, linear
expectations, covariance rows and quadratic forms, score-battery sums,
diagonal variances, vector dot products, Boolean indicator sums and
marginal probability sums**. The only remaining custom list recursion
in the finite-moment module, `unordered_covariance_sum`, depends on
the current list suffix and therefore cannot be replaced by a plain
sum over the original list without changing semantics.

`FiniteBridge.v` adds **fourteen kernel-checked declarations** that join
the two models through the shared finite sum. In particular,
`finite_event_probability_is_indicator_expectation` proves that
event mass equals expectation of the corresponding Boolean indicator;
`finite_event_indicator_variance` proves the Bernoulli identity;
`finite_event_indicator_covariance` proves the intersection-minus-product
identity; and the next two theorems derive the zero-covariance
independence and zero-variance extremal-mass characterizations.
Five further declarations prove the Bernoulli quarter-variance upper bound,
complement variance invariance, and three indicator-covariance complement laws.

**Proof boundaries:** these are exact algebraic identities for finite
real-weighted samples. A probabilistic interpretation requires
nonnegative masses summing to one; neither the bridge nor the
shared sum assumes normality, empirical reliability, or independence.

The pinned GitHub Actions job compiles `FiniteSum.v` before dependent
models and `FiniteBridge.v` after both models. No additional library
version is introduced beyond Rocq 9.2's standard library.

## Verified continuation: direct library-based proof reuse

The following additional results compile with Rocq 9.2 and preserve the
previous public theorem types:

- **FiniteUnion.v:** event-family union probability is insensitive to
  reordering or duplicate routes. These results use
  `Stdlib.List.existsb_exists`,
  `Stdlib.Sorting.Permutation.Permutation_in` and
  `Permutation_sym`, rather than a custom permutation induction.
- **Hoeflin.v:** two fixed-correlation epsilon bounds follow from the
  existing exact variance-gap identity and Stdlib real inverse/product
  inequality lemmas. Neither result imports a separate asymptotic analysis
  library to prove a purely algebraic threshold implication.
- **FiniteMoments.v:** affine variance and covariance results reuse
  `variance_of_shifted_score`, `variance_of_scaled_score`,
  `covariance_invariant_under_first_shift`, and
  `covariance_invariant_under_second_shift`. The mean of a centered
  standardized score now reuses
  `centered_score_has_zero_expectation` instead of duplicating the finite
  expectation calculation. Four matrix shape lemmas use
  `Stdlib.List.length_map` and `in_map_iff`.
- **Admissions.v:** conditional event probabilities are bounded by
  0 and 1 using existing four-cell probability identities together
  with `Stdlib.Reals.Rmult_le_pos`,
  `Rmult_le_compat_r`, and `Rinv_0_lt_compat`.
  Every conditioning denominator is required to be positive.

**Important:** A standard-library proof refactor is not the same as a
migration of all report-specific definitions to abstract measure theory.
The latter requires a chosen library version, import interoperability,
explicit equivalence theorems, and separate build/test validation.

## Additional Rocq 9.2 standard-library substitutions

The November 7 continuation kept all existing theorem types and used
the following library-based constructions and verified proof refactors.

| Module | Reused library and existing proofs | Mathematical result |
|---|---|---|
| `FiniteUnion.v` | `Stdlib.Bool.negb/orb/andb`, `Stdlib.List.existsb_app`, `map_app`, `fold_right_app`, and established finite-sum additivity/extensionality | Exact finite-event complement, binary inclusion–exclusion and event-family append formulas; no new event-set data structure |
| `FiniteMoments.v` | `Stdlib.Reals.Rle_0_sqr`, `Rmult_integral`, `Stdlib.Sorting.Permutation`, plus the existing centered-second-moment and fixed-basis covariance identities | Replaces the last manual real-square sign case split in the variance-nonnegative proof, derives the positive-weight support consequence of zero variance and establishes score-battery permutation invariance |
| `Admissions.v` | Existing conditional numerators, independence implications and `Stdlib.Reals.Rmult_comm` | Establishes both converses: under positive conditioning mass, independence is equivalent to conditional = marginal |
| `Hoeflin.v` | Existing composite-standard-deviation monotonicity and `Stdlib.Reals.Rplus_le_compat_l`, `Rmult_le_compat_l/r` and strict analogues | Derives weak and strict correlation-dependent cutoff-order theorems without duplicating the SD argument |

**Boundary:** There is deliberately no dependency on MathComp or Coquelicot
for simple finite Boolean/list and ordered-field calculations already
supported by Rocq Stdlib. Full replacement of the list-based finite
model by a general measure or matrix library is a future migration,
not something completed by these proof additions.

## Additional library-backed refactoring and proof results (November 7)

- `FiniteSum.v` derives map preservation using Rocq's `map_map`,
  reversal preservation using `Permutation_rev`, and signed-sum
  operations from existing finite-sum additivity and scaling. This
  adds **four** declarations without additional custom recursion.
- `FiniteUnion.v` no longer inducts over outcomes to show an empty
  event-family has zero probability. It instead uses the existing
  `finite_sum_zero` result. For singleton and two-event families,
  `orb_false_r` replaces Boolean truth-table proof branches.
- `FiniteBridge.v` obtains **five** new theorems by reduction to
  established finite-moment identities. The proof of `Var(1_A) <= 1/4`
  uses the standard nonnegativity of real squares. The remaining
  statements interpret event complements through normalization and
  covariance shift/scale/symmetry.
- An actual source recount reports **289** named theorem/lemma/example
  declarations: 64, 67, 30, 102, 12 and 14 for `Hoeflin`,
  `Admissions`, `FiniteUnion`, `FiniteMoments`, `FiniteSum`
  and `FiniteBridge`, respectively. The previous tally overcounted
  the `Hoeflin` module by one.

All three proof-source changes passed the Rocq 9.2 kernel job at
commit `65f1e6924b9edfa4bfc6799be27fe890d20a325a`.
The root README, historical Ada/SPARK evidence, and report PDFs
were not modified. This remains a targeted refactor, not a claim of
wholesale migration to MathComp, Coquelicot or general measure theory.

## Checked four-cell product interpretation and additional library reuse (November 8)

The `FourCellBridge.v` module interprets the four report-specific
admission outcomes on the standard `bool * bool` product type using
`Stdlib.List.list_prod [true; false] [true; false]`. Library
`in_prod` and `length_prod` prove the four-cell enumeration covers
every Boolean pair and has four entries. The model's weights use only
the original `Admissions.TwoEventModel` field projections, with
the original nonnegativity and normalization premises.

It then proves **13 declarations**: outcome completeness and length,
weight nonnegativity and normalized mass, marginal A/B mass, intersection
and union mass, exactly-one mass, covariance, independence criterion,
and Bernoulli variance of both indicators. Covariance and Bernoulli
variance are obtained by reusing the existing `FiniteBridge` results.

The `FiniteUnion` module adds **8** generic facts about finite event
mass and reuses `FiniteSum.finite_sum_app`, `finite_sum_permutation`,
`finite_sum_zero` and the established indicator order bounds.
The empty-event-family proof now delegates to its false-event result.

`FiniteMoments` removes two duplicate inductions over equal-length
`List.combine` arguments. A shared projection lemma and the library's
`List.combine_split` provide both public results. The existing
`expectation_sub` proof now uses `FiniteSum.finite_sum_sub`.
There is one new shared projection lemma; all previous theorem
statements are unchanged.

At the four-cell bridge milestone, the seven source files contained **311 declarations**:
64 (`Hoeflin`), 67 (`Admissions`), 38 (`FiniteUnion`),
103 (`FiniteMoments`), 12 (`FiniteSum`), 14 (`FiniteBridge`)
and 13 (`FourCellBridge`). The first six were checked for
named-statement preservation against `a2f6427`.

This remains an incremental refactor. No wholesale migration to
MathComp, Coquelicot, abstract measure theory or a separate matrix
library has been performed; such a migration needs checked
interpretation/compatibility proofs.

## Previous library-consolidation milestone: 320 checked declarations

This continuation verifies four generic finite-sum laws and five
finite-event laws, retaining all 311 prior named proof statements:

| Module | Reused library or theorem | Replaced/added proof responsibility |
|---|---|---|
| `FiniteSum.v` | `Stdlib.List.map_ext_in` | `finite_sum_ext_in` weakens the extensionality premise to support membership; the pre-existing `finite_sum_ext` is now a wrapper |
| `FiniteSum.v` | Existing `finite_sum_nonnegative` and real linear order | `finite_sum_member_le` and `finite_sum_nonnegative_zero` centralize nonnegative-weight member bounds and the zero-sum criterion |
| `FiniteSum.v` | Existing `finite_sum_add`, `finite_sum_zero`, Rocq Stdlib list folds | `finite_sum_swap` establishes the reusable finite Fubini identity, without introducing another recursion or requiring a general measure theory |
| `FiniteMoments.v` | `FiniteSum.finite_sum_nonnegative_zero` | `sum_finite_zero_implies_zero_terms` preserves its public theorem statement while removing its separate list induction |
| `FiniteUnion.v` | `Stdlib.List.existsb_exists`, `FiniteSum.finite_sum_member_le` | `union_indicator_bound` no longer performs bespoke Boolean-event list induction |
| `FiniteUnion.v` | `FiniteSum.finite_sum_scale` and `finite_sum_swap` | `interchange_finite_sums` delegates to generic finite-sum laws, eliminating another event-list induction |
| `FiniteUnion.v` | Support-aware extensionality and nonnegative member/zero theorems | Characterizes when event probability is zero and when an observed positive-weight event forces positive mass |
| `FiniteUnion.v` | `finite_prob_event_monotone`, `finite_prob_inclusion_exclusion`, `normalized_finite_prob_unit_interval` | Derives arbitrary finite-event Fréchet overlap bounds rather than repeating four-cell algebra |

**Inventory at this milestone:** `FiniteSum` 16; `Hoeflin` 64;
`Admissions` 67; `FiniteUnion` 43; `FiniteMoments` 103;
`FiniteBridge` 14; `FourCellBridge` 13. **Total: 320**.

The complete seven-module proof source at commit
`f7425656ff7b2f82ed96f5b6348020aec7c6aee1`
passed the pinned Rocq 9.2 kernel check. No previously named
theorem, lemma, or example statement was modified. The root README,
original report sources/PDFs and historical Ada/SPARK proof evidence
remain unchanged.

A complete replacement with MathComp matrices or a continuous
measure library is not claimed. Both would require pinned additional
dependencies and kernel-checked translation/equivalence theorems
that preserve the existing finite interpretations.

## Continued covariance and finite-sum consolidation: 325 checked declarations

At that covariance-refactoring milestone, the seven-module source inventory was **325**:
64 `Hoeflin`, 67 `Admissions`, 43 `FiniteUnion`,
107 `FiniteMoments`, 17 `FiniteSum`, 14 `FiniteBridge`,
and 13 `FourCellBridge`.

The current pinned Rocq 9.2 workflow **passed** for commit
`2a7af1e3639f96d749fb00519ad7ed97b3c022ec`.
The scope of the new changes is limited to `FiniteSum.v` and
`FiniteMoments.v`; the root README, original reports, Ada/SPARK
evidence and theorem statement types were not modified.

| Refactored theorem | Existing library/verified result | Replaced implementation |
|---|---|---|
| `diagonal_variance_sum_of_unit_scores` | New reusable `FiniteSum.finite_sum_const`, `finite_sum_ext_in`, Rocq Stdlib `INR` and `S_INR` | Removed unit-variance list induction |
| `covariance_row_sum_bounded_by_count` | `finite_sum_monotone`, `finite_sum_const`, checked unit-variance pairwise covariance bounds | Removed row sum induction |
| `covariance_double_sum_second_cons` | `finite_sum_add` and `covariance_symmetric` | Removed double covariance sum induction |
| `expectation_of_general_weighted_sum` | `finite_sum_swap`, `finite_sum_scale`, `finite_sum_ext` | Removed weighted-component expectation induction |
| `covariance_of_general_weighted_sums` | `covariance_of_general_weighted_second`, `covariance_symmetric`, `finite_sum_ext` | Removed first-battery covariance induction |
| `covariance_with_sum_scores` | `Stdlib.List.map`, `finite_sum_map`, `covariance_of_general_weighted_second` | Replaced single-battery covariance induction by two explicit, proved unweighted/weighted interpretation lemmas |
| `covariance_of_sum_scores` | `covariance_with_sum_scores`, `covariance_symmetric`, `finite_sum_ext` | Removed two-battery covariance induction |

**Five new declarations:** the generic
`FiniteSum.finite_sum_const`; `covariance_double_sum_symmetric`
using `finite_sum_swap`; `covariance_cross_matrix_bilinear_swap`
using the existing fixed-basis cross-matrix theorem; and
`unweighted_scores_as_linear_combination` plus
`unweighted_covariance_row_as_weighted` interpreting unweighted lists
as unit-weight components by `Stdlib.List.map`.

**Regression evidence:** direct source signature comparison against
the previously kernel-checked branch commit `98c030e` finds
all 320 original theorem/lemma/example declarations with **unchanged
statements**. The latest addition compiles without any new
`Axiom`, `Admitted`, `Parameter`, or external package dependency.

There are still indispensable structural list inductions for
suffix-dependent unordered-pair sums and list-shaped matrix
representations. Replacing the report-specific finite semantics with
MathComp matrices or arbitrary probability measures would require
additional *proved* interpretations and compatibility results, not
merely imports of new packages.

## Complete Rocq declaration documentation and Stdlib filter reuse

**Current public proof inventory:** 328 named theorem, lemma and example
declarations across seven modules: `Hoeflin.v` 64, `Admissions.v` 67,
`FiniteUnion.v` 45, `FiniteMoments.v` 107,
`FiniteSum.v` 18, `FiniteBridge.v` 14,
`FourCellBridge.v` 13. The extra `Local Lemma` in
`Hoeflin.v` is also checked, making 329 proof declarations when
internal scoped proof helpers are counted.

**Documentation coverage:** all 385 declarations, including definitions,
record types, local helper lemmas and theorems, now have explicit adjacent
`(** ... *)` comments. Each module begins with a multi-paragraph
header describing mathematical purpose, the explicit finite model,
required hypotheses, existing library dependencies, reproduction steps
and boundaries of the claims. Each declaration's comment identifies:

1. The precise formal statement/definition and mathematical interpretation.
2. Explicit normalization, positivity, dimension or nonzero hypotheses
   (where present), rather than an unexplained "probability" assumption.
3. The actual proof route, including uses of `rewrite`, `lra`,
   `nra`, `ring`, induction, and reused generic finite-sum lemmas.
4. The standard library imports and limitations on interpretation.

The **Rocq theorem statements and proof bodies were not modified**
during the documentation pass. Changes are purely comments apart from
three small mathematical library-backed proofs committed beforehand.

| New proof | Stdlib/earlier lemma reuse | Why this is preferable |
|---|---|---|
| `FiniteSum.finite_sum_filter` | `Stdlib.List.filter`, the existing `finite_sum` wrapper | One generic characterization of filtering, not new event-specific summation recursion |
| `FiniteUnion.finite_prob_as_filtered_mass` | `FiniteSum.finite_sum_filter`, `finite_sum_ext` | Event mass equals the sum of weights on outcomes selected by `List.filter`, with no extra normalization assumptions |
| `FiniteUnion.finite_prob_event_ext_on_samples` | `FiniteSum.finite_sum_ext_in` | Event predicates need agree only on the finite sample's support |

The new [`scripts/check_rocq_documentation.sh`](../scripts/check_rocq_documentation.sh)
is a reproducible *static documentation policy check*, not a proof
checker. It verifies the explanatory header and the adjacent,
declaration-named, substantive doc comments for all seven modules.
GitHub Actions runs it before pinned Rocq 9.2 kernel checking.
It is a standalone shell utility invoking Python's standard library
inline, rather than adding another Python source file. This preserves
the repository's existing source-pinned Python Deal/SPARK verification
inventory. The `Python contracts` workflow, its five-contracts-per-
function rule, and the original evidence are not weakened or altered.

**Source count distinction:** the README's 328 public theorem/lemma/example
declarations exclude the existing `Local Lemma`, whereas the checker
counts all 329 proof declarations and also 56 non-proof declarations
for a total of 385. This is a counting convention, not missing proof
coverage or new axioms.

The root README, source reports, and historical SPARK proof evidence
remain unchanged. This pass does not constitute a complete rewrite
using MathComp or an arbitrary-measure library. Any such migration
would need independently checked correspondence lemmas preserving
the finite semantics and theorem hypotheses.

## Previous proof-by-proof consolidation milestone: 332 scripts

The latest source now contains **329 public theorem/lemma/example
declarations** (FiniteSum 19, Hoeflin 64, Admissions 67,
FiniteUnion 45, FiniteMoments 107, FiniteBridge 14, FourCellBridge 13).
One existing `Local Lemma` and two `Definition` constructors with
explicit `Proof./Defined.` bring the source to **332 proof scripts**.
These belong to **386 named declarations** in the seven modules.

The [proof-by-proof register](PROOF_REFACTOR_REGISTER.md) lists all
332 scripts and classifies each by existing Rocq library use, proof
method, and retention or refactor decision. The Rocq CI documentation
checker validates the **complete ordered inventory** on every push.
This is a source-level completeness check; it is distinct from the
pinned Rocq 9.2 kernel checker, which verifies the actual terms.

| Proof refactor | Existing reusable library | Effect |
|---|---|---|
| `finite_sum_zero` | `FiniteSum.finite_sum_const`, `Stdlib.Reals` ring | Remove induction over an arbitrary finite list for the constant-zero special case |
| `finite_sum_monotone` | `finite_sum_nonnegative`, `finite_sum_sub`, `Stdlib.Lra` | Derive order preservation from the already checked sign of the pointwise difference |
| `finite_sum_zip_map` (generic helper) | `Stdlib.List.map`, `combine`, existing `finite_sum_map` | Prove the aligned zip/map identity once, not in report-specific matrix arguments |
| `covariance_row_as_vector_dot` | `finite_sum_zip_map`, support-independent `finite_sum_ext` | Eliminate a duplicated list induction over score components |
| `covariance_double_sum_as_matrix_product` | `Stdlib.List.map_map`, `finite_sum_zip_map`, `covariance_row_as_vector_dot` | Eliminate a second specialized matrix-row list induction |

**Structural induction review.** Exactly fifteen scripts still use an
induction tactic. Ten establish genuine basic fold/list algebra in
`FiniteSum`; one is the `Admissions.Nat.iter` closed-form theorem;
four are over weighted components or suffix-dependent covariance and
the `Stdlib.List.split` representation in `FiniteMoments`.
Keeping these inductions is intentional: a replacement must have
genuinely identical semantics, not merely a familiar theorem name.
Their names and refactoring dispositions are explicit in the
proof-by-proof register.

**Scope.** Every proof has been inspected and classified for library
reuse; not every proof text was changed. Trivial definitional proofs,
direct calls to Rocq's Reals/Lra/Psatz/ring/field facilities, and checked
previously formalized bridges should remain simple. The previous
public theorem statements and their hypotheses are unchanged.
No `Admitted`, project-specific axiom, external oracle, new recursive
matrix implementation, or unpinned library dependency has been added.

## Previous library consolidation: Boolean selection and sample partition

The current seven-module source inventory contains **333 public
theorem/lemma/example declarations**, plus one checked local helper,
and two proof-bearing four-cell record constructors, for **336 total
proof scripts**. All **390 named declarations** have their own
mathematical documentation comments, and the seven modules have
substantive explanatory opening headers.

This iteration reuses the native Rocq list and Boolean facilities
rather than creating a specialized event-selection implementation:

| New or revised proof | Reused checked library | Proof responsibility |
|---|---|---|
| `finite_prob_event_ext_on_samples` (refactor) | `Stdlib.List.filter_ext_in`, `finite_prob_as_filtered_mass` | Event predicates need agree only on the explicitly enumerated support |
| `finite_prob_on_filtered_samples` | `Stdlib.List.filter`, `Stdlib.Bool.andb`, `FiniteSum.finite_sum_filter` | Equate restriction of sample outcomes with Boolean intersection of events |
| `union_prob_on_filtered_samples` | Existing `finite_prob_on_filtered_samples`, `Stdlib.List.existsb` | Derive filtered union mass without custom event-family recursion |
| `finite_prob_filtered_partition` | Existing `finite_prob_on_filtered_samples`, `finite_sum_addition`, Bool case split | Recover full event mass by adding selected and rejected sample contributions |
| `union_prob_filtered_partition` | `finite_prob_filtered_partition`, existing `union_prob` abstraction | Lift the partition identity to an arbitrary finite union of routes |

**Hypothesis discipline:** identities are valid for arbitrary real
sample weights and support multiplicities. No nonnegative weights,
normalization or event independence is assumed just to prove an
equality. The separate distribution-free probability inequalities
retain their explicit sign and normalization hypotheses.

The [full proof-by-proof register](PROOF_REFACTOR_REGISTER.md)
now lists all 336 scripts and records a decision on each.
The [CI documentation checker](../scripts/check_rocq_documentation.sh)
compares register names in source order, verifies every declaration's
extensive `(** ... *)` comment and the module-level headers, and then
runs the pinned Rocq 9.2 kernel verification. No `Axiom`,
`Admitted`, `Parameter`, untrusted oracle, or new third-party Rocq
library was introduced.

As before, substantive structural inductions remain where they
establish generic fold laws, `Nat.iter` behavior or suffix-sensitive
covariance identities. They are not replaced with gratuitous duplicate
recursions. All existing theorem statements and mathematical
assumptions remain unchanged.

## Previous covariance consolidation: finite-sum linearity without normalizing mass

**Current inventory:** 334 public theorem/lemma/example declarations
across seven modules, one additional local helper, two explicitly
proved record constructors, **337 total proof scripts** and **391
named declarations**, all with declaration-level documentation.
Each Rocq file begins with an explanatory header.

The new theorem
`FiniteMoments.covariance_of_general_weighted_second_unconditional`
proves that covariance against a finite weighted component sum
equals the sum of the component covariances, with **no normalization
assumption** on sample weights. It follows purely from the definition
of covariance, expectation linearity and finite-sum algebra.

| Refactored proof | Standard/checked library reuse | Removed duplication |
|---|---|---|
| `covariance_of_general_weighted_second_unconditional` (new, stronger algebraic theorem) | `Stdlib.List.map`, `expectation_of_general_weighted_sum`, `FiniteSum.finite_sum_map`, `finite_sum_scale`, `finite_sum_sub`, `finite_sum_ext` | Combines finite covariance components without manually recursing through score batteries |
| `covariance_of_general_weighted_second` (original theorem preserved) | New unconditional identity | Removes the earlier repeated structural induction while preserving the exact `total_mass = 1` premise for API compatibility |

This removes one of the remaining report-specific component-list
inductions: **14 structural inductions** remain in the 337-script
[proof register](PROOF_REFACTOR_REGISTER.md). Generic fold algebra,
`Nat.iter` recurrence and suffix-sensitive unordered-pair covariance
still use structural induction where there is no equivalent direct
standard-library theorem. No additional recursion, custom algebra,
new axiom, `Admitted`, or unpinned package was introduced.

The mathematical interpretation is exact *finite real-weighted*
moment algebra. The stronger identity does not turn arbitrary signed
weights into probabilities, establish a Gaussian joint distribution,
or infer actual psychometric performance from a data set.

## Definition-level documentation audit: 19 foundational constructions

All 394 declarations have the required adjacent `(** ... *)`
comments, and seven module headers document representation,
assumptions, Stdlib dependency order, limitations and reproduction.
This additional pass replaces generic explanations for **19
foundational definitions**, without changing their terms:

- Shared sums: `FiniteSum.finite_sum`, with exact map/fold semantics,
  duplicate occurrences, sign freedom and permutation behavior.
- Finite Boolean events: eight definitions including `Event`,
  `indicator`, `any_event`, `sum_event_indicators`,
  `finite_prob`, `sum_marginal_probs` and `union_prob`.
  Their comments distinguish sums of overlapping marginals from
  union mass and identify `Stdlib.List.existsb` and filtering.
- Finite moments: ten definitions, including `sum_finite`,
  `total_mass`, `expect`, `covariance`, `variance`,
  `centered_second_moment`, `linear_combination`,
  `linear_expectation`, `covariance_row`, and
  `covariance_quadratic_form`.

The comments distinguish **a finite algebraic expression over
signed real weights** from a probability interpretation that
requires nonnegative sample mass and normalization. In particular,
centered second moment and variance coincide under explicit unit
mass, while the underlying definitions do not silently assume that
premise. This is important for assessing formal theorem claims:
correct kernel proofs over an unsuitable model would not be
evidence for empirical psychometric conclusions. Every new proof
and definition remains subject to the same source-order
documentation check and Rocq 9.2 kernel verification.

## Previous partition-library consolidation and proof coverage

The seven Rocq modules now contain **337 public theorem, lemma and
example declarations**, one additional local helper and two explicit
record-constructor proofs, totaling **340 proof scripts**.
All **394 named declarations** have detailed `(** ... *)`
comments, all modules retain explanatory header comments, and the
[complete ordered proof register](PROOF_REFACTOR_REGISTER.md) is
checked by the GitHub Actions documentation gate.

The latest changes deliberately reuse the existing Rocq Stdlib and
our proven generic finite-sum lemmas:

| Proof | Reused library results | Change |
|---|---|---|
| `FiniteSum.finite_sum_filter_partition` | `Stdlib.List.filter`, `Stdlib.Bool.negb`, `finite_sum_filter`, `finite_sum_add`, `finite_sum_ext`, `ring` | Proves list-fold partition additivity for arbitrary signed real terms without a separate list induction |
| `FiniteUnion.finite_prob_filtered_partition` | `finite_sum_filter_partition` | Removes project-specific Boolean/indicator case analysis in favor of the general list theorem |
| `FiniteUnion.finite_prob_complement` | `finite_prob_as_filtered_mass`, `finite_sum_filter_partition`, `Rplus_comm` | Derives event-complement mass using filtered lists rather than duplicated indicator algebra |
| `FiniteUnion.finite_prob_filtered_mass_le` | `finite_prob_event_monotone`, `Stdlib.Bool.andb_true_iff` | Proves nonnegative-weight selection monotonicity without another finite-sum proof |
| `FiniteUnion.union_prob_filtered_mass_le` | `finite_prob_filtered_mass_le`, `Stdlib.List.existsb` | Lifts monotonicity to finite unions of Boolean events |

No new recursive `filter`, `map`, list sum, covariance function,
or matrix implementation has been introduced. The sum identity is
valid even with negative weights; the two **monotonicity inequalities
require nonnegative sample weights** and correctly do not claim
bounds for signed masses. Neither independence nor total-mass-one
is required for these results.

Fourteen underlying structural inductions remain, all listed
in the proof register. The previous public theorem statements
and hypotheses remain unchanged. No new axioms, `Admitted`,
parameters, oracle, unpinned library or changes to the
historical Python/SPARK evidence were introduced.

## Theorem-comment audit: eight strengthened mathematical explanations

Beyond the 399 declaration-specific comments and seven explanatory
module headers, this continuation replaces generic comments on
**eight widely reused theorems**, without changing any declaration
statement or proof term:

- `FiniteBridge.finite_event_probability_is_indicator_expectation`,
  `finite_event_indicator_covariance` and
  `finite_event_independence_iff_zero_indicator_covariance`:
  clarify the direct 0-1 indicator equivalence, the covariance
  independence residual and the required normalization premises
  for interpreting algebraic factorization as independence.
- `FiniteMoments.variance_of_general_weighted_sum`,
  `covariance_matrix_is_positive_semidefinite` and
  `finite_covariance_cauchy_schwarz_squared`:
  explain the actual finite covariance quadratic form, precise
  nonnegative-weight hypotheses and degeneracy or strictness
  boundaries. The matrix theorem does not silently assert
  strict positive definiteness.
- `FiniteUnion.finite_prob_sample_append` and
  `union_prob_append`: distinguish concatenation of sample
  occurrences from concatenation of event-family predicates
  and identify the exact reusable Stdlib.List and FiniteSum
  laws that discharge the proofs.

This matters because a kernel-checked equality between real
list expressions is not, by itself, a validated probabilistic
or empirical model. The explanations make the scope of the
checked claims explicit and auditable.

## Previous Stdlib reuse: concatenated samples and indicator expectations

Seven Rocq modules now contain **342 public theorem/lemma/example
declarations**, one checked local helper and two constructed records
with explicit proofs, for **345 proof scripts** in total. All
**399 named declarations**, including definitions, have substantive
per-declaration comments, with explanatory module headers in each
`.v` file. The [proof register](PROOF_REFACTOR_REGISTER.md)
accounts for each proof in exact source order, enforced by CI.

Five new results make established finite enumeration operations
available across the event and moment layers, without adding new
recursive definitions:

| New proof | Existing checked/Stdlib law used | Purpose |
|---|---|---|
| `union_prob_sample_append` | `finite_prob_sample_append`, `union_prob` alias, `Stdlib.List.existsb` | Concatenate outcome lists while preserving union mass additivity |
| `finite_prob_filtered_append` | **`Stdlib.List.filter_app`**, `finite_prob_sample_append` | Distribute filtering of a sample append through finite event-mass sums |
| `union_prob_filtered_append` | **`Stdlib.List.filter_app`**, `union_prob_sample_append` | Obtain the corresponding result for a finite event family |
| `filtered_event_mass_is_indicator_expectation` | `finite_prob_on_filtered_samples`, `finite_event_probability_is_indicator_expectation` | Interpret filtered event mass as a Boolean conjunction indicator score |
| `filtered_union_mass_is_indicator_expectation` | `union_prob_on_filtered_samples`, `finite_event_probability_is_indicator_expectation` | Interpret filtered finite union mass through the existing finite-moment functional |

The preexisting `union_prob_append` proof was also refactored:
it now directly applies `finite_prob_event_ext_on_samples`
and `any_event_append` (which itself uses
**`Stdlib.List.existsb_app`**) rather than unfolding
and repeating a separate finite-sum extensionality calculation.

All new equalities are valid for **arbitrary real sample weights**,
including negative values, and **duplicate sample occurrences**.
Nonnegativity and normalization belong to separate probability
bounds and must not be inferred from these identities. Event
independence is neither assumed nor established. The new bridge
theorems do not construct conditional expectations, continuous
measures or empirical estimates.

The 14 structural-induction scripts remain justified by the
underlying generic fold, natural-number recurrence and
suffix-dependent covariance definitions. No extra fold, event
union, filter, matrix representation, custom axiom, `Admitted`
or unpinned library was added. Previous named theorem
statements and historical Python/SPARK evidence are unchanged.

## Previous library consolidation: unnormalized composite covariance/matrices

The [ordered proof-refactor register](PROOF_REFACTOR_REGISTER.md)
now records **350 proofs**, including five new, stronger finite
real-weighted covariance/matrix theorems. The formalization contains
**347 publicly named theorem/lemma/example declarations** and
**404 named declarations in total**, all with extensive adjacent
mathematical comments; the seven Rocq modules retain explanatory
opening headers.

The new statements deliberately avoid inventing any generic
matrix or covariance implementation, delegating to existing
checked algebra:

| New theorem | Reused Stdlib or established shared lemmas | Refactored public theorem |
|---|---|---|
| `covariance_of_general_weighted_sums_unconditional` | `covariance_of_general_weighted_second_unconditional`, `covariance_symmetric`, `FiniteSum.finite_sum_ext` | `covariance_of_general_weighted_sums` |
| `variance_of_general_weighted_sum_unconditional` | Generic unconditional composite covariance and the existing variance alias | `variance_of_general_weighted_sum` |
| `covariance_cross_matrix_bilinear_identity_unconditional` | `covariance_double_sum_as_matrix_product` and unconditional composite covariance | `covariance_cross_matrix_bilinear_identity` |
| `covariance_cross_matrix_bilinear_swap_unconditional` | Unconditional cross-matrix representation and `covariance_symmetric` | `covariance_cross_matrix_bilinear_swap` |
| `covariance_matrix_quadratic_form_is_variance_unconditional` | `covariance_matrix_quadratic_form_identity` and unconditional weighted variance | `covariance_matrix_quadratic_form_is_variance` |

The five pre-existing theorem signatures remain **unchanged**,
including their normalized-mass premises; each old proof now
specializes the more general algebraic theorem. No new induction
is needed. The 14 remaining structural inductions implement
generic list/fold algebra, the natural-index recurrence or
suffix-sensitive covariance enumeration and remain explicitly
justified in the register.

**Logical distinction:** A real-valued finite linear functional
does not need to satisfy `E[1] = 1` for covariance bilinearity.
Therefore these matrix/composite identities also hold for
unnormalized signed weights. However signed weights do **not**
imply probability measures, nonnegative variance or positive
semidefinite covariance matrices. The existing PSD/boundedness
results retain the required nonnegative-weight and unit-mass
premises. These results do not establish numerical correlations,
Gaussian distributions, or empirical IQ validity.

No new `Axiom`, `Parameter`, `Admitted`, unpinned dependency,
recursively reimplemented list/matrix primitive, or change to the
archived source-pinned SPARK/Python evidence is introduced.

## Current Stdlib consolidation: finite unweighted score-list moments

The existing Rocq code already uses `Stdlib.List.map` to represent
an unweighted list of score functions as unit-coefficient pairs
inside the shared `linear_combination` abstraction.
This is enough to generalize three score-list moment results
without adding a recursive list sum or a separate unweighted
covariance implementation.

| New unconditional theorem | Exact checked library reuse | Original theorem refactored |
|---|---|---|
| `covariance_with_sum_scores_unconditional` | `Stdlib.List.map`, `unweighted_scores_as_linear_combination`, `covariance_of_general_weighted_second_unconditional`, `unweighted_covariance_row_as_weighted` | `covariance_with_sum_scores` |
| `covariance_of_sum_scores_unconditional` | `covariance_with_sum_scores_unconditional`, `covariance_symmetric`, `FiniteSum.finite_sum_ext` | `covariance_of_sum_scores` |
| `variance_of_unweighted_sum_unconditional` | `covariance_of_sum_scores_unconditional`, the existing `variance` alias | `variance_of_unweighted_sum` |

The three original theorem statements, each including
`total_mass = 1`, remain unchanged; their bodies now apply
the stronger unconditional results. This continues the
algebraic generalization of finite composite covariance.
It does **not** infer nonnegative variance or PSD covariance
matrices for signed, unnormalized sample weights.

**Current audited inventory:** 424 public theorem/lemma/example
declarations, one local helper and two proof-bearing record
constructors, for **427 proof scripts**. There are **482 named
declarations** across seven Rocq modules, all with adjacent
mathematical comments; every module retains an explanatory header.
The [proof-by-proof register](PROOF_REFACTOR_REGISTER.md) contains
the exact ordered source inventory checked by CI.

The 14 remaining list/natural-number inductions stay in their
documented core fold/recurrence/suffix-dependent proofs.
No new untrusted axiom, `Admitted`, custom matrix or fold
implementation, unpinned library, or change to historical
Python/SPARK verification evidence has been introduced.

## Four-cell conditional probability bridges (November 8)

Five further theorems interpret the B-only event and all four existing
Admissions conditionals as generic finite-event masses and ratios.
The only enumerated proof is a direct standard-library Boolean pair
calculation; the ratio proofs reuse established event mass bridges.
Each denominator is explicitly positive. All prior statements remain
unchanged, and the audited inventory is 355 public claims, 358 scripts,
412 fully documented declarations across the original seven files.
No new recursion, probability axiom or empirical claim is introduced.

## Shared conditional event operator (November 8)

`FiniteUnion.finite_conditional_prob` is defined by composing the
pre-existing indicator-event intersection mass and conditioning mass
using standard real division. Its filtering theorem delegates to
`finite_prob_on_filtered_samples`; positive-mass self-conditioning
uses `finite_prob_event_ext_on_samples` and the standard `field` tactic with an explicit nonzero denominator. Two
four-cell corollaries reuse the preceding conditional bridge proofs,
with unchanged side conditions. The total source inventory rises to
359 publicly named claims, 362 proof blocks, and 417 declarations.
No new probability axioms, list recursions or matrix implementations
are introduced.

## New finite conditional bounds and event extensionality

Three new FiniteUnion results reuse finite_prob_event_monotone,
finite_intersection_at_most_first, finite_prob_event_ext_on_samples,
finite_prob_complement and finite_prob_as_filtered_mass to establish
bounded positive-mass conditional probability, pointwise support
extensionality, and conditional event/complement additivity. Reals
inverse cancellation and order lemmas handle division; no new list recursion or measure
implementation is introduced. The inventory at that earlier stage was
362 public proofs, 365 proof scripts and 420 named declarations.

## Completed four-cell conditional specialization

Two new FourCellBridge declarations bridge the generic conditional
operator to both-given-either and not-A-given-B, reusing
`finite_prob_event_ext_on_samples`,
`two_event_union_probability`, `Stdlib.Bool.andb_comm` and the
previously checked four-cell conditional ratios. Four of four report
conditional expressions now have exact generic finite-event
interpretations. The totals at that earlier stage were 364 public proofs,
367 proof scripts, and 422 documented declarations. All prior
statements remain unchanged and no alternate event/mass implementations
are introduced.

## Stronger conditional support and monotonicity results

Four new FiniteUnion proofs reuse Stdlib.Bool and existing
finite-event extensionality/monotonicity to prove target equality
on selected conditioning support, conditional monotonicity, the
true-event conditional identity and conditioning-event support
extensionality. An existing weaker support theorem has been
refactored to apply the new stronger result, rather than repeat
pointwise conjunction reasoning. No new recursions, unpinned
libraries, axioms or altered public claims are introduced.
At the preceding stage: 368 publicly named proofs, 371 scripts and
426 fully documented declarations.

## Conditional algebra, Bayes balance and finite partition

Four new FiniteUnion proofs reduce conditional false mass, two-event
inclusion–exclusion, Bayes balance and total probability to the shared
`finite_prob` and `finite_conditional_prob` definitions. Library
reuse is explicit: Stdlib.Bool.andb_comm, Stdlib.Reals field/ring,
`finite_prob_inclusion_exclusion`, `finite_prob_filtered_partition`,
`finite_prob_event_ext_on_samples`, and `Stdlib.List.filter`.
That preceding stage contained 372 public proofs, 375 proof blocks and
430 documented declarations. No new measure axioms are introduced.

## Chain rule and matrix null-direction consequences

The conditional chain rule invokes finite_prob_event_ext_on_samples,
Stdlib.Bool.andb_assoc and Rocq's real-field tactic. Three new finite
matrix results invoke existing fixed-basis variance identification,
finite Cauchy–Schwarz, zero-variance covariance, and positive-support
constant-score theorems. No separate matrix implementation or unverified
rank function is introduced. That earlier stage covered 376 public
claims, 379 proof scripts and 434 documented declarations.

## Duplicate-basis covariance degeneracy witness

The new constant-score variance lemma delegates to
`covariance_with_constant_first` rather than repeating expected-value
algebra. The duplicate-basis theorem uses existing fixed-basis
variance representation, `Stdlib.List.combine`, shared finite sums,
variance extensionality and ring/Lra to exhibit an explicit nonzero
zero-quadratic-form coefficient vector [1,-1]. It makes no unsupported
claim about a general rank implementation or numerical matrix rank.
At the earlier stage: 378 publicly checked claims, 381 proof scripts and
436 fully documented declarations.

## Enumerated-support extensionality reuse

Three additional finite-moment results reuse the canonical
`FiniteSum.finite_sum_ext_in` (Stdlib.List.map_ext_in) for equality of
expectation, covariance and variance from on-sample equality, with
unchanged weight multiplicity. The current source inventory covers
381 public proofs, 384 scripts and 439 documented declarations.

## Exact finite covariance null support equivalence

Positive-weight support extensionality for moments is derived from
FiniteSum.finite_sum_ext_in and Stdlib.Reals.Rle_lt_dec, with
zero-weight outcomes contributing no weighted integrand.
The resulting zero-variance converse combines with existing
`null_covariance_direction_constant_on_positive_mass` and
`fixed_basis_weighted_variance_identity` to characterize zero
fixed-basis covariance quadratic form exactly. No new data
structure, recursive finite sum, determinant or eigenvalue solver
is implemented. Inventory: 386 claims, 389 scripts, 444 declarations.

## Generic zero-variance equivalences and fixed-basis reuse

The equivalence between zero variance and constant positive-weight
support reuses checked forward/backward implications. Zero variance
is additionally equivalent to zero covariance with every comparison
score, by the finite Cauchy–Schwarz-derived covariance-zero lemma.
The previously added fixed-basis null/constant result now delegates
to the general equivalence, while a new fixed-basis orthogonality
iff follows from the existing variance/matrix identity.
No determinant, eigenvalue, or rank implementation is added.
Current inventory: 389 claims, 392 scripts and 447 declarations.

## Strict positivity from positive-weight score witnesses

Four new claims transfer the existing zero-variance support
characterization to strictly positive variance and fixed-basis
quadratic-form conclusions when one positive-weight score
deviates from its expectation, or two such outcomes differ.
All proofs reuse variance_nonnegative, existing support lemmas,
the fixed-basis variance identity, and Stdlib.Lra without
implementing another covariance or matrix algebra.
At the previous stage: 393 claims, 396 proofs, 451 named declarations.

## Finite covariance positive definiteness without rank reinvention

Three theorems derive positive variance and positive fixed-basis
quadratic form from positive-weight support nonconstancy, and
characterize positive definiteness in all nonzero coefficient
directions using Stdlib.List.repeat as the zero list. They reuse
variance_nonnegative, prior exact zero-variance iff facts and
the existing fixed-basis variance identity. Two old proofs now
delegate to those shared results, eliminating their duplicated
real-order case distinctions. No new recursion, rank function,
spectral library emulation or unproved axioms are introduced.
At the preceding stage: 396 public claims, 399 scripts, 454 declarations.

## Finite covariance positive-definiteness witnesses

Two new results apply the existing positive quadratic-form
witness lemmas to each nonzero compatible coefficient list.
A third reuses the fully checked fixed-basis covariance
orthogonality/nullity and strict-positivity equivalences,
establishing positive definiteness iff no nonzero
direction is uncorrelated with every comparison score.
Stdlib.List.repeat expresses the zero coefficient list;
no new matrix rank, determinant or kernel algorithm is added.
The latest audit covers 399 claims, 402 scripts and
457 fully documented declarations.

## Stronger finite support covariance and variance reuse

Zero covariance of a positive-support-constant score in either
argument is now derived directly from
covariance_extensional_on_positive_weight_support,
covariance_with_constant_first, and covariance symmetry.
The previous proof of zero variance for support-constant
scores is shortened to its self-covariance corollary,
and zero variance is characterized by existence of any
positive-support constant. No new matrix or fold algorithms,
axioms, or admitted statements are required.
Updated inventory: 402 claims, 405 proof scripts and
460 documented names.

## Supported constants, strict covariance curvature and duplicate-score obstruction

Generic strict variance positivity iff absence of any supported
constant follows from the existing zero variance and strict
variance equivalences. Fixed-basis covariance null and strict
quadratic-form iff results delegate to the existing matrix
variance bridge. Duplicate-basis non-positive-definiteness
uses the previously proved [1;-1] quadratic null witness,
Stdlib.List.repeat and Lra. No covariance summation or
new rank/determinant implementation is introduced.
Earlier inventory: 406 claims, 409 scripts, 464 declarations.

## Matrix-level affine covariance transformations

The cross-covariance affine theorem is now a direct entrywise
application of the previously checked covariance_of_affine_scores,
using Stdlib.List.map_map and map_ext rather than custom recursion.
The fixed-basis covariance specialization reuses the cross-matrix
theorem and the already defined list-of-list matrix representation.
This establishes the exact slope-product/slope-square behavior
for unit-mass finite weights without constructing a new
linear-algebra library, or assuming positivity for signed weights.
The latest audit covers 408 claims, 411 proof scripts and
466 fully documented named declarations.

## Finite-score affine dependence and covariance null witnesses

The original repeated-score null proof is a single use of the
new sampled affine-dependence theorem, using the fixed-basis
variance identity, variance_extensional_on_samples and existing
constant-score variance. Positive-support affine dependency
uses the previously checked supported-constant/null iff.
Its obstruction to positive definiteness reuses the same
nonzero vector and Stdlib.List.repeat. No new list fold,
custom rank, eigenvalue or determinant algorithm was added.
The audited totals are 411 claims, 414 scripts, 469 declarations.

## Finite-coordinate characterization of covariance nullity

A compatible coefficient vector has zero covariance-matrix
quadratic form iff its composite score is uncorrelated with
every finitely listed basis score. The proof uses
covariance_of_general_weighted_second_unconditional,
basis_of_combine, Stdlib.List.in_map and the existing
FiniteSum.finite_sum_ext_in/finite_sum_zero, rather than
building a matrix kernel API. Existing finite PSD plus
Stdlib.Rle_dec/Lra yields the corresponding strict
positivity iff, and hence the positive-definite iff
criterion over all nonzero compatible coefficient lists.
Current audit: 414 claims, 417 scripts, 472 named declarations.

## Finite covariance row-dot and exact nullspace equivalences

The existing covariance_of_general_weighted_second_unconditional
and covariance_row_as_vector_dot identify covariance with a
weighted-basis score with the coefficient dot product of a
covariance row; list projections use Stdlib.List.map_map
and the established List.combine lemmas. The actual
list-of-lists covariance matrix has zero quadratic form iff
its coefficient vector has zero dot product against every row,
using Stdlib.List.in_map_iff and the previously checked
basis-coordinate nullity theorem. No custom nullspace basis,
matrix multiply, determinant or rank algorithm was introduced.
The audit now covers 416 claims, 419 scripts, 474 declarations.

## Rowwise strict covariance positivity and precise core comments

The row-dot nullity equivalence combines with finite covariance
positive semidefiniteness to characterize strict quadratic
positivity and, consequently, positive definiteness by the
absence of nonzero compatible row-dot kernel vectors. No
additional matrix multiplication, rank, determinant or list
fold is constructed. Six foundational matrix and list-bridge
declarations were documented afresh with their exact list
truncation, finite weight, dimensionality, and reuse conditions:
vector_dot, basis_covariance_matrix, basis_cross_covariance_matrix,
covariance_row_as_vector_dot, basis_of_combine, and the
fixed-basis PSD theorem. Inventory: 418 public claims, 421
proof scripts and 476 fully documented declarations.

## General covariance null-witness obstruction and reuse

Any compatible nonzero covariance quadratic-null vector prevents
positive definiteness by direct Lra, irrespective of the sign or
normalization of sampled weights. A second theorem uses the
existing positive-support constant-score iff nullity to give
the corresponding arbitrary-basis degeneracy criterion under
normalized nonnegative weights. The duplicate-score and
affine-dependent pair obstructions now reuse this generic
null-witness lemma, rather than repeating their own strict
positivity contradictions. No new finite summation, matrix
rank, determinant or nullspace algorithm is introduced.
Current audited totals: 420 claims, 423 scripts and
478 documented declarations.

## Supported constants and the covariance row-dot kernel

An exact finite support-constant composite score implies zero
dot product against each list-of-lists covariance matrix row,
using the existing quadratic-null iff supported-constant and
quadratic-null iff row-kernel theorems. In turn, a compatible
nonzero row-kernel vector rules out strict positive definiteness
via the reusable general quadratic-null obstruction. Neither
result implements a matrix multiply, nullspace basis, rank,
determinant or new list traversal. Current inventory:
422 claims, 425 scripts and 480 documented declarations.

## Covariance row-nullity iff support constancy and core documentation audit

A checked two-way bridge now identifies zero dot product
against every row of the finite covariance matrix with
constant positive-weight composite-score support. The finite
covariance matrix is positive definite exactly when no
nonzero compatible coefficient vector has this property.
Both results reuse prior iff theorems, without introducing
matrix multiplication, rank, determinants, index loops or
new proof axioms. Detailed declaration comments were also
revised for matrix_bilinear_form, matrix_quadratic_form,
weighted_basis_sum, fixed_basis_weighted_variance_identity
and zero_variance_is_constant_on_positive_mass, recording
their exact representations, length and weight assumptions,
and dependency reuse. Totals: 424 claims, 427 scripts,
482 documented declarations.

## Deliberately retained project-specific definitions

- **Four-cell admissions model:** `TwoEventModel` defines the actual
  report-specific event representation and its explicit normalized weights.
  Replacing it with a probability library would require an equivalence proof,
  not just a change of syntax.
- **Finite weighted outcomes:** `expect`, `covariance`, and `variance`
  are mathematical definitions of the report's explicit finite model.
  They are not alternate implementations of a generic library algorithm.
- **Unordered covariance pairs:** `unordered_covariance_sum` uses a
  suffix-dependent traversal so each pair is counted once. Do not replace it
  with a naïve `fold_right` over the original list: that would lose the
  suffix and change the meaning. A future indexed finite-sum implementation
  should first prove equality with this definition.
- **Matrix entry indexing:** `basis_covariance_matrix` is a list-of-lists
  representation. Replacing it by a finite-indexed matrix library requires a
  dimension-preserving translation and a checked quadratic-form equivalence.
- **Cauchy–Schwarz:** the finite proof is currently derived from a
  variance-polynomial argument. Replacing it with a general inner-product
  library requires showing that this finite weighted space satisfies that
  library's hypotheses; a lemma with the same name is insufficient.


## Finite conditional-independence reuse extension

`FiniteUnion.finite_conditional_independent` is an explicit conjunction:
positive finite conditioning-event mass and product factorization of two
conditional event masses. It is not a new probability calculation.
The ten companion theorems derive joint-event commutativity,
conditional-independence symmetry, support extensionality for either target
event and the conditioning event, weighted sample permutation invariance,
conditional event partition, and complement closure for one or both targets. The proofs reuse the pre-existing
`finite_conditional_prob_event_ext_on_samples`,
`finite_conditional_prob_conditioning_ext_on_samples`,
`finite_prob_event_ext_on_samples`, `Stdlib.Bool.andb_comm` and
`Stdlib.Reals.Rmult_comm`. No second `finite_sum`, case split over
sample lists, finite-dimensional matrix algebra or external library dependency
is added.

The explicit `0 < finite_prob ... given` guard rejects undefined
zero-conditioning interpretations. Nonnegative sampled weights are not needed
for the symmetry and extensionality *algebra*, but are needed to interpret
the quotient as a bona fide conditional probability. The formalized interface
does not yet give generic eventwise conditional cross-product criteria, general conditional
random-variable independence, or continuous disintegration.

## Generic independence to four-cell model bridge

The `FiniteUnion` interface reuses `finite_prob_true` and sample-event
extensionality to show that a unit-weight-mass sample conditioned on true
reduces to the ordinary finite event mass. A companion theorem rewrites
the generic positive-conditioning independence predicate into the
joint-equals-product-of-marginals equation.

`FourCellBridge` reuses its previously checked normalizing mass and
two marginals, together with `four_cell_intersection_mass`, to specialize
that generic theorem without re-enumerating the Boolean product.
`Admissions.binary_independence_criterion` supplies the final equivalence
to `joint * neither = only_A * only_B`.
The four-cell weights are nonnegative and sum to one by record
construction; no distributional independence or Gaussian conclusion
is added, and the pinned Rocq Stdlib is sufficient.

## Certain and impossible conditional targets

Four degenerate but useful baseline independence laws in `FiniteUnion`
prove that the always-true and always-false target events factor with
every other target when conditioning mass is positive. They reuse
`finite_conditional_prob_true`, `finite_conditional_prob_false`,
`finite_conditional_prob_event_ext_on_samples` and the previously checked
`finite_conditional_independent_symmetric` rather than implementing
another finite summation, Boolean enumeration, or quotient. No
normalization or nonnegative-weight assumption is introduced into
these algebraic claims; both conditions are relevant when interpreting
arbitrary finite weights as actual probabilities.

## Normalized independence and zero-indicator-covariance bridges

`FiniteBridge.finite_normalized_conditional_independence_iff_zero_indicator_covariance`
derives equivalence between finite conditional independence given
the certain event and zero indicator covariance. It **only composes**
the existing normalized true-conditioning product criterion and
indicator covariance/product identity; there is no new finite
integration, indicator-product calculation, or covariance expansion.
`FourCellBridge.four_cell_generic_independence_iff_zero_indicator_covariance`
then instantiates this theorem with the existing four-cell weight
normalization. These exact finite results do not equate zero
covariance with independence of arbitrary real-valued scores.

## Cross-product criterion for conditioned finite events

A denominator-free cross-product characterization of
`finite_conditional_independent` under positive conditioning mass
follows by multiplying the existing conditional quotient equation
through by the square of its nonzero denominator. The proof uses only
`Stdlib.Reals` field cancellation and `Lra`. It neither duplicates
the shared `FiniteSum` fold nor creates a separate conditional event
representation. The criterion can be reused in future filtered
four-cell independence statements without expanding conditional
fractions or introducing an external probability library.

## Conditioning-event identity and union formula

The generic conditional independence predicate has two new
conditioning-event identity instances, using the previously checked
`finite_conditional_prob_event_ext_on_conditioned_samples`,
`finite_conditional_prob_self` and independence symmetry.
The independent-union theorem delegates to
`finite_conditional_prob_inclusion_exclusion` and substitutes
the established product factorization with Stdlib.Lra.
None of these proofs introduces another event summation, manual
union recursion, quotient implementation or external library.

## Explicit three-target conditional factorization

The `finite_conditional_three_event_product` theorem combines
two existing conditional-independence factorization equations
after a `Stdlib.Bool.andb_assoc` rewrite through the checked
conditional target-extensionality API. The second premise
requires independence of A∩B from C, rather than only C's
pairwise independence from A and B. This distinction prevents
accidentally elevating pairwise independence to mutual
independence. No new multievent operator, real-sum recursion,
measure-theory dependency or conditional quotient is added.

## Conditional-support extensionality refactoring

Two theorems prove invariance of conditional independence under
modification of either target **outside the selected conditioning
support**, using the already checked conditional-mass extensionality
theorem and symmetry. The earlier target extensionality proof is
refactored into a direct corollary, removing duplicated expansion
of the independence predicate. The complementary-conditioning-event
identity follows by applying this theorem to the already proved
impossible-event independence case. Existing theorem types remain
unchanged. No new recursion, quotient, axiom or external dependency
is introduced.

## Selected-sample equivalence of generic conditional independence

`FiniteUnion.finite_conditional_prob_as_filtered_true` uses the
already established filter and finite event-mass interfaces to
identify conditional probability with certain-event conditioning
on the restricted list. The corresponding
`finite_conditional_independent_iff_filtered_true` follows by
rewriting the positivity guard and joint/marginal conditional
masses without introducing a replacement probability operator.
The filtered cross-product result delegates to the existing
unfiltered cross-product criterion and `Stdlib.List.filter`
bridges. These exact structural results keep sample repetitions
and total-mass semantics explicit.

## General finite conjunction and product factorization

A finite intersection of arbitrary Boolean event lists is represented
with maintained `Stdlib.List.forallb`. The only new recursive
construct is the project-specific **logical assumption list**
`finite_conditional_prefix_independent`, which makes explicit
the stronger-than-pairwise premise that each event is independent,
given the same selector, from the conjunction of the remaining
events. The finite product itself uses Stdlib `map` and
`fold_right Rmult 1` and an induction that reuses the existing
binary independence predicate and the true-event conditional
probability theorem. Both definitions and the three theorems
are fully documented. There is no additional Boolean conjunction
recursion or probability integral implementation.

## Finite union and intersection bounds under positive conditioning

The general finite event-list union bound now applies to
a conditioning-selected sample through the checked
`finite_conditional_prob_filtered` representation.
`arbitrary_union_bound` supplies the only substantive
real inequality, while the standard reciprocal positivity
lemma handles division. The lower union bound reuses
`event_member_implies_union` and conditional event
monotonicity, and the upper intersection bound reuses
`Stdlib.List.forallb_forall` rather than a new Boolean
induction. The assumptions of nonnegative weights and a
strictly positive conditioning mass remain explicit.

## Library-based conditional union-bound normalization

The final conditional Boole bound is stated as an inequality
between a conditional union mass and the sum of its conditional
member masses. Its auxiliary denominator-factorization equality
uses the shared `FiniteSum.finite_sum_scale` and
`FiniteSum.finite_sum_ext` library-reuse bridges; no new
`fold_right` implementation or independent conditional
integration structure is introduced. The inequality itself is
just the prior selected-sample union bound rewritten in this
standard marginal-sum representation.

## Rescaling invariance by the existing finite-sum API

The event-mass scaling lemma delegates to
`FiniteSum.finite_sum_scale` and `finite_sum_ext`.
Conditional probabilities and the generic conditional
independence predicate inherit invariance under a
single strictly positive global scale by real-field
cancellation and the standard `nra` positivity
tactic. The side condition is essential: neither
nonuniform nor nonpositive reweightings have been
proved to preserve independence. All three
declarations carry explicit comments and no
alternative summation implementation is introduced.

## Membership and permutation reasoning for finite intersections

`all_events_membership_ext` identifies the pointwise
conjunction built by Stdlib.List.forallb using only the
existing Stdlib.List.forallb_forall equivalence. The
permutation consequence uses the maintained
`Stdlib.Sorting.Permutation` membership transport rather
than a new permutation or list-fold implementation.
Conditional intersection invariance then delegates to
`finite_conditional_prob_event_ext_on_samples`.
Monotonicity when extra events are required delegates
to the existing conditional probability monotonicity
theorem; the only Boolean step is a standard
`forallb_forall` membership argument. All weight
and denominator guards are explicit.

## Checked normalized filtered-sample covariance interpretation

The shared finite-sum scale lemma and the previously
verified `finite_prob_as_filtered_mass` give unit total
weight for `conditioned_weights` on a Boolean-filtered
sample when conditioning mass is strictly positive.
Existing Stdlib filter membership and nonnegative
multiplication lemmas establish retained-weight
nonnegativity. The new general conditional
independence/zero-indicator-covariance theorem only
composes the project’s finite filtered-true iff,
positive scaling iff, and normalized finite indicator
covariance equivalence. It neither redefines covariance
nor implements a second probability sum or
continuous conditional-expectation operator.

## Conditional event probability, Bernoulli variance and covariance residual

`FiniteBridge.finite_conditioned_event_mass` uses the
common finite probability scaling theorem and filtered
event-mass bridge to identify the exact event masses in
the normalized conditional sample. The two downstream
moment statements invoke the established Boolean-indicator
variance and covariance identities and replace event
masses with the conditional masses via this reusable
bridge. No second moment calculation, list fold,
independence axiom or alternate covariance implementation
is introduced.

## Reused Bernoulli variance theorems under positive conditioning

The normalized conditional sample introduced in
`FiniteBridge` supports direct instantiation of the
previously proved indicator-variance upper bound,
zero-variance/extreme-mass iff, and complement
invariance of Bernoulli indicator variance. The
last theorem obtains its unit-mass hypothesis
definitionally from `conditioned_weights_total_mass_one`
rather than reproving any finite expectation or
variance identity. Each new theorem is fully
documented, with positive conditioning mass and
statistical nonnegativity distinguished.

## Reusable total-mass bridge and conditional complement covariance

`conditioned_weights_moment_total_mass_one` exposes
the already checked filtered-sample normalization
directly in `FiniteMoments.total_mass` via
definitional equality with the common finite sum.
The conditional complement-variance proof was
refactored to invoke it. Three new conditional
Boolean-indicator covariance complement laws
then reuse the existing normalization-dependent
covariance theorems, with positive original
conditioning mass stated explicitly. No
new covariance sum, normalizing recursion,
event algebra or general measure-theory axiom
is introduced.

## Conditional indicator Cauchy–Schwarz and degenerate independence

`finite_conditioned_indicator_cauchy_schwarz_squared`
delegates to FiniteMoments' existing checked
finite-score Cauchy–Schwarz inequality and uses
the reusable unit-mass and nonnegative filtered-weight
bridges. The zero-variance covariance law likewise
reuses FiniteMoments' dedicated implication. Two
degenerate-event conditional-independence corollaries
then compose the previously proved extreme-mass
variance equivalence, covariance-to-independence
iff and symmetry, with all hypotheses explicit.
No duplicate discriminant proof, quadratic sum,
independence axiom or numerical approximation
is introduced.

## Sharp finite conditional covariance bounds from standard finite moments

`finite_conditioned_indicator_variance_nonnegative`
reuses `FiniteMoments.variance_nonnegative` after
normalization and nonnegative selected-weight checks.
The conditional indicator squared Cauchy–Schwarz bound
and existing universal Bernoulli variance upper bound
then establish the sharp algebraic 1/16 covariance
square bound; Rocq `nra` yields the signed ±1/4
covariance interval. No new probability sum or
independent covariance algebra is introduced, and
all assumptions needed for statistical semantics
are explicit.

## Source-indexed covariance entries before a matrix library migration

`basis_covariance_matrix_as_cross` exposes the square
representation as the rectangular cross-covariance
constructor with identical score bases.
The two basis-append laws are proved using Stdlib
`map_app`, `combine` and structural simplification.
The option-indexed entry lemma uses `nth_error_map`
to prove that a cell selected from the list of lists
is exactly the covariance of the corresponding
two basis scores. Combining the entry lemma with
`covariance_symmetric` establishes the two
corresponding entries of swapped score lists are
equal. This preserves bounds explicitly and
avoids building a bespoke matrix-indexing API.
Future conversion to an indexed matrix library must
retain these exact entry and dimension invariants
before any rank, nullspace or determinant claims.

## Bounds-aware square matrix entries and dimensional row preservation

Two further `nth_error` theorems for the rectangular
basis covariance matrix transport source-basis index
success into an exact covariance row and its length,
using maintained Stdlib `nth_error_map` and
`length_map`. Square basis covariance then inherits
entry fidelity and symmetry by the checked
equal-left-right cross-matrix specialization.
All successful index values are explicit
`Some` witnesses; future finite-indexed vectors
can use these facts without introducing an
out-of-range default or losing the matrix
column dimension.

## Bounded matrix indexing with the maintained Rocq vector library

The dimension-safe `indexed_basis_cross_covariance_matrix`
uses `Stdlib.Vectors.Fin.t` for row and column
indices and `Stdlib.Vectors.Vector.of_list/nth`
to select source scores. A new generic conversion
lemma is proved from maintained `VectorSpec`
`to_list_nth_order`/`to_list_of_list_opp`,
`Fin.of_nat_to_nat_inv` and
`List.nth_error_nth'`; this is a proof of semantic
agreement with the existing list rather than an
independent list-index implementation.
The indexed matrix's correspondence to the old
rectangular covariance list is then obtained
cellwise from the previous checked nth_error
entry theorem, and its swap law from existing
covariance symmetry. The library currently
proves only entry and dimension fidelity;
rank, determinants and eigenstructure have
not been formalized for this representation.

## Total finite-indexed covariance source correspondence

The `indexed_basis_cross_covariance_matrix_entry_total`
theorem upgrades conditional entry equality to an
existential witness of a successful source list row
and matching column cell for **every** bounded
row/column index pair. This constructs the original
Stdlib.List.map covariance row via the checked
vector/list index lemma and previously established
row- and cell-selection facts. The indexed square
matrix symmetry law is a direct specialization
of the rectangular swap theorem. No default-value
index fallback, new recursion, independent scalar
covariance or matrix rank claim is introduced.

## Dependencies to evaluate before deeper migration

1. Rocq **standard library** is the baseline for real-number algebra,
   list operations, Booleans and proof tactics.
2. **MathComp** (including its finite algebra/matrix libraries) is a
   candidate for fixed-dimensional covariance-matrix reasoning. Its scalar
   hierarchy and matrix indexing must be reconciled with the current
   `Stdlib.Reals.R` formulation.
3. **Coquelicot** and **MathComp Analysis** are candidates for a later
   transition to abstract/continuous measures and analytic limit
   theorems. This needs a separate dependency assessment and explicit
   interpretation lemmas; neither is automatically a drop-in replacement.
4. Do not import large libraries just to reimplement `map`, `fold_right`,
   `existsb`, field arithmetic or elementary square roots.

## Refactoring verification contract

- Preserve the **types of existing named theorems** and the finite-model
  normalization/nonnegativity hypotheses; a compiling *weaker* theorem
  is not a satisfactory replacement.
- Reject `Admitted`, added project axioms and unproved coercions.
- Compile every module using the pinned Rocq 9.2 toolchain.
- Run existing Python/Deal regression and source-pinned SPARK evidence audits.
- Update the declaration count from actual `Lemma`, `Theorem` and `Example`
  declarations, not by adding previous totals blindly: removing a redundant
  auxiliary lemma can reduce the count while preserving substantive coverage.
- Leave the root README and historical Ada/SPARK evidence unchanged, because
  the historical audits pin their source hashes.
- Do not merge the existing pull request without an explicit request.

## Indexed row and diagonal reuse

The `Stdlib.Vectors.Fin/Vector` bridge now exposes a total bounded row
lookup without implementing a new row/index algorithm:
`indexed_basis_cross_covariance_matrix_row` composes the existing
`vector_of_list_nth_error` with the existing rectangular list-row
selection theorem. The companion row-length result reuses the established
`basis_cross_covariance_matrix_nth_error_row_length` lemma.
The total indexed-cell theorem is refactored to use that row witness.

The indexed diagonal is *definitionally* the variance of the selected
score, and conditional nonnegativity is a direct application of
`variance_nonnegative`. Both use the project's existing algebra and
standard library, not a parallel custom matrix representation.
Rank-nullity and spectral properties still require separate checked
connections to an established finite-dimensional linear algebra library.

## Indexed covariance inequalities and support-nullity reuse

The indexed covariance Cauchy-Schwarz inequality is a specialization of
the existing `finite_covariance_cauchy_schwarz_squared`, not a separate
matrix inequality implementation. The exact positive-support constant
characterization and its zero-row consequence reuse
`variance_zero_iff_exists_constant_on_positive_weight_support`
and `zero_variance_implies_zero_covariance_first`. Each statement
retains explicit mass-one and nonnegative-weight premises.
The next rank/nullspace work should connect to an established
finite-dimensional linear-algebra library rather than duplicating
generic elimination, spectral or determinant algorithms.

## Rectangular nullity and two-coordinate covariance minors

A general left/right covariance zero-variance row theorem uses the
existing scalar `zero_variance_implies_zero_covariance_first`. Its
column counterpart reuses indexed symmetry instead of separately
reproving the scalar result. The former square zero-row proof now
delegates to that general rectangular theorem. Indexed zero-row
and zero-column iff criteria reuse the exact diagonal identities;
the two-coordinate minor bound is a direct consequence of the
earlier indexed Cauchy-Schwarz inequality and `Stdlib.Lra`.
No custom determinant or rank algorithm has been introduced.

## Zero covariance rows and columns as supported-constant scores

The total `Fin.t`-indexed covariance symmetry theorem supplies a
zero-row iff zero-column equivalence without probability hypotheses.
Under normalized nonnegative finite weights, zero row or column iff
support-constant score follows solely from the existing diagonal
variance equivalence and positive-weight-support theorem, using
`tauto`. These are exact logical compositions, not fresh
finite-sample inductions, linear algebra implementations or new
probability axioms.

## Strict coordinate positivity and nonconstant positive support

The strict diagonal criterion is derived from the existing
`variance_positive_iff_no_constant_on_positive_weight_support`.
The nonzero off-diagonal criterion reuses the scalar
`nonzero_covariance_implies_positive_variances`, and its
nonconstant-support consequence composes the two checked theorems.
These do not imply positive definiteness or an abstract matrix
rank theorem; they preserve the original finite weighted semantics.

## Rectangular variance bounds and inherited square proof

The new rectangular `Fin.t`-indexed covariance lemmas reuse
`finite_covariance_cauchy_schwarz_squared`,
`nonzero_covariance_implies_positive_variances`, and
`variance_positive_iff_no_constant_on_positive_weight_support`
directly. The square Cauchy-Schwarz theorem now depends on the
rectangular indexed bound rather than proving the same scalar
fact again. The change is a strict abstraction improvement, with
no new recursion, matrix operator, hypothesis or external library.

## Indexed two-coordinate quadratic and checked variance reuse

The small `indexed_basis_covariance_two_coordinate_form` is
composed only of existing `Fin.t`-bounded covariance cells.
Its exact two-score variance interpretation reuses
`variance_of_two_weighted_scores`; nonnegativity, zero,
and strict positivity reuse the established scalar
`variance_nonnegative`, positive-support zero-variance iff,
and strict-variance iff theorems. No custom matrix engine,
determinant/eigenvalue computation or extra axioms are used.
Extending to general rank/nullspace algorithms should integrate
maintained finite-dimensional linear algebra libraries.

## Indexed two-coordinate to list-matrix representation bridge

The new indexed quadratic/list matrix theorem reuses the existing
`covariance_matrix_quadratic_form_is_variance_unconditional`
and `variance_extensional` results, rather than implementing
fresh matrix traversal or finite summation. This is a direct
connection to the established list matrix framework and prepares
further PSD refactoring. It does not assert arbitrary matrix rank.

## Refactoring two-coordinate positivity to maintained covariance PSD

The indexed quadratic nonnegativity proof now delegates to the
existing all-finite-bases `fixed_basis_covariance_matrix_positive_semidefinite`
theorem. Its bridge to the list-matrix API is already checked and no
new matrix traversal, variance positivity argument, axiom or
library dependency is needed. All original side conditions remain.

## All-dimensional covariance quadratic through Stdlib vectors

An arbitrary-dimensional, exactly sized `Vector.t` of real
coefficients now drives the established finite list-matrix
quadratic. The maintained `VectorSpec.length_to_list` lemma
discharges its sole length obligation. Consequently the new
bounded coefficient theorems inherit variance equivalence,
positive semidefiniteness, positive-support constancy/nullity,
strict positivity, orthogonality to basis scores and the
zero-covariance-row-dot criterion from already checked
`fixed_basis_*` theorems, rather than adding duplicate
finite-sum induction or matrix traversal. This does not
construct a full `Fin.t` matrix multiplication engine or
calculate rank/kernel dimensions.

## Bounded coefficient orthogonality and positivity reuse

The maintained arbitrary-dimensional list covariance library
already proves zero quadratic iff covariance with every score
vanishes, strict positivity iff the basis is not entirely
orthogonal, strict positivity iff some covariance-row dot
is nonzero in the logical negation sense, and support constancy
iff zero row dots. These statements now have `Vector.t`-typed
coefficient variants that simply discharge all list lengths
using `VectorSpec.length_to_list`. Nonzero scalar covariance
also yields strict positivity via the previously checked
composite variance bridge. No custom finite sample induction,
matrix algorithm or new axiom was required.

## Bounded indexed rows and two-coordinate algebra

The existing two-coordinate quadratic form now has score/weight
swap and common-coefficient scaling proofs using indexed
covariance symmetry and Stdlib `ring`. The arbitrary-dimensional
vector coefficient nullity theorem reuses the established
list-matrix row-dot iff and the existing bounded row
correspondence; `Stdlib.List.nth_error_In` establishes row
membership without any custom traversal. Covariance with
each bounded score and positivity of a witnessed nonzero
covariance are direct instances of previously proven
all-scores results. This remains a one-way indexed-row
kernel statement, not rank-nullity or an eigenvalue algorithm.

## Complete bounded-index row coverage and nullspace equivalence

Every covariance row in the maintained list-matrix
representation now has a `Fin.t` index witness, using
`In_nth_error`, `nth_error_Some`, `length_map`,
`Fin.of_nat_lt`, `Fin.to_nat_of_nat` and the existing
indexed covariance row theorem. With the previously
proved bounded-row implication and the generic list-matrix
zero-row-dot iff, this supplies a fully bidirectional
dimension-safe row-kernel criterion. No new induction,
matrix elimination algorithm, rank computation or axiom
is introduced; the connection is exact for finite sums.

## Indexed coefficient positivity and zero-kernel equivalences

The fully bidirectional bounded-row covariance criterion
now supports three additional iff characterizations by
composing existing theorems with the standard `tauto`
tactic. A transparent `indexed_basis_covariance_positive_definite`
predicate quantifies over nonzero `Vector.t` coefficient
vectors; its support-constancy and no-nonzero-bounded-kernel
criteria are obtained pointwise from already checked indexed
quadratic iff results, without a duplicate rank algorithm,
vector zero implementation, extra axiom or added dependency.

## Typed positive definiteness through existing variance and PSD facts

New indexed positive-definiteness equivalences reuse the
existing composite-score variance identity, indexed
strict-positivity-versus-basis-orthogonality iff, and
positive-semidefinite nonnegativity with Stdlib.Lra to
exclude nonzero quadratic null directions. No determinant,
rank or matrix elimination implementation was added.
All sampled probability assumptions remain explicit.

## Constructive positive-support and bounded-row witnesses

Two new theorems derive strictly positive typed coefficient
quadratics from separated positive-weight outcome pairs and
derive whole-basis positive definiteness if all nonzero typed
directions have a pair. One explicit nonzero bounded covariance
row dot proves strict positivity, while one nonzero direction
annihilating every bounded covariance row refutes positive
definiteness. These proofs reuse the already kernel-checked
support-constancy and Fin.t matrix-row equivalences. No
additional vector algebra, finite-list induction or matrix
elimination code was introduced.

## Indexed covariance anchor and explicit degeneracy witnesses

Four proof scripts use maintained existing results to
characterize type-safe covariance nullity by pairwise
equality on positive-weight finite support and by comparison
to an arbitrary positive-support anchor. Two explicit
degeneracy witness theorems reuse the indexed
positive-definiteness iff criteria. `VectorSpec.length_to_list`
is the only vector/list conversion obligation. No duplicate
finite sums, matrix elimination or new axioms were introduced.

## Event-list duplicate idempotence from Stdlib booleans

Four finite union and intersection theorems lift the
Boolean idempotence of repeated `existsb` and `forallb`
head events to unconditional and conditional finite event
masses. The proofs rely on maintained
`finite_prob_event_ext_on_samples` and
`finite_conditional_prob_event_ext_on_samples` instead of
reimplementing finite sums or conditioning. No new
probability assumptions, external libraries or axioms
are necessary. Duplicate event-list constraints remain
distinct from additive marginal probability bounds.

## Reuse existing union membership and conjunction extensionality

The previously added duplicate-head union theorem was
recognized as redundant with `union_prob_duplicate_route`
and **replaced** by a stronger append-existing event rule.
A single membership lemma built on `Stdlib.List.in_app_iff`
avoids repeating proofs of list membership across the new
union, intersection, and conditional intersection theorems.
The duplicate-head intersection theorems themselves now
reuse `all_events_membership_ext` instead of Boolean case
splits. This is a deliberate consolidation of verified
library laws, with no additional finite probability recursion.

## Shared Boolean event membership under conditioning

`any_event_membership_ext` now centralizes the Stdlib
`existsb_exists` witness transport for list-membership-equivalent
event families. The unconditional union membership theorem delegates
to this helper. Three additional conditional union laws derive
permutation and duplicate-event invariance using existing conditional
target extensionality, `Permutation_in`, and the shared
`event_append_existing_membership_iff` rather than new enumeration
or Boolean recursion. Zero-mass conditioning is included.

## Ordinary and conditional event-family inclusion without new summation

The reusable `any_event_membership_monotone` lemma transports a
`Stdlib.List.existsb_exists` witness to a larger event family.
`finite_union_subset` and `finite_conditional_union_subset` reuse
established event-mass monotonicity, with explicit nonnegative weights
and positive conditional denominator only where needed.

## Conditional finite unions from existing list identities

Empty, singleton and append family conditional identities now delegate
to established false-event and target-extensionality lemmas, with
`any_event_append` supplying the standard `existsb_app` reduction.
No new enumeration or real-arithmetic normalization is introduced;
the identities include signed weights and zero conditioning mass as
algebraic quotient expressions only.

## Conditioned conjunction via maintained forallb

The empty and head-tail conjunction laws now reduce the shared
`all_events` definition through `Stdlib.List.forallb` and lift
its Boolean semantics with the already-proved conditional-event
extensionality theorem. The empty case explicitly uses positive
conditioning mass and `finite_conditional_prob_true`.
No new factorization, matrix algebra or fresh Boolean recursion occurs.

## Appended event lists reuse maintained list membership

Two append-family monotonicity corollaries rely only on
`Stdlib.List.in_or_app`, `finite_union_subset` and
`finite_conditional_union_subset`. They make nonnegative weights
and positive conditioning mass explicit, without fresh enumeration,
custom sums, independence or unproved probabilistic assumptions.

## Two-sided event-family append order via standard membership

Four append-order results use `Stdlib.List.in_or_app` and the
checked union/conjunction family-subset theorems. Ordinary union
monotonicity requires nonnegative sample weights; conditional union
and intersection bounds also require strictly positive conditioner
mass. Every proof avoids new `existsb` or `forallb` inductions
and remains inside finite weighted Boolean-event semantics.

## Consolidated forallb witness transport for conjunction order

`all_events_membership_antitone` factors a repeated two-way
`Stdlib.List.forallb_forall` argument into one documented helper.
The conditional conjunction subset theorem delegates to it, while a
new unconditional finite-mass subset theorem uses the maintained
generic event-mass monotonicity. Ordinary left/right append
corollaries reuse standard `in_or_app`. This refactor reduces
duplication without changing finite weighted-event semantics.

## Reused forallb_app semantics for finite conjunction families

A shared `all_events_append` helper delegates directly to
`Stdlib.List.forallb_app`. The conditional conjunction-append
theorem now uses this helper, and the new unconditional counterpart
reuses finite event-mass extensionality rather than unfolding the
weighted sum. Empty/singleton mass identities reuse established
`finite_prob_true` and the standard singleton `forallb`
computation. No new foundation or custom list induction is required.

## Conjunction transport under existing extensionality and permutation laws

Ordinary finite-mass head/tail, membership-set and permutation
identities now reuse `Stdlib.List.forallb`,
`Stdlib.Sorting.Permutation`, `all_events_membership_ext`
and `finite_prob_event_ext_on_samples`. A marginal upper bound
is reduced to the existing singleton and event-family inclusion
inequalities. No custom permutation induction, finite event sum,
probability normalization or independence assumption is introduced.

## Intersection versus union order by already checked bounds

Both finite conjunction-versus-union inequalities are obtained
by chaining the respective intersection-to-member and member-to-union
results with `Stdlib.Reals.Rle_trans`. The conditional version
retains the positive-conditioner premise and both versions require
a named member witness and nonnegative sampled weights. Reuse of
existing lemmas avoids a fresh sum induction, custom Boolean event
algebra or hidden independence assumptions.

## Two-event inclusion-exclusion via shared Bool/List reductions

The `all_events_pair` helper uses `Stdlib.List.forallb` and the
Boolean true identity to normalize a two-event family conjunction.
Both unconditional and conditional family inclusion-exclusion
statements reuse the existing mass/conditional-event extensionality
theorems and the already verified generic inclusion-exclusion
equalities. No second indicator algebra proof, custom list fold or
unproved independence premise was added.

## Conditional family independence via maintained pair lemmas

The two-element event-family intersection product and conditional
union sum-minus-product law reuse the existing
`finite_conditional_independent` predicate,
`finite_conditional_independent_union_formula`,
`all_events_pair` and standard `existsb`/Boolean identities.
Both conclusions are transported through the maintained conditional
target-event extensionality theorem; no duplicate indicator arithmetic,
new list recursion or hidden independence is added.

## Centralized two-element event-family Boolean identities

`any_event_pair` now supplies the maintained `existsb`/Boolean
OR identity for two-event lists, alongside `all_events_pair`
for `forallb`/Boolean AND. The conditional family
inclusion-exclusion and independent-union proofs delegate to that
lemma under existing conditional event extensionality, replacing
repeated local Boolean simplification without changing their types.

## Strict inequalities for generic finite sums

The shared finite-sum module now packages the nonnegative zero
criterion as a two-way equivalence and derives positive mass from
a positive listed contribution. The resulting strict monotonicity
lemma is obtained by applying positivity to the difference `g-f`
and rewriting with `finite_sum_sub`. The proofs reuse
`finite_sum_nonnegative_zero`, `finite_sum_ext_in`,
`finite_sum_zero`, `finite_sum_nonnegative`,
`Stdlib.Reals.Rle_dec` and `Stdlib.Lra`.
No new list induction, fold, separate strict-sum algorithm, or
additional axiom is needed. Nonnegativity of summands is essential
to the strict positivity argument; pointwise domination is essential
to strict monotonicity, with one witness of strict domination.

## Event support lemmas reuse generic strict sums

Two existing event-mass theorem bodies are refactored without changing
their propositions: the zero-mass support equivalence now uses
`FiniteSum.finite_sum_nonnegative_zero_iff`, while the positive-mass
witness implication uses `FiniteSum.finite_sum_positive_of_positive_member`.
The Boolean indicators still need only their standard two-case reduction
and the established nonnegative-product lemma. This removes duplicated
zero-sum and strict-member-bound reasoning from `FiniteUnion.v`
without assuming normalized weights or independence. All existing
event and sample semantics are preserved.

## Conditional-event positivity via positive-support and quotient lemmas

Positive conditional mass is derived using the maintained event
positive-support theorem for the Boolean conjunction, followed by
`Stdlib.Reals.Rdiv_lt_0_compat`. A second theorem derives the
positive conditioner mass from the same positive-weight witness,
rather than introducing a separate positivity computation. These
proofs reuse the existing `finite_prob` and `finite_conditional_prob`
interfaces, and add no new summation, event structure, conditional
distribution implementation, axiom or independence assumption.
Nonnegative weights, actual sample membership and two true event
predicates remain explicit hypotheses.

## Strict positive-support event comparisons from shared finite sums

Instead of introducing a custom induction over events or outcomes,
`finite_prob_event_strict_monotone` reuses
`FiniteSum.finite_sum_strict_monotone_at_member` for weighted Boolean
indicators. The two stricter sample-filter theorems transport that
inequality through `finite_prob_on_filtered_samples` and
`union_prob`. These are exact finite-list inequalities, preserving
duplicate occurrences, explicitly nonnegative weights, and positive
support witnesses. The library audit deliberately does not treat
them as empirical estimates or continuous-probability results.

## Strict conditional target inclusion and interior mass

Strict positive-weight event inclusion is lifted to fixed
positive-mass conditioning by `Stdlib.Reals.Rmult_lt_compat_r`
and `Rinv_0_lt_compat`. A pair of positive selected witnesses,
one for a target and one for its complement, gives strict interior
conditional mass using the prior `finite_conditional_prob_complement`
and conditional witness theorem. The source reuses the established
Boolean conjunction and real-quotient semantics without defining a
new conditional distribution or asserting population inference.

## Strict event-family append laws use standard Boolean folds

The strict unconditional and conditional append theorems reduce
directly to already checked strict event-mass and conditional
monotonicity. The only event-family transformation required is the
maintained `any_event_append` theorem based on
`Stdlib.List.existsb_app`. A fresh, positively weighted listed
outcome makes the comparison strict. No new event-recursive code,
membership search, probability model, or independence assumption
is necessary; the predicates retain finite multiset semantics.

## Hierarchical three-event conditional factorization

The maintained event-family `all_events` is still only
`Stdlib.List.forallb`; `all_events_triple` expands a three-element
list and uses `Stdlib.Bool.andb_assoc` rather than adding recursion
or a new event conjunction operator. The corresponding conditional
product result delegates to the existing two-event product theorem
and conditional target-extensionality. The additional
independence premise concerns the *conjunction* of the first two
events versus the third, so the proof does **not** conflate
pairwise independence with mutual independence.

## Nonempty chain positivity and family factorization reuse

The maintained arbitrary-event `finite_conditional_all_events_product`
already uses `Stdlib.List.map`/`fold_right`, so no replacement product
operator or induction is appropriate. The new nonempty-family corollary
simply extracts the positive denominator from its first existing
independence conjunct, then applies the checked arbitrary-list theorem.
The three-event-family wrapper now invokes the earlier general
`finite_conditional_three_event_product` rather than repeating
the same factorization rewrites.

## Complement-chain finite union formula from verified general laws

The standard `Stdlib.List.map`, `forallb` and `existsb`
represent complement families, intersections and unions; a
short De Morgan bridge uses `Stdlib.Bool.negb_orb`.
The arbitrary conditional union product delegates to the
already kernel-checked arbitrary-list conditional intersection
product theorem, `Stdlib.List.map_map` and `map_ext_in`,
plus the existing complement-sum identity. There is no new
probability recursion, custom real product, independent-family
axiom or assumption that pairwise independence implies mutual
independence. A nonempty complement chain provides its own
positive denominator through the previously checked projection.

## Union-complement partition reuse instead of repeated event algebra

The verified finite De Morgan identity is transported through the
already checked `finite_prob_event_ext_on_samples` and
`finite_conditional_prob_event_ext_on_samples` interfaces.
`finite_union_complement_partition` and its conditional
counterpart use the maintained complement-sum theorems, not new
set partitions or sum induction. The general conditional
union-product theorem now invokes the conditional partition
lemma directly, removing duplicate De Morgan transport
from its proof script while retaining all side conditions.

## Finite union support and zero-mass equivalence

The existing `finite_prob_zero_iff_no_positive_mass_support`
and `finite_prob_positive_of_positive_support` provide all
real-weight support reasoning. Their union counterparts are
direct aliases, while the characterization by member-event
zero masses uses `Stdlib.List.existsb_exists` for the one
required event-family witness and the existing member-implies-union
theorem in the reverse direction. No new probability fold,
finite-list recursion or event enumeration is needed.
Nonnegative weights explicitly prevent signed cancellation.

## Conditional zero masses and finite union members

Strictly positive conditioning mass makes the maintained quotient
zero exactly when the joint numerator is zero; the proof uses
`Stdlib.Reals.Rmult_integral` and `Rinv_0_lt_compat`.
The existing nonnegative finite-event support iff converts the
joint zero to a supported-outcome criterion with
`Stdlib.Bool.andb_true_iff`, and
`Stdlib.List.existsb_exists` transfers it to every member of
a conditional finite union. The shared base lemmas replace
a new quotient algebra, event recursion or finite-sum induction.
No abstract conditional measure is silently inferred.

## Scope limitation

This audit covers all seven proof modules; it does **not** claim that each
proof has been rewritten, that general finite probability has been replaced
by abstract measure theory, or that the report's empirical claims have been
proved. The remaining migration is structural work requiring explicit
equivalence proofs and regression testing.
