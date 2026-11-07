# Rocq proof-library audit and refactoring plan

This audit covers the four Rocq modules in the Hoeflin/Ferguson and Towers formalization.
It distinguishes **library functionality that should be reused** from
**report-specific definitions that must remain explicit**.

## Confirmed standard-library substitutions

| Module | Existing library facilities | Refactoring decision |
|---|---|---|
| `Hoeflin.v` | `Stdlib.Reals`: `Rplus_le_compat_l`, `Rmult_le_compat_l`, `Rdiv_lt_0_compat`, `sqrt_pos`, `sqrt_sqrt`, `sqrt_le_1`, `sqrt_lt_1` | Use the ordered-field and square-root lemmas directly rather than duplicating their proofs. Reuse them for reporting-scale monotonicity. |
| `Admissions.v` | `Stdlib.Reals.Rplus_le_le_0_compat`, `Stdlib.Lra`, `Stdlib.Psatz`, `Stdlib.Arith.PeanoNat` | Nonnegativity of sums uses library sign lemmas. Keep the four-cell model as explicit report evidence; it is not generic probability infrastructure. |
| `FiniteUnion.v` | `Stdlib.List` / `Stdlib.Bool`: `existsb`, `existsb_exists`, `map_ext`, `map`, `fold_right` | Use library Boolean-list membership and extensionality instead of explicit list inductions. Finite integration and marginal aggregation are already list folds. |
| `FiniteMoments.v` | `Stdlib.List`: `map_ext`, `map`, `fold_right`, `combine`, `map_map`; `Stdlib.Reals` | Use standard list operators for score sums, expectations, covariance rows and matrix-vector products. Extensionality reduces to `map_ext`. |

The previous library refactoring also replaced recursive `sum_finite`,
`sum_scores`, `vector_dot`, `linear_combination`, and
`weighted_basis_sum` implementations by standard folds and
`List.combine`. Preserve the public names as thin wrappers so downstream
proof statements and report mappings do not change.

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

## Scope limitation

This audit covers all four proof modules; it does **not** claim that each
proof has been rewritten, that general finite probability has been replaced
by abstract measure theory, or that the report's empirical claims have been
proved. The remaining migration is structural work requiring explicit
equivalence proofs and regression testing.
