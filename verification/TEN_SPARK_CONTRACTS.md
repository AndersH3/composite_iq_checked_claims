# Staged ten-clause SPARK contracts — 9 November 2026

## Scope and policy

The project requires **at least five explicit behavioral/flow contract
entries** for every current SPARK function and procedure. A separate
**target of ten** applies where there are meaningful nonduplicated
properties. This target does not silently become a stronger global
acceptance precondition. `verification/spark_contracts.py` derives
`target_contracts=10`, `entities_at_target`, and
`entities_below_target` in a separate
`ten_contract_summary(inventory(...))` function. The original
`inventory` return schema is unchanged to preserve exact historical
source-bound evidence comparisons. Five new Deal postconditions on
`inventory` validate its original accounting fields, while ten Deal
decorators on the separate summary validate the staged ten-clause
counters. The CLI adds `ten_contract_target` as derived presentation
without changing the archive-sensitive inventory return value.

The checker counts top-level Pre/Post/Refined_Post conjuncts,
Contract_Cases alternatives and Global/Depends aspects. It rejects
syntactic duplicate clauses, unsupported mode pragmas, trivial Boolean
padding, absent declared subprograms and incomplete five-clause
coverage. This **structural counter does not prove semantic
independence**, soundness of the specifications, or body correctness.

## First exact-arithmetic upgrades

Source: `analyses/towers-multiple-test-admissions/ada/src/admission_core.ads`.

| Subprogram | Additional useful specification properties |
|---|---|
| `Total` | Each of four disjoint cell counts is bounded by the total; a zero total implies that all four cells are empty |
| `Union_Count` | Union count dominates each of the A-only and B-only cells and their sum; with no neither-cell, it equals total |
| `Fraction` | The rational record retains numerator <= positive denominator; zero numerator and unit-ratio edge cases preserve their meanings |
| `Complement` | Exact subtraction, strict complement bounds inside the unit interval, and the two half-scale cases |
| `Conditional` | The returned denominator remains strictly positive and exact zero/unit conditional ratios preserve their boundary cases |
| `Marginal_A` | Each A-event cell is bounded by the A marginal, with both single-cell-zero and zero-marginal consequences |
| `Marginal_B` | Each B-event cell is bounded by the B marginal, with both single-cell-zero and zero-marginal consequences |

Additional source: `analyses/hoeflin-ferguson/ada/src/hoeflin_core.ads`.

| Subprogram | Additional useful specification properties |
|---|---|
| `Variance_Numerator` | Singleton-test identity, zero/full-correlation extremes and strictly positive correlation contribution for multiple tests |

Eight operations now meet the staged ten-clause contract target.
The additional contracts describe exact integer arithmetic and
subtype-bounded records, rather than numerical or psychometric model
validity. They do not weaken any former precondition or postcondition,
modify an implementation body, or change trusted numerical boundaries.

`tests/test_spark_contracts.py` requires ten or more distinct counted
clauses for each named routine, and checks representative textual
properties. `tests/test_contract_coverage.py` enforces ten Deal
decorators on the SPARK inventory reporting function.

## Proof status, historical evidence and follow-up

The Python contract CI, static lint, source-identity audits and Rocq
kernel checks are independent of GNATprove. The GitHub workflow **does
not run the native Ada compiler or GNATprove**, and an increased SPARK
contract count is not proof that a new verification condition was
discharged. A new source-pinned native GNATprove run on the updated
Ada tree, together with regression tests of runtime CSV outputs,
must precede any claim of fully verified strengthened SPARK bodies.

Historical GNATprove campaigns remain immutable. Their source hashes,
previous proof inventories and negative controls are not revised;
they are audited only with their explicitly pinned prior source trees.
Future upgrades should proceed from the easiest exact-arithmetic
routines to bounded loops and selected numerical contracts, testing
meaningful properties rather than chasing a decorator count.
