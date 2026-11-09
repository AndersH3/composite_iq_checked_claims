# Meaningful Python Deal-contract expansion

## Contract-policy interpretation

Every named Python function in this repository is checked by
`verification/check_contract_coverage.py` for **at least five distinct
Deal decorators**, including legacy scripts. The current checker rejects
missing, structurally duplicated or insufficient decorators. It is a
*syntactic* safeguard: it does **not** establish that the contracts are
mathematically independent or that all possible properties are verified.

The new development target is **ten independently useful contracts where
the function's domain and observable results support them**. Do not meet
this target by repeating equivalent type predicates or by inventing
preconditions that invalidate legitimate legacy invocations. Coverage
of ten is an enhancement target, **not** a claim that every function
already meets ten. In particular, deliberate negative-control fixtures
and the exact source of the symbolic theorem cases are protected; the
latter is checked by Deal Solver and must not be modified without
adjusting the supported language and evidence schema.

## First ten-contract upgrades (2026-11-09)

These eight functions in the original analysis scripts now each have
**ten distinct Deal decorators**. Their additional conditions check
mathematical identities, numerical round trips, limiting cases,
monotonic or enclosing bounds, or specified edge cases:

| Original Python file | Function | Added independent checks |
|---|---|---|
| `analyses/hoeflin-ferguson/scripts/verify_calculations.py` | `variance_factor` | Zero/perfect correlation, one test, correlation lower bound, independent-test lower bound |
| Same | `mean_threshold` | Zero quantile, singleton test, perfect/zero correlation and independent-threshold lower bound |
| Same | `_positive_ratio` | Zero/identity denominator, sign preservation, numerical numerator reconstruction |
| `analyses/hoeflin-ferguson/ada/scripts/validate_results.py` | `_positive_ratio` | Zero/identity denominator, no expansion under denominator >= 1, unit bound and round trip |
| Same | `wilson` | Interval representation and mathematically meaningful zero/all-success endpoint limits |
| `analyses/towers-multiple-test-admissions/scripts/verify_calculations.py` | `probability_union` | Exact inclusion-exclusion, two marginal bounds, sum bound, disjoint-events limit |
| Same | `conditional_probability` | Exact ratio, joint reconstruction and zero/equal/certain-event limits |
| `analyses/towers-multiple-test-admissions/ada/validate_results.py` | `_open_unit_ratio` | Quotient identity, numerator upper bound, Park–Miller state bounds and numeric round trip |

## Reproducible checks and evidence boundaries

Live code is tested using `python verification/check_contract_coverage.py`,
`python -m pytest -q tests`, static lint and the symbolic acceptance
gate. The intentional negative-control fixture remains deliberately
invalid; tests must still demonstrate its rejection.

The immutable `verification/evidence/symbolic-fixture-computer10-20261105`
manifest includes a Python inventory recorded with the historical
source version. The current CI therefore checks that archived campaign
against the exact earlier passing tree at commit
`afaa2974b2272dec9ed874c1045a7f577359c860`
using `--source-root`. This prevents a changed current Python file
from being misrepresented as the source that generated an older native
proof campaign. New Deal checks are separately validated on the
*current* checkout. No new SPARK campaign is asserted.

## Second ten-contract batch: historical validation predicates

Four original CSV/numerical validation predicates now have five
additional independent success postconditions apiece:
`_valid_rows` in the Hoeflin/Ferguson verifier and
`_valid_fields_rows`, `_valid_admissions`, `_valid_grid`
in the Towers verifier. These contracts certify table shapes,
field uniqueness, numerical domains, normalized IQ transforms,
and probability/correlation ranges. They use conditional
postconditions of the form `not result or condition` so that
malformed inputs are **still rejected by returning False** rather
than being turned into precondition exceptions.

This makes **twelve original analysis functions** subject to the
ten-distinct-Deal-contract regression checks, while retaining
the project-wide five-contract floor and immutable symbolic fixtures.

## Third ten-contract batch: parsers and preserved diagnostic scope

The original Hoeflin/Ferguson Ada output validator now has
ten contracts each on `csv_rows`, `validate_calculations`,
and `validate_simulation`. Its CSV parser certifies complete,
aligned nonempty headers and no missing values; the calculation
validator certifies exact output schema and numeric error bounds;
the simulation report certifies finite observable tail entries,
complete count schemas, and explicit language preventing
Monte Carlo diagnostics from being called a mathematical proof.

The original Towers Ada result validator's `read` function
also now has ten contracts certifying complete and consistent
CSV schema. These contracts describe **successful return values**
rather than precluding intentionally malformed inputs.

There are now **sixteen legacy analysis functions** with the
ten-distinct-contract regression floor, in addition to the
existing mandatory five-contract coverage of all Python
functions. Archived evidence source hashes remain unchanged.

## Enforced ten-contract regression subset

The project-wide contract checker reports two non-gating coverage
measures: `functions_at_target` and `functions_below_target`
for `TARGET_CONTRACTS = 10`. These make the gap explicit without
diluting the five-contract minimum, changing archived evidence
inventories or falsely claiming every function is at ten.

`tests/test_contract_coverage.py` additionally enforces the ten
**distinct**-contract floor on the sixteen upgraded historical
functions listed above. Their stronger postconditions are
exercised by the existing runtime and numerical property tests.
No new restrictions on previously valid arguments were added.

## Fourth ten-contract batch: Hoeflin threshold generator

The original Hoeflin/Ferguson `thresholds` generator now also
enforces ten distinct Deal decorators. Its five extra
postconditions specify the expected output row count and shape,
finite nonnegative quantile bounds, exact IQ-score conversion,
and the limiting infinite-test threshold. Empty-list guards in
two expressions accommodate Deal 4.24.6's approximation of loop
results; the preexisting `_valid_rows` result validator still
requires the full nonempty table.

Exploratory additions to the Towers `admission_rows` and
`basic_grid` postconditions triggered a third-party Deal
linter AST compilation failure. Those predicates were not kept,
rather than bypassing the static lint/negative control gate.
The underlying SciPy and NumPy numerical implementations remain
unchanged.

The enforced ten-contract set now includes **seventeen original
analysis Python functions**. The mandatory minimum remains five
per named function, with ten only where constraints are
independently meaningful and accepted by the pinned toolchain.

## Ten-contract consistency properties for the Python contract auditor

The live `verification/check_contract_coverage.py::audit_file` function
now has ten distinct Deal contracts. Its five additional return-value
conditions certify: one record per discovered named function,
the aggregate number of syntactic Deal decorators equals the sum of
per-function counts, the policy minimum is reported without
mutation, missing-contract functions are included among
under-minimum functions, and the number of duplicated-function
records never exceeds the parsed function count.

The same regression test now requires ten decorators on this
auditor, taking the explicitly enforced ten-contract target to
**18 named functions** (17 legacy analysis functions and one live
verification helper). These are *syntactic/accounting*
consistency claims, not a proof that every contract expresses an
independent semantic obligation. The fail-closed Deal lint gate
and the existing deliberately failing fixture remain intact.

## Ten-contract AST decorator recognition

`verification/check_contract_coverage.py::is_contract` now has five
additional Deal conditions discriminating bare-name and constant
expressions, named-call decorators without a Deal attribute, nested
attribute paths, and explicit direct imported Deal-attribute
recognition. The existing test for Deal import aliases now exercises
accepted and rejected AST examples, including a shadowed foreign
alias and a literal string containing decorator-looking source.
The ten-contract regression checks cover both recognition and
aggregate auditing, taking the explicit target subset to
**19 named functions** (17 historical analysis functions and
two current verification helpers).

These checks preserve the true AST-based audit's semantics and do
not treat source comments, strings, or names from other imported
modules as Deal decorators. Every Python function still has the
mandatory five distinct Deal decorators, including deliberately
failing or source-pinned cases where ten would be inappropriate.

## Ten-contract GNATprove source-location normalization

Two additional current verification functions now have ten
distinct Deal contracts: `spark_coverage.location` and
`spark_coverage.normalize_entity`. Five new conditions
preserve the exact input source filename and positive line
number, enforce the `.ads`/`.adb` source-file extension
and nonempty name, guarantee the normalized field schema,
and conserve the original entity name, SPARK status, number
of source locations and first source line.

No accepted GNATprove report schema or source-pin changed.
The regression target subset now contains **21 functions**
(17 historical analyses and 4 current verification helpers).
The unconditional five-contract minimum remains enforced on
every named Python function. Runtime property tests, static
Deal lint and source-pinned evidence verification remain
separate mandatory checks.

## Ten-contract native proof-gate accounting

`verification.proof_gate.totals_balanced` and `successful_checks`
now each have ten distinct Deal decorators. The five additional checks
on the former verify that an accepted nonnegative total bounds each
proof category and the three-category partial sum. The latter checks
clean native process status, positive proof inventory, no unproved or
justified goals, and unconditional rejection of failed process exits.
These are independently evaluated consequences of the existing
acceptance logic, not new assumptions about native SPARK proof.

The ten-contract regression subset contains **23 functions**:
17 historical analysis functions and six current verification helpers.
The five-contract minimum, historical evidence integrity, and
negative-control tests remain in force. The version-pinned symbolic
`verification/check_symbolic.py` gate now expects six independently
proved postconditions for each of these two functions instead of
silently retaining its former one-postcondition count. The deliberately
failing fixture still has the same exact three obligations. The archived
source-pinned symbolic record has only the older single postcondition per
proof-gate function. The version-aware symbolic acceptance logic permits
that historic shape **only** for the original proof-gate SHA-256 and the
historical evidence auditor additionally checks actual selected source
bytes and immutable release hashes; all live proofs require six verified
obligations each. There is no weakening of the current symbolic gate.

## Ten-contract outer-parenthesis parser

`verification.spark_contracts.unparenthesized` now has ten distinct
Deal contracts. The five additional postconditions check whitespace
normalization, source-substring preservation, the necessity of an
opening and closing parenthesis if any text was removed, and the
minimum two-character shortening when a wrapping pair is stripped.
The function still accepts unbalanced or partial top-level expressions
as before, and its original explicit malformed-outer-pair rejection
is unchanged. Regression tests distinguish true outer parentheses
from adjacent parenthesized clauses. No old SPARK evidence is modified.

The ten-contract regression target now covers **24 functions**:
17 historical analysis functions and seven current verification helpers.
Every Python function retains its mandatory five-contract minimum.

## Ten-contract Ada/SPARK explicit-clause extraction

`verification.spark_contracts.contract_entries` now has ten distinct
Deal decorators. Its five new postconditions guarantee that extracted
clauses remain dictionaries of exactly `aspect` and `clause`,
preserve source strings and known Ada aspect types, and refer only to
keys actually present in the caller's source-aspect mapping.
The existing anti-duplication and literal-Boolean-padding rejection
remain unchanged. A direct regression asserts the five expected
clauses and exact provenance in a standard Pre/Post/Global/Depends
fixture. No SPARK native evidence was modified.

The ten-contract test-enforced subset now covers **25 functions**:
17 historical analysis functions and eight current verification helpers.
The five-contract floor remains mandatory for all Python code.

## Ten-contract numeric-domain guards in original model scripts

The `_finite` utilities in the original Hoeflin/Ferguson and Towers
`scripts/verify_calculations.py` now each have ten distinct Deal
decorators. Five new postconditions separately reject Boolean inputs,
nonnumeric types, NaN, positive infinity and negative infinity,
without constraining legitimate finite numeric inputs. Regression
tests also exercise the existing oversized-integer overflow branch.
These safeguards do not constitute empirical validation of the
underlying statistical models.

The ten-contract regression subset now covers **27 functions**:
19 historical analysis functions and eight current verification
helpers. Every Python function maintains at least five contracts;
source-pinned historical native/SPARK evidence is unchanged.

## Ten-contract SPARK inventory report consistency

`verification.spark_contracts.inventory` now carries ten distinct Deal
decorators. Five additional postconditions validate that the immutable-
evidence-compatible inventory's original function, procedure,
clause, minimum and completion counts agree with its entity rows.
The separate `verification.spark_contracts.ten_contract_summary`
has ten decorators and reports staged coverage **without altering
the exact historical inventory schema**.
The original five-clause SPARK minimum and historical source hashes
remain unchanged. The dedicated `TEN_SPARK_CONTRACTS.md` explains
the native verification limitations.

The ten-contract test-enforced Python subset now covers **29 functions**:
19 historical analysis functions and ten current verification helpers.
Every Python named function still has at least five Deal contracts.

## Ten-contract source masking and native JSON object preservation

Two additional pure verification helpers reach ten Deal decorators:

- `verification.spark_contracts.masked` checks unchanged source
  length, native line count and column widths, no invented nonspace
  characters, and nonincreasing parenthesis/statement-delimiter counts.
  It preserves precise Ada source locations while excluding comments,
  string literals and character literals from the contract parser.
- `verification.spark_coverage.unique_object` checks that decoded JSON
  objects keep the original string keys, insertion order, value-object
  identity, and exact set of explicit null-valued fields. Duplicate
  keys still raise an error rather than being silently overwritten.

Regression assertions cover source offsets, quoted Ada syntax, ordered
JSON pairs and duplicate rejection. No historical evidence source hash,
stored inventory schema or negative-control expectation is modified.

The test-enforced ten-contract subset now covers **31 Python
functions** (19 original analysis functions, 12 current verification
helpers), while every named function still has at least five.

## Next upgrades

Extend the ten-contract target in small, testable batches across
legacy file/CSV validators and modern verification helpers. Preserve
the five-distinct-contract minimum until all applicable functions
have nonredundant contracts and the negative controls/symbolic gate
have suitable explicit exceptions. Never weaken native source or
evidence-hash integrity checks merely to raise the decorator count.
