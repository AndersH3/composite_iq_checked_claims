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

## Fourth ten-contract batch: legacy reference result generators

The original analysis programs now also enforce ten distinct Deal
contracts on `thresholds`, `admission_rows`, and `basic_grid`.
The five additional postconditions per function specify label
coverage, score-to-IQ conversion, theoretical quantile bounds,
Fréchet joint/union probability constraints, reconstruction of
the joint event from conditional rates, cutoff order, the
intersection-versus-marginal relationship, and exact reproduction
of the grid-minus-published residual.

All validators and model computations continue to use their
existing SciPy/NumPy library implementations; no duplicate
probability integral or numerical grid code was introduced.
These postconditions do not change the accepted input domains.

The enforced ten-contract set now includes **nineteen original
analysis Python functions**. The project-wide policy remains
a mandatory five contracts per named function and an optional
ten where the constraints can be justified and tested.

## Next upgrades

Extend the ten-contract target in small, testable batches across
legacy file/CSV validators and modern verification helpers. Preserve
the five-distinct-contract minimum until all applicable functions
have nonredundant contracts and the negative controls/symbolic gate
have suitable explicit exceptions. Never weaken native source or
evidence-hash integrity checks merely to raise the decorator count.
