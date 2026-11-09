# Ada/SPARK verification on computer10

The two analysis folders contain standalone Ada implementations:

- [Hoeflin/Ferguson](../analyses/hoeflin-ferguson/ada/): corrected thresholds, composite and latent-factor examples, and a Gaussian common-factor simulation.
- [Towers](../analyses/towers-multiple-test-admissions/ada/): bivariate-normal probabilities, the BASIC grid, calibrated admission cutoffs, and correlated-score simulations.

The [symbolic-check follow-up](evidence/symbolic-fixture-computer10-20261105/REPORT.md) records fresh Python checks and re-audits the unchanged 1,100 native SPARK checks from the [five-contract computer10 campaign](evidence/five-contracts-computer10-20261104/REPORT.md). No new GNATprove invocation is claimed for this Python-only fix. The native campaign retains source scope, proof results, raw `.spark` coverage, source-bound Ghost models, checked interfaces, erasure regressions and numerical comparisons. The [earlier expanded campaign](evidence/spark-expanded-computer10-20261031/REPORT.md) preserves its 209/434-check results against revision `ce0e895`; those are historical counts for the implementation before the Ghost additions. The [original campaign](evidence/computer10-20261031/REPORT.md) and [earlier integration campaign](evidence/deal-lint-spark-computer10-20261031/REPORT.md) remain immutable historical snapshots. Their 47-check Hoeflin and 31-check Towers totals apply to the old projects containing only the arithmetic cores; they are not totals for the expanded implementation.

## Reproduce the proof campaign

From the repository root on computer10:

```sh
python3 verification/run_computer10.py --portfolio-only
```

The runner discovers the matching toolchain through `alr -q printenv` in `~/.local/share/icar16-gnatprove-tools`. It parses an allowlist of literal exports without shell evaluation. Override the directory with `--alire-dir` if necessary.

Each invocation creates a new evidence directory and uses fresh temporary source copies and object directories. The portfolio requests bundled CVC5, Z3, Alt-Ergo, classic COLIBRI, and Yices together. Omit `--portfolio-only` to also run each prover independently. Portfolio completion does not imply that every independent solver run completes. The local configuration corrects the old COLIBRI adapter's incompatible `--steplimit` option to `--max-steps`; global tool configurations are not modified. `--steps=0` uses time budgets rather than a small implicit step cap.

An intentionally wrong inclusion-exclusion implementation in [negative_control](negative_control/) must be rejected. It is excluded from both production proof projects. A campaign is accepted only when the negative control is rejected with a native unproved contract and both production portfolios exit successfully, contain nonempty native totals, and report zero unproved and zero justified checks. Native coverage must also be retained and pass the assumption/suppression checks. A nonzero exit, missing report, timeout, incomplete metadata, or parsing failure cannot count as a successful project proof.

## Five explicit contracts per subprogram

`python verification/spark_contracts.py` inventories every supported project Ada function and procedure, including local, Ghost and specification-only interfaces. It counts top-level Pre/Post/Refined_Post conjunction clauses, Contract_Cases alternatives, and each explicit Global/Depends aspect. Ghost, SPARK_Mode, Inline, subtype declarations, body assertions and unsupported aspects are excluded. Exact normalized duplicates and literal Boolean padding fail. The per-entity inventory retains each clause and source location. Five entries do not imply five logically independent guarantees: bounds, predicate characterizations and endpoint consequences can overlap.

The checker handles this repository's restricted Ada subset, rejects ambiguous repeated/overloaded names and pragma-based mode changes, and relies on GNAT for Ada syntax/conformance. Native audits cross-check subprogram locations and all/spec status, and account separately for package/type entities. This is a structural floor and provenance check, not a general Ada semantic analyzer or proof that the specifications are adequate.

The model packages contain ordinary pure predicates/types so ordinary contracts can use them legally. Numerical observations, lexical checks and projection lemmas remain explicit Ghost operations. Hoeflin `Note` and Towers `Observe_Trials`, `Observe_Seed`, `Request_Report`, `Observe_Normal_Return` update ordinary request receipts; these remain active under Ghost Ignore and support normal-return postconditions. They record requested/observed state, not actual persistent bytes or filesystem success.

Current campaigns must pin both contract checkers, the complete Python inventory and a native-cross-checked SPARK clause inventory. Removing the new schema cannot downgrade an unrecognized/current campaign to an older policy. Historical exceptions require one of the exact retained campaign names and an explicitly matching old source checkout.

## What the proofs establish

The expanded proof projects enumerate the original cores, numerical support, calculation/simulation engines, SPARK-on main procedures, I/O interfaces, and three implemented model packages with explicit Ghost observers and checkers. `Hoeflin_Simulation`, `Hoeflin_Calculations`, and `Towers_Demo` are now in SPARK. Random-state updates, uniform generation, bisection and quadrature orchestration, simulation loops, accumulation, event counting, and probability conversion can therefore be analyzed along with the core arithmetic.

The Hoeflin core includes exact integer variance bookkeeping and bounded floating-point transforms. Some transforms use algebraically equivalent evaluation orders that aid proof; numerical equivalence is checked against the direct report formulas, rather than asserted to be bit-identical.

The Towers core uses exact integers and rational pairs for event counts and probability algebra. Continuous probabilities are rounded to units of `10^-15` at an explicit checked boundary. Both the raw floating results and the results using the exact SPARK algebra are retained; the small conditional-probability quantization error is separately accounted for in the implementation README.

Only small numerical validation bodies and the system I/O implementations remain outside SPARK. Their SPARK specifications expose explicit bounded normal-return contracts; their bodies check the promised ranges or relationships and raise an error instead of clamping an invalid value. These are runtime-checked trusted interfaces, not proofs that the checks can never fail. `Report_IO` and `Towers_IO` model external state explicitly; argument parsing, formatting, file operations, and their exceptions are not proved.

The installed Ada elementary-function specifications support SPARK, but provide only limited contracts. The analyzed code uses those contracts and the checked project interfaces. Proving a caller under these interfaces does not establish the backend's correctness, numerical accuracy, or totality. There are no project `pragma Assume` statements or proof suppressions in the analyzed code; that does not eliminate trust in unproved completions or the standard library. The proofs also do not certify quadrature error, Gaussian distributions, pseudo-random independence, a psychometric tail frequency, or the empirical validity of a test correlation. Those remain separate numerical and model questions.

## Ghost models and audited boundaries

`Hoeflin_Boundary_Models` and `Towers_Boundary_Models` encode accepted normal-return bounds and unchanged-value relationships. Actual excluded bodies invoke Ghost observers after ordinary checks. Explicit sine/cosine range observers inspect the actual cached elementary-function results in analyzed code. `Towers_IO_Models` and the Hoeflin receipt model cover restricted decimal parsing, integer images or lexical fields, requested data/layouts, observations and state transitions. These models have implemented, analyzed bodies; no imported model axioms or `pragma Assume` statements are used.

The [source-pinned register](ghost_boundaries.json) maps all native specification-only entities and both foreign imports, plus the three Hoeflin and four Towers private I/O helpers. It also maps the two trigonometric calls per project and inventories every external with-unit and five global unproved domains. The [Deal-contracted checker](ghost_boundaries.py) requires actual named source couplings, ordinary pure predicates, explicit Ghost observer/checker procedures or the five allowed ordinary request-receipt updates, native `all` model/caller statuses, complete inventories and explicit false implementation/adequacy-proof flags. Its constrained Ada source checks are a provenance audit, not a general Ada parser, semantic resolver or refinement proof.

A proved Ghost observation procedure is conditional on its precondition. Calls from excluded bodies are not thereby statically proved; they execute their Ghost checks when enabled. The Hoeflin receipt records a bounded modular summary and an admissibility flag, not proof that every output call follows a protocol. The Towers receipt records four requested files and twelve requested data rows followed by a normal return; it does not prove actual filesystem contents or persistence. Decimal and field models have restricted stated scopes. Backend accuracy, exact formatting/CSV bytes, failures/exceptions, physical I/O and model adequacy remain explicit obligations.

The programs compile and run with Ghost enabled and with Ghost disabled while ordinary assertions remain enabled. The erasure regression builds use these configuration pragmas in addition to the normal assertion-enabled project switches:

```ada
pragma Assertion_Policy (Check);
pragma Assertion_Policy (Ghost => Ignore);
```

Use `gprbuild -P PROJECT.gpr -p -cargs -gnatec=/absolute/path/to/policy.adc` in a fresh source/object tree to select the configuration. The retained runtime evidence includes the exact policy contents/hashes and actual commands. Both policies are compared against the original six CSVs, with numerical validation/replay and option-grammar cases. Finite erasure regressions do not prove noninterference or correctness of excluded implementations.

The [deliberately wrong Ghost ledger](ghost_negative_control/) leaves its event count unchanged despite a postcondition requiring an increment. It must be rejected with a native unproved functional contract, alongside the original incorrect union control. Both controls are excluded from production proof projects. The current campaign/auditor requires both rejections.

## Native coverage and proof scope

The runner retains the raw `.spark` JSON for each invocation. [spark_coverage.py](spark_coverage.py) records file hashes, native section names and entity counts, and normalized entity locations/statuses:

- `all`: specification and body are in SPARK, or the specification has no body;
- `spec`: the specification is in SPARK and its completion is outside the analysis;
- `no`: the declaration is outside SPARK.

These statuses describe language/analysis coverage, not successful proof of every verification condition. Native flow and proof totals are recorded separately. Whole units explicitly switched off may have an empty native entity array; `no=0` therefore does not mean that no code is excluded. The source inventory and empty raw-unit files remain visible alongside the entity counts.

Source filtering cannot hide a retained `pragma_assume` or suppressed flow/proof message. Explicit flow-only coverage can be used for a historical baseline; its analysis mode and proof-metadata completeness are recorded, and it cannot satisfy the full-proof completion flag. The current campaign report gives the actual coverage and final totals; earlier comparisons remain in their immutable reports.

## Numerical execution and replay

With the matching compiler in `PATH`, run `make check TRIALS=1000000` from either `ada/` folder. The retained campaign uses seed `20261030`: one million samples for each of eight Hoeflin test-count cases and one million shared correlated pairs for the four Towers cases.

Both implementations are compared with independent SciPy calculations. The Towers validator also replays every event count in Python. The [Hoeflin replay](replay_hoeflin.py) independently regenerates its 64-bit recurrence and Box-Muller pairs, checks all tail counts, and compares means and variances:

```sh
python3 verification/replay_hoeflin.py \
  verification/evidence/computer10-20261031/runtime/hoeflin/simulation.csv
```

Monte Carlo uncertainty is reported explicitly. Rare counts are descriptive; these sample sizes do not establish a one-in-a-million psychometric frequency.

Audit the committed symbolic-check follow-up against the current source with `python3 verification/verify_evidence.py`. Its default evidence directory is `verification/evidence/symbolic-fixture-computer10-20261105`. The follow-up pins the unchanged native records to their five-contract origin and checks the symbolic outcomes, original input hashes and normalized-input hashes against the selected source tree. The runner produces native proof/coverage and source-identity records. The published campaign additionally contains runtime, Python, document and complete checksum/source inventories; a new runner directory needs equivalent release inventories before the full retained-evidence auditor can accept it. The auditor checks checksums, native totals, raw coverage, source identities, Ghost mappings, and both negative-control results; it does not rerun the provers or independently validate SMT proof objects.

## Audit historical campaigns explicitly

Older campaigns describe explicitly identified earlier Ada sources. They must be checked against an explicitly selected old checkout, not silently substituted for current Ada source. From a full Git clone:

```sh
git worktree add --detach /tmp/composite-iq-before-expansion \
  2c32ecdd87690866bfcbf2d99725abba7cdad55e
python3 verification/verify_evidence.py \
  verification/evidence/computer10-20261031 \
  --source-root /tmp/composite-iq-before-expansion
```

The 1 November Ghost campaign predates the five-contract changes and requires its matching source revision:

```sh
git worktree add --detach /tmp/composite-iq-ghost-source \
  2a8e983fb3c8b90436b89db6e6adfe170872f5f5
python3 verification/verify_evidence.py \
  verification/evidence/ghost-boundaries-computer10-20261101 \
  --source-root /tmp/composite-iq-ghost-source
```

The pre-expansion source root shown first applies to the retained `deal-spark-computer10-20261031` and `deal-lint-spark-computer10-20261031` campaigns. The 643-check expanded campaign predates the Ghost models and requires its own matching source revision:

```sh
git worktree add --detach /tmp/composite-iq-expanded-source \
  ce0e895e472de86a6760f05a34d654f32ab0820e
python3 verification/verify_evidence.py \
  verification/evidence/spark-expanded-computer10-20261031 \
  --source-root /tmp/composite-iq-expanded-source
```

Its older required-body inventory is checked under the explicit historical policy; it cannot opt a current Ghost campaign out of model coverage. A mismatch against the selected Ada tree is an error. Historical Python tooling may still be resolved through verified Git blob identities in [source_history.json](source_history.json); there is no automatic Ada fallback. `--git-dir PATH` supplies a separate Git object database when needed. No historical uncontracted Python copies are added to the current tree.

The five-contract campaign predates the symbolic-check extension and now requires its explicit source revision:

```sh
git worktree add --detach /tmp/composite-iq-five-contract-source \
  1e4990e9eee64c8b353aea4b32da3a367deca1cd
python3 verification/verify_evidence.py \
  verification/evidence/five-contracts-computer10-20261104 \
  --source-root /tmp/composite-iq-five-contract-source
```

Together, these commands cover the six retained SPARK campaigns. Missing symbolic metadata is allowed only for these explicitly named historical campaigns with an explicit historical source root; it cannot downgrade a current campaign.

## Deal symbolic check

```sh
python verification/check_symbolic.py
python -O verification/check_symbolic.py
```

The project gate requires Deal 4.24.6 and Deal Solver 0.1.2. It checks both pure acceptance functions and both functions in the unchanged negative fixture. The three correct theorems prove; the deliberately incorrect function yields an actual counterexample to its nonnegative-result postcondition. All seventeen postcondition obligations are inspected individually: sixteen prove and one has the expected counterexample. Both proof-gate functions now expose six separately checked postconditions each; the symbolic source and result checks reject missing or unsupported clauses. An empty counterexample mapping is valid for the no-argument negative function. Skips, unsupported operations, tool errors, missing clauses or unexpected outcomes fail the gate. `make check` and GitHub Actions run this gate.

Stock Deal Solver cannot resolve `isinstance` in this fixture. The gate temporarily registers a project-local model of positional `isinstance(value, int)` for known primitive solver sorts. Integer and Boolean values return true, preserving Python's Boolean subtype behavior; float and string values return false. Other classes, sorts and unsupported source forms fail closed. The registry is restored even after an exception. Original fixture bytes, runtime contracts and installed dependency files are unchanged. The unextended `python -m deal prove` command still lacks this model and is not the reproduction command for the resolved check.

The pinned solver also evaluates only the first comparison in a chain. Before symbolic extraction, the gate expands chains with simple name/constant operands into conjunctions, retaining every bound and Python's short-circuit order in this restricted scalar subset. It rejects operands unsafe to repeat, such as calls, attributes and subscripts. The record pins both original and normalized source hashes. Regression cases detect a dropped upper bound, distinguish integer/Boolean returns from numerically equal floats, and exercise failure/skip handling and registry restoration.

The source-pinned historical campaign `symbolic-fixture-computer10-20261105` contains only one verified postcondition on each original proof-gate function. The validator retains that exact earlier obligation inventory **only** when the report identifies the original proof-gate SHA-256 (`1d32d786b1fc84f11de10d37a99e75c46cbcd5d9c1ac6e857d53da45fa10f51a`). The evidence auditor separately checks that the recorded hash matches the selected historical source tree and the release manifest. The current proof-gate source requires all six obligations per function; deleting any of them remains a failure. Historical evidence bytes, their source hashes, and the deliberately false fixture are unchanged.

This adapter and normalization use private, version-pinned solver APIs and belong to the trusted verification tooling; tests do not prove their general correctness. They support the two recorded source files, not arbitrary Python or universal verification of the project. Runtime/property tests, static lint, limited symbolic results, native SPARK proofs and statistical-model validity remain distinct evidence.

## Staged ten-clause SPARK contracts

The mandatory floor remains **five** distinct explicit Global, Depends,
Pre, Post, Refined_Post or Contract_Cases clauses per current SPARK
function/procedure. As with Python Deal, ten is an aspirational per-entity
target, **not** a global gate. A separate `ten_contract_summary(inventory(...))`
reports `target_contracts`, `entities_at_target` and
`entities_below_target`. The original `inventory` function retains its
**exact historical JSON schema** for immutable evidence comparisons,
and the CLI includes the derived counters under `ten_contract_target`.
The counters are checked by Deal contracts and regression tests.

Five exact-arithmetic routines in `Admission_Core` have strengthened
specifications with ten or more explicit conditions: `Total`,
`Union_Count`, `Fraction`, `Complement` and `Conditional`.
These specify individual cell lower bounds, zero-cell conditions,
positive denominators, exact complement regimes and conditional
zero/unit boundaries. The extensions introduce no floating-point
accuracy assumptions, operating-system success guarantees or new
`SPARK_Mode` exclusions. The formal clause definitions and source
integrity rules are explained in [TEN_SPARK_CONTRACTS.md](TEN_SPARK_CONTRACTS.md).

**Verification distinction:** GitHub Actions structurally checks
the declarations and Python regressions, but its workflow does not
execute GNATprove. Until a new native compilation/proof campaign runs
against the changed Ada source and its outputs are inspected, these
new postconditions are **asserted specifications, not newly certified
SPARK discharge results**. All retained campaigns remain immutable and
continue to be audited against their original pinned source revisions.

## Python contracts

Every current Python file imports Deal. Every named function, including tests and fixtures, carries at least five distinct meaningful Deal decorators. The gate accepts five or more distinct decorators, with no upper limit, and regression-tests five through eight. It rejects missing/insufficient declarations and repeated normalized syntax; it does not prove semantic independence or correctness. Install `requirements-dev.txt` and run `make check` from the repository root. The coverage gate also runs in GitHub Actions and inspects Git's file inventory, so adding a new Python file or function without contracts fails the check.

Run `python verification/check_static_lint.py` to inventory every Python file, require clean maintained code, and verify that the negative control still fails. Both `make check` and GitHub Actions enforce this gate. CLI entry points explicitly enable Deal even under `python -O`. The pinned Typeguard 3 integration is required by Deal 4.24.6's generated type checks. The current campaign report records the checks for the current implementation, including the native-coverage, Ghost-register and evidence-auditor tests. The full AI disclosure is in the main README and both reports.

The [historical Deal snapshot](evidence/deal-lint-clean-computer10-20261031/REPORT.md) retains its 110-test result and clean lint for its then-current 19 positive files. The [original Deal report](evidence/deal-computer10-20261031/REPORT.md) preserves the original 14 diagnostics and their subsequent resolution. Those records are immutable snapshots; adding the expanded coverage tooling changes the current Python inventory without rewriting earlier results.
