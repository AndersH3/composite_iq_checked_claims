# Symbolic negative-fixture fix, computer10, 5 November 2026

The unchanged Deal negative fixture is now rejected by an actual symbolic counterexample, rather than by an unsupported `isinstance` exception. No original contract or runtime predicate was removed, weakened, replaced or disabled. The project-local checker also preserves every bound in comparison chains, which the pinned native solver otherwise evaluates incompletely.

## Fresh Python verification

[Actual executions](python/checks.json) retain commands, working directory, start/end UTC timestamps, durations, return codes, full stdout/stderr and source hashes before/after. All executions passed their stated acceptance criteria on **computer10**. The final Python source hashes match before and after the checks.

- **28 Python files, 292 named functions, 1,460 distinct Deal decorators, minimum five, zero gaps.** Five is a lower bound with no upper limit; existing positive regressions for six, seven and eight remain active.
- **343 tests pass normally and 343 under `-O`.** Deal remains explicitly enabled. Upstream astroid deprecation warnings remain visible in the logs; the optimized run also retains pytest's assertion warning. Warnings were not suppressed or counted as proof failures.
- All **27 positive files** are static-lint clean. The unchanged negative fixture produces exactly one expected `DEL012`, for `return -1`, with nonzero exit. Separate direct optimized linter runs complement the optimized gate, whose lint child interpreters omit `-O`.
- The symbolic checker passes normally and optimized, producing identical structured records. Dependency consistency, compilation, both report calculation scripts, retained numerical-output validation and independent simulation replay pass in both relevant modes.
- All **six retained SPARK campaigns** pass fresh integrity/source audits normally and optimized, against explicitly matching source roots. Historical Python is resolved only through verified Git objects; Ada must match the selected source exactly.

[Python inventory](python_contracts.json), [SPARK structural inventory](spark-contracts.json), [historical audit executions](history/checks.json) and [preservation evidence](preservation.json) supply the details. Structural counts establish declared-contract coverage, not semantic independence, adequacy or universal correctness.

## Symbolic outcomes

[The full result](symbolic/result.json) pins the checker, versions, original source hashes and normalized source hashes through the [manifest](manifest.json). Every native postcondition obligation is independently enumerated; the checker rejects missing clauses, unexpected theorems, skips, partial/unknown outcomes, tool errors and missing counterexamples.

| Source / function | Native theorem result | Individual postconditions |
|---|---|---|
| `proof_gate.py`: `totals_balanced` | proved | 1 proved |
| `proof_gate.py`: `successful_checks` | proved | 1 proved |
| Negative fixture: `probability_identity` | proved | 2 proved |
| Negative fixture: `negative_probability` | expected counterexample | nonnegativity fails; integer type and upper bound prove |

Thus three correct theorems prove and one deliberately incorrect theorem has the expected counterexample: **six postconditions prove, one fails as expected, zero unsupported/skipped**. The no-argument negative function has an empty counterexample mapping `{}`; it is an existing model, not a missing model.

### Exact fix and retained semantics

`verification/check_symbolic.py` requires **Deal 4.24.6 / Deal Solver 0.1.2** and the expected builtin integer implementation. For the duration of the run it registers an exact, narrow model of positional `isinstance(value, int)`: known integer and Boolean proxy values satisfy it; float and string values do not. Python's Boolean subtype behavior is retained. Unknown classes, sorts and call forms are rejected. The registry is restored after success or an exception, and an existing handler is never overwritten.

The pinned solver's comparison evaluator returns after the first comparison in a chain. The project normalizer expands chains only for simple name/constant operands in the restricted primitive subset, preserving all bounds and short-circuit order without duplicating effectful evaluation. Calls, attributes and subscripts in chains are rejected. Original source bytes are retained; only the solver input is normalized, with both hashes recorded.

The source guard accepts only the small grammar used by the recorded inputs: one unaliased `import deal`, primitive-annotated functions with one return expression, the supported lambda Deal decorators, and the modeled integer type call. It rejects defaults, arbitrary decorators, named validators, builtin/Deal shadowing, nested imports, effectful forms and unsafe chains. Native context skips are checked even when a failing postcondition would otherwise make the upstream prover return early.

Regression cases independently exercise lower bound, upper bound and integer type: returns `0`, `1`, `False` and `True` satisfy the three negative-function postconditions; `-1` violates the lower bound, `2` the upper bound, and `0.0`/`1.0` the type condition. A separate chained-upper-bound mutation must fail. Restoration, wrong versions, unsupported classes/sorts, ignored source forms, malformed or incomplete evidence, missing inputs and optimized execution are also checked.

The original fixture is byte-identical to revision `1e4990e9eee64c8b353aea4b32da3a367deca1cd`, with SHA-256 `7f448b22a0c934ae5eee2ab4a7f51395878ec2923ed1ac095fd1c320ed8c2505`. All 102 inspected installed Deal/Deal Solver Python files remain byte-identical; no third-party package patch was made. The unextended `python -m deal prove` command still lacks the project model. Reproduce the resolved check with `python verification/check_symbolic.py`, or `make check`.

## SPARK: unchanged proofs, fresh audit

This Python-only correction does **not** claim a new GNATprove invocation. The native reports, invocation logs, raw coverage, per-project result objects and both negative controls are retained unchanged from the [five-contract campaign](../five-contracts-computer10-20261104/REPORT.md). `native_proof_origin` in the manifest records its exact revision, manifest hash and native-report hashes. The auditor compares the complete reused project/control/toolchain records to that origin and checks every selected Ada source identity.

| Production project | Native checks | Flow / provers | Unproved / justified | Native all / spec / no |
|---|---:|---:|---:|---:|
| Hoeflin/Ferguson | 404 | 129 / 275 | 0 / 0 | 53 / 14 / 0 |
| Towers | 696 | 230 / 466 | 0 / 0 | 89 / 16 / 0 |

The total remains **1,100 production checks**, with both deliberately incorrect SPARK controls rejected. The structural inventory remains **164 subprograms / 923 explicit entries**, including the two controls, minimum five. The native portfolio requested classic COLIBRI, CVC5, Z3, Alt-Ergo and Yices together; this does not mean each prover independently discharged every obligation. Native `all/spec/no` describes analysis coverage, not proof by itself. Empty records from off-mode units do not imply that nothing is excluded.

All Ada source/project files are unchanged. Fresh Python validation and replay use the six retained million-trial CSVs; they add no Monte Carlo samples. The earlier Ghost Check/Ignore builds and command-line regressions remain historical evidence and were not rerun for this fix.

## Reports, preservation and limitations

Both XeLaTeX/KOMA reports include the final Deal and SPARK results and limits, identify the unchanged native origin, and retain full AI disclosure current through **5 November 2026**. Both PDFs were rebuilt and all pages rendered and visually reviewed. [Document checks](documents/artifacts.json), final build/render logs and [release source hashes](source_hashes.json) pin the artifacts. All **1,040 historical evidence blobs** from the baseline remain byte-identical. The new record has its own complete `SHA256SUMS` inventory.

The adapter, AST normalization, source guard and native private APIs are part of the trusted verification toolchain; finite tests do not prove their general correctness. The symbolic result is limited to the two pinned source files and encoded postconditions, not universal verification of the full programs, runtime libraries, subprocess handling, Python or Z3. See the [Deal verification documentation](https://deal.readthedocs.io/basic/verification.html) for the upstream tool's restricted scope.

SPARK trusts the documented numerical completions, foreign/runtime implementations, compiler/ABI/arithmetic, operating system, hardware and proof tools. Ghost observations and ordinary receipts do not prove excluded implementation refinement, backend totality, exception freedom, numerical accuracy, exact formatting or physical I/O. No assumption, suppression or weakened contract was added. Evidence audits check integrity, source identities, structural floors, coverage and native totals; they neither rerun the provers nor independently check SMT proof objects.

Neither tests, Deal nor SPARK establishes empirical correlations, norms or reliability, Gaussian/common-factor assumptions, random independence, calibrated extreme psychometric tails, latent-ability interpretation or statistical-model adequacy. AI agents and automated tools performed the recorded work; independent human peer review is not recorded or claimed.
