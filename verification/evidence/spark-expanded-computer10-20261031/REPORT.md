# Expanded Ada/SPARK verification on computer10

Completed on 1 November 2026. The folder name retains 31 October, when this expansion began. This campaign replaces the previous core-only scope for current sources; every earlier evidence directory remains unchanged.

The original implementation excluded more code than necessary. Both Hoeflin main procedures, Towers_Demo, numerical orchestration, random-state updates, uniform generation, simulation/count loops and accumulation now run in SPARK. New I/O packages isolate parsing, formatting and file/output operations behind SPARK interfaces with explicit external state. The proof projects enumerate all production Ada sources, including trusted completions, and required-body checks prevent a missing algorithm or driver from silently passing the evidence gate.

## Fresh proof results

| Project | Total native checks | Flow | Provers | Unproved | Justified | Native all / spec / no |
|---|---:|---:|---:|---:|---:|---|
| Hoeflin/Ferguson | 209 | 43 | 166 | 0 | 0 | 22 / 14 / 0 |
| Towers | 434 | 91 | 343 | 0 | 0 | 36 / 16 / 0 |

CVC5, Z3, Alt-Ergo, classic COLIBRI and Yices were requested together. Both portfolios exited 0 with warnings/checks treated as errors, zero unproved or justified checks and no incomplete subprogram proofs. This does not mean each solver independently completed each obligation. Earlier independent-solver comparisons remain historical evidence; this expanded campaign runs the combined portfolio only. The deliberately incorrect inclusion-exclusion control was rejected with an unproved functional contract.

- [Manifest, tool hashes, source identities and statuses](manifest.json)
- [Hoeflin native report](hoeflin/portfolio/gnatprove.out), [run and coverage](hoeflin/portfolio/result.json), [raw native files](hoeflin/portfolio/spark/)
- [Towers native report](towers/portfolio/gnatprove.out), [run and coverage](towers/portfolio/result.json), [raw native files](towers/portfolio/spark/)
- [Negative-control report](negative_control/portfolio/gnatprove.out)
- [Source hashes](source_hashes.json), [checksums](SHA256SUMS)

The actual CLI used `--mode=all --level=2 --steps=0 --counterexamples=off -f -U --no-subprojects`, a 15-second prover timeout and a separate 1,800-second wall limit per invocation. Fresh temporary sources and object directories were used; no stale proof cache was accepted. The compiler identifies as GNAT 13.2.0 and the matching GNATprove binary has banner 0.0w; their executable hashes and version outputs are recorded separately. The local classic-COLIBRI adapter uses its supported `--max-steps` option; no global configuration was changed.

## Coverage comparison and what it means

The [explicit baseline](baseline/) was rerun against verified source revision `2c32ecdd87690866bfcbf2d99725abba7cdad55e` in **flow mode only** to retain native coverage. Its Hoeflin inventory has 9 all entities and three empty raw unit arrays; Towers has 11 all entities and two empty arrays. This baseline is not a new proof campaign. The old 47/31 proof-check results remain in their original immutable reports.

Native `all` means specification and body are in SPARK, or a declaration needs no body. `spec` means a SPARK specification with a completion outside the analysis; `no` is a non-SPARK declaration. These statuses describe analysis coverage, not successful verification conditions. The baseline illustrates why zero no-status entries cannot establish zero excluded code: whole off-mode units can emit empty arrays. The native inventories, raw-file hashes, empty arrays and complete source-file list are retained instead of reporting a misleading percentage.

The old proof projects selected only 4 source files (two cores); the expanded projects select all 17 production Ada sources. Five original whole off-mode bodies have been replaced by analyzed drivers/support/engines. Only the two new I/O bodies remain wholly off; numerical units are on with the local exceptions listed below. Additional helper declarations mean entity counts are not a fixed-denominator measure of code coverage.

The full-proof coverage parser requires native spark/flow/proof/pragma_assume arrays in every raw file. It rejects malformed/ambiguous JSON, conflicting statuses, missing metadata, and explicit assumptions or suppressions even in foreign-source entries. Flow-only parsing cannot satisfy the proof-completion flag. Required driver/numerical entities must have all status. The evidence auditor also requires exactly both production projects and their prescribed body inventories, preventing missing-project or schema-downgrade acceptance. Tests exercise these rejection paths.

## Explicit trusted boundary

Hoeflin keeps five checked numerical completions outside SPARK: `Normal_Support.Square_Root`, `Survival`, `Check_Inverse_Bracket`, `Rare_Quantile`, and `Checked_Radius`. `Report_IO`'s body handles command arguments, formatting and stdout; its specification explicitly models input/output state.

Towers keeps eight checked Normal_Model completions outside SPARK: `Square_Root`, `SF`, `Checked_Log`, `Checked_Exp`, `Checked_Exponent`, `Checked_Probability`, `Checked_Node`, and `Check_Grid_State`. Four Towers_Engine completions validate numeric-to-exact-core relationships: `Checked_Quantization`, `Check_Union_Units`, `Check_Conditional_Units`, and `Check_Joint`. `Towers_IO`'s body performs argument parsing, rendering and filesystem/output operations; its external state is explicit in the SPARK specification.

Both numerical units have an off-mode foreign C_erfc import. Every strengthened normal-return range or relationship above is checked in the body before normal return; rejection raises rather than clamping or modifying a value to force a bound. These are trusted runtime-checked interfaces, not proofs that their checks cannot fail. The installed Ada elementary-function specifications support SPARK and are used where possible, but their implementations and limited contracts remain trusted. No project pragma Assume, imported proof axiom or proof suppression was added. Native `pragma_assume` and suppressed-message inventories are empty; the separate native `assumptions` dependency graph is retained unmodified and is not an explicit-pragma inventory.

Successful caller proofs are conditional on these interfaces and input preconditions. They do not prove backend accuracy or totality, that off-mode guards always succeed, I/O success, survival monotonicity, inversion convergence, quadrature error, random independence, normality of transformed generator outputs, or any empirical psychometric claim. This mixed-code obligation is described in [AdaCore's SPARK_Mode guide](https://docs.adacore.com/spark2014-docs/html/ug/en/spark_mode.html); [levels of assurance](https://docs.adacore.com/spark2014-docs/html/ug/en/usage_scenarios.html) also distinguish analyzable code, flow analysis, absence of runtime errors and functional contracts.

## Numerical execution and regression

[Fresh runtime evidence](runtime/) records independent builds, source hashes, actual executable commands and checks. Hoeflin ran 1,000,000 trials for each of 8 test-count cases; Towers used 1,000,000 shared correlated pairs for 4 cases. Both used seed 20261030. **All six CSVs match the immutable original runtime CSVs byte for byte.** Independent SciPy validation and replay passed normally and under optimized Python. Hoeflin tail counts and all 16 Towers event-cell counts reproduced exactly; Hoeflin means/variances meet the recorded tolerances. Common random numbers make cases dependent.

Boundary regressions passed: Hoeflin trials 2 with seed 1 and maximum 64-bit unsigned seed, rejecting trials 0/1; Towers trials 1 with seed 1 and maximum valid Park-Miller seed, rejecting trials 0 and an out-of-range seed. These finite tests do not prove every boundary execution. Runtime assertions and overflow checks remain enabled. No numerical tolerances or RNG advancement order were changed.

Towers' core conversion retains its checked 0.51e-15 reconstruction tolerance. The conditional-ratio quantization bound in the report remains separate from numerical integration error. Panel refinement, agreement with SciPy and deterministic replay provide numerical evidence, not rigorous transcendental/quadrature error bounds or proof of a population model. Million-trial rare counts cannot validate one-in-a-million psychometric frequencies.

## Final Python/Deal checks

[Python command evidence](python/checks.json), [environment and dependency integrity](python/environment.json), [source identities](python/python_source_hashes.json) and the raw stdout/stderr record 21 accepted command checks on computer10. All 22 Python files and 177 named functions carry 502 Deal decorators, with zero gaps. All 21 positive files have zero static diagnostics in normal and optimized Python; the deliberate negative fixture produces exactly DEL012 and exit 1. The full runtime/property suite passes **164 tests in each mode**. Optimized pytest reports its expected warning about assertions in non-rewritten modules; CLI Deal contracts are explicitly enabled under optimization.

Both numerical scripts, pip check, compilation of all 22 Python files, and all three historical proof audits pass. Deal Solver proves exactly the two pure acceptance-gate postconditions and rejects the incorrect symbolic control. No unsupported checks are counted as proofs. Deal's exception extractor matches the previously recorded unmodified dependency hash; no dependency patch, suppression or disabled-contract escape was used. Python source inventory/hashes were unchanged throughout the final checks.

These results distinguish contract coverage, lint, finite runtime/property tests and limited symbolic proof. They do not prove the entire Python programs, subprocesses, SciPy, floating-point backend or statistical model. The full repository-wide checks include both analyses and shared tools; their counts must not be added once per report.

## Evidence audit and history

The new campaign audit passes in normal and optimized Python against current Ada and Python sources. The three old SPARK campaigns were audited against an explicitly selected verified 2c32 source tree, with verified Git blobs used only for older Python identities. Changed Ada never silently falls back to history. Every one of the 265 previously committed evidence blobs still matches its old Git blob identity. The [prior source revision](baseline/source_revision.json) and current source hash inventory distinguish these contexts.

From a full Git clone:

```sh
python verification/verify_evidence.py
# To rerun instead of only auditing retained evidence:
python verification/run_computer10.py --portfolio-only --timeout 15 --wall-seconds 1800
```

Auditing checks hashes, complete inventories, native totals, coverage and negative-control records; it does not independently validate SMT proof objects or rerun solvers. See the [verification guide](../../README.md#audit-historical-campaigns-explicitly) for explicit historical-source commands. Both XeLaTeX reports have been updated, rebuilt and visually checked; their artifact identities and build/render checks are recorded alongside the campaign.
