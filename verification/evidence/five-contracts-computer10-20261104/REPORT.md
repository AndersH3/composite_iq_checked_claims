# Minimum-five contracts and verification, computer10, 4 November 2026

This release enforces **at least five distinct Deal decorators per named Python function, with no upper limit**, and at least five explicit behavioral clauses/flow contracts per SPARK function and procedure. Six, seven and eight distinct Python decorators are positive regression cases; zero through four fail. Repeated normalized syntax cannot pad the minimum. All 603 historical evidence blobs from revision `2a8e983fb3c8b90436b89db6e6adfe170872f5f5` remain byte-identical.

## Final results

| Project | Functions / procedures | Explicit contract entries | Native checks | Flow / provers | Unproved / justified | Native all / spec / no |
|---|---:|---:|---:|---:|---:|---:|
| Hoeflin/Ferguson | 35 / 28 | 356 | 404 | 129 / 275 | 0 / 0 | 53 / 14 / 0 |
| Towers | 53 / 46 | 557 | 696 | 230 / 466 | 0 / 0 | 89 / 16 / 0 |

The two separate negative-control subprograms contribute ten explicit entries, giving **164 subprograms / 923 entries**, with minimum five and no gaps. Both deliberately incorrect controls are rejected. The production portfolios contain **1,100 checks**, all discharged without justification or suppression. The combined portfolio requested classic COLIBRI, CVC5, Z3, Alt-Ergo and Yices, with 30-second prover timeouts and 1,800-second wall limits, fresh source/object trees, `-f -U`, all-mode analysis, and checks/warnings treated as errors. This is a combined portfolio result; no claim is made that every solver independently proves every obligation.

- [Final manifest](manifest.json), [proof assembly and failed-attempt provenance](proof-assembly.json), [Hoeflin retry launch](hoeflin-retry-launch.json).
- [Hoeflin native report](hoeflin/portfolio/gnatprove.out), [result and per-subprogram clauses](hoeflin/portfolio/result.json), [raw native coverage](hoeflin/portfolio/spark/).
- [Towers native report](towers/portfolio/gnatprove.out), [result and per-subprogram clauses](towers/portfolio/result.json), [raw native coverage](towers/portfolio/spark/).
- [Complete structural SPARK inventory](spark-contracts.json), [complete Python inventory](python_contracts.json), [source-pinned model register](ghost_boundaries.json).

Native all/spec/no status describes language/body coverage, not proof by itself. Specification-only completions, foreign imports and physical I/O remain explicit trusted boundaries; empty raw files from off-mode units do not establish that nothing is excluded.

## What counts, and what does not

The SPARK audit counts top-level Pre/Post/Refined_Post conjuncts, Contract_Cases alternatives, and explicit Global/Depends aspects. It excludes Ghost/SPARK_Mode/Inline flags, subtype declarations, body assertions, unsupported aspects, repeated syntax and literal Boolean padding. The checker handles this project's restricted Ada subset, rejects unsupported ambiguous local-name/overload and pragma-mode cases, and cross-checks native subprogram locations/statuses. GNAT checks syntax and conformance. Five entries are not necessarily five logically independent guarantees: bounds, endpoint facts, exact field projections and predicate characterizations can overlap.

Python counts distinct real Deal decorator syntax, normalized for import alias and source locations. Every named function, including tests, fixtures, helpers and nested functions, is covered. Domain/result, exception, side-effect and preservation properties are appropriate to each function; the structural inventory is not a proof that those properties are sufficient or universally true. Five is a lower bound, not a required exact count or an upper limit.

## Final Python checks

The final inventory is **26 Python files, 251 named functions and 1,255 distinct Deal decorators**, with minimum five. **262 tests pass normally and under `-O`**. All 25 positive files are static-lint clean; the intentionally incorrect fixture produces exactly the expected DEL012 diagnostic and nonzero exit. Direct optimized linter invocations are included because invoking the gate under `-O` alone does not propagate `-O` to its lint children. CLI contracts explicitly enable Deal under optimization. The expected pytest warning about assertions outside rewritten modules remains in the optimized log.

[Minimum-policy final executions](python/minimum-final/checks.json) retain commands, return codes, timestamps, durations, source identities and actual stdout/stderr. [Parser-fix executions](python/parser-final/checks.json) and [earlier executions](python/checks.json) remain retained iterations; unavailable timestamps in the earliest eight executions are explicitly null rather than inferred. Two pure acceptance-gate postconditions are symbolically proved, dependencies pass, and both report calculation scripts pass. These focused symbolic results, clean lint and finite tests do not prove the full Python programs or their third-party libraries.

[Historical-source audits](history/checks.json) pass in both Python modes for all five retained SPARK campaigns, using explicitly matching Ada checkouts and verified Git objects for historical Python. Changed Ada never silently falls back to an older source version.

## Ghost models, ordinary receipts and runtime regression

The three model packages combine ordinary pure predicates/types with explicit Ghost numerical observers, lexical checkers and projection lemmas. Hoeflin `Note` and Towers `Observe_Trials`, `Observe_Seed`, `Request_Report`, `Observe_Normal_Return` are ordinary request-receipt updates, allowing normal-return postconditions to execute when Ghost is ignored. All original Ghost observation couplings remain covered by the register. Ordinary receipts record requests and observed returns; they do not certify output bytes, file creation, persistence or operating-system success.

[Final runtime records](runtime-final/summary.json) capture matching GNAT 13.2.0 builds with Ghost Check and Ghost Ignore, ordinary assertion/overflow checks enabled. Both policies reproduce **all six original CSVs byte for byte**: one million samples per each of eight Hoeflin cases and one million shared pairs for the four Towers cases, seed `20261030`. Numerical validation and separate-implementation replay pass normally and optimized; all tail/event counts agree exactly, with stated tolerances for moments. Each project/policy also passes eight CLI/domain/grammar cases. These duplicated-policy runs do not increase the Monte Carlo sample size or establish random independence or extreme-tail validity.

The current-source Hoeflin runtime was repeated after adding receipt loop invariants. Successful earlier Hoeflin runtime data remain in `runtime-final/hoeflin-before-loop-annotations/`; the summary references only final current-source runs. The initial failed Towers runtime attempt is explicitly retained under [runtime](runtime/ATTEMPT.md), not counted as a successful result.

## Resolved failures and compiler compatibility

The initial Hoeflin proof left one new driver receipt postcondition unproved. Adding outer-loop receipt invariants and an explicit index over the same test-count sequence allowed a fresh full-project retry to prove all 404 checks. Numerical expressions, random-state advancement and output order are unchanged. The [initial campaign](initial-campaign/manifest.json) and initial Hoeflin source/output remain available.

The initial Towers native invocation already proved all 696 checks. Its separate structural checker misread a Post aspect preceded by comments, producing an incomplete floor result. The comment-aware checker now preserves literals, excludes comments and rejects comment-based duplicate padding. Regression cases cover these forms. Final floors were re-audited against the identical pinned native proof/source files; native reports, solver outputs and invocation logs were not edited. The [exact initial checker bytes](initial-checker-source.txt) and initial records are retained. The final manifest explicitly assembles successful native invocations and subsequent structural audits; it does not change the initial launcher's observed exit status of 1.

[Compiler compatibility evidence](compiler-compatibility/README.md) exhausts the four Boolean Classify inputs. The original biconditional postcondition passed with the installed GNAT 13 at `-O0` and GNAT 14 at `-O0`/`-O2`, but raised caught assertions for three inputs with GNAT 13 at `-O2`. Equivalent guarded implications pass all four in the required optimized GNAT 13 build. Equivalent conditional Post clauses also avoid misleading GNAT 13 warnings on the expression-function Case_Name Contract_Cases form. Bodies remain unchanged. Probe harnesses catch exceptions, so their printed results, not exit status alone, determine case success. These finite compatibility observations are not a compiler-correctness proof.

[The symbolic negative-fixture attempt](python/symbolic-negative/result.json) is **unsupported**, not a successful rejection: the installed Deal Solver raises `UnsupportedError` on its `isinstance` postcondition. The correct helper in that fixture has its postconditions proved before the tool exception. This does not establish a counterexample result for the incorrect function. The independent static DEL012 negative control and the two pure acceptance-gate proofs remain successful. No type contract was weakened to accommodate the solver.

## Scope and limitations

No project proof axiom, pragma Assume or proof suppression was added. Complete native assumption/suppression inventories are empty. Checked unproved numerical completions, C erfc, the elementary-function/runtime implementations, compiler/ABI/target arithmetic, operating system, hardware and proof tools remain trusted. Successful caller/model proofs do not establish backend totality, guard acceptance on every execution, analytic or rounding accuracy, monotonicity, inverse convergence, quadrature error, full parser/formatter equivalence, exception behavior, physical output, or excluded implementation-to-model refinement. Receipt and lexical/decimal models retain their restricted stated domains. `Project_Number` models the two precisions actually used, 12 and 14.

Neither Deal nor SPARK establishes Gaussian/common-factor assumptions, empirical correlations/norms/reliability, pseudo-random independence, calibrated extreme psychometric tails, latent-ability interpretation, or model adequacy. Numerical comparisons, finite simulations, runtime contracts, static analysis and the two symbolic gate results are separate evidence. The retained-evidence auditor checks integrity, source identity, floors, coverage and native totals; it does not rerun the provers or independently validate SMT proof objects.

Both XeLaTeX/KOMA reports and the main README retain full AI disclosure, updated through 4 November 2026. AI agents and automated tools performed the recorded work; independent human peer review is not recorded or claimed. Source/PDF identities, final build/render checks, source hashes and complete checksums accompany this record.
