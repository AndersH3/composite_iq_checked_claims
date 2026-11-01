# Ghost boundary models, AI disclosure and verification

Executed on computer10 on 1 November 2026, against fresh copies of the source identities retained here. This campaign adds implemented SPARK Ghost models to the earlier expanded programs. All 397 prior committed evidence files remain unchanged. The earlier 209/434-check campaign describes source revision `ce0e895e472de86a6760f05a34d654f32ab0820e`; those historical totals do not describe the current Ghost-augmented programs.

## Native results and modeling inventory

| Project | Native total | Flow | Provers | Unproved / justified | Native all / spec / no | Registered spec-only + foreign boundaries | Private I/O helpers | Sin/Cos links |
|---|---:|---:|---:|---|---|---:|---:|---:|
| Hoeflin/Ferguson | 283 | 77 | 206 | 0 / 0 | 54 / 14 / 0 | 15 | 3 | 2 |
| Towers | 498 | 123 | 375 | 0 / 0 | 90 / 16 / 0 | 17 | 4 | 2 |

Both production portfolios completed with warnings/checks treated as errors and zero unproved or justified checks. The combined portfolio requested CVC5, Z3, Alt-Ergo, classic COLIBRI and Yices. This does not mean each solver independently proved every check. The original incorrect union contract and the new incorrect Ghost event-counter contract were both rejected with native unproved functional contracts; rejection is mandatory for campaign acceptance.

- [Manifest, source identities, tool hashes and actual commands](manifest.json)
- [Hoeflin native report](hoeflin/portfolio/gnatprove.out), [result and model audit](hoeflin/portfolio/result.json), [raw native JSON](hoeflin/portfolio/spark/)
- [Towers native report](towers/portfolio/gnatprove.out), [result and model audit](towers/portfolio/result.json), [raw native JSON](towers/portfolio/spark/)
- [Incorrect union control](negative_control/portfolio/gnatprove.out) and [incorrect Ghost control](ghost_negative_control/portfolio/gnatprove.out)
- [Source-pinned Ghost register](ghost_boundaries.json), [source hashes](source_hashes.json), [checksums](SHA256SUMS)

The actual invocations use fresh source/object directories, `--mode=all --level=2 --steps=0 --counterexamples=off -f -U --no-subprojects`, a 15-second prover timeout and a separate 1,800-second wall limit per invocation. GNAT reports 13.2.0; the matching GNATprove banner is 0.0w. Exact executables, version outputs and local prover configuration are retained. The local classic-COLIBRI adapter uses `--max-steps`; global tool configurations are unchanged. Runtime builds retain the original assertions, overflow checks, floating-point switches and mathematical evaluation order.

Native all/spec/no statuses are language/analysis coverage, not proof results by themselves. Spec-only entries remain explicitly trusted completions; adding Ghost models does not turn them into proved bodies. Whole off-mode units can emit empty native entity arrays, so no=0 cannot establish zero excluded code. Full-proof native metadata, exact required-body inventories, both production projects and both rejected controls are audited separately.

## Implemented Ghost models and actual coupling

Hoeflin_Boundary_Models models accepted numerical normal returns, C-erfc scaling, the sine/cosine range interface, canonical nonnegative decimal integer images, requested numeric values/precision, label separator metadata, and an abstract receipt. Actual excluded numerical bodies invoke Ghost observation procedures after their ordinary guards. All eight public I/O operations record their event/payload after successful output or parsing; the three private helpers have actual source-bound model uses.

The Hoeflin receipt contains the latest event, typed payload, section, nominal column count, modular counters and an admissibility flag. It is not a complete character history or proof that every protocol call is admissible. The label projection records length and separator counts, while numeric projection records the value and requested precision, not physical characters or rounding accuracy. Those limitations are explicit register obligations.

Towers_Boundary_Models covers the eight numerical and four engine completions, including unchanged-value relationships observed using actual entry snapshots. It also models the actual typed sine/cosine results. Towers_IO_Models implements bounded decimal digit accumulation and its bounds, lexical fields, case labels, report validity, nominal layouts and an abstract receipt. The main procedure proves receipt transitions through returned options, a requested data snapshot, four requested files/twelve requested data rows and an observed normal return. These are request/observation properties, not a theorem that files exist, were closed or persisted correctly.

The decimal model defines a restricted unsigned-digit interpretation using exact integer arithmetic. Its proved postconditions establish bounds and nonempty recognition, not universal equivalence with Ada Value parsing. Actual recognized values are compared under Ghost checking; other original Ada input forms remain accepted and have bounded-value observations. Real/integer lexical field models are not complete numeric round-trip, formatting-accuracy or CSV-serialization proofs.

The numerical observers are implemented Ghost procedures with real acceptance preconditions. Some observer bodies are null: their role is an executable model-precondition check, not a hidden backend implementation or a new accuracy theorem. Ghost helper bodies, range/projection functions and ledger transitions are analyzed in SPARK. An invocation inside an Off body is checked when Ghost is enabled but is not statically proved merely because its observer body was analyzed. Original ordinary postconditions/guards remain in force under Ghost Ignore; Ghost expressions were kept out of ordinary assertion contexts that would make erasure incompatible.

The register audits every native spec-only entity (14 Hoeflin, 16 Towers), each foreign C import, all seven project-private I/O helpers, and two standard trigonometric links per project. For each registered model it requires a declared Ghost package, matching source hashes, native all status and an actual model use in the named operation, rather than a comment or unrelated call. Standard links bind the cached result to its Sin/Cos assignment and subsequent observation. The constrained source audit is not a general Ada parser, semantic resolver or proof of refinement. It also inventories all external with-units (5 Hoeflin, 7 Towers) and five global unproved domains.

## What remains unproved

Every excluded boundary retains `implementation_proved:false` and `model_adequacy_proved:false`. No pragma Assume, imported proof axiom or proof suppression was added. The raw explicit-assumption/suppression inventories are empty; the separate native assumptions dependency graph remains unmodified. Installed library specifications, the compiler/runtime, proof tools and target platform remain trusted infrastructure.

Ghost coverage does not prove backend correctness or totality, transcendental identities/accuracy, survival monotonicity, inverse convergence, quadrature error, output precision or bytes, OS/filesystem behavior, memory/resource success, failures/exceptions, or excluded implementation-to-model refinement. The models principally cover accepted normal returns and observations/requests. Nor do they prove that contracts are adequate requirements, guards never reject, pseudo-random draws are independent, the transformed draws have an exact Gaussian distribution, population correlations/norms are empirically calibrated, or psychometric claims are valid.

These distinctions follow [AdaCore's Ghost specification guide](https://docs.adacore.com/live/wave/spark2014/html/spark2014_ug/en/source/specification_features.html) and [mixed-SPARK boundary obligations](https://docs.adacore.com/spark2014-docs/html/ug/en/spark_mode.html). The project supplies reviewable models and retained machine results, not a claim of end-to-end verification of excluded libraries or physical I/O.

## Ghost Check/Ignore and numerical execution

[Runtime evidence](runtime/) retains fresh source identities, policy contents/hashes, actual compiler/executable commands, comparisons, validator/replay results and boundary/grammar cases. Both Ghost Check and Ghost Ignore builds use ordinary assertion checking. The erasure configuration is:

```ada
pragma Assertion_Policy (Check);
pragma Assertion_Policy (Ghost => Ignore);
```

Both policies reproduce **all six original CSVs byte for byte**: the two Hoeflin outputs (one million trials for each of 8 cases) and four Towers outputs (one million shared pairs for 4 cases), seed 20261030. Validators and independent-implementation replay pass normally and under optimized Python under each policy. Hoeflin tail counts and all 16 Towers event-cell counts match exactly; mean/variance checks retain their tolerances. The duplicated policy runs reuse the same seed/data and do not increase the effective Monte Carlo sample size.

Each project/policy also passes 8 CLI/domain cases: canonical small runs, signs/whitespace, underscores, based literals, exponents, maximum seeds and invalid trials/seeds. These retain existing Ada Value syntax rather than narrowing accepted options to the restricted Ghost decimal grammar. Finite comparisons complement Ghost checks; they do not prove noninterference or totality of excluded implementations. Numerical agreement/refinement and rare Monte Carlo counts remain separate from approximation-error bounds or validation of extreme psychometric tails.

## Python/Deal, history and disclosures

[Final Python evidence](python/checks.json) records 23 accepted command checks on computer10. All 24 Python files and 213 named functions carry 607 Deal decorators, with zero gaps. All 23 positive files are lint-clean in normal and optimized Python; the deliberate negative fixture yields exactly DEL012/exit1. The full suite passes **209 tests in each mode**. The expected optimized-pytest warning about assertions in non-rewritten modules remains recorded; CLI Deal contracts are explicitly enabled.

Both numerical scripts, compilation of all 24 Python files, pip check/freeze, both pure symbolic postconditions and the rejected wrong symbolic contract pass as expected. All four earlier SPARK campaigns pass normal/optimized audits using explicitly matching historical Ada source trees; historical Python uses verified Git blobs. There is no automatic Ada fallback. Dependency files, including Deal's exception extractor, were not patched; final Python source hashes stayed unchanged through the tests. Coverage, lint, finite/property executions and two symbolic gate results are distinct forms of evidence, not a universal proof of Python correctness.

The current campaign audit passes in both modes against current sources. It checks checksums, native totals, both controls, raw coverage, exact project/body inventories, model mappings and source identities; it does not independently verify SMT proof objects or rerun solvers. The runner creates native campaign records; complete release inventories are also needed before using the full retained-evidence auditor on a newly generated directory. See the [verification guide](../../README.md) for reproduction and historical-source commands.

Both XeLaTeX reports and the main README now carry an upfront notice and full AI disclosure: substantial OpenAI Codex/sub-agent contributions, the human-requester role, session-identified model family and missing exact model metadata, AI/tool review versus absent recorded human peer review, the scope of source consultation, separate implementations versus independent authorship, synthetic data, retained evidence, and unavailable complete transcripts/per-line attribution. Exact model checkpoints or contribution percentages have not been invented. [Artifact identities and build/render checks](artifacts.json) and [final consistency checks](consistency.json) document the PDF rebuild and review.
