# Repository-wide refactoring register — November 28, 2026

**Researcher/requester:** Anders Hellström.

> **AI disclosure:** OpenAI ChatGPT assisted the repository inventory, source review and refactoring. The changes require compiler, contract, runtime, and document regression validation; no independent human review or additional mathematical theorem verification is claimed.

## Freeze and baseline

New mathematical proof development is suspended until the extensive refactoring and its regression checks are completed. PR #59 merged the prior verification history into main at `2346a7e63ea7d9f93e13e2d7bdcba3caee118732`. The merge preserves the uncompiled GaussianVarianceCalculus candidates outside active compilation. Baseline 3706 canonical proof scripts + 127 MathComp targets + 13 FormalML targets = 3846 combined compiled inventory; 140 independently checked and assumption-audited probability targets. These are earlier verified-source counts, not newly verified refactored counts. Five pre-merge CI workflows failed and log retrieval returned BlobNotFound. See CONTINUATION_20261126.md.

## Scan scope and evidence

The recursive Git tree at the merge commit was not truncated and listed 297 tracked blobs, including 96 Rocq files, 26 Python files, 58 TeX files, 9 CI workflows, 7 shell scripts, 5 Makefiles, 8 PDFs and 42 Markdown files. All Python sources were retrieved for a source-level inventory of definitions, imports, long decorator expressions and headers; this is not a substitute for the AST or Deal gate. The first source pass examined the root and four analysis Makefiles, central report style and compatibility wrappers, source ownership and report-template auditors, canonical Rocq compiler, probability and publication CI workflows, and the largest available canonical Rocq modules. The 1.33 MB FiniteMoments.v full-content retrieval returned empty; inspect that file locally in full. No full semantic source review of all 96 Rocq or 58 TeX files is claimed yet.

The tree contained three exact-blob duplicate groups: two analysis ignore files; the Hoeflin simulation moments.csv and tails.csv; and the IQ discrepancy offline-validation and simulation-data results.tex. Retain generated evidence and compatibility paths until their semantics, provenance and consumers are checked; byte identity alone does not justify deleting them.

## First refactoring batch

| Commit | Change | Static evidence / remaining validation |
| --- | --- | --- |
| e0eafe3 | Shared book_targets.mk for all four analyses; remove broken retired Sequential targets; ShellCheck preflight for root local structural targets | Preserve explicit document stems and IQ smoke/production output; dry run all targets and rebuild reports |
| 02d25bc | One ordered MathComp verified module manifest for compilation and separate audits | Same 20 compile modules and same 20 audit modules; audit order normalized to dependency order; pending calculus excluded |
| ca324aa | Bind PDF publication to exact built source SHA; add canonical LaTeX templates and offline evidence to document-build hashes; update outdated eight-book documentation | Publication must reject an advanced ref; run document-only build and inspect provenance |
| 0ab2dcf | Factor 165 identical StratifiedBernoulli proof bodies and 62 identical GaussianCovarianceDomain proof bodies into two local tactics | Exact byte-for-byte inverse transformation restored both original source files; statements, declaration order and comments unchanged; kernel rebuild pending |
| d4ff6f4 | Move partial_moment and merge_moments verbatim to library/python/moments.py, retain public compatibility imports and add identity regression checks; hash actual shared numerical library | 32 original decorators preserved (17 and 15); numerical code unchanged; rerun static lint, contracts and Dask tests |
| ad0e46e | Single ordered canonical Rocq source manifest consumed by compiler and documentation audit | All 45 original compile modules and source ownership paths preserved; audit and kernel rebuild pending |

## Remaining opportunities and order

1. Complete full-source duplicate proof scan, beginning with FiniteMoments.v and the large finite probability, Schur, pooling and conditional projection modules. Large repeated solver scripts are candidates for local tactics, and repeated mathematical arguments should use existing general lemmas. Do not erase theorem statements or inflate proof totals.
2. Centralize reusable named Deal predicates for long configuration and record checks, particularly reporting/simulate.py, reporting/block_simulations.py, library/python/statistics.py, reporting/assets.py, library/python/sequential.py, the Towers calculator and test helpers. Keep at least 15 meaningful distinct contracts per named function; replace semantic redundancies with substantive checks rather than reducing coverage or padding. For example graph_hoeflin repeats the per-seed range/type test inside a compound condition and in a separate decorator. The AST gate alone does not establish semantic nonredundancy.
3. Inspect the 58 TeX sources for repeated preamble or definitions, equivalent mathematical exposition and inconsistent evidence labels. Preserve the shared KOMA-Script template, one initial disclosure, final AI appendix and all eight report-specific mathematical derivations. Consolidate the report list used by build, migration audit, and template validation without losing the eight-document requirement.
4. Review FormalML compatibility patch script (large ordered historical patch series), isolated build dependencies, and the distinction between canonical Rocq, MathComp, FormalML and experimental probability sources. Keep version pins and independently checked assumption boundaries explicit; do not rewrite upstream compatibility patches blindly.
5. Review legacy arrays versus block-summary Dask paths and tests for independent algorithmic checks. Preserve seeds, chunking, numerical operations, output schemas and historical run records; document any new experiment separately. Verify the new shared reducer source hashes and the retained report provenance.
6. Reconcile README/verification registers against actual source ownership and evidence. Preserve historical counts as historical, and only update current verification totals when fresh compilation and audit evidence exists.

## Regression gate before resuming new mathematical proofs

- All tracked shell scripts pass ShellCheck before execution, then syntax checks.
- Run root make check; minimum 15 meaningful distinct Deal decorators per applicable named function, negative-control static lint, Python and Dask tests. Test the isolated IQ smoke path and confirm existing production assets are unchanged.
- Run canonical Rocq documentation/ownership and language checks and compile all 45 modules. Independently check the refactored modules (and downstream closure where necessary), with existing theorem statements and assumptions preserved.
- Compile the 20 verified MathComp modules and their separate audits using the pinned Rocq 9.2/MathComp Analysis 1.18.0 environment, independently check the existing roots. Reproduce FormalML under its documented pinned dependency environment.
- Rebuild all eight reports with XeLaTeX, validate exact source hashes, diagnostics, title author, initial disclosure, final appendix, and inspect rendered pages. No stale source/PDF pairing or silent replacement of historical simulation evidence.
- Only after complete source review and satisfactory regression validation, resume GaussianVarianceCalculus R3 at the density derivative (`mulr0` mismatch, line 85), followed by finite FTC and whole-line boundary limits. No new theorem development during this phase.

## Initial computer10 regression checkpoint

At `0cd10ab`, the user transcript confirms successful branch synchronization, ShellCheck of tracked shell scripts, canonical Python/Rocq source ownership, and all eight report-template structure checks (one initial AI notice and one final disclosure appendix each). `make check` stopped at the first Python contract audit because the invoked system `python3` lacked Deal. Static lint and runtime tests were not reached; no numerical or proof regression result is inferred. Use a Python 3.13 virtual environment with the pinned `requirements-dev.txt` and pass its interpreter explicitly as `PYTHON` to Make. The untracked IQ smoke output is disposable and should remain separate from production evidence; its directory is now ignored without deleting local files.

## Complete AI disclosure

This register is an AI-assisted engineering audit requested by Anders Hellström. The inventory, connector commits and reversible source transformations are direct evidence; proposed later changes and regression gates are not completed tests. The local execution environment could not resolve GitHub for a full clone and lacks ShellCheck; Rocq/Deal/Dask/XeLaTeX checks have not been run here. The supplied computer10 transcripts provide earlier verified-source evidence only. This refactoring register neither certifies every theorem or runtime contract nor validates empirical psychometric models. No new mathematical axioms or admitted proof placeholders were added by this batch.
