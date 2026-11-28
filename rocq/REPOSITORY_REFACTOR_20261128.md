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

## Successful Python and structural regression at ac5ddba

Computer10 (Debian 13, Python 3.13.5 in .venv) passed pip check, all four local report Makefile dry runs, and two full make check executions. Timed run: 32.61 s wall, 477504 KiB peak RSS, zero swaps, exit 0. AST audit: 27 files, 139 named functions, 2217 contracts, minimum 15, zero undocumented functions, no reported problems. Positive Deal lint: 26 files, zero diagnostics; negative control correctly failed with DEL012; 122 pytest tests passed (12.95 s in timed run; 13.81 s in first run). This validates the first numerical relocation and structural checks under the existing test suite, not semantic nonredundancy of every contract. Rocq kernel and actual eight-book builds remain pending. Continue refactoring with new theorem development suspended.

## Second refactoring batch — canonical report manifest and kernel regression option

`2c12957` consolidates the eight-book source inventory in `library/latex/books.txt`. The Dask document builder, shell template audit, migration audit and GitHub Actions matrix use the same ordered rows. The audit rejects duplicate books/styles and incomplete eight-book inventories; the document builder includes the manifest in provenance. Simulation-only selection now uses the declared style. Existing report names and order are preserved. The canonical compiler also supports `--independent-check` to replay all 45 compiled module roots before deleting its temporary directory. The new changes require another ShellCheck, Python/Deal test pass, clean canonical compilation and independent kernel replay. The existing report CI campaign behavior has not been changed, and local document-only builds remain available. No new theorem development.

## Successful second-batch regression at 2b06149

Computer10 reproduced the complete make check gate: 27 Python files, 139 named functions, 2217 Deal contracts, minimum 15, zero reported coverage problems, 26 positive lint inputs with zero diagnostics, expected DEL012 negative control, and 122 passing tests (12.74 s). Wall time 31.92 s, peak 570620 KiB, no swaps, exit 0. The new book manifest and all eight structural checks passed. Rocq-only and documentation audits passed: 4029 declarations, 3693 theorem proofs and 3706 registered proof scripts in 45 modules. Rocq 9.2 compiled all 45 canonical modules and independently replayed all roots and their dependencies, with explicit success messages, wall time 87.35 s, peak 1179312 KiB, no swaps, exit 0. This confirms the initial 227 refactored proof bodies at that source revision. Nonfatal Stdlib warnings concerned large natural literals and Fin.t/Vector.t. Kernel replay is not a separate exhaustive assumption audit and does not establish full report coverage.

## Third refactoring batch — further polynomial proof consolidation

- `4b3a400`: 150 identical proof bodies in FourContrastCovariance.v reuse one local normalization tactic.
- `6718dbf`: 106 identical unequal-history proof bodies and 15 two-rate variance proof bodies reuse three documented local tactics.

The inverse transformations restore each original source byte for byte. All statements, comments and declaration ordering are retained. The third batch changes 271 existing proofs, bringing the cumulative refactored count to 498 across five modules (227 previously validated, 271 pending). Existing Stdlib Ring is reused rather than introducing a custom solver. The canonical CI workflow now invokes the previously validated independent-check mode as well as compilation.

FiniteMoments.v was successfully retrieved directly via blob fd9fdfcb86cf2fd0b8f793ab08e86c10f243a614 (1331661 bytes). A structural proof-body scan found 651 scripts and no long identical proof body repeated three or more times after whitespace/comment normalization; only eight reflexivity scripts repeated at that threshold. There are 355 indexed_basis-prefixed declarations. The vector-related warnings identify a possible longer-term library migration, but replacing dependent vector/index types would alter public statements and require a distinct migration with compatibility proofs. Preserve the currently checked representation during this source-preserving batch; further semantic review, including modularization and reuse of general lemmas, is outstanding. No complete semantic review of that large file is claimed.

Re-run the canonical regression on this third batch and build all eight books using retained inputs, preferably from an isolated detached worktree. No new theorem development. The report build, full named-predicate/semantic contract review, probability-library regression and remaining source review are pending.

## Third-batch canonical regression and report diagnostics

At `fb59962`, computer10 passed ShellCheck, the canonical documentation and Rocq-only audits, all 45 canonical module compilations and independent kernel replay. Counts remain 4029 documented declarations, 3693 theorem proofs and 3706 registered proof scripts. Wall time 85.74 s, peak 1178484 KiB, no swaps, exit 0. All 498 previously consolidated proof bodies have now passed canonical kernel replay. No additional theorem is counted.

The detached eight-book document-only build stopped after 98.36 s (peak 268872 KiB, no swaps, make exit 2) at sequential_conditional_means: underfull hbox badness 1406 at lines 292–312; overfull hboxes 162.19351 pt and 2.18599 pt at lines 319–364. The ranges correspond to the included theorem_foundations.tex text containing long literal Rocq names, rather than necessarily the main book's source lines. Commit `a91676f` replaces 21 unbreakable texttt identifiers with existing xurl/hyperref nolinkurl markup and splits two paragraphs; exact identifier strings were checked before and after. This is a candidate layout correction, not a completed build or visual inspection. No suppression of diagnostics, margin change, new packages or mathematical modifications. Retest in a fresh detached worktree and retain the failed logs. New proof development remains suspended.

## Second report layout regression at 8865646

Computer10 confirmed both overfull hboxes eliminated by the breakable identifier refactor. The only remaining diagnostic was underfull hbox badness 1406 in theorem_foundations.tex lines 292–312, with the log explicitly identifying the opening Gaussian-to-independence bridge sentence. Build wall time 94.74 s, peak 268340 KiB, zero swaps, exit 2. Commit `5a73a0d` shortens the italic heading and rephrases the opening into two sentences, preserving the distributional uniqueness obligation and independence conclusion. Strict layout validation is unchanged. This candidate requires fresh compilation; full eight-book validation is not yet established.

## Successful eight-book report regression at 588a875

Computer10 rebuilt all eight books in a detached worktree at `588a875` using the pinned Python/Dask/Deal environment and retained simulation inputs. All document-builder checks passed; the final record was emitted and make exited 0. Wall time 97.84 s, peak 266992 KiB RSS, no swaps. A separate grep across final TeX logs returned no matching overfull/underfull, missing-character or undefined-reference/citation diagnostics. The R1 and R2 layout issues are resolved without changing the diagnostic gate or mathematical claims. Automated rendering and layout checks passed; manual visual review and publication of the rebuilt PDFs are not established by this transcript. Continue the contract and source refactoring; no new theorem development.

## Fourth refactoring batch — shared named seed predicate

Commit `9a465fb` extracts the six Dask graph constructors' repeated seed-domain checks to `library/python/numeric.py:valid_seed_values`, which has 15 Deal decorators and an explicit offset argument. It removes the duplicated Hoeflin seed-domain check; nonempty replicate count is already checked separately in that array graph. The predicate requires a sized, reiterable Collection rather than accepting arbitrary duck-typed iterables. Towers and Sequential block constructors now check the actual unsigned 32-bit worker input bound using offsets 1000 and 2300 respectively. Previously a base seed near the upper boundary could pass graph validation and fail only at the worker. This is an intentional early rejection of previously invalid worker inputs, not a change to the normal seeded numerical campaign. Existing scale regression test now checks accepted/rejected exact endpoints, noninteger seed types, and rejection before worker dispatch. The new predicate, changed graph contracts and test assertions are unvalidated until make check passes. Further named-predicate extraction and semantic redundancy analysis remain outstanding. No theorem development.

## Complete AI disclosure

This register is an AI-assisted engineering audit requested by Anders Hellström. The inventory, connector commits and reversible source transformations are direct evidence; proposed later changes and regression gates are not completed tests. The local execution environment could not resolve GitHub for a full clone and lacks ShellCheck; Rocq/Deal/Dask/XeLaTeX checks have not been run here. The supplied computer10 transcripts provide earlier verified-source evidence only. This refactoring register neither certifies every theorem or runtime contract nor validates empirical psychometric models. No new mathematical axioms or admitted proof placeholders were added by this batch.
