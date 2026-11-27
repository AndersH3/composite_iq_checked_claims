# Five-priority continuation — verification boundaries

Researcher/requester: Anders Hellström. AI-assisted source and analysis; only kernel and runtime checks establish verification.

Verified baseline: 8d2f76afb5fbbae250eb4d21c893d5e2cc4bda8d. All 45 canonical modules and the original 16 IQ algebra scripts passed locally with Rocq 9.3.0. Python 122 tests and 400 million synthetic rows passed before this change. Retain the published evidence unchanged until rerunning the revised source.

| Priority | Work in this revision | Open obligation |
|---|---|---|
| FormalML / MathComp | Upstream API inspection; CE transfer, normalized convolution and density-factorization candidates | Compile pinned libraries and all new scripts; upstream FormalML compatibility remains unresolved |
| Gaussian independence | Factor prior-likelihood density in centered residual coordinates using upstream conjugacy | Show measure pushforward under shear, factor rectangle probabilities and generalize to arbitrary joint Gaussian vectors, including singular boundaries |
| IQ propositions | Weighted Jensen deficit and strict inequality; written two-component proof | Folded normal integrals, joint order statistics, orthant law, selection and full Gaussian distributional arguments |
| Refactoring | Shared provenance, safe smoke path, floating-point correlation endpoint, small-scale folded mean | Re-run contracts, full Dask and PDFs |
| CI | Four failed workflows at verified baseline were submitted for failed-job rerun. Rocq job 140149809824 returned BlobNotFound and no step records | No verified root cause; inspect Actions UI or gh run view logs; never weaken gates to turn CI green |

CI run IDs: 45889938315 (books), 45889938182 (migration), 45889938621 (Python), 45889938258 (Rocq). The rerun requests were accepted, not confirmed successful. No change to required compiler versions or CI acceptance conditions. MathComp now requires all six candidate theorem declarations and Python CI verifies the smoke run does not modify tracked production data.


### Repeat computer10 validation at 0b22b3f

The researcher-provided November 26 terminal transcript identifies source revision `0b22b3f64c6429d04071b5c5f56028e86a3b8301` and records:

- ShellCheck and documentation audit passed: 4,020 declarations, 3,686 theorem/helper proofs and 3,699 registered proof scripts.
- Rocq 9.3.0 (OCaml 4.14.2) compiled all 45 canonical modules, including all 18 IQ discrepancy algebra theorems and both weighted-scale Jensen certificates. Stdlib is 9.2.0; the switch name `rocq-9.2` is not the actual compiler version.
- The Python audit passed for 139 functions and 2,217 contracts, with a minimum of 15; static lint passed with its expected DEL012 negative control; all 122 tests passed in 12.80 s.
- The isolated IQ smoke run completed and the production-data Git diff was empty. The full default Dask/Deal run exited zero in 25.76 s wall clock (379% CPU, 421,100 KiB peak RSS). Its ten scenarios each use 40 million rows; failure of any diagnostic would exit nonzero.
- Both XeLaTeX books built successfully (12 and 13 pages, respectively); the transcript shows the usual geometry and unicode-math warnings. No fresh visual inspection or artifact publication is demonstrated by this transcript. The new generated files and exact source hashes must be published from computer10.
- MathComp and FormalML were not installed in the inspected switch; Docker was not found in PATH. Their candidate scripts remain unverified. The existing validated switch is to be preserved; use the isolated environment in [PROBABILITY_LIBRARY_VALIDATION.md](PROBABILITY_LIBRARY_VALIDATION.md).


### Publication and first isolated probability-library installation

The researcher-published commit `80e49447148c9e2e8aaaa8cc197edcaa9ce95e14` contains both regenerated PDFs and the new production summary. The retained manifest records all ten scenario diagnostics passing, elapsed campaign time 24.892283699009567 s, IQ simulation SHA-256 `002df8927ba241f882c29438be054e7f399725c6e447f1c98462b37708894851`, shared reducer SHA-256 `06c1d2a4e272de9c778a73d4dc35ed2b0834f0fbdbba554ab98a659ad59e8cd1`, and provenance SHA-256 `c24b15528498eb9904364941eb118f06f9c779a97a6cb44dfde3ff90a3a25434`.

The separate gaussian-rocq-9.2 switch installed core/runtime/Stdlib 9.2.0 and MathComp core 2.6.0. Finmap 2.2.4 and Bigenough 1.0.4 failed during dependency compilation, before Analysis 1.18.0 could be installed. Inspection of the upstream release Makefiles suggests legacy commands may resolve to system Coq; add the official version-matched coq-core compatibility package first and verify paths. The same compatibility step is added to both probability workflows. See PROBABILITY_LIBRARY_VALIDATION.md for the recovery procedure. No new probability theorem has been kernel-verified by this transcript.

### Successful isolated dependency installation — November 27, 2026

The researcher-provided computer10 transcript confirms that installing the official coq-core.9.2.0 compatibility package resolved both dependency compilation failures. All five legacy/current executables resolved within gaussian-rocq-9.2; coqc and rocq reported the same switch library path. Bigenough 1.0.4, Finmap 2.2.4, Classical/Reals 1.18.0 and Analysis 1.18.0 all installed successfully. A new SSH shell did not retain PROJECT or LOGDIR; tee attempted to write under / and the Gaussian source was not copied. This is a shell-session setup failure, not a failed theorem. The next step is to initialize the variables and compile the six-theorem candidate module. FormalML remains unverified.

### First actual MathComp candidate compile — November 27, 2026

At `c6a26bf92df08c0c831f58460e1ec26eee55a775`, computer10 loaded MathComp-Analysis 1.18.0 under Rocq 9.2 and accepted the first three posterior declarations through their Qed commands. The compiler stopped at the fourth theorem declaration (line 177) because the realType of its untyped binders could not be inferred. No complete .vo was produced. Bind all real parameters explicitly to the section's R and the final measurable event to set R in the three new theorems. Specialize the upstream normal_pdfE and post_stddev_gt0 explicitly; isolate the translation identity using MathComp addrC/addrK. All six theorem statements retain their mathematical hypotheses and conclusions. These corrected scripts require another kernel run; the third-party notation and coercion warnings are nonfatal in the supplied transcript.

### Second MathComp candidate compile — November 27, 2026

Computer10 at `d467dd7e3ababde82d5fd6a8223c87f827148fec` accepted the explicit realType binders and reached line 183 of the fourth proof. The unrestricted addrC rewrite left no matching subterm for addrK; subtraction is addition of an opposite, so the commutativity rewrite must target the inner sum explicitly. The revised script uses [m + e]addrC and addrK and makes the later section-local density lemma application explicit. No mathematical statement is changed. The first three theorems again passed their Qed commands; no completed six-theorem .vo was produced. A further kernel run is required.

### Successful MathComp kernel compilation — November 27, 2026

On November 27, 2026, computer10 compiled the exact six-theorem MathComp module at revision `9f5a5508fcb0e5fc8b079fe4090c10aa0a7ef0e1` using Rocq 9.2.0 and MathComp-Analysis 1.18.0. The researcher supplied the successful terminal transcript (exit status 0, GaussianPosteriorMeasure.vo, 75 KiB). All six theorem scripts passed, including the centered residual density, scalar observation/residual density factorization and marginal observation measure. This is local kernel evidence, not a successful GitHub Actions run or a proof of full multivariate Gaussian residual independence. The six scripts are tracked separately from the 3,699 canonical Stdlib proof scripts; the three previously verified posterior results must not be double-counted.

Next: independently check the compiled module with rocq check and inspect Print Assumptions; build the FormalML dependency closure without changing the verified MathComp environment. The general joint Gaussian independence and full-history conditional expectation remain open.

### Independent kernel check and FormalML dependency preview — November 27, 2026

On November 27, 2026, the researcher supplied the full independent `rocq check GaussianPosteriorMeasure` transcript for the previously compiled module at source revision `9f5a5508fcb0e5fc8b079fe4090c10aa0a7ef0e1`. The checker traversed the imported dependency closure and explicitly checked all six project theorem constants, ending with `Modules were successfully checked`. This is independent compiled-object verification, not a transitive assumption audit or a GitHub Actions success. The subsequent FormalML checkout at `8ee433dc802fca35f6bceb6dacb69d3c1315e886` succeeded. Its opam dry-run proposed exactly four additions: conf-clang 2, coq-coquelicot 3.4.5, coq-ext-lib 0.13.1, coq-mathcomp-ssreflect 2.6.0, with no removals or version changes. The displayed installations were simulated; actual dependency installation and FormalML compilation remain pending.

### FormalML dependency installation and first local library build — November 27, 2026

At `6146c2de6ddcdaee876da2954a3e7f678784b6b2` computer10 installed all four previewed dependencies without changing the verified MathComp packages. The tracked shell scripts passed warning-level ShellCheck before the guarded compatibility utility ran. The required FormalML library build stopped at two independent upstream failures: Hilbert convex-projection characterization (patched line 1241, tactic cannot find witness) and negative infinite reciprocal limit (patched ELim_Seq.v line 2232, implicit posreal versus R). Neither required probability target was produced; the subsequent project CE import failure is downstream. The compatibility utility now explicitly coerces eps to pos eps in D174 and D176 replaces the entire forward convex-projection implication using the existing aux5 inequality and Stdlib Rmin bounds, preserving the theorem statement and D173 reverse proof. These changes have not been executed or kernel checked here. Apply the complete revised utility only in a fresh pinned FormalML checkout after ShellCheck; retain the earlier checkout and logs.

### Second local FormalML build — November 27, 2026

At `5141e68f2d20f8f794b052ce49c0cc28a177b0c8` warning-level ShellCheck and the revised compatibility patch passed. The build still stopped in hilbert.v line 1246 (arithmetic witness) and ELim_Seq.v line 2238 (tactic parser). Both probability targets remain absent. Refactor the negative-tail proof using Stdlib 9.2 Rinv_0_lt_contravar and Rinv_inv rather than reciprocal multiplication/field tactics; pass the explicit Rabs_left proof argument. Replace nonlinear automation in the reverse convex-projection bound with Rmult_le_0_lt_compat, and derive both finite bounds before destructing the extended-real infimum. Further simplify the forward bound with explicit Stdlib product lemmas. The exact generated Hilbert failing line was not included in the transcript, so these are candidate repairs, not a confirmed diagnosis of that line. No theorem statements changed. Use a new pinned local clone rather than downloading FormalML repeatedly; the prior committed upstream tree remains pristine even when its working files are patched.

### Third local FormalML build — November 27, 2026

Computer10 at `17fdaa4e67339dfc571b27d200ecf3560b0f0aec` passed ShellCheck and the compatibility utility. Its supplied numbered patched-source excerpts locate the two errors precisely: hilbert.v:1212 comma-separated rewrite syntax under ssreflect, and ELim_Seq.v:2242 the deprecated Rabs_Rinv rewrite (which has a nonzero side condition), followed by an unmatched Rabs_left rewrite. Use space-separated rewrite syntax in both forward Hilbert branches. Replace the reciprocal-absolute-value step with Stdlib 9.2 Rinv_lt_0_compat, Rabs_left on the reciprocal, and Rinv_opp; the preceding order proof already passed. Explicitly reduce the remaining finite Rbar equality in the reverse projection proof. No theorem statements changed. Both library targets still require a successful kernel run. The local detached upstream commit 72902bd9 records diagnostic patches only and is not a project-branch commit; clone locally and check out the original pinned upstream revision for each fresh test. Do not push to upstream FormalML.

### Fourth local FormalML build — November 27, 2026

At `d576088c5c0f8c27ea4228740e97140ab59dca1c`, ShellCheck and patch execution passed. ELim_Seq.v compiled in full, followed by RbarAdd.v, RiemannAdd.v, Utils.v and FunctionsToReal.v. The complete convex-projection characterization passed its Qed at patched hilbert.v:1281. The new blockers are the exported ortho_projection_convex_unique call at line 1319 (expected an existing nonemptiness premise before convexity) and Event.v:745 sa_sigma_const (negative branch unfolded the universal event instead of pre_event_none). D177 constructs nonemptiness from the existing minimizer and supplies the resulting premises explicitly; D178 uses pointwise equivalence to the appropriate universal/empty event. Both preserve original theorem statements. The probability targets still have not compiled; new changes need ShellCheck and kernel verification. The detached local diagnostic commit 77b96c74 is not a project commit and should not be pushed to IBM/FormalML.

### Fifth local FormalML build — November 27, 2026

At `1c19015484ccaa5a4a3d7586b9e88e5f54f19640` the compatibility patch and ShellCheck passed. Event.v compiled in full; SigmaAlgebras.v was reached and stopped at line 172 in pre_sub_partition_diff. The Hilbert module advanced past projection uniqueness and stopped at line 1491 in charac_ortho_projection_subspace2, with H3 already proving the equality-to-zero required for the right disjunct of nonpositivity. D179 makes that disjunct explicit and retains the compatibility certificate. D180 updates the other two downstream uses of projection uniqueness to supply the existing nonemptiness witness. D181 selects the subpartition disjunction branch and uses pre_event_diff_self/pre_event_diff_false_r. No new probability theorem is counted: both required FormalML targets still fail to build and the new proof patches require ShellCheck and kernel validation.
