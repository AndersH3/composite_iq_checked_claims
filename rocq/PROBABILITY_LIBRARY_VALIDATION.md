# Isolated probability-library verification on computer10

**Researcher/requester:** Anders Hellström. **AI disclosure:** AI-assisted reproduction instructions. No successful probability-library build is claimed until the kernel accepts the exact source.

The existing switch named rocq-9.2 has Rocq 9.3.0 core/runtime and Stdlib 9.2.0. Preserve it, as well as the Polytris switch. Use a new named switch rather than changing the global selection or relying on Docker. The following are interactive shell commands, not a new executable script. Repository shell utilities must pass ShellCheck before execution.

## 1. Pin the compiler and MathComp-Analysis

From the project checkout:

~~~bash
cd ~/src/composite_iq_verification
git pull --ff-only
export PROJECT="$PWD"
export LOGDIR="$HOME/validation-logs/composite-probability-$(date +%Y%m%d-%H%M%S)"
mkdir -p "$LOGDIR"
set -o pipefail

opam switch create gaussian-rocq-9.2 ocaml-base-compiler.4.14.2 --no-switch
opam repository add --switch=gaussian-rocq-9.2 rocq-released https://rocq-prover.org/opam/released
opam update
# Install the legacy command shims FIRST. Older upstream Makefiles
# otherwise prefer Debian's system coqtop/coq_makefile/coqdep.
opam install --switch=gaussian-rocq-9.2 -y \
  rocq-core.9.2.0 rocq-runtime.9.2.0 rocq-stdlib.9.2.0 coq-core.9.2.0
opam exec --switch=gaussian-rocq-9.2 -- coqc --version
opam install --switch=gaussian-rocq-9.2 -y -j 3 \
  rocq-core.9.2.0 rocq-runtime.9.2.0 rocq-stdlib.9.2.0 \
  coq-core.9.2.0 rocq-mathcomp-analysis.1.18.0 \
  2>&1 | tee "$LOGDIR/mathcomp-install.log"
~~~

If the switch already exists, do not recreate it. Check its installed versions before proceeding. If the solver rejects the exact versions, preserve the output instead of relaxing the pins.

### Recovery of the partially installed switch (November 26, 2026)

The first installation on computer10 installed Rocq 9.2.0 and MathComp 2.6.0, but Finmap 2.2.4 and Bigenough 1.0.4 could not resolve HB.structures or mathcomp.ssreflect, respectively. The subsequent Gaussian compile could not import mathcomp.classical_sets because MathComp-Analysis was never installed. The upstream Makefile.common files at finmap 2.2.4 and bigenough 1.0.4 choose legacy commands before falling back to rocq. The subsequent computer10 transcript confirms the repair: installing coq-core.9.2.0 put rocq, coqc, coqtop, coq_makefile and coqdep in the isolated switch, both previously failing dependencies built successfully, and Analysis 1.18.0 installed. The later file-not-found error was caused by unset shell variables after reconnecting over SSH, not by a proof or dependency failure.

Install the compatibility package as above, then verify the selected binaries and library paths:

~~~bash
opam exec --switch=gaussian-rocq-9.2 -- which rocq coqc coqtop coq_makefile coqdep
opam exec --switch=gaussian-rocq-9.2 -- coqc --version
opam exec --switch=gaussian-rocq-9.2 -- coqc -where
opam exec --switch=gaussian-rocq-9.2 -- rocq compile -where
~~~

The executable paths must be in the isolated switch, not /usr/bin or a different opam switch. Retry the two failed dependencies after verifying this:

~~~bash
opam install --switch=gaussian-rocq-9.2 -y -j 2 \
  rocq-core.9.2.0 rocq-runtime.9.2.0 rocq-stdlib.9.2.0 coq-core.9.2.0 \
  rocq-mathcomp-finmap.2.2.4 rocq-mathcomp-bigenough.1.0.4 \
  2>&1 | tee "$LOGDIR/mathcomp-dependency-retry.log"
~~~

Only after both succeed, resume installation of Analysis with the compiler pins above. Do not edit the system Coq installation, create manual symlinks, or delete the successful partial switch. If either build still fails, retain the full corresponding opam .out and .env logs. The official compatibility package is documented at https://opam.ocaml.org/packages/coq-core/coq-core.9.2.0/.

### Compile after successful installation (including after a fresh SSH login)

Reinitialize these variables on every new SSH connection. They do not persist between shells. In particular, an empty LOGDIR must never be used to construct a log path.

~~~bash
cd "$HOME/src/composite_iq_verification" &&
export PROJECT="$PWD" &&
export LOGDIR="$HOME/validation-logs/composite-probability-$(date +%Y%m%d-%H%M%S)" &&
mkdir -p "$LOGDIR/mathcomp"
set -o pipefail

opam exec --switch=gaussian-rocq-9.2 -- rocq --version
opam list --switch=gaussian-rocq-9.2 --installed
cp "${PROJECT:?Reinitialize PROJECT}/analyses/sequential-conditional-means/mathcomp/GaussianPosteriorMeasure.v" \
  "${LOGDIR:?Reinitialize LOGDIR}/mathcomp/" &&
cd "$LOGDIR/mathcomp" &&
opam exec --switch=gaussian-rocq-9.2 -- \
  rocq compile GaussianPosteriorMeasure.v \
  2>&1 | tee "$LOGDIR/mathcomp-kernel.log"
~~~

On November 27, 2026, computer10 compiled the exact six-theorem MathComp module at revision `9f5a5508fcb0e5fc8b079fe4090c10aa0a7ef0e1` using Rocq 9.2.0 and MathComp-Analysis 1.18.0. The researcher supplied the successful terminal transcript (exit status 0, GaussianPosteriorMeasure.vo, 75 KiB). All six theorem scripts passed, including the centered residual density, scalar observation/residual density factorization and marginal observation measure. This is local kernel evidence, not a successful GitHub Actions run or a proof of full multivariate Gaussian residual independence. The six scripts are tracked separately from the 3,699 canonical Stdlib proof scripts; the three previously verified posterior results must not be double-counted.

On November 27, 2026, the researcher supplied the full independent `rocq check GaussianPosteriorMeasure` transcript for the previously compiled module at source revision `9f5a5508fcb0e5fc8b079fe4090c10aa0a7ef0e1`. The checker traversed the imported dependency closure and explicitly checked all six project theorem constants, ending with `Modules were successfully checked`. This is independent compiled-object verification, not a transitive assumption audit or a GitHub Actions success. The subsequent FormalML checkout at `8ee433dc802fca35f6bceb6dacb69d3c1315e886` succeeded. Its opam dry-run proposed exactly four additions: conf-clang 2, coq-coquelicot 3.4.5, coq-ext-lib 0.13.1, coq-mathcomp-ssreflect 2.6.0, with no removals or version changes. The displayed installations were simulated; actual dependency installation and FormalML compilation remain pending.

The zero-scale fallback of the pinned normal density is not a Dirac measure. No full multivariate independence claim follows from a successful build.


## 2. FormalML separately

Only proceed after the MathComp result is recorded. If reconnecting over SSH, rerun the PROJECT and LOGDIR initialization above before using these commands. FormalML at upstream commit 8ee433dc802fca35f6bceb6dacb69d3c1315e886 needs a large compatibility patch. Use its own worktree in the validation directory and the pinned dependency metadata. Keep the exact Rocq version fixed. Preview the dependency solution first, preserving the successful MathComp installation. Use a separate switch if opam proposes changing or removing any installed package.

~~~bash
cd "$PROJECT"
git ls-files -z '*.sh' | xargs -0 -r shellcheck --severity=warning
~~~

If ShellCheck passes:

~~~bash
cd "$LOGDIR"
git clone --no-checkout https://github.com/IBM/FormalML.git FormalML
cd FormalML
git checkout --detach 8ee433dc802fca35f6bceb6dacb69d3c1315e886

opam install --switch=gaussian-rocq-9.2 --dry-run --deps-only . \
  rocq-core.9.2.0 rocq-runtime.9.2.0 rocq-stdlib.9.2.0 coq-core.9.2.0 \
  2>&1 | tee "$LOGDIR/formalml-dependency-plan.log"
~~~

Only if the preview succeeds and proposes no upgrades, downgrades or removals of existing packages, install. A dry-run does not actually install packages even if its output says installed. The November 27 preview meets this criterion. The following pins retain the four previewed versions and the verified Analysis release:

~~~bash
opam install --switch=gaussian-rocq-9.2 -y -j 2 \
  rocq-core.9.2.0 rocq-runtime.9.2.0 rocq-stdlib.9.2.0 coq-core.9.2.0 \
  rocq-mathcomp-analysis.1.18.0 conf-clang.2 coq-coquelicot.3.4.5 \
  coq-ext-lib.0.13.1 coq-mathcomp-ssreflect.2.6.0 \
  2>&1 | tee "$LOGDIR/formalml-dependencies.log"
opam list --switch=gaussian-rocq-9.2 --installed
~~~

If successful, run the previously ShellCheck-validated compatibility utility once on the pristine checkout:

~~~bash
sh "$PROJECT/scripts/patch_formalml_9_2.sh" \
  2>&1 | tee "$LOGDIR/formalml-patch.log"

opam exec --switch=gaussian-rocq-9.2 -- make Makefile.rocq
opam exec --switch=gaussian-rocq-9.2 -- make -k -j 2 -f Makefile.rocq \
  rocq/ProbTheory/ConditionalExpectation.vo \
  rocq/ProbTheory/ProductSpace.vo \
  2>&1 | tee "$LOGDIR/formalml-library.log"
~~~

If both required library targets pass:

~~~bash
mkdir -p "$LOGDIR/formalml-gaussian"
cp "$PROJECT"/analyses/sequential-conditional-means/formalml/*.v "$LOGDIR/formalml-gaussian/"
cd "$LOGDIR/formalml-gaussian"
opam exec --switch=gaussian-rocq-9.2 -- \
  rocq compile -R "$LOGDIR/FormalML/rocq" FormalML GaussianResidualConditionalExpectation.v \
  2>&1 | tee "$LOGDIR/formalml-residual.log"
~~~

Only if the residual module compiles:

~~~bash
opam exec --switch=gaussian-rocq-9.2 -- \
  rocq compile -R "$LOGDIR/FormalML/rocq" FormalML GaussianProductConditionalExpectation.v \
  2>&1 | tee "$LOGDIR/formalml-product.log"
~~~

Retain logs outside the Git checkout. These instructions use upstream probability modules rather than a custom conditional-expectation implementation. The current large compatibility patch may fail; preserve the first actual error and do not bypass any proof.

### Successful incremental FormalML build and independent verification (November 27, 2026)

The researcher supplied successful computer10 compilation logs for the residual module at `2a77faa` and product module at `26342d8` after applying D195 to the pinned upstream checkout. All nine individual Print Assumptions commands completed; the exact per-theorem inherited axiom matrix is in [CONTINUATION_20261126.md](CONTINUATION_20261126.md). Both compiled modules and their imported closure passed independent rocq check at `bc76b21`. The combined audit process was subsequently killed; the transcript does not establish why. The split assumption-only audits reproduce the earlier successful procedure in separate Rocq processes.

Reuse the existing working validation directory. Do not reapply D195. With PROJECT and LOGDIR initialized:

~~~bash
cp "$PROJECT"/analyses/sequential-conditional-means/formalml/Audit{Residual,Product}Assumptions.v \
  "$LOGDIR/project-gaussian/" &&
cd "$LOGDIR/project-gaussian" &&
set -o pipefail &&
opam exec --switch=gaussian-rocq-9.2 -- \
  rocq compile -R "$LOGDIR/FormalML/rocq" FormalML AuditResidualAssumptions.v \
  2>&1 | tee "$LOGDIR/gaussian-residual-assumptions-r2.log" &&
opam exec --switch=gaussian-rocq-9.2 -- \
  rocq compile -R "$LOGDIR/FormalML/rocq" FormalML AuditProductAssumptions.v \
  2>&1 | tee "$LOGDIR/gaussian-product-assumptions-r2.log"
~~~

The next candidate ProductLawIndependence.v can be compiled separately using the same -R mapping. A clean reproduction must use a fresh upstream checkout and apply the entire patch once. The split audit and clean CI results must be assessed independently from the local incremental build.

### Verified joint-law factorization bridge (November 27, 2026)

Both split audits passed at `30fbbc1`. ProductLawIndependence.v at `e17d8c6` passed compilation, assumption audit and independent kernel check; see the continuation record for exact timings and memory usage. The three original-space regression candidates in JointLawConditionalExpectation.v reuse this theorem and the earlier generic CE results. Compile that new module after the existing residual and product-law modules. Use AuditJointLawConditionalExpectation.v in a separate process and rocq check on the compiled module. The tracked AuditProductLawIndependence.v reproduces the already successful audit. The CI workflow now includes both bridges; clean CI and validation of the three new targets remain pending.

### Original-space conditional expectation independently verified

At `a7f2139` all three JointLawConditionalExpectation.v targets compiled and were independently kernel-checked and assumption-audited; see the continuation record. No new project-specific assumptions were reported; the inherited axiom set union remains 12. The compiled total is now 3725 across canonical, MathComp and FormalML lanes. The new MathComp GaussianResidualMeasure.v candidates reuse the compiled GaussianPosteriorMeasure.v, the pinned Analysis 1.18.0 library and its existing Lebesgue measure and pushforward integration machinery. Compile in a separate MathComp working directory with the same verified Rocq 9.2 switch, after compiling GaussianPosteriorMeasure.v there if needed. Do not reapply D195. Pinned upstream FormalML Gaussian.v contains Fubini axioms and is not imported by these new candidates. Joint Gaussian law identification and cross-library representation are still open.

### Verified MathComp residual measure R7 and original-coordinate continuation

At `be11a25` all four GaussianResidualMeasure.v targets passed compilation, assumption auditing and independent checking. Each depends only on the three inherited boolp axioms listed in CONTINUATION_20261126.md. The six earlier posterior targets were independently rechecked, but their own transitive audit remains pending. Pinned CI now checks both verified modules and runs their separate audits. Compile GaussianOriginalResidualMeasure.v after the already compiled GaussianResidualMeasure.vo; separately compile AuditGaussianOriginalResidualMeasure.v and independently check the candidate module if compilation succeeds. AuditGaussianPosteriorMeasure.v audits the earlier six targets without recompiling them. The new candidates remain unverified. Combined compiled inventory: 3729. No upstream Gaussian Fubini axioms are imported.

At `9dc8cf3` the separate posterior audit passed for all six targets, with precisely the same three boolp assumptions as the four residual-measure targets. All ten MathComp results are now independently kernel-checked and assumption-audited. Original-coordinate R1 failed at line 65 due to the enclosing extended-real scope affecting real subtraction; correction `3a41add` uses direct congruence of the already verified centering equality. Recompile only the original-coordinate module and, on success, its separate audit and independent check.

At `c80def4`, the original-coordinate module passed both targets, their separate three-axiom audits and independent checking of all twelve MathComp targets. Combined compiled inventory 3731; all 25 probability-library targets independently checked and audited. Pinned CI now includes the three validated MathComp modules and their separate audits. New GaussianJointDensityMeasure.v candidates construct a measure via nonnegative density integration and identify event mass through Tonelli; compile and audit separately. They are not yet counted, and joint probability normalization and residual pushforward identification remain unproved.

At `8782dca` GaussianJointDensityMeasure.v passed all seven targets, transitive assumption auditing (three inherited boolp axioms each), and independent kernel checking, including the HB measure registration. Combined compiled inventory 3738; all 32 probability-library targets independently checked and audited. Pinned CI includes the four validated MathComp modules and separate audits. GaussianResidualPushforward.v adds six candidate results for actual scalar residual pushforward, normalization and product measure uniqueness. Compile the new module, its audit and independent check separately; the six unvalidated candidates are excluded from the validated inventory and CI compile list. No new Gaussian independence axiom is introduced.
