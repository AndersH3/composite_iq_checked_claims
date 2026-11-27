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

Use the exact six-theorem candidate file; the zero-scale fallback of the pinned normal density is not a Dirac measure. No full multivariate independence claim follows from a successful build.

## 2. FormalML separately

Only proceed after the MathComp result is recorded. If reconnecting over SSH, rerun the PROJECT and LOGDIR initialization above before using these commands. FormalML at upstream commit 8ee433dc802fca35f6bceb6dacb69d3c1315e886 needs a large compatibility patch. Use its own worktree in the validation directory and the pinned dependency metadata. Keep the exact Rocq version fixed. A separate switch may be needed if dependency solving conflicts with MathComp-Analysis.

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

opam install --switch=gaussian-rocq-9.2 -y -j 2 --deps-only . \
  rocq-core.9.2.0 rocq-runtime.9.2.0 rocq-stdlib.9.2.0 coq-core.9.2.0 \
  2>&1 | tee "$LOGDIR/formalml-dependencies.log"
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
