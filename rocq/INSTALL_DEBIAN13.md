# Installing Rocq 9.2.0 on Debian 13 (computer10)

**AI disclosure:** This installation guide and the referenced Python utility were
drafted with AI assistance. The automated checks described below are not a
substitute for reviewing the generated opam command plan before execution.

The repository's GitHub Actions workflow builds proofs with
`rocq/rocq-prover:9.2.0`. Debian's `/usr/bin/coqc` is not an equivalent
test of whether the Rocq 9.2 `rocq` command is installed.

## Prerequisites

The installer requires an **initialized opam installation** and Python 3 with
Deal 4.24.6. On Debian 13, the compiler prerequisites can be installed with:

```sh
sudo apt update
sudo apt install -y opam build-essential m4 pkg-config python3-venv
```

A user who can already run `opam switch list` does not need to reinitialize
opam. Do not run the Python installer with `sudo`; it works in the user's
opam directory.

## Run from an existing repository checkout

```sh
cd ~/src/composite_iq_checked_claims
python3 -m venv .venv
.venv/bin/python -m pip install 'deal==4.24.6'
.venv/bin/python scripts/install_rocq_opam.py --dry-run
.venv/bin/python scripts/install_rocq_opam.py
```

If the checkout is located elsewhere, use its actual directory. Review the
dry-run output before running the installation command. The dry-run assumes
an initial installation and **does not contact opam or change files**.

The script installs the requested `rocq-core=9.2.0` and `rocq-prover`
into a dedicated switch, `rocq-9.2`, using the official released Rocq
package repository. It uses OCaml 4.14.2 and leaves the existing
`icar16-colibri2` and `default` switches selected and unmodified. A
re-run detects an existing target switch and avoids trying to recreate it.

## Confirm installation and compile proofs

```sh
opam exec --switch=rocq-9.2 -- rocq --version
opam exec --switch=rocq-9.2 -- rocq doc --help

cd rocq
opam exec --switch=rocq-9.2 -- rocq compile FiniteSum.v
```

For a complete ordered compilation, consult
[the existing Rocq workflow](../.github/workflows/rocq-proofs.yml).
The tool uses explicit `--switch=rocq-9.2` flags and does not require
evaluating opam environment changes in Bash.

## Test safely without installing Rocq

```sh
bash scripts/test_rocq_opam_installer.sh
```

This test checks all four switch/repository-presence combinations, rejects
incorrect input types through the active Deal preconditions, verifies the
non-mutating dry run, and uses a fake `opam` executable to test first and
repeated installations. It does not download Rocq or call the real opam.

The test runner automatically selects `.venv/bin/python` when available,
so it uses the Deal installation in the checkout's virtual environment even
if that environment has not been activated in Bash. When no `.venv` exists,
it falls back to `python3`. To select a different interpreter explicitly:

```sh
ROCQ_TEST_PYTHON=/path/to/python bash scripts/test_rocq_opam_installer.sh
```

A missing Deal dependency produces a diagnostic rather than an unexplained
`ModuleNotFoundError`. Successful installer execution has already been
confirmed on computer10 using the switch-specific `rocq --version` command.

## Scope and known limits

This is an opam installer, not a proof checker. Its Deal contracts verify
the planned argument vectors, explicit Rocq version, switch isolation,
order, and idempotent handling of optional commands. They do **not** prove
that external package repositories, compilers, or binaries are secure.
The actual Rocq proof compilation remains an independent verification step.

## AI disclosure — full statement

The installer, its contract design, these instructions, and the mock tests
were drafted with OpenAI assistance on November 14, 2026. The requester
specified the target repository, computer10, desired version compatibility,
and the requirement of at least ten substantive Deal contracts per Python
function. A Python syntax check and stub-assisted mock-opam shell tests were
run during drafting. Those checks did not run the real Deal package or build
Rocq in the drafting environment. GitHub Actions and the user's real
installation must be evaluated independently. AI authorship does not
constitute independent human review or formal verification of package
management side effects.
