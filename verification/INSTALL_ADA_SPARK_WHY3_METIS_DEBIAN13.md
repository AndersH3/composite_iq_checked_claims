# Ada/SPARK, Gappa, Metis and Why3 backends on Debian 13

**AI DISCLOSURE — This installation guide, shell script, and regression checks were prepared with OpenAI assistance. They have not been executed on computer10 by the assistant.** Before using privileged package installation, review the exact package list and the effects of every opt-in action.

## Purpose and host separation

Target: `computer10`, Debian 13 (Trixie), Linux x86_64. This complements the existing Rocq 9.2, Lean 4.35.0, Yices 2, PVS, Isabelle2026 and COLIBRI2 setup. The Isabelle download may be running in a detached process: **do not interrupt it**. Installing packages while it downloads could compete for disk space and network resources.

Use [`scripts/install_ada_spark_why3.sh`](../scripts/install_ada_spark_why3.sh). The script is non-mutating unless an explicit install/build flag is supplied. It **does not touch any opam switch**. Debian's `metis` is a graph partitioner — it must **not** be installed for the Joe Hurd theorem prover.

## Contents and sourcing

| Component | Source | Version/status | Install mechanism |
|---|---|---|---|
| GNAT Ada compiler | Debian Trixie `gnat` | GNAT 14 | apt, opt-in |
| GPRbuild and GPR project tools | Debian `gprbuild` | 2025.0.0 | apt, opt-in |
| Alire `alr` | Debian `alire` | 1.2.1 | apt, opt-in |
| Debuggers and build tools | Debian `gdb gcc g++ make git perl` | distribution versions | apt |
| Gappa floating-point theorem prover | Debian `gappa` | 1.6.0 | apt |
| Why3 verification platform | Debian `why3` | 1.8.0 | apt |
| Additional SMT/ATP solvers | Debian `z3`, `cvc5`, `eprover` | distribution versions | apt |
| Why3 examples | Debian `why3-examples` | distribution version | apt |
| GNATprove SPARK checker | Alire crate `gnatprove` | currently 16.1.0 in the Alire index | user-prefix installation |
| Joe Hurd Metis theorem prover | [gilith/metis](https://github.com/gilith/metis) | pinned development commit `7a23e4ea68bc92927716777ebc98bea09e91fe24` | separate source checkout; build requires Standard ML compiler |

**Two similarly named products:** Metis from `gilith/metis` is a first-order resolution theorem prover for TPTP problems. The Debian binary package `metis` is an entirely unrelated graph partitioner. The script never requests the Debian `metis` package.

The pinned development snapshot is *not* claimed to be the official Metis 2.4 release tarball. The official release is Metis 2.4 (20260920), but only a source archive was identified without a vendor-published checksum. The script therefore checks out an exact Git commit and checks its SHA before attempting to build. A pinned Git object is not independent code auditing.

## User commands on computer10

From the existing formal-tools checkout (no new clone is necessary):

```sh
cd ~/src/composite_iq_formal_tools
git pull --ff-only
bash scripts/test_ada_spark_why3.sh
bash scripts/install_ada_spark_why3.sh --plan
```

The `--plan` command prints the proposed packages and performs **no installation**.

To install the apt profile when you want to authorize system changes:

```sh
bash scripts/install_ada_spark_why3.sh --install-apt
```

This runs `sudo apt-get install --no-install-recommends` on the explicit manifest, after checking candidate availability. It prompts for authorization. It does not add repositories, perform a full system upgrade or install the similarly named graph-partitioning package.

To check that GNAT can compile, link and run a minimal standalone
Ada program without modifying the repository, run:

```sh
bash scripts/install_ada_spark_why3.sh --smoke-ada
```

This uses a disposable directory under `/tmp` and removes it after
completion. Successful compilation of this Ada test is **not** evidence
that any particular SPARK verification conditions have been discharged.

To obtain GNATprove in a **separate user prefix**:

```sh
bash scripts/install_ada_spark_why3.sh --install-spark
```

The command invokes `alr install --prefix="$HOME/.local/opt/ada-spark" gnatprove`. GNATprove is not included in Debian's `gnat` package and must be acquired separately. If Alire detects an incompatible compiler or unavailable dependency, stop and inspect its diagnostic; do not assume installation succeeded.

For **project-specific SPARK checking**, go to an Alire crate containing your Ada/SPARK code, run `alr with gnatprove`, and then `alr gnatprove`. Work through the GNATprove warnings and proof-obligation reports, rather than treating a tool's `--version` output as evidence that source-level contracts are established. Depending on your setup, use `alr gnatprove --mode=all` or `gnatprove -Pproject.gpr --mode=all`; verify the flags of the installed release.

To obtain the correct Metis theorem-prover source, not Debian's unrelated package:

```sh
bash scripts/install_ada_spark_why3.sh --metis-source
```

This checks out an immutable Git revision under `~/.local/src/metis-pinned` and verifies its identity. Building is **not** attempted until you explicitly request it:

```sh
bash scripts/install_ada_spark_why3.sh --metis-build
```

Metis requires **MLton**, **Poly/ML**, or **Moscow ML**, along with Make and Perl. As of this assessment, MLton and Poly/ML cannot be assumed to be in the Debian 13 stable repositories. The script fails with a clear message if none of those compilers is present; it does not enable Debian testing/unstable repositories or substitute SML/NJ. Once a supported ML compiler is independently installed, `--metis-build` runs the developer-provided build target and locates the `metis` executable. Test it with a TPTP problem and inspect output rather than mistaking the source checkout for a successful build.

Finally, enumerate the detected tools and register compatible external provers with Why3:

```sh
bash scripts/install_ada_spark_why3.sh --detect
```

Debian's Why3 1.8 and upstream Why3 1.9 use different `config` syntax; the script inspects local help and selects the syntax available. After adding Yices, Metis, Gappa, PVS or other provers, repeat configuration detection. If a prover cannot be detected, check compatibility with Why3's supported versions; do not claim it is usable merely because the binary is on `PATH`.

## Further Ada/SPARK facilities

For a broader development workflow, consider the Ada Language Server (AdaCore's VS Code Ada extension), GNAT Studio, GNATformat, GNATtest, GNATcov, GNATdoc, gnatcheck and Libadalang. Some are in the [Alire package index](https://alire.ada.dev/crates.html) and some have separate AdaCore community releases. They are **optional** and are not silently downloaded or installed by the base script. Record each available version and license before using it in reproducible project checks.

For Why3, further candidates include Alt-Ergo, veriT, Vampire and SPASS. Availability and exact compatibility require separate checks. In particular, do not install the Debian `ergo` quantum-chemistry package while looking for the *Alt-Ergo* SMT prover.

## Validation limits

The offline test `bash scripts/test_ada_spark_why3.sh` validates shell syntax, command-plan outputs, negative controls for the wrong Metis package, and the absence of prohibited automatic changes. GitHub Actions runs that test as part of its existing Python-contracts workflow, alongside the separate Deal coverage and runtime-test gates.

The user's computer has not been operated remotely by the assistant. Installation, real compiler execution, SPARK proof closure, Metis build success, and Why3 backend acceptance are **not confirmed** until the appropriate commands have run on computer10. Runtime success is distinct from a formal proof of software correctness.

## Provenance

- [Why3 external provers](https://why3.org/#provers) and [Why3 configuration manual](https://why3.org/doc/manpages.html).
- [Debian Trixie packages](https://packages.debian.org/trixie/) for GNAT, GPRbuild, Gappa, Why3, Alire, cvc5, Z3, E prover, and build utilities.
- [Alire GNATprove crate](https://alire.ada.dev/crates/gnatprove) and [AdaCore community transition guide](https://alire.ada.dev/transition_from_gnat_community.html).
- [Official Metis release page](https://www.gilith.com/software/metis/) and [Metis development checkout](https://github.com/gilith/metis).

## Appendix — Full AI disclosure

OpenAI assisted in identifying toolchain variants, researching package repositories and vendor pages, composing the Bash installation and test scripts, writing the guide, and committing repository changes through the connected GitHub integration. The requested target was Debian 13 on computer10. The user previously reported installed Rocq, Lean, Yices and PVS facilities and an in-progress detached Isabelle transfer, but no AI-initiated installation was carried out on their host. Source locations and release information were checked against public vendor and Debian records on November 15, 2026; remote inventories and future package updates may differ. The installer offers explicit mutating actions requiring invocation by the user; its tests are offline and do not validate live downloads, the validity of third-party proofs, vendor build-chain trust, or SPARK proof closure. The source checkout for Metis is a pinned development commit, **not** a verified official Metis binary release. GNATprove's Alire crate is community software and may differ from commercial SPARK Pro. Formal claims made in project reports require separately recorded reproducible compilation, proof success, and a proof-status audit on the actual source revision.
