# Ada/SPARK, Gappa, Metis and Why3 backends on Debian 13

**AI DISCLOSURE — This installation guide, shell script, and regression checks were prepared with OpenAI assistance. They have not been executed on computer10 by the assistant.** Before using privileged package installation, review the exact package list and the effects of every opt-in action.

## Purpose and host separation

Target: `computer10`, Debian 13 (Trixie), Linux x86_64. This complements the existing Rocq 9.2, Lean 4.35.0, Yices 2, PVS, Isabelle2026 and COLIBRI2 setup. An official Isabelle2026 archive has now been downloaded, verified, and extracted on computer10; verify the launcher before calling its installation operational.

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
| GNATprove SPARK checker | [Official GNAT-FSF-builds release](https://github.com/alire-project/GNAT-FSF-builds/releases/tag/gnatprove-16.1.0-1), SHA-256 from upstream Alire index | 16.1.0, Linux x86-64 | 473 MB user-local vendor download; no Alire-version upgrade |
| Joe Hurd Metis theorem prover | [gilith/metis](https://github.com/gilith/metis) | pinned development commit `7a23e4ea68bc92927716777ebc98bea09e91fe24` | separate source checkout; build requires Standard ML compiler |

**Two similarly named products:** Metis from `gilith/metis` is a first-order resolution theorem prover for TPTP problems. The Debian binary package `metis` is an entirely unrelated graph partitioner. The script never requests the Debian `metis` package.

The pinned development snapshot is *not* claimed to be the official Metis 2.4 release tarball. The official release is Metis 2.4 (20260920), but only a source archive was identified without a vendor-published checksum. The script therefore checks out an exact Git commit and checks its SHA before attempting to build. A pinned Git object is not independent code auditing.

## Observed computer10 results (November 15, 2026)

The user's terminal output confirms that `gnat` 14.1, `gprbuild`
2025.0.0-4, `alire` 1.2.1, GDB, GCC/G++, Make, Git, Perl, Gappa 1.6.0,
Why3 1.8.0, Z3, and CVC5 were installed already. The apt action installed
`eprover` 3.2.5, `picosat` 965, and `why3-examples` 1.8.0. However,
the attempted GNATprove installation stopped immediately with
`error: Unrecognized command: install`; no GNATprove download or
functional SPARK proof-check was confirmed.

The user's separately submitted `why3 config --detect` command also
reported `unrecognized option '--detect'`. The fixed installer avoids both
unsupported invocations. These are observed host facts, not test results from
the GitHub Actions runner.

### New computer10 installation results: Ada and Isabelle

The user ran `bash scripts/install_ada_spark_why3.sh --smoke-ada` and
obtained `Ada compiler smoke test succeeded`. GNAT's compilation,
link, and execution are therefore confirmed for that minimal Ada file.

The detached Isabelle2026 installer reported the completed download
of **1,412,134,191 bytes**, a passing published SHA-256 check
(`858c995b32216b3876bf395c3be843147d1f1eee404bc6c958d7534ee335e48d`),
and successful extraction under
`~/.local/opt/formal-provers/isabelle-2026/Isabelle2026/`.
The installer lock was released. The exact discovered launcher was:

```text
/home/anonymous/.local/opt/formal-provers/isabelle-2026/Isabelle2026/bin/isabelle
```

For a runtime version check (without changing global `PATH`), run:

```sh
"$HOME/.local/opt/formal-provers/isabelle-2026/Isabelle2026/bin/isabelle" version
```

This version check has not yet been reported by the user; archive
verification and successful extraction are not proof that the runtime
works for Isabelle theories.

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

**Correction for Debian 13 (Alire index compatibility):** The user's
Debian Alire is **1.2.1** and has no `install` subcommand. The initial
`alr install` attempt therefore failed. The next attempted command,
`alr -n get gnatprove=16.1.0`, also failed with *Release ... does not
exist in the catalog.* The official community index has GNATprove
13.2.1 on branch `stable-1.2.1` (for Alire 1.2.1), but GNATprove
16.1.0 appears only in the newer `stable-1.4.0` index.

The corrected `--install-spark` action downloads **the original vendor
binary archive referenced by the official newer Alire index** rather
than modifying Debian's `alire` or its index. The release asset is
`gnatprove-x86_64-linux-16.1.0-1.tar.gz` (472,919,963 bytes).
Its independently pinned manifest SHA-256 is

```text
82528bef29857e239373fcc36732837d743f5a00805d502c70455422ffc97191
```

The installer downloads to a persistent `.partial` file and can
resume after an interrupted transfer on the next explicit invocation;
it checks both the size and SHA-256 **before extraction**,
uses a temporary extraction directory and installs under
`~/.local/opt/ada-spark/gnatprove-16.1.0`. It creates the user-local
wrapper `~/.local/opt/ada-spark/bin/gnatprove` after finding a unique
vendor executable, adds only that bundle's `bin` to the child process
`PATH`, and verifies the version invocation. A 473 MB archive may
require substantial additional temporary disk space. Installation
remains opt-in. A package checksum is an integrity measure, not
independent auditing of the third-party binaries.

Upstream sources: [GNAT-FSF-builds release](https://github.com/alire-project/GNAT-FSF-builds/releases/tag/gnatprove-16.1.0-1),
[stable-1.2.1 index](https://github.com/alire-project/alire-index/tree/stable-1.2.1/index/gn/gnatprove),
and [stable-1.4.0 GNATprove manifest](https://github.com/alire-project/alire-index/blob/stable-1.4.0/index/gn/gnatprove/gnatprove-16.1.0.toml).

To query the GNATprove launcher after installation:

```sh
~/.local/opt/ada-spark/bin/gnatprove --version
```

GNATprove is not included in Debian's `gnat` package. This direct vendor download requires network access and sufficient free space but **does not require an updated Alire index**. If it fails, retain the diagnostics; do not claim GNATprove was installed. The Debian GNAT 14 compiler may also be too old for some GNATprove 16/SPARK workflows; verify actual SPARK proof execution rather than equating a successful `--version` probe with toolchain compatibility.

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

**Correction for Debian Why3 1.8.0:** use `why3 config detect`, followed
by `why3 --list-provers`. The previous recommendation to run
`why3 config --detect` failed because it is not a recognized option in
this package. The corrected script issues the documented Debian 13 commands
directly. After adding Yices, Metis, Gappa, PVS or other provers, repeat configuration detection. If a prover cannot be detected, check compatibility with Why3's supported versions; do not claim it is usable merely because the binary is on `PATH`.

## Why3 1.8.0 prover compatibility observed on computer10

On November 15, 2026, the user's `why3 config detect` output reported
**CVC5 1.1.2** and **Z3 4.13.3** as recognized. It also reported six
provers with unrecognized versions among the 13 configurations added.
In particular, the installed Why3 drivers did not recognize **Gappa
1.6.0**, **Eprover 3.2.5**, **Beagle 5.5**, or **Yices 2.7.0**.
The installed Yices detection entry explicitly expects **Yices 1.0.38**;
Yices 2.x is a different major version, not a straightforward match.
Why3 also detected **Isabelle 2025-2**, **PVS 8.1**, and **Coq 8.20.1**,
but reported no compiled Why3 proof-assistant libraries for them.

These messages are **version/driver integration warnings**, not
evidence that the independently installed solvers or proof assistants
are defective. Their registrations in `~/.why3.conf` are not sufficient
for validated Why3 use. Do not suppress the warnings or rewrite
`~/.why3.conf` to pretend unsupported drivers are supported.
Note that `Isabelle 2025-2` is only the version detected in the user's
PATH; it does **not** establish that the separately downloaded
Isabelle2026 package is installed or accessible to Why3.

### Why3 1.8 prover-selection ambiguity: computer10 follow-up

The user ran `bash verification/why3/check_backends.sh` on computer10.
The first Z3 invocation failed **before executing the proof** with:

```text
More than one prover in /home/anonymous/.why3.conf correspond to "Z3":
Z3 4.13.3, Z3 4.13.3 (counterexamples), Z3 4.13.3 (noBV)
```

Why3's `-P` selector accepts `name,version,alternative`; the *trailing
comma* denotes the empty, default alternative. The corrected script pins
the configurations `Z3,4.13.3,` and `CVC5,1.1.2,` and leaves
`~/.why3.conf` unchanged. A mock regression rejects the abbreviated
prover name rather than passing it to a solver; proof results themselves
still require actual execution on computer10. If versions change, use
`why3 --list-provers` to inspect the available configurations instead
of silently selecting a different version.

### Why3 1.8 multiline proof-result parser correction

On computer10, the corrected fully qualified selector
`Z3,4.13.3,` successfully invoked Z3 for `TrueGoal`. Why3 returned:

```text
Goal TrueGoal.
Prover result is: Valid (0.00s, 18 steps).
```

That result **establishes the positive Z3 smoke test passed on the real
host**, but the previous shell audit mistakenly expected a *single-line*
`TrueGoal: Valid` status; it therefore stopped before the negative
control or any CVC5 check. The corrected audit explicitly matches the
goal header and prover-result line separately, requires exactly one of
each, and confirms the intended `Valid` or `Invalid` outcome.
The offline regression now reproduces the actual multiline text and
rejects unknown, falsely valid, and wrong-goal replies.

To run the corrected smoke test on computer10:

```sh
cd ~/src/composite_iq_formal_tools
git pull --ff-only
bash scripts/test_ada_spark_why3.sh
bash verification/why3/check_backends.sh
```

Only when the final script runs to completion and prints two PASS
messages can both backends be marked verified for these small controls.

### False-goal result on computer10: Unknown (sat)

On November 15, 2026, the user ran the smoke test on the actual Why3
1.8.0 / Z3 4.13.3 environment. The positive control returned
`Valid (0.00s, 18 steps)`. The negative control returned:

```text
Goal FalseGoal.
Prover result is: Unknown (sat) (0.00s, 11 steps).
```

The Why3 CLI also returned a nonzero exit code for that unproved goal,
which the earlier smoke script incorrectly interpreted as a failed
solver invocation. **This is not a proof of the false goal**. The
`sat` annotation is encouraging for a false-goal check, but Why3's
formal result category is `Unknown`, so it must not be renamed
`Invalid`. The corrected script distinguishes this exact observed
outcome from other `Unknown` messages, and from an erroneously reported
`Valid`. CVC5 has not yet been tested by the user in this sequence.

The user's later run showed `Unknown (sat)` and **exit code 2**, which
the intermediate script still rejected. The offline tests also failed on
CI because the fake Why3 had exit code 1 and a stale error-message
assertion; the user observed the offline test exit silently with no pass
message. The correction changes the fake to exit 2, explicitly checks
failure modes 0/1/124, updates the message assertion, and makes any
future assertion failure report a source line number.

### Confirmed computer10 Z3/CVC5 backend smoke results

The user subsequently ran the corrected test on Debian 13 with
Why3 1.8.0 and reported exit status **0**. Both registered SMT backends
were invoked using explicit default-alternative selectors:

| Backend | TrueGoal (`forall x:int. x + 0 = x`) | FalseGoal (`0 = 1`) | Smoke script |
|---|---|---|---|
| Z3 4.13.3 | `Valid`, 18 steps | `Unknown (sat)`, 11 steps | PASS |
| CVC5 1.1.2 | `Valid`, 25 steps | `Unknown (sat)`, 37 steps | PASS |

These are small operational smoke tests, **not** validation of a substantive
project theorem or a claim that Why3 established the false goals as
`Invalid`. The deliberate false goals were not proved `Valid`.
Both mock-based offline tests and the real backend script completed with
exit status 0; the user also reported clean ShellCheck for
`verification/why3/check_backends.sh`. A separate
ShellCheck **SC2154** warning was found in the offline test harness's
ERR trap; the trap was refactored into a named reporting function
on the same branch. A clean rerun of ShellCheck on that corrected
offline test still requires local confirmation.

### Functional proof tests for recognized backends

After updating this branch, run:

```sh
shellcheck scripts/test_ada_spark_why3.sh
shellcheck verification/why3/check_backends.sh
bash verification/why3/check_backends.sh
```

The Bash script in `verification/why3/check_backends.sh` invokes Z3 and
CVC5 **through Why3** on
[`verification/why3/backend_smoke.why`](why3/backend_smoke.why).
Both must report `Valid` for integer addition by zero.
For the deliberately false statement `0 = 1`, the script accepts
**`Invalid`** (Why3 explicitly reports an invalid goal), or the exact
**`Unknown (sat)`** indication seen on the user's Z3 4.13.3 driver.
`Unknown (sat)` is **not** the same as `Invalid`: the Why3 interface
has not established invalidity, although its message indicates a
satisfiable negated goal. The script prints distinct messages for those
two outcomes and does not count generic `Unknown`, timeout or tool
errors as successful negative controls.

Every prover invocation has a 30-second limit. Unlike a positive proof
check, an unproved negative goal may cause `why3 prove` to return
nonzero, so the script inspects both the exit code and the *exact*
structured goal/result output. The computer10 run established that
Why3 1.8 returns **exit code 2** for this unproved goal: the corrected
script requires code 2 and one exact goal/result pair for the negative
control, rejecting codes 0, 1, 124 (timeout), and other abnormal statuses. It never
touches the user's Why3 configuration and does not establish the
solver's general soundness. A functional test must execute on computer10
before any backend is marked verified.

You can inspect registered names using `why3 --list-provers`, and
the installed Why3 configuration data with `why3 --print-datadir`.
Why3's official `provers-detection-data.conf` controls supported
version patterns and drivers. Installing another Why3 version alone
does not guarantee Yices 2, Gappa 1.6, or newer Eprover compatibility:
those drivers and their version patterns must be checked separately.

## Verified GNATprove 16.1.0 and Isabelle2026 on computer10

The user performed a full local run on November 15, 2026 with no errors
from ShellCheck or the offline installer regressions. Unlike the earlier
Alire 1.2.1 failure, the direct official GNAT-FSF 16.1.0 download
completed. The installer verified its pinned 472,919,963-byte archive
and SHA-256, extracted it under the user prefix, and created
`$HOME/.local/opt/ada-spark/bin/gnatprove`. Its real `--version`
output and the user's subsequent direct version check both reported:

| Installed component | Observed local version |
|---|---|
| GNATprove FSF | 16.1.0 |
| Bundled Why3 for GNATprove | 1.8.2+git |
| Bundled Alt-Ergo | 2.6.1 |
| Bundled CVC5 | 1.3.2, git `86cecd8` |
| Bundled Z3 | 4.15.4, 64-bit |
| Isabelle launcher | `Isabelle2026` |

Isabelle's published archive SHA-256 had also been verified independently
during installation. The separate launcher command
`"$HOME/.local/opt/formal-provers/isabelle-2026/Isabelle2026/bin/isabelle" version`
returned `Isabelle2026`. This confirms the Isabelle executable starts
and identifies its release; it does not yet prove that particular
Isabelle theory files compile.

The GNATprove bundle reports newer versions of Z3 and CVC5 than
Debian's system Why3 1.8.0 uses. Keep the **system Why3** smoke tests
and the **bundled GNATprove** solver inventory distinct. The later
native GNATprove smoke run **did discharge the bounded-count SPARK
verification conditions on computer10**. This is an operational
verification of the isolated fixture only; it does not establish that
all project code or report-derived theorems are proved.

### GNATprove 16.1 option syntax correction (computer10)

The first attempted native SPARK proof smoke run did **not** analyze the
fixture. The user reported exit status 1 with this diagnostic:

```text
error: wrong argument "--warnings=error" for --checks-as-errors,
must be one of (on, off)
```

The original command mistakenly passed bare `--checks-as-errors`.
GNATprove 16.1 requires **`--checks-as-errors=on`**, while
`--warnings=error` remains an independent switch. The script and its
offline regression check now require the explicit, single CLI argument.
The regression mock records shell argument boundaries and rejects a
bare `--checks-as-errors`. This fix addresses the CLI parsing error;
the actual native proof still requires rerunning on computer10.

### GNATprove 16.1 flow-dependency error (computer10)

The second real proof-smoke invocation, after correction of
`--checks-as-errors=on`, reached **Phase 2: generation of Global
contracts**. GNATprove rejected an incomplete explicit
`Depends` specification at `bounded_counts.ads:44`:

```text
error: parameter "Capacity" is missing from input dependence list
+ add "null => Capacity" dependency to ignore this input
gnatprove: error during generation of Global contracts
```

The output `Total` is calculated solely from `Previous` and
`Increment`; `Capacity` is a precondition and assertion bound, not
an input to the output calculation. The corrected declaration accounts
for all inputs explicitly:

```ada
Depends => (Total => (Previous, Increment),
            null => Capacity),
```

This follows GNATprove's actual diagnostic; it is **not** an added
assumption or an excuse to ignore an output dependency. A regression
assertion now guards against restoring the incomplete contract.
The user also reported an earlier Phase 1 data-representation generation
warning: `generation of data representation information failed`.
It did **not** recur in the subsequent successful native run, but its
earlier cause was not independently diagnosed. The corrected flow
contract **was validated** by GNATprove in that successful run.

### Confirmed native GNATprove SPARK proof (computer10)

The user ran `bash scripts/smoke_gnatprove.sh` after updating to
repository branch revision `662cd2b`. The execution reported all
three GNATprove phases completed, including flow analysis and proof,
without the earlier representation warning or Depends error.
The final result was:

```text
Success: all checks proved (11 checks).
Summary logged in /tmp/tmp.9UKduIhnMl/obj/gnatprove/gnatprove.out
Native proof summary from gnatprove.out:
Total                           11    3 (27%)       8 (73%)      .      .
PASS: GNATprove completed nonempty SPARK analysis with --checks-as-errors=on.
GNATprove exit code: 0
```

The native summary's **11 checks** comprise **three flow** and
**eight prover-dispatched** checks, with **zero justified** and
**zero unproved** checks. The ten substantive postcondition clauses
are *not* ten separate native check-count entries: GNATprove grouped
and split the postcondition into verification conditions, and
reported `postcondition proved (Z3: 15 VC ...)`. Its other completed
obligations included absence of integer overflow, the capacity
assertion, initialization, data dependencies, and flow dependencies.
Z3 and CVC5 contributed to the proof as shown by the native
diagnostic; `--prover=cvc5,z3,altergo` does not imply that each
solver independently proved every check.

This is actual execution evidence supplied in the user's terminal
transcript, **not a retained source-pinned raw proof campaign**.
The smoke script uses a disposable work directory, which it deletes
on successful exit; the transient `gnatprove.out` file therefore
is not available as an independently auditable archived artifact.
For source-pinned evidence across the full Hoeflin/Ferguson and
Towers projects, continue to use the documented proof runner with
fresh native reports, hashes, explicit trusted boundaries, and
negative controls. Do not substitute this isolated proof result for
those project verification campaigns.

### Next: actual native SPARK verification, not merely version detection

Run the dedicated isolated proof fixture from the current repository
checkout (no global configuration changes):

```sh
cd ~/src/composite_iq_formal_tools
git pull --ff-only
bash -n scripts/smoke_gnatprove.sh
bash scripts/smoke_gnatprove.sh
```

The fixture is `verification/spark_smoke/src/bounded_counts.ads` and
`bounded_counts.adb`, with an explicit checked capacity assertion and
ten substantive count-accounting postconditions, as well as domain and
data-flow contracts. The script runs the real GNATprove 16.1.0 through
its user-local wrapper in a disposable copy, with `--mode=all` and
`--checks-as-errors=on`, requesting bundled CVC5, Z3 and Alt-Ergo.
It reports PASS **only after GNATprove exits successfully**. This smoke
suite is not itself a proof of the IQ model calculations or all SPARK
projects.

For the existing substantive Hoeflin/Ferguson and Towers proof
campaigns, use the source-pinned proof runner described in
[`verification/README.md`](README.md); it derives a separate
Alire toolchain environment and retains evidence for both the native
proof reports and negative controls. Do not replace historical
campaign results with this minimal smoke fixture. The runner's default
workspace is `~/.local/share/icar16-gnatprove-tools` and is separate
from this newly downloaded user-local GNATprove binary. A successful
smoke test does not establish that the older workspace and the new
bundle use identical compilers or prover configurations.

## Further Ada/SPARK facilities

For a broader development workflow, consider the Ada Language Server (AdaCore's VS Code Ada extension), GNAT Studio, GNATformat, GNATtest, GNATcov, GNATdoc, gnatcheck and Libadalang. Some are in the [Alire package index](https://alire.ada.dev/crates.html) and some have separate AdaCore community releases. They are **optional** and are not silently downloaded or installed by the base script. Record each available version and license before using it in reproducible project checks.

For Why3, further candidates include Alt-Ergo, veriT, Vampire and SPASS. Availability and exact compatibility require separate checks. In particular, do not install the Debian `ergo` quantum-chemistry package while looking for the *Alt-Ergo* SMT prover.

## Validation limits

The offline test `bash scripts/test_ada_spark_why3.sh` validates shell
syntax, exact vendor size/SHA-256 metadata, and rejection of an
unsupported OS before download. It additionally checks the exact
`why3 config detect` dispatch and negative controls for the wrong Metis
package, and the absence of prohibited automatic system changes. GitHub Actions runs that test as part of its existing Python-contracts workflow, alongside the separate Deal coverage and runtime-test gates.

The user's computer has not been operated remotely by the assistant. User-provided terminal logs confirm real Ada compilation, Isabelle version detection, a checksum-verified GNATprove installation, the system Why3 backends, and **the isolated 11-check native SPARK smoke proof**. Metis build success and a fresh proof of the complete statistical analysis projects remain unconfirmed. Runtime and fixture-proof success are distinct from formal verification of all report-derived claims.

## Provenance

- [Why3 external provers](https://why3.org/#provers) and [Why3 configuration manual](https://why3.org/doc/manpages.html).
- [Debian Trixie packages](https://packages.debian.org/trixie/) for GNAT, GPRbuild, Gappa, Why3, Alire, cvc5, Z3, E prover, and build utilities.
- [Alire GNATprove crate](https://alire.ada.dev/crates/gnatprove) and [AdaCore community transition guide](https://alire.ada.dev/transition_from_gnat_community.html).
- [Official Metis release page](https://www.gilith.com/software/metis/) and [Metis development checkout](https://github.com/gilith/metis).

## Appendix — Full AI disclosure

The user's latest terminal output confirmed that the AI-assisted
Bounded_Counts smoke fixture ran under real GNATprove FSF 16.1.0 and
successfully discharged all 11 native checks (three flow and eight
prover-dispatched), with zero justified or unproved checks. The user
reported exit code 0 and a nonempty GNATprove summary. The assistant
recorded this evidence and corrected the document's previously
unverified-status statements. No raw ephemeral proof report was
persisted to the repository, and this fixture does not prove the
statistical claims in the three reports. Source-pinned project-level
verification is a separate obligation.


The next native run reached GNATprove Phase 2 and failed because the
AI-authored Bounded_Counts Depends aspect omitted Capacity from its input
list. The user provided the complete GNATprove diagnostic including its
suggested null => Capacity specification. The AI then updated the
specification and added a structural regression test. The revised flow
contract has not been checked by the user's GNATprove installation yet;
a passing mocked test alone is not proof closure. The Phase 1 partial
data-representation warning remains an open diagnostic.


The user's first execution of the AI-generated native GNATprove smoke script failed before analysis because the CLI flag `--checks-as-errors` was missing its required `=on` value and consumed `--warnings=error` instead. The assistant checked the official AdaCore command-line documentation, corrected the flag, and extended the mocked offline regression to check exact argument boundaries. The result is not yet evidence of a successful SPARK proof until rerun against the actual GNATprove executable.

The user later supplied terminal results confirming GNATprove FSF 16.1.0 downloaded, passed the installer integrity checks, and executed with its bundled Why3, Alt-Ergo, CVC5, and Z3. Isabelle2026 also executed its version command. The assistant added a standalone SPARK counter-increment proof fixture and isolated native proof-runner script; these were authored with AI assistance. Until the user runs the new script, neither the current GNATprove 16 bundle's native proof closure nor its compatibility with the host GNAT compiler is established.

The November 15 computer10 logs further showed that Ada compilation
succeeded and Isabelle2026 passed its official archive SHA-256 check
and extraction. They also showed `alr -n get gnatprove=16.1.0` failing,
because Alire 1.2.1's index does not contain this recent release.
The assistant inspected both upstream Alire index branches and the
official GNAT-FSF GitHub release, then replaced the erroneous Alire
installation path with a verified-hash vendor archive installer.
The new download/extraction path has not yet been executed on computer10
and the downloaded vendor executable has not been tested in this chat.


On November 15, 2026, the user supplied an additional real computer10 run confirming that both Z3 and CVC5 completed the Why3 smoke test with an overall exit status of 0. Both positive goals were Valid; both false goals were Unknown (sat), not Invalid. User-provided ShellCheck output also exposed SC2154 in the AI-generated error trap. The assistant refactored that diagnostic and recorded these results. No new live proof execution was performed by the assistant.

The initial test incorrectly demanded `Invalid` on a deliberately false goal and treated Why3's nonzero exit for `Unknown (sat)` as an invocation failure. User-provided logs showed a correctly completed Z3 invocation with Why3 category `Unknown (sat)` and a nonzero process result. The AI revised the test to accept and distinctly report this exact qualified nonproof status, without equating it with a formally established `Invalid` response, and extended the offline mock regression cases. No real CVC5 run has yet been validated by the AI.

A further error in the AI-generated Why3 smoke test assumed a single-line goal/result format. The user supplied authentic output with separate `Goal TrueGoal.` and `Prover result is: Valid` lines, demonstrating a successful Z3 proof but a false failure in the script's output parser. The AI updated the parser and added multiline regression cases with negative controls. These regression cases remain mocked and do not replace live Z3/CVC5 verification on computer10.

The initial Why3 smoke script erroneously passed ambiguous bare prover names to Why3 1.8.0. The user supplied the resulting multi-prover error. A subsequent fix explicitly selects pinned name, version and empty alternative, and the offline mock test now rejects ambiguous shorthand. The exact real prover behavior after that correction is unverified until it is rerun on computer10.

The user subsequently provided Why3 1.8.0 prover detection output and a shellcheck invocation error. The AI incorporated an explicit version-compatibility summary and added a Why3/Z3/CVC5 positive/negative proof smoke test. Its GitHub CI uses mocked prover output, not actual SMT solver execution; real backend success still requires the user to run the smoke test on computer10.

The initial AI-generated installer gave incorrect `alr install` and
`why3 config --detect` commands for the user's Debian 13 versions.
The user supplied exact CLI error logs, and the correction was verified
against Debian's Why3 manpage and Alire's `alr get` and `with` facilities.
Mock-based CI tests do not establish that the binary can be downloaded or
that SPARK proof obligations close on computer10. This known error and its
subsequent correction are included to preserve transparent provenance.


OpenAI assisted in identifying toolchain variants, researching package repositories and vendor pages, composing the Bash installation and test scripts, writing the guide, and committing repository changes through the connected GitHub integration. The requested target was Debian 13 on computer10. The user previously reported installed Rocq, Lean, Yices and PVS facilities and an in-progress detached Isabelle transfer, but no AI-initiated installation was carried out on their host. Source locations and release information were checked against public vendor and Debian records on November 15, 2026; remote inventories and future package updates may differ. The installer offers explicit mutating actions requiring invocation by the user; its tests are offline and do not validate live downloads, the validity of third-party proofs, vendor build-chain trust, or SPARK proof closure. The source checkout for Metis is a pinned development commit, **not** a verified official Metis binary release. GNATprove's Alire crate is community software and may differ from commercial SPARK Pro. Formal claims made in project reports require separately recorded reproducible compilation, proof success, and a proof-status audit on the actual source revision.
