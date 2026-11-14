# Installing additional formal-methods tools on Debian 13

**AI disclosure — this guide and the Python installer were AI-assisted.**
Source URLs, version numbers and vendor-provided SHA256 values were reviewed
on November 14, 2026. Verification of downloaded bytes is *not* a formal
proof of the software's correctness, security, or operational compatibility.

For Ada/SPARK, Gappa, Joe Hurd's Metis and Why3 backends, see [the separate Debian 13 Ada/SPARK guide](INSTALL_ADA_SPARK_WHY3_METIS_DEBIAN13.md). This is a separately opted-in installation, preserving the ongoing Isabelle download.

## Scope and naming

The host is `computer10` (Debian 13, x86_64). Install each tool in its
own location. **Do not remove or replace the working Rocq 9.2 environment,
the system `coqc`, or the `icar16-colibri2` opam switch.**

* **Lean 4:** pin Lean 4.35.0 (stable) through `elan` 4.2.4.
* **Isabelle/HOL:** pin the complete Isabelle2026 Linux distribution.
* **Yices 2:** use Yices 2.7.0. The requester wrote "Yikes"; **this is
  an interpretation, not a confirmed identity**. There is no Yikes
  installation in this script.
* **COLIBRI (classic):** the original SMT/constraint solver, distributed
  as a bundle and distinct from the OCaml `colibri2` package.
* **PVS:** pin SRI's PVS 8.1.3 Linux x86_64 prebuilt release. Use the
  documented user-level installation and check runtime dependencies.

The four fully pinned releases use the vendor's official archive and digest.
For classic COLIBRI, the vendor's GitLab release download is behind an
interactive access-control page; no digest or machine-accessible artifact
was established. It therefore remains a **manual** step, not a silently
substituted COLIBRI2 install.

## Reproduction using a separate checkout

From `~/src`, clone this branch into a new, unused folder:

```sh
git clone --branch tooling/formal-provers-debian13 --single-branch https://github.com/AndersH3/composite_iq_checked_claims.git ~/src/composite_iq_formal_tools
cd ~/src/composite_iq_formal_tools
python3 -m venv .venv
.venv/bin/python -m pip install 'deal==4.24.6'
bash scripts/test_formal_provers.sh
```

Each command is intentionally standalone. Do not paste explanatory prose or
citation markup into Bash.

List pinned artifacts **without downloads or changes**:

```sh
.venv/bin/python scripts/install_formal_provers.py
```

Review an installation plan, e.g. for Yices:

```sh
.venv/bin/python scripts/install_formal_provers.py --tool yices
```

Perform an installation explicitly, one tool at a time:

```sh
.venv/bin/python scripts/install_formal_provers.py --tool lean --install
.venv/bin/python scripts/install_formal_provers.py --tool yices --install
.venv/bin/python scripts/install_formal_provers.py --tool pvs --install
.venv/bin/python scripts/install_formal_provers.py --tool isabelle --install
```

The Isabelle download alone is approximately 1.4 GB; ensure adequate disk
space for the download and extracted distribution. The script fails closed
on mismatched SHA256 values or archive sizes, does not use `sudo`, and
refuses to overwrite existing versioned installation directories. It
extracts with Python's `tarfile` data filter. Running a binary after
extraction is a separate action; the only installer bootstrap executed
automatically is the digest-pinned `elan-init` program.

**Lean:** If `elan` already exists, the script reuses it. Otherwise it
installs the verified `elan` bootstrap in the user's home without editing
their PATH or changing the default toolchain. The selected Lean 4.35.0
toolchain is installed independently and verified with `elan run`. After
installation, invoke:

```sh
~/.elan/bin/elan run leanprover/lean4:v4.35.0 lean --version
```

**Isabelle:** Locate its executable, then invoke its version command:

```sh
find ~/.local/opt/formal-provers/isabelle-2026 -type f -path '*/bin/isabelle'
```

Use the returned path followed by `version`. Its official bundle includes
a full Isabelle/HOL development environment; no separate opam switch is
required.

**Yices:** Locate `yices-smt2` and use `--version`:

```sh
find ~/.local/opt/formal-provers/yices-2.7.0 -type f -name yices-smt2
```

**PVS:** Locate the release's `pvs` launcher, consult its accompanying
`INSTALL`/README, and then test `--version`:

```sh
find ~/.local/opt/formal-provers/pvs-8.1.3 -type f -name pvs
```

For PVS or Isabelle, runtime compatibility is not established merely by a
successful archive extraction. Avoid system-wide links until the launcher
and a representative proof/check have run successfully.

## Resuming Isabelle when SSH disconnects

A dropped SSH session can terminate an interactive `curl` or Bash script
even when the download server is working. In the reported run, the HTTPS
transfer had already reached hundreds of megabytes; the partially
downloaded `~/Isabelle2026_linux.tar.gz` must be retained. **Do not
delete it or restart from byte zero.** Do not paste the full contents of
the shell script into an interactive Bash prompt: execute the file itself.

On `computer10`, from a normal shell:

```sh
cd ~/src/composite_iq_formal_tools
git pull --ff-only
bash scripts/retry_isabelle_computer10.sh --detach
```

The `--detach` flag launches the installer with `setsid` and `nohup`,
outside the invoking SSH session, and redirects progress to
`~/isabelle2026-install.log`. A `flock` lock prevents duplicate jobs.
For recoverable network interruptions, each new `curl -C -` attempt resumes
from the current file size. HTTPS certificate errors are not retried or
bypassed. This mechanism usually survives SSH disconnection; it cannot
survive a machine reboot or a server policy that forcibly terminates all
user processes. If that happens, rerun `--detach` to resume the archive.

Check status without launching a second installer:

```sh
bash ~/src/composite_iq_formal_tools/scripts/retry_isabelle_computer10.sh --status
```

Once the download has finished, the worker checks the archive's exact
1,412,134,191 byte size and the pinned SHA256, installs it, and lists
the Isabelle launcher in the log. The status command reports whether the
worker holds its exclusive lock and shows recent log output. "No installer
process" does not alone mean success; inspect the end of the log.

## Isabelle download failures and official mirror

**November 14, 2026 correction:** The original script mistakenly used
`mirror.cosi.clarkson.edu`. This caused an SSL hostname mismatch on
computer10, which correctly rejected the untrusted host. The official
Clarkson mirror identifies itself as `mirror.clarkson.edu`; its
`/isabelle/dist/index.html` lists the exact Isabelle2026 archive and
SHA256 checksum. The installer, documentation, and regression tests now
use the corrected hostname. **Do not bypass TLS verification** with
`curl -k`, `--insecure`, or an unverified Python SSL context.

If Isabelle fails with `[Errno 101] Network is unreachable`, this is a
network/download problem, not a Lean, PVS, or Yices failure. First reconnect
to `computer10` if the SSH session ended, and check its network connection.
The Isabelle project has noted intermittent problems with the Munich mirror.
It lists Clarkson as an official release mirror, with the **same SHA256**
and **1412134191-byte** bundle as the pinned Munich release.

From the cloned repository checkout on `computer10`:

```sh
git pull --ff-only
.venv/bin/python scripts/install_formal_provers.py --tool isabelle --mirror clarkson
.venv/bin/python scripts/install_formal_provers.py --tool isabelle --mirror clarkson --install
```

`--mirror clarkson` only changes the download host; all archive-size and
SHA256 checks remain unchanged. Other tool names reject this mirror. An
unreachable network yields a short diagnostic and does not disturb existing
Lean, Yices, PVS, Rocq or COLIBRI2 installations.

If `computer10` has no internet connection, download the **exact**
`Isabelle2026_linux.tar.gz` on another machine from the official Clarkson
distribution directory, verify or transfer it without modification, and copy
it to computer10. For example, from `computer7`:

```sh
curl --fail --location --continue-at - --retry 3 --output Isabelle2026_linux.tar.gz https://mirror.clarkson.edu/isabelle/dist/Isabelle2026_linux.tar.gz
sha256sum Isabelle2026_linux.tar.gz
scp Isabelle2026_linux.tar.gz anonymous@computer10:~/
```

The required SHA256 is
`858c995b32216b3876bf395c3be843147d1f1eee404bc6c958d7534ee335e48d`.
Then on `computer10`, in this repository directory:

```sh
.venv/bin/python scripts/install_formal_provers.py --tool isabelle --install --archive "$HOME/Isabelle2026_linux.tar.gz"
```

The Python installer independently verifies both the hash and the exact
byte count **before** extracting any archive. A partial transfer fails
verification. If the mirror is inaccessible from both machines, investigate
DNS, routing, firewall, proxy, or IPv4/IPv6 connectivity rather than
disabling certificate or checksum verification.

## Classic COLIBRI: explicit manual step

Download from the vendor's own
[COLIBRI page](https://colibri.frama-c.com/download.html), selecting
**COLIBRI** rather than **Colibri2**. The vendor describes a `bundle`
directory containing the `colibri` executable and dependencies.

Inspect the download and any vendor checksums. After reviewing its contents
and its own installation instructions, place the resulting `bundle`
directory under `~/.local/opt/formal-provers/colibri-classic/`. The
provided Python script intentionally does not download or execute that
unverified release.

## Release provenance

| Tool | Version | SHA256 of Linux x86_64 archive | Official source |
|---|---|---|---|
| elan for Lean | 4.2.4 | `42b94d4244e8353142c456ec0e4ca6528fd898a6c604d4059f494e706e431f63` | [GitHub release](https://github.com/leanprover/elan/releases/tag/v4.2.4) |
| Isabelle/HOL | 2026 | `858c995b32216b3876bf395c3be843147d1f1eee404bc6c958d7534ee335e48d` | [Official distribution](https://isabelle.in.tum.de/) |
| Yices 2 | 2.7.0 | `49566b6f817692820538df78fe406878400d79810631c9372b2495bc81d3e00a` | [GitHub release](https://github.com/SRI-CSL/yices2/releases/tag/yices-2.7.0) |
| PVS | 8.1.3 | `42a05d275be7230790e0dc61f4579cde23b99575957c6053a45d16369b5aa2e1` | [GitHub release](https://github.com/SRI-CSL/PVS/releases/tag/pvs8.1.3) |
| Classic COLIBRI | Manual selection | No verified digest available | [Official downloads](https://colibri.frama-c.com/download.html) |

The Isabelle digest was cross-checked against the published 2026
distribution index at an Isabelle mirror. GitHub release asset metadata
exposed the elan, Yices and PVS digests. The script deliberately pins
versions rather than silently switching to a future release.

## Validation and limitations

Run the **offline** test harness:

```sh
bash scripts/test_formal_provers.sh
```

It checks Deal release contracts, expected hashes, rejection of corrupted
synthetic archives, and that each planning mode runs without any installer
or network call. This does **not** build, execute, or prove all five tools
in Debian 13. The user must run each requested installation and complete
the functional checks. A failed installation should preserve its diagnostic
output for troubleshooting; do not claim verification from a downloaded
archive alone.

## Appendix — complete AI disclosure

This document, the installer program, its Deal contract statements, and
the associated shell-based tests were generated and reviewed with OpenAI
assistance on November 14, 2026. The requester specified the Debian 13
environment, GitHub repository, existing Rocq/COLIBRI2 installations,
software targets, and a project policy requiring at least ten meaningful
Deal contracts per Python function. Public vendor pages and GitHub release
asset metadata were consulted for exact release identifiers, source
locations and published SHA256 hashes. No PVS, Isabelle, COLIBRI,
Yices or Lean installation was actually performed on the requester's host
by the AI. Repository CI and offline tests, where available, support
source checks but not binary provenance beyond pinned hashes, runtime
correctness, soundness, or independent human review. Uncertainty remains
around the name "Yikes" and the official classic COLIBRI bundle, and is
made explicit rather than silently resolved. The complete conversation
and toolchain executions are not preserved as a cryptographically
authenticated build provenance record.
