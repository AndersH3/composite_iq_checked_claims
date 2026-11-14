#!/usr/bin/env python3
"""Acquire pinned formal-methods binaries without changing system packages.

AI disclosure: This installer was authored with OpenAI assistance. Contracts
check stated input, release-metadata, and checksum properties. They do NOT
prove the integrity of vendor build systems, archive executables, or upstream
theorem-prover implementations.

Purpose: Install Lean 4, Isabelle/HOL, Yices 2, and PVS in isolated user
directories on Debian 13 x86_64. Classic COLIBRI is explicitly documented
but is NOT installed automatically: its official GitLab download currently
requires interactive access, and we have no verified artifact digest.

Security model: Official download locations and release SHA256 hashes are
pinned. No sudo, shell interpolation, opam modification, PATH mutation, or
unverified archive extraction. Python 3.13's tarfile data filter is used
during extraction. The Elan bootstrap binary is digest checked before it
is executed, and no Lean default toolchain is changed.

Scope: A verified archive checksum attests equality to the pinned release
asset, not independent correctness, formal proof, or platform compatibility.
"""

from __future__ import annotations

import argparse
import hashlib
import os
from pathlib import Path
import platform
import shutil
import subprocess
import sys
import tarfile
import tempfile
import urllib.error
import urllib.request

import deal

LEAN_TOOLCHAIN = "leanprover/lean4:v4.35.0"
COLIBRI_URL = "https://colibri.frama-c.com/download.html"
# (HTTPS URL, vendor-published SHA256, official byte count, install directory)
SPECS = {
    "lean": (
        "https://github.com/leanprover/elan/releases/download/v4.2.4/"
        "elan-x86_64-unknown-linux-gnu.tar.gz",
        "42b94d4244e8353142c456ec0e4ca6528fd898a6c604d4059f494e706e431f63",
        4996571,
        "elan-4.2.4",
    ),
    "isabelle": (
        "https://isabelle.in.tum.de/dist/Isabelle2026_linux.tar.gz",
        "858c995b32216b3876bf395c3be843147d1f1eee404bc6c958d7534ee335e48d",
        1412134191,
        "isabelle-2026",
    ),
    "yices": (
        "https://github.com/SRI-CSL/yices2/releases/download/yices-2.7.0/"
        "yices-2.7.0-x86_64-pc-linux-gnu-static-gmp.tar.gz",
        "49566b6f817692820538df78fe406878400d79810631c9372b2495bc81d3e00a",
        9848047,
        "yices-2.7.0",
    ),
    "pvs": (
        "https://github.com/SRI-CSL/PVS/releases/download/pvs8.1.3/"
        "pvs8.1.3-20261028-linux-x86_64.tgz",
        "42a05d275be7230790e0dc61f4579cde23b99575957c6053a45d16369b5aa2e1",
        61735502,
        "pvs-8.1.3",
    ),
}
ALLOWED_HOSTS = ("https://github.com/", "https://isabelle.in.tum.de/")
ISABELLE_CLARKSON = (
    "https://mirror.cosi.clarkson.edu/isabelle/dist/Isabelle2026_linux.tar.gz"
)
MIRRORS = ("primary", "clarkson")
HEX = frozenset("0123456789abcdef")


@deal.pre(lambda name: isinstance(name, str))
@deal.pre(lambda name: name in SPECS)
@deal.pure
@deal.post(lambda result: isinstance(result, tuple) and len(result) == 4)
@deal.post(lambda result: result[0].startswith("https://"))
@deal.post(lambda result: result[0].startswith(ALLOWED_HOSTS))
@deal.post(lambda result: result[0].endswith((".tar.gz", ".tgz")))
@deal.post(lambda result: "?" not in result[0] and "#" not in result[0])
@deal.post(lambda result: isinstance(result[1], str) and len(result[1]) == 64)
@deal.post(lambda result: set(result[1]) <= HEX)
@deal.post(lambda result: isinstance(result[2], int) and result[2] > 4096)
@deal.post(lambda result: isinstance(result[3], str) and result[3].count("/") == 0)
@deal.post(lambda result: result[3] not in (".", "..", ""))
@deal.ensure(lambda name, result: result == SPECS[name])
@deal.ensure(lambda name, result: result[3].startswith(name if name != "lean" else "elan"))
def release_spec(name: str) -> tuple[str, str, int, str]:
    """Return pinned, reviewed release metadata for a supported tool.

    Constraints: tool whitelist; immutable tuple shape; HTTPS; approved
    hosts; tarball format; no URL query fragments; SHA256 alphabet and
    length; positive recorded size; single safe directory component;
    exact mapping to the pinned manifest and expected tool prefix.
    This is metadata validation, not verification of a remote server.
    """
    return SPECS[name]


@deal.pre(lambda tool, mirror: isinstance(tool, str))
@deal.pre(lambda tool, mirror: tool in SPECS)
@deal.pre(lambda tool, mirror: isinstance(mirror, str))
@deal.pre(lambda tool, mirror: mirror in MIRRORS)
@deal.pre(lambda tool, mirror: mirror == "primary" or tool == "isabelle")
@deal.pure
@deal.post(lambda result: isinstance(result, str))
@deal.post(lambda result: result.startswith("https://"))
@deal.post(lambda result: "?" not in result and "#" not in result)
@deal.post(lambda result: result.endswith((".tar.gz", ".tgz")))
@deal.post(lambda result: result.startswith(
    ("https://github.com/", "https://isabelle.in.tum.de/",
     "https://mirror.cosi.clarkson.edu/")))
@deal.ensure(lambda tool, mirror, result:
             result.rsplit("/", maxsplit=1)[-1] ==
             SPECS[tool][0].rsplit("/", maxsplit=1)[-1])
@deal.ensure(lambda tool, mirror, result:
             mirror != "primary" or result == SPECS[tool][0])
@deal.ensure(lambda tool, mirror, result:
             mirror != "clarkson" or result == ISABELLE_CLARKSON)
def download_url(tool: str, mirror: str) -> str:
    """Select a whitelisted official archive host, never an arbitrary URL.

    The original filename is preserved exactly, so the SHA256 and byte count
    pinned by release_spec continue to apply regardless of download host.
    Only Isabelle supports the alternate mirror; other tools refuse it.
    The mirror source is the Isabelle project's public mirror listing.

    Preconditions specify accepted solver names and valid tool/mirror pairs;
    postconditions specify HTTPS, host allowlist, archive file extension,
    and absence of query/fragment parameters. Relational contracts require
    exact filename, vendor URL for primary, and pinned Clarkson URL otherwise.
    """
    return SPECS[tool][0] if mirror == "primary" else ISABELLE_CLARKSON



@deal.pre(lambda archive, digest, expected_size: isinstance(archive, Path))
@deal.pre(lambda archive, digest, expected_size: archive.is_absolute())
@deal.pre(lambda archive, digest, expected_size: archive.is_file())
@deal.pre(lambda archive, digest, expected_size: not archive.is_symlink())
@deal.pre(lambda archive, digest, expected_size:
          archive.name.endswith((".tar.gz", ".tgz")))
@deal.pre(lambda archive, digest, expected_size: isinstance(digest, str))
@deal.pre(lambda archive, digest, expected_size: len(digest) == 64)
@deal.pre(lambda archive, digest, expected_size: set(digest) <= HEX)
@deal.pre(lambda archive, digest, expected_size:
          isinstance(expected_size, int) and expected_size > 0)
@deal.post(lambda result: result is True)
@deal.raises(OSError, ValueError)
@deal.has("read")
@deal.ensure(lambda archive, digest, expected_size, result:
             not result or archive.stat().st_size == expected_size)
def verify_archive(archive: Path, digest: str, expected_size: int) -> bool:
    """Verify exact file size and streaming SHA256 before extraction.

    Reject a symbolic-link archive, unexpected size, or mismatched digest.
    Keeping verification independent of extraction allows safe tests using
    synthetic archives without running downloaded software.
    """
    if archive.stat().st_size != expected_size:
        raise ValueError("Archive size differs from official release metadata")
    sha = hashlib.sha256()
    with archive.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            sha.update(chunk)
    if sha.hexdigest() != digest:
        raise ValueError("SHA256 mismatch; refusing to extract or execute archive")
    return True


if __name__ == "__main__":
    deal.enable(warn=False)
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--tool", choices=(*SPECS, "colibri"))
    parser.add_argument("--install", action="store_true",
                        help="download, verify, and install the selected pinned release")
    parser.add_argument("--archive", type=Path,
                        help="use a previously downloaded archive instead of fetching")
    parser.add_argument("--mirror", choices=MIRRORS, default="primary",
                        help="official download mirror; clarkson is for Isabelle only")
    parser.add_argument("--prefix", type=Path,
                        default=Path.home() / ".local" / "opt" / "formal-provers",
                        help="isolated user directory (default: ~/.local/opt/formal-provers)")
    args = parser.parse_args()

    if platform.system() != "Linux" or platform.machine() not in ("x86_64", "AMD64"):
        parser.error("This version of the installer supports Linux x86_64 only")
    if not args.install and args.archive is not None:
        parser.error("--archive requires --install")
    if args.mirror != "primary" and args.tool != "isabelle":
        parser.error("--mirror clarkson is only supported for Isabelle")
    if args.mirror != "primary" and args.archive is not None:
        parser.error("--mirror and --archive are mutually exclusive")
    if args.tool is None:
        if args.install:
            parser.error("--install requires --tool")
        for tool in SPECS:
            url, digest, size, dirname = release_spec(tool)
            print(f"{tool}: {dirname}; {size} bytes; sha256={digest}; {url}")
        print(f"colibri (classic): MANUAL download from {COLIBRI_URL}")
        raise SystemExit(0)
    if args.tool == "colibri":
        print("Classic COLIBRI cannot currently be installed automatically.")
        print("Download the vendor bundle manually from:", COLIBRI_URL)
        print("After download, follow the bundle's own README and verify its")
        print("contents and provenance. Do not substitute opam colibri2.")
        raise SystemExit(0 if not args.install else 2)

    original_url, digest, size, dirname = release_spec(args.tool)
    url = download_url(args.tool, args.mirror)
    target = args.prefix.expanduser().resolve() / dirname
    print(f"Tool: {args.tool}; expected SHA256: {digest}")
    print(f"Selected official URL ({args.mirror}): {url}")
    print(f"User installation: {target}")
    if args.tool == "lean":
        print(f"Pinned Lean toolchain: {LEAN_TOOLCHAIN}")
    if not args.install:
        print("PLAN ONLY: nothing was downloaded, installed, or changed.")
        raise SystemExit(0)

    prefix = args.prefix.expanduser().resolve()
    home = Path.home().resolve()
    if not prefix.is_relative_to(home):
        parser.error("Installation directory must remain within the user's home")
    if args.archive is None and target.exists() and args.tool != "lean":
        parser.error("The versioned target directory already exists; refusing overwrite")
    prefix.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="formal-tool-", dir=prefix) as temporary:
        scratch = Path(temporary)
        archive = args.archive.expanduser().resolve() if args.archive else (
            scratch / url.rsplit("/", maxsplit=1)[-1])
        if args.archive is None:
            print("Downloading pinned official release...", flush=True)
            try:
                with urllib.request.urlopen(url, timeout=60) as response:
                    with archive.open("wb") as output:
                        shutil.copyfileobj(response, output, length=1024 * 1024)
            except (urllib.error.URLError, TimeoutError, ConnectionError) as error:
                print(f"Download failed from {url}: {error}", file=sys.stderr)
                if args.tool == "isabelle":
                    print("If the network is reachable, try the official"
                          " alternate mirror:", file=sys.stderr)
                    print("  .venv/bin/python scripts/install_formal_provers.py"
                          " --tool isabelle --mirror clarkson --install", file=sys.stderr)
                    print("Alternatively, download Isabelle2026_linux.tar.gz"
                          " on another computer and invoke --archive /path/to/file",
                          file=sys.stderr)
                print("No installation was created; other installed tools"
                      " are unchanged.", file=sys.stderr)
                raise SystemExit(3) from error
        verify_archive(archive, digest, size)
        print("Official release SHA256 and size verified.", flush=True)

        extraction = scratch / "extracted"
        extraction.mkdir()
        with tarfile.open(archive, "r:gz") as bundle:
            # The Python 3.13 data filter rejects absolute paths, traversals,
            # special files and links escaping the extraction destination.
            bundle.extractall(path=extraction, filter="data")

        if args.tool == "lean":
            elan = shutil.which("elan")
            installed_lean_elan = Path.home() / ".elan" / "bin" / "elan"
            if elan is None and installed_lean_elan.is_file():
                elan = str(installed_lean_elan)
            if elan is None:
                installers = [p for p in extraction.rglob("elan-init") if p.is_file()]
                if len(installers) != 1:
                    parser.error("Expected one elan-init program in the verified archive")
                subprocess.run([str(installers[0]), "-y", "--no-modify-path",
                                "--default-toolchain", "none"], check=True)
                elan = str(installed_lean_elan)
                if not installed_lean_elan.is_file():
                    parser.error("elan-init did not create the expected user binary")
            subprocess.run([elan, "toolchain", "install", LEAN_TOOLCHAIN], check=True)
            subprocess.run([elan, "run", LEAN_TOOLCHAIN, "lean", "--version"], check=True)
            print("Lean installed; the existing elan default was not changed.")
        else:
            # Atomic rename avoids leaving a partly installed target behind.
            # The caller controls only a target path under their home directory.
            if target.exists():
                parser.error("Target exists; not overwriting an existing installation")
            os.replace(extraction, target)
            print(f"Installed verified archive to {target}")
            if args.tool == "isabelle":
                print("Find the entry point: find", target, "-path '*/bin/isabelle'")
            elif args.tool == "yices":
                print("Find the entry point: find", target, "-name yices-smt2")
            elif args.tool == "pvs":
                print("Find the entry point: find", target, "-name pvs")
