#!/usr/bin/env python3
"""Audit recorded proof integrity, native totals, and current source identity.

This does not replace rerunning GNATprove or independently check SMT proofs.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess

import deal
from json import JSONDecodeError
from subprocess import CalledProcessError

try:
    from verification.run_computer10 import ROOT, report_summary, is_sha256
except ModuleNotFoundError:
    from run_computer10 import ROOT, report_summary, is_sha256

DEFAULT_HISTORY = ROOT.joinpath("verification/evidence/deal-lint-clean-computer10-20261031/source_history.json")


@deal.pre(lambda path: isinstance(path, Path))
@deal.post(is_sha256)
@deal.raises(OSError, ValueError)
@deal.has("read")
def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


@deal.pre(lambda condition, message: isinstance(condition, bool) and isinstance(message, str))
@deal.post(lambda result: result is None)
@deal.raises(ValueError)
@deal.reason(ValueError, lambda condition, message: not condition)
@deal.has()
def check(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)
    return None


@deal.pre(lambda relative, expected, history, git_dir=None: isinstance(relative, str) and isinstance(expected, str)
          and len(expected) == 64 and all(c in "0123456789abcdef" for c in expected)
          and isinstance(history, Path) and (git_dir is None or isinstance(git_dir, Path)))
@deal.ensure(lambda relative, expected, history, git_dir=None, result=None:
             isinstance(result, str) and bool(result)
             and (result == str(ROOT.joinpath(relative)) or result.startswith("git:")))
@deal.raises(OSError, ValueError, KeyError, TypeError, JSONDecodeError, subprocess.SubprocessError)
@deal.has("read", "syscall")
def evidence_source(relative: str, expected: str, history: Path, git_dir: Path | None = None) -> str:
    path = Path(relative)
    check(not path.is_absolute() and ".." not in path.parts, "Unsafe source path")
    current = ROOT.joinpath(path)
    if sha(current) == expected:
        return str(current)
    # Ada/SPARK source must still match the working tree. Only historical
    # Python tooling may be resolved to the original immutable Git blob.
    # No uncontracted historical .py copy is kept in the current tree.
    if current.suffix == ".py":
        record = json.loads(history.read_text())
        matches = [entry for entry in record["files"] if entry["path"] == relative and entry["sha256"] == expected]
        check(len(matches) == 1, "Historical source identity is not recorded: " + relative)
        blob = matches[0]["git_blob"]
        check(isinstance(blob, str) and len(blob) == 40 and all(c in "0123456789abcdef" for c in blob), "Invalid Git blob")
        command = ["git", "--git-dir", str(git_dir)] if git_dir else ["git", "-C", str(ROOT)]
        try:
            source = subprocess.check_output([*command, "cat-file", "blob", blob], stderr=subprocess.PIPE, timeout=15)
        except CalledProcessError as error:
            raise ValueError("Historical Git object is missing; fetch repository history or supply --git-dir") from error
        check(hashlib.sha256(source).hexdigest() == expected, "Historical Git source hash differs: " + relative)
        return "git:" + blob
    raise ValueError("Proof source changed: " + relative)


@deal.pre(lambda folder, source_history=DEFAULT_HISTORY, git_dir=None: isinstance(folder, Path) and folder.is_dir()
          and isinstance(source_history, Path) and (git_dir is None or isinstance(git_dir, Path)))
@deal.post(lambda result: result["production_checks"] > 0 and result["portfolio_complete"] is True
           and result["negative_control_rejected"] is True and isinstance(result["historical_python_sources"], list))
@deal.raises(OSError, ValueError, KeyError, TypeError, JSONDecodeError, subprocess.SubprocessError)
@deal.has("read", "syscall")
def verify(folder: Path, source_history: Path = DEFAULT_HISTORY, git_dir: Path | None = None) -> dict:
    folder = folder.resolve()
    manifest = json.loads(folder.joinpath("manifest.json").read_text())
    check(manifest["host"].split(".")[0] == "computer10", "Wrong recorded host")
    check(manifest["portfolio_complete"], "Campaign did not finish successfully")
    evidence_source("verification/run_computer10.py", manifest["runner_sha256"], source_history, git_dir)
    check(sha(folder.joinpath("provers.conf")) == manifest["prover_config_sha256"], "Prover configuration changed")
    totals = 0
    archived_python = []
    for name, runs in manifest["projects"].items():
        for label, recorded in runs.items():
            native = report_summary(folder.joinpath(name, label, "gnatprove.out"))
            check(native == recorded["native"], f"Native report disagrees: {name}/{label}")
            check(sha(folder.joinpath(name, label, "invocation.log")) == recorded["log_sha256"], "Invocation log changed")
            for source in recorded["sources"]:
                evidence_source(source["path"], source["sha256"], source_history, git_dir)
            if label == "portfolio":
                total = native["categories"]["Total"]
                check(recorded["complete"] and recorded["returncode"] == 0 and not recorded["timed_out"], "Incomplete portfolio")
                check(total["unproved"] == total["justified"] == 0, "Unproved or justified portfolio check")
                check(not native["contains_not_proved"], "Native subprogram proof incomplete")
                totals += total["total"]
    control = manifest["negative_control"]
    check(control["expected_failure_rejected"], "Negative control was not rejected")
    bad = report_summary(folder.joinpath("negative_control/portfolio/gnatprove.out"))
    check(bad == control["result"]["native"], "Negative-control report changed")
    check(bad["categories"]["Functional Contracts"]["unproved"] > 0, "Negative control has no failed contract")
    for entry in json.loads(folder.joinpath("source_hashes.json").read_text())["files"]:
        actual_source = evidence_source(entry["path"], entry["sha256"], source_history, git_dir)
        if actual_source.startswith("git:"):
            archived_python.append(entry["path"])
    listed = set()
    for line in folder.joinpath("SHA256SUMS").read_text().splitlines():
        expected, relative = line.split("  ", 1)
        path = folder.joinpath(relative).resolve()
        check(path.is_relative_to(folder), "Unsafe evidence path")
        check(sha(path) == expected, "Evidence checksum mismatch: " + relative)
        listed.add(relative)
    actual = {str(p.relative_to(folder)) for p in folder.rglob("*") if p.is_file() and p.name != "SHA256SUMS"}
    check(listed == actual, "Evidence inventory differs from SHA256SUMS")
    return {"production_checks": totals, "portfolio_complete": True, "negative_control_rejected": True,
            "historical_python_sources": archived_python}


@deal.raises(SystemExit, OSError, ValueError, KeyError, TypeError, JSONDecodeError, subprocess.SubprocessError)
@deal.has("read", "stdout", "stderr", "syscall")
def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("directory", nargs="?", type=Path,
                        default=ROOT.joinpath("verification/evidence/computer10-20261031"))
    parser.add_argument("--source-history", type=Path, default=DEFAULT_HISTORY)
    parser.add_argument("--git-dir", type=Path, help="optional local Git object database for historical sources")
    args = parser.parse_args()
    result = verify(args.directory, args.source_history, args.git_dir)
    print(f"Verified evidence integrity: {result['production_checks']} production checks; zero unproved or justified portfolio checks.")
    print(f"Current Ada/SPARK sources match; {len(result['historical_python_sources'])} historical Python sources match immutable Git objects.")
    print("The deliberately incorrect union contract was rejected. Individual incomplete solver runs remain recorded as incomplete.")


if __name__ == "__main__":
    deal.enable(warn=False)
    main()
