#!/usr/bin/env python3
"""Audit recorded proof integrity, native totals, and current source identity.

This does not replace rerunning GNATprove or independently check SMT proofs.
"""
import argparse
import hashlib
import json
from pathlib import Path

from run_computer10 import ROOT, report_summary


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def check(condition, message):
    if not condition:
        raise ValueError(message)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("directory", nargs="?", type=Path,
                        default=ROOT / "verification/evidence/computer10-20261031")
    folder = parser.parse_args().directory.resolve()
    manifest = json.loads((folder / "manifest.json").read_text())
    check(manifest["host"].split(".")[0] == "computer10", "Wrong recorded host")
    check(manifest["portfolio_complete"], "Campaign did not finish successfully")
    check(sha(ROOT / "verification/run_computer10.py") == manifest["runner_sha256"], "Runner source changed")
    check(sha(folder / "provers.conf") == manifest["prover_config_sha256"], "Prover configuration changed")
    totals = 0
    for name, runs in manifest["projects"].items():
        for label, recorded in runs.items():
            native = report_summary(folder / name / label / "gnatprove.out")
            check(native == recorded["native"], f"Native report disagrees: {name}/{label}")
            check(sha(folder / name / label / "invocation.log") == recorded["log_sha256"], "Invocation log changed")
            for source in recorded["sources"]:
                check(sha(ROOT / source["path"]) == source["sha256"], "Proof source changed: " + source["path"])
            if label == "portfolio":
                total = native["categories"]["Total"]
                check(recorded["complete"] and recorded["returncode"] == 0 and not recorded["timed_out"], "Incomplete portfolio")
                check(total["unproved"] == total["justified"] == 0, "Unproved or justified portfolio check")
                check(not native["contains_not_proved"], "Native subprogram proof incomplete")
                totals += total["total"]
    control = manifest["negative_control"]
    check(control["expected_failure_rejected"], "Negative control was not rejected")
    bad = report_summary(folder / "negative_control/portfolio/gnatprove.out")
    check(bad == control["result"]["native"], "Negative-control report changed")
    check(bad["categories"]["Functional Contracts"]["unproved"] > 0, "Negative control has no failed contract")
    for entry in json.loads((folder / "source_hashes.json").read_text())["files"]:
        check(sha(ROOT / entry["path"]) == entry["sha256"], "Source inventory changed: " + entry["path"])
    listed = set()
    for line in (folder / "SHA256SUMS").read_text().splitlines():
        expected, relative = line.split("  ", 1)
        path = (folder / relative).resolve()
        check(path.is_relative_to(folder), "Unsafe evidence path")
        check(sha(path) == expected, "Evidence checksum mismatch: " + relative)
        listed.add(relative)
    actual = {str(p.relative_to(folder)) for p in folder.rglob("*") if p.is_file() and p.name != "SHA256SUMS"}
    check(listed == actual, "Evidence inventory differs from SHA256SUMS")
    print(f"Verified source identity and evidence integrity: {totals} production checks; zero unproved or justified portfolio checks.")
    print("The deliberately incorrect union contract was rejected. Individual incomplete solver runs remain recorded as incomplete.")


if __name__ == "__main__":
    main()
