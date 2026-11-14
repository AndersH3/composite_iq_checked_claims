#!/usr/bin/env python3
"""Audit unchanged Ada proof evidence and revalidate it with current Python.

This read-only audit does not invoke GNATprove. Python-only integration fixes
need new Python checks, rather than another proof of identical Ada bytes.
"""
import argparse
import hashlib
import json
from json import JSONDecodeError
from pathlib import Path
import tarfile

import deal
from numpy.linalg import LinAlgError

# Reuse the campaign's maintained parsers and validator; do not implement a
# second native-proof parser or a second interpretation of simulation results.
from run_spark import (ROOT, ANALYSIS_RELATIVE, digest, report_summary,
                       read_coverage, inventory, validate)


@deal.pre(lambda source_root, evidence: isinstance(source_root, Path) and source_root.is_dir())
@deal.pre(lambda source_root, evidence: isinstance(evidence, Path) and evidence.is_dir() and evidence.joinpath("campaign.json").is_file())
@deal.post(lambda result: isinstance(result, dict) and result["schema"] == "sequential-current-audit-v1")
@deal.post(lambda result: result["complete"] is True and result["validation"]["complete"] is True)
@deal.post(lambda result: result["native_total"] > 0 and result["ada_sources_checked"] > 0)
@deal.ensure(lambda source_root, evidence, result: result["source_context"] == str(source_root.resolve()))
@deal.ensure(lambda source_root, evidence, result: result["evidence"] == str(evidence.resolve()))
@deal.ensure(lambda source_root, evidence, result: result["current_validator_sha256"] == digest(Path(__file__).with_name("validate_spark.py")))
@deal.raises(OSError, ValueError, TypeError, KeyError, JSONDecodeError, tarfile.TarError, LinAlgError)
@deal.has("read")
def audit_campaign(source_root, evidence):
    """Check every artifact/source hash, native scope and current CSV results.

    The archived original Python is verified against its own snapshot. All
    Ada/project files must match the current checkout exactly; differences
    reject the audit. Python differences are disclosed explicitly. Numerical
    revalidation always calls the CURRENT Deal-contracted implementation.
    """
    record = json.loads(evidence.joinpath("campaign.json").read_text())
    if record.get("schema") != "sequential-fresh-campaign-v1" or record.get("complete") is not True:
        raise ValueError("Only a completed native campaign can be audited")
    for artifact in record["artifacts"]:
        relative = Path(artifact["path"])
        if relative.is_absolute() or ".." in relative.parts:
            raise ValueError("Unsafe retained artifact path")
        path = evidence.joinpath(relative)
        if not path.is_file() or path.is_symlink() or digest(path) != artifact["sha256"]:
            raise ValueError("Retained artifact hash differs: " + str(relative))
    ada_count, python_changes = 0, []
    with tarfile.open(evidence.joinpath("sources.tar.gz"), "r:gz") as archive:
        members = {member.name: member for member in archive.getmembers()}
        if len(members) != len(record["sources"]):
            raise ValueError("Compressed source inventory differs")
        for source in record["sources"]:
            relative = Path(source["path"])
            if relative.is_absolute() or ".." in relative.parts:
                raise ValueError("Unsafe retained source path")
            member = members.get(source["path"])
            if member is None or not member.isfile():
                raise ValueError("Source archive member missing or nonregular")
            with archive.extractfile(member) as stream:
                if hashlib.sha256(stream.read()).hexdigest() != source["sha256"]:
                    raise ValueError("Compressed source hash differs: " + source["path"])
            current = source_root.joinpath(relative)
            if relative.suffix in {".ads", ".adb", ".gpr"}:
                if not current.is_file() or digest(current) != source["sha256"]:
                    raise ValueError("Current Ada/project hash differs: " + source["path"])
                ada_count += 1
            elif relative.suffix == ".py" and (not current.is_file() or digest(current) != source["sha256"]):
                python_changes.append(source["path"])
    native = report_summary(evidence.joinpath("gnatprove.out"))
    if native != record["native"] or native["contains_not_proved"]:
        raise ValueError("Native proof summary differs")
    total = native["categories"]["Total"]
    if total["unproved"] or total["justified"] or record["proof"]["returncode"] != 0:
        raise ValueError("Native campaign did not discharge every obligation")
    sources = {source["path"]: source_root.joinpath(source["path"]).read_text()
               for source in record["sources"] if source["path"].startswith(ANALYSIS_RELATIVE.as_posix())
               and Path(source["path"]).suffix in {".ads", ".adb"}
               and Path(source["path"]).name != "sequential_run.adb"}
    coverage = read_coverage(evidence.joinpath("spark"), {Path(path).name for path in sources})
    if coverage != record["coverage"] or inventory(sources, coverage) != record["native_contract_floor"]:
        raise ValueError("Current native coverage or contract inventory differs")
    return {"schema": "sequential-current-audit-v1", "complete": True,
            "source_context": str(source_root.resolve()), "evidence": str(evidence.resolve()),
            "campaign_sha256": digest(evidence.joinpath("campaign.json")),
            "native_total": total["total"], "ada_sources_checked": ada_count,
            "python_sources_changed_since_native_run": python_changes,
            "current_auditor_sha256": digest(Path(__file__)),
            "current_validator_sha256": digest(Path(__file__).with_name("validate_spark.py")),
            "validation": validate(evidence.joinpath("runtime")), "new_prover_invocation": False}


if __name__ == "__main__":
    deal.enable(warn=False)
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("evidence", type=Path)
    parser.add_argument("--source-root", type=Path, default=ROOT)
    arguments = parser.parse_args()
    print(json.dumps(audit_campaign(Path(arguments.source_root).resolve(), Path(arguments.evidence).resolve()), indent=2))
