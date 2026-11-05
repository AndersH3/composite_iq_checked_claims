#!/usr/bin/env python3
"""Audit recorded proof integrity, native totals, and current source identity.

This does not replace rerunning GNATprove or independently check SMT proofs.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess

import sys

import deal
from json import JSONDecodeError
from subprocess import CalledProcessError

try:
    from verification.run_computer10 import ROOT, PROJECTS, BASE_REQUIRED_BODIES, REQUIRED_BODIES, report_summary, is_sha256
    from verification.spark_coverage import read_coverage
    from verification.check_symbolic import SCHEMA as SYMBOLIC_SCHEMA, accepted as symbolic_accepted, normalized_source, UnsupportedError
    from verification.spark_contracts import SCHEMA as CONTRACT_SCHEMA, inventory as contract_inventory
    from verification.check_contract_coverage import audit_file, python_files, MINIMUM_CONTRACTS
    from verification.ghost_boundaries import GHOST_SCHEMA, ghost_package, pinned_ada_sources, validate_boundaries
except ModuleNotFoundError:
    from run_computer10 import ROOT, PROJECTS, BASE_REQUIRED_BODIES, REQUIRED_BODIES, report_summary, is_sha256
    from spark_coverage import read_coverage
    from check_symbolic import SCHEMA as SYMBOLIC_SCHEMA, accepted as symbolic_accepted, normalized_source, UnsupportedError
    from spark_contracts import SCHEMA as CONTRACT_SCHEMA, inventory as contract_inventory
    from check_contract_coverage import audit_file, python_files, MINIMUM_CONTRACTS
    from ghost_boundaries import GHOST_SCHEMA, ghost_package, pinned_ada_sources, validate_boundaries

DEFAULT_HISTORY = ROOT.joinpath("verification/source_history.json")
DEFAULT_EVIDENCE = ROOT.joinpath("verification/evidence/symbolic-fixture-computer10-20261105")
LEGACY_CAMPAIGNS = {
    "computer10-20261031", "deal-spark-computer10-20261031",
    "deal-lint-spark-computer10-20261031",
}


@deal.pre(lambda path: isinstance(path, Path))
@deal.post(is_sha256)
@deal.raises(OSError, ValueError)
@deal.has("read")
@deal.ensure(lambda path, result: result == hashlib.sha256(path.read_bytes()).hexdigest())
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


@deal.pre(lambda manifest, campaign_name, explicit_source: isinstance(manifest, dict)
          and isinstance(campaign_name, str) and bool(campaign_name) and isinstance(explicit_source, bool))
@deal.post(lambda result: isinstance(result, bool))
@deal.ensure(lambda manifest, campaign_name, explicit_source, result:
             result == ("coverage_schema" in manifest))
@deal.raises(ValueError)
@deal.has()
def campaign_policy(manifest: dict, campaign_name: str, explicit_source: bool) -> bool:
    """Reject incomplete or downgraded coverage campaigns before auditing files.

    Only the three retained pre-coverage campaigns may use the legacy format,
    and their caller must explicitly select a historical source tree.
    """
    coverage = "coverage_schema" in manifest
    check(coverage or (explicit_source and campaign_name in LEGACY_CAMPAIGNS),
          "Native SPARK coverage schema is required for current or unrecognized campaigns")
    if not coverage:
        return False
    check(manifest["coverage_schema"] == "gnat13-sloc-v1", "Unknown native coverage schema")
    ghost = "ghost_boundary_schema" in manifest
    check(ghost or (explicit_source and campaign_name == "spark-expanded-computer10-20261031"),
          "Ghost boundary schema is required for current or unrecognized coverage campaigns")
    if ghost:
        check(manifest["ghost_boundary_schema"] == GHOST_SCHEMA, "Unknown ghost boundary schema")
        check(is_sha256(manifest.get("ghost_registry_sha256")), "Ghost registry hash is invalid")
        check(isinstance(manifest.get("ghost_negative_control"), dict), "Ghost negative control is missing")
    floor = "contract_floor_schema" in manifest
    prior_coverage = {"spark-expanded-computer10-20261031", "ghost-boundaries-computer10-20261101"}
    check(floor or (explicit_source and campaign_name in prior_coverage),
          "Five-contract schema is required for current or unrecognized campaigns")
    if floor:
        check(manifest["contract_floor_schema"] == CONTRACT_SCHEMA
              and manifest.get("minimum_contracts") == MINIMUM_CONTRACTS, "Invalid five-contract schema or minimum")
        check(all(is_sha256(manifest.get(key)) for key in
                  ("python_contracts_sha256", "contract_checker_sha256", "python_checker_sha256")),
              "Contract checker/inventory hashes are invalid")
    required_policy = REQUIRED_BODIES if ghost else BASE_REQUIRED_BODIES
    projects = manifest.get("projects")
    check(isinstance(projects, dict) and set(projects) == set(PROJECTS),
          "Production project inventory differs from the required projects")
    for name, runs in projects.items():
        check(isinstance(runs, dict) and "portfolio" in runs,
              "Required portfolio is missing: " + name)
        for label, recorded in runs.items():
            check(isinstance(recorded, dict) and "coverage" in recorded,
                  "Native SPARK coverage is missing: " + name + "/" + str(label))
            required = recorded.get("required_full_entities")
            check(isinstance(required, list) and all(isinstance(entity, str) for entity in required)
                  and len(required) == len(required_policy[name])
                  and set(required) == required_policy[name],
                  "Required-body inventory differs from the runner policy: " + name + "/" + str(label))
            if floor:
                check(isinstance(recorded.get("contract_floor"), dict)
                      and recorded["contract_floor"].get("complete") is True,
                      "SPARK contract floor is missing or incomplete: " + name + "/" + str(label))
            if ghost:
                check(isinstance(recorded.get("ghost_boundaries"), dict),
                      "Ghost boundary result is missing: " + name + "/" + str(label))
    symbolic = "symbolic_schema" in manifest
    prior_symbolic = LEGACY_CAMPAIGNS | {"spark-expanded-computer10-20261031",
        "ghost-boundaries-computer10-20261101", "five-contracts-computer10-20261104"}
    check(symbolic or (explicit_source and campaign_name in prior_symbolic),
          "Symbolic verification schema is required for current or unrecognized campaigns")
    if symbolic:
        check(manifest["symbolic_schema"] == SYMBOLIC_SCHEMA, "Unknown symbolic verification schema")
        check(all(is_sha256(manifest.get(key)) for key in
                  ("symbolic_report_sha256", "symbolic_checker_sha256")), "Symbolic report/checker hashes are invalid")
        relative = manifest.get("symbolic_report")
        check(isinstance(relative, str) and bool(relative), "Symbolic report path is missing")
        path = Path(relative)
        check(not path.is_absolute() and ".." not in path.parts and path.suffix == ".json",
              "Unsafe symbolic report path")
    return True


@deal.pre(lambda relative, expected, history, git_dir=None, source_root=ROOT: isinstance(relative, str))
@deal.pre(lambda relative, expected, history, git_dir=None, source_root=ROOT: isinstance(expected, str) and len(expected) == 64 and all((c in '0123456789abcdef' for c in expected)) and isinstance(history, Path) and (git_dir is None or isinstance(git_dir, Path)) and isinstance(source_root, Path) and source_root.is_dir())
@deal.ensure(lambda relative, expected, history, git_dir=None, source_root=ROOT, result=None:
             isinstance(result, str) and bool(result)
             and (result == str(source_root.joinpath(relative)) or result.startswith("git:")))
@deal.raises(OSError, ValueError, KeyError, TypeError, JSONDecodeError, subprocess.SubprocessError)
@deal.has("read", "syscall")
def evidence_source(relative: str, expected: str, history: Path, git_dir: Path | None = None,
                    source_root: Path = ROOT) -> str:
    path = Path(relative)
    check(not path.is_absolute() and ".." not in path.parts, "Unsafe source path")
    current = source_root.joinpath(path)
    check(current.is_file(), "Proof source is missing: " + relative)
    if sha(current) == expected:
        return str(current)
    # Ada/SPARK source must match the explicitly selected source tree. Only historical
    # Python tooling may be resolved to the original immutable Git blob.
    # No uncontracted historical .py copy is kept in the current tree.
    if current.suffix == ".py":
        record = json.loads(history.read_text())
        matches = [entry for entry in record["files"] if entry["path"] == relative and entry["sha256"] == expected]
        check(len(matches) == 1, "Historical source identity is not recorded: " + relative)
        blob = matches[0]["git_blob"]
        check(isinstance(blob, str) and len(blob) == 40 and all(c in "0123456789abcdef" for c in blob), "Invalid Git blob")
        command = ["git", "--git-dir", str(git_dir)] if git_dir else ["git", "-C", str(source_root)]
        try:
            source = subprocess.check_output([*command, "cat-file", "blob", blob], stderr=subprocess.PIPE, timeout=15)
        except CalledProcessError as error:
            raise ValueError("Historical Git object is missing; fetch repository history or supply --git-dir") from error
        check(hashlib.sha256(source).hexdigest() == expected, "Historical Git source hash differs: " + relative)
        return "git:" + blob
    raise ValueError("Proof source changed: " + relative)


@deal.pre(lambda manifest, source_root: isinstance(manifest, dict))
@deal.pre(lambda manifest, source_root: isinstance(source_root, Path) and source_root.is_dir())
@deal.post(lambda result: result is None)
@deal.raises(OSError, ValueError, KeyError, TypeError, JSONDecodeError)
@deal.has("read")
def verify_native_origin(manifest: dict, source_root: Path) -> None:
    """Reused proofs retain exactly the pinned invocation and source records."""
    origin = manifest.get("native_proof_origin")
    if origin is None:
        return None
    check(isinstance(origin, dict), "Native proof origin must be an object")
    relative = origin.get("campaign")
    check(isinstance(relative, str) and relative.startswith("verification/evidence/"),
          "Native proof origin campaign path is invalid")
    path = Path(relative)
    check(not path.is_absolute() and ".." not in path.parts, "Unsafe native proof origin path")
    revision = origin.get("revision")
    check(isinstance(revision, str) and len(revision) == 40
          and set(revision) <= set("0123456789abcdef"), "Native proof origin revision is invalid")
    expected = origin.get("manifest_sha256")
    check(is_sha256(expected), "Native proof origin manifest hash is invalid")
    source = source_root.joinpath(path, "manifest.json")
    check(source.is_file() and not source.is_symlink(), "Native proof origin manifest is missing")
    check(sha(source) == expected, "Native proof origin manifest changed")
    prior = json.loads(source.read_text())
    check(isinstance(prior, dict), "Native proof origin manifest must be an object")
    for key in ("projects", "negative_control", "ghost_negative_control", "toolchain",
                "provers_requested", "prover_config_sha256", "runner_sha256"):
        check(manifest.get(key) == prior.get(key) and key in prior,
              "Reused native proof record differs from its origin: " + key)
    hashes = {name: runs["portfolio"]["native"]["report_sha256"]
              for name, runs in manifest["projects"].items()}
    check(origin.get("native_reports") == hashes, "Native proof origin report inventory differs")
    return None


@deal.pre(lambda folder, manifest, source_root: isinstance(folder, Path) and folder.is_dir())
@deal.pre(lambda folder, manifest, source_root: isinstance(manifest, dict) and isinstance(source_root, Path) and source_root.is_dir())
@deal.post(lambda result: result is None)
@deal.raises(OSError, ValueError, KeyError, TypeError, JSONDecodeError)
@deal.has("read")
def verify_symbolic_record(folder: Path, manifest: dict, source_root: Path) -> None:
    """Validate the recorded outcomes against exact selected-source identities."""
    checker = source_root.joinpath("verification/check_symbolic.py")
    check(checker.is_file() and not checker.is_symlink(), "Symbolic checker must be a regular source file")
    check(sha(checker) == manifest["symbolic_checker_sha256"], "Symbolic checker source changed")
    relative = manifest["symbolic_report"]
    check(isinstance(relative, str) and bool(relative), "Symbolic report path is missing")
    report_path = folder.joinpath(relative)
    check(report_path.resolve().is_relative_to(folder.resolve()), "Unsafe symbolic report path")
    check(report_path.is_file() and not report_path.is_symlink(), "Symbolic report must be a regular file")
    check(sha(report_path) == manifest["symbolic_report_sha256"], "Symbolic report changed")
    symbolic = json.loads(report_path.read_text())
    check(isinstance(symbolic, dict) and symbolic.get("complete") is True and symbolic_accepted(symbolic),
          "Symbolic verification outcomes are missing, unsupported or incorrect")
    expected_sources = {"verification/proof_gate.py", "tests/fixtures/contract_negative_control.py"}
    sources = symbolic.get("files")
    check(isinstance(sources, list) and len(sources) == len(expected_sources)
          and all(isinstance(entry, dict) for entry in sources)
          and {entry.get("path") for entry in sources} == expected_sources,
          "Symbolic source inventory differs")
    for entry in sources:
        check(is_sha256(entry.get("sha256")), "Symbolic source hash is invalid")
        path = source_root.joinpath(entry["path"])
        check(path.is_file() and not path.is_symlink(), "Symbolic input must be a regular source file")
        check(sha(path) == entry["sha256"], "Symbolic input source changed: " + entry["path"])
        try:
            normalized = normalized_source(path.read_text())
        except (SyntaxError, UnsupportedError) as error:
            raise ValueError("Symbolic input normalization is unsupported: " + entry["path"]) from error
        normalized_sha = hashlib.sha256(normalized.encode("utf-8")).hexdigest()
        check(entry.get("normalized_sha256") == normalized_sha,
              "Symbolic normalized source differs: " + entry["path"])
    return None


@deal.pre(lambda folder, source_history=DEFAULT_HISTORY, git_dir=None, source_root=ROOT: isinstance(folder, Path))
@deal.pre(lambda folder, source_history=DEFAULT_HISTORY, git_dir=None, source_root=ROOT: folder.is_dir() and isinstance(source_history, Path) and (git_dir is None or isinstance(git_dir, Path)) and isinstance(source_root, Path) and source_root.is_dir())
@deal.post(lambda result: result["production_checks"] > 0 and result["portfolio_complete"] is True
           and result["negative_control_rejected"] is True and isinstance(result["historical_python_sources"], list))
@deal.raises(OSError, ValueError, KeyError, TypeError, SyntaxError, JSONDecodeError, subprocess.SubprocessError)
@deal.has("read", "syscall", "import")
def verify(folder: Path, source_history: Path = DEFAULT_HISTORY, git_dir: Path | None = None,
           source_root: Path = ROOT) -> dict:
    folder = folder.resolve()
    manifest = json.loads(folder.joinpath("manifest.json").read_text())
    check(isinstance(manifest, dict), "Campaign manifest must be an object")
    coverage_campaign = campaign_policy(manifest, folder.name, source_root.resolve() != ROOT)
    check(manifest["host"].split(".")[0] == "computer10", "Wrong recorded host")
    check(manifest["portfolio_complete"], "Campaign did not finish successfully")
    verify_native_origin(manifest, source_root)
    registry = None
    if "ghost_boundary_schema" in manifest:
        registry_path = folder.joinpath("ghost_boundaries.json")
        check(registry_path.is_file(), "Ghost registry file is missing")
        check(sha(registry_path) == manifest["ghost_registry_sha256"], "Ghost registry changed")
        evidence_source("verification/ghost_boundaries.json", manifest["ghost_registry_sha256"],
                        source_history, git_dir, source_root)
        registry = json.loads(registry_path.read_text())
    evidence_source("verification/run_computer10.py", manifest["runner_sha256"], source_history, git_dir, source_root)
    check(sha(folder.joinpath("provers.conf")) == manifest["prover_config_sha256"], "Prover configuration changed")
    if "contract_floor_schema" in manifest:
        for relative, key in (("verification/spark_contracts.py", "contract_checker_sha256"),
                              ("verification/check_contract_coverage.py", "python_checker_sha256")):
            evidence_source(relative, manifest[key], source_history, git_dir, source_root)
        python_path = folder.joinpath("python_contracts.json")
        check(sha(python_path) == manifest["python_contracts_sha256"], "Python contract inventory changed")
        python_inventory = [audit_file(path) for path in python_files(source_root)]
        for row in python_inventory:
            row["path"] = str(Path(row["path"]).relative_to(source_root))
            row["sha256"] = sha(source_root.joinpath(row["path"]))
        check(python_inventory == json.loads(python_path.read_text()), "Python contract inventory differs from selected source")
        check(all(not row["insufficient"] and not row["duplicated"] and row["imports_deal"] for row in python_inventory),
              "Python five-contract floor failed")
    if "symbolic_schema" in manifest:
        verify_symbolic_record(folder, manifest, source_root)
    totals = 0
    archived_python = []
    for name, runs in manifest["projects"].items():
        for label, recorded in runs.items():
            native = report_summary(folder.joinpath(name, label, "gnatprove.out"))
            check(native == recorded["native"], f"Native report disagrees: {name}/{label}")
            check(sha(folder.joinpath(name, label, "invocation.log")) == recorded["log_sha256"], "Invocation log changed")
            for source in recorded["sources"]:
                evidence_source(source["path"], source["sha256"], source_history, git_dir, source_root)
            if "coverage" in recorded:
                coverage = read_coverage(folder.joinpath(name, label, "spark"),
                    {Path(entry["path"]).name for entry in recorded["sources"]
                     if Path(entry["path"]).suffix in {".ads", ".adb"}})
                check(coverage == recorded["coverage"], "Native SPARK coverage disagrees: " + name + "/" + label)
                check(coverage["no_assumptions_or_suppressions"], "Assumption or suppression in native SPARK coverage")
                analyzed = {row["name"].casefold() for row in coverage["entities"] if row["status"] == "all"}
                missing = [entity for entity in recorded["required_full_entities"] if entity.casefold() not in analyzed]
                check(missing == recorded["missing_full_entities"], "Required-body coverage record disagrees")
                if "contract_floor_schema" in manifest:
                    floor = contract_inventory(pinned_ada_sources(recorded["sources"], source_root), coverage)
                    check(floor == recorded["contract_floor"] and floor["complete"],
                          "SPARK contract inventory differs or is incomplete: " + name + "/" + label)
                if registry is not None:
                    ghost = validate_boundaries(registry, name, coverage, recorded["sources"], source_root)
                    check(ghost == recorded["ghost_boundaries"], "Ghost boundary coverage disagrees: " + name + "/" + label)
            if label == "portfolio":
                total = native["categories"]["Total"]
                check(recorded["complete"] and recorded["returncode"] == 0 and not recorded["timed_out"], "Incomplete portfolio")
                check(total["unproved"] == total["justified"] == 0, "Unproved or justified portfolio check")
                check(not native["contains_not_proved"], "Native subprogram proof incomplete")
                if coverage_campaign:
                    check(bool(recorded["required_full_entities"]) and not recorded["missing_full_entities"],
                          "A required numerical or driver body was not analyzed")
                totals += total["total"]
    control = manifest["negative_control"]
    if coverage_campaign:
        recorded_control = control["result"]
        control_coverage = read_coverage(folder.joinpath("negative_control/portfolio/spark"),
            {Path(entry["path"]).name for entry in recorded_control["sources"]
             if Path(entry["path"]).suffix in {".ads", ".adb"}})
        check(control_coverage == recorded_control.get("coverage"), "Negative-control native coverage disagrees")
        check(control_coverage["no_assumptions_or_suppressions"], "Assumption or suppression in negative control")
    check(control["expected_failure_rejected"], "Negative control was not rejected")
    bad = report_summary(folder.joinpath("negative_control/portfolio/gnatprove.out"))
    check(bad == control["result"]["native"], "Negative-control report changed")
    check(bad["categories"]["Functional Contracts"]["unproved"] > 0, "Negative control has no failed contract")
    if registry is not None:
        ghost_control = manifest["ghost_negative_control"]
        recorded = ghost_control["result"]
        check(ghost_control["expected_failure_rejected"] and recorded["returncode"] != 0
              and not recorded["timed_out"], "Ghost negative control was not rejected")
        ghost_native = report_summary(folder.joinpath("ghost_negative_control/portfolio/gnatprove.out"))
        check(ghost_native == recorded["native"], "Ghost negative-control report changed")
        check(ghost_native["categories"]["Functional Contracts"]["unproved"] > 0,
              "Ghost negative control has no failed contract")
        check(sha(folder.joinpath("ghost_negative_control/portfolio/invocation.log")) == recorded["log_sha256"],
              "Ghost negative-control invocation changed")
        for source in recorded["sources"]:
            evidence_source(source["path"], source["sha256"], source_history, git_dir, source_root)
        ghost_sources = pinned_ada_sources(recorded["sources"], source_root)
        ghost_spec = [text for path, text in ghost_sources.items() if Path(path).name == "negative_ghost_ledger.ads"]
        check(len(ghost_spec) == 1 and ghost_package(ghost_spec[0]).casefold() == "negative_ghost_ledger",
              "Ghost negative control lacks its Ghost declaration")
        ghost_coverage = read_coverage(folder.joinpath("ghost_negative_control/portfolio/spark"),
            {Path(entry["path"]).name for entry in recorded["sources"]
             if Path(entry["path"]).suffix in {".ads", ".adb"}})
        check(ghost_coverage == recorded["coverage"] and ghost_coverage["no_assumptions_or_suppressions"],
              "Ghost negative-control coverage disagrees")
        check(any(row["name"].casefold() == "negative_ghost_ledger.record_event" and row["status"] == "all"
                  for row in ghost_coverage["entities"]), "Ghost negative-control body was not analyzed")
    for entry in json.loads(folder.joinpath("source_hashes.json").read_text())["files"]:
        actual_source = evidence_source(entry["path"], entry["sha256"], source_history, git_dir, source_root)
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
            "historical_python_sources": archived_python,
            "source_root": str(source_root.resolve()),
            "source_context": "current" if source_root.resolve() == ROOT else "explicit"}


@deal.raises(SystemExit, OSError, ValueError, KeyError, TypeError, SyntaxError, JSONDecodeError, subprocess.SubprocessError)
@deal.has("read", "stdout", "stderr", "syscall", "import")
@deal.pre(lambda: isinstance(sys.argv, list))
@deal.pre(lambda: all(isinstance(argument, str) for argument in sys.argv))
@deal.pre(lambda: ROOT.is_dir())
def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("directory", nargs="?", type=Path,
                        default=DEFAULT_EVIDENCE)
    parser.add_argument("--source-history", type=Path, default=DEFAULT_HISTORY)
    parser.add_argument("--git-dir", type=Path, help="optional local Git object database for historical sources")
    parser.add_argument("--source-root", type=Path, default=ROOT,
                        help="explicit source tree for a historical campaign; defaults to the current repository")
    args = parser.parse_args()
    result = verify(args.directory, args.source_history, args.git_dir, args.source_root)
    print(f"Verified evidence integrity: {result['production_checks']} production checks; zero unproved or justified portfolio checks.")
    print(f"Selected {result['source_context']} source tree: {result['source_root']}")
    print(f"Ada/SPARK source identities match; {len(result['historical_python_sources'])} historical Python sources match immutable Git objects.")
    print("The deliberately incorrect union contract was rejected. Individual incomplete solver runs remain recorded as incomplete.")


if __name__ == "__main__":
    deal.enable(warn=False)
    main()
