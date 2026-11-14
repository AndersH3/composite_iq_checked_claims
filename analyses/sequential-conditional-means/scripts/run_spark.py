#!/usr/bin/env python3
"""Record a fresh sequential-score build, native SPARK proof and simulation run.

Existing campaigns are immutable.  Every invocation creates a new evidence
directory and builds copied current sources in an empty temporary mirror.
Native proof coverage, trusted boundaries, numerical validation and sampling
diagnostics are recorded separately; a failed phase remains a failed phase.
"""
import argparse
from datetime import datetime, timezone
import json
from pathlib import Path
import shutil
import socket
import subprocess
import sys
import tarfile
from subprocess import CalledProcessError, TimeoutExpired
from shutil import SameFileError, SpecialFileError
from tempfile import TemporaryDirectory

import deal
from numpy.linalg import LinAlgError

ROOT = Path(__file__).resolve().parents[3]
ANALYSIS_RELATIVE = Path("analyses/sequential-conditional-means")
LIBRARY_RELATIVE = Path("analyses/hoeflin-ferguson/ada/src")
LIBRARY_FILES = ("hoeflin_core.ads", "hoeflin_core.adb", "hoeflin_boundary_models.ads",
                 "hoeflin_boundary_models.adb", "normal_support.ads", "normal_support.adb")
PROVERS = ("cvc5", "z3", "altergo", "Colibri_Classic", "Yices")
sys.path.insert(0, str(ROOT))
sys.path.insert(0, str(Path(__file__).resolve().parent))
from verification.run_computer10 import digest, dump, environment, execute, report_summary, utc, version_record
from verification.spark_coverage import read_coverage
from verification.spark_contracts import inventory, ten_contract_summary
from validate_spark import validate


@deal.pre(lambda env, output: isinstance(env, dict) and all(isinstance(key, str) and isinstance(value, str) for key, value in env.items()))
@deal.pre(lambda env, output: all(key in env for key in ("GNATPROVE_ALIRE_PREFIX", "GNAT_NATIVE_ALIRE_PREFIX", "GPRBUILD_ALIRE_PREFIX", "PATH")))
@deal.pre(lambda env, output: isinstance(output, Path) and output.is_dir() and not output.joinpath("provers.conf").exists())
@deal.post(lambda result: isinstance(result, dict) and result.keys() == {"configuration", "configuration_sha256", "tools", "provers"})
@deal.post(lambda result: result["provers"] == list(PROVERS) and len(result["configuration_sha256"]) == 64)
@deal.post(lambda result: set(result["tools"]) == set(PROVERS) | {"gnatprove", "gnat", "gprbuild"})
@deal.ensure(lambda env, output, result: output.joinpath("provers.conf").is_file() and digest(output.joinpath("provers.conf")) == result["configuration_sha256"])
@deal.ensure(lambda env, output, result: Path(result["configuration"]) == output.joinpath("provers.conf"))
@deal.raises(OSError, ValueError, TypeError, subprocess.SubprocessError, CalledProcessError, TimeoutExpired)
@deal.has("read", "write", "syscall")
def configure_toolchain(env, output):
    """Reuse the established five-prover portfolio and hash every executable.

    GNATprove discovers its bundled SMT solvers itself.  The extra Why3
    entries name the already installed Yices and classic Colibri drivers.
    Configuration follows verification/run_computer10.py; it does not modify
    that historical campaign runner or install any replacement tools.
    """
    prefix = Path(env["GNATPROVE_ALIRE_PREFIX"])
    binaries = prefix.joinpath("libexec", "spark", "bin")
    paths = {"cvc5": binaries.joinpath("cvc5"), "z3": binaries.joinpath("z3"),
             "altergo": binaries.joinpath("alt-ergo"),
             "Colibri_Classic": Path(shutil.which("colibri", path=env["PATH"]) or "/missing/colibri"),
             "Yices": Path("/usr/local/bin/yices-smt2")}
    if not all(path.is_file() for path in paths.values()):
        raise ValueError("A requested portfolio prover is unavailable")
    configuration = output.joinpath("provers.conf")
    configuration.write_text('[prover]\nname = "Yices"\nversion = "2.7.0"\nalternative = "SMT2"\ncommand = '
                             + json.dumps(str(paths["Yices"]) + " --timeout=%t %f") + '\ndriver = '
                             + json.dumps(str(prefix.joinpath("libexec/spark/share/why3/drivers/yices-smt2.drv")))
                             + '\n\n[prover]\nname = "Colibri_Classic"\nversion = "2026.06-v7"\ncommand = '
                             + json.dumps(str(paths["Colibri_Classic"]) + " --get-steps --memlimit %m %f")
                             + '\ncommand_steps = '
                             + json.dumps(str(paths["Colibri_Classic"]) + " --get-steps --max-steps %S --memlimit %m %f")
                             + '\ndriver = '
                             + json.dumps(str(prefix.joinpath("libexec/spark/share/why3/drivers/colibri.drv"))) + "\n")
    tools = {"gnatprove": version_record(prefix.joinpath("bin", "gnatprove"), ["--version"], env),
             "gnat": version_record(Path(env["GNAT_NATIVE_ALIRE_PREFIX"]).joinpath("bin", "gnat"), ["--version"], env),
             "gprbuild": version_record(Path(env["GPRBUILD_ALIRE_PREFIX"]).joinpath("bin", "gprbuild"), ["--version"], env)}
    for name in PROVERS:
        tools[name] = version_record(paths[name], ["-version"] if name == "z3" else ["--version"], env)
    return {"configuration": str(configuration), "configuration_sha256": digest(configuration),
            "tools": tools, "provers": list(PROVERS)}


@deal.pre(lambda source_root, mirror: isinstance(source_root, Path) and source_root.is_dir())
@deal.pre(lambda source_root, mirror: isinstance(mirror, Path) and mirror.is_dir() and not any(mirror.iterdir()))
@deal.pre(lambda source_root, mirror: source_root.joinpath(ANALYSIS_RELATIVE, "ada", "sequential.gpr").is_file())
@deal.post(lambda result: isinstance(result, list) and all(row.keys() == {"path", "sha256"} for row in result))
@deal.post(lambda result: len({row["path"] for row in result}) == len(result) and all(len(row["sha256"]) == 64 for row in result))
@deal.ensure(lambda source_root, mirror, result: bool(result) and all(mirror.joinpath(row["path"]).is_file() and digest(mirror.joinpath(row["path"])) == row["sha256"] for row in result))
@deal.ensure(lambda source_root, mirror, result: all(digest(source_root.joinpath(row["path"])) == row["sha256"] for row in result))
@deal.ensure(lambda source_root, mirror, result: all(not Path(row["path"]).is_absolute() and ".." not in Path(row["path"]).parts for row in result))
@deal.raises(OSError, ValueError, shutil.Error, SameFileError, SpecialFileError)
@deal.has("read", "write")
def capture_sources(source_root, mirror):
    """Copy current project sources while preserving their relative GPR paths.

    Only source files enter the empty mirror.  Existing objects, proof caches,
    executables and old evidence cannot influence a fresh campaign.  Python
    orchestration dependencies are retained too so the audit can identify the
    exact validator and coverage parsers used to interpret native evidence.
    """
    ada_root = source_root.joinpath(ANALYSIS_RELATIVE, "ada")
    selected = list(ada_root.glob("*.gpr")) + list(ada_root.joinpath("src").glob("*.ads")) + list(ada_root.joinpath("src").glob("*.adb"))
    selected += [source_root.joinpath(LIBRARY_RELATIVE, name) for name in LIBRARY_FILES]
    selected += list(source_root.joinpath("verification").glob("*.py"))
    selected += list(source_root.joinpath(ANALYSIS_RELATIVE, "scripts").glob("*.py"))
    selected += [source_root.joinpath("requirements-dev.txt"), source_root.joinpath("AGENTS.md")]
    records = []
    for path in sorted(set(selected)):
        if not path.is_file() or path.is_symlink():
            raise ValueError("Campaign inputs must be existing regular source files: " + str(path))
        relative = path.relative_to(source_root)
        destination = mirror.joinpath(relative)
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(path, destination)
        records.append({"path": relative.as_posix(), "sha256": digest(destination)})
    if not records:
        raise ValueError("The source inventory cannot be empty")
    # Return an independent list after the explicit nonempty check; this also
    # avoids the static linter treating the loop-mutated initial list as empty.
    return list(records)


@deal.pre(lambda source_root, output, alire_dir, trials=200000, wall_seconds=1800: isinstance(source_root, Path) and source_root.is_dir())
@deal.pre(lambda source_root, output, alire_dir, trials=200000, wall_seconds=1800: isinstance(output, Path) and output.is_absolute() and not output.exists())
@deal.pre(lambda source_root, output, alire_dir, trials=200000, wall_seconds=1800: isinstance(alire_dir, Path) and alire_dir.is_dir())
@deal.pre(lambda source_root, output, alire_dir, trials=200000, wall_seconds=1800: type(trials) is int and 2 <= trials <= 1_000_000)
@deal.pre(lambda source_root, output, alire_dir, trials=200000, wall_seconds=1800: type(wall_seconds) is int and 1 <= wall_seconds <= 86400)
@deal.post(lambda result: isinstance(result, dict) and type(result["complete"]) is bool and result["schema"] == "sequential-fresh-campaign-v1")
@deal.ensure(lambda source_root, output, alire_dir, trials=200000, wall_seconds=1800, result=None: output.joinpath("campaign.json").is_file() and json.loads(output.joinpath("campaign.json").read_text()) == result)
@deal.ensure(lambda source_root, output, alire_dir, trials=200000, wall_seconds=1800, result=None: result["trials"] == trials and result["source_context"] == str(source_root.resolve()))
@deal.raises(OSError, ValueError, TypeError, shutil.Error, SameFileError, SpecialFileError, subprocess.SubprocessError, CalledProcessError, TimeoutExpired, LinAlgError)
@deal.has("io", "syscall", "time", "random")
def run_campaign(source_root, output, alire_dir, trials=200000, wall_seconds=1800):
    """Keep complete evidence even when native proof or runtime validation fails.

    The completion predicate requires native proof totals, coverage of current
    new-package bodies, contract inventories, a checked build and a successful
    independent numerical/statistical validator.  Reused numerical/PRNG bodies
    retain their existing trusted boundaries and are explicitly identified.
    No negative-control campaign is silently implied by this result.
    """
    output.mkdir(parents=True, exist_ok=False)
    report = {"schema": "sequential-fresh-campaign-v1", "host": socket.gethostname(),
              "started_utc": utc(), "source_context": str(source_root.resolve()), "trials": trials,
              "runner_sha256": digest(Path(__file__)), "complete": False,
              "negative_controls_run": False,
              "limits": ["SPARK_Mode Off CLI and numerical completions are trusted boundaries.",
                         "Native proof establishes discharged program obligations under its model.",
                         "Numerical and Monte Carlo validation are separate from formal proof."]}
    dump(output.joinpath("campaign.json"), report)
    try:
        env = environment(alire_dir)
        report["toolchain"] = configure_toolchain(env, output)
        with TemporaryDirectory(prefix="sequential-fresh-") as temporary:
            mirror = Path(temporary)
            report["sources"] = capture_sources(source_root, mirror)
            # Preserve the exact pre-build mirror for later source-context
            # audits, while compiler/prover objects remain temporary.
            # A compressed source archive preserves the analyzed bytes without
            # creating extra executable Python copies in the current tree.
            with tarfile.open(output.joinpath("sources.tar.gz"), "x:gz") as archive:
                for source in report["sources"]:
                    archive.add(mirror.joinpath(source["path"]), arcname=source["path"])
            ada = mirror.joinpath(ANALYSIS_RELATIVE, "ada")
            new_sources = {row["path"]: mirror.joinpath(row["path"]).read_text()
                           for row in report["sources"] if row["path"].startswith(ANALYSIS_RELATIVE.as_posix())
                           and Path(row["path"]).suffix in {".ads", ".adb"}}
            report["contract_floor"] = inventory(new_sources)
            report["ten_contract_target"] = ten_contract_summary(report["contract_floor"])
            reused_sources = {row["path"]: mirror.joinpath(row["path"]).read_text()
                              for row in report["sources"] if row["path"].startswith(LIBRARY_RELATIVE.as_posix())
                              and Path(row["path"]).suffix in {".ads", ".adb"}}
            report["reused_contract_floor"] = inventory(reused_sources)
            report["trusted_reused_completions"] = report["reused_contract_floor"]["excluded_completions"]
            report["excluded_cli"] = {"path": ANALYSIS_RELATIVE.joinpath("ada", "src", "sequential_run.adb").as_posix(),
                                      "reason": "SPARK_Mode Off command-line, filesystem and diagnostics boundary"}
            native_sources = {path: text for path, text in new_sources.items() if Path(path).name != "sequential_run.adb"}
            tools = report["toolchain"]["tools"]
            report["build"] = execute([tools["gprbuild"]["path"], "-P", "sequential.gpr", "-p", "-f", "-j2"],
                                      ada, env, output.joinpath("build.log"), wall_seconds)
            proof_command = [tools["gnatprove"]["path"], "-P", "sequential_proof.gpr", "--mode=all", "--level=2",
                             "--steps=0", "--checks-as-errors", "--warnings=error", "--report=statistics",
                             "--counterexamples=off", "-f", "-U", "-j2", "--no-subprojects", "--timeout=30",
                             "--prover=" + ",".join(PROVERS), "--why3-conf=" + report["toolchain"]["configuration"]]
            report["proof"] = execute(proof_command, ada, env, output.joinpath("proof.log"), wall_seconds)
            native_reports = list(ada.rglob("gnatprove.out"))
            if len(native_reports) == 1:
                native_report = output.joinpath("gnatprove.out")
                shutil.copyfile(native_reports[0], native_report)
                try:
                    report["native"] = report_summary(native_report)
                except ValueError as error:
                    report["native_error"] = str(error)
            else:
                report["native_error"] = "Expected exactly one fresh gnatprove.out, found " + str(len(native_reports))
            raw_directory = output.joinpath("spark")
            raw_directory.mkdir()
            for path in sorted(ada.rglob("*.spark")):
                destination = raw_directory.joinpath(path.relative_to(ada))
                destination.parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(path, destination)
            try:
                report["coverage"] = read_coverage(raw_directory, {Path(path).name for path in native_sources})
                report["native_contract_floor"] = inventory(native_sources, report["coverage"])
                required_bodies = {"sequential_core.d_numerator", "sequential_core.valid",
                                   "sequential_core.calculate", "sequential_core.limits",
                                   "sequential_experiments.value", "sequential_experiments.from_coefficients",
                                   "sequential_experiments.reset", "sequential_experiments.add",
                                   "sequential_experiments.finish", "sequential_sampling.draw"}
                bodies = {row["name"].casefold() for row in report["coverage"]["entities"] if row["status"] == "all"}
                report["missing_bodies"] = sorted(required_bodies - bodies)
                report["trusted_new_entities"] = [row["name"] for row in report["coverage"]["entities"] if row["status"] == "spec"]
                report["unexpected_spec_entities"] = [name for name in report["trusted_new_entities"]
                                                       if name.casefold() != "sequential_sampling.checked_sqrt"]
            except ValueError as error:
                report["coverage_error"] = str(error)
            runtime_directory = output.joinpath("runtime")
            runtime_directory.mkdir()
            if report["build"]["returncode"] == 0:
                report["runtime"] = execute([str(ada.joinpath("bin", "sequential_run")), str(trials)], runtime_directory,
                                            env, output.joinpath("runtime.log"), wall_seconds)
                if report["runtime"]["returncode"] == 0:
                    try:
                        report["validation"] = validate(runtime_directory)
                        dump(runtime_directory.joinpath("validation.json"), report["validation"])
                    except (ValueError, LinAlgError) as error:
                        report["validation_error"] = str(error)
            total = report.get("native", {}).get("categories", {}).get("Total", {})
            report["complete"] = (report["build"]["returncode"] == 0 and report["proof"]["returncode"] == 0
                                  and total.get("total", 0) > 0 and total.get("unproved", -1) == 0 and total.get("justified", -1) == 0
                                  and not report.get("native", {}).get("contains_not_proved", True)
                                  and report.get("coverage", {}).get("no_assumptions_or_suppressions", False)
                                  and report.get("coverage", {}).get("counts", {}).get("no", -1) == 0
                                  and report.get("missing_bodies", ["missing coverage"]) == []
                                  and report.get("unexpected_spec_entities", ["missing coverage"]) == []
                                  and report.get("trusted_new_entities", []) == ["Sequential_Sampling.Checked_Sqrt"]
                                  and report["contract_floor"]["complete"] and report["reused_contract_floor"]["complete"]
                                  and report.get("native_contract_floor", {}).get("complete", False)
                                  and report.get("runtime", {}).get("returncode", -1) == 0 and report.get("validation", {}).get("complete", False))
    except (OSError, ValueError, TypeError, shutil.Error, subprocess.SubprocessError, LinAlgError) as error:
        report["campaign_error"] = type(error).__name__ + ": " + str(error)
    finally:
        report["finished_utc"] = utc()
        # Hash every retained native artifact and runtime CSV.  The manifest
        # excludes itself to avoid a circular self-hash.
        report["artifacts"] = [{"path": path.relative_to(output).as_posix(), "sha256": digest(path)}
                               for path in sorted(output.rglob("*")) if path.is_file() and path.name != "campaign.json"]
        dump(output.joinpath("campaign.json"), report)
    return report


@deal.pre(lambda argv=None: argv is None or (isinstance(argv, list) and all(isinstance(value, str) and "\x00" not in value for value in argv)))
@deal.pre(lambda argv=None: ROOT.is_dir())
@deal.post(lambda result: type(result) is int and result in (0, 1))
@deal.raises(OSError, ValueError, TypeError, shutil.Error, SameFileError, SpecialFileError, subprocess.SubprocessError, CalledProcessError, TimeoutExpired, LinAlgError, SystemExit)
@deal.has("io", "syscall", "time", "random")
def main(argv=None):
    """Choose an unused evidence path and return failure for incomplete proof."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-root", type=Path, default=ROOT)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--alire-dir", type=Path, default=Path.home().joinpath(".local/share/icar16-gnatprove-tools"))
    parser.add_argument("--trials", type=int, default=200000)
    parser.add_argument("--wall-seconds", type=int, default=1800)
    args = parser.parse_args(argv)
    if not 2 <= args.trials <= 1_000_000 or not 1 <= args.wall_seconds <= 86400:
        parser.error("trials must be 2..1000000 and wall-seconds must be 1..86400")
    output = args.output or ROOT.joinpath(ANALYSIS_RELATIVE, "evidence", "campaign-" + datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%S%fZ"))
    output = output.resolve()
    if output.exists():
        parser.error("output already exists; recorded campaigns cannot be overwritten")
    report = run_campaign(args.source_root.resolve(), output, args.alire_dir.resolve(), args.trials, args.wall_seconds)
    print(json.dumps({"output": str(output), "complete": report["complete"]}, indent=2))
    return 0 if report["complete"] else 1


if __name__ == "__main__":
    deal.enable(warn=False)
    raise SystemExit(main())
