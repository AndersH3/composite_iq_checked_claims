#!/usr/bin/env python3
"""Run source-pinned, fresh GNATprove campaigns on computer10.

The proof projects enumerate analyzed units and retain native body/spec coverage.
Trusted external and I/O completions remain explicit numerical/runtime boundaries.
"""

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import shlex
import shutil
import signal
import socket
import subprocess
import tempfile
import time

import deal
from subprocess import CalledProcessError, TimeoutExpired
from shutil import SameFileError, SpecialFileError

try:
    from verification.proof_gate import totals_balanced, successful_checks
    from verification.spark_coverage import read_coverage
except ModuleNotFoundError:
    from proof_gate import totals_balanced, successful_checks
    from spark_coverage import read_coverage

ROOT = Path(__file__).resolve().parents[1]
PROJECTS = {
    "hoeflin": ("analyses/hoeflin-ferguson/ada", "hoeflin_proof.gpr", "hoeflin_core"),
    "towers": ("analyses/towers-multiple-test-admissions/ada", "towers_proof.gpr", "admission_core"),
}
REQUIRED_BODIES = {
    "hoeflin": {"Hoeflin_Calculations", "Hoeflin_Simulation",
                "Normal_Support.Inverse_Survival", "Normal_Support.Reset",
                "Normal_Support.Uniform", "Normal_Support.Normal_Pair", "Hoeflin_Core.Observe"},
    "towers": {"Towers_Demo", "Towers_Engine.Compute", "Normal_Model.Inverse_SF",
               "Normal_Model.Joint_Tail", "Normal_Model.Calibrated_OR_Cutoff",
               "Normal_Model.Basic_Grid", "Normal_Model.Reset", "Normal_Model.Uniform",
               "Normal_Model.Normal_Pair", "Admission_Core.Observe"},
}
ALLOWED_EXPORTS = {
    "ALIRE", "GNATPROVE_ALIRE_PREFIX", "GNAT_NATIVE_ALIRE_PREFIX",
    "GPRBUILD_ALIRE_PREFIX", "GPR_PROJECT_PATH", "ICAR16_GNATPROVE_TOOLS_ALIRE_PREFIX", "PATH",
}
FIELDS_PATTERN = re.compile(r"\s{2,}")
COUNT_PATTERN = re.compile(r"\d+")


@deal.raises()
@deal.has()
def is_sha256(value: str) -> bool:
    return isinstance(value, str) and len(value) == 64 and all(c in "0123456789abcdef" for c in value)


@deal.post(lambda result: isinstance(result, str) and result.endswith("+00:00"))
@deal.has("time")
def utc() -> str:
    return datetime.now(timezone.utc).isoformat()


@deal.pre(lambda path: isinstance(path, Path))
@deal.post(is_sha256)
@deal.raises(OSError, ValueError)
@deal.has("read")
def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


@deal.pre(lambda path, value: isinstance(path, Path))
@deal.post(lambda result: result is None)
@deal.raises(OSError, ValueError, TypeError)
@deal.has("write")
def dump(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2) + "\n", encoding="utf-8")


@deal.pre(lambda alire_dir: isinstance(alire_dir, Path) and alire_dir.is_dir())
@deal.post(lambda result: isinstance(result, dict)
           and all(isinstance(k, str) and isinstance(v, str) for k, v in result.items())
           and all(k in result for k in ("PATH", "GNATPROVE_ALIRE_PREFIX", "GNAT_NATIVE_ALIRE_PREFIX", "GPRBUILD_ALIRE_PREFIX")))
@deal.raises(OSError, ValueError, subprocess.SubprocessError, CalledProcessError, TimeoutExpired)
@deal.has("read", "syscall")
def environment(alire_dir: Path) -> dict:
    process = subprocess.run(["alr", "-q", "printenv"], cwd=alire_dir,
                             capture_output=True, text=True, check=True, timeout=30)
    env = os.environ.copy()
    exports = {}
    for line in process.stdout.splitlines():
        lexer = shlex.shlex(line, posix=True)
        lexer.whitespace_split = True
        lexer.commenters = ""
        parts = list(lexer)
        if len(parts) != 2 or parts[0] != "export" or "=" not in parts[1]:
            raise ValueError("Unexpected Alire export syntax")
        key, value = parts[1].split("=", 1)
        if key not in ALLOWED_EXPORTS or key in exports:
            raise ValueError("Unexpected or duplicate Alire export name")
        exports[key] = value
    for key in ("GNATPROVE_ALIRE_PREFIX", "GNAT_NATIVE_ALIRE_PREFIX", "GPRBUILD_ALIRE_PREFIX", "PATH"):
        if key not in exports:
            raise ValueError("Missing required toolchain export: " + key)
    env.update(exports)
    colibri = Path.home().joinpath('.local/share/icar16-classic-colibri/2026.06-v7/colibri-2026.06-v7')
    if (colibri.joinpath('colibri')).is_file():
        env["PATH"] = str(colibri) + os.pathsep + env["PATH"]
    return env


@deal.pre(lambda argv, cwd, env, log, wall_seconds=900:
          isinstance(argv, list) and bool(argv) and all(isinstance(a, str) for a in argv)
          and isinstance(cwd, Path) and cwd.is_dir() and isinstance(env, dict)
          and all(isinstance(k, str) and isinstance(v, str) for k, v in env.items())
          and isinstance(log, Path) and isinstance(wall_seconds, int) and wall_seconds > 0)
@deal.ensure(lambda argv, cwd, env, log, wall_seconds=900, result=None:
             result["argv"] == argv and result["cwd"] == str(cwd)
             and result["elapsed_seconds"] >= 0
             and isinstance(result["returncode"], int) and isinstance(result["timed_out"], bool)
             and (not result["timed_out"] or result["returncode"] == 124)
             and len(result["log_sha256"]) == 64)
@deal.raises(OSError, ValueError, subprocess.SubprocessError, CalledProcessError, TimeoutExpired)
@deal.has("io", "syscall", "time")
def execute(argv: list, cwd: Path, env: dict, log: Path, wall_seconds: int = 900) -> dict:
    start = utc()
    before = time.monotonic()
    timed_out = False
    log.parent.mkdir(parents=True, exist_ok=True)
    with log.open("wb") as stream:
        process = subprocess.Popen(argv, cwd=cwd, env=env, stdout=stream,
                                   stderr=subprocess.STDOUT, start_new_session=True)
        try:
            code = process.wait(timeout=wall_seconds)
        except TimeoutExpired:
            timed_out = True
            os.killpg(process.pid, signal.SIGTERM)
            try:
                process.wait(timeout=10)
            except TimeoutExpired:
                os.killpg(process.pid, signal.SIGKILL)
                process.wait()
            code = 124
    return {"argv": argv, "cwd": str(cwd), "started_utc": start, "finished_utc": utc(),
            "elapsed_seconds": time.monotonic() - before, "returncode": code,
            "timed_out": timed_out, "log_sha256": digest(log)}


@deal.pre(lambda path, args, env: isinstance(path, Path) and path.is_file()
          and isinstance(args, list) and all(isinstance(a, str) for a in args)
          and isinstance(env, dict) and all(isinstance(k, str) and isinstance(v, str) for k, v in env.items()))
@deal.ensure(lambda path, args, env, result: result["path"] == str(path)
             and result["argv"] == [str(path), *args] and len(result["sha256"]) == 64
             and isinstance(result["returncode"], int) and isinstance(result["output"], str))
@deal.raises(OSError, ValueError, subprocess.SubprocessError, TimeoutExpired)
@deal.has("read", "syscall")
def version_record(path: Path, args: list, env: dict) -> dict:
    with subprocess.Popen([str(path), *args], env=env, stdout=subprocess.PIPE,
                          stderr=subprocess.PIPE, text=True) as process:
        try:
            stdout, stderr = process.communicate(timeout=15)
        except TimeoutExpired:
            process.kill()
            process.communicate()
            raise
        except BaseException:
            process.kill()
            raise
    return {"path": str(path), "sha256": digest(Path(path)), "argv": [str(path), *args],
            "returncode": process.returncode, "output": (stdout + stderr).strip()}


@deal.pre(lambda value: isinstance(value, str))
@deal.post(lambda result: isinstance(result, int) and result >= 0)
@deal.raises(ValueError)
@deal.has()
def summary_number(value: str) -> int:
    if value == ".":
        return 0
    match = COUNT_PATTERN.match(value)
    if match is None:
        raise ValueError("Malformed native GNATprove count")
    return int(match.group())


@deal.pre(lambda report: isinstance(report, Path))
@deal.post(lambda result: isinstance(result, dict) and "Total" in result["categories"]
           and result["categories"]["Total"]["total"] > 0
           and all(totals_balanced(row["total"], row["flow"], row["provers"], row["justified"], row["unproved"])
                   for row in result["categories"].values())
           and isinstance(result["contains_not_proved"], bool) and len(result["report_sha256"]) == 64)
@deal.raises(OSError, ValueError)
@deal.has("read")
def report_summary(report: Path) -> dict:
    text = report.read_text(errors="replace")
    rows = {}
    for line in text.splitlines():
        fields = FIELDS_PATTERN.split(line.strip())
        if len(fields) == 6 and (fields[0] == "Total" or fields[0] in
            {"Run-time Checks", "Assertions", "Functional Contracts", "Initialization", "Data Dependencies"}):
            rows[fields[0]] = dict(zip(("total", "flow", "provers", "justified", "unproved"),
                                       map(summary_number, fields[1:])))
    if "Total" not in rows or rows["Total"]["total"] == 0:
        raise ValueError("Missing or empty native GNATprove totals")
    if not all(totals_balanced(row["total"], row["flow"], row["provers"], row["justified"], row["unproved"])
               for row in rows.values()):
        raise ValueError("Inconsistent native GNATprove totals")
    units = re.search(r"Analyzed (\d+) units?", text)
    return {"categories": rows, "analyzed_units": int(units.group(1)) if units else None,
            "contains_not_proved": "and not proved" in text,
            "report_sha256": digest(report)}


@deal.pre(lambda folder, target: isinstance(folder, Path) and folder.is_dir()
          and folder.is_relative_to(ROOT) and isinstance(target, Path) and not target.exists())
@deal.post(lambda result: isinstance(result, list)
           and all(isinstance(e["path"], str) and len(e["sha256"]) == 64 for e in result))
@deal.raises(OSError, ValueError, SameFileError, SpecialFileError)
@deal.has("read", "write")
def snapshot(folder: Path, target: Path) -> list:
    target.mkdir(parents=True)
    copied = []
    for path in sorted(folder.rglob("*")):
        if path.is_file() and (path.suffix in {".ads", ".adb", ".gpr", ".adc"}) and not any(
            part.startswith(("obj", "bin", ".")) or part in {"proof_obj", "results"}
            for part in path.relative_to(folder).parts):
            relative = path.relative_to(folder)
            dest = target.joinpath(relative)
            dest.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(path, dest)
            copied.append({"path": str(path.relative_to(ROOT)), "sha256": digest(path)})
    return copied


@deal.pre(lambda name, folder, project, unit, aliases, label, work, output, env, config, timeout, wall:
          isinstance(folder, Path) and folder.is_dir() and (folder.joinpath(project)).is_file()
          and bool(name) and bool(unit) and bool(label) and bool(aliases)
          and all(isinstance(a, str) and bool(a) for a in aliases)
          and isinstance(work, Path) and work.is_dir() and isinstance(output, Path) and output.is_dir()
          and isinstance(config, Path) and isinstance(env, dict) and "GNATPROVE_ALIRE_PREFIX" in env
          and isinstance(timeout, int) and timeout > 0 and isinstance(wall, int) and wall > 0)
@deal.post(lambda result: isinstance(result["complete"], bool) and bool(result["sources"])
           and (not result["complete"] or successful_checks(result["returncode"],
               result["native"]["categories"]["Total"]["total"],
               result["native"]["categories"]["Total"]["unproved"],
               result["native"]["categories"]["Total"]["justified"])))
@deal.raises(OSError, ValueError, TypeError, SameFileError, SpecialFileError,
             subprocess.SubprocessError, CalledProcessError, TimeoutExpired)
@deal.has("io", "syscall", "time")
def campaign(name: str, folder: Path, project: str, unit: str, aliases: list, label: str,
             work: Path, output: Path, env: dict, config: Path, timeout: int, wall: int) -> dict:
    source = work.joinpath(name).joinpath(label)
    hashes = snapshot(folder, source)
    run_dir = output.joinpath(name).joinpath(label)
    run_dir.mkdir(parents=True)
    prover = str(Path(env['GNATPROVE_ALIRE_PREFIX']).joinpath('bin/gnatprove'))
    argv = [prover, "-P", project, "--mode=all", "--report=statistics", "--checks-as-errors",
            "--warnings=error", "--level=2", "--steps=0", "--counterexamples=off", "-j2", "-f", "-U",
            "--no-subprojects", "--timeout=" + str(timeout), "--prover=" + ",".join(aliases)]
    if "Yices" in aliases or "Colibri_Classic" in aliases:
        argv.append("--why3-conf=" + str(config))
    result = execute(argv, source, env, run_dir.joinpath('invocation.log'), wall)
    native = list(source.rglob("gnatprove.out"))
    if len(native) == 1:
        report = run_dir.joinpath('gnatprove.out')
        shutil.copyfile(native[0], report)
        try:
            result["native"] = report_summary(report)
        except ValueError as error:
            result["parse_error"] = str(error)
    result["sources"] = hashes
    result["provers_requested"] = aliases
    coverage_dir = run_dir.joinpath("spark")
    coverage_dir.mkdir()
    for raw in sorted(source.rglob("*.spark")):
        destination = coverage_dir.joinpath(raw.relative_to(source))
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(raw, destination)
    try:
        result["coverage"] = read_coverage(coverage_dir,
            {Path(entry["path"]).name for entry in hashes if Path(entry["path"]).suffix in {".ads", ".adb"}})
    except ValueError as error:
        result["coverage_error"] = str(error)
    result["required_full_entities"] = sorted(REQUIRED_BODIES.get(name, set()))
    analyzed_bodies = {row["name"].casefold() for row in result.get("coverage", {}).get("entities", [])
                       if row["status"] == "all"}
    result["missing_full_entities"] = [entity for entity in result["required_full_entities"]
                                       if entity.casefold() not in analyzed_bodies]
    total = result.get("native", {}).get("categories", {}).get("Total", {})
    text = (run_dir.joinpath('gnatprove.out')).read_text(errors="replace") if (run_dir.joinpath('gnatprove.out')).is_file() else ""
    result["complete"] = (successful_checks(result["returncode"], total.get("total", 0),
                           total.get("unproved", 0), total.get("justified", 0))
                           and not result.get("native", {}).get("contains_not_proved", True)
                           and result.get("coverage", {}).get("no_assumptions_or_suppressions", False)
                           and not result["missing_full_entities"]
                           and ("in unit " + unit) in text)
    dump(run_dir.joinpath('result.json'), result)
    return result


@deal.raises(SystemExit, OSError, ValueError, TypeError, subprocess.SubprocessError,
             CalledProcessError, TimeoutExpired, SameFileError, SpecialFileError)
@deal.has("io", "syscall", "time")
def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--alire-dir", type=Path,
                        default=Path.home().joinpath('.local/share/icar16-gnatprove-tools'))
    parser.add_argument("--run-id", default="computer10-" + datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ"))
    parser.add_argument("--timeout", type=int, default=15)
    parser.add_argument("--wall-seconds", type=int, default=900)
    parser.add_argument("--portfolio-only", action="store_true")
    parser.add_argument("--provers", default="cvc5,z3,altergo,Colibri_Classic,Yices")
    args = parser.parse_args()
    if not re.fullmatch(r"[A-Za-z0-9][A-Za-z0-9_.-]*", args.run_id):
        parser.error("run-id must be one safe directory name")
    if args.timeout <= 0 or args.wall_seconds <= 0:
        parser.error("timeout and wall-seconds must be positive")
    if socket.gethostname().split(".")[0] != "computer10":
        raise SystemExit("This evidence campaign must actually run on computer10")
    output = ROOT.joinpath('verification/evidence').joinpath(args.run_id)
    output.mkdir(parents=True, exist_ok=False)
    env = environment(args.alire_dir)
    prefix = Path(env["GNATPROVE_ALIRE_PREFIX"])
    binaries = prefix.joinpath('libexec/spark/bin')
    aliases = args.provers.split(",")
    paths = {"cvc5": binaries.joinpath('cvc5'), "z3": binaries.joinpath('z3'), "altergo": binaries.joinpath('alt-ergo'),
             "Colibri_Classic": Path(shutil.which("colibri", path=env["PATH"]) or "/missing/colibri"),
             "Yices": Path("/usr/local/bin/yices-smt2")}
    for alias in aliases:
        if alias not in paths or not paths[alias].is_file():
            raise ValueError("Requested prover unavailable: " + alias)
    config = output.joinpath('provers.conf')
    config.write_text('[prover]\nname = "Yices"\nversion = "2.7.0"\nalternative = "SMT2"\ncommand = '
                      + json.dumps(str(paths["Yices"]) + " --timeout=%t %f") + '\ndriver = '
                      + json.dumps(str(prefix.joinpath('libexec/spark/share/why3/drivers/yices-smt2.drv')))
                      + '\n\n[prover]\nname = "Colibri_Classic"\nversion = "2026.06-v7"\ncommand = '
                      + json.dumps(str(paths["Colibri_Classic"]) + " --get-steps --memlimit %m %f")
                      + '\ncommand_steps = '
                      + json.dumps(str(paths["Colibri_Classic"]) + " --get-steps --max-steps %S --memlimit %m %f")
                      + '\ndriver = '
                      + json.dumps(str(prefix.joinpath('libexec/spark/share/why3/drivers/colibri.drv'))) + "\n")
    tools = {"gnatprove": version_record(prefix.joinpath('bin/gnatprove'), ["--version"], env),
             "gnat": version_record(Path(env['GNAT_NATIVE_ALIRE_PREFIX']).joinpath('bin/gnat'), ["--version"], env),
             "gprbuild": version_record(Path(env['GPRBUILD_ALIRE_PREFIX']).joinpath('bin/gprbuild'), ["--version"], env)}
    for alias in aliases:
        tools[alias] = version_record(paths[alias], ["-version"] if alias == "z3" else ["--version"], env)
    manifest = {"host": socket.gethostname(), "started_utc": utc(), "runner_sha256": digest(Path(__file__)),
                "toolchain": tools, "provers_requested": aliases, "prover_config_sha256": digest(config),
                "coverage_schema": "gnat13-sloc-v1", "projects": {}}
    dump(output.joinpath('manifest.json'), manifest)
    with tempfile.TemporaryDirectory(prefix="composite-iq-spark-") as temp:
        work = Path(temp)
        control = campaign("negative_control", ROOT.joinpath('verification/negative_control'), "negative.gpr",
                           "negative_union", aliases, "portfolio", work, output, env, config,
                           args.timeout, args.wall_seconds)
        control_contracts = control.get("native", {}).get("categories", {}).get("Functional Contracts", {})
        manifest["negative_control"] = {
            "expected_failure_rejected": control["returncode"] != 0 and not control["timed_out"]
                and control_contracts.get("unproved", 0) > 0,
            "result": control,
        }
        dump(output.joinpath('manifest.json'), manifest)
        print("negative_control", "REJECTED AS EXPECTED" if manifest["negative_control"]["expected_failure_rejected"]
              else "INVALID GATE", flush=True)
        for name, (relative, project, unit) in PROJECTS.items():
            folder = ROOT.joinpath(relative)
            runs = {}
            labels = [("portfolio", aliases)]
            if not args.portfolio_only:
                labels += [(alias.lower(), [alias]) for alias in aliases]
            for label, selection in labels:
                result = campaign(name, folder, project, unit, selection, label, work, output,
                                  env, config, args.timeout, args.wall_seconds)
                runs[label] = result
                print(name, label, "COMPLETE" if result["complete"] else "INCOMPLETE",
                      result.get("native", {}).get("categories", {}).get("Total", {}), flush=True)
            manifest["projects"][name] = runs
            dump(output.joinpath('manifest.json'), manifest)
    manifest["finished_utc"] = utc()
    manifest["portfolio_complete"] = (manifest["negative_control"]["expected_failure_rejected"]
                                      and all(r["portfolio"]["complete"] for r in manifest["projects"].values()))
    dump(output.joinpath('manifest.json'), manifest)
    raise SystemExit(0 if manifest["portfolio_complete"] else 1)


if __name__ == "__main__":
    deal.enable(warn=False)
    main()
