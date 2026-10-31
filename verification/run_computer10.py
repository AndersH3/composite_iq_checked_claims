#!/usr/bin/env python3
"""Run source-pinned, fresh GNATprove campaigns on computer10.

Only SPARK proof projects are certified. Ada numerical libraries and simulations
have a separate numerical-validation boundary documented beside each project.
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

ROOT = Path(__file__).resolve().parents[1]
PROJECTS = {
    "hoeflin": ("analyses/hoeflin-ferguson/ada", "hoeflin_proof.gpr", "hoeflin_core"),
    "towers": ("analyses/towers-multiple-test-admissions/ada", "towers_proof.gpr", "admission_core"),
}
ALLOWED_EXPORTS = {
    "ALIRE", "GNATPROVE_ALIRE_PREFIX", "GNAT_NATIVE_ALIRE_PREFIX",
    "GPRBUILD_ALIRE_PREFIX", "GPR_PROJECT_PATH", "ICAR16_GNATPROVE_TOOLS_ALIRE_PREFIX", "PATH",
}


def utc():
    return datetime.now(timezone.utc).isoformat()


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def dump(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2) + "\n", encoding="utf-8")


def environment(alire_dir):
    process = subprocess.run(["alr", "-q", "printenv"], cwd=alire_dir,
                             capture_output=True, text=True, check=True)
    env = os.environ.copy()
    exports = {}
    for line in process.stdout.splitlines():
        parts = shlex.split(line)
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
    colibri = Path.home() / ".local/share/icar16-classic-colibri/2026.06-v7/colibri-2026.06-v7"
    if (colibri / "colibri").is_file():
        env["PATH"] = str(colibri) + os.pathsep + env["PATH"]
    return env


def execute(argv, cwd, env, log, wall_seconds=900):
    start = utc()
    before = time.monotonic()
    timed_out = False
    log.parent.mkdir(parents=True, exist_ok=True)
    with log.open("wb") as stream:
        process = subprocess.Popen(argv, cwd=cwd, env=env, stdout=stream,
                                   stderr=subprocess.STDOUT, start_new_session=True)
        try:
            code = process.wait(timeout=wall_seconds)
        except subprocess.TimeoutExpired:
            timed_out = True
            os.killpg(process.pid, signal.SIGTERM)
            try:
                process.wait(timeout=10)
            except subprocess.TimeoutExpired:
                os.killpg(process.pid, signal.SIGKILL)
                process.wait()
            code = 124
    return {"argv": argv, "cwd": str(cwd), "started_utc": start, "finished_utc": utc(),
            "elapsed_seconds": time.monotonic() - before, "returncode": code,
            "timed_out": timed_out, "log_sha256": digest(log)}


def version_record(path, args, env):
    process = subprocess.run([str(path), *args], env=env, capture_output=True,
                             text=True, timeout=15)
    return {"path": str(path), "sha256": digest(Path(path)), "argv": [str(path), *args],
            "returncode": process.returncode, "output": (process.stdout + process.stderr).strip()}


def report_summary(report):
    text = report.read_text(errors="replace")
    rows = {}
    for line in text.splitlines():
        fields = re.split(r"\s{2,}", line.strip())
        if len(fields) == 6 and (fields[0] == "Total" or fields[0] in
            {"Run-time Checks", "Assertions", "Functional Contracts", "Initialization", "Data Dependencies"}):
            def number(value):
                return 0 if value == "." else int(re.match(r"\d+", value).group())
            rows[fields[0]] = dict(zip(("total", "flow", "provers", "justified", "unproved"),
                                       map(number, fields[1:])))
    if "Total" not in rows or rows["Total"]["total"] == 0:
        raise ValueError("Missing or empty native GNATprove totals")
    units = re.search(r"Analyzed (\d+) units?", text)
    return {"categories": rows, "analyzed_units": int(units.group(1)) if units else None,
            "contains_not_proved": "and not proved" in text,
            "report_sha256": digest(report)}


def snapshot(folder, target):
    target.mkdir(parents=True)
    copied = []
    for path in sorted(folder.rglob("*")):
        if path.is_file() and (path.suffix in {".ads", ".adb", ".gpr"}) and not any(
            part.startswith(("obj", "bin", ".")) or part in {"proof_obj", "results"}
            for part in path.relative_to(folder).parts):
            relative = path.relative_to(folder)
            dest = target / relative
            dest.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(path, dest)
            copied.append({"path": str(path.relative_to(ROOT)), "sha256": digest(path)})
    return copied


def campaign(name, folder, project, unit, aliases, label, work, output, env, config, timeout, wall):
    source = work / name / label
    hashes = snapshot(folder, source)
    run_dir = output / name / label
    run_dir.mkdir(parents=True)
    prover = str(Path(env["GNATPROVE_ALIRE_PREFIX"]) / "bin/gnatprove")
    argv = [prover, "-P", project, "--mode=all", "--report=statistics", "--checks-as-errors",
            "--warnings=error", "--level=2", "--steps=0", "--counterexamples=off", "-j2", "-f", "-U",
            "--no-subprojects", "--timeout=" + str(timeout), "--prover=" + ",".join(aliases)]
    if "Yices" in aliases or "Colibri_Classic" in aliases:
        argv.append("--why3-conf=" + str(config))
    result = execute(argv, source, env, run_dir / "invocation.log", wall)
    native = list(source.rglob("gnatprove.out"))
    if len(native) == 1:
        report = run_dir / "gnatprove.out"
        shutil.copyfile(native[0], report)
        try:
            result["native"] = report_summary(report)
        except ValueError as error:
            result["parse_error"] = str(error)
    result["sources"] = hashes
    result["provers_requested"] = aliases
    total = result.get("native", {}).get("categories", {}).get("Total", {})
    text = (run_dir / "gnatprove.out").read_text(errors="replace") if native else ""
    result["complete"] = (result["returncode"] == 0 and total.get("unproved") == 0
                           and total.get("justified") == 0 and not result.get("native", {}).get("contains_not_proved", True)
                           and ("in unit " + unit) in text)
    dump(run_dir / "result.json", result)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--alire-dir", type=Path,
                        default=Path.home() / ".local/share/icar16-gnatprove-tools")
    parser.add_argument("--run-id", default="computer10-" + datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ"))
    parser.add_argument("--timeout", type=int, default=15)
    parser.add_argument("--wall-seconds", type=int, default=900)
    parser.add_argument("--portfolio-only", action="store_true")
    parser.add_argument("--provers", default="cvc5,z3,altergo,Colibri_Classic,Yices")
    args = parser.parse_args()
    if socket.gethostname().split(".")[0] != "computer10":
        raise SystemExit("This evidence campaign must actually run on computer10")
    output = ROOT / "verification/evidence" / args.run_id
    output.mkdir(parents=True, exist_ok=False)
    env = environment(args.alire_dir)
    prefix = Path(env["GNATPROVE_ALIRE_PREFIX"])
    binaries = prefix / "libexec/spark/bin"
    aliases = args.provers.split(",")
    paths = {"cvc5": binaries / "cvc5", "z3": binaries / "z3", "altergo": binaries / "alt-ergo",
             "Colibri_Classic": Path(shutil.which("colibri", path=env["PATH"]) or "/missing/colibri"),
             "Yices": Path("/usr/local/bin/yices-smt2")}
    for alias in aliases:
        if alias not in paths or not paths[alias].is_file():
            raise ValueError("Requested prover unavailable: " + alias)
    config = output / "provers.conf"
    config.write_text('[prover]\nname = "Yices"\nversion = "2.7.0"\nalternative = "SMT2"\ncommand = '
                      + json.dumps(str(paths["Yices"]) + " --timeout=%t %f") + '\ndriver = '
                      + json.dumps(str(prefix / "libexec/spark/share/why3/drivers/yices-smt2.drv"))
                      + '\n\n[prover]\nname = "Colibri_Classic"\nversion = "2026.06-v7"\ncommand = '
                      + json.dumps(str(paths["Colibri_Classic"]) + " --get-steps --memlimit %m %f")
                      + '\ncommand_steps = '
                      + json.dumps(str(paths["Colibri_Classic"]) + " --get-steps --max-steps %S --memlimit %m %f")
                      + '\ndriver = '
                      + json.dumps(str(prefix / "libexec/spark/share/why3/drivers/colibri.drv")) + "\n")
    tools = {"gnatprove": version_record(prefix / "bin/gnatprove", ["--version"], env),
             "gnat": version_record(Path(env["GNAT_NATIVE_ALIRE_PREFIX"]) / "bin/gnat", ["--version"], env),
             "gprbuild": version_record(Path(env["GPRBUILD_ALIRE_PREFIX"]) / "bin/gprbuild", ["--version"], env)}
    for alias in aliases:
        tools[alias] = version_record(paths[alias], ["-version"] if alias == "z3" else ["--version"], env)
    manifest = {"host": socket.gethostname(), "started_utc": utc(), "runner_sha256": digest(Path(__file__)),
                "toolchain": tools, "provers_requested": aliases, "prover_config_sha256": digest(config), "projects": {}}
    dump(output / "manifest.json", manifest)
    with tempfile.TemporaryDirectory(prefix="composite-iq-spark-") as temp:
        work = Path(temp)
        control = campaign("negative_control", ROOT / "verification/negative_control", "negative.gpr",
                           "negative_union", aliases, "portfolio", work, output, env, config,
                           args.timeout, args.wall_seconds)
        control_contracts = control.get("native", {}).get("categories", {}).get("Functional Contracts", {})
        manifest["negative_control"] = {
            "expected_failure_rejected": control["returncode"] != 0 and not control["timed_out"]
                and control_contracts.get("unproved", 0) > 0,
            "result": control,
        }
        dump(output / "manifest.json", manifest)
        print("negative_control", "REJECTED AS EXPECTED" if manifest["negative_control"]["expected_failure_rejected"]
              else "INVALID GATE", flush=True)
        for name, (relative, project, unit) in PROJECTS.items():
            folder = ROOT / relative
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
            dump(output / "manifest.json", manifest)
    manifest["finished_utc"] = utc()
    manifest["portfolio_complete"] = (manifest["negative_control"]["expected_failure_rejected"]
                                      and all(r["portfolio"]["complete"] for r in manifest["projects"].values()))
    dump(output / "manifest.json", manifest)
    raise SystemExit(0 if manifest["portfolio_complete"] else 1)


if __name__ == "__main__":
    main()
