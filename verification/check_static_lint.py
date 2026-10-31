#!/usr/bin/env python3
"""Lint every repository Python file and check the deliberate failing control.

Only the explicitly named negative fixture is expected to fail. Its diagnostic
is checked separately; no maintained implementation or test is exempted.
"""
import argparse
import json
from json import JSONDecodeError
from pathlib import Path
import subprocess
from subprocess import CalledProcessError, TimeoutExpired
import sys

import deal

try:
    from verification.check_contract_coverage import ROOT, python_files
except ModuleNotFoundError:
    from check_contract_coverage import ROOT, python_files

NEGATIVE_CONTROL = "tests/fixtures/contract_negative_control.py"


@deal.pre(lambda root, paths: isinstance(root, Path) and root.is_dir()
          and isinstance(paths, list) and bool(paths)
          and all(isinstance(path, Path) and path.is_file()
                  and path.is_relative_to(root) and path.suffix == ".py" for path in paths))
@deal.post(lambda result: isinstance(result, dict) and isinstance(result["returncode"], int)
           and isinstance(result["stdout"], str) and isinstance(result["stderr"], str)
           and isinstance(result["diagnostics"], list) and bool(result["paths"]))
@deal.raises(OSError, ValueError, JSONDecodeError, TimeoutExpired)
@deal.has("read", "syscall")
def lint_paths(root: Path, paths: list) -> dict:
    relative = [str(path.relative_to(root)) for path in paths]
    command = [sys.executable, "-m", "deal", "lint", "--json", *relative]
    try:
        process = subprocess.run(command, cwd=root, capture_output=True, text=True,
                                 check=True, timeout=120)
        code, stdout, stderr = process.returncode, process.stdout, process.stderr
    except CalledProcessError as error:
        code, stdout, stderr = error.returncode, error.stdout, error.stderr
    diagnostics = [json.JSONDecoder().decode(line) for line in stdout.splitlines() if line.strip()]
    return {"argv": command, "paths": relative, "returncode": code,
            "stdout": stdout, "stderr": stderr, "diagnostics": diagnostics}


@deal.pre(lambda positive, negative: isinstance(positive, dict) and isinstance(negative, dict)
          and all(key in record for record in (positive, negative)
                  for key in ("returncode", "stdout", "stderr", "diagnostics")))
@deal.post(lambda result: isinstance(result, bool))
@deal.raises()
@deal.has()
def accepted(positive: dict, negative: dict) -> bool:
    expected = negative["diagnostics"]
    return (positive["returncode"] == 0 and positive["stdout"] == ""
            and positive["stderr"] == "" and positive["diagnostics"] == []
            and negative["returncode"] == 1 and negative["stderr"] == ""
            and isinstance(expected, list) and len(expected) == 1
            and isinstance(expected[0], dict)
            and expected[0].get("path") == NEGATIVE_CONTROL
            and expected[0].get("code") == "DEL012"
            and expected[0].get("text") == "post contract error"
            and expected[0].get("value") == "-1"
            and isinstance(expected[0].get("content"), str)
            and expected[0]["content"].strip() == "return -1")


@deal.raises(SystemExit, OSError, ValueError, JSONDecodeError, subprocess.SubprocessError, TimeoutExpired)
@deal.has("read", "syscall", "stdout", "stderr")
def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=ROOT)
    args = parser.parse_args()
    root = args.root.resolve()
    files = python_files(root)
    control = root.joinpath(NEGATIVE_CONTROL)
    if control not in files:
        raise ValueError("The expected negative control is missing from the Python inventory")
    positive = lint_paths(root, [path for path in files if path != control])
    negative = lint_paths(root, [control])
    complete = accepted(positive, negative)
    print(json.dumps({"python_files": len(files), "positive_files": len(positive["paths"]),
                      "positive": positive, "negative_control": negative,
                      "complete": complete}, indent=2))
    raise SystemExit(0 if complete else 1)


if __name__ == "__main__":
    deal.enable(warn=False)
    main()
