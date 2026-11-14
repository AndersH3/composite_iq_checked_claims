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


@deal.pre(lambda root, paths: isinstance(root, Path))
@deal.pre(lambda root, paths: root.is_dir() and isinstance(paths, list) and bool(paths) and all((isinstance(path, Path) and path.is_file() and path.is_relative_to(root) and (path.suffix == '.py') for path in paths)))
@deal.post(lambda result: isinstance(result, dict) and isinstance(result["returncode"], int)
           and isinstance(result["stdout"], str) and isinstance(result["stderr"], str)
           and isinstance(result["diagnostics"], list) and bool(result["paths"]))
@deal.raises(OSError, ValueError, JSONDecodeError, TimeoutExpired)
@deal.has("read", "syscall")
@deal.ensure(lambda root, paths, result:
             result["paths"] == [str(path.relative_to(root)) for path in paths])
@deal.ensure(lambda root, paths, result:
             result["argv"] == [sys.executable, "-m", "deal", "lint", "--json",
                                *result["paths"]])
@deal.ensure(lambda root, paths, result:
             all(isinstance(item, dict) for item in result["diagnostics"]))
def lint_paths(root: Path, paths: list) -> dict:
    """Run Deal lint on precisely the supplied files and decode JSON diagnostics.

    Invariants: each path is constrained by preconditions to remain under
    the requested root, and input order is retained in both the command line
    and returned report. Every nonblank stdout line must decode to a JSON
    object. Failed Deal lint exits are recorded, not suppressed; subprocess
    and JSON-decoding errors propagate through the declared exception contract.
    The runner does not silently exempt the deliberate negative fixture.
    """
    relative = [str(path.relative_to(root)) for path in paths]
    command = [sys.executable, "-m", "deal", "lint", "--json", *relative]
    try:
        process = subprocess.run(command, cwd=root, capture_output=True, text=True,
                                 check=True, timeout=120)
        code, stdout, stderr = process.returncode, process.stdout, process.stderr
    except CalledProcessError as error:
        code, stdout, stderr = error.returncode, error.stdout, error.stderr
    # Keep the already lint-accepted standard-library decoder interface.
    # The installed Deal static analyzer cannot validate json.loads here,
    # whereas this form has the same fail-closed JSON error behavior.
    diagnostics = [json.JSONDecoder().decode(line) for line in stdout.splitlines() if line.strip()]
    return {"argv": command, "paths": relative, "returncode": code,
            "stdout": stdout, "stderr": stderr, "diagnostics": diagnostics}


@deal.pre(lambda positive, negative: isinstance(positive, dict))
@deal.pre(lambda positive, negative: isinstance(negative, dict) and all((key in record for record in (positive, negative) for key in ('returncode', 'stdout', 'stderr', 'diagnostics'))))
@deal.post(lambda result: isinstance(result, bool))
@deal.raises()
@deal.has()
@deal.ensure(lambda positive, negative, result:
             not result or positive["returncode"] == 0)
@deal.ensure(lambda positive, negative, result:
             not result or (positive["stdout"] == "" and
                            positive["stderr"] == "" and
                            positive["diagnostics"] == []))
@deal.ensure(lambda positive, negative, result:
             not result or negative["returncode"] == 1)
@deal.ensure(lambda positive, negative, result:
             not result or (negative["stderr"] == "" and
                            len(negative["diagnostics"]) == 1))
@deal.ensure(lambda positive, negative, result:
             not result or (negative["diagnostics"][0].get("path") ==
                            NEGATIVE_CONTROL and
                            negative["diagnostics"][0].get("code") == "DEL012" and
                            negative["diagnostics"][0].get("value") == "-1"))
def accepted(positive: dict, negative: dict) -> bool:
    """Fail closed unless every source passed and the exact control failed.

    Accepting a run requires clean linting of every non-control source file,
    no unexplained stderr, and exactly one DEL012 diagnostic from the named
    negative-control fixture. The five additional semantic postconditions
    independently guard success-side exit/outputs and negative-side
    exit, diagnostic count, identity, code, and bad value. A malformed or
    missing field must not be silently considered a successful audit.
    """
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
@deal.pre(lambda: isinstance(sys.argv, list))
@deal.pre(lambda: all(isinstance(argument, str) for argument in sys.argv))
@deal.pre(lambda: ROOT.is_dir())
def main() -> None:
    """Audit all current Python sources, including the negative fixture.

    The coverage inventory, Deal lint invocation, JSON diagnostics, and
    fail-closed acceptance are delegated to existing library-backed helpers.
    If a batch fails with stderr, per-file reruns collect diagnostics without
    excluding any source from the overall result. The CLI exits nonzero on
    incomplete audits and enables Deal contracts at its entry point.
    """
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=ROOT)
    args = parser.parse_args()
    root = args.root.resolve()
    files = python_files(root)
    # Keep Path.joinpath: the installed linter misclassifies Path / str
    # as an unchecked numeric division without improving path safety.
    control = root.joinpath(NEGATIVE_CONTROL)
    if control not in files:
        raise ValueError("The expected negative control is missing from the Python inventory")
    positive = lint_paths(root, [path for path in files if path != control])
    negative = lint_paths(root, [control])
    complete = accepted(positive, negative)
    # Fail closed as before, but isolate third-party linter exceptions by
    # repository path. This is diagnostic only; no file is exempted and the
    # expected negative control must still be rejected independently.
    isolated_failures = []
    if positive["returncode"] != 0 and positive["stderr"]:
        for path in files:
            if path == control:
                continue
            individual = lint_paths(root, [path])
            if individual["returncode"] != 0 or individual["stderr"]:
                isolated_failures.append({
                    "path": str(path.relative_to(root)),
                    "returncode": individual["returncode"],
                    "stderr_tail": individual["stderr"][-1800:],
                    "diagnostics": individual["diagnostics"],
                })
    print(json.dumps({"python_files": len(files), "positive_files": len(positive["paths"]),
                      "positive": positive, "negative_control": negative,
                      "isolated_failures": isolated_failures,
                      "complete": complete}, indent=2))
    raise SystemExit(0 if complete else 1)


if __name__ == "__main__":
    deal.enable(warn=False)
    main()
