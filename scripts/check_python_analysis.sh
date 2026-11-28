#!/usr/bin/env bash
# Run independent Python static analyzers against the exact tracked inventory.
# Keep all findings and native exit codes; separate baseline findings from
# mandatory correctness/security gates. Never install or auto-fix source here.
# Researcher/requester: Anders Hellström. AI-assisted tooling.
set -euo pipefail
cd "$(dirname "$0")/.."

# The Makefile and CI must ShellCheck this script before invoking it.
python=$1
prospector_python=$2
out=$3
mode=$4
[[ "$mode" == baseline || "$mode" == strict ]] || exit 2
mkdir -p "$out"
out=$(cd "$out" && pwd)
# Prevent stale reports from being mistaken for fresh successful executions.
: > "$out/status.tsv"
printf 'check\tpolicy\texit_code\tresult\n' > "$out/status.tsv"
git rev-parse HEAD > "$out/source-commit.txt"
git status --porcelain > "$out/source-status.txt"
git ls-files -z -- '*.py' > "$out/python-files.nul"
mapfile -d '' -t files < "$out/python-files.nul"
(("${#files[@]}" > 0)) || { echo 'Empty Python inventory' >&2; exit 2; }
printf '%s\n' "${files[@]}" > "$out/python-files.txt"
# Include tests, fixtures and compatibility imports. The Deal negative
# control is intentionally included; only Deal interprets its DEL012 result.
"$python" -m pip check > "$out/pip-check.txt" 2>&1
"$prospector_python" -m pip check > "$out/prospector-pip-check.txt" 2>&1
"$python" -m pip freeze > "$out/environment.txt"
"$prospector_python" -m pip freeze > "$out/prospector-environment.txt"
# Missing distributions must not masquerade as a tool finding (exit 1).
for tool in pylint flake8 pyflakes bandit vulture radon ruff; do
  "$python" -m pip show "$tool" > "$out/$tool.package.txt" || exit 2
done
"$prospector_python" -m pip show prospector > "$out/prospector.package.txt" || exit 2

failed=0
# Execute every analyzer even if an earlier one reports findings.
# The allowed finding exit code is tool-specific. Other nonzero codes
# are execution errors. Pylint uses a bit mask, not a single finding code.
run_check() {
  local name=$1 policy=$2 finding=$3 rc=0 result=clean
  shift 3
  printf 'Running %s (%s)\n' "$name" "$policy"
  "$@" > "$out/$name.log" 2> "$out/$name.stderr" || rc=$?
  if (( rc != 0 )); then
    if [[ "$finding" == pylint ]] && (( rc < 64 && (rc & 33) == 0 )); then
      result=findings
    elif [[ "$finding" != pylint && "$rc" == "$finding" ]]; then
      result=findings
    else
      result=execution-error
    fi
    # A traceback or missing module is an execution error even when its
    # exit status happens to coincide with the tool's findings status.
    if grep -Eq 'Traceback \(most recent call last\)|No module named |^Fatal Python error:' "$out/$name.stderr"; then
      result=execution-error
    fi
    if [[ "$result" == execution-error || "$policy" == gate || "$mode" == strict ]]; then
      failed=1
    fi
  fi
  printf '%s\t%s\t%s\t%s\n' "$name" "$policy" "$rc" "$result" >> "$out/status.tsv"
}

# Full reports are retained even where existing debt is not yet a gate.
# Pylint's fatal (1) and usage (32) bits always fail the run.
run_check pylint baseline pylint "$python" -m pylint --reports=y --score=y --persistent=n "${files[@]}"
# Deal registers a Flake8 AST plugin through package entry points. Apply
# the same already-tested location repair as the standalone Deal audit.
# Serial execution keeps the process-local compatibility patch active
# regardless of multiprocessing start method. Deal diagnostics (including
# DEL012) remain the responsibility of the separate mandatory Deal audit.
flake8_bootstrap='from deal._cached_property import cached_property
from deal.linter._contract import Contract
from verification.deal_lint_compat import compile_fixed_locations
from flake8.main.cli import main
Contract.bytecode = cached_property(compile_fixed_locations)
raise SystemExit(main())'
run_check flake8 baseline 1 "$python" -c "$flake8_bootstrap" --isolated --jobs=1 --extend-ignore=DEL --max-complexity=10 --statistics "${files[@]}"
run_check pyflakes baseline 1 "$python" -m pyflakes "${files[@]}"
run_check bandit baseline 1 "$python" -m bandit -f json "${files[@]}"
run_check vulture baseline 3 "$python" -m vulture --min-confidence 60 "${files[@]}"
# Resolve Radon's installed console entry point in the selected environment.
radon=$("$python" -c 'import sysconfig; print(sysconfig.get_path("scripts") + "/radon")')
# Radon reports metrics, not a zero-complexity policy. It does not return
# a nonzero status simply because a function is complex.
run_check radon-cc metrics 999 "$radon" cc -s -j "${files[@]}"
run_check radon-mi metrics 999 "$radon" mi -s -j "${files[@]}"
run_check radon-raw metrics 999 "$radon" raw -j "${files[@]}"
run_check radon-hal metrics 999 "$radon" hal -j "${files[@]}"
run_check prospector baseline 1 "$prospector_python" -m prospector --strictness high --test-warnings --doc-warnings --no-autodetect --no-blending --die-on-tool-error --output-format json "${files[@]}"
run_check ruff baseline 1 "$python" -m ruff check --isolated --target-version py313 --select E,F,W,I,UP,B,S,SIM,C90 --output-format json "${files[@]}"

# Enforce serious, relatively low-ambiguity findings from the first run.
# Ruff reports syntax errors unconditionally. Undefined names, invalid
# control flow and high-confidence/high-
# severity security findings are not merely style debt.
run_check ruff-correctness gate 1 "$python" -m ruff check --isolated --target-version py313 --select F63,F7,F82 "${files[@]}"
run_check bandit-high gate 1 "$python" -m bandit -lll -iii "${files[@]}"

# Validate machine-readable report structure; malformed reports fail,
# without creating another custom Python analyzer or uncontracted functions.
for name in bandit radon-cc radon-mi radon-raw radon-hal prospector ruff; do
  if ! "$python" -m json.tool "$out/$name.log" > /dev/null 2>&1; then
    printf '%s: report was not valid JSON; inspect native output\n' "$name" >&2
    failed=1
  fi
done

# Radon can report syntax errors inside otherwise valid JSON. Reject these
# and any incomplete Bandit scan even if the tool itself returned zero.
if ! "$python" -c 'import json, pathlib, sys; root=pathlib.Path(sys.argv[1]); data=[json.loads((root / (name + ".log")).read_text()) for name in ("radon-cc","radon-mi","radon-raw","radon-hal")]; bandit=json.loads((root / "bandit.log").read_text()); sys.exit(int(any(isinstance(value, dict) and "error" in value for report in data for value in report.values()) or bool(bandit.get("errors"))))' "$out"; then
  echo 'Incomplete Radon or Bandit scan; inspect reports' >&2
  failed=1
fi
cat "$out/status.tsv"
printf 'Reports: %s\n' "$out"
exit "$failed"
