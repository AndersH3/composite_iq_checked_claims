#!/usr/bin/env bash
# Why3 1.8 / Debian 13: validate actual Z3 and CVC5 proof invocations.
# AI disclosure: drafted with AI assistance. This is a smoke test, NOT a
# proof of the correctness of the underlying SMT solvers.
#
# Positive control must be Valid; false control must never be Valid. Why3 1.8
# may report Unknown (sat), rather than Invalid, for a satisfiable negation.
# The script does not change ~/.why3.conf, package versions, opam switches,
# PATH, or the user's substantive formal proof files.
set -euo pipefail

self_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd -P)"
fixture="$self_dir/backend_smoke.why"
if ! command -v why3 >/dev/null 2>&1; then
  printf '%s\n' 'ERROR: Why3 is not in PATH.' >&2
  exit 2
fi
if ! command -v timeout >/dev/null 2>&1; then
  printf '%s\n' 'ERROR: GNU timeout is required.' >&2
  exit 2
fi
if [[ ! -f "$fixture" ]]; then
  printf 'ERROR: Missing fixture: %s\n' "$fixture" >&2
  exit 2
fi

# Why3 1.8's CLI reports one selected goal and its answer on SEPARATE
# lines, e.g. "Goal TrueGoal." followed by
# "Prover result is: Valid (0.00s, 18 steps).".
# Enforce exactly one goal header and exactly one result header, then verify
# the requested status. This prevents matching unrelated diagnostics or a
# status for a different goal. Only Why3's reported result counts, never the
# process exit status by itself.
why3_result_is() {
  local output="$1" goal="$2" expected="$3"
  local goal_headers result_headers
  goal_headers="$(grep -Fxc "Goal $goal." <<<"$output" || true)"
  result_headers="$(grep -Ec '^Prover result is:[[:space:]]*' <<<"$output" || true)"
  [[ "$goal_headers" == "1" && "$result_headers" == "1" ]] &&
    grep -Eq "^Prover result is:[[:space:]]*${expected}([[:space:]]|$)" <<<"$output"
}

printf '%s\n' 'Why3 external backend smoke test (positive and negative controls)'
why3 --version
# Why3 1.8 treats a short name as ambiguous when it detects multiple
# alternatives for one prover version, e.g. "Z3 4.13.3",
# "Z3 4.13.3 (counterexamples)", and "Z3 4.13.3 (noBV)".
# The trailing comma explicitly selects the default (empty) alternative.
# Versions are pinned to the Debian 13 environment reported on computer10.
# If a version changes, inspect "why3 --list-provers" rather than choosing
# an unrelated or unsupported alternative.
for selector in "Z3,4.13.3," "CVC5,1.1.2,"; do
  prover="${selector%%,*}"
  printf '\n== %s (%s): positive control ==\n' "$prover" "$selector"
  if positive="$(timeout 30s why3 prove -P "$selector" "$fixture" \
    -T BackendSmoke -G TrueGoal 2>&1)"; then
    printf '%s\n' "$positive"
  else
    printf 'ERROR: %s positive-control invocation failed.\n%s\n' \
      "$prover" "$positive" >&2
    exit 3
  fi
  # This check deliberately examines the prover's ANSWER, not merely
  # process exit code: Why3 can exit normally after Unknown or Timeout.
  if ! why3_result_is "$positive" TrueGoal Valid; then
    printf 'ERROR: %s did not prove TrueGoal as Valid.\n' "$prover" >&2
    exit 4
  fi

  printf '\n== %s: false-goal negative control ==\n' "$prover"
  # Why3's "prove" command may exit with status 1 for an unproved goal.
  # Capture the result anyway; unlike an invocation error, "Unknown (sat)"
  # is a structured Why3 answer observed on computer10 for 0 = 1.
  # Do NOT treat a generic Unknown, timeout, or tool failure as success.
  negative_rc=0
  negative="$(timeout 30s why3 prove -P "$selector" "$fixture" \
    -T BackendSmoke -G FalseGoal 2>&1)" || negative_rc=$?
  printf '%s\n' "$negative"
  if (( negative_rc != 0 && negative_rc != 1 )); then
    printf 'ERROR: %s negative control exited unexpectedly (%d).\n' \
      "$prover" "$negative_rc" >&2
    exit 5
  fi

  if why3_result_is "$negative" FalseGoal Valid; then
    printf 'ERROR: %s incorrectly proved FalseGoal as Valid!\n' "$prover" >&2
    exit 6
  fi

  if why3_result_is "$negative" FalseGoal Invalid; then
    # "Invalid" is Why3's explicit invalidity classification.
    printf 'PASS: %s proved TrueGoal; Why3 classified FalseGoal Invalid.\n' \
      "$prover"
  elif why3_result_is "$negative" FalseGoal 'Unknown \(sat\)'; then
    # This is a SAT indication, NOT a Why3 Invalid result. Since 0 = 1
    # is independently false, it is useful evidence that this prover did
    # not incorrectly discharge the negative control. No claim of a
    # formally established counterexample is made.
    printf 'PASS: %s proved TrueGoal; FalseGoal was NOT proved (Unknown (sat)).\n' \
      "$prover"
  else
    printf 'ERROR: %s: FalseGoal must report Invalid or Unknown (sat), not an inconclusive or failed result.\n' \
      "$prover" >&2
    exit 7
  fi
done

printf '\n%s\n' 'PASS: Both Why3 backend smoke checks completed; inspect each negative-control status.'
