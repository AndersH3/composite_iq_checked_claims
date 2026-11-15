#!/usr/bin/env bash
# Why3 1.8 / Debian 13: validate actual Z3 and CVC5 proof invocations.
# AI disclosure: drafted with AI assistance. This is a smoke test, NOT a
# proof of the correctness of the underlying SMT solvers.
#
# Positive control must be proved Valid; negative control must be Invalid.
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

printf '%s\n' 'Why3 external backend smoke test (positive and negative controls)'
why3 --version
for prover in Z3 CVC5; do
  printf '\n== %s: positive control ==\n' "$prover"
  if positive="$(timeout 30s why3 prove -P "$prover" "$fixture" \
    -T BackendSmoke -G TrueGoal 2>&1)"; then
    printf '%s\n' "$positive"
  else
    printf 'ERROR: %s positive-control invocation failed.\n%s\n' \
      "$prover" "$positive" >&2
    exit 3
  fi
  # This check deliberately examines the prover's ANSWER, not merely
  # process exit code: Why3 can exit normally after Unknown or Timeout.
  if ! grep -Eq 'TrueGoal[[:space:]]*:[[:space:]]*Valid([[:space:]]|$)' <<<"$positive"; then
    printf 'ERROR: %s did not prove TrueGoal as Valid.\n' "$prover" >&2
    exit 4
  fi

  printf '\n== %s: false-goal negative control ==\n' "$prover"
  if negative="$(timeout 30s why3 prove -P "$prover" "$fixture" \
    -T BackendSmoke -G FalseGoal 2>&1)"; then
    printf '%s\n' "$negative"
  else
    printf '%s\n' "$negative"
    printf 'ERROR: %s negative-control invocation failed.\n' "$prover" >&2
    exit 5
  fi
  if grep -Eq 'FalseGoal[[:space:]]*:[[:space:]]*Valid([[:space:]]|$)' <<<"$negative"; then
    printf 'ERROR: %s incorrectly proved a false goal!\n' "$prover" >&2
    exit 6
  fi
  if ! grep -Eq 'FalseGoal[[:space:]]*:[[:space:]]*Invalid([[:space:]]|$)' <<<"$negative"; then
    printf 'ERROR: %s did not reject FalseGoal as Invalid.\n' "$prover" >&2
    exit 7
  fi
  printf 'PASS: %s proved TrueGoal and rejected FalseGoal.\n' "$prover"
done

printf '\n%s\n' 'PASS: Both Why3 backends passed positive and negative controls.'
