#!/usr/bin/env bash
# Offline, non-mutating regression tests for the Ada/SPARK and Why3 installer.
# Tests avoid sudo, apt, downloads, Alire, and Standard ML compilers.
set -euo pipefail
# Make unexpected regressions visible instead of exiting silently under
# 'set -e'. Capture the original exit code as a trap argument, rather than
# assigning a variable inside an opaque trap string (ShellCheck SC2154).
# A dedicated function keeps the exit-code reporting easy to test and read.
report_regression_error() {
  local exit_code="$1"
  local line_number="$2"
  local failed_command="$3"
  printf 'ERROR: offline regression line %s exited %s: %s\n' \
    "$line_number" "$exit_code" "$failed_command" >&2
}
trap 'report_regression_error "$?" "$LINENO" "$BASH_COMMAND"' ERR
cd "$(dirname "$0")/.."
installer=scripts/install_ada_spark_why3.sh

bash -n "$installer"
bash "$installer" --help | grep -F -- '--metis-source' >/dev/null
bash "$installer" --help | grep -F -- '--install-spark' >/dev/null
bash "$installer" --help | grep -F -- '--smoke-ada' >/dev/null
plan="$(bash "$installer" --plan)"
grep -F 'gappa' <<<"$plan" >/dev/null
grep -F 'why3' <<<"$plan" >/dev/null
grep -F 'gprbuild' <<<"$plan" >/dev/null
grep -F 'gnat' <<<"$plan" >/dev/null
grep -F 'cvc5' <<<"$plan" >/dev/null
grep -F 'gnatprove' <<<"$plan" >/dev/null
# Run the real Ada smoke test only on hosts where GNAT is present.
if command -v gnatmake >/dev/null; then
  bash "$installer" --smoke-ada | grep -F 'succeeded' >/dev/null
fi
grep -F '7a23e4ea68bc92927716777ebc98bea09e91fe24' <<<"$plan" >/dev/null
grep -F 'apt install metis is WRONG' <<<"$plan" >/dev/null
# The Alire 1.2.1 catalog cannot supply GNATprove 16.1.0. The
# installer must instead point to the exact official upstream asset
# with immutable length and SHA256 pinned in the stable-1.4.0 index.
grep -F 'GNATprove 16.1.0' <<<"$plan" >/dev/null
grep -F 'gnatprove-x86_64-linux-16.1.0-1.tar.gz' <<<"$plan" >/dev/null
grep -F '82528bef29857e239373fcc36732837d743f5a00805d502c70455422ffc97191' <<<"$plan" >/dev/null
grep -F '472919963 bytes' <<<"$plan" >/dev/null
grep -F 'Alire 1.2.1 catalog lists only older GNATprove releases' <<<"$plan" >/dev/null
grep -F 'why3 config detect' <<<"$plan" >/dev/null

# Offline preflight: the install action must reject an unsupported
# platform before network/download/extraction or any user-prefix changes.
# No fake upstream binaries or checksum bypasses are accepted by the
# production installer; the real vendor SHA256 is tested only on computer10.
fixture="$(mktemp -d)"
trap 'rm -rf -- "$fixture"' EXIT
mkdir -p "$fixture/home" "$fixture/bin"
cat > "$fixture/bin/uname" <<'MOCK_UNAME'
#!/usr/bin/env bash
set -euo pipefail
if [[ "${1:-}" == "-s" ]]; then
  printf '%s\n' 'FreeBSD'
elif [[ "${1:-}" == "-m" ]]; then
  printf '%s\n' 'amd64'
else
  exit 90
fi
MOCK_UNAME
chmod 755 "$fixture/bin/uname"
if HOME="$fixture/home" PATH="$fixture/bin:$PATH" \
    bash "$installer" --install-spark >"$fixture/wrong-platform.out" 2>&1; then
  printf '%s\n' 'ERROR: GNATprove installation accepted non-Linux platform' >&2
  exit 1
fi
grep -F 'only for Linux x86_64' "$fixture/wrong-platform.out" >/dev/null
test ! -e "$fixture/home/.local/opt/ada-spark"
rm "$fixture/bin/uname"

# Debian Why3 1.8.0 requires "config detect" and "--list-provers".
# A fake binary that refuses the obsolete "--detect" checks exact dispatch.
cat > "$fixture/bin/why3" <<'MOCK_WHY3'
#!/usr/bin/env bash
set -euo pipefail
printf '%s\n' "$*" >>"$HOME/why3-calls"
if [[ "$*" == "config detect" ]]; then
  printf '%s\n' 'Why3 1.8 detection stub'
elif [[ "$*" == "--list-provers" ]]; then
  printf '%s\n' 'Why3 known provers stub'
else
  printf 'Unsupported Why3 arguments: %s\n' "$*" >&2
  exit 79
fi
MOCK_WHY3
chmod 755 "$fixture/bin/why3"
HOME="$fixture/home" PATH="$fixture/bin:$PATH" \
  bash "$installer" --detect >"$fixture/detect.out"
grep -Fx 'config detect' "$fixture/home/why3-calls" >/dev/null
grep -Fx -- '--list-provers' "$fixture/home/why3-calls" >/dev/null
[[ "$(wc -l <"$fixture/home/why3-calls")" -eq 2 ]]

# Contract-like negative controls for shell CLI and manifest integrity.
if bash "$installer" --unsupported-option >/dev/null 2>&1; then
  printf '%s\n' 'ERROR: unknown CLI action was accepted' >&2
  exit 1
fi
if grep -Eq '(^|[[:space:]])metis([[:space:]]|$)'     <(sed -n '/ADA_PACKAGES=(/,/^)/p' "$installer"); then
  printf '%s\n' 'ERROR: Debian graph-partitioning metis entered the apt manifest' >&2
  exit 1
fi
if grep -Eq 'curl[[:space:]].*(-k|--insecure)' "$installer"; then
  printf '%s\n' 'ERROR: TLS verification bypass was introduced' >&2
  exit 1
fi
if grep -Eq '^[[:space:]]*(opam[[:space:]]+switch|apt-get[[:space:]]+dist-upgrade)' "$installer"; then
  printf '%s\n' 'ERROR: script changes unrelated toolchain or entire system' >&2
  exit 1
fi

# Check the real proof-result audit script with a deterministic mock. The
# production script must accept a true goal, reject a false goal, and never
# equate process exit code 0 with successful proof verification.
smoke=verification/why3/check_backends.sh
test -f verification/why3/backend_smoke.why
bash -n "$smoke"
grep -F 'goal TrueGoal' verification/why3/backend_smoke.why >/dev/null
grep -F 'goal FalseGoal' verification/why3/backend_smoke.why >/dev/null
cat > "$fixture/bin/why3" <<'MOCK_PROOF_WHY3'
#!/usr/bin/env bash
set -euo pipefail
case "${1:-}" in
  --version)
    printf '%s\n' 'Why3 1.8.0 (mock)'
    ;;
  prove)
    [[ "$*" == *" -T BackendSmoke -G "* ]] || exit 78
    # Explicit version AND empty alternative are mandatory: a short name
    # would be ambiguous on computer10 due to multiple prover variants.
    [[ "$*" == *" -P Z3,4.13.3, "* ||
       "$*" == *" -P CVC5,1.1.2, "* ]] || {
      printf 'More than one prover corresponds to the abbreviated name\n' >&2
      exit 79
    }
    # Match the real Why3 1.8 text format observed on computer10:
    # File "..." line ..., Goal TrueGoal., Prover result is: Valid (...).
    # A one-line mock used previously allowed the broken result parser
    # to pass CI while failing on the actual Debian installation.
    if [[ "$*" == *" -G TrueGoal" ]]; then
      printf '%s\n' 'File "backend_smoke.why", line 20, characters 17-41:'
      printf 'Goal %s.\n' "${WHY3_FAKE_GOAL:-TrueGoal}"
      printf 'Prover result is: %s (0.00s, 18 steps).\n' \
        "${WHY3_FAKE_POSITIVE:-Valid}"
    elif [[ "$*" == *" -G FalseGoal" ]]; then
      printf '%s\n' 'File "backend_smoke.why", line 25, characters 18-23:'
      printf '%s\n' 'Goal FalseGoal.'
      printf 'Prover result is: %s (0.00s, 11 steps).\n' \
        "${WHY3_FAKE_NEGATIVE:-Unknown (sat)}"
      # Reproduce nonzero Why3 exit code for an unproved goal as observed
      # on computer10; a well-formed result must still be parsed.
      exit "${WHY3_FAKE_NEGATIVE_RC:-2}"
    else
      exit 80
    fi
    ;;
  *)
    printf '%s\n' 'Unknown mock why3 command' >&2
    exit 81
    ;;
esac
MOCK_PROOF_WHY3
chmod 755 "$fixture/bin/why3"
HOME="$fixture/home" PATH="$fixture/bin:$PATH" \
  bash "$smoke" >"$fixture/proof-smoke.out"
grep -F 'Both Why3 backend smoke checks completed' "$fixture/proof-smoke.out" >/dev/null
grep -F 'FalseGoal was NOT proved (Unknown (sat))' "$fixture/proof-smoke.out" >/dev/null
grep -F 'Z3,4.13.3,' "$fixture/proof-smoke.out" >/dev/null
grep -F 'CVC5,1.1.2,' "$fixture/proof-smoke.out" >/dev/null
# Negative controls against incorrectly claiming that a false goal is Valid,
# accepting an arbitrary Unknown, a timeout, or a result for the wrong goal.
# Why3 1.8 exit status 2 (unproved goal) is required with exact
# Invalid or Unknown (sat) answer. Exit 1 is not accepted as proof evidence.
HOME="$fixture/home" PATH="$fixture/bin:$PATH" WHY3_FAKE_NEGATIVE=Invalid \
  bash "$smoke" >"$fixture/invalid-negative.out"
grep -F 'Why3 classified FalseGoal Invalid' "$fixture/invalid-negative.out" >/dev/null
if HOME="$fixture/home" PATH="$fixture/bin:$PATH" WHY3_FAKE_NEGATIVE=Valid \
    bash "$smoke" >"$fixture/unsound.out" 2>&1; then
  printf '%s\n' 'ERROR: Why3 proof audit accepted a false goal as Valid' >&2
  exit 1
fi
grep -F 'incorrectly proved FalseGoal as Valid' "$fixture/unsound.out" >/dev/null

if HOME="$fixture/home" PATH="$fixture/bin:$PATH" WHY3_FAKE_NEGATIVE=Unknown \
    bash "$smoke" >"$fixture/unknown-negative.out" 2>&1; then
  printf '%s\n' 'ERROR: Why3 proof audit accepted Unknown for FalseGoal' >&2
  exit 1
fi
grep -F 'FalseGoal must report Invalid or Unknown (sat)' "$fixture/unknown-negative.out" >/dev/null

if HOME="$fixture/home" PATH="$fixture/bin:$PATH" WHY3_FAKE_POSITIVE=Unknown \
    bash "$smoke" >"$fixture/unknown-positive.out" 2>&1; then
  printf '%s\n' 'ERROR: Why3 proof audit accepted Unknown for TrueGoal' >&2
  exit 1
fi
grep -F 'did not prove TrueGoal as Valid' "$fixture/unknown-positive.out" >/dev/null

if HOME="$fixture/home" PATH="$fixture/bin:$PATH" WHY3_FAKE_NEGATIVE_RC=124 \
    bash "$smoke" >"$fixture/timeout-negative.out" 2>&1; then
  printf '%s\n' 'ERROR: Why3 proof audit accepted an interrupted solver call' >&2
  exit 1
fi
grep -F 'negative control exited with 124' "$fixture/timeout-negative.out" >/dev/null

# Ensure a CLI failure (exit 1) and a silent "success" (exit 0)
# cannot masquerade as Why3's unproved-goal result (exit 2).
for invalid_rc in 0 1; do
  if HOME="$fixture/home" PATH="$fixture/bin:$PATH" WHY3_FAKE_NEGATIVE_RC="$invalid_rc" \
      bash "$smoke" >"$fixture/bad-exit-$invalid_rc.out" 2>&1; then
    printf 'ERROR: Why3 audit accepted negative-control exit %s\n' "$invalid_rc" >&2
    exit 1
  fi
  grep -F "negative control exited with $invalid_rc" \
    "$fixture/bad-exit-$invalid_rc.out" >/dev/null
done

if HOME="$fixture/home" PATH="$fixture/bin:$PATH" WHY3_FAKE_GOAL=UnrelatedGoal \
    bash "$smoke" >"$fixture/wrong-goal.out" 2>&1; then
  printf '%s\n' 'ERROR: Why3 audit attributed a Valid result to the wrong goal' >&2
  exit 1
fi
grep -F 'did not prove TrueGoal as Valid' "$fixture/wrong-goal.out" >/dev/null

# Native SPARK smoke fixture: structurally verify that the test uses a
# substantive contracted subprogram and proof-only native flags. This is
# NOT a substitute for executing GNATprove on computer10.
spark_smoke=scripts/smoke_gnatprove.sh
spark_spec=verification/spark_smoke/src/bounded_counts.ads
test -f verification/spark_smoke/src/bounded_counts.adb
test -f verification/spark_smoke/spark_smoke.gpr
bash -n "$spark_smoke"
grep -F 'Global => null' "$spark_spec" >/dev/null
grep -F 'Depends => ' "$spark_spec" >/dev/null
grep -F 'Pre =>' "$spark_spec" >/dev/null
grep -F 'Post =>' "$spark_spec" >/dev/null
grep -F -- '--mode=all' "$spark_smoke" >/dev/null
# GNATprove 16.1.0 requires the boolean value in the same argument.
# A bare --checks-as-errors consumes the next switch as its value and
# fails before the proof starts, even though the old offline test passed.
grep -F -- '--checks-as-errors=on' "$spark_smoke" >/dev/null
grep -F -- '--warnings=error' "$spark_smoke" >/dev/null
grep -F 'Summary of SPARK analysis' "$spark_smoke" >/dev/null

# Two adversarial offline mock executions:
# 1. A fake prover returning 0 without any native proof report MUST fail.
# 2. A fake prover returning nonzero MUST also fail, even with version data.
# Both tests prove that this shell wrapper cannot be fooled by an exit
# status alone; only an actual GNATprove run can validate the fixture.
cat > "$fixture/bin/fake-gnatprove" <<'MOCK_GNATPROVE'
#!/usr/bin/env bash
set -euo pipefail
if [[ "${1:-}" == "--version" ]]; then
  printf '%s\n' 'FSF GNATprove fake version; not a proof'
  exit 0
fi
# Record each complete argv exactly once per line, preserving argument
# boundaries so the regression detects a value swallowed by a bare option.
printf '%s\n' "$@" > "${GNATPROVE_FAKE_ARGS_LOG:?}"
exit "${GNATPROVE_FAKE_EXIT:-0}"
MOCK_GNATPROVE
chmod 755 "$fixture/bin/fake-gnatprove"
if GNATPROVE="$fixture/bin/fake-gnatprove" \
    GNATPROVE_FAKE_ARGS_LOG="$fixture/fake-invocation.argv" \
    bash "$spark_smoke" >"$fixture/fake-no-report.out" 2>&1; then
  printf '%s\n' 'ERROR: Native SPARK smoke accepted an empty fake proof' >&2
  exit 1
fi
grep -F 'no native gnatprove.out report' "$fixture/fake-no-report.out" >/dev/null
grep -Fx -- '--checks-as-errors=on' "$fixture/fake-invocation.argv" >/dev/null
grep -Fx -- '--warnings=error' "$fixture/fake-invocation.argv" >/dev/null
grep -Fx -- '--mode=all' "$fixture/fake-invocation.argv" >/dev/null
if grep -Fx -- '--checks-as-errors' "$fixture/fake-invocation.argv" >/dev/null; then
  printf '%s\n' 'ERROR: GNATprove 16 received a bare --checks-as-errors' >&2
  exit 1
fi

if GNATPROVE="$fixture/bin/fake-gnatprove" GNATPROVE_FAKE_EXIT=13 \
    GNATPROVE_FAKE_ARGS_LOG="$fixture/fake-error.argv" \
    bash "$spark_smoke" >"$fixture/fake-error.out" 2>&1; then
  printf '%s\n' 'ERROR: Native SPARK smoke accepted a failing fake prover' >&2
  exit 1
fi
if grep -F 'PASS: GNATprove completed' "$fixture/fake-error.out" >/dev/null; then
  printf '%s\n' 'ERROR: Native SPARK smoke printed PASS on fake failure' >&2
  exit 1
fi

printf '%s\n' 'Ada/SPARK/Why3 offline checksum-plan, safe-platform, and Why3 regression tests passed'
