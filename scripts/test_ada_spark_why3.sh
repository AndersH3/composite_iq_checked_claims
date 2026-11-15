#!/usr/bin/env bash
# Offline, non-mutating regression tests for the Ada/SPARK and Why3 installer.
# The tests do not use sudo, apt, network, Alire, or a Standard ML compiler.
set -euo pipefail
# Make unexpected regressions visible instead of exiting silently under
# 'set -e'. This diagnostic does not alter expected-failure test cases.
trap 'status=$?; printf "ERROR: offline regression line %s exited %s: %s\n" "$LINENO" "$status" "$BASH_COMMAND" >&2' ERR
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
grep -F 'alr -n get gnatprove=16.1.0' <<<"$plan" >/dev/null
grep -F 'why3 config detect' <<<"$plan" >/dev/null

# Simulate Alire 1.2.1, which supports "get" but rejects "install".
# A fake downloaded GNATprove tree tests bundle selection, wrapper PATH
# behavior, version checking, and idempotent reuse without network access.
fixture="$(mktemp -d)"
trap 'rm -rf -- "$fixture"' EXIT
mkdir -p "$fixture/home" "$fixture/bin"
cat > "$fixture/bin/alr" <<'MOCK_ALR'
#!/usr/bin/env bash
set -euo pipefail
printf '%s\n' "$*" >>"$HOME/alr-calls"
[[ "$#" -eq 3 && "$1" == "-n" && "$2" == "get" &&
   "$3" == "gnatprove=16.1.0" ]] || exit 77
mkdir -p gnatprove_16.1.0_test/bin
cat > gnatprove_16.1.0_test/bin/gnatprove <<'MOCK_PROVER'
#!/usr/bin/env bash
set -euo pipefail
[[ "${1:-}" == "--version" ]] || exit 78
echo 'GNATprove 16.1.0 (offline test stub)'
MOCK_PROVER
chmod 755 gnatprove_16.1.0_test/bin/gnatprove
MOCK_ALR
chmod 755 "$fixture/bin/alr"

HOME="$fixture/home" PATH="$fixture/bin:$PATH" \
  bash "$installer" --install-spark >"$fixture/install.out"
grep -F 'GNATprove 16.1.0 (offline test stub)' "$fixture/install.out" >/dev/null
wrapper="$fixture/home/.local/opt/ada-spark/bin/gnatprove"
test -x "$wrapper"
"$wrapper" --version | grep -F 'GNATprove 16.1.0' >/dev/null
HOME="$fixture/home" PATH="$fixture/bin:$PATH" \
  bash "$installer" --install-spark >"$fixture/reinstall.out"
[[ "$(wc -l <"$fixture/home/alr-calls")" -eq 1 ]]

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

printf '%s\n' 'Ada/SPARK/Why3 offline plan, Alire 1.2 GNATprove, and Why3 detection regression tests passed'
