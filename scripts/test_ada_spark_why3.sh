#!/usr/bin/env bash
# Offline, non-mutating regression tests for the Ada/SPARK and Why3 installer.
# The tests do not use sudo, apt, network, Alire, or a Standard ML compiler.
set -euo pipefail
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

printf '%s\n' 'Ada/SPARK/Why3 offline plan, Alire 1.2 GNATprove, and Why3 detection regression tests passed'
