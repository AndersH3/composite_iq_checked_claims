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

printf '%s\n' 'Ada/SPARK/Why3 offline installer syntax, plan, and safety controls passed'
