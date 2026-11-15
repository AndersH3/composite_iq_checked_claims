#!/usr/bin/env bash
# Real GNATprove 16 integration smoke test for a ten-postcondition SPARK unit.
# AI disclosure: authored with AI assistance; not yet executed on computer10.
#
# No network, sudo, package changes, opam switches, Alire index changes,
# repository writes, or global PATH updates are performed. All proof artifacts
# are placed in a disposable copy. The run must use actual GNATprove rather
# than a mock and --checks-as-errors to reject unproved obligations.
# A successful smoke test is NOT proof of the three statistical reports.
set -euo pipefail

root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd -P)"
source_dir="$root/verification/spark_smoke"
gnatprove="${GNATPROVE:-$HOME/.local/opt/ada-spark/bin/gnatprove}"

if [[ ! -x "$gnatprove" ]]; then
  printf 'ERROR: GNATprove executable not found: %s\n' "$gnatprove" >&2
  exit 2
fi
for file in spark_smoke.gpr src/bounded_counts.ads src/bounded_counts.adb; do
  if [[ ! -f "$source_dir/$file" ]]; then
    printf 'ERROR: Missing SPARK smoke fixture: %s\n' "$file" >&2
    exit 2
  fi
done

workdir="$(mktemp -d)"
trap 'rm -rf -- "$workdir"' EXIT
mkdir -p "$workdir/src"
cp -- "$source_dir/spark_smoke.gpr" "$workdir/spark_smoke.gpr"
cp -- "$source_dir/src/bounded_counts.ads" "$workdir/src/bounded_counts.ads"
cp -- "$source_dir/src/bounded_counts.adb" "$workdir/src/bounded_counts.adb"

printf '%s\n' '== Actual GNATprove bundled toolchain version =='
"$gnatprove" --version
printf '\n%s\n' '== Proving 10 functional postconditions, 2 preconditions and flow aspects =='
printf '%s\n' 'Positive proof: checked addition with exact count and headroom guarantees'
(
  cd "$workdir"
  # These switches are already used by the project's native proof runner.
  # --mode=all checks both flow and proof; --checks-as-errors makes each
  # unproved verification condition fatal; -f requests fresh analysis.
  "$gnatprove" -P spark_smoke.gpr --mode=all \
    --checks-as-errors --warnings=error --report=statistics \
    --prover=cvc5,z3,altergo --timeout=15 --steps=0 \
    -j2 -f -U
)
# GNATprove's command return code under --checks-as-errors is the
# acceptance gate; a version banner or flow-only run is insufficient.
printf '\n%s\n' 'PASS: GNATprove completed the SPARK proof smoke with --checks-as-errors.'
