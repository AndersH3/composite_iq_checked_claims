#!/usr/bin/env bash
# Real GNATprove 16 integration smoke test for a ten-postcondition SPARK unit.
# AI disclosure: authored with AI assistance; user-validated on computer10
# against GNATprove FSF 16.1.0 with 11/11 checks proved. Future changes
# require fresh local proof runs; an archived raw report is not retained.
#
# No network, sudo, package changes, opam switches, Alire index changes,
# repository writes, or global PATH updates are performed. All proof artifacts
# are placed in a disposable copy. The run must use actual GNATprove rather
# than a mock and --checks-as-errors=on to reject unproved obligations.
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
  # --mode=all checks both flow and proof; GNATprove 16 requires
  # --checks-as-errors=on (not a bare flag), making unproved VCs fatal.
  # --warnings=error independently rejects warnings; -f reruns analysis.
  "$gnatprove" -P spark_smoke.gpr --mode=all \
    --checks-as-errors=on --warnings=error --report=statistics \
    --prover=cvc5,z3,altergo --timeout=15 --steps=0 \
    -j2 -f -U
)
# A zero exit code alone could mask an empty/unconfigured analysis.
# Demand a native nonempty SPARK summary from this disposable source tree.
# --checks-as-errors=on above additionally requires every generated check to
# pass; this does not establish solver soundness or model adequacy.
mapfile -d '' -t reports < <(
  find "$workdir" -type f -name 'gnatprove.out' -print0
)
if (( ${#reports[@]} == 0 )); then
  printf '%s\n' 'ERROR: GNATprove emitted no native gnatprove.out report.' >&2
  exit 4
fi
for report in "${reports[@]}"; do
  if ! grep -Fq 'Summary of SPARK analysis' "$report" ||
     ! grep -Eq '^Total[[:space:]]+[1-9][0-9]*[[:space:]]+' "$report"; then
    printf 'ERROR: Missing or empty native proof summary: %s\n' "$report" >&2
    exit 5
  fi
  printf 'Native proof summary from %s:\n' "$(basename "$report")"
  grep -E '^Total[[:space:]]+[1-9][0-9]*[[:space:]]+' "$report"
done
printf '\n%s\n' 'PASS: GNATprove completed nonempty SPARK analysis with --checks-as-errors=on.'
