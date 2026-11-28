#!/bin/sh
# Canonical Rocq source compiler for the shared math library and the four
# specialized report libraries. Uses the complete explicit 45-module dependency order,
# never copies sources back into Git, and rejects duplicate module basenames.
# This is a build utility, not a substitute for the Rocq kernel checker.
set -eu
# Optional independent kernel replay checks all canonical module roots.
case "${1:-}" in
  "") independent=no ;;
  --independent-check) independent=yes ;;
  *) echo "Usage: $0 [--independent-check]" >&2; exit 2 ;;
esac
[ "$#" -le 1 ] || exit 2
ROOT=$(CDPATH="" cd -- "$(dirname -- "$0")/.." && pwd)
WORK=$(mktemp -d)
trap 'rm -rf "$WORK"' EXIT HUP INT TERM
# The same ordered source inventory is consumed by the documentation audit.
manifest="$ROOT/rocq/canonical-modules.txt"
test -s "$manifest"
while IFS= read -r relative; do
  f="$ROOT/$relative"
  [ -f "$f" ] || { echo "Missing proof source: $f" >&2; exit 1; }
  name=$(basename "$f")
  [ ! -e "$WORK/$name" ] || { echo "Duplicate Rocq module: $name" >&2; exit 1; }
  cp "$f" "$WORK/$name"
done < "$manifest"
cd "$WORK"
rocq --version
while IFS= read -r relative; do
  rocq compile "$(basename "$relative")"
done < "$manifest"
printf '%s\n' 'Rocq kernel compilation passed for all 45 modules.'
if [ "$independent" = yes ]; then
  set --
  while IFS= read -r relative; do
    set -- "$@" "$(basename "$relative" .v)"
  done < "$manifest"
  rocq check "$@"
  printf '%s\n' 'Independent kernel check passed for all canonical module roots.'
fi
