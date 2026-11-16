#!/usr/bin/env bash
# Enforce canonical Python statistical sources and Rocq library ownership.
# This is a structural audit, not a proof of model correctness.
set -euo pipefail
cd "$(dirname "$0")/.."

for source in \
  library/python/numeric.py library/python/statistics.py \
  library/rocq/FiniteSum.v library/rocq/FiniteConditionalCovariance.v \
  library/rocq/ListPoolingAlgebra.v library/rocq/FourContrastCovariance.v \
  library/rocq/SampleContrastCauchy.v \
  reporting/simulate.py reporting/assets.py reporting/provenance.py
do
  test -f "$source" || { echo "Missing canonical source: $source" >&2; exit 1; }
done

for project in hoeflin-ferguson towers-multiple-test-admissions sequential-conditional-means
do
  test -d "analyses/$project/rocq" || exit 1
  if test -d "analyses/$project/scripts"; then
    grep -q "library.python.numeric import finite_real" "analyses/$project/scripts/"*.py || {
      echo "Missing shared numeric consumer: $project" >&2; exit 1;
    }
    if grep -q "def _finite(" "analyses/$project/scripts/"*.py; then
      echo "Duplicate finite-real helper in $project" >&2
      exit 1
    fi
  fi
done

if find . -path './.git' -prune -o -type f \( -name '*.adb' -o -name '*.ads' -o -name '*.gpr' \) -print | grep -q .; then
  echo "Retired compiler source or intermediate found in the working tree" >&2
  exit 1
fi
echo "Canonical Python/Rocq source ownership and retired-source exclusion: OK"
