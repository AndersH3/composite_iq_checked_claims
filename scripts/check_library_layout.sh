#!/usr/bin/env bash
# Verify single canonical ownership of reused SPARK, Python and Rocq code.
# This structural gate is complementary to the Rocq 9.2 kernel, the Deal test
# suite, and future source-pinned GNATprove campaigns; it cannot determine
# whether mathematically different implementations are semantically equivalent.
set -euo pipefail
cd "$(dirname "$0")/.."

for shared in \
  library/python/numeric.py library/python/statistics.py \
  library/spark/src/shared_equicorrelation.ads \
  library/spark/src/shared_equicorrelation.adb \
  library/spark/src/shared_event_arithmetic.ads \
  library/spark/src/shared_event_arithmetic.adb \
  library/spark/src/shared_normal_sampling.ads \
  library/spark/src/shared_normal_sampling.adb \
  library/rocq/FiniteSum.v library/rocq/FiniteConditionalCovariance.v \
  library/rocq/TwoObservationSchur.v
do
  test -f "$shared" || { echo "Missing canonical source: $shared" >&2; exit 1; }
done

for project in hoeflin-ferguson towers-multiple-test-admissions sequential-conditional-means
do
  test -d "analyses/$project/rocq" || exit 1
  test -d "analyses/$project/ada/src" || exit 1
  test -d "analyses/$project/scripts" || exit 1
  grep -q "library.python.numeric import finite_real" "analyses/$project/scripts/"*.py ||
    { echo "Missing Python numeric library consumer: $project" >&2; exit 1; }
  if grep -q "def _finite(" "analyses/$project/scripts/"*.py; then
    echo "Duplicate finite-real validator in $project" >&2
    exit 1
  fi
done

for spec in \
  "analyses/hoeflin-ferguson/ada/hoeflin.gpr" \
  "analyses/towers-multiple-test-admissions/ada/towers.gpr" \
  "analyses/sequential-conditional-means/ada/sequential.gpr" \
  "analyses/sequential-conditional-means/ada/sequential_core_proof.gpr"
do
  grep -q "../../../library/spark/src" "$spec" ||
    { echo "No canonical SPARK source directory in $spec" >&2; exit 1; }
done

# Enforce shared normal-sampling ownership and reject cross-report source paths.
# No report is permitted to retain an independent copy of the central LCG
# coefficients or Box--Muller elementary-function calculation.
if grep -RniE '6_364_136_223_846_793_005|1_442_695_040_888_963_407' \
    analyses/hoeflin-ferguson/ada/src/normal_support.ad[bs] \
    analyses/sequential-conditional-means/ada/src/sequential_sampling.ad[bs]; then
  echo "Duplicated central PRNG constants in a specialized adapter" >&2
  exit 1
fi
if grep -niE 'Math\.(Cos|Sin|Log)' \
    analyses/hoeflin-ferguson/ada/src/normal_support.adb \
    analyses/sequential-conditional-means/ada/src/sequential_sampling.adb; then
  echo "Report-local Box--Muller implementation duplicates shared library" >&2
  exit 1
fi
grep -q "Shared_Normal_Sampling.Normal_Pair" analyses/hoeflin-ferguson/ada/src/normal_support.adb
grep -q "Shared_Normal_Sampling.Normal_Pair" analyses/sequential-conditional-means/ada/src/sequential_sampling.adb
grep -q "Shared_Normal_Sampling.Checked_Sqrt" analyses/sequential-conditional-means/ada/src/sequential_sampling.adb
grep -q "Shared_Normal_Sampling.Reset" analyses/sequential-conditional-means/ada/src/sequential_run.adb
if grep -qE 'hoeflin-ferguson/ada/src|hoeflin_core\.|hoeflin_boundary_models\.|normal_support\.' \
    analyses/sequential-conditional-means/ada/sequential.gpr; then
  echo "Sequential still links Hoeflin-specific source code" >&2
  exit 1
fi
if grep -niE '^[[:space:]]*with[[:space:]]+(Hoeflin_|Normal_Support)' \
    analyses/sequential-conditional-means/ada/src/*.ad[bs]; then
  echo "Sequential imports Hoeflin-specific Ada packages" >&2
  exit 1
fi
grep -q "Shared_Equicorrelation.Numerator" analyses/hoeflin-ferguson/ada/src/hoeflin_core.adb
grep -q "Shared_Equicorrelation.Numerator" analyses/sequential-conditional-means/ada/src/sequential_core.adb
grep -q "Shared_Event_Arithmetic.Union_Units" analyses/towers-multiple-test-admissions/ada/src/admission_core.adb
grep -q "Shared_Event_Arithmetic.Complement_Units" analyses/towers-multiple-test-admissions/ada/src/admission_core.adb
grep -q "from library.python.statistics import" reporting/simulate.py
grep -q "require(finite_real(value)" analyses/sequential-conditional-means/scripts/validate_spark.py

# Shared libraries must not import report-local SPARK packages.
if grep -niE "^[[:space:]]*with[[:space:]]+(Hoeflin_|Sequential_|Admission_|Normal_Support|Towers_)" library/spark/src/*.ad[bs]; then
  echo "Shared SPARK library illegally depends on specialized report source" >&2
  exit 1
fi
# The former shared proof sources must not remain as duplicate .v copies.
if find rocq -maxdepth 1 -name '*.v' | grep -q .; then
  echo "Noncanonical duplicate proof sources remain under rocq/" >&2
  exit 1
fi
test -f analyses/hoeflin-ferguson/rocq/Hoeflin.v
test -f analyses/towers-multiple-test-admissions/rocq/Admissions.v
test -f analyses/sequential-conditional-means/rocq/SequentialReport.v
echo "Central source ownership and all three report consumers: OK."
