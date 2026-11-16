#!/bin/sh
# Canonical Rocq source compiler for the shared math library and the three
# specialized report libraries. Uses the complete explicit 35-module dependency order,
# never copies sources back into Git, and rejects duplicate module basenames.
# This is a build utility, not a substitute for the Rocq kernel checker.
set -eu
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
WORK=$(mktemp -d)
trap 'rm -rf "$WORK"' EXIT HUP INT TERM
for f in "$ROOT"/library/rocq/*.v \
  "$ROOT"/analyses/hoeflin-ferguson/rocq/*.v \
  "$ROOT"/analyses/towers-multiple-test-admissions/rocq/*.v \
  "$ROOT"/analyses/sequential-conditional-means/rocq/*.v
do
  [ -f "$f" ] || { echo "Missing proof source: $f" >&2; exit 1; }
  name=$(basename "$f")
  [ ! -e "$WORK/$name" ] || { echo "Duplicate Rocq module: $name" >&2; exit 1; }
  cp "$f" "$WORK/$name"
done
cd "$WORK"
rocq --version
rocq compile FiniteSum.v
rocq compile Hoeflin.v
rocq compile Admissions.v
rocq compile FiniteUnion.v
rocq compile FiniteMoments.v
rocq compile FiniteBridge.v
rocq compile FourCellBridge.v
rocq compile ThreeTestAdmissions.v
rocq compile ThreeTestPairBridge.v
rocq compile ThreeTestConditionalStrata.v
rocq compile TwoStratumAssociation.v
rocq compile TwoStratumReversal.v
rocq compile ThreeTestSelectionDecomposition.v
rocq compile ThreeTestReversalCriteria.v
rocq compile SequentialReport.v
rocq compile SequentialSensitivity.v
rocq compile ReportRounding.v
rocq compile ReportCounterexample.v
rocq compile EquicorrelationSpectral.v
rocq compile EquicorrelationVectors.v
rocq compile EquicorrelationInverseVectors.v
rocq compile FiniteTwoCellProjection.v
rocq compile FiniteNestedProjection.v
rocq compile FiniteConditionalCovariance.v
rocq compile FiniteConditionalResidual.v
rocq compile TwoObservationSchur.v
rocq compile TrivariateSchur.v
rocq compile WilsonScoreAlgebra.v
rocq compile SamplingPrecision.v
rocq compile ConditionalRatioStability.v
rocq compile PooledMomentsAlgebra.v
rocq compile ThreeGroupPooling.v
rocq compile TwoRatePrecision.v
rocq compile StratifiedBernoulli.v
rocq compile ThreeTestSchur.v
