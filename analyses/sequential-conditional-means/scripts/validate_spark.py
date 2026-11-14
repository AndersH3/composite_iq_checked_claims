#!/usr/bin/env python3
"""Independently validate the sequential-score Ada calculations and simulations.

The Ada executable and this validator intentionally use different algorithms.
Exact rational arithmetic checks the reported formulas, while NumPy conditions
the complete covariance matrix.  SciPy supplies the normal and chi-square
sampling distributions used for Monte Carlo diagnostics.  These finite checks
do not prove the Gaussian model or the accuracy of the Ada math library.
"""
import argparse
import csv
import fractions
import json
import math
from pathlib import Path

import deal
import numpy as np
from numpy.linalg import LinAlgError
from scipy.stats import chi2, norm


ROOT = Path(__file__).resolve().parents[1]
MOMENT_FIELDS = frozenset({"prediction_z", "mean_z", "population_variance", "conditional_variance"})
LIMIT_FIELDS = frozenset({"prediction_limit_z", "mean_limit_z", "population_variance_limit", "conditional_variance_limit"})
CALCULATION_COLUMNS = frozenset({"r", "k", "c", "a_z"}) | MOMENT_FIELDS | LIMIT_FIELDS
EXTRA_CALCULATION_COLUMNS = frozenset({"prediction_iq", "mean_iq", "population_sd_iq", "conditional_sd_iq", "regression_coefficient", "residual_variance", "common_eigenvalue", "contrast_eigenvalue", "has_inverse", "inverse_diagonal", "inverse_off_diagonal"})
SIMULATION_COLUMNS = frozenset({"mode", "r", "k", "c", "a_z", "trials", "seed", "sample_mean_z", "sample_variance_z"})
MODES = frozenset({"population", "conditional", "population_limit", "conditional_limit"})
MATRIX_LIMIT = 256
# A two-sided 1e-10 tail per moment is deliberately conservative for the
# small, fixed case grid.  This remains a sampling diagnostic, not a proof.
MOMENT_TAIL = 1e-10
NUMERIC_TOLERANCE = 2e-10
# These diagnostic names bind the CSV to the actual identities described in
# the paper.  An executable cannot approve its own answer by changing both
# the ``actual`` and ``expected`` columns together.
CHECK_REFERENCES = {
    "prediction_recursion_r1": 0.0,
    "prediction_recursion_r2": 0.0,
    "prediction_recursion_r3": 0.0,
    "covariance_eigen_common": 0.0,
    "covariance_eigen_contrast": 0.0,
    "inverse_identity_r1": 0.0,
    "inverse_identity_r2": 0.0,
    "inverse_identity_r3": 0.0,
    "total_variance_decomposition": 0.0,
    "conditional_growth_identity": 0.0,
    "counterexample_mean_x0": 0.0,
    "counterexample_variance_x0": 1.0,
    "counterexample_mean_x1": 0.0,
    "counterexample_variance_x1": 1.0,
    "counterexample_covariance": 0.0,
    "counterexample_conditional": -1.0,
    "counterexample_inclusive_mean": -0.5,
    "counterexample_independent_conditional": 0.0,
}


@deal.pre(lambda value: isinstance(value, (int, float, fractions.Fraction)) and not isinstance(value, bool))
@deal.pre(lambda value: math.isfinite(float(value)) and abs(value) <= 1e12)
@deal.post(lambda result: isinstance(result, fractions.Fraction))
@deal.ensure(lambda value, result: float(result) == float(value))
@deal.raises()
@deal.has()
def rational(value):
    """Keep exact fractions and interpret a printed decimal without binary noise."""
    return value if isinstance(value, fractions.Fraction) else fractions.Fraction(str(value))


@deal.pre(lambda condition, message: type(condition) is bool)
@deal.pre(lambda condition, message: isinstance(message, str) and bool(message))
@deal.ensure(lambda condition, message, result: condition and result is None)
@deal.raises(ValueError)
@deal.has()
def require(condition, message):
    """Raise a validation error even under optimized Python, which removes asserts."""
    if not condition:
        raise ValueError(message)


@deal.pre(lambda r, k, c, a_z: type(r) is int and 1 <= r <= 1000)
@deal.pre(lambda r, k, c, a_z: type(k) is int and 1 <= k <= 1_000_000)
@deal.pre(lambda r, k, c, a_z: type(r) is int and r >= 1 and type(k) is int and k >= 1 and isinstance(c, (int, float, fractions.Fraction)) and not isinstance(c, bool) and math.isfinite(float(c)) and fractions.Fraction(-1, r + k - 1) <= rational(c) <= 1)
@deal.pre(lambda r, k, c, a_z: isinstance(a_z, (int, float, fractions.Fraction)) and not isinstance(a_z, bool) and math.isfinite(float(a_z)) and abs(a_z) <= 1000)
@deal.post(lambda result: isinstance(result, dict) and result.keys() == MOMENT_FIELDS and all(isinstance(value, fractions.Fraction) for value in result.values()))
@deal.post(lambda result: 0 <= result["population_variance"] <= 1)
@deal.post(lambda result: result["conditional_variance"] >= 0)
@deal.post(lambda result: result["conditional_variance"] <= result["population_variance"])
@deal.ensure(lambda r, k, c, a_z, result: result["mean_z"] == (r * rational(a_z) + k * result["prediction_z"]) / (r + k))
@deal.ensure(lambda r, k, c, a_z, result: c != 0 or (result["prediction_z"] == 0 and result["population_variance"] == fractions.Fraction(1, r + k) and result["conditional_variance"] == fractions.Fraction(k, (r + k) ** 2)))
@deal.ensure(lambda r, k, c, a_z, result: c != 1 or (result["prediction_z"] == rational(a_z) and result["mean_z"] == rational(a_z) and result["conditional_variance"] == 0))
@deal.raises()
@deal.has()
def exact_moments(r, k, c, a_z):
    """Calculate finite-battery moments with Python's arbitrary-precision rationals.

    The counts distinguish the observed block (r) from subsequent predictions
    (k).  No decimal square root is taken here, so boundary variances remain
    exactly zero rather than small signed floating-point residuals.
    """
    correlation, start = rational(c), rational(a_z)
    total = r + k
    initial_eigenvalue = 1 + (r - 1) * correlation
    total_eigenvalue = 1 + (total - 1) * correlation
    return {
        "prediction_z": r * correlation * start / initial_eigenvalue,
        "mean_z": r * total_eigenvalue * start / (total * initial_eigenvalue),
        "population_variance": total_eigenvalue / total,
        "conditional_variance": k * (1 - correlation) * total_eigenvalue / (total * total * initial_eigenvalue),
    }


@deal.pre(lambda r, k, c, a_z: type(r) is int and 1 <= r < MATRIX_LIMIT)
@deal.pre(lambda r, k, c, a_z: type(k) is int and 1 <= k and r + k <= MATRIX_LIMIT)
@deal.pre(lambda r, k, c, a_z: type(r) is int and r >= 1 and type(k) is int and k >= 1 and isinstance(c, (int, float, fractions.Fraction)) and not isinstance(c, bool) and math.isfinite(float(c)) and fractions.Fraction(-1, r + k - 1) <= rational(c) <= 1)
@deal.pre(lambda r, k, c, a_z: isinstance(a_z, (int, float, fractions.Fraction)) and not isinstance(a_z, bool) and math.isfinite(float(a_z)) and abs(a_z) <= 1000)
@deal.post(lambda result: isinstance(result, dict) and result.keys() == MOMENT_FIELDS and all(isinstance(value, float) and math.isfinite(value) for value in result.values()))
@deal.post(lambda result: -NUMERIC_TOLERANCE <= result["population_variance"] <= 1 + NUMERIC_TOLERANCE)
@deal.post(lambda result: result["conditional_variance"] >= -NUMERIC_TOLERANCE)
@deal.post(lambda result: result["conditional_variance"] <= result["population_variance"] + NUMERIC_TOLERANCE)
@deal.ensure(lambda r, k, c, a_z, result: math.isclose(result["mean_z"], (r * float(a_z) + k * result["prediction_z"]) / (r + k), abs_tol=NUMERIC_TOLERANCE, rel_tol=NUMERIC_TOLERANCE))
@deal.ensure(lambda r, k, c, a_z, result: a_z != 0 or abs(result["mean_z"]) <= NUMERIC_TOLERANCE)
@deal.raises(ValueError, LinAlgError)
@deal.has()
def matrix_moments(r, k, c, a_z):
    """Condition a complete covariance matrix, independently of scalar formulas.

    NumPy's Moore-Penrose inverse also handles the c=1 initial block.  Its
    equal-score history is on the Gaussian support.  We retain tiny signed
    round-off residuals in the returned variance; the explicit tolerance
    documents that numerical matrix algebra is not exact rational proof.
    """
    total, correlation = r + k, float(c)
    covariance = (1 - correlation) * np.eye(total) + correlation * np.ones((total, total))
    initial = covariance[:r, :r]
    cross = covariance[r:, :r]
    future = covariance[r:, r:]
    inverse = np.linalg.pinv(initial, hermitian=True)
    future_mean = cross @ inverse @ np.full(r, float(a_z))
    conditional = future - cross @ inverse @ cross.T
    return {
        "prediction_z": float(np.mean(future_mean)),
        "mean_z": bounded_ratio(r * float(a_z) + float(future_mean.sum()), total),
        "population_variance": bounded_ratio(float(covariance.sum()), total * total),
        "conditional_variance": bounded_ratio(float(conditional.sum()), total * total),
    }


@deal.pre(lambda r, c, a_z: type(r) is int and 1 <= r <= 1000)
@deal.pre(lambda r, c, a_z: isinstance(c, (int, float, fractions.Fraction)) and not isinstance(c, bool) and math.isfinite(float(c)) and 0 <= rational(c) <= 1)
@deal.pre(lambda r, c, a_z: isinstance(a_z, (int, float, fractions.Fraction)) and not isinstance(a_z, bool) and math.isfinite(float(a_z)) and abs(a_z) <= 1000)
@deal.post(lambda result: isinstance(result, dict) and result.keys() == LIMIT_FIELDS and all(isinstance(value, fractions.Fraction) for value in result.values()))
@deal.post(lambda result: 0 <= result["population_variance_limit"] <= 1)
@deal.post(lambda result: 0 <= result["conditional_variance_limit"] <= result["population_variance_limit"])
@deal.post(lambda result: result["prediction_limit_z"] == result["mean_limit_z"])
@deal.ensure(lambda r, c, a_z, result: min(0, rational(a_z)) <= result["mean_limit_z"] <= max(0, rational(a_z)))
@deal.ensure(lambda r, c, a_z, result: c != 0 or all(value == 0 for value in result.values()))
@deal.ensure(lambda r, c, a_z, result: c != 1 or (result["mean_limit_z"] == rational(a_z) and result["conditional_variance_limit"] == 0))
@deal.raises()
@deal.has()
def limit_moments(r, c, a_z):
    """Return infinite-future limits only on the admissible nonnegative-c domain."""
    correlation, start = rational(c), rational(a_z)
    initial_eigenvalue = 1 + (r - 1) * correlation
    prediction = r * correlation * start / initial_eigenvalue
    return {
        "prediction_limit_z": prediction,
        "mean_limit_z": prediction,
        "population_variance_limit": correlation,
        "conditional_variance_limit": correlation * (1 - correlation) / initial_eigenvalue,
    }


@deal.pre(lambda path: isinstance(path, Path))
@deal.pre(lambda path: path.is_file())
@deal.post(lambda result: isinstance(result, list) and bool(result) and all(isinstance(row, dict) and all(isinstance(key, str) and isinstance(value, str) for key, value in row.items()) for row in result))
@deal.post(lambda result: all(row.keys() == result[0].keys() for row in result))
@deal.post(lambda result: all(key for key in result[0]))
@deal.raises(OSError, ValueError, csv.Error)
@deal.has("read")
def read_csv(path):
    """Read a CSV strictly, rejecting duplicate headers or mismatched row widths."""
    with path.open(newline="") as stream:
        reader = csv.DictReader(stream)
        names = reader.fieldnames or []
        require(bool(names) and all(names) and len(names) == len(set(names)), "CSV requires distinct nonempty headers")
        rows = list(reader)
    require(bool(rows), "CSV contains no records")
    require(not any(None in row or any(value is None for value in row.values()) for row in rows), "CSV row width differs from its header")
    return rows


@deal.pre(lambda row, key: isinstance(row, dict) and all(isinstance(name, str) and isinstance(value, str) for name, value in row.items()))
@deal.pre(lambda row, key: isinstance(key, str) and key in row)
@deal.post(lambda result: isinstance(result, float) and math.isfinite(result))
@deal.raises(ValueError)
@deal.has()
def finite_field(row, key):
    """Parse a numeric field without admitting NaN or infinity into comparisons."""
    value = float(row[key])
    require(math.isfinite(value), f"Nonfinite field {key}")
    return value


@deal.pre(lambda row, key: isinstance(row, dict) and all(isinstance(name, str) and isinstance(value, str) for name, value in row.items()))
@deal.pre(lambda row, key: isinstance(key, str) and key in row)
@deal.post(lambda result: type(result) is int)
@deal.raises(ValueError)
@deal.has()
def integer_field(row, key):
    """Use the standard integer parser rather than silently truncating floats."""
    return int(row[key])


@deal.pre(lambda actual, expected, label, tolerance=NUMERIC_TOLERANCE: math.isfinite(actual) and math.isfinite(expected))
@deal.pre(lambda actual, expected, label, tolerance=NUMERIC_TOLERANCE: isinstance(label, str) and bool(label))
@deal.pre(lambda actual, expected, label, tolerance=NUMERIC_TOLERANCE: math.isfinite(tolerance) and tolerance > 0)
@deal.ensure(lambda actual, expected, label, tolerance=NUMERIC_TOLERANCE, result=None: result is None and math.isclose(actual, expected, abs_tol=tolerance, rel_tol=tolerance))
@deal.raises(ValueError)
@deal.has()
def close(actual, expected, label, tolerance=NUMERIC_TOLERANCE):
    """Compare finite output to an independent reference with a declared tolerance."""
    require(math.isclose(actual, expected, abs_tol=tolerance, rel_tol=tolerance), f"{label}: {actual!r} differs from {expected!r}")
    return None


@deal.pre(lambda numerator, denominator: isinstance(numerator, (int, float)) and not isinstance(numerator, bool) and math.isfinite(numerator) and abs(numerator) <= 1e10)
@deal.pre(lambda numerator, denominator: isinstance(denominator, (int, float)) and not isinstance(denominator, bool) and math.isfinite(denominator) and 1 <= denominator <= 100_000_000)
@deal.post(lambda result: isinstance(result, float) and math.isfinite(result))
@deal.ensure(lambda numerator, denominator, result: abs(result) <= abs(numerator))
@deal.raises()
@deal.has()
def bounded_ratio(numerator, denominator):
    """Divide bounded moment quantities by positive trial counts.

    This small checked boundary states why Monte Carlo standard errors cannot
    divide by zero.  The actual arithmetic remains Python's division operator.
    """
    return numerator / denominator


@deal.pre(lambda rows: isinstance(rows, list) and bool(rows))
@deal.pre(lambda rows: all(isinstance(row, dict) and all(isinstance(key, str) and isinstance(value, str) for key, value in row.items()) for row in rows))
@deal.post(lambda result: isinstance(result, dict) and result.keys() == {"calculation_rows", "matrix_cross_checks", "limit_rows"})
@deal.post(lambda result: all(type(value) is int and value >= 0 for value in result.values()))
@deal.ensure(lambda rows, result: result["calculation_rows"] == len(rows))
@deal.ensure(lambda rows, result: result["matrix_cross_checks"] <= len(rows) and result["limit_rows"] <= len(rows))
@deal.raises(ValueError, LinAlgError)
@deal.has()
def validate_calculations(rows):
    """Check finite results, valid-domain endpoints and all reported limits."""
    seen, matrix_count, limit_count = set(), 0, 0
    for row in rows:
        require(row.keys() in (CALCULATION_COLUMNS, CALCULATION_COLUMNS | EXTRA_CALCULATION_COLUMNS), "Calculation CSV columns do not match the declared schema")
        r, k = integer_field(row, "r"), integer_field(row, "k")
        c, a_z = finite_field(row, "c"), finite_field(row, "a_z")
        require(1 <= r <= 1000 and 1 <= k <= 1_000_000 and abs(a_z) <= 1000, "Calculation counts or starting score outside reference domain")
        require(fractions.Fraction(-1, r + k - 1) <= rational(c) <= 1, "Calculation correlation does not define a PSD covariance")
        identity = (r, k, c, a_z)
        require(identity not in seen, "Duplicate calculation case")
        seen.add(identity)
        exact = exact_moments(r, k, c, a_z)
        for key in MOMENT_FIELDS:
            close(finite_field(row, key), float(exact[key]), f"calculation {identity} {key}")
        if EXTRA_CALCULATION_COLUMNS <= row.keys():
            correlation = rational(c)
            initial_eigenvalue = 1 + (r - 1) * correlation
            has_inverse = r == 1 or correlation < 1
            # A singular starting block has explicit zero placeholders, not
            # a fabricated inverse.  NumPy's pseudoinverse remains separate.
            diagonal, off_diagonal = fractions.Fraction(0), fractions.Fraction(0)
            if r == 1:
                diagonal = fractions.Fraction(1)
            elif has_inverse:
                diagonal = (initial_eigenvalue - correlation) / ((1 - correlation) * initial_eigenvalue)
                off_diagonal = -correlation / ((1 - correlation) * initial_eigenvalue)
            extras = {
                "prediction_iq": float(100 + 15 * exact["prediction_z"]),
                "mean_iq": float(100 + 15 * exact["mean_z"]),
                "population_sd_iq": 15 * math.sqrt(float(exact["population_variance"])),
                "conditional_sd_iq": 15 * math.sqrt(float(exact["conditional_variance"])),
                "regression_coefficient": float(correlation / initial_eigenvalue),
                "residual_variance": float((1 - correlation) * (1 + r * correlation) / initial_eigenvalue),
                "common_eigenvalue": float(1 + (r + k - 1) * correlation),
                "contrast_eigenvalue": float(1 - correlation),
                "inverse_diagonal": float(diagonal),
                "inverse_off_diagonal": float(off_diagonal),
            }
            require(row["has_inverse"].strip().lower() == str(has_inverse).lower(), "Starting-block invertibility flag differs")
            for key, expected in extras.items():
                close(finite_field(row, key), expected, f"extra calculation {identity} {key}")
        if r + k <= MATRIX_LIMIT:
            matrix = matrix_moments(r, k, c, a_z)
            for key in MOMENT_FIELDS:
                close(matrix[key], float(exact[key]), f"matrix {identity} {key}")
            matrix_count += 1
        if c >= 0:
            limits = limit_moments(r, c, a_z)
            for key in LIMIT_FIELDS:
                close(finite_field(row, key), float(limits[key]), f"limit {identity} {key}")
            limit_count += 1
        else:
            require(all(row[key].strip() == "" for key in LIMIT_FIELDS), "Negative-c finite cases cannot claim an infinite-future extension")
    return {"calculation_rows": len(rows), "matrix_cross_checks": matrix_count, "limit_rows": limit_count}


@deal.pre(lambda rows: isinstance(rows, list) and bool(rows))
@deal.pre(lambda rows: all(isinstance(row, dict) and all(isinstance(key, str) and isinstance(value, str) for key, value in row.items()) for row in rows))
@deal.post(lambda result: isinstance(result, dict) and result.keys() == {"simulation_rows", "minimum_trials", "maximum_mean_standard_errors"})
@deal.post(lambda result: type(result["simulation_rows"]) is int and result["simulation_rows"] > 0)
@deal.post(lambda result: type(result["minimum_trials"]) is int and result["minimum_trials"] >= 2)
@deal.post(lambda result: math.isfinite(result["maximum_mean_standard_errors"]) and result["maximum_mean_standard_errors"] >= 0)
@deal.ensure(lambda rows, result: result["simulation_rows"] == len(rows))
@deal.raises(ValueError)
@deal.has()
def validate_simulations(rows):
    """Check sample moments against normal and chi-square sampling laws.

    The output variance must use the unbiased n-1 denominator.  Neither a
    successful Monte Carlo diagnostic nor the PRNG contracts prove independent
    Gaussian draws; this check is deliberately reported separately from SPARK.
    """
    seen, minimum_trials, maximum_error = set(), 100_000_000, 0.0
    for row in rows:
        require(SIMULATION_COLUMNS <= row.keys(), "Missing simulation CSV columns")
        mode = row["mode"].strip()
        require(mode in MODES, "Unknown simulation mode")
        r, k = integer_field(row, "r"), integer_field(row, "k")
        c, a_z = finite_field(row, "c"), finite_field(row, "a_z")
        trials, seed = integer_field(row, "trials"), integer_field(row, "seed")
        require(1 <= r <= 1000 and abs(a_z) <= 1000, "Simulation starting block outside reference domain")
        require(2 <= trials <= 100_000_000 and 0 <= seed < 2 ** 64, "Simulation trial count or seed outside domain")
        identity = (mode, r, k, c, a_z)
        require(identity not in seen, "Duplicate simulation case")
        seen.add(identity)
        if mode.endswith("_limit"):
            require(k == 0 and 0 <= c <= 1, "Limit simulations require k=0 sentinel and nonnegative correlation")
            reference = limit_moments(r, c, a_z)
            expected_mean = 0.0 if mode == "population_limit" else float(reference["mean_limit_z"])
            expected_variance = float(reference["population_variance_limit"] if mode == "population_limit" else reference["conditional_variance_limit"])
        else:
            require(1 <= k <= 1_000_000 and fractions.Fraction(-1, r + k - 1) <= rational(c) <= 1, "Finite simulation does not have an admissible covariance")
            reference = exact_moments(r, k, c, a_z)
            expected_mean = 0.0 if mode == "population" else float(reference["mean_z"])
            expected_variance = float(reference["population_variance"] if mode == "population" else reference["conditional_variance"])
        observed_mean = finite_field(row, "sample_mean_z")
        observed_variance = finite_field(row, "sample_variance_z")
        require(observed_variance >= 0, "Sample variance must be nonnegative")
        minimum_trials = min(minimum_trials, trials)
        if expected_variance == 0:
            close(observed_mean, expected_mean, f"degenerate mean {identity}", 1e-8)
            close(observed_variance, 0.0, f"degenerate variance {identity}", 1e-8)
        else:
            standard_error = math.sqrt(bounded_ratio(expected_variance, trials))
            mean_error = abs(observed_mean - expected_mean) / standard_error
            maximum_error = max(maximum_error, mean_error)
            require(mean_error <= float(norm.isf(MOMENT_TAIL * 0.5)) + 1e-7, f"Monte Carlo mean outside normal diagnostic for {identity}")
            degrees = trials - 1
            lower = bounded_ratio(expected_variance * float(chi2.ppf(MOMENT_TAIL * 0.5, degrees)), degrees)
            upper = bounded_ratio(expected_variance * float(chi2.isf(MOMENT_TAIL * 0.5, degrees)), degrees)
            require(lower - 1e-10 <= observed_variance <= upper + 1e-10, f"Monte Carlo variance outside chi-square diagnostic for {identity}")
    return {"simulation_rows": len(rows), "minimum_trials": minimum_trials, "maximum_mean_standard_errors": maximum_error}


@deal.pre(lambda rows: isinstance(rows, list) and bool(rows))
@deal.pre(lambda rows: all(isinstance(row, dict) and all(isinstance(key, str) and isinstance(value, str) for key, value in row.items()) for row in rows))
@deal.post(lambda result: isinstance(result, dict) and result.keys() == {"identity_checks", "maximum_absolute_error"})
@deal.post(lambda result: type(result["identity_checks"]) is int and result["identity_checks"] == len(CHECK_REFERENCES))
@deal.post(lambda result: math.isfinite(result["maximum_absolute_error"]) and 0 <= result["maximum_absolute_error"] <= 1e-8)
@deal.ensure(lambda rows, result: result["identity_checks"] == len(rows))
@deal.raises(ValueError)
@deal.has()
def validate_checks(rows):
    """Bind algebraic residuals and counterexample diagnostics to fixed answers.

    Recursion, inverse and eigenvector records are maximum absolute residuals,
    rather than eigenvalues without a declared matrix dimension.  Their target
    is zero.  The finite-PMF values are evaluated independently below as well.
    A tolerance larger than 1e-8 would erase the intended numerical guarantee.
    """
    seen, maximum_error = set(), 0.0
    for row in rows:
        require(row.keys() == {"name", "actual", "expected", "tolerance"}, "Identity-check CSV columns differ from their schema")
        name = row["name"].strip()
        require(name in CHECK_REFERENCES and name not in seen, "Unknown or duplicate identity-check name")
        seen.add(name)
        actual = finite_field(row, "actual")
        expected = finite_field(row, "expected")
        tolerance = finite_field(row, "tolerance")
        require(0 < tolerance <= 1e-8, "Identity-check tolerance is outside the declared accuracy bound")
        require(abs(expected - CHECK_REFERENCES[name]) <= NUMERIC_TOLERANCE, f"Identity-check {name} changed its fixed expected value")
        error = abs(actual - CHECK_REFERENCES[name])
        require(error <= tolerance, f"Identity-check {name} exceeds its absolute tolerance")
        if name.startswith(("prediction_recursion_", "covariance_eigen_", "inverse_identity_")) or name in {"total_variance_decomposition", "conditional_growth_identity"}:
            require(actual >= 0, "A maximum absolute residual cannot be negative")
        maximum_error = max(maximum_error, error)
    require(seen == CHECK_REFERENCES.keys(), "Required identity or counterexample checks are absent")
    return {"identity_checks": len(rows), "maximum_absolute_error": maximum_error}


@deal.pre(lambda value, rounded, scale, square_root=False: isinstance(value, fractions.Fraction) and value >= 0)
@deal.pre(lambda value, rounded, scale, square_root=False: isinstance(rounded, fractions.Fraction) and rounded > 0)
@deal.pre(lambda value, rounded, scale, square_root=False: type(scale) is int and scale in (100, 1_000_000))
@deal.pre(lambda value, rounded, scale, square_root=False: isinstance(rounded, fractions.Fraction) and type(scale) is int and (rounded * scale).denominator == 1)
@deal.pre(lambda value, rounded, scale, square_root=False: type(square_root) is bool)
@deal.post(lambda result: isinstance(result, tuple) and all(type(number) is int for number in result))
@deal.post(lambda result: all(number > 0 for number in result))
@deal.ensure(lambda value, rounded, scale, square_root=False, result=None: len(result) == (2 if square_root else 1))
@deal.ensure(lambda value, rounded, scale, square_root=False, result=None: square_root or result[0] == value.denominator - 2 * abs(scale * value.numerator - int(rounded * scale) * value.denominator))
@deal.raises(ValueError)
@deal.has()
def rounding_certificate(value, rounded, scale, square_root=False):
    """Evaluate the paper's strict integer nearest-grid certificates exactly.

    Fractions expose reduced integer numerators and positive denominators, so
    these checks use no binary floating point or approximate square roots.
    Failure means that the requested rounded value is not certified uniquely.
    """
    numerator, denominator = value.numerator, value.denominator
    grid_integer = int(rounded * scale)
    if square_root:
        certificates = (4 * scale * scale * numerator - (2 * grid_integer - 1) ** 2 * denominator,
                        (2 * grid_integer + 1) ** 2 * denominator - 4 * scale * scale * numerator)
    else:
        certificates = (denominator - 2 * abs(scale * numerator - grid_integer * denominator),)
    require(all(number > 0 for number in certificates), "Printed decimal does not have strict positive rounding certificates")
    return certificates


@deal.post(lambda result: isinstance(result, dict) and result.keys() == {"iq_rows", "matrix_cases", "counterexample_checked", "rounding_entries", "certificate_integers", "standardized_rows", "limit_rows"})
@deal.post(lambda result: result["iq_rows"] == 9 and result["matrix_cases"] >= 9)
@deal.post(lambda result: result["counterexample_checked"] is True)
@deal.post(lambda result: result["rounding_entries"] == 27)
@deal.post(lambda result: result["certificate_integers"] == 74)
@deal.post(lambda result: result["standardized_rows"] == 3 and result["limit_rows"] == 3)
@deal.raises(ValueError, LinAlgError)
@deal.has()
def paper_self_check():
    """Recheck the paper's nine rational certificates and its counterexample.

    The stored fractions are independent reference data from the paper's exact
    certificate table.  NumPy's block conditioning is checked in addition to
    scalar algebra, and the rounding test uses exact squares rather than a
    floating square root as its oracle.
    """
    cases = [
        (1, 1, fractions.Fraction(140), fractions.Fraction(180), fractions.Fraction(36), "140.00", "13.42", "6.00"),
        (1, 2, fractions.Fraction(410, 3), fractions.Fraction(165), fractions.Fraction(44), "136.67", "12.85", "6.63"),
        (1, 10, fractions.Fraction(1450, 11), fractions.Fraction(1575, 11), fractions.Fraction(6300, 121), "131.82", "11.97", "7.22"),
        (2, 1, fractions.Fraction(875, 6), fractions.Fraction(165), fractions.Fraction(55, 4), "145.83", "12.85", "3.71"),
        (2, 2, fractions.Fraction(575, 4), fractions.Fraction(315, 2), fractions.Fraction(315, 16), "143.75", "12.55", "4.44"),
        (2, 10, fractions.Fraction(1675, 12), fractions.Fraction(285, 2), fractions.Fraction(475, 16), "139.58", "11.94", "5.45"),
        (3, 1, fractions.Fraction(1625, 11), fractions.Fraction(315, 2), fractions.Fraction(315, 44), "147.73", "12.55", "2.68"),
        (3, 2, fractions.Fraction(1610, 11), fractions.Fraction(153), fractions.Fraction(612, 55), "146.36", "12.37", "3.34"),
        (3, 10, fractions.Fraction(20450, 143), fractions.Fraction(1845, 13), fractions.Fraction(36900, 1859), "143.01", "11.91", "4.46"),
    ]
    # Independent transcriptions of all printed integer certificate columns.
    # Checking only their positivity could miss a mistyped integer in the PDF.
    iq_certificates = [(1, 1511, 9225, 2399, 2401), (1, 239, 10041, 4375, 929),
                       (7, 9061, 96275, 47871, 651025), (2, 239, 10041, 3676, 8196),
                       (4, 9838, 10242, 11696, 45136), (4, 4462, 14642, 25264, 44496),
                       (5, 9838, 10242, 6100, 88236), (3, 4271, 5625, 11105, 135855),
                       (57, 100907, 22957, 175221, 6457691)]
    for case, expected_certificates in zip(cases, iq_certificates, strict=True):
        r, k, expected_mean, population_variance, conditional_variance, rounded_mean, rounded_population, rounded_conditional = case
        exact = exact_moments(r, k, fractions.Fraction(3, 5), fractions.Fraction(10, 3))
        require(100 + 15 * exact["mean_z"] == expected_mean, "Exact IQ mean certificate differs")
        require(225 * exact["population_variance"] == population_variance, "Exact population variance certificate differs")
        require(225 * exact["conditional_variance"] == conditional_variance, "Exact conditional variance certificate differs")
        require(abs(expected_mean - fractions.Fraction(rounded_mean)) < fractions.Fraction(1, 200), "IQ mean rounding is not certified")
        for variance, rounded in ((population_variance, rounded_population), (conditional_variance, rounded_conditional)):
            candidate = fractions.Fraction(rounded)
            require((candidate - fractions.Fraction(1, 200)) ** 2 < variance < (candidate + fractions.Fraction(1, 200)) ** 2, "IQ SD rounding is not certified")
        certificates = (rounding_certificate(expected_mean, fractions.Fraction(rounded_mean), 100)
                        + rounding_certificate(population_variance, fractions.Fraction(rounded_population), 100, True)
                        + rounding_certificate(conditional_variance, fractions.Fraction(rounded_conditional), 100, True))
        require(certificates == expected_certificates, "Printed IQ integer certificates differ")
        matrix = matrix_moments(r, k, fractions.Fraction(3, 5), fractions.Fraction(10, 3))
        for key in MOMENT_FIELDS:
            close(matrix[key], float(exact[key]), f"paper matrix {r},{k} {key}")
    standardized_cases = [(1, fractions.Fraction(6, 5), fractions.Fraction(7, 5), fractions.Fraction(7, 10), fractions.Fraction(21, 100)),
                          (2, fractions.Fraction(3, 2), fractions.Fraction(17, 10), fractions.Fraction(17, 25), fractions.Fraction(51, 500)),
                          (3, fractions.Fraction(18, 11), fractions.Fraction(20, 11), fractions.Fraction(2, 3), fractions.Fraction(2, 33))]
    for r, prediction, mean, population_variance, conditional_variance in standardized_cases:
        exact, matrix = exact_moments(r, 3, fractions.Fraction(3, 5), 2), matrix_moments(r, 3, fractions.Fraction(3, 5), 2)
        require(exact == dict(zip(("prediction_z", "mean_z", "population_variance", "conditional_variance"),
                                 (prediction, mean, population_variance, conditional_variance), strict=True)), "Standardized worked example differs")
        for key in MOMENT_FIELDS:
            close(matrix[key], float(exact[key]), f"standardized matrix {r} {key}")
    mean_certificates = [(fractions.Fraction(18, 11), "1.636364", 1_000_000, 3),
                         (fractions.Fraction(20, 11), "1.818182", 1_000_000, 7),
                         (fractions.Fraction(1550, 11), "140.909091", 1_000_000, 9),
                         (fractions.Fraction(1550, 11), "140.91", 100, 9),
                         (fractions.Fraction(1675, 12), "139.583333", 1_000_000, 4)]
    for value, rounded, scale, expected in mean_certificates:
        require(rounding_certificate(value, fractions.Fraction(rounded), scale) == (expected,), "Printed additional mean certificate differs")
    sd_certificates = [(fractions.Fraction(7, 10), "0.836660", 35242390, 31690410),
                       (fractions.Fraction(21, 100), "0.458258", 25477500, 341128900),
                       (fractions.Fraction(17, 25), "0.824621", 103097975, 61826225),
                       (fractions.Fraction(51, 500), "0.319374", 1134995500, 142500500),
                       (fractions.Fraction(2, 3), "0.816497", 1585853, 18010075),
                       (fractions.Fraction(2, 33), "0.246183", 31323575, 33668737),
                       (fractions.Fraction(285, 2), "11.937336", 169283518, 21713858),
                       (fractions.Fraction(475, 16), "5.448624", 125135856, 572288016),
                       (fractions.Fraction(135), "11.618950", 50065799, 42885801),
                       (fractions.Fraction(54), "7.348469", 42818031, 15969721),
                       (fractions.Fraction(135, 4), "5.809475", 96541596, 89361604),
                       (fractions.Fraction(270, 11), "4.954337", 193169781, 242811875)]
    for variance, rounded, lower, upper in sd_certificates:
        require(rounding_certificate(variance, fractions.Fraction(rounded), 1_000_000, True) == (lower, upper), "Printed additional SD certificates differ")
    for r, expected_mean, expected_variance, rounded_mean in [(1, fractions.Fraction(130), fractions.Fraction(54), "130.000000"),
                                                           (2, fractions.Fraction(275, 2), fractions.Fraction(135, 4), "137.500000"),
                                                           (3, fractions.Fraction(1550, 11), fractions.Fraction(270, 11), "140.909091")]:
        limits = limit_moments(r, fractions.Fraction(3, 5), fractions.Fraction(10, 3))
        require(100 + 15 * limits["mean_limit_z"] == expected_mean, "IQ limit mean differs")
        require(225 * limits["population_variance_limit"] == 135, "IQ population limit variance differs")
        require(225 * limits["conditional_variance_limit"] == expected_variance, "IQ conditional limit variance differs")
        require(abs(expected_mean - fractions.Fraction(rounded_mean)) < fractions.Fraction(1, 2_000_000), "IQ limit mean rounding differs")
    for r in (1, 2, 3):
        correlation = fractions.Fraction(3, 5)
        initial_eigenvalue = 1 + (r - 1) * correlation
        for k in (1, 2, 10):
            total = r + k
            finite, following = exact_moments(r, k, correlation, 2), exact_moments(r, k + 1, correlation, 2)
            total_eigenvalue = 1 + (total - 1) * correlation
            centre_variance = fractions.Fraction(r) * total_eigenvalue ** 2 / (total ** 2 * initial_eigenvalue)
            require(finite["population_variance"] == centre_variance + finite["conditional_variance"], "Total-variance decomposition differs")
            if (r, k) == (2, 10):
                require(225 * centre_variance == fractions.Fraction(1805, 16) and 225 * finite["population_variance"] == fractions.Fraction(285, 2)
                        and 225 * finite["conditional_variance"] == fractions.Fraction(475, 16), "Worked IQ variance decomposition differs")
            polynomial = ((2 * correlation * r - initial_eigenvalue) * k * k
                          + (2 * correlation * r * r + 2 * correlation * r - initial_eigenvalue) * k
                          + r * r * (correlation + initial_eigenvalue))
            difference = (1 - correlation) * polynomial / (initial_eigenvalue * total ** 2 * (total + 1) ** 2)
            require(following["conditional_variance"] - finite["conditional_variance"] == difference and difference > 0,
                    "Conditional-variance finite-difference polynomial differs")
            require(following["population_variance"] - finite["population_variance"] == fractions.Fraction(-(1 - correlation), total * (total + 1)),
                    "Population-variance finite difference differs")
    # Boundary cases challenge singular full covariances and an initial block
    # of rank one, rather than merely repeating the illustrative c=0.6 grid.
    edges = [(1, 1, fractions.Fraction(-1)), (2, 1, fractions.Fraction(-1, 2)), (3, 1, fractions.Fraction(-1, 3)), (2, 2, fractions.Fraction(0)), (3, 2, fractions.Fraction(1))]
    for r, k, c in edges:
        exact, matrix = exact_moments(r, k, c, 2), matrix_moments(r, k, c, 2)
        for key in MOMENT_FIELDS:
            close(matrix[key], float(exact[key]), f"boundary matrix {r},{k},{c} {key}")
    # The three-atom example has standardized marginals and zero covariance,
    # but conditioning the second coordinate on the first being zero gives -1.
    support = np.asarray([-math.sqrt(2), 0.0, math.sqrt(2)])
    weights = np.asarray([0.25, 0.5, 0.25])
    second = support * support - 1
    close(float(weights @ support), 0.0, "counterexample first mean")
    close(float(weights @ second), 0.0, "counterexample second mean")
    close(float(weights @ (support * support)), 1.0, "counterexample first variance")
    close(float(weights @ (second * second)), 1.0, "counterexample second variance")
    close(float(weights @ (support * second)), 0.0, "counterexample covariance")
    require(bool(second[1] == -1 and weights[1] == 0.5), "Counterexample positive-probability conditional value differs")
    return {"iq_rows": 9, "matrix_cases": len(cases) + len(edges) + len(standardized_cases), "counterexample_checked": True,
            "rounding_entries": 27, "certificate_integers": 74, "standardized_rows": 3, "limit_rows": 3}


@deal.pre(lambda directory, calculations=None, simulation=None, checks=None: isinstance(directory, Path) and directory.is_dir())
@deal.pre(lambda directory, calculations=None, simulation=None, checks=None: calculations is None or isinstance(calculations, Path))
@deal.pre(lambda directory, calculations=None, simulation=None, checks=None: simulation is None or isinstance(simulation, Path))
@deal.pre(lambda directory, calculations=None, simulation=None, checks=None: checks is None or isinstance(checks, Path))
@deal.post(lambda result: isinstance(result, dict) and result.keys() == {"paper", "calculations", "simulations", "checks", "complete"})
@deal.post(lambda result: result["complete"] is True)
@deal.raises(OSError, ValueError, csv.Error, LinAlgError)
@deal.has("read")
def validate(directory, calculations=None, simulation=None, checks=None):
    """Validate results and require coverage of every illustrative paper case.

    Low-level validators support small test fixtures.  This orchestration gate
    additionally insists on the entire nine-case IQ grid, its eighteen finite
    sampling experiments, and all six limit experiments.  Extra admissible
    edge cases may supplement that minimum coverage.
    """
    calculation_path = calculations if calculations is not None else directory.joinpath("calculation.csv")
    simulation_path = simulation if simulation is not None else directory.joinpath("simulation.csv")
    check_path = checks if checks is not None else directory.joinpath("checks.csv")
    require(calculation_path.is_file() and simulation_path.is_file() and check_path.is_file(), "Required Ada CSV output is missing")
    # Normalize optional CLI paths at the I/O boundary; all downstream readers
    # receive concrete standard-library Path values, never parser sentinels.
    calculation_rows, simulation_rows = read_csv(Path(calculation_path)), read_csv(Path(simulation_path))
    calculations_report = validate_calculations(calculation_rows)
    simulations_report = validate_simulations(simulation_rows)
    calculation_cases = {(int(row["r"]), int(row["k"])) for row in calculation_rows
                         if math.isclose(float(row["c"]), 0.6, abs_tol=NUMERIC_TOLERANCE)
                         and math.isclose(float(row["a_z"]), float(fractions.Fraction(10, 3)), abs_tol=NUMERIC_TOLERANCE)}
    required_cases = {(r, k) for r in (1, 2, 3) for k in (1, 2, 10)}
    require(required_cases <= calculation_cases, "Calculation output omits a required IQ example")
    simulation_cases = {(row["mode"].strip(), int(row["r"]), int(row["k"])) for row in simulation_rows
                        if math.isclose(float(row["c"]), 0.6, abs_tol=NUMERIC_TOLERANCE)
                        and math.isclose(float(row["a_z"]), float(fractions.Fraction(10, 3)), abs_tol=NUMERIC_TOLERANCE)}
    required_simulations = {(mode, r, k) for mode in ("population", "conditional") for r, k in required_cases}
    required_simulations |= {(mode, r, 0) for mode in ("population_limit", "conditional_limit") for r in (1, 2, 3)}
    require(required_simulations <= simulation_cases, "Simulation output omits a required finite or limit example")
    return {
        "paper": paper_self_check(),
        "calculations": calculations_report,
        "simulations": simulations_report,
        "checks": validate_checks(read_csv(Path(check_path))),
        "complete": True,
    }


@deal.pre(lambda argv=None: argv is None or (isinstance(argv, list) and all(isinstance(arg, str) for arg in argv)))
@deal.pre(lambda argv=None: argv is None or all("\x00" not in arg for arg in argv))
@deal.pre(lambda argv=None: ROOT.is_dir())
@deal.post(lambda result: result == 0)
@deal.raises(OSError, ValueError, csv.Error, LinAlgError, SystemExit)
@deal.has("read", "write", "stdout", "stderr")
def main(argv=None):
    """CLI orchestration delegates mathematics, CSV parsing and statistics to libraries."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("directory", nargs="?", type=Path, default=ROOT.joinpath("ada", "results"))
    parser.add_argument("--calculations", type=Path)
    parser.add_argument("--simulation", type=Path)
    parser.add_argument("--checks", type=Path)
    parser.add_argument("--json-output", type=Path)
    args = parser.parse_args(argv)
    report = validate(args.directory, args.calculations, args.simulation, args.checks)
    serialized = json.dumps(report, indent=2) + "\n"
    if args.json_output is not None:
        args.json_output.write_text(serialized)
    print(serialized, end="")
    return 0


if __name__ == "__main__":
    deal.enable(warn=False)
    raise SystemExit(main())
