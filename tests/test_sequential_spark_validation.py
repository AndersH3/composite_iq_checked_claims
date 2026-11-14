"""Independent matrix checks and rejection tests for the sequential CSV gate.

The tests challenge PSD boundaries, deliberately corrupted numerical output,
missing experiment coverage and sampling diagnostics.  Their scratch output is
separate from the repository's immutable scientific evidence and published PDF.
"""
import copy
import csv
from fractions import Fraction
import json
import math
from pathlib import Path

import deal
import numpy as np
import pytest

from conftest import load_script, protected_history_intact, reference_inputs_intact


VALIDATOR = load_script("sequential_spark_validator", "analyses/sequential-conditional-means/scripts/validate_spark.py")


@pytest.fixture
@deal.pre(lambda: protected_history_intact())
@deal.post(lambda result: isinstance(result, tuple) and len(result) == 3)
@deal.post(lambda result: len(result[0]) == 9 and len(result[1]) == 24 and len(result[2]) == 18)
@deal.post(lambda result: all(isinstance(row, dict) and all(isinstance(value, str) for value in row.values()) for rows in result for row in rows))
@deal.ensure(lambda *, result: protected_history_intact())
@deal.ensure(lambda *, result: reference_inputs_intact())
@deal.has("read")
def result_rows():
    """Construct complete ideal-moment fixtures for mutation and CLI tests.

    Ideal moments intentionally avoid random test failures in tests of CSV
    plumbing.  A separate test below uses actual independent NumPy draws.
    """
    calculations, simulations = [], []
    for r in (1, 2, 3):
        for k in (1, 2, 10):
            reference = VALIDATOR.exact_moments(r, k, Fraction(3, 5), Fraction(10, 3))
            limits = VALIDATOR.limit_moments(r, Fraction(3, 5), Fraction(10, 3))
            row = {"r": str(r), "k": str(k), "c": "0.6", "a_z": str(float(Fraction(10, 3)))}
            row.update({key: str(float(value)) for key, value in (reference | limits).items()})
            calculations.append(row)
            for mode in ("population", "conditional"):
                mean = 0.0 if mode == "population" else float(reference["mean_z"])
                variance = float(reference[mode + "_variance"])
                simulations.append({"mode": mode, "r": str(r), "k": str(k), "c": "0.6", "a_z": str(float(Fraction(10, 3))),
                                    "trials": "100000", "seed": "8317", "sample_mean_z": str(mean), "sample_variance_z": str(variance)})
        for mode in ("population_limit", "conditional_limit"):
            mean = 0.0 if mode == "population_limit" else float(limits["mean_limit_z"])
            variance = float(limits[mode.replace("_limit", "_variance_limit")])
            simulations.append({"mode": mode, "r": str(r), "k": "0", "c": "0.6", "a_z": str(float(Fraction(10, 3))),
                                "trials": "100000", "seed": "8317", "sample_mean_z": str(mean), "sample_variance_z": str(variance)})
    checks = [{"name": name, "actual": str(expected), "expected": str(expected), "tolerance": "1e-10"}
              for name, expected in VALIDATOR.CHECK_REFERENCES.items()]
    return calculations, simulations, checks


@pytest.fixture
@deal.pre(lambda tmp_path, result_rows: isinstance(tmp_path, Path) and tmp_path.is_dir())
@deal.pre(lambda tmp_path, result_rows: isinstance(result_rows, tuple) and len(result_rows) == 3 and all(rows for rows in result_rows))
@deal.ensure(lambda tmp_path, result_rows, result: result == tmp_path)
@deal.post(lambda result: all(result.joinpath(name).is_file() for name in ("calculation.csv", "simulation.csv", "checks.csv")))
@deal.ensure(lambda tmp_path, result_rows, result: protected_history_intact())
@deal.ensure(lambda tmp_path, result_rows, result: reference_inputs_intact())
@deal.raises(OSError)
@deal.has("read", "write")
def result_directory(tmp_path, result_rows):
    """Serialize test fixtures through Python's standard CSV library."""
    for name, rows in zip(("calculation.csv", "simulation.csv", "checks.csv"), result_rows, strict=True):
        with tmp_path.joinpath(name).open("w", newline="") as stream:
            writer = csv.DictWriter(stream, fieldnames=list(rows[0]))
            writer.writeheader()
            writer.writerows(rows)
    return tmp_path


@pytest.mark.parametrize("r,k,c", [(1, 1, -1), (2, 1, Fraction(-1, 2)), (3, 1, Fraction(-1, 3)), (2, 2, Fraction(-1, 4)), (1, 10, 0), (3, 10, Fraction(3, 5)), (3, 2, 1)])
@deal.pre(lambda r, k, c: protected_history_intact())
@deal.pre(lambda r, k, c: type(r) is int and r > 0 and type(k) is int and k > 0 and Fraction(-1, r + k - 1) <= c <= 1)
@deal.ensure(lambda r, k, c, result: protected_history_intact())
@deal.ensure(lambda r, k, c, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has("read")
def test_exact_moments_match_full_matrix_conditioning(r, k, c):
    """Challenge the formulas with singular matrices and negative correlations."""
    exact = VALIDATOR.exact_moments(r, k, c, Fraction(10, 3))
    matrix = VALIDATOR.matrix_moments(r, k, c, Fraction(10, 3))
    for key in VALIDATOR.MOMENT_FIELDS:
        assert math.isclose(matrix[key], float(exact[key]), abs_tol=2e-10, rel_tol=2e-10)
    if c == Fraction(-1, r + k - 1):
        assert exact["population_variance"] == exact["conditional_variance"] == 0
    if c == 1:
        assert exact["prediction_z"] == Fraction(10, 3)
        assert exact["conditional_variance"] == 0


@pytest.mark.parametrize("arguments", [(0, 1, 0.6, 1), (True, 1, 0.6, 1), (1, 0, 0.6, 1), (2, 2, -0.5, 1), (1, 1, float("nan"), 1), (1, 1, 0.6, float("inf"))])
@deal.pre(lambda arguments: protected_history_intact())
@deal.pre(lambda arguments: isinstance(arguments, tuple) and len(arguments) == 4)
@deal.ensure(lambda arguments, result: protected_history_intact())
@deal.ensure(lambda arguments, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has("read")
def test_invalid_mathematical_domains_trigger_contracts(arguments):
    """The contracts reject invalid domains before any division or matrix call."""
    with pytest.raises(deal.PreContractError):
        VALIDATOR.exact_moments(*arguments)


@pytest.mark.parametrize("r,c", [(1, 0), (2, Fraction(3, 5)), (3, 1)])
@deal.pre(lambda r, c: protected_history_intact())
@deal.pre(lambda r, c: type(r) is int and 1 <= r <= 3 and 0 <= c <= 1)
@deal.ensure(lambda r, c, result: protected_history_intact())
@deal.ensure(lambda r, c, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has("read")
def test_limit_and_finite_correction_identity(r, c):
    """An exact 1/(r+k) correction checks the limiting mean independently."""
    start, k = Fraction(10, 3), 100000
    finite = VALIDATOR.exact_moments(r, k, c, start)
    limits = VALIDATOR.limit_moments(r, c, start)
    correction = Fraction(r, r + k) * (start - limits["mean_limit_z"])
    assert finite["mean_z"] - limits["mean_limit_z"] == correction
    assert abs(finite["population_variance"] - limits["population_variance_limit"]) <= Fraction(1, r + k)
    assert abs(finite["conditional_variance"] - limits["conditional_variance_limit"]) < Fraction(1, 10000)
    with pytest.raises(deal.PreContractError):
        VALIDATOR.limit_moments(r, Fraction(-1, 100), start)


@pytest.mark.parametrize("field,value", [("mean_z", "99"), ("conditional_variance", "-0.1"), ("population_variance", "nan"), ("prediction_limit_z", "0"), ("c", "-1"), ("k", "0"), ("r", "1.5")])
@deal.pre(lambda result_rows, field, value: protected_history_intact())
@deal.pre(lambda result_rows, field, value: isinstance(field, str) and isinstance(value, str))
@deal.ensure(lambda result_rows, field, value, result: protected_history_intact())
@deal.ensure(lambda result_rows, field, value, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has("read")
def test_corrupted_calculations_are_rejected(result_rows, field, value):
    """Reject incorrect results, nonfinite data and invalid CSV parameter fields."""
    damaged = copy.deepcopy(result_rows[0])
    damaged[0][field] = value
    with pytest.raises(ValueError):
        VALIDATOR.validate_calculations(damaged)


@deal.pre(lambda result_rows: protected_history_intact())
@deal.ensure(lambda result_rows, result: protected_history_intact())
@deal.ensure(lambda result_rows, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has("read")
def test_negative_finite_case_cannot_claim_infinite_extension(result_rows):
    """A valid finite negative-c battery must leave all limit fields empty."""
    row = dict(result_rows[0][0])
    row.update({"c": "-0.5", **{key: str(float(value)) for key, value in VALIDATOR.exact_moments(1, 1, -0.5, float(row["a_z"])).items()}})
    for key in VALIDATOR.LIMIT_FIELDS:
        row[key] = ""
    assert VALIDATOR.validate_calculations([row])["limit_rows"] == 0
    row["mean_limit_z"] = "0"
    with pytest.raises(ValueError, match="infinite-future"):
        VALIDATOR.validate_calculations([row])


@deal.pre(lambda result_rows: protected_history_intact())
@deal.ensure(lambda result_rows, result: protected_history_intact())
@deal.ensure(lambda result_rows, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has("read", "random")
def test_actual_normal_samples_pass_all_four_sampling_modes(result_rows):
    """Use NumPy's independent generator and unbiased empirical variances."""
    selected = [dict(row) for row in result_rows[1] if row["r"] == "2" and row["k"] in ("2", "0")]
    generator = np.random.default_rng(918071)
    for row in selected:
        samples = generator.normal(float(row["sample_mean_z"]), math.sqrt(float(row["sample_variance_z"])), int(row["trials"]))
        row["sample_mean_z"] = str(float(samples.mean()))
        row["sample_variance_z"] = str(float(samples.var(ddof=1)))
    report = VALIDATOR.validate_simulations(selected)
    assert report["simulation_rows"] == 4
    assert report["maximum_mean_standard_errors"] < 6


@pytest.mark.parametrize("field,value", [("sample_mean_z", "5"), ("sample_variance_z", "0.01"), ("sample_variance_z", "-1"), ("mode", "unknown"), ("trials", "1"), ("seed", "-1"), ("sample_mean_z", "inf")])
@deal.pre(lambda result_rows, field, value: protected_history_intact())
@deal.pre(lambda result_rows, field, value: isinstance(field, str) and isinstance(value, str))
@deal.ensure(lambda result_rows, field, value, result: protected_history_intact())
@deal.ensure(lambda result_rows, field, value, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has("read")
def test_biased_or_invalid_simulations_are_rejected(result_rows, field, value):
    """A CSV with plausible syntax can still fail the statistical diagnostics."""
    damaged = [dict(result_rows[1][0])]
    damaged[0][field] = value
    with pytest.raises(ValueError):
        VALIDATOR.validate_simulations(damaged)


@deal.pre(lambda result_rows: protected_history_intact())
@deal.ensure(lambda result_rows, result: protected_history_intact())
@deal.ensure(lambda result_rows, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has("read")
def test_degenerate_simulation_and_duplicate_records(result_rows):
    """At c=1 conditioning fixes every score, so the sample variance is zero."""
    row = dict(result_rows[1][1])
    row.update({"c": "1", "sample_mean_z": row["a_z"], "sample_variance_z": "0"})
    assert VALIDATOR.validate_simulations([row])["simulation_rows"] == 1
    row["sample_variance_z"] = "0.001"
    with pytest.raises(ValueError):
        VALIDATOR.validate_simulations([row])
    with pytest.raises(ValueError, match="Duplicate"):
        VALIDATOR.validate_calculations(result_rows[0] + [result_rows[0][0]])
    with pytest.raises(ValueError, match="Duplicate"):
        VALIDATOR.validate_simulations(result_rows[1] + [result_rows[1][0]])


@pytest.mark.parametrize("contents", ["x,x\n1,2\n", "x,y\n1\n", "x\n1,2\n", "x,y\n"])
@deal.pre(lambda tmp_path, contents: protected_history_intact())
@deal.pre(lambda tmp_path, contents: isinstance(contents, str) and tmp_path.is_dir())
@deal.ensure(lambda tmp_path, contents, result: protected_history_intact())
@deal.ensure(lambda tmp_path, contents, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has("read", "write")
def test_csv_structure_is_strict(tmp_path, contents):
    """Reject duplicate headers, truncated records and excess columns."""
    path = tmp_path.joinpath("bad.csv")
    path.write_text(contents)
    with pytest.raises(ValueError):
        VALIDATOR.read_csv(path)


@pytest.mark.parametrize("field,value", [("actual", "1"), ("expected", "1"), ("tolerance", "1"), ("actual", "nan"), ("name", "unknown")])
@deal.pre(lambda result_rows, field, value: protected_history_intact())
@deal.pre(lambda result_rows, field, value: isinstance(field, str) and isinstance(value, str))
@deal.ensure(lambda result_rows, field, value, result: protected_history_intact())
@deal.ensure(lambda result_rows, field, value, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has("read")
def test_identity_checker_cannot_approve_its_own_changed_targets(result_rows, field, value):
    """The checks CSV may not replace the paper's identities or loosen bounds."""
    damaged = copy.deepcopy(result_rows[2])
    damaged[0][field] = value
    with pytest.raises(ValueError):
        VALIDATOR.validate_checks(damaged)


@deal.pre(lambda result_rows: protected_history_intact())
@deal.ensure(lambda result_rows, result: protected_history_intact())
@deal.ensure(lambda result_rows, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has("read")
def test_missing_checks_and_negative_absolute_residuals_are_rejected(result_rows):
    """Completeness and the sign of a maximum residual carry real content."""
    with pytest.raises(ValueError, match="absent"):
        VALIDATOR.validate_checks(result_rows[2][1:])
    damaged = copy.deepcopy(result_rows[2])
    damaged[0]["actual"] = "-1e-12"
    with pytest.raises(ValueError, match="cannot be negative"):
        VALIDATOR.validate_checks(damaged)


@deal.pre(lambda: protected_history_intact())
@deal.ensure(lambda *, result: protected_history_intact())
@deal.ensure(lambda *, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has("read")
def test_rounding_certificates_reject_wrong_values_and_halfway_ties():
    """Strict inequalities are needed to establish a unique rounded result."""
    assert VALIDATOR.rounding_certificate(Fraction(54), Fraction("7.348469"), 1_000_000, True) == (42818031, 15969721)
    with pytest.raises(ValueError):
        VALIDATOR.rounding_certificate(Fraction(54), Fraction("7.348470"), 1_000_000, True)
    with pytest.raises(ValueError):
        VALIDATOR.rounding_certificate(Fraction(201, 200), Fraction(1), 100)
    with pytest.raises(deal.PreContractError):
        VALIDATOR.rounding_certificate(Fraction(1), Fraction("1.001"), 100)


@deal.pre(lambda result_directory, result_rows: protected_history_intact())
@deal.ensure(lambda result_directory, result_rows, result: protected_history_intact())
@deal.ensure(lambda result_directory, result_rows, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has("read", "write")
def test_complete_validator_rejects_missing_experiment_coverage(result_directory, result_rows):
    """Correct individual results do not excuse an omitted paper example."""
    assert VALIDATOR.validate(result_directory)["complete"] is True
    with result_directory.joinpath("calculation.csv").open("w", newline="") as stream:
        writer = csv.DictWriter(stream, fieldnames=list(result_rows[0][0]))
        writer.writeheader()
        writer.writerows(result_rows[0][1:])
    with pytest.raises(ValueError, match="omits a required IQ"):
        VALIDATOR.validate(result_directory)


@deal.pre(lambda result_directory, capsys: protected_history_intact())
@deal.ensure(lambda result_directory, capsys, result: protected_history_intact())
@deal.ensure(lambda result_directory, capsys, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has("read", "write", "stdout", "stderr")
def test_cli_summary_and_exact_paper_certificates(result_directory, capsys):
    """Exercise serialization and all 27 independently certified rounded cells."""
    output = result_directory.joinpath("summary.json")
    assert VALIDATOR.main([str(result_directory), "--json-output", str(output)]) == 0
    printed = json.loads(capsys.readouterr().out)
    assert printed == json.loads(output.read_text())
    assert printed["calculations"]["matrix_cross_checks"] == 9
    assert printed["simulations"]["simulation_rows"] == 24
    assert printed["checks"]["identity_checks"] == 18
    assert printed["paper"] == {"iq_rows": 9, "matrix_cases": 17, "counterexample_checked": True, "rounding_entries": 27,
                                "certificate_integers": 74, "standardized_rows": 3, "limit_rows": 3}
