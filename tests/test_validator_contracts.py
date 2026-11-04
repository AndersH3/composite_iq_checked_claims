"""Validate retained outputs and reject deliberately corrupted copies."""
from conftest import protected_history_intact, reference_inputs_intact
import csv
import io
import math
from pathlib import Path
import shutil
import subprocess
from subprocess import CalledProcessError, TimeoutExpired
import sys

import deal
from hypothesis import given, settings, strategies as st
import pytest

from conftest import EVIDENCE, ROOT, load_script


@deal.ensure(lambda path, field, value, index=0, *, result: protected_history_intact())
@deal.pre(lambda path, field, value, index=0:
          isinstance(path, Path) and path.is_file() and isinstance(field, str) and bool(field)
          and isinstance(value, str) and isinstance(index, int) and not isinstance(index, bool) and index >= 0)
@deal.post(lambda result: result is None)
@deal.raises(OSError, ValueError, KeyError, IndexError, csv.Error)
@deal.has("read", "write")
def rewrite_csv(path: Path, field: str, value: str, index: int = 0) -> None:
    with path.open(newline="") as stream:
        reader = csv.DictReader(stream)
        fields, rows = reader.fieldnames, list(reader)
    rows[index][field] = value
    with path.open("w", newline="") as stream:
        writer = csv.DictWriter(stream, fieldnames=fields)
        writer.writeheader()
        writer.writerows(rows)


@deal.ensure(lambda tmp_path, *, result: protected_history_intact())
@deal.pre(lambda tmp_path: isinstance(tmp_path, Path) and tmp_path.is_dir()
          and not (tmp_path / "calculations.csv").exists())
@deal.post(lambda result: isinstance(result, Path) and result.is_file()
           and result.name == "calculations.csv" and "nan" in result.read_text())
@deal.raises(OSError, ValueError, KeyError, IndexError, csv.Error)
@deal.has("read", "write")
def corrupted_hoeflin_calculations(tmp_path: Path) -> Path:
    original = EVIDENCE.joinpath("hoeflin/calculations.csv").read_text()
    table, examples = original.split("# examples\n")
    reader = csv.DictReader(io.StringIO(table))
    fields, rows = reader.fieldnames, list(reader)
    rows[0]["mean_score_sd16"] = "nan"
    buf = io.StringIO()
    writer = csv.DictWriter(buf, fieldnames=fields)
    writer.writeheader()
    writer.writerows(rows)
    path = tmp_path.joinpath("calculations.csv")
    path.write_text(buf.getvalue() + "# examples\n" + examples)
    return path


@pytest.mark.parametrize("actual,expected", [(math.nan, 1.0), (1.0, math.inf)])
@deal.pre(lambda hoeflin_validator, towers_validator, actual, expected: protected_history_intact())
@deal.ensure(lambda hoeflin_validator, towers_validator, actual, expected, *, result: protected_history_intact())
@deal.ensure(lambda hoeflin_validator, towers_validator, actual, expected, *, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has('stdout', 'stderr', "read")
def test_comparison_helpers_reject_nonfinite_values(hoeflin_validator, towers_validator, actual, expected):
    with pytest.raises(deal.PreContractError):
        hoeflin_validator.require_close(actual, expected, "nonfinite")
    with pytest.raises(deal.PreContractError):
        towers_validator.close(actual, expected, "nonfinite")


@pytest.mark.parametrize("tolerance", [0.0, -1.0, math.nan, math.inf])
@deal.pre(lambda hoeflin_validator, towers_validator, tolerance: protected_history_intact())
@deal.ensure(lambda hoeflin_validator, towers_validator, tolerance, *, result: protected_history_intact())
@deal.ensure(lambda hoeflin_validator, towers_validator, tolerance, *, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has('stdout', 'stderr', "read")
def test_comparison_helpers_reject_invalid_tolerances(hoeflin_validator, towers_validator, tolerance):
    with pytest.raises(deal.PreContractError):
        hoeflin_validator.require_close(1.0, 1.0, "invalid tolerance", atol=tolerance)
    with pytest.raises(deal.PreContractError):
        towers_validator.close(1.0, 1.0, "invalid tolerance", tolerance)


@pytest.mark.parametrize("successes,total", [
    (-1, 10), (11, 10), (0, 0), (0, 100_000_001), (True, 10), (0, True),
])
@deal.pre(lambda hoeflin_validator, successes, total: protected_history_intact())
@deal.ensure(lambda hoeflin_validator, successes, total, *, result: protected_history_intact())
@deal.ensure(lambda hoeflin_validator, successes, total, *, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has('stdout', 'stderr', "read")
def test_wilson_rejects_invalid_count_domain(hoeflin_validator, successes, total):
    with pytest.raises(deal.PreContractError):
        hoeflin_validator.wilson(successes, total)


@deal.pre(lambda hoeflin_validator: protected_history_intact())
@deal.ensure(lambda hoeflin_validator, *, result: protected_history_intact())
@deal.ensure(lambda hoeflin_validator, *, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has('stdout', 'stderr', "read")
def test_wilson_extreme_counts_are_finite_ordered_intervals(hoeflin_validator):
    for successes in (0, 100):
        lower, upper = hoeflin_validator.wilson(successes, 100)
        assert math.isfinite(lower) and math.isfinite(upper)
        assert 0 <= lower <= upper <= 1
        assert lower <= successes/100 <= upper + 1e-15


@settings(max_examples=40, derandomize=True, deadline=None)
@given(total=st.integers(1, 100_000_000), fraction=st.floats(0, 1, allow_nan=False, allow_infinity=False))
@deal.pre(lambda hoeflin_validator, total, fraction: protected_history_intact())
@deal.ensure(lambda hoeflin_validator, total, fraction, *, result: protected_history_intact())
@deal.ensure(lambda hoeflin_validator, total, fraction, *, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has('stdout', 'stderr', "read")
def test_wilson_respects_success_failure_symmetry(hoeflin_validator, total, fraction):
    successes = min(total, int(total * fraction))
    lo, hi = hoeflin_validator.wilson(successes, total)
    other_lo, other_hi = hoeflin_validator.wilson(total - successes, total)
    assert lo == pytest.approx(1-other_hi, abs=2e-14)
    assert hi == pytest.approx(1-other_lo, abs=2e-14)


@deal.pre(lambda hoeflin_validator: protected_history_intact())
@deal.ensure(lambda hoeflin_validator, *, result: protected_history_intact())
@deal.ensure(lambda hoeflin_validator, *, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has('stdout', 'stderr', 'read')
def test_hoeflin_retained_calculations_and_simulation_are_accepted(hoeflin_validator):
    result = hoeflin_validator.validate_calculations(EVIDENCE / "hoeflin/calculations.csv")
    assert result["threshold_rows"] == 9 and result["worked_examples"] == 4
    assert result["max_absolute_numeric_error"] < result["tolerance"]
    simulation = hoeflin_validator.validate_simulation(EVIDENCE / "hoeflin/simulation.csv")
    assert len(simulation["cases"]) == 8


@deal.pre(lambda towers_validator: protected_history_intact())
@deal.ensure(lambda towers_validator, *, result: protected_history_intact())
@deal.ensure(lambda towers_validator, *, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has('stdout', 'stderr', 'read')
def test_towers_retained_calculations_and_simulation_are_accepted(towers_validator):
    towers_validator.validate(EVIDENCE / "towers", replay=False)


@deal.pre(lambda hoeflin_validator, tmp_path: protected_history_intact())
@deal.ensure(lambda hoeflin_validator, tmp_path, *, result: protected_history_intact())
@deal.ensure(lambda hoeflin_validator, tmp_path, *, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has('stdout', 'stderr', 'read', 'write')
def test_hoeflin_validator_rejects_nonfinite_calculated_value(hoeflin_validator, tmp_path):
    path = corrupted_hoeflin_calculations(tmp_path)
    with pytest.raises((ValueError, deal.ContractError)):
        hoeflin_validator.validate_calculations(path)


@deal.pre(lambda hoeflin_validator, tmp_path: protected_history_intact())
@deal.ensure(lambda hoeflin_validator, tmp_path, *, result: protected_history_intact())
@deal.ensure(lambda hoeflin_validator, tmp_path, *, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has('stdout', 'stderr', 'read', 'write')
def test_hoeflin_validator_rejects_non_nested_counts(hoeflin_validator, tmp_path):
    path = tmp_path / "simulation.csv"
    # Preserve the two metadata comments while editing the first data row.
    text = (EVIDENCE / "hoeflin/simulation.csv").read_text()
    comments = [line for line in text.splitlines() if line.startswith("#")]
    rows = list(csv.DictReader(line for line in text.splitlines() if not line.startswith("#")))
    rows[0]["above3"] = str(int(rows[0]["above2"]) + 1)
    buf = io.StringIO()
    writer = csv.DictWriter(buf, fieldnames=list(rows[0]))
    writer.writeheader()
    writer.writerows(rows)
    path.write_text("\n".join(comments) + "\n" + buf.getvalue())
    with pytest.raises((ValueError, deal.ContractError)):
        hoeflin_validator.validate_simulation(path)


@deal.pre(lambda towers_validator, tmp_path: protected_history_intact())
@deal.ensure(lambda towers_validator, tmp_path, *, result: protected_history_intact())
@deal.ensure(lambda towers_validator, tmp_path, *, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has('stdout', 'stderr', 'read', 'write')
def test_towers_validator_rejects_missing_data_rows(towers_validator, tmp_path):
    directory = tmp_path / "towers"
    shutil.copytree(EVIDENCE / "towers", directory)
    (directory / "calculation.csv").write_text("case\n")
    with pytest.raises((ValueError, deal.ContractError)):
        towers_validator.validate(directory)


@deal.pre(lambda towers_validator, tmp_path: protected_history_intact())
@deal.ensure(lambda towers_validator, tmp_path, *, result: protected_history_intact())
@deal.ensure(lambda towers_validator, tmp_path, *, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has('stdout', 'stderr', 'read', 'write')
def test_towers_validator_rejects_negative_count_cell(towers_validator, tmp_path):
    directory = tmp_path / "towers"
    shutil.copytree(EVIDENCE / "towers", directory)
    rewrite_csv(directory / "simulation.csv", "both", "-1")
    with pytest.raises((ValueError, deal.ContractError)):
        towers_validator.validate(directory)


@deal.ensure(lambda arguments, *, result: protected_history_intact())
@deal.pre(lambda arguments: isinstance(arguments, (list, tuple)) and bool(arguments)
          and all(isinstance(value, (str, Path)) for value in arguments)
          and Path(arguments[0]).is_file())
@deal.post(lambda result: result is None)
@deal.raises(AssertionError, OSError, ValueError, subprocess.SubprocessError,
             CalledProcessError, TimeoutExpired)
@deal.has("read", "write", "syscall", "time", "stdout", "stderr")
def assert_optimized_cli_rejects(arguments: list) -> None:
    process = subprocess.run([sys.executable, "-O", *map(str, arguments)],
                             capture_output=True, text=True, timeout=30)
    assert process.returncode != 0, process.stdout
    assert "ModuleNotFoundError" not in process.stderr
    assert "ValueError" in process.stderr or "ContractError" in process.stderr, process.stderr


@deal.pre(lambda tmp_path: protected_history_intact())
@deal.ensure(lambda tmp_path, *, result: protected_history_intact())
@deal.ensure(lambda tmp_path, *, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has('stdout', 'stderr', 'read', 'write', 'syscall', 'time')
def test_hoeflin_optimized_cli_rejects_corrupt_data(tmp_path):
    bad = corrupted_hoeflin_calculations(tmp_path)
    assert_optimized_cli_rejects([
        ROOT / "analyses/hoeflin-ferguson/ada/scripts/validate_results.py", "--calculations", bad,
    ])


@deal.pre(lambda tmp_path: protected_history_intact())
@deal.ensure(lambda tmp_path, *, result: protected_history_intact())
@deal.ensure(lambda tmp_path, *, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has('stdout', 'stderr', 'read', 'write', 'syscall', 'time')
def test_towers_optimized_cli_rejects_corrupt_data(tmp_path):
    directory = tmp_path / "towers"
    shutil.copytree(EVIDENCE / "towers", directory)
    (directory / "calculation.csv").write_text("case\n")
    assert_optimized_cli_rejects([
        ROOT / "analyses/towers-multiple-test-admissions/ada/validate_results.py", directory,
    ])


@deal.pre(lambda: protected_history_intact())
@deal.ensure(lambda *, result: protected_history_intact())
@deal.ensure(lambda *, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has('stdout', 'stderr', 'read', 'write', 'import', 'global')
def test_contract_negative_control_rejects_bad_precondition():
    module = load_script("contract_negative_pre", "tests/fixtures/contract_negative_control.py")
    with pytest.raises(deal.PreContractError):
        module.probability_identity(-.1)


@deal.pre(lambda: protected_history_intact())
@deal.ensure(lambda *, result: protected_history_intact())
@deal.ensure(lambda *, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has('stdout', 'stderr', 'read', 'write', 'import', 'global')
def test_contract_negative_control_rejects_wrong_postcondition():
    module = load_script("contract_negative_post", "tests/fixtures/contract_negative_control.py")
    with pytest.raises(deal.PostContractError):
        module.negative_probability()
