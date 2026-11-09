#!/usr/bin/env python3
"""Compare Ada outputs with the independently computed SciPy reference CSVs."""
import argparse
import csv
import math
from pathlib import Path

import deal

ROOT = Path(__file__).resolve().parent


@deal.pre(lambda numerator, denominator: type(numerator) is int)
@deal.pre(lambda numerator, denominator: type(denominator) is int and 1 <= numerator < denominator <= 2147483647)
@deal.post(lambda result: math.isfinite(result) and 0 < result < 1)
@deal.raises()
@deal.has()
# An open-unit Park--Miller state preserves its exact quotient, lower
# unit, upper-complement and floating-point reconstruction constraints.
@deal.ensure(lambda numerator, denominator, result: result == numerator / denominator)
@deal.ensure(lambda numerator, denominator, result: result <= numerator)
@deal.ensure(lambda numerator, denominator, result: result >= 1 / denominator)
@deal.ensure(lambda numerator, denominator, result: result <=
             1 - 1 / denominator + 1e-15)
@deal.ensure(lambda numerator, denominator, result: math.isclose(
    result * denominator, numerator, rel_tol=8e-15, abs_tol=1e-8))
def _open_unit_ratio(numerator, denominator):
    """Map a positive Park--Miller state to an open-unit-interval float."""
    return numerator / denominator


@deal.pre(lambda condition, message: type(condition) is bool)
@deal.pre(lambda condition, message: isinstance(message, str))
@deal.ensure(lambda condition, message, result: condition and result is None)
@deal.raises(ValueError)
@deal.has()
def require(condition, message):
    """Validation that remains active when Python assertions are optimized away."""
    if not condition:
        raise ValueError(message)


@deal.pre(lambda path: isinstance(path, Path))
@deal.pre(lambda path: path.is_file())
@deal.post(lambda result: isinstance(result, list) and all(
    isinstance(row, dict) and all(isinstance(key, str) and isinstance(value, str)
                                 for key, value in row.items()) for row in result))
@deal.raises(OSError, ValueError, csv.Error)
@deal.has("read")
# The result retains a consistent complete CSV schema, never accepts
# a missing parsed column, and contains only nonempty string headers.
@deal.post(lambda result: all(None not in row for row in result))
@deal.post(lambda result: all(
    value is not None for row in result for value in row.values()))
@deal.post(lambda result: not result or
           all(row.keys() == result[0].keys() for row in result))
@deal.post(lambda result: all(
    isinstance(key, str) and bool(key) for row in result for key in row))
@deal.post(lambda result: not result or len(result[0]) > 0)
def read(path):
    with path.open(newline="") as stream:
        reader = csv.DictReader(stream)
        names = reader.fieldnames or []
        require(bool(names) and all(names) and len(set(names)) == len(names),
                "CSV requires distinct, nonempty column names")
        rows = list(reader)
    require(not any(None in row or any(value is None for value in row.values()) for row in rows),
            "CSV row width does not match its header")
    return rows


@deal.pre(lambda x, y, label, tolerance=1e-10: math.isfinite(x))
@deal.pre(lambda x, y, label, tolerance=1e-10: math.isfinite(y) and math.isfinite(tolerance) and (tolerance > 0) and isinstance(label, str))
@deal.ensure(lambda x, y, label, tolerance=1e-10, result=None:
             result is None and abs(x-y) <= tolerance)
@deal.raises(ValueError)
@deal.has()
def close(x, y, label, tolerance=1e-10):
    if abs(x-y) > tolerance:
        raise ValueError(f"{label}: {x!r} differs from reference {y!r}")


@deal.pre(lambda rows, columns, label: isinstance(rows, list))
@deal.pre(lambda rows, columns, label: isinstance(columns, set) and all((isinstance(row, dict) for row in rows)) and isinstance(label, str))
@deal.ensure(lambda rows, columns, label, result:
             result is None and all(columns <= row.keys() for row in rows))
@deal.raises(ValueError)
@deal.has()
def require_columns(rows, columns, label):
    require(all(columns <= row.keys() for row in rows), f"Missing {label} CSV columns")
    return None


@deal.pre(lambda directory, replay=False: isinstance(directory, Path))
@deal.pre(lambda directory, replay=False: directory.is_dir() and type(replay) is bool)
@deal.post(lambda result: result is None)
@deal.raises(OSError, ValueError, csv.Error)
@deal.has("read", "stdout")
def validate(directory, replay=False):
    calculated = read(directory.joinpath("calculation.csv"))
    expected = read(ROOT.parent.joinpath("data", "admission_probabilities.csv"))
    fields = {"case", "rho", "cutoff_a_z", "cutoff_b_z", "p_a", "p_b", "joint",
              "union", "conditional_b_given_a", "conditional_a_given_b", "phi"}
    require_columns(expected, fields, "reference calculation")
    require_columns(calculated, fields | {"joint_refinement_delta", "raw_union",
                    "raw_conditional_b_given_a", "raw_conditional_a_given_b", "complement_a_units"}, "calculation")
    require(len(calculated) == len(expected) == 4, "Expected four calculation cases")
    for row, reference in zip(calculated, expected):
        require(row["case"] == reference["case"], "Calculation case labels differ")
        for key in reference.keys() - {"case"}:
            close(float(row[key]), float(reference[key]), f"{row['case']}: {key}")
        for key in ("union", "conditional_b_given_a", "conditional_a_given_b"):
            close(float(row["raw_"+key]), float(reference[key]), f"raw {row['case']}: {key}", 1e-12)
        require(int(row["complement_a_units"]) == 10**15-round(float(row["p_a"])*10**15),
                "Incorrect exact probability complement")
        require(0 <= float(row["joint_refinement_delta"]) < 1e-11,
                "Quadrature refinement difference must be finite, nonnegative, and below tolerance")

    actual_grid = read(directory.joinpath("grid.csv"))
    expected_grid = read(ROOT.parent.joinpath("data", "followup_grid.csv"))
    grid_fields = {"cutoff_iq", "marginal_continuous", "joint_continuous", "conditional_continuous",
                   "grid_joint", "grid_marginal", "grid_conditional"}
    require_columns(actual_grid, grid_fields, "grid")
    require_columns(expected_grid, grid_fields, "reference grid")
    require(len(actual_grid) == len(expected_grid) == 3, "Expected three grid cases")
    for row, reference in zip(actual_grid, expected_grid):
        require(set(row) == grid_fields, "Unexpected grid CSV columns")
        for key in grid_fields:
            close(float(row[key]), float(reference[key]), f"grid: {key}")

    calibrations = read(directory.joinpath("calibration.csv"))
    require(len(calibrations) == 1, "Expected one calibration case")
    require_columns(calibrations, {"cutoff_z", "cutoff_iq_sd16", "actual_union"}, "calibration")
    calibration = calibrations[0]
    close(float(calibration["cutoff_z"]), 2.2700549290597922, "calibrated OR cutoff")
    close(float(calibration["cutoff_iq_sd16"]), 136.32087886495668, "calibrated IQ cutoff", 2e-9)
    close(float(calibration["actual_union"]), 0.02, "calibrated union probability")

    simulations = read(directory.joinpath("simulation.csv"))
    require_columns(simulations, {"case", "trials", "seed", "neither", "a_only", "b_only", "both",
                    "marginal_a", "marginal_b", "union", "joint_fraction", "conditional_b_given_a",
                    "conditional_a_given_b", "joint_wilson_lower", "joint_wilson_upper"}, "simulation")
    require(len(simulations) == 4, "Expected four simulation cases")
    trial_seed_pairs = {(int(row["trials"]), int(row["seed"])) for row in simulations}
    require(len(trial_seed_pairs) == 1, "Simulation rows must share the recorded trial count and seed")
    for row, reference in zip(simulations, expected):
        require(row["case"] == reference["case"], "Simulation case labels differ")
        n = int(row["trials"])
        require(1 <= n <= 100_000_000, "Simulation trial count is outside the Ada domain")
        require(1 <= int(row["seed"]) <= 2_147_483_646, "Simulation seed is outside the Park-Miller domain")
        c00, c10, c01, c11 = (int(row[key]) for key in ("neither", "a_only", "b_only", "both"))
        require(min(c00,c10,c01,c11) >= 0, "Simulation event counts must be nonnegative")
        require(c00+c10+c01+c11 == n, "Simulation cells do not sum to the trial count")
        require(int(row["marginal_a"]) == c10+c11, "Incorrect marginal A count")
        require(int(row["marginal_b"]) == c01+c11, "Incorrect marginal B count")
        require(int(row["union"]) == c10+c01+c11, "Incorrect union count")
        close(float(row["joint_fraction"]), c11/n, "Monte Carlo fraction", 2e-15)
        for key, denom in (("conditional_b_given_a", c10+c11), ("conditional_a_given_b", c01+c11)):
            if denom:
                close(float(row[key]), c11/denom, key, 2e-15)
            else:
                require(row[key] == "NA", "A zero denominator must be reported as NA")
        p = float(reference["joint"])
        if abs(c11/n-p) > 6*math.sqrt(p*(1-p)/n)+10/n:
            raise ValueError("Monte Carlo outcome is unexpectedly far from the Gaussian model")
        lo, hi = float(row["joint_wilson_lower"]), float(row["joint_wilson_upper"])
        require(0 <= lo <= hi <= 1, "Wilson interval must be finite, ordered, and inside [0,1]")
        print(f"{row['case']}: both={c11}/{n}; 95% Wilson [{lo:.10g}, {hi:.10g}]; model={p:.10g}")
    if replay:
        trials = int(simulations[0]["trials"])
        state = int(simulations[0]["seed"])
        counts = [[0]*4 for _ in simulations]
        a = [float(row["cutoff_a_z"]) for row in calculated]
        b = [float(row["cutoff_b_z"]) for row in calculated]
        for _ in range(trials):
            state = 48271*state % 2147483647
            u = _open_unit_ratio(state, 2147483647)
            state = 48271*state % 2147483647
            v = _open_unit_ratio(state, 2147483647)
            radius = math.sqrt(-2*math.log(u))
            angle = 2*math.pi*v
            x = radius*math.cos(angle)
            y = .7*x+math.sqrt(.51)*radius*math.sin(angle)
            for k in range(4):
                counts[k][2*int(x>a[k])+int(y>b[k])] += 1
        for row, tally in zip(simulations,counts):
            require(tally == [int(row[k]) for k in ("neither","b_only","a_only","both")],
                    "Independent simulation replay differs from the recorded event cells")
        print(f"Independent Python replay matches all four count cells for {trials} trials.")
    print("Ada numerical outputs agree with independent SciPy reference CSVs within 1e-10 absolute tolerance.")


if __name__ == "__main__":
    deal.enable(warn=False)
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("directory", nargs="?", type=Path, default=ROOT/"results")
    parser.add_argument("--replay", action="store_true")
    args = parser.parse_args()
    validate(args.directory, args.replay)
