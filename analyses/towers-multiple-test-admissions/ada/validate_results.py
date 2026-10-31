#!/usr/bin/env python3
"""Compare Ada outputs with the independently computed SciPy reference CSVs."""
import argparse
import csv
import math
from pathlib import Path

ROOT = Path(__file__).resolve().parent


def read(path):
    with path.open(newline="") as stream:
        return list(csv.DictReader(stream))


def close(x, y, label, tolerance=1e-10):
    if not math.isfinite(x) or abs(x-y) > tolerance:
        raise ValueError(f"{label}: {x!r} differs from reference {y!r}")


def validate(directory, replay=False):
    calculated = read(directory / "calculation.csv")
    expected = read(ROOT.parent / "data/admission_probabilities.csv")
    assert len(calculated) == len(expected) == 4
    for row, reference in zip(calculated, expected):
        assert row["case"] == reference["case"]
        for key in reference.keys() - {"case"}:
            close(float(row[key]), float(reference[key]), f"{row['case']}: {key}")
        for key in ("union", "conditional_b_given_a", "conditional_a_given_b"):
            close(float(row["raw_"+key]), float(reference[key]), f"raw {row['case']}: {key}", 1e-12)
        assert int(row["complement_a_units"]) == 10**15-round(float(row["p_a"])*10**15)
        assert float(row["joint_refinement_delta"]) < 1e-11

    actual_grid = read(directory / "grid.csv")
    expected_grid = read(ROOT.parent / "data/followup_grid.csv")
    assert len(actual_grid) == len(expected_grid) == 3
    for row, reference in zip(actual_grid, expected_grid):
        for key in row:
            close(float(row[key]), float(reference[key]), f"grid: {key}")

    calibration, = read(directory / "calibration.csv")
    close(float(calibration["cutoff_z"]), 2.2700549290597922, "calibrated OR cutoff")
    close(float(calibration["cutoff_iq_sd16"]), 136.32087886495668, "calibrated IQ cutoff", 2e-9)
    close(float(calibration["actual_union"]), 0.02, "calibrated union probability")

    simulations = read(directory / "simulation.csv")
    assert len(simulations) == 4
    for row, reference in zip(simulations, expected):
        assert row["case"] == reference["case"]
        n = int(row["trials"])
        c00, c10, c01, c11 = (int(row[key]) for key in ("neither", "a_only", "b_only", "both"))
        assert min(c00,c10,c01,c11) >= 0
        assert c00+c10+c01+c11 == n
        assert int(row["marginal_a"]) == c10+c11
        assert int(row["marginal_b"]) == c01+c11
        assert int(row["union"]) == c10+c01+c11
        close(float(row["joint_fraction"]), c11/n, "Monte Carlo fraction", 2e-15)
        for key, denom in (("conditional_b_given_a", c10+c11), ("conditional_a_given_b", c01+c11)):
            if denom:
                close(float(row[key]), c11/denom, key, 2e-15)
            else:
                assert row[key] == "NA"
        p = float(reference["joint"])
        if abs(c11/n-p) > 6*math.sqrt(p*(1-p)/n)+10/n:
            raise ValueError("Monte Carlo outcome is unexpectedly far from the Gaussian model")
        lo, hi = float(row["joint_wilson_lower"]), float(row["joint_wilson_upper"])
        assert 0 <= lo <= hi <= 1
        print(f"{row['case']}: both={c11}/{n}; 95% Wilson [{lo:.10g}, {hi:.10g}]; model={p:.10g}")
    if replay:
        trials = int(simulations[0]["trials"])
        state = int(simulations[0]["seed"])
        counts = [[0]*4 for _ in simulations]
        a = [float(row["cutoff_a_z"]) for row in calculated]
        b = [float(row["cutoff_b_z"]) for row in calculated]
        for _ in range(trials):
            state = 48271*state % 2147483647
            u = state/2147483647
            state = 48271*state % 2147483647
            v = state/2147483647
            radius = math.sqrt(-2*math.log(u))
            angle = 2*math.pi*v
            x = radius*math.cos(angle)
            y = .7*x+math.sqrt(.51)*radius*math.sin(angle)
            for k in range(4):
                counts[k][2*int(x>a[k])+int(y>b[k])] += 1
        for row, tally in zip(simulations,counts):
            assert tally == [int(row[k]) for k in ("neither","b_only","a_only","both")]
        print(f"Independent Python replay matches all four count cells for {trials} trials.")
    print("Ada numerical outputs agree with independent SciPy reference CSVs within 1e-10 absolute tolerance.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("directory", nargs="?", type=Path, default=ROOT/"results")
    parser.add_argument("--replay", action="store_true")
    args = parser.parse_args()
    validate(args.directory, args.replay)
