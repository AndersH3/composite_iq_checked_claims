#!/usr/bin/env python3
"""Independently compare Ada output with SciPy and assess moderate MC tails.

This is numerical validation, not a proof of libm or of the Gaussian model.
"""
import argparse
import csv
import io
import json
import math
from pathlib import Path

from scipy.stats import norm

COUNTS = (1, 2, 3, 4, 5, 10, 100, 1000)


def require_close(actual, expected, label, *, atol=5e-11):
    if not math.isfinite(actual) or abs(actual - expected) > atol:
        raise ValueError(f"{label}: {actual!r} differs from {expected!r}")


def validate_calculations(path):
    content = path.read_text(encoding="utf-8")
    table, example_text = content.split("# examples\n")
    rows = list(csv.DictReader(io.StringIO(table)))
    if [r["tests"] for r in rows] != [str(n) for n in COUNTS] + ["infinity"]:
        raise ValueError("Unexpected threshold table row labels")
    q = float(norm.isf(1e-6))
    max_error = 0.0
    for row in rows:
        n = None if row["tests"] == "infinity" else int(row["tests"])
        factor = .6 if n is None else .6 + .4/n
        z = q * math.sqrt(factor)
        for field, expected in (("variance_factor", factor), ("mean_z", z),
                                ("mean_score_sd16", 100 + 16*z)):
            actual = float(row[field])
            require_close(actual, expected, f"n={n}, {field}")
            max_error = max(max_error, abs(actual - expected))
    examples = {r[0]: float(r[1]) for r in csv.reader(io.StringIO(example_text))}
    expected = {
        "upper_tail_quantile": q,
        "three_test_mean160_composite_iq": 100 + 60/math.sqrt(.6 + .4/3),
        "latent_conditional_mean_iq": 100 + 16*q*math.sqrt(1.8/2.2),
        "latent_conditional_sd_iq": 16*math.sqrt(.4/2.2),
    }
    if set(examples) != set(expected):
        raise ValueError("Unexpected worked-example labels")
    for label, value in expected.items():
        require_close(examples[label], value, label)
        max_error = max(max_error, abs(examples[label]-value))
    return {"threshold_rows": len(rows), "worked_examples": len(expected),
            "max_absolute_numeric_error": max_error, "tolerance": 5e-11}


def wilson(successes, total):
    z = float(norm.isf(.025))
    phat = successes / total
    denominator = 1 + z*z/total
    center = (phat + z*z/(2*total))/denominator
    radius = z*math.sqrt(phat*(1-phat)/total + z*z/(4*total*total))/denominator
    return [max(0, center-radius), min(1, center+radius)]


def validate_simulation(path):
    lines = [s for s in path.read_text(encoding="utf-8").splitlines()
             if not s.startswith("#")]
    rows = list(csv.DictReader(lines))
    if [int(r["tests"]) for r in rows] != list(COUNTS):
        raise ValueError("Unexpected simulation row labels")
    summaries = []
    for row in rows:
        n, trials = int(row["tests"]), int(row["trials"])
        if trials < 2:
            raise ValueError("Simulation needs at least two trials")
        k2, k3, rare = (int(row[k]) for k in ("above2", "above3", "above_rare"))
        if not 0 <= rare <= k3 <= k2 <= trials:
            raise ValueError("Simulation counter nesting failed")
        mean, variance = float(row["mean_composite_z"]), float(row["variance_composite_z"])
        # Broad six-standard-error diagnostics at specified moderate tails.
        # They are stochastic diagnostics, not conditions of formal proof.
        if abs(mean) > 6/math.sqrt(trials):
            raise ValueError(f"n={n}: mean exceeds six-SE diagnostic bound")
        if abs(variance-1) > 6*math.sqrt(2/(trials-1)):
            raise ValueError(f"n={n}: variance exceeds six-SE diagnostic bound")
        tails = {}
        for cutoff, count in ((2, k2), (3, k3)):
            expected = float(norm.sf(cutoff))
            actual = count/trials
            require_close(float(row[f"rate_above{cutoff}"]), actual,
                          f"n={n}: recorded rate{cutoff}", atol=6e-13)
            require_close(float(row[f"expected_rate{cutoff}"]), expected,
                          f"n={n}: reference rate{cutoff}", atol=6e-13)
            diagnostic_bound = 6*math.sqrt(expected*(1-expected)/trials) + 1/trials
            if abs(actual-expected) > diagnostic_bound:
                raise ValueError(f"n={n}: tail {cutoff} exceeds six-SE diagnostic bound")
            tails[str(cutoff)] = {"observed": actual, "reference": expected,
                                  "wilson_95_interval": wilson(count, trials)}
        summaries.append({"tests": n, "trials": trials, "mean": mean,
                          "variance": variance, "tails": tails,
                          "rare_count_descriptive_only": rare})
    return {"cases": summaries,
            "limitation": "MC diagnostics do not establish the one-in-a-million tail, libm correctness, model validity, or formal proof."}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--calculations", type=Path, required=True)
    parser.add_argument("--simulation", type=Path)
    parser.add_argument("--json-output", type=Path)
    args = parser.parse_args()
    report = {"calculations": validate_calculations(args.calculations)}
    if args.simulation:
        report["simulation"] = validate_simulation(args.simulation)
    if args.json_output:
        args.json_output.parent.mkdir(parents=True, exist_ok=True)
        args.json_output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(report["calculations"], sort_keys=True))
    if args.simulation:
        print(f"Validated {len(report['simulation']['cases'])} simulation cases (moderate-tail diagnostics only).")


if __name__ == "__main__":
    main()
