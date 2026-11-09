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

import sys

import deal
from scipy.stats import norm

COUNTS = (1, 2, 3, 4, 5, 10, 100, 1000)


@deal.pre(lambda numerator, denominator: type(numerator) in (int, float))
@deal.pre(lambda numerator, denominator: 0 <= numerator <= 2 and type(denominator) in (int, float) and (1 <= denominator <= 1000))
@deal.post(lambda result: math.isfinite(result) and 0 <= result <= 2)
@deal.raises()
@deal.has()
# Verify quotient boundary behavior and a numerical round-trip separately
# from the basic interval/range contract of the old Ada validator.
@deal.ensure(lambda numerator, denominator, result: numerator != 0 or result == 0)
@deal.ensure(lambda numerator, denominator, result: denominator != 1 or result == numerator)
@deal.ensure(lambda numerator, denominator, result: result <= numerator)
@deal.ensure(lambda numerator, denominator, result: numerator > denominator or result <= 1)
@deal.ensure(lambda numerator, denominator, result: math.isclose(
    result * denominator, numerator, rel_tol=8e-15, abs_tol=1e-15))
def _positive_ratio(numerator, denominator):
    """Divide bounded variance terms by a positive test count or variance sum."""
    return numerator / denominator


@deal.pre(lambda actual, expected, label, atol=5e-11: math.isfinite(actual))
@deal.pre(lambda actual, expected, label, atol=5e-11: math.isfinite(expected) and math.isfinite(atol) and (atol > 0) and isinstance(label, str))
@deal.ensure(lambda actual, expected, label, atol=5e-11, result=None:
             result is None and abs(actual - expected) <= atol)
@deal.raises(ValueError)
@deal.has()
def require_close(actual, expected, label, *, atol=5e-11):
    if abs(actual - expected) > atol:
        raise ValueError(f"{label}: {actual!r} differs from {expected!r}")


@deal.pre(lambda content: isinstance(content, str))
@deal.post(lambda result: all((isinstance(row, dict) and all((isinstance(key, str) and isinstance(value, str) for key, value in row.items())) for row in result)))
@deal.post(lambda result: isinstance(result, list))
@deal.raises(ValueError, csv.Error)
@deal.has()
def csv_rows(content):
    """Reject missing, duplicate, or uneven fields instead of accepting zip truncation."""
    reader = csv.DictReader(io.StringIO(content))
    names = reader.fieldnames or []
    if not names or any(not name for name in names) or len(set(names)) != len(names):
        raise ValueError("CSV requires distinct, nonempty column names")
    rows = list(reader)
    if any(None in row or any(value is None for value in row.values()) for row in rows):
        raise ValueError("CSV row width does not match the header")
    return rows


@deal.pre(lambda path: isinstance(path, Path))
@deal.pre(lambda path: path.is_file())
@deal.post(lambda result: result["threshold_rows"] == 9 and result["worked_examples"] == 4
           and math.isfinite(result["max_absolute_numeric_error"])
           and 0 <= result["max_absolute_numeric_error"] <= result["tolerance"]
           and result["tolerance"] == 5e-11)
@deal.raises(OSError, ValueError, csv.Error)
@deal.has("read")
def validate_calculations(path):
    content = path.read_text(encoding="utf-8")
    table, example_text = content.split("# examples\n")
    rows = csv_rows(table)
    if not rows or set(rows[0]) != {"tests", "variance_factor", "mean_z", "mean_score_sd16"}:
        raise ValueError("Unexpected threshold CSV columns")
    if [r["tests"] for r in rows] != [str(n) for n in COUNTS] + ["infinity"]:
        raise ValueError("Unexpected threshold table row labels")
    q = float(norm.isf(1e-6))
    max_error = 0.0
    for row in rows:
        n = None if row["tests"] == "infinity" else int(row["tests"])
        factor = .6 if n is None else .6 + _positive_ratio(.4, n)
        z = q * math.sqrt(factor)
        for field, expected in (("variance_factor", factor), ("mean_z", z),
                                ("mean_score_sd16", 100 + 16*z)):
            actual = float(row[field])
            require_close(actual, expected, f"n={n}, {field}")
            max_error = max(max_error, abs(actual - expected))
    example_rows = list(csv.reader(io.StringIO(example_text)))
    if any(len(row) != 2 or not row[0] for row in example_rows):
        raise ValueError("Worked examples require a label and one numeric value")
    if len({row[0] for row in example_rows}) != len(example_rows):
        raise ValueError("Duplicate worked-example labels")
    examples = {r[0]: float(r[1]) for r in example_rows}
    expected = {
        "upper_tail_quantile": q,
        "three_test_mean160_composite_iq": 100 + 60/math.sqrt(.6 + _positive_ratio(.4, 3)),
        "latent_conditional_mean_iq": 100 + 16*q*math.sqrt(_positive_ratio(1.8, 2.2)),
        "latent_conditional_sd_iq": 16*math.sqrt(_positive_ratio(.4, 2.2)),
    }
    if set(examples) != set(expected):
        raise ValueError("Unexpected worked-example labels")
    for label, value in expected.items():
        require_close(examples[label], value, label)
        max_error = max(max_error, abs(examples[label]-value))
    return {"threshold_rows": len(rows), "worked_examples": len(expected),
            "max_absolute_numeric_error": max_error, "tolerance": 5e-11}


@deal.pre(lambda successes, total: type(successes) is int and type(total) is int
          and 1 <= total <= 100_000_000 and 0 <= successes <= total)
@deal.post(lambda result: len(result) == 2 and all(math.isfinite(x) for x in result)
           and 0 <= result[0] <= result[1] <= 1)
@deal.ensure(lambda successes, total, result:
             result[0] <= successes / total + 1e-15
             and successes / total - 1e-15 <= result[1])
@deal.raises()
@deal.has()
# Wilson intervals retain list shape and correctly cover the zero-count
# and all-success limiting cases, including positive finite-width bounds.
@deal.post(lambda result: isinstance(result, list))
@deal.ensure(lambda successes, total, result: successes != 0 or result[0] <= 1e-14)
@deal.ensure(lambda successes, total, result: successes != total or result[1] >= 1 - 1e-14)
@deal.ensure(lambda successes, total, result: successes != 0 or result[1] > 0)
@deal.ensure(lambda successes, total, result: successes != total or result[0] < 1)
def wilson(successes, total):
    z = float(norm.isf(.025))
    phat = successes / total
    denominator = 1 + z*z/total
    center = (phat + z*z/(2*total))/denominator
    radius = z*math.sqrt(phat*(1-phat)/total + z*z/(4*total*total))/denominator
    return [max(0, center-radius), min(1, center+radius)]


@deal.pre(lambda path: isinstance(path, Path))
@deal.pre(lambda path: path.is_file())
@deal.post(lambda result: len(result["cases"]) == len(COUNTS)
           and [case["tests"] for case in result["cases"]] == list(COUNTS)
           and all(2 <= case["trials"] <= 100_000_000
                   and math.isfinite(case["mean"])
                   and math.isfinite(case["variance"]) and case["variance"] >= 0
                   and 0 <= case["rare_count_descriptive_only"] <= case["trials"]
                   for case in result["cases"]))
@deal.raises(OSError, ValueError, csv.Error)
@deal.has("read")
def validate_simulation(path):
    lines = [s for s in path.read_text(encoding="utf-8").splitlines()
             if not s.startswith("#")]
    rows = csv_rows("\n".join(lines))
    fields = {"tests", "trials", "mean_composite_z", "variance_composite_z", "above2",
              "above3", "above_rare", "rate_above2", "rate_above3", "expected_rate2", "expected_rate3"}
    if not rows or set(rows[0]) != fields:
        raise ValueError("Unexpected simulation CSV columns")
    if [int(r["tests"]) for r in rows] != list(COUNTS):
        raise ValueError("Unexpected simulation row labels")
    summaries = []
    for row in rows:
        n, trials = int(row["tests"]), int(row["trials"])
        if not 2 <= trials <= 100_000_000:
            raise ValueError("Simulation trial count must be in 2..100000000")
        k2, k3, rare = (int(row[k]) for k in ("above2", "above3", "above_rare"))
        if not 0 <= rare <= k3 <= k2 <= trials:
            raise ValueError("Simulation counter nesting failed")
        mean, variance = float(row["mean_composite_z"]), float(row["variance_composite_z"])
        if not math.isfinite(mean) or not math.isfinite(variance) or variance < 0:
            raise ValueError("Simulation mean and variance must be finite; variance must be nonnegative")
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


@deal.post(lambda result: result is None)
@deal.raises(SystemExit, OSError, ValueError, csv.Error)
@deal.has("read", "write", "stdout", "stderr")
@deal.pre(lambda: isinstance(sys.argv, list))
@deal.pre(lambda: all(isinstance(argument, str) for argument in sys.argv))
def main():
    deal.enable(warn=False)
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
