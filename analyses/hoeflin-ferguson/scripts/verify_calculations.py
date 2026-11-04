#!/usr/bin/env python3
"""Recompute the report's conditional normal-model results and verify its data."""

import argparse
import csv
import math
from pathlib import Path
import re

import sys

import deal
from scipy.stats import norm


ROOT = Path(__file__).resolve().parents[1]
CSV_PATH = ROOT / "data" / "thresholds.csv"
TEX_PATH = ROOT / "composite_iq_analysis.tex"
RHO = 0.60
Q = float(norm.isf(1e-6))
COUNTS = (1, 2, 3, 4, 5, 10, 100, 1000)
FIELDS = ("tests", "mean_z", "mean_score_sd16")


@deal.post(lambda result: isinstance(result, bool))
@deal.has()
@deal.raises()
@deal.ensure(lambda value, result: not result or isinstance(value, (int, float)) and not isinstance(value, bool))
@deal.ensure(lambda value, result: not result or -math.inf < value < math.inf)
def _finite(value) -> bool:
    if not isinstance(value, (int, float)) or isinstance(value, bool):
        return False
    try:
        return math.isfinite(value)
    except OverflowError:
        return False


@deal.pre(lambda n, rho: isinstance(n, int) and not isinstance(n, bool)
          and 1 <= n <= 1_000_000 and _finite(rho) and 0 <= rho <= 1)
@deal.post(lambda result: _finite(result) and 0 < result <= 1)
@deal.ensure(lambda n, rho, result: math.isclose(
    n * result, 1 + (n - 1) * rho, rel_tol=8e-15, abs_tol=1e-15))
@deal.has()
@deal.raises()
def variance_factor(n: int, rho: float) -> float:
    """Variance of an equally weighted mean for the nonnegative-correlation model."""
    return rho + (1 - rho) / n


@deal.pre(lambda n, rho, quantile: isinstance(n, int) and not isinstance(n, bool)
          and 1 <= n <= 1_000_000 and _finite(rho) and 0 <= rho <= 1
          and _finite(quantile) and 0 <= quantile <= 10)
@deal.post(lambda result: _finite(result) and result >= 0)
@deal.ensure(lambda n, rho, quantile, result: result <= quantile)
@deal.has()
@deal.raises()
def mean_threshold(n: int, rho: float, quantile: float) -> float:
    """Convert a positive composite quantile to a required component mean."""
    return quantile * math.sqrt(variance_factor(n, rho))


@deal.pre(lambda numerator, denominator: _finite(numerator))
@deal.pre(lambda numerator, denominator: abs(numerator) <= 1e+100 and _finite(denominator) and (1e-100 <= denominator <= 1e+100))
@deal.post(lambda result: _finite(result))
@deal.has()
@deal.raises()
def _positive_ratio(numerator: float, denominator: float) -> float:
    """A finite scalar quotient on the documented numerical working range."""
    return numerator / denominator


@deal.post(lambda result: isinstance(result, bool))
@deal.has()
@deal.raises()
@deal.ensure(lambda rows, result: not result or len(rows) == len(COUNTS) + 1)
@deal.ensure(lambda rows, result: not result or [row[0] for row in rows] == [str(n) for n in COUNTS] + ["infinity"])
def _valid_rows(rows) -> bool:
    if not isinstance(rows, (list, tuple)) or len(rows) != len(COUNTS) + 1:
        return False
    for row, label in zip(rows, [str(n) for n in COUNTS] + ["infinity"]):
        if not isinstance(row, (list, tuple)) or len(row) != 3 or row[0] != label:
            return False
        if not _finite(row[1]) or not _finite(row[2]) or row[1] < 0:
            return False
        if not math.isclose(row[2], 100 + 16 * row[1], rel_tol=0, abs_tol=1e-12):
            return False
    return True


@deal.post(_valid_rows)
@deal.has()
@deal.raises()
@deal.pre(lambda: bool(COUNTS) and len(COUNTS) == len(set(COUNTS)) and all(type(n) is int and 1 <= n <= 1_000_000 for n in COUNTS))
@deal.pre(lambda: _finite(RHO) and 0 <= RHO <= 1 and _finite(Q) and 0 < Q <= 10)
def thresholds() -> list[tuple[str, float, float]]:
    rows = []
    for n in COUNTS:
        z = mean_threshold(n, RHO, Q)
        rows.append((str(n), z, 100 + 16 * z))
    z_limit = Q * math.sqrt(RHO)
    rows.append(("infinity", z_limit, 100 + 16 * z_limit))
    return rows


@deal.pre(lambda actual, expected, label: _finite(actual) and _finite(expected)
          and isinstance(label, str))
@deal.post(lambda result: result is None)
@deal.raises(ValueError)
@deal.reason(ValueError, lambda actual, expected, label:
             not math.isclose(actual, expected, rel_tol=0, abs_tol=1e-9))
@deal.has()
def check_close(actual: float, expected: float, label: str) -> None:
    if not math.isclose(actual, expected, rel_tol=0, abs_tol=1e-9):
        raise ValueError(f"{label}: got {actual!r}, expected {expected!r}")


@deal.pre(_valid_rows)
@deal.post(lambda result: result is None)
@deal.has("read", "write")
@deal.raises(OSError, csv.Error)
@deal.ensure(lambda rows, result: CSV_PATH.is_file())
def write_csv(rows: list[tuple[str, float, float]]) -> None:
    CSV_PATH.parent.mkdir(parents=True, exist_ok=True)
    with CSV_PATH.open("w", newline="", encoding="utf-8") as stream:
        writer = csv.writer(stream)
        writer.writerow(FIELDS)
        for n, z, score in rows:
            writer.writerow((n, f"{z:.12f}", f"{score:.12f}"))


@deal.pre(_valid_rows)
@deal.post(lambda result: result is None)
@deal.has("read")
@deal.raises(OSError, ValueError, csv.Error)
@deal.ensure(lambda rows, result: _valid_rows(rows))
def verify_csv(rows: list[tuple[str, float, float]]) -> None:
    with CSV_PATH.open(newline="", encoding="utf-8") as stream:
        reader = csv.DictReader(stream)
        if tuple(reader.fieldnames or ()) != FIELDS:
            raise ValueError("CSV headers do not match the documented schema")
        stored = list(reader)
    if len(stored) != len(rows):
        raise ValueError("CSV row count differs from the expected table")
    for record, (n, z, score) in zip(stored, rows):
        if record["tests"] != n:
            raise ValueError(f"Unexpected test count: {record['tests']!r}")
        try:
            stored_z = float(record["mean_z"])
            stored_score = float(record["mean_score_sd16"])
        except (TypeError, KeyError) as error:
            raise ValueError(f"CSV n={n}: missing numeric value") from error
        if not _finite(stored_z) or not _finite(stored_score):
            raise ValueError(f"CSV n={n}: non-finite numeric value")
        check_close(stored_z, z, f"CSV n={n}, mean z")
        check_close(stored_score, score,
                    f"CSV n={n}, mean SD-16 score")


@deal.pre(_valid_rows)
@deal.post(lambda result: result is None)
@deal.has("read", "stdout")
@deal.raises(OSError, ValueError)
@deal.ensure(lambda rows, result: _valid_rows(rows))
def verify_source_values(rows: list[tuple[str, float, float]]) -> None:
    if not TEX_PATH.exists():
        print("XeLaTeX source not present; source-value check skipped.")
        return
    source = TEX_PATH.read_text(encoding="utf-8")
    table_rows = re.findall(
        r"(?m)^\s*(.*?)\s*&\s*(\d+\.\d+)\s*&\s*(\d+\.\d+)\s*\\\\\s*$",
        source,
    )
    if len(table_rows) != len(rows):
        raise ValueError("XeLaTeX table row count differs from the expected table")
    for (label, displayed_z, displayed_score), (n, z, score) in zip(table_rows, rows):
        expected_label = r"Limit as \(n\) increases" if n == "infinity" else f"{int(n):,}"
        if label != expected_label or displayed_z != f"{z:.4f}" or displayed_score != f"{score:.2f}":
            raise ValueError(f"XeLaTeX table row for n={n} does not match the calculation")


@deal.post(lambda result: result is None)
@deal.raises(ValueError)
@deal.ensure(lambda result: math.isclose(Q, 4.753424308822899, rel_tol=0, abs_tol=1e-9))
@deal.pre(lambda: _finite(Q) and 0 < Q <= 10)
@deal.pre(lambda: _finite(RHO) and 0 < RHO < 1)
def verify_examples() -> None:
    check_close(Q, 4.753424308822899, "upper-tail normal quantile")
    check_close(float(norm.sf(Q)), 1e-6, "quantile's upper-tail probability")

    n = 3
    mean_z = (160 - 100) * 0.0625
    composite_z = _positive_ratio(mean_z, math.sqrt(variance_factor(n, RHO)))
    check_close(100 + 16 * composite_z, 170.06490497453706,
                "three-test worked composite")

    # This factor-model illustration assumes independent Gaussian residuals.
    reliability = _positive_ratio(n * RHO, 1 + (n - 1) * RHO)
    latent_mean = math.sqrt(reliability) * Q
    latent_sd = math.sqrt(_positive_ratio(1 - RHO, 1 + (n - 1) * RHO))
    check_close(100 + 16 * latent_mean, 168.7941450256873,
                "latent-factor conditional mean on the SD-16 scale")
    check_close(16 * latent_sd, 6.822422923379534,
                "latent-factor conditional standard deviation")

    higher_rho_z = mean_threshold(n, 0.90, Q)
    check_close(100 + 16 * higher_rho_z, 173.47590665989093,
                "three-test correlation sensitivity example")


@deal.post(lambda result: result is None)
@deal.has("read", "write", "stdout", "stderr", "syscall")
@deal.raises(OSError, ValueError, csv.Error, SystemExit)
@deal.pre(lambda: isinstance(sys.argv, list))
@deal.pre(lambda: all(isinstance(argument, str) for argument in sys.argv))
def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true",
                        help="regenerate data/thresholds.csv before checking")
    args = parser.parse_args()
    rows = thresholds()
    if args.write:
        write_csv(rows)
        print(f"Wrote {CSV_PATH.relative_to(ROOT)}")
    verify_csv(rows)
    verify_examples()
    verify_source_values(rows)
    print(f"Verified {len(rows)} table rows and the worked examples.")
    print(f"One-in-a-million upper-tail normal quantile: {Q:.12f}")


if __name__ == "__main__":
    deal.enable(warn=False)
    main()
