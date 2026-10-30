#!/usr/bin/env python3
"""Recompute the report's conditional normal-model results and verify its data."""

import argparse
import csv
import math
from pathlib import Path
import re

from scipy.stats import norm


ROOT = Path(__file__).resolve().parents[1]
CSV_PATH = ROOT / "data" / "thresholds.csv"
TEX_PATH = ROOT / "composite_iq_analysis.tex"
RHO = 0.60
Q = float(norm.isf(1e-6))
COUNTS = (1, 2, 3, 4, 5, 10, 100, 1000)
FIELDS = ("tests", "mean_z", "mean_score_sd16")


def thresholds():
    rows = []
    for n in COUNTS:
        z = Q * math.sqrt(RHO + (1 - RHO) / n)
        rows.append((str(n), z, 100 + 16 * z))
    z_limit = Q * math.sqrt(RHO)
    rows.append(("infinity", z_limit, 100 + 16 * z_limit))
    return rows


def check_close(actual, expected, label):
    if not math.isclose(actual, expected, rel_tol=0, abs_tol=1e-9):
        raise ValueError(f"{label}: got {actual!r}, expected {expected!r}")


def write_csv(rows):
    CSV_PATH.parent.mkdir(parents=True, exist_ok=True)
    with CSV_PATH.open("w", newline="", encoding="utf-8") as stream:
        writer = csv.writer(stream)
        writer.writerow(FIELDS)
        for n, z, score in rows:
            writer.writerow((n, f"{z:.12f}", f"{score:.12f}"))


def verify_csv(rows):
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
        check_close(float(record["mean_z"]), z, f"CSV n={n}, mean z")
        check_close(float(record["mean_score_sd16"]), score,
                    f"CSV n={n}, mean SD-16 score")


def verify_source_values(rows):
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


def verify_examples():
    check_close(Q, 4.753424308822899, "upper-tail normal quantile")
    check_close(float(norm.sf(Q)), 1e-6, "quantile's upper-tail probability")

    n = 3
    mean_z = (160 - 100) / 16
    composite_z = mean_z / math.sqrt(RHO + (1 - RHO) / n)
    check_close(100 + 16 * composite_z, 170.06490497453706,
                "three-test worked composite")

    # This factor-model illustration assumes independent Gaussian residuals.
    reliability = n * RHO / (1 + (n - 1) * RHO)
    latent_mean = math.sqrt(reliability) * Q
    latent_sd = math.sqrt((1 - RHO) / (1 + (n - 1) * RHO))
    check_close(100 + 16 * latent_mean, 168.7941450256873,
                "latent-factor conditional mean on the SD-16 scale")
    check_close(16 * latent_sd, 6.822422923379534,
                "latent-factor conditional standard deviation")

    higher_rho_z = Q * math.sqrt(0.90 + 0.10 / n)
    check_close(100 + 16 * higher_rho_z, 173.47590665989093,
                "three-test correlation sensitivity example")


def main():
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
    main()
