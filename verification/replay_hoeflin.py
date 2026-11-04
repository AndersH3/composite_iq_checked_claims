#!/usr/bin/env python3
"""Independently replay the recorded Ada generator and simulation count cells.

Agreement checks the implementation and recorded seed, not random independence
or the empirical truth of a Gaussian ability model.
"""
import argparse
import csv
import hashlib
import json
import math
from pathlib import Path
import re

import numpy as np
from scipy.stats import norm
import sys

import deal


@deal.pre(lambda simulation: isinstance(simulation, Path))
@deal.post(lambda result: 2 <= result['trials_per_case'] <= 100000000 and 0 <= result['seed'] < 2 ** 64 and (result['all_tail_counts_match'] is True) and (result['mean_and_variance_agree'] is True) and (len(result['input_sha256']) == len(result['replay_source_sha256']) == 64))
@deal.post(lambda result: result['cases'] == 8)
@deal.raises(OSError, ValueError, KeyError, TypeError, MemoryError, OverflowError)
@deal.has("read")
def replay(simulation: Path) -> dict:
    text = simulation.read_text()
    seed_match = re.search(r"seed=(\d+)", text)
    if seed_match is None:
        raise ValueError("Simulation seed is missing")
    seed = int(seed_match.group(1))
    if not 0 <= seed < 2**64:
        raise ValueError("Seed is outside the Ada unsigned-64 domain")
    rows = list(csv.DictReader(line for line in text.splitlines() if not line.startswith("#")))
    if [int(row["tests"]) for row in rows] != [1, 2, 3, 4, 5, 10, 100, 1000]:
        raise ValueError("Simulation requires the eight specified test-count cases")
    trials = int(rows[0]["trials"])
    if not 2 <= trials <= 100_000_000 or any(int(row["trials"]) != trials for row in rows):
        raise ValueError("Invalid or inconsistent trial counts")
    for row in rows:
        if not all(math.isfinite(float(row[key])) for key in ("mean_composite_z", "variance_composite_z")):
            raise ValueError("Non-finite simulation summary")
        counts = [int(row[key]) for key in ("above_rare", "above3", "above2")]
        if not 0 <= counts[0] <= counts[1] <= counts[2] <= trials:
            raise ValueError("Invalid nested tail counts")
    state = seed
    mask = 2**64 - 1
    x, y = np.empty(trials), np.empty(trials)
    for i in range(trials):
        state = (state * 6364136223846793005 + 1442695040888963407) & mask
        u = ((state >> 12) + 0.5) * 2**-52
        state = (state * 6364136223846793005 + 1442695040888963407) & mask
        v = ((state >> 12) + 0.5) * 2**-52
        radius, angle = math.sqrt(-2 * math.log(u)), 2 * math.pi * v
        x[i], y[i] = radius * math.cos(angle), radius * math.sin(angle)
    q = norm.isf(1e-6)
    for row in rows:
        n = int(row["tests"])
        factor = (1000 + 600*(n-1)) / (1000*n)
        z = (math.sqrt(.6)*x + math.sqrt(.4/n)*y) / math.sqrt(factor)
        for key, threshold in (("above2", 2), ("above3", 3), ("above_rare", q)):
            count = int(np.count_nonzero(z > threshold))
            if count != int(row[key]):
                raise ValueError(f"Replay differs for n={n}, {key}: {count} != {row[key]}")
        if abs(float(np.mean(z)) - float(row["mean_composite_z"])) > 2e-12:
            raise ValueError("Replayed mean differs beyond printed precision")
        if abs(float(np.var(z, ddof=1)) - float(row["variance_composite_z"])) > 2e-12:
            raise ValueError("Replayed variance differs beyond printed precision")
    result = {"cases": len(rows), "trials_per_case": trials, "seed": seed,
              "all_tail_counts_match": True, "mean_and_variance_agree": True,
              "input_sha256": hashlib.sha256(simulation.read_bytes()).hexdigest(),
              "replay_source_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              "scope": "Deterministic implementation replay, not a proof of stochastic independence or model validity."}
    return result


@deal.post(lambda result: result is None)
@deal.raises(SystemExit, OSError, ValueError, KeyError, TypeError, MemoryError, OverflowError)
@deal.has("read", "write", "stdout", "stderr")
@deal.pre(lambda: isinstance(sys.argv, list))
@deal.pre(lambda: all(isinstance(argument, str) for argument in sys.argv))
def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("simulation", type=Path)
    parser.add_argument("--json-output", type=Path)
    args = parser.parse_args()
    result = replay(args.simulation)
    if args.json_output:
        args.json_output.parent.mkdir(parents=True, exist_ok=True)
        args.json_output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, sort_keys=True))
    return None


if __name__ == "__main__":
    deal.enable(warn=False)
    main()
