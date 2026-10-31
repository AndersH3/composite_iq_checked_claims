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


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("simulation", type=Path)
    parser.add_argument("--json-output", type=Path)
    args = parser.parse_args()
    text = args.simulation.read_text()
    seed = int(re.search(r"seed=(\d+)", text).group(1))
    rows = list(csv.DictReader(line for line in text.splitlines() if not line.startswith("#")))
    trials = int(rows[0]["trials"])
    if any(int(row["trials"]) != trials for row in rows):
        raise ValueError("Trials differ between rows")
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
    from scipy.stats import norm
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
              "input_sha256": hashlib.sha256(args.simulation.read_bytes()).hexdigest(),
              "replay_source_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              "scope": "Deterministic implementation replay, not a proof of stochastic independence or model validity."}
    if args.json_output:
        args.json_output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, sort_keys=True))


if __name__ == "__main__":
    main()
