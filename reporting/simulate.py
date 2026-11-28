#!/usr/bin/env python3
"""Dask-native simulation, analysis, asset and XeLaTeX task graphs.

The scalable default uses one Dask task per seeded sample block and returns
compact numerical statistics rather than moving full samples between workers.
The retained reference Dask Array engine supports historical cross-checks;
report production and reference calculations also remain in the task graph.
no retired native implementation or historical CSV input is required.
Small scalar reference calculations reuse the maintained SciPy code inside
Dask delayed tasks. No expensive computation happens during graph creation.
"""
# Dask distributed workers share their process with an asynchronous socket
# event loop. Deal's runtime offline checker monkeypatches socket process-wide;
# permitting the worker transport avoids breaking unrelated scheduler I/O.
# Source-level numeric invariants and exception contracts remain in force.
import argparse
import csv
import importlib.metadata
import json
import os
from pathlib import Path
import runpy
import subprocess
from subprocess import CalledProcessError, TimeoutExpired
import sys
import math
import time

import dask
import dask.array as da
from dask.delayed import Delayed
from dask.multiprocessing import RemoteException
import deal
from scipy import optimize, stats

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from library.python.statistics import moment_result, event_result, pool_rows
from reporting.assets import write_assets
from reporting.provenance import digest, dump
from reporting.block_simulations import (
    COUNTS, hoeflin_block, towers_block, sequential_block, finish_moment, finish_event,
)

PROJECTS = ("hoeflin-ferguson", "towers-multiple-test-admissions", "sequential-conditional-means")
SEEDS = (20261114, 20261115, 20261116, 20261117,
         20261118, 20261119, 20261120, 20261121)
DEFAULT_TRIALS = 5_000_000
DEFAULT_CHUNK = 500_000
DEFAULT_REPLICATES = 8


@deal.pre(lambda project: project in PROJECTS)
@deal.post(lambda result: isinstance(result, dict) and {"project", "sources", "cases"} == result.keys())
@deal.post(lambda result: isinstance(result["cases"], list) and isinstance(result["sources"], list))
@deal.post(lambda result: len(result["cases"]) == (5 if result["project"] == PROJECTS[1] else 0))
@deal.post(lambda result: len(result["sources"]) == (1 if result["project"] == PROJECTS[1] else 0))
@deal.ensure(lambda project, result: result["project"] == project)
@deal.post(lambda result: all(len(row["sha256"]) == 64 for row in result["sources"]))
@deal.post(lambda result: all(isinstance(row["path"], str) and not row["path"].startswith("/") for row in result["sources"]))
@deal.post(lambda result: len({row["path"] for row in result["sources"]}) == len(result["sources"]))
@deal.post(lambda result: len({row["case_index"] for row in result["cases"]}) == len(result["cases"]))
@deal.raises(OSError, ValueError, TypeError, ImportError)
@deal.has("network", "read", "import")
@deal.post(lambda result: all(0 < case["p_a"] < 1 and 0 < case["p_b"] < 1 for case in result["cases"]))
@deal.post(lambda result: all(type(case["case_index"]) is int and 1 <= case["case_index"] <= 5 for case in result["cases"]))
@deal.post(lambda result: all(source["path"].endswith(".py") for source in result["sources"]))
def reference_data(project):
    """Compute numerical reference cases without importing a retired simulator.

    SciPy/NumPy and the maintained Python calculation modules own the
    reference quadrature. Sources are SHA-256 recorded for reproducibility.
    """
    sources = []
    cases = []
    if project == PROJECTS[1]:
        script_path = ROOT.joinpath("analyses", project, "scripts", "verify_calculations.py")
        library = runpy.run_path(str(script_path))
        sources.append({"path": script_path.relative_to(ROOT).as_posix(), "sha256": digest(script_path)})
        # A fixed nominal 2% threshold is not the same as an OR rule that
        # admits 2% overall. Solve the latter against the reference integral.
        cutoff = optimize.brentq(lambda q: 2 * stats.norm.sf(q) - library["joint_tail"](q, q, .7) - .02, 1.5, 3.0, xtol=1e-13)
        for index, ((name, p_a, p_b), label) in enumerate(zip(library["CASES"], ("E2", "E0.1", "Rare", "Mixed"), strict=True), 1):
            a, b = float(stats.norm.isf(p_a)), float(stats.norm.isf(p_b))
            cases.append({"case_index": index, "case": name, "label": label, "p_a": p_a, "p_b": p_b,
                          "cutoff_a": a, "cutoff_b": b, "theory_joint": library["joint_tail"](a, b, .7)})
        marginal = float(stats.norm.sf(cutoff))
        cases.append({"case_index": 5, "case": "calibrated_or", "label": "Calibrated", "p_a": marginal, "p_b": marginal,
                      "cutoff_a": cutoff, "cutoff_b": cutoff, "theory_joint": library["joint_tail"](cutoff, cutoff, .7)})
    return {"project": project, "sources": sources, "cases": cases}


@deal.pre(lambda config: isinstance(config, dict) and {"trials", "chunk", "seeds"} <= config.keys())
@deal.pre(lambda config: type(config["trials"]) is int and 2 <= config["trials"] <= 1_000_000)
@deal.pre(lambda config: type(config["chunk"]) is int and 1 <= config["chunk"] <= config["trials"])
@deal.pre(lambda config: bool(config["seeds"]) and len(set(config["seeds"])) == len(config["seeds"]) and all(type(seed) is int and 0 <= seed < 2 ** 32 for seed in config["seeds"]))
@deal.ensure(lambda config, result: isinstance(result, list) and bool(result) and all(isinstance(item, Delayed) for item in result))
@deal.ensure(lambda config, result: len(result) == len(config["seeds"]) * len(COUNTS))
@deal.has("network", "read", "import", "random")
@deal.raises(ValueError, TypeError, OverflowError, NotImplementedError)
@deal.pre(lambda config: all(type(seed) is int and 0 <= seed < 2 ** 32 for seed in config["seeds"]))
@deal.pre(lambda config: 1 <= len(config["seeds"]) <= len(SEEDS))
@deal.ensure(lambda config, result: all(isinstance(row.key, str) and bool(row.key) for row in result))
@deal.ensure(lambda config, result: len({row.key for row in result}) == len(result))
@deal.ensure(lambda config, result: all(bool(row.dask) for row in result))
@deal.ensure(lambda config, result: len(result) % len(COUNTS) == 0)
@deal.ensure(lambda config, result: len(result) >= len(COUNTS))
def graph_hoeflin(config):
    """Construct the exact Gaussian aggregate law with common random numbers.

    Under joint normality, a mean of N residuals has the same distribution as
    E/sqrt(N). This permits N=1000 without materializing a billion individual
    tests. Shared G/E couples the eight marginal experiments; the eight rows
    are not eight independent replications of rare-tail evidence.
    """
    rows = []
    n, chunk = config["trials"], config["chunk"]
    rare_threshold = da.from_delayed(dask.delayed(stats.norm.isf)(1e-6), shape=(), dtype=float)
    for replicate, seed in enumerate(config["seeds"], 1):
        generator = da.random.default_rng(seed)
        latent = generator.standard_normal(n, chunks=chunk)
        residual = generator.standard_normal(n, chunks=chunk)
        for count in COUNTS:
            variance = .6 + da.divide(0.4, count)
            mean_score = da.sqrt(.6) * latent + da.sqrt(da.divide(0.4, count)) * residual
            composite = da.divide(mean_score, da.sqrt(variance))
            estimate = da.divide(da.sqrt(0.6) * mean_score, variance)
            meta = {"project": PROJECTS[0], "replicate": replicate, "seed": seed, "n_samples": n,
                    "n": count, "theory_mean": 0.0, "theory_variance": 1.0,
                    "theory_sd": variance ** .5, "theory_mse": 1 - da.divide(0.6, variance)}
            counts = ((composite > 2).sum(), (composite > 3).sum(), (composite > rare_threshold).sum())
            rows.append(dask.delayed(moment_result)(meta, composite.mean(), composite.var(ddof=1), ((estimate - latent) ** 2).mean(), counts))
    return rows


@deal.pre(lambda config, reference: isinstance(config, dict) and {"trials", "chunk", "seeds"} <= config.keys())
@deal.pre(lambda config, reference: type(config["trials"]) is int and 2 <= config["trials"] <= 1_000_000)
@deal.pre(lambda config, reference: type(config["chunk"]) is int and 1 <= config["chunk"] <= config["trials"])
@deal.pre(lambda config, reference: bool(config["seeds"]) and len(set(config["seeds"])) == len(config["seeds"]))
@deal.pre(lambda config, reference: isinstance(reference, Delayed))
@deal.ensure(lambda config, reference, result: isinstance(result, list) and all(isinstance(item, Delayed) for item in result))
@deal.ensure(lambda config, reference, result: len(result) == 5 * len(config["seeds"]))
@deal.raises(ValueError, TypeError, OverflowError, NotImplementedError)
@deal.has("network", "read", "import", "random")
@deal.pre(lambda config, reference: all(type(seed) is int and 0 <= seed < 2 ** 32 for seed in config["seeds"]))
@deal.pre(lambda config, reference: 1 <= len(config["seeds"]) <= len(SEEDS))
@deal.ensure(lambda config, reference, result: all(isinstance(row.key, str) and bool(row.key) for row in result))
@deal.ensure(lambda config, reference, result: len({row.key for row in result}) == len(result))
@deal.ensure(lambda config, reference, result: len(result) % 5 == 0)
@deal.ensure(lambda config, reference, result: bool(result))
def graph_towers(config, reference):
    """Count disjoint event cells on shared correlated Dask random arrays."""
    rows = []
    n, chunk = config["trials"], config["chunk"]
    for replicate, seed in enumerate(config["seeds"], 1):
        generator = da.random.default_rng(seed + 1000)
        x = generator.standard_normal(n, chunks=chunk)
        y = .7 * x + da.sqrt(1 - .7 ** 2) * generator.standard_normal(n, chunks=chunk)
        for index in range(5):
            case = reference["cases"][index]
            # Scalar thresholds remain lazy graph dependencies of every event
            # classification; reading/integrating references is a Dask task.
            a = da.from_delayed(case["cutoff_a"], shape=(), dtype=float)
            b = da.from_delayed(case["cutoff_b"], shape=(), dtype=float)
            above_a, above_b = x > a, y > b
            counts = ((~above_a & ~above_b).sum(), (above_a & ~above_b).sum(),
                      (~above_a & above_b).sum(), (above_a & above_b).sum())
            meta = {"project": PROJECTS[1], "replicate": replicate, "seed": seed + 1000, "n_samples": n}
            # Dask delayed resolves nested mappings, preserving a single
            # shared reference task rather than recomputing quadrature.
            meta.update({key: case[key] for key in ("case_index", "label", "p_a", "p_b", "theory_joint", "cutoff_a", "cutoff_b")})
            rows.append(dask.delayed(event_result)(meta, counts))
    return rows


@deal.pre(lambda config: isinstance(config, dict) and {"trials", "chunk", "seeds"} <= config.keys())
@deal.pre(lambda config: type(config["trials"]) is int and 2 <= config["trials"] <= 1_000_000)
@deal.pre(lambda config: type(config["chunk"]) is int and 1 <= config["chunk"] <= config["trials"])
@deal.pre(lambda config: bool(config["seeds"]) and len(set(config["seeds"])) == len(config["seeds"]))
@deal.ensure(lambda config, result: isinstance(result, list) and all(isinstance(item, Delayed) for item in result))
@deal.ensure(lambda config, result: len(result) == 24 * len(config["seeds"]))
@deal.raises(ValueError, TypeError, OverflowError, NotImplementedError)
@deal.has("network", "read", "import", "random")
@deal.pre(lambda config: all(type(seed) is int and 0 <= seed < 2 ** 32 for seed in config["seeds"]))
@deal.pre(lambda config: 1 <= len(config["seeds"]) <= len(SEEDS))
@deal.ensure(lambda config, result: all(isinstance(row.key, str) and bool(row.key) for row in result))
@deal.ensure(lambda config, result: len({row.key for row in result}) == len(result))
@deal.ensure(lambda config, result: len(result) % 24 == 0)
@deal.ensure(lambda config, result: bool(result))
@deal.ensure(lambda config, result: len(result) >= 24)
def graph_sequential(config):
    """Generate full finite test/future vectors, plus limiting latent laws.

    Conditional sampling draws the posterior common factor directly. Rejecting
    unconditioned draws until r exact IQ values are 150 would fail for a
    continuous model. Finite vectors supply an independent implementation of
    a separate implementation using maintained Gaussian algebra.
    """
    rows = []
    n, chunk = config["trials"], config["chunk"]
    for replicate, seed in enumerate(config["seeds"], 1):
        for r in (1, 2, 3):
            generator = da.random.default_rng(seed + 2000 + 100 * r)
            latent = generator.standard_normal(n, chunks=chunk)
            population_noise = generator.standard_normal((n, r + 10), chunks=(chunk, r + 10))
            future_noise = generator.standard_normal((n, 10), chunks=(chunk, 10))
            dr = 1 + (r - 1) * .6
            posterior_mean, posterior_sd = da.divide(r * 0.6 ** 0.5 * da.divide(10, 3), dr), (da.divide(0.4, dr)) ** .5
            posterior = posterior_mean + posterior_sd * latent
            for k in (1, 2, 10, 0):
                total = r + k
                if k:
                    population = da.sqrt(.6) * latent + da.sqrt(.4) * population_noise[:, :total].mean(axis=1)
                    conditional = da.divide(r * da.divide(10, 3) + k * da.sqrt(0.6) * posterior + da.sqrt(0.4) * future_noise[:, :k].sum(axis=1), total)
                    dn = 1 + (total - 1) * .6
                    theory_mean = da.divide(r * dn * da.divide(10, 3), total * dr)
                    popvar, condvar = da.divide(dn, total), da.divide(k * 0.4 * dn, total * total * dr)
                else:
                    population, conditional = da.sqrt(.6) * latent, da.sqrt(.6) * posterior
                    theory_mean, popvar, condvar = da.divide(r * 0.6 * da.divide(10, 3), dr), .6, da.divide(0.24, dr)
                for mode, values, mean, variance in (("population", population, 0.0, popvar), ("conditional", conditional, theory_mean, condvar)):
                    meta = {"project": PROJECTS[2], "replicate": replicate, "seed": seed + 2000 + 100 * r,
                            "n_samples": n, "r": r, "k": k, "mode": mode + ("_limit" if k == 0 else ""),
                            "theory_mean": mean, "theory_variance": variance}
                    rows.append(dask.delayed(moment_result)(meta, values.mean(), values.var(ddof=1)))
    return rows




@deal.pre(lambda trials, chunk: type(trials) is int and 2 <= trials <= 100_000_000)
@deal.pre(lambda trials, chunk: type(chunk) is int and 1 <= chunk <= 2_000_000)
@deal.pre(lambda trials, chunk: (trials + chunk - 1) // chunk <= 1024)
@deal.post(lambda result: isinstance(result, list) and bool(result))
@deal.post(lambda result: all(type(value) is int and value >= 1 for value in result))
@deal.ensure(lambda trials, chunk, result: sum(result) == trials)
@deal.ensure(lambda trials, chunk, result: max(result) <= chunk)
@deal.ensure(lambda trials, chunk, result: len(result) == (trials + chunk - 1) // chunk)
@deal.ensure(lambda trials, chunk, result: all(value == chunk for value in result[:-1]))
@deal.ensure(lambda trials, chunk, result: result[-1] == trials - chunk * (len(result) - 1))
@deal.ensure(lambda trials, chunk, result: all(value <= trials for value in result))
@deal.raises()
@deal.has("network")
@deal.ensure(lambda trials, chunk, result: 1 <= len(result) <= 1024)
@deal.ensure(lambda trials, chunk, result: 1 <= result[-1] <= min(trials, chunk))
def block_sizes(trials, chunk):
    """Partition a single replicate into bounded-size, ordered sample blocks.

    Every sample contributes to exactly one block. Block index, not task
    completion order, addresses each independently seeded PRNG substream.
    """
    return [min(chunk, trials - start) for start in range(0, trials, chunk)]


@deal.pre(lambda config: isinstance(config, dict) and {"trials", "chunk", "seeds"} <= config.keys())
@deal.pre(lambda config: type(config["trials"]) is int and 2 <= config["trials"] <= 100_000_000)
@deal.pre(lambda config: type(config["chunk"]) is int and 1 <= config["chunk"] <= 2_000_000)
@deal.pre(lambda config: bool(config["seeds"]) and len(set(config["seeds"])) == len(config["seeds"]))
@deal.pre(lambda config: all(type(seed) is int and 0 <= seed < 2**32 for seed in config["seeds"]))
@deal.pre(lambda config: (config["trials"] + config["chunk"] - 1) // config["chunk"] <= 1024)
@deal.ensure(lambda config, result: isinstance(result, list) and len(result) == len(config["seeds"]) * len(COUNTS))
@deal.ensure(lambda config, result: all(isinstance(row, Delayed) for row in result))
@deal.ensure(lambda config, result: len({row.key for row in result}) == len(result))
@deal.ensure(lambda config, result: all(row.key for row in result))
@deal.raises(ValueError, TypeError, OverflowError, ZeroDivisionError, KeyError, NotImplementedError)
@deal.has("network", "import")
@deal.ensure(lambda config, result: len(result) >= len(COUNTS))
@deal.ensure(lambda config, result: all(isinstance(row.key, str) for row in result))
@deal.ensure(lambda config, result: len(result) % len(COUNTS) == 0)
def graph_hoeflin_blocks(config):
    """Create one Dask worker task per common-random-number block and replicate.

    A block evaluates all eight composite sizes, returns centered moments,
    MSEs and nested exceedance counts. Only scalar statistics cross worker
    boundaries; no per-sample or per-case scalar reduction is scheduled.
    """
    rows = []
    sizes = block_sizes(config["trials"], config["chunk"])
    cutoff = float(stats.norm.isf(1e-6))
    for replicate, seed in enumerate(config["seeds"], 1):
        blocks = [dask.delayed(hoeflin_block)(seed, index, size, cutoff)
                  for index, size in enumerate(sizes)]
        for count in COUNTS:
            variance = .6 + .4 / count
            meta = {"project": PROJECTS[0], "replicate": replicate, "seed": seed,
                    "n_samples": config["trials"], "n": count, "theory_mean": 0.0,
                    "theory_variance": 1.0, "theory_sd": math.sqrt(variance),
                    "theory_mse": 1.0 - .6 / variance}
            rows.append(dask.delayed(finish_moment)(meta, blocks, count))
    return rows


@deal.pre(lambda config, reference: isinstance(config, dict) and {"trials", "chunk", "seeds"} <= config.keys())
@deal.pre(lambda config, reference: isinstance(reference, Delayed))
@deal.pre(lambda config, reference: type(config["trials"]) is int and 2 <= config["trials"] <= 100_000_000)
@deal.pre(lambda config, reference: type(config["chunk"]) is int and 1 <= config["chunk"] <= 2_000_000)
@deal.pre(lambda config, reference: bool(config["seeds"]) and len(set(config["seeds"])) == len(config["seeds"]))
@deal.pre(lambda config, reference: (config["trials"] + config["chunk"] - 1) // config["chunk"] <= 1024)
@deal.ensure(lambda config, reference, result: isinstance(result, list) and len(result) == 5 * len(config["seeds"]))
@deal.ensure(lambda config, reference, result: all(isinstance(row, Delayed) for row in result))
@deal.ensure(lambda config, reference, result: len({row.key for row in result}) == len(result))
@deal.ensure(lambda config, reference, result: all(row.key for row in result))
@deal.raises(ValueError, TypeError, OverflowError, KeyError, NotImplementedError)
@deal.has("network", "import")
@deal.pre(lambda config, reference: all(type(seed) is int and 0 <= seed < 2**32 for seed in config["seeds"]))
@deal.ensure(lambda config, reference, result: all(isinstance(row.key, str) for row in result))
@deal.ensure(lambda config, reference, result: len(result) % 5 == 0)
def graph_towers_blocks(config, reference):
    """Share one lazy cutoff reference and one Gaussian pair across five rules."""
    rows = []
    sizes = block_sizes(config["trials"], config["chunk"])
    for replicate, seed in enumerate(config["seeds"], 1):
        blocks = [dask.delayed(towers_block)(seed + 1000, index, size, reference)
                  for index, size in enumerate(sizes)]
        meta = {"project": PROJECTS[1], "replicate": replicate,
                "seed": seed + 1000, "n_samples": config["trials"]}
        for index in range(1, 6):
            rows.append(dask.delayed(finish_event)(meta, blocks, index, reference))
    return rows


@deal.pre(lambda config: isinstance(config, dict) and {"trials", "chunk", "seeds"} <= config.keys())
@deal.pre(lambda config: type(config["trials"]) is int and 2 <= config["trials"] <= 100_000_000)
@deal.pre(lambda config: type(config["chunk"]) is int and 1 <= config["chunk"] <= 2_000_000)
@deal.pre(lambda config: bool(config["seeds"]) and len(set(config["seeds"])) == len(config["seeds"]))
@deal.pre(lambda config: all(type(seed) is int and 0 <= seed < 2**32 for seed in config["seeds"]))
@deal.pre(lambda config: (config["trials"] + config["chunk"] - 1) // config["chunk"] <= 1024)
@deal.ensure(lambda config, result: isinstance(result, list) and len(result) == 24 * len(config["seeds"]))
@deal.ensure(lambda config, result: all(isinstance(row, Delayed) for row in result))
@deal.ensure(lambda config, result: len({row.key for row in result}) == len(result))
@deal.ensure(lambda config, result: all(row.key for row in result))
@deal.raises(ValueError, TypeError, OverflowError, ZeroDivisionError, KeyError, NotImplementedError)
@deal.has("network", "import")
@deal.ensure(lambda config, result: len(result) >= 24)
@deal.ensure(lambda config, result: all(isinstance(row.key, str) for row in result))
@deal.ensure(lambda config, result: len(result) % 24 == 0)
def graph_sequential_blocks(config):
    """Generate finite score vectors within each worker, never across workers.

    All four k configurations and both population/conditional modes reuse
    each block's latent and Gaussian residual draws. The last configuration
    samples the separately derived limiting law, not an empty test battery.
    """
    rows = []
    sizes = block_sizes(config["trials"], config["chunk"])
    for replicate, seed in enumerate(config["seeds"], 1):
        for r in (1, 2, 3):
            block_seed = seed + 2000 + 100 * r
            blocks = [dask.delayed(sequential_block)(block_seed, index, size, r)
                      for index, size in enumerate(sizes)]
            dr = 1 + (r - 1) * .6
            for k in (1, 2, 10, 0):
                if k:
                    total = r + k
                    dn = 1 + (total - 1) * .6
                    theory_mean = r * dn * (10.0 / 3.0) / (total * dr)
                    popvar = dn / total
                    condvar = k * .4 * dn / (total * total * dr)
                else:
                    theory_mean = r * .6 * (10.0 / 3.0) / dr
                    popvar, condvar = .6, .24 / dr
                for mode, mean, variance in (("population", 0.0, popvar),
                                             ("conditional", theory_mean, condvar)):
                    meta = {"project": PROJECTS[2], "replicate": replicate,
                            "seed": block_seed, "n_samples": config["trials"],
                            "r": r, "k": k, "mode": mode + ("_limit" if k == 0 else ""),
                            "theory_mean": mean, "theory_variance": variance}
                    rows.append(dask.delayed(finish_moment)(meta, blocks, (k, mode)))
    return rows


@deal.pre(lambda config, task_count: isinstance(config, dict) and {"trials", "chunk", "seeds", "workers", "engine", "scheduler"} <= config.keys())
@deal.pre(lambda config, task_count: type(task_count) is int and task_count > 0)
@deal.pre(lambda config, task_count: type(config["trials"]) is int and config["trials"] >= 2)
@deal.pre(lambda config, task_count: type(config["chunk"]) is int and config["chunk"] >= 1)
@deal.pre(lambda config, task_count: isinstance(config["seeds"], list) and bool(config["seeds"]))
@deal.pre(lambda config, task_count: type(config["workers"]) is int and 1 <= config["workers"] <= 32)
@deal.pre(lambda config, task_count: config["engine"] in ("blocks", "arrays"))
@deal.pre(lambda config, task_count: config["scheduler"] in ("processes", "distributed", "single-threaded"))
@deal.ensure(lambda config, task_count, result: result["graph_tasks"] == task_count)
@deal.ensure(lambda config, task_count, result: result["samples_per_case"] == config["trials"] * len(config["seeds"]))
@deal.ensure(lambda config, task_count, result: result["blocks_per_replicate"] == (config["trials"] + config["chunk"] - 1) // config["chunk"])
@deal.ensure(lambda config, task_count, result: result["estimated_gaussian_input_bytes_per_sequential_block"] == 8 * config["chunk"] *  (13 + 10 + 1))
@deal.ensure(lambda config, task_count, result: result["expected_rare_events_per_case"] == result["samples_per_case"] / 1_000_000)
@deal.ensure(lambda config, task_count, result: result["relative_poisson_noise_at_rare_event"] > 0)
@deal.post(lambda result: result["graph_tasks"] > 0 and result["blocks_per_replicate"] > 0)
@deal.raises(ZeroDivisionError)
@deal.has("network")
def execution_plan(config, task_count):
    """Report actual graph size and raw input allocation, without executing.

    Memory is ONLY raw Gaussian input arrays for the largest sequential
    block (r=3): it is not a peak-RSS prediction. Working arrays, the Dask
    scheduler, libraries and concurrent blocks add memory. The rare-event
    noise estimate is a Poisson heuristic, not a measured standard error.
    """
    samples = config["trials"] * len(config["seeds"])
    return {
        "config": config,
        "graph_tasks": task_count,
        "blocks_per_replicate": (config["trials"] + config["chunk"] - 1) // config["chunk"],
        "samples_per_case": samples,
        "estimated_gaussian_input_bytes_per_sequential_block": 8 * config["chunk"] * (13 + 10 + 1),
        "expected_rare_events_per_case": samples / 1_000_000,
        "relative_poisson_noise_at_rare_event": (samples / 1_000_000) ** -0.5,
        "notes": ("Raw block bytes exclude intermediate arrays, memory overlap, "
                  "scheduler overhead and PDF production; measure peak RSS on target hardware.")
    }

@deal.pre(lambda project, rows, reference, config: project in PROJECTS)
@deal.pre(lambda project, rows, reference, config: isinstance(rows, list) and bool(rows))
@deal.pre(lambda project, rows, reference, config: isinstance(reference, dict) and reference["project"] == project)
@deal.ensure(lambda project, rows, reference, config, result: result["project"] == project)
@deal.post(lambda result: isinstance(result, dict) and bool(result["files"]))
@deal.raises(OSError, ValueError, TypeError, KeyError, OverflowError, csv.Error)
@deal.has("network", "read", "write")
@deal.pre(lambda project, rows, reference, config: isinstance(config, dict) and {"trials", "chunk", "seeds"} <= config.keys())
@deal.pre(lambda project, rows, reference, config: all(isinstance(row, dict) and row["project"] == project for row in rows))
@deal.pre(lambda project, rows, reference, config: bool(config["seeds"]) and len(set(config["seeds"])) == len(config["seeds"]))
@deal.ensure(lambda project, rows, reference, config, result: result["n_rows"] > 0)
@deal.ensure(lambda project, rows, reference, config, result: result["n_replicates"] == len(rows))
@deal.ensure(lambda project, rows, reference, config, result: len(result["files"]) >= 3)
@deal.ensure(lambda project, rows, reference, config, result: all(Path(path).is_file() for path in result["files"]))
@deal.ensure(lambda project, rows, reference, config, result: Path(result["directory"]).name == "simulation-data")
def analyze_and_write(project, rows, reference, config):
    """Pool equal-design replicates and serialize assets as a terminal task."""
    pooled = pool_rows(project, rows)
    # Fail on gross implementation discrepancies, separately from the 95%
    # descriptive intervals printed in the reports. No seed is rerolled.
    for row in pooled:
        if "variance" in row:
            if row["mean_error_se"] > float(stats.norm.isf(5e-11)):
                raise ValueError("Mean differs from its model beyond the fixed diagnostic")
            n, v = row["n_samples"], row["theory_variance"]
            pivot = da.divide((n - 1) * row["variance"], v) if v else 0
            if v and not float(stats.chi2.ppf(5e-11, n - 1)) <= pivot <= float(stats.chi2.isf(5e-11, n - 1)):
                raise ValueError("Variance differs from the fixed chi-square diagnostic")
        else:
            for count, probability in ((row["both"], row["theory_joint"]), (row["union_count"], row["theory_union"])):
                if float(stats.binomtest(count, row["n_samples"], probability).pvalue) < 1e-10:
                    raise ValueError("Event count differs from its fixed binomial diagnostic")
    data = {"pooled": pooled, "replicates": rows,
            "config": config, "sources": reference["sources"], "diagnostics_passed": True,
            "diagnostic_tail": 1e-10}
    return write_assets(project, data)


@deal.pre(lambda result: isinstance(result, dict) and result["project"] in PROJECTS)
@deal.post(lambda result: isinstance(result, dict) and result["pdf_pages"] > 0)
@deal.post(lambda result: len(result["pdf_sha256"]) == 64)
@deal.post(lambda result: result["xelatex"] is True)
@deal.raises(OSError, ValueError, subprocess.SubprocessError, CalledProcessError, TimeoutExpired)
@deal.has("network", "read", "write", "syscall")
@deal.post(lambda result: result["project"] in PROJECTS)
@deal.post(lambda result: result["pdf"].endswith(".pdf"))
@deal.post(lambda result: result["pdf"].startswith("analyses/"))
@deal.post(lambda result: result["pdf_sha256"].isascii())
@deal.post(lambda result: all(character in "0123456789abcdef" for character in result["pdf_sha256"]))
@deal.post(lambda result: type(result["pdf_pages"]) is int)
@deal.post(lambda result: Path(ROOT.joinpath(result["pdf"])).is_file())
@deal.post(lambda result: set(result) == {"project", "xelatex", "pdf_pages", "pdf_sha256", "pdf"})
@deal.post(lambda result: result["pdf_pages"] < 200)
def build_report(result):
    """Run XeLaTeX/BibTeX and Poppler only after Dask has written the assets."""
    project = result["project"]
    stem = {PROJECTS[0]: "hoeflin_simulations", PROJECTS[1]: "towers_simulations", PROJECTS[2]: "sequential_simulations"}[project]
    directory = ROOT.joinpath("analyses", project)
    log_directory = directory.joinpath("simulation-data")
    with log_directory.joinpath("build.log").open("w") as stream:
        subprocess.run(["latexmk", "-xelatex", "-outdir=output/pdf", "-interaction=nonstopmode", "-halt-on-error", stem + ".tex"], cwd=directory, env={**os.environ, "BIBINPUTS": str(ROOT.joinpath("reporting")) + os.pathsep + str(directory) + os.pathsep}, stdout=stream, stderr=subprocess.STDOUT, check=True, timeout=180)
    pdf = directory.joinpath("output/pdf", stem + ".pdf")
    info = subprocess.run(["pdfinfo", str(pdf)], capture_output=True, text=True, check=True, timeout=30).stdout
    pages = int(next(line.split(":", 1)[1] for line in info.splitlines() if line.startswith("Pages:")))
    render = directory.joinpath("tmp", "pdfs", stem)
    render.mkdir(parents=True, exist_ok=True)
    subprocess.run(["pdftoppm", "-scale-to", "1200", "-png", str(pdf), str(render.joinpath("page"))], capture_output=True, check=True, timeout=120)
    return {"project": project, "xelatex": True, "pdf_pages": pages, "pdf_sha256": digest(pdf), "pdf": str(pdf.relative_to(ROOT))}


@deal.pre(lambda results, config, task_count: isinstance(results, list) and len(results) == 3)
@deal.pre(lambda results, config, task_count: isinstance(config, dict) and type(task_count) is int and task_count > 0)
@deal.post(lambda result: result["schema"] == "dask-simulation-reports-v1")
@deal.post(lambda result: len(result["results"]) == 3 and bool(result["outputs"]))
@deal.ensure(lambda results, config, task_count, result: result["config"] == config and result["results"] == results)
@deal.ensure(lambda results, config, task_count, result: result["graph_tasks"] == task_count)
@deal.post(lambda result: all(len(entry["sha256"]) == 64 for entry in result["sources"] + result["outputs"]))
@deal.raises(OSError, ValueError, TypeError)
@deal.has("network", "read", "write")
@deal.post(lambda result: result["matplotlib_used"] is False)
@deal.post(lambda result: len(result["sources"]) > 0)
@deal.post(lambda result: len(result["outputs"]) > 0)
@deal.post(lambda result: all(entry["path"] and not entry["path"].startswith("/") for entry in result["sources"] + result["outputs"]))
@deal.post(lambda result: result["graph_tasks"] > 0)
@deal.post(lambda result: all(set(entry) == {"path", "sha256"} for entry in result["sources"] + result["outputs"]))
def finalize_run(results, config, task_count):
    """Hash the actual source/data/PDF artifacts in the final Dask task.

    This manifest is excluded from its own output list to avoid a circular
    self-hash. Python source, configuration and Dask data are hashed directly.
    Fresh figures are TeX/PGFPlots output; no plotting runtime is imported.
    """
    source_paths = list(ROOT.joinpath("reporting").glob("*.py")) + list(ROOT.joinpath("reporting").glob("*.tex")) + list(ROOT.joinpath("reporting").glob("*.bib"))
    # Include the implementations behind the shared reporting imports.
    source_paths += list(ROOT.joinpath("library", "python").glob("*.py"))
    source_paths += list(ROOT.joinpath("library", "latex").glob("*.tex"))
    source_paths += [ROOT.joinpath("requirements-dev.txt")]
    output_paths = []
    for project in PROJECTS:
        directory = ROOT.joinpath("analyses", project)
        source_paths += list(directory.glob("*simulations.tex"))
        output_paths += [path for path in directory.joinpath("simulation-data").iterdir() if path.is_file()]
    for result in results:
        if "pdf" in result:
            output_paths.append(ROOT.joinpath(result["pdf"]))
    record = {"schema": "dask-simulation-reports-v1", "config": config, "graph_tasks": task_count,
              "results": results, "matplotlib_used": False,
              "sources": [{"path": str(path.relative_to(ROOT)), "sha256": digest(path)} for path in sorted(set(source_paths))],
              "outputs": [{"path": str(path.relative_to(ROOT)), "sha256": digest(path)} for path in sorted(set(output_paths))]}
    dump(ROOT.joinpath("reporting", "run.json"), record)
    return record


@deal.pre(lambda argv=None: argv is None or isinstance(argv, list) and all(isinstance(arg, str) and "\x00" not in arg for arg in argv))
@deal.pre(lambda argv=None: ROOT.is_dir())
@deal.post(lambda result: result == 0)
@deal.pre(lambda argv=None: argv is None or len(argv) <= 128)
@deal.pre(lambda argv=None: argv is None or all(bool(arg) for arg in argv))
@deal.pre(lambda argv=None: argv is None or all(len(arg) <= 4096 for arg in argv))
@deal.ensure(lambda argv=None, result=None: result == 0)
@deal.ensure(lambda argv=None, result=None: argv is None or all("\\x00" not in arg for arg in argv))
@deal.ensure(lambda argv=None, result=None: ROOT.is_dir())
@deal.pre(lambda argv=None: argv is None or not any(arg.isspace() for arg in argv))
@deal.pre(lambda argv=None: argv is None or all(isinstance(arg, str) for arg in argv))
# Dask may synthesize worker exceptions; @deal.raises would mask the cause
# with RaisesContractError. Keep explicit domain and result contracts.
# Do not apply @deal.has to the *outer* Dask scheduler entrypoint: its
# socket monkeypatch breaks ssl.SSLSocket when Dask imports distributed.
# Contracted inner data/report operations retain their own effect scopes.
@deal.pre(lambda argv=None: isinstance(PROJECTS, tuple) and len(PROJECTS) == 3)
@deal.pre(lambda argv=None: len(set(PROJECTS)) == len(PROJECTS))
@deal.pre(lambda argv=None: ROOT.is_absolute())
@deal.pre(lambda argv=None: all(ROOT.joinpath("analyses", project).is_dir() for project in PROJECTS))
def main(argv=None):
    """Execute one shared graph for all three sub-projects, not a case loop of compute calls."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--trials", type=int, default=DEFAULT_TRIALS,
                        help="Samples per replicate (default 5,000,000; max 100,000,000)")
    parser.add_argument("--chunk", type=int, default=DEFAULT_CHUNK,
                        help="Samples in one bounded Dask worker task (default 500,000)")
    parser.add_argument("--replicates", type=int, choices=range(1, len(SEEDS) + 1),
                        default=DEFAULT_REPLICATES)
    parser.add_argument("--workers", type=int, default=min(4, os.cpu_count() or 1))
    parser.add_argument("--engine", choices=("blocks", "arrays"), default="blocks",
                        help="Block summaries reduce graph overhead; arrays retain the legacy cross-check")
    parser.add_argument("--scheduler", choices=("processes", "distributed", "single-threaded"),
                        default="processes", help="Local process pool or distributed LocalCluster")
    parser.add_argument("--memory-limit", default="2GiB",
                        help="Per-worker memory limit for the distributed scheduler")
    parser.add_argument("--dashboard-address", default=None,
                        help="Optional distributed dashboard bind (for example :8787)")
    parser.add_argument("--performance-report", default=None,
                        help="Optional distributed scheduler performance HTML output")
    parser.add_argument("--plan", action="store_true",
                        help="Build and inspect the lazy task graph without drawing samples or writing files")
    parser.add_argument("--pdf", action="store_true", help="Build and render all three XeLaTeX reports after analysis")
    args = parser.parse_args(argv)
    if not 2 <= args.trials <= 100_000_000 or not 1 <= args.chunk <= 2_000_000:
        parser.error("trials must be 2..100000000 and chunk must be 1..2000000")
    if not 1 <= args.workers <= 32:
        parser.error("workers must be 1..32")
    if (args.trials + args.chunk - 1) // args.chunk > 1024:
        parser.error("too many blocks per replicate (maximum 1024); increase --chunk")
    if args.engine == "arrays" and args.trials > 1_000_000:
        parser.error("the reference Dask Array engine is limited to <=1 million trials per replicate; use --engine blocks for scale")
    if args.scheduler != "distributed" and (args.dashboard_address or args.performance_report):
        parser.error("--dashboard-address and --performance-report require --scheduler distributed")
    config = {"trials": args.trials, "chunk": min(args.chunk, args.trials),
              "replicates": args.replicates, "seeds": list(SEEDS[:args.replicates]),
              "engine": args.engine, "scheduler": args.scheduler, "workers": args.workers,
              "memory_limit": args.memory_limit if args.scheduler == "distributed" else None,
              "versions": {name: importlib.metadata.version(name) for name in ("dask", "numpy", "scipy", "deal")}}
    references = {project: dask.delayed(reference_data)(project) for project in PROJECTS}
    if args.engine == "blocks":
        graphs = {PROJECTS[0]: graph_hoeflin_blocks(config),
                  PROJECTS[1]: graph_towers_blocks(config, references[PROJECTS[1]]),
                  PROJECTS[2]: graph_sequential_blocks(config)}
    else:
        graphs = {PROJECTS[0]: graph_hoeflin(config),
                  PROJECTS[1]: graph_towers(config, references[PROJECTS[1]]),
                  PROJECTS[2]: graph_sequential(config)}
    terminals = [dask.delayed(analyze_and_write)(project, graphs[project], references[project], config) for project in PROJECTS]
    if args.pdf:
        terminals = [dask.delayed(build_report)(terminal) for terminal in terminals]
    # One shared graph shares each random block across all experimental cases.
    task_count = len(dask.highlevelgraph.HighLevelGraph.merge(*(terminal.dask for terminal in terminals))) + 1
    if args.plan:
        print(json.dumps(execution_plan(config, task_count), indent=2))
        return 0
    terminal = dask.delayed(finalize_run)(terminals, config, task_count)
    started = time.monotonic()
    try:
        if args.scheduler == "distributed":
            # Optional worker memory spilling and live observability. No nested
            # Dask computations: all reductions and file writes are DAG nodes.
            from contextlib import nullcontext
            from dask.distributed import Client, LocalCluster, performance_report
            with LocalCluster(n_workers=args.workers, threads_per_worker=1,
                              processes=True, memory_limit=args.memory_limit,
                              dashboard_address=args.dashboard_address) as cluster:
                with Client(cluster) as client:
                    diagnostic_context = (performance_report(filename=args.performance_report)
                                          if args.performance_report else nullcontext())
                    with diagnostic_context:
                        record = client.compute(terminal).result()
        elif args.scheduler == "single-threaded":
            # Diagnostic path: preserve the original Python exception trace
            # without process-pool serialization masking contract failures.
            record = dask.compute(terminal, scheduler="single-threaded")[0]
        else:
            record = dask.compute(terminal, scheduler="processes", num_workers=args.workers)[0]
    except RemoteException as error:
        # Dynamic remote exception classes need a stable typed failure boundary.
        raise RuntimeError("Dask worker task failed; inspect the chained error and build logs") from error
    elapsed = time.monotonic() - started
    print(json.dumps({"execution_seconds": elapsed,
                      "performance_report": args.performance_report,
                      "samples_per_case": config["trials"] * len(config["seeds"]),
                      "graph_tasks": task_count,
                      "total_case_observations": config["trials"] * len(config["seeds"]) * (8 + 5 + 24),
                      "report_manifest": record}, indent=2))
    return 0



if __name__ == "__main__":
    # Function-level Deal contracts are already active in normal Python runs.
    # Do not globally monkey-patch socket.socket: the Dask distributed import
    # initializes ssl/asyncio, and its workers need standard socket behavior.
    # Preconditions and postconditions remain enforced by their decorators.
    raise SystemExit(main())
