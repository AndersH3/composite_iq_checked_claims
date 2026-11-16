"""Validate the high-throughput Dask block engine without a production run.

These tests distinguish lazy graph creation from executing seeded samples,
check stable centered moment aggregation, and compare synthetic outcomes
against independently derived Gaussian laws. The tracked publication
artifacts must remain unmodified by these checks.

Researcher/requester: Anders Hellström.
AI disclosure: OpenAI assisted the performance refactor and test construction.
"""

import json
from json import JSONDecodeError
import csv
import subprocess
from subprocess import CalledProcessError, TimeoutExpired
import math

import dask
import deal
import numpy as np
import pytest

from conftest import protected_history_intact, reference_inputs_intact
from reporting import block_simulations, simulate


@deal.pre(lambda: protected_history_intact())
@deal.pre(lambda: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.ensure(lambda *, result: protected_history_intact())
@deal.ensure(lambda *, result: reference_inputs_intact())
@deal.has("network", "read", "random", "import", "syscall", "global")
@deal.raises(AssertionError, ValueError, TypeError, OverflowError, KeyError, ZeroDivisionError)
@deal.ensure(lambda *, result: result is None)
@deal.pre(lambda: len(block_simulations.COUNTS) == 8)
@deal.pre(lambda: simulate.DEFAULT_TRIALS >= 5_000_000)
def test_centered_block_moment_merge_and_seeded_substreams():
    """Merging blocks must preserve between-block variation and tail counts."""
    left = np.array([1_000_001.0, 1_000_003.0])
    right = np.array([1_000_011.0, 1_000_013.0, 1_000_015.0])
    partials = [block_simulations.partial_moment(values) for values in (left, right)]
    merged = block_simulations.merge_moments(partials)
    combined = np.concatenate((left, right))
    assert merged["n"] == len(combined)
    assert merged["mean"] == pytest.approx(float(combined.mean()), abs=1e-10)
    assert merged["m2"] / (merged["n"] - 1) == pytest.approx(
        float(combined.var(ddof=1)), abs=1e-10,
    )
    threshold = float(4.753424308822899)
    first = block_simulations.hoeflin_block(20261114, 0, 1000, threshold)
    second = block_simulations.hoeflin_block(20261114, 0, 1000, threshold)
    third = block_simulations.hoeflin_block(20261114, 1, 1000, threshold)
    assert first == second
    assert first != third
    assert all(entry["n"] == 1000 for entry in first.values())


@deal.pre(lambda: protected_history_intact())
@deal.pre(lambda: reference_inputs_intact())
@deal.pre(lambda: simulate.DEFAULT_REPLICATES == 8)
@deal.pre(lambda: simulate.DEFAULT_CHUNK >= 250_000)
@deal.post(lambda result: result is None)
@deal.ensure(lambda *, result: protected_history_intact())
@deal.ensure(lambda *, result: reference_inputs_intact())
@deal.has("network", "read", "import", "syscall", "random", "global")
@deal.raises(AssertionError, ValueError, TypeError, OverflowError, KeyError, ZeroDivisionError, OSError, NotImplementedError, ImportError)
@deal.ensure(lambda *, result: result is None)
def test_large_default_graph_has_fewer_tasks_than_recorded_small_graph():
    """A tenfold sample increase must not create a larger task graph."""
    config = {"trials": simulate.DEFAULT_TRIALS, "chunk": simulate.DEFAULT_CHUNK,
              "seeds": list(simulate.SEEDS[:simulate.DEFAULT_REPLICATES])}
    ref = dask.delayed(simulate.reference_data)("towers-multiple-test-admissions")
    graphs = [simulate.graph_hoeflin_blocks(config),
              simulate.graph_towers_blocks(config, ref),
              simulate.graph_sequential_blocks(config)]
    terminal = dask.delayed(lambda *rows: len(rows))(*[row for group in graphs for row in group])
    tasks = len(terminal.dask)
    assert len(graphs[0]) == 8 * 8
    assert len(graphs[1]) == 5 * 8
    assert len(graphs[2]) == 24 * 8
    assert tasks < 5_000, tasks
    assert tasks < 31_254  # Former recorded 4x1M/50k Dask Array run.
    assert config["trials"] * len(config["seeds"]) == 40_000_000
    plan = simulate.execution_plan(config | {"workers": 4, "engine": "blocks",
                                             "scheduler": "processes"}, tasks)
    assert plan["expected_rare_events_per_case"] == 40.0
    assert plan["blocks_per_replicate"] == 10
    assert plan["estimated_gaussian_input_bytes_per_sequential_block"] == 96_000_000


@deal.pre(lambda: protected_history_intact())
@deal.pre(lambda: reference_inputs_intact())
@deal.pre(lambda: simulate.DEFAULT_REPLICATES >= 4)
@deal.post(lambda result: result is None)
@deal.ensure(lambda *, result: protected_history_intact())
@deal.ensure(lambda *, result: reference_inputs_intact())
@deal.has("network", "read", "import", "random", "global", "syscall")
@deal.raises(AssertionError, ValueError, TypeError, OverflowError, KeyError, ZeroDivisionError, OSError, NotImplementedError, ImportError)
@deal.ensure(lambda *, result: result is None)
@deal.pre(lambda: len(simulate.PROJECTS) == 3)
def test_seeded_block_simulations_match_analytic_reference_laws():
    """Small out-of-core graphs retain the models and deterministic seeds."""
    config = {"trials": 12000, "chunk": 3000, "seeds": [simulate.SEEDS[0]]}
    ref = dask.delayed(simulate.reference_data)("towers-multiple-test-admissions")
    groups = [simulate.graph_hoeflin_blocks(config),
              simulate.graph_towers_blocks(config, ref),
              simulate.graph_sequential_blocks(config)]
    rows = dask.compute(*(row for group in groups for row in group),
                        scheduler="single-threaded")
    assert len(rows) == 37
    assert all(row["n_samples"] == 12000 for row in rows)
    for row in rows:
        if "variance" in row:
            assert 0.8 <= row["variance"] / row["theory_variance"] <= 1.2
            assert row["mean_error_se"] < 6
        else:
            assert row["neither"] + row["a_only"] + row["b_only"] + row["both"] == 12000
            assert row["joint_low"] <= row["joint"] <= row["joint_high"]
    ho = [row for row in rows if row["project"] == "hoeflin-ferguson"]
    tw = [row for row in rows if row["project"] == "towers-multiple-test-admissions"]
    sq = [row for row in rows if row["project"] == "sequential-conditional-means"]
    assert len(ho) == 8 and len(tw) == 5 and len(sq) == 24
    assert all(row["count2"] >= row["count3"] >= row["count_rare"] for row in ho)
    example = next(row for row in sq if (row["r"], row["k"], row["mode"]) == (2, 10, "conditional"))
    assert example["theory_mean_iq"] == pytest.approx(1675 / 12)
    assert example["theory_sd_iq"] ** 2 == pytest.approx(475 / 16)


@deal.pre(lambda capsys: protected_history_intact())
@deal.pre(lambda capsys: reference_inputs_intact())
@deal.pre(lambda capsys: capsys is not None)
@deal.post(lambda result: result is None)
@deal.ensure(lambda capsys, result: protected_history_intact())
@deal.ensure(lambda capsys, result: reference_inputs_intact())
@deal.has("network", "read", "write", "stdout", "stderr", "time", "import", "syscall", "random", "global")
@deal.raises(AssertionError, ValueError, TypeError, OverflowError, KeyError, ZeroDivisionError, OSError, ImportError, RuntimeError, JSONDecodeError, NotImplementedError, csv.Error, subprocess.SubprocessError, CalledProcessError, TimeoutExpired, SystemExit)
@deal.ensure(lambda capsys, result: result is None)
@deal.pre(lambda capsys: simulate.DEFAULT_TRIALS > 1_000_000)
def test_dry_run_reports_scaling_without_touching_published_results(capsys):
    """--plan must produce a reproducible graph budget without computation."""
    assert simulate.main(["--plan", "--trials", "5000000", "--chunk", "500000",
                          "--replicates", "8", "--workers", "4"]) == 0
    report = json.loads(capsys.readouterr().out)
    assert report["samples_per_case"] == 40_000_000
    assert report["blocks_per_replicate"] == 10
    assert report["graph_tasks"] < 5_000
    assert report["config"]["engine"] == "blocks"
    assert report["config"]["scheduler"] == "processes"
