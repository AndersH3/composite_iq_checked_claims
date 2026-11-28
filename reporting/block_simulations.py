"""Bounded-memory, block-aggregated Dask Monte Carlo kernel.

Each Dask delayed task owns one independent, explicitly seeded NumPy block,
evaluates every coupled experimental case on that block, and returns only
compact sufficient statistics. Neither whole samples nor a separate Dask
task for every scalar reduction cross worker boundaries. The deterministic
Chan--Golub--LeVeque/parallel-variance merge preserves between-block
variation; it does NOT average block standard deviations.

Changing chunk size changes the block-addressed PRNG streams. All samples
are synthetic Gaussian-model draws, not empirical IQ measurements. This
module does not write reports or alter existing recorded simulation assets.

Researcher/requester: Anders Hellström.
AI disclosure: OpenAI ChatGPT/Codex assisted algorithms, contracts, and tests.
"""

# Dask distributed workers share their process with an asynchronous socket
# event loop. Deal's runtime offline checker monkeypatches socket process-wide;
# permitting the worker transport avoids breaking unrelated scheduler I/O.
# Source-level numeric invariants and exception contracts remain in force.
import math

import deal
import numpy as np

from library.python.statistics import event_result, moment_result
# Public compatibility imports preserve the original worker/test interface.
from library.python.moments import partial_moment, merge_moments

# Vectorized worker tasks own these blocks; only dictionaries of scalar
# sufficient statistics are transferred to the Dask scheduler.
COUNTS = (1, 2, 3, 4, 5, 10, 100, 1000)


@deal.pre(lambda seed, block_index, size, rare_threshold: type(seed) is int and 0 <= seed < 2**32)
@deal.pre(lambda seed, block_index, size, rare_threshold: type(block_index) is int and block_index >= 0)
@deal.pre(lambda seed, block_index, size, rare_threshold: type(size) is int and 1 <= size <= 2_000_000)
@deal.pre(lambda seed, block_index, size, rare_threshold: type(rare_threshold) is float and math.isfinite(rare_threshold) and rare_threshold > 3)
@deal.ensure(lambda seed, block_index, size, rare_threshold, result: isinstance(result, dict) and set(result) == set(COUNTS))
@deal.ensure(lambda seed, block_index, size, rare_threshold, result: all(row["n"] == size for row in result.values()))
@deal.ensure(lambda seed, block_index, size, rare_threshold, result: all(row["m2"] >= 0 and row["mse_sum"] >= 0 for row in result.values()))
@deal.ensure(lambda seed, block_index, size, rare_threshold, result: all(row["counts"][0] >= row["counts"][1] >= row["counts"][2] for row in result.values()))
@deal.ensure(lambda seed, block_index, size, rare_threshold, result: all(row["counts"][0] <= size for row in result.values()))
@deal.ensure(lambda seed, block_index, size, rare_threshold, result: all(math.isfinite(row["mean"]) for row in result.values()))
@deal.ensure(lambda seed, block_index, size, rare_threshold, result: len(result) == 8)
@deal.raises(ValueError, TypeError, OverflowError, ZeroDivisionError)
@deal.has("network", "random", "import")
@deal.ensure(lambda seed, block_index, size, rare_threshold, result: all(len(row["counts"]) == 3 for row in result.values()))
@deal.ensure(lambda seed, block_index, size, rare_threshold, result: all(math.isfinite(row["mse_sum"]) for row in result.values()))
def hoeflin_block(seed, block_index, size, rare_threshold):
    """Compute all eight composite-score cases from one common pair of draws.

    The Gaussian aggregate law uses one normal latent factor and one normal
    residual. This is equivalent in distribution to drawing all constituent
    tests for each size and avoids gigabytes of unnecessary score matrices.
    """
    rng = np.random.default_rng(np.random.SeedSequence((seed, block_index, 1001)))
    latent = rng.standard_normal(size)
    residual = rng.standard_normal(size)
    result = {}
    for count in COUNTS:
        variance = .6 + .4 / count
        mean_score = math.sqrt(.6) * latent + math.sqrt(.4 / count) * residual
        composite = mean_score / math.sqrt(variance)
        estimate = math.sqrt(.6) * mean_score / variance
        result[count] = partial_moment(composite, (estimate - latent) ** 2, rare_threshold)
    return result


@deal.pre(lambda seed, block_index, size, reference: type(seed) is int and 0 <= seed < 2**32)
@deal.pre(lambda seed, block_index, size, reference: type(block_index) is int and block_index >= 0)
@deal.pre(lambda seed, block_index, size, reference: type(size) is int and 1 <= size <= 2_000_000)
@deal.pre(lambda seed, block_index, size, reference: isinstance(reference, dict) and reference.get("project") == "towers-multiple-test-admissions")
@deal.pre(lambda seed, block_index, size, reference: len(reference["cases"]) == 5)
@deal.pre(lambda seed, block_index, size, reference: all(0 < case["p_a"] < 1 and 0 < case["p_b"] < 1 for case in reference["cases"]))
@deal.ensure(lambda seed, block_index, size, reference, result: isinstance(result, dict) and set(result) == {1, 2, 3, 4, 5})
@deal.ensure(lambda seed, block_index, size, reference, result: all(len(counts) == 4 for counts in result.values()))
@deal.ensure(lambda seed, block_index, size, reference, result: all(sum(counts) == size for counts in result.values()))
@deal.ensure(lambda seed, block_index, size, reference, result: all(all(type(count) is int and count >= 0 for count in counts) for counts in result.values()))
@deal.ensure(lambda seed, block_index, size, reference, result: len(result) == len(reference["cases"]))
@deal.raises(ValueError, TypeError, OverflowError, KeyError)
@deal.has("network", "random", "import")
@deal.pre(lambda seed, block_index, size, reference: all(math.isfinite(float(case["cutoff_a"])) for case in reference["cases"]))
@deal.pre(lambda seed, block_index, size, reference: all(math.isfinite(float(case["cutoff_b"])) for case in reference["cases"]))
def towers_block(seed, block_index, size, reference):
    """Classify each paired observation once per admission rule, in one task.

    Cutoffs are computed once by the shared lazy reference task and passed
    to all blocks. The four cells form an exhaustive disjoint partition.
    """
    rng = np.random.default_rng(np.random.SeedSequence((seed, block_index, 1002)))
    first = rng.standard_normal(size)
    second = .7 * first + math.sqrt(1 - .7**2) * rng.standard_normal(size)
    result = {}
    for index, case in enumerate(reference["cases"], 1):
        above_a, above_b = first > case["cutoff_a"], second > case["cutoff_b"]
        result[index] = (
            int(np.count_nonzero(~above_a & ~above_b)),
            int(np.count_nonzero(above_a & ~above_b)),
            int(np.count_nonzero(~above_a & above_b)),
            int(np.count_nonzero(above_a & above_b)),
        )
    return result


@deal.pre(lambda seed, block_index, size, r: type(seed) is int and 0 <= seed < 2**32)
@deal.pre(lambda seed, block_index, size, r: type(block_index) is int and block_index >= 0)
@deal.pre(lambda seed, block_index, size, r: type(size) is int and 1 <= size <= 2_000_000)
@deal.pre(lambda seed, block_index, size, r: type(r) is int and r in (1, 2, 3))
@deal.ensure(lambda seed, block_index, size, r, result: isinstance(result, dict) and len(result) == 8)
@deal.ensure(lambda seed, block_index, size, r, result: set(result) == {(k, mode) for k in (1, 2, 10, 0) for mode in ("population", "conditional")})
@deal.ensure(lambda seed, block_index, size, r, result: all(row["n"] == size for row in result.values()))
@deal.ensure(lambda seed, block_index, size, r, result: all(row["m2"] >= 0 and row["mse_sum"] == 0 for row in result.values()))
@deal.ensure(lambda seed, block_index, size, r, result: all(row["counts"] == (0, 0, 0) for row in result.values()))
@deal.ensure(lambda seed, block_index, size, r, result: all(math.isfinite(row["mean"]) for row in result.values()))
@deal.ensure(lambda seed, block_index, size, r, result: (0, "population") in result and (0, "conditional") in result)
@deal.raises(ValueError, TypeError, OverflowError, ZeroDivisionError)
@deal.has("network", "random", "import")
@deal.ensure(lambda seed, block_index, size, r, result: all(set(row) == {"n", "mean", "m2", "mse_sum", "counts"} for row in result.values()))
@deal.ensure(lambda seed, block_index, size, r, result: all(math.isfinite(row["m2"]) for row in result.values()))
def sequential_block(seed, block_index, size, r):
    """Compute all eight conditional/population cases for one starting count.

    The task generates full finite residual vectors for the three requested
    future counts, sharing latent factors and prefix noise as in the recorded
    array method. The k=0 labels denote separate analytic limit laws, not
    a finite empty test battery. No arrays leave the worker task.
    """
    rng = np.random.default_rng(np.random.SeedSequence((seed, block_index, 1003, r)))
    latent = rng.standard_normal(size)
    population_noise = rng.standard_normal((size, r + 10))
    future_noise = rng.standard_normal((size, 10))
    dr = 1 + (r - 1) * .6
    posterior = r * math.sqrt(.6) * (10.0 / 3.0) / dr + math.sqrt(.4 / dr) * latent
    result = {}
    for k in (1, 2, 10, 0):
        if k:
            total = r + k
            population = (math.sqrt(.6) * latent +
                          math.sqrt(.4) * population_noise[:, :total].mean(axis=1))
            conditional = (r * (10.0 / 3.0) + k * math.sqrt(.6) * posterior +
                           math.sqrt(.4) * future_noise[:, :k].sum(axis=1)) / total
        else:
            population = math.sqrt(.6) * latent
            conditional = math.sqrt(.6) * posterior
        result[k, "population"] = partial_moment(population)
        result[k, "conditional"] = partial_moment(conditional)
    return result


@deal.pre(lambda meta, parts, key: isinstance(meta, dict) and {"n_samples", "project", "theory_mean", "theory_variance"} <= meta.keys())
@deal.pre(lambda meta, parts, key: isinstance(parts, list) and bool(parts))
@deal.pre(lambda meta, parts, key: all(isinstance(block, dict) and key in block for block in parts))
@deal.pre(lambda meta, parts, key: type(meta["n_samples"]) is int and meta["n_samples"] >= 2)
@deal.pre(lambda meta, parts, key: meta["theory_variance"] >= 0)
@deal.pre(lambda meta, parts, key: sum(block[key]["n"] for block in parts) == meta["n_samples"])
@deal.ensure(lambda meta, parts, key, result: isinstance(result, dict) and result["n_samples"] == meta["n_samples"])
@deal.ensure(lambda meta, parts, key, result: result["variance"] >= 0 and result["mse"] >= 0)
@deal.ensure(lambda meta, parts, key, result: result["count2"] >= result["count3"] >= result["count_rare"] >= 0)
@deal.ensure(lambda meta, parts, key, result: result["mean_se"] >= 0 and result["mean_error_se"] >= 0)
@deal.ensure(lambda meta, parts, key, result: math.isfinite(result["mean"]) and math.isfinite(result["variance"]))
@deal.ensure(lambda meta, parts, key, result: all(result[field] == meta[field] for field in ("replicate", "seed", "project")))
@deal.raises(ValueError, TypeError, OverflowError, KeyError, ZeroDivisionError)
@deal.has("network")
@deal.ensure(lambda meta, parts, key, result: result["mean_error_se"] >= 0)
def finish_moment(meta, parts, key):
    """Return the same statistics schema as the canonical array engine."""
    summary = merge_moments([block[key] for block in parts])
    return moment_result(meta, summary["mean"], summary["m2"] / (summary["n"] - 1),
                         summary["mse_sum"] / summary["n"], summary["counts"])


@deal.pre(lambda meta, parts, index, reference: isinstance(meta, dict) and {"n_samples", "project", "seed", "replicate"} <= meta.keys())
@deal.pre(lambda meta, parts, index, reference: meta["project"] == "towers-multiple-test-admissions")
@deal.pre(lambda meta, parts, index, reference: isinstance(parts, list) and bool(parts))
@deal.pre(lambda meta, parts, index, reference: type(index) is int and 1 <= index <= 5)
@deal.pre(lambda meta, parts, index, reference: isinstance(reference, dict) and reference["project"] == meta["project"])
@deal.pre(lambda meta, parts, index, reference: len(reference["cases"]) == 5 and all(index in block for block in parts))
@deal.pre(lambda meta, parts, index, reference: sum(sum(block[index]) for block in parts) == meta["n_samples"])
@deal.ensure(lambda meta, parts, index, reference, result: isinstance(result, dict) and result["case_index"] == index)
@deal.ensure(lambda meta, parts, index, reference, result: result["n_samples"] == meta["n_samples"])
@deal.ensure(lambda meta, parts, index, reference, result: result["neither"] + result["a_only"] + result["b_only"] + result["both"] == meta["n_samples"])
@deal.ensure(lambda meta, parts, index, reference, result: result["replicate"] == meta["replicate"] and result["seed"] == meta["seed"])
@deal.ensure(lambda meta, parts, index, reference, result: 0 <= result["joint"] <= result["union"] <= 1)
@deal.raises(ValueError, TypeError, OverflowError, KeyError)
@deal.has("network")
@deal.ensure(lambda meta, parts, index, reference, result: 0 <= result["joint_low"] <= result["joint"] <= result["joint_high"] <= 1)
def finish_event(meta, parts, index, reference):
    """Reduce per-block disjoint cell counts with exact integer addition."""
    case = reference["cases"][index - 1]
    complete_meta = dict(meta, **{field: case[field] for field in (
        "case_index", "label", "p_a", "p_b", "theory_joint", "cutoff_a", "cutoff_b"
    )})
    counts = tuple(sum(block[index][j] for block in parts) for j in range(4))
    return event_result(complete_meta, counts)
