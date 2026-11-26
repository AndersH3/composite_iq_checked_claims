"""Chunked synthetic IQ-gap experiments with worker-local sufficient statistics.

Anders Hellström requested the comparison of independent people and correlated
scores. NumPy supplies sampling and reduction, SciPy supplies analytic reference
values, Dask schedules bounded blocks, and Deal checks callable boundaries.
No participant data enter this module. The CLI records run-specific provenance.
"""
import math
from pathlib import Path

# The CLI is launched from its analysis directory; Makefile sets PYTHONPATH.

import dask
import deal
import numpy as np
from scipy.integrate import quad
from scipy.stats import foldnorm, norm

from reporting.block_simulations import merge_moments, partial_moment
from reporting.provenance import digest, dump

MODES = ("Gaussian", "Shared mixture", "Smooth mixture", "Block", "Conditional")
# Use distinct clauses for each estimand rather than one large compound predicate.
# Floating-point tolerances here are for summation, not statistical uncertainty.
MOMENT_RTOL = 1e-10
MOMENT_ATOL = 1e-7


@deal.pre(lambda seed, n, k, rho, mu, sigma, mode: type(seed) is int)
@deal.pre(lambda seed, n, k, rho, mu, sigma, mode: 0 <= seed < 2**64)
@deal.pre(lambda seed, n, k, rho, mu, sigma, mode: type(n) is int)
@deal.pre(lambda seed, n, k, rho, mu, sigma, mode: 2 <= n <= 1_000_000)
@deal.pre(lambda seed, n, k, rho, mu, sigma, mode: type(k) is int)
@deal.pre(lambda seed, n, k, rho, mu, sigma, mode: 2 <= k <= 100)
@deal.pre(lambda seed, n, k, rho, mu, sigma, mode: type(rho) in (float, int))
@deal.pre(lambda seed, n, k, rho, mu, sigma, mode: -1 <= rho <= 1)
@deal.pre(lambda seed, n, k, rho, mu, sigma, mode: rho >= -np.divide(1, k - 1))
@deal.pre(lambda seed, n, k, rho, mu, sigma, mode: type(mu) in (float, int))
@deal.pre(lambda seed, n, k, rho, mu, sigma, mode: abs(mu) <= 1000)
@deal.pre(lambda seed, n, k, rho, mu, sigma, mode: type(sigma) in (float, int))
@deal.pre(lambda seed, n, k, rho, mu, sigma, mode: 0 < sigma <= 100)
@deal.pre(lambda seed, n, k, rho, mu, sigma, mode: mode in MODES)
@deal.pre(lambda seed, n, k, rho, mu, sigma, mode: mode == "Gaussian" or rho == 0.6)
@deal.pre(lambda seed, n, k, rho, mu, sigma, mode: mode != "Conditional" or k == 2)
@deal.pre(lambda seed, n, k, rho, mu, sigma, mode: mode in ("Gaussian", "Conditional") or k == 5)
@deal.post(lambda result: isinstance(result, tuple) and len(result) == 3)
@deal.post(lambda result: all(math.isfinite(row["mean"]) and math.isfinite(row["m2"]) for row in result))
@deal.post(lambda result: all(row["m2"] >= 0 for row in result))
@deal.post(lambda result: 0 <= result[0]["mean"] <= result[1]["mean"] + MOMENT_ATOL)
@deal.post(lambda result: abs(result[2]["mean"]) <= result[0]["mean"] + MOMENT_ATOL)
@deal.ensure(lambda seed, n, k, rho, mu, sigma, mode, result: all(row["n"] == n for row in result))
@deal.post(lambda result: all(row["counts"] == (0, 0, 0) for row in result))
@deal.post(lambda result: all(row["mse_sum"] == 0 for row in result))
@deal.ensure(lambda seed, n, k, rho, mu, sigma, mode, result: k != 2 or result[0] == result[1])
@deal.ensure(lambda seed, n, k, rho, mu, sigma, mode, result: mode != "Block" or result[0] == result[1])
@deal.ensure(lambda seed, n, k, rho, mu, sigma, mode, result:
             mode != "Gaussian" or rho != 1 or all(row["mean"] == row["m2"] == 0 for row in result))
@deal.raises(ValueError, TypeError, OverflowError, MemoryError)
@deal.has("network", "random", "import")
def simulate_block(seed: int, n: int, k: int, rho: float, mu: float,
                   sigma: float, mode: str) -> tuple:
    """Generate one bounded block and return three centered-moment records.

    Rows are synthetic batteries or independent pairs. The seed selects a local
    PCG64 generator, not a mathematical proof of independence. The projection
    includes singular correlation boundaries. Conditional rows fix X1 at 145;
    block-model rows measure the cross-group gap. No participant input or I/O.
    Invalid model parameters violate the documented preconditions; allocation
    failures are not converted into simulated observations.
    """
    rng = np.random.Generator(np.random.PCG64(seed))
    z = rng.standard_normal((n, k))
    if mode == "Block":
        # Four within-group pairs have correlation one; six have correlation 1/3.
        # Both denominators are fixed positive integers. Use NumPy's division
        # ufunc directly rather than declare an impossible zero-divisor exception.
        second = np.divide(z[:, 0], 3) + np.sqrt(np.divide(8, 9)) * z[:, 1]
        scores = mu + sigma * np.column_stack((z[:, 0], z[:, 0], z[:, 0], second, second))
    elif mode == "Conditional":
        scores = np.column_stack((np.full(n, 145.0),
            mu + rho * (145 - mu) + sigma * np.sqrt(1 - rho**2) * z[:, 0]))
    else:
        # Mixture choice is per person, not per test.
        if mode == "Shared mixture":
            c = np.where(rng.random((n, 1)) < rho, 1.0, 0.0)
        elif mode == "Smooth mixture":
            c = np.where(rng.random((n, 1)) < 0.5, 0.3, 0.9)
        else:
            c = rho
        center = z.mean(axis=1, keepdims=True)
        scores = mu + sigma * (np.sqrt(1 - c) * (z - center)
            + np.sqrt(np.maximum(0, 1 + (k - 1) * c)) * center)
    signed = scores[:, 0] - scores[:, -1] if mode == "Block" else scores[:, 0] - scores[:, 1]
    # Center before squaring via the existing shared reducer; no raw-moment
    # subtraction or duplicate pooling algorithm is maintained here.
    return (partial_moment(np.abs(signed)), partial_moment(np.ptp(scores, axis=1)),
            partial_moment(signed))


# Separate the analytic reference from the random-number implementation.
@deal.pre(lambda k, rho, mu, sigma, mode: type(k) is int)
@deal.pre(lambda k, rho, mu, sigma, mode: 2 <= k <= 100)
@deal.pre(lambda k, rho, mu, sigma, mode: type(rho) in (float, int))
@deal.pre(lambda k, rho, mu, sigma, mode: -1 <= rho <= 1)
@deal.pre(lambda k, rho, mu, sigma, mode: rho >= -np.divide(1, k - 1))
@deal.pre(lambda k, rho, mu, sigma, mode: type(mu) in (float, int))
@deal.pre(lambda k, rho, mu, sigma, mode: abs(mu) <= 1000)
@deal.pre(lambda k, rho, mu, sigma, mode: type(sigma) in (float, int))
@deal.pre(lambda k, rho, mu, sigma, mode: 0 < sigma <= 100)
@deal.pre(lambda k, rho, mu, sigma, mode: mode in MODES)
@deal.pre(lambda k, rho, mu, sigma, mode: mode == "Gaussian" or rho == 0.6)
@deal.pre(lambda k, rho, mu, sigma, mode: mode != "Conditional" or k == 2)
@deal.pre(lambda k, rho, mu, sigma, mode: mode in ("Gaussian", "Conditional") or k == 5)
@deal.post(lambda result: isinstance(result, np.ndarray) and result.shape == (3,))
@deal.post(lambda result: bool(np.isfinite(result).all()))
@deal.post(lambda result: 0 <= result[0] <= result[1] + MOMENT_ATOL)
@deal.post(lambda result: abs(result[2]) <= result[0] + MOMENT_ATOL)
@deal.ensure(lambda k, rho, mu, sigma, mode, result: mode == "Conditional" or result[2] == 0)
@deal.ensure(lambda k, rho, mu, sigma, mode, result: k != 2 or result[0] == result[1])
@deal.ensure(lambda k, rho, mu, sigma, mode, result: mode != "Block" or result[0] == result[1])
@deal.ensure(lambda k, rho, mu, sigma, mode, result: rho != 1 or np.count_nonzero(result) == 0)
@deal.ensure(lambda k, rho, mu, sigma, mode, result:
             mode != "Conditional" or math.isclose(result[2], (1 - rho) * (145 - mu)))
def analytic_means(k: int, rho: float, mu: float, sigma: float, mode: str) -> np.ndarray:
    """Evaluate the three model means without random draws or Dask tasks.

    The result orders absolute gap, range, and signed gap. The Gaussian
    two-score and duplicated-group cases have closed forms; other ranges use
    SciPy quadrature. The folded-normal library handles nonzero conditional
    means. Returned decimals are approximations, not certified enclosures.
    """
    if mode == "Conditional":
        delta = (1 - rho) * (145 - mu)
        tau = sigma * math.sqrt(1 - rho**2)
        # Avoid overflow in standardizing a near-degenerate conditional law.
        # Beyond 40 SDs the folded correction is below binary64 resolution.
        if tau == 0 or abs(delta) >= 40 * tau:
            gap = abs(delta)
        elif delta == 0:
            gap = tau * math.sqrt(2 / math.pi)
        else:
            gap = foldnorm.mean(np.divide(abs(delta), tau), scale=tau)
        return np.array([gap, gap, delta])
    if mode == "Block":
        gap = 2 * sigma * math.sqrt((2 / 3) / math.pi)
        return np.array([gap, gap, 0.0])
    scale = math.sqrt(1 - rho)
    if mode == "Shared mixture":
        scale = 1 - rho
    elif mode == "Smooth mixture":
        scale = (math.sqrt(0.7) + math.sqrt(0.1)) / 2
    gap = 2 * sigma * scale / math.sqrt(math.pi)
    if k == 2 or scale == 0:
        return np.array([gap, gap, 0.0])
    # The order-statistic density is k phi(x) Phi(x)^(k-1).
    a = quad(lambda x: k * x * norm.pdf(x) * norm.cdf(x)**(k - 1),
             -np.inf, np.inf, epsabs=1e-11)[0]
    return np.array([gap, 2 * sigma * scale * a, 0.0])


if __name__ == "__main__":
    # Eight separately seeded replicates of five million rows per scenario.
    # Explicit worker count and bounded blocks limit memory and scheduler overhead.
    import argparse
    import platform
    import time
    from importlib.metadata import version

    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--rows-per-replicate", type=int, default=5_000_000)
    parser.add_argument("--replicates", type=int, default=8)
    parser.add_argument("--block", type=int, default=250_000)
    parser.add_argument("--workers", type=int, default=4)
    parser.add_argument("--output-dir", type=Path,
                        default=Path(__file__).resolve().parent / "simulation-data",
                        help="Separate smoke evidence from production datasets")
    args = parser.parse_args()
    if not (2 <= args.block <= 1_000_000 and args.rows_per_replicate >= args.block
            and args.rows_per_replicate % args.block == 0
            and args.replicates >= 2 and args.workers >= 1):
        parser.error("Require >=2 replicates, positive workers and exact bounded blocks")
    deal.enable()
    seed = 20261126
    scenarios = [
        ("Independent people", 2, 0.0, "Gaussian"),
        ("Two tests", 2, 0.6, "Gaussian"),
        ("Five tests", 5, 0.6, "Gaussian"),
        ("Negative correlation", 5, -0.25, "Gaussian"),
        ("Identical tests", 5, 1.0, "Gaussian"),
        ("Shared mixture", 5, 0.6, "Shared mixture"),
        ("Smooth mixture", 5, 0.6, "Smooth mixture"),
        ("Block cross-group gap", 5, 0.6, "Block"),
        ("First score 145", 2, 0.6, "Conditional"),
        ("Ten tests", 10, 0.6, "Gaussian"),
    ]
    blocks = args.rows_per_replicate // args.block
    streams = np.random.SeedSequence(seed).spawn(len(scenarios) * args.replicates * blocks)
    total = args.replicates * args.rows_per_replicate
    rows = []
    started = time.perf_counter()
    for index, (label, k, rho, mode) in enumerate(scenarios):
        tasks = [
            dask.delayed(simulate_block, pure=False)(
                int(streams[(index * args.replicates + rep) * blocks + j].generate_state(1, dtype=np.uint64)[0]),
                args.block, k, rho, 100.0, 15.0, mode)
            for rep in range(args.replicates) for j in range(blocks)
        ]
        results = dask.compute(*tasks, scheduler="threads", num_workers=args.workers)
        # Pool in submission order, first within each replicate and then across
        # replicates. Shared merge_moments retains between-block variation.
        per_rep = [
            [merge_moments([row[j] for row in results[rep * blocks:(rep + 1) * blocks]])
             for j in range(3)]
            for rep in range(args.replicates)
        ]
        aggregate = [merge_moments([row[j] for row in per_rep]) for j in range(3)]
        means = np.array([row["mean"] for row in aggregate])
        se = np.array([math.sqrt(row["m2"] / (row["n"] - 1) / row["n"])
                       for row in aggregate])
        exact = analytic_means(k, rho, 100.0, 15.0, mode)
        passed = bool(np.all(np.abs(means - exact) <= 6 * se + 1e-8))
        rows.append(dict(label=label, k=k, rho=rho, mode=mode, means=means.tolist(),
                         analytic=exact.tolist(), mcse=se.tolist(), passed=passed,
                         replicate_means=[[row["mean"] for row in replicate] for replicate in per_rep]))
    output = args.output_dir.resolve()
    output.mkdir(parents=True, exist_ok=True)
    metadata = dict(seed=seed, rows_per_scenario=total, settings={key: value for key, value in vars(args).items() if key != "output_dir"},
                    elapsed_seconds=time.perf_counter() - started,
                    source_sha256=digest(Path(__file__)),
                    bit_generator="PCG64", scheduler="threads",
                    shared_reducer_sha256=digest(
                        Path(__file__).resolve().parents[2] / "reporting/block_simulations.py"),
                    provenance_sha256=digest(Path(__file__).resolve().parents[2] / "reporting/provenance.py"),
                    python=platform.python_version(),
                    versions={name: version(name) for name in ("numpy", "scipy", "dask", "deal")},
                    rows=rows)
    dump(output / "summary.json", metadata)
    lines = [
        f"{row['label']} & {row['means'][0]:.5f} & {row['analytic'][0]:.5f} & "
        f"{row['mcse'][0]:.5f} & {row['means'][1]:.5f} & {row['analytic'][1]:.5f} & "
        f"{row['mcse'][1]:.5f} & {'PASS' if row['passed'] else 'FAIL'} " + r"\\"
        for row in rows
    ]
    (output / "results.tex").write_text("\n".join(lines) + "\n", encoding="utf-8")
    (output / "run.tex").write_text(
        f"Executed {total:,} rows per scenario in {args.replicates} replicates; "
        f"block size {args.block:,}, root seed {seed}, {args.workers} threads.\n",
        encoding="utf-8")
    if not all(row["passed"] for row in rows):
        raise SystemExit("Monte Carlo diagnostic failed; inspect retained results")
