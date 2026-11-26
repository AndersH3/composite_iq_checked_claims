"""Chunked synthetic IQ-gap experiments with worker-local sufficient statistics.

Anders Hellström requested the comparison of independent people and correlated
tests. No participant data enter this module. All reductions use NumPy/Dask.
"""
import json
from pathlib import Path

import dask
import deal
import numpy as np
from scipy.integrate import quad
from scipy.stats import foldnorm, norm

# A block returns first and second raw moment sums for three estimands:
# absolute gap, range, and signed gap. Rows are independent model replications.
@deal.pre(lambda seed, n, k, rho, mu, sigma, mode: type(seed) is int)
@deal.pre(lambda seed, n, k, rho, mu, sigma, mode: 0 <= seed < 2**64)
@deal.pre(lambda seed, n, k, rho, mu, sigma, mode: type(n) is int)
@deal.pre(lambda seed, n, k, rho, mu, sigma, mode: 2 <= n <= 1_000_000)
@deal.pre(lambda seed, n, k, rho, mu, sigma, mode: type(k) is int)
@deal.pre(lambda seed, n, k, rho, mu, sigma, mode: 2 <= k <= 100)
@deal.pre(lambda seed, n, k, rho, mu, sigma, mode: np.isfinite(rho) and -1 <= rho <= 1)
@deal.pre(lambda seed, n, k, rho, mu, sigma, mode: rho >= -1 / (k - 1))
@deal.pre(lambda seed, n, k, rho, mu, sigma, mode: np.isfinite(mu) and abs(mu) <= 1000)
@deal.pre(lambda seed, n, k, rho, mu, sigma, mode: np.isfinite(sigma) and 0 < sigma <= 100)
@deal.pre(lambda seed, n, k, rho, mu, sigma, mode: mode in ("Gaussian", "Shared mixture", "Smooth mixture", "Block", "Conditional"))
@deal.pre(lambda seed, n, k, rho, mu, sigma, mode: mode not in ("Shared mixture", "Smooth mixture", "Block") or (k == 5 and rho == 0.6))
@deal.pre(lambda seed, n, k, rho, mu, sigma, mode: mode != "Conditional" or (k == 2 and rho == 0.6))
@deal.post(lambda result: isinstance(result, np.ndarray) and result.shape == (2, 3))
@deal.post(lambda result: bool(np.isfinite(result).all()))
@deal.post(lambda result: bool((result[1] >= 0).all()))
@deal.post(lambda result: 0 <= result[0, 0] <= result[0, 1] + 1e-7)
@deal.post(lambda result: abs(result[0, 2]) <= result[0, 0] + 1e-7)
@deal.ensure(lambda seed, n, k, rho, mu, sigma, mode, result: k != 2 or np.allclose(result[:, 0], result[:, 1]))
@deal.ensure(lambda seed, n, k, rho, mu, sigma, mode, result: bool((result[0]**2 <= n * result[1] + 1e-5 * np.maximum(1, n * result[1])).all()))
@deal.ensure(lambda seed, n, k, rho, mu, sigma, mode, result: mode != "Gaussian" or rho != 1 or bool((result == 0).all()))
def simulate_block(seed, n, k, rho, mu, sigma, mode):
    """Generate one bounded block and reduce it to six finite moment sums.

    The seed selects a local generator; it does not certify mathematical
    independence. Equicorrelation uses orthogonal mean/residual projections
    to accommodate negative correlations as well as singular boundaries.
    The conditional case fixes the first score at 145. The block counterexample
    repeats three scores in one group and two in another. No external I/O.
    """
    rng = np.random.default_rng(seed)
    z = rng.standard_normal((n, k))
    if mode == "Block":
        # Four within-group pairs have correlation one; six have correlation 1/3.
        second = z[:, 0] / 3 + np.sqrt(8 / 9) * z[:, 1]
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
    values = np.column_stack((np.abs(signed), np.ptp(scores, axis=1), signed))
    return np.stack((values.sum(axis=0), np.square(values).sum(axis=0)))


if __name__ == "__main__":
    # Eight independently seeded replicates of five million rows per scenario.
    # Explicit worker count and bounded blocks limit memory and scheduler overhead.
    import argparse
    import platform
    from importlib.metadata import version

    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--rows-per-replicate", type=int, default=5_000_000)
    parser.add_argument("--replicates", type=int, default=8)
    parser.add_argument("--block", type=int, default=250_000)
    parser.add_argument("--workers", type=int, default=4)
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
    # Evaluate independent normal order-statistic integrals via SciPy quadrature.
    for index, (label, k, rho, mode) in enumerate(scenarios):
        tasks = [
            dask.delayed(simulate_block, pure=False)(
                int(streams[(index * args.replicates + rep) * blocks + j].generate_state(1, dtype=np.uint64)[0]),
                args.block, k, rho, 100.0, 15.0, mode)
            for rep in range(args.replicates) for j in range(blocks)
        ]
        sums = np.asarray(dask.compute(*tasks, scheduler="threads", num_workers=args.workers))
        per_rep = sums.reshape(args.replicates, blocks, 2, 3).sum(axis=1)
        aggregate = per_rep.sum(axis=0)
        means = aggregate[0] / total
        variance = np.maximum(0, (aggregate[1] - total * means**2) / (total - 1))
        se = np.sqrt(variance / total)
        a = quad(lambda x: k * x * norm.pdf(x) * norm.cdf(x)**(k - 1),
                 -np.inf, np.inf, epsabs=1e-11)[0]
        scale = np.sqrt(1 - rho)
        if mode == "Shared mixture":
            scale = 1 - rho
        if mode == "Smooth mixture":
            scale = (np.sqrt(0.7) + np.sqrt(0.1)) / 2
        exact = np.array([30 * scale / np.sqrt(np.pi), 30 * scale * a, 0.0])
        if mode == "Block":
            exact[:2] = 30 * np.sqrt((2 / 3) / np.pi)
        if mode == "Conditional":
            gap = foldnorm.mean(18 / 12, scale=12)
            exact = np.array([gap, gap, 18.0])
        passed = bool(np.all(np.abs(means - exact) <= 6 * se + 1e-8))
        rows.append(dict(label=label, k=k, rho=rho, mode=mode, means=means.tolist(),
                         analytic=exact.tolist(), mcse=se.tolist(), passed=passed,
                         replicate_means=(per_rep[:, 0] / args.rows_per_replicate).tolist()))
    output = Path(__file__).resolve().parent / "simulation-data"
    output.mkdir(exist_ok=True)
    metadata = dict(seed=seed, rows_per_scenario=total, settings=vars(args),
                    python=platform.python_version(),
                    versions={name: version(name) for name in ("numpy", "scipy", "dask", "deal")},
                    rows=rows)
    (output / "summary.json").write_text(json.dumps(metadata, indent=2) + "\n", encoding="utf-8")
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
