"""Canonical centered-moment reduction shared by Dask and IQ-gap studies.

NumPy calculates block means and centered variances; the parallel
Chan merge retains between-block variation. Inputs and outputs carry the
original Deal contracts, including the worker transport allowance.
No model-specific sampling or file I/O belongs in this module.

Researcher/requester: Anders Hellström.
AI disclosure: AI-assisted source consolidation; regression checks pending.
"""
import math

import deal
import numpy as np


@deal.pre(lambda values, mse=None, rare_threshold=None: isinstance(values, np.ndarray))
@deal.pre(lambda values, mse=None, rare_threshold=None: values.ndim == 1 and values.size >= 1)
@deal.pre(lambda values, mse=None, rare_threshold=None: np.issubdtype(values.dtype, np.floating))
@deal.pre(lambda values, mse=None, rare_threshold=None: values.size <= 2_000_000)
@deal.pre(lambda values, mse=None, rare_threshold=None: mse is None or isinstance(mse, np.ndarray) and mse.shape == values.shape)
@deal.pre(lambda values, mse=None, rare_threshold=None: mse is None or np.issubdtype(mse.dtype, np.floating))
@deal.pre(lambda values, mse=None, rare_threshold=None: rare_threshold is None or isinstance(rare_threshold, float) and math.isfinite(rare_threshold) and rare_threshold > 3)
@deal.ensure(lambda values, mse=None, rare_threshold=None, result=None: result["n"] == values.size)
@deal.ensure(lambda values, mse=None, rare_threshold=None, result=None: math.isfinite(result["mean"]) and math.isfinite(result["m2"]))
@deal.ensure(lambda values, mse=None, rare_threshold=None, result=None: result["m2"] >= 0 and result["mse_sum"] >= 0)
@deal.ensure(lambda values, mse=None, rare_threshold=None, result=None: isinstance(result["counts"], tuple) and len(result["counts"]) == 3)
@deal.ensure(lambda values, mse=None, rare_threshold=None, result=None: all(type(count) is int and 0 <= count <= values.size for count in result["counts"]))
@deal.ensure(lambda values, mse=None, rare_threshold=None, result=None: rare_threshold is not None or result["counts"] == (0, 0, 0))
@deal.ensure(lambda values, mse=None, rare_threshold=None, result=None: result["counts"][0] >= result["counts"][1] >= result["counts"][2])
@deal.ensure(lambda values, mse=None, rare_threshold=None, result=None: mse is not None or result["mse_sum"] == 0)
@deal.raises(ValueError, TypeError, OverflowError)
@deal.has("network")
def partial_moment(values, mse=None, rare_threshold=None):
    """Center each block before squaring to avoid unstable raw second moments.

    n, mean, and m2=sum((x-mean)^2) admit numerically stable parallel
    composition. Optional squared prediction errors and nested tail counts
    use identical rows, rather than independent resimulated samples.
    """
    mean = float(np.mean(values))
    m2 = float(np.var(values, ddof=0)) * int(values.size)
    if rare_threshold is None:
        counts = (0, 0, 0)
    else:
        counts = tuple(int(np.count_nonzero(values > cutoff)) for cutoff in (2.0, 3.0, rare_threshold))
    return {"n": int(values.size), "mean": mean, "m2": m2,
            "mse_sum": float(np.sum(mse)) if mse is not None else 0.0,
            "counts": counts}


@deal.pre(lambda parts: isinstance(parts, list) and bool(parts))
@deal.pre(lambda parts: all(isinstance(item, dict) and {"n", "mean", "m2", "mse_sum", "counts"} <= item.keys() for item in parts))
@deal.pre(lambda parts: all(type(item["n"]) is int and item["n"] > 0 for item in parts))
@deal.pre(lambda parts: all(math.isfinite(item["mean"]) and math.isfinite(item["m2"]) and math.isfinite(item["mse_sum"]) for item in parts))
@deal.pre(lambda parts: all(item["m2"] >= 0 and item["mse_sum"] >= 0 for item in parts))
@deal.pre(lambda parts: all(len(item["counts"]) == 3 for item in parts))
@deal.pre(lambda parts: all(item["counts"][0] >= item["counts"][1] >= item["counts"][2] >= 0 for item in parts))
@deal.ensure(lambda parts, result: result["n"] == sum(item["n"] for item in parts))
@deal.ensure(lambda parts, result: result["n"] > 0 and result["m2"] >= 0 and result["mse_sum"] >= 0)
@deal.ensure(lambda parts, result: math.isfinite(result["mean"]) and math.isfinite(result["m2"]))
@deal.ensure(lambda parts, result: result["counts"] == tuple(sum(item["counts"][i] for item in parts) for i in range(3)))
@deal.ensure(lambda parts, result: math.isclose(result["mse_sum"], math.fsum(item["mse_sum"] for item in parts), rel_tol=1e-13, abs_tol=1e-12))
@deal.ensure(lambda parts, result: 0 <= result["counts"][2] <= result["counts"][1] <= result["counts"][0] <= result["n"])
@deal.raises(ValueError, TypeError, OverflowError, KeyError)
@deal.has("network")
def merge_moments(parts):
    """Merge partial centered moments without ignoring between-block shifts.

    For block means m_A,m_B, counts n_A,n_B and sums M2_A,M2_B,
    the new M2 is M2_A + M2_B + (m_B-m_A)^2*n_A*n_B/(n_A+n_B).
    Counts and squared prediction errors are additive. The merge order is
    fixed by the ascending block index and independent of task completion.
    """
    n, mean, m2 = 0, 0.0, 0.0
    counts = [0, 0, 0]
    for item in parts:
        size = item["n"]
        new_total = n + size
        delta = item["mean"] - mean
        mean += delta * (size / new_total)
        m2 += item["m2"] + delta * delta * (n * size / new_total)
        for j in range(3):
            counts[j] += item["counts"][j]
        n = new_total
    return {"n": n, "mean": mean, "m2": m2,
            "mse_sum": math.fsum(item["mse_sum"] for item in parts),
            "counts": tuple(counts)}
