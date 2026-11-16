"""Pure statistical summaries evaluated inside the Dask report task graph.

Dask Array supplies the sample reductions.  These small functions interpret
those reductions, reuse SciPy's maintained confidence-interval algorithms,
and preserve enough metadata to pool complete replicates correctly.  They
perform no I/O and never draw or replace random seeds after seeing a result.
"""
# Dask distributed workers share their process with an asynchronous socket
# event loop. Deal's runtime offline checker monkeypatches socket process-wide;
# permitting the worker transport avoids breaking unrelated scheduler I/O.
# Source-level numeric invariants and exception contracts remain in force.
import json
import math
import numbers

import deal
from scipy.stats import binomtest, chi2, norm

HOEFLIN = "hoeflin-ferguson"
TOWERS = "towers-multiple-test-admissions"
SEQUENTIAL = "sequential-conditional-means"
PROJECTS = (HOEFLIN, TOWERS, SEQUENTIAL)
COMMON = {"project", "n_samples", "replicate", "seed"}
MOMENT_META = COMMON | {"theory_mean", "theory_variance"}
EVENT_META = COMMON | {"case_index", "label", "p_a", "p_b", "theory_joint", "cutoff_a", "cutoff_b"}


@deal.pre(lambda meta, mean, variance, mse=0.0, counts=(0, 0, 0): isinstance(meta, dict))
@deal.pre(lambda meta, mean, variance, mse=0.0, counts=(0, 0, 0): MOMENT_META <= meta.keys() and meta["project"] in (HOEFLIN, SEQUENTIAL))
@deal.pre(lambda meta, mean, variance, mse=0.0, counts=(0, 0, 0): isinstance(counts, (list, tuple)) and len(counts) == 3)
@deal.post(lambda result: isinstance(result, dict) and isinstance(result["_meta"], dict))
@deal.ensure(lambda meta, mean, variance, mse=0.0, counts=(0, 0, 0), result=None: all(result[key] == value for key, value in meta.items()))
@deal.ensure(lambda meta, mean, variance, mse=0.0, counts=(0, 0, 0), result=None: result["mean"] == float(mean) and result["variance"] == float(variance) and result["mse"] == float(mse))
@deal.ensure(lambda meta, mean, variance, mse=0.0, counts=(0, 0, 0), result=None: (result["count2"], result["count3"], result["count_rare"]) == tuple(counts))
@deal.post(lambda result: result["variance"] >= 0 and result["mse"] >= 0 and result["mean_error_se"] >= 0)
@deal.post(lambda result: 0 <= result["rare_low"] <= result["rate_rare"] <= result["rare_high"] <= 1)
@deal.raises(ValueError, TypeError, OverflowError)
@deal.has("network")
def moment_result(meta, mean, variance, mse=0.0, counts=(0, 0, 0)):
    """Interpret unbiased variance, fixed-model mean error and tail counts.

    Hoeflin reductions concern standardized composites Z; observed_sd converts
    their empirical SD back to the raw arithmetic-mean scale. Sequential
    reductions already concern actual standardized means and are also reported
    on the affine IQ scale. A deterministic theoretical law is checked without
    division by a zero standard error.
    """
    values = (mean, variance, mse, meta["theory_mean"], meta["theory_variance"])
    if not all(isinstance(value, numbers.Real) and not isinstance(value, bool)
               and math.isfinite(float(value)) and abs(value) <= 1e12 for value in values):
        raise ValueError("Moment inputs must be finite bounded real values")
    if variance < 0 or mse < 0 or meta["theory_variance"] < 0:
        raise ValueError("Variances and mean squared errors must be nonnegative")
    if not all(isinstance(meta[key], numbers.Integral) and not isinstance(meta[key], bool)
               and meta[key] >= 0 for key in ("n_samples", "replicate", "seed")) or meta["n_samples"] < 2:
        raise ValueError("Moment counts and seed identifiers are outside their domain")
    n = int(meta["n_samples"])
    if not all(isinstance(count, numbers.Integral) and not isinstance(count, bool) and 0 <= count <= n for count in counts):
        raise ValueError("Tail counts must be nonnegative integers bounded by the sample size")
    c2, c3, cr = (int(count) for count in counts)
    if not c2 >= c3 >= cr:
        raise ValueError("Nested threshold counts are inconsistent")
    clean = {key: int(value) if isinstance(value, numbers.Integral) and not isinstance(value, bool)
             else float(value) if isinstance(value, numbers.Real) else value for key, value in meta.items()}
    json.dumps(clean, allow_nan=False)
    mu, v = float(meta["theory_mean"]), float(meta["theory_variance"])
    observed_mean, observed_variance = float(mean), float(variance)
    se = math.sqrt(v / n)
    if se == 0 and (abs(observed_mean - mu) > 1e-8 or observed_variance > 1e-8):
        raise ValueError("A deterministic law produced nonconstant moment summaries")
    rare = binomtest(cr, n).proportion_ci(confidence_level=0.95, method="exact")
    interval2 = binomtest(c2, n).proportion_ci(confidence_level=0.95, method="wilson")
    interval3 = binomtest(c3, n).proportion_ci(confidence_level=0.95, method="wilson")
    row = dict(clean)
    row.update(_meta=dict(clean), mean=observed_mean, variance=observed_variance, mse=float(mse),
               mean_se=se, mean_error_se=abs(observed_mean - mu) / se if se else 0.0,
               observed_sd=math.sqrt(observed_variance), count2=c2, count3=c3, count_rare=cr,
               rate2=c2 / n, rate3=c3 / n, rate_rare=cr / n,
               rare_low=float(rare.low), rare_high=float(rare.high),
               rate2_low=float(interval2.low), rate2_high=float(interval2.high),
               rate3_low=float(interval3.low), rate3_high=float(interval3.high),
               theory_rate2=float(norm.sf(2)), theory_rate3=float(norm.sf(3)), theory_rate_rare=1e-6)
    if meta["project"] == HOEFLIN:
        if not {"n", "theory_sd", "theory_mse"} <= meta.keys() or not isinstance(meta["n"], numbers.Integral) or isinstance(meta["n"], bool) or meta["n"] < 1 or not 0 < float(meta["theory_sd"]) <= 1 or not 0 <= float(meta["theory_mse"]) <= 1:
            raise ValueError("Hoeflin metadata must include the raw-mean scale and MSE target")
        row["observed_sd"] *= float(meta["theory_sd"])
    else:
        if not {"r", "k", "mode"} <= meta.keys() or not all(isinstance(meta[name], numbers.Integral) and not isinstance(meta[name], bool) for name in ("r", "k")) or meta["r"] < 1 or meta["k"] < 0 or not isinstance(meta["mode"], str) or not meta["mode"]:
            raise ValueError("Sequential metadata must identify its starting block and count")
        low = math.sqrt((n - 1) * observed_variance / float(chi2.ppf(0.975, n - 1)))
        high = math.sqrt((n - 1) * observed_variance / float(chi2.ppf(0.025, n - 1)))
        row.update(mean_iq=100 + 15 * observed_mean, theory_mean_iq=100 + 15 * mu,
                   sd_iq=15 * math.sqrt(observed_variance), theory_sd_iq=15 * math.sqrt(v),
                   mean_se_iq=15 * se, sd_low_iq=15 * low, sd_high_iq=15 * high)
    return row


@deal.pre(lambda meta, counts: isinstance(meta, dict) and EVENT_META <= meta.keys())
@deal.pre(lambda meta, counts: meta["project"] == TOWERS)
@deal.pre(lambda meta, counts: isinstance(counts, (tuple, list)) and len(counts) == 4)
@deal.post(lambda result: isinstance(result, dict) and isinstance(result["_meta"], dict))
@deal.ensure(lambda meta, counts, result: sum(counts) == result["n_samples"])
@deal.ensure(lambda meta, counts, result: (result["neither"], result["a_only"], result["b_only"], result["both"]) == tuple(counts))
@deal.ensure(lambda meta, counts, result: result["joint"] == counts[3] / meta["n_samples"])
@deal.post(lambda result: 0 <= result["joint_low"] <= result["joint"] <= result["joint_high"] <= 1)
@deal.post(lambda result: 0 <= result["union_low"] <= result["union"] <= result["union_high"] <= 1)
@deal.ensure(lambda meta, counts, result: result["conditional_b_given_a"] == (counts[3] / (counts[1] + counts[3]) if counts[1] + counts[3] else None))
@deal.ensure(lambda meta, counts, result: result["conditional_a_given_b"] == (counts[3] / (counts[2] + counts[3]) if counts[2] + counts[3] else None))
@deal.raises(ValueError, TypeError, OverflowError)
@deal.has("network")
def event_result(meta, counts):
    """Summarize a four-cell partition using the actual selected denominators.

    An undefined conditional probability is None, never an invented zero. The
    pointwise Wilson intervals use SciPy, and rare-joint exact intervals use
    binomial inversion. Neither interpretation proves pseudorandom normality.
    """
    if not all(isinstance(meta[key], numbers.Integral) and not isinstance(meta[key], bool)
               and meta[key] >= 0 for key in ("n_samples", "replicate", "seed")) or meta["n_samples"] < 2:
        raise ValueError("Event counts and identifiers are outside their domain")
    n = int(meta["n_samples"])
    if not all(isinstance(count, numbers.Integral) and not isinstance(count, bool) and 0 <= count <= n for count in counts) or sum(counts) != n:
        raise ValueError("Four event cells must be a nonnegative integer partition of the sample")
    pa, pb, j = (float(meta[key]) for key in ("p_a", "p_b", "theory_joint"))
    if not all(math.isfinite(value) for value in (pa, pb, j)) or not 0 < pa < 1 or not 0 < pb < 1 or not max(0, pa + pb - 1) <= j <= min(pa, pb):
        raise ValueError("Theoretical event probabilities violate their domain")
    cells = tuple(int(count) for count in counts)
    neither, aonly, bonly, both = cells
    na, nb, nu = aonly + both, bonly + both, aonly + bonly + both
    joint, union, theory_union = both / n, nu / n, pa + pb - j
    jci = binomtest(both, n).proportion_ci(confidence_level=0.95, method="wilson")
    uci = binomtest(nu, n).proportion_ci(confidence_level=0.95, method="wilson")
    exact = binomtest(both, n).proportion_ci(confidence_level=0.95, method="exact")
    aci = binomtest(both, na).proportion_ci(confidence_level=0.95, method="wilson") if na else None
    bci = binomtest(both, nb).proportion_ci(confidence_level=0.95, method="wilson") if nb else None
    empirical_denominator = math.sqrt((na / n) * (1 - na / n) * (nb / n) * (1 - nb / n))
    errors = []
    for observed, expected in ((joint, j), (union, theory_union)):
        se = math.sqrt(expected * (1 - expected) / n)
        if not se and abs(observed - expected) > 1e-12:
            raise ValueError("A deterministic event probability has inconsistent counts")
        errors.append(abs(observed - expected) / se if se else 0.0)
    clean = {key: int(value) if isinstance(value, numbers.Integral) and not isinstance(value, bool)
             else float(value) if isinstance(value, numbers.Real) else value for key, value in meta.items()}
    json.dumps(clean, allow_nan=False)
    row = dict(clean)
    row.update(_meta=dict(clean), neither=neither, a_only=aonly, b_only=bonly, both=both,
               marginal_a=na, marginal_b=nb, union_count=nu, joint=joint, union=union,
               theory_union=theory_union, joint_low=float(jci.low), joint_high=float(jci.high),
               union_low=float(uci.low), union_high=float(uci.high),
               exact_joint_low=float(exact.low), exact_joint_high=float(exact.high),
               conditional_b_given_a=both / na if na else None,
               conditional_a_given_b=both / nb if nb else None,
               conditional_b_given_a_low=float(aci.low) if aci else None,
               conditional_b_given_a_high=float(aci.high) if aci else None,
               conditional_a_given_b_low=float(bci.low) if bci else None,
               conditional_a_given_b_high=float(bci.high) if bci else None,
               theory_conditional_b_given_a=j / pa, theory_conditional_a_given_b=j / pb,
               phi=(joint - na * nb / (n * n)) / empirical_denominator if empirical_denominator else None,
               theory_phi=(j - pa * pb) / math.sqrt(pa * (1 - pa) * pb * (1 - pb)),
               mean_error_se=max(errors))
    return row


@deal.pre(lambda project, rows: project in PROJECTS)
@deal.pre(lambda project, rows: isinstance(rows, list) and bool(rows) and all(isinstance(row, dict) for row in rows))
@deal.pre(lambda project, rows: all(row.get("project") == project for row in rows))
@deal.post(lambda result: isinstance(result, list))
@deal.post(lambda result: all(row["replicate"] == 0 and row["seed"] == 0 for row in result))
@deal.ensure(lambda project, rows, result: sum(row["n_samples"] for row in result) == sum(row["n_samples"] for row in rows))
@deal.ensure(lambda project, rows, result: bool(result) and len(result) <= len(rows))
@deal.post(lambda result: all(row["replicates"] == len(row["seeds"]) and row["replicates"] >= 1 for row in result))
@deal.raises(ValueError, TypeError, KeyError, OverflowError)
@deal.has("network")
def pool_rows(project, rows):
    """Pool complete equal-design replicates, including between-run variation.

    Averaging SDs discards information. The within-plus-between decomposition
    below reconstructs the unbiased variance from counts, means and unbiased
    replicate variances. Exact event counts and weighted MSEs pool by addition.
    Duplicate stream identifiers and inconsistent case theories are rejected.
    """
    groups = {}
    for row in rows:
        key = (row["n"],) if project == HOEFLIN else (row["case_index"],) if project == TOWERS else (row["r"], row["k"], row["mode"])
        groups.setdefault(key, []).append(row)
    result = []
    for key in sorted(groups):
        group = groups[key]
        ids = [row["replicate"] for row in group]
        if len(set(ids)) != len(ids):
            raise ValueError("A case contains duplicate replicate identifiers")
        first = group[0]
        # Result constructors preserve the original metadata separately so
        # derived statistics cannot accidentally become new theory inputs.
        if "_meta" not in first:
            required = EVENT_META if project == TOWERS else MOMENT_META | ({"n", "theory_sd", "theory_mse"} if project == HOEFLIN else {"r", "k", "mode"})
            meta = {name: first[name] for name in required}
        else:
            meta = dict(first["_meta"])
        identity = {name: value for name, value in meta.items() if name not in {"n_samples", "replicate", "seed"}}
        for row in group:
            if any(row.get(name) != value for name, value in identity.items()):
                raise ValueError("Replicates disagree about their case identity or theoretical model")
            if not isinstance(row["n_samples"], numbers.Integral) or row["n_samples"] < 2:
                raise ValueError("Every replicate must have at least two observations")
            if project == TOWERS:
                cells = tuple(row[name] for name in ("neither", "a_only", "b_only", "both"))
                if not all(isinstance(count, numbers.Integral) and not isinstance(count, bool) and 0 <= count <= row["n_samples"] for count in cells) or sum(cells) != row["n_samples"]:
                    raise ValueError("An individual replicate has an invalid event partition")
            else:
                if not all(isinstance(row[name], numbers.Real) and not isinstance(row[name], bool) and math.isfinite(float(row[name])) for name in ("mean", "variance", "mse")) or row["variance"] < 0 or row["mse"] < 0:
                    raise ValueError("An individual replicate has invalid moment summaries")
                tails = tuple(row[name] for name in ("count2", "count3", "count_rare"))
                if not all(isinstance(count, numbers.Integral) and not isinstance(count, bool) and 0 <= count <= row["n_samples"] for count in tails) or not tails[0] >= tails[1] >= tails[2]:
                    raise ValueError("An individual replicate has invalid nested event counts")
        total = sum(int(row["n_samples"]) for row in group)
        meta.update(n_samples=total, replicate=0, seed=0)
        if project == TOWERS:
            counts = tuple(sum(int(row[name]) for row in group) for name in ("neither", "a_only", "b_only", "both"))
            pooled = event_result(meta, counts)
        else:
            mean = math.fsum(row["n_samples"] * row["mean"] for row in group) / total
            within = math.fsum((row["n_samples"] - 1) * row["variance"] for row in group)
            between = math.fsum(row["n_samples"] * (row["mean"] - mean) ** 2 for row in group)
            variance = (within + between) / (total - 1)
            mse = math.fsum(row["n_samples"] * row["mse"] for row in group) / total
            counts = tuple(sum(int(row[name]) for row in group) for name in ("count2", "count3", "count_rare"))
            pooled = moment_result(meta, mean, variance, mse, counts)
        pooled.update(replicates=len(group), seeds=[int(row["seed"]) for row in sorted(group, key=lambda row: row["replicate"])])
        result.append(pooled)
    return result
