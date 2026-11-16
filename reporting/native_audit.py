"""Reinterpret immutable native observations in the Dask report graph.

This is a deterministic results audit, not a random experiment, replay of an
Ada executable, or GNATprove run. Shared statistics and SciPy supply interval
calculations. Their probability interpretation requires the ideal model
proved in the reports; it is not inferred from passing this audit.
"""
import csv
import json
from json import JSONDecodeError
import math
from pathlib import Path

import deal

from library.python.statistics import event_result, moment_result

ROOT = Path(__file__).resolve().parents[1]
PROJECTS = ("hoeflin-ferguson", "towers-multiple-test-admissions", "sequential-conditional-means")
SOURCES = (
    "verification/evidence/five-contracts-computer10-20261104/runtime-final/hoeflin/check/simulation.csv",
    "verification/evidence/five-contracts-computer10-20261104/runtime-final/towers/check/simulation.csv",
    "analyses/sequential-conditional-means/evidence/campaign-20261114-current/runtime/simulation.csv",
)
COUNTS = (8, 4, 46)


@deal.pre(lambda project: project in PROJECTS)
@deal.pre(lambda project: ROOT.joinpath(SOURCES[PROJECTS.index(project)]).is_file())
@deal.post(lambda result: isinstance(result, dict) and result["historical_rows_equal"] is True)
@deal.ensure(lambda project, result: result["project"] == project)
@deal.ensure(lambda project, result: result["source"] == SOURCES[PROJECTS.index(project)])
@deal.ensure(lambda project, result: len(result["rows"]) == COUNTS[PROJECTS.index(project)])
@deal.post(lambda result: all(row["n_samples"] >= 2 for row in result["rows"]))
@deal.post(lambda result: result["random_draws_generated"] == 0)
@deal.post(lambda result: result["native_execution_performed"] is False)
@deal.post(lambda result: all(row["sample_variance"] >= 0 for row in result["rows"] if "sample_variance" in row))
@deal.raises(OSError, ValueError, TypeError, KeyError, StopIteration, IndexError, OverflowError, csv.Error, JSONDecodeError)
@deal.has("read")
def audit_project(project):
    """Check raw native rows and derive a comparison without pooling engines.

    The retained Dask summaries pin the complete historical CSV records, so
    equality here verifies that the latest named native campaign really uses
    those observations. All 46 sequential rows are audited, including rows
    outside the 24 Dask laws. Finite reference moments come from the native
    calculation CSV, itself independently matrix-checked in its campaign;
    this is a consistency audit, not an independent reproof of those targets.
    """
    index = PROJECTS.index(project)
    with ROOT.joinpath(SOURCES[index]).open(encoding="utf-8") as stream:
        native = list(csv.DictReader(line for line in stream if not line.startswith("#")))
    summary = json.loads(ROOT.joinpath("analyses", project, "simulation-data", "summary.json").read_text(encoding="utf-8"))
    if len(native) != COUNTS[index] or native != summary["historical"]:
        raise ValueError("Native records differ from the retained Dask historical inputs")
    pooled = summary["pooled"]
    calculations = []
    if index == 2:
        with ROOT.joinpath(SOURCES[index]).with_name("calculation.csv").open(encoding="utf-8") as stream:
            calculations = list(csv.DictReader(stream))
    rows = []
    for position, raw in enumerate(native):
        samples = int(raw["trials"])
        if index == 1:
            # Reuse the canonical four-cell/conditional-denominator routines.
            target = next(row for row in pooled if row["case_index"] == position + 1)
            meta = dict(target["_meta"], n_samples=samples, replicate=0, seed=int(raw["seed"]))
            counts = tuple(int(raw[name]) for name in ("neither", "a_only", "b_only", "both"))
            interpreted = event_result(meta, counts)
            for source_key, result_key in (("marginal_a", "marginal_a"), ("marginal_b", "marginal_b"), ("union", "union_count"), ("joint_fraction", "joint"), ("conditional_b_given_a", "conditional_b_given_a"), ("conditional_a_given_b", "conditional_a_given_b"), ("joint_wilson_lower", "joint_low"), ("joint_wilson_upper", "joint_high")):
                if not math.isclose(float(raw[source_key]), interpreted[result_key], rel_tol=1e-12, abs_tol=1e-12):
                    raise ValueError("Native event projection/interval mismatch: " + source_key)
            rows.append({"case": raw["case"], **{key: value for key, value in interpreted.items() if key != "_meta"},
                         "dask_joint": target["joint"], "dask_union": target["union"],
                         "joint_difference_native_minus_dask": interpreted["joint"] - target["joint"]})
            continue
        if index == 0:
            size = int(raw["tests"])
            target = next(row for row in pooled if row["n"] == size)
            meta = dict(target["_meta"], n_samples=samples, replicate=0, seed=20261030)
            mean, variance = float(raw["mean_composite_z"]), float(raw["variance_composite_z"])
            counts = tuple(int(raw[name]) for name in ("above2", "above3", "above_rare"))
            interpreted = moment_result(meta, mean, variance, counts=counts)
            # Native HF did not record latent-factor MSE. Never present the
            # helper's unused default value as an observed native MSE.
            row = {"n": size, "n_samples": samples, "sample_mean": mean, "sample_variance": variance,
                   "mean_error_se": interpreted["mean_error_se"],
                   "count2": counts[0], "count3": counts[1], "count_rare": counts[2],
                   "dask_sample_mean": target["mean"], "dask_sample_variance": target["variance"]}
            row.update({key: interpreted[key] for key in ("rate2_low", "rate2_high", "rate3_low", "rate3_high", "rare_low", "rare_high")})
            rows.append(row)
            continue
        mode, r, k = raw["mode"].strip(), int(raw["r"]), int(raw["k"])
        correlation, anchor = float(raw["c"]), float(raw["a_z"])
        # Find the same finite case, or an anchor row carrying its limit.
        calculation = next(item for item in calculations if int(item["r"]) == r and
                           (int(item["k"]) == k or mode.endswith("_limit")) and
                           math.isclose(float(item["c"]), correlation, abs_tol=1e-13) and
                           math.isclose(float(item["a_z"]), anchor, abs_tol=1e-13))
        suffix = "_limit" if mode.endswith("_limit") else ""
        conditional = mode.startswith("conditional")
        mu = float(calculation["mean" + suffix + "_z"]) if conditional else 0.0
        variance = float(calculation[("conditional" if conditional else "population") + "_variance" + suffix])
        meta = {"project": project, "r": r, "k": k, "mode": mode, "n_samples": samples,
                "replicate": position, "seed": int(raw["seed"]), "theory_mean": mu, "theory_variance": variance}
        interpreted = moment_result(meta, float(raw["sample_mean_z"]), float(raw["sample_variance_z"]))
        row = {key: interpreted[key] for key in ("r", "k", "mode", "n_samples", "seed", "theory_mean", "theory_variance", "mean_error_se", "mean_iq", "sd_iq", "theory_sd_iq")}
        row.update(c=correlation, a_z=anchor, sample_mean=interpreted["mean"], sample_variance=interpreted["variance"])
        # Only the IQ150/c=.6 laws are present in the Dask campaign. Other
        # native cases retain a null comparison instead of a fabricated row.
        match = next((item for item in pooled if item["r"] == r and item["k"] == k and item["mode"] == mode and
                      math.isclose(correlation, .6) and math.isclose(anchor, 3.3333333333333335)), None)
        row["dask_sample_mean"] = match["mean"] if match is not None else None
        row["dask_sample_variance"] = match["variance"] if match is not None else None
        rows.append(row)
    return {"project": project, "source": SOURCES[index], "historical_rows_equal": True,
            "random_draws_generated": 0, "native_execution_performed": False, "rows": rows}
