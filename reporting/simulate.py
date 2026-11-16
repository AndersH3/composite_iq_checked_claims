#!/usr/bin/env python3
"""Dask-native simulation, analysis, asset and XeLaTeX task graphs.

Fresh random arrays, reductions and report production are Dask tasks;
no retired native implementation or historical CSV input is required.
Small scalar reference calculations reuse the maintained SciPy code inside
Dask delayed tasks. No expensive computation happens during graph creation.
"""
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

PROJECTS = ("hoeflin-ferguson", "towers-multiple-test-admissions", "sequential-conditional-means")
COUNTS = (1, 2, 3, 4, 5, 10, 100, 1000)
SEEDS = (20261114, 20261115, 20261116, 20261117)


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
@deal.has("read", "import")
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
@deal.has("read", "import", "random")
@deal.raises(ValueError, TypeError, OverflowError, NotImplementedError)
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
@deal.has("read", "import", "random")
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
@deal.has("read", "import", "random")
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


@deal.pre(lambda project, rows, reference, config: project in PROJECTS)
@deal.pre(lambda project, rows, reference, config: isinstance(rows, list) and bool(rows))
@deal.pre(lambda project, rows, reference, config: isinstance(reference, dict) and reference["project"] == project)
@deal.ensure(lambda project, rows, reference, config, result: result["project"] == project)
@deal.post(lambda result: isinstance(result, dict) and bool(result["files"]))
@deal.raises(OSError, ValueError, TypeError, KeyError, OverflowError, csv.Error)
@deal.has("read", "write")
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
@deal.has("read", "write", "syscall")
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
@deal.has("read", "write")
def finalize_run(results, config, task_count):
    """Hash the actual source/data/PDF artifacts in the final Dask task.

    This manifest is excluded from its own output list to avoid a circular
    self-hash. Python source, configuration and Dask data are hashed directly.
    Fresh figures are TeX/PGFPlots output; no plotting runtime is imported.
    """
    source_paths = list(ROOT.joinpath("reporting").glob("*.py")) + list(ROOT.joinpath("reporting").glob("*.tex")) + list(ROOT.joinpath("reporting").glob("*.bib"))
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
@deal.raises(OSError, ValueError, TypeError, KeyError, ImportError, OverflowError, NotImplementedError, csv.Error, subprocess.SubprocessError, CalledProcessError, TimeoutExpired, RuntimeError, SystemExit)
@deal.has("read", "write", "syscall", "import", "random", "stdout", "stderr")
def main(argv=None):
    """Execute one shared graph for all three sub-projects, not a case loop of compute calls."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--trials", type=int, default=1_000_000)
    parser.add_argument("--chunk", type=int, default=50_000)
    parser.add_argument("--replicates", type=int, choices=range(1, 5), default=4)
    parser.add_argument("--workers", type=int, default=2)
    parser.add_argument("--pdf", action="store_true", help="Build and render all three XeLaTeX reports after analysis")
    args = parser.parse_args(argv)
    if not 2 <= args.trials <= 1_000_000 or not 1 <= args.chunk or not 1 <= args.workers <= 8:
        parser.error("trials must be 2..1000000, chunk positive, workers1..8")
    config = {"trials": args.trials, "chunk": min(args.chunk, args.trials), "replicates": args.replicates,
              "seeds": list(SEEDS[:args.replicates]), "scheduler": "processes", "workers": args.workers,
              "versions": {name: importlib.metadata.version(name) for name in ("dask", "numpy", "scipy", "deal")}}
    references = {project: dask.delayed(reference_data)(project) for project in PROJECTS}
    graphs = {PROJECTS[0]: graph_hoeflin(config), PROJECTS[1]: graph_towers(config, references[PROJECTS[1]]), PROJECTS[2]: graph_sequential(config)}
    terminals = [dask.delayed(analyze_and_write)(project, graphs[project], references[project], config) for project in PROJECTS]
    if args.pdf:
        terminals = [dask.delayed(build_report)(terminal) for terminal in terminals]
    # Process workers isolate Deal's runtime side-effect instrumentation while
    # retaining Dask parallelism. Array chunks and seeds determine the draws.
    task_count = len(dask.highlevelgraph.HighLevelGraph.merge(*(terminal.dask for terminal in terminals))) + 1
    terminal = dask.delayed(finalize_run)(terminals, config, task_count)
    try:
        record = dask.compute(terminal, scheduler="processes", num_workers=args.workers)[0]
    except RemoteException as error:
        # Dask may synthesize dynamic remote exception classes. Give the CLI
        # a stable typed failure boundary and retain the original traceback.
        raise RuntimeError("Dask report task failed; inspect the chained error and project build logs") from error
    print(json.dumps(record, indent=2))
    return 0


if __name__ == "__main__":
    deal.enable(warn=False)
    raise SystemExit(main())
