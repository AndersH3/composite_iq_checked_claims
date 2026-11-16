#!/usr/bin/env python3
"""Rebuild selected proof-complete KOMA-Script books in one Dask graph.

The November simulation campaign is immutable input. This document revision
neither reruns its random experiment nor relabels its old source hashes as
current. Maintained XeLaTeX/BibTeX and Poppler tools handle typesetting and
rendering; Dask schedules those tasks and the final revision manifest.
"""
import argparse
import csv
import json
from json import JSONDecodeError
import os
from pathlib import Path
import re
import subprocess
from subprocess import CalledProcessError, TimeoutExpired

import dask
from dask.multiprocessing import RemoteException
import deal

from verification.run_computer10 import digest, dump
# Keep the caller's imported grid distinct from audit_project's own PROJECTS
# global. Deal's static cross-module extractor otherwise builds an invalid
# import-node location when compiling that callee's unchanged preconditions.
from reporting.native_audit import PROJECTS as AUDIT_PROJECTS, audit_project

ROOT = Path(__file__).resolve().parents[1]
DOCUMENTS = (
    ("hoeflin-ferguson", "composite_iq_analysis"),
    ("hoeflin-ferguson", "hoeflin_simulations"),
    ("towers-multiple-test-admissions", "towers_admissions_analysis"),
    ("towers-multiple-test-admissions", "towers_simulations"),
    ("sequential-conditional-means", "sequential_conditional_means"),
    ("sequential-conditional-means", "sequential_simulations"),
)
RECORD = ROOT.joinpath("reporting", "contextual-attribution", "revision.json")
CAMPAIGN = ROOT.joinpath("reporting", "run.json")
# Pin the actual native experiment and validation files used by the expanded
# reports, not merely the old Dask reproduction's historical CSV copies.
# Reading an archived manifest does not rerun GNATprove or prove current code.
NATIVE_CAMPAIGN = "verification/evidence/five-contracts-computer10-20261104"
SEQUENTIAL_CAMPAIGN = "analyses/sequential-conditional-means/evidence/campaign-20261114-current"
NATIVE_INPUTS = (
    NATIVE_CAMPAIGN + "/manifest.json",
    NATIVE_CAMPAIGN + "/artifacts.json",
    NATIVE_CAMPAIGN + "/REPORT.md",
    NATIVE_CAMPAIGN + "/hoeflin/portfolio/result.json",
    NATIVE_CAMPAIGN + "/towers/portfolio/result.json",
    NATIVE_CAMPAIGN + "/runtime-final/summary.json",
    NATIVE_CAMPAIGN + "/runtime-final/hoeflin/check/simulation.csv",
    NATIVE_CAMPAIGN + "/runtime-final/hoeflin/check/calculations.csv",
    NATIVE_CAMPAIGN + "/runtime-final/hoeflin/check/runtime.json",
    NATIVE_CAMPAIGN + "/runtime-final/hoeflin/check/replay-normal.json",
    NATIVE_CAMPAIGN + "/runtime-final/hoeflin/check/replay-optimized.json",
    NATIVE_CAMPAIGN + "/runtime-final/hoeflin/check/validation-normal.json",
    NATIVE_CAMPAIGN + "/runtime-final/hoeflin/check/validation-optimized.json",
    NATIVE_CAMPAIGN + "/runtime-final/towers/check/simulation.csv",
    NATIVE_CAMPAIGN + "/runtime-final/towers/check/runtime.json",
    NATIVE_CAMPAIGN + "/runtime-final/towers/check/validation-normal.log",
    NATIVE_CAMPAIGN + "/runtime-final/towers/check/validation-optimized.log",
    SEQUENTIAL_CAMPAIGN + "/runtime/simulation.csv",
    SEQUENTIAL_CAMPAIGN + "/runtime/calculation.csv",
    SEQUENTIAL_CAMPAIGN + "/runtime/checks.csv",
    SEQUENTIAL_CAMPAIGN + "/runtime/validation.json",
    SEQUENTIAL_CAMPAIGN + "/campaign.json",
    SEQUENTIAL_CAMPAIGN + "/sources.tar.gz",
    SEQUENTIAL_CAMPAIGN + "/gnatprove.out",
)
REQUIRED_PACKAGES = (
    "fontspec", "unicode-math", "tcolorbox", "tabularray", "hyperref",
    "bookmark", "mathtools", "microtype", "scrlayer-scrpage", "cleveref",
    "amsthm", "booktabs", "graphicx", "float", "enumitem", "scrhack",
    "listings", "natbib", "xurl",
)


@deal.pre(lambda: CAMPAIGN.is_file())
@deal.post(lambda result: isinstance(result, dict) and result["verified"] is True)
@deal.post(lambda result: len(result["campaign_sha256"]) == 64)
@deal.post(lambda result: len(result["inputs"]) > 30)
@deal.post(lambda result: all("/simulation-data/" in row["path"] for row in result["inputs"]))
@deal.post(lambda result: all(len(row["sha256"]) == 64 for row in result["inputs"]))
@deal.post(lambda result: len({row["path"] for row in result["inputs"]}) == len(result["inputs"]))
@deal.post(lambda result: {row["path"] for row in result["native_campaign_inputs"]} == set(NATIVE_INPUTS))
@deal.post(lambda result: all(len(row["sha256"]) == 64 for row in result["native_campaign_inputs"]))
@deal.ensure(lambda *, result: result["campaign_sha256"] == digest(CAMPAIGN))
@deal.raises(OSError, ValueError, TypeError, KeyError, JSONDecodeError)
@deal.has("read")
def retained_data():
    """Reject any changed simulation data, including the historical build logs.

    The original manifest also pins PDFs and old source versions. Those are
    deliberately not asserted current: this operation is revising the PDFs.
    Only the complete, unchanged simulation-data subset is reused here.
    """
    previous = json.JSONDecoder().decode(CAMPAIGN.read_text(encoding="utf-8"))
    inputs = [row for row in previous["outputs"] if "/simulation-data/" in row["path"]]
    if len(inputs) <= 30 or len({row["path"] for row in inputs}) != len(inputs):
        raise ValueError("Incomplete or duplicate retained simulation input inventory")
    for row in inputs:
        source = ROOT.joinpath(row["path"])
        if not source.is_relative_to(ROOT) or digest(source) != row["sha256"]:
            raise ValueError("Retained campaign input hash mismatch: " + row["path"])
    native_inputs = [{"path": name, "sha256": digest(ROOT.joinpath(name))} for name in NATIVE_INPUTS]
    return {"verified": True, "campaign_sha256": digest(CAMPAIGN), "inputs": inputs,
            "native_campaign_inputs": native_inputs}


@deal.pre(lambda document, retained: document in DOCUMENTS)
@deal.pre(lambda document, retained: isinstance(retained, dict) and retained["verified"] is True)
@deal.pre(lambda document, retained: ROOT.joinpath("analyses", document[0], document[1] + ".tex").is_file())
@deal.post(lambda result: isinstance(result, dict) and result["xelatex"] is True)
@deal.post(lambda result: type(result["pages"]) is int and 0 < result["pages"] < 200)
@deal.post(lambda result: len(result["sha256"]) == 64)
@deal.post(lambda result: result["layout_diagnostics"] == [])
@deal.post(lambda result: result["document_class"] == "scrbook" and result["toc"] and result["final_ai_appendix"])
@deal.post(lambda result: result["author"] == "Anders Hellström" and result["name_only_author"] is True)
@deal.ensure(lambda document, retained, result: result["project"] == document[0] and result["stem"] == document[1])
@deal.raises(OSError, ValueError, TypeError, StopIteration, subprocess.SubprocessError, CalledProcessError, TimeoutExpired)
@deal.has("read", "write", "syscall")
def build_document(document, retained):
    """Typeset, check the final engine log, and render every page in a task.

    Each report has separate output/intermediate paths. Shared appendices are
    read-only inputs, so parallel builds cannot race on a generated asset.
    Build stdout is new revision evidence; the old simulation build logs are
    never overwritten. TeX diagnostics fail closed before an artifact is
    described as successfully rebuilt.
    """
    project, stem = document
    directory = ROOT.joinpath("analyses", project)
    evidence = RECORD.parent
    evidence.mkdir(parents=True, exist_ok=True)
    with evidence.joinpath(stem + ".build.txt").open("w", encoding="utf-8") as stream:
        subprocess.run(
            ["latexmk", "-g", "-xelatex", "-outdir=output/pdf", "-interaction=nonstopmode", "-halt-on-error", stem + ".tex"],
            cwd=directory, env={**os.environ, "BIBINPUTS": str(ROOT.joinpath("reporting")) + os.pathsep + str(directory) + os.pathsep},
            stdout=stream, stderr=subprocess.STDOUT, check=True, timeout=240,
        )
    log = directory.joinpath("output", "pdf", stem + ".log").read_text(encoding="utf-8")
    # Validate actual compiler inputs rather than trusting a comment or README.
    inputs = directory.joinpath("output", "pdf", stem + ".fls").read_text(encoding="utf-8")
    loaded = {Path(line[6:]).name for line in inputs.splitlines() if line.startswith("INPUT ")}
    if "scrbook.cls" not in loaded or "This is XeTeX" not in log:
        raise ValueError("Report did not use XeLaTeX and KOMA-Script scrbook: " + stem)
    missing = [name for name in REQUIRED_PACKAGES if name + ".sty" not in loaded]
    if missing:
        raise ValueError("Missing required report packages: " + repr(missing))
    # Geometry reports the actual four outer margins in TeX points. Sixteen
    # millimetres is 45.5244 pt to the log's precision; check both dimensions.
    horizontal = re.search(r"\* h-part:\(L,W,R\)=\(([\d.]+)pt, [\d.]+pt, ([\d.]+)pt\)", log)
    vertical = re.search(r"\* v-part:\(T,H,B\)=\(([\d.]+)pt, [\d.]+pt, ([\d.]+)pt\)", log)
    if horizontal is None or vertical is None:
        raise ValueError("Missing actual geometry margin record: " + stem)
    margins = [float(value) for value in horizontal.groups() + vertical.groups()]
    if not all(abs(value - 45.5244) < 0.001 for value in margins):
        raise ValueError("Report does not have four 16 mm margins: " + stem)
    toc = directory.joinpath("output", "pdf", stem + ".toc").read_text(encoding="utf-8")
    chapters = [line for line in toc.splitlines() if "\\contentsline {chapter}" in line]
    if not chapters or "AI disclosure" not in chapters[-1] or "appendix." not in chapters[-1]:
        raise ValueError("Full AI disclosure is not the final appendix chapter: " + stem)
    # Only the final XeLaTeX log is checked: intermediate passes legitimately
    # have unresolved references before BibTeX/latexmk resolve dependencies.
    diagnostics = re.findall(r"(?:Overfull|Underfull) \\[hv]box[^\n]*|Missing character:[^\n]*|[^\n]*(?:undefined references|undefined citations|multiply defined|Citation[^\n]*undefined|Reference[^\n]*undefined)[^\n]*", log)
    if diagnostics:
        raise ValueError("Unresolved typesetting diagnostics for " + stem + ": " + repr(diagnostics))
    pdf = directory.joinpath("output", "pdf", stem + ".pdf")
    info = subprocess.run(["pdfinfo", str(pdf)], capture_output=True, text=True, check=True, timeout=30).stdout
    author = next((line.split(":", 1)[1].strip() for line in info.splitlines() if line.startswith("Author:")), "")
    if author != "Anders Hellström":
        raise ValueError("Incorrect PDF author metadata: " + stem)
    title = subprocess.run(["pdftotext", "-f", "1", "-l", "1", str(pdf), "-"], capture_output=True, text=True, check=True, timeout=30).stdout
    # Check the author declaration as well as extracted text: a prefixed name
    # or a second role line is not an acceptable replacement for the author.
    source = directory.joinpath(stem + ".tex").read_text(encoding="utf-8")
    declarations = re.findall(r"\\author\{([^\n]*)\}", source)
    title_lines = [line.strip() for line in title.splitlines() if line.strip()]
    if declarations != [r"\ProjectAuthor"] or title_lines.count("Anders Hellström") != 1:
        raise ValueError("Author must be the name alone in source and title page: " + stem)
    pages = int(next(line.split(":", 1)[1] for line in info.splitlines() if line.startswith("Pages:")))
    render = directory.joinpath("tmp", "pdfs", "contextual-attribution", stem)
    render.mkdir(parents=True, exist_ok=True)
    # A shorter revised PDF must not leave a stale final page in visual QA.
    # Only this report's temporary, reproducible page images are removed.
    for stale in render.glob("page-*.png"):
        stale.unlink()
    subprocess.run(["pdftoppm", "-scale-to", "1200", "-png", str(pdf), str(render.joinpath("page"))], capture_output=True, check=True, timeout=180)
    return {"project": project, "stem": stem, "pdf": pdf.relative_to(ROOT).as_posix(),
            "sha256": digest(pdf), "pages": pages, "xelatex": True, "layout_diagnostics": [],
            "document_class": "scrbook", "required_packages": list(REQUIRED_PACKAGES),
            "toc": True, "final_ai_appendix": True, "margin_mm": 16,
            "actual_margins_pt": margins, "author": author,
            "name_only_author": True}


@deal.pre(lambda results, retained, graph_tasks, audits: isinstance(results, list) and 0 < len(results) <= len(DOCUMENTS))
@deal.pre(lambda results, retained, graph_tasks, audits: len({(row["project"], row["stem"]) for row in results}) == len(results))
@deal.pre(lambda results, retained, graph_tasks, audits: all((row["project"], row["stem"]) in DOCUMENTS for row in results))
@deal.pre(lambda results, retained, graph_tasks, audits: type(graph_tasks) is int and graph_tasks >= len(results) + 5)
@deal.pre(lambda results, retained, graph_tasks, audits: len(audits) == 3 and {row["project"] for row in audits} == set(AUDIT_PROJECTS))
@deal.post(lambda result: result["schema"] == "dask-contextual-attribution-v1")
@deal.post(lambda result: result["simulation_rerun"] is False)
@deal.post(lambda result: result["new_native_proof_run"] is False)
@deal.ensure(lambda results, retained, graph_tasks, audits, result: result["reports"] == results)
@deal.ensure(lambda results, retained, graph_tasks, audits, result: result["retained_campaign"] == retained)
@deal.ensure(lambda results, retained, graph_tasks, audits, result: result["graph_tasks"] == graph_tasks)
@deal.ensure(lambda results, retained, graph_tasks, audits, result: result["native_results_audit"] == audits)
@deal.raises(OSError, ValueError, TypeError, KeyError, JSONDecodeError)
@deal.has("read", "write")
def record_revision(results, retained, graph_tasks, audits):
    """Pin this revision while keeping original campaign and evidence intact.

    Hash all TeX/Bib sources in each project because a main document can input
    several project appendices as well as the shared foundations. Rendered
    PNGs are temporary QA assets; PDF bytes are the versioned deliverables.
    A second input audit detects accidental writes during parallel builds.
    """
    if retained_data() != retained:
        raise ValueError("Retained simulation inputs changed during the document revision")
    sources = list(ROOT.joinpath("reporting").glob("*.tex")) + list(ROOT.joinpath("reporting").glob("*.bib"))
    sources += [Path(__file__).resolve(), ROOT.joinpath("reporting", "native_audit.py"),
                ROOT.joinpath("library", "python", "statistics.py"), ROOT.joinpath("verification", "run_computer10.py"),
                ROOT.joinpath("AGENTS.md"), ROOT.joinpath("requirements-dev.txt")]
    for project in sorted({document[0] for document in DOCUMENTS}):
        directory = ROOT.joinpath("analyses", project)
        sources += list(directory.glob("*.tex")) + list(directory.glob("*.bib"))
    record = {"schema": "dask-contextual-attribution-v1", "date": "2026-11-16",
              "scheduler": "processes", "dask_version": dask.__version__,
              "graph_tasks": graph_tasks, "reports": results, "native_results_audit": audits,
              "simulation_rerun": False, "new_native_proof_run": False, "matplotlib_used": False,
              "retained_campaign": retained,
              "sources": [{"path": path.relative_to(ROOT).as_posix(), "sha256": digest(path)} for path in sorted(set(sources))]}
    dump(RECORD, record)
    return record


@deal.pre(lambda argv=None: argv is None or isinstance(argv, list) and all(isinstance(arg, str) and "\x00" not in arg for arg in argv))
@deal.pre(lambda argv=None: ROOT.is_dir())
@deal.post(lambda result: result == 0)
@deal.raises(OSError, ValueError, TypeError, KeyError, JSONDecodeError, StopIteration, IndexError, OverflowError, csv.Error, subprocess.SubprocessError, CalledProcessError, TimeoutExpired, RuntimeError, SystemExit)
@deal.has("read", "write", "syscall", "import", "stdout", "stderr")
def main(argv=None):
    """Schedule the chosen books after their immutable experiment input audit."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--workers", type=int, choices=range(1, 5), default=2)
    parser.add_argument("--simulations-only", action="store_true",
                        help="Build the three simulation books; leave analytical PDFs untouched")
    args = parser.parse_args(argv)
    documents = tuple(document for document in DOCUMENTS if not args.simulations_only or document[1].endswith("simulations"))
    retained = dask.delayed(retained_data)()
    builds = [dask.delayed(build_document)(document, retained) for document in documents]
    audits = [dask.delayed(audit_project)(project) for project in AUDIT_PROJECTS]
    graph_tasks = len(dask.highlevelgraph.HighLevelGraph.merge(*(item.dask for item in builds + audits))) + 1
    terminal = dask.delayed(record_revision)(builds, retained, graph_tasks, audits)
    try:
        record = dask.compute(terminal, scheduler="processes", num_workers=args.workers)[0]
    except RemoteException as error:
        raise RuntimeError("Dask report build failed; inspect reporting/contextual-attribution build logs") from error
    print(json.dumps(record, indent=2))
    return 0


if __name__ == "__main__":
    deal.enable(warn=False)
    raise SystemExit(main())
