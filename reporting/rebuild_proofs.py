#!/usr/bin/env python3
"""Rebuild selected proof-complete KOMA-Script books in one Dask graph.

The active, versioned Dask numerical assets are inputs to a document-only
revision. This tool never reruns the random experiment; it typesets the six
KOMA-Script books and records a fresh hash manifest of source and outputs.
XeLaTeX/BibTeX and Poppler perform rendering and Dask schedules tasks.
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

from reporting.provenance import digest, dump
ROOT = Path(__file__).resolve().parents[1]
DOCUMENTS = (
    ("hoeflin-ferguson", "composite_iq_analysis"),
    ("hoeflin-ferguson", "hoeflin_simulations"),
    ("towers-multiple-test-admissions", "towers_admissions_analysis"),
    ("towers-multiple-test-admissions", "towers_simulations"),
    ("sequential-conditional-means", "sequential_conditional_means"),
    ("sequential-conditional-means", "sequential_simulations"),
    ("iq-test-differences", "iq_test_differences"),
    ("iq-test-differences", "iq_difference_simulations"),
)
RECORD = ROOT.joinpath("reporting", "build-records", "revision.json")
CAMPAIGN = ROOT.joinpath("reporting", "run.json")

REQUIRED_PACKAGES = (
    "fontspec", "unicode-math", "tcolorbox", "tabularray", "hyperref",
    "bookmark", "mathtools", "microtype", "scrlayer-scrpage", "cleveref",
    "amsthm", "booktabs", "graphicx", "float", "enumitem", "scrhack",
    "listings", "natbib", "xurl",
)


@deal.pre(lambda: CAMPAIGN.is_file())
@deal.pre(lambda: ROOT.is_dir() and ROOT.joinpath("analyses").is_dir())
@deal.post(lambda result: isinstance(result, dict) and result["verified"] is True)
@deal.post(lambda result: isinstance(result["inputs"], list) and len(result["inputs"]) >= 20)
@deal.post(lambda result: all("/simulation-data/" in row["path"] for row in result["inputs"]))
@deal.post(lambda result: all(len(row["sha256"]) == 64 for row in result["inputs"]))
@deal.post(lambda result: len({row["path"] for row in result["inputs"]}) == len(result["inputs"]))
@deal.post(lambda result: result["run_schema"] == "dask-simulation-reports-v1")
@deal.ensure(lambda result: result["campaign_sha256"] == digest(CAMPAIGN))
@deal.raises(OSError, ValueError, TypeError, KeyError, JSONDecodeError)
@deal.has("network", "read")
@deal.post(lambda result: all(row["path"].startswith("analyses/") for row in result["inputs"]))
@deal.post(lambda result: all(row["path"].endswith((".csv", ".tex", ".json")) for row in result["inputs"]))
@deal.post(lambda result: all(set(row) == {"path", "sha256"} for row in result["inputs"]))
@deal.post(lambda result: all(all(character in "0123456789abcdef" for character in row["sha256"]) for row in result["inputs"]))
def retained_data():
    """Snapshot current Python/Dask data without calling a native simulator.

    Input contents are version-controlled and hashed at build time. This
    function checks that the source manifest describes a Dask experiment;
    it does not assert unchanged bytes from an earlier removed campaign.
    """
    run = json.loads(CAMPAIGN.read_text(encoding="utf-8"))
    if run["schema"] != "dask-simulation-reports-v1":
        raise ValueError("Expected the Python/Dask simulation source manifest")
    paths = []
    for project in sorted({row[0] for row in DOCUMENTS}):
        folder = ROOT.joinpath("analyses", project, "simulation-data")
        paths.extend(path for path in folder.iterdir()
                     if path.is_file() and path.suffix in {".csv", ".tex", ".json"}
                     and not path.name.startswith("historical"))
    if len(paths) < 20:
        raise ValueError("Missing active Dask simulation assets")
    inputs = [{"path": path.relative_to(ROOT).as_posix(), "sha256": digest(path)}
              for path in sorted(set(paths))]
    return {"verified": True, "campaign_sha256": digest(CAMPAIGN),
            "run_schema": run["schema"], "inputs": inputs}


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
@deal.has("network", "read", "write", "syscall")
@deal.post(lambda result: result["margin_mm"] == 16)
@deal.post(lambda result: len(result["actual_margins_pt"]) == 4)
@deal.post(lambda result: result["required_packages"] == list(REQUIRED_PACKAGES))
def build_document(document, retained):
    """Typeset, check the final engine log, and render every page in a task.

    Each report has separate output/intermediate paths. Shared appendices are
    read-only inputs, so parallel builds cannot race on a generated asset.
    Build stdout is new revision evidence; the Dask simulation data is
    never overwritten by this document-only task. TeX diagnostics fail closed before an artifact is
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


@deal.pre(lambda results, retained, graph_tasks: isinstance(results, list) and 0 < len(results) <= len(DOCUMENTS))
@deal.pre(lambda results, retained, graph_tasks: all((r["project"], r["stem"]) in DOCUMENTS for r in results))
@deal.pre(lambda results, retained, graph_tasks: len({(r["project"],r["stem"]) for r in results}) == len(results))
@deal.pre(lambda results, retained, graph_tasks: type(graph_tasks) is int and graph_tasks >= len(results) + 1)
@deal.pre(lambda results, retained, graph_tasks: retained["verified"] is True)
@deal.post(lambda result: result["schema"] == "dask-python-report-build-v1")
@deal.post(lambda result: result["simulation_rerun"] is False)
@deal.post(lambda result: result["reports"] and all(len(r["sha256"]) == 64 for r in result["reports"]))
@deal.ensure(lambda results, retained, graph_tasks, result: result["reports"] == results and result["graph_tasks"] == graph_tasks)
@deal.ensure(lambda results, retained, graph_tasks, result: result["retained_dask_data"] == retained)
@deal.raises(OSError, ValueError, TypeError, KeyError, JSONDecodeError)
@deal.has("network", "read", "write")
@deal.post(lambda result: result["scheduler"] == "processes")
@deal.post(lambda result: result["matplotlib_used"] is False)
@deal.ensure(lambda results, retained, graph_tasks, result: result["dask_version"] == dask.__version__)
def record_revision(results, retained, graph_tasks):
    """Hash document sources/outputs without relabeling old numerical draws."""
    if retained_data() != retained:
        raise ValueError("Dask numerical assets changed during document build")
    sources = list(ROOT.joinpath("reporting").glob("*.tex")) + list(ROOT.joinpath("reporting").glob("*.bib"))
    sources += [Path(__file__).resolve(), ROOT.joinpath("reporting", "provenance.py"),
                ROOT.joinpath("library", "python", "statistics.py"),
                ROOT.joinpath("AGENTS.md"), ROOT.joinpath("requirements-dev.txt")]
    for project in sorted({item[0] for item in DOCUMENTS}):
        folder = ROOT.joinpath("analyses", project)
        sources += list(folder.glob("*.tex")) + list(folder.glob("*.bib"))
    record = {"schema": "dask-python-report-build-v1", "date": "2026-11-16",
              "scheduler": "processes", "dask_version": dask.__version__,
              "graph_tasks": graph_tasks, "reports": results,
              "simulation_rerun": False, "matplotlib_used": False,
              "retained_dask_data": retained,
              "sources": [{"path": item.relative_to(ROOT).as_posix(), "sha256": digest(item)}
                          for item in sorted(set(sources))]}
    RECORD.parent.mkdir(parents=True, exist_ok=True)
    dump(RECORD, record)
    return record


@deal.pre(lambda argv=None: argv is None or isinstance(argv, list) and all(isinstance(arg, str) and "\x00" not in arg for arg in argv))
@deal.pre(lambda argv=None: ROOT.is_dir())
@deal.pre(lambda argv=None: CAMPAIGN.is_file())
@deal.pre(lambda argv=None: bool(DOCUMENTS) and len(DOCUMENTS) == 6)
@deal.pre(lambda argv=None: RECORD.suffix == ".json")
@deal.ensure(lambda argv=None, result=None: result != 0 or RECORD.is_file())
@deal.post(lambda result: result == 0)
@deal.raises(OSError, ValueError, TypeError, KeyError, JSONDecodeError, StopIteration, IndexError, OverflowError, csv.Error, subprocess.SubprocessError, CalledProcessError, TimeoutExpired, RuntimeError, SystemExit)
@deal.has("network", "read", "write", "syscall", "import", "stdout", "stderr")
@deal.pre(lambda argv=None: all(isinstance(document, tuple) and len(document) == 2 for document in DOCUMENTS))
@deal.pre(lambda argv=None: all(ROOT.joinpath("analyses", project).is_dir() for project, _ in DOCUMENTS))
@deal.pre(lambda argv=None: ROOT.joinpath("reporting", "provenance.py").is_file())
@deal.pre(lambda argv=None: isinstance(REQUIRED_PACKAGES, tuple) and len(REQUIRED_PACKAGES) >= 18)
@deal.pre(lambda argv=None: all(isinstance(package, str) and bool(package) for package in REQUIRED_PACKAGES))
@deal.pre(lambda argv=None: all(" " not in package for package in REQUIRED_PACKAGES))
def main(argv=None):
    """Schedule the chosen documents from existing versioned Dask data."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--workers", type=int, choices=range(1, 5), default=2)
    parser.add_argument("--simulations-only", action="store_true",
                        help="Build the three simulation books; leave analytical PDFs untouched")
    args = parser.parse_args(argv)
    documents = tuple(document for document in DOCUMENTS if not args.simulations_only or document[1].endswith("simulations"))
    retained = dask.delayed(retained_data)()
    builds = [dask.delayed(build_document)(document, retained) for document in documents]
    graph_tasks = len(dask.highlevelgraph.HighLevelGraph.merge(*(item.dask for item in builds))) + 1
    terminal = dask.delayed(record_revision)(builds, retained, graph_tasks)
    try:
        record = dask.compute(terminal, scheduler="processes", num_workers=args.workers)[0]
    except RemoteException as error:
        raise RuntimeError("Dask report build failed; inspect reporting/build-records build logs") from error
    print(json.dumps(record, indent=2))
    return 0


if __name__ == "__main__":
    deal.enable(warn=False)
    raise SystemExit(main())
