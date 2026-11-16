# Composite IQ: Checked Claims

**Author/researcher:** Anders Hellström.

> **AI DISCLOSURE:** OpenAI ChatGPT/Codex and collaborating AI systems have substantially assisted with the mathematical analyses, program development, formalization, simulation reporting, editing, and repository maintenance. Automated checks do not constitute independent human review.

This repository examines composite IQ scores, multiple-test admissions, and sequential conditional means under explicitly stated statistical models. **The maintained computational stack is Python, Dask, NumPy/SciPy, and Deal. Rocq is used for separately scoped mathematical proofs.** The former discontinued alternate-engine simulation and verification implementation has been removed from the current tree; its historical revisions remain accessible through Git history. No retired proof run is evidence that current Python is formally verified.

## Six reports

| Analysis | Mathematical report | Simulation methods and results |
|---|---|---|
| Hoeflin/Ferguson: combining IQ scores | [PDF](analyses/hoeflin-ferguson/output/pdf/composite_iq_analysis.pdf) / [XeLaTeX](analyses/hoeflin-ferguson/composite_iq_analysis.tex) | [PDF](analyses/hoeflin-ferguson/output/pdf/hoeflin_simulations.pdf) / [XeLaTeX](analyses/hoeflin-ferguson/hoeflin_simulations.tex) |
| Towers: multiple-test admissions | [PDF](analyses/towers-multiple-test-admissions/output/pdf/towers_admissions_analysis.pdf) / [XeLaTeX](analyses/towers-multiple-test-admissions/towers_admissions_analysis.tex) | [PDF](analyses/towers-multiple-test-admissions/output/pdf/towers_simulations.pdf) / [XeLaTeX](analyses/towers-multiple-test-admissions/towers_simulations.tex) |
| Sequential conditional means | [PDF](analyses/sequential-conditional-means/output/pdf/sequential_conditional_means.pdf) / [XeLaTeX](analyses/sequential-conditional-means/sequential_conditional_means.tex) | [PDF](analyses/sequential-conditional-means/output/pdf/sequential_simulations.pdf) / [XeLaTeX](analyses/sequential-conditional-means/sequential_simulations.tex) |

**Publication status:** Source revisions and regenerated PDF artifacts must be checked together. The checked-in PDF files may predate the Python-only migration until a new XeLaTeX build is completed and committed; a PDF link alone does not establish that the PDF reflects the current TeX source.

## Python/Dask/Deal workflow

The shared engine [`reporting/simulate.py`](reporting/simulate.py) constructs seeded, chunked Dask task graphs for all three studies. [`reporting/assets.py`](reporting/assets.py) writes numerical tables, scalar plotting data and structured summaries; [`reporting/provenance.py`](reporting/provenance.py) records content hashes. [`library/python/`](library/python/) owns shared numerical/statistical helpers. Independent model calculations use established NumPy/SciPy operations rather than bespoke probability integrations. The simulation-data directories retain the actual recorded Python/Dask results. The original numerical campaign is not silently rerun by documentation edits.

Using Python 3.13 and the requirements file:

```sh
python3 -m venv .venv
. .venv/bin/activate
python -m pip install -r requirements-dev.txt
make check PYTHON=.venv/bin/python
make simulations PYTHON=.venv/bin/python
make report-books PYTHON=.venv/bin/python
```

The simulation command executes a **new** Monte Carlo campaign and rewrites its recorded assets; document-only builds reuse already recorded Dask data. XeLaTeX/KOMA-Script and Poppler are required for document production. See [the reporting guide](reporting/README.md) and each analysis README for details.

## Contracts, proofs and scope

Every maintained named Python function must have at least five genuine Deal decorators; the project's development target is ten or more meaningfully distinct contracts wherever justified. Deal checks, static lint and property tests verify selected code properties, not the statistical validity of the underlying model or the numerical correctness of unverified external libraries. The [Rocq corpus](rocq/README.md) checks explicitly stated finite and algebraic theorems under their premises, not a general Gaussian sampling law, numerical error certificate, or empirically observed human IQ distribution.

The mathematical reports distinguish deductions from model assumptions and observed simulation results. In particular, simulations do not prove a one-in-a-million empirical tail probability, admissions fractions in a real organization, independent test administrations, or a real-world latent-ability model.

## Provenance and disclosure

Historical discontinued alternate-engine files, old verification campaigns and experimental comparisons were removed from the **active tree** as part of the Python/Dask transition. Git history preserves the earlier source revisions and their methodological context; those outputs must not be attributed to the current Python/Dask implementation. New numerical results require a fresh explicit Dask run with recorded configuration and model assumptions. No participant data were collected for the model simulations.

**Full AI disclosure:** The requesting researcher Anders Hellström defined the questions and priorities. OpenAI ChatGPT/Codex and AI-assisted workflows contributed textual and mathematical drafts, Python/Dask source, Deal contracts, Rocq proof scripts, report structure, verification procedures, documentation and repository edits. Automated mathematics and CI apply only to their exact statements and checked revisions. Independent human peer review, empirical psychometric validation, guaranteed PRNG independence and complete per-line human/AI authorship are not claimed. The report PDFs contain their own AI disclosure appendices. Repository licensing applies to original materials subject to third-party rights.
