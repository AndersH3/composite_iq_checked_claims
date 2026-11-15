# KOMA-Script book-format validation

The six maintained PDF reports were rebuilt on 15 November 2026 as XeLaTeX KOMA-Script `scrbook` volumes. Every volume uses A4 paper, one-sided chapters, four 16 mm outer margins, a native overview and table of contents, and full AI disclosure as its final appendix after the bibliography.

| Project | Main volume | Simulation volume |
|---|---:|---:|
| Hoeflin/Ferguson | 30 pages | 29 pages |
| Towers admissions | 30 pages | 28 pages |
| Sequential conditional means | 42 pages | 29 pages |

All **188 final pages** were visually reviewed through complete contact sheets and selected full-page images. Final checks covered title pages, contents, chapter and appendix numbering, mathematical proofs and certificates, tables and charts, claim maps, bibliographies, headers/folios and final disclosures. Short computational/bibliographic continuation pages were reflowed without changing their conclusions, numbers or trust limits. The final logs have no unresolved references/citations, overfull or underfull boxes, missing characters or duplicate labels.

## Reproduce

From the repository root:

```sh
make report-books PYTHON=.venv/bin/python
```

`make proof-reports` is a compatibility alias. The existing contracted Dask builder now records this presentation revision here, leaving the earlier proof-text and simulation evidence unchanged. Its single graph has eight tasks: retained-input verification, six XeLaTeX/BibTeX/Poppler builds and renders, and a final manifest. No Matplotlib is used. PGFPlots is loaded only by the simulation wrapper for its scientific charts; text, formulas, headings and tables use native TeX layout. Xy-pic is not needed for these books.

The canonical `../book_style.tex` loads all 19 required packages: `fontspec`, `unicode-math`, `tcolorbox`, `tabularray`, `hyperref`, `bookmark`, `mathtools`, `microtype`, `scrlayer-scrpage`, `cleveref`, `amsthm`, `booktabs`, `graphicx`, `float`, `enumitem`, `scrhack`, `listings`, `natbib` and `xurl`. Per-report preambles retain only project metadata and specialized settings. The report-format policy is also recorded in the root `AGENTS.md`.

## Checks and evidence

- [`revision.json`](revision.json) pins current TeX/Bib sources, instructions, builder and all six PDFs. Actual compiler-input files confirm `scrbook.cls` and every required `.sty`. The engine log confirms XeTeX; the geometry log confirms all four margins as 45.5244 TeX points, corresponding to 16 mm.
- [`artifact-audit.json`](artifact-audit.json) verifies those source/PDF hashes, current page counts, populated contents, absence of chapter-zero numbering, and each final AI appendix's actual PDF destination and complete text. Each disclosure has at least 350 words; visual review confirms its content and final placement rather than treating length alone as adequacy.
- [`check.txt`](check.txt) records `make check PYTHON=.venv/bin/python`: canonical library ownership, Python/Deal and SPARK structural inventories, clean positive static lint and the exact expected negative-control failure, **446 passing runtime/property tests**, and the scoped symbolic acceptance gate.
- The Python inventory covers 41 files and 377 named functions with 2,277 Deal declarations. Every named function meets the five-decorator floor; 56 meet the staged ten-contract target. The builder has four functions with meaningful domain, output, exception and side-effect contracts, enabled at the CLI.
- The SPARK structural inventory covers 183 entities (102 functions, 81 procedures), all meeting the five-clause floor; 26 meet the staged ten-clause target. This is not a fresh GNATprove run. The scoped symbolic results also do not establish arbitrary Python correctness or statistical-model validity.
- The six `*.build.txt` files retain actual build stdout, including harmless package notices and their original whitespace. Final engine-log diagnostics and all package/margin/navigation checks passed.

All 50 original `simulation-data/` files, the original `../run.json`, earlier `../proof-revision/` records and native verification evidence remain unchanged. Historical manifests describe their original source/PDF snapshots; this directory describes the current books. The mathematical proofs, exact numerical certificates and observed simulation data were preserved. No new simulation, SPARK or Rocq campaign is claimed for this presentation revision.

AI disclosure: OpenAI Codex and collaborating AI agents prepared this layout revision, its reviews and these validation notes. Every final book contains its complete project disclosure as the last appendix. Independent human peer review or empirical IQ-model validation is not claimed.
