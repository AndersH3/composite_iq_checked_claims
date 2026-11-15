# Project attribution update

**Author, researcher and requester:** Anders Hellström.

The six maintained report volumes now credit Anders Hellström on their title pages, with the visible role line **Author, researcher and requester**, and in their PDF author metadata. The disclosures name his role in supplying the questions, directing the research and requesting the work while retaining the substantive AI-contribution and verification-scope statements. The canonical `../book_style.tex` provides `\ProjectAuthor` and `\ProjectRoles`; `AGENTS.md` records the attribution convention for future reports and current documentation.

Current READMEs and other maintained project Markdown documentation carry the same credit. External source authors and bibliographic citations are unchanged. Historical simulation files, native evidence and previous verification/presentation records retain their original bytes and source contexts.

## Reproduction and checks

Run `make report-books PYTHON=.venv/bin/python` from the repository root. The contracted Dask builder checks both the actual PDF author field and extracted first-page name/roles, including the **ö**. It also retains the XeLaTeX, `scrbook`, 19-package, four 16 mm margin, table-of-contents and final full-AI-appendix checks.

- [`revision.json`](revision.json) pins current source and PDF hashes for all six volumes, with verified author metadata and visible-role results.
- [`artifact-audit.json`](artifact-audit.json) verifies the names in all title pages, PDF metadata and final AI disclosures, every current README, all source/PDF hashes, preserved report-format rules and unchanged historical evidence.
- [`check.txt`](check.txt) records the complete repository gate: canonical library ownership, Deal/SPARK structural inventories, positive static lint and the exact negative control, **446 passing runtime/property tests**, and the scoped symbolic acceptance gate.
- [`documentation-check.txt`](documentation-check.txt) records the source-comment/register audit after the concurrent upstream Rocq additions were retained. It is a documentation audit, not a new kernel proof run.
- The six `*.build.txt` files retain actual XeLaTeX/BibTeX stdout. All final references/citations and layout checks pass.

Visual review covered all six full title pages and final AI pages, including the diacritic and role line, plus the final reflowed computational page. The two main disclosures keep the full name together. All six books retain their prior pagination: Hoeflin/Ferguson 30+29 pages, Towers 30+28 and Sequential 42+29, totaling 188 pages. No mathematical result or recorded numerical observation changed.

AI disclosure: OpenAI Codex and collaborating AI agents implemented and reviewed this attribution update at Anders Hellström's request. Full project disclosures remain in the final appendix of every volume. Independent human peer review or empirical psychometric validation is not claimed; no new simulation, SPARK or Rocq campaign was run for this update.
