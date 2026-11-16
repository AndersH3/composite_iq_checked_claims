# Python contract policy

All current repository Python files, including tests, fixtures, helpers, and nested functions, must use Deal contracts. Every named function must carry at least five real Deal contract decorators; import-only compatibility modules and package initializers with no functions have no such obligations; there is no upper limit. Use distinct, meaningful value/domain, output, exception, side-effect and frame properties appropriate to the function. Splitting orthogonal conditions is acceptable; tautologies, duplicate padding, imports or comments do not meet the policy. The structural checker counts declarations but does not establish their adequacy or universal validity.

Do not disable contracts or replace them with permissive placeholders to satisfy the coverage check. CLI entry points must explicitly enable Deal with `deal.enable(warn=False)` so optimized Python also checks contracts.

Run `python verification/check_contract_coverage.py`, `python verification/check_static_lint.py`, and `python -m pytest -q tests` in the environment installed from `requirements-dev.txt`, or run `make check`. The GitHub Python-contracts workflow enforces repository-wide coverage, static lint, and tests. The static gate must inspect every Python file and verify the exact expected failure of the explicit negative fixture. Intentionally incorrect contract fixtures are negative controls, not production implementations.

Keep recorded proof evidence immutable. Historical Python versions needed for old proof hashes are resolved from verified Git-history blobs, rather than copied into the current tree without contracts. Changed Ada/SPARK source must never be silently substituted with an old version during an audit. Current-source audits must use the latest campaign. A historical campaign may be audited against an explicitly selected checkout using `--source-root`; the auditor must report that source context and reject every Ada hash mismatch in it.

Distinguish runtime and property tests, limited symbolic proofs, static-lint diagnostics, SPARK core proofs, numerical accuracy, and statistical-model validity in reports. Do not label unsupported or skipped verification as a successful proof.


# SPARK contract policy

Each current SPARK function and procedure, including local and ghost helpers and interfaces with trusted completions, must have at least five explicit meaningful contract entries. Run `python verification/spark_contracts.py`. Count top-level Pre/Post/Refined_Post conjuncts, Contract_Cases alternatives, and explicit Global/Depends aspects. Do not count Ghost/SPARK_Mode/Inline, subtype declarations, body assertions, unsupported aspects, repeated syntax, or literal Boolean padding. The structural floor does not imply logical independence or contract adequacy. Work toward ten nonredundant clauses per SPARK subprogram where mathematically justified; report both the mandatory five-clause floor and staged ten-clause inventory without declaring unrun GNATprove verification successful. Preserve existing properties and runtime behavior; keep trusted completions and model/refinement limits explicit. Retain Ghost observations for excluded implementations. Ordinary request receipts may support normal-return contracts under Ghost Ignore without claiming operating-system success.


# PDF report format policy

All maintained report PDFs and future report PDFs use XeLaTeX and the KOMA-Script `scrbook` class with narrow margins (the shared style uses 16 mm). Use the canonical `reporting/book_style.tex` preamble, a table of contents, and a full AI-disclosure appendix at the end, after the bibliography and all other substantive material. Preserve the mathematical proofs and keep historical evidence immutable when revising presentation.

Load `fontspec`, `unicode-math`, `tcolorbox`, `tabularray`, `hyperref`, `bookmark`, `mathtools`, `microtype`, `scrlayer-scrpage`, `cleveref`, `amsthm`, `booktabs`, `graphicx`, `float`, `enumitem`, `scrhack`, `listings`, `natbib`, and `xurl`. Load/use Xy-pic and TikZ/PGF only when necessary for diagrams or graphics. Text and formulas use native text/math typesetting. The simulation wrapper loads PGFPlots for its scientific charts; the common book style does not use a graphics canvas to typeset text or formulas.

Build and render through the Dask report workflow, check all final references/citations and layout diagnostics, and visually review the resulting pages. Record a new presentation revision separately from earlier simulation and proof-evidence records.

Each sub-project's simulation report must explain both the SPARK and Dask experiments: their algorithms, cases and sample sizes, observed numerical results, comparisons and verification limits. Identify source-pinned native campaigns and additional cases covered by only one implementation. Duplicated Ghost-policy runs and exact replay do not add independent Monte Carlo observations; historical native proof results do not certify later changed sources.


# Project attribution

Credit **Anders Hellström** as the author, researcher and requester in maintained reports, title pages, PDF author metadata, READMEs and other current project documentation. The canonical book style supplies `\ProjectAuthor` and `\ProjectRoles` for consistent typeset credits. Keep the substantive AI-contribution disclosures, source-author citations and verification limits accurate. Preserve recorded historical evidence in its original form; record attribution updates separately.
