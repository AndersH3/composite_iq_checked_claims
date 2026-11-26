# Maintained Python/Dask/Deal development policy

**Researcher/requester:** Anders Hellström.

The maintained numerical workflow is **Python 3.13, Dask, NumPy/SciPy and Deal**. Do not restore retired native simulation, compiler-specific source or legacy proof campaigns as active implementations. Past snapshots and results are accessible through Git history, not as present-day checks.

Every named Python function, including Python/Dask entry points, test helpers, and fixtures, must carry **at least fifteen (>=15)** syntactically distinct, nonredundant, meaningful Deal decorators. This is a **minimum, not an exact quota or an upper bound**. Cover relevant input domains, return values, exception types, effects, frames, numerical assumptions and data integrity; more than fifteen are encouraged when justified. Do not add tautological or duplicate contracts to inflate counts. Entry points explicitly enable Deal at runtime. The static contract inventory verifies declarations, not universal validity.

Every maintained `.py` file must begin with a substantive module docstring explaining its purpose, including tests, fixtures, package entry points and import facades. Every named Python function, including nested helpers and Dask tasks, must have function-specific documentation describing its behavior, domain assumptions, side effects and failure cases where relevant. The AST-based CI gate requires a purpose header and at least six words of function documentation as an objective minimum; reviewers must still check substance, accuracy and the adequacy of explanatory comments. Do not insert filler to satisfy the syntax check.

All tracked shell scripts must pass `shellcheck --severity=warning` **before** they are run. Maintain this ordering in GitHub Actions and local tooling; an unchecked script must not be executed.

Use existing maintained standard-library, NumPy/SciPy and Dask functions rather than implementing parallel summation, random sampling, probability or matrix libraries. Keep Dask random seeds, chunk sizes, scheduler configuration, model parameters and exact source/data revisions explicit. Do not claim that random draws are independent merely because the generator takes separate seeds. Preserve reproducible numerical tables and distinguish analytical formulas, empirical data and Monte Carlo estimates.

Run `make check`, including Python/Rocq ownership checks, Deal contract coverage, static lint with its deliberate negative control, and Python/Dask tests. Run the pinned Rocq 9.2 proof workflow for changes to formal proofs. No discontinued alternate-engine, retired compiler proof or native campaign steps are part of the active CI.

All Rocq source files need explanatory module headers and extensive comments for definitions, lemmas, theorems and hypotheses. Refactor proof code continuously and reuse previously checked definitions and Stdlib lemmas. No admitted proof placeholders, extra axioms or unverifiable theorem-count inflation.

All eight reports use XeLaTeX and KOMA-Script `scrbook`, narrow margins, tables of contents and explicit early AI disclosures plus full AI disclosure appendices. Include `fontspec`, `unicode-math`, `tcolorbox`, `tabularray`, `hyperref`, `bookmark`, `mathtools`, `microtype`, `scrlayer-scrpage`, `cleveref`, `amsthm`, `booktabs`, `graphicx`, `float`, `enumitem`, `scrhack`, `listings`, `natbib` and `xurl` as required. Use TikZ/PGF only when appropriate for figures. Build, inspect and regenerate all eight PDFs after report-source revisions; never claim a stale checked-in PDF contains the latest text.

Keep simulation output provenance honest. A document-only rebuild does not rerun the Dask experiment; an earlier implementation's evidence is not proof of present Python source. Publish exact Git commits, verification status and unproved statistical/model assumptions.

> **AI disclosure:** This instruction and migration were prepared with assistance from OpenAI ChatGPT/Codex. Automated checks alone are not independent human validation.
