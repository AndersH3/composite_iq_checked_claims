# Maintained Python/Dask/Deal development policy

**Researcher/requester:** Anders Hellström.

The maintained numerical workflow is **Python 3.13, Dask, NumPy/SciPy and Deal**. Do not restore retired native simulation, compiler-specific source or legacy proof campaigns as active implementations. Past snapshots and results are accessible through Git history, not as present-day checks.

Every named function, including test helpers and fixtures, must carry **at least five** nonredundant meaningful Deal decorators; prefer **ten to fifteen** distinct contracts covering relevant input domains, return values, exception types, effects, frames and data integrity. Do not add tautological or duplicate contracts to inflate counts. Entry points explicitly enable Deal at runtime. The static contract inventory verifies declarations, not universal validity.

Use existing maintained standard-library, NumPy/SciPy and Dask functions rather than implementing parallel summation, random sampling, probability or matrix libraries. Keep Dask random seeds, chunk sizes, scheduler configuration, model parameters and exact source/data revisions explicit. Do not claim that random draws are independent merely because the generator takes separate seeds. Preserve reproducible numerical tables and distinguish analytical formulas, empirical data and Monte Carlo estimates.

Run `make check`, including Python/Rocq ownership checks, Deal contract coverage, static lint with its deliberate negative control, and Python/Dask tests. Run the pinned Rocq 9.2 proof workflow for changes to formal proofs. No discontinued alternate-engine, retired compiler proof or native campaign steps are part of the active CI.

All Rocq source files need explanatory module headers and extensive comments for definitions, lemmas, theorems and hypotheses. Refactor proof code continuously and reuse previously checked definitions and Stdlib lemmas. No admitted proof placeholders, extra axioms or unverifiable theorem-count inflation.

All six reports use XeLaTeX and KOMA-Script `scrbook`, narrow margins, tables of contents and explicit early AI disclosures plus full AI disclosure appendices. Include `fontspec`, `unicode-math`, `tcolorbox`, `tabularray`, `hyperref`, `bookmark`, `mathtools`, `microtype`, `scrlayer-scrpage`, `cleveref`, `amsthm`, `booktabs`, `graphicx`, `float`, `enumitem`, `scrhack`, `listings`, `natbib` and `xurl` as required. Use TikZ/PGF only when appropriate for figures. Build, inspect and regenerate all six PDFs after report-source revisions; never claim a stale checked-in PDF contains the latest text.

Keep simulation output provenance honest. A document-only rebuild does not rerun the Dask experiment; an earlier implementation's evidence is not proof of present Python source. Publish exact Git commits, verification status and unproved statistical/model assumptions.

> **AI disclosure:** This instruction and migration were prepared with assistance from OpenAI ChatGPT/Codex. Automated checks alone are not independent human validation.
