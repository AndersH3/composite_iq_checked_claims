# Deal contracts — maintained Python inventory

**Researcher/requester:** Anders Hellström.

> **AI disclosure:** OpenAI ChatGPT/Codex contributed to contract design, runtime testing and documentation. A count of contracts is not a proof of program correctness.

The supported computational stack is **Python, Dask, NumPy/SciPy and Deal**. [The canonical contract checker](check_contract_coverage.py) examines actual Python AST decorators rather than trusting comments or repeated decorator strings. Each named Python function must have at least **five distinct meaningful Deal contracts**; the design target is **ten to fifteen** where supported by independent domain restrictions, return guarantees, effect/frame boundaries and declared exceptions.

Run these source checks:

    python verification/check_contract_coverage.py
    python verification/check_static_lint.py
    python -m pytest -q tests

The canonical code consists of [numeric helpers](../library/python/numeric.py), [statistical estimates](../library/python/statistics.py), [Dask simulation tasks](../reporting/simulate.py), [numerical output formatting](../reporting/assets.py), [document builds](../reporting/rebuild_proofs.py) and [SHA-256 provenance](../reporting/provenance.py). Contract declarations can be incomplete, and independent run-time tests cannot certify every path through an opaque external numerical library.

The intentionally failing [Deal negative fixture](../tests/fixtures/contract_negative_control.py) must cause exactly the specified DEL012 diagnostic. It is not production code, and deleting the fixture invalidates the static-lint acceptance gate. Other tests use fixed numerical examples and deliberately invalid records.

[Rocq](../rocq/README.md) checks explicit formal algebraic propositions under their assumptions. It does not certify Python floating-point accuracy, independent random draws or empirical psychometric population assumptions.

The discontinued alternate simulation and compiler code is not maintained in the active tree; its earlier source and campaign data are available through Git history, not current Python verification.

## Full AI disclosure

AI systems materially assisted with source, contracts, tests and documentation. The researcher Anders Hellström supplied the scope and migration direction. Automated results are revision-specific, with no independent human peer review or empirical human score-validation dataset claimed.
