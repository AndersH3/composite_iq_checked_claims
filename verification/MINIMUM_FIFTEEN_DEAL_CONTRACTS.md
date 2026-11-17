# Deal contracts — minimum fifteen per named Python function

**Researcher/requester:** Anders Hellström.

> **AI disclosure:** OpenAI ChatGPT/Codex contributed to contract design, runtime testing and documentation. A count of contracts is not a proof of program correctness.

The supported computational stack is **Python, Dask, NumPy/SciPy and Deal**. [The canonical contract checker](check_contract_coverage.py) examines actual Python AST decorators rather than trusting comments or repeated decorator strings. Every tracked Python or Python/Dask named function, including test functions, fixtures and helper functions, must declare **at least fifteen (>=15) distinct Deal contracts**. This is a minimum, **not an exact count**, and there is no upper limit. A file-wide total of fifteen cannot substitute for fifteen per individual function. Import-only modules have no functions to contract.

The checker counts decorators from the parsed AST, canonicalizes aliases and rejects syntactic duplicates on the same function. **Static counts cannot establish meaningfulness:** reviewers must ensure that each predicate expresses a real input boundary, numerical invariant, return guarantee, declared exception, or effect boundary. No contracts should be added solely to inflate a count.

The per-function 15-contract minimum includes both positive and deliberately failing test fixtures. The negative fixture must still produce exactly one specified lint diagnostic; contracts are added only to its correct helper. The finite-real validator now documents accepted representable integers, rejected overlarge integers, and unsupported numeric/input categories.

Run these source checks:

    python verification/check_contract_coverage.py
    python verification/check_static_lint.py
    python -m pytest -q tests

The canonical code consists of [numeric helpers](../library/python/numeric.py), [statistical estimates](../library/python/statistics.py), [Dask simulation tasks](../reporting/simulate.py), [numerical output formatting](../reporting/assets.py), [document builds](../reporting/rebuild_proofs.py) and [SHA-256 provenance](../reporting/provenance.py). Contract declarations can be incomplete, and independent run-time tests cannot certify every path through an opaque external numerical library.

The intentionally failing [Deal negative fixture](../tests/fixtures/contract_negative_control.py) must cause exactly the specified DEL012 diagnostic. It is not production code, and deleting the fixture invalidates the static-lint acceptance gate. Other tests use fixed numerical examples and deliberately invalid records.

[Rocq](../rocq/README.md) checks explicit formal algebraic propositions under their assumptions. It does not certify Python floating-point accuracy, independent random draws or empirical psychometric population assumptions.

The discontinued alternate simulation and compiler code is not maintained in the active tree; its earlier source and campaign data are available through Git history, not current Python verification.

## CI acceptance criteria

`python verification/check_contract_coverage.py` exits nonzero if an executable
Python function has fewer than fifteen distinct decorators, a decorator is
duplicated, or a named function omits the Deal import. The file-wide minimum
remains an additional (redundant) guard, never a substitute for the per-function
floor. `tests/test_contract_coverage.py` exercises the 14-versus-15-versus-16
boundary and ensures that a 15-contract file total cannot conceal functions
with fewer than fifteen contracts.

## Full AI disclosure

AI systems materially assisted with source, contracts, tests and documentation. The researcher Anders Hellström supplied the scope and migration direction. Automated results are revision-specific, with no independent human peer review or empirical human score-validation dataset claimed.
