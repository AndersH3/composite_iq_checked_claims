# Python/Dask/Deal verification

**Researcher:** Anders Hellström.

> **AI disclosure:** This verification documentation and part of the tooling were developed with OpenAI ChatGPT/Codex assistance.

Current checks are run with `make check` or directly:

```sh
python verification/check_contract_coverage.py
python verification/check_static_lint.py
python -m pytest -q tests
bash scripts/check_library_layout.sh
```

All maintained Python and Python/Dask functions, including test helpers and fixtures, require **at least fifteen (>=15) distinct, meaningful Deal decorators per named function**; there is no upper limit. The AST-based coverage check rejects any function below that floor, irrespective of aggregate file counts. Distinct syntax does not establish substantive independent meaning; review the actual propositions.

Deal contracts specify input domains, output invariants, exceptions and effects of maintained Python source. A deliberately incorrect negative-control fixture is expected to produce exactly one specified static-lint diagnostic; deleting or ignoring it invalidates the acceptance gate. Property and runtime tests exercise selected finite inputs; they are not proofs of arbitrary numerical software or pseudorandom generator independence.

Rocq uses a separate pinned 9.2 GitHub Actions workflow to kernel-check explicitly stated mathematical propositions; see [formal proof inventory](../rocq/README.md). Its finite statistical algebra is not a proof of Gaussian conditioning, confidence coverage or population psychometric validity.

The discontinued discontinued alternate-engine compiler sources and recorded native campaigns were removed from the working tree. Their contents remain accessible through Git history, but those earlier results are not current-source verification for Python/Dask/Deal.

**Full AI disclosure:** AI assistance covered specification, test scripting, debugging, source/document refactoring and automated audit design. The published status is limited to checks actually run on the exact source revision; no independent human peer review or empirical population validity is claimed.
