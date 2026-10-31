# Python contract policy

All current repository Python files, including tests, fixtures, helpers, and nested functions, must use Deal contracts. Every named function must carry at least one real Deal decorator. Use meaningful value/domain, output, exception, and side-effect contracts appropriate to the function; an import or a comment alone is insufficient.

Do not disable contracts or replace them with permissive placeholders to satisfy the coverage check. CLI entry points must explicitly enable Deal with `deal.enable(warn=False)` so optimized Python also checks contracts.

Run `python verification/check_contract_coverage.py` and `python -m pytest -q tests` in the environment installed from `requirements-dev.txt`. The GitHub Python-contracts workflow enforces repository-wide coverage and tests. Intentionally incorrect contract fixtures are negative controls, not production implementations.

Keep recorded proof evidence immutable. Historical Python versions needed for old proof hashes are resolved from verified Git-history blobs, rather than copied into the current tree without contracts. Changed Ada/SPARK source must never be silently substituted with an old version during an audit.

Distinguish runtime and property tests, limited symbolic proofs, static-lint diagnostics, SPARK core proofs, numerical accuracy, and statistical-model validity in reports. Do not label unsupported or skipped verification as a successful proof.
