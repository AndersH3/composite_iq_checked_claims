# Python Deal checks on computer10, 31 October 2026

Every current Python file in the repository carries Deal contracts, including tests and fixtures. The AST coverage gate found **16 Python files, 119 named functions, 359 Deal decorators, and zero gaps**. It checks actual decorator syntax, not mentions in comments or strings. A GitHub workflow and root `make check` enforce this policy for future files.

## Results

| Check | Result |
|---|---|
| Repository-wide contract coverage | Passed: all 16 files and 119 named functions |
| Runtime/property/generated tests | 91 passed, zero failures or skips |
| Independent numerical scripts | Both passed normally and with `python -O` |
| Retained Ada-output validators and simulations | Passed; independent replay counts match |
| Pure proof-acceptance gates | Both symbolic postconditions proved by Deal Solver |
| Contract negative controls | Runtime pre/post failures, static DEL012, and symbolic wrong-post failure detected |
| Existing SPARK evidence | Audited unchanged, resolving historical Python through Git blobs |
| New contract-enabled proof launcher | Both SPARK portfolios rerun: 47 + 31 checks, zero unproved or justified |
| Full production static lint | **Not clean: 14 diagnostics retained and reviewed** |

The static result is deliberately not presented as a clean pass. The numerical scripts themselves pass Deal lint. The wider diagnostics include a confirmed Deal 4.24.6 extractor bug: it reports ZeroDivisionError for a constant denominator without checking that the constant is zero. The [minimal positive probe](../../../tests/fixtures/nonzero_division_lint_probe.py) returns 0.5 and satisfies its runtime contracts, while lint flags `1.0 / 2.0`. Other findings involve conservative standard-library, exception-subclass, and path/string inference; one shlex warning remains an unresolved static-analysis result. No dependencies were patched, contracts disabled, bogus exception permissions added, or diagnostics suppressed to obtain a green report.

## Scope

Contracts specify finite inputs, count bounds, feasible probabilities, positive denominators, result shapes, CSV schemas, checksum/source identities, allowed exceptions, and side effects. Validation assertions that could disappear under optimization were replaced by explicit errors. CLI entry points force Deal on under optimized Python. The new property tests found a real quadrature-tolerance mismatch at the independent Gaussian case; the requested relative tolerance was tightened to match the enforced error budget. Stored numerical CSVs and Ada sources remain unchanged.

The two [pure gates](../../proof_gate.py) are proved for their annotated integer domains. This is not a universal Python proof. SciPy, quadrature, file I/O, subprocesses, pseudo-random independence, and Gaussian/psychometric validity are not thereby formally verified. See the [official Deal verification limitations](https://deal.readthedocs.io/basic/verification.html) and [linter documentation](https://deal.readthedocs.io/basic/linter.html).

## Reproduce

```sh
python3 -m venv .venv
. .venv/bin/activate
python -m pip install -r requirements-dev.txt
make check
python -m deal prove --skipped --nocolor verification/proof_gate.py
python verification/verify_evidence.py
```

Use a full Git clone for historical-source auditing. On this connector-authored computer10 workspace, the audit used `--git-dir /tmp/composite-iq-historical-git`, a temporary object database populated with the exact verified blobs from commit `6c2afecd4a1e8b66b8d67561b2cfbe9713637421`. The committed [source-history map](source_history.json) contains only identities, not uncontracted Python copies. All older proof evidence remains byte-for-byte unchanged.

The clean isolated environment was Python 3.13.5, Deal 4.24.6, Deal Solver 0.1.2, Typeguard 3.0.2, Astroid 4.3.4, Pytest 8.4.2, Hypothesis 6.170.14, NumPy 2.5.4, and SciPy 1.18.1. Typeguard 4 is incompatible with this Deal release's generated-test integration; the development dependency pins the compatible version. [Full package versions](packages.txt) and [environment metadata](environment.json) are retained.

## Evidence

- [Coverage](final-coverage.stdout), [test log](final-pytest.stdout), and [JUnit results](pytest.xml)
- [Commands, timestamps, statuses, and log hashes](checks.json)
- [Static lint diagnostics](static-lint.jsonl) and [review](static-lint-review.json)
- [Focused symbolic proof](pure-gate-symbolic-proof.stdout) and [rejected symbolic negative control](negative-symbolic-control.stdout)
- [Source hashes](source_hashes.json) and [checksums](SHA256SUMS)
- [SPARK rerun through the contracted Python launcher](../deal-spark-computer10-20261031/REPORT.md)

There were 20 recorded command checks with their expected outcomes, plus the separately retained non-clean production lint result. No skipped or failed symbolic checks are counted as proved.
