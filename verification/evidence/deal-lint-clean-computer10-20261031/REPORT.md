# Deal static-lint fixes checked on computer10

All 14 diagnostics in the [earlier production lint run](../deal-computer10-20261031/static-lint.jsonl) are resolved. The current gate inventories **20 Python files, 142 named functions, and 416 Deal decorators, with zero contract-coverage gaps**. All 19 positive files, including tests and the lint gate itself, produce zero diagnostics, empty output, and exit status 0. The deliberately incorrect fixture produces exactly one expected `DEL012` and exit status 1.

## Results

| Check | Result |
|---|---|
| Repository-wide contract coverage | Passed normally and under optimized Python |
| Static lint gate | Passed normally and under optimized Python; no positive diagnostics |
| Runtime, property, and generated tests | 110 passed; zero failures or skips |
| Both independent numerical scripts | Passed normally and with `python -O` |
| Both Ada-output validators | Passed normally and with `python -O` |
| Towers replay | All four event cells matched over 1,000,000 trials, in both modes |
| Hoeflin independent replay | All eight cases matched the retained million-trial results, in both modes |
| Symbolic acceptance gates | Two postconditions proved; no skips counted as proofs |
| Incorrect symbolic contract | Rejected as expected |
| Original and earlier Deal SPARK evidence | Audits passed in both modes using immutable Git-history identities |
| Revised launcher integration | Fresh SPARK portfolios passed: 47 + 31 checks, zero unproved or justified |
| Fresh SPARK evidence audit | Passed normally and with `python -O` |
| Dependency consistency and Python compilation | Passed |

There are [27 recorded Python command checks](checks.json), each with an accepted outcome, exact arguments, UTC timestamps, and stdout/stderr hashes. The separate [fresh SPARK manifest](../deal-lint-spark-computer10-20261031/manifest.json) records the actual prover invocations, binary identities, and native totals. The launcher also parsed the real Alire exports during that campaign.

## Resolution of the diagnostics

| Earlier findings | Change and validation |
|---|---|
| Six validator division findings, including a propagated warning | Bounded pure quotient helpers require positive denominators. They execute the original `numerator / denominator` operation, preserving floating-point rounding and integer true division. Numerical tolerances and exact replay counts are unchanged. |
| Runner's inferred `shlex.split` exception | The parser now uses the same POSIX lexer setup as `shlex.split`: whitespace splitting enabled, comments disabled, then token collection. Tests cover malformed quoting, duplicate/unknown exports, quoted spaces, and literal shell syntax. Export names remain allowlisted; no shell evaluation is performed. |
| Runner's inferred checked-process exception in version capture | `Popen` and bounded `communicate` retain nonzero exit metadata and both streams. The timeout path kills and reaps the process. Regressions verify exit 7 and timeout cleanup. |
| Two propagated file-copy exception warnings | The runner entry point explicitly names `SameFileError` and `SpecialFileError`, already subclasses of the allowed `OSError`. Its permitted runtime exception family is unchanged. |
| Verifier's inferred empty path string | An input-dependent `ensure` retains the nonempty-string condition and additionally requires the current source path or a Git identity. Tests exercise the current path and the error paths. |
| Verifier and coverage checker's inferred checked-process exceptions | `check_output` gives these output-only Git calls an explicit nonzero-exit branch. Missing history retains its explicit `ValueError`; the coverage inventory retains its non-checkout fallback. |
| Propagated JSON parse warning | The verifier entry point explicitly names `JSONDecodeError`, already within its allowed `ValueError` family. A malformed-history regression checks that the original error remains observable under optimized Python. |

The [resolution index](static-lint-resolution.json) maps each of the 14 original diagnostics to its resolution. The earlier literal-division probe is retained in Git history; its current version uses a contracted positive quotient helper and remains a clean positive control. Its tests also check denominator rejection and exact division arithmetic. The original probe output and diagnostic remain in the immutable earlier evidence directory.

No diagnostics were suppressed, installed dependencies patched, contracts disabled, or exception families broadened to obtain the result. New tests verify that a newly introduced unsafe implementation, a missing negative fixture, an unexpected diagnostic, and a linter failure cannot pass the gate. A further read-only review found no blocking issues in the changes.

## Reproduce

From a full Git clone, install [the pinned dependencies](../../../requirements-dev.txt), then run:

```sh
make check
python -O verification/check_static_lint.py
python -m deal prove --skipped --nocolor verification/proof_gate.py
python verification/verify_evidence.py
python verification/verify_evidence.py verification/evidence/deal-spark-computer10-20261031
python verification/verify_evidence.py verification/evidence/deal-lint-spark-computer10-20261031
```

The complete numerical and optimized command list is in [checks.json](checks.json). The connector-authored computer10 workspace supplied `--git-dir /tmp/composite-iq-historical-git` for historical-source audits. The [source-history map](source_history.json) records verified blob IDs from the two ancestor commits; it contains no historical Python source copies. Earlier evidence directories, Ada/SPARK source, report PDFs, and numerical CSVs retain their prior bytes.

## Evidence and scope

- [Coverage](contract-coverage.stdout), [runtime/property test output](pytest.stdout), and [JUnit results](pytest.xml)
- [Normal static gate output](static-lint.stdout) and [optimized gate output](static-lint-optimized.stdout), including raw empty positive output and the exact negative diagnostic
- [Two symbolic proofs](pure-gate-symbolic-proof.stdout) and [rejected symbolic control](negative-symbolic-control.stdout)
- [Commands and statuses](checks.json), [environment](environment.json), and [installed versions](packages.txt)
- [Source identities](source_hashes.json), [history identities](source_history.json), and [checksums](SHA256SUMS)
- [Fresh SPARK integration](../deal-lint-spark-computer10-20261031/REPORT.md)

The isolated environment uses Python 3.13.5, Deal 4.24.6, Deal Solver 0.1.2, Typeguard 3.0.2, Astroid 4.3.4, Pytest 8.4.2, Hypothesis 6.170.14, NumPy 2.5.4, and SciPy 1.18.1. The installed Deal exception extractor still has the same SHA-256 as in the earlier run; the environment record captures it.

A clean linter result is a static check, not a universal Python proof. Input-dependent contracts remain checked at runtime; the symbolic result covers only the two pure acceptance gates. The SPARK totals concern the specified Ada cores. Numerical libraries, quadrature, random independence, Gaussian assumptions, and psychometric validity remain separate boundaries. See Deal's official [linter](https://deal.readthedocs.io/basic/linter.html) and [value-contract](https://deal.readthedocs.io/basic/values.html) documentation.
