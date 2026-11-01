# Composite IQ: Checked Claims

Statistical analyses of claims about combining IQ scores. Each analysis has its own folder containing its source, compiled report, references, and supporting calculations.

| Analysis | Report | Source |
|---|---|---|
| [Hoeflin/Ferguson: combining IQ scores](analyses/hoeflin-ferguson/) | [PDF](analyses/hoeflin-ferguson/output/pdf/composite_iq_analysis.pdf) | [XeLaTeX](analyses/hoeflin-ferguson/composite_iq_analysis.tex) |
| [Towers: multiple-test admissions, original letter and follow-up](analyses/towers-multiple-test-admissions/) | [PDF](analyses/towers-multiple-test-admissions/output/pdf/towers_admissions_analysis.pdf) | [XeLaTeX](analyses/towers-multiple-test-admissions/towers_admissions_analysis.tex) |

Build instructions and numerical verification commands are in each analysis folder's README.

Both analyses include [Ada calculations and simulations with SPARK verification on computer10](verification/README.md). The [expanded campaign](verification/evidence/spark-expanded-computer10-20261031/REPORT.md) covers the algorithm and driver bodies as well as the original arithmetic cores. Small checked numerical interfaces and system I/O remain explicit trusted boundaries. Native `.spark` records distinguish analyzed bodies from specifications whose bodies were not proved; numerical validation and Monte Carlo results remain separate evidence.

All current Python files, including tests and fixtures, must contain [Deal contracts](https://deal.readthedocs.io/). Every named function is checked for a real Deal decorator by `verification/check_contract_coverage.py`; comments and strings do not count. The GitHub workflow enforces this repository-wide policy.

For Python development and checks:

```sh
python3 -m venv .venv
. .venv/bin/activate
python -m pip install -r requirements-dev.txt
make check
```

`make check` and GitHub Actions require contract coverage, clean positive static lint, the exact expected failure of the deliberately broken fixture, and runtime/property tests. The [expanded campaign report](verification/evidence/spark-expanded-computer10-20261031/REPORT.md) records the checks for the expanded implementation. The [earlier Deal snapshot](verification/evidence/deal-lint-clean-computer10-20261031/REPORT.md) retains its 110-test result and optimized-Python, numerical, and symbolic evidence; those historical counts are not the current test inventory. The [original Deal report](verification/evidence/deal-computer10-20261031/REPORT.md) preserves the resolved diagnostics. Runtime checks and property tests are distinct from universal formal verification.

The repository's original material is governed by [LICENSE](LICENSE), subject to third-party rights.
