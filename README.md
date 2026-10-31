# Composite IQ: Checked Claims

Statistical analyses of claims about combining IQ scores. Each analysis has its own folder containing its source, compiled report, references, and supporting calculations.

| Analysis | Report | Source |
|---|---|---|
| [Hoeflin/Ferguson: combining IQ scores](analyses/hoeflin-ferguson/) | [PDF](analyses/hoeflin-ferguson/output/pdf/composite_iq_analysis.pdf) | [XeLaTeX](analyses/hoeflin-ferguson/composite_iq_analysis.tex) |
| [Towers: multiple-test admissions, original letter and follow-up](analyses/towers-multiple-test-admissions/) | [PDF](analyses/towers-multiple-test-admissions/output/pdf/towers_admissions_analysis.pdf) | [XeLaTeX](analyses/towers-multiple-test-admissions/towers_admissions_analysis.tex) |

Build instructions and numerical verification commands are in each analysis folder's README.

Both analyses include [Ada calculations and simulations with SPARK verification on computer10](verification/README.md). The retained evidence separates formal core proofs from numerical validation and Monte Carlo results.

All current Python files, including tests and fixtures, must contain [Deal contracts](https://deal.readthedocs.io/). Every named function is checked for a real Deal decorator by `verification/check_contract_coverage.py`; comments and strings do not count. The GitHub workflow enforces this repository-wide policy.

For Python development and checks:

```sh
python3 -m venv .venv
. .venv/bin/activate
python -m pip install -r requirements-dev.txt
make check
```

[Current computer10 Deal evidence](verification/evidence/deal-lint-clean-computer10-20261031/REPORT.md) records clean static lint for every maintained Python file, 110 passing tests, optimized-Python checks, numerical replay, and symbolic gate proofs. `make check` and GitHub Actions require both clean positive files and the expected failure of the deliberately broken fixture. The [earlier report](verification/evidence/deal-computer10-20261031/REPORT.md) preserves the original diagnostics. Runtime checks and property tests are distinct from universal formal verification.

The repository's original material is governed by [LICENSE](LICENSE), subject to third-party rights.
