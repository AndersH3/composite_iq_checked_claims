# Composite IQ: Checked Claims

Statistical analyses of claims about combining IQ scores. Each analysis has its own folder containing its source, compiled report, references, and supporting calculations.

| Analysis | Report | Source |
|---|---|---|
| [Hoeflin/Ferguson: combining IQ scores](analyses/hoeflin-ferguson/) | [PDF](analyses/hoeflin-ferguson/output/pdf/composite_iq_analysis.pdf) | [XeLaTeX](analyses/hoeflin-ferguson/composite_iq_analysis.tex) |
| [Towers: multiple-test admissions, original letter and follow-up](analyses/towers-multiple-test-admissions/) | [PDF](analyses/towers-multiple-test-admissions/output/pdf/towers_admissions_analysis.pdf) | [XeLaTeX](analyses/towers-multiple-test-admissions/towers_admissions_analysis.tex) |

Build instructions and numerical verification commands are in each analysis folder's README.

Both analyses include [Ada calculations and simulations with SPARK verification on computer10](verification/README.md). The retained evidence separates formal core proofs from numerical validation and Monte Carlo results.

The repository's original material is governed by [LICENSE](LICENSE), subject to third-party rights.
