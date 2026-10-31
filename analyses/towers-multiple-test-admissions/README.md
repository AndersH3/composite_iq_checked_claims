# Multiple-Test Admissions: Towers's Letter and Follow-up

A joint statistical analysis and independently written corrected treatment of Grady Towers's two letters about multiple tests for high-IQ society admissions. The report distinguishes nominal population eligibility under OR and AND rules, conditional pass probabilities, and claims about underlying ability or actual society membership.

- [Compiled PDF](output/pdf/towers_admissions_analysis.pdf)
- [XeLaTeX source](towers_admissions_analysis.tex)
- [Bibliography](references.bib)
- [Markdown analysis](analysis.md)
- [Nominal-cutoff probabilities](data/admission_probabilities.csv)
- [Follow-up grid reproduction](data/followup_grid.csv)
- [Numerical verification](scripts/verify_calculations.py)
- [Ada/SPARK calculations and simulations](ada/README.md)
- [Computer10 prover evidence](../../verification/README.md)
- [Archived-source provenance and hashes](source_manifest.json)

The PDF uses XeLaTeX, KOMA-Script `scrartcl`, A4 paper, 16 mm margins, and TeX Gyre Pagella text and mathematics, with TeX Gyre Heros and Latin Modern Mono. The report's probability calculations are conditional on the stated bivariate-normal model; their numerical verification does not validate that model for actual tests or membership populations.

The Markdown companion contains the same analysis and corrected article; the XeLaTeX source and PDF are the authoritative typeset version.

## Reproduce the analysis

From the repository root:

```sh
cd analyses/towers-multiple-test-admissions
python3 -m pip install -r requirements.txt
make check
make pdf
```

Install a TeX distribution containing XeLaTeX, `latexmk`, KOMA-Script, the packages loaded by the source, and the fonts above. A full TeX Live installation includes these dependencies. Use Python 3.9 or later with compatible NumPy and SciPy versions for the numerical checks. `make` runs the checks and builds the PDF; `make clean` retains the PDF while removing LaTeX auxiliary files.

To regenerate the CSV files:

```sh
python3 scripts/verify_calculations.py --write
```

The script calculates bivariate normal joint tails by one-dimensional conditional-normal integration and checks them independently by integrating the bivariate density over the correlation parameter. It checks event-probability bounds and four nominal-cutoff cases, reproduces the follow-up's finite BASIC point grid for three IQ cutoffs, and verifies cutoffs calibrated to a 2% overall OR or AND eligibility rate. The CSV files distinguish continuous-cutoff results from grid results and distinguish consistent conditional probabilities from division by the follow-up's rounded marginal probabilities.

The modern floating-point grid reproduction agrees closely with the follow-up's printed results but does not reproduce every printed digit. The script checks agreement within a stated relative tolerance of `3e-7`, and the CSV records the printed values and residuals. These small numerical residuals are separate from the larger cutoff and denominator inconsistencies analysed in the report.

## Sources and scope

The sources are the archived [initial letter](https://web.archive.org/web/20260309223409/http://miyaguchi.4sigma.org/gradytowers/societies.html) and [follow-up dated 12 January 2000](https://web.archive.org/web/20220505012535/http://miyaguchi.4sigma.org/gradytowers/followup.html). Archive capture dates are not publication dates. The bibliography records the supporting mathematical and testing references used in the report.

The historical letters are cited and analysed, not reproduced or relicensed here. The repository's [LICENSE](../../LICENSE) governs its original material, subject to third-party rights.
