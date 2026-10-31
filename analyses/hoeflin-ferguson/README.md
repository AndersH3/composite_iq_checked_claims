# Combining IQ Scores: Checked Claims

A statistical analysis and independently written replacement for Ronald K. Hoeflin's [article on combining IQ scores](https://megasociety.org/noesis/141/ferguson.html). The report preserves the valid covariance algebra, corrects the numerical table, and distinguishes standardized composites from latent-ability estimates and empirically established extreme percentiles.

- [Compiled PDF](output/pdf/composite_iq_analysis.pdf)
- [XeLaTeX source](composite_iq_analysis.tex)
- [Bibliography](references.bib)
- [Original Markdown analysis](analysis.md)
- [Recalculated thresholds](data/thresholds.csv)
- [Numerical verification](scripts/verify_calculations.py)
- [Ada/SPARK calculations and simulations](ada/README.md)
- [Computer10 prover evidence](../../verification/README.md)

The PDF uses XeLaTeX, KOMA-Script `scrartcl`, A4 paper, 16 mm margins, TeX Gyre Pagella text and mathematics, TeX Gyre Heros sans-serif text, and Latin Modern Mono. The source is the authoritative typeset version; the Markdown file preserves the earlier analysis.

## Reproduce the report

Run the commands below from `analyses/hoeflin-ferguson/`:

```sh
cd analyses/hoeflin-ferguson
```

Install a TeX distribution with XeLaTeX, `latexmk`, KOMA-Script, the packages loaded in the source, and the fonts above. A full TeX Live installation includes these dependencies. Also install Python 3.9 or later and SciPy for the numerical checks:

```sh
python3 -m pip install -r requirements.txt
make check
make pdf
```

The PDF is written to `output/pdf/composite_iq_analysis.pdf`. `make` runs the checks and builds the PDF. `make clean` removes LaTeX auxiliary files while retaining the PDF.

To regenerate the CSV from the formulas:

```sh
python3 scripts/verify_calculations.py --write
```

The verification script uses the upper-tail normal quantile `scipy.stats.norm.isf(1e-6)`. It independently recomputes the table at average correlation 0.60, compares it with the stored CSV and the rounded table values in the XeLaTeX source, and checks the worked composite and latent-factor examples. These checks establish numerical consistency under the stated model; they do not validate its empirical psychometric assumptions.

## Sources and scope

The report cites the original article, the [AERA/APA/NCME testing standards](https://www.testingstandards.net/uploads/7/6/6/4/76643089/9780935302356.pdf), [Sackett and Yang on range restriction](https://pubmed.ncbi.nlm.nih.gov/10740961/), [Hausknecht and colleagues on retesting](https://doi.org/10.1037/0021-9010.92.2.373), and the [official R normal-distribution documentation](https://stat.ethz.ch/R-manual/R-devel/library/stats/html/Normal.html). Full references are included in the PDF and bibliography.

The historical article and other cited works are not reproduced or relicensed here. The repository's existing [LICENSE](../../LICENSE) governs the repository's original material, subject to third-party rights.
