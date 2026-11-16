# Combining IQ Scores: Checked Claims

**Author, researcher and requester:** Anders Hellström.

**Formal proof coverage:** [Six-report Rocq proof-obligation audit](../../rocq/SIX_REPORT_PROOF_OBLIGATIONS.md) scans the **three analytical and three simulation volumes**, including imported proof appendices and source-mapped missing Rocq theorems. A written TeX proof, a finite algebraic proof and a certified Gaussian probability theorem are recorded separately.


A statistical analysis and independently written replacement for Ronald K. Hoeflin's [article on combining IQ scores](https://megasociety.org/noesis/141/ferguson.html). The report preserves the valid covariance algebra, corrects the numerical table, and distinguishes standardized composites from latent-ability estimates and empirically established extreme percentiles.

- [Compiled PDF](output/pdf/composite_iq_analysis.pdf)
- [XeLaTeX source](composite_iq_analysis.tex)
- [Bibliography](references.bib)
- [Original Markdown analysis](analysis.md)
- [Recalculated thresholds](data/thresholds.csv)
- [Numerical verification](scripts/verify_calculations.py)
- [Ada/SPARK calculations and simulations](ada/README.md)
- [Computer10 prover evidence](../../verification/README.md)

Both PDFs use XeLaTeX, KOMA-Script `scrbook`, A4 paper, 16 mm margins, TeX Gyre Pagella text and mathematics, TeX Gyre Heros sans-serif text, and Latin Modern Mono. Each volume has a table of contents and full AI disclosure as its final appendix after the bibliography. The [shared preamble](../../reporting/book_style.tex) loads the required package set. The source is the authoritative typeset version; the Markdown file preserves the earlier analysis.

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

## Dedicated simulation report

The [simulation report](output/pdf/hoeflin_simulations.pdf) covers **both SPARK and Dask**: native generator and aggregate algorithm, all eight native result rows, deterministic calculations, Dask pooled/replicate results, direct comparisons and verification limits. It derives the ideal Box–Muller law and explains why its hypotheses do not follow from a finite-state generator. Its [XeLaTeX source](hoeflin_simulations.tex) consumes the generated tables in [simulation-data](simulation-data/); scientific charts use XeLaTeX/PGFPlots with Dask-produced CSVs. The [dual-simulation revision](../../reporting/dual-simulation/README.md) pins and audits the retained native observations without claiming a new native proof or random experiment. Rebuild the three simulation volumes with `make simulation-reports PYTHON=.venv/bin/python` from the repository root.

From the repository root, regenerate all three experiments, tables, PDFs and rendered review pages with:

```sh
.venv/bin/python -m reporting.simulate --pdf
```

See the [shared Dask workflow](../../reporting/README.md) for seeds, chunk layout, dependency versions, contracts and verification scope. With the generated data already present, `make simulation-pdf` in this directory rebuilds only this report using XeLaTeX. The main and simulation reports both include referenced working proofs and claim/evidence maps. From the repository root, `make proof-reports PYTHON=.venv/bin/python` rebuilds all six proof-complete reports and records the document revision separately, preserving the original numerical campaign and historical evidence.
