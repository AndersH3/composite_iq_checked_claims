# Sequential Conditional Means of Equicorrelated Scores

A full derivation for a fixed starting standardized score `a` and the subsequent recursive predictions `e_1, ..., e_k`. Under joint Gaussianity and equal pairwise correlation `c`, every prediction equals `c a`; their average also equals `c a`. The starting score is excluded from the requested average.

- [Compiled PDF](output/pdf/sequential_conditional_means.pdf)
- [XeLaTeX source](sequential_conditional_means.tex)

The report derives the Gaussian regression function using a residual independent of the conditioning scores, solves the recursion by induction and by telescoping partial sums, and distinguishes the deterministic predictions from actual future outcomes. It covers the raw-score scale, the admissible finite-battery correlation interval and both singular endpoints. A discrete counterexample shows why correlation alone is insufficient.

## Build

From this directory, run:

```sh
make pdf
```

The build requires XeLaTeX, `latexmk`, KOMA-Script, the packages loaded by the source, TeX Gyre Pagella text and mathematics, TeX Gyre Heros, and Latin Modern Mono. The output is `output/pdf/sequential_conditional_means.pdf`. `make clean` removes auxiliary files while retaining the PDF.

The report follows the typography and output layout of the existing [Hoeflin/Ferguson analysis](../hoeflin-ferguson/). It introduces no Python or SPARK implementation and has no additional runtime dependencies.

## Verification and limits

The derivation was reviewed by collaborating AI agents. Validation completed on 13 November 2026:

- `make pdf` passed; the six-page PDF was rendered and visually inspected. The final LaTeX log had no unresolved references, missing glyphs, or overfull/underfull boxes.
- From the repository root, `make check PYTHON=.venv/bin/python` passed using the exact versions in `requirements-dev.txt`. This includes Python contract coverage, the SPARK structural contract audit, static lint with its required negative control, **343 runtime/property tests**, and the existing scoped symbolic acceptance gate.
- The symbolic gate proved its six expected postcondition obligations and found the required negative-control counterexample. Those obligations concern the existing software; they do not formally verify this new analysis.

These checks do not constitute machine-checked mathematical proof of the derivation or empirical validation of the Gaussian test model. No new SPARK prover campaign was run.

The text explicitly specifies the continuous Gaussian conditional-mean version so that recursive evaluation at probability-zero point histories is well defined. For `k` future tests and one starting test, the correlation domain is `-1/k <= c <= 1`; an arbitrarily long collection requires `0 <= c <= 1`.

## AI disclosure and license

The mathematical exposition, documentation and typesetting were prepared with OpenAI Codex and collaborating AI agents in response to the requester's problem and indexing clarification. Review took place within that workflow; independent human peer review is not claimed. The report includes its own disclosure dated 13 November 2026. Historical verification evidence for other analyses is not evidence of a new formal verification of this report.

The repository's existing [LICENSE](../../LICENSE) governs its original material, subject to third-party rights.
