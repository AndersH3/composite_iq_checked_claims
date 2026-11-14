# Sequential analysis: recorded verification and limits

The 14 November 2026 campaign actually ran on computer10 using a fresh temporary source mirror and empty build/proof objects. It follows the upstream integration through `b90da09` and preserves all older repository evidence. The native invocation, compiler/prover identities and binary hashes, source archive, source hashes, logs and `.spark` files are retained in [campaign-20261114-current](campaign-20261114-current/).

## Native results

[GNATprove's report](campaign-20261114-current/gnatprove.out) gives **430 total checks: 124 flow and 306 prover checks**, with **zero unproved and zero justified**. The six analyzed units include the three new packages and the three reused library/model packages. Native metadata contains no project assumptions or suppressed checks.

| Native check category | Discharged |
|---|---:|
| Data dependencies | 54 |
| Flow dependencies | 54 |
| Initialization | 16 |
| Run-time checks | 229 |
| Assertions | 8 |
| Functional contracts | 69 |
| Total | 430 |

The requested portfolio was CVC5, Z3, Alt-Ergo, classic Colibri and Yices, using the recorded matching GNAT 13.2 environment. Portfolio success does not claim that each solver independently completed every obligation. GNATprove's native version string is retained verbatim rather than replaced by an invented release label.

For the new packages, native coverage is `all:13, spec:1, no:0`: three packages and ten subprogram bodies are analyzed; `Sequential_Sampling.Checked_Sqrt` has a specification-only trusted completion. The whole `SPARK_Mode => Off` CLI unit is separately disclosed; an empty native unit inventory is not counted as proof of its body. Reused transcendental numerical bodies and their normal-return checks remain trusted boundaries.

All eleven new SPARK interfaces satisfy the mandatory five-entry floor: **139 total entries**, minimum **5**; **8 of 11** reach the staged ten-entry target. The per-entity clauses and native source locations are in [campaign.json](campaign-20261114-current/campaign.json). These structural counts do not prove that the contracts are independent or adequate.

## Numerical and sampling results

The original runtime files are retained under [runtime](campaign-20261114-current/runtime/):

- 20 finite calculations and 20 independent full-matrix checks; 16 nonnegative-correlation rows also contain analytic limit coefficients.
- All nine requested IQ-150 examples and all three earlier standardized examples, independence/perfect-correlation cases, a negative interior and singular negative endpoints.
- 40 finite population/conditional batches plus six limiting-parameter batches, each with 200,000 observations: **9.2 million scalar aggregate values**.
- 18 recursion, inverse/eigenvector, total-variance, conditional-growth and PMF checks; maximum absolute discrepancy `1.77635683940025e-15`.
- Every statistical diagnostic passed. Maximum absolute empirical-mean discrepancy: `1.525037766488471` theoretical standard errors. The normal/chi-square diagnostic tail per moment is `1e-10`; pseudorandom independence/normality is not established by those ideal reference laws.
- The independent paper self-check covers 17 matrix cases, three standardized rows, nine IQ rows, three limiting rows, the finite counterexample and **all 74 printed integer certificate entries**.

Sampling uses the proved scalar Gaussian laws. It checks the implementation pipeline and complements independently computed exact fractions and full covariance-matrix conditioning; it does not independently derive a formula merely by sampling that formula's distribution. A deterministic fixed prediction list has SD zero; nonzero conditional SD concerns actual future score outcomes.

## Current-source audit and repository checks

After the native run began, the supplementary validator received a Python-only import/path normalization to work with the updated pinned Astroid version. No Ada or project source changed. The immutable original source archive and campaign hashes remain untouched. [current-source-audit.json](current-source-audit.json) verifies every retained artifact and archived source hash, matches all **16 current Ada/project files**, recomputes native totals/coverage/contracts, lists the changed Python path and revalidates every original CSV with the current validator. It explicitly reports `new_prover_invocation:false`.

Reproduce that read-only audit from the repository root:

```sh
.venv/bin/python analyses/sequential-conditional-means/scripts/audit_spark.py analyses/sequential-conditional-means/evidence/campaign-20261114-current
```

The [auditor rejection checks](audit-rejection-checks.json) used disposable source/evidence copies: a one-byte Ada-source change and a changed retained proof log were both rejected. These are runtime audit tests, not new native prover negative controls. No new SPARK negative-control campaign is claimed.

[Release checks](release-checks/) retain the actual `make check PYTHON=.venv/bin/python` log: **420 runtime/property tests passed**, structural contract inventories passed, static lint accepted every positive file and rejected the expected negative fixture, and the existing scoped symbolic acceptance gate passed with its required counterexample. A final lint/coverage rerun includes the evidence auditor added after the full test run: 32 Python files, 343 named functions and 2,010 Deal decorators, minimum five; 50 functions reach ten. The SPARK-wide structural inventory is likewise separate from this campaign's native results.

The 32-page report was built with XeLaTeX/BibTeX and every rendered page visually reviewed. Its final log has no unresolved references, missing glyphs or overfull/underfull boxes. Mathematical limit, variance-decomposition, finite-difference and simulation-reference-law proofs were independently reviewed within the AI workflow. Human peer review is not claimed.

## Trust and scope

The core is exact bounded integer formula construction. Floating-point contracts describe executed machine arithmetic. Ordinary checks enforce square-root normal-return promises; they do not prove library implementation accuracy or totality. The CLI, diagnostic loops, physical I/O and parsing are runtime boundaries. PRNG distributions/independence, universal numerical accuracy and statistical model adequacy are not native proof conclusions.

The paper's mathematical statements have written derivations from named primary reference theorems. The new program evidence does not machine-check that entire exposition. Concurrent upstream Rocq additions are preserved, but no new Rocq invocation is claimed by this SPARK/Python campaign. No empirical psychometric study was conducted. The repository's AI disclosure and license apply.
