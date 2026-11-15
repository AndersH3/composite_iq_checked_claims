# Sequential scores: Ada/SPARK calculations and simulations

This implementation evaluates the paper's formulas for one, two or three equal starting scores and also supports other bounded starting-block counts. It calculates the inclusive mean, actual-mean population and conditional variances, Gaussian regression/residual coefficients, covariance eigenvalues, initial-block inverse and analytic infinite-count limits. The exact formula core accepts signed correlations in thousandths, `r,k >= 1`, and `r+k <= 1000`, subject to covariance admissibility. Fixed negative correlations have finite cases but no infinite-count result. At `c=1`, equal-score support is handled without pretending a singular starting block has an ordinary inverse.

The source is separated by responsibility:

- `Sequential_Core`: exact integer numerator/denominator construction and domain checks. These pairs are formula coefficients, rather than a new general-purpose rational library.
- `Sequential_Experiments`: named conversion to machine floating point, standardized/IQ moments, bounded count/sum/squared-sum accumulation and the sample variance with denominator `n-1`.
- `Sequential_Sampling`: scalar Gaussian-law sampling using the central `Shared_Normal_Sampling.Normal_Pair`. A zero SD returns the location without consuming random state. The square-root adapter delegates to the central checked numerical routine, which validates its normal-return guarantees.
- `sequential_run.adb`: one disclosed `SPARK_Mode => Off` command-line/CSV boundary. It drives the fixed experiment grid, writes results and computes independent recursion, matrix-identity and finite-PMF diagnostics. Its physical I/O, parsing and loop orchestration are runtime checked; they are not proved SPARK bodies.

The heavily commented packages reuse Ada's standard integer/elementary libraries and the canonical contracted generator in `library/spark/src`. They introduce no second PRNG, Box–Muller algorithm or matrix solver. The supplementary Python validator uses `Fraction`, `csv`, NumPy and SciPy for independent arithmetic, full covariance conditioning and sampling diagnostics.

## Contracts

Every new SPARK subprogram has at least five explicit behavioral/flow entries. Eight of the eleven have at least ten; the total is 139. These counts describe specifications, not independent theorems.

| Subprogram | Entries | Implementation scope |
|---|---:|---|
| `D_Numerator` | 11 | SPARK integer arithmetic |
| `Valid` | 10 | SPARK domain predicate |
| `Calculate` | 27 | SPARK exact finite coefficients |
| `Limits` | 17 | SPARK exact limit coefficients |
| `Value` | 7 | SPARK bounded machine division |
| `From_Coefficients` | 18 | SPARK standardized/IQ mapping |
| `Reset` | 5 | SPARK reset of three accumulator fields |
| `Add` | 13 | SPARK bounded numerical updates |
| `Finish` | 12 | SPARK sample-moment evaluation |
| `Checked_Sqrt` | 11 | Trusted completion with ordinary runtime checks |
| `Draw` | 8 | SPARK state flow and displacement bounds |

Reset has three distinct state-reset obligations plus two flow contracts. Value and Draw retain their appropriate range, algebraic or frame properties without artificial padding to reach ten. The trusted square-root interface is included in the minimum. The source-inventory audit explicitly excludes its body and the CLI body, and native coverage distinguishes `all` from `spec`. Reused library interfaces retain their own contracts and trusted completions.

## Reproduction

Install the repository's exact `requirements-dev.txt` in `.venv`. A matching GNAT/GPRbuild/GNATprove environment is discovered using the existing contracted `verification.run_computer10.environment` helper and `alr -q printenv` in `~/.local/share/icar16-gnatprove-tools`. CVC5, Z3, Alt-Ergo, classic Colibri and Yices must already be available; the runner records their paths, versions and hashes.

From the repository root:

```sh
.venv/bin/python analyses/sequential-conditional-means/scripts/run_spark.py --trials 200000
```

Alternatively, from the analysis directory, run `make spark`. `--alire-dir` overrides the toolchain directory; `--output` chooses an unused absolute evidence path. Existing evidence is never overwritten. Each campaign copies current sources into an empty temporary mirror, builds and proves with fresh objects, runs the executable, and calls the independent Deal validator. The retained compressed source archive, source hashes, actual commands/logs, raw `.spark` metadata, contract inventory, runtime CSVs and JSON summary identify the actual scope. An incomplete proof or validator failure gives a nonzero exit and `complete: false`. No new native negative-control campaign is implied.

With a matching compiler already in `PATH`, a runtime-only run is:

```sh
gprbuild -P analyses/sequential-conditional-means/ada/sequential.gpr -p -j2
mkdir -p analyses/sequential-conditional-means/ada/results
cd analyses/sequential-conditional-means/ada/results
../bin/sequential_run 200000
```

The optional executable argument is the number of observations per row, from 2 to 1,000,000. The three CSVs are `calculation.csv`, `simulation.csv` and `checks.csv`. All checks and overflow/assertion checking remain enabled in the project.

## Experiments and interpretation

There are 20 finite calculations: the nine IQ-150 cases, all three earlier `a=2,k=3` examples, independence/perfect-correlation cases, a valid negative interior case and singular negative endpoints. Nonnegative cases also report the exact analytic limits. There are 40 finite population/conditional sampling rows and six limit rows, with an explicit incremented seed for each row. The standard run uses 200,000 observations per row: 9.2 million aggregate values. Eighteen diagnostic rows cover original-recursion agreement, eigenvector/inverse residuals, total variance, the conditional-growth identity and the paper's non-Gaussian PMF.

Population samples have standardized mean zero. Conditional samples have the inclusive predicted mean as their centre after fixing the starting block. They are samples of the **actual score mean**, whose nonzero conditional SD is different from the zero SD of the fixed list of predictions. The sampler uses the analytically proved scalar Gaussian law, so moment agreement checks the implementation pipeline. Independent full-matrix NumPy conditioning and exact Fraction calculations check the finite formulas separately. Infinite-count rows sample Gaussian laws with the analytically calculated limiting parameters; a finite simulation does not prove convergence.

The normal generator has bounded outputs and finite deterministic state. Neither its contracts nor the new proofs establish exact normality, independence or PRNG quality. Machine-arithmetic contracts do not establish universal numerical accuracy. The square-root normal-return checks do not prove the elementary library's implementation or totality. The native campaign is program evidence under these boundaries, separate from the paper's mathematical proofs and statistical assumptions. The [retained report](../evidence/REPORT.md) records 430 discharged native checks (124 flow, 306 prover), zero unproved/justified, all ten new analyzed subprogram bodies, and the explicit checked-square-root specification-only entity. Read-only re-auditing with the current validator is:

```sh
.venv/bin/python analyses/sequential-conditional-means/scripts/audit_spark.py analyses/sequential-conditional-means/evidence/campaign-20261114-current
```

The audit rejects every current Ada/project hash mismatch and any changed retained artifact. Original Python source bytes remain verified against their archive; later Python-only differences are disclosed and numerical validation uses the current code. No new prover invocation is implied by the audit.

## Independent SPARK sampling dependency

The `sequential.gpr` source directories are the report-specific `src/` and
`library/spark/src/` only. Its normal pairs, RNG recurrence and checked
bounded square root come from `Shared_Normal_Sampling`. The Hoeflin/Ferguson
adapter calls the same canonical generator but retains its own survival and
quantile numerical boundaries. A fixed-seed parity test checks both adapters.
No Gaussian distribution theorem or backend sqrt accuracy proof follows from
this source migration; GNATprove must be rerun for source-specific proof status.
