# Hoeflin/Ferguson calculations in Ada and SPARK

This standalone implementation reproduces the corrected thresholds and worked examples in the parent analysis. It also simulates the expressly assumed Gaussian common-factor model. It does not treat that model as an empirical fact about IQ tests.

## Build and run

Use matching GNAT and GNATprove versions. On computer10, the installed Alire tool environment is `/home/anonymous/.local/share/icar16-gnatprove-tools`; `alr -q printenv` from that directory identifies the tool paths. The root repository's verification runner captures the actual environment and proof reports.

```sh
gprbuild -P hoeflin.gpr -p
bin/hoeflin_calculations > calculations.csv
bin/hoeflin_simulation 500000 20261030 > simulation.csv
python3 scripts/validate_results.py --calculations calculations.csv \
  --simulation simulation.csv --json-output validation.json
```

`hoeflin_calculations` writes nine threshold rows, followed by `# examples` and four named worked examples. `hoeflin_simulation [trials] [seed]` writes comment metadata and eight CSV rows. The admissible trial count is 2 through 100,000,000. The default is 500,000 per case, with seed 20261030. The same seed is reset for each test count, giving common random numbers across cases.

The validator needs the parent analysis's Python/SciPy dependencies. It compares all calculated values with independently computed SciPy results, checks event-counter nesting, and supplies six-standard-error diagnostics and Wilson intervals for moderate tails. A diagnostic pass is not a proof or a rare-tail validation.

## Expanded SPARK architecture

`hoeflin_proof.gpr` now includes the core, `Normal_Support`, `Report_IO`, and both main procedures. `Hoeflin_Calculations` and `Hoeflin_Simulation` are SPARK-on rather than whole-program exclusions. Calculation orchestration, sample generation, common-factor combination, accumulation, frequencies, and nested count updates are available for analysis. The expanded [computer10 campaign](../../../verification/evidence/spark-expanded-computer10-20261031/REPORT.md) records the actual coverage and proof totals; the earlier 47-check result belongs to the historical core-only project.

The original `Hoeflin_Core` contracts still specify:

- the exact integer numerator `1000 + r * (n - 1)` and its bounds for the variance factor, with correlations expressed in permille;
- the floating-point variance and latent-factor reliability ranges;
- bounded threshold, composite, and IQ-scale calculations, including threshold contraction and composite expansion for positive input scores;
- nested simulation event counts and the exact counter increments for thresholds 2, 3, and the selected rare cutoff.

`Normal_Support` now keeps the generator state, exact modular recurrence, midpoint-uniform mapping, inverse-tail bisection, and Box-Muller composition in SPARK. The simulation loop has explicit count and bounded-accumulator invariants. This adds proofs of specified ranges, flow, arithmetic, and bookkeeping; it does not establish a probability distribution for the generator or a numerical approximation theorem.

The remaining checked numerical completions are `Square_Root`, `Survival`/foreign C `erfc`, `Check_Inverse_Bracket`, `Rare_Quantile`, and `Checked_Radius`. Their bodies validate bounds or the supported bracket and raise an exception on an unexpected result. They are trusted normal-return interfaces: proof does not show that backend failures or those exceptions are impossible. `Report_IO` has a SPARK specification with separate command-input and report-output states; its body handles only argument parsing, formatting, and output. The driver computes the frequency and survival values before calling it.

Run the centrally configured portfolio from the repository root:

```sh
python3 verification/run_computer10.py --portfolio-only
```

The runner selects this folder's proof project and the Towers project in fresh temporary directories. Use the retained native reports to determine which obligations were proved. Its raw `.spark` data distinguishes analyzed bodies (`all`), specification-only completions (`spec`), and non-SPARK declarations (`no`). A declaration in SPARK does not mean its body was proved. The native unit/entity inventory is reported separately from successful flow/proof checks.

The [verification guide](../../../verification/README.md) describes the project-local COLIBRI/Yices configuration and optional independent-prover runs. A successful portfolio does not mean every solver independently proves every obligation. The analyzed source does not use `pragma Assume`, imported project proof axioms, proof suppressions, or silent clamping. It still relies on checked unproved completions and the installed standard-library contracts.

The threshold and composite use the mathematically equivalent forms `q - q*(1-s)` and `m + (m*(1-s))/s`. These forms make their contraction/expansion properties more accessible to the provers. They are not asserted to be bit-identical to direct multiplication or division. Their numerical results are independently compared with the report's direct formulas.

## Numerical and simulation limits

The installed Ada elementary-function specifications support SPARK, but their contracts supply only limited domain/range facts. Their implementation accuracy, the platform `erfc`, and the checked numerical completions are not proved here. Inverse-tail bisection can be analyzed for bounded iteration and arithmetic without proving its returned approximation error. I/O success, backend totality, Gaussian assumptions, and psychometric validity remain outside the result. Executables retain assertion and overflow checks (`-gnata -gnato`), with SSE floating-point options on this x86-64 platform.

The generator uses a 64-bit modular linear-congruential state transition and a Box-Muller transform. Uniforms are generated from the top 52 state bits as exactly representable binary64 midpoints strictly between zero and one. This avoids `log(0)` without clamping. This is a reproducible Monte Carlo implementation, not a cryptographic generator or a proof of independence.

For each test count `n`, the simulation samples

```text
mean_z = sqrt(0.6) * G + sqrt(0.4/n) * E
composite_z = mean_z / sqrt(0.6 + 0.4/n)
```

where the Gaussian residual mean is represented by one normal draw. Under the Gaussian model, this has exactly the same mathematical distribution as explicitly averaging `n` independent residual terms. It saves work for the 100- and 1000-test cases. Empirical composite means, variances, and tails above 2 and 3 are reported. Counts above the one-in-a-million cutoff are descriptive only; the default sample size cannot validate that tail.

The refactor retains RNG advancement, uniform conversion, numerical expressions, seed handling, and CSV formatting. Exact replay and byte comparison with the retained calculations/simulation are regression checks, not consequences of the SPARK range proofs. Their recorded outcome is in the expanded campaign report.

Audit the committed current campaign with `python3 verification/verify_evidence.py` from the repository root. Older campaigns must explicitly select an old source checkout with `--source-root`; the [verification guide](../../../verification/README.md#audit-historical-campaigns-explicitly) gives the commands. Prior evidence is not rewritten, and changed Ada source is never matched through an automatic historical fallback.

The repository's [LICENSE](../../../LICENSE) applies to its original material, subject to third-party rights.

## Ghost models for excluded boundaries

`Hoeflin_Boundary_Models` is a separate package marked `SPARK_Mode, Ghost`, with implemented predicates, projections, a receipt-state transition, and observation procedures. It is included in the proof project alongside every production source. It has no imported bodies, proof axioms, assumptions, or suppressed checks.

| Excluded code | Ghost link in the actual body | Modeled property |
|---|---|---|
| `Normal_Support.Square_Root` | `Observe_Sqrt` | The existing checked nonnegative and conditional range bounds |
| `Survival`, including the C `erfc` import | `Observe_Erfc`, `Observe_Probability` | Actual cached C result, its binary64 half-scaling, and the checked probability range |
| `Check_Inverse_Bracket` | `Observe_Inverse_Bracket` | Cached endpoint survival values enclose the requested probability |
| `Rare_Quantile` | `Observe_Rare_Quantile` | The checked range `[3,10]` |
| `Checked_Radius`, including logarithm and square-root use | `Observe_Log_Radius` | The checked log range `[-38,0]`, open-unit input, and radius range `[0,9]` |
| Installed `Sin`/`Cos` backend bodies used by `Normal_Pair` | `Observe_Trig` on each cached actual result | The range `[-1,1]` provided by the installed SPARK-compatible elementary-function specifications |
| All eight public `Report_IO` operations | `Note` / `Transition` | Operation tag, copied typed payload, nominal logical column count, section state, and whether the call follows the model's input/protocol conditions |
| Private `Number` helper and its `Float_IO.Put` call | `Project_Number`, `Observe_Number` | The value and requested decimal precision, accepting every original argument value in the declared scalar domains |
| Private `Trimmed` helper and its `'Image`/slice operations | `Observe_Decimal_Image`, `Decimal_Image` | Canonical natural-number decimal text and value reconstruction |
| Private `Named_Row` helper and label/string emission | `Project_Label`, `Observe_Label` | Label length and counts of commas, line feeds, and carriage returns; arbitrary original labels remain accepted |

The I/O receipt ledger is ghost state local to the excluded I/O body. Its event and row counters use explicit arithmetic modulo `2^64`. `Transition` and the projections are proved as models, while the actual calls from excluded bodies remain an implementation-to-model refinement obligation. The ledger records a call-admissibility Boolean; it does not reject an unusual call order or assert that every actual I/O call satisfies the protocol. Its column count describes the intended logical schema, not a theorem about serialized CSV bytes. Example payloads retain label length, not complete label content. Physical text formatting, escaping, encoding, stream/filesystem behavior, exception paths, and the correctness of the Ada/C libraries remain unproved.

The numeric observation procedures run after the original concrete guards. Their preconditions express the acceptance predicates without replacing the existing ordinary preconditions, postconditions, or body checks. C results and inverse-bracket values are cached at the original evaluation points, preserving external-call order and short-circuit behavior; the observations do not make extra transcendental or C calls. CLI parsing still uses the original Ada `'Value` grammar, including its accepted signs, whitespace, underscores, and based literals. No raw-argument decimal-only restriction was added.

With GNAT13, an ordinary checked contract cannot reference a ghost entity that is erased by `Ghost => Ignore`. Therefore model links are calls to ghost procedures inside the actual bodies, rather than ghost conjuncts added to ordinary contracts. This permits independent `Ghost => Check` and `Ghost => Ignore` builds while retaining all other runtime assertion checks. The campaign records the final build/output comparison; a finite erasure regression supplements rather than replaces GNATprove's non-interference checks on analyzed ghost code. Excluded callers and their external effects remain trusted.

These models do not establish square-root/log/erfc accuracy, inverse convergence, Gaussian distributional correctness, random independence, or empirical psychometric validity. They make the remaining specifications and observational boundaries explicit; successful proof of a model is not proof that an excluded implementation realizes it.

The trigonometric observations execute in the analyzed `Normal_Pair` body. Each result is cached immediately before its original multiplication, in the original cosine/X then sine/Y order, and the observer makes no library call. The client proof establishes that the installed specifications imply the observer's range precondition; it does not verify the backend's accuracy, periodicity, or implementation.
