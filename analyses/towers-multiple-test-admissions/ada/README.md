# Ada calculations, Monte Carlo simulation, and SPARK contracts

This standalone project calculates the four nominal-cutoff examples in the joint Towers report, reproduces the follow-up's finite BASIC grid, calibrates a two-test OR rule, and simulates correlated Gaussian scores. All files stay with this analysis.

## Build and run

Use a matching GNAT and GNATprove toolchain in `PATH`:

```sh
gprbuild -P towers.gpr -p
bin/towers_demo 1000000 20261030 results
python3 validate_results.py results --replay
```

The positional arguments are number of trials (1 to 100,000,000), Park-Miller seed (1 to 2,147,483,646), and output directory. The defaults are shown above. The calculation uses binary64 `Long_Float`, `libm`'s `erfc`, Ada elementary functions, and composite Simpson integration over the correlation parameter with 20,000 panels. A 10,000-panel result is included for an empirical refinement check; this is not a proved quadrature error bound.

Outputs:

- `calculation.csv`: inverse-normal thresholds, joint tails, union and conditional probabilities, binary phi, refinement differences, and raw floating results alongside the quantized SPARK results.
- `grid.csv`: the BASIC grid reproduction and continuous-cutoff results with matching marginal denominators.
- `calibration.csv`: the common cutoff giving 2% overall two-test OR eligibility.
- `simulation.csv`: all four event-cell counts, conditional rates, and a 95% Wilson interval for the joint frequency.

The validator compares calculations with the independently computed SciPy CSVs in the parent analysis. `--replay` independently replays the Park-Miller recurrence, Box-Muller transformation, and classifications in Python and requires every event-cell count to match. It also checks count identities and broad simulation consistency. The Wilson intervals describe Monte Carlo sampling uncertainty under the model; with only a few rare joint events they remain wide and do not validate an extreme-tail psychometric claim.

## Expanded SPARK architecture

`towers_proof.gpr` now includes `Admission_Core`, `Normal_Model`, `Towers_Engine`, the `Towers_IO` interface and trusted completion, and `Towers_Demo`. The main procedure and algorithm bodies are SPARK-on. The [expanded computer10 campaign](../../../verification/evidence/spark-expanded-computer10-20261031/REPORT.md) records current proof results and coverage. The earlier 31-check result is a historical snapshot of the core-only project, not the total for this expanded scope.

The original `Admission_Core` contracts still establish:

- correct classification into neither, A only, B only, and both;
- exactly one increment per observation, with every other cell unchanged;
- exact marginal and union counts, their bounds, and exact rational count fractions;
- exact inclusion-exclusion and complement calculations for probabilities represented in units of `10^-15`;
- exact rational conditional probabilities, preserving their numerator and denominator and ensuring numerator does not exceed the positive denominator;
- absence of run-time checks failing in those kernels, subject to their explicit preconditions.

`Normal_Model` now exposes bisection, Simpson summation, BASIC-grid loops, the exact Park-Miller recurrence, open-unit conversion, and Box-Muller composition to analysis. Its explicit proof domains include `0 <= Rho <= 0.95`, a positive even Simpson panel count, and `abs(A), abs(B) <= 1e100` for joint tails; inverse survival requires a probability strictly inside the survival values at -12 and +12. The main calculation cases satisfy these domains. These are bounded implementation contracts, not an accuracy theorem over arbitrary real arguments. `Towers_Engine` performs the calculations, quantization conversion, simulation/count loops, Wilson arithmetic, and assembly of result records in SPARK. The generator contract records its exact state transition and uniform conversion. `Towers_Demo` reads bounded options, calls the engine, and passes the records to the I/O interface.

Small bodies remain off at explicit checked boundaries. In `Normal_Model` these cover square root, survival/foreign `erfc`, logarithm/exponential ranges, exponent and quadrature-node validation, returned probability bounds, and final grid normalization state. In `Towers_Engine` they validate quantization reconstruction error and the joint/union/conditional relationships required before entering exact core algebra. Each validates its stated normal-return property and raises an error instead of changing an invalid value. These checks are not proofs that a backend failure or rejection is impossible. `Towers_IO` models external I/O state in its SPARK specification; its body performs argument parsing, string formatting, and filesystem/output operations outside the proof.

The installed Ada elementary-function specifications themselves support SPARK. Analysis uses their limited contracts and the checked project interfaces; it does not verify the implementations of `libm`, transcendental functions, or these off-mode completions. Bounded arithmetic and loop proofs do not establish normal-inversion accuracy or a Simpson quadrature error bound. The executables retain runtime assertions and overflow checks, and numerical outputs are independently validated.

The engine rounds each probability to the nearest `10^-15` unit in SPARK and calls the checked reconstruction-error interface enforcing `0.51e-15`. It raises an exception on an unexpected value; it never clamps probabilities to force a contract. Raw floating union and conditional values are retained in `calculation.csv`. For a conditional `j/p`, if both inputs differ by at most delta, the rational change is bounded by `delta*(1+j/p)/(p-delta)`, provided `p>delta`. With delta=`0.51e-15` and the smallest nominal marginal `1/33000`, this is at most approximately `3.37e-11`; actual checked differences are smaller. This quantization accounting is separate from libm, quadrature, and model accuracy.

Run the centrally configured portfolio from the repository root:

```sh
python3 verification/run_computer10.py --portfolio-only
```

The runner creates fresh sources and object directories and retains commands, hashes, versions, statuses, native totals, and raw `.spark` files. Native `all`/`spec`/`no` entity statuses distinguish analyzed SPARK bodies from specification-only or excluded code; they are not counts of fully proved requirements. Empty native entity arrays for whole off-mode units are retained rather than interpreted as no exclusions. Flow-only coverage is explicitly identified and cannot be accepted as a full proof. Omit `--portfolio-only` for independent solver comparisons; a successful combined portfolio does not imply every solver succeeds independently.

The analyzed code has no `pragma Assume`, imported project proof axioms, or proof suppressions. This does not remove trust in checked normal-return interfaces or standard-library contracts, prove backend/I/O totality, establish stochastic independence, or validate the Gaussian model and empirical test correlation. Those limitations remain even when all selected verification conditions are discharged.

The refactor retains RNG advancement, numerical expressions, and CSV formatting. The independent million-pair replay and comparison with all four retained CSVs check regression consistency; the expanded campaign report records their outcome. A finite replay or successful executable run is not a formal proof of the excluded numerical or psychometric boundaries.

`python3 verification/verify_evidence.py` audits the committed expanded campaign against current sources. Historical campaigns require an explicit old checkout through `--source-root`; see the [verification guide](../../../verification/README.md#audit-historical-campaigns-explicitly). Their records stay immutable, and the auditor does not automatically substitute old Ada for changed current code.

The repository's [license](../../../LICENSE) applies to original material, subject to third-party rights.
