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

## What SPARK verifies

`towers_proof.gpr` contains only `Admission_Core`. Its checked contracts establish:

- correct classification into neither, A only, B only, and both;
- exactly one increment per observation, with every other cell unchanged;
- exact marginal and union counts, their bounds, and exact rational count fractions;
- exact inclusion-exclusion and complement calculations for probabilities represented in units of `10^-15`;
- exact rational conditional probabilities, preserving their numerator and denominator and ensuring numerator does not exceed the positive denominator;
- absence of run-time checks failing in those kernels, subject to their explicit preconditions.

The normal-distribution integrations are not theorems of this SPARK project. `Normal_Model` and the driver explicitly have `SPARK_Mode => Off`. They contain the transcendental functions, floating quantization/rendering, random generation, numerical integration, I/O, and orchestration. They are compiled with runtime assertions and overflow checks enabled, and their numerical outputs are independently validated.

At the floating-to-SPARK boundary, the driver rounds each probability to the nearest `10^-15` unit and checks that the reconstructed value differs by no more than `0.51e-15`. It raises an exception on an unexpected value; it never clamps probabilities to force a contract. Raw floating union and conditional values are retained in `calculation.csv`. For a conditional `j/p`, if both inputs differ by at most delta, the rational change is bounded by `delta*(1+j/p)/(p-delta)`, provided `p>delta`. With delta=`0.51e-15` and the smallest nominal marginal `1/33000`, this is at most approximately `3.37e-11`; actual checked differences are smaller. This quantization accounting is separate from libm, quadrature, and model accuracy.

Run a fresh proof campaign with, for example:

```sh
gnatprove -P towers_proof.gpr -U -f --subdirs=fresh-cvc5 \
  --prover=cvc5 --timeout=10 --report=statistics --checks-as-errors
```

Use fresh `--subdirs` for independent prover runs so cached results from another prover are not mistaken for new proofs. The repository's central computer10 evidence records the actual commands, source hashes, tool versions, exit statuses, and proof totals. An execution of the executable is not a formal proof of the excluded numerical boundary, the Gaussian distribution assumption, or the real-world validity of the test correlation.

The repository's [license](../../../LICENSE) applies to original material, subject to third-party rights.
