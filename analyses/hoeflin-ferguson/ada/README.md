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

## Formal scope

`hoeflin_proof.gpr` includes exactly `hoeflin_core.ads` and `hoeflin_core.adb`. These units are in SPARK and have no assumptions, imported axioms, proof suppressions, or silent clamping. Their contracts specify:

- the exact integer numerator `1000 + r * (n - 1)` and its bounds for the variance factor, with correlations expressed in permille;
- the floating-point variance and latent-factor reliability ranges;
- bounded threshold, composite, and IQ-scale calculations, including threshold contraction and composite expansion for positive input scores;
- nested simulation event counts and the exact counter increments for thresholds 2, 3, and the selected rare cutoff.

Typical proof command:

```sh
gnatprove -P hoeflin_proof.gpr -U --mode=all \
  --prover=cvc5,z3,altergo,colibri --steps=0 --timeout=30 \
  --report=statistics --checks-as-errors
```

Use the retained reports from an actual invocation to determine which obligations were proved. A zero unproved-check count applies only to the selected SPARK core, not to the I/O or numerical-library boundary. Proof of a bound is also distinct from proof of a numerical approximation error.

The full [computer10 campaign](../../../verification/README.md) uses a project-local configuration for classic COLIBRI and Yices, records independent prover runs, and avoids incompatible legacy COLIBRI step-limit flags. The bundled three-prover combination alone may leave floating-point bounds unresolved.

The threshold and composite use the mathematically equivalent forms `q - q*(1-s)` and `m + (m*(1-s))/s`. These forms make their contraction/expansion properties more accessible to the provers. They are not asserted to be bit-identical to direct multiplication or division. Their numerical results are independently compared with the report's direct formulas.

## Numerical and simulation boundary

`normal_support` and the executable drivers are explicitly `SPARK_Mode => Off`. They use Ada elementary functions and the platform C `erfc` implementation for the survival function, followed by bisection for the inverse tail. Their numerical accuracy is checked against SciPy, not established by the SPARK proof. The generated executables retain assertion and overflow checks (`-gnata -gnato`), with SSE floating-point options on this x86-64 platform.

The generator uses a 64-bit modular linear-congruential state transition and a Box-Muller transform. Uniforms are generated from the top 52 state bits as exactly representable binary64 midpoints strictly between zero and one. This avoids `log(0)` without clamping. This is a reproducible Monte Carlo implementation, not a cryptographic generator or a proof of independence.

For each test count `n`, the simulation samples

```text
mean_z = sqrt(0.6) * G + sqrt(0.4/n) * E
composite_z = mean_z / sqrt(0.6 + 0.4/n)
```

where the Gaussian residual mean is represented by one normal draw. Under the Gaussian model, this has exactly the same mathematical distribution as explicitly averaging `n` independent residual terms. It saves work for the 100- and 1000-test cases. Empirical composite means, variances, and tails above 2 and 3 are reported. Counts above the one-in-a-million cutoff are descriptive only; the default sample size cannot validate that tail.

The repository's [LICENSE](../../../LICENSE) applies to its original material, subject to third-party rights.
