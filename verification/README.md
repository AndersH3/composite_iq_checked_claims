# Ada/SPARK verification on computer10

The two analysis folders contain standalone Ada implementations:

- [Hoeflin/Ferguson](../analyses/hoeflin-ferguson/ada/): corrected thresholds, composite and latent-factor examples, and a Gaussian common-factor simulation.
- [Towers](../analyses/towers-multiple-test-admissions/ada/): bivariate-normal probabilities, the BASIC grid, calibrated admission cutoffs, and correlated-score simulations.

The [expanded computer10 campaign](evidence/spark-expanded-computer10-20261031/REPORT.md) records the current source scope, proof results, native `.spark` coverage, checked interfaces, numerical comparisons, and Python checks. The [original campaign](evidence/computer10-20261031/REPORT.md) and [earlier integration campaign](evidence/deal-lint-spark-computer10-20261031/REPORT.md) remain immutable historical snapshots. Their 47-check Hoeflin and 31-check Towers totals apply to the old projects containing only the arithmetic cores; they are not totals for the expanded implementation.

## Reproduce the proof campaign

From the repository root on computer10:

```sh
python3 verification/run_computer10.py --portfolio-only
```

The runner discovers the matching toolchain through `alr -q printenv` in `~/.local/share/icar16-gnatprove-tools`. It parses an allowlist of literal exports without shell evaluation. Override the directory with `--alire-dir` if necessary.

Each invocation creates a new evidence directory and uses fresh temporary source copies and object directories. The portfolio requests bundled CVC5, Z3, Alt-Ergo, classic COLIBRI, and Yices together. Omit `--portfolio-only` to also run each prover independently. Portfolio completion does not imply that every independent solver run completes. The local configuration corrects the old COLIBRI adapter's incompatible `--steplimit` option to `--max-steps`; global tool configurations are not modified. `--steps=0` uses time budgets rather than a small implicit step cap.

An intentionally wrong inclusion-exclusion implementation in [negative_control](negative_control/) must be rejected. It is excluded from both production proof projects. A campaign is accepted only when the negative control is rejected with a native unproved contract and both production portfolios exit successfully, contain nonempty native totals, and report zero unproved and zero justified checks. Native coverage must also be retained and pass the assumption/suppression checks. A nonzero exit, missing report, timeout, incomplete metadata, or parsing failure cannot count as a successful project proof.

## What the proofs establish

The expanded proof projects enumerate the original cores, numerical support, calculation/simulation engines, SPARK-on main procedures, and I/O interfaces. `Hoeflin_Simulation`, `Hoeflin_Calculations`, and `Towers_Demo` are now in SPARK. Random-state updates, uniform generation, bisection and quadrature orchestration, simulation loops, accumulation, event counting, and probability conversion can therefore be analyzed along with the core arithmetic.

The Hoeflin core includes exact integer variance bookkeeping and bounded floating-point transforms. Some transforms use algebraically equivalent evaluation orders that aid proof; numerical equivalence is checked against the direct report formulas, rather than asserted to be bit-identical.

The Towers core uses exact integers and rational pairs for event counts and probability algebra. Continuous probabilities are rounded to units of `10^-15` at an explicit checked boundary. Both the raw floating results and the results using the exact SPARK algebra are retained; the small conditional-probability quantization error is separately accounted for in the implementation README.

Only small numerical validation bodies and the system I/O implementations remain outside SPARK. Their SPARK specifications expose explicit bounded normal-return contracts; their bodies check the promised ranges or relationships and raise an error instead of clamping an invalid value. These are runtime-checked trusted interfaces, not proofs that the checks can never fail. `Report_IO` and `Towers_IO` model external state explicitly; argument parsing, formatting, file operations, and their exceptions are not proved.

The installed Ada elementary-function specifications support SPARK, but provide only limited contracts. The analyzed code uses those contracts and the checked project interfaces. Proving a caller under these interfaces does not establish the backend's correctness, numerical accuracy, or totality. There are no project `pragma Assume` statements or proof suppressions in the analyzed code; that does not eliminate trust in unproved completions or the standard library. The proofs also do not certify quadrature error, Gaussian distributions, pseudo-random independence, a psychometric tail frequency, or the empirical validity of a test correlation. Those remain separate numerical and model questions.

## Native coverage and proof scope

The runner retains the raw `.spark` JSON for each invocation. [spark_coverage.py](spark_coverage.py) records file hashes, native section names and entity counts, and normalized entity locations/statuses:

- `all`: specification and body are in SPARK, or the specification has no body;
- `spec`: the specification is in SPARK and its completion is outside the analysis;
- `no`: the declaration is outside SPARK.

These statuses describe language/analysis coverage, not successful proof of every verification condition. Native flow and proof totals are recorded separately. Whole units explicitly switched off may have an empty native entity array; `no=0` therefore does not mean that no code is excluded. The source inventory and empty raw-unit files remain visible alongside the entity counts.

Source filtering cannot hide a retained `pragma_assume` or suppressed flow/proof message. Explicit flow-only coverage can be used for a historical baseline; its analysis mode and proof-metadata completeness are recorded, and it cannot satisfy the full-proof completion flag. The expanded campaign report gives the actual comparison and final totals.

## Numerical execution and replay

With the matching compiler in `PATH`, run `make check TRIALS=1000000` from either `ada/` folder. The retained campaign uses seed `20261030`: one million samples for each of eight Hoeflin test-count cases and one million shared correlated pairs for the four Towers cases.

Both implementations are compared with independent SciPy calculations. The Towers validator also replays every event count in Python. The [Hoeflin replay](replay_hoeflin.py) independently regenerates its 64-bit recurrence and Box-Muller pairs, checks all tail counts, and compares means and variances:

```sh
python3 verification/replay_hoeflin.py \
  verification/evidence/computer10-20261031/runtime/hoeflin/simulation.csv
```

Monte Carlo uncertainty is reported explicitly. Rare counts are descriptive; these sample sizes do not establish a one-in-a-million psychometric frequency.

Audit the committed expanded campaign against the current source with `python3 verification/verify_evidence.py`. Its default evidence directory is `verification/evidence/spark-expanded-computer10-20261031`. To audit a newly generated campaign instead, supply that invocation's evidence directory as the positional argument. The auditor checks checksums, native totals, raw coverage, source identities, and the negative-control result; it does not rerun the provers or independently validate SMT proof objects.

## Audit historical campaigns explicitly

Older campaigns describe the Ada sources before the expansion. They must be checked against an explicitly selected old checkout, not silently substituted for current Ada source. From a full Git clone:

```sh
git worktree add --detach /tmp/composite-iq-before-expansion \
  2c32ecdd87690866bfcbf2d99725abba7cdad55e
python3 verification/verify_evidence.py \
  verification/evidence/computer10-20261031 \
  --source-root /tmp/composite-iq-before-expansion
```

The same explicit source root applies to the retained `deal-spark-computer10-20261031` and `deal-lint-spark-computer10-20261031` campaigns. A mismatch against the selected Ada tree is an error. Historical Python tooling may still be resolved through verified Git blob identities in [source_history.json](source_history.json); there is no automatic Ada fallback. `--git-dir PATH` supplies a separate Git object database when needed. No historical uncontracted Python copies are added to the current tree.

## Python contracts

Every current Python file and every named function, including tests and fixtures, carries Deal contracts. Install `requirements-dev.txt` and run `make check` from the repository root. The coverage gate also runs in GitHub Actions and inspects Git's file inventory, so adding a new Python file or function without contracts fails the check.

Run `python verification/check_static_lint.py` to inventory every Python file, require clean maintained code, and verify that the negative control still fails. Both `make check` and GitHub Actions enforce this gate. CLI entry points explicitly enable Deal even under `python -O`. The pinned Typeguard 3 integration is required by Deal 4.24.6's generated type checks. The expanded campaign report records the checks for the current implementation, including the native-coverage helper and evidence-auditor tests.

The [historical Deal snapshot](evidence/deal-lint-clean-computer10-20261031/REPORT.md) retains its 110-test result and clean lint for its then-current 19 positive files. The [original Deal report](evidence/deal-computer10-20261031/REPORT.md) preserves the original 14 diagnostics and their subsequent resolution. Those records are immutable snapshots; adding the expanded coverage tooling changes the current Python inventory without rewriting earlier results.
