# Ada/SPARK verification on computer10

The two analysis folders contain standalone Ada implementations:

- [Hoeflin/Ferguson](../analyses/hoeflin-ferguson/ada/): corrected thresholds, composite and latent-factor examples, and a Gaussian common-factor simulation.
- [Towers](../analyses/towers-multiple-test-admissions/ada/): bivariate-normal probabilities, the BASIC grid, calibrated admission cutoffs, and correlated-score simulations.

[The recorded computer10 campaign](evidence/computer10-20261031/REPORT.md) contains the final totals, independent prover outcomes, source hashes, exact invocations, versions, native GNATprove reports, and numerical results. The records distinguish flow checks from prover-discharged checks and identify any independent solver runs that remain incomplete.

## Reproduce the proof campaign

From the repository root on computer10:

```sh
python3 verification/run_computer10.py
```

The runner discovers the matching toolchain through `alr -q printenv` in `~/.local/share/icar16-gnatprove-tools`. It parses an allowlist of literal exports without shell evaluation. Override the directory with `--alire-dir` if necessary.

Each invocation creates a new evidence directory and uses fresh temporary source copies and object directories for every project/prover pair. It runs a five-prover portfolio and each prover independently: bundled CVC5, Z3, Alt-Ergo, classic COLIBRI, and Yices. The local configuration corrects the old COLIBRI adapter's incompatible `--steplimit` option to `--max-steps`; global tool configurations are not modified. `--steps=0` uses time budgets rather than a small implicit step cap. Use `--portfolio-only` to omit the independent comparison runs.

An intentionally wrong inclusion-exclusion implementation in [negative_control](negative_control/) must be rejected. It is excluded from both production proof projects. A campaign is accepted only when the negative control is rejected with a native unproved contract and both production portfolios exit successfully, contain nonempty native totals, and report zero unproved and zero justified checks. A nonzero exit, missing report, timeout, or parsing failure cannot count as a successful project proof.

## What the proofs establish

The SPARK projects enumerate their complete core source files explicitly. They verify the specified finite arithmetic, bounds, contracts, and event-count updates under their input preconditions. There are no project `pragma Assume` statements, imported proof axioms, or suppressed checks in these cores.

The Hoeflin core includes exact integer variance bookkeeping and bounded floating-point transforms. Some transforms use algebraically equivalent evaluation orders that aid proof; numerical equivalence is checked against the direct report formulas, rather than asserted to be bit-identical.

The Towers core uses exact integers and rational pairs for event counts and probability algebra. Continuous probabilities are rounded to units of `10^-15` at an explicit checked boundary. Both the raw floating results and the results using the exact SPARK algebra are retained; the small conditional-probability quantization error is separately accounted for in the implementation README.

The Ada drivers and numerical adapters are explicitly outside SPARK. The proofs do not certify `libm`, elementary functions, normal inversion, quadrature error, random independence, the Gaussian model, or the empirical validity of a test correlation. Those boundaries are independently checked numerically. A successful simulation is not a formal proof.

## Numerical execution and replay

With the matching compiler in `PATH`, run `make check TRIALS=1000000` from either `ada/` folder. The retained campaign uses seed `20261030`: one million samples for each of eight Hoeflin test-count cases and one million shared correlated pairs for the four Towers cases.

Both implementations are compared with independent SciPy calculations. The Towers validator also replays every event count in Python. The [Hoeflin replay](replay_hoeflin.py) independently regenerates its 64-bit recurrence and Box-Muller pairs, checks all tail counts, and compares means and variances:

```sh
python3 verification/replay_hoeflin.py \
  verification/evidence/computer10-20261031/runtime/hoeflin/simulation.csv
```

Monte Carlo uncertainty is reported explicitly. Rare counts are descriptive; these sample sizes do not establish a one-in-a-million psychometric frequency.

Audit the retained evidence and its match to the current source with `python3 verification/verify_evidence.py`. This checks checksums, native totals, source identities, and the negative-control result; it does not replace rerunning the provers.

## Python contracts

Every current Python file and every named function, including tests and fixtures, carries Deal contracts. Install `requirements-dev.txt` and run `make check` from the repository root. The coverage gate also runs in GitHub Actions and inspects Git's file inventory, so adding a new Python file or function without contracts fails the check.

The [current Deal computer10 report](evidence/deal-lint-clean-computer10-20261031/REPORT.md) records 110 passing tests, clean static lint for all 19 positive Python files, and the single expected diagnostic from the deliberately incorrect fixture. Run `python verification/check_static_lint.py` to inventory every Python file, require clean maintained code, and verify that the negative control still fails. Both `make check` and GitHub Actions enforce this gate. CLI entry points explicitly enable Deal even under `python -O`. The pinned Typeguard 3 integration is required by Deal 4.24.6's generated type checks.

The [earlier Deal report](evidence/deal-computer10-20261031/REPORT.md) retains the original 14 diagnostics. The new report explains each resolution and links the [fresh SPARK integration campaign](evidence/deal-lint-spark-computer10-20261031/REPORT.md), which exercises the revised launcher and again passes both portfolios.

The original SPARK evidence remains byte-for-byte unchanged. Its Python tooling hashes refer to commit `6c2afecd4a1e8b66b8d67561b2cfbe9713637421`; the earlier Deal campaign refers to versions in `5e9e8ec7ea0ca17ec68d44f9c4e56430f3d0297c`. The auditor's [current source-history map](evidence/deal-lint-clean-computer10-20261031/source_history.json) resolves both sets through verified Git blob IDs; it never substitutes a historical version for changed Ada/SPARK source. A normal full Git clone supplies those objects. For a separate local object database, use `--git-dir PATH`. No uncontracted archival Python copies are kept in the current tree.
