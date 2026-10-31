# Ada/SPARK results on computer10, 31 October 2026

Both production SPARK portfolios completed with **zero unproved and zero justified checks**. This applies to the declared cores, not to the numerical libraries or statistical model.

| Project | Total checks | Flow | Proof checks | Unproved | Justified | Native report |
|---|---:|---:|---:|---:|---:|---|
| hoeflin | 47 | 8 | 39 | 0 | 0 | [report](hoeflin/portfolio/gnatprove.out) |
| towers | 31 | 9 | 22 | 0 | 0 | [report](towers/portfolio/gnatprove.out) |

The totals are 78 checks: 17 flow checks and 61 proof checks, including checks discharged by GNATprove simplification. The deliberately incorrect union contract was rejected with one unproved functional contract and a nonzero exit; it is not part of either production total.

## Independent prover comparison

Every row below was run from a fresh source copy and object directory. Incomplete individual runs are not counted as completed proofs. The portfolio combines complementary results; it does not imply that every solver proves every obligation.

| Prover | Hoeflin proof checks / 39 | Hoeflin unproved | Towers proof checks / 22 | Towers unproved |
|---|---:|---:|---:|---:|
| cvc5 | 34 | 5 | 22 | 0 |
| z3 | 29 | 10 | 22 | 0 |
| altergo | 33 | 6 | 22 | 0 |
| Colibri_Classic | 28 | 11 | 5 | 17 |
| Yices | 18 | 21 | 1 | 21 |

## Execution and provenance

- Host: `computer10`; started `2026-10-31T00:39:07.612065+00:00`; finished `2026-10-31T00:44:18.897749+00:00`.
- Actual banners: GNATprove `0.0w`, GNAT `13.2.0`, GPRbuild `22.0.0`, bundled CVC5 `1.0.5`, Z3 `4.12.2`, Alt-Ergo `2.4.0`, classic COLIBRI `2026.06`, and Yices `2.7.0`. Alire package versions must not be substituted for these executable banners.
- Commands, timestamps, exit statuses, executable hashes and full banners: [manifest](manifest.json). Additional Why3/platform/driver information: [tool details](tool_details.json).
- Complete logs, native summaries and per-run result JSONs are under each project/prover folder. Generated temporary object directories and native task/session files were not retained. The checked source is retained in the repository and matched by [source hashes](source_hashes.json).
- A local [prover configuration](provers.conf) fixes the classic COLIBRI adapter flags without modifying global configuration.
- The exact campaign runner is [run_computer10.py](../../run_computer10.py). `--checks-as-errors`, warnings-as-errors, nonempty native reports, and rejection of the negative control prevent an incomplete run from being labelled complete.

## Numerical calculations and simulations

Both Ada programs were rebuilt with the matching toolchain and runtime checks enabled. All deterministic outputs passed independent SciPy validation. The maximum observed absolute discrepancy for the Hoeflin table and examples was `2.842170943040401e-14` (acceptance tolerance `5e-11`). Towers quantized probabilities and conditionals passed `1e-10` absolute checks; retained raw floating results passed `1e-12` checks.

- [Hoeflin calculations](runtime/hoeflin/calculations.csv), [simulation](runtime/hoeflin/simulation.csv), [validation](runtime/hoeflin/validation.json), and [independent replay](runtime/hoeflin/replay.json).
- [Towers calculations](runtime/towers/calculation.csv), [grid reproduction](runtime/towers/grid.csv), [calibration](runtime/towers/calibration.csv), [simulation](runtime/towers/simulation.csv), and [validation/replay log](runtime/towers/validation.log).
- [Build and execution records](runtime/results.json) retain the commands and executable hashes.

The seed is `20261030`. Hoeflin uses one million samples for each of eight test-count cases, resetting the seed to use common random numbers. Towers uses one million shared pairs for four cutoff cases. Every recorded tail/event count matches an independent Python replay. Rare joint events remain noisy: the Towers 1-in-33,000 case produced four joint passes, with a 95% Wilson interval approximately `[1.56e-6, 1.03e-5]`; this is not an extreme-tail validation.

## Exact scope

Hoeflin proves finite variance bookkeeping, bounded floating-point transforms, and nested counter updates. Towers proves event classification, exact count updates, and inclusion-exclusion/complement/conditional arithmetic using integer probability units and rational pairs. Their numerical adapters and drivers are explicitly SPARK-off. Special functions, quadrature accuracy, floating quantization/rendering, pseudo-random independence, Gaussian assumptions, and psychometric validity are outside the formal proof. Those numerical boundaries are independently checked, not silently assumed to be proved.

All evidence files are covered by [SHA256SUMS](SHA256SUMS). Run `python3 verification/verify_evidence.py` from the repository root to check integrity and source correspondence.
