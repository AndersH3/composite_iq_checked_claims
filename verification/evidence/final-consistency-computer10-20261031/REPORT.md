# Final report consistency audit on computer10

The audit of report revision `9a244d8e629ca669bbc05c77f91b941a9108f99b` on 31 October 2026 found **no discrepancies requiring correction** in the corrected formulas, numerical tables, worked examples, or verification claims. Both XeLaTeX reports now contain a short final-audit note. Their PDFs were rebuilt and reviewed. The calculation sources, numerical reference CSVs, and all earlier verification evidence remain unchanged.

## Numerical audit

The audit combined independent recomputation, inspection of Python and Ada source, fresh Ada builds, normal and optimized Python validation/replay, and comparison with the retained evidence. Reported original authors' erroneous figures were distinguished from this repository's corrected calculations.

| Report | Claims checked | Outcome |
|---|---|---|
| Hoeflin/Ferguson | Covariance and weighted/equal-weight composite identities; single-test case; nine threshold rows; infinite-test limit; SD-15 and correlation-0.9 illustrations; composite and latent-factor examples | All corrected displayed values and rounding agree |
| Towers | Four nominal joint probabilities; unions and conditional denominators; binary phi; equal and mixed cutoffs; integer-cutoff tables; correlation sensitivity; rarity equivalents; calibrated OR rule | All corrected displayed values and rounding agree |
| Towers follow-up | BASIC-grid nodes, dimensions, ratios, boundary shift, integer versus nominal marginal denominators | Code, saved outputs, and report agree |
| Numerical/proof boundary | Hoeflin algebraic evaluation orders; Towers integer units/rational pairs and floating quantization budget | The report describes the implemented boundaries accurately |
| Simulation | Hoeflin's eight cases with 1,000,000 trials per case and a reset common seed; Towers' four cases from 1,000,000 shared pairs | All replayed counts match; dependence and rare-tail limitations are stated accurately |

Selected independently recomputed values were:

| Quantity | Value before report rounding |
|---|---:|
| One-in-a-million upper-tail normal quantile | 4.753424308822899 |
| Three scores averaging 160, SD 16, correlation 0.6: composite score | 170.06490497453706 |
| Three tests, correlation 0.9: required average SD-16 score | 173.47590665989094 |
| Hypothetical latent-factor conditional mean on SD-16 scale | 168.7941450256873 |
| Hypothetical latent-factor conditional SD on SD-16 scale | 6.822422923379534 |
| Equal top-2% case: both among the eligible union | 18.610855824% |
| Mixed case: lower-cutoff pass given higher, correlation 0.5 | 33.5942719% |
| Same conditional, correlation 0.7 | 65.8588804% |
| Same conditional, correlation 0.9 | 97.9861004% |
| Two-test OR rarity equivalent, SD 16 | 129.2588916 |
| Two-test AND rarity equivalent, SD 16 | 139.9394858 |
| Worst-case stated conditional quantization budget | 3.36600000005665e-11 |

Independent direct-tail and correlation-integral calculations of the four Towers joint probabilities agreed with the stored values within `1.1e-19` absolute. Independently recomputed Wilson endpoints agreed within `1.7e-21`. These are observed numerical comparisons, not proved error bounds for the integration libraries.

## Fresh Ada execution

Both projects were copied to fresh temporary directories and compiled using the matching Alire environment with their existing runtime assertion and overflow checks. The compiler and builder executable hashes match the retained proof campaign; see [environment metadata](environment.json). The fresh commands, timestamps, statuses, and source identities are in [fresh-ada-checks.json](fresh-ada-checks.json), [Hoeflin source hashes](hoeflin/source_hashes.json), and [Towers source hashes](towers/source_hashes.json).

Seed `20261030` and 1,000,000 trials were used. All six fresh numerical CSVs are byte-for-byte identical to their counterparts in `verification/evidence/computer10-20261031/runtime/`:

- Hoeflin: [calculations](hoeflin/calculations.csv) and [simulation](hoeflin/simulation.csv).
- Towers: [calculation](towers/calculation.csv), [grid](towers/grid.csv), [calibration](towers/calibration.csv), and [simulation](towers/simulation.csv).

Validation and independent replay passed both normally and under `python -O`. Hoeflin's maximum observed calculation error remains `2.842170943040401e-14` against tolerance `5e-11`. Its [replay](hoeflin/replay.json) matches all tail counts and agrees on means/variances within the recorded tolerances. The [Towers validation log](towers-validation.stdout) confirms agreement with the independent reference CSVs and exact replay of all 16 event-cell counts across four cases. The optimized logs and JSON results are also retained in this directory.

## Deal and SPARK evidence

`make check PYTHON=.venv-deal/bin/python` passed contract coverage, the static gate, and all **110 tests**, with no test failures or skips. The [complete log](python-checks.log) confirms 20 Python files, 142 named functions, 416 Deal decorators, 19 clean positive lint files, and the required single `DEL012` negative diagnostic. The [focused symbolic rerun](symbolic-proof.log) proved both pure acceptance-gate postconditions, with no skips counted as proofs.

The verification audit inspected the actual coverage/static JSON, JUnit results, 27-command record, symbolic logs, native GNATprove summaries, tool banners, GPR source lists, core contracts, explicit SPARK-off adapters, and source-history mechanism. All reported metrics and limitations agree:

| Core | Native total | Flow | Proof | Unproved | Justified |
|---|---:|---:|---:|---:|---:|
| Hoeflin/Ferguson | 47 | 8 | 39 | 0 | 0 |
| Towers | 31 | 9 | 22 | 0 | 0 |

The Towers native report confirms 11/11 subprograms and packages analyzed, with 13 run-time checks and 9 functional-contract checks. The Hoeflin native report confirms 9/9 analyzed; its proof category includes GNATprove simplification. The five-prover portfolio result does not imply that all independent solver runs completed.

All three retained SPARK campaigns passed source/integrity auditing in both normal and optimized Python: see [evidence-audits.json](evidence-audits.json) and its six stdout/stderr pairs. All five earlier evidence directories retain complete checksum inventories. All 23 historical Python identities resolve to verified Git blobs, and all 18 current Ada/GPR identities match the proof-campaign records. The negative union control remains rejected.

**The provers were not rerun for this audit.** The proof sources have not changed; this step checked retained reports and their identities. The latest actual prover run remains the [previous SPARK integration campaign](../deal-lint-spark-computer10-20261031/REPORT.md). The [final Deal campaign](../deal-lint-clean-computer10-20261031/REPORT.md) retains its original 27-command evidence without alteration.

## Rebuild and scope

Both reports were rebuilt with their `make pdf` targets using XeLaTeX and KOMA-Script with the existing 16 mm margins. [Hoeflin build log](hoeflin-pdf-build.log) and [Towers build log](towers-pdf-build.log) are retained. Final source/PDF identities are in [artifacts.json](artifacts.json); [SHA256SUMS](SHA256SUMS) covers this audit's evidence files.

This audit checks internal consistency and reproducibility against repository code and retained evidence. It does not authenticate the historical authors' claims afresh, establish a universal Python proof, independently recheck SMT proof objects, prove numerical-library or quadrature error bounds, establish pseudo-random independence, or validate Gaussian/psychometric assumptions. Those boundaries remain explicit in both reports.
