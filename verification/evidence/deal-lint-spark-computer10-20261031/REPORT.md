# SPARK integration after the Deal lint fixes

Executed on computer10 on 31 October 2026 with the revised Python launcher and Deal runtime contracts enabled. Both fresh portfolios passed: Hoeflin/Ferguson 47 checks (8 flow, 39 proof), and Towers 31 checks (9 flow, 22 proof). Both have zero unproved and zero justified checks. The deliberately incorrect union contract was rejected.

The launcher used CVC5, Z3, Alt-Ergo, classic COLIBRI, and Yices together. This integration run exercises the revised literal export parsing and bounded version-process capture. The earlier independent-prover comparisons remain in the [original campaign](../computer10-20261031/REPORT.md).

- [Manifest, tool versions and actual commands](manifest.json)
- [Hoeflin native report](hoeflin/portfolio/gnatprove.out)
- [Towers native report](towers/portfolio/gnatprove.out)
- [Rejected negative control](negative_control/portfolio/gnatprove.out)
- [Source hashes](source_hashes.json) and [checksums](SHA256SUMS)
- [Python checks after the fixes](../deal-lint-clean-computer10-20261031/REPORT.md)

The native totals establish the specified SPARK core properties. They do not prove the Python orchestrator, numerical libraries, pseudo-random independence, or psychometric assumptions.

Audit from a full Git clone:

```sh
python verification/verify_evidence.py verification/evidence/deal-lint-spark-computer10-20261031
```

The connector-authored computer10 workspace additionally supplied `--git-dir /tmp/composite-iq-historical-git` for older evidence; all sources for this fresh campaign match the current tree directly.
