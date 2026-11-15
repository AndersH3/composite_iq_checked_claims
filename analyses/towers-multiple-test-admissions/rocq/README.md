# Towers admissions specialized Rocq proofs

> **AI disclosure:** This module-ownership documentation was AI-assisted.

[`Admissions.v`](Admissions.v) and [`FourCellBridge.v`](FourCellBridge.v) own the report's four-cell event model, union, conditional-admissions and dependence theorems. Shared finite-event summation, moment and covariance operations reside in [the central Rocq library](../../../library/rocq/README.md). Specialized SPARK and Python source remains in the adjacent `ada/src/` and `scripts/` directories, using central exact event arithmetic where applicable.

Build using `sh scripts/compile_rocq.sh`; see the [report theorem inventory](../../../rocq/REPORT_THEOREM_INVENTORY.md). These discrete probability identities do not establish a continuous Gaussian joint-tail model.

## Complete AI disclosure

ChatGPT assisted with source placement and documentation. Kernel compilation validates only the declared theorem statements and hypotheses; empirical admissions rates and Gaussian assumptions remain unverified.
