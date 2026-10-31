# SPARK rerun through the Deal-contracted launcher

Executed on computer10 on 31 October 2026 with Deal runtime contracts enabled. Both portfolios passed: Hoeflin/Ferguson 47 checks (8 flow, 39 proof) and Towers 31 checks (9 flow, 22 proof), with zero unproved or justified checks. The incorrect union control was rejected.

The Ada/SPARK sources are unchanged. This run checks the newly contracted orchestration path; it does not convert Python, numerical libraries, or Gaussian assumptions into SPARK proofs.

- [Manifest and actual invocations](manifest.json)
- [Hoeflin native report](hoeflin/portfolio/gnatprove.out)
- [Towers native report](towers/portfolio/gnatprove.out)
- [Source hashes](source_hashes.json)
- [Checksums](SHA256SUMS)
- [Full earlier independent-prover comparison](../computer10-20261031/REPORT.md)
- [Python contract checks](../deal-computer10-20261031/REPORT.md)

Audit this run with `python3 verification/verify_evidence.py verification/evidence/deal-spark-computer10-20261031` from a repository checkout.
