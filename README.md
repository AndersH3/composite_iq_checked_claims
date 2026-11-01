# Composite IQ: Checked Claims

Statistical analyses of claims about combining IQ scores. Each analysis has its own folder containing its source, compiled report, references, and supporting calculations.

**AI disclosure:** this project was substantially generated and revised with OpenAI Codex and collaborating AI agents. The full disclosure below covers the analyses, replacement texts, software, verification and publication workflow.

| Analysis | Report | Source |
|---|---|---|
| [Hoeflin/Ferguson: combining IQ scores](analyses/hoeflin-ferguson/) | [PDF](analyses/hoeflin-ferguson/output/pdf/composite_iq_analysis.pdf) | [XeLaTeX](analyses/hoeflin-ferguson/composite_iq_analysis.tex) |
| [Towers: multiple-test admissions, original letter and follow-up](analyses/towers-multiple-test-admissions/) | [PDF](analyses/towers-multiple-test-admissions/output/pdf/towers_admissions_analysis.pdf) | [XeLaTeX](analyses/towers-multiple-test-admissions/towers_admissions_analysis.tex) |

Build instructions and numerical verification commands are in each analysis folder's README.

Both analyses include [Ada calculations and simulations with SPARK verification on computer10](verification/README.md). The [Ghost-boundary campaign](verification/evidence/ghost-boundaries-computer10-20261101/REPORT.md) covers the algorithm and driver bodies as well as the original arithmetic cores. Small checked numerical interfaces and system I/O remain explicit trusted boundaries. Native `.spark` records distinguish analyzed bodies from specifications whose bodies were not proved; numerical validation and Monte Carlo results remain separate evidence.

Implemented SPARK Ghost predicates, observations and abstract receipts model every remaining project specification-only boundary, foreign import and private I/O helper. The source-pinned register also audits explicit sine/cosine model links and lists external dependencies. Models cover accepted returns and report requests; excluded implementation refinement, exact bytes, exception behavior and model adequacy remain unproved. Both Ghost-enabled and Ghost-disabled builds retain ordinary runtime assertions, and their numerical outputs are compared.

All current Python files, including tests and fixtures, must contain [Deal contracts](https://deal.readthedocs.io/). Every named function is checked for a real Deal decorator by `verification/check_contract_coverage.py`; comments and strings do not count. The GitHub workflow enforces this repository-wide policy.

For Python development and checks:

```sh
python3 -m venv .venv
. .venv/bin/activate
python -m pip install -r requirements-dev.txt
make check
```

`make check` and GitHub Actions require contract coverage, clean positive static lint, the exact expected failure of the deliberately broken fixture, and runtime/property tests. The [Ghost-boundary campaign report](verification/evidence/ghost-boundaries-computer10-20261101/REPORT.md) records the checks for the expanded implementation. The [earlier Deal snapshot](verification/evidence/deal-lint-clean-computer10-20261031/REPORT.md) retains its 110-test result and optimized-Python, numerical, and symbolic evidence; those historical counts are not the current test inventory. The [original Deal report](verification/evidence/deal-computer10-20261031/REPORT.md) preserves the resolved diagnostics. Runtime checks and property tests are distinct from universal formal verification.

## AI disclosure and provenance

This project was substantially generated and revised using **OpenAI Codex and collaborating AI sub-agents**. The session identifies Codex as based on the GPT-6 family. Exact serving checkpoints, per-agent model identifiers and generation settings were not preserved as versioned provenance; no more precise model attribution is claimed. This disclosure covers both reports, their corrected replacement texts, the project's supporting code and earlier revisions, as well as the current additions.

AI contributions included interpreting the supplied articles; drafting and revising mathematical exposition and statistical discussion; selecting and checking numerical examples; researching references; designing and editing Python/Deal and Ada/SPARK programs, ghost models, tests and evidence auditors; running verification tools; typesetting and visually inspecting PDFs; and preparing repository commits. The human requester supplied the source articles, specified the objectives, formats and verification requirements, requested revisions, and authorized publication. The recorded audits and parallel reviews were carried out by AI agents and automated tools. **Independent human peer review or professional sign-off is not recorded and is not claimed.** Repository ownership and Git commit attribution do not establish that text or code was human-authored.

The original authors remain credited as sources. The replacement articles are AI-generated analytical reconstructions prepared for this project. No endorsement by the original authors, source hosts or cited organizations is claimed. Sources were consulted at different levels, including article text, software documentation and bibliographic metadata; per-reference notes identify access limits. Full-text review of every cited work is not claimed.

Calculations, tests and prover invocations were actually executed on **computer10**. Versioned evidence retains actual commands, native outputs, tool identities, source hashes and checksums. Formal claims rest on the machine-checker results under the documented specifications and assumptions. “Independent” numerical validation or replay means a separate implementation, algorithm or library; it does not mean independent human authorship. The code, contracts, tests and their reviews were developed within the same AI workflow. Correctness of the specifications, excluded implementation refinement, numerical accuracy and statistical-model adequacy remain separate from proof of the encoded properties. Ghost models do not prove foreign numerical libraries or physical I/O correct.

No new participant data were collected and no empirical psychometric validation study was performed for this project. Simulations use synthetic draws under the stated mathematical model. The repository preserves source and evidence history, but not a complete prompt/tool transcript, exact per-line authorship or an AI-contribution percentage. Those details cannot be reconstructed reliably and have not been invented. This disclosure is current through **1 November 2026**. Each PDF contains an upfront notice and the full disclosure so it remains visible when distributed separately.

The repository's original material is governed by [LICENSE](LICENSE), subject to third-party rights.
