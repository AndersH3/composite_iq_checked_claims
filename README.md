# Composite IQ: Checked Claims

Statistical analyses of claims about combining IQ scores. Each analysis has its own folder containing its source, compiled report, references, and supporting calculations.

**AI disclosure:** this project was substantially generated and revised with OpenAI Codex and collaborating AI agents. The full disclosure below covers the analyses, replacement texts, software, verification and publication workflow.

| Analysis | Report | Source |
|---|---|---|
| [Hoeflin/Ferguson: combining IQ scores](analyses/hoeflin-ferguson/) | [PDF](analyses/hoeflin-ferguson/output/pdf/composite_iq_analysis.pdf) | [XeLaTeX](analyses/hoeflin-ferguson/composite_iq_analysis.tex) |
| [Towers: multiple-test admissions, original letter and follow-up](analyses/towers-multiple-test-admissions/) | [PDF](analyses/towers-multiple-test-admissions/output/pdf/towers_admissions_analysis.pdf) | [XeLaTeX](analyses/towers-multiple-test-admissions/towers_admissions_analysis.tex) |
| [Sequential conditional means: one, two or three fixed starting scores](analyses/sequential-conditional-means/) | [PDF](analyses/sequential-conditional-means/output/pdf/sequential_conditional_means.pdf) | [XeLaTeX](analyses/sequential-conditional-means/sequential_conditional_means.tex) |

Build instructions and numerical verification commands are in each analysis folder's README.

The Hoeflin/Ferguson and Towers analyses include [Ada calculations and simulations with SPARK verification on computer10](verification/README.md). The [symbolic-check follow-up](verification/evidence/symbolic-fixture-computer10-20261105/REPORT.md) records fresh Python verification and re-audits the unchanged 1,100 native SPARK checks from the [five-contract campaign](verification/evidence/five-contracts-computer10-20261104/REPORT.md). The follow-up does not claim a new GNATprove run. The Ada proofs cover the algorithm and driver bodies as well as the original arithmetic cores. Small checked numerical interfaces and system I/O remain explicit trusted boundaries. Native `.spark` records distinguish analyzed bodies from specifications whose bodies were not proved; numerical validation and Monte Carlo results remain separate evidence.

The sequential conditional-means analysis derives the average of `a, e_1, ..., e_k`, including the fixed starting score `a` as the first value. Every test has population mean 0 and standard deviation 1. Under the stated joint Gaussian model, every subsequent recursive prediction equals `c a`, and the requested average is `a (1 + k c) / (k + 1)`. It also derives the population standard deviation of the actual test-score mean, `sqrt((1 + k c) / (k + 1))`, and its conditional standard deviation after fixing the first score, `sqrt(k (1 - c) (1 + k c)) / (k + 1)`. The fixed recursive average itself has standard deviation zero. Additional derivations cover two or three initial scores all equal to `a`, with every starting score included in the mean and with corresponding population and conditional SD formulas. Worked IQ-150 examples use a mean-100, SD-15 reporting scale, correlation 0.6, and 1, 2 or 10 subsequent predictions for each starting-score count. Its own [README](analyses/sequential-conditional-means/) records the scope, build checks and AI disclosure for this analysis; the historical formal-verification campaigns above do not cover its mathematical text.

Implemented SPARK predicates, explicit Ghost observations and ordinary request receipts model every remaining project specification-only boundary, foreign import and private I/O helper. The source-pinned register also audits explicit sine/cosine model links and lists external dependencies. Models cover accepted returns and report requests; excluded implementation refinement, exact bytes, exception behavior and model adequacy remain unproved. Both Ghost-enabled and Ghost-disabled builds retain ordinary runtime assertions, and their numerical outputs are compared.

All current Python files, including tests and fixtures, must contain [Deal contracts](https://deal.readthedocs.io/). Every named function must have at least five distinct, meaningful Deal decorators, checked by `verification/check_contract_coverage.py`; comments, strings and repeated decorator syntax do not count. There is no upper limit: functions with six or more distinct contracts are accepted. The GitHub workflow enforces this repository-wide policy.

Every SPARK function and procedure, including local helpers, ghost operations and trusted interfaces, has at least five explicit behavioral clauses or flow contracts. [The per-subprogram audit](verification/spark_contracts.py) counts top-level Pre/Post conjuncts, Contract_Cases alternatives and explicit Global/Depends aspects. It excludes mode flags, subtype declarations and body assertions. Five counted entries need not be five logically independent guarantees; range characterizations and endpoint facts may overlap. Native body/spec coverage and proof results remain separate checks.

The model packages now combine ordinary pure predicates/types with explicit Ghost observers/checkers. Five request-receipt updates are ordinary SPARK so normal-return postconditions remain executable with Ghost disabled. Request state does not certify physical I/O. Earlier Ghost-only records remain unchanged.

For Python development and checks:

```sh
git clone https://github.com/AndersH3/composite_iq_checked_claims.git
cd composite_iq_checked_claims
python3 -m venv .venv
. .venv/bin/activate
python -m pip install -r requirements-dev.txt
make check
```

The [local folder relocation record](verification/evidence/local-folder-rename-computer10-20261102/REPORT.md) documents environment repairs and preservation checks on computer10.

`make check` and GitHub Actions require contract coverage, clean positive static lint, the exact expected failure of the deliberately broken fixture, runtime/property tests, and the [symbolic acceptance gate](verification/check_symbolic.py). The [current evidence report](verification/evidence/symbolic-fixture-computer10-20261105/REPORT.md) records these results. The unchanged negative fixture now yields an actual symbolic counterexample, rather than an unsupported-tool exception; all six other postcondition obligations prove. A scoped, version-pinned integer type model and a restricted comparison-chain normalization preserve its original contracts. The extension is part of the trusted verification tooling and does not prove arbitrary Python. See [reproduction and limits](verification/README.md#deal-symbolic-check). The [earlier Deal snapshot](verification/evidence/deal-lint-clean-computer10-20261031/REPORT.md) retains its 110-test result and optimized-Python, numerical, and symbolic evidence; those historical counts are not the current test inventory. The [original Deal report](verification/evidence/deal-computer10-20261031/REPORT.md) preserves the resolved diagnostics. Runtime checks and property tests are distinct from universal formal verification.

## AI disclosure and provenance

This project was substantially generated and revised using **OpenAI Codex and collaborating AI sub-agents**. The session identifies Codex as based on the GPT-6 family. Exact serving checkpoints, per-agent model identifiers and generation settings were not preserved as versioned provenance; no more precise model attribution is claimed. The historical disclosure below covers the Hoeflin/Ferguson and Towers reports, their corrected replacement texts, and the project's supporting code and earlier revisions. The sequential conditional-means report includes its own disclosure dated 13 November 2026.

AI contributions included interpreting the supplied articles; drafting and revising mathematical exposition and statistical discussion; selecting and checking numerical examples; researching references; designing and editing Python/Deal and Ada/SPARK programs, ghost models, tests and evidence auditors; running verification tools; typesetting and visually inspecting PDFs; and preparing repository commits. The human requester supplied the source articles, specified the objectives, formats and verification requirements, requested revisions, and authorized publication. The recorded audits and parallel reviews were carried out by AI agents and automated tools. **Independent human peer review or professional sign-off is not recorded and is not claimed.** Repository ownership and Git commit attribution do not establish that text or code was human-authored.

The original authors remain credited as sources. The replacement articles are AI-generated analytical reconstructions prepared for this project. No endorsement by the original authors, source hosts or cited organizations is claimed. Sources were consulted at different levels, including article text, software documentation and bibliographic metadata; per-reference notes identify access limits. Full-text review of every cited work is not claimed.

Calculations, tests and prover invocations were actually executed on **computer10**. Versioned evidence retains actual commands, native outputs, tool identities, source hashes and checksums. Formal claims rest on the machine-checker results under the documented specifications and assumptions. “Independent” numerical validation or replay means a separate implementation, algorithm or library; it does not mean independent human authorship. The code, contracts, tests and their reviews were developed within the same AI workflow. Correctness of the specifications, excluded implementation refinement, numerical accuracy and statistical-model adequacy remain separate from proof of the encoded properties. Ghost models do not prove foreign numerical libraries or physical I/O correct.

No new participant data were collected and no empirical psychometric validation study was performed for this project. Simulations use synthetic draws under the stated mathematical model. The repository preserves source and evidence history, but not a complete prompt/tool transcript, exact per-line authorship or an AI-contribution percentage. Those details cannot be reconstructed reliably and have not been invented. This disclosure is current through **5 November 2026**. Each PDF contains an upfront notice and the full disclosure so it remains visible when distributed separately.

The repository's original material is governed by [LICENSE](LICENSE), subject to third-party rights.
