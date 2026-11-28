# Expanded Python static analysis

**Researcher/requester:** Anders Hellström.

> **AI disclosure:** AI-assisted configuration and integration. Tool installation, execution and findings must be verified on the pinned Python 3.13 environment. No clean static-analysis result is claimed before actual execution.

Install the standalone analyzers alongside the existing tested Deal environment, and isolate Prospector's aggregator dependencies:

```bash
.venv/bin/python -m pip install -r requirements-analysis.txt
python3 -m venv .venv-prospector
.venv-prospector/bin/python -m pip install -r requirements-prospector.txt
.venv/bin/python -m pip check
.venv-prospector/bin/python -m pip check
make static-analysis PYTHON=.venv/bin/python
```

All eight requested tools scan the tracked Python inventory, including tests and fixtures. The two requirements files retain the existing runtime/Deal/Astroid pins. All eight pinned analyzer installations passed pip check on computer10; full execution regression remains pending; transitive packages are recorded using pip freeze. No runtime pin is upgraded intentionally.

| Tool | Report | Initial policy |
| --- | --- | --- |
| Pylint | Full default messages, score and reports | Findings baseline; fatal/usage errors fail |
| Flake8 | Default style and Pyflakes rules, McCabe threshold 10 | Baseline |
| Pyflakes | Independent binding/import scan | Baseline |
| Bandit | All severity/confidence levels in JSON | Baseline; separate high-severity/high-confidence gate |
| Vulture | Unused-code candidates, confidence >=60 | Baseline; dynamic uses need review |
| Radon | CC, MI, raw and Halstead JSON metrics | Metrics; errors fail |
| Prospector | High strictness, test and doc warnings, unblended JSON | Baseline; tool errors fail |
| Ruff | E/F/W/I/UP/B/S/SIM/C90 JSON | Baseline; F63/F7/F82 and unconditional syntax-error correctness gate |

`make check` includes the extended suite in addition to all previous Deal checks and runtime tests. `make static-analysis` runs only the extended checks. `make static-analysis-strict` additionally fails on any baseline finding; Radon measurements themselves are not findings. No automatic edits or baseline-wide suppression. Strict mode is deliberately not the initial default because existing findings have not yet been triaged. Review each warning, especially Dask delayed objects, public compatibility imports, pytest fixtures and security warnings about deliberate test assertions or seeded numerical simulation. A heuristic finding is not proof of dead code or exploitability.

The runner checks that every requested distribution is installed, validates machine-readable output, and retains native stdout, stderr, exit codes, tracked source list, Git commit/status, and package environments under `.analysis-results/` (override with ANALYSIS_OUTPUT). CI uploads that directory even on failure. The CI job is independent of the existing Deal and Dask test jobs. Only the existing mandatory Deal audit interprets the deliberate DEL012 fixture as a negative control. Flake8 loads the Deal plugin automatically, so it reuses the existing `compile_fixed_locations` compatibility helper and runs serially to retain the process-local patch. Its output excludes the duplicate DEL rule family, which the independent mandatory Deal audit checks in full. Other Flake8 rules and all tracked Python files remain in scope.

Initial correctness/security gates are intentionally narrow, not a claim that all other issues are harmless. Establish the first diagnostic baseline, refactor genuine defects, and tighten the mandatory checks as findings are resolved. A zero exit from baseline mode is not proof that all eight analyzers reported no findings. No new mathematical proof development is authorized by this tooling change.

## Initial diagnostic triage

At 42a1814 all eight tools installed successfully. Seven completed their scans; the Flake8 traceback identified Deal's synthetic AST range error in its automatically loaded plugin, not a native Flake8 defect. The runner now reuses the same location-only compatibility function as the standalone Deal lint, without modifying the installed package. Pyflakes identified ten intentional re-exports in reporting/statistics.py (now explicitly declared in __all__) and one unused math import in a test (removed). Vulture identified the pytest fixture contracts_enabled, two deliberate lint-fixture functions, the dynamically loaded compile_fixed_locations helper and MOMENT_RTOL. Retain the first four; review references to the constant before removal. These changes are pending execution regression. Full native analysis findings remain necessary before broader refactoring.

## Complete AI disclosure

The source integration, version selection and staged enforcement policy were AI-assisted at the request of Anders Hellström. The analyzers provide overlapping, imperfect static evidence; no program-correctness, security, or empirical model certification follows from their results. Runtime and independent Rocq verification remain separate.
