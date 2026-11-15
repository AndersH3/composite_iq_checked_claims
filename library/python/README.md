# Shared Python source

> **AI disclosure:** The consolidation and this documentation were AI-assisted.

`numeric.finite_real` is the **single production implementation** of the finite real guard formerly duplicated in the Hoeflin/Ferguson and Towers calculation validators. The Sequential CSV validator imports the same guard. It has ten distinct Deal decorators documenting rejection of NaN, infinities, booleans, nonnumbers and large integer overflow; no string coercion is permitted.

`statistics.py` is the original pure, shared Dask-report statistical aggregation implementation. It is **moved**, not duplicated. Its three functions provide the cross-report moment, event and replicate-pooling calculations, reusing SciPy maintained statistics. `reporting/statistics.py` remains an import-only compatibility interface and `reporting/simulate.py` consumes the canonical library directly.

Every analysis retains specialized calculations and checks in its own `analyses/<project>/scripts/` directory. Keep statistical metadata, report interpretation, CSV I/O and numerical model assumptions in those adapters; move only genuinely reusable algorithms into this library.

Verify with `python verification/check_contract_coverage.py`, `python -m pytest -q tests`, `bash scripts/check_library_layout.sh` and the CI workflows.

## Complete AI disclosure

ChatGPT performed this source consolidation and documentation. Deal contracts test declared pre/postconditions in their supported execution scope, not empirical IQ-model validity or correctness of arbitrary scientific assumptions. Historical hashes and datasets remain separate immutable evidence.
