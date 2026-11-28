# Canonical mathematical and numerical libraries

**Author:** Anders Hellström.

The current library has three maintained components: [Python statistical/numeric helpers](python/README.md), reused by Dask simulation and verification, and [Rocq mathematical proofs](rocq/README.md), checked by the documented Rocq kernel workflows. There is **no maintained discontinued alternate-engine source or duplicated report-local sampling engine**. Reuse Python/NumPy/SciPy/Dask standard interfaces and checked Rocq lemmas instead of constructing parallel implementations. The [shared XeLaTeX report template](latex/README.md) is the third component and is imported by all eight books.

The repository enforces library ownership with `scripts/check_library_layout.sh`, Python/Deal contract checks and the separate Rocq compilation. Program contracts and formal proofs have distinct premises, and neither certifies empirical psychometric assumptions.

> **AI disclosure:** This shared-library organization and substantial parts of its source and documentation were developed with AI assistance. Automated validation does not equal independent human verification.
