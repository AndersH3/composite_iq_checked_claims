# Canonical shared libraries

> **AI disclosure:** This source architecture and documentation were drafted with AI assistance. Rocq compilation, Python contracts and static SPARK checks have separate verification scopes; model validity is not inferred from source reuse.

The three analyzed reports have separate specialized sources and proofs, but **one canonical ownership location** for every shared component:

| Language | Reusable source | Primary consumers |
|---|---|---|
| [Rocq 9.2](rocq/README.md) | `library/rocq/*.v` | all three report-specific `analyses/*/rocq/` theorem families |
| [SPARK 2022](spark/README.md) | `library/spark/src/*.ads, *.adb` | Hoeflin and Sequential share the exact equicorrelation numerator; Towers uses shared exact event arithmetic |
| [Python 3.13](python/README.md) | `library/python/numeric.py` and `statistics.py` | Hoeflin, Towers and Sequential validators, common Dask aggregation |

The formal specialization directories are [Hoeflin/Ferguson](../analyses/hoeflin-ferguson/rocq/), [Towers admissions](../analyses/towers-multiple-test-admissions/rocq/) and [Sequential conditional means](../analyses/sequential-conditional-means/rocq/). Each report also retains its specialized `ada/src/` units, `scripts/` validators and data; imported generic algorithms live in `library/`, not copied into other reports.

Run `bash scripts/check_library_layout.sh` to enforce canonical locations, three report consumers and the absence of duplicate finite-real validators; `bash scripts/check_rocq_documentation.sh` verifies the 18-module proof inventory; `sh scripts/compile_rocq.sh` compiles a fresh copy of the canonical source tree under Rocq 9.2. `make check` includes structural, Deal, runtime and symbolic checks. The historical evidence and fixed source revisions remain unmodified.

**Trust boundary:** structural checks detect specified duplication and dependency violations, not all possible semantic duplication. A successful SPARK contract inventory is not a new GNATprove proof of changed source. Normality, tail-integral accuracy and empirical IQ-model parameters remain independently unverified.

## Complete AI disclosure

OpenAI ChatGPT assisted with the library design, migration and reproducibility documentation, exact SPARK implementation and contract wording, Python reuse, Rocq source relocation and CI integration. Automated checks are necessary but do not prove scientific-model assumptions. A new source-specific GNATprove campaign is required for the changed SPARK callers; the existing archived campaigns cannot serve as fresh verification. Repository maintainers are responsible for review, numerical validation and accurate publication claims.
