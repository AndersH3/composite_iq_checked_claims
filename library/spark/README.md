# Central SPARK 2022 shared library

> **AI disclosure:** This source and design are AI-assisted. Source contracts are obligations; they are not claims of a completed GNATprove campaign on this revision.

Two independently reusable packages now centralize previously duplicated integer arithmetic:

- `Shared_Equicorrelation` owns **one exact signed scaled numerator** `1000 + (N-1)*C` for Hoeflin/Ferguson and Sequential, with more than ten distinct sign/domain/boundary postconditions.
- `Shared_Event_Arithmetic` owns the **exact unit-scale inclusion-exclusion and complement** calculations consumed by Towers admissions. It does not perform numerical integration or infer independent events.

The packages do not import report-specific code and never claim normality or population assumptions. Their consumers reside in each analysis' `ada/src/`, with project files pointing to `../../../library/spark/src`. Interfaces preserve the public domain-specific Ada types and contracts; the canonical implementations have no report-specific dependencies.

`verification/spark_contracts.py` inventories current shared and specialized clauses. A fresh GNATprove proof campaign (and source-specific evidence hashes) must be run separately before claiming static proof of all new calling contexts. Historical campaigns are immutable.

## Complete AI disclosure

OpenAI ChatGPT wrote and refactored this shared SPARK code and its documentation. Explicit contracts must still be discharged or enforced; compiler success alone cannot certify floating-point accuracy, Gaussian assumptions, empirical IQ data or a fresh GNATprove proof campaign.
