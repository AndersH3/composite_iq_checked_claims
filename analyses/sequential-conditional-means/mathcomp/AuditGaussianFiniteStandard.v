(** Module: AuditGaussianFiniteStandard.v
    Purpose: Audit the eight finite-dimensional standard Gaussian
    construction, normalization and coordinate-law proof targets.
    Researcher/requester: Anders Hellström.
    AI disclosure: AI-assisted audit source.
*)
Require Import GaussianFiniteStandard.

Print Assumptions gmc_history_cons_measurable.
Print Assumptions gmc_standard_history_normalized.
Print Assumptions gmc_standard_history_empty.
Print Assumptions gmc_history_cons_rectangle.
Print Assumptions gmc_standard_history_rectangle.
Print Assumptions gmc_standard_history_head.
Print Assumptions gmc_standard_history_tail.
Print Assumptions gmc_standard_history_coordinate.
