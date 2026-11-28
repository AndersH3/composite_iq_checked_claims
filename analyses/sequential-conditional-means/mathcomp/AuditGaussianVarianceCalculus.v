(** Module: AuditGaussianVarianceCalculus.v
    Purpose: Audit seven standard normal density differentiation,
    continuity and finite-interval integration theorem targets.
    Researcher/requester: Anders Hellström.
    AI disclosure: AI-assisted audit source.
*)
Require Import GaussianVarianceCalculus.

Print Assumptions gmc_standard_density_expression.
Print Assumptions gmc_standard_exponent_derivative.
Print Assumptions gmc_standard_density_derivative.
Print Assumptions gmc_standard_weighted_density_derivative.
Print Assumptions gmc_standard_weighted_density_continuous.
Print Assumptions gmc_standard_density_balance_continuous.
Print Assumptions gmc_standard_density_balance_interval.
