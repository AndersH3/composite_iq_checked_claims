(** Module: AuditGaussianCrossMoment.v
    Purpose: Audit the seven pair-law and cross-moment proof targets.
    Researcher/requester: Anders Hellström.
    AI disclosure: AI-assisted audit source.
*)
Require Import GaussianCrossMoment.

Print Assumptions gmc_standard_pair_product_measurable.
Print Assumptions gmc_standard_pair_product_integrable.
Print Assumptions gmc_standard_pair_product_mean_zero.
Print Assumptions gmc_standard_coordinate_pair_measurable.
Print Assumptions gmc_standard_coordinate_pair_law.
Print Assumptions gmc_standard_coordinate_cross_integrable.
Print Assumptions gmc_standard_coordinate_cross_zero.
