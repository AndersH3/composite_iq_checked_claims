(** Module: AuditGaussianLocationMean.v
    Purpose: Print transitive assumptions for seven Gaussian centering
    and location-mean targets.
    Researcher/requester: Anders Hellström.
    AI disclosure: AI-assisted audit source.
*)
Require Import GaussianLocationMean.

Print Assumptions gmc_normal_centered_nonnegative_integral.
Print Assumptions gmc_normal_centered_integrable.
Print Assumptions gmc_normal_centered_signed_integral.
Print Assumptions gmc_normal_centered_coordinate_integrable.
Print Assumptions gmc_normal_centered_coordinate_mean_zero.
Print Assumptions gmc_normal_first_moment_integrable.
Print Assumptions gmc_normal_mean.
