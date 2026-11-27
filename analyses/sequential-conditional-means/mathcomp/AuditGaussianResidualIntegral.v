(** Module: AuditGaussianResidualIntegral.v
    Purpose: Print transitive assumptions for the actual residual
    integral transport and posterior first-moment proof targets.
    Researcher/requester: Anders Hellström.
    AI disclosure: AI-assisted audit source.
*)
Require Import GaussianResidualIntegral.

Print Assumptions gmc_residual_nonnegative_integral.
Print Assumptions gmc_residual_integrable.
Print Assumptions gmc_residual_signed_integral.
Print Assumptions gmc_posterior_first_moment_integrable.
Print Assumptions gmc_posterior_first_moment.
