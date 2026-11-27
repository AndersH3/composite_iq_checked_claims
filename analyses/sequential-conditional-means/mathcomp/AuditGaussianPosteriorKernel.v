(** Module: AuditGaussianPosteriorKernel.v
    Purpose: Inspect transitive assumptions of all five scalar Gaussian
    conditional-distribution and observation marginal proof targets.
    Researcher/requester: Anders Hellström.
    AI disclosure: AI-assisted audit source.
*)
Require Import GaussianPosteriorKernel.

Print Assumptions gmc_posterior_kernel_measurable.
Print Assumptions gmc_posterior_kernel_integrable.
Print Assumptions gmc_posterior_joint_slice.
Print Assumptions gmc_posterior_kernel_rectangle.
Print Assumptions gmc_observation_marginal.
