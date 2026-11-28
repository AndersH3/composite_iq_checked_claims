(** Module: AuditGaussianScalarConditionalMean.v
    Purpose: Audit nine scalar joint Gaussian integrability,
    residual event and conditional mean characterization targets.
    Researcher/requester: Anders Hellström.
    AI disclosure: AI-assisted audit source.
*)
Require Import GaussianScalarConditionalMean.

Print Assumptions gmc_product_observation_integrable.
Print Assumptions gmc_product_residual_integrable.
Print Assumptions gmc_posterior_mean_marginal_integrable.
Print Assumptions gmc_joint_residual_integrable.
Print Assumptions gmc_joint_posterior_mean_integrable.
Print Assumptions gmc_joint_latent_integrable.
Print Assumptions gmc_joint_residual_event_zero.
Print Assumptions gmc_joint_conditional_mean_event.
Print Assumptions gmc_joint_conditional_mean_characterization.
