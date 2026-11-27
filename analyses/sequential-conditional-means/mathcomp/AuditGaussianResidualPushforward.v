(** Module: AuditGaussianResidualPushforward.v
    Purpose: Audit the six scalar residual pushforward proof targets.
    Researcher/requester: Anders Hellström.
    AI disclosure: AI-assisted audit source.
*)
Require Import GaussianResidualPushforward.

Print Assumptions gmc_post_mean_measurable.
Print Assumptions gmc_residual_map_measurable.
Print Assumptions gmc_residual_rectangle_section.
Print Assumptions gmc_residual_pushforward_rectangle.
Print Assumptions gmc_joint_probability_mass.
Print Assumptions gmc_residual_pushforward_product.
