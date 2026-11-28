(** Module: AuditGaussianJointDensityMeasure.v
    Purpose: Audit each mathematical target of the scalar Gaussian
    joint density measure independently of compilation and kernel checking.
    Researcher/requester: Anders Hellström.
    AI disclosure: AI-assisted audit source; no new mathematical axioms.
*)
Require Import GaussianJointDensityMeasure.

Print Assumptions gmc_joint_likelihood_center.
Print Assumptions gmc_joint_density_measurable.
Print Assumptions gmc_joint_density_ge0.
Print Assumptions gmc_joint_mass0.
Print Assumptions gmc_joint_mass_ge0.
Print Assumptions gmc_joint_mass_sigma_additive.
Print Assumptions gmc_joint_mass_sections.
