(** Module: AuditGaussianFirstMoment.v
    Purpose: Audit transitive assumptions of the six Gaussian
    domination, nonnegative integral and first-moment proof targets.
    Researcher/requester: Anders Hellström.
    AI disclosure: AI-assisted audit source.
*)
Require Import GaussianFirstMoment.

Print Assumptions gmc_abs_le_one_square.
Print Assumptions gmc_abs_exp_bound.
Print Assumptions gmc_centered_weighted_pdf_bound.
Print Assumptions gmc_centered_weighted_pdf_integrable.
Print Assumptions gmc_normal_nonnegative_integral.
Print Assumptions gmc_centered_normal_first_moment_integrable.
