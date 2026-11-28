(** Module: AuditGaussianSignedMean.v
    Purpose: Print transitive assumptions of five signed-reflection,
    odd-integral and centered Gaussian mean proof targets.
    Researcher/requester: Anders Hellström.
    AI disclosure: AI-assisted audit source.
*)
Require Import GaussianSignedMean.

Print Assumptions gmc_lebesgue_signed_reflection.
Print Assumptions gmc_lebesgue_odd_integral_zero.
Print Assumptions gmc_centered_normal_pdf_even.
Print Assumptions gmc_centered_weighted_pdf_integral_zero.
Print Assumptions gmc_centered_normal_mean_zero.
