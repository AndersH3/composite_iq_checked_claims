(** Module: AuditGaussianPosteriorMeasure.v
    Purpose: Report transitive logical assumptions of each theorem in
    GaussianPosteriorMeasure.v, in a process separate from compilation and
    independent kernel checking. No additional mathematical declarations.
    Researcher/requester: Anders Hellström.
    AI disclosure: AI-assisted audit source.
*)
Require Import GaussianPosteriorMeasure.

Print Assumptions gmc_sufficient_statistic_posterior_center.
Print Assumptions gmc_sufficient_statistic_posterior_variance.
Print Assumptions gmc_normalized_gaussian_sufficient_statistic_posterior.
Print Assumptions gmc_normal_pdf_centered_residual.
Print Assumptions gmc_gaussian_observation_residual_density_factor.
Print Assumptions gmc_gaussian_observation_marginal_measure.
