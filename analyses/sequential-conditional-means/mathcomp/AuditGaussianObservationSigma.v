(** Module: AuditGaussianObservationSigma.v
    Purpose: Print transitive assumptions for twelve observation
    sigma-algebra, integral-transport and uniqueness targets.
    Researcher/requester: Anders Hellström.
    AI disclosure: AI-assisted audit source.
*)
Require Import GaussianObservationSigma.

Print Assumptions gmc_observation_sigma_events.
Print Assumptions gmc_observation_sigma_sub.
Print Assumptions gmc_observation_factor_measurable.
Print Assumptions gmc_observation_fiber_constant.
Print Assumptions gmc_observation_factorization.
Print Assumptions gmc_conditional_mean_sigma_measurable.
Print Assumptions gmc_observation_pushforward_event.
Print Assumptions gmc_observation_nonnegative_integral.
Print Assumptions gmc_observation_marginal_integrable.
Print Assumptions gmc_observation_signed_integral.
Print Assumptions gmc_conditional_mean_sigma_event.
Print Assumptions gmc_conditional_mean_unique.
