(** Module: AuditGaussianProductHistory.v
    Purpose: Audit the five generic product-history integration targets.
    Researcher/requester: Anders Hellström.
    AI disclosure: AI-assisted audit source.
*)
Require Import GaussianProductHistory.

Print Assumptions gmc_product_fst_integrable.
Print Assumptions gmc_product_snd_integrable.
Print Assumptions gmc_product_residual_zero_event.
Print Assumptions gmc_product_additive_integrable.
Print Assumptions gmc_product_additive_mean_event.
