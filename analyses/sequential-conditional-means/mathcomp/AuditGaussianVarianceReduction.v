(** Module: AuditGaussianVarianceReduction.v
    Purpose: Audit seven scalar variance reduction and coordinate
    product theorem targets; the exact unit variance is not assumed.
    Researcher/requester: Anders Hellström.
    AI disclosure: AI-assisted audit source.
*)
Require Import GaussianVarianceReduction.

Print Assumptions gmc_standard_variance_finite.
Print Assumptions gmc_standard_variance_density.
Print Assumptions gmc_standard_density_balance_integrable.
Print Assumptions gmc_standard_density_balance_integral.
Print Assumptions gmc_standard_coordinate_variance_value.
Print Assumptions gmc_standard_all_coordinate_products_integrable.
Print Assumptions gmc_standard_coordinate_product_value.
