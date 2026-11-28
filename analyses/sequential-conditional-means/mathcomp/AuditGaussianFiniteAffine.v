(** Module: AuditGaussianFiniteAffine.v
    Purpose: Audit the nine coordinate-moment and affine-law
    proof targets independently of their proof compilation.
    Researcher/requester: Anders Hellström.
    AI disclosure: AI-assisted audit source.
*)
Require Import GaussianFiniteAffine.

Print Assumptions gmc_standard_coordinate_nonnegative.
Print Assumptions gmc_standard_coordinate_integrable.
Print Assumptions gmc_standard_coordinate_signed.
Print Assumptions gmc_standard_coordinate_first_moment.
Print Assumptions gmc_standard_coordinate_mean_zero.
Print Assumptions gmc_affine_row_measurable.
Print Assumptions gmc_affine_map_measurable.
Print Assumptions gmc_affine_history_normalized.
Print Assumptions gmc_affine_history_event.
