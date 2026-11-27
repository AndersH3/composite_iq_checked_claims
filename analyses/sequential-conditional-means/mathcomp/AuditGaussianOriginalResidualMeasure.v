(** Module: AuditGaussianOriginalResidualMeasure.v
    Purpose: Report transitive logical assumptions of each theorem in
    GaussianOriginalResidualMeasure.v, in a process separate from compilation and
    independent kernel checking. No additional mathematical declarations.
    Researcher/requester: Anders Hellström.
    AI disclosure: AI-assisted audit source.
*)
Require Import GaussianOriginalResidualMeasure.

Print Assumptions gmc_original_residual_slice.
Print Assumptions gmc_original_residual_rectangle.
