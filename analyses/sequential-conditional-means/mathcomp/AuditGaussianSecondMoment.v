(** Module: AuditGaussianSecondMoment.v
    Purpose: Audit all 4 new proof targets independently of compilation.
    Researcher/requester: Anders Hellström.
    AI disclosure: AI-assisted audit source.
*)
Require Import GaussianSecondMoment.

Print Assumptions gmc_weighted_pdf_nonzero_witness.
Print Assumptions gmc_centered_square_pdf_integrable.
Print Assumptions gmc_centered_normal_second_moment_integrable.
Print Assumptions gmc_standard_coordinate_second_moment.
