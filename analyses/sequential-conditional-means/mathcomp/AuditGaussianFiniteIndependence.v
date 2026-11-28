(** Module: AuditGaussianFiniteIndependence.v
    Purpose: Audit all 5 new proof targets independently of compilation.
    Researcher/requester: Anders Hellström.
    AI disclosure: AI-assisted audit source.
*)
Require Import GaussianFiniteIndependence.

Print Assumptions gmc_history_tail_coordinate.
Print Assumptions gmc_history_coordinate_event_measurable.
Print Assumptions gmc_standard_history_head_other.
Print Assumptions gmc_standard_history_other_other.
Print Assumptions gmc_standard_history_pair_independent.
