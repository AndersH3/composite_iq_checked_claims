(** Module: AuditJointLawConditionalExpectation.v
    Purpose: Audit the three original-space regression bridge targets
    in a separate Rocq process without expensive signature printing.
    Researcher/requester: Anders Hellström.
    AI disclosure: AI-assisted audit source; no new declarations.
*)
Require Import JointLawConditionalExpectation.

(* Audit independence of the residual from the full history. *)
Print Assumptions joint_law_iff_innovation_independent_of_history.
(* Audit the defining conditional-expectation identity. *)
Print Assumptions joint_law_regression_conditional_expectation.
(* Audit the canonical almost-sure conditional mean. *)
Print Assumptions joint_law_regression_conditional_mean_almost_sure.
