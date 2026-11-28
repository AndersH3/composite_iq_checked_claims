(** Module: AuditResidualAssumptions.v
    Purpose: Audit the transitive logical axioms of the compiled residual
    conditional-expectation targets. Run in a separate Rocq process to
    limit peak resource usage. Match the previously successful local
    Print Assumptions-only procedure; do not pretty-print the large
    dependent theorem signatures in this audit.
    Researcher/requester: Anders Hellström.
    AI disclosure: AI-assisted audit source; kernel output is the evidence.
    No declarations, axioms, or proof scripts are introduced.
*)
Require Import GaussianResidualConditionalExpectation.

(* Audit gaussian_regression_conditional_expectation_with_residual_mean. *)
Print Assumptions gaussian_regression_conditional_expectation_with_residual_mean.

(* Audit gaussian_regression_conditional_expectation_centered. *)
Print Assumptions gaussian_regression_conditional_expectation_centered.

(* Audit gaussian_regression_perfect_information_conditional_expectation. *)
Print Assumptions gaussian_regression_perfect_information_conditional_expectation.

(* Audit gaussian_regression_perfect_information_mean_almost_sure. *)
Print Assumptions gaussian_regression_perfect_information_mean_almost_sure.

(* Audit gaussian_regression_conditional_mean_almost_sure. *)
Print Assumptions gaussian_regression_conditional_mean_almost_sure.

(* Audit gaussian_regression_transfer_to_future. *)
Print Assumptions gaussian_regression_transfer_to_future.
