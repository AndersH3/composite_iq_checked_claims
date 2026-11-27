(** Module: AuditProductAssumptions.v
    Purpose: Audit the transitive logical axioms of the compiled product
    conditional-expectation targets. Run in a separate Rocq process to
    limit peak resource usage. Match the previously successful local
    Print Assumptions-only procedure; do not pretty-print the large
    dependent theorem signatures in this audit.
    Researcher/requester: Anders Hellström.
    AI disclosure: AI-assisted audit source; kernel output is the evidence.
    No declarations, axioms, or proof scripts are introduced.
*)
Require Import GaussianProductConditionalExpectation.

(* Audit product_gaussian_innovation_independent. *)
Print Assumptions product_gaussian_innovation_independent.

(* Audit product_gaussian_regression_conditional_expectation. *)
Print Assumptions product_gaussian_regression_conditional_expectation.

(* Audit product_gaussian_conditional_mean_almost_sure. *)
Print Assumptions product_gaussian_conditional_mean_almost_sure.
