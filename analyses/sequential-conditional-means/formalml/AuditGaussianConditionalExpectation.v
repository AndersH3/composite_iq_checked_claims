(** Module: AuditGaussianConditionalExpectation.v
    Purpose: Reproduce the complete transitive logical-assumption audit of
    the nine residual and independent-product conditional-expectation
    targets, using the compiled project modules and pinned FormalML.
    Each Check prints the exact theorem signature, immediately followed by
    its Print Assumptions output so that premises and logical axioms are
    distinguishable. No declarations, new axioms or proof scripts are added.
    Researcher/requester: Anders Hellström.
    AI disclosure: AI-assisted audit source; the Rocq output is the evidence.
*)
Require Import GaussianResidualConditionalExpectation.
Require Import GaussianProductConditionalExpectation.

(* Audit gaussian_regression_conditional_expectation_with_residual_mean: retain the exact statement and its axiom closure. *)
Check gaussian_regression_conditional_expectation_with_residual_mean.
Print Assumptions gaussian_regression_conditional_expectation_with_residual_mean.

(* Audit gaussian_regression_conditional_expectation_centered: retain the exact statement and its axiom closure. *)
Check gaussian_regression_conditional_expectation_centered.
Print Assumptions gaussian_regression_conditional_expectation_centered.

(* Audit gaussian_regression_perfect_information_conditional_expectation: retain the exact statement and its axiom closure. *)
Check gaussian_regression_perfect_information_conditional_expectation.
Print Assumptions gaussian_regression_perfect_information_conditional_expectation.

(* Audit gaussian_regression_perfect_information_mean_almost_sure: retain the exact statement and its axiom closure. *)
Check gaussian_regression_perfect_information_mean_almost_sure.
Print Assumptions gaussian_regression_perfect_information_mean_almost_sure.

(* Audit gaussian_regression_conditional_mean_almost_sure: retain the exact statement and its axiom closure. *)
Check gaussian_regression_conditional_mean_almost_sure.
Print Assumptions gaussian_regression_conditional_mean_almost_sure.

(* Audit gaussian_regression_transfer_to_future: retain the exact statement and its axiom closure. *)
Check gaussian_regression_transfer_to_future.
Print Assumptions gaussian_regression_transfer_to_future.

(* Audit product_gaussian_innovation_independent: retain the exact statement and its axiom closure. *)
Check product_gaussian_innovation_independent.
Print Assumptions product_gaussian_innovation_independent.

(* Audit product_gaussian_regression_conditional_expectation: retain the exact statement and its axiom closure. *)
Check product_gaussian_regression_conditional_expectation.
Print Assumptions product_gaussian_regression_conditional_expectation.

(* Audit product_gaussian_conditional_mean_almost_sure: retain the exact statement and its axiom closure. *)
Check product_gaussian_conditional_mean_almost_sure.
Print Assumptions product_gaussian_conditional_mean_almost_sure.
