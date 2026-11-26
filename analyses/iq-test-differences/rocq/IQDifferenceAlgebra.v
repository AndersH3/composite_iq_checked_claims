(* Algebraic foundations for IQ discrepancy propositions.
   Anders Hellström, requester. This module does not formalize Gaussian
   integration, random variables or conditional expectations. *)
From Stdlib Require Import Reals Lra Ring Field.
Open Scope R_scope.

(* Expand the covariance-based variance of a two-score contrast. *)
Theorem iq_gap_variance (sigma rho : R) :
  sigma * sigma + sigma * sigma - 2 * (sigma * sigma * rho)
  = 2 * sigma^2 * (1-rho).
Proof. ring. Qed.

(* The variance factor is nonnegative throughout the correlation domain. *)
Theorem iq_gap_variance_nonnegative (sigma rho : R) :
  rho <= 1 -> 0 <= 2 * sigma^2 * (1-rho).
Proof. intros H. apply Rmult_le_pos; [nra | lra]. Qed.

(* Average correlation in the three-plus-two duplicated Gaussian example. *)
Theorem iq_block_average : (4 + 6 * (1/3)) / 10 = 3/5.
Proof. field. Qed.

(* Equal-weight mixture correlations preserve the target average. *)
Theorem iq_smooth_mixture_average : (3/10 + 9/10)/2 = 3/5.
Proof. field. Qed.

(* For the example with first score 145, the regression contrast is 18. *)
Theorem iq_conditional_example : (1-3/5)*(145-100)=18.
Proof. field. Qed.

(* Conditional Gaussian residual variance in square IQ points. *)
Theorem iq_conditional_variance_example : 15^2*(1-(3/5)^2)=12^2.
Proof. field. Qed.

(* Shift invariance of a difference, used after cancelling the common factor. *)
Theorem iq_common_shift (a x y : R) : (a+x)-(a+y)=x-y.
Proof. ring. Qed.

(* Scaling of a difference by a shared positive or negative scale. *)
Theorem iq_scaled_gap (s x y : R) : s*x-s*y=s*(x-y).
Proof. ring. Qed.

(* Covariance-domain eigenvalue factor for an arbitrary real dimension parameter. *)
Theorem iq_equicorrelation_domain (k rho : R) :
  2 <= k -> -1 <= (k-1)*rho -> rho <= 1 ->
  0 <= 1+(k-1)*rho /\ 0 <= 1-rho.
Proof. intros Hk Hlow Hhigh. split; lra. Qed.

(* Mixture correlation in the shared/independent example. *)
Theorem iq_shared_mixture_average : (3/5)*1+(2/5)*0=3/5.
Proof. ring. Qed.
