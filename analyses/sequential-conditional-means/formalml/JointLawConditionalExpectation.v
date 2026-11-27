(** Module: JointLawConditionalExpectation.v
    Purpose: Transport the already verified independent-innovation
    conditional-expectation results to random variables on their original
    probability space, using equality of their joint law with the
    product of their marginal laws. The observed sigma algebra is
    precisely the pullback of the history's measurable structure.
    This result works with singular or atomic laws as well as densities.
    Gaussian factorization, centering and moment computations are separate
    obligations; no covariance-to-independence axiom is introduced.
    Researcher/requester: Anders Hellström.
    AI disclosure: AI-assisted source; compilation and audit pending.
*)
From Stdlib Require Import Reals.
From Coquelicot Require Import Rbar.
From FormalML.ProbTheory Require Import
  ConditionalExpectation Independence ProductSpace RandomVariable
  RealRandomVariable Expectation SigmaAlgebras ProbSpace.
From FormalML.utils Require Import Utils.
Require Import ProductLawIndependence GaussianResidualConditionalExpectation.
Open Scope R_scope.

Section JointLawRegression.
  Context {Omega History : Type}.
  Context {dom : SigmaAlgebra Omega}.
  Context (prob : ProbSpace dom).
  Context {history_sa : SigmaAlgebra History}.
  Context (history : Omega -> History).
  Context {history_rv : RandomVariable dom history_sa history}.
  Context (predictor innovation : Omega -> R).
  Context {innovation_rv : RandomVariable dom borel_sa innovation}.

  (* Observe the entire history rather than only the predictor. *)
  Let observed := pullback_sa history_sa history.
  (* Reuse exactly the library's measurability inclusion witness. *)
  Let observed_sub : sa_sub observed dom :=
    pullback_rv_sub dom history_sa history history_rv.

  (** Joint-law factorization is equivalent to independence of the
      residual-generated sigma algebra from the full observed history.
      This is stronger than independence from the scalar predictor.
      The law is written innovation first to align the inclusion
      certificates with FormalML's independent_rv_sas theorem. *)
  Theorem joint_law_iff_innovation_independent_of_history :
    ps_equiv
      (product_ps (pullback_ps _ _ prob innovation)
                  (pullback_ps _ _ prob history))
      (pullback_ps _ _ prob (fun w => (innovation w, history w))) <->
    independent_sas prob
      (pullback_rv_sub dom borel_sa innovation innovation_rv)
      observed_sub.
  Proof.
    (* Both equivalences are library-backed and preserve the exact
       random-variable certificates in the dependent event types. *)
    rewrite <- (@independent_rv_sas Omega dom prob R borel_sa
                 History history_sa innovation history innovation_rv history_rv).
    symmetry.
    exact (@independent_rvs_iff_product_joint_law Omega R History dom
             prob borel_sa history_sa innovation history innovation_rv history_rv).
  Qed.

  Context {predictor_rv_obs : RandomVariable observed borel_sa predictor}.
  Context {predictor_rv_full : RandomVariable dom borel_sa predictor}.
  Context {predictor_integrable : IsFiniteExpectation prob predictor}.
  Context {innovation_integrable : IsFiniteExpectation prob innovation}.

  (** Joint product-law factorization on the original space implies
      the universal conditional event-integral identity of a centered
      residual regression. The predictor is assumed measurable with
      respect to the observed history, and both summands integrable. *)
  Theorem joint_law_regression_conditional_expectation
    (Hlaw : ps_equiv
      (product_ps (pullback_ps _ _ prob innovation)
                  (pullback_ps _ _ prob history))
      (pullback_ps _ _ prob (fun w => (innovation w, history w))))
    (Hcenter : FiniteExpectation prob innovation = 0) :
    is_conditional_expectation prob observed
      (rvplus predictor innovation) (fun w => Finite (predictor w)).
  Proof.
    exact (@gaussian_regression_conditional_expectation_centered
      Omega dom prob observed observed_sub predictor innovation
      predictor_rv_obs predictor_rv_full innovation_rv
      predictor_integrable innovation_integrable
      (proj1 joint_law_iff_innovation_independent_of_history Hlaw)
      Hcenter).
  Qed.

  (** The canonical library conditional expectation equals the
      adapted predictor almost surely under the observed probability
      subspace. Reuse the existing existence/uniqueness proof. *)
  Theorem joint_law_regression_conditional_mean_almost_sure
    (Hlaw : ps_equiv
      (product_ps (pullback_ps _ _ prob innovation)
                  (pullback_ps _ _ prob history))
      (pullback_ps _ _ prob (fun w => (innovation w, history w))))
    (Hcenter : FiniteExpectation prob innovation = 0) :
    almostR2 (prob_space_sa_sub prob observed_sub) eq
      (ConditionalExpectation prob observed_sub (rvplus predictor innovation))
      (fun w => Finite (predictor w)).
  Proof.
    exact (@gaussian_regression_conditional_mean_almost_sure
      Omega dom prob observed observed_sub predictor innovation
      predictor_rv_obs predictor_rv_full innovation_rv
      predictor_integrable innovation_integrable
      (proj1 joint_law_iff_innovation_independent_of_history Hlaw)
      Hcenter).
  Qed.
End JointLawRegression.
