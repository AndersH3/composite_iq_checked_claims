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
  Let observed : SigmaAlgebra Omega := pullback_sa history_sa history.
  (* Reuse exactly the library's measurability inclusion witness. *)
  Let observed_sub : sa_sub observed dom :=
    pullback_rv_sub dom history_sa history history_rv.

  (** Fix the carrier, sigma algebras and the exact existing
      measurability certificates before forming any pushforward law.
      With a real-valued component, unconstrained typeclass search for
      the pair can recurse through the real-random-variable instances.
      Use the same library product certificate as ProductLawIndependence,
      with no additional mathematical hypothesis. *)
  Let innovation_law : ProbSpace borel_sa :=
    @pullback_ps Omega R dom borel_sa prob innovation innovation_rv.
  Let history_law : ProbSpace history_sa :=
    @pullback_ps Omega History dom history_sa prob history history_rv.
  Let joint_sa : SigmaAlgebra (R * History) :=
    product_sa borel_sa history_sa.
  Let joint_rv :
    RandomVariable dom joint_sa (fun w => (innovation w, history w)) :=
    @product_sa_rv Omega R History dom borel_sa history_sa
      innovation history innovation_rv history_rv.
  Let joint_law : ProbSpace joint_sa :=
    @pullback_ps Omega (R * History)%type dom joint_sa prob
      (fun w => (innovation w, history w)) joint_rv.
  Let marginal_product_law : ProbSpace joint_sa :=
    @product_ps R History borel_sa history_sa innovation_law history_law.

  (** Name the common factorization proposition once, rather than
      elaborating three independent copies with unresolved instances.
      The transparent local abbreviation retains equality of measures
      on every measurable event, not merely a covariance condition. *)
  Let joint_factorization : Prop :=
    @ps_equiv (R * History)%type joint_sa marginal_product_law joint_law.

  (** Joint-law factorization is equivalent to independence of the
      residual-generated sigma algebra from the full observed history.
      This is stronger than independence from the scalar predictor.
      The law is written innovation first to align the inclusion
      certificates with FormalML's independent_rv_sas theorem. *)
  Theorem joint_law_iff_innovation_independent_of_history :
    joint_factorization <->
    independent_sas prob
      (pullback_rv_sub dom borel_sa innovation innovation_rv)
      observed_sub.
  Proof.
    (* Both equivalences are library-backed and preserve the exact
       random-variable certificates in the dependent event types. *)
    pose proof (@independent_rv_sas Omega dom prob R borel_sa
                  History history_sa innovation history innovation_rv history_rv)
      as Hsigma.
    pose proof (@independent_rvs_iff_product_joint_law Omega R History dom
                  prob borel_sa history_sa innovation history innovation_rv history_rv)
      as Hproduct.
    (* Compose the implications directly; do not rewrite a dependent
       probability-space expression or launch fresh typeclass search. *)
    split; intro H.
    - exact (proj1 Hsigma (proj2 Hproduct H)).
    - exact (proj1 Hproduct (proj2 Hsigma H)).
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
    (Hlaw : joint_factorization)
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
    (Hlaw : joint_factorization)
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
