(** Module: GaussianProductConditionalExpectation.v
 Purpose: Construct the observed-history/residual product probability space
 and prove its actual (event-integral) conditional expectation, rather than
 taking independence from the history as an additional premise.
 Mathematical representation: History is the measurable carrier of all
 observed scores, and a second real-valued factor is an innovation.
 Their product measure is constructed with IBM FormalML ProductSpace.
 The future-score process is the observed-history regression function
 c*sum(X_i)/d_n(c) plus the second coordinate. This covers any n with
 an observed-history measurable score-sum and positive denominator.
 Explicit hypotheses: The two factor probability spaces and their
 existing sigma-algebras; measurable history sum; integrable predictor
 and innovation; zero innovation expectation. The product probability
 measure supplies *independence* as a proved lemma, not as a parameter.
 Joint Gaussianity, the marginal equicorrelated history law and Gaussian
 first/second moments are NOT proved here, and require a separate
 distributional construction before this specializes to every jointly
 Gaussian covariance model, including signed-correlation endpoints.
 Library reuse: IBM FormalML ProductSpace.product_ps,
 ProductSpace.product_independent_sas,
 ProductSpace.independent_sas_comm, RandomVariable.pullback_compose_rv,
 and GaussianResidualConditionalExpectation's generic independence-to-CE
 theorem, which itself reuses the FormalML conditional-expectation API.
 Verification: The dedicated pinned Rocq 9.2 FormalML GitHub workflow.
 AI disclosure: OpenAI ChatGPT assisted the specification, comments and
 proof source for researcher/requester Anders Hellström. Count as proved
 only after the exact-source Rocq kernel workflow succeeds.
*)
From Stdlib Require Import Reals Lia Lra.
(* Import the extended-real constructor Finite explicitly. *)
From Coquelicot Require Import Rbar.
From FormalML.ProbTheory Require Import
  ConditionalExpectation Independence ProductSpace
  RandomVariable RealRandomVariable Expectation SigmaAlgebras.
From FormalML.utils Require Import Utils.
Require Import GaussianResidualConditionalExpectation.
Open Scope R_scope.

Section ProductGaussianRegression.
  Context {History : Type}.
  Context {history_sa : SigmaAlgebra History}.
  Context (history_probability : ProbSpace history_sa).
  Context (innovation_probability : ProbSpace borel_sa).
  Context (n : nat) (c : R).
  Context (history_sum : History -> R).
  Context {history_sum_rv : RandomVariable history_sa borel_sa history_sum}.

  Let full_sa : SigmaAlgebra (History * R) :=
    product_sa history_sa borel_sa.
  Let full_probability : ProbSpace full_sa :=
    product_ps history_probability innovation_probability.
  Let observed_sa : SigmaAlgebra (History * R) :=
    pullback_sa history_sa (@fst History R).
  Let observed_sub : sa_sub observed_sa full_sa :=
    pullback_rv_sub full_sa history_sa (@fst History R)
                    (fst_rv history_sa borel_sa).

  (** [product_gaussian_predictor] (definition).
   The exact report coefficient c/d_n(c) times the complete observed
   score sum. It is a *candidate* regression function until the relevant
   Gaussian covariance construction connects it to actual observations.
   No new prediction or covariance algebra is implemented here.
  *)
  Definition product_gaussian_predictor (w : History * R) : R :=
    (c / (1 + (INR n - 1) * c)) * history_sum (fst w).

  (** [product_gaussian_innovation] (definition).
   The centered second product coordinate; it is independent from all
   observed events because the product measure is independently built.
  *)
  Definition product_gaussian_innovation (w : History * R) : R :=
    snd w.

  Local Instance product_predictor_observed_rv :
    RandomVariable observed_sa borel_sa product_gaussian_predictor.
  Proof.
    unfold product_gaussian_predictor.
    apply rvscale_rv.
    apply pullback_compose_rv.
    exact history_sum_rv.
  Qed.

  Local Instance product_predictor_full_rv :
    RandomVariable full_sa borel_sa product_gaussian_predictor.
  Proof.
    (* Reuse sigma-algebra inclusion without a redundant probability argument. *)
    eapply RandomVariable_sa_sub.
    - exact observed_sub.
    - exact product_predictor_observed_rv.
  Qed.

  Local Instance product_innovation_full_rv :
    RandomVariable full_sa borel_sa product_gaussian_innovation.
  Proof.
    unfold product_gaussian_innovation.
    exact (snd_rv history_sa borel_sa).
  Qed.

  (** [product_gaussian_innovation_independent] (lemma).
   This is the crucial measure-theoretic independence assertion for
   the explicitly constructed product model. It is DERIVED from the
   library's independent-projections theorem rather than assumed via
   an extra Gaussian residual-independence hypothesis.
   This lemma does not assert that arbitrary jointly Gaussian vectors
   have an independent regression residual; proving their product
   representation is still required.
  *)
  Lemma product_gaussian_innovation_independent :
    independent_sas full_probability
      (pullback_rv_sub full_sa borel_sa
         product_gaussian_innovation product_innovation_full_rv)
      observed_sub.
  Proof.
    unfold product_gaussian_innovation.
    apply (proj1 (independent_sas_comm observed_sub
               (pullback_rv_sub full_sa borel_sa (@snd History R)
                    (snd_rv history_sa borel_sa)))).
    exact (product_independent_sas
             history_probability innovation_probability).
  Qed.

  Context {predictor_integrable :
    IsFiniteExpectation full_probability product_gaussian_predictor}.
  Context {innovation_integrable :
    IsFiniteExpectation full_probability product_gaussian_innovation}.

  (** [product_gaussian_regression_conditional_expectation] (theorem).
   Meaning: In the actual product probability space carrying the whole
   observed history and a centered independent residual, the adapted
   Gaussian regression candidate is the conditional expectation of
   the future score obtained by adding that residual.
   Exact proposition: for every event in the sigma-algebra generated
   by the observed first coordinate, the integral of the future score
   over that event equals the integral of
   c*history_sum/d_n(c). This is FormalML's universal
   is_conditional_expectation predicate, not covariance orthogonality.
   Hypotheses: n >= 1 and positive denominator; measurable full history
   sum; finite predictor/residual first moments; zero residual mean.
   Independence follows from the product-space construction and
   FormalML's product_independent_sas theorem.
   Limitation: This is a constructive independent-residual Gaussian
   regression representation. It does not yet prove that every
   jointly Gaussian vector with a given equicorrelation covariance
   has this representation, nor normality of its chosen factors.
   Source: FormalML's conditional-expectation library and this module.
  *)
  Theorem product_gaussian_regression_conditional_expectation
    (n_positive : (1 <= n)%nat)
    (observed_invertible : 0 < 1 + (INR n - 1) * c)
    (innovation_centered :
       FiniteExpectation full_probability product_gaussian_innovation = 0) :
    is_conditional_expectation full_probability observed_sa
      (rvplus product_gaussian_predictor product_gaussian_innovation)
      (fun w => Finite (product_gaussian_predictor w)).
  Proof.
    apply gaussian_regression_conditional_expectation_centered.
    - apply product_gaussian_innovation_independent.
    - exact innovation_centered.
  Qed.

  (** Integrability of the future score is established centrally:
   [gaussian_regression_future_integrable] in the residual module
   reuses FormalML's [IsFiniteExpectation_plus] lemma, avoiding an
   identical instance here. The independent product probability
   space supplies the stronger regression premise instead.
  *)

  (** [product_gaussian_conditional_mean_almost_sure] (theorem).
   This supplies the report's characteristic almost-sure form of the
   conditional-expectation identity, in the *constructed* product
   independent-innovation model with coefficient c/d_n(c).
   FormalML's actual ConditionalExpectation exists in L1, and its
   uniqueness theorem identifies it with the adapted linear predictor
   almost surely under the observed-history probability subspace.
   We reuse the previously proved universal event-integral CE property.
   There is no explicit CE hypothesis, independence parameter,
   disintegration axiom, or custom Gaussian integration.
   The remaining mathematical obligation for an *arbitrary* jointly
   Gaussian equicorrelated vector is to kernel-prove that its regression
   residual is equivalent to such an independent product coordinate.
  *)
  Theorem product_gaussian_conditional_mean_almost_sure
    (n_positive : (1 <= n)%nat)
    (observed_invertible : 0 < 1 + (INR n - 1) * c)
    (innovation_centered :
       FiniteExpectation full_probability product_gaussian_innovation = 0) :
    almostR2 (prob_space_sa_sub full_probability observed_sub) eq
      (ConditionalExpectation full_probability observed_sub
         (rvplus product_gaussian_predictor product_gaussian_innovation))
      (fun w => Finite (product_gaussian_predictor w)).
  Proof.
    apply gaussian_regression_conditional_mean_almost_sure.
    - apply product_gaussian_innovation_independent.
    - exact innovation_centered.
  Qed.
End ProductGaussianRegression.
