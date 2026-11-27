(** Module: GaussianResidualConditionalExpectation.v
 Purpose: Verify the defining measure-theoretic conditional expectation
 property of the Gaussian residual regression construction using the
 established IBM FormalML probability library.
 Mathematical representation: Future score Y is an observed-history
 measurable linear predictor p plus a centered integrable innovation e.
 If the innovation's generated sigma algebra is independent of the
 entire observed-history sigma algebra, then E[Y|G]=p.
 Explicit hypotheses: Genuine probability space, two sigma algebras
 with an inclusion morphism, measurable integrable predictor and
 residual, and independence of the residual from the history. This
 module does not silently infer independence from zero covariance:
 that separate Gaussian-to-independence implication must be proved
 using a joint multivariate normal distribution construction.
 Library use: FormalML ConditionalExpectation is_conditional_expectation_id,
 is_conditional_expectation_independent_sa,
 is_conditional_expectation_plus and is_conditional_expectation_proper.
 No custom conditional expectation integral, random variable, or axiom.
 Limitations: The theorem is a measure-theoretic conditional expectation
 for an independently centered Gaussian-regression innovation model,
 conditional on independence/integrability; no joint Gaussian
 distribution is constructed in this module. No assumption directly
 postulates the desired conditional-expectation conclusion.
 Reproduction: dedicated FormalML CI with pinned Rocq 9.2 and FormalML.
 AI disclosure: AI-assisted theorem and proof; only kernel acceptance
 establishes formal verification.
*)
From Stdlib Require Import Reals Lra.
(* Import the extended-real constructor Finite explicitly. *)
From Coquelicot Require Import Rbar.
From FormalML.ProbTheory Require Import
  ConditionalExpectation Independence RealRandomVariable RandomVariable
  Expectation SigmaAlgebras.
From FormalML.utils Require Import Utils.

Open Scope R_scope.

Section GaussianLinearConditionalExpectation.
Context {Omega : Type} {dom : SigmaAlgebra Omega}.
Context (prob : ProbSpace dom).
Context {observed : SigmaAlgebra Omega}.
Context (obs_sub : sa_sub observed dom).
Context (predictor innovation : Omega -> R).
Context {predictor_rv_obs : RandomVariable observed borel_sa predictor}.
Context {predictor_rv_full : RandomVariable dom borel_sa predictor}.
Context {innovation_rv : RandomVariable dom borel_sa innovation}.
Context {prediction_integrable : IsFiniteExpectation prob predictor}.
Context {innovation_integrable : IsFiniteExpectation prob innovation}.

(** [gaussian_regression_conditional_expectation_with_residual_mean].
 Mathematical meaning: The conditional expectation of a future score
 given its observed-history sigma algebra equals the adapted predictor
 plus the unconditional mean of its independent innovation.
 Exact checked proposition: is_conditional_expectation observed
 (rvplus predictor innovation)
 (Rbar_rvplus (Finite o predictor)
             (const (FiniteExpectation prob innovation))).
 Premises and side conditions: Genuine probability space, measurable
 predictor adapted to observed, finite first moments, and independence
 of the residual-generated sigma algebra from observed. Independence
 is required as a theorem input, not inferred from covariance.
 Proof/definition method: Reuse FormalML's CE identity for an adapted
 random variable, CE independence theorem and CE linearity.
 Library reuse: is_conditional_expectation_id,
 is_conditional_expectation_independent_sa,
 is_conditional_expectation_plus, existing random-variable morphisms.
 Boundary: Full measure-theoretic universal conditional-expectation
 identity conditional on residual independence; Gaussianity alone has
 not yet been kernel-proved to imply that independence in this module.
*)
Theorem gaussian_regression_conditional_expectation_with_residual_mean
  (innovation_independent :
    independent_sas prob
      (pullback_rv_sub _ _ _ innovation_rv) obs_sub) :
  is_conditional_expectation prob observed
    (rvplus predictor innovation)
    (Rbar_rvplus (fun w => Finite (predictor w))
                  (const (FiniteExpectation prob innovation))).
Proof.
  apply (is_conditional_expectation_plus prob obs_sub predictor innovation
           (fun w => Finite (predictor w))
           (const (FiniteExpectation prob innovation))).
  - apply is_conditional_expectation_id.
  - apply (is_conditional_expectation_independent_sa
             prob obs_sub innovation); exact innovation_independent.
Qed.

(** [gaussian_regression_conditional_expectation_centered].
 Mathematical meaning: With centered independent innovation, a future
 score's conditional expectation on all observed information is its
 adapted predictor, not merely its unconditional least-squares fit.
 Exact checked proposition: is_conditional_expectation observed
 (rvplus predictor innovation) (fun w => Finite(predictor w)).
 Premises and side conditions: All measurable and integrable conditions
 above, residual independence from observed and exact residual mean zero.
 In a jointly Gaussian model, the linear covariance inversion supplies
 a candidate residual; proving that Gaussianity gives its independence
 is a logically separate explicit obligation.
 Proof/definition method: Derive from the real measure-theoretic
 independent-innovation CE theorem; rewrite the finite Rbar constant
 using the residual's proven zero mean and FormalML CE congruence.
 Library reuse: FormalML is_conditional_expectation_proper,
 is_conditional_expectation_plus, all_almost, Rbar_rvplus, and
 existing real-random-variable finite-lift definitions.
 Boundary: A conditional-expectation result under independence,
 not an assumed conditional-expectation law nor a joint Gaussian
 realization for arbitrary negative exchangeable correlation.
*)
Theorem gaussian_regression_conditional_expectation_centered
  (innovation_independent :
    independent_sas prob
      (pullback_rv_sub _ _ _ innovation_rv) obs_sub)
  (innovation_centered :
    FiniteExpectation prob innovation = 0) :
  is_conditional_expectation prob observed
    (rvplus predictor innovation)
    (fun w => Finite (predictor w)).
Proof.
  pose proof
    (gaussian_regression_conditional_expectation_with_residual_mean
       innovation_independent) as Hregression.
  apply
    (is_conditional_expectation_proper
       prob obs_sub
       (rvplus predictor innovation)
       (rvplus predictor innovation)
       (Rbar_rvplus (fun w => Finite (predictor w))
                     (const (FiniteExpectation prob innovation)))
       (fun w => Finite (predictor w))).
  - apply all_almost; intro w; reflexivity.
  - apply all_almost; intro w.
    unfold Rbar_rvplus, const; rewrite innovation_centered.
    simpl; rewrite Rplus_0_r; reflexivity.
  - exact Hregression.
Qed.


(** [gaussian_regression_future_integrable] (local instance).
 The sum of an observed-history predictor and an independent innovation
 has a finite first moment whenever each summand has one. Independence
 is not required for this integrability conclusion.
 This avoids duplicating the positive/negative-part construction:
 the instance is obtained directly from FormalML's
 [IsFiniteExpectation_plus] theorem.
*)
Local Instance gaussian_regression_future_integrable :
  IsFiniteExpectation prob (rvplus predictor innovation).
Proof.
  apply IsFiniteExpectation_plus; typeclasses eauto.
Qed.


(** [gaussian_regression_perfect_information_conditional_expectation].
 Mathematical meaning: When the future score is almost surely equal to an
 observed-measurable predictor, its event-integral conditional expectation
 is that predictor, even if the innovation is not assumed independent.
 Exact checked proposition: is_conditional_expectation on the entire
 observed sigma-algebra for the future score [predictor + innovation].
 Premises: a genuine probability space, adapted/integrable predictor,
 integrable future score (established above from component integrability),
 and almost-sure equality of the future score and predictor. This is
 suitable for the perfectly correlated singular boundary only after
 that almost-sure equality has been derived from the actual Gaussian law.
 Proof method: [is_conditional_expectation_id] for an adapted predictor,
 followed by [is_conditional_expectation_proper] under almost-sure equality.
 Library reuse: FormalML ConditionalExpectation and Almost.
 Boundary: Does not infer almost-sure equality from a zero covariance
 or fabricate independence; the joint-Gaussian support theorem is separate.
*)
Theorem gaussian_regression_perfect_information_conditional_expectation
  (future_predictor_ae :
    almostR2 prob eq (rvplus predictor innovation) predictor) :
  is_conditional_expectation prob observed
    (rvplus predictor innovation)
    (fun w => Finite (predictor w)).
Proof.
  apply
    (is_conditional_expectation_proper
       prob obs_sub
       predictor (rvplus predictor innovation)
       (fun w => Finite (predictor w))
       (fun w => Finite (predictor w))).
  (* Transfer the CE of the adapted predictor TO the future variable;
     the upstream congruence theorem takes source before destination. *)
  - symmetry; exact future_predictor_ae.
  - apply all_almost; intro w; reflexivity.
  - apply is_conditional_expectation_id.
Qed.

(** [gaussian_regression_perfect_information_mean_almost_sure].
 Mathematical meaning: The library's canonical conditional-expectation
 random variable equals the predictor almost surely in the perfect
 observation case, without a residual-independence hypothesis.
 Exact checked proposition: almostR2 equality on the observed probability
 subspace between FormalML's ConditionalExpectation and the predictor.
 Premises: identical measurable/integrable context and almost-sure
 equality of future score with the observed-history predictor.
 Proof method: Apply FormalML [Condexp_cond_exp] for existence and
 [is_conditional_expectation_unique] for uniqueness; reuse the event
 identity above, rather than rebuilding the integral.
 Boundary: No claim of a universal jointly Gaussian law, distributional
 factorization, or covariance-pseudoinverse identification is made here.
*)
Theorem gaussian_regression_perfect_information_mean_almost_sure
  (future_predictor_ae :
    almostR2 prob eq (rvplus predictor innovation) predictor) :
  almostR2 (prob_space_sa_sub prob obs_sub) eq
    (ConditionalExpectation prob obs_sub
       (rvplus predictor innovation))
    (fun w => Finite (predictor w)).
Proof.
  eapply is_conditional_expectation_unique.
  - apply Condexp_cond_exp.
  - apply gaussian_regression_perfect_information_conditional_expectation.
    exact future_predictor_ae.
Qed.

(** [gaussian_regression_conditional_mean_almost_sure] (theorem).
 Mathematical content: The *library-defined* conditional expectation,
 rather than just a candidate satisfying its event-integral identity,
 is almost surely equal to the adapted predictor when its residual
 is centered, integrable, and independent of the observed sigma algebra.
 The hypotheses assert true sigma-algebra independence, not merely
 vanishing cross-covariance or Gaussian-sounding terminology.
 Proof: Combine the event-integral theorem proved above with FormalML's
 existence theorem [Condexp_cond_exp] and the library's almost-sure
 uniqueness theorem [is_conditional_expectation_unique].
 This is a full measure-theoretic identity under an explicit independent
 residual hypothesis. The separate derivation of this hypothesis for
 arbitrary jointly Gaussian vectors (including singular covariance
 matrices) remains open and is not concealed in this declaration.
*)
Theorem gaussian_regression_conditional_mean_almost_sure
  (innovation_independent :
    independent_sas prob
      (pullback_rv_sub _ _ _ innovation_rv) obs_sub)
  (innovation_centered :
    FiniteExpectation prob innovation = 0) :
  almostR2 (prob_space_sa_sub prob obs_sub) eq
    (ConditionalExpectation prob obs_sub
      (rvplus predictor innovation))
    (fun w => Finite (predictor w)).
Proof.
  eapply is_conditional_expectation_unique.
  - apply Condexp_cond_exp.
  - apply gaussian_regression_conditional_expectation_centered; assumption.
Qed.

(** [gaussian_regression_transfer_to_future] (theorem).
 Mathematical meaning: Transfer the conditional expectation of an
 adapted predictor plus centered independent innovation to an actual
 measured future-score random variable agreeing almost surely with it.
 Exact representation: Event-integral CE of future equals predictor.
 Premises and side conditions: Measurable future, integrable summands,
 residual independence, zero mean and almost-sure decomposition.
 Proof/definition method: Reuse the centered regression identity and
 the library's almost-sure congruence theorem.
 Library reuse: FormalML is_conditional_expectation_proper, all_almost.
 Boundary: Residual independence remains a hypothesis, not a consequence
 inferred from zero covariance.
*)
Theorem gaussian_regression_transfer_to_future
  (future : Omega -> R)
  {future_rv : RandomVariable dom borel_sa future}
  (future_decomposition :
     almostR2 prob eq (rvplus predictor innovation) future)
  (innovation_independent :
    independent_sas prob
      (pullback_rv_sub _ _ _ innovation_rv) obs_sub)
  (innovation_centered : FiniteExpectation prob innovation = 0) :
  is_conditional_expectation prob observed future
    (fun w => Finite (predictor w)).
Proof.
  eapply is_conditional_expectation_proper.
  - exact future_decomposition.
  - apply all_almost; intro w; reflexivity.
  - apply gaussian_regression_conditional_expectation_centered;
      assumption.
Qed.

End GaussianLinearConditionalExpectation.
