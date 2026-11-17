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
From FormalML.ProbTheory Require Import
  ConditionalExpectation Independence RealRandomVariable RandomVariable
  Expectation SigmaAlgebras.
From FormalML Require Import Utils.

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
  - apply (is_conditional_expectation_id prob obs_sub predictor).
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

End GaussianLinearConditionalExpectation.
