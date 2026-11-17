(** Module: GaussianConditionalKernel.v
 Purpose: Prove exact Gaussian likelihood square completion for an arbitrary,
 unequal finite history of scores and the equicorrelated common-factor model.
 Mathematical representation: A latent centered normal signal theta with
 prior variance c and n noisy scores with idiosyncratic variance 1-c
 yields a joint Gaussian likelihood exp(-Q/2). The resulting conditional
 kernel is identified pointwise by completing its quadratic exponent.
 Explicit hypotheses: The statistically meaningful signal/noise model uses
 a nonempty history, 0<c<1, and d_n(c)>0. Division and positivity
 hypotheses are explicit; algebraic identities use only nonzero denominators.
 Library use: Reuse the canonical FiniteSum, EquicorrelationVectors and
 SequentialReport formulas; use Rocq Stdlib Reals, Ring, Field and Psatz
 for exact algebra, exp laws for factorization, and no hand-built sum fold.
 Limitations: Pointwise Gaussian density factorization plus a unique center
 is NOT by itself the measure-theoretic normalizing-integral theorem nor a
 proof of regular conditional expectation. The independent Gaussian prior
 and score noise laws are specified by the model but not constructed here.
 The separate mathematical probability bridge must use a proven normal
 measure / conditional-expectation theorem rather than assume that result.
 Reproduction: scripts/compile_rocq.sh under the pinned Rocq 9.2 workflow.
 AI disclosure: AI assisted proof design, source, documentation and review;
 only kernel-accepted propositions may be called checked.
*)
From Stdlib Require Import Reals Lra Psatz Ring Field List.
Require Import FiniteSum SequentialReport EquicorrelationVectors
  UnequalHistoryLinearPrediction.
Import ListNotations.
Open Scope R_scope.

(** [gk_mass] (definition).
 Mathematical meaning: The actual count of observed standardized test scores.
 Exact definition: gk_mass(xs:list R) : R := INR (length xs).
 Premises and side conditions: For a probabilistic Gaussian interpretation,
 score observations have a latent independent-normal residual model and
 0<c<1; algebraic proofs state the necessary nonzero divisions explicitly.
 Proof/definition method: Direct real algebra, explicit completion of a
 positive Gaussian quadratic, or a previously verified finite-list identity.
 Library reuse: Rocq Stdlib Reals/Field/Ring/Psatz and canonical
 FiniteSum/EquicorrelationVectors/SequentialReport definitions; no
 new bespoke summation implementation, probability axiom or floating point.
 Boundary: An exact deterministic Gaussian density/precision relation,
 not an independent proof of measure normalization or conditional expectation.
*)
Definition gk_mass (xs:list R) : R := INR (length xs).

(** [gk_sum] (definition).
 Mathematical meaning: The actual sum of arbitrary observed standardized test scores.
 Exact definition: gk_sum(xs:list R) : R := vector_real_sum xs.
 Premises and side conditions: For a probabilistic Gaussian interpretation,
 score observations have a latent independent-normal residual model and
 0<c<1; algebraic proofs state the necessary nonzero divisions explicitly.
 Proof/definition method: Direct real algebra, explicit completion of a
 positive Gaussian quadratic, or a previously verified finite-list identity.
 Library reuse: Rocq Stdlib Reals/Field/Ring/Psatz and canonical
 FiniteSum/EquicorrelationVectors/SequentialReport definitions; no
 new bespoke summation implementation, probability axiom or floating point.
 Boundary: An exact deterministic Gaussian density/precision relation,
 not an independent proof of measure normalization or conditional expectation.
*)
Definition gk_sum (xs:list R) : R := vector_real_sum xs.

(** [gk_d] (definition).
 Mathematical meaning: The canonical equicorrelation conditioning denominator at the observed count.
 Exact definition: gk_d(xs:list R) (c:R) : R := sequential_d (gk_mass xs) c.
 Premises and side conditions: For a probabilistic Gaussian interpretation,
 score observations have a latent independent-normal residual model and
 0<c<1; algebraic proofs state the necessary nonzero divisions explicitly.
 Proof/definition method: Direct real algebra, explicit completion of a
 positive Gaussian quadratic, or a previously verified finite-list identity.
 Library reuse: Rocq Stdlib Reals/Field/Ring/Psatz and canonical
 FiniteSum/EquicorrelationVectors/SequentialReport definitions; no
 new bespoke summation implementation, probability axiom or floating point.
 Boundary: An exact deterministic Gaussian density/precision relation,
 not an independent proof of measure normalization or conditional expectation.
*)
Definition gk_d (xs:list R) (c:R) : R := sequential_d (gk_mass xs) c.

(** [gk_precision] (definition).
 Mathematical meaning: The precision of the latent Gaussian signal posterior under conditionally independent noise.
 Exact definition: gk_precision(xs:list R) (c:R) : R := /c + gk_mass xs / (1-c).
 Premises and side conditions: For a probabilistic Gaussian interpretation,
 score observations have a latent independent-normal residual model and
 0<c<1; algebraic proofs state the necessary nonzero divisions explicitly.
 Proof/definition method: Direct real algebra, explicit completion of a
 positive Gaussian quadratic, or a previously verified finite-list identity.
 Library reuse: Rocq Stdlib Reals/Field/Ring/Psatz and canonical
 FiniteSum/EquicorrelationVectors/SequentialReport definitions; no
 new bespoke summation implementation, probability axiom or floating point.
 Boundary: An exact deterministic Gaussian density/precision relation,
 not an independent proof of measure normalization or conditional expectation.
*)
Definition gk_precision (xs:list R) (c:R) : R := /c + gk_mass xs / (1-c).

(** [gk_variance] (definition).
 Mathematical meaning: The proposed posterior latent variance for the common-factor Gaussian model.
 Exact definition: gk_variance(xs:list R) (c:R) : R := c*(1-c)/gk_d xs c.
 Premises and side conditions: For a probabilistic Gaussian interpretation,
 score observations have a latent independent-normal residual model and
 0<c<1; algebraic proofs state the necessary nonzero divisions explicitly.
 Proof/definition method: Direct real algebra, explicit completion of a
 positive Gaussian quadratic, or a previously verified finite-list identity.
 Library reuse: Rocq Stdlib Reals/Field/Ring/Psatz and canonical
 FiniteSum/EquicorrelationVectors/SequentialReport definitions; no
 new bespoke summation implementation, probability axiom or floating point.
 Boundary: An exact deterministic Gaussian density/precision relation,
 not an independent proof of measure normalization or conditional expectation.
*)
Definition gk_variance (xs:list R) (c:R) : R := c*(1-c)/gk_d xs c.

(** [gk_center] (definition).
 Mathematical meaning: The proposed posterior mean of the latent common factor given arbitrary unequal observed scores.
 Exact definition: gk_center(xs:list R) (c:R) : R := c*gk_sum xs/gk_d xs c.
 Premises and side conditions: For a probabilistic Gaussian interpretation,
 score observations have a latent independent-normal residual model and
 0<c<1; algebraic proofs state the necessary nonzero divisions explicitly.
 Proof/definition method: Direct real algebra, explicit completion of a
 positive Gaussian quadratic, or a previously verified finite-list identity.
 Library reuse: Rocq Stdlib Reals/Field/Ring/Psatz and canonical
 FiniteSum/EquicorrelationVectors/SequentialReport definitions; no
 new bespoke summation implementation, probability axiom or floating point.
 Boundary: An exact deterministic Gaussian density/precision relation,
 not an independent proof of measure normalization or conditional expectation.
*)
Definition gk_center (xs:list R) (c:R) : R := c*gk_sum xs/gk_d xs c.

(** [gk_residual_energy] (definition).
 Mathematical meaning: The data conditional squared-residual sum for a fixed latent signal.
 Exact definition: gk_residual_energy(xs:list R) (theta:R) : R := vector_center_energy xs theta.
 Premises and side conditions: For a probabilistic Gaussian interpretation,
 score observations have a latent independent-normal residual model and
 0<c<1; algebraic proofs state the necessary nonzero divisions explicitly.
 Proof/definition method: Direct real algebra, explicit completion of a
 positive Gaussian quadratic, or a previously verified finite-list identity.
 Library reuse: Rocq Stdlib Reals/Field/Ring/Psatz and canonical
 FiniteSum/EquicorrelationVectors/SequentialReport definitions; no
 new bespoke summation implementation, probability axiom or floating point.
 Boundary: An exact deterministic Gaussian density/precision relation,
 not an independent proof of measure normalization or conditional expectation.
*)
Definition gk_residual_energy (xs:list R) (theta:R) : R := vector_center_energy xs theta.

(** [gk_joint_quadratic] (definition).
 Mathematical meaning: The negative log Gaussian prior-plus-likelihood exponent multiplied by two.
 Exact definition: gk_joint_quadratic(xs:list R) (c theta:R) : R := theta*theta/c + gk_residual_energy xs theta/(1-c).
 Premises and side conditions: For a probabilistic Gaussian interpretation,
 score observations have a latent independent-normal residual model and
 0<c<1; algebraic proofs state the necessary nonzero divisions explicitly.
 Proof/definition method: Direct real algebra, explicit completion of a
 positive Gaussian quadratic, or a previously verified finite-list identity.
 Library reuse: Rocq Stdlib Reals/Field/Ring/Psatz and canonical
 FiniteSum/EquicorrelationVectors/SequentialReport definitions; no
 new bespoke summation implementation, probability axiom or floating point.
 Boundary: An exact deterministic Gaussian density/precision relation,
 not an independent proof of measure normalization or conditional expectation.
*)
Definition gk_joint_quadratic (xs:list R) (c theta:R) : R := theta*theta/c + gk_residual_energy xs theta/(1-c).

(** [gk_evidence_quadratic] (definition).
 Mathematical meaning: The data-only quadratic term left after analytically integrating out the linear normal parameter.
 Exact definition: gk_evidence_quadratic(xs:list R) (c:R) : R := (vector_square_energy xs - c*gk_sum xs*gk_sum xs/gk_d xs c)/(1-c).
 Premises and side conditions: For a probabilistic Gaussian interpretation,
 score observations have a latent independent-normal residual model and
 0<c<1; algebraic proofs state the necessary nonzero divisions explicitly.
 Proof/definition method: Direct real algebra, explicit completion of a
 positive Gaussian quadratic, or a previously verified finite-list identity.
 Library reuse: Rocq Stdlib Reals/Field/Ring/Psatz and canonical
 FiniteSum/EquicorrelationVectors/SequentialReport definitions; no
 new bespoke summation implementation, probability axiom or floating point.
 Boundary: An exact deterministic Gaussian density/precision relation,
 not an independent proof of measure normalization or conditional expectation.
*)
Definition gk_evidence_quadratic (xs:list R) (c:R) : R := (vector_square_energy xs - c*gk_sum xs*gk_sum xs/gk_d xs c)/(1-c).

(** [gk_posterior_quadratic] (definition).
 Mathematical meaning: The centered Gaussian posterior exponent with precision determined by the prior and n observations.
 Exact definition: gk_posterior_quadratic(xs:list R) (c theta:R) : R := gk_precision xs c*(theta-gk_center xs c)*(theta-gk_center xs c).
 Premises and side conditions: For a probabilistic Gaussian interpretation,
 score observations have a latent independent-normal residual model and
 0<c<1; algebraic proofs state the necessary nonzero divisions explicitly.
 Proof/definition method: Direct real algebra, explicit completion of a
 positive Gaussian quadratic, or a previously verified finite-list identity.
 Library reuse: Rocq Stdlib Reals/Field/Ring/Psatz and canonical
 FiniteSum/EquicorrelationVectors/SequentialReport definitions; no
 new bespoke summation implementation, probability axiom or floating point.
 Boundary: An exact deterministic Gaussian density/precision relation,
 not an independent proof of measure normalization or conditional expectation.
*)
Definition gk_posterior_quadratic (xs:list R) (c theta:R) : R := gk_precision xs c*(theta-gk_center xs c)*(theta-gk_center xs c).

(** [gk_joint_kernel] (definition).
 Mathematical meaning: The unnormalized joint Gaussian likelihood as a positive real function of latent theta.
 Exact definition: gk_joint_kernel(xs:list R) (c theta:R) : R := exp (-gk_joint_quadratic xs c theta/2).
 Premises and side conditions: For a probabilistic Gaussian interpretation,
 score observations have a latent independent-normal residual model and
 0<c<1; algebraic proofs state the necessary nonzero divisions explicitly.
 Proof/definition method: Direct real algebra, explicit completion of a
 positive Gaussian quadratic, or a previously verified finite-list identity.
 Library reuse: Rocq Stdlib Reals/Field/Ring/Psatz and canonical
 FiniteSum/EquicorrelationVectors/SequentialReport definitions; no
 new bespoke summation implementation, probability axiom or floating point.
 Boundary: An exact deterministic Gaussian density/precision relation,
 not an independent proof of measure normalization or conditional expectation.
*)
Definition gk_joint_kernel (xs:list R) (c theta:R) : R := exp (-gk_joint_quadratic xs c theta/2).

(** [gk_posterior_kernel] (definition).
 Mathematical meaning: The unnormalized centered normal posterior kernel as a positive real function of theta.
 Exact definition: gk_posterior_kernel(xs:list R) (c theta:R) : R := exp (-gk_posterior_quadratic xs c theta/2).
 Premises and side conditions: For a probabilistic Gaussian interpretation,
 score observations have a latent independent-normal residual model and
 0<c<1; algebraic proofs state the necessary nonzero divisions explicitly.
 Proof/definition method: Direct real algebra, explicit completion of a
 positive Gaussian quadratic, or a previously verified finite-list identity.
 Library reuse: Rocq Stdlib Reals/Field/Ring/Psatz and canonical
 FiniteSum/EquicorrelationVectors/SequentialReport definitions; no
 new bespoke summation implementation, probability axiom or floating point.
 Boundary: An exact deterministic Gaussian density/precision relation,
 not an independent proof of measure normalization or conditional expectation.
*)
Definition gk_posterior_kernel (xs:list R) (c theta:R) : R := exp (-gk_posterior_quadratic xs c theta/2).

(** [gk_evidence_kernel] (definition).
 Mathematical meaning: The positive data-only factor in the Gaussian likelihood factorization.
 Exact definition: gk_evidence_kernel(xs:list R) (c:R) : R := exp (-gk_evidence_quadratic xs c/2).
 Premises and side conditions: For a probabilistic Gaussian interpretation,
 score observations have a latent independent-normal residual model and
 0<c<1; algebraic proofs state the necessary nonzero divisions explicitly.
 Proof/definition method: Direct real algebra, explicit completion of a
 positive Gaussian quadratic, or a previously verified finite-list identity.
 Library reuse: Rocq Stdlib Reals/Field/Ring/Psatz and canonical
 FiniteSum/EquicorrelationVectors/SequentialReport definitions; no
 new bespoke summation implementation, probability axiom or floating point.
 Boundary: An exact deterministic Gaussian density/precision relation,
 not an independent proof of measure normalization or conditional expectation.
*)
Definition gk_evidence_kernel (xs:list R) (c:R) : R := exp (-gk_evidence_quadratic xs c/2).

(** [gk_mass_nonnegative] (theorem).
 Mathematical meaning: The count of observed test scores cannot be negative.
 Exact checked proposition: gk_mass_nonnegative: forall xs, 0 <= gk_mass xs.
 Premises and side conditions: For a probabilistic Gaussian interpretation,
 score observations have a latent independent-normal residual model and
 0<c<1; algebraic proofs state the necessary nonzero divisions explicitly.
 Proof/definition method: Direct real algebra, explicit completion of a
 positive Gaussian quadratic, or a previously verified finite-list identity.
 Library reuse: Rocq Stdlib Reals/Field/Ring/Psatz and canonical
 FiniteSum/EquicorrelationVectors/SequentialReport definitions; no
 new bespoke summation implementation, probability axiom or floating point.
 Boundary: An exact deterministic Gaussian density/precision relation,
 not an independent proof of measure normalization or conditional expectation.
*)
Theorem gk_mass_nonnegative : forall xs, 0 <= gk_mass xs.
Proof.
 intro xs; unfold gk_mass; apply pos_INR.
Qed.

(** [gk_mass_nonzero] (theorem).
 Mathematical meaning: A nonempty score history has positive embedded sample size.
 Exact checked proposition: gk_mass_nonzero: forall xs, xs<>nil -> gk_mass xs <> 0.
 Premises and side conditions: For a probabilistic Gaussian interpretation,
 score observations have a latent independent-normal residual model and
 0<c<1; algebraic proofs state the necessary nonzero divisions explicitly.
 Proof/definition method: Direct real algebra, explicit completion of a
 positive Gaussian quadratic, or a previously verified finite-list identity.
 Library reuse: Rocq Stdlib Reals/Field/Ring/Psatz and canonical
 FiniteSum/EquicorrelationVectors/SequentialReport definitions; no
 new bespoke summation implementation, probability axiom or floating point.
 Boundary: An exact deterministic Gaussian density/precision relation,
 not an independent proof of measure normalization or conditional expectation.
*)
Theorem gk_mass_nonzero : forall xs, xs<>nil -> gk_mass xs <> 0.
Proof.
 intros xs H; unfold gk_mass; destruct xs as [|a xs]; [contradiction|]; simpl; pose proof (pos_INR (length xs)); lra.
Qed.

(** [gk_d_decompose] (theorem).
 Mathematical meaning: The common-mode covariance eigenvalue splits into noise and signal contributions.
 Exact checked proposition: gk_d_decompose: forall xs c, gk_d xs c = (1-c)+gk_mass xs*c.
 Premises and side conditions: For a probabilistic Gaussian interpretation,
 score observations have a latent independent-normal residual model and
 0<c<1; algebraic proofs state the necessary nonzero divisions explicitly.
 Proof/definition method: Direct real algebra, explicit completion of a
 positive Gaussian quadratic, or a previously verified finite-list identity.
 Library reuse: Rocq Stdlib Reals/Field/Ring/Psatz and canonical
 FiniteSum/EquicorrelationVectors/SequentialReport definitions; no
 new bespoke summation implementation, probability axiom or floating point.
 Boundary: An exact deterministic Gaussian density/precision relation,
 not an independent proof of measure normalization or conditional expectation.
*)
Theorem gk_d_decompose : forall xs c, gk_d xs c = (1-c)+gk_mass xs*c.
Proof.
 intros; unfold gk_d, sequential_d; ring.
Qed.

(** [gk_d_positive] (theorem).
 Mathematical meaning: Strict Gaussian signal-noise parameters make the observation covariance nondegenerate.
 Exact checked proposition: gk_d_positive: forall xs c, 0<c -> c<1 -> 0<=gk_mass xs -> 0<gk_d xs c.
 Premises and side conditions: For a probabilistic Gaussian interpretation,
 score observations have a latent independent-normal residual model and
 0<c<1; algebraic proofs state the necessary nonzero divisions explicitly.
 Proof/definition method: Direct real algebra, explicit completion of a
 positive Gaussian quadratic, or a previously verified finite-list identity.
 Library reuse: Rocq Stdlib Reals/Field/Ring/Psatz and canonical
 FiniteSum/EquicorrelationVectors/SequentialReport definitions; no
 new bespoke summation implementation, probability axiom or floating point.
 Boundary: An exact deterministic Gaussian density/precision relation,
 not an independent proof of measure normalization or conditional expectation.
*)
Theorem gk_d_positive : forall xs c, 0<c -> c<1 -> 0<=gk_mass xs -> 0<gk_d xs c.
Proof.
 intros xs c Hc Hc1 Hn; rewrite gk_d_decompose; nra.
Qed.

(** [gk_center_matches_unequal_history] (theorem).
 Mathematical meaning: The Gaussian posterior center is precisely the arbitrary-score history candidate predictor.
 Exact checked proposition: gk_center_matches_unequal_history: forall xs c, gk_center xs c = hp (gk_mass xs) c (gk_sum xs).
 Premises and side conditions: For a probabilistic Gaussian interpretation,
 score observations have a latent independent-normal residual model and
 0<c<1; algebraic proofs state the necessary nonzero divisions explicitly.
 Proof/definition method: Direct real algebra, explicit completion of a
 positive Gaussian quadratic, or a previously verified finite-list identity.
 Library reuse: Rocq Stdlib Reals/Field/Ring/Psatz and canonical
 FiniteSum/EquicorrelationVectors/SequentialReport definitions; no
 new bespoke summation implementation, probability axiom or floating point.
 Boundary: An exact deterministic Gaussian density/precision relation,
 not an independent proof of measure normalization or conditional expectation.
*)
Theorem gk_center_matches_unequal_history : forall xs c, gk_center xs c = hp (gk_mass xs) c (gk_sum xs).
Proof.
 intros; unfold gk_center, hp, gk_d; reflexivity.
Qed.

(** [gk_center_repeat] (theorem).
 Mathematical meaning: The Gaussian posterior center reduces exactly to the existing equal-history report expression.
 Exact checked proposition: gk_center_repeat: forall n a c, gk_center (repeat a n) c = sequential_prediction (INR n) c a.
 Premises and side conditions: For a probabilistic Gaussian interpretation,
 score observations have a latent independent-normal residual model and
 0<c<1; algebraic proofs state the necessary nonzero divisions explicitly.
 Proof/definition method: Direct real algebra, explicit completion of a
 positive Gaussian quadratic, or a previously verified finite-list identity.
 Library reuse: Rocq Stdlib Reals/Field/Ring/Psatz and canonical
 FiniteSum/EquicorrelationVectors/SequentialReport definitions; no
 new bespoke summation implementation, probability axiom or floating point.
 Boundary: An exact deterministic Gaussian density/precision relation,
 not an independent proof of measure normalization or conditional expectation.
*)
Theorem gk_center_repeat : forall n a c, gk_center (repeat a n) c = sequential_prediction (INR n) c a.
Proof.
 intros n a c; unfold gk_center, gk_d, gk_mass, gk_sum; rewrite repeat_length, vector_real_sum_repeat; unfold sequential_prediction; reflexivity.
Qed.

(** [gk_precision_formula] (theorem).
 Mathematical meaning: The Gaussian posterior precision equals the canonical common-mode eigenvalue divided by the product of signal/noise variances.
 Exact checked proposition: gk_precision_formula: forall xs c, c<>0 -> 1-c<>0 -> gk_precision xs c = gk_d xs c/(c*(1-c)).
 Premises and side conditions: For a probabilistic Gaussian interpretation,
 score observations have a latent independent-normal residual model and
 0<c<1; algebraic proofs state the necessary nonzero divisions explicitly.
 Proof/definition method: Direct real algebra, explicit completion of a
 positive Gaussian quadratic, or a previously verified finite-list identity.
 Library reuse: Rocq Stdlib Reals/Field/Ring/Psatz and canonical
 FiniteSum/EquicorrelationVectors/SequentialReport definitions; no
 new bespoke summation implementation, probability axiom or floating point.
 Boundary: An exact deterministic Gaussian density/precision relation,
 not an independent proof of measure normalization or conditional expectation.
*)
Theorem gk_precision_formula : forall xs c, c<>0 -> 1-c<>0 -> gk_precision xs c = gk_d xs c/(c*(1-c)).
Proof.
 intros xs c Hc Hc1; unfold gk_precision, gk_d, sequential_d; field; nra.
Qed.

(** [gk_precision_positive] (theorem).
 Mathematical meaning: Positive signal and noise variances yield strictly positive posterior precision.
 Exact checked proposition: gk_precision_positive: forall xs c, 0<c -> c<1 -> 0<gk_precision xs c.
 Premises and side conditions: For a probabilistic Gaussian interpretation,
 score observations have a latent independent-normal residual model and
 0<c<1; algebraic proofs state the necessary nonzero divisions explicitly.
 Proof/definition method: Direct real algebra, explicit completion of a
 positive Gaussian quadratic, or a previously verified finite-list identity.
 Library reuse: Rocq Stdlib Reals/Field/Ring/Psatz and canonical
 FiniteSum/EquicorrelationVectors/SequentialReport definitions; no
 new bespoke summation implementation, probability axiom or floating point.
 Boundary: An exact deterministic Gaussian density/precision relation,
 not an independent proof of measure normalization or conditional expectation.
*)
Theorem gk_precision_positive : forall xs c, 0<c -> c<1 -> 0<gk_precision xs c.
Proof.
 intros xs c Hc Hc1; unfold gk_precision; assert (Hn:0<=gk_mass xs) by apply gk_mass_nonnegative; apply Rplus_lt_le_0_compat; [apply Rinv_0_lt_compat; lra|apply Rdiv_le_0_compat; lra].
Qed.

(** [gk_variance_positive] (theorem).
 Mathematical meaning: Posterior variance is strictly positive even for an empty history, as the latent prior is nondegenerate.
 Exact checked proposition: gk_variance_positive: forall xs c, 0<c -> c<1 -> 0<gk_variance xs c.
 Premises and side conditions: For a probabilistic Gaussian interpretation,
 score observations have a latent independent-normal residual model and
 0<c<1; algebraic proofs state the necessary nonzero divisions explicitly.
 Proof/definition method: Direct real algebra, explicit completion of a
 positive Gaussian quadratic, or a previously verified finite-list identity.
 Library reuse: Rocq Stdlib Reals/Field/Ring/Psatz and canonical
 FiniteSum/EquicorrelationVectors/SequentialReport definitions; no
 new bespoke summation implementation, probability axiom or floating point.
 Boundary: An exact deterministic Gaussian density/precision relation,
 not an independent proof of measure normalization or conditional expectation.
*)
Theorem gk_variance_positive : forall xs c, 0<c -> c<1 -> 0<gk_variance xs c.
Proof.
 intros xs c Hc Hc1; unfold gk_variance; apply Rdiv_lt_0_compat; [nra|apply gk_d_positive; try lra; apply gk_mass_nonnegative].
Qed.

(** [gk_precision_variance] (theorem).
 Mathematical meaning: The normal posterior precision is the reciprocal of the normal posterior variance.
 Exact checked proposition: gk_precision_variance: forall xs c, 0<c -> c<1 -> gk_precision xs c*gk_variance xs c=1.
 Premises and side conditions: For a probabilistic Gaussian interpretation,
 score observations have a latent independent-normal residual model and
 0<c<1; algebraic proofs state the necessary nonzero divisions explicitly.
 Proof/definition method: Direct real algebra, explicit completion of a
 positive Gaussian quadratic, or a previously verified finite-list identity.
 Library reuse: Rocq Stdlib Reals/Field/Ring/Psatz and canonical
 FiniteSum/EquicorrelationVectors/SequentialReport definitions; no
 new bespoke summation implementation, probability axiom or floating point.
 Boundary: An exact deterministic Gaussian density/precision relation,
 not an independent proof of measure normalization or conditional expectation.
*)
Theorem gk_precision_variance : forall xs c, 0<c -> c<1 -> gk_precision xs c*gk_variance xs c=1.
Proof.
 intros xs c Hc Hc1; unfold gk_precision, gk_variance, gk_d, sequential_d, gk_mass; field; nra.
Qed.

(** [gk_variance_below_prior] (theorem).
 Mathematical meaning: Observing any number of noisy measurements cannot increase the signal posterior variance.
 Exact checked proposition: gk_variance_below_prior: forall xs c, 0<c -> c<1 -> gk_variance xs c<=c.
 Premises and side conditions: For a probabilistic Gaussian interpretation,
 score observations have a latent independent-normal residual model and
 0<c<1; algebraic proofs state the necessary nonzero divisions explicitly.
 Proof/definition method: Direct real algebra, explicit completion of a
 positive Gaussian quadratic, or a previously verified finite-list identity.
 Library reuse: Rocq Stdlib Reals/Field/Ring/Psatz and canonical
 FiniteSum/EquicorrelationVectors/SequentialReport definitions; no
 new bespoke summation implementation, probability axiom or floating point.
 Boundary: An exact deterministic Gaussian density/precision relation,
 not an independent proof of measure normalization or conditional expectation.
*)
Theorem gk_variance_below_prior : forall xs c, 0<c -> c<1 -> gk_variance xs c<=c.
Proof.
 intros xs c Hc Hc1; unfold gk_variance, gk_d, sequential_d; assert(Hn:0<=gk_mass xs) by apply gk_mass_nonnegative; assert(Hd:0<(1-c)+gk_mass xs*c) by nra; apply Rmult_le_reg_r with (r:=((1-c)+gk_mass xs*c)); [assumption|]; rewrite Rdiv_def; rewrite Rmult_assoc; rewrite Rinv_l by lra; rewrite Rmult_1_r; nra.
Qed.

(** [gk_center_zero_history] (theorem).
 Mathematical meaning: With no observations the centered posterior estimate is zero.
 Exact checked proposition: gk_center_zero_history: forall c, gk_center nil c = 0.
 Premises and side conditions: For a probabilistic Gaussian interpretation,
 score observations have a latent independent-normal residual model and
 0<c<1; algebraic proofs state the necessary nonzero divisions explicitly.
 Proof/definition method: Direct real algebra, explicit completion of a
 positive Gaussian quadratic, or a previously verified finite-list identity.
 Library reuse: Rocq Stdlib Reals/Field/Ring/Psatz and canonical
 FiniteSum/EquicorrelationVectors/SequentialReport definitions; no
 new bespoke summation implementation, probability axiom or floating point.
 Boundary: An exact deterministic Gaussian density/precision relation,
 not an independent proof of measure normalization or conditional expectation.
*)
Theorem gk_center_zero_history : forall c, gk_center nil c = 0.
Proof.
 intro c; unfold gk_center, gk_sum, gk_mass, gk_d, vector_real_sum, finite_sum, sequential_d; simpl; field; lra.
Qed.

(** [gk_residual_expansion] (theorem).
 Mathematical meaning: The arbitrary list of noisy Gaussian scores expands into the correct quadratic sufficient statistics.
 Exact checked proposition: gk_residual_expansion: forall xs theta, gk_residual_energy xs theta = vector_square_energy xs - 2*theta*gk_sum xs + gk_mass xs*theta*theta.
 Premises and side conditions: For a probabilistic Gaussian interpretation,
 score observations have a latent independent-normal residual model and
 0<c<1; algebraic proofs state the necessary nonzero divisions explicitly.
 Proof/definition method: Direct real algebra, explicit completion of a
 positive Gaussian quadratic, or a previously verified finite-list identity.
 Library reuse: Rocq Stdlib Reals/Field/Ring/Psatz and canonical
 FiniteSum/EquicorrelationVectors/SequentialReport definitions; no
 new bespoke summation implementation, probability axiom or floating point.
 Boundary: An exact deterministic Gaussian density/precision relation,
 not an independent proof of measure normalization or conditional expectation.
*)
Theorem gk_residual_expansion : forall xs theta, gk_residual_energy xs theta = vector_square_energy xs - 2*theta*gk_sum xs + gk_mass xs*theta*theta.
Proof.
 intros; unfold gk_residual_energy, gk_mass, gk_sum; apply vector_center_energy_expansion.
Qed.

(** [gk_joint_quadratic_expansion] (theorem).
 Mathematical meaning: The likelihood of unequal score histories depends on the data through count, sum and squared sum.
 Exact checked proposition: gk_joint_quadratic_expansion: forall xs c theta, gk_joint_quadratic xs c theta = theta*theta/c + (vector_square_energy xs - 2*theta*gk_sum xs + gk_mass xs*theta*theta)/(1-c).
 Premises and side conditions: For a probabilistic Gaussian interpretation,
 score observations have a latent independent-normal residual model and
 0<c<1; algebraic proofs state the necessary nonzero divisions explicitly.
 Proof/definition method: Direct real algebra, explicit completion of a
 positive Gaussian quadratic, or a previously verified finite-list identity.
 Library reuse: Rocq Stdlib Reals/Field/Ring/Psatz and canonical
 FiniteSum/EquicorrelationVectors/SequentialReport definitions; no
 new bespoke summation implementation, probability axiom or floating point.
 Boundary: An exact deterministic Gaussian density/precision relation,
 not an independent proof of measure normalization or conditional expectation.
*)
Theorem gk_joint_quadratic_expansion : forall xs c theta, gk_joint_quadratic xs c theta = theta*theta/c + (vector_square_energy xs - 2*theta*gk_sum xs + gk_mass xs*theta*theta)/(1-c).
Proof.
 intros; unfold gk_joint_quadratic; rewrite gk_residual_expansion; reflexivity.
Qed.

(** [gk_square_completion] (theorem).
 Mathematical meaning: Gaussian square completion separates the theta-dependent posterior quadratic from the data-only evidence quadratic.
 Exact checked proposition: gk_square_completion: forall xs c theta, c<>0 -> 1-c<>0 -> gk_d xs c<>0 -> gk_joint_quadratic xs c theta = gk_posterior_quadratic xs c theta + gk_evidence_quadratic xs c.
 Premises and side conditions: For a probabilistic Gaussian interpretation,
 score observations have a latent independent-normal residual model and
 0<c<1; algebraic proofs state the necessary nonzero divisions explicitly.
 Proof/definition method: Direct real algebra, explicit completion of a
 positive Gaussian quadratic, or a previously verified finite-list identity.
 Library reuse: Rocq Stdlib Reals/Field/Ring/Psatz and canonical
 FiniteSum/EquicorrelationVectors/SequentialReport definitions; no
 new bespoke summation implementation, probability axiom or floating point.
 Boundary: An exact deterministic Gaussian density/precision relation,
 not an independent proof of measure normalization or conditional expectation.
*)
Theorem gk_square_completion : forall xs c theta, c<>0 -> 1-c<>0 -> gk_d xs c<>0 -> gk_joint_quadratic xs c theta = gk_posterior_quadratic xs c theta + gk_evidence_quadratic xs c.
Proof.
 intros xs c theta Hc Hnoise Hd; rewrite gk_joint_quadratic_expansion; unfold gk_posterior_quadratic, gk_evidence_quadratic, gk_precision, gk_center, gk_d, sequential_d, gk_mass, gk_sum; field; nra.
Qed.

(** [gk_joint_kernel_positive] (theorem).
 Mathematical meaning: Every unnormalized Gaussian joint likelihood kernel is strictly positive.
 Exact checked proposition: gk_joint_kernel_positive: forall xs c theta, 0<gk_joint_kernel xs c theta.
 Premises and side conditions: For a probabilistic Gaussian interpretation,
 score observations have a latent independent-normal residual model and
 0<c<1; algebraic proofs state the necessary nonzero divisions explicitly.
 Proof/definition method: Direct real algebra, explicit completion of a
 positive Gaussian quadratic, or a previously verified finite-list identity.
 Library reuse: Rocq Stdlib Reals/Field/Ring/Psatz and canonical
 FiniteSum/EquicorrelationVectors/SequentialReport definitions; no
 new bespoke summation implementation, probability axiom or floating point.
 Boundary: An exact deterministic Gaussian density/precision relation,
 not an independent proof of measure normalization or conditional expectation.
*)
Theorem gk_joint_kernel_positive : forall xs c theta, 0<gk_joint_kernel xs c theta.
Proof.
 intros; unfold gk_joint_kernel; apply exp_pos.
Qed.

(** [gk_evidence_kernel_positive] (theorem).
 Mathematical meaning: Gaussian square-completion evidence factor is nonzero for any real algebraic inputs.
 Exact checked proposition: gk_evidence_kernel_positive: forall xs c, 0<gk_evidence_kernel xs c.
 Premises and side conditions: For a probabilistic Gaussian interpretation,
 score observations have a latent independent-normal residual model and
 0<c<1; algebraic proofs state the necessary nonzero divisions explicitly.
 Proof/definition method: Direct real algebra, explicit completion of a
 positive Gaussian quadratic, or a previously verified finite-list identity.
 Library reuse: Rocq Stdlib Reals/Field/Ring/Psatz and canonical
 FiniteSum/EquicorrelationVectors/SequentialReport definitions; no
 new bespoke summation implementation, probability axiom or floating point.
 Boundary: An exact deterministic Gaussian density/precision relation,
 not an independent proof of measure normalization or conditional expectation.
*)
Theorem gk_evidence_kernel_positive : forall xs c, 0<gk_evidence_kernel xs c.
Proof.
 intros; unfold gk_evidence_kernel; apply exp_pos.
Qed.

(** [gk_posterior_kernel_positive] (theorem).
 Mathematical meaning: Every Gaussian posterior density kernel is strictly positive.
 Exact checked proposition: gk_posterior_kernel_positive: forall xs c theta, 0<gk_posterior_kernel xs c theta.
 Premises and side conditions: For a probabilistic Gaussian interpretation,
 score observations have a latent independent-normal residual model and
 0<c<1; algebraic proofs state the necessary nonzero divisions explicitly.
 Proof/definition method: Direct real algebra, explicit completion of a
 positive Gaussian quadratic, or a previously verified finite-list identity.
 Library reuse: Rocq Stdlib Reals/Field/Ring/Psatz and canonical
 FiniteSum/EquicorrelationVectors/SequentialReport definitions; no
 new bespoke summation implementation, probability axiom or floating point.
 Boundary: An exact deterministic Gaussian density/precision relation,
 not an independent proof of measure normalization or conditional expectation.
*)
Theorem gk_posterior_kernel_positive : forall xs c theta, 0<gk_posterior_kernel xs c theta.
Proof.
 intros; unfold gk_posterior_kernel; apply exp_pos.
Qed.

(** [gk_joint_factorization] (theorem).
 Mathematical meaning: The full Gaussian prior times the Gaussian observation likelihood factors into posterior theta-kernel and data-only evidence.
 Exact checked proposition: gk_joint_factorization: forall xs c theta, c<>0 -> 1-c<>0 -> gk_d xs c<>0 -> gk_joint_kernel xs c theta = gk_posterior_kernel xs c theta * gk_evidence_kernel xs c.
 Premises and side conditions: For a probabilistic Gaussian interpretation,
 score observations have a latent independent-normal residual model and
 0<c<1; algebraic proofs state the necessary nonzero divisions explicitly.
 Proof/definition method: Direct real algebra, explicit completion of a
 positive Gaussian quadratic, or a previously verified finite-list identity.
 Library reuse: Rocq Stdlib Reals/Field/Ring/Psatz and canonical
 FiniteSum/EquicorrelationVectors/SequentialReport definitions; no
 new bespoke summation implementation, probability axiom or floating point.
 Boundary: An exact deterministic Gaussian density/precision relation,
 not an independent proof of measure normalization or conditional expectation.
*)
Theorem gk_joint_factorization : forall xs c theta, c<>0 -> 1-c<>0 -> gk_d xs c<>0 -> gk_joint_kernel xs c theta = gk_posterior_kernel xs c theta * gk_evidence_kernel xs c.
Proof.
 intros xs c theta Hc Hnoise Hd; unfold gk_joint_kernel, gk_posterior_kernel, gk_evidence_kernel; rewrite (gk_square_completion xs c theta Hc Hnoise Hd); rewrite <- exp_plus; f_equal; ring.
Qed.

(** [gk_kernel_reflection] (theorem).
 Mathematical meaning: The posterior Gaussian kernel is exactly symmetric around the candidate conditional mean.
 Exact checked proposition: gk_kernel_reflection: forall xs c t, gk_posterior_kernel xs c (gk_center xs c + t) = gk_posterior_kernel xs c (gk_center xs c - t).
 Premises and side conditions: For a probabilistic Gaussian interpretation,
 score observations have a latent independent-normal residual model and
 0<c<1; algebraic proofs state the necessary nonzero divisions explicitly.
 Proof/definition method: Direct real algebra, explicit completion of a
 positive Gaussian quadratic, or a previously verified finite-list identity.
 Library reuse: Rocq Stdlib Reals/Field/Ring/Psatz and canonical
 FiniteSum/EquicorrelationVectors/SequentialReport definitions; no
 new bespoke summation implementation, probability axiom or floating point.
 Boundary: An exact deterministic Gaussian density/precision relation,
 not an independent proof of measure normalization or conditional expectation.
*)
Theorem gk_kernel_reflection : forall xs c t, gk_posterior_kernel xs c (gk_center xs c + t) = gk_posterior_kernel xs c (gk_center xs c - t).
Proof.
 intros; unfold gk_posterior_kernel, gk_posterior_quadratic; f_equal; ring.
Qed.

(** [gk_kernel_at_center] (theorem).
 Mathematical meaning: The posterior Gaussian kernel attains its unit peak at the regression estimate.
 Exact checked proposition: gk_kernel_at_center: forall xs c, gk_posterior_kernel xs c (gk_center xs c)=1.
 Premises and side conditions: For a probabilistic Gaussian interpretation,
 score observations have a latent independent-normal residual model and
 0<c<1; algebraic proofs state the necessary nonzero divisions explicitly.
 Proof/definition method: Direct real algebra, explicit completion of a
 positive Gaussian quadratic, or a previously verified finite-list identity.
 Library reuse: Rocq Stdlib Reals/Field/Ring/Psatz and canonical
 FiniteSum/EquicorrelationVectors/SequentialReport definitions; no
 new bespoke summation implementation, probability axiom or floating point.
 Boundary: An exact deterministic Gaussian density/precision relation,
 not an independent proof of measure normalization or conditional expectation.
*)
Theorem gk_kernel_at_center : forall xs c, gk_posterior_kernel xs c (gk_center xs c)=1.
Proof.
 intros; unfold gk_posterior_kernel, gk_posterior_quadratic; replace (gk_center xs c - gk_center xs c) with 0 by ring; ring_simplify; apply exp_0.
Qed.

(** [gk_kernel_at_least_zero] (theorem).
 Mathematical meaning: Positive posterior precision guarantees the posterior Gaussian kernel never exceeds its unit maximum.
 Exact checked proposition: gk_kernel_at_least_zero: forall xs c theta, 0<c -> c<1 -> gk_posterior_kernel xs c theta <= 1.
 Premises and side conditions: For a probabilistic Gaussian interpretation,
 score observations have a latent independent-normal residual model and
 0<c<1; algebraic proofs state the necessary nonzero divisions explicitly.
 Proof/definition method: Direct real algebra, explicit completion of a
 positive Gaussian quadratic, or a previously verified finite-list identity.
 Library reuse: Rocq Stdlib Reals/Field/Ring/Psatz and canonical
 FiniteSum/EquicorrelationVectors/SequentialReport definitions; no
 new bespoke summation implementation, probability axiom or floating point.
 Boundary: An exact deterministic Gaussian density/precision relation,
 not an independent proof of measure normalization or conditional expectation.
*)
Theorem gk_kernel_at_least_zero : forall xs c theta, 0<c -> c<1 -> gk_posterior_kernel xs c theta <= 1.
Proof.
 intros xs c theta Hc Hc1; unfold gk_posterior_kernel, gk_posterior_quadratic; rewrite <- exp_0; apply exp_le; assert(Hp:0<gk_precision xs c) by (apply gk_precision_positive; assumption); nra.
Qed.

(** [gk_posterior_kernel_variance] (theorem).
 Mathematical meaning: The Gaussian posterior kernel has variance parameter c(1-c)/d, rather than just an unidentified positive quadratic coefficient.
 Exact checked proposition: gk_posterior_kernel_variance: forall xs c theta, 0<c -> c<1 -> gk_posterior_kernel xs c theta = exp (- (theta-gk_center xs c)*(theta-gk_center xs c)/(2*gk_variance xs c)).
 Premises and side conditions: For a probabilistic Gaussian interpretation,
 score observations have a latent independent-normal residual model and
 0<c<1; algebraic proofs state the necessary nonzero divisions explicitly.
 Proof/definition method: Direct real algebra, explicit completion of a
 positive Gaussian quadratic, or a previously verified finite-list identity.
 Library reuse: Rocq Stdlib Reals/Field/Ring/Psatz and canonical
 FiniteSum/EquicorrelationVectors/SequentialReport definitions; no
 new bespoke summation implementation, probability axiom or floating point.
 Boundary: An exact deterministic Gaussian density/precision relation,
 not an independent proof of measure normalization or conditional expectation.
*)
Theorem gk_posterior_kernel_variance : forall xs c theta, 0<c -> c<1 -> gk_posterior_kernel xs c theta = exp (- (theta-gk_center xs c)*(theta-gk_center xs c)/(2*gk_variance xs c)).
Proof.
 intros xs c theta Hc Hc1; unfold gk_posterior_kernel, gk_posterior_quadratic; f_equal; pose proof (gk_precision_variance xs c Hc Hc1) as Hpv; pose proof (gk_variance_positive xs c Hc Hc1) as Hv; field; nra.
Qed.

(** [gk_kernel_ratio] (theorem).
 Mathematical meaning: Conditioning on a fixed data set cancels the Gaussian evidence and leaves the unique theta-dependent posterior kernel.
 Exact checked proposition: gk_kernel_ratio: forall xs c theta, c<>0 -> 1-c<>0 -> gk_d xs c<>0 -> gk_joint_kernel xs c theta/gk_evidence_kernel xs c = gk_posterior_kernel xs c theta.
 Premises and side conditions: For a probabilistic Gaussian interpretation,
 score observations have a latent independent-normal residual model and
 0<c<1; algebraic proofs state the necessary nonzero divisions explicitly.
 Proof/definition method: Direct real algebra, explicit completion of a
 positive Gaussian quadratic, or a previously verified finite-list identity.
 Library reuse: Rocq Stdlib Reals/Field/Ring/Psatz and canonical
 FiniteSum/EquicorrelationVectors/SequentialReport definitions; no
 new bespoke summation implementation, probability axiom or floating point.
 Boundary: An exact deterministic Gaussian density/precision relation,
 not an independent proof of measure normalization or conditional expectation.
*)
Theorem gk_kernel_ratio : forall xs c theta, c<>0 -> 1-c<>0 -> gk_d xs c<>0 -> gk_joint_kernel xs c theta/gk_evidence_kernel xs c = gk_posterior_kernel xs c theta.
Proof.
 intros xs c theta Hc Hnoise Hd; rewrite (gk_joint_factorization xs c theta Hc Hnoise Hd); field; pose proof (gk_evidence_kernel_positive xs c); lra.
Qed.

(** [gk_posterior_at_mean] (theorem).
 Mathematical meaning: The completed Gaussian posterior quadratic vanishes at its center.
 Exact checked proposition: gk_posterior_at_mean: forall xs c, gk_posterior_quadratic xs c (gk_center xs c)=0.
 Premises and side conditions: For a probabilistic Gaussian interpretation,
 score observations have a latent independent-normal residual model and
 0<c<1; algebraic proofs state the necessary nonzero divisions explicitly.
 Proof/definition method: Direct real algebra, explicit completion of a
 positive Gaussian quadratic, or a previously verified finite-list identity.
 Library reuse: Rocq Stdlib Reals/Field/Ring/Psatz and canonical
 FiniteSum/EquicorrelationVectors/SequentialReport definitions; no
 new bespoke summation implementation, probability axiom or floating point.
 Boundary: An exact deterministic Gaussian density/precision relation,
 not an independent proof of measure normalization or conditional expectation.
*)
Theorem gk_posterior_at_mean : forall xs c, gk_posterior_quadratic xs c (gk_center xs c)=0.
Proof.
 intros; unfold gk_posterior_quadratic; ring.
Qed.
