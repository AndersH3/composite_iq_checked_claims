(** Module: SequentialReport.v
   Purpose: Formally check the deterministic algebra actually used in the
   sequential conditional-means report, including equal-correlation
   recursion, inclusive score means, residual variance, correlation
   boundaries and exact IQ-150 arithmetic certificates.
   Mathematical representation: The number of initial and later tests is
   represented as a real scalar for symbolic algebra; positive integer
   test counts are instances of these real identities. The regression
   coefficient and residual covariance are explicit arithmetic inputs.
   Explicit hypotheses: Every theorem requiring a valid division or sign
   uses stated nonzero or positive denominator and correlation premises.
   Library use: Stdlib.Reals, Lra, Psatz, Field/Ring; reuse Hoeflin's
   already checked equal-weight covariance expression rather than
   implementing another finite sum or bespoke matrix package.
   Limitations: No theorem here establishes Gaussian random variables,
   regular conditional distributions, Gaussian regression, a spectral
   decomposition or uniqueness of conditional-expectation versions.
   The report's Gaussian theorems remain separate formalization tasks.
   Proof documentation: Every definition and theorem has a comment with
   mathematical meaning, exact formula, assumptions, method and boundary.
   Reproduction: rocq compile Hoeflin.v && rocq compile SequentialReport.v
   with Rocq 9.2; see rocq/REPORT_THEOREM_INVENTORY.md for claim mapping,
   rocq/README.md for module order and the checked-claim register.
 *)
From Stdlib Require Import Reals Lra Psatz Lia ZArith.
Require Import Hoeflin.
Open Scope R_scope.

(**
 [sequential_d] (definition) — Equicorrelation conditioning denominator.
 Mathematical meaning: Equicorrelation conditioning denominator.
 Exact declaration: d_n(c)=1+(n-1)c.
 Premises and side conditions: Any real n,c; intended sample counts are positive integers.
 Proof/definition method: Transparent standard real arithmetic expression, with any
 nonzero denominator requirements deliberately deferred to the corresponding theorem.
 Library reuse: Stdlib.Reals, Stdlib.Psatz and already verified Hoeflin covariance formulas.
 Boundary: The arithmetic model does not construct any random variable, a Gaussian law,
 conditional expectation, or empirical population calibration.
 *)
Definition sequential_d (n c : R) : R := 1 + (n - 1) * c.

(**
 [sequential_prediction] (definition) — One scalar prediction given r equal observed scores.
 Mathematical meaning: One scalar prediction given r equal observed scores.
 Exact declaration: b_r=r c a/d_r.
 Premises and side conditions: Nonzero d_r is required in the interpretation, though R division is total.
 Proof/definition method: Transparent standard real arithmetic expression, with any
 nonzero denominator requirements deliberately deferred to the corresponding theorem.
 Library reuse: Stdlib.Reals, Stdlib.Psatz and already verified Hoeflin covariance formulas.
 Boundary: The arithmetic model does not construct any random variable, a Gaussian law,
 conditional expectation, or empirical population calibration.
 *)
Definition sequential_prediction (r c a : R) : R := r * c * a / sequential_d r c.

(**
 [sequential_inclusive_mean] (definition) — The inclusive arithmetic mean of r observed equal scores and k repeated predictions.
 Mathematical meaning: The inclusive arithmetic mean of r observed equal scores and k repeated predictions.
 Exact declaration: B_{r,k}=(ra+k b_r)/(r+k).
 Premises and side conditions: The total count r+k is nonzero in statistical interpretations.
 Proof/definition method: Transparent standard real arithmetic expression, with any
 nonzero denominator requirements deliberately deferred to the corresponding theorem.
 Library reuse: Stdlib.Reals, Stdlib.Psatz and already verified Hoeflin covariance formulas.
 Boundary: The arithmetic model does not construct any random variable, a Gaussian law,
 conditional expectation, or empirical population calibration.
 *)
Definition sequential_inclusive_mean (r k c a : R) : R := (r * a + k * sequential_prediction r c a) / (r + k).

(**
 [sequential_population_variance] (definition) — Variance formula for an equal-weight, equicorrelated score battery.
 Mathematical meaning: Variance formula for an equal-weight, equicorrelated score battery.
 Exact declaration: V_pop=d_n/n.
 Premises and side conditions: Requires a stochastic covariance hypothesis in order to equal an actual variance.
 Proof/definition method: Transparent standard real arithmetic expression, with any
 nonzero denominator requirements deliberately deferred to the corresponding theorem.
 Library reuse: Stdlib.Reals, Stdlib.Psatz and already verified Hoeflin covariance formulas.
 Boundary: The arithmetic model does not construct any random variable, a Gaussian law,
 conditional expectation, or empirical population calibration.
 *)
Definition sequential_population_variance (n c : R) : R := sequential_d n c / n.

(**
 [sequential_conditional_variance] (definition) — Residual average-variance formula for k scores conditional on r initial scores.
 Mathematical meaning: Residual average-variance formula for k scores conditional on r initial scores.
 Exact declaration: V_cond=k(1-c)d_{r+k}/((r+k)^2 d_r).
 Premises and side conditions: The Gaussian residual covariance formula is not established by a field identity.
 Proof/definition method: Transparent standard real arithmetic expression, with any
 nonzero denominator requirements deliberately deferred to the corresponding theorem.
 Library reuse: Stdlib.Reals, Stdlib.Psatz and already verified Hoeflin covariance formulas.
 Boundary: The arithmetic model does not construct any random variable, a Gaussian law,
 conditional expectation, or empirical population calibration.
 *)
Definition sequential_conditional_variance (r k c : R) : R := k * (1 - c) * sequential_d (r + k) c / ((r + k) * (r + k) * sequential_d r c).
(**
 [sequential_denominator_one] (theorem) — The single observed score yields the unit regression denominator.
 Mathematical meaning: The single observed score yields the unit regression denominator.
 Exact checked proposition: forall c, sequential_d 1 c = 1.
 Premises and side conditions: None; the correlation is any real scalar.
 Proof/definition method: Normalize the denominator at one observation using real ring arithmetic.
 Library reuse: Stdlib.Reals, Stdlib.Lra, Stdlib.Psatz; previously checked sequential real identities.
 Boundary: Exact real-algebraic identity only; no Gaussian conditional distribution or empirical IQ model is established.
 *)
Theorem sequential_denominator_one :
  forall c, sequential_d 1 c = 1.
Proof.
  intros c; unfold sequential_d; ring.
Qed.

(**
 [sequential_denominator_add] (theorem) — The equicorrelation regression denominator updates additively when more tests are included.
 Mathematical meaning: The equicorrelation regression denominator updates additively when more tests are included.
 Exact checked proposition: forall r k c, sequential_d (r + k) c = sequential_d r c + k * c.
 Premises and side conditions: Real counts r and k; intended natural-number counts embed in the reals.
 Proof/definition method: Expand the same denominator definition and normalize by the standard ring tactic.
 Library reuse: Stdlib.Reals, Stdlib.Lra, Stdlib.Psatz; previously checked sequential real identities.
 Boundary: Exact real-algebraic identity only; no Gaussian conditional distribution or empirical IQ model is established.
 *)
Theorem sequential_denominator_add :
  forall r k c, sequential_d (r + k) c = sequential_d r c + k * c.
Proof.
  intros r k c; unfold sequential_d; ring.
Qed.

(**
 [sequential_denominator_at_zero_correlation] (theorem) — The regression denominator equals one for independent scores.
 Mathematical meaning: The regression denominator equals one for independent scores.
 Exact checked proposition: forall n, sequential_d n 0 = 1.
 Premises and side conditions: Any real count, including integer counts; c=0 is an explicit model input.
 Proof/definition method: Reduce at zero correlation and normalize with ring.
 Library reuse: Stdlib.Reals, Stdlib.Lra, Stdlib.Psatz; previously checked sequential real identities.
 Boundary: Exact real-algebraic identity only; no Gaussian conditional distribution or empirical IQ model is established.
 *)
Theorem sequential_denominator_at_zero_correlation :
  forall n, sequential_d n 0 = 1.
Proof.
  intros n; unfold sequential_d; ring.
Qed.

(**
 [sequential_denominator_at_unit_correlation] (theorem) — Perfect correlation makes the regression denominator equal the number of observed scores.
 Mathematical meaning: Perfect correlation makes the regression denominator equal the number of observed scores.
 Exact checked proposition: forall n, sequential_d n 1 = n.
 Premises and side conditions: Arbitrary real count; c=1 is an explicit boundary parameter.
 Proof/definition method: Normalize a linear real expression by ring.
 Library reuse: Stdlib.Reals, Stdlib.Lra, Stdlib.Psatz; previously checked sequential real identities.
 Boundary: Exact real-algebraic identity only; no Gaussian conditional distribution or empirical IQ model is established.
 *)
Theorem sequential_denominator_at_unit_correlation :
  forall n, sequential_d n 1 = n.
Proof.
  intros n; unfold sequential_d; ring.
Qed.

(**
 [sequential_denominator_positive_nonnegative_correlation] (theorem) — Equicorrelation denominators are strictly positive for at least one observed score and nonnegative correlation.
 Mathematical meaning: Equicorrelation denominators are strictly positive for at least one observed score and nonnegative correlation.
 Exact checked proposition: forall n c, 1 <= n -> 0 <= c -> 0 < sequential_d n c.
 Premises and side conditions: At least one score and 0<=c; the negative-correlation admissibility domain requires additional analysis.
 Proof/definition method: Factor the nonnegative count and correlation contribution using Psatz.nra.
 Library reuse: Stdlib.Reals, Stdlib.Lra, Stdlib.Psatz; previously checked sequential real identities.
 Boundary: Exact real-algebraic identity only; no Gaussian conditional distribution or empirical IQ model is established.
 *)
Theorem sequential_denominator_positive_nonnegative_correlation :
  forall n c, 1 <= n -> 0 <= c -> 0 < sequential_d n c.
Proof.
  intros n c Hn Hc; unfold sequential_d; nra.
Qed.

(**
 [sequential_population_variance_matches_composite] (theorem) — The sequential report's population average-variance formula is exactly the composite-score formula already checked for Hoeflin.
 Mathematical meaning: The sequential report's population average-variance formula is exactly the composite-score formula already checked for Hoeflin.
 Exact checked proposition: forall n c, n <> 0 -> sequential_population_variance n c = Hoeflin.equal_weight_variance n c.
 Premises and side conditions: Nonzero count; covariance structure is a model premise, not inferred from Gaussianity.
 Proof/definition method: Rewrite the new denominator and reuse the existing equal-weight covariance algebra with field cancellation.
 Library reuse: Hoeflin.equal_weight_variance; Stdlib.Field.
 Boundary: Equivalence of two arithmetic formulas; it does not independently prove a stochastic variance law.
 *)
Theorem sequential_population_variance_matches_composite :
  forall n c, n <> 0 -> sequential_population_variance n c = Hoeflin.equal_weight_variance n c.
Proof.
  intros n c Hn; unfold sequential_population_variance, sequential_d, Hoeflin.equal_weight_variance; field; exact Hn.
Qed.

(**
 [sequential_population_variance_positive] (theorem) — For positive count and nonnegative correlation, the specified population variance is strictly positive.
 Mathematical meaning: For positive count and nonnegative correlation, the specified population variance is strictly positive.
 Exact checked proposition: forall n c, 1 <= n -> 0 <= c -> 0 < sequential_population_variance n c.
 Premises and side conditions: 1<=n and c>=0; no upper correlation bound needed for this particular inequality.
 Proof/definition method: Use positive-denominator theorem and Stdlib's strict positivity of a quotient.
 Library reuse: sequential_denominator_positive_nonnegative_correlation, Rdiv_lt_0_compat.
 Boundary: Exact real-algebraic identity only; no Gaussian conditional distribution or empirical IQ model is established.
 *)
Theorem sequential_population_variance_positive :
  forall n c, 1 <= n -> 0 <= c -> 0 < sequential_population_variance n c.
Proof.
  intros n c Hn Hc; unfold sequential_population_variance; apply Rdiv_lt_0_compat; [apply sequential_denominator_positive_nonnegative_correlation; assumption | lra].
Qed.

(**
 [sequential_prediction_single_start] (theorem) — The single-start Gaussian regression arithmetic produces the first prediction ca.
 Mathematical meaning: The single-start Gaussian regression arithmetic produces the first prediction ca.
 Exact checked proposition: forall c a, sequential_prediction 1 c a = c * a.
 Premises and side conditions: The scalar regression formula is adopted as a definition; Gaussian derivation remains a separate prerequisite.
 Proof/definition method: Reduce r=1 and cancel its unit denominator using the field tactic.
 Library reuse: Stdlib.Reals, Stdlib.Lra, Stdlib.Psatz; previously checked sequential real identities.
 Boundary: Exact real-algebraic identity only; no Gaussian conditional distribution or empirical IQ model is established.
 *)
Theorem sequential_prediction_single_start :
  forall c a, sequential_prediction 1 c a = c * a.
Proof.
  intros c a; unfold sequential_prediction, sequential_d; field.
Qed.

(**
 [sequential_prediction_recursive_fixed_point] (theorem) — The report's recursive conditional prediction is a fixed point, including after any number of previously fixed predictions.
 Mathematical meaning: The report's recursive conditional prediction is a fixed point, including after any number of previously fixed predictions.
 Exact checked proposition: forall r j c a, sequential_d r c <> 0 -> sequential_d (r+j) c <> 0 -> c * (r * a + j * sequential_prediction r c a) / sequential_d (r+j) c = sequential_prediction r c a.
 Premises and side conditions: Both current and updated denominators are nonzero; interpreted in the Gaussian report only after separate conditional-regression hypotheses.
 Proof/definition method: Exact common-denominator cancellation and real field normalization.
 Library reuse: sequential_denominator_add, Stdlib.Field.
 Boundary: Verifies the deterministic recursion step assuming the regression coefficient; does not prove Gaussian conditioning.
 *)
Theorem sequential_prediction_recursive_fixed_point :
  forall r j c a,
  sequential_d r c <> 0 ->
  sequential_d (r+j) c <> 0 ->
  c * (r * a + j * sequential_prediction r c a) / sequential_d (r+j) c = sequential_prediction r c a.
Proof.
  intros r j c a Hdr Hnext.
  unfold sequential_prediction, sequential_d in *.
  field; nra.
Qed.

(**
 [sequential_inclusive_mean_closed_form] (theorem) — The inclusive average of r observed scores and k equal predictions has the exact closed form in the sequential report.
 Mathematical meaning: The inclusive average of r observed scores and k equal predictions has the exact closed form in the sequential report.
 Exact checked proposition: forall r k c a, sequential_d r c <> 0 -> r+k <> 0 -> sequential_inclusive_mean r k c a = r * sequential_d (r+k) c * a / ((r+k) * sequential_d r c).
 Premises and side conditions: Nonzero initial-regression denominator and total score count; the Gaussian prediction relation is a separate model assumption.
 Proof/definition method: Combine arithmetic and cancel the common denominator using Stdlib.Field.
 Library reuse: Stdlib.Reals, Stdlib.Lra, Stdlib.Psatz; previously checked sequential real identities.
 Boundary: Exact real-algebraic identity only; no Gaussian conditional distribution or empirical IQ model is established.
 *)
Theorem sequential_inclusive_mean_closed_form :
  forall r k c a,
  sequential_d r c <> 0 ->
  r+k <> 0 ->
  sequential_inclusive_mean r k c a = r * sequential_d (r+k) c * a / ((r+k) * sequential_d r c).
Proof.
  intros r k c a Hdr Hn.
  unfold sequential_inclusive_mean, sequential_prediction, sequential_d in *.
  field; nra.
Qed.

(**
 [sequential_mean_single_start] (theorem) — With one initial score, the average is (1+kc)a/(1+k), including the initial score.
 Mathematical meaning: With one initial score, the average is (1+kc)a/(1+k), including the initial score.
 Exact checked proposition: forall k c a, 1 + k <> 0 -> sequential_inclusive_mean 1 k c a = sequential_d (1+k) c * a / (1+k).
 Premises and side conditions: The total score count 1+k must be nonzero; c and a arbitrary.
 Proof/definition method: Specialize the general inclusive-mean theorem at r=1 and simplify the unit denominator.
 Library reuse: sequential_inclusive_mean_closed_form, sequential_denominator_one, Stdlib.Ring.
 Boundary: Exact real-algebraic identity only; no Gaussian conditional distribution or empirical IQ model is established.
 *)
Theorem sequential_mean_single_start :
  forall k c a, 1 + k <> 0 ->
  sequential_inclusive_mean 1 k c a = sequential_d (1+k) c * a / (1+k).
Proof.
  intros k c a Hn.
  pose proof (sequential_inclusive_mean_closed_form 1 k c a) as H.
  assert (Hone : sequential_d 1 c <> 0).
  { rewrite sequential_denominator_one; lra. }
  specialize (H Hone Hn).
  rewrite sequential_denominator_one in H.
  rewrite H.
  field; exact Hn.
Qed.

(**
 [sequential_prediction_two_starts] (theorem) — For two equal initial scores, every recursive prediction is 2ca/(1+c).
 Mathematical meaning: For two equal initial scores, every recursive prediction is 2ca/(1+c).
 Exact checked proposition: forall c a, 1+c <> 0 -> sequential_prediction 2 c a = 2*c*a/(1+c).
 Premises and side conditions: The two-observation regression denominator 1+c is nonzero.
 Proof/definition method: Direct specialization of the generic prediction formula, normalized by Field.
 Library reuse: Stdlib.Reals, Stdlib.Lra, Stdlib.Psatz; previously checked sequential real identities.
 Boundary: Exact real-algebraic identity only; no Gaussian conditional distribution or empirical IQ model is established.
 *)
Theorem sequential_prediction_two_starts :
  forall c a, 1+c <> 0 ->
  sequential_prediction 2 c a = 2*c*a/(1+c).
Proof.
  intros c a Hd; unfold sequential_prediction, sequential_d in *; field; nra.
Qed.

(**
 [sequential_prediction_three_starts] (theorem) — For three equal initial scores, every recursive prediction is 3ca/(1+2c).
 Mathematical meaning: For three equal initial scores, every recursive prediction is 3ca/(1+2c).
 Exact checked proposition: forall c a, 1+2*c <> 0 -> sequential_prediction 3 c a = 3*c*a/(1+2*c).
 Premises and side conditions: The three-observation regression denominator 1+2c is nonzero.
 Proof/definition method: Direct specialization of the generic prediction formula, normalized by Field.
 Library reuse: Stdlib.Reals, Stdlib.Lra, Stdlib.Psatz; previously checked sequential real identities.
 Boundary: Exact real-algebraic identity only; no Gaussian conditional distribution or empirical IQ model is established.
 *)
Theorem sequential_prediction_three_starts :
  forall c a, 1+2*c <> 0 ->
  sequential_prediction 3 c a = 3*c*a/(1+2*c).
Proof.
  intros c a Hd; unfold sequential_prediction, sequential_d in *; field; nra.
Qed.

(**
 [sequential_mean_two_starts] (theorem) — The two-start inclusive mean matches the exact rational formula displayed as cor:two-starts.
 Mathematical meaning: The two-start inclusive mean matches the exact rational formula displayed as cor:two-starts.
 Exact checked proposition: forall k c a, 1+c <> 0 -> 2+k <> 0 -> sequential_inclusive_mean 2 k c a = 2*(1+(k+1)*c)*a/((k+2)*(1+c)).
 Premises and side conditions: Nonzero initial conditioning denominator and total score count.
 Proof/definition method: Expand the two-start regression and normalize the rational arithmetic using Field.
 Library reuse: Stdlib.Reals, Stdlib.Lra, Stdlib.Psatz; previously checked sequential real identities.
 Boundary: Exact real-algebraic identity only; no Gaussian conditional distribution or empirical IQ model is established.
 *)
Theorem sequential_mean_two_starts :
  forall k c a, 1+c <> 0 -> 2+k <> 0 ->
  sequential_inclusive_mean 2 k c a = 2*(1+(k+1)*c)*a/((k+2)*(1+c)).
Proof.
  intros k c a Hd Hn.
  unfold sequential_inclusive_mean, sequential_prediction, sequential_d in *.
  field; nra.
Qed.

(**
 [sequential_mean_three_starts] (theorem) — The three-start inclusive mean matches the exact rational formula displayed as cor:three-starts.
 Mathematical meaning: The three-start inclusive mean matches the exact rational formula displayed as cor:three-starts.
 Exact checked proposition: forall k c a, 1+2*c <> 0 -> 3+k <> 0 -> sequential_inclusive_mean 3 k c a = 3*(1+(k+2)*c)*a/((k+3)*(1+2*c)).
 Premises and side conditions: Nonzero three-observation denominator and total score count.
 Proof/definition method: Expand the three-start prediction and normalize the rational arithmetic.
 Library reuse: Stdlib.Reals, Stdlib.Lra, Stdlib.Psatz; previously checked sequential real identities.
 Boundary: Exact real-algebraic identity only; no Gaussian conditional distribution or empirical IQ model is established.
 *)
Theorem sequential_mean_three_starts :
  forall k c a, 1+2*c <> 0 -> 3+k <> 0 ->
  sequential_inclusive_mean 3 k c a = 3*(1+(k+2)*c)*a/((k+3)*(1+2*c)).
Proof.
  intros k c a Hd Hn.
  unfold sequential_inclusive_mean, sequential_prediction, sequential_d in *.
  field; nra.
Qed.

(**
 [sequential_residual_variance_identity] (theorem) — The residual diagonal covariance after r equal-correlation observations factors as (1-c)(1+rc)/d_r.
 Mathematical meaning: The residual diagonal covariance after r equal-correlation observations factors as (1-c)(1+rc)/d_r.
 Exact checked proposition: forall r c, sequential_d r c <> 0 -> 1 - r*c*c/sequential_d r c = (1-c)*(1+r*c)/sequential_d r c.
 Premises and side conditions: Nonzero conditioning block denominator d_r; actual Gaussian residual interpretation requires independent proof.
 Proof/definition method: Cancel the common regression denominator by Field and real ring normalization.
 Library reuse: Stdlib.Reals, Stdlib.Lra, Stdlib.Psatz; previously checked sequential real identities.
 Boundary: Exact real-algebraic identity only; no Gaussian conditional distribution or empirical IQ model is established.
 *)
Theorem sequential_residual_variance_identity :
  forall r c, sequential_d r c <> 0 ->
  1 - r*c*c/sequential_d r c = (1-c)*(1+r*c)/sequential_d r c.
Proof.
  intros r c Hd; unfold sequential_d in *; field; nra.
Qed.

(**
 [sequential_residual_covariance_identity] (theorem) — The residual off-diagonal covariance after conditioning factors as c(1-c)/d_r.
 Mathematical meaning: The residual off-diagonal covariance after conditioning factors as c(1-c)/d_r.
 Exact checked proposition: forall r c, sequential_d r c <> 0 -> c - r*c*c/sequential_d r c = c*(1-c)/sequential_d r c.
 Premises and side conditions: Nonzero d_r; the covariance assignment is conditional on the Gaussian model.
 Proof/definition method: Use algebraic cancellation and the maintained regression denominator.
 Library reuse: Stdlib.Reals, Stdlib.Lra, Stdlib.Psatz; previously checked sequential real identities.
 Boundary: Exact real-algebraic identity only; no Gaussian conditional distribution or empirical IQ model is established.
 *)
Theorem sequential_residual_covariance_identity :
  forall r c, sequential_d r c <> 0 ->
  c - r*c*c/sequential_d r c = c*(1-c)/sequential_d r c.
Proof.
  intros r c Hd; unfold sequential_d in *; field; nra.
Qed.

(**
 [sequential_conditional_variance_from_pairings] (theorem) — Summing all future conditioned residual diagonal and cross terms yields k(1-c)d_{r+k}/((r+k)^2 d_r).
 Mathematical meaning: Summing all future conditioned residual diagonal and cross terms yields k(1-c)d_{r+k}/((r+k)^2 d_r).
 Exact checked proposition: forall r k c, sequential_d r c <> 0 -> r+k <> 0 -> (k*(1-r*c*c/sequential_d r c) + k*(k-1)*(c-r*c*c/sequential_d r c))/((r+k)*(r+k)) = sequential_conditional_variance r k c.
 Premises and side conditions: The regression denominator and sample count are nonzero; Gaussian conditional covariance identities must be established separately.
 Proof/definition method: Collect the k diagonal and k(k-1) off-diagonal terms and simplify with real field identities.
 Library reuse: Stdlib.Reals, Stdlib.Lra, Stdlib.Psatz; previously checked sequential real identities.
 Boundary: Exact real-algebraic identity only; no Gaussian conditional distribution or empirical IQ model is established.
 *)
Theorem sequential_conditional_variance_from_pairings :
  forall r k c,
  sequential_d r c <> 0 -> r+k <> 0 ->
  (k*(1-r*c*c/sequential_d r c) +
     k*(k-1)*(c-r*c*c/sequential_d r c))/((r+k)*(r+k))
     = sequential_conditional_variance r k c.
Proof.
  intros r k c Hdr Hn.
  unfold sequential_conditional_variance, sequential_d in *.
  field; nra.
Qed.

(**
 [sequential_conditional_variance_one_start] (theorem) — With one initial score, the conditional-variance formula is k(1-c)(1+kc)/(k+1)^2.
 Mathematical meaning: With one initial score, the conditional-variance formula is k(1-c)(1+kc)/(k+1)^2.
 Exact checked proposition: forall k c, 1+k <> 0 -> sequential_conditional_variance 1 k c = k*(1-c)*(1+k*c)/((1+k)*(1+k)).
 Premises and side conditions: Total count 1+k nonzero; no Gaussian distribution is constructed by this arithmetic theorem.
 Proof/definition method: Specialize the generic residual variance at r=1 and normalize denominators.
 Library reuse: Stdlib.Reals, Stdlib.Lra, Stdlib.Psatz; previously checked sequential real identities.
 Boundary: Exact real-algebraic identity only; no Gaussian conditional distribution or empirical IQ model is established.
 *)
Theorem sequential_conditional_variance_one_start :
  forall k c, 1+k <> 0 ->
  sequential_conditional_variance 1 k c = k*(1-c)*(1+k*c)/((1+k)*(1+k)).
Proof.
  intros k c Hn; unfold sequential_conditional_variance, sequential_d; field; nra.
Qed.

(**
 [sequential_conditional_variance_lambda_identity] (theorem) — The single-start conditional variance equals lambda_k(1-lambda_k) with lambda_k=(1+kc)/(1+k).
 Mathematical meaning: The single-start conditional variance equals lambda_k(1-lambda_k) with lambda_k=(1+kc)/(1+k).
 Exact checked proposition: forall k c, 1+k <> 0 -> sequential_conditional_variance 1 k c = (sequential_d (1+k) c /(1+k)) * (1 - sequential_d (1+k) c /(1+k)).
 Premises and side conditions: Only total count nonzero; positivity of the variance requires admissible correlation hypotheses.
 Proof/definition method: Use a single real field identity rather than re-derive stochastic conditioning.
 Library reuse: Stdlib.Reals, Stdlib.Lra, Stdlib.Psatz; previously checked sequential real identities.
 Boundary: Exact real-algebraic identity only; no Gaussian conditional distribution or empirical IQ model is established.
 *)
Theorem sequential_conditional_variance_lambda_identity :
  forall k c, 1+k <> 0 ->
  sequential_conditional_variance 1 k c =
    (sequential_d (1+k) c /(1+k)) *
    (1 - sequential_d (1+k) c /(1+k)).
Proof.
  intros k c Hn;
  unfold sequential_conditional_variance, sequential_d;
  field; nra.
Qed.

(**
 [sequential_prediction_independence_limit] (theorem) — The independent-tests boundary gives zero subsequent prediction in the arithmetic regression.
 Mathematical meaning: The independent-tests boundary gives zero subsequent prediction in the arithmetic regression.
 Exact checked proposition: forall r a, sequential_prediction r 0 a = 0.
 Premises and side conditions: Correlation c=0; d_r=1 for all real counts.
 Proof/definition method: Evaluate the closed-form prediction at zero correlation.
 Library reuse: Stdlib.Reals, Stdlib.Lra, Stdlib.Psatz; previously checked sequential real identities.
 Boundary: Exact real-algebraic identity only; no Gaussian conditional distribution or empirical IQ model is established.
 *)
Theorem sequential_prediction_independence_limit :
  forall r a, sequential_prediction r 0 a = 0.
Proof.
  intros r a; unfold sequential_prediction, sequential_d; field.
Qed.

(**
 [sequential_mean_independence_limit] (theorem) — With independent tests, the inclusive average is the observed initial-sum contribution ra/(r+k).
 Mathematical meaning: With independent tests, the inclusive average is the observed initial-sum contribution ra/(r+k).
 Exact checked proposition: forall r k a, r+k <> 0 -> sequential_inclusive_mean r k 0 a = r*a/(r+k).
 Premises and side conditions: Total count nonzero; regression predictions vanish at c=0.
 Proof/definition method: Specialize the exact mean and normalize its independent-test boundary.
 Library reuse: Stdlib.Reals, Stdlib.Lra, Stdlib.Psatz; previously checked sequential real identities.
 Boundary: Exact real-algebraic identity only; no Gaussian conditional distribution or empirical IQ model is established.
 *)
Theorem sequential_mean_independence_limit :
  forall r k a, r+k <> 0 ->
  sequential_inclusive_mean r k 0 a = r*a/(r+k).
Proof.
  intros r k a Hn; unfold sequential_inclusive_mean, sequential_prediction, sequential_d; field; nra.
Qed.

(**
 [sequential_mean_perfect_correlation_limit] (theorem) — At perfect correlation and compatible equal-score histories, all predictions equal a and so does the inclusive mean.
 Mathematical meaning: At perfect correlation and compatible equal-score histories, all predictions equal a and so does the inclusive mean.
 Exact checked proposition: forall r k a, r <> 0 -> r+k <> 0 -> sequential_inclusive_mean r k 1 a = a.
 Premises and side conditions: Nonzero r and total count; c=1, only compatible histories make probabilistic sense.
 Proof/definition method: Cancel r and r+k via the real field normalizer.
 Library reuse: Stdlib.Reals, Stdlib.Lra, Stdlib.Psatz; previously checked sequential real identities.
 Boundary: Exact real-algebraic identity only; no Gaussian conditional distribution or empirical IQ model is established.
 *)
Theorem sequential_mean_perfect_correlation_limit :
  forall r k a, r <> 0 -> r+k <> 0 ->
  sequential_inclusive_mean r k 1 a = a.
Proof.
  intros r k a Hr Hn;
  unfold sequential_inclusive_mean, sequential_prediction, sequential_d;
  field; nra.
Qed.

(**
 [sequential_conditional_variance_perfect_correlation] (theorem) — At perfect correlation the defined conditional residual-variance formula vanishes.
 Mathematical meaning: At perfect correlation the defined conditional residual-variance formula vanishes.
 Exact checked proposition: forall r k, sequential_conditional_variance r k 1 = 0.
 Premises and side conditions: Correlation parameter c=1; no division-premise is needed for the algebraic total expression.
 Proof/definition method: Use the explicit zero factor without assuming an inverse is nonzero.
 Library reuse: Stdlib.Reals, Stdlib.Lra, Stdlib.Psatz; previously checked sequential real identities.
 Boundary: Exact real-algebraic identity only; no Gaussian conditional distribution or empirical IQ model is established.
 *)
Theorem sequential_conditional_variance_perfect_correlation :
  forall r k, sequential_conditional_variance r k 1 = 0.
Proof.
  intros r k; unfold sequential_conditional_variance;
  replace (1-1) with 0 by ring;
  unfold Rdiv; ring.
Qed.

(**
 [sequential_conditional_variance_singular_boundary] (theorem) — At the singular lower-correlation boundary, zero total variance factor forces the conditional-variance formula to vanish.
 Mathematical meaning: At the singular lower-correlation boundary, zero total variance factor forces the conditional-variance formula to vanish.
 Exact checked proposition: forall r k c, sequential_d (r+k) c = 0 -> sequential_conditional_variance r k c = 0.
 Premises and side conditions: The algebraic hypothesis d_{r+k}=0; admissible Gaussian realization at this endpoint is not proved here.
 Proof/definition method: Rewrite the numerator to zero and use real ring arithmetic.
 Library reuse: Stdlib.Reals, Stdlib.Lra, Stdlib.Psatz; previously checked sequential real identities.
 Boundary: Exact real-algebraic identity only; no Gaussian conditional distribution or empirical IQ model is established.
 *)
Theorem sequential_conditional_variance_singular_boundary :
  forall r k c,
  sequential_d (r+k) c = 0 ->
  sequential_conditional_variance r k c = 0.
Proof.
  intros r k c Hzero; unfold sequential_conditional_variance;
  rewrite Hzero; unfold Rdiv; ring.
Qed.

(**
 [sequential_conditional_variance_nonnegative] (theorem) — The defined conditional variance is nonnegative throughout the algebraically admissible denominator/sign regime.
 Mathematical meaning: The defined conditional variance is nonnegative throughout the algebraically admissible denominator/sign regime.
 Exact checked proposition: forall r k c, 0 <= k -> c <= 1 -> 0 <= sequential_d (r+k) c -> 0 < r+k -> 0 < sequential_d r c -> 0 <= sequential_conditional_variance r k c.
 Premises and side conditions: k>=0, c<=1, d_{r+k}>=0, total count>0 and d_r>0; these are explicit and do not assert a Gaussian law.
 Proof/definition method: Apply Stdlib's nonnegative product and inverse-positive lemmas.
 Library reuse: Rmult_le_pos, Rinv_0_lt_compat, Stdlib.Psatz.nra.
 Boundary: Exact real-algebraic identity only; no Gaussian conditional distribution or empirical IQ model is established.
 *)
Theorem sequential_conditional_variance_nonnegative :
  forall r k c,
  0 <= k -> c <= 1 -> 0 <= sequential_d (r+k) c ->
  0 < r+k -> 0 < sequential_d r c ->
  0 <= sequential_conditional_variance r k c.
Proof.
  intros r k c Hk Hc Htotal Hn Hdr.
  unfold sequential_conditional_variance.
  unfold Rdiv.
  apply Rmult_le_pos.
  - apply Rmult_le_pos.
    + apply Rmult_le_pos; [exact Hk | lra].
    + exact Htotal.
  - apply Rlt_le, Rinv_0_lt_compat.
    apply Rmult_lt_0_compat.
    + apply Rmult_lt_0_compat; exact Hn.
    + exact Hdr.
Qed.

(**
 [sequential_iq_start_standardized] (theorem) — The IQ 150 observation on an SD-15 scale corresponds exactly to standardized a=10/3.
 Mathematical meaning: The IQ 150 observation on an SD-15 scale corresponds exactly to standardized a=10/3.
 Exact checked proposition: (150-100)/15 = (10/3 : R).
 Premises and side conditions: The reporting scale is defined as IQ=100+15X.
 Proof/definition method: Normalize exact rational arithmetic rather than rely on rounded decimals.
 Library reuse: Stdlib.Reals, Stdlib.Lra, Stdlib.Psatz; previously checked sequential real identities.
 Boundary: Exact real-algebraic identity only; no Gaussian conditional distribution or empirical IQ model is established.
 *)
Theorem sequential_iq_start_standardized :
  (150-100)/15 = (10/3 : R).
Proof.
  field.
Qed.

(**
 [sequential_iq_prediction_exact] (theorem) — At c=3/5 and standardized a=10/3, the predicted IQ is exactly 100+150r/(3r+2).
 Mathematical meaning: At c=3/5 and standardized a=10/3, the predicted IQ is exactly 100+150r/(3r+2).
 Exact checked proposition: forall r, 3*r+2 <> 0 -> 100+15*sequential_prediction r (3/5) (10/3) = 100 + 150*r/(3*r+2).
 Premises and side conditions: Nonzero transformed regression denominator 3r+2; the input c is a model parameter.
 Proof/definition method: Use exact rational normalization of the IQ scale and closed-form regression.
 Library reuse: Stdlib.Reals, Stdlib.Lra, Stdlib.Psatz; previously checked sequential real identities.
 Boundary: Exact real-algebraic identity only; no Gaussian conditional distribution or empirical IQ model is established.
 *)
Theorem sequential_iq_prediction_exact :
  forall r, 3*r+2 <> 0 ->
  100+15*sequential_prediction r (3/5) (10/3) =
  100 + 150*r/(3*r+2).
Proof.
  intros r Hd; unfold sequential_prediction, sequential_d; field; nra.
Qed.

(**
 [sequential_iq_mean_exact] (theorem) — The IQ 150 inclusive-mean certificate matches the report's exact 100+50r(3N+2)/(N(3r+2)).
 Mathematical meaning: The IQ 150 inclusive-mean certificate matches the report's exact 100+50r(3N+2)/(N(3r+2)).
 Exact checked proposition: forall r k, 3*r+2 <> 0 -> r+k <> 0 -> 100+15*sequential_inclusive_mean r k (3/5) (10/3) = 100+50*r*(3*(r+k)+2)/((r+k)*(3*r+2)).
 Premises and side conditions: c=3/5, a=10/3, nonzero d_r and total count; no floating-point assumption.
 Proof/definition method: Normalize the full scaled recursive average directly with Stdlib.Field.
 Library reuse: Stdlib.Reals, Stdlib.Lra, Stdlib.Psatz; previously checked sequential real identities.
 Boundary: Exact real-algebraic identity only; no Gaussian conditional distribution or empirical IQ model is established.
 *)
Theorem sequential_iq_mean_exact :
  forall r k, 3*r+2 <> 0 -> r+k <> 0 ->
  100+15*sequential_inclusive_mean r k (3/5) (10/3) =
  100+50*r*(3*(r+k)+2)/((r+k)*(3*r+2)).
Proof.
  intros r k Hdr Hn;
  unfold sequential_inclusive_mean, sequential_prediction, sequential_d.
  field; nra.
Qed.

(**
 [sequential_iq_population_variance_exact] (theorem) — The exact IQ-scale population variance is 45(3N+2)/N at c=3/5 and SD 15.
 Mathematical meaning: The exact IQ-scale population variance is 45(3N+2)/N at c=3/5 and SD 15.
 Exact checked proposition: forall n, n <> 0 -> 225 * sequential_population_variance n (3/5) = 45*(3*n+2)/n.
 Premises and side conditions: Nonzero number of tests N; covariance model is an explicit premise.
 Proof/definition method: Convert the normalized population variance by factor 15²=225 and cancel exact rational factors.
 Library reuse: Stdlib.Reals, Stdlib.Lra, Stdlib.Psatz; previously checked sequential real identities.
 Boundary: Exact real-algebraic identity only; no Gaussian conditional distribution or empirical IQ model is established.
 *)
Theorem sequential_iq_population_variance_exact :
  forall n, n <> 0 ->
  225 * sequential_population_variance n (3/5) = 45*(3*n+2)/n.
Proof.
  intros n Hn; unfold sequential_population_variance, sequential_d;
  field; nra.
Qed.

(**
 [sequential_iq_conditional_variance_exact] (theorem) — The exact IQ-scale conditional variance certificate is 90k(3N+2)/(N²(3r+2)).
 Mathematical meaning: The exact IQ-scale conditional variance certificate is 90k(3N+2)/(N²(3r+2)).
 Exact checked proposition: forall r k, 3*r+2 <> 0 -> r+k <> 0 -> 225 * sequential_conditional_variance r k (3/5) = 90*k*(3*(r+k)+2)/((r+k)*(r+k)*(3*r+2)).
 Premises and side conditions: c=3/5, SD=15, nonzero conditioning denominator and total count; the Gaussian conditioning theorem is a distinct prerequisite.
 Proof/definition method: Scale the already specified conditional variance by 225 and verify a real field identity.
 Library reuse: Stdlib.Reals, Stdlib.Lra, Stdlib.Psatz; previously checked sequential real identities.
 Boundary: Exact real-algebraic identity only; no Gaussian conditional distribution or empirical IQ model is established.
 *)
Theorem sequential_iq_conditional_variance_exact :
  forall r k, 3*r+2 <> 0 -> r+k <> 0 ->
  225 * sequential_conditional_variance r k (3/5) =
    90*k*(3*(r+k)+2)/((r+k)*(r+k)*(3*r+2)).
Proof.
  intros r k Hdr Hn; unfold sequential_conditional_variance, sequential_d; field; nra.
Qed.

(**
 [sequential_recursive_history_sum] (fixpoint) —
 The total history after a prescribed number of recursive predictions.
 Mathematical meaning: Begin with the r identical observed scores, whose
 sum is r*a, and iteratively add the next prediction given by the
 equicorrelation scalar-regression formula.
 Exact declaration: T_0=r*a and T_(j+1)=T_j+c*T_j/d_(r+j).
 Premises and side conditions: Natural number j counts subsequent predictions;
 r,c,a are real parameters; denominators need not be nonzero to define
 the expression, but later theorems require the relevant nonzero hypotheses.
 Proof/definition method: Structurally recursive on the natural history count
 using standard Rocq recursion, not a custom finite-list sum.
 Library reuse: Stdlib.Init.Nat, Stdlib.Reals.INR and sequential_d.
 Boundary: The conditional regression coefficient is a stated arithmetic
 input; this does not prove any Gaussian conditional distribution.
 *)
Fixpoint sequential_recursive_history_sum (j : nat) (r c a : R) : R :=
  match j with
  | O => r * a
  | S n =>
      let previous := sequential_recursive_history_sum n r c a in
      previous + c * previous / sequential_d (r + INR n) c
  end.

(**
 [sequential_recursive_next_score] (definition) —
 The next scalar prediction following a finite recursive history.
 Mathematical meaning: The regression rule is evaluated at the complete
 history of initial scores and earlier recursive predictions.
 Exact declaration: e_(j+1)=c*T_j/d_(r+j), with T_j the canonical history sum.
 Premises and side conditions: A natural-number history count and real-valued
 count, correlation, and observed score; interpretation requires a nonzero
 regression denominator, proved explicitly in later theorems.
 Proof/definition method: A transparent application of the checked history
 function and the previously specified denominator; no auxiliary matrix,
 probabilistic axiom or bespoke finite-sum implementation is introduced.
 Library reuse: sequential_recursive_history_sum, sequential_d, Stdlib.Reals.INR.
 Boundary: This is not a conditional-expectation construction.
 *)
Definition sequential_recursive_next_score (j : nat) (r c a : R) : R :=
  c * sequential_recursive_history_sum j r c a /
    sequential_d (r + INR j) c.

(**
 [sequential_recursive_history_sum_closed_form] (theorem) — The complete recursively generated scalar history has a closed form for every natural number of later predictions.
 Mathematical meaning: The complete recursively generated scalar history has a closed form for every natural number of later predictions.
 Exact checked proposition: forall j r c a, sequential_d r c <> 0 -> (forall n, (n < j)%nat -> sequential_d (r + INR n) c <> 0) -> sequential_recursive_history_sum j r c a = r * a + INR j * sequential_prediction r c a.
 Premises and side conditions: Nonzero initial denominator and all previous recursive denominators; every history length is a natural number.
 Proof/definition method: Induct on j and use the previously checked fixed-point identity to close the successor case.
 Library reuse: Stdlib.Lia, Stdlib.Reals.S_INR, sequential_prediction_recursive_fixed_point.
 Boundary: Deterministic recursive algebra only; the Gaussian conditioning
 interpretation depends on the report's separately stated distribution model
 and its currently unformalized conditional-expectation theorem.
 *)
Theorem sequential_recursive_history_sum_closed_form :
  forall j r c a,
   sequential_d r c <> 0 ->
   (forall n, (n < j)%nat -> sequential_d (r + INR n) c <> 0) ->
   sequential_recursive_history_sum j r c a =
     r * a + INR j * sequential_prediction r c a.
Proof.
 induction j as [|j IH]; intros r c a Hdr Hall.
 - simpl [sequential_recursive_history_sum].
   simpl.
   ring.
 - assert (Hprev :
     sequential_recursive_history_sum j r c a =
       r*a + INR j * sequential_prediction r c a).
   { apply IH.
     + exact Hdr.
     + intros n Hlt; apply Hall; lia. }
   change
     (sequential_recursive_history_sum j r c a +
       c * sequential_recursive_history_sum j r c a /
         sequential_d (r + INR j) c =
      r * a + INR (S j) * sequential_prediction r c a).
   rewrite Hprev.
   rewrite S_INR.
   assert (Hstep : sequential_d (r + INR j) c <> 0).
   { apply Hall; lia. }
   rewrite (sequential_prediction_recursive_fixed_point
     r (INR j) c a Hdr Hstep).
   ring.
Qed.

(**
 [sequential_recursive_prediction_constant] (theorem) — Every next prediction generated by the entire recursive history equals the same exact closed-form value.
 Mathematical meaning: Every next prediction generated by the entire recursive history equals the same exact closed-form value.
 Exact checked proposition: forall j r c a, sequential_d r c <> 0 -> (forall n, (n <= j)%nat -> sequential_d (r + INR n) c <> 0) -> sequential_recursive_next_score j r c a = sequential_prediction r c a.
 Premises and side conditions: Nonzero initial and each intermediate regression denominator through step j.
 Proof/definition method: Rewrite the entire history using its inductive closed form and reuse scalar regression fixed-point uniqueness.
 Library reuse: sequential_recursive_history_sum_closed_form, sequential_prediction_recursive_fixed_point.
 Boundary: Deterministic recursive algebra only; the Gaussian conditioning
 interpretation depends on the report's separately stated distribution model
 and its currently unformalized conditional-expectation theorem.
 *)
Theorem sequential_recursive_prediction_constant :
  forall j r c a,
   sequential_d r c <> 0 ->
   (forall n, (n <= j)%nat -> sequential_d (r + INR n) c <> 0) ->
   sequential_recursive_next_score j r c a =
     sequential_prediction r c a.
Proof.
 intros j r c a Hdr Hall.
 unfold sequential_recursive_next_score.
 assert (Hsum :
   sequential_recursive_history_sum j r c a =
     r*a + INR j * sequential_prediction r c a).
 { apply sequential_recursive_history_sum_closed_form.
   - exact Hdr.
   - intros n Hlt; apply Hall; lia. }
 rewrite Hsum.
 apply sequential_prediction_recursive_fixed_point.
 - exact Hdr.
 - apply Hall; lia.
Qed.

(**
 [sequential_recursive_inclusive_mean_closed_form] (theorem) — Dividing the actual recursive history sum by its count yields exactly the inclusive score average in the report.
 Mathematical meaning: Dividing the actual recursive history sum by its count yields exactly the inclusive score average in the report.
 Exact checked proposition: forall k r c a, sequential_d r c <> 0 -> (forall n, (n < k)%nat -> sequential_d (r + INR n) c <> 0) -> r + INR k <> 0 -> sequential_recursive_history_sum k r c a / (r + INR k) = sequential_inclusive_mean r (INR k) c a.
 Premises and side conditions: Nonzero initial and previous regression denominators and positive/nonzero total count.
 Proof/definition method: Rewrite by natural induction and compare two definitionally equal expressions.
 Library reuse: sequential_recursive_history_sum_closed_form, sequential_inclusive_mean.
 Boundary: Deterministic recursive algebra only; the Gaussian conditioning
 interpretation depends on the report's separately stated distribution model
 and its currently unformalized conditional-expectation theorem.
 *)
Theorem sequential_recursive_inclusive_mean_closed_form :
  forall k r c a,
   sequential_d r c <> 0 ->
   (forall n, (n < k)%nat -> sequential_d (r + INR n) c <> 0) ->
   r + INR k <> 0 ->
   sequential_recursive_history_sum k r c a / (r + INR k) =
     sequential_inclusive_mean r (INR k) c a.
Proof.
 intros k r c a Hdr Hall Hcount.
 rewrite (sequential_recursive_history_sum_closed_form
   k r c a Hdr Hall).
 unfold sequential_inclusive_mean.
 reflexivity.
Qed.

(**
 [sequential_recursive_single_start_predictions_constant] (theorem) — Every future score in the single-start recursion equals c*a, for an arbitrary finite history length.
 Mathematical meaning: Every future score in the single-start recursion equals c*a, for an arbitrary finite history length.
 Exact checked proposition: forall j c a, (forall n, (n <= j)%nat -> sequential_d (1 + INR n) c <> 0) -> sequential_recursive_next_score j 1 c a = c * a.
 Premises and side conditions: Nonzero denominators through j; no Gaussian distribution has been constructed.
 Proof/definition method: Specialize the inductive constant-prediction result to one observed score.
 Library reuse: sequential_recursive_prediction_constant, sequential_prediction_single_start.
 Boundary: Deterministic recursive algebra only; the Gaussian conditioning
 interpretation depends on the report's separately stated distribution model
 and its currently unformalized conditional-expectation theorem.
 *)
Theorem sequential_recursive_single_start_predictions_constant :
  forall j c a,
   (forall n, (n <= j)%nat -> sequential_d (1 + INR n) c <> 0) ->
   sequential_recursive_next_score j 1 c a = c * a.
Proof.
 intros j c a Hall.
 assert (Hone : sequential_d 1 c <> 0).
 { rewrite sequential_denominator_one; lra. }
 rewrite (sequential_recursive_prediction_constant j 1 c a Hone Hall).
 apply sequential_prediction_single_start.
Qed.

(**
 [sequential_recursive_nonnegative_correlation_denominators_positive] (theorem) — Every finite regression denominator stays positive if there is at least one initial score and correlations are nonnegative.
 Mathematical meaning: Every finite regression denominator stays positive if there is at least one initial score and correlations are nonnegative.
 Exact checked proposition: forall j r c, 1 <= r -> 0 <= c -> 0 < sequential_d (r + INR j) c.
 Premises and side conditions: At least one observed score and c>=0; negative correlations require the full domain inequalities.
 Proof/definition method: Prove natural-to-real count nonnegativity by Rocq induction, then reuse denominator positivity.
 Library reuse: Stdlib.Reals.S_INR, sequential_denominator_positive_nonnegative_correlation.
 Boundary: Deterministic recursive algebra only; the Gaussian conditioning
 interpretation depends on the report's separately stated distribution model
 and its currently unformalized conditional-expectation theorem.
 *)
Theorem sequential_recursive_nonnegative_correlation_denominators_positive :
  forall j r c, 1 <= r -> 0 <= c ->
   0 < sequential_d (r + INR j) c.
Proof.
 intros j r c Hr Hc.
 assert (Hnat : 0 <= INR j).
 { induction j as [|j IH].
   - simpl; lra.
   - rewrite S_INR; lra. }
 apply sequential_denominator_positive_nonnegative_correlation; lra.
Qed.

(**
 [sequential_recursive_history_nonnegative_correlation] (theorem) — The full history sum has its closed form without any individual denominator premises in the c>=0 regime.
 Mathematical meaning: The full history sum has its closed form without any individual denominator premises in the c>=0 regime.
 Exact checked proposition: forall j r c a, 1 <= r -> 0 <= c -> sequential_recursive_history_sum j r c a = r*a + INR j * sequential_prediction r c a.
 Premises and side conditions: Real initial score count at least one and nonnegative correlation; the proof does not assume Gaussianity.
 Proof/definition method: Compose full-history induction with the checked positivity of every prefix denominator.
 Library reuse: sequential_recursive_history_sum_closed_form, sequential_recursive_nonnegative_correlation_denominators_positive.
 Boundary: Deterministic recursive algebra only; the Gaussian conditioning
 interpretation depends on the report's separately stated distribution model
 and its currently unformalized conditional-expectation theorem.
 *)
Theorem sequential_recursive_history_nonnegative_correlation :
  forall j r c a, 1 <= r -> 0 <= c ->
   sequential_recursive_history_sum j r c a =
     r*a + INR j * sequential_prediction r c a.
Proof.
 intros j r c a Hr Hc.
 apply sequential_recursive_history_sum_closed_form.
 - pose proof
     (sequential_denominator_positive_nonnegative_correlation
       r c Hr Hc) as Hpositive.
   lra.
 - intros n Hlt.
   pose proof
     (sequential_recursive_nonnegative_correlation_denominators_positive
       n r c Hr Hc) as Hpositive.
   lra.
Qed.


(**
 [sequential_rounding_grid_separation] (theorem) — Distinct integer grid indices differ by at least one unit in one of the two real order directions.
 Mathematical meaning: Distinct integer grid indices differ by at least one unit in one of the two real order directions.
 Exact checked proposition: j<>t implies IZR j <= IZR t-1 or IZR t+1<=IZR j.
 Premises and side conditions: Arbitrary integers j,t; no statistical or decimal assumptions.
 Proof/definition method: Split integer order with Z_lt_ge_dec and transfer inequalities using Stdlib ZArith IZR_le.
 Library reuse: Stdlib.ZArith, Stdlib.Lia, Stdlib.Reals.
 Boundary: Elementary grid geometry, not a rounding certificate for a specific reported decimal.
 *)
Theorem sequential_rounding_grid_separation :
  forall t j : Z, j <> t ->
  IZR j <= IZR t - 1 \/ IZR t + 1 <= IZR j.
Proof.
  intros t j Hneq.
  destruct (Z_lt_ge_dec j t) as [Hlt|Hge].
  - left.
    assert (Hz : (j <= t - 1)%Z) by lia.
    apply IZR_le in Hz.
    rewrite minus_IZR in Hz.
    simpl in Hz.
    lra.
  - right.
    assert (Hz : (t + 1 <= j)%Z) by lia.
    apply IZR_le in Hz.
    rewrite plus_IZR in Hz.
    simpl in Hz.
    lra.
Qed.

(**
 [sequential_rounding_strict_midpoint_unique] (theorem) — A real number strictly between two adjacent midpoint boundaries has strictly smaller squared scaled error to its proposed grid index than to every other integer.
 Mathematical meaning: A real number strictly between two adjacent midpoint boundaries has strictly smaller squared scaled error to its proposed grid index than to every other integer.
 Exact checked proposition: If t-1/2<T*x<t+1/2 and j<>t then (T*x-t)^2<(T*x-j)^2.
 Premises and side conditions: T>0; t,j integer; the scaled target lies strictly inside the target rounding cell.
 Proof/definition method: Use the integer grid-separation lemma, then elementary polynomial order to compare squared errors; no numerical approximations.
 Library reuse: sequential_rounding_grid_separation, Stdlib.Psatz.nra.
 Boundary: States uniqueness by squared error, which is equivalent to Euclidean nearest-grid-point ordering at positive scale.
 *)
Theorem sequential_rounding_strict_midpoint_unique :
  forall T x : R, forall t j : Z,
  0 < T -> j <> t ->
  2 * IZR t - 1 < 2 * T * x ->
  2 * T * x < 2 * IZR t + 1 ->
  (T*x-IZR t)*(T*x-IZR t) <
  (T*x-IZR j)*(T*x-IZR j).
Proof.
  intros T x t j HT Hneq Hlower Hupper.
  destruct (sequential_rounding_grid_separation t j Hneq)
    as [Hleft|Hright]; nra.
Qed.

(**
 [sequential_rounding_rational_certificate_unique] (theorem) — A strictly positive exact rational midpoint certificate implies the stated decimal grid point is the unique nearest candidate by squared distance.
 Mathematical meaning: A strictly positive exact rational midpoint certificate implies the stated decimal grid point is the unique nearest candidate by squared distance.
 Exact checked proposition: Q>0, T>0 and Q-2|TP-tQ|>0 imply the t-grid error is strictly smaller than every j<>t.
 Premises and side conditions: P,Q,T real-valued exact rational numerator, positive denominator and positive grid scale; t,j integer; this formulation can be instantiated with IZR numerator/denominator.
 Proof/definition method: Convert the strict absolute-value certificate to its exact open midpoint interval, cancel Q using the field tactic, and apply the universal rounding cell theorem.
 Library reuse: Stdlib.Reals.Rabs_lt, Stdlib.Field, sequential_rounding_strict_midpoint_unique.
 Boundary: Pure rational rounding; actual rounded decimals require individually checked positive certificate inputs.
 *)
Theorem sequential_rounding_rational_certificate_unique :
  forall T P Q : R, forall t j : Z,
  0 < T -> 0 < Q -> j <> t ->
  0 < Q - 2 * Rabs (T*P-IZR t*Q) ->
  (T*(P/Q)-IZR t)*(T*(P/Q)-IZR t) <
  (T*(P/Q)-IZR j)*(T*(P/Q)-IZR j).
Proof.
  intros T P Q t j HT HQ Hneq Hcertificate.
  assert (Habs : Rabs (T*P-IZR t*Q) < Q/2) by lra.
  apply Rabs_lt in Habs.
  destruct Habs as [Habslo Habshi].
  assert (Hdiv : T*(P/Q)*Q = T*P).
  { field; lra. }
  apply sequential_rounding_strict_midpoint_unique; try assumption.
  - nra.
  - nra.
Qed.

(**
 [sequential_rounding_sqrt_squared_midpoints] (theorem) — Strict squared upper and lower bounds around a nonnegative variance translate into strict midpoint bounds on its nonnegative standard deviation.
 Mathematical meaning: Strict squared upper and lower bounds around a nonnegative variance translate into strict midpoint bounds on its nonnegative standard deviation.
 Exact checked proposition: 0<=v, 0<T, t>=1 and (2t-1)^2<4T^2v<(2t+1)^2 imply t-1/2<T sqrt(v)<t+1/2.
 Premises and side conditions: Nonnegative real variance, positive real decimal scale, integer index at least one, and strict squared bracket.
 Proof/definition method: Use Stdlib sqrt_sqrt and sqrt_pos; compare squares of nonnegative quantities via nra.
 Library reuse: Stdlib.Reals.sqrt_sqrt, Stdlib.Reals.sqrt_pos, Stdlib.Psatz.nra.
 Boundary: No square-root interpretation of a negative variance; no Gaussian distribution or measurement model is inferred.
 *)
Theorem sequential_rounding_sqrt_squared_midpoints :
  forall T v : R, forall t : Z,
  0 < T -> 0 <= v -> 1 <= IZR t ->
  (2*IZR t-1)*(2*IZR t-1) < 4*T*T*v ->
  4*T*T*v < (2*IZR t+1)*(2*IZR t+1) ->
  2*IZR t-1 < 2*T*sqrt v /\
  2*T*sqrt v < 2*IZR t+1.
Proof.
  intros T v t HT Hv Ht Hlower Hupper.
  pose proof (sqrt_pos v) as Hsqrt.
  pose proof (sqrt_sqrt v Hv) as Hsquare.
  rewrite <- Hsquare in Hlower, Hupper.
  split; nra.
Qed.

(**
 [sequential_rounding_sqrt_certificate_unique] (theorem) — The report's two positive integer square-root certificates prove uniqueness of the nearest rounded standard-deviation grid point.
 Mathematical meaning: The report's two positive integer square-root certificates prove uniqueness of the nearest rounded standard-deviation grid point.
 Exact checked proposition: L=4T^2P-(2t-1)^2Q>0 and U=(2t+1)^2Q-4T^2P>0 imply unique nearest grid index t to sqrt(P/Q).
 Premises and side conditions: T>0, Q>0, P>=0, t>=1 integer, j<>t; all certificates are exact real interpretations of integer comparisons.
 Proof/definition method: Divide the strict squared certificates by positive Q via exact field normalization, derive sqrt midpoint bounds using Stdlib sqrt lemmas, then apply the checked nearest-grid theorem.
 Library reuse: sequential_rounding_sqrt_squared_midpoints, sequential_rounding_strict_midpoint_unique, Stdlib.Field.
 Boundary: Provides general rounding certification; specific report table entries must instantiate its numerator, denominator and certificate inequalities.
 *)
Theorem sequential_rounding_sqrt_certificate_unique :
  forall T P Q : R, forall t j : Z,
  0 < T -> 0 < Q -> 0 <= P -> 1 <= IZR t -> j <> t ->
  0 < 4*T*T*P-(2*IZR t-1)*(2*IZR t-1)*Q ->
  0 < (2*IZR t+1)*(2*IZR t+1)*Q-4*T*T*P ->
  (T*sqrt(P/Q)-IZR t)*(T*sqrt(P/Q)-IZR t) <
  (T*sqrt(P/Q)-IZR j)*(T*sqrt(P/Q)-IZR j).
Proof.
  intros T P Q t j HT HQ HP Ht Hneq HL HU.
  assert (Hdiv : (P/Q)*Q=P).
  { field; lra. }
  assert (Hv : 0 <= P/Q).
  { apply Rdiv_le_0_compat; lra. }
  assert (Hlower : (2*IZR t-1)*(2*IZR t-1) < 4*T*T*(P/Q)).
  { nra. }
  assert (Hupper : 4*T*T*(P/Q) < (2*IZR t+1)*(2*IZR t+1)).
  { nra. }
  destruct (sequential_rounding_sqrt_squared_midpoints
    T (P/Q) t HT Hv Ht Hlower Hupper) as [Hmidlo Hmidhi].
  apply sequential_rounding_strict_midpoint_unique; assumption.
Qed.
