(** Module: UnequalHistoryLinearPrediction.v
 Purpose: Extend the six statistical books' sequential equal-history calculations
 to arbitrary, unequal observed-score totals, cohort perturbations, inclusive
 averages, future-count aggregation, innovations, and affine score baselines.
 Mathematical representation: Exact real algebra with observed score sum s,
 sample count n, correlation c, future horizon k, and realized score x.
 Explicit hypotheses: Equal-correlation linear prediction is the *assumed*
 model; these polynomial linearity identities do not require an invertible
 denominator, because Rocq's total real division is used consistently.
 A regression interpretation does require the positive equicorrelation domain.
 Library use: Reuse the canonical SequentialReport.sequential_d denominator
 and Stdlib Reals/Ring. No custom finite sums, Gaussian kernels, matrices,
 recursive predictions or duplicative conditional-probability definitions.
 Limitations: The results establish exact identities among deterministic
 candidate forecasts, not the Gaussian conditional expectation property,
 existence of a covariance model, independent sampling, or empirical IQ claims.
 Reproduction: Run scripts/compile_rocq.sh under Rocq 9.2 and the
 documentation/source-ownership checks in GitHub Actions.
 AI disclosure: Proof design, documentation and code were AI-assisted;
 only kernel-checked exact propositions count as formally proved.
*)
From Stdlib Require Import Reals Ring Lra Psatz Field.
Require Import SequentialReport.
Open Scope R_scope.

(** [hp] (definition).
 Mathematical meaning: The next-score candidate equicorrelation predictor from the sum of arbitrary observed standardized scores, rather than identical initial scores.
 Exact definition: hp (n c s:R) : R := c*s / sequential_d n c.
 Premises and side conditions: Inputs are real-valued algebraic summaries; a valid
 conditional-Gaussian interpretation separately needs a positive model covariance
 and nonzero denominator. This declaration does not assume sampling independence.
 Proof/definition method: Compose existing equicorrelation denominator algebra.
 Library reuse: SequentialReport.sequential_d and Stdlib real arithmetic;
 no independent summation, regression library, or probabilistic axiom is introduced.
 Boundary: Purely deterministic predictor notation, not a Gaussian law or
 empirical IQ calibration result.
*)
Definition hp (n c s:R) : R := c*s / sequential_d n c.

(** [hf] (definition).
 Mathematical meaning: The predicted sum of k future standardized scores under the same fixed initial history.
 Exact definition: hf (n k c s:R) : R := k*hp n c s.
 Premises and side conditions: Inputs are real-valued algebraic summaries; a valid
 conditional-Gaussian interpretation separately needs a positive model covariance
 and nonzero denominator. This declaration does not assume sampling independence.
 Proof/definition method: Compose existing equicorrelation denominator algebra.
 Library reuse: SequentialReport.sequential_d and Stdlib real arithmetic;
 no independent summation, regression library, or probabilistic axiom is introduced.
 Boundary: Purely deterministic predictor notation, not a Gaussian law or
 empirical IQ calibration result.
*)
Definition hf (n k c s:R) : R := k*hp n c s.

(** [ht] (definition).
 Mathematical meaning: The expected inclusive score total retaining every observed initial test result.
 Exact definition: ht (n k c s:R) : R := s + hf n k c s.
 Premises and side conditions: Inputs are real-valued algebraic summaries; a valid
 conditional-Gaussian interpretation separately needs a positive model covariance
 and nonzero denominator. This declaration does not assume sampling independence.
 Proof/definition method: Compose existing equicorrelation denominator algebra.
 Library reuse: SequentialReport.sequential_d and Stdlib real arithmetic;
 no independent summation, regression library, or probabilistic axiom is introduced.
 Boundary: Purely deterministic predictor notation, not a Gaussian law or
 empirical IQ calibration result.
*)
Definition ht (n k c s:R) : R := s + hf n k c s.

(** [hm] (definition).
 Mathematical meaning: The expected inclusive mean for n prior tests and k future predicted scores.
 Exact definition: hm (n k c s:R) : R := ht n k c s / (n+k).
 Premises and side conditions: Inputs are real-valued algebraic summaries; a valid
 conditional-Gaussian interpretation separately needs a positive model covariance
 and nonzero denominator. This declaration does not assume sampling independence.
 Proof/definition method: Compose existing equicorrelation denominator algebra.
 Library reuse: SequentialReport.sequential_d and Stdlib real arithmetic;
 no independent summation, regression library, or probabilistic axiom is introduced.
 Boundary: Purely deterministic predictor notation, not a Gaussian law or
 empirical IQ calibration result.
*)
Definition hm (n k c s:R) : R := ht n k c s / (n+k).

(** [he] (definition).
 Mathematical meaning: The innovation between a realized future score and its deterministic forecast.
 Exact definition: he (n c s x:R) : R := x - hp n c s.
 Premises and side conditions: Inputs are real-valued algebraic summaries; a valid
 conditional-Gaussian interpretation separately needs a positive model covariance
 and nonzero denominator. This declaration does not assume sampling independence.
 Proof/definition method: Compose existing equicorrelation denominator algebra.
 Library reuse: SequentialReport.sequential_d and Stdlib real arithmetic;
 no independent summation, regression library, or probabilistic axiom is introduced.
 Boundary: Purely deterministic predictor notation, not a Gaussian law or
 empirical IQ calibration result.
*)
Definition he (n c s x:R) : R := x - hp n c s.

(** [hc] (definition).
 Mathematical meaning: The forecast on an affine baseline scale, including IQ-style origin and scale shifts.
 Exact definition: hc (n c s mu:R) : R := mu + hp n c (s-n*mu).
 Premises and side conditions: Inputs are real-valued algebraic summaries; a valid
 conditional-Gaussian interpretation separately needs a positive model covariance
 and nonzero denominator. This declaration does not assume sampling independence.
 Proof/definition method: Compose existing equicorrelation denominator algebra.
 Library reuse: SequentialReport.sequential_d and Stdlib real arithmetic;
 no independent summation, regression library, or probabilistic axiom is introduced.
 Boundary: Purely deterministic predictor notation, not a Gaussian law or
 empirical IQ calibration result.
*)
Definition hc (n c s mu:R) : R := mu + hp n c (s-n*mu).

(** [hp_zero] (theorem).
 Mathematical meaning: A zero-sum standardized history contributes no linear predictor. This establishes general unequal-history next-score linear regression predictor for arbitrary unequal observed-score contributions.
 Exact checked proposition: forall (n c:R), hp n c (0) = 0.
 Premises and side conditions: The proposition compares total real-arithmetic
 expressions with a common equicorrelation conditioning denominator. Under a
 probabilistic interpretation, valid positive covariance-domain and sampling
 premises must be supplied separately; no Gaussian regression theorem is assumed.
 Proof/definition method: Unfold only the canonical linear-forecast wrappers
 and invoke Stdlib Ring for exact polynomial normalization, never floating-point
 experiments or manually duplicated finite-list recursions.
 Library reuse: SequentialReport.sequential_d and Rocq Stdlib Reals/Ring;
 existing definitions are preserved as one authoritative report denominator.
 Boundary: Deterministic linearity/contrast/increment relation only; it does
 not establish distributional conditional expectation or confidence coverage.
*)
Theorem hp_zero : forall (n c:R), hp n c (0) = 0.
Proof.
 intros; unfold hp, hf, ht, hm, he, hc, Rdiv; ring.
Qed.

(** [hp_add] (theorem).
 Mathematical meaning: Combining two score-total contributions is additive at fixed design. This establishes general unequal-history next-score linear regression predictor for arbitrary unequal observed-score contributions.
 Exact checked proposition: forall (n c s t:R), hp n c (s+t) = hp n c (s)+hp n c (t).
 Premises and side conditions: The proposition compares total real-arithmetic
 expressions with a common equicorrelation conditioning denominator. Under a
 probabilistic interpretation, valid positive covariance-domain and sampling
 premises must be supplied separately; no Gaussian regression theorem is assumed.
 Proof/definition method: Unfold only the canonical linear-forecast wrappers
 and invoke Stdlib Ring for exact polynomial normalization, never floating-point
 experiments or manually duplicated finite-list recursions.
 Library reuse: SequentialReport.sequential_d and Rocq Stdlib Reals/Ring;
 existing definitions are preserved as one authoritative report denominator.
 Boundary: Deterministic linearity/contrast/increment relation only; it does
 not establish distributional conditional expectation or confidence coverage.
*)
Theorem hp_add : forall (n c s t:R), hp n c (s+t) = hp n c (s)+hp n c (t).
Proof.
 intros; unfold hp, hf, ht, hm, he, hc, Rdiv; ring.
Qed.

(** [hp_subtract] (theorem).
 Mathematical meaning: A score-total contrast propagates linearly to the report estimator. This establishes general unequal-history next-score linear regression predictor for arbitrary unequal observed-score contributions.
 Exact checked proposition: forall (n c s t:R), hp n c (s-t) = hp n c (s)-hp n c (t).
 Premises and side conditions: The proposition compares total real-arithmetic
 expressions with a common equicorrelation conditioning denominator. Under a
 probabilistic interpretation, valid positive covariance-domain and sampling
 premises must be supplied separately; no Gaussian regression theorem is assumed.
 Proof/definition method: Unfold only the canonical linear-forecast wrappers
 and invoke Stdlib Ring for exact polynomial normalization, never floating-point
 experiments or manually duplicated finite-list recursions.
 Library reuse: SequentialReport.sequential_d and Rocq Stdlib Reals/Ring;
 existing definitions are preserved as one authoritative report denominator.
 Boundary: Deterministic linearity/contrast/increment relation only; it does
 not establish distributional conditional expectation or confidence coverage.
*)
Theorem hp_subtract : forall (n c s t:R), hp n c (s-t) = hp n c (s)-hp n c (t).
Proof.
 intros; unfold hp, hf, ht, hm, he, hc, Rdiv; ring.
Qed.

(** [hp_negate] (theorem).
 Mathematical meaning: Changing signs of all centered history scores reverses the estimate. This establishes general unequal-history next-score linear regression predictor for arbitrary unequal observed-score contributions.
 Exact checked proposition: forall (n c s:R), hp n c ((-s)) = -hp n c (s).
 Premises and side conditions: The proposition compares total real-arithmetic
 expressions with a common equicorrelation conditioning denominator. Under a
 probabilistic interpretation, valid positive covariance-domain and sampling
 premises must be supplied separately; no Gaussian regression theorem is assumed.
 Proof/definition method: Unfold only the canonical linear-forecast wrappers
 and invoke Stdlib Ring for exact polynomial normalization, never floating-point
 experiments or manually duplicated finite-list recursions.
 Library reuse: SequentialReport.sequential_d and Rocq Stdlib Reals/Ring;
 existing definitions are preserved as one authoritative report denominator.
 Boundary: Deterministic linearity/contrast/increment relation only; it does
 not establish distributional conditional expectation or confidence coverage.
*)
Theorem hp_negate : forall (n c s:R), hp n c ((-s)) = -hp n c (s).
Proof.
 intros; unfold hp, hf, ht, hm, he, hc, Rdiv; ring.
Qed.

(** [hp_scale] (theorem).
 Mathematical meaning: A common standardized score scaling propagates exactly to the estimate. This establishes general unequal-history next-score linear regression predictor for arbitrary unequal observed-score contributions.
 Exact checked proposition: forall (n c s q:R), hp n c (q*s) = q*hp n c (s).
 Premises and side conditions: The proposition compares total real-arithmetic
 expressions with a common equicorrelation conditioning denominator. Under a
 probabilistic interpretation, valid positive covariance-domain and sampling
 premises must be supplied separately; no Gaussian regression theorem is assumed.
 Proof/definition method: Unfold only the canonical linear-forecast wrappers
 and invoke Stdlib Ring for exact polynomial normalization, never floating-point
 experiments or manually duplicated finite-list recursions.
 Library reuse: SequentialReport.sequential_d and Rocq Stdlib Reals/Ring;
 existing definitions are preserved as one authoritative report denominator.
 Boundary: Deterministic linearity/contrast/increment relation only; it does
 not establish distributional conditional expectation or confidence coverage.
*)
Theorem hp_scale : forall (n c s q:R), hp n c (q*s) = q*hp n c (s).
Proof.
 intros; unfold hp, hf, ht, hm, he, hc, Rdiv; ring.
Qed.

(** [hp_sum_three] (theorem).
 Mathematical meaning: Three disjoint observed subtotal contributions aggregate without loss. This establishes general unequal-history next-score linear regression predictor for arbitrary unequal observed-score contributions.
 Exact checked proposition: forall (n c s t u:R), hp n c (s+t+u) = hp n c (s)+hp n c (t)+hp n c (u).
 Premises and side conditions: The proposition compares total real-arithmetic
 expressions with a common equicorrelation conditioning denominator. Under a
 probabilistic interpretation, valid positive covariance-domain and sampling
 premises must be supplied separately; no Gaussian regression theorem is assumed.
 Proof/definition method: Unfold only the canonical linear-forecast wrappers
 and invoke Stdlib Ring for exact polynomial normalization, never floating-point
 experiments or manually duplicated finite-list recursions.
 Library reuse: SequentialReport.sequential_d and Rocq Stdlib Reals/Ring;
 existing definitions are preserved as one authoritative report denominator.
 Boundary: Deterministic linearity/contrast/increment relation only; it does
 not establish distributional conditional expectation or confidence coverage.
*)
Theorem hp_sum_three : forall (n c s t u:R), hp n c (s+t+u) = hp n c (s)+hp n c (t)+hp n c (u).
Proof.
 intros; unfold hp, hf, ht, hm, he, hc, Rdiv; ring.
Qed.

(** [hp_sum_four] (theorem).
 Mathematical meaning: Four test-battery subtotals aggregate to the identical forecast. This establishes general unequal-history next-score linear regression predictor for arbitrary unequal observed-score contributions.
 Exact checked proposition: forall (n c s t u v:R), hp n c (s+t+u+v) = hp n c (s)+hp n c (t)+hp n c (u)+hp n c (v).
 Premises and side conditions: The proposition compares total real-arithmetic
 expressions with a common equicorrelation conditioning denominator. Under a
 probabilistic interpretation, valid positive covariance-domain and sampling
 premises must be supplied separately; no Gaussian regression theorem is assumed.
 Proof/definition method: Unfold only the canonical linear-forecast wrappers
 and invoke Stdlib Ring for exact polynomial normalization, never floating-point
 experiments or manually duplicated finite-list recursions.
 Library reuse: SequentialReport.sequential_d and Rocq Stdlib Reals/Ring;
 existing definitions are preserved as one authoritative report denominator.
 Boundary: Deterministic linearity/contrast/increment relation only; it does
 not establish distributional conditional expectation or confidence coverage.
*)
Theorem hp_sum_four : forall (n c s t u v:R), hp n c (s+t+u+v) = hp n c (s)+hp n c (t)+hp n c (u)+hp n c (v).
Proof.
 intros; unfold hp, hf, ht, hm, he, hc, Rdiv; ring.
Qed.

(** [hp_increment] (theorem).
 Mathematical meaning: The marginal effect of adding a history subtotal is independent of baseline. This establishes general unequal-history next-score linear regression predictor for arbitrary unequal observed-score contributions.
 Exact checked proposition: forall (n c s t:R), hp n c (s+t)-hp n c (s) = hp n c (t).
 Premises and side conditions: The proposition compares total real-arithmetic
 expressions with a common equicorrelation conditioning denominator. Under a
 probabilistic interpretation, valid positive covariance-domain and sampling
 premises must be supplied separately; no Gaussian regression theorem is assumed.
 Proof/definition method: Unfold only the canonical linear-forecast wrappers
 and invoke Stdlib Ring for exact polynomial normalization, never floating-point
 experiments or manually duplicated finite-list recursions.
 Library reuse: SequentialReport.sequential_d and Rocq Stdlib Reals/Ring;
 existing definitions are preserved as one authoritative report denominator.
 Boundary: Deterministic linearity/contrast/increment relation only; it does
 not establish distributional conditional expectation or confidence coverage.
*)
Theorem hp_increment : forall (n c s t:R), hp n c (s+t)-hp n c (s) = hp n c (t).
Proof.
 intros; unfold hp, hf, ht, hm, he, hc, Rdiv; ring.
Qed.

(** [hp_translation_contrast] (theorem).
 Mathematical meaning: Common observed history cancels from a predicted-score contrast. This establishes general unequal-history next-score linear regression predictor for arbitrary unequal observed-score contributions.
 Exact checked proposition: forall (n c s t u:R), hp n c (s+u)-hp n c (t+u) = hp n c (s)-hp n c (t).
 Premises and side conditions: The proposition compares total real-arithmetic
 expressions with a common equicorrelation conditioning denominator. Under a
 probabilistic interpretation, valid positive covariance-domain and sampling
 premises must be supplied separately; no Gaussian regression theorem is assumed.
 Proof/definition method: Unfold only the canonical linear-forecast wrappers
 and invoke Stdlib Ring for exact polynomial normalization, never floating-point
 experiments or manually duplicated finite-list recursions.
 Library reuse: SequentialReport.sequential_d and Rocq Stdlib Reals/Ring;
 existing definitions are preserved as one authoritative report denominator.
 Boundary: Deterministic linearity/contrast/increment relation only; it does
 not establish distributional conditional expectation or confidence coverage.
*)
Theorem hp_translation_contrast : forall (n c s t u:R), hp n c (s+u)-hp n c (t+u) = hp n c (s)-hp n c (t).
Proof.
 intros; unfold hp, hf, ht, hm, he, hc, Rdiv; ring.
Qed.

(** [hp_parallelogram] (theorem).
 Mathematical meaning: Opposite history perturbations cancel in their paired estimates. This establishes general unequal-history next-score linear regression predictor for arbitrary unequal observed-score contributions.
 Exact checked proposition: forall (n c s t:R), hp n c (s+t)+hp n c (s-t) = 2*hp n c (s).
 Premises and side conditions: The proposition compares total real-arithmetic
 expressions with a common equicorrelation conditioning denominator. Under a
 probabilistic interpretation, valid positive covariance-domain and sampling
 premises must be supplied separately; no Gaussian regression theorem is assumed.
 Proof/definition method: Unfold only the canonical linear-forecast wrappers
 and invoke Stdlib Ring for exact polynomial normalization, never floating-point
 experiments or manually duplicated finite-list recursions.
 Library reuse: SequentialReport.sequential_d and Rocq Stdlib Reals/Ring;
 existing definitions are preserved as one authoritative report denominator.
 Boundary: Deterministic linearity/contrast/increment relation only; it does
 not establish distributional conditional expectation or confidence coverage.
*)
Theorem hp_parallelogram : forall (n c s t:R), hp n c (s+t)+hp n c (s-t) = 2*hp n c (s).
Proof.
 intros; unfold hp, hf, ht, hm, he, hc, Rdiv; ring.
Qed.

(** [hp_convex] (theorem).
 Mathematical meaning: Linear mixing of observed score totals is compatible with linear prediction. This establishes general unequal-history next-score linear regression predictor for arbitrary unequal observed-score contributions.
 Exact checked proposition: forall (n c s t q:R), hp n c (q*s+(1-q)*t) = q*hp n c (s)+(1-q)*hp n c (t).
 Premises and side conditions: The proposition compares total real-arithmetic
 expressions with a common equicorrelation conditioning denominator. Under a
 probabilistic interpretation, valid positive covariance-domain and sampling
 premises must be supplied separately; no Gaussian regression theorem is assumed.
 Proof/definition method: Unfold only the canonical linear-forecast wrappers
 and invoke Stdlib Ring for exact polynomial normalization, never floating-point
 experiments or manually duplicated finite-list recursions.
 Library reuse: SequentialReport.sequential_d and Rocq Stdlib Reals/Ring;
 existing definitions are preserved as one authoritative report denominator.
 Boundary: Deterministic linearity/contrast/increment relation only; it does
 not establish distributional conditional expectation or confidence coverage.
*)
Theorem hp_convex : forall (n c s t q:R), hp n c (q*s+(1-q)*t) = q*hp n c (s)+(1-q)*hp n c (t).
Proof.
 intros; unfold hp, hf, ht, hm, he, hc, Rdiv; ring.
Qed.

(** [hp_balanced_contrasts] (theorem).
 Mathematical meaning: Two-cohort observed contrasts decompose into corresponding forecast contrasts. This establishes general unequal-history next-score linear regression predictor for arbitrary unequal observed-score contributions.
 Exact checked proposition: forall (n c s t u v:R), hp n c (s+t)-hp n c (u+v) = hp n c (s-u)+hp n c (t-v).
 Premises and side conditions: The proposition compares total real-arithmetic
 expressions with a common equicorrelation conditioning denominator. Under a
 probabilistic interpretation, valid positive covariance-domain and sampling
 premises must be supplied separately; no Gaussian regression theorem is assumed.
 Proof/definition method: Unfold only the canonical linear-forecast wrappers
 and invoke Stdlib Ring for exact polynomial normalization, never floating-point
 experiments or manually duplicated finite-list recursions.
 Library reuse: SequentialReport.sequential_d and Rocq Stdlib Reals/Ring;
 existing definitions are preserved as one authoritative report denominator.
 Boundary: Deterministic linearity/contrast/increment relation only; it does
 not establish distributional conditional expectation or confidence coverage.
*)
Theorem hp_balanced_contrasts : forall (n c s t u v:R), hp n c (s+t)-hp n c (u+v) = hp n c (s-u)+hp n c (t-v).
Proof.
 intros; unfold hp, hf, ht, hm, he, hc, Rdiv; ring.
Qed.

(** [hp_contrast_pairs] (theorem).
 Mathematical meaning: Two independent score-contrast contributions add on the prediction scale. This establishes general unequal-history next-score linear regression predictor for arbitrary unequal observed-score contributions.
 Exact checked proposition: forall (n c s t u v:R), hp n c ((s-t)+(u-v)) = hp n c (s)-hp n c (t)+hp n c (u)-hp n c (v).
 Premises and side conditions: The proposition compares total real-arithmetic
 expressions with a common equicorrelation conditioning denominator. Under a
 probabilistic interpretation, valid positive covariance-domain and sampling
 premises must be supplied separately; no Gaussian regression theorem is assumed.
 Proof/definition method: Unfold only the canonical linear-forecast wrappers
 and invoke Stdlib Ring for exact polynomial normalization, never floating-point
 experiments or manually duplicated finite-list recursions.
 Library reuse: SequentialReport.sequential_d and Rocq Stdlib Reals/Ring;
 existing definitions are preserved as one authoritative report denominator.
 Boundary: Deterministic linearity/contrast/increment relation only; it does
 not establish distributional conditional expectation or confidence coverage.
*)
Theorem hp_contrast_pairs : forall (n c s t u v:R), hp n c ((s-t)+(u-v)) = hp n c (s)-hp n c (t)+hp n c (u)-hp n c (v).
Proof.
 intros; unfold hp, hf, ht, hm, he, hc, Rdiv; ring.
Qed.

(** [hp_antisymmetry] (theorem).
 Mathematical meaning: Reversing a score contrast exactly reverses the estimated contrast. This establishes general unequal-history next-score linear regression predictor for arbitrary unequal observed-score contributions.
 Exact checked proposition: forall (n c s t:R), hp n c (s-t)+hp n c (t-s) = 0.
 Premises and side conditions: The proposition compares total real-arithmetic
 expressions with a common equicorrelation conditioning denominator. Under a
 probabilistic interpretation, valid positive covariance-domain and sampling
 premises must be supplied separately; no Gaussian regression theorem is assumed.
 Proof/definition method: Unfold only the canonical linear-forecast wrappers
 and invoke Stdlib Ring for exact polynomial normalization, never floating-point
 experiments or manually duplicated finite-list recursions.
 Library reuse: SequentialReport.sequential_d and Rocq Stdlib Reals/Ring;
 existing definitions are preserved as one authoritative report denominator.
 Boundary: Deterministic linearity/contrast/increment relation only; it does
 not establish distributional conditional expectation or confidence coverage.
*)
Theorem hp_antisymmetry : forall (n c s t:R), hp n c (s-t)+hp n c (t-s) = 0.
Proof.
 intros; unfold hp, hf, ht, hm, he, hc, Rdiv; ring.
Qed.

(** [hp_contrast_of_contrasts] (theorem).
 Mathematical meaning: Difference-in-differences for score totals is preserved by the estimator. This establishes general unequal-history next-score linear regression predictor for arbitrary unequal observed-score contributions.
 Exact checked proposition: forall (n c s t u v:R), hp n c ((s-t)-(u-v)) = hp n c (s)-hp n c (t)-hp n c (u)+hp n c (v).
 Premises and side conditions: The proposition compares total real-arithmetic
 expressions with a common equicorrelation conditioning denominator. Under a
 probabilistic interpretation, valid positive covariance-domain and sampling
 premises must be supplied separately; no Gaussian regression theorem is assumed.
 Proof/definition method: Unfold only the canonical linear-forecast wrappers
 and invoke Stdlib Ring for exact polynomial normalization, never floating-point
 experiments or manually duplicated finite-list recursions.
 Library reuse: SequentialReport.sequential_d and Rocq Stdlib Reals/Ring;
 existing definitions are preserved as one authoritative report denominator.
 Boundary: Deterministic linearity/contrast/increment relation only; it does
 not establish distributional conditional expectation or confidence coverage.
*)
Theorem hp_contrast_of_contrasts : forall (n c s t u v:R), hp n c ((s-t)-(u-v)) = hp n c (s)-hp n c (t)-hp n c (u)+hp n c (v).
Proof.
 intros; unfold hp, hf, ht, hm, he, hc, Rdiv; ring.
Qed.

(** [hp_weighted_three] (theorem).
 Mathematical meaning: Three-way weighted score aggregation commutes with the estimator. This establishes general unequal-history next-score linear regression predictor for arbitrary unequal observed-score contributions.
 Exact checked proposition: forall (n c s t u v q:R), hp n c (q*s+u*t+v) = q*hp n c (s)+u*hp n c (t)+hp n c (v).
 Premises and side conditions: The proposition compares total real-arithmetic
 expressions with a common equicorrelation conditioning denominator. Under a
 probabilistic interpretation, valid positive covariance-domain and sampling
 premises must be supplied separately; no Gaussian regression theorem is assumed.
 Proof/definition method: Unfold only the canonical linear-forecast wrappers
 and invoke Stdlib Ring for exact polynomial normalization, never floating-point
 experiments or manually duplicated finite-list recursions.
 Library reuse: SequentialReport.sequential_d and Rocq Stdlib Reals/Ring;
 existing definitions are preserved as one authoritative report denominator.
 Boundary: Deterministic linearity/contrast/increment relation only; it does
 not establish distributional conditional expectation or confidence coverage.
*)
Theorem hp_weighted_three : forall (n c s t u v q:R), hp n c (q*s+u*t+v) = q*hp n c (s)+u*hp n c (t)+hp n c (v).
Proof.
 intros; unfold hp, hf, ht, hm, he, hc, Rdiv; ring.
Qed.

(** [hf_zero] (theorem).
 Mathematical meaning: A zero-sum standardized history contributes no linear predictor. This establishes aggregate forecast for a specified future score count for arbitrary unequal observed-score contributions.
 Exact checked proposition: forall (n k c:R), hf n k c (0) = 0.
 Premises and side conditions: The proposition compares total real-arithmetic
 expressions with a common equicorrelation conditioning denominator. Under a
 probabilistic interpretation, valid positive covariance-domain and sampling
 premises must be supplied separately; no Gaussian regression theorem is assumed.
 Proof/definition method: Unfold only the canonical linear-forecast wrappers
 and invoke Stdlib Ring for exact polynomial normalization, never floating-point
 experiments or manually duplicated finite-list recursions.
 Library reuse: SequentialReport.sequential_d and Rocq Stdlib Reals/Ring;
 existing definitions are preserved as one authoritative report denominator.
 Boundary: Deterministic linearity/contrast/increment relation only; it does
 not establish distributional conditional expectation or confidence coverage.
*)
Theorem hf_zero : forall (n k c:R), hf n k c (0) = 0.
Proof.
 intros; unfold hp, hf, ht, hm, he, hc, Rdiv; ring.
Qed.

(** [hf_add] (theorem).
 Mathematical meaning: Combining two score-total contributions is additive at fixed design. This establishes aggregate forecast for a specified future score count for arbitrary unequal observed-score contributions.
 Exact checked proposition: forall (n k c s t:R), hf n k c (s+t) = hf n k c (s)+hf n k c (t).
 Premises and side conditions: The proposition compares total real-arithmetic
 expressions with a common equicorrelation conditioning denominator. Under a
 probabilistic interpretation, valid positive covariance-domain and sampling
 premises must be supplied separately; no Gaussian regression theorem is assumed.
 Proof/definition method: Unfold only the canonical linear-forecast wrappers
 and invoke Stdlib Ring for exact polynomial normalization, never floating-point
 experiments or manually duplicated finite-list recursions.
 Library reuse: SequentialReport.sequential_d and Rocq Stdlib Reals/Ring;
 existing definitions are preserved as one authoritative report denominator.
 Boundary: Deterministic linearity/contrast/increment relation only; it does
 not establish distributional conditional expectation or confidence coverage.
*)
Theorem hf_add : forall (n k c s t:R), hf n k c (s+t) = hf n k c (s)+hf n k c (t).
Proof.
 intros; unfold hp, hf, ht, hm, he, hc, Rdiv; ring.
Qed.

(** [hf_subtract] (theorem).
 Mathematical meaning: A score-total contrast propagates linearly to the report estimator. This establishes aggregate forecast for a specified future score count for arbitrary unequal observed-score contributions.
 Exact checked proposition: forall (n k c s t:R), hf n k c (s-t) = hf n k c (s)-hf n k c (t).
 Premises and side conditions: The proposition compares total real-arithmetic
 expressions with a common equicorrelation conditioning denominator. Under a
 probabilistic interpretation, valid positive covariance-domain and sampling
 premises must be supplied separately; no Gaussian regression theorem is assumed.
 Proof/definition method: Unfold only the canonical linear-forecast wrappers
 and invoke Stdlib Ring for exact polynomial normalization, never floating-point
 experiments or manually duplicated finite-list recursions.
 Library reuse: SequentialReport.sequential_d and Rocq Stdlib Reals/Ring;
 existing definitions are preserved as one authoritative report denominator.
 Boundary: Deterministic linearity/contrast/increment relation only; it does
 not establish distributional conditional expectation or confidence coverage.
*)
Theorem hf_subtract : forall (n k c s t:R), hf n k c (s-t) = hf n k c (s)-hf n k c (t).
Proof.
 intros; unfold hp, hf, ht, hm, he, hc, Rdiv; ring.
Qed.

(** [hf_negate] (theorem).
 Mathematical meaning: Changing signs of all centered history scores reverses the estimate. This establishes aggregate forecast for a specified future score count for arbitrary unequal observed-score contributions.
 Exact checked proposition: forall (n k c s:R), hf n k c ((-s)) = -hf n k c (s).
 Premises and side conditions: The proposition compares total real-arithmetic
 expressions with a common equicorrelation conditioning denominator. Under a
 probabilistic interpretation, valid positive covariance-domain and sampling
 premises must be supplied separately; no Gaussian regression theorem is assumed.
 Proof/definition method: Unfold only the canonical linear-forecast wrappers
 and invoke Stdlib Ring for exact polynomial normalization, never floating-point
 experiments or manually duplicated finite-list recursions.
 Library reuse: SequentialReport.sequential_d and Rocq Stdlib Reals/Ring;
 existing definitions are preserved as one authoritative report denominator.
 Boundary: Deterministic linearity/contrast/increment relation only; it does
 not establish distributional conditional expectation or confidence coverage.
*)
Theorem hf_negate : forall (n k c s:R), hf n k c ((-s)) = -hf n k c (s).
Proof.
 intros; unfold hp, hf, ht, hm, he, hc, Rdiv; ring.
Qed.

(** [hf_scale] (theorem).
 Mathematical meaning: A common standardized score scaling propagates exactly to the estimate. This establishes aggregate forecast for a specified future score count for arbitrary unequal observed-score contributions.
 Exact checked proposition: forall (n k c s q:R), hf n k c (q*s) = q*hf n k c (s).
 Premises and side conditions: The proposition compares total real-arithmetic
 expressions with a common equicorrelation conditioning denominator. Under a
 probabilistic interpretation, valid positive covariance-domain and sampling
 premises must be supplied separately; no Gaussian regression theorem is assumed.
 Proof/definition method: Unfold only the canonical linear-forecast wrappers
 and invoke Stdlib Ring for exact polynomial normalization, never floating-point
 experiments or manually duplicated finite-list recursions.
 Library reuse: SequentialReport.sequential_d and Rocq Stdlib Reals/Ring;
 existing definitions are preserved as one authoritative report denominator.
 Boundary: Deterministic linearity/contrast/increment relation only; it does
 not establish distributional conditional expectation or confidence coverage.
*)
Theorem hf_scale : forall (n k c s q:R), hf n k c (q*s) = q*hf n k c (s).
Proof.
 intros; unfold hp, hf, ht, hm, he, hc, Rdiv; ring.
Qed.

(** [hf_sum_three] (theorem).
 Mathematical meaning: Three disjoint observed subtotal contributions aggregate without loss. This establishes aggregate forecast for a specified future score count for arbitrary unequal observed-score contributions.
 Exact checked proposition: forall (n k c s t u:R), hf n k c (s+t+u) = hf n k c (s)+hf n k c (t)+hf n k c (u).
 Premises and side conditions: The proposition compares total real-arithmetic
 expressions with a common equicorrelation conditioning denominator. Under a
 probabilistic interpretation, valid positive covariance-domain and sampling
 premises must be supplied separately; no Gaussian regression theorem is assumed.
 Proof/definition method: Unfold only the canonical linear-forecast wrappers
 and invoke Stdlib Ring for exact polynomial normalization, never floating-point
 experiments or manually duplicated finite-list recursions.
 Library reuse: SequentialReport.sequential_d and Rocq Stdlib Reals/Ring;
 existing definitions are preserved as one authoritative report denominator.
 Boundary: Deterministic linearity/contrast/increment relation only; it does
 not establish distributional conditional expectation or confidence coverage.
*)
Theorem hf_sum_three : forall (n k c s t u:R), hf n k c (s+t+u) = hf n k c (s)+hf n k c (t)+hf n k c (u).
Proof.
 intros; unfold hp, hf, ht, hm, he, hc, Rdiv; ring.
Qed.

(** [hf_sum_four] (theorem).
 Mathematical meaning: Four test-battery subtotals aggregate to the identical forecast. This establishes aggregate forecast for a specified future score count for arbitrary unequal observed-score contributions.
 Exact checked proposition: forall (n k c s t u v:R), hf n k c (s+t+u+v) = hf n k c (s)+hf n k c (t)+hf n k c (u)+hf n k c (v).
 Premises and side conditions: The proposition compares total real-arithmetic
 expressions with a common equicorrelation conditioning denominator. Under a
 probabilistic interpretation, valid positive covariance-domain and sampling
 premises must be supplied separately; no Gaussian regression theorem is assumed.
 Proof/definition method: Unfold only the canonical linear-forecast wrappers
 and invoke Stdlib Ring for exact polynomial normalization, never floating-point
 experiments or manually duplicated finite-list recursions.
 Library reuse: SequentialReport.sequential_d and Rocq Stdlib Reals/Ring;
 existing definitions are preserved as one authoritative report denominator.
 Boundary: Deterministic linearity/contrast/increment relation only; it does
 not establish distributional conditional expectation or confidence coverage.
*)
Theorem hf_sum_four : forall (n k c s t u v:R), hf n k c (s+t+u+v) = hf n k c (s)+hf n k c (t)+hf n k c (u)+hf n k c (v).
Proof.
 intros; unfold hp, hf, ht, hm, he, hc, Rdiv; ring.
Qed.

(** [hf_increment] (theorem).
 Mathematical meaning: The marginal effect of adding a history subtotal is independent of baseline. This establishes aggregate forecast for a specified future score count for arbitrary unequal observed-score contributions.
 Exact checked proposition: forall (n k c s t:R), hf n k c (s+t)-hf n k c (s) = hf n k c (t).
 Premises and side conditions: The proposition compares total real-arithmetic
 expressions with a common equicorrelation conditioning denominator. Under a
 probabilistic interpretation, valid positive covariance-domain and sampling
 premises must be supplied separately; no Gaussian regression theorem is assumed.
 Proof/definition method: Unfold only the canonical linear-forecast wrappers
 and invoke Stdlib Ring for exact polynomial normalization, never floating-point
 experiments or manually duplicated finite-list recursions.
 Library reuse: SequentialReport.sequential_d and Rocq Stdlib Reals/Ring;
 existing definitions are preserved as one authoritative report denominator.
 Boundary: Deterministic linearity/contrast/increment relation only; it does
 not establish distributional conditional expectation or confidence coverage.
*)
Theorem hf_increment : forall (n k c s t:R), hf n k c (s+t)-hf n k c (s) = hf n k c (t).
Proof.
 intros; unfold hp, hf, ht, hm, he, hc, Rdiv; ring.
Qed.

(** [hf_translation_contrast] (theorem).
 Mathematical meaning: Common observed history cancels from a predicted-score contrast. This establishes aggregate forecast for a specified future score count for arbitrary unequal observed-score contributions.
 Exact checked proposition: forall (n k c s t u:R), hf n k c (s+u)-hf n k c (t+u) = hf n k c (s)-hf n k c (t).
 Premises and side conditions: The proposition compares total real-arithmetic
 expressions with a common equicorrelation conditioning denominator. Under a
 probabilistic interpretation, valid positive covariance-domain and sampling
 premises must be supplied separately; no Gaussian regression theorem is assumed.
 Proof/definition method: Unfold only the canonical linear-forecast wrappers
 and invoke Stdlib Ring for exact polynomial normalization, never floating-point
 experiments or manually duplicated finite-list recursions.
 Library reuse: SequentialReport.sequential_d and Rocq Stdlib Reals/Ring;
 existing definitions are preserved as one authoritative report denominator.
 Boundary: Deterministic linearity/contrast/increment relation only; it does
 not establish distributional conditional expectation or confidence coverage.
*)
Theorem hf_translation_contrast : forall (n k c s t u:R), hf n k c (s+u)-hf n k c (t+u) = hf n k c (s)-hf n k c (t).
Proof.
 intros; unfold hp, hf, ht, hm, he, hc, Rdiv; ring.
Qed.

(** [hf_parallelogram] (theorem).
 Mathematical meaning: Opposite history perturbations cancel in their paired estimates. This establishes aggregate forecast for a specified future score count for arbitrary unequal observed-score contributions.
 Exact checked proposition: forall (n k c s t:R), hf n k c (s+t)+hf n k c (s-t) = 2*hf n k c (s).
 Premises and side conditions: The proposition compares total real-arithmetic
 expressions with a common equicorrelation conditioning denominator. Under a
 probabilistic interpretation, valid positive covariance-domain and sampling
 premises must be supplied separately; no Gaussian regression theorem is assumed.
 Proof/definition method: Unfold only the canonical linear-forecast wrappers
 and invoke Stdlib Ring for exact polynomial normalization, never floating-point
 experiments or manually duplicated finite-list recursions.
 Library reuse: SequentialReport.sequential_d and Rocq Stdlib Reals/Ring;
 existing definitions are preserved as one authoritative report denominator.
 Boundary: Deterministic linearity/contrast/increment relation only; it does
 not establish distributional conditional expectation or confidence coverage.
*)
Theorem hf_parallelogram : forall (n k c s t:R), hf n k c (s+t)+hf n k c (s-t) = 2*hf n k c (s).
Proof.
 intros; unfold hp, hf, ht, hm, he, hc, Rdiv; ring.
Qed.

(** [hf_convex] (theorem).
 Mathematical meaning: Linear mixing of observed score totals is compatible with linear prediction. This establishes aggregate forecast for a specified future score count for arbitrary unequal observed-score contributions.
 Exact checked proposition: forall (n k c s t q:R), hf n k c (q*s+(1-q)*t) = q*hf n k c (s)+(1-q)*hf n k c (t).
 Premises and side conditions: The proposition compares total real-arithmetic
 expressions with a common equicorrelation conditioning denominator. Under a
 probabilistic interpretation, valid positive covariance-domain and sampling
 premises must be supplied separately; no Gaussian regression theorem is assumed.
 Proof/definition method: Unfold only the canonical linear-forecast wrappers
 and invoke Stdlib Ring for exact polynomial normalization, never floating-point
 experiments or manually duplicated finite-list recursions.
 Library reuse: SequentialReport.sequential_d and Rocq Stdlib Reals/Ring;
 existing definitions are preserved as one authoritative report denominator.
 Boundary: Deterministic linearity/contrast/increment relation only; it does
 not establish distributional conditional expectation or confidence coverage.
*)
Theorem hf_convex : forall (n k c s t q:R), hf n k c (q*s+(1-q)*t) = q*hf n k c (s)+(1-q)*hf n k c (t).
Proof.
 intros; unfold hp, hf, ht, hm, he, hc, Rdiv; ring.
Qed.

(** [hf_balanced_contrasts] (theorem).
 Mathematical meaning: Two-cohort observed contrasts decompose into corresponding forecast contrasts. This establishes aggregate forecast for a specified future score count for arbitrary unequal observed-score contributions.
 Exact checked proposition: forall (n k c s t u v:R), hf n k c (s+t)-hf n k c (u+v) = hf n k c (s-u)+hf n k c (t-v).
 Premises and side conditions: The proposition compares total real-arithmetic
 expressions with a common equicorrelation conditioning denominator. Under a
 probabilistic interpretation, valid positive covariance-domain and sampling
 premises must be supplied separately; no Gaussian regression theorem is assumed.
 Proof/definition method: Unfold only the canonical linear-forecast wrappers
 and invoke Stdlib Ring for exact polynomial normalization, never floating-point
 experiments or manually duplicated finite-list recursions.
 Library reuse: SequentialReport.sequential_d and Rocq Stdlib Reals/Ring;
 existing definitions are preserved as one authoritative report denominator.
 Boundary: Deterministic linearity/contrast/increment relation only; it does
 not establish distributional conditional expectation or confidence coverage.
*)
Theorem hf_balanced_contrasts : forall (n k c s t u v:R), hf n k c (s+t)-hf n k c (u+v) = hf n k c (s-u)+hf n k c (t-v).
Proof.
 intros; unfold hp, hf, ht, hm, he, hc, Rdiv; ring.
Qed.

(** [hf_contrast_pairs] (theorem).
 Mathematical meaning: Two independent score-contrast contributions add on the prediction scale. This establishes aggregate forecast for a specified future score count for arbitrary unequal observed-score contributions.
 Exact checked proposition: forall (n k c s t u v:R), hf n k c ((s-t)+(u-v)) = hf n k c (s)-hf n k c (t)+hf n k c (u)-hf n k c (v).
 Premises and side conditions: The proposition compares total real-arithmetic
 expressions with a common equicorrelation conditioning denominator. Under a
 probabilistic interpretation, valid positive covariance-domain and sampling
 premises must be supplied separately; no Gaussian regression theorem is assumed.
 Proof/definition method: Unfold only the canonical linear-forecast wrappers
 and invoke Stdlib Ring for exact polynomial normalization, never floating-point
 experiments or manually duplicated finite-list recursions.
 Library reuse: SequentialReport.sequential_d and Rocq Stdlib Reals/Ring;
 existing definitions are preserved as one authoritative report denominator.
 Boundary: Deterministic linearity/contrast/increment relation only; it does
 not establish distributional conditional expectation or confidence coverage.
*)
Theorem hf_contrast_pairs : forall (n k c s t u v:R), hf n k c ((s-t)+(u-v)) = hf n k c (s)-hf n k c (t)+hf n k c (u)-hf n k c (v).
Proof.
 intros; unfold hp, hf, ht, hm, he, hc, Rdiv; ring.
Qed.

(** [hf_antisymmetry] (theorem).
 Mathematical meaning: Reversing a score contrast exactly reverses the estimated contrast. This establishes aggregate forecast for a specified future score count for arbitrary unequal observed-score contributions.
 Exact checked proposition: forall (n k c s t:R), hf n k c (s-t)+hf n k c (t-s) = 0.
 Premises and side conditions: The proposition compares total real-arithmetic
 expressions with a common equicorrelation conditioning denominator. Under a
 probabilistic interpretation, valid positive covariance-domain and sampling
 premises must be supplied separately; no Gaussian regression theorem is assumed.
 Proof/definition method: Unfold only the canonical linear-forecast wrappers
 and invoke Stdlib Ring for exact polynomial normalization, never floating-point
 experiments or manually duplicated finite-list recursions.
 Library reuse: SequentialReport.sequential_d and Rocq Stdlib Reals/Ring;
 existing definitions are preserved as one authoritative report denominator.
 Boundary: Deterministic linearity/contrast/increment relation only; it does
 not establish distributional conditional expectation or confidence coverage.
*)
Theorem hf_antisymmetry : forall (n k c s t:R), hf n k c (s-t)+hf n k c (t-s) = 0.
Proof.
 intros; unfold hp, hf, ht, hm, he, hc, Rdiv; ring.
Qed.

(** [hf_contrast_of_contrasts] (theorem).
 Mathematical meaning: Difference-in-differences for score totals is preserved by the estimator. This establishes aggregate forecast for a specified future score count for arbitrary unequal observed-score contributions.
 Exact checked proposition: forall (n k c s t u v:R), hf n k c ((s-t)-(u-v)) = hf n k c (s)-hf n k c (t)-hf n k c (u)+hf n k c (v).
 Premises and side conditions: The proposition compares total real-arithmetic
 expressions with a common equicorrelation conditioning denominator. Under a
 probabilistic interpretation, valid positive covariance-domain and sampling
 premises must be supplied separately; no Gaussian regression theorem is assumed.
 Proof/definition method: Unfold only the canonical linear-forecast wrappers
 and invoke Stdlib Ring for exact polynomial normalization, never floating-point
 experiments or manually duplicated finite-list recursions.
 Library reuse: SequentialReport.sequential_d and Rocq Stdlib Reals/Ring;
 existing definitions are preserved as one authoritative report denominator.
 Boundary: Deterministic linearity/contrast/increment relation only; it does
 not establish distributional conditional expectation or confidence coverage.
*)
Theorem hf_contrast_of_contrasts : forall (n k c s t u v:R), hf n k c ((s-t)-(u-v)) = hf n k c (s)-hf n k c (t)-hf n k c (u)+hf n k c (v).
Proof.
 intros; unfold hp, hf, ht, hm, he, hc, Rdiv; ring.
Qed.

(** [hf_weighted_three] (theorem).
 Mathematical meaning: Three-way weighted score aggregation commutes with the estimator. This establishes aggregate forecast for a specified future score count for arbitrary unequal observed-score contributions.
 Exact checked proposition: forall (n k c s t u v q:R), hf n k c (q*s+u*t+v) = q*hf n k c (s)+u*hf n k c (t)+hf n k c (v).
 Premises and side conditions: The proposition compares total real-arithmetic
 expressions with a common equicorrelation conditioning denominator. Under a
 probabilistic interpretation, valid positive covariance-domain and sampling
 premises must be supplied separately; no Gaussian regression theorem is assumed.
 Proof/definition method: Unfold only the canonical linear-forecast wrappers
 and invoke Stdlib Ring for exact polynomial normalization, never floating-point
 experiments or manually duplicated finite-list recursions.
 Library reuse: SequentialReport.sequential_d and Rocq Stdlib Reals/Ring;
 existing definitions are preserved as one authoritative report denominator.
 Boundary: Deterministic linearity/contrast/increment relation only; it does
 not establish distributional conditional expectation or confidence coverage.
*)
Theorem hf_weighted_three : forall (n k c s t u v q:R), hf n k c (q*s+u*t+v) = q*hf n k c (s)+u*hf n k c (t)+hf n k c (v).
Proof.
 intros; unfold hp, hf, ht, hm, he, hc, Rdiv; ring.
Qed.

(** [ht_zero] (theorem).
 Mathematical meaning: A zero-sum standardized history contributes no linear predictor. This establishes combined observed-plus-predicted score total for arbitrary unequal observed-score contributions.
 Exact checked proposition: forall (n k c:R), ht n k c (0) = 0.
 Premises and side conditions: The proposition compares total real-arithmetic
 expressions with a common equicorrelation conditioning denominator. Under a
 probabilistic interpretation, valid positive covariance-domain and sampling
 premises must be supplied separately; no Gaussian regression theorem is assumed.
 Proof/definition method: Unfold only the canonical linear-forecast wrappers
 and invoke Stdlib Ring for exact polynomial normalization, never floating-point
 experiments or manually duplicated finite-list recursions.
 Library reuse: SequentialReport.sequential_d and Rocq Stdlib Reals/Ring;
 existing definitions are preserved as one authoritative report denominator.
 Boundary: Deterministic linearity/contrast/increment relation only; it does
 not establish distributional conditional expectation or confidence coverage.
*)
Theorem ht_zero : forall (n k c:R), ht n k c (0) = 0.
Proof.
 intros; unfold hp, hf, ht, hm, he, hc, Rdiv; ring.
Qed.

(** [ht_add] (theorem).
 Mathematical meaning: Combining two score-total contributions is additive at fixed design. This establishes combined observed-plus-predicted score total for arbitrary unequal observed-score contributions.
 Exact checked proposition: forall (n k c s t:R), ht n k c (s+t) = ht n k c (s)+ht n k c (t).
 Premises and side conditions: The proposition compares total real-arithmetic
 expressions with a common equicorrelation conditioning denominator. Under a
 probabilistic interpretation, valid positive covariance-domain and sampling
 premises must be supplied separately; no Gaussian regression theorem is assumed.
 Proof/definition method: Unfold only the canonical linear-forecast wrappers
 and invoke Stdlib Ring for exact polynomial normalization, never floating-point
 experiments or manually duplicated finite-list recursions.
 Library reuse: SequentialReport.sequential_d and Rocq Stdlib Reals/Ring;
 existing definitions are preserved as one authoritative report denominator.
 Boundary: Deterministic linearity/contrast/increment relation only; it does
 not establish distributional conditional expectation or confidence coverage.
*)
Theorem ht_add : forall (n k c s t:R), ht n k c (s+t) = ht n k c (s)+ht n k c (t).
Proof.
 intros; unfold hp, hf, ht, hm, he, hc, Rdiv; ring.
Qed.

(** [ht_subtract] (theorem).
 Mathematical meaning: A score-total contrast propagates linearly to the report estimator. This establishes combined observed-plus-predicted score total for arbitrary unequal observed-score contributions.
 Exact checked proposition: forall (n k c s t:R), ht n k c (s-t) = ht n k c (s)-ht n k c (t).
 Premises and side conditions: The proposition compares total real-arithmetic
 expressions with a common equicorrelation conditioning denominator. Under a
 probabilistic interpretation, valid positive covariance-domain and sampling
 premises must be supplied separately; no Gaussian regression theorem is assumed.
 Proof/definition method: Unfold only the canonical linear-forecast wrappers
 and invoke Stdlib Ring for exact polynomial normalization, never floating-point
 experiments or manually duplicated finite-list recursions.
 Library reuse: SequentialReport.sequential_d and Rocq Stdlib Reals/Ring;
 existing definitions are preserved as one authoritative report denominator.
 Boundary: Deterministic linearity/contrast/increment relation only; it does
 not establish distributional conditional expectation or confidence coverage.
*)
Theorem ht_subtract : forall (n k c s t:R), ht n k c (s-t) = ht n k c (s)-ht n k c (t).
Proof.
 intros; unfold hp, hf, ht, hm, he, hc, Rdiv; ring.
Qed.

(** [ht_negate] (theorem).
 Mathematical meaning: Changing signs of all centered history scores reverses the estimate. This establishes combined observed-plus-predicted score total for arbitrary unequal observed-score contributions.
 Exact checked proposition: forall (n k c s:R), ht n k c ((-s)) = -ht n k c (s).
 Premises and side conditions: The proposition compares total real-arithmetic
 expressions with a common equicorrelation conditioning denominator. Under a
 probabilistic interpretation, valid positive covariance-domain and sampling
 premises must be supplied separately; no Gaussian regression theorem is assumed.
 Proof/definition method: Unfold only the canonical linear-forecast wrappers
 and invoke Stdlib Ring for exact polynomial normalization, never floating-point
 experiments or manually duplicated finite-list recursions.
 Library reuse: SequentialReport.sequential_d and Rocq Stdlib Reals/Ring;
 existing definitions are preserved as one authoritative report denominator.
 Boundary: Deterministic linearity/contrast/increment relation only; it does
 not establish distributional conditional expectation or confidence coverage.
*)
Theorem ht_negate : forall (n k c s:R), ht n k c ((-s)) = -ht n k c (s).
Proof.
 intros; unfold hp, hf, ht, hm, he, hc, Rdiv; ring.
Qed.

(** [ht_scale] (theorem).
 Mathematical meaning: A common standardized score scaling propagates exactly to the estimate. This establishes combined observed-plus-predicted score total for arbitrary unequal observed-score contributions.
 Exact checked proposition: forall (n k c s q:R), ht n k c (q*s) = q*ht n k c (s).
 Premises and side conditions: The proposition compares total real-arithmetic
 expressions with a common equicorrelation conditioning denominator. Under a
 probabilistic interpretation, valid positive covariance-domain and sampling
 premises must be supplied separately; no Gaussian regression theorem is assumed.
 Proof/definition method: Unfold only the canonical linear-forecast wrappers
 and invoke Stdlib Ring for exact polynomial normalization, never floating-point
 experiments or manually duplicated finite-list recursions.
 Library reuse: SequentialReport.sequential_d and Rocq Stdlib Reals/Ring;
 existing definitions are preserved as one authoritative report denominator.
 Boundary: Deterministic linearity/contrast/increment relation only; it does
 not establish distributional conditional expectation or confidence coverage.
*)
Theorem ht_scale : forall (n k c s q:R), ht n k c (q*s) = q*ht n k c (s).
Proof.
 intros; unfold hp, hf, ht, hm, he, hc, Rdiv; ring.
Qed.

(** [ht_sum_three] (theorem).
 Mathematical meaning: Three disjoint observed subtotal contributions aggregate without loss. This establishes combined observed-plus-predicted score total for arbitrary unequal observed-score contributions.
 Exact checked proposition: forall (n k c s t u:R), ht n k c (s+t+u) = ht n k c (s)+ht n k c (t)+ht n k c (u).
 Premises and side conditions: The proposition compares total real-arithmetic
 expressions with a common equicorrelation conditioning denominator. Under a
 probabilistic interpretation, valid positive covariance-domain and sampling
 premises must be supplied separately; no Gaussian regression theorem is assumed.
 Proof/definition method: Unfold only the canonical linear-forecast wrappers
 and invoke Stdlib Ring for exact polynomial normalization, never floating-point
 experiments or manually duplicated finite-list recursions.
 Library reuse: SequentialReport.sequential_d and Rocq Stdlib Reals/Ring;
 existing definitions are preserved as one authoritative report denominator.
 Boundary: Deterministic linearity/contrast/increment relation only; it does
 not establish distributional conditional expectation or confidence coverage.
*)
Theorem ht_sum_three : forall (n k c s t u:R), ht n k c (s+t+u) = ht n k c (s)+ht n k c (t)+ht n k c (u).
Proof.
 intros; unfold hp, hf, ht, hm, he, hc, Rdiv; ring.
Qed.

(** [ht_sum_four] (theorem).
 Mathematical meaning: Four test-battery subtotals aggregate to the identical forecast. This establishes combined observed-plus-predicted score total for arbitrary unequal observed-score contributions.
 Exact checked proposition: forall (n k c s t u v:R), ht n k c (s+t+u+v) = ht n k c (s)+ht n k c (t)+ht n k c (u)+ht n k c (v).
 Premises and side conditions: The proposition compares total real-arithmetic
 expressions with a common equicorrelation conditioning denominator. Under a
 probabilistic interpretation, valid positive covariance-domain and sampling
 premises must be supplied separately; no Gaussian regression theorem is assumed.
 Proof/definition method: Unfold only the canonical linear-forecast wrappers
 and invoke Stdlib Ring for exact polynomial normalization, never floating-point
 experiments or manually duplicated finite-list recursions.
 Library reuse: SequentialReport.sequential_d and Rocq Stdlib Reals/Ring;
 existing definitions are preserved as one authoritative report denominator.
 Boundary: Deterministic linearity/contrast/increment relation only; it does
 not establish distributional conditional expectation or confidence coverage.
*)
Theorem ht_sum_four : forall (n k c s t u v:R), ht n k c (s+t+u+v) = ht n k c (s)+ht n k c (t)+ht n k c (u)+ht n k c (v).
Proof.
 intros; unfold hp, hf, ht, hm, he, hc, Rdiv; ring.
Qed.

(** [ht_increment] (theorem).
 Mathematical meaning: The marginal effect of adding a history subtotal is independent of baseline. This establishes combined observed-plus-predicted score total for arbitrary unequal observed-score contributions.
 Exact checked proposition: forall (n k c s t:R), ht n k c (s+t)-ht n k c (s) = ht n k c (t).
 Premises and side conditions: The proposition compares total real-arithmetic
 expressions with a common equicorrelation conditioning denominator. Under a
 probabilistic interpretation, valid positive covariance-domain and sampling
 premises must be supplied separately; no Gaussian regression theorem is assumed.
 Proof/definition method: Unfold only the canonical linear-forecast wrappers
 and invoke Stdlib Ring for exact polynomial normalization, never floating-point
 experiments or manually duplicated finite-list recursions.
 Library reuse: SequentialReport.sequential_d and Rocq Stdlib Reals/Ring;
 existing definitions are preserved as one authoritative report denominator.
 Boundary: Deterministic linearity/contrast/increment relation only; it does
 not establish distributional conditional expectation or confidence coverage.
*)
Theorem ht_increment : forall (n k c s t:R), ht n k c (s+t)-ht n k c (s) = ht n k c (t).
Proof.
 intros; unfold hp, hf, ht, hm, he, hc, Rdiv; ring.
Qed.

(** [ht_translation_contrast] (theorem).
 Mathematical meaning: Common observed history cancels from a predicted-score contrast. This establishes combined observed-plus-predicted score total for arbitrary unequal observed-score contributions.
 Exact checked proposition: forall (n k c s t u:R), ht n k c (s+u)-ht n k c (t+u) = ht n k c (s)-ht n k c (t).
 Premises and side conditions: The proposition compares total real-arithmetic
 expressions with a common equicorrelation conditioning denominator. Under a
 probabilistic interpretation, valid positive covariance-domain and sampling
 premises must be supplied separately; no Gaussian regression theorem is assumed.
 Proof/definition method: Unfold only the canonical linear-forecast wrappers
 and invoke Stdlib Ring for exact polynomial normalization, never floating-point
 experiments or manually duplicated finite-list recursions.
 Library reuse: SequentialReport.sequential_d and Rocq Stdlib Reals/Ring;
 existing definitions are preserved as one authoritative report denominator.
 Boundary: Deterministic linearity/contrast/increment relation only; it does
 not establish distributional conditional expectation or confidence coverage.
*)
Theorem ht_translation_contrast : forall (n k c s t u:R), ht n k c (s+u)-ht n k c (t+u) = ht n k c (s)-ht n k c (t).
Proof.
 intros; unfold hp, hf, ht, hm, he, hc, Rdiv; ring.
Qed.

(** [ht_parallelogram] (theorem).
 Mathematical meaning: Opposite history perturbations cancel in their paired estimates. This establishes combined observed-plus-predicted score total for arbitrary unequal observed-score contributions.
 Exact checked proposition: forall (n k c s t:R), ht n k c (s+t)+ht n k c (s-t) = 2*ht n k c (s).
 Premises and side conditions: The proposition compares total real-arithmetic
 expressions with a common equicorrelation conditioning denominator. Under a
 probabilistic interpretation, valid positive covariance-domain and sampling
 premises must be supplied separately; no Gaussian regression theorem is assumed.
 Proof/definition method: Unfold only the canonical linear-forecast wrappers
 and invoke Stdlib Ring for exact polynomial normalization, never floating-point
 experiments or manually duplicated finite-list recursions.
 Library reuse: SequentialReport.sequential_d and Rocq Stdlib Reals/Ring;
 existing definitions are preserved as one authoritative report denominator.
 Boundary: Deterministic linearity/contrast/increment relation only; it does
 not establish distributional conditional expectation or confidence coverage.
*)
Theorem ht_parallelogram : forall (n k c s t:R), ht n k c (s+t)+ht n k c (s-t) = 2*ht n k c (s).
Proof.
 intros; unfold hp, hf, ht, hm, he, hc, Rdiv; ring.
Qed.

(** [ht_convex] (theorem).
 Mathematical meaning: Linear mixing of observed score totals is compatible with linear prediction. This establishes combined observed-plus-predicted score total for arbitrary unequal observed-score contributions.
 Exact checked proposition: forall (n k c s t q:R), ht n k c (q*s+(1-q)*t) = q*ht n k c (s)+(1-q)*ht n k c (t).
 Premises and side conditions: The proposition compares total real-arithmetic
 expressions with a common equicorrelation conditioning denominator. Under a
 probabilistic interpretation, valid positive covariance-domain and sampling
 premises must be supplied separately; no Gaussian regression theorem is assumed.
 Proof/definition method: Unfold only the canonical linear-forecast wrappers
 and invoke Stdlib Ring for exact polynomial normalization, never floating-point
 experiments or manually duplicated finite-list recursions.
 Library reuse: SequentialReport.sequential_d and Rocq Stdlib Reals/Ring;
 existing definitions are preserved as one authoritative report denominator.
 Boundary: Deterministic linearity/contrast/increment relation only; it does
 not establish distributional conditional expectation or confidence coverage.
*)
Theorem ht_convex : forall (n k c s t q:R), ht n k c (q*s+(1-q)*t) = q*ht n k c (s)+(1-q)*ht n k c (t).
Proof.
 intros; unfold hp, hf, ht, hm, he, hc, Rdiv; ring.
Qed.

(** [ht_balanced_contrasts] (theorem).
 Mathematical meaning: Two-cohort observed contrasts decompose into corresponding forecast contrasts. This establishes combined observed-plus-predicted score total for arbitrary unequal observed-score contributions.
 Exact checked proposition: forall (n k c s t u v:R), ht n k c (s+t)-ht n k c (u+v) = ht n k c (s-u)+ht n k c (t-v).
 Premises and side conditions: The proposition compares total real-arithmetic
 expressions with a common equicorrelation conditioning denominator. Under a
 probabilistic interpretation, valid positive covariance-domain and sampling
 premises must be supplied separately; no Gaussian regression theorem is assumed.
 Proof/definition method: Unfold only the canonical linear-forecast wrappers
 and invoke Stdlib Ring for exact polynomial normalization, never floating-point
 experiments or manually duplicated finite-list recursions.
 Library reuse: SequentialReport.sequential_d and Rocq Stdlib Reals/Ring;
 existing definitions are preserved as one authoritative report denominator.
 Boundary: Deterministic linearity/contrast/increment relation only; it does
 not establish distributional conditional expectation or confidence coverage.
*)
Theorem ht_balanced_contrasts : forall (n k c s t u v:R), ht n k c (s+t)-ht n k c (u+v) = ht n k c (s-u)+ht n k c (t-v).
Proof.
 intros; unfold hp, hf, ht, hm, he, hc, Rdiv; ring.
Qed.

(** [ht_contrast_pairs] (theorem).
 Mathematical meaning: Two independent score-contrast contributions add on the prediction scale. This establishes combined observed-plus-predicted score total for arbitrary unequal observed-score contributions.
 Exact checked proposition: forall (n k c s t u v:R), ht n k c ((s-t)+(u-v)) = ht n k c (s)-ht n k c (t)+ht n k c (u)-ht n k c (v).
 Premises and side conditions: The proposition compares total real-arithmetic
 expressions with a common equicorrelation conditioning denominator. Under a
 probabilistic interpretation, valid positive covariance-domain and sampling
 premises must be supplied separately; no Gaussian regression theorem is assumed.
 Proof/definition method: Unfold only the canonical linear-forecast wrappers
 and invoke Stdlib Ring for exact polynomial normalization, never floating-point
 experiments or manually duplicated finite-list recursions.
 Library reuse: SequentialReport.sequential_d and Rocq Stdlib Reals/Ring;
 existing definitions are preserved as one authoritative report denominator.
 Boundary: Deterministic linearity/contrast/increment relation only; it does
 not establish distributional conditional expectation or confidence coverage.
*)
Theorem ht_contrast_pairs : forall (n k c s t u v:R), ht n k c ((s-t)+(u-v)) = ht n k c (s)-ht n k c (t)+ht n k c (u)-ht n k c (v).
Proof.
 intros; unfold hp, hf, ht, hm, he, hc, Rdiv; ring.
Qed.

(** [ht_antisymmetry] (theorem).
 Mathematical meaning: Reversing a score contrast exactly reverses the estimated contrast. This establishes combined observed-plus-predicted score total for arbitrary unequal observed-score contributions.
 Exact checked proposition: forall (n k c s t:R), ht n k c (s-t)+ht n k c (t-s) = 0.
 Premises and side conditions: The proposition compares total real-arithmetic
 expressions with a common equicorrelation conditioning denominator. Under a
 probabilistic interpretation, valid positive covariance-domain and sampling
 premises must be supplied separately; no Gaussian regression theorem is assumed.
 Proof/definition method: Unfold only the canonical linear-forecast wrappers
 and invoke Stdlib Ring for exact polynomial normalization, never floating-point
 experiments or manually duplicated finite-list recursions.
 Library reuse: SequentialReport.sequential_d and Rocq Stdlib Reals/Ring;
 existing definitions are preserved as one authoritative report denominator.
 Boundary: Deterministic linearity/contrast/increment relation only; it does
 not establish distributional conditional expectation or confidence coverage.
*)
Theorem ht_antisymmetry : forall (n k c s t:R), ht n k c (s-t)+ht n k c (t-s) = 0.
Proof.
 intros; unfold hp, hf, ht, hm, he, hc, Rdiv; ring.
Qed.

(** [ht_contrast_of_contrasts] (theorem).
 Mathematical meaning: Difference-in-differences for score totals is preserved by the estimator. This establishes combined observed-plus-predicted score total for arbitrary unequal observed-score contributions.
 Exact checked proposition: forall (n k c s t u v:R), ht n k c ((s-t)-(u-v)) = ht n k c (s)-ht n k c (t)-ht n k c (u)+ht n k c (v).
 Premises and side conditions: The proposition compares total real-arithmetic
 expressions with a common equicorrelation conditioning denominator. Under a
 probabilistic interpretation, valid positive covariance-domain and sampling
 premises must be supplied separately; no Gaussian regression theorem is assumed.
 Proof/definition method: Unfold only the canonical linear-forecast wrappers
 and invoke Stdlib Ring for exact polynomial normalization, never floating-point
 experiments or manually duplicated finite-list recursions.
 Library reuse: SequentialReport.sequential_d and Rocq Stdlib Reals/Ring;
 existing definitions are preserved as one authoritative report denominator.
 Boundary: Deterministic linearity/contrast/increment relation only; it does
 not establish distributional conditional expectation or confidence coverage.
*)
Theorem ht_contrast_of_contrasts : forall (n k c s t u v:R), ht n k c ((s-t)-(u-v)) = ht n k c (s)-ht n k c (t)-ht n k c (u)+ht n k c (v).
Proof.
 intros; unfold hp, hf, ht, hm, he, hc, Rdiv; ring.
Qed.

(** [ht_weighted_three] (theorem).
 Mathematical meaning: Three-way weighted score aggregation commutes with the estimator. This establishes combined observed-plus-predicted score total for arbitrary unequal observed-score contributions.
 Exact checked proposition: forall (n k c s t u v q:R), ht n k c (q*s+u*t+v) = q*ht n k c (s)+u*ht n k c (t)+ht n k c (v).
 Premises and side conditions: The proposition compares total real-arithmetic
 expressions with a common equicorrelation conditioning denominator. Under a
 probabilistic interpretation, valid positive covariance-domain and sampling
 premises must be supplied separately; no Gaussian regression theorem is assumed.
 Proof/definition method: Unfold only the canonical linear-forecast wrappers
 and invoke Stdlib Ring for exact polynomial normalization, never floating-point
 experiments or manually duplicated finite-list recursions.
 Library reuse: SequentialReport.sequential_d and Rocq Stdlib Reals/Ring;
 existing definitions are preserved as one authoritative report denominator.
 Boundary: Deterministic linearity/contrast/increment relation only; it does
 not establish distributional conditional expectation or confidence coverage.
*)
Theorem ht_weighted_three : forall (n k c s t u v q:R), ht n k c (q*s+u*t+v) = q*ht n k c (s)+u*ht n k c (t)+ht n k c (v).
Proof.
 intros; unfold hp, hf, ht, hm, he, hc, Rdiv; ring.
Qed.

(** [hm_zero] (theorem).
 Mathematical meaning: A zero-sum standardized history contributes no linear predictor. This establishes inclusive observed-and-future predicted score mean for arbitrary unequal observed-score contributions.
 Exact checked proposition: forall (n k c:R), hm n k c (0) = 0.
 Premises and side conditions: The proposition compares total real-arithmetic
 expressions with a common equicorrelation conditioning denominator. Under a
 probabilistic interpretation, valid positive covariance-domain and sampling
 premises must be supplied separately; no Gaussian regression theorem is assumed.
 Proof/definition method: Unfold only the canonical linear-forecast wrappers
 and invoke Stdlib Ring for exact polynomial normalization, never floating-point
 experiments or manually duplicated finite-list recursions.
 Library reuse: SequentialReport.sequential_d and Rocq Stdlib Reals/Ring;
 existing definitions are preserved as one authoritative report denominator.
 Boundary: Deterministic linearity/contrast/increment relation only; it does
 not establish distributional conditional expectation or confidence coverage.
*)
Theorem hm_zero : forall (n k c:R), hm n k c (0) = 0.
Proof.
 intros; unfold hp, hf, ht, hm, he, hc, Rdiv; ring.
Qed.

(** [hm_add] (theorem).
 Mathematical meaning: Combining two score-total contributions is additive at fixed design. This establishes inclusive observed-and-future predicted score mean for arbitrary unequal observed-score contributions.
 Exact checked proposition: forall (n k c s t:R), hm n k c (s+t) = hm n k c (s)+hm n k c (t).
 Premises and side conditions: The proposition compares total real-arithmetic
 expressions with a common equicorrelation conditioning denominator. Under a
 probabilistic interpretation, valid positive covariance-domain and sampling
 premises must be supplied separately; no Gaussian regression theorem is assumed.
 Proof/definition method: Unfold only the canonical linear-forecast wrappers
 and invoke Stdlib Ring for exact polynomial normalization, never floating-point
 experiments or manually duplicated finite-list recursions.
 Library reuse: SequentialReport.sequential_d and Rocq Stdlib Reals/Ring;
 existing definitions are preserved as one authoritative report denominator.
 Boundary: Deterministic linearity/contrast/increment relation only; it does
 not establish distributional conditional expectation or confidence coverage.
*)
Theorem hm_add : forall (n k c s t:R), hm n k c (s+t) = hm n k c (s)+hm n k c (t).
Proof.
 intros; unfold hp, hf, ht, hm, he, hc, Rdiv; ring.
Qed.

(** [hm_subtract] (theorem).
 Mathematical meaning: A score-total contrast propagates linearly to the report estimator. This establishes inclusive observed-and-future predicted score mean for arbitrary unequal observed-score contributions.
 Exact checked proposition: forall (n k c s t:R), hm n k c (s-t) = hm n k c (s)-hm n k c (t).
 Premises and side conditions: The proposition compares total real-arithmetic
 expressions with a common equicorrelation conditioning denominator. Under a
 probabilistic interpretation, valid positive covariance-domain and sampling
 premises must be supplied separately; no Gaussian regression theorem is assumed.
 Proof/definition method: Unfold only the canonical linear-forecast wrappers
 and invoke Stdlib Ring for exact polynomial normalization, never floating-point
 experiments or manually duplicated finite-list recursions.
 Library reuse: SequentialReport.sequential_d and Rocq Stdlib Reals/Ring;
 existing definitions are preserved as one authoritative report denominator.
 Boundary: Deterministic linearity/contrast/increment relation only; it does
 not establish distributional conditional expectation or confidence coverage.
*)
Theorem hm_subtract : forall (n k c s t:R), hm n k c (s-t) = hm n k c (s)-hm n k c (t).
Proof.
 intros; unfold hp, hf, ht, hm, he, hc, Rdiv; ring.
Qed.

(** [hm_negate] (theorem).
 Mathematical meaning: Changing signs of all centered history scores reverses the estimate. This establishes inclusive observed-and-future predicted score mean for arbitrary unequal observed-score contributions.
 Exact checked proposition: forall (n k c s:R), hm n k c ((-s)) = -hm n k c (s).
 Premises and side conditions: The proposition compares total real-arithmetic
 expressions with a common equicorrelation conditioning denominator. Under a
 probabilistic interpretation, valid positive covariance-domain and sampling
 premises must be supplied separately; no Gaussian regression theorem is assumed.
 Proof/definition method: Unfold only the canonical linear-forecast wrappers
 and invoke Stdlib Ring for exact polynomial normalization, never floating-point
 experiments or manually duplicated finite-list recursions.
 Library reuse: SequentialReport.sequential_d and Rocq Stdlib Reals/Ring;
 existing definitions are preserved as one authoritative report denominator.
 Boundary: Deterministic linearity/contrast/increment relation only; it does
 not establish distributional conditional expectation or confidence coverage.
*)
Theorem hm_negate : forall (n k c s:R), hm n k c ((-s)) = -hm n k c (s).
Proof.
 intros; unfold hp, hf, ht, hm, he, hc, Rdiv; ring.
Qed.

(** [hm_scale] (theorem).
 Mathematical meaning: A common standardized score scaling propagates exactly to the estimate. This establishes inclusive observed-and-future predicted score mean for arbitrary unequal observed-score contributions.
 Exact checked proposition: forall (n k c s q:R), hm n k c (q*s) = q*hm n k c (s).
 Premises and side conditions: The proposition compares total real-arithmetic
 expressions with a common equicorrelation conditioning denominator. Under a
 probabilistic interpretation, valid positive covariance-domain and sampling
 premises must be supplied separately; no Gaussian regression theorem is assumed.
 Proof/definition method: Unfold only the canonical linear-forecast wrappers
 and invoke Stdlib Ring for exact polynomial normalization, never floating-point
 experiments or manually duplicated finite-list recursions.
 Library reuse: SequentialReport.sequential_d and Rocq Stdlib Reals/Ring;
 existing definitions are preserved as one authoritative report denominator.
 Boundary: Deterministic linearity/contrast/increment relation only; it does
 not establish distributional conditional expectation or confidence coverage.
*)
Theorem hm_scale : forall (n k c s q:R), hm n k c (q*s) = q*hm n k c (s).
Proof.
 intros; unfold hp, hf, ht, hm, he, hc, Rdiv; ring.
Qed.

(** [hm_sum_three] (theorem).
 Mathematical meaning: Three disjoint observed subtotal contributions aggregate without loss. This establishes inclusive observed-and-future predicted score mean for arbitrary unequal observed-score contributions.
 Exact checked proposition: forall (n k c s t u:R), hm n k c (s+t+u) = hm n k c (s)+hm n k c (t)+hm n k c (u).
 Premises and side conditions: The proposition compares total real-arithmetic
 expressions with a common equicorrelation conditioning denominator. Under a
 probabilistic interpretation, valid positive covariance-domain and sampling
 premises must be supplied separately; no Gaussian regression theorem is assumed.
 Proof/definition method: Unfold only the canonical linear-forecast wrappers
 and invoke Stdlib Ring for exact polynomial normalization, never floating-point
 experiments or manually duplicated finite-list recursions.
 Library reuse: SequentialReport.sequential_d and Rocq Stdlib Reals/Ring;
 existing definitions are preserved as one authoritative report denominator.
 Boundary: Deterministic linearity/contrast/increment relation only; it does
 not establish distributional conditional expectation or confidence coverage.
*)
Theorem hm_sum_three : forall (n k c s t u:R), hm n k c (s+t+u) = hm n k c (s)+hm n k c (t)+hm n k c (u).
Proof.
 intros; unfold hp, hf, ht, hm, he, hc, Rdiv; ring.
Qed.

(** [hm_sum_four] (theorem).
 Mathematical meaning: Four test-battery subtotals aggregate to the identical forecast. This establishes inclusive observed-and-future predicted score mean for arbitrary unequal observed-score contributions.
 Exact checked proposition: forall (n k c s t u v:R), hm n k c (s+t+u+v) = hm n k c (s)+hm n k c (t)+hm n k c (u)+hm n k c (v).
 Premises and side conditions: The proposition compares total real-arithmetic
 expressions with a common equicorrelation conditioning denominator. Under a
 probabilistic interpretation, valid positive covariance-domain and sampling
 premises must be supplied separately; no Gaussian regression theorem is assumed.
 Proof/definition method: Unfold only the canonical linear-forecast wrappers
 and invoke Stdlib Ring for exact polynomial normalization, never floating-point
 experiments or manually duplicated finite-list recursions.
 Library reuse: SequentialReport.sequential_d and Rocq Stdlib Reals/Ring;
 existing definitions are preserved as one authoritative report denominator.
 Boundary: Deterministic linearity/contrast/increment relation only; it does
 not establish distributional conditional expectation or confidence coverage.
*)
Theorem hm_sum_four : forall (n k c s t u v:R), hm n k c (s+t+u+v) = hm n k c (s)+hm n k c (t)+hm n k c (u)+hm n k c (v).
Proof.
 intros; unfold hp, hf, ht, hm, he, hc, Rdiv; ring.
Qed.

(** [hm_increment] (theorem).
 Mathematical meaning: The marginal effect of adding a history subtotal is independent of baseline. This establishes inclusive observed-and-future predicted score mean for arbitrary unequal observed-score contributions.
 Exact checked proposition: forall (n k c s t:R), hm n k c (s+t)-hm n k c (s) = hm n k c (t).
 Premises and side conditions: The proposition compares total real-arithmetic
 expressions with a common equicorrelation conditioning denominator. Under a
 probabilistic interpretation, valid positive covariance-domain and sampling
 premises must be supplied separately; no Gaussian regression theorem is assumed.
 Proof/definition method: Unfold only the canonical linear-forecast wrappers
 and invoke Stdlib Ring for exact polynomial normalization, never floating-point
 experiments or manually duplicated finite-list recursions.
 Library reuse: SequentialReport.sequential_d and Rocq Stdlib Reals/Ring;
 existing definitions are preserved as one authoritative report denominator.
 Boundary: Deterministic linearity/contrast/increment relation only; it does
 not establish distributional conditional expectation or confidence coverage.
*)
Theorem hm_increment : forall (n k c s t:R), hm n k c (s+t)-hm n k c (s) = hm n k c (t).
Proof.
 intros; unfold hp, hf, ht, hm, he, hc, Rdiv; ring.
Qed.

(** [hm_translation_contrast] (theorem).
 Mathematical meaning: Common observed history cancels from a predicted-score contrast. This establishes inclusive observed-and-future predicted score mean for arbitrary unequal observed-score contributions.
 Exact checked proposition: forall (n k c s t u:R), hm n k c (s+u)-hm n k c (t+u) = hm n k c (s)-hm n k c (t).
 Premises and side conditions: The proposition compares total real-arithmetic
 expressions with a common equicorrelation conditioning denominator. Under a
 probabilistic interpretation, valid positive covariance-domain and sampling
 premises must be supplied separately; no Gaussian regression theorem is assumed.
 Proof/definition method: Unfold only the canonical linear-forecast wrappers
 and invoke Stdlib Ring for exact polynomial normalization, never floating-point
 experiments or manually duplicated finite-list recursions.
 Library reuse: SequentialReport.sequential_d and Rocq Stdlib Reals/Ring;
 existing definitions are preserved as one authoritative report denominator.
 Boundary: Deterministic linearity/contrast/increment relation only; it does
 not establish distributional conditional expectation or confidence coverage.
*)
Theorem hm_translation_contrast : forall (n k c s t u:R), hm n k c (s+u)-hm n k c (t+u) = hm n k c (s)-hm n k c (t).
Proof.
 intros; unfold hp, hf, ht, hm, he, hc, Rdiv; ring.
Qed.

(** [hm_parallelogram] (theorem).
 Mathematical meaning: Opposite history perturbations cancel in their paired estimates. This establishes inclusive observed-and-future predicted score mean for arbitrary unequal observed-score contributions.
 Exact checked proposition: forall (n k c s t:R), hm n k c (s+t)+hm n k c (s-t) = 2*hm n k c (s).
 Premises and side conditions: The proposition compares total real-arithmetic
 expressions with a common equicorrelation conditioning denominator. Under a
 probabilistic interpretation, valid positive covariance-domain and sampling
 premises must be supplied separately; no Gaussian regression theorem is assumed.
 Proof/definition method: Unfold only the canonical linear-forecast wrappers
 and invoke Stdlib Ring for exact polynomial normalization, never floating-point
 experiments or manually duplicated finite-list recursions.
 Library reuse: SequentialReport.sequential_d and Rocq Stdlib Reals/Ring;
 existing definitions are preserved as one authoritative report denominator.
 Boundary: Deterministic linearity/contrast/increment relation only; it does
 not establish distributional conditional expectation or confidence coverage.
*)
Theorem hm_parallelogram : forall (n k c s t:R), hm n k c (s+t)+hm n k c (s-t) = 2*hm n k c (s).
Proof.
 intros; unfold hp, hf, ht, hm, he, hc, Rdiv; ring.
Qed.

(** [hm_convex] (theorem).
 Mathematical meaning: Linear mixing of observed score totals is compatible with linear prediction. This establishes inclusive observed-and-future predicted score mean for arbitrary unequal observed-score contributions.
 Exact checked proposition: forall (n k c s t q:R), hm n k c (q*s+(1-q)*t) = q*hm n k c (s)+(1-q)*hm n k c (t).
 Premises and side conditions: The proposition compares total real-arithmetic
 expressions with a common equicorrelation conditioning denominator. Under a
 probabilistic interpretation, valid positive covariance-domain and sampling
 premises must be supplied separately; no Gaussian regression theorem is assumed.
 Proof/definition method: Unfold only the canonical linear-forecast wrappers
 and invoke Stdlib Ring for exact polynomial normalization, never floating-point
 experiments or manually duplicated finite-list recursions.
 Library reuse: SequentialReport.sequential_d and Rocq Stdlib Reals/Ring;
 existing definitions are preserved as one authoritative report denominator.
 Boundary: Deterministic linearity/contrast/increment relation only; it does
 not establish distributional conditional expectation or confidence coverage.
*)
Theorem hm_convex : forall (n k c s t q:R), hm n k c (q*s+(1-q)*t) = q*hm n k c (s)+(1-q)*hm n k c (t).
Proof.
 intros; unfold hp, hf, ht, hm, he, hc, Rdiv; ring.
Qed.

(** [hm_balanced_contrasts] (theorem).
 Mathematical meaning: Two-cohort observed contrasts decompose into corresponding forecast contrasts. This establishes inclusive observed-and-future predicted score mean for arbitrary unequal observed-score contributions.
 Exact checked proposition: forall (n k c s t u v:R), hm n k c (s+t)-hm n k c (u+v) = hm n k c (s-u)+hm n k c (t-v).
 Premises and side conditions: The proposition compares total real-arithmetic
 expressions with a common equicorrelation conditioning denominator. Under a
 probabilistic interpretation, valid positive covariance-domain and sampling
 premises must be supplied separately; no Gaussian regression theorem is assumed.
 Proof/definition method: Unfold only the canonical linear-forecast wrappers
 and invoke Stdlib Ring for exact polynomial normalization, never floating-point
 experiments or manually duplicated finite-list recursions.
 Library reuse: SequentialReport.sequential_d and Rocq Stdlib Reals/Ring;
 existing definitions are preserved as one authoritative report denominator.
 Boundary: Deterministic linearity/contrast/increment relation only; it does
 not establish distributional conditional expectation or confidence coverage.
*)
Theorem hm_balanced_contrasts : forall (n k c s t u v:R), hm n k c (s+t)-hm n k c (u+v) = hm n k c (s-u)+hm n k c (t-v).
Proof.
 intros; unfold hp, hf, ht, hm, he, hc, Rdiv; ring.
Qed.

(** [hm_contrast_pairs] (theorem).
 Mathematical meaning: Two independent score-contrast contributions add on the prediction scale. This establishes inclusive observed-and-future predicted score mean for arbitrary unequal observed-score contributions.
 Exact checked proposition: forall (n k c s t u v:R), hm n k c ((s-t)+(u-v)) = hm n k c (s)-hm n k c (t)+hm n k c (u)-hm n k c (v).
 Premises and side conditions: The proposition compares total real-arithmetic
 expressions with a common equicorrelation conditioning denominator. Under a
 probabilistic interpretation, valid positive covariance-domain and sampling
 premises must be supplied separately; no Gaussian regression theorem is assumed.
 Proof/definition method: Unfold only the canonical linear-forecast wrappers
 and invoke Stdlib Ring for exact polynomial normalization, never floating-point
 experiments or manually duplicated finite-list recursions.
 Library reuse: SequentialReport.sequential_d and Rocq Stdlib Reals/Ring;
 existing definitions are preserved as one authoritative report denominator.
 Boundary: Deterministic linearity/contrast/increment relation only; it does
 not establish distributional conditional expectation or confidence coverage.
*)
Theorem hm_contrast_pairs : forall (n k c s t u v:R), hm n k c ((s-t)+(u-v)) = hm n k c (s)-hm n k c (t)+hm n k c (u)-hm n k c (v).
Proof.
 intros; unfold hp, hf, ht, hm, he, hc, Rdiv; ring.
Qed.

(** [hm_antisymmetry] (theorem).
 Mathematical meaning: Reversing a score contrast exactly reverses the estimated contrast. This establishes inclusive observed-and-future predicted score mean for arbitrary unequal observed-score contributions.
 Exact checked proposition: forall (n k c s t:R), hm n k c (s-t)+hm n k c (t-s) = 0.
 Premises and side conditions: The proposition compares total real-arithmetic
 expressions with a common equicorrelation conditioning denominator. Under a
 probabilistic interpretation, valid positive covariance-domain and sampling
 premises must be supplied separately; no Gaussian regression theorem is assumed.
 Proof/definition method: Unfold only the canonical linear-forecast wrappers
 and invoke Stdlib Ring for exact polynomial normalization, never floating-point
 experiments or manually duplicated finite-list recursions.
 Library reuse: SequentialReport.sequential_d and Rocq Stdlib Reals/Ring;
 existing definitions are preserved as one authoritative report denominator.
 Boundary: Deterministic linearity/contrast/increment relation only; it does
 not establish distributional conditional expectation or confidence coverage.
*)
Theorem hm_antisymmetry : forall (n k c s t:R), hm n k c (s-t)+hm n k c (t-s) = 0.
Proof.
 intros; unfold hp, hf, ht, hm, he, hc, Rdiv; ring.
Qed.

(** [hm_contrast_of_contrasts] (theorem).
 Mathematical meaning: Difference-in-differences for score totals is preserved by the estimator. This establishes inclusive observed-and-future predicted score mean for arbitrary unequal observed-score contributions.
 Exact checked proposition: forall (n k c s t u v:R), hm n k c ((s-t)-(u-v)) = hm n k c (s)-hm n k c (t)-hm n k c (u)+hm n k c (v).
 Premises and side conditions: The proposition compares total real-arithmetic
 expressions with a common equicorrelation conditioning denominator. Under a
 probabilistic interpretation, valid positive covariance-domain and sampling
 premises must be supplied separately; no Gaussian regression theorem is assumed.
 Proof/definition method: Unfold only the canonical linear-forecast wrappers
 and invoke Stdlib Ring for exact polynomial normalization, never floating-point
 experiments or manually duplicated finite-list recursions.
 Library reuse: SequentialReport.sequential_d and Rocq Stdlib Reals/Ring;
 existing definitions are preserved as one authoritative report denominator.
 Boundary: Deterministic linearity/contrast/increment relation only; it does
 not establish distributional conditional expectation or confidence coverage.
*)
Theorem hm_contrast_of_contrasts : forall (n k c s t u v:R), hm n k c ((s-t)-(u-v)) = hm n k c (s)-hm n k c (t)-hm n k c (u)+hm n k c (v).
Proof.
 intros; unfold hp, hf, ht, hm, he, hc, Rdiv; ring.
Qed.

(** [hm_weighted_three] (theorem).
 Mathematical meaning: Three-way weighted score aggregation commutes with the estimator. This establishes inclusive observed-and-future predicted score mean for arbitrary unequal observed-score contributions.
 Exact checked proposition: forall (n k c s t u v q:R), hm n k c (q*s+u*t+v) = q*hm n k c (s)+u*hm n k c (t)+hm n k c (v).
 Premises and side conditions: The proposition compares total real-arithmetic
 expressions with a common equicorrelation conditioning denominator. Under a
 probabilistic interpretation, valid positive covariance-domain and sampling
 premises must be supplied separately; no Gaussian regression theorem is assumed.
 Proof/definition method: Unfold only the canonical linear-forecast wrappers
 and invoke Stdlib Ring for exact polynomial normalization, never floating-point
 experiments or manually duplicated finite-list recursions.
 Library reuse: SequentialReport.sequential_d and Rocq Stdlib Reals/Ring;
 existing definitions are preserved as one authoritative report denominator.
 Boundary: Deterministic linearity/contrast/increment relation only; it does
 not establish distributional conditional expectation or confidence coverage.
*)
Theorem hm_weighted_three : forall (n k c s t u v q:R), hm n k c (q*s+u*t+v) = q*hm n k c (s)+u*hm n k c (t)+hm n k c (v).
Proof.
 intros; unfold hp, hf, ht, hm, he, hc, Rdiv; ring.
Qed.

(** [he_source_increment] (theorem).
 Mathematical meaning: Adding an observed-score subtotal lowers the fixed-outcome prediction residual by its predicted contribution.
 Exact checked proposition: forall (n c s t x:R), he n c (s+t) x = he n c s x - hp n c t.
 Premises and side conditions: The proposition compares total real-arithmetic
 expressions with a common equicorrelation conditioning denominator. Under a
 probabilistic interpretation, valid positive covariance-domain and sampling
 premises must be supplied separately; no Gaussian regression theorem is assumed.
 Proof/definition method: Unfold only the canonical linear-forecast wrappers
 and invoke Stdlib Ring for exact polynomial normalization, never floating-point
 experiments or manually duplicated finite-list recursions.
 Library reuse: SequentialReport.sequential_d and Rocq Stdlib Reals/Ring;
 existing definitions are preserved as one authoritative report denominator.
 Boundary: Deterministic linearity/contrast/increment relation only; it does
 not establish distributional conditional expectation or confidence coverage.
*)
Theorem he_source_increment : forall (n c s t x:R), he n c (s+t) x = he n c s x - hp n c t.
Proof.
 intros; unfold hp, hf, ht, hm, he, hc, Rdiv; ring.
Qed.

(** [he_source_decrement] (theorem).
 Mathematical meaning: Removing an observed-score subtotal raises the prediction error by its forecast contribution.
 Exact checked proposition: forall (n c s t x:R), he n c (s-t) x = he n c s x + hp n c t.
 Premises and side conditions: The proposition compares total real-arithmetic
 expressions with a common equicorrelation conditioning denominator. Under a
 probabilistic interpretation, valid positive covariance-domain and sampling
 premises must be supplied separately; no Gaussian regression theorem is assumed.
 Proof/definition method: Unfold only the canonical linear-forecast wrappers
 and invoke Stdlib Ring for exact polynomial normalization, never floating-point
 experiments or manually duplicated finite-list recursions.
 Library reuse: SequentialReport.sequential_d and Rocq Stdlib Reals/Ring;
 existing definitions are preserved as one authoritative report denominator.
 Boundary: Deterministic linearity/contrast/increment relation only; it does
 not establish distributional conditional expectation or confidence coverage.
*)
Theorem he_source_decrement : forall (n c s t x:R), he n c (s-t) x = he n c s x + hp n c t.
Proof.
 intros; unfold hp, hf, ht, hm, he, hc, Rdiv; ring.
Qed.

(** [he_outcome_increment] (theorem).
 Mathematical meaning: A realized future-score perturbation enters the residual with coefficient one.
 Exact checked proposition: forall (n c s x y:R), he n c s (x+y) = he n c s x + y.
 Premises and side conditions: The proposition compares total real-arithmetic
 expressions with a common equicorrelation conditioning denominator. Under a
 probabilistic interpretation, valid positive covariance-domain and sampling
 premises must be supplied separately; no Gaussian regression theorem is assumed.
 Proof/definition method: Unfold only the canonical linear-forecast wrappers
 and invoke Stdlib Ring for exact polynomial normalization, never floating-point
 experiments or manually duplicated finite-list recursions.
 Library reuse: SequentialReport.sequential_d and Rocq Stdlib Reals/Ring;
 existing definitions are preserved as one authoritative report denominator.
 Boundary: Deterministic linearity/contrast/increment relation only; it does
 not establish distributional conditional expectation or confidence coverage.
*)
Theorem he_outcome_increment : forall (n c s x y:R), he n c s (x+y) = he n c s x + y.
Proof.
 intros; unfold hp, hf, ht, hm, he, hc, Rdiv; ring.
Qed.

(** [he_outcome_decrement] (theorem).
 Mathematical meaning: Subtraction of a future observation perturbation is exactly reflected in residuals.
 Exact checked proposition: forall (n c s x y:R), he n c s (x-y) = he n c s x - y.
 Premises and side conditions: The proposition compares total real-arithmetic
 expressions with a common equicorrelation conditioning denominator. Under a
 probabilistic interpretation, valid positive covariance-domain and sampling
 premises must be supplied separately; no Gaussian regression theorem is assumed.
 Proof/definition method: Unfold only the canonical linear-forecast wrappers
 and invoke Stdlib Ring for exact polynomial normalization, never floating-point
 experiments or manually duplicated finite-list recursions.
 Library reuse: SequentialReport.sequential_d and Rocq Stdlib Reals/Ring;
 existing definitions are preserved as one authoritative report denominator.
 Boundary: Deterministic linearity/contrast/increment relation only; it does
 not establish distributional conditional expectation or confidence coverage.
*)
Theorem he_outcome_decrement : forall (n c s x y:R), he n c s (x-y) = he n c s x - y.
Proof.
 intros; unfold hp, hf, ht, hm, he, hc, Rdiv; ring.
Qed.

(** [he_joint_add] (theorem).
 Mathematical meaning: Two hypothetical score/observation pairs have exactly additive forecast innovations.
 Exact checked proposition: forall (n c s t x y:R), he n c (s+t) (x+y) = he n c s x + he n c t y.
 Premises and side conditions: The proposition compares total real-arithmetic
 expressions with a common equicorrelation conditioning denominator. Under a
 probabilistic interpretation, valid positive covariance-domain and sampling
 premises must be supplied separately; no Gaussian regression theorem is assumed.
 Proof/definition method: Unfold only the canonical linear-forecast wrappers
 and invoke Stdlib Ring for exact polynomial normalization, never floating-point
 experiments or manually duplicated finite-list recursions.
 Library reuse: SequentialReport.sequential_d and Rocq Stdlib Reals/Ring;
 existing definitions are preserved as one authoritative report denominator.
 Boundary: Deterministic linearity/contrast/increment relation only; it does
 not establish distributional conditional expectation or confidence coverage.
*)
Theorem he_joint_add : forall (n c s t x y:R), he n c (s+t) (x+y) = he n c s x + he n c t y.
Proof.
 intros; unfold hp, hf, ht, hm, he, hc, Rdiv; ring.
Qed.

(** [he_joint_sub] (theorem).
 Mathematical meaning: Contrasts between observed and future score pairs respect signed differences.
 Exact checked proposition: forall (n c s t x y:R), he n c (s-t) (x-y) = he n c s x - he n c t y.
 Premises and side conditions: The proposition compares total real-arithmetic
 expressions with a common equicorrelation conditioning denominator. Under a
 probabilistic interpretation, valid positive covariance-domain and sampling
 premises must be supplied separately; no Gaussian regression theorem is assumed.
 Proof/definition method: Unfold only the canonical linear-forecast wrappers
 and invoke Stdlib Ring for exact polynomial normalization, never floating-point
 experiments or manually duplicated finite-list recursions.
 Library reuse: SequentialReport.sequential_d and Rocq Stdlib Reals/Ring;
 existing definitions are preserved as one authoritative report denominator.
 Boundary: Deterministic linearity/contrast/increment relation only; it does
 not establish distributional conditional expectation or confidence coverage.
*)
Theorem he_joint_sub : forall (n c s t x y:R), he n c (s-t) (x-y) = he n c s x - he n c t y.
Proof.
 intros; unfold hp, hf, ht, hm, he, hc, Rdiv; ring.
Qed.

(** [he_joint_scale] (theorem).
 Mathematical meaning: Uniform scale changes preserve the dimensionless innovation relationship.
 Exact checked proposition: forall (n c s x q:R), he n c (q*s) (q*x) = q*he n c s x.
 Premises and side conditions: The proposition compares total real-arithmetic
 expressions with a common equicorrelation conditioning denominator. Under a
 probabilistic interpretation, valid positive covariance-domain and sampling
 premises must be supplied separately; no Gaussian regression theorem is assumed.
 Proof/definition method: Unfold only the canonical linear-forecast wrappers
 and invoke Stdlib Ring for exact polynomial normalization, never floating-point
 experiments or manually duplicated finite-list recursions.
 Library reuse: SequentialReport.sequential_d and Rocq Stdlib Reals/Ring;
 existing definitions are preserved as one authoritative report denominator.
 Boundary: Deterministic linearity/contrast/increment relation only; it does
 not establish distributional conditional expectation or confidence coverage.
*)
Theorem he_joint_scale : forall (n c s x q:R), he n c (q*s) (q*x) = q*he n c s x.
Proof.
 intros; unfold hp, hf, ht, hm, he, hc, Rdiv; ring.
Qed.

(** [he_joint_neg] (theorem).
 Mathematical meaning: Opposite centered histories and outcomes reverse prediction errors.
 Exact checked proposition: forall (n c s x:R), he n c (-s) (-x) = -he n c s x.
 Premises and side conditions: The proposition compares total real-arithmetic
 expressions with a common equicorrelation conditioning denominator. Under a
 probabilistic interpretation, valid positive covariance-domain and sampling
 premises must be supplied separately; no Gaussian regression theorem is assumed.
 Proof/definition method: Unfold only the canonical linear-forecast wrappers
 and invoke Stdlib Ring for exact polynomial normalization, never floating-point
 experiments or manually duplicated finite-list recursions.
 Library reuse: SequentialReport.sequential_d and Rocq Stdlib Reals/Ring;
 existing definitions are preserved as one authoritative report denominator.
 Boundary: Deterministic linearity/contrast/increment relation only; it does
 not establish distributional conditional expectation or confidence coverage.
*)
Theorem he_joint_neg : forall (n c s x:R), he n c (-s) (-x) = -he n c s x.
Proof.
 intros; unfold hp, hf, ht, hm, he, hc, Rdiv; ring.
Qed.

(** [he_on_prediction] (theorem).
 Mathematical meaning: A future score equal to its own linear prediction has exactly zero innovation.
 Exact checked proposition: forall (n c s:R), he n c s (hp n c s) = 0.
 Premises and side conditions: The proposition compares total real-arithmetic
 expressions with a common equicorrelation conditioning denominator. Under a
 probabilistic interpretation, valid positive covariance-domain and sampling
 premises must be supplied separately; no Gaussian regression theorem is assumed.
 Proof/definition method: Unfold only the canonical linear-forecast wrappers
 and invoke Stdlib Ring for exact polynomial normalization, never floating-point
 experiments or manually duplicated finite-list recursions.
 Library reuse: SequentialReport.sequential_d and Rocq Stdlib Reals/Ring;
 existing definitions are preserved as one authoritative report denominator.
 Boundary: Deterministic linearity/contrast/increment relation only; it does
 not establish distributional conditional expectation or confidence coverage.
*)
Theorem he_on_prediction : forall (n c s:R), he n c s (hp n c s) = 0.
Proof.
 intros; unfold hp, hf, ht, hm, he, hc, Rdiv; ring.
Qed.

(** [he_on_prediction_plus] (theorem).
 Mathematical meaning: The innovation recovers an additive deviation from the predicted score.
 Exact checked proposition: forall (n c s t:R), he n c s (hp n c s+t) = t.
 Premises and side conditions: The proposition compares total real-arithmetic
 expressions with a common equicorrelation conditioning denominator. Under a
 probabilistic interpretation, valid positive covariance-domain and sampling
 premises must be supplied separately; no Gaussian regression theorem is assumed.
 Proof/definition method: Unfold only the canonical linear-forecast wrappers
 and invoke Stdlib Ring for exact polynomial normalization, never floating-point
 experiments or manually duplicated finite-list recursions.
 Library reuse: SequentialReport.sequential_d and Rocq Stdlib Reals/Ring;
 existing definitions are preserved as one authoritative report denominator.
 Boundary: Deterministic linearity/contrast/increment relation only; it does
 not establish distributional conditional expectation or confidence coverage.
*)
Theorem he_on_prediction_plus : forall (n c s t:R), he n c s (hp n c s+t) = t.
Proof.
 intros; unfold hp, hf, ht, hm, he, hc, Rdiv; ring.
Qed.

(** [he_shifted_history] (theorem).
 Mathematical meaning: An unchanged prior forecast becomes an error under a new observed subtotal.
 Exact checked proposition: forall (n c s t:R), he n c (s+t) (hp n c s) = -hp n c t.
 Premises and side conditions: The proposition compares total real-arithmetic
 expressions with a common equicorrelation conditioning denominator. Under a
 probabilistic interpretation, valid positive covariance-domain and sampling
 premises must be supplied separately; no Gaussian regression theorem is assumed.
 Proof/definition method: Unfold only the canonical linear-forecast wrappers
 and invoke Stdlib Ring for exact polynomial normalization, never floating-point
 experiments or manually duplicated finite-list recursions.
 Library reuse: SequentialReport.sequential_d and Rocq Stdlib Reals/Ring;
 existing definitions are preserved as one authoritative report denominator.
 Boundary: Deterministic linearity/contrast/increment relation only; it does
 not establish distributional conditional expectation or confidence coverage.
*)
Theorem he_shifted_history : forall (n c s t:R), he n c (s+t) (hp n c s) = -hp n c t.
Proof.
 intros; unfold hp, hf, ht, hm, he, hc, Rdiv; ring.
Qed.

(** [he_updated_prediction] (theorem).
 Mathematical meaning: Updating the prediction by the new subtotal restores zero innovation.
 Exact checked proposition: forall (n c s t:R), he n c (s+t) (hp n c s+hp n c t) = 0.
 Premises and side conditions: The proposition compares total real-arithmetic
 expressions with a common equicorrelation conditioning denominator. Under a
 probabilistic interpretation, valid positive covariance-domain and sampling
 premises must be supplied separately; no Gaussian regression theorem is assumed.
 Proof/definition method: Unfold only the canonical linear-forecast wrappers
 and invoke Stdlib Ring for exact polynomial normalization, never floating-point
 experiments or manually duplicated finite-list recursions.
 Library reuse: SequentialReport.sequential_d and Rocq Stdlib Reals/Ring;
 existing definitions are preserved as one authoritative report denominator.
 Boundary: Deterministic linearity/contrast/increment relation only; it does
 not establish distributional conditional expectation or confidence coverage.
*)
Theorem he_updated_prediction : forall (n c s t:R), he n c (s+t) (hp n c s+hp n c t) = 0.
Proof.
 intros; unfold hp, hf, ht, hm, he, hc, Rdiv; ring.
Qed.

(** [he_outcome_contrast] (theorem).
 Mathematical meaning: Two future outcomes under the same observed history have unchanged contrast.
 Exact checked proposition: forall (n c s x y:R), he n c s x-he n c s y=x-y.
 Premises and side conditions: The proposition compares total real-arithmetic
 expressions with a common equicorrelation conditioning denominator. Under a
 probabilistic interpretation, valid positive covariance-domain and sampling
 premises must be supplied separately; no Gaussian regression theorem is assumed.
 Proof/definition method: Unfold only the canonical linear-forecast wrappers
 and invoke Stdlib Ring for exact polynomial normalization, never floating-point
 experiments or manually duplicated finite-list recursions.
 Library reuse: SequentialReport.sequential_d and Rocq Stdlib Reals/Ring;
 existing definitions are preserved as one authoritative report denominator.
 Boundary: Deterministic linearity/contrast/increment relation only; it does
 not establish distributional conditional expectation or confidence coverage.
*)
Theorem he_outcome_contrast : forall (n c s x y:R), he n c s x-he n c s y=x-y.
Proof.
 intros; unfold hp, hf, ht, hm, he, hc, Rdiv; ring.
Qed.

(** [he_history_contrast] (theorem).
 Mathematical meaning: Comparing residuals for one outcome isolates the opposite prediction contrast.
 Exact checked proposition: forall (n c s t x:R), he n c s x-he n c t x=hp n c t-hp n c s.
 Premises and side conditions: The proposition compares total real-arithmetic
 expressions with a common equicorrelation conditioning denominator. Under a
 probabilistic interpretation, valid positive covariance-domain and sampling
 premises must be supplied separately; no Gaussian regression theorem is assumed.
 Proof/definition method: Unfold only the canonical linear-forecast wrappers
 and invoke Stdlib Ring for exact polynomial normalization, never floating-point
 experiments or manually duplicated finite-list recursions.
 Library reuse: SequentialReport.sequential_d and Rocq Stdlib Reals/Ring;
 existing definitions are preserved as one authoritative report denominator.
 Boundary: Deterministic linearity/contrast/increment relation only; it does
 not establish distributional conditional expectation or confidence coverage.
*)
Theorem he_history_contrast : forall (n c s t x:R), he n c s x-he n c t x=hp n c t-hp n c s.
Proof.
 intros; unfold hp, hf, ht, hm, he, hc, Rdiv; ring.
Qed.

(** [hc_zero_baseline] (theorem).
 Mathematical meaning: Centering at zero recovers the standardized arbitrary-history forecast.
 Exact checked proposition: forall (n c s:R), hc n c s 0 = hp n c s.
 Premises and side conditions: The proposition compares total real-arithmetic
 expressions with a common equicorrelation conditioning denominator. Under a
 probabilistic interpretation, valid positive covariance-domain and sampling
 premises must be supplied separately; no Gaussian regression theorem is assumed.
 Proof/definition method: Unfold only the canonical linear-forecast wrappers
 and invoke Stdlib Ring for exact polynomial normalization, never floating-point
 experiments or manually duplicated finite-list recursions.
 Library reuse: SequentialReport.sequential_d and Rocq Stdlib Reals/Ring;
 existing definitions are preserved as one authoritative report denominator.
 Boundary: Deterministic linearity/contrast/increment relation only; it does
 not establish distributional conditional expectation or confidence coverage.
*)
Theorem hc_zero_baseline : forall (n c s:R), hc n c s 0 = hp n c s.
Proof.
 intros; unfold hp, hf, ht, hm, he, hc, Rdiv; ring.
Qed.

(** [hc_at_own_baseline] (theorem).
 Mathematical meaning: An initial score total exactly at the baseline has baseline prediction.
 Exact checked proposition: forall (n c mu:R), hc n c (n*mu) mu = mu.
 Premises and side conditions: The proposition compares total real-arithmetic
 expressions with a common equicorrelation conditioning denominator. Under a
 probabilistic interpretation, valid positive covariance-domain and sampling
 premises must be supplied separately; no Gaussian regression theorem is assumed.
 Proof/definition method: Unfold only the canonical linear-forecast wrappers
 and invoke Stdlib Ring for exact polynomial normalization, never floating-point
 experiments or manually duplicated finite-list recursions.
 Library reuse: SequentialReport.sequential_d and Rocq Stdlib Reals/Ring;
 existing definitions are preserved as one authoritative report denominator.
 Boundary: Deterministic linearity/contrast/increment relation only; it does
 not establish distributional conditional expectation or confidence coverage.
*)
Theorem hc_at_own_baseline : forall (n c mu:R), hc n c (n*mu) mu = mu.
Proof.
 intros; unfold hp, hf, ht, hm, he, hc, Rdiv; ring.
Qed.

(** [hc_add_history] (theorem).
 Mathematical meaning: The centered predicted score responds additively to extra observed totals.
 Exact checked proposition: forall (n c s t mu:R), hc n c (s+t) mu = hc n c s mu + hp n c t.
 Premises and side conditions: The proposition compares total real-arithmetic
 expressions with a common equicorrelation conditioning denominator. Under a
 probabilistic interpretation, valid positive covariance-domain and sampling
 premises must be supplied separately; no Gaussian regression theorem is assumed.
 Proof/definition method: Unfold only the canonical linear-forecast wrappers
 and invoke Stdlib Ring for exact polynomial normalization, never floating-point
 experiments or manually duplicated finite-list recursions.
 Library reuse: SequentialReport.sequential_d and Rocq Stdlib Reals/Ring;
 existing definitions are preserved as one authoritative report denominator.
 Boundary: Deterministic linearity/contrast/increment relation only; it does
 not establish distributional conditional expectation or confidence coverage.
*)
Theorem hc_add_history : forall (n c s t mu:R), hc n c (s+t) mu = hc n c s mu + hp n c t.
Proof.
 intros; unfold hp, hf, ht, hm, he, hc, Rdiv; ring.
Qed.

(** [hc_sub_history] (theorem).
 Mathematical meaning: An observed-score removal reduces the baseline-centered forecast.
 Exact checked proposition: forall (n c s t mu:R), hc n c (s-t) mu = hc n c s mu - hp n c t.
 Premises and side conditions: The proposition compares total real-arithmetic
 expressions with a common equicorrelation conditioning denominator. Under a
 probabilistic interpretation, valid positive covariance-domain and sampling
 premises must be supplied separately; no Gaussian regression theorem is assumed.
 Proof/definition method: Unfold only the canonical linear-forecast wrappers
 and invoke Stdlib Ring for exact polynomial normalization, never floating-point
 experiments or manually duplicated finite-list recursions.
 Library reuse: SequentialReport.sequential_d and Rocq Stdlib Reals/Ring;
 existing definitions are preserved as one authoritative report denominator.
 Boundary: Deterministic linearity/contrast/increment relation only; it does
 not establish distributional conditional expectation or confidence coverage.
*)
Theorem hc_sub_history : forall (n c s t mu:R), hc n c (s-t) mu = hc n c s mu - hp n c t.
Proof.
 intros; unfold hp, hf, ht, hm, he, hc, Rdiv; ring.
Qed.

(** [hc_baseline_up] (theorem).
 Mathematical meaning: Changing reference means shifts both the prediction intercept and centered history.
 Exact checked proposition: forall (n c s mu t:R), hc n c s (mu+t) = hc n c s mu + t-hp n c (n*t).
 Premises and side conditions: The proposition compares total real-arithmetic
 expressions with a common equicorrelation conditioning denominator. Under a
 probabilistic interpretation, valid positive covariance-domain and sampling
 premises must be supplied separately; no Gaussian regression theorem is assumed.
 Proof/definition method: Unfold only the canonical linear-forecast wrappers
 and invoke Stdlib Ring for exact polynomial normalization, never floating-point
 experiments or manually duplicated finite-list recursions.
 Library reuse: SequentialReport.sequential_d and Rocq Stdlib Reals/Ring;
 existing definitions are preserved as one authoritative report denominator.
 Boundary: Deterministic linearity/contrast/increment relation only; it does
 not establish distributional conditional expectation or confidence coverage.
*)
Theorem hc_baseline_up : forall (n c s mu t:R), hc n c s (mu+t) = hc n c s mu + t-hp n c (n*t).
Proof.
 intros; unfold hp, hf, ht, hm, he, hc, Rdiv; ring.
Qed.

(** [hc_baseline_down] (theorem).
 Mathematical meaning: Lowering the baseline has exactly the opposite centered-score adjustment.
 Exact checked proposition: forall (n c s mu t:R), hc n c s (mu-t) = hc n c s mu - t+hp n c (n*t).
 Premises and side conditions: The proposition compares total real-arithmetic
 expressions with a common equicorrelation conditioning denominator. Under a
 probabilistic interpretation, valid positive covariance-domain and sampling
 premises must be supplied separately; no Gaussian regression theorem is assumed.
 Proof/definition method: Unfold only the canonical linear-forecast wrappers
 and invoke Stdlib Ring for exact polynomial normalization, never floating-point
 experiments or manually duplicated finite-list recursions.
 Library reuse: SequentialReport.sequential_d and Rocq Stdlib Reals/Ring;
 existing definitions are preserved as one authoritative report denominator.
 Boundary: Deterministic linearity/contrast/increment relation only; it does
 not establish distributional conditional expectation or confidence coverage.
*)
Theorem hc_baseline_down : forall (n c s mu t:R), hc n c s (mu-t) = hc n c s mu - t+hp n c (n*t).
Proof.
 intros; unfold hp, hf, ht, hm, he, hc, Rdiv; ring.
Qed.

(** [hc_joint_translation] (theorem).
 Mathematical meaning: Shifting every observed score and the baseline translates the prediction by the same amount.
 Exact checked proposition: forall (n c s mu t:R), hc n c (s+n*t) (mu+t) = hc n c s mu+t.
 Premises and side conditions: The proposition compares total real-arithmetic
 expressions with a common equicorrelation conditioning denominator. Under a
 probabilistic interpretation, valid positive covariance-domain and sampling
 premises must be supplied separately; no Gaussian regression theorem is assumed.
 Proof/definition method: Unfold only the canonical linear-forecast wrappers
 and invoke Stdlib Ring for exact polynomial normalization, never floating-point
 experiments or manually duplicated finite-list recursions.
 Library reuse: SequentialReport.sequential_d and Rocq Stdlib Reals/Ring;
 existing definitions are preserved as one authoritative report denominator.
 Boundary: Deterministic linearity/contrast/increment relation only; it does
 not establish distributional conditional expectation or confidence coverage.
*)
Theorem hc_joint_translation : forall (n c s mu t:R), hc n c (s+n*t) (mu+t) = hc n c s mu+t.
Proof.
 intros; unfold hp, hf, ht, hm, he, hc, Rdiv; ring.
Qed.

(** [hc_joint_translation_inverse] (theorem).
 Mathematical meaning: Undoing a scale-center translation recovers the appropriately shifted prediction.
 Exact checked proposition: forall (n c s mu t:R), hc n c (s-n*t) (mu-t) = hc n c s mu-t.
 Premises and side conditions: The proposition compares total real-arithmetic
 expressions with a common equicorrelation conditioning denominator. Under a
 probabilistic interpretation, valid positive covariance-domain and sampling
 premises must be supplied separately; no Gaussian regression theorem is assumed.
 Proof/definition method: Unfold only the canonical linear-forecast wrappers
 and invoke Stdlib Ring for exact polynomial normalization, never floating-point
 experiments or manually duplicated finite-list recursions.
 Library reuse: SequentialReport.sequential_d and Rocq Stdlib Reals/Ring;
 existing definitions are preserved as one authoritative report denominator.
 Boundary: Deterministic linearity/contrast/increment relation only; it does
 not establish distributional conditional expectation or confidence coverage.
*)
Theorem hc_joint_translation_inverse : forall (n c s mu t:R), hc n c (s-n*t) (mu-t) = hc n c s mu-t.
Proof.
 intros; unfold hp, hf, ht, hm, he, hc, Rdiv; ring.
Qed.

(** [hc_joint_scale] (theorem).
 Mathematical meaning: Affine IQ scoring with a common scale factor commutes with centered prediction.
 Exact checked proposition: forall (n c s mu q:R), hc n c (q*s) (q*mu) = q*hc n c s mu.
 Premises and side conditions: The proposition compares total real-arithmetic
 expressions with a common equicorrelation conditioning denominator. Under a
 probabilistic interpretation, valid positive covariance-domain and sampling
 premises must be supplied separately; no Gaussian regression theorem is assumed.
 Proof/definition method: Unfold only the canonical linear-forecast wrappers
 and invoke Stdlib Ring for exact polynomial normalization, never floating-point
 experiments or manually duplicated finite-list recursions.
 Library reuse: SequentialReport.sequential_d and Rocq Stdlib Reals/Ring;
 existing definitions are preserved as one authoritative report denominator.
 Boundary: Deterministic linearity/contrast/increment relation only; it does
 not establish distributional conditional expectation or confidence coverage.
*)
Theorem hc_joint_scale : forall (n c s mu q:R), hc n c (q*s) (q*mu) = q*hc n c s mu.
Proof.
 intros; unfold hp, hf, ht, hm, he, hc, Rdiv; ring.
Qed.

(** [hc_joint_negate] (theorem).
 Mathematical meaning: Simultaneous sign reversal of score totals and reference mean reverses prediction.
 Exact checked proposition: forall (n c s mu:R), hc n c (-s) (-mu) = -hc n c s mu.
 Premises and side conditions: The proposition compares total real-arithmetic
 expressions with a common equicorrelation conditioning denominator. Under a
 probabilistic interpretation, valid positive covariance-domain and sampling
 premises must be supplied separately; no Gaussian regression theorem is assumed.
 Proof/definition method: Unfold only the canonical linear-forecast wrappers
 and invoke Stdlib Ring for exact polynomial normalization, never floating-point
 experiments or manually duplicated finite-list recursions.
 Library reuse: SequentialReport.sequential_d and Rocq Stdlib Reals/Ring;
 existing definitions are preserved as one authoritative report denominator.
 Boundary: Deterministic linearity/contrast/increment relation only; it does
 not establish distributional conditional expectation or confidence coverage.
*)
Theorem hc_joint_negate : forall (n c s mu:R), hc n c (-s) (-mu) = -hc n c s mu.
Proof.
 intros; unfold hp, hf, ht, hm, he, hc, Rdiv; ring.
Qed.

(** [hc_general_affine] (theorem).
 Mathematical meaning: Independent changes to the initial score sum and baseline have a precise combined sensitivity.
 Exact checked proposition: forall (n c s t mu v:R), hc n c (s+t) (mu+v) = hc n c s mu+v+hp n c (t-n*v).
 Premises and side conditions: The proposition compares total real-arithmetic
 expressions with a common equicorrelation conditioning denominator. Under a
 probabilistic interpretation, valid positive covariance-domain and sampling
 premises must be supplied separately; no Gaussian regression theorem is assumed.
 Proof/definition method: Unfold only the canonical linear-forecast wrappers
 and invoke Stdlib Ring for exact polynomial normalization, never floating-point
 experiments or manually duplicated finite-list recursions.
 Library reuse: SequentialReport.sequential_d and Rocq Stdlib Reals/Ring;
 existing definitions are preserved as one authoritative report denominator.
 Boundary: Deterministic linearity/contrast/increment relation only; it does
 not establish distributional conditional expectation or confidence coverage.
*)
Theorem hc_general_affine : forall (n c s t mu v:R), hc n c (s+t) (mu+v) = hc n c s mu+v+hp n c (t-n*v).
Proof.
 intros; unfold hp, hf, ht, hm, he, hc, Rdiv; ring.
Qed.

(** [hc_history_difference] (theorem).
 Mathematical meaning: Difference in conditional centered predictions isolates added historical evidence.
 Exact checked proposition: forall (n c s t mu:R), hc n c (s+t) mu - hc n c s mu = hp n c t.
 Premises and side conditions: The proposition compares total real-arithmetic
 expressions with a common equicorrelation conditioning denominator. Under a
 probabilistic interpretation, valid positive covariance-domain and sampling
 premises must be supplied separately; no Gaussian regression theorem is assumed.
 Proof/definition method: Unfold only the canonical linear-forecast wrappers
 and invoke Stdlib Ring for exact polynomial normalization, never floating-point
 experiments or manually duplicated finite-list recursions.
 Library reuse: SequentialReport.sequential_d and Rocq Stdlib Reals/Ring;
 existing definitions are preserved as one authoritative report denominator.
 Boundary: Deterministic linearity/contrast/increment relation only; it does
 not establish distributional conditional expectation or confidence coverage.
*)
Theorem hc_history_difference : forall (n c s t mu:R), hc n c (s+t) mu - hc n c s mu = hp n c t.
Proof.
 intros; unfold hp, hf, ht, hm, he, hc, Rdiv; ring.
Qed.

(** [hc_baseline_rate] (theorem).
 Mathematical meaning: A shared shift to all observed test scores contributes the expected sample-weighted forecast.
 Exact checked proposition: forall (n c s mu t:R), hc n c (s+n*t) mu - hc n c s mu = hp n c (n*t).
 Premises and side conditions: The proposition compares total real-arithmetic
 expressions with a common equicorrelation conditioning denominator. Under a
 probabilistic interpretation, valid positive covariance-domain and sampling
 premises must be supplied separately; no Gaussian regression theorem is assumed.
 Proof/definition method: Unfold only the canonical linear-forecast wrappers
 and invoke Stdlib Ring for exact polynomial normalization, never floating-point
 experiments or manually duplicated finite-list recursions.
 Library reuse: SequentialReport.sequential_d and Rocq Stdlib Reals/Ring;
 existing definitions are preserved as one authoritative report denominator.
 Boundary: Deterministic linearity/contrast/increment relation only; it does
 not establish distributional conditional expectation or confidence coverage.
*)
Theorem hc_baseline_rate : forall (n c s mu t:R), hc n c (s+n*t) mu - hc n c s mu = hp n c (n*t).
Proof.
 intros; unfold hp, hf, ht, hm, he, hc, Rdiv; ring.
Qed.

(** [hc_baseline_gap] (theorem).
 Mathematical meaning: The predicted deviation from a reference score is the forecast of total centered history.
 Exact checked proposition: forall (n c s mu:R), hc n c s mu-mu = hp n c (s-n*mu).
 Premises and side conditions: The proposition compares total real-arithmetic
 expressions with a common equicorrelation conditioning denominator. Under a
 probabilistic interpretation, valid positive covariance-domain and sampling
 premises must be supplied separately; no Gaussian regression theorem is assumed.
 Proof/definition method: Unfold only the canonical linear-forecast wrappers
 and invoke Stdlib Ring for exact polynomial normalization, never floating-point
 experiments or manually duplicated finite-list recursions.
 Library reuse: SequentialReport.sequential_d and Rocq Stdlib Reals/Ring;
 existing definitions are preserved as one authoritative report denominator.
 Boundary: Deterministic linearity/contrast/increment relation only; it does
 not establish distributional conditional expectation or confidence coverage.
*)
Theorem hc_baseline_gap : forall (n c s mu:R), hc n c s mu-mu = hp n c (s-n*mu).
Proof.
 intros; unfold hp, hf, ht, hm, he, hc, Rdiv; ring.
Qed.

(** [future_count_add] (theorem).
 Mathematical meaning: Predicting two successive future batches sums their expected standardized score totals.
 Exact checked proposition: forall (n k t c s:R), hf n (k+t) c s = hf n k c s + hf n t c s.
 Premises and side conditions: The proposition compares total real-arithmetic
 expressions with a common equicorrelation conditioning denominator. Under a
 probabilistic interpretation, valid positive covariance-domain and sampling
 premises must be supplied separately; no Gaussian regression theorem is assumed.
 Proof/definition method: Unfold only the canonical linear-forecast wrappers
 and invoke Stdlib Ring for exact polynomial normalization, never floating-point
 experiments or manually duplicated finite-list recursions.
 Library reuse: SequentialReport.sequential_d and Rocq Stdlib Reals/Ring;
 existing definitions are preserved as one authoritative report denominator.
 Boundary: Deterministic linearity/contrast/increment relation only; it does
 not establish distributional conditional expectation or confidence coverage.
*)
Theorem future_count_add : forall (n k t c s:R), hf n (k+t) c s = hf n k c s + hf n t c s.
Proof.
 intros; unfold hp, hf, ht, hm, he, hc, Rdiv; ring.
Qed.

(** [future_count_scale] (theorem).
 Mathematical meaning: Scaling the number of predicted scores scales their aggregate linearly.
 Exact checked proposition: forall (n k q c s:R), hf n (q*k) c s=q*hf n k c s.
 Premises and side conditions: The proposition compares total real-arithmetic
 expressions with a common equicorrelation conditioning denominator. Under a
 probabilistic interpretation, valid positive covariance-domain and sampling
 premises must be supplied separately; no Gaussian regression theorem is assumed.
 Proof/definition method: Unfold only the canonical linear-forecast wrappers
 and invoke Stdlib Ring for exact polynomial normalization, never floating-point
 experiments or manually duplicated finite-list recursions.
 Library reuse: SequentialReport.sequential_d and Rocq Stdlib Reals/Ring;
 existing definitions are preserved as one authoritative report denominator.
 Boundary: Deterministic linearity/contrast/increment relation only; it does
 not establish distributional conditional expectation or confidence coverage.
*)
Theorem future_count_scale : forall (n k q c s:R), hf n (q*k) c s=q*hf n k c s.
Proof.
 intros; unfold hp, hf, ht, hm, he, hc, Rdiv; ring.
Qed.

(** [total_future_count_add] (theorem).
 Mathematical meaning: Appending an additional forecast cohort changes total score by its predicted sum.
 Exact checked proposition: forall (n k t c s:R), ht n (k+t) c s=ht n k c s+hf n t c s.
 Premises and side conditions: The proposition compares total real-arithmetic
 expressions with a common equicorrelation conditioning denominator. Under a
 probabilistic interpretation, valid positive covariance-domain and sampling
 premises must be supplied separately; no Gaussian regression theorem is assumed.
 Proof/definition method: Unfold only the canonical linear-forecast wrappers
 and invoke Stdlib Ring for exact polynomial normalization, never floating-point
 experiments or manually duplicated finite-list recursions.
 Library reuse: SequentialReport.sequential_d and Rocq Stdlib Reals/Ring;
 existing definitions are preserved as one authoritative report denominator.
 Boundary: Deterministic linearity/contrast/increment relation only; it does
 not establish distributional conditional expectation or confidence coverage.
*)
Theorem total_future_count_add : forall (n k t c s:R), ht n (k+t) c s=ht n k c s+hf n t c s.
Proof.
 intros; unfold hp, hf, ht, hm, he, hc, Rdiv; ring.
Qed.

(** [total_future_count_contrast] (theorem).
 Mathematical meaning: The score-total difference between future horizon sizes equals the extra predicted sum.
 Exact checked proposition: forall (n k t c s:R), ht n k c s-ht n t c s=hf n (k-t) c s.
 Premises and side conditions: The proposition compares total real-arithmetic
 expressions with a common equicorrelation conditioning denominator. Under a
 probabilistic interpretation, valid positive covariance-domain and sampling
 premises must be supplied separately; no Gaussian regression theorem is assumed.
 Proof/definition method: Unfold only the canonical linear-forecast wrappers
 and invoke Stdlib Ring for exact polynomial normalization, never floating-point
 experiments or manually duplicated finite-list recursions.
 Library reuse: SequentialReport.sequential_d and Rocq Stdlib Reals/Ring;
 existing definitions are preserved as one authoritative report denominator.
 Boundary: Deterministic linearity/contrast/increment relation only; it does
 not establish distributional conditional expectation or confidence coverage.
*)
Theorem total_future_count_contrast : forall (n k t c s:R), ht n k c s-ht n t c s=hf n (k-t) c s.
Proof.
 intros; unfold hp, hf, ht, hm, he, hc, Rdiv; ring.
Qed.

(** [total_score_gap] (theorem).
 Mathematical meaning: Future predicted test scores account exactly for the excess over the observed total.
 Exact checked proposition: forall (n k c s:R), ht n k c s-s=hf n k c s.
 Premises and side conditions: The proposition compares total real-arithmetic
 expressions with a common equicorrelation conditioning denominator. Under a
 probabilistic interpretation, valid positive covariance-domain and sampling
 premises must be supplied separately; no Gaussian regression theorem is assumed.
 Proof/definition method: Unfold only the canonical linear-forecast wrappers
 and invoke Stdlib Ring for exact polynomial normalization, never floating-point
 experiments or manually duplicated finite-list recursions.
 Library reuse: SequentialReport.sequential_d and Rocq Stdlib Reals/Ring;
 existing definitions are preserved as one authoritative report denominator.
 Boundary: Deterministic linearity/contrast/increment relation only; it does
 not establish distributional conditional expectation or confidence coverage.
*)
Theorem total_score_gap : forall (n k c s:R), ht n k c s-s=hf n k c s.
Proof.
 intros; unfold hp, hf, ht, hm, he, hc, Rdiv; ring.
Qed.

(** [residual_recovers_outcome] (theorem).
 Mathematical meaning: A forecast plus the associated innovation reconstructs the actual future outcome.
 Exact checked proposition: forall (n c s x:R), he n c s x + hp n c s=x.
 Premises and side conditions: The proposition compares total real-arithmetic
 expressions with a common equicorrelation conditioning denominator. Under a
 probabilistic interpretation, valid positive covariance-domain and sampling
 premises must be supplied separately; no Gaussian regression theorem is assumed.
 Proof/definition method: Unfold only the canonical linear-forecast wrappers
 and invoke Stdlib Ring for exact polynomial normalization, never floating-point
 experiments or manually duplicated finite-list recursions.
 Library reuse: SequentialReport.sequential_d and Rocq Stdlib Reals/Ring;
 existing definitions are preserved as one authoritative report denominator.
 Boundary: Deterministic linearity/contrast/increment relation only; it does
 not establish distributional conditional expectation or confidence coverage.
*)
Theorem residual_recovers_outcome : forall (n c s x:R), he n c s x + hp n c s=x.
Proof.
 intros; unfold hp, hf, ht, hm, he, hc, Rdiv; ring.
Qed.

(** [centered_residual_recovers] (theorem).
 Mathematical meaning: The centered prediction plus standardized innovation reconstructs the baseline-adjusted observation.
 Exact checked proposition: forall (n c s mu x:R), hc n c s mu+he n c (s-n*mu) x = mu+x.
 Premises and side conditions: The proposition compares total real-arithmetic
 expressions with a common equicorrelation conditioning denominator. Under a
 probabilistic interpretation, valid positive covariance-domain and sampling
 premises must be supplied separately; no Gaussian regression theorem is assumed.
 Proof/definition method: Unfold only the canonical linear-forecast wrappers
 and invoke Stdlib Ring for exact polynomial normalization, never floating-point
 experiments or manually duplicated finite-list recursions.
 Library reuse: SequentialReport.sequential_d and Rocq Stdlib Reals/Ring;
 existing definitions are preserved as one authoritative report denominator.
 Boundary: Deterministic linearity/contrast/increment relation only; it does
 not establish distributional conditional expectation or confidence coverage.
*)
Theorem centered_residual_recovers : forall (n c s mu x:R), hc n c s mu+he n c (s-n*mu) x = mu+x.
Proof.
 intros; unfold hp, hf, ht, hm, he, hc, Rdiv; ring.
Qed.

(** [centered_outcome_reconstruction] (theorem).
 Mathematical meaning: Centered prediction and a centered future residual reconstruct the uncentered outcome.
 Exact checked proposition: forall (n c s mu x:R), hc n c s mu+he n c (s-n*mu) (x-mu)=x.
 Premises and side conditions: The proposition compares total real-arithmetic
 expressions with a common equicorrelation conditioning denominator. Under a
 probabilistic interpretation, valid positive covariance-domain and sampling
 premises must be supplied separately; no Gaussian regression theorem is assumed.
 Proof/definition method: Unfold only the canonical linear-forecast wrappers
 and invoke Stdlib Ring for exact polynomial normalization, never floating-point
 experiments or manually duplicated finite-list recursions.
 Library reuse: SequentialReport.sequential_d and Rocq Stdlib Reals/Ring;
 existing definitions are preserved as one authoritative report denominator.
 Boundary: Deterministic linearity/contrast/increment relation only; it does
 not establish distributional conditional expectation or confidence coverage.
*)
Theorem centered_outcome_reconstruction : forall (n c s mu x:R), hc n c s mu+he n c (s-n*mu) (x-mu)=x.
Proof.
 intros; unfold hp, hf, ht, hm, he, hc, Rdiv; ring.
Qed.

(** [total_residual_plus] (theorem).
 Mathematical meaning: Replacing one future prediction with an outcome corrects the total by the innovation.
 Exact checked proposition: forall (n k c s x:R), ht n k c s+he n c s x=s+x+(k-1)*hp n c s.
 Premises and side conditions: The proposition compares total real-arithmetic
 expressions with a common equicorrelation conditioning denominator. Under a
 probabilistic interpretation, valid positive covariance-domain and sampling
 premises must be supplied separately; no Gaussian regression theorem is assumed.
 Proof/definition method: Unfold only the canonical linear-forecast wrappers
 and invoke Stdlib Ring for exact polynomial normalization, never floating-point
 experiments or manually duplicated finite-list recursions.
 Library reuse: SequentialReport.sequential_d and Rocq Stdlib Reals/Ring;
 existing definitions are preserved as one authoritative report denominator.
 Boundary: Deterministic linearity/contrast/increment relation only; it does
 not establish distributional conditional expectation or confidence coverage.
*)
Theorem total_residual_plus : forall (n k c s x:R), ht n k c s+he n c s x=s+x+(k-1)*hp n c s.
Proof.
 intros; unfold hp, hf, ht, hm, he, hc, Rdiv; ring.
Qed.

(** [total_residual_minus] (theorem).
 Mathematical meaning: Subtracting an outcome innovation gives the exact inverse correction to predicted total.
 Exact checked proposition: forall (n k c s x:R), ht n k c s-he n c s x=s-x+(k+1)*hp n c s.
 Premises and side conditions: The proposition compares total real-arithmetic
 expressions with a common equicorrelation conditioning denominator. Under a
 probabilistic interpretation, valid positive covariance-domain and sampling
 premises must be supplied separately; no Gaussian regression theorem is assumed.
 Proof/definition method: Unfold only the canonical linear-forecast wrappers
 and invoke Stdlib Ring for exact polynomial normalization, never floating-point
 experiments or manually duplicated finite-list recursions.
 Library reuse: SequentialReport.sequential_d and Rocq Stdlib Reals/Ring;
 existing definitions are preserved as one authoritative report denominator.
 Boundary: Deterministic linearity/contrast/increment relation only; it does
 not establish distributional conditional expectation or confidence coverage.
*)
Theorem total_residual_minus : forall (n k c s x:R), ht n k c s-he n c s x=s-x+(k+1)*hp n c s.
Proof.
 intros; unfold hp, hf, ht, hm, he, hc, Rdiv; ring.
Qed.

(** [future_residual_plus] (theorem).
 Mathematical meaning: One realized outcome and the remaining predicted future outcomes form the corrected future sum.
 Exact checked proposition: forall (n k c s x:R), hf n k c s+he n c s x=x+(k-1)*hp n c s.
 Premises and side conditions: The proposition compares total real-arithmetic
 expressions with a common equicorrelation conditioning denominator. Under a
 probabilistic interpretation, valid positive covariance-domain and sampling
 premises must be supplied separately; no Gaussian regression theorem is assumed.
 Proof/definition method: Unfold only the canonical linear-forecast wrappers
 and invoke Stdlib Ring for exact polynomial normalization, never floating-point
 experiments or manually duplicated finite-list recursions.
 Library reuse: SequentialReport.sequential_d and Rocq Stdlib Reals/Ring;
 existing definitions are preserved as one authoritative report denominator.
 Boundary: Deterministic linearity/contrast/increment relation only; it does
 not establish distributional conditional expectation or confidence coverage.
*)
Theorem future_residual_plus : forall (n k c s x:R), hf n k c s+he n c s x=x+(k-1)*hp n c s.
Proof.
 intros; unfold hp, hf, ht, hm, he, hc, Rdiv; ring.
Qed.

(** [future_residual_minus] (theorem).
 Mathematical meaning: Removing the innovation from the future expected sum has an exact balancing form.
 Exact checked proposition: forall (n k c s x:R), hf n k c s-he n c s x= -x+(k+1)*hp n c s.
 Premises and side conditions: The proposition compares total real-arithmetic
 expressions with a common equicorrelation conditioning denominator. Under a
 probabilistic interpretation, valid positive covariance-domain and sampling
 premises must be supplied separately; no Gaussian regression theorem is assumed.
 Proof/definition method: Unfold only the canonical linear-forecast wrappers
 and invoke Stdlib Ring for exact polynomial normalization, never floating-point
 experiments or manually duplicated finite-list recursions.
 Library reuse: SequentialReport.sequential_d and Rocq Stdlib Reals/Ring;
 existing definitions are preserved as one authoritative report denominator.
 Boundary: Deterministic linearity/contrast/increment relation only; it does
 not establish distributional conditional expectation or confidence coverage.
*)
Theorem future_residual_minus : forall (n k c s x:R), hf n k c s-he n c s x= -x+(k+1)*hp n c s.
Proof.
 intros; unfold hp, hf, ht, hm, he, hc, Rdiv; ring.
Qed.

(** [total_difference_history] (theorem).
 Mathematical meaning: Different observed histories affect the combined total through observed and forecast components.
 Exact checked proposition: forall (n k c s t:R), ht n k c s-ht n k c t=(s-t)+hf n k c (s-t).
 Premises and side conditions: The proposition compares total real-arithmetic
 expressions with a common equicorrelation conditioning denominator. Under a
 probabilistic interpretation, valid positive covariance-domain and sampling
 premises must be supplied separately; no Gaussian regression theorem is assumed.
 Proof/definition method: Unfold only the canonical linear-forecast wrappers
 and invoke Stdlib Ring for exact polynomial normalization, never floating-point
 experiments or manually duplicated finite-list recursions.
 Library reuse: SequentialReport.sequential_d and Rocq Stdlib Reals/Ring;
 existing definitions are preserved as one authoritative report denominator.
 Boundary: Deterministic linearity/contrast/increment relation only; it does
 not establish distributional conditional expectation or confidence coverage.
*)
Theorem total_difference_history : forall (n k c s t:R), ht n k c s-ht n k c t=(s-t)+hf n k c (s-t).
Proof.
 intros; unfold hp, hf, ht, hm, he, hc, Rdiv; ring.
Qed.

(** [total_forecast_extra] (theorem).
 Mathematical meaning: Two future expected batches can be pooled into a single horizon without rounding.
 Exact checked proposition: forall (n k t c s:R), ht n k c s +hf n t c s=ht n (k+t) c s.
 Premises and side conditions: The proposition compares total real-arithmetic
 expressions with a common equicorrelation conditioning denominator. Under a
 probabilistic interpretation, valid positive covariance-domain and sampling
 premises must be supplied separately; no Gaussian regression theorem is assumed.
 Proof/definition method: Unfold only the canonical linear-forecast wrappers
 and invoke Stdlib Ring for exact polynomial normalization, never floating-point
 experiments or manually duplicated finite-list recursions.
 Library reuse: SequentialReport.sequential_d and Rocq Stdlib Reals/Ring;
 existing definitions are preserved as one authoritative report denominator.
 Boundary: Deterministic linearity/contrast/increment relation only; it does
 not establish distributional conditional expectation or confidence coverage.
*)
Theorem total_forecast_extra : forall (n k t c s:R), ht n k c s +hf n t c s=ht n (k+t) c s.
Proof.
 intros; unfold hp, hf, ht, hm, he, hc, Rdiv; ring.
Qed.
