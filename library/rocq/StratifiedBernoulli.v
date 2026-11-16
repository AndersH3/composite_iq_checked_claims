(** Module: StratifiedBernoulli.v
 Purpose: Establish heterogeneous three-cohort count, Bernoulli-variance
 target, calibration-residual and between-cohort dispersion identities for
 the six statistical report books and their simulation diagnostics.
 Mathematical representation: Real cohort exposures n,m,k, marginal rates
 p,q,r and an optional benchmark t; exact polynomial expressions over reals.
 Explicit hypotheses: These equalities hold for all real inputs. Nonnegative
 exposures, rates between zero and one, and independent sampling would
 be additional assumptions for the statistical interpretations.
 Library use: Rocq Stdlib Reals/Ring/Lra/Psatz, SamplingPrecision and
 TwoRatePrecision; no duplicate Bernoulli variance or two-rate definition.
 Limitations: The proofs do not establish a binomial law, a stochastic
 independence property, Gaussian conditional probabilities, confidence
 coverage or empirical IQ population characteristics.
 Reproduction: scripts/compile_rocq.sh with Rocq 9.2 pinned by CI.
 AI disclosure: AI assisted definitions, mathematical specifications and
 source comments. Only successful Rocq compilation establishes proofs.
*)
From Stdlib Require Import Reals Ring Lra Psatz.
Require Import SamplingPrecision TwoRatePrecision.
Open Scope R_scope.

(** [sb_mass] (definition).
 Mathematical meaning: Aggregate exposure weight across three population or simulation cohorts.
 Exact definition: Definition sb_mass (n m k:R) : R := n+m+k..
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: A short transparent polynomial using the canonical shared variance factor.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Definition sb_mass (n m k:R) : R := n+m+k.

(** [sb_success] (definition).
 Mathematical meaning: Expected successes under a hypothetical independent Bernoulli sampling model.
 Exact definition: Definition sb_success (n m k p q r:R) : R := n*p+m*q+k*r..
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: A short transparent polynomial using the canonical shared variance factor.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Definition sb_success (n m k p q r:R) : R := n*p+m*q+k*r.

(** [sb_failure] (definition).
 Mathematical meaning: Expected failures across the same three cohort weights.
 Exact definition: Definition sb_failure (n m k p q r:R) : R := n*(1-p)+m*(1-q)+k*(1-r)..
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: A short transparent polynomial using the canonical shared variance factor.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Definition sb_failure (n m k p q r:R) : R := n*(1-p)+m*(1-q)+k*(1-r).

(** [sb_variance] (definition).
 Mathematical meaning: Sum of Bernoulli count-variance targets across heterogeneous cohorts.
 Exact definition: Definition sb_variance (n m k p q r:R) : R := n*sampling_bernoulli_variance p+m*sampling_bernoulli_variance q+k*sampling_bernoulli_variance r..
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: A short transparent polynomial using the canonical shared variance factor.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Definition sb_variance (n m k p q r:R) : R := n*sampling_bernoulli_variance p+m*sampling_bernoulli_variance q+k*sampling_bernoulli_variance r.

(** [sb_second] (definition).
 Mathematical meaning: Exposure-weighted second rate moment, measuring raw rate concentration.
 Exact definition: Definition sb_second (n m k p q r:R) : R := n*p*p+m*q*q+k*r*r..
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: A short transparent polynomial using the canonical shared variance factor.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Definition sb_second (n m k p q r:R) : R := n*p*p+m*q*q+k*r*r.

(** [sb_loss] (definition).
 Mathematical meaning: Squared calibration deviation of cohort event rates from a common benchmark.
 Exact definition: Definition sb_loss (n m k p q r t:R) : R := n*(p-t)*(p-t)+m*(q-t)*(q-t)+k*(r-t)*(r-t)..
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: A short transparent polynomial using the canonical shared variance factor.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Definition sb_loss (n m k p q r t:R) : R := n*(p-t)*(p-t)+m*(q-t)*(q-t)+k*(r-t)*(r-t).

(** [sb_dispersion] (definition).
 Mathematical meaning: Pairwise exposure-weighted dispersion between heterogeneous admission/event rates.
 Exact definition: Definition sb_dispersion (n m k p q r:R) : R := n*m*(p-q)*(p-q)+m*k*(q-r)*(q-r)+k*n*(r-p)*(r-p)..
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: A short transparent polynomial using the canonical shared variance factor.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Definition sb_dispersion (n m k p q r:R) : R := n*m*(p-q)*(p-q)+m*k*(q-r)*(q-r)+k*n*(r-p)*(r-p).

(** [sb_net] (definition).
 Mathematical meaning: Signed expected successes-minus-failures count contrast.
 Exact definition: Definition sb_net (n m k p q r:R) : R := sb_success n m k p q r-sb_failure n m k p q r..
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: A short transparent polynomial using the canonical shared variance factor.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Definition sb_net (n m k p q r:R) : R := sb_success n m k p q r-sb_failure n m k p q r.

(** [sb_offset] (definition).
 Mathematical meaning: Signed excess expected success count over a common benchmark rate.
 Exact definition: Definition sb_offset (n m k p q r t:R) : R := sb_success n m k p q r-t*(sb_mass n m k)..
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: A short transparent polynomial using the canonical shared variance factor.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Definition sb_offset (n m k p q r t:R) : R := sb_success n m k p q r-t*(sb_mass n m k).

(** [success_swap_cohorts] (theorem).
 Mathematical meaning: The success report statistic is invariant under simultaneous permutation of the first two strata.
 Exact proposition: Theorem success_swap_cohorts : forall n m k p q r, sb_success n m k p q r = sb_success m n k q p r.
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem success_swap_cohorts : forall n m k p q r, sb_success n m k p q r = sb_success m n k q p r.
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [success_rotate_cohorts] (theorem).
 Mathematical meaning: The success statistic is independent of cyclic reordering of stratified observations.
 Exact proposition: Theorem success_rotate_cohorts : forall n m k p q r, sb_success n m k p q r = sb_success m k n q r p.
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem success_rotate_cohorts : forall n m k p q r, sb_success n m k p q r = sb_success m k n q r p.
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [success_zero_exposure_1] (theorem).
 Mathematical meaning: A zero-size cohort contributes nothing to the success diagnostic even if its nominal rate changes.
 Exact proposition: Theorem success_zero_exposure_1 : forall n m k p q r, sb_success 0 m k p q r = sb_success 0 m k 0 q r.
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem success_zero_exposure_1 : forall n m k p q r, sb_success 0 m k p q r = sb_success 0 m k 0 q r.
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [success_zero_exposure_2] (theorem).
 Mathematical meaning: A zero-size cohort contributes nothing to the success diagnostic even if its nominal rate changes.
 Exact proposition: Theorem success_zero_exposure_2 : forall n m k p q r, sb_success n 0 k p q r = sb_success n 0 k p 0 r.
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem success_zero_exposure_2 : forall n m k p q r, sb_success n 0 k p q r = sb_success n 0 k p 0 r.
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [success_zero_exposure_3] (theorem).
 Mathematical meaning: A zero-size cohort contributes nothing to the success diagnostic even if its nominal rate changes.
 Exact proposition: Theorem success_zero_exposure_3 : forall n m k p q r, sb_success n m 0 p q r = sb_success n m 0 p q 0.
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem success_zero_exposure_3 : forall n m k p q r, sb_success n m 0 p q r = sb_success n m 0 p q 0.
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [success_exposure_rescale] (theorem).
 Mathematical meaning: Uniform rescaling of sample weights respects the exact success homogeneity degree.
 Exact proposition: Theorem success_exposure_rescale : forall n m k p q r h, sb_success (h*n) (h*m) (h*k) p q r = h*(sb_success n m k p q r).
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem success_exposure_rescale : forall n m k p q r h, sb_success (h*n) (h*m) (h*k) p q r = h*(sb_success n m k p q r).
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [failure_swap_cohorts] (theorem).
 Mathematical meaning: The failure report statistic is invariant under simultaneous permutation of the first two strata.
 Exact proposition: Theorem failure_swap_cohorts : forall n m k p q r, sb_failure n m k p q r = sb_failure m n k q p r.
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem failure_swap_cohorts : forall n m k p q r, sb_failure n m k p q r = sb_failure m n k q p r.
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [failure_rotate_cohorts] (theorem).
 Mathematical meaning: The failure statistic is independent of cyclic reordering of stratified observations.
 Exact proposition: Theorem failure_rotate_cohorts : forall n m k p q r, sb_failure n m k p q r = sb_failure m k n q r p.
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem failure_rotate_cohorts : forall n m k p q r, sb_failure n m k p q r = sb_failure m k n q r p.
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [failure_zero_exposure_1] (theorem).
 Mathematical meaning: A zero-size cohort contributes nothing to the failure diagnostic even if its nominal rate changes.
 Exact proposition: Theorem failure_zero_exposure_1 : forall n m k p q r, sb_failure 0 m k p q r = sb_failure 0 m k 0 q r.
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem failure_zero_exposure_1 : forall n m k p q r, sb_failure 0 m k p q r = sb_failure 0 m k 0 q r.
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [failure_zero_exposure_2] (theorem).
 Mathematical meaning: A zero-size cohort contributes nothing to the failure diagnostic even if its nominal rate changes.
 Exact proposition: Theorem failure_zero_exposure_2 : forall n m k p q r, sb_failure n 0 k p q r = sb_failure n 0 k p 0 r.
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem failure_zero_exposure_2 : forall n m k p q r, sb_failure n 0 k p q r = sb_failure n 0 k p 0 r.
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [failure_zero_exposure_3] (theorem).
 Mathematical meaning: A zero-size cohort contributes nothing to the failure diagnostic even if its nominal rate changes.
 Exact proposition: Theorem failure_zero_exposure_3 : forall n m k p q r, sb_failure n m 0 p q r = sb_failure n m 0 p q 0.
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem failure_zero_exposure_3 : forall n m k p q r, sb_failure n m 0 p q r = sb_failure n m 0 p q 0.
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [failure_exposure_rescale] (theorem).
 Mathematical meaning: Uniform rescaling of sample weights respects the exact failure homogeneity degree.
 Exact proposition: Theorem failure_exposure_rescale : forall n m k p q r h, sb_failure (h*n) (h*m) (h*k) p q r = h*(sb_failure n m k p q r).
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem failure_exposure_rescale : forall n m k p q r h, sb_failure (h*n) (h*m) (h*k) p q r = h*(sb_failure n m k p q r).
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [variance_swap_cohorts] (theorem).
 Mathematical meaning: The variance report statistic is invariant under simultaneous permutation of the first two strata.
 Exact proposition: Theorem variance_swap_cohorts : forall n m k p q r, sb_variance n m k p q r = sb_variance m n k q p r.
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem variance_swap_cohorts : forall n m k p q r, sb_variance n m k p q r = sb_variance m n k q p r.
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [variance_rotate_cohorts] (theorem).
 Mathematical meaning: The variance statistic is independent of cyclic reordering of stratified observations.
 Exact proposition: Theorem variance_rotate_cohorts : forall n m k p q r, sb_variance n m k p q r = sb_variance m k n q r p.
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem variance_rotate_cohorts : forall n m k p q r, sb_variance n m k p q r = sb_variance m k n q r p.
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [variance_zero_exposure_1] (theorem).
 Mathematical meaning: A zero-size cohort contributes nothing to the variance diagnostic even if its nominal rate changes.
 Exact proposition: Theorem variance_zero_exposure_1 : forall n m k p q r, sb_variance 0 m k p q r = sb_variance 0 m k 0 q r.
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem variance_zero_exposure_1 : forall n m k p q r, sb_variance 0 m k p q r = sb_variance 0 m k 0 q r.
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [variance_zero_exposure_2] (theorem).
 Mathematical meaning: A zero-size cohort contributes nothing to the variance diagnostic even if its nominal rate changes.
 Exact proposition: Theorem variance_zero_exposure_2 : forall n m k p q r, sb_variance n 0 k p q r = sb_variance n 0 k p 0 r.
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem variance_zero_exposure_2 : forall n m k p q r, sb_variance n 0 k p q r = sb_variance n 0 k p 0 r.
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [variance_zero_exposure_3] (theorem).
 Mathematical meaning: A zero-size cohort contributes nothing to the variance diagnostic even if its nominal rate changes.
 Exact proposition: Theorem variance_zero_exposure_3 : forall n m k p q r, sb_variance n m 0 p q r = sb_variance n m 0 p q 0.
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem variance_zero_exposure_3 : forall n m k p q r, sb_variance n m 0 p q r = sb_variance n m 0 p q 0.
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [variance_exposure_rescale] (theorem).
 Mathematical meaning: Uniform rescaling of sample weights respects the exact variance homogeneity degree.
 Exact proposition: Theorem variance_exposure_rescale : forall n m k p q r h, sb_variance (h*n) (h*m) (h*k) p q r = h*(sb_variance n m k p q r).
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem variance_exposure_rescale : forall n m k p q r h, sb_variance (h*n) (h*m) (h*k) p q r = h*(sb_variance n m k p q r).
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [second_swap_cohorts] (theorem).
 Mathematical meaning: The second report statistic is invariant under simultaneous permutation of the first two strata.
 Exact proposition: Theorem second_swap_cohorts : forall n m k p q r, sb_second n m k p q r = sb_second m n k q p r.
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem second_swap_cohorts : forall n m k p q r, sb_second n m k p q r = sb_second m n k q p r.
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [second_rotate_cohorts] (theorem).
 Mathematical meaning: The second statistic is independent of cyclic reordering of stratified observations.
 Exact proposition: Theorem second_rotate_cohorts : forall n m k p q r, sb_second n m k p q r = sb_second m k n q r p.
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem second_rotate_cohorts : forall n m k p q r, sb_second n m k p q r = sb_second m k n q r p.
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [second_zero_exposure_1] (theorem).
 Mathematical meaning: A zero-size cohort contributes nothing to the second diagnostic even if its nominal rate changes.
 Exact proposition: Theorem second_zero_exposure_1 : forall n m k p q r, sb_second 0 m k p q r = sb_second 0 m k 0 q r.
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem second_zero_exposure_1 : forall n m k p q r, sb_second 0 m k p q r = sb_second 0 m k 0 q r.
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [second_zero_exposure_2] (theorem).
 Mathematical meaning: A zero-size cohort contributes nothing to the second diagnostic even if its nominal rate changes.
 Exact proposition: Theorem second_zero_exposure_2 : forall n m k p q r, sb_second n 0 k p q r = sb_second n 0 k p 0 r.
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem second_zero_exposure_2 : forall n m k p q r, sb_second n 0 k p q r = sb_second n 0 k p 0 r.
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [second_zero_exposure_3] (theorem).
 Mathematical meaning: A zero-size cohort contributes nothing to the second diagnostic even if its nominal rate changes.
 Exact proposition: Theorem second_zero_exposure_3 : forall n m k p q r, sb_second n m 0 p q r = sb_second n m 0 p q 0.
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem second_zero_exposure_3 : forall n m k p q r, sb_second n m 0 p q r = sb_second n m 0 p q 0.
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [second_exposure_rescale] (theorem).
 Mathematical meaning: Uniform rescaling of sample weights respects the exact second homogeneity degree.
 Exact proposition: Theorem second_exposure_rescale : forall n m k p q r h, sb_second (h*n) (h*m) (h*k) p q r = h*(sb_second n m k p q r).
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem second_exposure_rescale : forall n m k p q r h, sb_second (h*n) (h*m) (h*k) p q r = h*(sb_second n m k p q r).
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [loss_swap_cohorts] (theorem).
 Mathematical meaning: The loss report statistic is invariant under simultaneous permutation of the first two strata.
 Exact proposition: Theorem loss_swap_cohorts : forall n m k p q r t, sb_loss n m k p q r t = sb_loss m n k q p r t.
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem loss_swap_cohorts : forall n m k p q r t, sb_loss n m k p q r t = sb_loss m n k q p r t.
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [loss_rotate_cohorts] (theorem).
 Mathematical meaning: The loss statistic is independent of cyclic reordering of stratified observations.
 Exact proposition: Theorem loss_rotate_cohorts : forall n m k p q r t, sb_loss n m k p q r t = sb_loss m k n q r p t.
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem loss_rotate_cohorts : forall n m k p q r t, sb_loss n m k p q r t = sb_loss m k n q r p t.
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [loss_zero_exposure_1] (theorem).
 Mathematical meaning: A zero-size cohort contributes nothing to the loss diagnostic even if its nominal rate changes.
 Exact proposition: Theorem loss_zero_exposure_1 : forall n m k p q r t, sb_loss 0 m k p q r t = sb_loss 0 m k 0 q r t.
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem loss_zero_exposure_1 : forall n m k p q r t, sb_loss 0 m k p q r t = sb_loss 0 m k 0 q r t.
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [loss_zero_exposure_2] (theorem).
 Mathematical meaning: A zero-size cohort contributes nothing to the loss diagnostic even if its nominal rate changes.
 Exact proposition: Theorem loss_zero_exposure_2 : forall n m k p q r t, sb_loss n 0 k p q r t = sb_loss n 0 k p 0 r t.
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem loss_zero_exposure_2 : forall n m k p q r t, sb_loss n 0 k p q r t = sb_loss n 0 k p 0 r t.
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [loss_zero_exposure_3] (theorem).
 Mathematical meaning: A zero-size cohort contributes nothing to the loss diagnostic even if its nominal rate changes.
 Exact proposition: Theorem loss_zero_exposure_3 : forall n m k p q r t, sb_loss n m 0 p q r t = sb_loss n m 0 p q 0 t.
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem loss_zero_exposure_3 : forall n m k p q r t, sb_loss n m 0 p q r t = sb_loss n m 0 p q 0 t.
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [loss_exposure_rescale] (theorem).
 Mathematical meaning: Uniform rescaling of sample weights respects the exact loss homogeneity degree.
 Exact proposition: Theorem loss_exposure_rescale : forall n m k p q r t h, sb_loss (h*n) (h*m) (h*k) p q r t = h*(sb_loss n m k p q r t).
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem loss_exposure_rescale : forall n m k p q r t h, sb_loss (h*n) (h*m) (h*k) p q r t = h*(sb_loss n m k p q r t).
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [dispersion_swap_cohorts] (theorem).
 Mathematical meaning: The dispersion report statistic is invariant under simultaneous permutation of the first two strata.
 Exact proposition: Theorem dispersion_swap_cohorts : forall n m k p q r, sb_dispersion n m k p q r = sb_dispersion m n k q p r.
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem dispersion_swap_cohorts : forall n m k p q r, sb_dispersion n m k p q r = sb_dispersion m n k q p r.
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [dispersion_rotate_cohorts] (theorem).
 Mathematical meaning: The dispersion statistic is independent of cyclic reordering of stratified observations.
 Exact proposition: Theorem dispersion_rotate_cohorts : forall n m k p q r, sb_dispersion n m k p q r = sb_dispersion m k n q r p.
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem dispersion_rotate_cohorts : forall n m k p q r, sb_dispersion n m k p q r = sb_dispersion m k n q r p.
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [dispersion_zero_exposure_1] (theorem).
 Mathematical meaning: A zero-size cohort contributes nothing to the dispersion diagnostic even if its nominal rate changes.
 Exact proposition: Theorem dispersion_zero_exposure_1 : forall n m k p q r, sb_dispersion 0 m k p q r = sb_dispersion 0 m k 0 q r.
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem dispersion_zero_exposure_1 : forall n m k p q r, sb_dispersion 0 m k p q r = sb_dispersion 0 m k 0 q r.
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [dispersion_zero_exposure_2] (theorem).
 Mathematical meaning: A zero-size cohort contributes nothing to the dispersion diagnostic even if its nominal rate changes.
 Exact proposition: Theorem dispersion_zero_exposure_2 : forall n m k p q r, sb_dispersion n 0 k p q r = sb_dispersion n 0 k p 0 r.
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem dispersion_zero_exposure_2 : forall n m k p q r, sb_dispersion n 0 k p q r = sb_dispersion n 0 k p 0 r.
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [dispersion_zero_exposure_3] (theorem).
 Mathematical meaning: A zero-size cohort contributes nothing to the dispersion diagnostic even if its nominal rate changes.
 Exact proposition: Theorem dispersion_zero_exposure_3 : forall n m k p q r, sb_dispersion n m 0 p q r = sb_dispersion n m 0 p q 0.
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem dispersion_zero_exposure_3 : forall n m k p q r, sb_dispersion n m 0 p q r = sb_dispersion n m 0 p q 0.
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [dispersion_exposure_rescale] (theorem).
 Mathematical meaning: Uniform rescaling of sample weights respects the exact dispersion homogeneity degree.
 Exact proposition: Theorem dispersion_exposure_rescale : forall n m k p q r h, sb_dispersion (h*n) (h*m) (h*k) p q r = h*h*(sb_dispersion n m k p q r).
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem dispersion_exposure_rescale : forall n m k p q r h, sb_dispersion (h*n) (h*m) (h*k) p q r = h*h*(sb_dispersion n m k p q r).
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [net_swap_cohorts] (theorem).
 Mathematical meaning: The net report statistic is invariant under simultaneous permutation of the first two strata.
 Exact proposition: Theorem net_swap_cohorts : forall n m k p q r, sb_net n m k p q r = sb_net m n k q p r.
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem net_swap_cohorts : forall n m k p q r, sb_net n m k p q r = sb_net m n k q p r.
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [net_rotate_cohorts] (theorem).
 Mathematical meaning: The net statistic is independent of cyclic reordering of stratified observations.
 Exact proposition: Theorem net_rotate_cohorts : forall n m k p q r, sb_net n m k p q r = sb_net m k n q r p.
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem net_rotate_cohorts : forall n m k p q r, sb_net n m k p q r = sb_net m k n q r p.
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [net_zero_exposure_1] (theorem).
 Mathematical meaning: A zero-size cohort contributes nothing to the net diagnostic even if its nominal rate changes.
 Exact proposition: Theorem net_zero_exposure_1 : forall n m k p q r, sb_net 0 m k p q r = sb_net 0 m k 0 q r.
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem net_zero_exposure_1 : forall n m k p q r, sb_net 0 m k p q r = sb_net 0 m k 0 q r.
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [net_zero_exposure_2] (theorem).
 Mathematical meaning: A zero-size cohort contributes nothing to the net diagnostic even if its nominal rate changes.
 Exact proposition: Theorem net_zero_exposure_2 : forall n m k p q r, sb_net n 0 k p q r = sb_net n 0 k p 0 r.
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem net_zero_exposure_2 : forall n m k p q r, sb_net n 0 k p q r = sb_net n 0 k p 0 r.
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [net_zero_exposure_3] (theorem).
 Mathematical meaning: A zero-size cohort contributes nothing to the net diagnostic even if its nominal rate changes.
 Exact proposition: Theorem net_zero_exposure_3 : forall n m k p q r, sb_net n m 0 p q r = sb_net n m 0 p q 0.
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem net_zero_exposure_3 : forall n m k p q r, sb_net n m 0 p q r = sb_net n m 0 p q 0.
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [net_exposure_rescale] (theorem).
 Mathematical meaning: Uniform rescaling of sample weights respects the exact net homogeneity degree.
 Exact proposition: Theorem net_exposure_rescale : forall n m k p q r h, sb_net (h*n) (h*m) (h*k) p q r = h*(sb_net n m k p q r).
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem net_exposure_rescale : forall n m k p q r h, sb_net (h*n) (h*m) (h*k) p q r = h*(sb_net n m k p q r).
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [offset_swap_cohorts] (theorem).
 Mathematical meaning: The offset report statistic is invariant under simultaneous permutation of the first two strata.
 Exact proposition: Theorem offset_swap_cohorts : forall n m k p q r t, sb_offset n m k p q r t = sb_offset m n k q p r t.
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem offset_swap_cohorts : forall n m k p q r t, sb_offset n m k p q r t = sb_offset m n k q p r t.
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [offset_rotate_cohorts] (theorem).
 Mathematical meaning: The offset statistic is independent of cyclic reordering of stratified observations.
 Exact proposition: Theorem offset_rotate_cohorts : forall n m k p q r t, sb_offset n m k p q r t = sb_offset m k n q r p t.
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem offset_rotate_cohorts : forall n m k p q r t, sb_offset n m k p q r t = sb_offset m k n q r p t.
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [offset_zero_exposure_1] (theorem).
 Mathematical meaning: A zero-size cohort contributes nothing to the offset diagnostic even if its nominal rate changes.
 Exact proposition: Theorem offset_zero_exposure_1 : forall n m k p q r t, sb_offset 0 m k p q r t = sb_offset 0 m k 0 q r t.
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem offset_zero_exposure_1 : forall n m k p q r t, sb_offset 0 m k p q r t = sb_offset 0 m k 0 q r t.
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [offset_zero_exposure_2] (theorem).
 Mathematical meaning: A zero-size cohort contributes nothing to the offset diagnostic even if its nominal rate changes.
 Exact proposition: Theorem offset_zero_exposure_2 : forall n m k p q r t, sb_offset n 0 k p q r t = sb_offset n 0 k p 0 r t.
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem offset_zero_exposure_2 : forall n m k p q r t, sb_offset n 0 k p q r t = sb_offset n 0 k p 0 r t.
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [offset_zero_exposure_3] (theorem).
 Mathematical meaning: A zero-size cohort contributes nothing to the offset diagnostic even if its nominal rate changes.
 Exact proposition: Theorem offset_zero_exposure_3 : forall n m k p q r t, sb_offset n m 0 p q r t = sb_offset n m 0 p q 0 t.
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem offset_zero_exposure_3 : forall n m k p q r t, sb_offset n m 0 p q r t = sb_offset n m 0 p q 0 t.
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [offset_exposure_rescale] (theorem).
 Mathematical meaning: Uniform rescaling of sample weights respects the exact offset homogeneity degree.
 Exact proposition: Theorem offset_exposure_rescale : forall n m k p q r t h, sb_offset (h*n) (h*m) (h*k) p q r t = h*(sb_offset n m k p q r t).
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem offset_exposure_rescale : forall n m k p q r t h, sb_offset (h*n) (h*m) (h*k) p q r t = h*(sb_offset n m k p q r t).
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [success_size_increment_1] (theorem).
 Mathematical meaning: The 1th cohort exposure marginal for success is exactly the cohort-specific rate score.
 Exact proposition: Theorem success_size_increment_1 : forall n m k p q r h, sb_success (n+h) m k p q r = sb_success n m k p q r+h*p.
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem success_size_increment_1 : forall n m k p q r h, sb_success (n+h) m k p q r = sb_success n m k p q r+h*p.
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [success_size_increment_2] (theorem).
 Mathematical meaning: The 2th cohort exposure marginal for success is exactly the cohort-specific rate score.
 Exact proposition: Theorem success_size_increment_2 : forall n m k p q r h, sb_success n (m+h) k p q r = sb_success n m k p q r+h*q.
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem success_size_increment_2 : forall n m k p q r h, sb_success n (m+h) k p q r = sb_success n m k p q r+h*q.
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [success_size_increment_3] (theorem).
 Mathematical meaning: The 3th cohort exposure marginal for success is exactly the cohort-specific rate score.
 Exact proposition: Theorem success_size_increment_3 : forall n m k p q r h, sb_success n m (k+h) p q r = sb_success n m k p q r+h*r.
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem success_size_increment_3 : forall n m k p q r h, sb_success n m (k+h) p q r = sb_success n m k p q r+h*r.
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [failure_size_increment_1] (theorem).
 Mathematical meaning: The 1th cohort exposure marginal for failure is exactly the cohort-specific rate score.
 Exact proposition: Theorem failure_size_increment_1 : forall n m k p q r h, sb_failure (n+h) m k p q r = sb_failure n m k p q r+h*(1-p).
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem failure_size_increment_1 : forall n m k p q r h, sb_failure (n+h) m k p q r = sb_failure n m k p q r+h*(1-p).
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [failure_size_increment_2] (theorem).
 Mathematical meaning: The 2th cohort exposure marginal for failure is exactly the cohort-specific rate score.
 Exact proposition: Theorem failure_size_increment_2 : forall n m k p q r h, sb_failure n (m+h) k p q r = sb_failure n m k p q r+h*(1-q).
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem failure_size_increment_2 : forall n m k p q r h, sb_failure n (m+h) k p q r = sb_failure n m k p q r+h*(1-q).
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [failure_size_increment_3] (theorem).
 Mathematical meaning: The 3th cohort exposure marginal for failure is exactly the cohort-specific rate score.
 Exact proposition: Theorem failure_size_increment_3 : forall n m k p q r h, sb_failure n m (k+h) p q r = sb_failure n m k p q r+h*(1-r).
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem failure_size_increment_3 : forall n m k p q r h, sb_failure n m (k+h) p q r = sb_failure n m k p q r+h*(1-r).
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [variance_size_increment_1] (theorem).
 Mathematical meaning: The 1th cohort exposure marginal for variance is exactly the cohort-specific rate score.
 Exact proposition: Theorem variance_size_increment_1 : forall n m k p q r h, sb_variance (n+h) m k p q r = sb_variance n m k p q r+h*p*(1-p).
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem variance_size_increment_1 : forall n m k p q r h, sb_variance (n+h) m k p q r = sb_variance n m k p q r+h*p*(1-p).
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [variance_size_increment_2] (theorem).
 Mathematical meaning: The 2th cohort exposure marginal for variance is exactly the cohort-specific rate score.
 Exact proposition: Theorem variance_size_increment_2 : forall n m k p q r h, sb_variance n (m+h) k p q r = sb_variance n m k p q r+h*q*(1-q).
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem variance_size_increment_2 : forall n m k p q r h, sb_variance n (m+h) k p q r = sb_variance n m k p q r+h*q*(1-q).
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [variance_size_increment_3] (theorem).
 Mathematical meaning: The 3th cohort exposure marginal for variance is exactly the cohort-specific rate score.
 Exact proposition: Theorem variance_size_increment_3 : forall n m k p q r h, sb_variance n m (k+h) p q r = sb_variance n m k p q r+h*r*(1-r).
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem variance_size_increment_3 : forall n m k p q r h, sb_variance n m (k+h) p q r = sb_variance n m k p q r+h*r*(1-r).
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [second_size_increment_1] (theorem).
 Mathematical meaning: The 1th cohort exposure marginal for second is exactly the cohort-specific rate score.
 Exact proposition: Theorem second_size_increment_1 : forall n m k p q r h, sb_second (n+h) m k p q r = sb_second n m k p q r+h*p*p.
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem second_size_increment_1 : forall n m k p q r h, sb_second (n+h) m k p q r = sb_second n m k p q r+h*p*p.
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [second_size_increment_2] (theorem).
 Mathematical meaning: The 2th cohort exposure marginal for second is exactly the cohort-specific rate score.
 Exact proposition: Theorem second_size_increment_2 : forall n m k p q r h, sb_second n (m+h) k p q r = sb_second n m k p q r+h*q*q.
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem second_size_increment_2 : forall n m k p q r h, sb_second n (m+h) k p q r = sb_second n m k p q r+h*q*q.
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [second_size_increment_3] (theorem).
 Mathematical meaning: The 3th cohort exposure marginal for second is exactly the cohort-specific rate score.
 Exact proposition: Theorem second_size_increment_3 : forall n m k p q r h, sb_second n m (k+h) p q r = sb_second n m k p q r+h*r*r.
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem second_size_increment_3 : forall n m k p q r h, sb_second n m (k+h) p q r = sb_second n m k p q r+h*r*r.
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [loss_size_increment_1] (theorem).
 Mathematical meaning: The 1th cohort exposure marginal for loss is exactly the cohort-specific rate score.
 Exact proposition: Theorem loss_size_increment_1 : forall n m k p q r t h, sb_loss (n+h) m k p q r t = sb_loss n m k p q r t+h*(p-t)*(p-t).
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem loss_size_increment_1 : forall n m k p q r t h, sb_loss (n+h) m k p q r t = sb_loss n m k p q r t+h*(p-t)*(p-t).
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [loss_size_increment_2] (theorem).
 Mathematical meaning: The 2th cohort exposure marginal for loss is exactly the cohort-specific rate score.
 Exact proposition: Theorem loss_size_increment_2 : forall n m k p q r t h, sb_loss n (m+h) k p q r t = sb_loss n m k p q r t+h*(q-t)*(q-t).
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem loss_size_increment_2 : forall n m k p q r t h, sb_loss n (m+h) k p q r t = sb_loss n m k p q r t+h*(q-t)*(q-t).
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [loss_size_increment_3] (theorem).
 Mathematical meaning: The 3th cohort exposure marginal for loss is exactly the cohort-specific rate score.
 Exact proposition: Theorem loss_size_increment_3 : forall n m k p q r t h, sb_loss n m (k+h) p q r t = sb_loss n m k p q r t+h*(r-t)*(r-t).
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem loss_size_increment_3 : forall n m k p q r t h, sb_loss n m (k+h) p q r t = sb_loss n m k p q r t+h*(r-t)*(r-t).
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [net_size_increment_1] (theorem).
 Mathematical meaning: The 1th cohort exposure marginal for net is exactly the cohort-specific rate score.
 Exact proposition: Theorem net_size_increment_1 : forall n m k p q r h, sb_net (n+h) m k p q r = sb_net n m k p q r+h*(2*p-1).
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem net_size_increment_1 : forall n m k p q r h, sb_net (n+h) m k p q r = sb_net n m k p q r+h*(2*p-1).
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [net_size_increment_2] (theorem).
 Mathematical meaning: The 2th cohort exposure marginal for net is exactly the cohort-specific rate score.
 Exact proposition: Theorem net_size_increment_2 : forall n m k p q r h, sb_net n (m+h) k p q r = sb_net n m k p q r+h*(2*q-1).
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem net_size_increment_2 : forall n m k p q r h, sb_net n (m+h) k p q r = sb_net n m k p q r+h*(2*q-1).
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [net_size_increment_3] (theorem).
 Mathematical meaning: The 3th cohort exposure marginal for net is exactly the cohort-specific rate score.
 Exact proposition: Theorem net_size_increment_3 : forall n m k p q r h, sb_net n m (k+h) p q r = sb_net n m k p q r+h*(2*r-1).
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem net_size_increment_3 : forall n m k p q r h, sb_net n m (k+h) p q r = sb_net n m k p q r+h*(2*r-1).
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [offset_size_increment_1] (theorem).
 Mathematical meaning: The 1th cohort exposure marginal for offset is exactly the cohort-specific rate score.
 Exact proposition: Theorem offset_size_increment_1 : forall n m k p q r t h, sb_offset (n+h) m k p q r t = sb_offset n m k p q r t+h*(p-t).
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem offset_size_increment_1 : forall n m k p q r t h, sb_offset (n+h) m k p q r t = sb_offset n m k p q r t+h*(p-t).
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [offset_size_increment_2] (theorem).
 Mathematical meaning: The 2th cohort exposure marginal for offset is exactly the cohort-specific rate score.
 Exact proposition: Theorem offset_size_increment_2 : forall n m k p q r t h, sb_offset n (m+h) k p q r t = sb_offset n m k p q r t+h*(q-t).
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem offset_size_increment_2 : forall n m k p q r t h, sb_offset n (m+h) k p q r t = sb_offset n m k p q r t+h*(q-t).
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [offset_size_increment_3] (theorem).
 Mathematical meaning: The 3th cohort exposure marginal for offset is exactly the cohort-specific rate score.
 Exact proposition: Theorem offset_size_increment_3 : forall n m k p q r t h, sb_offset n m (k+h) p q r t = sb_offset n m k p q r t+h*(r-t).
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem offset_size_increment_3 : forall n m k p q r t h, sb_offset n m (k+h) p q r t = sb_offset n m k p q r t+h*(r-t).
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [success_rate_replacement_1] (theorem).
 Mathematical meaning: Exact finite change in success when the 1th event rate is replaced by an alternative rate.
 Exact proposition: Theorem success_rate_replacement_1 : forall n m k p q r s, sb_success n m k s q r = sb_success n m k p q r+n*(s-p).
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem success_rate_replacement_1 : forall n m k p q r s, sb_success n m k s q r = sb_success n m k p q r+n*(s-p).
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [success_rate_replacement_2] (theorem).
 Mathematical meaning: Exact finite change in success when the 2th event rate is replaced by an alternative rate.
 Exact proposition: Theorem success_rate_replacement_2 : forall n m k p q r s, sb_success n m k p s r = sb_success n m k p q r+m*(s-q).
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem success_rate_replacement_2 : forall n m k p q r s, sb_success n m k p s r = sb_success n m k p q r+m*(s-q).
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [success_rate_replacement_3] (theorem).
 Mathematical meaning: Exact finite change in success when the 3th event rate is replaced by an alternative rate.
 Exact proposition: Theorem success_rate_replacement_3 : forall n m k p q r s, sb_success n m k p q s = sb_success n m k p q r+k*(s-r).
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem success_rate_replacement_3 : forall n m k p q r s, sb_success n m k p q s = sb_success n m k p q r+k*(s-r).
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [failure_rate_replacement_1] (theorem).
 Mathematical meaning: Exact finite change in failure when the 1th event rate is replaced by an alternative rate.
 Exact proposition: Theorem failure_rate_replacement_1 : forall n m k p q r s, sb_failure n m k s q r = sb_failure n m k p q r+n*(p-s).
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem failure_rate_replacement_1 : forall n m k p q r s, sb_failure n m k s q r = sb_failure n m k p q r+n*(p-s).
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [failure_rate_replacement_2] (theorem).
 Mathematical meaning: Exact finite change in failure when the 2th event rate is replaced by an alternative rate.
 Exact proposition: Theorem failure_rate_replacement_2 : forall n m k p q r s, sb_failure n m k p s r = sb_failure n m k p q r+m*(q-s).
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem failure_rate_replacement_2 : forall n m k p q r s, sb_failure n m k p s r = sb_failure n m k p q r+m*(q-s).
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [failure_rate_replacement_3] (theorem).
 Mathematical meaning: Exact finite change in failure when the 3th event rate is replaced by an alternative rate.
 Exact proposition: Theorem failure_rate_replacement_3 : forall n m k p q r s, sb_failure n m k p q s = sb_failure n m k p q r+k*(r-s).
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem failure_rate_replacement_3 : forall n m k p q r s, sb_failure n m k p q s = sb_failure n m k p q r+k*(r-s).
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [variance_rate_replacement_1] (theorem).
 Mathematical meaning: Exact finite change in variance when the 1th event rate is replaced by an alternative rate.
 Exact proposition: Theorem variance_rate_replacement_1 : forall n m k p q r s, sb_variance n m k s q r = sb_variance n m k p q r+n*(s-p)*(1-s-p).
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem variance_rate_replacement_1 : forall n m k p q r s, sb_variance n m k s q r = sb_variance n m k p q r+n*(s-p)*(1-s-p).
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [variance_rate_replacement_2] (theorem).
 Mathematical meaning: Exact finite change in variance when the 2th event rate is replaced by an alternative rate.
 Exact proposition: Theorem variance_rate_replacement_2 : forall n m k p q r s, sb_variance n m k p s r = sb_variance n m k p q r+m*(s-q)*(1-s-q).
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem variance_rate_replacement_2 : forall n m k p q r s, sb_variance n m k p s r = sb_variance n m k p q r+m*(s-q)*(1-s-q).
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [variance_rate_replacement_3] (theorem).
 Mathematical meaning: Exact finite change in variance when the 3th event rate is replaced by an alternative rate.
 Exact proposition: Theorem variance_rate_replacement_3 : forall n m k p q r s, sb_variance n m k p q s = sb_variance n m k p q r+k*(s-r)*(1-s-r).
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem variance_rate_replacement_3 : forall n m k p q r s, sb_variance n m k p q s = sb_variance n m k p q r+k*(s-r)*(1-s-r).
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [second_rate_replacement_1] (theorem).
 Mathematical meaning: Exact finite change in second when the 1th event rate is replaced by an alternative rate.
 Exact proposition: Theorem second_rate_replacement_1 : forall n m k p q r s, sb_second n m k s q r = sb_second n m k p q r+n*(s-p)*(s+p).
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem second_rate_replacement_1 : forall n m k p q r s, sb_second n m k s q r = sb_second n m k p q r+n*(s-p)*(s+p).
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [second_rate_replacement_2] (theorem).
 Mathematical meaning: Exact finite change in second when the 2th event rate is replaced by an alternative rate.
 Exact proposition: Theorem second_rate_replacement_2 : forall n m k p q r s, sb_second n m k p s r = sb_second n m k p q r+m*(s-q)*(s+q).
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem second_rate_replacement_2 : forall n m k p q r s, sb_second n m k p s r = sb_second n m k p q r+m*(s-q)*(s+q).
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [second_rate_replacement_3] (theorem).
 Mathematical meaning: Exact finite change in second when the 3th event rate is replaced by an alternative rate.
 Exact proposition: Theorem second_rate_replacement_3 : forall n m k p q r s, sb_second n m k p q s = sb_second n m k p q r+k*(s-r)*(s+r).
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem second_rate_replacement_3 : forall n m k p q r s, sb_second n m k p q s = sb_second n m k p q r+k*(s-r)*(s+r).
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [loss_rate_replacement_1] (theorem).
 Mathematical meaning: Exact finite change in loss when the 1th event rate is replaced by an alternative rate.
 Exact proposition: Theorem loss_rate_replacement_1 : forall n m k p q r t s, sb_loss n m k s q r t = sb_loss n m k p q r t+n*(s-p)*(s+p-2*t).
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem loss_rate_replacement_1 : forall n m k p q r t s, sb_loss n m k s q r t = sb_loss n m k p q r t+n*(s-p)*(s+p-2*t).
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [loss_rate_replacement_2] (theorem).
 Mathematical meaning: Exact finite change in loss when the 2th event rate is replaced by an alternative rate.
 Exact proposition: Theorem loss_rate_replacement_2 : forall n m k p q r t s, sb_loss n m k p s r t = sb_loss n m k p q r t+m*(s-q)*(s+q-2*t).
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem loss_rate_replacement_2 : forall n m k p q r t s, sb_loss n m k p s r t = sb_loss n m k p q r t+m*(s-q)*(s+q-2*t).
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [loss_rate_replacement_3] (theorem).
 Mathematical meaning: Exact finite change in loss when the 3th event rate is replaced by an alternative rate.
 Exact proposition: Theorem loss_rate_replacement_3 : forall n m k p q r t s, sb_loss n m k p q s t = sb_loss n m k p q r t+k*(s-r)*(s+r-2*t).
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem loss_rate_replacement_3 : forall n m k p q r t s, sb_loss n m k p q s t = sb_loss n m k p q r t+k*(s-r)*(s+r-2*t).
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [net_rate_replacement_1] (theorem).
 Mathematical meaning: Exact finite change in net when the 1th event rate is replaced by an alternative rate.
 Exact proposition: Theorem net_rate_replacement_1 : forall n m k p q r s, sb_net n m k s q r = sb_net n m k p q r+n*2*(s-p).
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem net_rate_replacement_1 : forall n m k p q r s, sb_net n m k s q r = sb_net n m k p q r+n*2*(s-p).
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [net_rate_replacement_2] (theorem).
 Mathematical meaning: Exact finite change in net when the 2th event rate is replaced by an alternative rate.
 Exact proposition: Theorem net_rate_replacement_2 : forall n m k p q r s, sb_net n m k p s r = sb_net n m k p q r+m*2*(s-q).
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem net_rate_replacement_2 : forall n m k p q r s, sb_net n m k p s r = sb_net n m k p q r+m*2*(s-q).
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [net_rate_replacement_3] (theorem).
 Mathematical meaning: Exact finite change in net when the 3th event rate is replaced by an alternative rate.
 Exact proposition: Theorem net_rate_replacement_3 : forall n m k p q r s, sb_net n m k p q s = sb_net n m k p q r+k*2*(s-r).
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem net_rate_replacement_3 : forall n m k p q r s, sb_net n m k p q s = sb_net n m k p q r+k*2*(s-r).
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [offset_rate_replacement_1] (theorem).
 Mathematical meaning: Exact finite change in offset when the 1th event rate is replaced by an alternative rate.
 Exact proposition: Theorem offset_rate_replacement_1 : forall n m k p q r t s, sb_offset n m k s q r t = sb_offset n m k p q r t+n*(s-p).
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem offset_rate_replacement_1 : forall n m k p q r t s, sb_offset n m k s q r t = sb_offset n m k p q r t+n*(s-p).
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [offset_rate_replacement_2] (theorem).
 Mathematical meaning: Exact finite change in offset when the 2th event rate is replaced by an alternative rate.
 Exact proposition: Theorem offset_rate_replacement_2 : forall n m k p q r t s, sb_offset n m k p s r t = sb_offset n m k p q r t+m*(s-q).
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem offset_rate_replacement_2 : forall n m k p q r t s, sb_offset n m k p s r t = sb_offset n m k p q r t+m*(s-q).
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [offset_rate_replacement_3] (theorem).
 Mathematical meaning: Exact finite change in offset when the 3th event rate is replaced by an alternative rate.
 Exact proposition: Theorem offset_rate_replacement_3 : forall n m k p q r t s, sb_offset n m k p q s t = sb_offset n m k p q r t+k*(s-r).
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem offset_rate_replacement_3 : forall n m k p q r t s, sb_offset n m k p q s t = sb_offset n m k p q r t+k*(s-r).
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [dispersion_size_increment_1] (theorem).
 Mathematical meaning: Exact pairwise-heterogeneity increase when the 1th cohort exposure changes.
 Exact proposition: Theorem dispersion_size_increment_1 : forall n m k p q r h, sb_dispersion (n+h) m k p q r = sb_dispersion n m k p q r+h*m*(p-q)*(p-q)+h*k*(p-r)*(p-r).
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem dispersion_size_increment_1 : forall n m k p q r h, sb_dispersion (n+h) m k p q r = sb_dispersion n m k p q r+h*m*(p-q)*(p-q)+h*k*(p-r)*(p-r).
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [dispersion_rate_replacement_1] (theorem).
 Mathematical meaning: Exact quadratic influence of the 1th cohort rate on three-way between-group dispersion.
 Exact proposition: Theorem dispersion_rate_replacement_1 : forall n m k p q r s, sb_dispersion n m k s q r = sb_dispersion n m k p q r+n*(s-p)*(m*(s+p-2*q)+k*(s+p-2*r)).
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem dispersion_rate_replacement_1 : forall n m k p q r s, sb_dispersion n m k s q r = sb_dispersion n m k p q r+n*(s-p)*(m*(s+p-2*q)+k*(s+p-2*r)).
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [dispersion_size_increment_2] (theorem).
 Mathematical meaning: Exact pairwise-heterogeneity increase when the 2th cohort exposure changes.
 Exact proposition: Theorem dispersion_size_increment_2 : forall n m k p q r h, sb_dispersion n (m+h) k p q r = sb_dispersion n m k p q r+h*k*(q-r)*(q-r)+h*n*(q-p)*(q-p).
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem dispersion_size_increment_2 : forall n m k p q r h, sb_dispersion n (m+h) k p q r = sb_dispersion n m k p q r+h*k*(q-r)*(q-r)+h*n*(q-p)*(q-p).
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [dispersion_rate_replacement_2] (theorem).
 Mathematical meaning: Exact quadratic influence of the 2th cohort rate on three-way between-group dispersion.
 Exact proposition: Theorem dispersion_rate_replacement_2 : forall n m k p q r s, sb_dispersion n m k p s r = sb_dispersion n m k p q r+m*(s-q)*(k*(s+q-2*r)+n*(s+q-2*p)).
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem dispersion_rate_replacement_2 : forall n m k p q r s, sb_dispersion n m k p s r = sb_dispersion n m k p q r+m*(s-q)*(k*(s+q-2*r)+n*(s+q-2*p)).
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [dispersion_size_increment_3] (theorem).
 Mathematical meaning: Exact pairwise-heterogeneity increase when the 3th cohort exposure changes.
 Exact proposition: Theorem dispersion_size_increment_3 : forall n m k p q r h, sb_dispersion n m (k+h) p q r = sb_dispersion n m k p q r+h*n*(r-p)*(r-p)+h*m*(r-q)*(r-q).
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem dispersion_size_increment_3 : forall n m k p q r h, sb_dispersion n m (k+h) p q r = sb_dispersion n m k p q r+h*n*(r-p)*(r-p)+h*m*(r-q)*(r-q).
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [dispersion_rate_replacement_3] (theorem).
 Mathematical meaning: Exact quadratic influence of the 3th cohort rate on three-way between-group dispersion.
 Exact proposition: Theorem dispersion_rate_replacement_3 : forall n m k p q r s, sb_dispersion n m k p q s = sb_dispersion n m k p q r+k*(s-r)*(n*(s+r-2*p)+m*(s+r-2*q)).
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem dispersion_rate_replacement_3 : forall n m k p q r s, sb_dispersion n m k p q s = sb_dispersion n m k p q r+k*(s-r)*(n*(s+r-2*p)+m*(s+r-2*q)).
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [success_common_rate_translation] (theorem).
 Mathematical meaning: Common affine shift of all three event rates yields the precise success response.
 Exact proposition: Theorem success_common_rate_translation : forall n m k p q r h, sb_success n m k (p+h) (q+h) (r+h) = sb_success n m k p q r+h*(sb_mass n m k).
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem success_common_rate_translation : forall n m k p q r h, sb_success n m k (p+h) (q+h) (r+h) = sb_success n m k p q r+h*(sb_mass n m k).
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [success_common_rate_rescale] (theorem).
 Mathematical meaning: Scaling all event rates yields the exact success response.
 Exact proposition: Theorem success_common_rate_rescale : forall n m k p q r h, sb_success n m k (h*p) (h*q) (h*r) = h*(sb_success n m k p q r).
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem success_common_rate_rescale : forall n m k p q r h, sb_success n m k (h*p) (h*q) (h*r) = h*(sb_success n m k p q r).
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [success_complement_event_rates] (theorem).
 Mathematical meaning: Complementing all events establishes the exact successes/failures success duality.
 Exact proposition: Theorem success_complement_event_rates : forall n m k p q r, sb_success n m k (1-p) (1-q) (1-r) = sb_failure n m k p q r.
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem success_complement_event_rates : forall n m k p q r, sb_success n m k (1-p) (1-q) (1-r) = sb_failure n m k p q r.
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [success_homogeneous_rate] (theorem).
 Mathematical meaning: Three groups with a common event rate collapse into a single pooled success formula.
 Exact proposition: Theorem success_homogeneous_rate : forall n m k p, sb_success n m k p p p = (sb_mass n m k)*p.
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem success_homogeneous_rate : forall n m k p, sb_success n m k p p p = (sb_mass n m k)*p.
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [success_impossible_event] (theorem).
 Mathematical meaning: All-impossible Bernoulli event endpoint gives the exact success diagnostic.
 Exact proposition: Theorem success_impossible_event : forall n m k, sb_success n m k 0 0 0 = 0.
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem success_impossible_event : forall n m k, sb_success n m k 0 0 0 = 0.
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [success_certain_event] (theorem).
 Mathematical meaning: All-certain Bernoulli event endpoint gives the exact success diagnostic.
 Exact proposition: Theorem success_certain_event : forall n m k, sb_success n m k 1 1 1 = sb_mass n m k.
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem success_certain_event : forall n m k, sb_success n m k 1 1 1 = sb_mass n m k.
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [failure_common_rate_translation] (theorem).
 Mathematical meaning: Common affine shift of all three event rates yields the precise failure response.
 Exact proposition: Theorem failure_common_rate_translation : forall n m k p q r h, sb_failure n m k (p+h) (q+h) (r+h) = sb_failure n m k p q r-h*(sb_mass n m k).
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem failure_common_rate_translation : forall n m k p q r h, sb_failure n m k (p+h) (q+h) (r+h) = sb_failure n m k p q r-h*(sb_mass n m k).
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [failure_common_rate_rescale] (theorem).
 Mathematical meaning: Scaling all event rates yields the exact failure response.
 Exact proposition: Theorem failure_common_rate_rescale : forall n m k p q r h, sb_failure n m k (h*p) (h*q) (h*r) = sb_mass n m k-h*(sb_success n m k p q r).
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem failure_common_rate_rescale : forall n m k p q r h, sb_failure n m k (h*p) (h*q) (h*r) = sb_mass n m k-h*(sb_success n m k p q r).
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [failure_complement_event_rates] (theorem).
 Mathematical meaning: Complementing all events establishes the exact successes/failures failure duality.
 Exact proposition: Theorem failure_complement_event_rates : forall n m k p q r, sb_failure n m k (1-p) (1-q) (1-r) = sb_success n m k p q r.
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem failure_complement_event_rates : forall n m k p q r, sb_failure n m k (1-p) (1-q) (1-r) = sb_success n m k p q r.
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [failure_homogeneous_rate] (theorem).
 Mathematical meaning: Three groups with a common event rate collapse into a single pooled failure formula.
 Exact proposition: Theorem failure_homogeneous_rate : forall n m k p, sb_failure n m k p p p = (sb_mass n m k)*(1-p).
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem failure_homogeneous_rate : forall n m k p, sb_failure n m k p p p = (sb_mass n m k)*(1-p).
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [failure_impossible_event] (theorem).
 Mathematical meaning: All-impossible Bernoulli event endpoint gives the exact failure diagnostic.
 Exact proposition: Theorem failure_impossible_event : forall n m k, sb_failure n m k 0 0 0 = sb_mass n m k.
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem failure_impossible_event : forall n m k, sb_failure n m k 0 0 0 = sb_mass n m k.
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [failure_certain_event] (theorem).
 Mathematical meaning: All-certain Bernoulli event endpoint gives the exact failure diagnostic.
 Exact proposition: Theorem failure_certain_event : forall n m k, sb_failure n m k 1 1 1 = 0.
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem failure_certain_event : forall n m k, sb_failure n m k 1 1 1 = 0.
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [variance_common_rate_translation] (theorem).
 Mathematical meaning: Common affine shift of all three event rates yields the precise variance response.
 Exact proposition: Theorem variance_common_rate_translation : forall n m k p q r h, sb_variance n m k (p+h) (q+h) (r+h) = sb_variance n m k p q r+h*(sb_mass n m k)-2*h*(sb_success n m k p q r)-h*h*(sb_mass n m k).
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem variance_common_rate_translation : forall n m k p q r h, sb_variance n m k (p+h) (q+h) (r+h) = sb_variance n m k p q r+h*(sb_mass n m k)-2*h*(sb_success n m k p q r)-h*h*(sb_mass n m k).
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [variance_common_rate_rescale] (theorem).
 Mathematical meaning: Scaling all event rates yields the exact variance response.
 Exact proposition: Theorem variance_common_rate_rescale : forall n m k p q r h, sb_variance n m k (h*p) (h*q) (h*r) = h*(sb_success n m k p q r)-h*h*(sb_second n m k p q r).
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem variance_common_rate_rescale : forall n m k p q r h, sb_variance n m k (h*p) (h*q) (h*r) = h*(sb_success n m k p q r)-h*h*(sb_second n m k p q r).
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [variance_complement_event_rates] (theorem).
 Mathematical meaning: Complementing all events establishes the exact successes/failures variance duality.
 Exact proposition: Theorem variance_complement_event_rates : forall n m k p q r, sb_variance n m k (1-p) (1-q) (1-r) = sb_variance n m k p q r.
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem variance_complement_event_rates : forall n m k p q r, sb_variance n m k (1-p) (1-q) (1-r) = sb_variance n m k p q r.
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [variance_homogeneous_rate] (theorem).
 Mathematical meaning: Three groups with a common event rate collapse into a single pooled variance formula.
 Exact proposition: Theorem variance_homogeneous_rate : forall n m k p, sb_variance n m k p p p = (sb_mass n m k)*p*(1-p).
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem variance_homogeneous_rate : forall n m k p, sb_variance n m k p p p = (sb_mass n m k)*p*(1-p).
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [variance_impossible_event] (theorem).
 Mathematical meaning: All-impossible Bernoulli event endpoint gives the exact variance diagnostic.
 Exact proposition: Theorem variance_impossible_event : forall n m k, sb_variance n m k 0 0 0 = 0.
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem variance_impossible_event : forall n m k, sb_variance n m k 0 0 0 = 0.
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [variance_certain_event] (theorem).
 Mathematical meaning: All-certain Bernoulli event endpoint gives the exact variance diagnostic.
 Exact proposition: Theorem variance_certain_event : forall n m k, sb_variance n m k 1 1 1 = 0.
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem variance_certain_event : forall n m k, sb_variance n m k 1 1 1 = 0.
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [second_common_rate_translation] (theorem).
 Mathematical meaning: Common affine shift of all three event rates yields the precise second response.
 Exact proposition: Theorem second_common_rate_translation : forall n m k p q r h, sb_second n m k (p+h) (q+h) (r+h) = sb_second n m k p q r+2*h*(sb_success n m k p q r)+h*h*(sb_mass n m k).
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem second_common_rate_translation : forall n m k p q r h, sb_second n m k (p+h) (q+h) (r+h) = sb_second n m k p q r+2*h*(sb_success n m k p q r)+h*h*(sb_mass n m k).
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [second_common_rate_rescale] (theorem).
 Mathematical meaning: Scaling all event rates yields the exact second response.
 Exact proposition: Theorem second_common_rate_rescale : forall n m k p q r h, sb_second n m k (h*p) (h*q) (h*r) = h*h*(sb_second n m k p q r).
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem second_common_rate_rescale : forall n m k p q r h, sb_second n m k (h*p) (h*q) (h*r) = h*h*(sb_second n m k p q r).
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [second_complement_event_rates] (theorem).
 Mathematical meaning: Complementing all events establishes the exact successes/failures second duality.
 Exact proposition: Theorem second_complement_event_rates : forall n m k p q r, sb_second n m k (1-p) (1-q) (1-r) = sb_mass n m k-2*(sb_success n m k p q r)+sb_second n m k p q r.
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem second_complement_event_rates : forall n m k p q r, sb_second n m k (1-p) (1-q) (1-r) = sb_mass n m k-2*(sb_success n m k p q r)+sb_second n m k p q r.
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [second_homogeneous_rate] (theorem).
 Mathematical meaning: Three groups with a common event rate collapse into a single pooled second formula.
 Exact proposition: Theorem second_homogeneous_rate : forall n m k p, sb_second n m k p p p = (sb_mass n m k)*p*p.
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem second_homogeneous_rate : forall n m k p, sb_second n m k p p p = (sb_mass n m k)*p*p.
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [second_impossible_event] (theorem).
 Mathematical meaning: All-impossible Bernoulli event endpoint gives the exact second diagnostic.
 Exact proposition: Theorem second_impossible_event : forall n m k, sb_second n m k 0 0 0 = 0.
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem second_impossible_event : forall n m k, sb_second n m k 0 0 0 = 0.
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [second_certain_event] (theorem).
 Mathematical meaning: All-certain Bernoulli event endpoint gives the exact second diagnostic.
 Exact proposition: Theorem second_certain_event : forall n m k, sb_second n m k 1 1 1 = sb_mass n m k.
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem second_certain_event : forall n m k, sb_second n m k 1 1 1 = sb_mass n m k.
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [loss_common_rate_translation] (theorem).
 Mathematical meaning: Common affine shift of all three event rates yields the precise loss response.
 Exact proposition: Theorem loss_common_rate_translation : forall n m k p q r t h, sb_loss n m k (p+h) (q+h) (r+h) t = sb_loss n m k p q r (t-h).
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem loss_common_rate_translation : forall n m k p q r t h, sb_loss n m k (p+h) (q+h) (r+h) t = sb_loss n m k p q r (t-h).
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [loss_common_rate_rescale] (theorem).
 Mathematical meaning: Scaling all event rates and the reference rate yields the exact loss response.
 Exact proposition: Theorem loss_common_rate_rescale : forall n m k p q r t h, sb_loss n m k (h*p) (h*q) (h*r) (h*t) = h*h*(sb_loss n m k p q r t).
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem loss_common_rate_rescale : forall n m k p q r t h, sb_loss n m k (h*p) (h*q) (h*r) (h*t) = h*h*(sb_loss n m k p q r t).
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [loss_complement_event_rates] (theorem).
 Mathematical meaning: Complementing all events establishes the exact successes/failures loss duality.
 Exact proposition: Theorem loss_complement_event_rates : forall n m k p q r t, sb_loss n m k (1-p) (1-q) (1-r) (1-t) = sb_loss n m k p q r t.
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem loss_complement_event_rates : forall n m k p q r t, sb_loss n m k (1-p) (1-q) (1-r) (1-t) = sb_loss n m k p q r t.
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [loss_homogeneous_rate] (theorem).
 Mathematical meaning: Three groups with a common event rate collapse into a single pooled loss formula.
 Exact proposition: Theorem loss_homogeneous_rate : forall n m k p t, sb_loss n m k p p p t = (sb_mass n m k)*(p-t)*(p-t).
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem loss_homogeneous_rate : forall n m k p t, sb_loss n m k p p p t = (sb_mass n m k)*(p-t)*(p-t).
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [loss_impossible_event] (theorem).
 Mathematical meaning: All-impossible Bernoulli event endpoint gives the exact loss diagnostic.
 Exact proposition: Theorem loss_impossible_event : forall n m k t, sb_loss n m k 0 0 0 t = (sb_mass n m k)*t*t.
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem loss_impossible_event : forall n m k t, sb_loss n m k 0 0 0 t = (sb_mass n m k)*t*t.
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [loss_certain_event] (theorem).
 Mathematical meaning: All-certain Bernoulli event endpoint gives the exact loss diagnostic.
 Exact proposition: Theorem loss_certain_event : forall n m k t, sb_loss n m k 1 1 1 t = (sb_mass n m k)*(1-t)*(1-t).
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem loss_certain_event : forall n m k t, sb_loss n m k 1 1 1 t = (sb_mass n m k)*(1-t)*(1-t).
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [dispersion_common_rate_translation] (theorem).
 Mathematical meaning: Common affine shift of all three event rates yields the precise dispersion response.
 Exact proposition: Theorem dispersion_common_rate_translation : forall n m k p q r h, sb_dispersion n m k (p+h) (q+h) (r+h) = sb_dispersion n m k p q r.
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem dispersion_common_rate_translation : forall n m k p q r h, sb_dispersion n m k (p+h) (q+h) (r+h) = sb_dispersion n m k p q r.
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [dispersion_common_rate_rescale] (theorem).
 Mathematical meaning: Scaling all event rates yields the exact dispersion response.
 Exact proposition: Theorem dispersion_common_rate_rescale : forall n m k p q r h, sb_dispersion n m k (h*p) (h*q) (h*r) = h*h*(sb_dispersion n m k p q r).
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem dispersion_common_rate_rescale : forall n m k p q r h, sb_dispersion n m k (h*p) (h*q) (h*r) = h*h*(sb_dispersion n m k p q r).
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [dispersion_complement_event_rates] (theorem).
 Mathematical meaning: Complementing all events establishes the exact successes/failures dispersion duality.
 Exact proposition: Theorem dispersion_complement_event_rates : forall n m k p q r, sb_dispersion n m k (1-p) (1-q) (1-r) = sb_dispersion n m k p q r.
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem dispersion_complement_event_rates : forall n m k p q r, sb_dispersion n m k (1-p) (1-q) (1-r) = sb_dispersion n m k p q r.
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [dispersion_homogeneous_rate] (theorem).
 Mathematical meaning: Three groups with a common event rate collapse into a single pooled dispersion formula.
 Exact proposition: Theorem dispersion_homogeneous_rate : forall n m k p, sb_dispersion n m k p p p = 0.
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem dispersion_homogeneous_rate : forall n m k p, sb_dispersion n m k p p p = 0.
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [dispersion_impossible_event] (theorem).
 Mathematical meaning: All-impossible Bernoulli event endpoint gives the exact dispersion diagnostic.
 Exact proposition: Theorem dispersion_impossible_event : forall n m k, sb_dispersion n m k 0 0 0 = 0.
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem dispersion_impossible_event : forall n m k, sb_dispersion n m k 0 0 0 = 0.
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [dispersion_certain_event] (theorem).
 Mathematical meaning: All-certain Bernoulli event endpoint gives the exact dispersion diagnostic.
 Exact proposition: Theorem dispersion_certain_event : forall n m k, sb_dispersion n m k 1 1 1 = 0.
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem dispersion_certain_event : forall n m k, sb_dispersion n m k 1 1 1 = 0.
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [net_common_rate_translation] (theorem).
 Mathematical meaning: Common affine shift of all three event rates yields the precise net response.
 Exact proposition: Theorem net_common_rate_translation : forall n m k p q r h, sb_net n m k (p+h) (q+h) (r+h) = sb_net n m k p q r+2*h*(sb_mass n m k).
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem net_common_rate_translation : forall n m k p q r h, sb_net n m k (p+h) (q+h) (r+h) = sb_net n m k p q r+2*h*(sb_mass n m k).
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [net_common_rate_rescale] (theorem).
 Mathematical meaning: Scaling all event rates yields the exact net response.
 Exact proposition: Theorem net_common_rate_rescale : forall n m k p q r h, sb_net n m k (h*p) (h*q) (h*r) = 2*h*(sb_success n m k p q r)-sb_mass n m k.
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem net_common_rate_rescale : forall n m k p q r h, sb_net n m k (h*p) (h*q) (h*r) = 2*h*(sb_success n m k p q r)-sb_mass n m k.
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [net_complement_event_rates] (theorem).
 Mathematical meaning: Complementing all events establishes the exact successes/failures net duality.
 Exact proposition: Theorem net_complement_event_rates : forall n m k p q r, sb_net n m k (1-p) (1-q) (1-r) = -(sb_net n m k p q r).
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem net_complement_event_rates : forall n m k p q r, sb_net n m k (1-p) (1-q) (1-r) = -(sb_net n m k p q r).
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [net_homogeneous_rate] (theorem).
 Mathematical meaning: Three groups with a common event rate collapse into a single pooled net formula.
 Exact proposition: Theorem net_homogeneous_rate : forall n m k p, sb_net n m k p p p = (sb_mass n m k)*(2*p-1).
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem net_homogeneous_rate : forall n m k p, sb_net n m k p p p = (sb_mass n m k)*(2*p-1).
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [net_impossible_event] (theorem).
 Mathematical meaning: All-impossible Bernoulli event endpoint gives the exact net diagnostic.
 Exact proposition: Theorem net_impossible_event : forall n m k, sb_net n m k 0 0 0 = -(sb_mass n m k).
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem net_impossible_event : forall n m k, sb_net n m k 0 0 0 = -(sb_mass n m k).
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [net_certain_event] (theorem).
 Mathematical meaning: All-certain Bernoulli event endpoint gives the exact net diagnostic.
 Exact proposition: Theorem net_certain_event : forall n m k, sb_net n m k 1 1 1 = sb_mass n m k.
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem net_certain_event : forall n m k, sb_net n m k 1 1 1 = sb_mass n m k.
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [offset_common_rate_translation] (theorem).
 Mathematical meaning: Common affine shift of all three event rates yields the precise offset response.
 Exact proposition: Theorem offset_common_rate_translation : forall n m k p q r t h, sb_offset n m k (p+h) (q+h) (r+h) t = sb_offset n m k p q r t+h*(sb_mass n m k).
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem offset_common_rate_translation : forall n m k p q r t h, sb_offset n m k (p+h) (q+h) (r+h) t = sb_offset n m k p q r t+h*(sb_mass n m k).
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [offset_common_rate_rescale] (theorem).
 Mathematical meaning: Scaling all event rates and the reference rate yields the exact offset response.
 Exact proposition: Theorem offset_common_rate_rescale : forall n m k p q r t h, sb_offset n m k (h*p) (h*q) (h*r) (h*t) = h*(sb_offset n m k p q r t).
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem offset_common_rate_rescale : forall n m k p q r t h, sb_offset n m k (h*p) (h*q) (h*r) (h*t) = h*(sb_offset n m k p q r t).
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [offset_complement_event_rates] (theorem).
 Mathematical meaning: Complementing all events establishes the exact successes/failures offset duality.
 Exact proposition: Theorem offset_complement_event_rates : forall n m k p q r t, sb_offset n m k (1-p) (1-q) (1-r) (1-t) = -(sb_offset n m k p q r t).
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem offset_complement_event_rates : forall n m k p q r t, sb_offset n m k (1-p) (1-q) (1-r) (1-t) = -(sb_offset n m k p q r t).
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [offset_homogeneous_rate] (theorem).
 Mathematical meaning: Three groups with a common event rate collapse into a single pooled offset formula.
 Exact proposition: Theorem offset_homogeneous_rate : forall n m k p t, sb_offset n m k p p p t = (sb_mass n m k)*(p-t).
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem offset_homogeneous_rate : forall n m k p t, sb_offset n m k p p p t = (sb_mass n m k)*(p-t).
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [offset_impossible_event] (theorem).
 Mathematical meaning: All-impossible Bernoulli event endpoint gives the exact offset diagnostic.
 Exact proposition: Theorem offset_impossible_event : forall n m k t, sb_offset n m k 0 0 0 t = -t*(sb_mass n m k).
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem offset_impossible_event : forall n m k t, sb_offset n m k 0 0 0 t = -t*(sb_mass n m k).
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [offset_certain_event] (theorem).
 Mathematical meaning: All-certain Bernoulli event endpoint gives the exact offset diagnostic.
 Exact proposition: Theorem offset_certain_event : forall n m k t, sb_offset n m k 1 1 1 t = (1-t)*(sb_mass n m k).
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem offset_certain_event : forall n m k t, sb_offset n m k 1 1 1 t = (1-t)*(sb_mass n m k).
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [loss_joint_rate_target_translation] (theorem).
 Mathematical meaning: Squared calibration loss is invariant under simultaneous rate and benchmark translation.
 Exact proposition: Theorem loss_joint_rate_target_translation : forall n m k p q r t h, sb_loss n m k (p+h) (q+h) (r+h) (t+h) = sb_loss n m k p q r t.
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem loss_joint_rate_target_translation : forall n m k p q r t h, sb_loss n m k (p+h) (q+h) (r+h) (t+h) = sb_loss n m k p q r t.
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [offset_joint_rate_target_translation] (theorem).
 Mathematical meaning: Signed benchmark count residual is invariant under simultaneous rate and benchmark translation.
 Exact proposition: Theorem offset_joint_rate_target_translation : forall n m k p q r t h, sb_offset n m k (p+h) (q+h) (r+h) (t+h) = sb_offset n m k p q r t.
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem offset_joint_rate_target_translation : forall n m k p q r t h, sb_offset n m k (p+h) (q+h) (r+h) (t+h) = sb_offset n m k p q r t.
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [mass_success_failure_decomposition] (theorem).
 Mathematical meaning: Expected success and failure counts partition the three-cohort exposure.
 Exact proposition: Theorem mass_success_failure_decomposition : forall n m k p q r, sb_success n m k p q r+sb_failure n m k p q r = sb_mass n m k.
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem mass_success_failure_decomposition : forall n m k p q r, sb_success n m k p q r+sb_failure n m k p q r = sb_mass n m k.
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [failure_as_complement] (theorem).
 Mathematical meaning: Expected failures are the exposure complement of expected successes.
 Exact proposition: Theorem failure_as_complement : forall n m k p q r, sb_failure n m k p q r = sb_mass n m k-sb_success n m k p q r.
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem failure_as_complement : forall n m k p q r, sb_failure n m k p q r = sb_mass n m k-sb_success n m k p q r.
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [net_as_success_failure_gap] (theorem).
 Mathematical meaning: Net expected count equals successes minus failures.
 Exact proposition: Theorem net_as_success_failure_gap : forall n m k p q r, sb_net n m k p q r = sb_success n m k p q r-sb_failure n m k p q r.
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem net_as_success_failure_gap : forall n m k p q r, sb_net n m k p q r = sb_success n m k p q r-sb_failure n m k p q r.
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [net_as_two_success_minus_mass] (theorem).
 Mathematical meaning: Signed count contrast equals twice expected successes minus total opportunities.
 Exact proposition: Theorem net_as_two_success_minus_mass : forall n m k p q r, sb_net n m k p q r = 2*(sb_success n m k p q r)-sb_mass n m k.
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem net_as_two_success_minus_mass : forall n m k p q r, sb_net n m k p q r = 2*(sb_success n m k p q r)-sb_mass n m k.
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [net_plus_twice_failures] (theorem).
 Mathematical meaning: Reconstruct total opportunities from failures and net successes.
 Exact proposition: Theorem net_plus_twice_failures : forall n m k p q r, sb_net n m k p q r+2*(sb_failure n m k p q r) = sb_mass n m k.
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem net_plus_twice_failures : forall n m k p q r, sb_net n m k p q r+2*(sb_failure n m k p q r) = sb_mass n m k.
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [net_minus_twice_successes] (theorem).
 Mathematical meaning: Reconstruct total opportunities from successes and net expected count.
 Exact proposition: Theorem net_minus_twice_successes : forall n m k p q r, sb_net n m k p q r-2*(sb_success n m k p q r) = -(sb_mass n m k).
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem net_minus_twice_successes : forall n m k p q r, sb_net n m k p q r-2*(sb_success n m k p q r) = -(sb_mass n m k).
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [variance_as_success_minus_square] (theorem).
 Mathematical meaning: Variance of ideal independent Bernoulli trials is first minus second rate moment.
 Exact proposition: Theorem variance_as_success_minus_square : forall n m k p q r, sb_variance n m k p q r = sb_success n m k p q r-sb_second n m k p q r.
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem variance_as_success_minus_square : forall n m k p q r, sb_variance n m k p q r = sb_success n m k p q r-sb_second n m k p q r.
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [second_as_success_minus_variance] (theorem).
 Mathematical meaning: Second marginal rate moment is recoverable from count and ideal variance.
 Exact proposition: Theorem second_as_success_minus_variance : forall n m k p q r, sb_second n m k p q r = sb_success n m k p q r-sb_variance n m k p q r.
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem second_as_success_minus_variance : forall n m k p q r, sb_second n m k p q r = sb_success n m k p q r-sb_variance n m k p q r.
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [variance_second_sum] (theorem).
 Mathematical meaning: Exact raw-second plus Bernoulli variance decomposition of expected counts.
 Exact proposition: Theorem variance_second_sum : forall n m k p q r, sb_variance n m k p q r+sb_second n m k p q r = sb_success n m k p q r.
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem variance_second_sum : forall n m k p q r, sb_variance n m k p q r+sb_second n m k p q r = sb_success n m k p q r.
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [loss_second_moment_expansion] (theorem).
 Mathematical meaning: Exact quadratic expansion of three-stratum calibration loss.
 Exact proposition: Theorem loss_second_moment_expansion : forall n m k p q r t, sb_loss n m k p q r t = sb_second n m k p q r-2*t*(sb_success n m k p q r)+t*t*(sb_mass n m k).
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem loss_second_moment_expansion : forall n m k p q r t, sb_loss n m k p q r t = sb_second n m k p q r-2*t*(sb_success n m k p q r)+t*t*(sb_mass n m k).
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [loss_at_zero_target] (theorem).
 Mathematical meaning: Zero-benchmark quadratic loss identifies the second marginal rate moment.
 Exact proposition: Theorem loss_at_zero_target : forall n m k p q r, sb_loss n m k p q r 0 = sb_second n m k p q r.
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem loss_at_zero_target : forall n m k p q r, sb_loss n m k p q r 0 = sb_second n m k p q r.
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [loss_at_unit_target] (theorem).
 Mathematical meaning: Unit-benchmark quadratic loss equals squared failure-rate moment.
 Exact proposition: Theorem loss_at_unit_target : forall n m k p q r, sb_loss n m k p q r 1 = sb_mass n m k-2*(sb_success n m k p q r)+sb_second n m k p q r.
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem loss_at_unit_target : forall n m k p q r, sb_loss n m k p q r 1 = sb_mass n m k-2*(sb_success n m k p q r)+sb_second n m k p q r.
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [offset_from_success] (theorem).
 Mathematical meaning: Excess event count is difference between heterogeneous expectation and common benchmark.
 Exact proposition: Theorem offset_from_success : forall n m k p q r t, sb_offset n m k p q r t = sb_success n m k p q r-t*(sb_mass n m k).
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem offset_from_success : forall n m k p q r t, sb_offset n m k p q r t = sb_success n m k p q r-t*(sb_mass n m k).
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [offset_at_zero_target] (theorem).
 Mathematical meaning: Zero-benchmark signed offset is the expected successes total.
 Exact proposition: Theorem offset_at_zero_target : forall n m k p q r, sb_offset n m k p q r 0 = sb_success n m k p q r.
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem offset_at_zero_target : forall n m k p q r, sb_offset n m k p q r 0 = sb_success n m k p q r.
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [offset_at_one_target] (theorem).
 Mathematical meaning: Unit-benchmark signed offset is negative expected failures.
 Exact proposition: Theorem offset_at_one_target : forall n m k p q r, sb_offset n m k p q r 1 = -(sb_failure n m k p q r).
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem offset_at_one_target : forall n m k p q r, sb_offset n m k p q r 1 = -(sb_failure n m k p q r).
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [loss_target_increment] (theorem).
 Mathematical meaning: Exact change in squared deviation when the common calibration target is adjusted.
 Exact proposition: Theorem loss_target_increment : forall n m k p q r t h, sb_loss n m k p q r (t+h) = sb_loss n m k p q r t+h*(2*t*(sb_mass n m k)+h*(sb_mass n m k)-2*(sb_success n m k p q r)).
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem loss_target_increment : forall n m k p q r t h, sb_loss n m k p q r (t+h) = sb_loss n m k p q r t+h*(2*t*(sb_mass n m k)+h*(sb_mass n m k)-2*(sb_success n m k p q r)).
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [offset_target_increment] (theorem).
 Mathematical meaning: Exact linear adjustment of count residual as the benchmark changes.
 Exact proposition: Theorem offset_target_increment : forall n m k p q r t h, sb_offset n m k p q r (t+h) = sb_offset n m k p q r t-h*(sb_mass n m k).
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem offset_target_increment : forall n m k p q r t h, sb_offset n m k p q r (t+h) = sb_offset n m k p q r t-h*(sb_mass n m k).
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [loss_target_sign_pair] (theorem).
 Mathematical meaning: Positive and negative benchmark losses isolate the second rate moment.
 Exact proposition: Theorem loss_target_sign_pair : forall n m k p q r t, sb_loss n m k p q r t+sb_loss n m k p q r (-t) = 2*(sb_second n m k p q r)+2*t*t*(sb_mass n m k).
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem loss_target_sign_pair : forall n m k p q r t, sb_loss n m k p q r t+sb_loss n m k p q r (-t) = 2*(sb_second n m k p q r)+2*t*t*(sb_mass n m k).
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [loss_target_opposite_difference] (theorem).
 Mathematical meaning: Loss difference between opposite benchmarks recovers the expected count.
 Exact proposition: Theorem loss_target_opposite_difference : forall n m k p q r t, sb_loss n m k p q r (-t) = sb_loss n m k p q r t+4*t*(sb_success n m k p q r).
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem loss_target_opposite_difference : forall n m k p q r t, sb_loss n m k p q r (-t) = sb_loss n m k p q r t+4*t*(sb_success n m k p q r).
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [pair_dispersion_moment_identity] (theorem).
 Mathematical meaning: Exact three-rate pairwise dispersion equals total exposure times second moment minus squared first moment.
 Exact proposition: Theorem pair_dispersion_moment_identity : forall n m k p q r, sb_dispersion n m k p q r = (sb_mass n m k)*(sb_second n m k p q r)-(sb_success n m k p q r)*(sb_success n m k p q r).
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem pair_dispersion_moment_identity : forall n m k p q r, sb_dispersion n m k p q r = (sb_mass n m k)*(sb_second n m k p q r)-(sb_success n m k p q r)*(sb_success n m k p q r).
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [pair_dispersion_loss_certificate] (theorem).
 Mathematical meaning: General weighted ANOVA identity decomposes scaled loss into pairwise rate heterogeneity and benchmark bias.
 Exact proposition: Theorem pair_dispersion_loss_certificate : forall n m k p q r t, (sb_mass n m k)*(sb_loss n m k p q r t) = sb_dispersion n m k p q r+(sb_offset n m k p q r t)*(sb_offset n m k p q r t).
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem pair_dispersion_loss_certificate : forall n m k p q r t, (sb_mass n m k)*(sb_loss n m k p q r t) = sb_dispersion n m k p q r+(sb_offset n m k p q r t)*(sb_offset n m k p q r t).
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [loss_offset_difference_identity] (theorem).
 Mathematical meaning: Heterogeneity dispersion is invariant under calibration-benchmark choice.
 Exact proposition: Theorem loss_offset_difference_identity : forall n m k p q r t, (sb_mass n m k)*(sb_loss n m k p q r t)-(sb_offset n m k p q r t)*(sb_offset n m k p q r t) = sb_dispersion n m k p q r.
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem loss_offset_difference_identity : forall n m k p q r t, (sb_mass n m k)*(sb_loss n m k p q r t)-(sb_offset n m k p q r t)*(sb_offset n m k p q r t) = sb_dispersion n m k p q r.
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [success_two_rate_bridge] (theorem).
 Mathematical meaning: Three-group expected counts recover the existing canonical two-rate expression.
 Exact proposition: Theorem success_two_rate_bridge : forall n m k p q r, sb_success n m 0 p q r = rate_count n m p q.
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem success_two_rate_bridge : forall n m k p q r, sb_success n m 0 p q r = rate_count n m p q.
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

(** [variance_two_rate_bridge] (theorem).
 Mathematical meaning: Three-group hypothetical Bernoulli variance specializes to the canonical two-rate target.
 Exact proposition: Theorem variance_two_rate_bridge : forall n m k p q r, sb_variance n m 0 p q r = rate_count_variance n m p q.
 Premises and side conditions: Algebraic identities use the real number field with no hidden statistical assumptions. For a Bernoulli count interpretation, nonnegative trial counts, rates in [0,1] and independent trials would require additional justification.
 Proof/definition method: Expand canonical definitions and use the maintained Rocq Ring normalization tactic with an explicit kernel-checked proof.
 Library reuse: Stdlib Reals, Ring, Lra and Psatz, together with the canonical SamplingPrecision and TwoRatePrecision modules.
 Boundary: This is deterministic exact weighted-moment algebra, not a constructed probability space, independent-binomial sampling law, Gaussian distribution, empirical IQ validation or confidence interval coverage.
*)
Theorem variance_two_rate_bridge : forall n m k p q r, sb_variance n m 0 p q r = rate_count_variance n m p q.
Proof.
  intros; cbv [sb_mass sb_success sb_failure sb_variance sb_second sb_loss sb_dispersion sb_net sb_offset sampling_bernoulli_variance rate_count rate_count_variance]; ring.
Qed.

