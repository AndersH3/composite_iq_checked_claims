(* Mathematical identities from analyses/hoeflin-ferguson/analysis.md.
   No probability-law, Gaussianity, or empirical-correlation assumptions are
   introduced as logical axioms.  Results below are elementary real algebra
   under precisely stated hypotheses. *)
From Stdlib Require Import Reals Lra Psatz.
Open Scope R_scope.

(* Only the non-strict quotient sign combination needs a local helper:
   Rmult_le_pos and Rinv_0_lt_compat are from Stdlib.Reals; strictly
   positive quotients use Stdlib.RIneq.Rdiv_lt_0_compat directly. *)
Local Lemma nonnegative_quotient :
  forall numerator denominator,
    0 <= numerator -> 0 < denominator ->
    0 <= numerator / denominator.
Proof.
  intros a b Ha Hb.
  unfold Rdiv.
  apply Rmult_le_pos.
  - exact Ha.
  - apply Rlt_le, Rinv_0_lt_compat; exact Hb.
Qed.


Definition equal_weight_variance (n rho : R) : R :=
  rho + (1 - rho) / n.

Definition latent_reliability (n rho : R) : R :=
  n * rho / (1 + (n - 1) * rho).

Definition latent_posterior_variance (n rho : R) : R :=
  (1 - rho) / (1 + (n - 1) * rho).

Definition standardize (x mu sigma : R) : R := (x - mu) / sigma.
Definition iq_report (z scale : R) : R := 100 + scale * z.

(* The identity holds for the average correlation of distinct pairs:
   identical pairwise correlations are NOT required. *)
Theorem pair_average_variance :
  forall n pair_sum rho,
    1 < n ->
    2 * pair_sum = n * (n - 1) * rho ->
    (n + 2 * pair_sum) / (n * n) = equal_weight_variance n rho.
Proof.
  intros n pair_sum rho Hn Hsum.
  rewrite Hsum.
  unfold equal_weight_variance.
  field; lra.
Qed.

Theorem equicorrelation_variance :
  forall n rho, n <> 0 ->
    (n + n * (n - 1) * rho) / (n * n) =
    equal_weight_variance n rho.
Proof.
  intros n rho Hn.
  unfold equal_weight_variance.
  field; lra.
Qed.

Theorem variance_alternative_form :
  forall n rho, n <> 0 ->
    equal_weight_variance n rho = (1 + (n - 1) * rho) / n.
Proof.
  intros n rho Hn.
  unfold equal_weight_variance.
  field; lra.
Qed.

Theorem one_test_variance :
  forall rho, equal_weight_variance 1 rho = 1.
Proof.
  intro rho; unfold equal_weight_variance; field.
Qed.

Theorem independent_tests_variance :
  forall n, n <> 0 -> equal_weight_variance n 0 = 1 / n.
Proof.
  intros n Hn; unfold equal_weight_variance; field; lra.
Qed.

Theorem perfectly_correlated_variance :
  forall n, n <> 0 -> equal_weight_variance n 1 = 1.
Proof.
  intros n Hn; unfold equal_weight_variance; field; lra.
Qed.

Theorem variance_strictly_positive :
  forall n rho,
    1 <= n -> 0 <= rho -> rho <= 1 ->
    0 < equal_weight_variance n rho.
Proof.
  intros n rho Hn Hr0 Hr1.
  rewrite variance_alternative_form by lra.
  apply Rdiv_lt_0_compat; nra.
Qed.

Theorem variance_at_least_correlation :
  forall n rho,
    0 < n -> rho <= 1 ->
    rho <= equal_weight_variance n rho.
Proof.
  intros n rho Hn Hr.
  unfold equal_weight_variance.
  assert (Hq : 0 <= (1 - rho) / n).
  { apply nonnegative_quotient; lra. }
  lra.
Qed.

Theorem variance_at_most_one :
  forall n rho,
    1 <= n -> rho <= 1 ->
    equal_weight_variance n rho <= 1.
Proof.
  intros n rho Hn Hr.
  assert (Hdiff : 0 <= (n - 1) * (1 - rho) / n).
  { apply nonnegative_quotient; nra. }
  assert (Heq :
    1 - equal_weight_variance n rho =
      (n - 1) * (1 - rho) / n).
  { unfold equal_weight_variance; field; lra. }
  lra.
Qed.

Theorem variance_nondecreasing_in_correlation :
  forall n rho1 rho2,
    1 <= n -> rho1 <= rho2 ->
    equal_weight_variance n rho1 <= equal_weight_variance n rho2.
Proof.
  intros n rho1 rho2 Hn Hr.
  assert (Hq : 0 <= (n - 1) * (rho2 - rho1) / n).
  { apply nonnegative_quotient; nra. }
  assert (Heq :
    equal_weight_variance n rho2 - equal_weight_variance n rho1 =
      (n - 1) * (rho2 - rho1) / n).
  { unfold equal_weight_variance; field; lra. }
  lra.
Qed.

Theorem variance_gap_to_limiting_correlation :
  forall n rho, n <> 0 ->
    equal_weight_variance n rho - rho = (1 - rho) / n.
Proof.
  intros n rho Hn; unfold equal_weight_variance; ring.
Qed.

Theorem iq_standardization_inversion :
  forall x mu sigma,
    sigma <> 0 ->
    mu + sigma * standardize x mu sigma = x.
Proof.
  intros x mu sigma Hs.
  unfold standardize; field; lra.
Qed.

Theorem iq_report_standardization :
  forall x scale,
    scale <> 0 ->
    iq_report (standardize x 100 scale) scale = x.
Proof.
  intros x scale Hs.
  unfold iq_report, standardize; field; lra.
Qed.

Theorem equal_sd_composite_scale :
  forall average_iq scale divisor,
    scale <> 0 -> divisor <> 0 ->
    iq_report (standardize average_iq 100 scale / divisor) scale =
       100 + (average_iq - 100) / divisor.
Proof.
  intros average_iq scale divisor Hs Hd.
  unfold iq_report, standardize; field; lra.
Qed.

Theorem threshold_recovered_after_normalization :
  forall q positive_sd,
    positive_sd <> 0 ->
    (q * positive_sd) / positive_sd = q.
Proof.
  intros q sd Hsd; field; lra.
Qed.

Theorem normalized_variance_is_one :
  forall variance sd,
    sd <> 0 ->
    sd * sd = variance ->
    variance / (sd * sd) = 1.
Proof.
  intros variance sd Hsd Heq; subst variance; field; nra.
Qed.

Theorem standardized_160_sd15 :
  standardize 160 100 15 = 4.
Proof.
  unfold standardize; field.
Qed.

Theorem standardized_160_sd16 :
  standardize 160 100 16 = 15 / 4.
Proof.
  unfold standardize; field.
Qed.

Theorem latent_reliability_plus_posterior_variance :
  forall n rho,
    1 <= n -> 0 <= rho ->
    latent_reliability n rho +
      latent_posterior_variance n rho = 1.
Proof.
  intros n rho Hn Hr.
  unfold latent_reliability, latent_posterior_variance.
  field; nra.
Qed.

Theorem latent_reliability_nonnegative :
  forall n rho,
    1 <= n -> 0 <= rho ->
    0 <= latent_reliability n rho.
Proof.
  intros n rho Hn Hr.
  unfold latent_reliability.
  apply nonnegative_quotient; nra.
Qed.

Theorem latent_posterior_variance_nonnegative :
  forall n rho,
    1 <= n -> 0 <= rho -> rho <= 1 ->
    0 <= latent_posterior_variance n rho.
Proof.
  intros n rho Hn Hr0 Hr1.
  unfold latent_posterior_variance.
  apply nonnegative_quotient; nra.
Qed.

Theorem latent_reliability_at_most_one :
  forall n rho,
    1 <= n -> 0 <= rho -> rho <= 1 ->
    latent_reliability n rho <= 1.
Proof.
  intros n rho Hn Hr0 Hr1.
  pose proof (latent_reliability_plus_posterior_variance
    n rho Hn Hr0) as Hp.
  pose proof (latent_posterior_variance_nonnegative
    n rho Hn Hr0 Hr1) as Hnv.
  lra.
Qed.

Theorem latent_reliability_for_one_test :
  forall rho, latent_reliability 1 rho = rho.
Proof.
  intro rho; unfold latent_reliability; field.
Qed.

Theorem latent_reliability_at_zero :
  forall n, latent_reliability n 0 = 0.
Proof.
  intro n; unfold latent_reliability; field.
Qed.

Theorem latent_variance_at_zero :
  forall n, latent_posterior_variance n 0 = 1.
Proof.
  intro n; unfold latent_posterior_variance; field.
Qed.

Theorem latent_variance_at_perfect_correlation :
  forall n, 1 <= n -> latent_posterior_variance n 1 = 0.
Proof.
  intros n Hn; unfold latent_posterior_variance; field; lra.
Qed.

(* The covariance/conditional-Gaussian interpretation of these formulas,
   numerical normal quantiles and the limiting sqrt expression are NOT
   established by these algebraic theorems. *)


(* Extensions: monotonicity and sensitivity of the composite's dispersion.
   For fixed rho <= 1, averaging more equally weighted tests cannot
   increase this model variance. No distributional assumption is used. *)

Theorem variance_decreases_with_test_count :
  forall n1 n2 rho,
    1 <= n1 -> n1 <= n2 -> rho <= 1 ->
    equal_weight_variance n2 rho <= equal_weight_variance n1 rho.
Proof.
  intros n1 n2 rho Hn1 Horder Hr.
  assert (Hfrac :
    0 <= (1 - rho) * (n2 - n1) / (n1 * n2)).
  { apply nonnegative_quotient; nra. }
  assert (Hidentity :
    equal_weight_variance n1 rho -
      equal_weight_variance n2 rho =
      (1 - rho) * (n2 - n1) / (n1 * n2)).
  { unfold equal_weight_variance; field; nra. }
  lra.
Qed.

Theorem variance_strictly_decreases_with_test_count :
  forall n1 n2 rho,
    1 <= n1 -> n1 < n2 -> rho < 1 ->
    equal_weight_variance n2 rho < equal_weight_variance n1 rho.
Proof.
  intros n1 n2 rho Hn1 Horder Hr.
  assert (Hfrac :
    0 < (1 - rho) * (n2 - n1) / (n1 * n2)).
  { apply Rdiv_lt_0_compat; nra. }
  assert (Hidentity :
    equal_weight_variance n1 rho -
      equal_weight_variance n2 rho =
      (1 - rho) * (n2 - n1) / (n1 * n2)).
  { unfold equal_weight_variance; field; nra. }
  lra.
Qed.

Theorem variance_is_affine_in_correlation :
  forall n rho,
    n <> 0 ->
    equal_weight_variance n rho =
      1 / n + ((n - 1) / n) * rho.
Proof.
  intros n rho Hn.
  unfold equal_weight_variance.
  field; lra.
Qed.

Theorem variance_correlation_sensitivity :
  forall n rho1 rho2,
    n <> 0 ->
    equal_weight_variance n rho2 -
      equal_weight_variance n rho1 =
      ((n - 1) / n) * (rho2 - rho1).
Proof.
  intros n rho1 rho2 Hn.
  unfold equal_weight_variance.
  field; lra.
Qed.

Theorem variance_of_two_equicorrelated_tests :
  forall rho, equal_weight_variance 2 rho = (1 + rho) / 2.
Proof.
  intro rho; unfold equal_weight_variance; field.
Qed.

Theorem variance_of_three_equicorrelated_tests :
  forall rho, equal_weight_variance 3 rho = (1 + 2 * rho) / 3.
Proof.
  intro rho; unfold equal_weight_variance; field.
Qed.

Theorem latent_variance_denominator_positive :
  forall n rho,
    1 <= n -> 0 <= rho ->
    0 < 1 + (n - 1) * rho.
Proof.
  intros n rho Hn Hr; nra.
Qed.

Theorem latent_variance_decreases_with_test_count :
  forall n1 n2 rho,
    1 <= n1 -> n1 <= n2 ->
    0 <= rho -> rho <= 1 ->
    latent_posterior_variance n2 rho <=
      latent_posterior_variance n1 rho.
Proof.
  intros n1 n2 rho Hn1 Hn2 Hr0 Hr1.
  assert (Hd1 : 0 < 1 + (n1 - 1) * rho)
    by (apply latent_variance_denominator_positive; nra).
  assert (Hd2 : 0 < 1 + (n2 - 1) * rho)
    by (apply latent_variance_denominator_positive; nra).
  assert (Hq :
    0 <= ((1 - rho) * rho * (n2 - n1)) /
      ((1 + (n1 - 1) * rho) * (1 + (n2 - 1) * rho))).
  { apply nonnegative_quotient.
    - apply Rmult_le_pos.
      + apply Rmult_le_pos; lra.
      + lra.
    - nra. }
  assert (Hident :
    latent_posterior_variance n1 rho -
      latent_posterior_variance n2 rho =
      ((1 - rho) * rho * (n2 - n1)) /
      ((1 + (n1 - 1) * rho) * (1 + (n2 - 1) * rho))).
  { unfold latent_posterior_variance; field; nra. }
  lra.
Qed.

Theorem latent_reliability_increases_with_test_count :
  forall n1 n2 rho,
    1 <= n1 -> n1 <= n2 ->
    0 <= rho -> rho <= 1 ->
    latent_reliability n1 rho <= latent_reliability n2 rho.
Proof.
  intros n1 n2 rho Hn1 Hn2 Hr0 Hr1.
  pose proof
    (latent_reliability_plus_posterior_variance n1 rho Hn1 Hr0)
    as Hfirst.
  pose proof
    (latent_reliability_plus_posterior_variance n2 rho
      (Rle_trans _ _ _ Hn1 Hn2) Hr0)
    as Hsecond.
  pose proof
    (latent_variance_decreases_with_test_count
      n1 n2 rho Hn1 Hn2 Hr0 Hr1) as Hv.
  lra.
Qed.


(* Elementary quantitative consequences of the equal-weight formula, under
   fixed average correlation. These statements do not extrapolate empirical
   correlation stability as the test battery grows. *)

Theorem doubling_battery_halves_variance_excess :
  forall n rho,
    0 < n ->
    equal_weight_variance (2 * n) rho - rho =
      (equal_weight_variance n rho - rho) / 2.
Proof.
  intros n rho Hn.
  unfold equal_weight_variance.
  field; lra.
Qed.

Theorem nonnegative_correlation_variance_at_least_independent :
  forall n rho,
    1 <= n -> 0 <= rho ->
    1 / n <= equal_weight_variance n rho.
Proof.
  intros n rho Hn Hr.
  assert (Heq :
    equal_weight_variance n rho - 1 / n = (n - 1) * rho / n).
  { unfold equal_weight_variance; field; lra. }
  assert (Hnonneg : 0 <= (n - 1) * rho / n).
  { apply nonnegative_quotient; nra. }
  lra.
Qed.

Theorem variance_excess_bound_by_inverse_battery_size :
  forall n rho,
    0 < n -> 0 <= rho -> rho <= 1 ->
    0 <= equal_weight_variance n rho - rho /\
    equal_weight_variance n rho - rho <= 1 / n.
Proof.
  intros n rho Hn Hr0 Hr1.
  rewrite variance_gap_to_limiting_correlation by lra.
  assert (Hlower : 0 <= (1 - rho) / n).
  { apply nonnegative_quotient; lra. }
  assert (Hdiff : 0 <= rho / n).
  { apply nonnegative_quotient; lra. }
  assert (Hident : 1 / n - (1 - rho) / n = rho / n).
  { field; lra. }
  lra.
Qed.

Theorem latent_reliability_times_composite_variance :
  forall n rho,
    1 <= n -> 0 <= rho ->
    latent_reliability n rho * equal_weight_variance n rho = rho.
Proof.
  intros n rho Hn Hr.
  assert (Hd : 0 < 1 + (n - 1) * rho).
  { apply latent_variance_denominator_positive; assumption. }
  unfold latent_reliability, equal_weight_variance.
  field; nra.
Qed.

Theorem latent_posterior_times_composite_variance :
  forall n rho,
    1 <= n -> 0 <= rho ->
    latent_posterior_variance n rho *
      equal_weight_variance n rho = (1 - rho) / n.
Proof.
  intros n rho Hn Hr.
  assert (Hd : 0 < 1 + (n - 1) * rho).
  { apply latent_variance_denominator_positive; assumption. }
  unfold latent_posterior_variance, equal_weight_variance.
  field; nra.
Qed.


(* Standard deviation is the standard-library real square root; the
   mathematics below reuses Stdlib.Reals sqrt_sqrt, sqrt_pos and sqrt_le_1
   rather than supplying any bespoke square-root implementation. *)

Definition composite_standard_deviation (n rho : R) : R :=
  sqrt (equal_weight_variance n rho).

Theorem composite_standard_deviation_nonnegative :
  forall n rho, 0 <= composite_standard_deviation n rho.
Proof.
  intros n rho.
  unfold composite_standard_deviation.
  apply sqrt_pos.
Qed.

Theorem composite_standard_deviation_squared :
  forall n rho,
    1 <= n -> 0 <= rho -> rho <= 1 ->
    composite_standard_deviation n rho *
      composite_standard_deviation n rho =
      equal_weight_variance n rho.
Proof.
  intros n rho Hn Hr0 Hr1.
  unfold composite_standard_deviation.
  apply sqrt_sqrt.
  pose proof (variance_strictly_positive n rho Hn Hr0 Hr1); lra.
Qed.

Theorem composite_standard_deviation_at_zero_correlation :
  forall n, 1 <= n ->
    composite_standard_deviation n 0 = sqrt (1 / n).
Proof.
  intros n Hn.
  unfold composite_standard_deviation.
  rewrite independent_tests_variance by lra.
  reflexivity.
Qed.

Theorem composite_standard_deviation_at_perfect_correlation :
  forall n, 1 <= n ->
    composite_standard_deviation n 1 = 1.
Proof.
  intros n Hn.
  unfold composite_standard_deviation.
  rewrite perfectly_correlated_variance by lra.
  apply sqrt_1.
Qed.

Theorem composite_standard_deviation_nondecreasing_in_correlation :
  forall n rho1 rho2,
    1 <= n -> 0 <= rho1 -> rho1 <= rho2 -> rho2 <= 1 ->
    composite_standard_deviation n rho1 <=
      composite_standard_deviation n rho2.
Proof.
  intros n rho1 rho2 Hn Hr0 Horder Hr1.
  assert (Hv1 : 0 <= equal_weight_variance n rho1).
  { assert (Hr1a : rho1 <= 1) by lra.
    pose proof (variance_strictly_positive n rho1 Hn Hr0 Hr1a); lra. }
  assert (Hv2 : 0 <= equal_weight_variance n rho2).
  { assert (Hr2a : 0 <= rho2) by lra.
    pose proof (variance_strictly_positive n rho2 Hn Hr2a Hr1); lra. }
  unfold composite_standard_deviation.
  apply sqrt_le_1; try assumption.
  apply variance_nondecreasing_in_correlation; lra.
Qed.

Theorem composite_standard_deviation_nonincreasing_in_test_count :
  forall n1 n2 rho,
    1 <= n1 -> n1 <= n2 ->
    0 <= rho -> rho <= 1 ->
    composite_standard_deviation n2 rho <=
      composite_standard_deviation n1 rho.
Proof.
  intros n1 n2 rho Hn1 Horder Hr0 Hr1.
  assert (Hn2 : 1 <= n2) by lra.
  assert (Hv1 : 0 <= equal_weight_variance n1 rho).
  { pose proof (variance_strictly_positive n1 rho Hn1 Hr0 Hr1).
    lra. }
  assert (Hv2 : 0 <= equal_weight_variance n2 rho).
  { pose proof (variance_strictly_positive n2 rho Hn2 Hr0 Hr1).
    lra. }
  unfold composite_standard_deviation.
  apply sqrt_le_1; try assumption.
  apply variance_decreases_with_test_count; lra.
Qed.

Theorem composite_standard_deviation_at_most_one :
  forall n rho,
    1 <= n -> 0 <= rho -> rho <= 1 ->
    composite_standard_deviation n rho <= 1.
Proof.
  intros n rho Hn Hr0 Hr1.
  unfold composite_standard_deviation.
  rewrite <- sqrt_1.
  apply sqrt_le_1.
  - pose proof (variance_strictly_positive n rho Hn Hr0 Hr1); lra.
  - lra.
  - apply variance_at_most_one; lra.
Qed.

Theorem composite_standard_deviation_at_least_sqrt_correlation :
  forall n rho,
    1 <= n -> 0 <= rho -> rho <= 1 ->
    sqrt rho <= composite_standard_deviation n rho.
Proof.
  intros n rho Hn Hr0 Hr1.
  unfold composite_standard_deviation.
  apply sqrt_le_1.
  - exact Hr0.
  - pose proof (variance_strictly_positive n rho Hn Hr0 Hr1); lra.
  - apply variance_at_least_correlation; lra.
Qed.


(* Strict and quantitative standard-deviation comparisons, by reusing the
   standard-library monotonicity theorems for sqrt. *)

Theorem composite_standard_deviation_positive :
  forall n rho,
    1 <= n -> 0 <= rho -> rho <= 1 ->
    0 < composite_standard_deviation n rho.
Proof.
  intros n rho Hn Hr0 Hr1.
  unfold composite_standard_deviation.
  apply sqrt_lt_R0.
  apply variance_strictly_positive; assumption.
Qed.

Theorem composite_standard_deviation_strictly_decreases_with_test_count :
  forall n1 n2 rho,
    1 <= n1 -> n1 < n2 ->
    0 <= rho -> rho < 1 ->
    composite_standard_deviation n2 rho <
      composite_standard_deviation n1 rho.
Proof.
  intros n1 n2 rho Hn1 Horder Hr0 Hr1.
  assert (Hn2 : 1 <= n2) by lra.
  assert (Hrle : rho <= 1) by lra.
  unfold composite_standard_deviation.
  apply sqrt_lt_1.
  - pose proof (variance_strictly_positive n2 rho Hn2 Hr0 Hrle).
    lra.
  - pose proof (variance_strictly_positive n1 rho Hn1 Hr0 Hrle).
    lra.
  - apply variance_strictly_decreases_with_test_count; lra.
Qed.

Theorem composite_standard_deviation_strictly_increases_in_correlation :
  forall n rho1 rho2,
    1 < n ->
    0 <= rho1 -> rho1 < rho2 -> rho2 <= 1 ->
    composite_standard_deviation n rho1 <
      composite_standard_deviation n rho2.
Proof.
  intros n rho1 rho2 Hn Hr0 Horder Hr1.
  assert (Hn1 : 1 <= n) by lra.
  assert (Hrho1le : rho1 <= 1) by lra.
  assert (Hr2 : 0 <= rho2) by lra.
  assert (Hcoeff : 0 < (n - 1) / n).
  { apply Rdiv_lt_0_compat; lra. }
  assert (Hdelta :
    0 < equal_weight_variance n rho2 -
        equal_weight_variance n rho1).
  { rewrite variance_correlation_sensitivity by lra.
    nra. }
  unfold composite_standard_deviation.
  apply sqrt_lt_1.
  - pose proof (variance_strictly_positive n rho1 Hn1 Hr0 Hrho1le).
    lra.
  - pose proof (variance_strictly_positive n rho2 Hn1 Hr2 Hr1).
    lra.
  - lra.
Qed.

Theorem composite_standard_deviation_at_least_independent_baseline :
  forall n rho,
    1 <= n -> 0 <= rho -> rho <= 1 ->
    sqrt (1 / n) <= composite_standard_deviation n rho.
Proof.
  intros n rho Hn Hr0 Hr1.
  assert (Hbaseline : 0 <= 1 / n).
  { apply nonnegative_quotient; lra. }
  assert (Hvariance : 0 <= equal_weight_variance n rho).
  { pose proof (variance_strictly_positive n rho Hn Hr0 Hr1).
    lra. }
  unfold composite_standard_deviation.
  apply sqrt_le_1.
  - exact Hbaseline.
  - exact Hvariance.
  - apply nonnegative_correlation_variance_at_least_independent;
      assumption.
Qed.

Theorem composite_standard_deviation_strictly_below_one :
  forall n rho,
    1 < n -> 0 <= rho -> rho < 1 ->
    composite_standard_deviation n rho < 1.
Proof.
  intros n rho Hn Hr0 Hr1.
  assert (Hn1 : 1 <= n) by lra.
  assert (Hrle : rho <= 1) by lra.
  assert (Hgap : 0 < (n - 1) * (1 - rho) / n).
  { apply Rdiv_lt_0_compat; nra. }
  assert (Heq :
    1 - equal_weight_variance n rho =
      (n - 1) * (1 - rho) / n).
  { unfold equal_weight_variance; field; lra. }
  assert (Hvlt : equal_weight_variance n rho < 1) by lra.
  unfold composite_standard_deviation.
  rewrite <- sqrt_1.
  apply sqrt_lt_1.
  - pose proof (variance_strictly_positive n rho Hn1 Hr0 Hrle).
    lra.
  - lra.
  - exact Hvlt.
Qed.


(* Reporting-threshold transformations are exact real identities.  They do
   not provide Gaussian quantiles, empirical cutoffs, or tail probabilities. *)

Theorem standardized_affine_cutoff_round_trip :
  forall z mu sigma,
    0 < sigma ->
    standardize (mu + sigma * z) mu sigma = z.
Proof.
  intros z mu sigma Hsigma.
  unfold standardize.
  field; lra.
Qed.

Theorem positive_scale_preserves_cutoff_order :
  forall z1 z2 mu sigma,
    0 < sigma -> z1 <= z2 ->
    mu + sigma * z1 <= mu + sigma * z2.
Proof.
  intros z1 z2 mu sigma Hsigma Horder.
  nra.
Qed.

Theorem composite_standardized_cutoff_round_trip :
  forall z mu scale n rho,
    1 <= n -> 0 <= rho -> rho <= 1 -> 0 < scale ->
    standardize
      (mu + (scale * composite_standard_deviation n rho) * z)
      mu (scale * composite_standard_deviation n rho) = z.
Proof.
  intros z mu scale n rho Hn Hr0 Hr1 Hscale.
  pose proof
    (composite_standard_deviation_positive n rho Hn Hr0 Hr1) as Hsd.
  apply standardized_affine_cutoff_round_trip; nra.
Qed.

Theorem positive_cutoff_nonincreasing_with_test_count :
  forall n1 n2 rho mu scale z,
    1 <= n1 -> n1 <= n2 ->
    0 <= rho -> rho <= 1 ->
    0 <= scale -> 0 <= z ->
    mu + (scale * composite_standard_deviation n2 rho) * z <=
      mu + (scale * composite_standard_deviation n1 rho) * z.
Proof.
  intros n1 n2 rho mu scale z Hn Horder Hr0 Hr1 Hscale Hz.
  pose proof
    (composite_standard_deviation_nonincreasing_in_test_count
      n1 n2 rho Hn Horder Hr0 Hr1) as Hsd.
  apply Rplus_le_compat_l.
  apply Rmult_le_compat_r; [exact Hz |].
  apply Rmult_le_compat_l; [exact Hscale | exact Hsd].
Qed.
