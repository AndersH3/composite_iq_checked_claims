(* Mathematical identities from analyses/hoeflin-ferguson/analysis.md.
   No probability-law, Gaussianity, or empirical-correlation assumptions are
   introduced as logical axioms.  Results below are elementary real algebra
   under precisely stated hypotheses. *)
From Stdlib Require Import Reals Lra Psatz.
Open Scope R_scope.

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
  { apply Rdiv_le_0_compat; lra. }
  lra.
Qed.

Theorem variance_at_most_one :
  forall n rho,
    1 <= n -> rho <= 1 ->
    equal_weight_variance n rho <= 1.
Proof.
  intros n rho Hn Hr.
  assert (Hdiff : 0 <= (n - 1) * (1 - rho) / n).
  { apply Rdiv_le_0_compat; nra. }
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
  { apply Rdiv_le_0_compat; nra. }
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
  apply Rdiv_le_0_compat; nra.
Qed.

Theorem latent_posterior_variance_nonnegative :
  forall n rho,
    1 <= n -> 0 <= rho -> rho <= 1 ->
    0 <= latent_posterior_variance n rho.
Proof.
  intros n rho Hn Hr0 Hr1.
  unfold latent_posterior_variance.
  apply Rdiv_le_0_compat; nra.
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
