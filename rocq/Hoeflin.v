(** Module: Hoeflin.v
   Purpose: Exact algebra for the Hoeflin/Ferguson composite-score report.
   Proves real-number identities for equal-weight score batteries, correlation bounds, standardization, and elementary latent-factor formulas.
   Mathematical representation: Inputs such as test count, average pairwise covariance, scale, and residual variance are explicit real parameters rather than estimated distributions.
   Explicit hypotheses: Nonzero denominators, admissible correlation ranges and sign requirements are represented by theorem hypotheses.
   Library use: Stdlib.Reals, Lra and Psatz (including ring and field tactics).
   Limitations: No normal distribution, population correlation estimate, or measurement reliability is inferred from the algebra.
   Proof documentation: Every public and helper declaration below has its
   own statement, hypothesis, proof-approach, and scope commentary.
   Reproduction: rocq compile Hoeflin.v (after imported local modules);
   see rocq/README.md and rocq/LIBRARY_AUDIT.md for dependency order,
   checked-claim mapping, and library audit. All results are Rocq-kernel
   checked; no unchecked evidence is created by comments.
 *)
(* Mathematical identities from analyses/hoeflin-ferguson/analysis.md.
   No probability-law, Gaussianity, or empirical-correlation assumptions are
   introduced as logical axioms.  Results below are elementary real algebra
   under precisely stated hypotheses. *)
From Stdlib Require Import Reals Lra Psatz.
Open Scope R_scope.

(* Only the non-strict quotient sign combination needs a local helper:
   Rmult_le_pos and Rinv_0_lt_compat are from Stdlib.Reals; strictly
   positive quotients use Stdlib.RIneq.Rdiv_lt_0_compat directly. *)
(**
   [nonnegative_quotient] (lemma).
   Meaning: Gives a precise computational or algebraic interpretation of the
   named construction or assertion.
   Formal conclusion: 0 <= numerator / denominator.
   Hypotheses: Requires explicit nonzero/strict-positive denominator or scale
   where shown in the statement; all other constraints remain explicit.
   Proof outline: application of already-proved lemmas; notably Rmult_le_pos..
   Library discipline: Stdlib.Reals, Lra and Psatz (including ring and field
   tactics).
   Scope: No normal distribution, population correlation estimate, or
   measurement reliability is inferred from the algebra.
 *)
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


(**
   [equal_weight_variance] (definition).
   Meaning: Establishes a finite-sample variance identity or bound, including
   all stated scaling assumptions.
   Formal construction: (n rho : R) : R := rho + (1 - rho) / n.
   Hypotheses: A definition; its parameters and fields appear in the signature,
   with no silent statistical assumptions.
   Implementation: equational rewriting, Stdlib Lra linear arithmetic,
   ring/field normalization; notably equal_weight_variance..
   Library discipline: Stdlib.Reals, Lra and Psatz (including ring and field
   tactics).
   Scope: No normal distribution, population correlation estimate, or
   measurement reliability is inferred from the algebra.
 *)
Definition equal_weight_variance (n rho : R) : R :=
  rho + (1 - rho) / n.

(**
   [latent_reliability] (definition).
   Meaning: Relates variance, square root, correlation or reliability
   parameters under the displayed numerical constraints.
   Formal construction: (n rho : R) : R := n * rho / (1 + (n - 1) * rho).
   Hypotheses: A definition; its parameters and fields appear in the signature,
   with no silent statistical assumptions.
   Implementation: equational rewriting, Stdlib Lra linear arithmetic,
   ring/field normalization; notably equal_weight_variance..
   Library discipline: Stdlib.Reals, Lra and Psatz (including ring and field
   tactics).
   Scope: No normal distribution, population correlation estimate, or
   measurement reliability is inferred from the algebra.
 *)
Definition latent_reliability (n rho : R) : R :=
  n * rho / (1 + (n - 1) * rho).

(**
   [latent_posterior_variance] (definition).
   Meaning: Establishes a finite-sample variance identity or bound, including
   all stated scaling assumptions.
   Formal construction: (n rho : R) : R := (1 - rho) / (1 + (n - 1) * rho).
   Hypotheses: A definition; its parameters and fields appear in the signature,
   with no silent statistical assumptions.
   Implementation: equational rewriting, Stdlib Lra linear arithmetic,
   ring/field normalization; notably equal_weight_variance..
   Library discipline: Stdlib.Reals, Lra and Psatz (including ring and field
   tactics).
   Scope: No normal distribution, population correlation estimate, or
   measurement reliability is inferred from the algebra.
 *)
Definition latent_posterior_variance (n rho : R) : R :=
  (1 - rho) / (1 + (n - 1) * rho).

(**
   [standardize] (definition).
   Meaning: Justifies a score conversion or standardization formula by exact
   real arithmetic.
   Formal construction: (x mu sigma : R) : R := (x - mu) / sigma.
   Hypotheses: A definition; its parameters and fields appear in the signature,
   with no silent statistical assumptions.
   Implementation: equational rewriting, Stdlib Lra linear arithmetic,
   ring/field normalization; notably equal_weight_variance..
   Library discipline: Stdlib.Reals, Lra and Psatz (including ring and field
   tactics).
   Scope: No normal distribution, population correlation estimate, or
   measurement reliability is inferred from the algebra.
 *)
Definition standardize (x mu sigma : R) : R := (x - mu) / sigma.
(**
   [iq_report] (definition).
   Meaning: Justifies a score conversion or standardization formula by exact
   real arithmetic.
   Formal construction: (z scale : R) : R := 100 + scale * z.
   Hypotheses: A definition; its parameters and fields appear in the signature,
   with no silent statistical assumptions.
   Implementation: equational rewriting, Stdlib Lra linear arithmetic,
   ring/field normalization; notably equal_weight_variance..
   Library discipline: Stdlib.Reals, Lra and Psatz (including ring and field
   tactics).
   Scope: No normal distribution, population correlation estimate, or
   measurement reliability is inferred from the algebra.
 *)
Definition iq_report (z scale : R) : R := 100 + scale * z.

(* The identity holds for the average correlation of distinct pairs:
   identical pairwise correlations are NOT required. *)
(**
   [pair_average_variance] (theorem).
   Meaning: Establishes a finite-sample variance identity or bound, including
   all stated scaling assumptions.
   Formal conclusion: (n + 2 * pair_sum) / (n * n) = equal_weight_variance n
   rho.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: equational rewriting, Stdlib Lra linear arithmetic,
   ring/field normalization; notably equal_weight_variance..
   Library discipline: Stdlib.Reals, Lra and Psatz (including ring and field
   tactics).
   Scope: No normal distribution, population correlation estimate, or
   measurement reliability is inferred from the algebra.
 *)
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

(**
   [equicorrelation_variance] (theorem).
   Meaning: Establishes a finite-sample variance identity or bound, including
   all stated scaling assumptions.
   Formal conclusion: (n + n * (n - 1) * rho) / (n * n) = equal_weight_variance
   n rho.
   Hypotheses: Requires explicit nonzero/strict-positive denominator or scale
   where shown in the statement; all other constraints remain explicit.
   Proof outline: Stdlib Lra linear arithmetic, ring/field normalization;
   notably equal_weight_variance..
   Library discipline: Stdlib.Reals, Lra and Psatz (including ring and field
   tactics).
   Scope: No normal distribution, population correlation estimate, or
   measurement reliability is inferred from the algebra.
 *)
Theorem equicorrelation_variance :
  forall n rho, n <> 0 ->
    (n + n * (n - 1) * rho) / (n * n) =
    equal_weight_variance n rho.
Proof.
  intros n rho Hn.
  unfold equal_weight_variance.
  field; lra.
Qed.

(**
   [variance_alternative_form] (theorem).
   Meaning: Establishes a finite-sample variance identity or bound, including
   all stated scaling assumptions.
   Formal conclusion: equal_weight_variance n rho = (1 + (n - 1) * rho) / n.
   Hypotheses: Requires explicit nonzero/strict-positive denominator or scale
   where shown in the statement; all other constraints remain explicit.
   Proof outline: Stdlib Lra linear arithmetic, ring/field normalization;
   notably equal_weight_variance..
   Library discipline: Stdlib.Reals, Lra and Psatz (including ring and field
   tactics).
   Scope: No normal distribution, population correlation estimate, or
   measurement reliability is inferred from the algebra.
 *)
Theorem variance_alternative_form :
  forall n rho, n <> 0 ->
    equal_weight_variance n rho = (1 + (n - 1) * rho) / n.
Proof.
  intros n rho Hn.
  unfold equal_weight_variance.
  field; lra.
Qed.

(**
   [one_test_variance] (theorem).
   Meaning: Establishes a finite-sample variance identity or bound, including
   all stated scaling assumptions.
   Formal conclusion: forall rho, equal_weight_variance 1 rho = 1.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: ring/field normalization; notably equal_weight_variance.
   Library discipline: Stdlib.Reals, Lra and Psatz (including ring and field
   tactics).
   Scope: No normal distribution, population correlation estimate, or
   measurement reliability is inferred from the algebra.
 *)
Theorem one_test_variance :
  forall rho, equal_weight_variance 1 rho = 1.
Proof.
  intro rho; unfold equal_weight_variance; field.
Qed.

(**
   [independent_tests_variance] (theorem).
   Meaning: Establishes a finite-sample variance identity or bound, including
   all stated scaling assumptions.
   Formal conclusion: equal_weight_variance n 0 = 1 / n.
   Hypotheses: Requires explicit nonzero/strict-positive denominator or scale
   where shown in the statement; all other constraints remain explicit.
   Proof outline: Stdlib Lra linear arithmetic, ring/field normalization;
   notably equal_weight_variance.
   Library discipline: Stdlib.Reals, Lra and Psatz (including ring and field
   tactics).
   Scope: No normal distribution, population correlation estimate, or
   measurement reliability is inferred from the algebra.
 *)
Theorem independent_tests_variance :
  forall n, n <> 0 -> equal_weight_variance n 0 = 1 / n.
Proof.
  intros n Hn; unfold equal_weight_variance; field; lra.
Qed.

(**
   [perfectly_correlated_variance] (theorem).
   Meaning: Establishes a finite-sample variance identity or bound, including
   all stated scaling assumptions.
   Formal conclusion: equal_weight_variance n 1 = 1.
   Hypotheses: Requires explicit nonzero/strict-positive denominator or scale
   where shown in the statement; all other constraints remain explicit.
   Proof outline: Stdlib Lra linear arithmetic, ring/field normalization;
   notably equal_weight_variance.
   Library discipline: Stdlib.Reals, Lra and Psatz (including ring and field
   tactics).
   Scope: No normal distribution, population correlation estimate, or
   measurement reliability is inferred from the algebra.
 *)
Theorem perfectly_correlated_variance :
  forall n, n <> 0 -> equal_weight_variance n 1 = 1.
Proof.
  intros n Hn; unfold equal_weight_variance; field; lra.
Qed.

(**
   [variance_strictly_positive] (theorem).
   Meaning: Establishes a finite-sample variance identity or bound, including
   all stated scaling assumptions.
   Formal conclusion: 0 < equal_weight_variance n rho.
   Hypotheses: Requires explicit nonzero/strict-positive denominator or scale
   where shown in the statement; all other constraints remain explicit.
   Proof outline: equational rewriting, application of already-proved lemmas,
   Stdlib Lra linear arithmetic, Stdlib Psatz nonlinear arithmetic; notably
   variance_alternative_form, Rdiv_lt_0_compat.
   Library discipline: Stdlib.Reals, Lra and Psatz (including ring and field
   tactics).
   Scope: No normal distribution, population correlation estimate, or
   measurement reliability is inferred from the algebra.
 *)
Theorem variance_strictly_positive :
  forall n rho,
    1 <= n -> 0 <= rho -> rho <= 1 ->
    0 < equal_weight_variance n rho.
Proof.
  intros n rho Hn Hr0 Hr1.
  rewrite variance_alternative_form by lra.
  apply Rdiv_lt_0_compat; nra.
Qed.

(**
   [variance_at_least_correlation] (theorem).
   Meaning: Establishes a finite-sample variance identity or bound, including
   all stated scaling assumptions.
   Formal conclusion: rho <= equal_weight_variance n rho.
   Hypotheses: Requires explicit nonzero/strict-positive denominator or scale
   where shown in the statement; all other constraints remain explicit.
   Proof outline: application of already-proved lemmas, Stdlib Lra linear
   arithmetic; notably equal_weight_variance., nonnegative_quotient.
   Library discipline: Stdlib.Reals, Lra and Psatz (including ring and field
   tactics).
   Scope: No normal distribution, population correlation estimate, or
   measurement reliability is inferred from the algebra.
 *)
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

(**
   [variance_at_most_one] (theorem).
   Meaning: Establishes a finite-sample variance identity or bound, including
   all stated scaling assumptions.
   Formal conclusion: equal_weight_variance n rho <= 1.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: application of already-proved lemmas, Stdlib Lra linear
   arithmetic, Stdlib Psatz nonlinear arithmetic, ring/field normalization;
   notably nonnegative_quotient, equal_weight_variance.
   Library discipline: Stdlib.Reals, Lra and Psatz (including ring and field
   tactics).
   Scope: No normal distribution, population correlation estimate, or
   measurement reliability is inferred from the algebra.
 *)
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

(**
   [variance_nondecreasing_in_correlation] (theorem).
   Meaning: Establishes a finite-sample variance identity or bound, including
   all stated scaling assumptions.
   Formal conclusion: equal_weight_variance n rho1 <= equal_weight_variance n
   rho2.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: application of already-proved lemmas, Stdlib Lra linear
   arithmetic, Stdlib Psatz nonlinear arithmetic, ring/field normalization;
   notably nonnegative_quotient, equal_weight_variance.
   Library discipline: Stdlib.Reals, Lra and Psatz (including ring and field
   tactics).
   Scope: No normal distribution, population correlation estimate, or
   measurement reliability is inferred from the algebra.
 *)
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

(**
   [variance_gap_to_limiting_correlation] (theorem).
   Meaning: Establishes a finite-sample variance identity or bound, including
   all stated scaling assumptions.
   Formal conclusion: equal_weight_variance n rho - rho = (1 - rho) / n.
   Hypotheses: Requires explicit nonzero/strict-positive denominator or scale
   where shown in the statement; all other constraints remain explicit.
   Proof outline: ring/field normalization; notably equal_weight_variance.
   Library discipline: Stdlib.Reals, Lra and Psatz (including ring and field
   tactics).
   Scope: No normal distribution, population correlation estimate, or
   measurement reliability is inferred from the algebra.
 *)
Theorem variance_gap_to_limiting_correlation :
  forall n rho, n <> 0 ->
    equal_weight_variance n rho - rho = (1 - rho) / n.
Proof.
  intros n rho Hn; unfold equal_weight_variance; ring.
Qed.

(**
   [iq_standardization_inversion] (theorem).
   Meaning: Justifies a score conversion or standardization formula by exact
   real arithmetic.
   Formal conclusion: mu + sigma * standardize x mu sigma = x.
   Hypotheses: Requires explicit nonzero/strict-positive denominator or scale
   where shown in the statement; all other constraints remain explicit.
   Proof outline: Stdlib Lra linear arithmetic, ring/field normalization;
   notably standardize.
   Library discipline: Stdlib.Reals, Lra and Psatz (including ring and field
   tactics).
   Scope: No normal distribution, population correlation estimate, or
   measurement reliability is inferred from the algebra.
 *)
Theorem iq_standardization_inversion :
  forall x mu sigma,
    sigma <> 0 ->
    mu + sigma * standardize x mu sigma = x.
Proof.
  intros x mu sigma Hs.
  unfold standardize; field; lra.
Qed.

(**
   [iq_report_standardization] (theorem).
   Meaning: Justifies a score conversion or standardization formula by exact
   real arithmetic.
   Formal conclusion: iq_report (standardize x 100 scale) scale = x.
   Hypotheses: Requires explicit nonzero/strict-positive denominator or scale
   where shown in the statement; all other constraints remain explicit.
   Proof outline: Stdlib Lra linear arithmetic, ring/field normalization;
   notably iq_report.
   Library discipline: Stdlib.Reals, Lra and Psatz (including ring and field
   tactics).
   Scope: No normal distribution, population correlation estimate, or
   measurement reliability is inferred from the algebra.
 *)
Theorem iq_report_standardization :
  forall x scale,
    scale <> 0 ->
    iq_report (standardize x 100 scale) scale = x.
Proof.
  intros x scale Hs.
  unfold iq_report, standardize; field; lra.
Qed.

(**
   [equal_sd_composite_scale] (theorem).
   Meaning: Justifies a score conversion or standardization formula by exact
   real arithmetic.
   Formal conclusion: iq_report (standardize average_iq 100 scale / divisor)
   scale = 100 + (average_iq - 100) / divisor.
   Hypotheses: Requires explicit nonzero/strict-positive denominator or scale
   where shown in the statement; all other constraints remain explicit.
   Proof outline: Stdlib Lra linear arithmetic, ring/field normalization;
   notably iq_report.
   Library discipline: Stdlib.Reals, Lra and Psatz (including ring and field
   tactics).
   Scope: No normal distribution, population correlation estimate, or
   measurement reliability is inferred from the algebra.
 *)
Theorem equal_sd_composite_scale :
  forall average_iq scale divisor,
    scale <> 0 -> divisor <> 0 ->
    iq_report (standardize average_iq 100 scale / divisor) scale =
       100 + (average_iq - 100) / divisor.
Proof.
  intros average_iq scale divisor Hs Hd.
  unfold iq_report, standardize; field; lra.
Qed.

(**
   [threshold_recovered_after_normalization] (theorem).
   Meaning: Justifies a score conversion or standardization formula by exact
   real arithmetic.
   Formal conclusion: (q * positive_sd) / positive_sd = q.
   Hypotheses: Requires explicit nonzero/strict-positive denominator or scale
   where shown in the statement; all other constraints remain explicit.
   Proof outline: Stdlib Lra linear arithmetic, ring/field normalization.
   Library discipline: Stdlib.Reals, Lra and Psatz (including ring and field
   tactics).
   Scope: No normal distribution, population correlation estimate, or
   measurement reliability is inferred from the algebra.
 *)
Theorem threshold_recovered_after_normalization :
  forall q positive_sd,
    positive_sd <> 0 ->
    (q * positive_sd) / positive_sd = q.
Proof.
  intros q sd Hsd; field; lra.
Qed.

(**
   [normalized_variance_is_one] (theorem).
   Meaning: Establishes a finite-sample variance identity or bound, including
   all stated scaling assumptions.
   Formal conclusion: variance / (sd * sd) = 1.
   Hypotheses: Requires explicit nonzero/strict-positive denominator or scale;
   unit-variance or stated moment hypotheses where shown in the statement; all
   other constraints remain explicit.
   Proof outline: Stdlib Psatz nonlinear arithmetic, ring/field normalization.
   Library discipline: Stdlib.Reals, Lra and Psatz (including ring and field
   tactics).
   Scope: No normal distribution, population correlation estimate, or
   measurement reliability is inferred from the algebra.
 *)
Theorem normalized_variance_is_one :
  forall variance sd,
    sd <> 0 ->
    sd * sd = variance ->
    variance / (sd * sd) = 1.
Proof.
  intros variance sd Hsd Heq; subst variance; field; nra.
Qed.

(**
   [standardized_160_sd15] (theorem).
   Meaning: Justifies a score conversion or standardization formula by exact
   real arithmetic.
   Formal conclusion: standardize 160 100 15 = 4.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: ring/field normalization; notably standardize.
   Library discipline: Stdlib.Reals, Lra and Psatz (including ring and field
   tactics).
   Scope: No normal distribution, population correlation estimate, or
   measurement reliability is inferred from the algebra.
 *)
Theorem standardized_160_sd15 :
  standardize 160 100 15 = 4.
Proof.
  unfold standardize; field.
Qed.

(**
   [standardized_160_sd16] (theorem).
   Meaning: Justifies a score conversion or standardization formula by exact
   real arithmetic.
   Formal conclusion: standardize 160 100 16 = 15 / 4.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: ring/field normalization; notably standardize.
   Library discipline: Stdlib.Reals, Lra and Psatz (including ring and field
   tactics).
   Scope: No normal distribution, population correlation estimate, or
   measurement reliability is inferred from the algebra.
 *)
Theorem standardized_160_sd16 :
  standardize 160 100 16 = 15 / 4.
Proof.
  unfold standardize; field.
Qed.

(**
   [latent_reliability_plus_posterior_variance] (theorem).
   Meaning: Establishes a finite-sample variance identity or bound, including
   all stated scaling assumptions.
   Formal conclusion: latent_reliability n rho + latent_posterior_variance n
   rho = 1.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: Stdlib Psatz nonlinear arithmetic, ring/field normalization;
   notably latent_reliability.
   Library discipline: Stdlib.Reals, Lra and Psatz (including ring and field
   tactics).
   Scope: No normal distribution, population correlation estimate, or
   measurement reliability is inferred from the algebra.
 *)
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

(**
   [latent_reliability_nonnegative] (theorem).
   Meaning: Relates variance, square root, correlation or reliability
   parameters under the displayed numerical constraints.
   Formal conclusion: 0 <= latent_reliability n rho.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: application of already-proved lemmas, Stdlib Psatz nonlinear
   arithmetic; notably latent_reliability., nonnegative_quotient.
   Library discipline: Stdlib.Reals, Lra and Psatz (including ring and field
   tactics).
   Scope: No normal distribution, population correlation estimate, or
   measurement reliability is inferred from the algebra.
 *)
Theorem latent_reliability_nonnegative :
  forall n rho,
    1 <= n -> 0 <= rho ->
    0 <= latent_reliability n rho.
Proof.
  intros n rho Hn Hr.
  unfold latent_reliability.
  apply nonnegative_quotient; nra.
Qed.

(**
   [latent_posterior_variance_nonnegative] (theorem).
   Meaning: Establishes a finite-sample variance identity or bound, including
   all stated scaling assumptions.
   Formal conclusion: 0 <= latent_posterior_variance n rho.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: application of already-proved lemmas, Stdlib Psatz nonlinear
   arithmetic; notably latent_posterior_variance., nonnegative_quotient.
   Library discipline: Stdlib.Reals, Lra and Psatz (including ring and field
   tactics).
   Scope: No normal distribution, population correlation estimate, or
   measurement reliability is inferred from the algebra.
 *)
Theorem latent_posterior_variance_nonnegative :
  forall n rho,
    1 <= n -> 0 <= rho -> rho <= 1 ->
    0 <= latent_posterior_variance n rho.
Proof.
  intros n rho Hn Hr0 Hr1.
  unfold latent_posterior_variance.
  apply nonnegative_quotient; nra.
Qed.

(**
   [latent_reliability_at_most_one] (theorem).
   Meaning: Relates variance, square root, correlation or reliability
   parameters under the displayed numerical constraints.
   Formal conclusion: latent_reliability n rho <= 1.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: application of already-proved lemmas, Stdlib Lra linear
   arithmetic; notably latent_reliability_plus_posterior_variance,
   latent_posterior_variance_nonnegative.
   Library discipline: Stdlib.Reals, Lra and Psatz (including ring and field
   tactics).
   Scope: No normal distribution, population correlation estimate, or
   measurement reliability is inferred from the algebra.
 *)
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

(**
   [latent_reliability_for_one_test] (theorem).
   Meaning: Relates variance, square root, correlation or reliability
   parameters under the displayed numerical constraints.
   Formal conclusion: forall rho, latent_reliability 1 rho = rho.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: ring/field normalization; notably latent_reliability.
   Library discipline: Stdlib.Reals, Lra and Psatz (including ring and field
   tactics).
   Scope: No normal distribution, population correlation estimate, or
   measurement reliability is inferred from the algebra.
 *)
Theorem latent_reliability_for_one_test :
  forall rho, latent_reliability 1 rho = rho.
Proof.
  intro rho; unfold latent_reliability; field.
Qed.

(**
   [latent_reliability_at_zero] (theorem).
   Meaning: Relates variance, square root, correlation or reliability
   parameters under the displayed numerical constraints.
   Formal conclusion: forall n, latent_reliability n 0 = 0.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: ring/field normalization; notably latent_reliability.
   Library discipline: Stdlib.Reals, Lra and Psatz (including ring and field
   tactics).
   Scope: No normal distribution, population correlation estimate, or
   measurement reliability is inferred from the algebra.
 *)
Theorem latent_reliability_at_zero :
  forall n, latent_reliability n 0 = 0.
Proof.
  intro n; unfold latent_reliability; field.
Qed.

(**
   [latent_variance_at_zero] (theorem).
   Meaning: Establishes a finite-sample variance identity or bound, including
   all stated scaling assumptions.
   Formal conclusion: forall n, latent_posterior_variance n 0 = 1.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: ring/field normalization; notably latent_posterior_variance.
   Library discipline: Stdlib.Reals, Lra and Psatz (including ring and field
   tactics).
   Scope: No normal distribution, population correlation estimate, or
   measurement reliability is inferred from the algebra.
 *)
Theorem latent_variance_at_zero :
  forall n, latent_posterior_variance n 0 = 1.
Proof.
  intro n; unfold latent_posterior_variance; field.
Qed.

(**
   [latent_variance_at_perfect_correlation] (theorem).
   Meaning: Establishes a finite-sample variance identity or bound, including
   all stated scaling assumptions.
   Formal conclusion: latent_posterior_variance n 1 = 0.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: Stdlib Lra linear arithmetic, ring/field normalization;
   notably latent_posterior_variance.
   Library discipline: Stdlib.Reals, Lra and Psatz (including ring and field
   tactics).
   Scope: No normal distribution, population correlation estimate, or
   measurement reliability is inferred from the algebra.
 *)
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

(**
   [variance_decreases_with_test_count] (theorem).
   Meaning: Establishes a finite-sample variance identity or bound, including
   all stated scaling assumptions.
   Formal conclusion: equal_weight_variance n2 rho <= equal_weight_variance n1
   rho.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: application of already-proved lemmas, Stdlib Lra linear
   arithmetic, Stdlib Psatz nonlinear arithmetic, ring/field normalization;
   notably nonnegative_quotient, equal_weight_variance.
   Library discipline: Stdlib.Reals, Lra and Psatz (including ring and field
   tactics).
   Scope: No normal distribution, population correlation estimate, or
   measurement reliability is inferred from the algebra.
 *)
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

(**
   [variance_strictly_decreases_with_test_count] (theorem).
   Meaning: Establishes a finite-sample variance identity or bound, including
   all stated scaling assumptions.
   Formal conclusion: equal_weight_variance n2 rho < equal_weight_variance n1
   rho.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: application of already-proved lemmas, Stdlib Lra linear
   arithmetic, Stdlib Psatz nonlinear arithmetic, ring/field normalization;
   notably Rdiv_lt_0_compat, equal_weight_variance.
   Library discipline: Stdlib.Reals, Lra and Psatz (including ring and field
   tactics).
   Scope: No normal distribution, population correlation estimate, or
   measurement reliability is inferred from the algebra.
 *)
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

(**
   [variance_is_affine_in_correlation] (theorem).
   Meaning: Establishes a finite-sample variance identity or bound, including
   all stated scaling assumptions.
   Formal conclusion: equal_weight_variance n rho = 1 / n + ((n - 1) / n) *
   rho.
   Hypotheses: Requires explicit nonzero/strict-positive denominator or scale
   where shown in the statement; all other constraints remain explicit.
   Proof outline: Stdlib Lra linear arithmetic, ring/field normalization;
   notably equal_weight_variance..
   Library discipline: Stdlib.Reals, Lra and Psatz (including ring and field
   tactics).
   Scope: No normal distribution, population correlation estimate, or
   measurement reliability is inferred from the algebra.
 *)
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

(**
   [variance_correlation_sensitivity] (theorem).
   Meaning: Establishes a finite-sample variance identity or bound, including
   all stated scaling assumptions.
   Formal conclusion: equal_weight_variance n rho2 - equal_weight_variance n
   rho1 = ((n - 1) / n) * (rho2 - rho1).
   Hypotheses: Requires explicit nonzero/strict-positive denominator or scale
   where shown in the statement; all other constraints remain explicit.
   Proof outline: Stdlib Lra linear arithmetic, ring/field normalization;
   notably equal_weight_variance..
   Library discipline: Stdlib.Reals, Lra and Psatz (including ring and field
   tactics).
   Scope: No normal distribution, population correlation estimate, or
   measurement reliability is inferred from the algebra.
 *)
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

(**
   [variance_of_two_equicorrelated_tests] (theorem).
   Meaning: Establishes a finite-sample variance identity or bound, including
   all stated scaling assumptions.
   Formal conclusion: forall rho, equal_weight_variance 2 rho = (1 + rho) / 2.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: ring/field normalization; notably equal_weight_variance.
   Library discipline: Stdlib.Reals, Lra and Psatz (including ring and field
   tactics).
   Scope: No normal distribution, population correlation estimate, or
   measurement reliability is inferred from the algebra.
 *)
Theorem variance_of_two_equicorrelated_tests :
  forall rho, equal_weight_variance 2 rho = (1 + rho) / 2.
Proof.
  intro rho; unfold equal_weight_variance; field.
Qed.

(**
   [variance_of_three_equicorrelated_tests] (theorem).
   Meaning: Establishes a finite-sample variance identity or bound, including
   all stated scaling assumptions.
   Formal conclusion: forall rho, equal_weight_variance 3 rho = (1 + 2 * rho) /
   3.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: ring/field normalization; notably equal_weight_variance.
   Library discipline: Stdlib.Reals, Lra and Psatz (including ring and field
   tactics).
   Scope: No normal distribution, population correlation estimate, or
   measurement reliability is inferred from the algebra.
 *)
Theorem variance_of_three_equicorrelated_tests :
  forall rho, equal_weight_variance 3 rho = (1 + 2 * rho) / 3.
Proof.
  intro rho; unfold equal_weight_variance; field.
Qed.

(**
   [latent_variance_denominator_positive] (theorem).
   Meaning: Establishes a finite-sample variance identity or bound, including
   all stated scaling assumptions.
   Formal conclusion: 0 < 1 + (n - 1) * rho.
   Hypotheses: Requires explicit nonzero/strict-positive denominator or scale
   where shown in the statement; all other constraints remain explicit.
   Proof outline: Stdlib Psatz nonlinear arithmetic.
   Library discipline: Stdlib.Reals, Lra and Psatz (including ring and field
   tactics).
   Scope: No normal distribution, population correlation estimate, or
   measurement reliability is inferred from the algebra.
 *)
Theorem latent_variance_denominator_positive :
  forall n rho,
    1 <= n -> 0 <= rho ->
    0 < 1 + (n - 1) * rho.
Proof.
  intros n rho Hn Hr; nra.
Qed.

(**
   [latent_variance_decreases_with_test_count] (theorem).
   Meaning: Establishes a finite-sample variance identity or bound, including
   all stated scaling assumptions.
   Formal conclusion: latent_posterior_variance n2 rho <=
   latent_posterior_variance n1 rho.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: application of already-proved lemmas, Stdlib Lra linear
   arithmetic, Stdlib Psatz nonlinear arithmetic, ring/field normalization;
   notably latent_variance_denominator_positive, nonnegative_quotient.,
   Rmult_le_pos..
   Library discipline: Stdlib.Reals, Lra and Psatz (including ring and field
   tactics).
   Scope: No normal distribution, population correlation estimate, or
   measurement reliability is inferred from the algebra.
 *)
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

(**
   [latent_reliability_increases_with_test_count] (theorem).
   Meaning: Relates variance, square root, correlation or reliability
   parameters under the displayed numerical constraints.
   Formal conclusion: latent_reliability n1 rho <= latent_reliability n2 rho.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: application of already-proved lemmas, Stdlib Lra linear
   arithmetic; notably latent_reliability_plus_posterior_variance,
   latent_variance_decreases_with_test_count.
   Library discipline: Stdlib.Reals, Lra and Psatz (including ring and field
   tactics).
   Scope: No normal distribution, population correlation estimate, or
   measurement reliability is inferred from the algebra.
 *)
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

(**
   [doubling_battery_halves_variance_excess] (theorem).
   Meaning: Establishes a finite-sample variance identity or bound, including
   all stated scaling assumptions.
   Formal conclusion: equal_weight_variance (2 * n) rho - rho =
   (equal_weight_variance n rho - rho) / 2.
   Hypotheses: Requires explicit nonzero/strict-positive denominator or scale
   where shown in the statement; all other constraints remain explicit.
   Proof outline: Stdlib Lra linear arithmetic, ring/field normalization;
   notably equal_weight_variance..
   Library discipline: Stdlib.Reals, Lra and Psatz (including ring and field
   tactics).
   Scope: No normal distribution, population correlation estimate, or
   measurement reliability is inferred from the algebra.
 *)
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

(**
   [nonnegative_correlation_variance_at_least_independent] (theorem).
   Meaning: Establishes a finite-sample variance identity or bound, including
   all stated scaling assumptions.
   Formal conclusion: 1 / n <= equal_weight_variance n rho.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: application of already-proved lemmas, Stdlib Lra linear
   arithmetic, Stdlib Psatz nonlinear arithmetic, ring/field normalization;
   notably equal_weight_variance, nonnegative_quotient.
   Library discipline: Stdlib.Reals, Lra and Psatz (including ring and field
   tactics).
   Scope: No normal distribution, population correlation estimate, or
   measurement reliability is inferred from the algebra.
 *)
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

(**
   [variance_excess_bound_by_inverse_battery_size] (theorem).
   Meaning: Establishes a finite-sample variance identity or bound, including
   all stated scaling assumptions.
   Formal conclusion: 0 <= equal_weight_variance n rho - rho /\
   equal_weight_variance n rho - rho <= 1 / n.
   Hypotheses: Requires explicit nonzero/strict-positive denominator or scale
   where shown in the statement; all other constraints remain explicit.
   Proof outline: equational rewriting, application of already-proved lemmas,
   Stdlib Lra linear arithmetic, ring/field normalization; notably
   variance_gap_to_limiting_correlation, nonnegative_quotient.
   Library discipline: Stdlib.Reals, Lra and Psatz (including ring and field
   tactics).
   Scope: No normal distribution, population correlation estimate, or
   measurement reliability is inferred from the algebra.
 *)
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

(**
   [latent_reliability_times_composite_variance] (theorem).
   Meaning: Establishes a finite-sample variance identity or bound, including
   all stated scaling assumptions.
   Formal conclusion: latent_reliability n rho * equal_weight_variance n rho =
   rho.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: application of already-proved lemmas, Stdlib Psatz nonlinear
   arithmetic, ring/field normalization; notably
   latent_variance_denominator_positive, latent_reliability.
   Library discipline: Stdlib.Reals, Lra and Psatz (including ring and field
   tactics).
   Scope: No normal distribution, population correlation estimate, or
   measurement reliability is inferred from the algebra.
 *)
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

(**
   [latent_posterior_times_composite_variance] (theorem).
   Meaning: Establishes a finite-sample variance identity or bound, including
   all stated scaling assumptions.
   Formal conclusion: latent_posterior_variance n rho * equal_weight_variance n
   rho = (1 - rho) / n.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: application of already-proved lemmas, Stdlib Psatz nonlinear
   arithmetic, ring/field normalization; notably
   latent_variance_denominator_positive, latent_posterior_variance.
   Library discipline: Stdlib.Reals, Lra and Psatz (including ring and field
   tactics).
   Scope: No normal distribution, population correlation estimate, or
   measurement reliability is inferred from the algebra.
 *)
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

(**
   [composite_standard_deviation] (definition).
   Meaning: Justifies a score conversion or standardization formula by exact
   real arithmetic.
   Formal construction: (n rho : R) : R := sqrt (equal_weight_variance n rho).
   Hypotheses: A definition; its parameters and fields appear in the signature,
   with no silent statistical assumptions.
   Implementation: application of already-proved lemmas; notably
   composite_standard_deviation., sqrt_pos..
   Library discipline: Stdlib.Reals, Lra and Psatz (including ring and field
   tactics).
   Scope: No normal distribution, population correlation estimate, or
   measurement reliability is inferred from the algebra.
 *)
Definition composite_standard_deviation (n rho : R) : R :=
  sqrt (equal_weight_variance n rho).

(**
   [composite_standard_deviation_nonnegative] (theorem).
   Meaning: Justifies a score conversion or standardization formula by exact
   real arithmetic.
   Formal conclusion: forall n rho, 0 <= composite_standard_deviation n rho.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: application of already-proved lemmas; notably
   composite_standard_deviation., sqrt_pos..
   Library discipline: Stdlib.Reals, Lra and Psatz (including ring and field
   tactics).
   Scope: No normal distribution, population correlation estimate, or
   measurement reliability is inferred from the algebra.
 *)
Theorem composite_standard_deviation_nonnegative :
  forall n rho, 0 <= composite_standard_deviation n rho.
Proof.
  intros n rho.
  unfold composite_standard_deviation.
  apply sqrt_pos.
Qed.

(**
   [composite_standard_deviation_squared] (theorem).
   Meaning: Justifies a score conversion or standardization formula by exact
   real arithmetic.
   Formal conclusion: composite_standard_deviation n rho *
   composite_standard_deviation n rho = equal_weight_variance n rho.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: application of already-proved lemmas, Stdlib Lra linear
   arithmetic; notably composite_standard_deviation., sqrt_sqrt.,
   variance_strictly_positive.
   Library discipline: Stdlib.Reals, Lra and Psatz (including ring and field
   tactics).
   Scope: No normal distribution, population correlation estimate, or
   measurement reliability is inferred from the algebra.
 *)
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

(**
   [composite_standard_deviation_at_zero_correlation] (theorem).
   Meaning: Justifies a score conversion or standardization formula by exact
   real arithmetic.
   Formal conclusion: composite_standard_deviation n 0 = sqrt (1 / n).
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: equational rewriting, Stdlib Lra linear arithmetic,
   definitional computation; notably composite_standard_deviation.,
   independent_tests_variance.
   Library discipline: Stdlib.Reals, Lra and Psatz (including ring and field
   tactics).
   Scope: No normal distribution, population correlation estimate, or
   measurement reliability is inferred from the algebra.
 *)
Theorem composite_standard_deviation_at_zero_correlation :
  forall n, 1 <= n ->
    composite_standard_deviation n 0 = sqrt (1 / n).
Proof.
  intros n Hn.
  unfold composite_standard_deviation.
  rewrite independent_tests_variance by lra.
  reflexivity.
Qed.

(**
   [composite_standard_deviation_at_perfect_correlation] (theorem).
   Meaning: Justifies a score conversion or standardization formula by exact
   real arithmetic.
   Formal conclusion: composite_standard_deviation n 1 = 1.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: equational rewriting, application of already-proved lemmas,
   Stdlib Lra linear arithmetic; notably composite_standard_deviation.,
   perfectly_correlated_variance, sqrt_1..
   Library discipline: Stdlib.Reals, Lra and Psatz (including ring and field
   tactics).
   Scope: No normal distribution, population correlation estimate, or
   measurement reliability is inferred from the algebra.
 *)
Theorem composite_standard_deviation_at_perfect_correlation :
  forall n, 1 <= n ->
    composite_standard_deviation n 1 = 1.
Proof.
  intros n Hn.
  unfold composite_standard_deviation.
  rewrite perfectly_correlated_variance by lra.
  apply sqrt_1.
Qed.

(**
   [composite_standard_deviation_nondecreasing_in_correlation] (theorem).
   Meaning: Justifies a score conversion or standardization formula by exact
   real arithmetic.
   Formal conclusion: composite_standard_deviation n rho1 <=
   composite_standard_deviation n rho2.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: application of already-proved lemmas, Stdlib Lra linear
   arithmetic; notably variance_strictly_positive,
   composite_standard_deviation., sqrt_le_1.
   Library discipline: Stdlib.Reals, Lra and Psatz (including ring and field
   tactics).
   Scope: No normal distribution, population correlation estimate, or
   measurement reliability is inferred from the algebra.
 *)
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

(**
   [composite_standard_deviation_nonincreasing_in_test_count] (theorem).
   Meaning: Justifies a score conversion or standardization formula by exact
   real arithmetic.
   Formal conclusion: composite_standard_deviation n2 rho <=
   composite_standard_deviation n1 rho.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: application of already-proved lemmas, Stdlib Lra linear
   arithmetic; notably variance_strictly_positive,
   composite_standard_deviation., sqrt_le_1.
   Library discipline: Stdlib.Reals, Lra and Psatz (including ring and field
   tactics).
   Scope: No normal distribution, population correlation estimate, or
   measurement reliability is inferred from the algebra.
 *)
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

(**
   [composite_standard_deviation_at_most_one] (theorem).
   Meaning: Justifies a score conversion or standardization formula by exact
   real arithmetic.
   Formal conclusion: composite_standard_deviation n rho <= 1.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: equational rewriting, application of already-proved lemmas,
   Stdlib Lra linear arithmetic; notably composite_standard_deviation.,
   sqrt_le_1., variance_strictly_positive.
   Library discipline: Stdlib.Reals, Lra and Psatz (including ring and field
   tactics).
   Scope: No normal distribution, population correlation estimate, or
   measurement reliability is inferred from the algebra.
 *)
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

(**
   [composite_standard_deviation_at_least_sqrt_correlation] (theorem).
   Meaning: Justifies a score conversion or standardization formula by exact
   real arithmetic.
   Formal conclusion: sqrt rho <= composite_standard_deviation n rho.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: application of already-proved lemmas, Stdlib Lra linear
   arithmetic; notably composite_standard_deviation., sqrt_le_1.,
   variance_strictly_positive.
   Library discipline: Stdlib.Reals, Lra and Psatz (including ring and field
   tactics).
   Scope: No normal distribution, population correlation estimate, or
   measurement reliability is inferred from the algebra.
 *)
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

(**
   [composite_standard_deviation_positive] (theorem).
   Meaning: Justifies a score conversion or standardization formula by exact
   real arithmetic.
   Formal conclusion: 0 < composite_standard_deviation n rho.
   Hypotheses: Requires explicit nonzero/strict-positive denominator or scale
   where shown in the statement; all other constraints remain explicit.
   Proof outline: application of already-proved lemmas; notably
   composite_standard_deviation., sqrt_lt_R0., variance_strictly_positive.
   Library discipline: Stdlib.Reals, Lra and Psatz (including ring and field
   tactics).
   Scope: No normal distribution, population correlation estimate, or
   measurement reliability is inferred from the algebra.
 *)
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

(**
   [composite_standard_deviation_strictly_decreases_with_test_count] (theorem).
   Meaning: Justifies a score conversion or standardization formula by exact
   real arithmetic.
   Formal conclusion: composite_standard_deviation n2 rho <
   composite_standard_deviation n1 rho.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: application of already-proved lemmas, Stdlib Lra linear
   arithmetic; notably composite_standard_deviation., sqrt_lt_1.,
   variance_strictly_positive.
   Library discipline: Stdlib.Reals, Lra and Psatz (including ring and field
   tactics).
   Scope: No normal distribution, population correlation estimate, or
   measurement reliability is inferred from the algebra.
 *)
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

(**
   [composite_standard_deviation_strictly_increases_in_correlation] (theorem).
   Meaning: Justifies a score conversion or standardization formula by exact
   real arithmetic.
   Formal conclusion: composite_standard_deviation n rho1 <
   composite_standard_deviation n rho2.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: equational rewriting, application of already-proved lemmas,
   Stdlib Lra linear arithmetic, Stdlib Psatz nonlinear arithmetic; notably
   Rdiv_lt_0_compat, variance_correlation_sensitivity,
   composite_standard_deviation..
   Library discipline: Stdlib.Reals, Lra and Psatz (including ring and field
   tactics).
   Scope: No normal distribution, population correlation estimate, or
   measurement reliability is inferred from the algebra.
 *)
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

(**
   [composite_standard_deviation_at_least_independent_baseline] (theorem).
   Meaning: Makes an event-independence or conditional-probability relationship
   explicit, including necessary denominators.
   Formal conclusion: sqrt (1 / n) <= composite_standard_deviation n rho.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: application of already-proved lemmas, Stdlib Lra linear
   arithmetic; notably nonnegative_quotient, variance_strictly_positive,
   composite_standard_deviation..
   Library discipline: Stdlib.Reals, Lra and Psatz (including ring and field
   tactics).
   Scope: No normal distribution, population correlation estimate, or
   measurement reliability is inferred from the algebra.
 *)
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

(**
   [composite_standard_deviation_strictly_below_one] (theorem).
   Meaning: Justifies a score conversion or standardization formula by exact
   real arithmetic.
   Formal conclusion: composite_standard_deviation n rho < 1.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: equational rewriting, application of already-proved lemmas,
   Stdlib Lra linear arithmetic, Stdlib Psatz nonlinear arithmetic, ring/field
   normalization; notably Rdiv_lt_0_compat, equal_weight_variance,
   composite_standard_deviation..
   Library discipline: Stdlib.Reals, Lra and Psatz (including ring and field
   tactics).
   Scope: No normal distribution, population correlation estimate, or
   measurement reliability is inferred from the algebra.
 *)
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

(**
   [standardized_affine_cutoff_round_trip] (theorem).
   Meaning: Justifies a score conversion or standardization formula by exact
   real arithmetic.
   Formal conclusion: standardize (mu + sigma * z) mu sigma = z.
   Hypotheses: Requires explicit nonzero/strict-positive denominator or scale
   where shown in the statement; all other constraints remain explicit.
   Proof outline: Stdlib Lra linear arithmetic, ring/field normalization;
   notably standardize..
   Library discipline: Stdlib.Reals, Lra and Psatz (including ring and field
   tactics).
   Scope: No normal distribution, population correlation estimate, or
   measurement reliability is inferred from the algebra.
 *)
Theorem standardized_affine_cutoff_round_trip :
  forall z mu sigma,
    0 < sigma ->
    standardize (mu + sigma * z) mu sigma = z.
Proof.
  intros z mu sigma Hsigma.
  unfold standardize.
  field; lra.
Qed.

(**
   [positive_scale_preserves_cutoff_order] (theorem).
   Meaning: Justifies a score conversion or standardization formula by exact
   real arithmetic.
   Formal conclusion: mu + sigma * z1 <= mu + sigma * z2.
   Hypotheses: Requires explicit nonzero/strict-positive denominator or scale
   where shown in the statement; all other constraints remain explicit.
   Proof outline: application of already-proved lemmas, Stdlib Lra linear
   arithmetic; notably Rplus_le_compat_l., Rmult_le_compat_l.
   Library discipline: Stdlib.Reals, Lra and Psatz (including ring and field
   tactics).
   Scope: No normal distribution, population correlation estimate, or
   measurement reliability is inferred from the algebra.
 *)
Theorem positive_scale_preserves_cutoff_order :
  forall z1 z2 mu sigma,
    0 < sigma -> z1 <= z2 ->
    mu + sigma * z1 <= mu + sigma * z2.
Proof.
  intros z1 z2 mu sigma Hsigma Horder.
  apply Rplus_le_compat_l.
  apply Rmult_le_compat_l; [lra | exact Horder].
Qed.

(**
   [composite_standardized_cutoff_round_trip] (theorem).
   Meaning: Justifies a score conversion or standardization formula by exact
   real arithmetic.
   Formal conclusion: standardize (mu + (scale * composite_standard_deviation n
   rho) * z) mu (scale * composite_standard_deviation n rho) = z.
   Hypotheses: Requires explicit nonzero/strict-positive denominator or scale
   where shown in the statement; all other constraints remain explicit.
   Proof outline: application of already-proved lemmas, Stdlib Psatz nonlinear
   arithmetic; notably composite_standard_deviation_positive,
   standardized_affine_cutoff_round_trip.
   Library discipline: Stdlib.Reals, Lra and Psatz (including ring and field
   tactics).
   Scope: No normal distribution, population correlation estimate, or
   measurement reliability is inferred from the algebra.
 *)
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

(**
   [positive_cutoff_nonincreasing_with_test_count] (theorem).
   Meaning: Gives a precise computational or algebraic interpretation of the
   named construction or assertion.
   Formal conclusion: mu + (scale * composite_standard_deviation n2 rho) * z <=
   mu + (scale * composite_standard_deviation n1 rho) * z.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: application of already-proved lemmas; notably
   composite_standard_deviation_nonincreasing_in_test_count,
   Rplus_le_compat_l., Rmult_le_compat_r.
   Library discipline: Stdlib.Reals, Lra and Psatz (including ring and field
   tactics).
   Scope: No normal distribution, population correlation estimate, or
   measurement reliability is inferred from the algebra.
 *)
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


(* Reporting-scale order facts reuse the Stdlib ordered-field lemmas.
   Unlike a probabilistic tail statement, these require only positive
   scaling and the established affine reporting definitions. *)

(**
   [standardize_preserves_order] (theorem).
   Meaning: Justifies a score conversion or standardization formula by exact
   real arithmetic.
   Formal conclusion: standardize x mu sigma <= standardize y mu sigma.
   Hypotheses: Requires explicit nonzero/strict-positive denominator or scale
   where shown in the statement; all other constraints remain explicit.
   Proof outline: application of already-proved lemmas, Stdlib Lra linear
   arithmetic; notably standardize, Rmult_le_compat_r., Hsigma..
   Library discipline: Stdlib.Reals, Lra and Psatz (including ring and field
   tactics).
   Scope: No normal distribution, population correlation estimate, or
   measurement reliability is inferred from the algebra.
 *)
Theorem standardize_preserves_order :
  forall x y mu sigma,
    0 < sigma -> x <= y ->
    standardize x mu sigma <= standardize y mu sigma.
Proof.
  intros x y mu sigma Hsigma Horder.
  unfold standardize, Rdiv.
  apply Rmult_le_compat_r.
  - apply Rlt_le, Rinv_0_lt_compat; exact Hsigma.
  - lra.
Qed.

(**
   [iq_report_preserves_order] (theorem).
   Meaning: Justifies a score conversion or standardization formula by exact
   real arithmetic.
   Formal conclusion: iq_report x scale <= iq_report y scale.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: application of already-proved lemmas; notably iq_report.,
   Rplus_le_compat_l., Rmult_le_compat_l.
   Library discipline: Stdlib.Reals, Lra and Psatz (including ring and field
   tactics).
   Scope: No normal distribution, population correlation estimate, or
   measurement reliability is inferred from the algebra.
 *)
Theorem iq_report_preserves_order :
  forall x y scale,
    0 <= scale -> x <= y ->
    iq_report x scale <= iq_report y scale.
Proof.
  intros x y scale Hscale Horder.
  unfold iq_report.
  apply Rplus_le_compat_l.
  apply Rmult_le_compat_l; assumption.
Qed.

(**
   [standardized_iq_reporting_preserves_order] (theorem).
   Meaning: Justifies a score conversion or standardization formula by exact
   real arithmetic.
   Formal conclusion: iq_report (standardize x mu sigma) scale <= iq_report
   (standardize y mu sigma) scale.
   Hypotheses: Requires explicit nonzero/strict-positive denominator or scale
   where shown in the statement; all other constraints remain explicit.
   Proof outline: application of already-proved lemmas; notably
   iq_report_preserves_order., Hscale., standardize_preserves_order.
   Library discipline: Stdlib.Reals, Lra and Psatz (including ring and field
   tactics).
   Scope: No normal distribution, population correlation estimate, or
   measurement reliability is inferred from the algebra.
 *)
Theorem standardized_iq_reporting_preserves_order :
  forall x y mu sigma scale,
    0 < sigma -> 0 <= scale -> x <= y ->
    iq_report (standardize x mu sigma) scale <=
      iq_report (standardize y mu sigma) scale.
Proof.
  intros x y mu sigma scale Hsigma Hscale Horder.
  apply iq_report_preserves_order.
  - exact Hscale.
  - apply standardize_preserves_order; assumption.
Qed.


(* Quantitative epsilon bounds do not require a separate asymptotic-limit
   infrastructure: they follow from the exact fixed-rho variance gap and
   standard ordered-field identities.  The parameter rho is held fixed. *)

(**
   [fixed_correlation_variance_epsilon_bound] (theorem).
   Meaning: Establishes a finite-sample variance identity or bound, including
   all stated scaling assumptions.
   Formal conclusion: 0 <= equal_weight_variance n rho - rho /\
   equal_weight_variance n rho - rho < eps.
   Hypotheses: Requires explicit nonzero/strict-positive denominator or scale
   where shown in the statement; all other constraints remain explicit.
   Proof outline: equational rewriting, application of already-proved lemmas,
   Stdlib Lra linear arithmetic, ring/field normalization; notably
   variance_gap_to_limiting_correlation, Rinv_0_lt_compat, Rmult_lt_compat_r.
   Library discipline: Stdlib.Reals, Lra and Psatz (including ring and field
   tactics).
   Scope: No normal distribution, population correlation estimate, or
   measurement reliability is inferred from the algebra.
 *)
Theorem fixed_correlation_variance_epsilon_bound :
  forall n rho eps,
    0 < n -> rho <= 1 -> 0 < eps ->
    1 - rho < eps * n ->
    0 <= equal_weight_variance n rho - rho /\
      equal_weight_variance n rho - rho < eps.
Proof.
  intros n rho eps Hn Hr Heps Hthreshold.
  rewrite variance_gap_to_limiting_correlation by lra.
  assert (Hinv : 0 < / n).
  { apply Rinv_0_lt_compat; exact Hn. }
  assert (Hscaled :
    (1 - rho) * / n < (eps * n) * / n).
  { apply Rmult_lt_compat_r; assumption. }
  replace ((eps * n) * / n) with eps in Hscaled.
  2: { field; lra. }
  unfold Rdiv; split.
  - apply Rmult_le_pos; lra.
  - exact Hscaled.
Qed.

(**
   [fixed_correlation_variance_epsilon_after_threshold] (theorem).
   Meaning: Establishes a finite-sample variance identity or bound, including
   all stated scaling assumptions.
   Formal conclusion: 0 <= equal_weight_variance n rho - rho /\
   equal_weight_variance n rho - rho < eps.
   Hypotheses: Requires explicit nonzero/strict-positive denominator or scale
   where shown in the statement; all other constraints remain explicit.
   Proof outline: application of already-proved lemmas, Stdlib Lra linear
   arithmetic, Stdlib Psatz nonlinear arithmetic, ring/field normalization;
   notably nonnegative_quotient, Rmult_lt_compat_r,
   fixed_correlation_variance_epsilon_bound.
   Library discipline: Stdlib.Reals, Lra and Psatz (including ring and field
   tactics).
   Scope: No normal distribution, population correlation estimate, or
   measurement reliability is inferred from the algebra.
 *)
Theorem fixed_correlation_variance_epsilon_after_threshold :
  forall n rho eps,
    rho <= 1 -> 0 < eps ->
    (1 - rho) / eps < n ->
    0 <= equal_weight_variance n rho - rho /\
      equal_weight_variance n rho - rho < eps.
Proof.
  intros n rho eps Hr Heps Hcount.
  assert (Hratio_nonnegative : 0 <= (1 - rho) / eps).
  { apply nonnegative_quotient; lra. }
  assert (Hn : 0 < n) by lra.
  assert (Hthreshold :
    (1 - rho) < eps * n).
  { assert (Hm :
      ((1 - rho) / eps) * eps < n * eps).
    { apply Rmult_lt_compat_r; assumption. }
    replace (((1 - rho) / eps) * eps)
      with (1 - rho) in Hm by (field; lra).
    nra. }
  apply fixed_correlation_variance_epsilon_bound; assumption.
Qed.


(* Positive reporting cutoffs inherit the finite-battery standard-deviation
   ordering from existing theorems.  The only arithmetic is the standard
   ordered-field compatibility of positive scalar multiplication. *)

(**
   [positive_cutoff_nondecreasing_in_correlation] (theorem).
   Meaning: Relates variance, square root, correlation or reliability
   parameters under the displayed numerical constraints.
   Formal conclusion: mu + (scale * composite_standard_deviation n rho1) * z <=
   mu + (scale * composite_standard_deviation n rho2) * z.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: application of already-proved lemmas; notably
   composite_standard_deviation_nondecreasing_in_correlation,
   Rplus_le_compat_l., Rmult_le_compat_r.
   Library discipline: Stdlib.Reals, Lra and Psatz (including ring and field
   tactics).
   Scope: No normal distribution, population correlation estimate, or
   measurement reliability is inferred from the algebra.
 *)
Theorem positive_cutoff_nondecreasing_in_correlation :
  forall n rho1 rho2 mu scale z,
    1 <= n -> 0 <= rho1 -> rho1 <= rho2 -> rho2 <= 1 ->
    0 <= scale -> 0 <= z ->
    mu + (scale * composite_standard_deviation n rho1) * z <=
      mu + (scale * composite_standard_deviation n rho2) * z.
Proof.
  intros n rho1 rho2 mu scale z Hn Hr0 Horder Hr1 Hscale Hz.
  pose proof
    (composite_standard_deviation_nondecreasing_in_correlation
      n rho1 rho2 Hn Hr0 Horder Hr1) as Hsd.
  apply Rplus_le_compat_l.
  apply Rmult_le_compat_r; [exact Hz |].
  apply Rmult_le_compat_l; [exact Hscale | exact Hsd].
Qed.

(**
   [positive_cutoff_strictly_increases_in_correlation] (theorem).
   Meaning: Relates variance, square root, correlation or reliability
   parameters under the displayed numerical constraints.
   Formal conclusion: mu + (scale * composite_standard_deviation n rho1) * z <
   mu + (scale * composite_standard_deviation n rho2) * z.
   Hypotheses: Requires explicit nonzero/strict-positive denominator or scale
   where shown in the statement; all other constraints remain explicit.
   Proof outline: application of already-proved lemmas; notably
   composite_standard_deviation_strictly_increases_in_correlation,
   Rplus_lt_compat_l., Rmult_lt_compat_r.
   Library discipline: Stdlib.Reals, Lra and Psatz (including ring and field
   tactics).
   Scope: No normal distribution, population correlation estimate, or
   measurement reliability is inferred from the algebra.
 *)
Theorem positive_cutoff_strictly_increases_in_correlation :
  forall n rho1 rho2 mu scale z,
    1 < n -> 0 <= rho1 -> rho1 < rho2 -> rho2 <= 1 ->
    0 < scale -> 0 < z ->
    mu + (scale * composite_standard_deviation n rho1) * z <
      mu + (scale * composite_standard_deviation n rho2) * z.
Proof.
  intros n rho1 rho2 mu scale z Hn Hr0 Horder Hr1 Hscale Hz.
  pose proof
    (composite_standard_deviation_strictly_increases_in_correlation
      n rho1 rho2 Hn Hr0 Horder Hr1) as Hsd.
  apply Rplus_lt_compat_l.
  apply Rmult_lt_compat_r; [exact Hz |].
  apply Rmult_lt_compat_l; [exact Hscale | exact Hsd].
Qed.
