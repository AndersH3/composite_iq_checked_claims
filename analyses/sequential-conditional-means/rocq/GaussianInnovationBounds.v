(** Module: GaussianInnovationBounds.v
 Purpose: Formalize signed Gaussian-regression candidate predictions and
 strict Schur covariance reduction across repeated observed score batches.
 Mathematical representation: Real-valued symbolic observed count n,
 incoming batch size k, equicorrelation c, observed score sum s, and
 incoming score sum t. Results refer to deterministic Gaussian regression
 coefficients and Schur covariance candidates, NOT a random-variable CE.
 Explicit hypotheses: All nonzero inverses are guarded by explicitly
 positive d_n(c); full multivariate Gaussian feasibility is required
 independently before interpreting signed c probabilistically.
 Library use: Reuse SequentialReport, UnequalHistoryLinearPrediction,
 GaussianCovarianceDomain, EquicorrelationVectors and Stdlib Reals/Lra/Psatz.
 Limitations: The propositions do not construct a Gaussian measure or
 prove independence of the innovation from the observed sigma algebra.
 Reproduction: scripts/compile_rocq.sh with the Rocq 9.2 pinned CI;
 every theorem is source-ordered in PROOF_REFACTOR_GAUSSIAN.md.
 AI disclosure: OpenAI ChatGPT assisted all specifications and proof
 scripts; only a successful pinned Rocq kernel build verifies them.
*)
From Stdlib Require Import Reals Lra Psatz.
Require Import SequentialReport UnequalHistoryLinearPrediction
  EquicorrelationSpectral EquicorrelationVectors GaussianCovarianceDomain.
Open Scope R_scope.

(** [gib_signed_negative_predictor_positive_history] (theorem).
 Mathematical meaning: A positive history sum predicts a below-zero next score when signed correlation is negative.
 Exact checked proposition: forall n c s:R, c<0 -> 0<sequential_d n c -> 0<s -> hp n c s<0.
 Premises and side conditions: Positivity of d_n(c) supplies inverse
 existence and a strictly positive inverse; inequalities in c, observed
 score sums, and batch innovations are stated explicitly. Signed
 equicorrelation additionally needs full-block PSD for Gaussian use.
 Proof/definition method: Reuse previously verified predictor, Schur
 identity, covariance contrast and batch innovation lemmas, then apply
 standard Rocq real order and positivity tactics to exact expressions.
 Library reuse: GaussianCovarianceDomain, SequentialReport,
 UnequalHistoryLinearPrediction, EquicorrelationVectors and Stdlib.
 Boundary: A deterministic candidate-score or covariance identity,
 not a measure-theoretic conditional expectation or empirical IQ claim.
*)
Theorem gib_signed_negative_predictor_positive_history : forall n c s:R, c<0 -> 0<sequential_d n c -> 0<s -> hp n c s<0.
Proof.
  intros n c s Hc Hd Hs; unfold hp, Rdiv;
  assert (Hi:0< /sequential_d n c) by (apply Rinv_0_lt_compat; exact Hd);
  assert (Hprod:c*s<0) by nra;
  replace 0 with (0 * /sequential_d n c) by ring;
  apply Rmult_lt_compat_r; assumption.
Qed.

(** [gib_signed_negative_predictor_negative_history] (theorem).
 Mathematical meaning: Two negative factors, correlation and observed sum, yield a positive predictor.
 Exact checked proposition: forall n c s:R, c<0 -> 0<sequential_d n c -> s<0 -> 0<hp n c s.
 Premises and side conditions: Positivity of d_n(c) supplies inverse
 existence and a strictly positive inverse; inequalities in c, observed
 score sums, and batch innovations are stated explicitly. Signed
 equicorrelation additionally needs full-block PSD for Gaussian use.
 Proof/definition method: Reuse previously verified predictor, Schur
 identity, covariance contrast and batch innovation lemmas, then apply
 standard Rocq real order and positivity tactics to exact expressions.
 Library reuse: GaussianCovarianceDomain, SequentialReport,
 UnequalHistoryLinearPrediction, EquicorrelationVectors and Stdlib.
 Boundary: A deterministic candidate-score or covariance identity,
 not a measure-theoretic conditional expectation or empirical IQ claim.
*)
Theorem gib_signed_negative_predictor_negative_history : forall n c s:R, c<0 -> 0<sequential_d n c -> s<0 -> 0<hp n c s.
Proof.
  intros n c s Hc Hd Hs; unfold hp, Rdiv;
  assert (Hi:0< /sequential_d n c) by (apply Rinv_0_lt_compat; exact Hd);
  apply Rmult_lt_0_compat; [nra|exact Hi].
Qed.

(** [gib_signed_positive_predictor_negative_history] (theorem).
 Mathematical meaning: For positive correlation the signed regression predictor preserves negative history sums.
 Exact checked proposition: forall n c s:R, 0<c -> 0<sequential_d n c -> s<0 -> hp n c s<0.
 Premises and side conditions: Positivity of d_n(c) supplies inverse
 existence and a strictly positive inverse; inequalities in c, observed
 score sums, and batch innovations are stated explicitly. Signed
 equicorrelation additionally needs full-block PSD for Gaussian use.
 Proof/definition method: Reuse previously verified predictor, Schur
 identity, covariance contrast and batch innovation lemmas, then apply
 standard Rocq real order and positivity tactics to exact expressions.
 Library reuse: GaussianCovarianceDomain, SequentialReport,
 UnequalHistoryLinearPrediction, EquicorrelationVectors and Stdlib.
 Boundary: A deterministic candidate-score or covariance identity,
 not a measure-theoretic conditional expectation or empirical IQ claim.
*)
Theorem gib_signed_positive_predictor_negative_history : forall n c s:R, 0<c -> 0<sequential_d n c -> s<0 -> hp n c s<0.
Proof.
  intros n c s Hc Hd Hs; unfold hp, Rdiv;
  assert (Hi:0< /sequential_d n c) by (apply Rinv_0_lt_compat; exact Hd);
  assert (Hprod:c*s<0) by nra;
  replace 0 with (0 * /sequential_d n c) by ring;
  apply Rmult_lt_compat_r; assumption.
Qed.

(** [gib_signed_positive_predictor_positive_product] (theorem).
 Mathematical meaning: A positive correlation-times-sum product ensures a positive predictor in the feasible denominator domain.
 Exact checked proposition: forall n c s:R, 0<c*s -> 0<sequential_d n c -> 0<hp n c s.
 Premises and side conditions: Positivity of d_n(c) supplies inverse
 existence and a strictly positive inverse; inequalities in c, observed
 score sums, and batch innovations are stated explicitly. Signed
 equicorrelation additionally needs full-block PSD for Gaussian use.
 Proof/definition method: Reuse previously verified predictor, Schur
 identity, covariance contrast and batch innovation lemmas, then apply
 standard Rocq real order and positivity tactics to exact expressions.
 Library reuse: GaussianCovarianceDomain, SequentialReport,
 UnequalHistoryLinearPrediction, EquicorrelationVectors and Stdlib.
 Boundary: A deterministic candidate-score or covariance identity,
 not a measure-theoretic conditional expectation or empirical IQ claim.
*)
Theorem gib_signed_positive_predictor_positive_product : forall n c s:R, 0<c*s -> 0<sequential_d n c -> 0<hp n c s.
Proof.
  intros n c s Hprod Hd; unfold hp, Rdiv;
  apply Rmult_lt_0_compat; [exact Hprod|apply Rinv_0_lt_compat; exact Hd].
Qed.

(** [gib_signed_negative_predictor_negative_product] (theorem).
 Mathematical meaning: A negative correlation-times-sum product ensures a negative predictor.
 Exact checked proposition: forall n c s:R, c*s<0 -> 0<sequential_d n c -> hp n c s<0.
 Premises and side conditions: Positivity of d_n(c) supplies inverse
 existence and a strictly positive inverse; inequalities in c, observed
 score sums, and batch innovations are stated explicitly. Signed
 equicorrelation additionally needs full-block PSD for Gaussian use.
 Proof/definition method: Reuse previously verified predictor, Schur
 identity, covariance contrast and batch innovation lemmas, then apply
 standard Rocq real order and positivity tactics to exact expressions.
 Library reuse: GaussianCovarianceDomain, SequentialReport,
 UnequalHistoryLinearPrediction, EquicorrelationVectors and Stdlib.
 Boundary: A deterministic candidate-score or covariance identity,
 not a measure-theoretic conditional expectation or empirical IQ claim.
*)
Theorem gib_signed_negative_predictor_negative_product : forall n c s:R, c*s<0 -> 0<sequential_d n c -> hp n c s<0.
Proof.
  intros n c s Hprod Hd; unfold hp, Rdiv;
  assert (Hi:0< /sequential_d n c) by (apply Rinv_0_lt_compat; exact Hd);
  replace 0 with (0 * /sequential_d n c) by ring;
  apply Rmult_lt_compat_r; assumption.
Qed.

(** [gib_positive_correlation_history_weak_order] (theorem).
 Mathematical meaning: Increasing an observed score sum cannot decrease its predictor at positive correlation.
 Exact checked proposition: forall n c s t:R, 0<=c -> 0<sequential_d n c -> s<=t -> hp n c s<=hp n c t.
 Premises and side conditions: Positivity of d_n(c) supplies inverse
 existence and a strictly positive inverse; inequalities in c, observed
 score sums, and batch innovations are stated explicitly. Signed
 equicorrelation additionally needs full-block PSD for Gaussian use.
 Proof/definition method: Reuse previously verified predictor, Schur
 identity, covariance contrast and batch innovation lemmas, then apply
 standard Rocq real order and positivity tactics to exact expressions.
 Library reuse: GaussianCovarianceDomain, SequentialReport,
 UnequalHistoryLinearPrediction, EquicorrelationVectors and Stdlib.
 Boundary: A deterministic candidate-score or covariance identity,
 not a measure-theoretic conditional expectation or empirical IQ claim.
*)
Theorem gib_positive_correlation_history_weak_order : forall n c s t:R, 0<=c -> 0<sequential_d n c -> s<=t -> hp n c s<=hp n c t.
Proof.
  intros n c s t Hc Hd Hst; unfold hp, Rdiv; apply Rmult_le_compat_r; [left; apply Rinv_0_lt_compat; exact Hd|apply Rmult_le_compat_l; assumption].
Qed.

(** [gib_negative_correlation_history_weak_order] (theorem).
 Mathematical meaning: At negative correlation a larger observed score sum gives a weakly smaller prediction.
 Exact checked proposition: forall n c s t:R, c<=0 -> 0<sequential_d n c -> s<=t -> hp n c t<=hp n c s.
 Premises and side conditions: Positivity of d_n(c) supplies inverse
 existence and a strictly positive inverse; inequalities in c, observed
 score sums, and batch innovations are stated explicitly. Signed
 equicorrelation additionally needs full-block PSD for Gaussian use.
 Proof/definition method: Reuse previously verified predictor, Schur
 identity, covariance contrast and batch innovation lemmas, then apply
 standard Rocq real order and positivity tactics to exact expressions.
 Library reuse: GaussianCovarianceDomain, SequentialReport,
 UnequalHistoryLinearPrediction, EquicorrelationVectors and Stdlib.
 Boundary: A deterministic candidate-score or covariance identity,
 not a measure-theoretic conditional expectation or empirical IQ claim.
*)
Theorem gib_negative_correlation_history_weak_order : forall n c s t:R, c<=0 -> 0<sequential_d n c -> s<=t -> hp n c t<=hp n c s.
Proof.
  intros n c s t Hc Hd Hst; unfold hp, Rdiv; apply Rmult_le_compat_r; [left; apply Rinv_0_lt_compat; exact Hd|nra].
Qed.

(** [gib_positive_correlation_history_strict_order] (theorem).
 Mathematical meaning: Strictly increasing the observed sum strictly raises the regression predictor at positive correlation.
 Exact checked proposition: forall n c s t:R, 0<c -> 0<sequential_d n c -> s<t -> hp n c s<hp n c t.
 Premises and side conditions: Positivity of d_n(c) supplies inverse
 existence and a strictly positive inverse; inequalities in c, observed
 score sums, and batch innovations are stated explicitly. Signed
 equicorrelation additionally needs full-block PSD for Gaussian use.
 Proof/definition method: Reuse previously verified predictor, Schur
 identity, covariance contrast and batch innovation lemmas, then apply
 standard Rocq real order and positivity tactics to exact expressions.
 Library reuse: GaussianCovarianceDomain, SequentialReport,
 UnequalHistoryLinearPrediction, EquicorrelationVectors and Stdlib.
 Boundary: A deterministic candidate-score or covariance identity,
 not a measure-theoretic conditional expectation or empirical IQ claim.
*)
Theorem gib_positive_correlation_history_strict_order : forall n c s t:R, 0<c -> 0<sequential_d n c -> s<t -> hp n c s<hp n c t.
Proof.
  intros n c s t Hc Hd Hst; unfold hp, Rdiv; apply Rmult_lt_compat_r; [apply Rinv_0_lt_compat; exact Hd|apply Rmult_lt_compat_l; assumption].
Qed.

(** [gib_negative_correlation_history_strict_order] (theorem).
 Mathematical meaning: A strictly larger history sum decreases the predicted next score at strictly negative correlation.
 Exact checked proposition: forall n c s t:R, c<0 -> 0<sequential_d n c -> s<t -> hp n c t<hp n c s.
 Premises and side conditions: Positivity of d_n(c) supplies inverse
 existence and a strictly positive inverse; inequalities in c, observed
 score sums, and batch innovations are stated explicitly. Signed
 equicorrelation additionally needs full-block PSD for Gaussian use.
 Proof/definition method: Reuse previously verified predictor, Schur
 identity, covariance contrast and batch innovation lemmas, then apply
 standard Rocq real order and positivity tactics to exact expressions.
 Library reuse: GaussianCovarianceDomain, SequentialReport,
 UnequalHistoryLinearPrediction, EquicorrelationVectors and Stdlib.
 Boundary: A deterministic candidate-score or covariance identity,
 not a measure-theoretic conditional expectation or empirical IQ claim.
*)
Theorem gib_negative_correlation_history_strict_order : forall n c s t:R, c<0 -> 0<sequential_d n c -> s<t -> hp n c t<hp n c s.
Proof.
  intros n c s t Hc Hd Hst; unfold hp, Rdiv; apply Rmult_lt_compat_r; [apply Rinv_0_lt_compat; exact Hd|nra].
Qed.

(** [gib_negative_schur_cross_covariance] (theorem).
 Mathematical meaning: Future-score conditional cross-covariance is strictly negative under admissible negative correlation.
 Exact checked proposition: forall n c:R, c<0 -> c<1 -> 0<sequential_d n c -> equicorr_schur_cross n c<0.
 Premises and side conditions: Positivity of d_n(c) supplies inverse
 existence and a strictly positive inverse; inequalities in c, observed
 score sums, and batch innovations are stated explicitly. Signed
 equicorrelation additionally needs full-block PSD for Gaussian use.
 Proof/definition method: Reuse previously verified predictor, Schur
 identity, covariance contrast and batch innovation lemmas, then apply
 standard Rocq real order and positivity tactics to exact expressions.
 Library reuse: GaussianCovarianceDomain, SequentialReport,
 UnequalHistoryLinearPrediction, EquicorrelationVectors and Stdlib.
 Boundary: A deterministic candidate-score or covariance identity,
 not a measure-theoretic conditional expectation or empirical IQ claim.
*)
Theorem gib_negative_schur_cross_covariance : forall n c:R, c<0 -> c<1 -> 0<sequential_d n c -> equicorr_schur_cross n c<0.
Proof.
  intros n c Hc Hupper Hd; rewrite d051_schur_cross_closed by lra; unfold Rdiv;
  assert (Hi:0< /sequential_d n c) by (apply Rinv_0_lt_compat; exact Hd);
  assert (Hprod:c*(1-c)<0) by nra;
  replace 0 with (0 * /sequential_d n c) by ring;
  apply Rmult_lt_compat_r; assumption.
Qed.

(** [gib_positive_schur_cross_covariance] (theorem).
 Mathematical meaning: Future-score conditional cross-covariance is strictly positive under admissible positive correlation.
 Exact checked proposition: forall n c:R, 0<c -> c<1 -> 0<sequential_d n c -> 0<equicorr_schur_cross n c.
 Premises and side conditions: Positivity of d_n(c) supplies inverse
 existence and a strictly positive inverse; inequalities in c, observed
 score sums, and batch innovations are stated explicitly. Signed
 equicorrelation additionally needs full-block PSD for Gaussian use.
 Proof/definition method: Reuse previously verified predictor, Schur
 identity, covariance contrast and batch innovation lemmas, then apply
 standard Rocq real order and positivity tactics to exact expressions.
 Library reuse: GaussianCovarianceDomain, SequentialReport,
 UnequalHistoryLinearPrediction, EquicorrelationVectors and Stdlib.
 Boundary: A deterministic candidate-score or covariance identity,
 not a measure-theoretic conditional expectation or empirical IQ claim.
*)
Theorem gib_positive_schur_cross_covariance : forall n c:R, 0<c -> c<1 -> 0<sequential_d n c -> 0<equicorr_schur_cross n c.
Proof.
  intros n c Hc Hupper Hd; rewrite d051_schur_cross_closed by lra; unfold Rdiv;
  assert (Hi:0< /sequential_d n c) by (apply Rinv_0_lt_compat; exact Hd);
  apply Rmult_lt_0_compat; [nra|exact Hi].
Qed.

(** [gib_perfect_correlation_zero_future_cross] (theorem).
 Mathematical meaning: Perfectly correlated standardized scores have zero residual cross-covariance after observing a nonsingular first block.
 Exact checked proposition: forall n:R, 0<sequential_d n 1 -> equicorr_schur_cross n 1=0.
 Premises and side conditions: Positivity of d_n(c) supplies inverse
 existence and a strictly positive inverse; inequalities in c, observed
 score sums, and batch innovations are stated explicitly. Signed
 equicorrelation additionally needs full-block PSD for Gaussian use.
 Proof/definition method: Reuse previously verified predictor, Schur
 identity, covariance contrast and batch innovation lemmas, then apply
 standard Rocq real order and positivity tactics to exact expressions.
 Library reuse: GaussianCovarianceDomain, SequentialReport,
 UnequalHistoryLinearPrediction, EquicorrelationVectors and Stdlib.
 Boundary: A deterministic candidate-score or covariance identity,
 not a measure-theoretic conditional expectation or empirical IQ claim.
*)
Theorem gib_perfect_correlation_zero_future_cross : forall n:R, 0<sequential_d n 1 -> equicorr_schur_cross n 1=0.
Proof.
  intros n Hd; rewrite d051_schur_cross_closed by lra; unfold Rdiv; ring.
Qed.

(** [gib_perfect_correlation_zero_future_diagonal] (theorem).
 Mathematical meaning: At perfect correlation a nonsingular observed block determines every future coordinate with zero residual variance.
 Exact checked proposition: forall n:R, 0<sequential_d n 1 -> equicorr_schur_diagonal n 1=0.
 Premises and side conditions: Positivity of d_n(c) supplies inverse
 existence and a strictly positive inverse; inequalities in c, observed
 score sums, and batch innovations are stated explicitly. Signed
 equicorrelation additionally needs full-block PSD for Gaussian use.
 Proof/definition method: Reuse previously verified predictor, Schur
 identity, covariance contrast and batch innovation lemmas, then apply
 standard Rocq real order and positivity tactics to exact expressions.
 Library reuse: GaussianCovarianceDomain, SequentialReport,
 UnequalHistoryLinearPrediction, EquicorrelationVectors and Stdlib.
 Boundary: A deterministic candidate-score or covariance identity,
 not a measure-theoretic conditional expectation or empirical IQ claim.
*)
Theorem gib_perfect_correlation_zero_future_diagonal : forall n:R, 0<sequential_d n 1 -> equicorr_schur_diagonal n 1=0.
Proof.
  intros n Hd; rewrite d051_schur_diagonal_closed by lra; unfold Rdiv; ring.
Qed.

(** [gib_nested_diagonal_strict_variance_reduction] (theorem).
 Mathematical meaning: With a nonzero feasible correlation every additional observation strictly reduces the next-score Schur variance.
 Exact checked proposition: forall n k c:R, 0<k -> c<>0 -> c<1 -> 0<sequential_d n c -> 0<sequential_d (n+k) c -> equicorr_schur_diagonal (n+k) c<equicorr_schur_diagonal n c.
 Premises and side conditions: Positivity of d_n(c) supplies inverse
 existence and a strictly positive inverse; inequalities in c, observed
 score sums, and batch innovations are stated explicitly. Signed
 equicorrelation additionally needs full-block PSD for Gaussian use.
 Proof/definition method: Reuse previously verified predictor, Schur
 identity, covariance contrast and batch innovation lemmas, then apply
 standard Rocq real order and positivity tactics to exact expressions.
 Library reuse: GaussianCovarianceDomain, SequentialReport,
 UnequalHistoryLinearPrediction, EquicorrelationVectors and Stdlib.
 Boundary: A deterministic candidate-score or covariance identity,
 not a measure-theoretic conditional expectation or empirical IQ claim.
*)
Theorem gib_nested_diagonal_strict_variance_reduction : forall n k c:R, 0<k -> c<>0 -> c<1 -> 0<sequential_d n c -> 0<sequential_d (n+k) c -> equicorr_schur_diagonal (n+k) c<equicorr_schur_diagonal n c.
Proof.
  intros n k c Hk Hc Hu Hn Hnk; pose proof (d051_cov_diagonal_variance_drop n k c (Rgt_not_eq _ _ Hn) (Rgt_not_eq _ _ Hnk)) as Hdiff; assert (Hsq:0<c*c) by nra;
  assert (Hnum:0<k*c*c*(1-c)).
  { replace (k*c*c*(1-c)) with ((k*(c*c))*(1-c)) by ring.
    apply Rmult_lt_0_compat.
    - apply Rmult_lt_0_compat; assumption.
    - lra. }
  assert (Hden:0<sequential_d n c*sequential_d (n+k) c)
    by (apply Rmult_lt_0_compat; assumption); assert (Hratio:0<k*c*c*(1-c)/(sequential_d n c*sequential_d (n+k) c)) by (unfold Rdiv; apply Rmult_lt_0_compat; [exact Hnum|apply Rinv_0_lt_compat; exact Hden]); lra.
Qed.

(** [gib_nested_cross_strict_covariance_reduction] (theorem).
 Mathematical meaning: With a nonzero feasible correlation every additional observation strictly reduces the future shared Schur covariance.
 Exact checked proposition: forall n k c:R, 0<k -> c<>0 -> c<1 -> 0<sequential_d n c -> 0<sequential_d (n+k) c -> equicorr_schur_cross (n+k) c<equicorr_schur_cross n c.
 Premises and side conditions: Positivity of d_n(c) supplies inverse
 existence and a strictly positive inverse; inequalities in c, observed
 score sums, and batch innovations are stated explicitly. Signed
 equicorrelation additionally needs full-block PSD for Gaussian use.
 Proof/definition method: Reuse previously verified predictor, Schur
 identity, covariance contrast and batch innovation lemmas, then apply
 standard Rocq real order and positivity tactics to exact expressions.
 Library reuse: GaussianCovarianceDomain, SequentialReport,
 UnequalHistoryLinearPrediction, EquicorrelationVectors and Stdlib.
 Boundary: A deterministic candidate-score or covariance identity,
 not a measure-theoretic conditional expectation or empirical IQ claim.
*)
Theorem gib_nested_cross_strict_covariance_reduction : forall n k c:R, 0<k -> c<>0 -> c<1 -> 0<sequential_d n c -> 0<sequential_d (n+k) c -> equicorr_schur_cross (n+k) c<equicorr_schur_cross n c.
Proof.
  intros n k c Hk Hc Hu Hn Hnk; pose proof (gib_nested_diagonal_strict_variance_reduction n k c Hk Hc Hu Hn Hnk) as Hvar; pose proof (equicorr_schur_diagonal_contrast_gap n c) as H1; pose proof (equicorr_schur_diagonal_contrast_gap (n+k) c) as H2; lra.
Qed.

(** [gib_nested_diagonal_cross_drop_equal] (theorem).
 Mathematical meaning: The reduction in future marginal variance exactly equals the reduction in common residual covariance after a new observed block.
 Exact checked proposition: forall n k c:R, equicorr_schur_diagonal n c-equicorr_schur_diagonal (n+k) c=equicorr_schur_cross n c-equicorr_schur_cross (n+k) c.
 Premises and side conditions: Positivity of d_n(c) supplies inverse
 existence and a strictly positive inverse; inequalities in c, observed
 score sums, and batch innovations are stated explicitly. Signed
 equicorrelation additionally needs full-block PSD for Gaussian use.
 Proof/definition method: Reuse previously verified predictor, Schur
 identity, covariance contrast and batch innovation lemmas, then apply
 standard Rocq real order and positivity tactics to exact expressions.
 Library reuse: GaussianCovarianceDomain, SequentialReport,
 UnequalHistoryLinearPrediction, EquicorrelationVectors and Stdlib.
 Boundary: A deterministic candidate-score or covariance identity,
 not a measure-theoretic conditional expectation or empirical IQ claim.
*)
Theorem gib_nested_diagonal_cross_drop_equal : forall n k c:R, equicorr_schur_diagonal n c-equicorr_schur_diagonal (n+k) c=equicorr_schur_cross n c-equicorr_schur_cross (n+k) c.
Proof.
  intros n k c; pose proof (equicorr_schur_diagonal_contrast_gap n c) as H1; pose proof (equicorr_schur_diagonal_contrast_gap (n+k) c) as H2; lra.
Qed.

(** [gib_innovation_positive_correlation_positive_update] (theorem).
 Mathematical meaning: A batch with positive innovation raises the future predictor under positive correlation.
 Exact checked proposition: forall n k c s t:R, 0<c -> 0<sequential_d n c -> 0<sequential_d (n+k) c -> 0<t-k*hp n c s -> hp n c s<hp (n+k) c (s+t).
 Premises and side conditions: Positivity of d_n(c) supplies inverse
 existence and a strictly positive inverse; inequalities in c, observed
 score sums, and batch innovations are stated explicitly. Signed
 equicorrelation additionally needs full-block PSD for Gaussian use.
 Proof/definition method: Reuse previously verified predictor, Schur
 identity, covariance contrast and batch innovation lemmas, then apply
 standard Rocq real order and positivity tactics to exact expressions.
 Library reuse: GaussianCovarianceDomain, SequentialReport,
 UnequalHistoryLinearPrediction, EquicorrelationVectors and Stdlib.
 Boundary: A deterministic candidate-score or covariance identity,
 not a measure-theoretic conditional expectation or empirical IQ claim.
*)
Theorem gib_innovation_positive_correlation_positive_update : forall n k c s t:R, 0<c -> 0<sequential_d n c -> 0<sequential_d (n+k) c -> 0<t-k*hp n c s -> hp n c s<hp (n+k) c (s+t).
Proof.
  intros n k c s t Hc Hn Hnk Hinnov; rewrite d051_mean_batch_innovation by lra; unfold Rdiv;
  assert (Hi:0< /sequential_d (n+k) c) by (apply Rinv_0_lt_compat; exact Hnk);
  assert (Hprod:0<c*(t-k*hp n c s)) by nra;
  assert (Hq:0<(c*(t-k*hp n c s))* /sequential_d (n+k) c) by (apply Rmult_lt_0_compat; assumption);
  lra.
Qed.

(** [gib_innovation_positive_correlation_negative_update] (theorem).
 Mathematical meaning: A batch with negative innovation lowers the future predictor under positive correlation.
 Exact checked proposition: forall n k c s t:R, 0<c -> 0<sequential_d n c -> 0<sequential_d (n+k) c -> t-k*hp n c s<0 -> hp (n+k) c (s+t)<hp n c s.
 Premises and side conditions: Positivity of d_n(c) supplies inverse
 existence and a strictly positive inverse; inequalities in c, observed
 score sums, and batch innovations are stated explicitly. Signed
 equicorrelation additionally needs full-block PSD for Gaussian use.
 Proof/definition method: Reuse previously verified predictor, Schur
 identity, covariance contrast and batch innovation lemmas, then apply
 standard Rocq real order and positivity tactics to exact expressions.
 Library reuse: GaussianCovarianceDomain, SequentialReport,
 UnequalHistoryLinearPrediction, EquicorrelationVectors and Stdlib.
 Boundary: A deterministic candidate-score or covariance identity,
 not a measure-theoretic conditional expectation or empirical IQ claim.
*)
Theorem gib_innovation_positive_correlation_negative_update : forall n k c s t:R, 0<c -> 0<sequential_d n c -> 0<sequential_d (n+k) c -> t-k*hp n c s<0 -> hp (n+k) c (s+t)<hp n c s.
Proof.
  intros n k c s t Hc Hn Hnk Hinnov; rewrite d051_mean_batch_innovation by lra; unfold Rdiv;
  assert (Hi:0< /sequential_d (n+k) c) by (apply Rinv_0_lt_compat; exact Hnk);
  assert (Hprod:c*(t-k*hp n c s)<0) by nra;
  assert (Hq:(c*(t-k*hp n c s))* /sequential_d (n+k) c<0).
  { replace 0 with (0 * /sequential_d (n+k) c) by ring;
    apply Rmult_lt_compat_r; assumption. }
  lra.
Qed.

(** [gib_innovation_negative_correlation_positive_update] (theorem).
 Mathematical meaning: At negative equicorrelation, observing a positive innovation lowers the next-score prediction.
 Exact checked proposition: forall n k c s t:R, c<0 -> 0<sequential_d n c -> 0<sequential_d (n+k) c -> 0<t-k*hp n c s -> hp (n+k) c (s+t)<hp n c s.
 Premises and side conditions: Positivity of d_n(c) supplies inverse
 existence and a strictly positive inverse; inequalities in c, observed
 score sums, and batch innovations are stated explicitly. Signed
 equicorrelation additionally needs full-block PSD for Gaussian use.
 Proof/definition method: Reuse previously verified predictor, Schur
 identity, covariance contrast and batch innovation lemmas, then apply
 standard Rocq real order and positivity tactics to exact expressions.
 Library reuse: GaussianCovarianceDomain, SequentialReport,
 UnequalHistoryLinearPrediction, EquicorrelationVectors and Stdlib.
 Boundary: A deterministic candidate-score or covariance identity,
 not a measure-theoretic conditional expectation or empirical IQ claim.
*)
Theorem gib_innovation_negative_correlation_positive_update : forall n k c s t:R, c<0 -> 0<sequential_d n c -> 0<sequential_d (n+k) c -> 0<t-k*hp n c s -> hp (n+k) c (s+t)<hp n c s.
Proof.
  intros n k c s t Hc Hn Hnk Hinnov; rewrite d051_mean_batch_innovation by lra; unfold Rdiv;
  assert (Hi:0< /sequential_d (n+k) c) by (apply Rinv_0_lt_compat; exact Hnk);
  assert (Hprod:c*(t-k*hp n c s)<0) by nra;
  assert (Hq:(c*(t-k*hp n c s))* /sequential_d (n+k) c<0).
  { replace 0 with (0 * /sequential_d (n+k) c) by ring;
    apply Rmult_lt_compat_r; assumption. }
  lra.
Qed.

(** [gib_innovation_negative_correlation_negative_update] (theorem).
 Mathematical meaning: At negative equicorrelation, a negative innovation raises the next-score prediction.
 Exact checked proposition: forall n k c s t:R, c<0 -> 0<sequential_d n c -> 0<sequential_d (n+k) c -> t-k*hp n c s<0 -> hp n c s<hp (n+k) c (s+t).
 Premises and side conditions: Positivity of d_n(c) supplies inverse
 existence and a strictly positive inverse; inequalities in c, observed
 score sums, and batch innovations are stated explicitly. Signed
 equicorrelation additionally needs full-block PSD for Gaussian use.
 Proof/definition method: Reuse previously verified predictor, Schur
 identity, covariance contrast and batch innovation lemmas, then apply
 standard Rocq real order and positivity tactics to exact expressions.
 Library reuse: GaussianCovarianceDomain, SequentialReport,
 UnequalHistoryLinearPrediction, EquicorrelationVectors and Stdlib.
 Boundary: A deterministic candidate-score or covariance identity,
 not a measure-theoretic conditional expectation or empirical IQ claim.
*)
Theorem gib_innovation_negative_correlation_negative_update : forall n k c s t:R, c<0 -> 0<sequential_d n c -> 0<sequential_d (n+k) c -> t-k*hp n c s<0 -> hp n c s<hp (n+k) c (s+t).
Proof.
  intros n k c s t Hc Hn Hnk Hinnov; rewrite d051_mean_batch_innovation by lra; unfold Rdiv;
  assert (Hi:0< /sequential_d (n+k) c) by (apply Rinv_0_lt_compat; exact Hnk);
  assert (Hprod:0<c*(t-k*hp n c s)) by nra;
  assert (Hq:0<(c*(t-k*hp n c s))* /sequential_d (n+k) c) by (apply Rmult_lt_0_compat; assumption);
  lra.
Qed.

(** [gib_innovation_zero_exact_stability] (theorem).
 Mathematical meaning: A future batch with zero innovation leaves the predictor unchanged independent of the sign of correlation.
 Exact checked proposition: forall n k c s t:R, 0<sequential_d n c -> 0<sequential_d (n+k) c -> t-k*hp n c s=0 -> hp (n+k) c (s+t)=hp n c s.
 Premises and side conditions: Positivity of d_n(c) supplies inverse
 existence and a strictly positive inverse; inequalities in c, observed
 score sums, and batch innovations are stated explicitly. Signed
 equicorrelation additionally needs full-block PSD for Gaussian use.
 Proof/definition method: Reuse previously verified predictor, Schur
 identity, covariance contrast and batch innovation lemmas, then apply
 standard Rocq real order and positivity tactics to exact expressions.
 Library reuse: GaussianCovarianceDomain, SequentialReport,
 UnequalHistoryLinearPrediction, EquicorrelationVectors and Stdlib.
 Boundary: A deterministic candidate-score or covariance identity,
 not a measure-theoretic conditional expectation or empirical IQ claim.
*)
Theorem gib_innovation_zero_exact_stability : forall n k c s t:R, 0<sequential_d n c -> 0<sequential_d (n+k) c -> t-k*hp n c s=0 -> hp (n+k) c (s+t)=hp n c s.
Proof.
  intros n k c s t Hn Hnk Hi; rewrite d051_mean_batch_innovation by lra; rewrite Hi; unfold Rdiv; ring.
Qed.

(** [gib_innovation_batch_strict_score_order_positive] (theorem).
 Mathematical meaning: With positive correlation and feasible denominator, a higher new-batch score sum gives a higher updated predictor.
 Exact checked proposition: forall n k c s t u:R, 0<c -> 0<sequential_d (n+k) c -> t<u -> hp (n+k) c (s+t)<hp (n+k) c (s+u).
 Premises and side conditions: Positivity of d_n(c) supplies inverse
 existence and a strictly positive inverse; inequalities in c, observed
 score sums, and batch innovations are stated explicitly. Signed
 equicorrelation additionally needs full-block PSD for Gaussian use.
 Proof/definition method: Reuse previously verified predictor, Schur
 identity, covariance contrast and batch innovation lemmas, then apply
 standard Rocq real order and positivity tactics to exact expressions.
 Library reuse: GaussianCovarianceDomain, SequentialReport,
 UnequalHistoryLinearPrediction, EquicorrelationVectors and Stdlib.
 Boundary: A deterministic candidate-score or covariance identity,
 not a measure-theoretic conditional expectation or empirical IQ claim.
*)
Theorem gib_innovation_batch_strict_score_order_positive : forall n k c s t u:R, 0<c -> 0<sequential_d (n+k) c -> t<u -> hp (n+k) c (s+t)<hp (n+k) c (s+u).
Proof.
  intros n k c s t u Hc Hd Htu; apply gib_positive_correlation_history_strict_order; [exact Hc|exact Hd|lra].
Qed.

(** [gib_innovation_batch_strict_score_order_negative] (theorem).
 Mathematical meaning: With negative correlation and feasible denominator, a higher new-batch score sum gives a lower updated predictor.
 Exact checked proposition: forall n k c s t u:R, c<0 -> 0<sequential_d (n+k) c -> t<u -> hp (n+k) c (s+u)<hp (n+k) c (s+t).
 Premises and side conditions: Positivity of d_n(c) supplies inverse
 existence and a strictly positive inverse; inequalities in c, observed
 score sums, and batch innovations are stated explicitly. Signed
 equicorrelation additionally needs full-block PSD for Gaussian use.
 Proof/definition method: Reuse previously verified predictor, Schur
 identity, covariance contrast and batch innovation lemmas, then apply
 standard Rocq real order and positivity tactics to exact expressions.
 Library reuse: GaussianCovarianceDomain, SequentialReport,
 UnequalHistoryLinearPrediction, EquicorrelationVectors and Stdlib.
 Boundary: A deterministic candidate-score or covariance identity,
 not a measure-theoretic conditional expectation or empirical IQ claim.
*)
Theorem gib_innovation_batch_strict_score_order_negative : forall n k c s t u:R, c<0 -> 0<sequential_d (n+k) c -> t<u -> hp (n+k) c (s+u)<hp (n+k) c (s+t).
Proof.
  intros n k c s t u Hc Hd Htu; apply gib_negative_correlation_history_strict_order; [exact Hc|exact Hd|lra].
Qed.


(** [gib_observed_denominator_positive_given_full_psd] (theorem).
 Mathematical meaning: A feasible common-mode eigenvalue for the full battery and at least one future score forces the observed common mode to be strictly positive, without an independent inverse hypothesis.
 Exact checked proposition: forall n k c:R, 1<=n -> 0<k -> 0<=sequential_d (n+k) c -> 0<sequential_d n c.
 Premises and side conditions: Count n represents at least one observed
 score and k denotes at least one future score where specified.
 Signed correlations require the complete common/contrast eigenvalue
 feasibility conditions before a probabilistic interpretation.
 Proof/definition method: Eliminate the otherwise redundant observed
 invertibility hypothesis through the checked equicorrelation update
 identity, or reuse previously proved exact Schur spectral and residual
 covariance formulas and Stdlib order algebra.
 Library reuse: SequentialReport, EquicorrelationSpectral,
 GaussianCovarianceDomain and Rocq Stdlib Reals/Lra/Psatz/Field.
 Boundary: Exact deterministic covariance or regression arithmetic;
 no new Gaussian probability space, random variable or conditional
 expectation independence claim is introduced.
*)
Theorem gib_observed_denominator_positive_given_full_psd : forall n k c:R, 1<=n -> 0<k -> 0<=sequential_d (n+k) c -> 0<sequential_d n c.
Proof.
  intros n k c Hn Hk Hfull.
  destruct (Rlt_le_dec c 0) as [Hneg|Hnonneg].
  - rewrite sequential_denominator_add in Hfull.
    assert (Hkc:k*c<0) by nra; lra.
  - apply sequential_denominator_positive_nonnegative_correlation; assumption.
Qed.

(** [gib_observed_denominator_positive_given_full_pd] (theorem).
 Mathematical meaning: Strictly positive full common mode also forces strict observed-block invertibility, including signed correlation.
 Exact checked proposition: forall n k c:R, 1<=n -> 0<k -> 0<sequential_d (n+k) c -> 0<sequential_d n c.
 Premises and side conditions: Count n represents at least one observed
 score and k denotes at least one future score where specified.
 Signed correlations require the complete common/contrast eigenvalue
 feasibility conditions before a probabilistic interpretation.
 Proof/definition method: Eliminate the otherwise redundant observed
 invertibility hypothesis through the checked equicorrelation update
 identity, or reuse previously proved exact Schur spectral and residual
 covariance formulas and Stdlib order algebra.
 Library reuse: SequentialReport, EquicorrelationSpectral,
 GaussianCovarianceDomain and Rocq Stdlib Reals/Lra/Psatz/Field.
 Boundary: Exact deterministic covariance or regression arithmetic;
 no new Gaussian probability space, random variable or conditional
 expectation independence claim is introduced.
*)
Theorem gib_observed_denominator_positive_given_full_pd : forall n k c:R, 1<=n -> 0<k -> 0<sequential_d (n+k) c -> 0<sequential_d n c.
Proof.
  intros n k c Hn Hk Hfull.
  apply (gib_observed_denominator_positive_given_full_psd n k c Hn Hk); lra.
Qed.

(** [gib_observed_denominator_positive_at_full_singularity] (theorem).
 Mathematical meaning: A singular full common mode still leaves the proper observed block invertible when at least one future score exists.
 Exact checked proposition: forall n k c:R, 1<=n -> 0<k -> sequential_d (n+k) c=0 -> 0<sequential_d n c.
 Premises and side conditions: Count n represents at least one observed
 score and k denotes at least one future score where specified.
 Signed correlations require the complete common/contrast eigenvalue
 feasibility conditions before a probabilistic interpretation.
 Proof/definition method: Eliminate the otherwise redundant observed
 invertibility hypothesis through the checked equicorrelation update
 identity, or reuse previously proved exact Schur spectral and residual
 covariance formulas and Stdlib order algebra.
 Library reuse: SequentialReport, EquicorrelationSpectral,
 GaussianCovarianceDomain and Rocq Stdlib Reals/Lra/Psatz/Field.
 Boundary: Exact deterministic covariance or regression arithmetic;
 no new Gaussian probability space, random variable or conditional
 expectation independence claim is introduced.
*)
Theorem gib_observed_denominator_positive_at_full_singularity : forall n k c:R, 1<=n -> 0<k -> sequential_d (n+k) c=0 -> 0<sequential_d n c.
Proof.
  intros n k c Hn Hk Hfull.
  apply (gib_observed_denominator_positive_given_full_psd n k c Hn Hk); lra.
Qed.

(** [gib_full_common_singularity_requires_negative_correlation] (theorem).
 Mathematical meaning: If the full common-mode eigenvalue vanishes at a genuine battery length, the exchangeable correlation must be strictly negative.
 Exact checked proposition: forall n k c:R, 1<=n -> 0<k -> sequential_d (n+k) c=0 -> c<0.
 Premises and side conditions: Count n represents at least one observed
 score and k denotes at least one future score where specified.
 Signed correlations require the complete common/contrast eigenvalue
 feasibility conditions before a probabilistic interpretation.
 Proof/definition method: Eliminate the otherwise redundant observed
 invertibility hypothesis through the checked equicorrelation update
 identity, or reuse previously proved exact Schur spectral and residual
 covariance formulas and Stdlib order algebra.
 Library reuse: SequentialReport, EquicorrelationSpectral,
 GaussianCovarianceDomain and Rocq Stdlib Reals/Lra/Psatz/Field.
 Boundary: Exact deterministic covariance or regression arithmetic;
 no new Gaussian probability space, random variable or conditional
 expectation independence claim is introduced.
*)
Theorem gib_full_common_singularity_requires_negative_correlation : forall n k c:R, 1<=n -> 0<k -> sequential_d (n+k) c=0 -> c<0.
Proof.
  intros n k c Hn Hk Hfull.
  destruct (Rlt_le_dec c 0) as [Hneg|Hnonneg]; [exact Hneg|].
  assert (Hnk:1<=n+k) by lra.
  pose proof (sequential_denominator_positive_nonnegative_correlation
                (n+k) c Hnk Hnonneg) as Hstrict; lra.
Qed.

(** [gib_observed_denominator_positive_negative_full_domain] (theorem).
 Mathematical meaning: A negative correlation with feasible full common-mode energy produces a strictly positive observed common-mode eigenvalue.
 Exact checked proposition: forall n k c:R, 0<k -> c<0 -> 0<=sequential_d (n+k) c -> 0<sequential_d n c.
 Premises and side conditions: Count n represents at least one observed
 score and k denotes at least one future score where specified.
 Signed correlations require the complete common/contrast eigenvalue
 feasibility conditions before a probabilistic interpretation.
 Proof/definition method: Eliminate the otherwise redundant observed
 invertibility hypothesis through the checked equicorrelation update
 identity, or reuse previously proved exact Schur spectral and residual
 covariance formulas and Stdlib order algebra.
 Library reuse: SequentialReport, EquicorrelationSpectral,
 GaussianCovarianceDomain and Rocq Stdlib Reals/Lra/Psatz/Field.
 Boundary: Exact deterministic covariance or regression arithmetic;
 no new Gaussian probability space, random variable or conditional
 expectation independence claim is introduced.
*)
Theorem gib_observed_denominator_positive_negative_full_domain : forall n k c:R, 0<k -> c<0 -> 0<=sequential_d (n+k) c -> 0<sequential_d n c.
Proof.
  intros n k c Hk Hneg Hfull.
  rewrite sequential_denominator_add in Hfull.
  assert (Hkc:k*c<0) by nra; lra.
Qed.

(** [gib_future_one_denominator_nonnegative_given_full_psd] (theorem).
 Mathematical meaning: For an admissible future battery of size at least one, the leading one-future-score common mode is nonnegative.
 Exact checked proposition: forall n k c:R, 1<=n -> 1<=k -> 0<=sequential_d (n+k) c -> 0<=sequential_d (n+1) c.
 Premises and side conditions: Count n represents at least one observed
 score and k denotes at least one future score where specified.
 Signed correlations require the complete common/contrast eigenvalue
 feasibility conditions before a probabilistic interpretation.
 Proof/definition method: Eliminate the otherwise redundant observed
 invertibility hypothesis through the checked equicorrelation update
 identity, or reuse previously proved exact Schur spectral and residual
 covariance formulas and Stdlib order algebra.
 Library reuse: SequentialReport, EquicorrelationSpectral,
 GaussianCovarianceDomain and Rocq Stdlib Reals/Lra/Psatz/Field.
 Boundary: Exact deterministic covariance or regression arithmetic;
 no new Gaussian probability space, random variable or conditional
 expectation independence claim is introduced.
*)
Theorem gib_future_one_denominator_nonnegative_given_full_psd : forall n k c:R, 1<=n -> 1<=k -> 0<=sequential_d (n+k) c -> 0<=sequential_d (n+1) c.
Proof.
  intros n k c Hn Hk Hfull.
  destruct (Rlt_le_dec c 0) as [Hneg|Hnonneg].
  - pose proof (sequential_denominator_add (n+1) (k-1) c) as Hsplit.
    replace ((n+1)+(k-1)) with (n+k) in Hsplit by ring.
    assert (Hprod:(k-1)*c<=0) by nra.
    rewrite Hsplit in Hfull; lra.
  - assert (Hone:1<=n+1) by lra.
    pose proof (sequential_denominator_positive_nonnegative_correlation
                  (n+1) c Hone Hnonneg) as Hpositive; lra.
Qed.

(** [gib_future_one_denominator_positive_given_full_pd] (theorem).
 Mathematical meaning: Positive full common-mode energy yields a strictly positive leading one-future-score common mode.
 Exact checked proposition: forall n k c:R, 1<=n -> 1<=k -> 0<sequential_d (n+k) c -> 0<sequential_d (n+1) c.
 Premises and side conditions: Count n represents at least one observed
 score and k denotes at least one future score where specified.
 Signed correlations require the complete common/contrast eigenvalue
 feasibility conditions before a probabilistic interpretation.
 Proof/definition method: Eliminate the otherwise redundant observed
 invertibility hypothesis through the checked equicorrelation update
 identity, or reuse previously proved exact Schur spectral and residual
 covariance formulas and Stdlib order algebra.
 Library reuse: SequentialReport, EquicorrelationSpectral,
 GaussianCovarianceDomain and Rocq Stdlib Reals/Lra/Psatz/Field.
 Boundary: Exact deterministic covariance or regression arithmetic;
 no new Gaussian probability space, random variable or conditional
 expectation independence claim is introduced.
*)
Theorem gib_future_one_denominator_positive_given_full_pd : forall n k c:R, 1<=n -> 1<=k -> 0<sequential_d (n+k) c -> 0<sequential_d (n+1) c.
Proof.
  intros n k c Hn Hk Hfull.
  destruct (Rlt_le_dec c 0) as [Hneg|Hnonneg].
  - pose proof (sequential_denominator_add (n+1) (k-1) c) as Hsplit.
    replace ((n+1)+(k-1)) with (n+k) in Hsplit by ring.
    assert (Hprod:(k-1)*c<=0) by nra.
    rewrite Hsplit in Hfull; lra.
  - assert (Hone:1<=n+1) by lra.
    exact (sequential_denominator_positive_nonnegative_correlation
             (n+1) c Hone Hnonneg).
Qed.

(** [gib_next_variance_nonnegative_full_psd] (theorem).
 Mathematical meaning: The scalar conditional Schur variance is nonnegative in the full signed covariance feasibility domain without assuming observed invertibility separately.
 Exact checked proposition: forall n k c:R, 1<=n -> 1<=k -> c<=1 -> 0<=sequential_d (n+k) c -> 0<=equicorr_schur_diagonal n c.
 Premises and side conditions: Count n represents at least one observed
 score and k denotes at least one future score where specified.
 Signed correlations require the complete common/contrast eigenvalue
 feasibility conditions before a probabilistic interpretation.
 Proof/definition method: Eliminate the otherwise redundant observed
 invertibility hypothesis through the checked equicorrelation update
 identity, or reuse previously proved exact Schur spectral and residual
 covariance formulas and Stdlib order algebra.
 Library reuse: SequentialReport, EquicorrelationSpectral,
 GaussianCovarianceDomain and Rocq Stdlib Reals/Lra/Psatz/Field.
 Boundary: Exact deterministic covariance or regression arithmetic;
 no new Gaussian probability space, random variable or conditional
 expectation independence claim is introduced.
*)
Theorem gib_next_variance_nonnegative_full_psd : forall n k c:R, 1<=n -> 1<=k -> c<=1 -> 0<=sequential_d (n+k) c -> 0<=equicorr_schur_diagonal n c.
Proof.
  intros n k c Hn Hk Hc Hfull.
  assert (Hdn:0<sequential_d n c)
    by (apply (gib_observed_denominator_positive_given_full_psd n k c); lra).
  assert (Hone:0<=sequential_d (n+1) c)
    by (apply (gib_future_one_denominator_nonnegative_given_full_psd n k c); assumption).
  exact (d052_diagonal_nonnegative n c Hc Hdn Hone).
Qed.

(** [gib_next_variance_positive_full_pd] (theorem).
 Mathematical meaning: Under a strict feasible full Gaussian covariance, each future coordinate has strictly positive conditional variance.
 Exact checked proposition: forall n k c:R, 1<=n -> 1<=k -> c<1 -> 0<sequential_d (n+k) c -> 0<equicorr_schur_diagonal n c.
 Premises and side conditions: Count n represents at least one observed
 score and k denotes at least one future score where specified.
 Signed correlations require the complete common/contrast eigenvalue
 feasibility conditions before a probabilistic interpretation.
 Proof/definition method: Eliminate the otherwise redundant observed
 invertibility hypothesis through the checked equicorrelation update
 identity, or reuse previously proved exact Schur spectral and residual
 covariance formulas and Stdlib order algebra.
 Library reuse: SequentialReport, EquicorrelationSpectral,
 GaussianCovarianceDomain and Rocq Stdlib Reals/Lra/Psatz/Field.
 Boundary: Exact deterministic covariance or regression arithmetic;
 no new Gaussian probability space, random variable or conditional
 expectation independence claim is introduced.
*)
Theorem gib_next_variance_positive_full_pd : forall n k c:R, 1<=n -> 1<=k -> c<1 -> 0<sequential_d (n+k) c -> 0<equicorr_schur_diagonal n c.
Proof.
  intros n k c Hn Hk Hc Hfull.
  assert (Hdn:0<sequential_d n c)
    by (apply (gib_observed_denominator_positive_given_full_psd n k c); lra).
  assert (Hone:0<sequential_d (n+1) c)
    by (apply (gib_future_one_denominator_positive_given_full_pd n k c); assumption).
  exact (d052_diagonal_strict n c Hc Hdn Hone).
Qed.

(** [gib_future_common_mode_nonnegative_full_psd] (theorem).
 Mathematical meaning: The full signed covariance feasibility conditions alone guarantee a nonnegative conditional common-mode eigenvalue.
 Exact checked proposition: forall n k c:R, 1<=n -> 0<k -> c<=1 -> 0<=sequential_d (n+k) c -> 0<=equicorr_schur_diagonal n c+(k-1)*equicorr_schur_cross n c.
 Premises and side conditions: Count n represents at least one observed
 score and k denotes at least one future score where specified.
 Signed correlations require the complete common/contrast eigenvalue
 feasibility conditions before a probabilistic interpretation.
 Proof/definition method: Eliminate the otherwise redundant observed
 invertibility hypothesis through the checked equicorrelation update
 identity, or reuse previously proved exact Schur spectral and residual
 covariance formulas and Stdlib order algebra.
 Library reuse: SequentialReport, EquicorrelationSpectral,
 GaussianCovarianceDomain and Rocq Stdlib Reals/Lra/Psatz/Field.
 Boundary: Exact deterministic covariance or regression arithmetic;
 no new Gaussian probability space, random variable or conditional
 expectation independence claim is introduced.
*)
Theorem gib_future_common_mode_nonnegative_full_psd : forall n k c:R, 1<=n -> 0<k -> c<=1 -> 0<=sequential_d (n+k) c -> 0<=equicorr_schur_diagonal n c+(k-1)*equicorr_schur_cross n c.
Proof.
  intros n k c Hn Hk Hc Hfull.
  apply d052_common_mode_nonnegative; try assumption.
  apply (gib_observed_denominator_positive_given_full_psd n k c); assumption.
Qed.

(** [gib_future_common_mode_positive_full_pd] (theorem).
 Mathematical meaning: A strictly feasible full exchangeable covariance yields strictly positive residual common-mode variance.
 Exact checked proposition: forall n k c:R, 1<=n -> 0<k -> c<1 -> 0<sequential_d (n+k) c -> 0<equicorr_schur_diagonal n c+(k-1)*equicorr_schur_cross n c.
 Premises and side conditions: Count n represents at least one observed
 score and k denotes at least one future score where specified.
 Signed correlations require the complete common/contrast eigenvalue
 feasibility conditions before a probabilistic interpretation.
 Proof/definition method: Eliminate the otherwise redundant observed
 invertibility hypothesis through the checked equicorrelation update
 identity, or reuse previously proved exact Schur spectral and residual
 covariance formulas and Stdlib order algebra.
 Library reuse: SequentialReport, EquicorrelationSpectral,
 GaussianCovarianceDomain and Rocq Stdlib Reals/Lra/Psatz/Field.
 Boundary: Exact deterministic covariance or regression arithmetic;
 no new Gaussian probability space, random variable or conditional
 expectation independence claim is introduced.
*)
Theorem gib_future_common_mode_positive_full_pd : forall n k c:R, 1<=n -> 0<k -> c<1 -> 0<sequential_d (n+k) c -> 0<equicorr_schur_diagonal n c+(k-1)*equicorr_schur_cross n c.
Proof.
  intros n k c Hn Hk Hc Hfull.
  apply d052_common_mode_strict; try assumption.
  apply (gib_observed_denominator_positive_given_full_psd n k c Hn Hk); lra.
Qed.

(** [gib_future_sum_variance_nonnegative_full_psd] (theorem).
 Mathematical meaning: A future batch-total residual variance is nonnegative over the full signed Gaussian covariance PSD domain.
 Exact checked proposition: forall n k c:R, 1<=n -> 0<k -> c<=1 -> 0<=sequential_d (n+k) c -> 0<=k*equicorr_schur_diagonal n c+k*(k-1)*equicorr_schur_cross n c.
 Premises and side conditions: Count n represents at least one observed
 score and k denotes at least one future score where specified.
 Signed correlations require the complete common/contrast eigenvalue
 feasibility conditions before a probabilistic interpretation.
 Proof/definition method: Eliminate the otherwise redundant observed
 invertibility hypothesis through the checked equicorrelation update
 identity, or reuse previously proved exact Schur spectral and residual
 covariance formulas and Stdlib order algebra.
 Library reuse: SequentialReport, EquicorrelationSpectral,
 GaussianCovarianceDomain and Rocq Stdlib Reals/Lra/Psatz/Field.
 Boundary: Exact deterministic covariance or regression arithmetic;
 no new Gaussian probability space, random variable or conditional
 expectation independence claim is introduced.
*)
Theorem gib_future_sum_variance_nonnegative_full_psd : forall n k c:R, 1<=n -> 0<k -> c<=1 -> 0<=sequential_d (n+k) c -> 0<=k*equicorr_schur_diagonal n c+k*(k-1)*equicorr_schur_cross n c.
Proof.
  intros n k c Hn Hk Hc Hfull.
  apply d052_future_sum_nonnegative; try assumption; try lra.
  apply (gib_observed_denominator_positive_given_full_psd n k c); assumption.
Qed.

(** [gib_future_sum_variance_positive_full_pd] (theorem).
 Mathematical meaning: Every nonempty future batch has strictly positive residual total-score variance in the strict covariance domain.
 Exact checked proposition: forall n k c:R, 1<=n -> 0<k -> c<1 -> 0<sequential_d (n+k) c -> 0<k*equicorr_schur_diagonal n c+k*(k-1)*equicorr_schur_cross n c.
 Premises and side conditions: Count n represents at least one observed
 score and k denotes at least one future score where specified.
 Signed correlations require the complete common/contrast eigenvalue
 feasibility conditions before a probabilistic interpretation.
 Proof/definition method: Eliminate the otherwise redundant observed
 invertibility hypothesis through the checked equicorrelation update
 identity, or reuse previously proved exact Schur spectral and residual
 covariance formulas and Stdlib order algebra.
 Library reuse: SequentialReport, EquicorrelationSpectral,
 GaussianCovarianceDomain and Rocq Stdlib Reals/Lra/Psatz/Field.
 Boundary: Exact deterministic covariance or regression arithmetic;
 no new Gaussian probability space, random variable or conditional
 expectation independence claim is introduced.
*)
Theorem gib_future_sum_variance_positive_full_pd : forall n k c:R, 1<=n -> 0<k -> c<1 -> 0<sequential_d (n+k) c -> 0<k*equicorr_schur_diagonal n c+k*(k-1)*equicorr_schur_cross n c.
Proof.
  intros n k c Hn Hk Hc Hfull.
  apply d052_future_sum_strict; try assumption.
  apply (gib_observed_denominator_positive_given_full_psd n k c Hn Hk); lra.
Qed.

(** [gib_feasible_energy_nonnegative_full_psd] (theorem).
 Mathematical meaning: Every Cauchy-feasible abstract future quadratic summary has nonnegative Schur residual energy under full-battery covariance feasibility.
 Exact checked proposition: forall n k c energy total:R, 1<=n -> 0<k -> c<=1 -> 0<=sequential_d (n+k) c -> 0<=energy-total*total/k -> 0<=equicorr_schur_energy n c energy total.
 Premises and side conditions: Count n represents at least one observed
 score and k denotes at least one future score where specified.
 Signed correlations require the complete common/contrast eigenvalue
 feasibility conditions before a probabilistic interpretation.
 Proof/definition method: Eliminate the otherwise redundant observed
 invertibility hypothesis through the checked equicorrelation update
 identity, or reuse previously proved exact Schur spectral and residual
 covariance formulas and Stdlib order algebra.
 Library reuse: SequentialReport, EquicorrelationSpectral,
 GaussianCovarianceDomain and Rocq Stdlib Reals/Lra/Psatz/Field.
 Boundary: Exact deterministic covariance or regression arithmetic;
 no new Gaussian probability space, random variable or conditional
 expectation independence claim is introduced.
*)
Theorem gib_feasible_energy_nonnegative_full_psd : forall n k c energy total:R, 1<=n -> 0<k -> c<=1 -> 0<=sequential_d (n+k) c -> 0<=energy-total*total/k -> 0<=equicorr_schur_energy n c energy total.
Proof.
  intros n k c energy total Hn Hk Hc Hfull Hfeasible.
  apply (gcd_schur_psd_arbitrary_sign n k c energy total); try assumption.
  apply (gib_observed_denominator_positive_given_full_psd n k c); assumption.
Qed.

(** [gib_feasible_energy_positive_full_pd] (theorem).
 Mathematical meaning: Every nonzero Cauchy-feasible future energy summary has strictly positive Schur energy when the full covariance is PD.
 Exact checked proposition: forall n k c energy total:R, 1<=n -> 0<k -> c<1 -> 0<sequential_d (n+k) c -> 0<energy -> 0<=energy-total*total/k -> 0<equicorr_schur_energy n c energy total.
 Premises and side conditions: Count n represents at least one observed
 score and k denotes at least one future score where specified.
 Signed correlations require the complete common/contrast eigenvalue
 feasibility conditions before a probabilistic interpretation.
 Proof/definition method: Eliminate the otherwise redundant observed
 invertibility hypothesis through the checked equicorrelation update
 identity, or reuse previously proved exact Schur spectral and residual
 covariance formulas and Stdlib order algebra.
 Library reuse: SequentialReport, EquicorrelationSpectral,
 GaussianCovarianceDomain and Rocq Stdlib Reals/Lra/Psatz/Field.
 Boundary: Exact deterministic covariance or regression arithmetic;
 no new Gaussian probability space, random variable or conditional
 expectation independence claim is introduced.
*)
Theorem gib_feasible_energy_positive_full_pd : forall n k c energy total:R, 1<=n -> 0<k -> c<1 -> 0<sequential_d (n+k) c -> 0<energy -> 0<=energy-total*total/k -> 0<equicorr_schur_energy n c energy total.
Proof.
  intros n k c energy total Hn Hk Hc Hfull Henergy Hfeasible.
  apply (gcd_schur_pd_arbitrary_sign n k c energy total); try assumption.
  apply (gib_observed_denominator_positive_given_full_psd n k c Hn Hk); lra.
Qed.

(** [gib_singular_full_common_mode_zero] (theorem).
 Mathematical meaning: At the lower singular covariance boundary the future all-ones residual eigenvalue is exactly zero.
 Exact checked proposition: forall n k c:R, 1<=n -> 0<k -> sequential_d (n+k) c=0 -> equicorr_schur_diagonal n c+(k-1)*equicorr_schur_cross n c=0.
 Premises and side conditions: Count n represents at least one observed
 score and k denotes at least one future score where specified.
 Signed correlations require the complete common/contrast eigenvalue
 feasibility conditions before a probabilistic interpretation.
 Proof/definition method: Eliminate the otherwise redundant observed
 invertibility hypothesis through the checked equicorrelation update
 identity, or reuse previously proved exact Schur spectral and residual
 covariance formulas and Stdlib order algebra.
 Library reuse: SequentialReport, EquicorrelationSpectral,
 GaussianCovarianceDomain and Rocq Stdlib Reals/Lra/Psatz/Field.
 Boundary: Exact deterministic covariance or regression arithmetic;
 no new Gaussian probability space, random variable or conditional
 expectation independence claim is introduced.
*)
Theorem gib_singular_full_common_mode_zero : forall n k c:R, 1<=n -> 0<k -> sequential_d (n+k) c=0 -> equicorr_schur_diagonal n c+(k-1)*equicorr_schur_cross n c=0.
Proof.
  intros n k c Hn Hk Hzero.
  assert (Hdn:0<sequential_d n c)
    by (apply (gib_observed_denominator_positive_given_full_psd n k c); lra).
  rewrite d051_schur_common_mode by lra.
  rewrite Hzero; unfold Rdiv; ring.
Qed.

(** [gib_singular_full_future_total_variance_zero] (theorem).
 Mathematical meaning: At the singular full common mode, the sum of future Gaussian residuals has exactly zero model variance.
 Exact checked proposition: forall n k c:R, 1<=n -> 0<k -> sequential_d (n+k) c=0 -> k*equicorr_schur_diagonal n c+k*(k-1)*equicorr_schur_cross n c=0.
 Premises and side conditions: Count n represents at least one observed
 score and k denotes at least one future score where specified.
 Signed correlations require the complete common/contrast eigenvalue
 feasibility conditions before a probabilistic interpretation.
 Proof/definition method: Eliminate the otherwise redundant observed
 invertibility hypothesis through the checked equicorrelation update
 identity, or reuse previously proved exact Schur spectral and residual
 covariance formulas and Stdlib order algebra.
 Library reuse: SequentialReport, EquicorrelationSpectral,
 GaussianCovarianceDomain and Rocq Stdlib Reals/Lra/Psatz/Field.
 Boundary: Exact deterministic covariance or regression arithmetic;
 no new Gaussian probability space, random variable or conditional
 expectation independence claim is introduced.
*)
Theorem gib_singular_full_future_total_variance_zero : forall n k c:R, 1<=n -> 0<k -> sequential_d (n+k) c=0 -> k*equicorr_schur_diagonal n c+k*(k-1)*equicorr_schur_cross n c=0.
Proof.
  intros n k c Hn Hk Hzero.
  assert (Hdn:0<sequential_d n c)
    by (apply (gib_observed_denominator_positive_given_full_psd n k c); lra).
  rewrite d051_schur_future_sum_variance by lra.
  rewrite Hzero; unfold Rdiv; ring.
Qed.

(** [gib_singular_single_future_variance_zero] (theorem).
 Mathematical meaning: A single future score is completely determined in the lower singular full covariance endpoint.
 Exact checked proposition: forall n c:R, 1<=n -> sequential_d (n+1) c=0 -> equicorr_schur_diagonal n c=0.
 Premises and side conditions: Count n represents at least one observed
 score and k denotes at least one future score where specified.
 Signed correlations require the complete common/contrast eigenvalue
 feasibility conditions before a probabilistic interpretation.
 Proof/definition method: Eliminate the otherwise redundant observed
 invertibility hypothesis through the checked equicorrelation update
 identity, or reuse previously proved exact Schur spectral and residual
 covariance formulas and Stdlib order algebra.
 Library reuse: SequentialReport, EquicorrelationSpectral,
 GaussianCovarianceDomain and Rocq Stdlib Reals/Lra/Psatz/Field.
 Boundary: Exact deterministic covariance or regression arithmetic;
 no new Gaussian probability space, random variable or conditional
 expectation independence claim is introduced.
*)
Theorem gib_singular_single_future_variance_zero : forall n c:R, 1<=n -> sequential_d (n+1) c=0 -> equicorr_schur_diagonal n c=0.
Proof.
  intros n c Hn Hzero.
  assert (Hdn:0<sequential_d n c).
  { apply (gib_observed_denominator_positive_given_full_psd n 1 c); lra. }
  apply gcd_single_future_lower_singularity; lra.
Qed.

(** [gib_perfect_correlation_predictor_observed_mean] (theorem).
 Mathematical meaning: At perfect correlation, the canonical next-score candidate predictor equals the mean of an observed battery.
 Exact checked proposition: forall n s:R, 0<n -> hp n 1 s=s/n.
 Premises and side conditions: Count n represents at least one observed
 score and k denotes at least one future score where specified.
 Signed correlations require the complete common/contrast eigenvalue
 feasibility conditions before a probabilistic interpretation.
 Proof/definition method: Eliminate the otherwise redundant observed
 invertibility hypothesis through the checked equicorrelation update
 identity, or reuse previously proved exact Schur spectral and residual
 covariance formulas and Stdlib order algebra.
 Library reuse: SequentialReport, EquicorrelationSpectral,
 GaussianCovarianceDomain and Rocq Stdlib Reals/Lra/Psatz/Field.
 Boundary: Exact deterministic covariance or regression arithmetic;
 no new Gaussian probability space, random variable or conditional
 expectation independence claim is introduced.
*)
Theorem gib_perfect_correlation_predictor_observed_mean : forall n s:R, 0<n -> hp n 1 s=s/n.
Proof.
  intros n s Hn.
  unfold hp; rewrite sequential_denominator_at_unit_correlation.
  field; lra.
Qed.

(** [gib_perfect_correlation_equal_observation_predictor] (theorem).
 Mathematical meaning: A perfectly correlated history with all scores a predicts precisely a rather than an attenuated value.
 Exact checked proposition: forall n a:R, 0<n -> hp n 1 (n*a)=a.
 Premises and side conditions: Count n represents at least one observed
 score and k denotes at least one future score where specified.
 Signed correlations require the complete common/contrast eigenvalue
 feasibility conditions before a probabilistic interpretation.
 Proof/definition method: Eliminate the otherwise redundant observed
 invertibility hypothesis through the checked equicorrelation update
 identity, or reuse previously proved exact Schur spectral and residual
 covariance formulas and Stdlib order algebra.
 Library reuse: SequentialReport, EquicorrelationSpectral,
 GaussianCovarianceDomain and Rocq Stdlib Reals/Lra/Psatz/Field.
 Boundary: Exact deterministic covariance or regression arithmetic;
 no new Gaussian probability space, random variable or conditional
 expectation independence claim is introduced.
*)
Theorem gib_perfect_correlation_equal_observation_predictor : forall n a:R, 0<n -> hp n 1 (n*a)=a.
Proof.
  intros n a Hn.
  rewrite gib_perfect_correlation_predictor_observed_mean by lra.
  field; lra.
Qed.

