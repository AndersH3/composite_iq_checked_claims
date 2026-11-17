(** Module: GaussianBatchBalance.v
 Purpose: Prove exact observed-versus-future score-total conservation,
 the full-to-observed covariance eigenvalue gain, positivity, signed
 attenuation, inclusive predicted mean, and lower singular endpoints.
 Mathematical representation: The number n of observed scores and k
 of as-yet unobserved scores are real symbolic battery counts, with
 observed sum s and common covariance correlation c. The canonical
 sufficient-sum predictor hp, predicted future sum hf, predicted
 whole-battery total ht and inclusive mean hm are reused unchanged.
 Explicit hypotheses: Positive observed sizes and future counts
 explicitly represent valid sample sizes. Nonzero eigenvalue divisors,
 strict feasibility, and signed correlation assumptions appear in each
 proposition that needs them.
 Library use: Reuses GaussianInnovationBounds, SequentialReport,
 UnequalHistoryLinearPrediction, GaussianCovarianceDomain, and Rocq
 Stdlib Reals, Lra, Psatz, Ring, Field rather than new scoring functions.
 Limitations: This is exact deterministic Gaussian best-linear-predictor
 arithmetic. It does not construct a normal probability measure,
 independence of innovations, conditional expectation, or IQ calibration.
 Reproduction: scripts/compile_rocq.sh with pinned Rocq 9.2.
 AI disclosure: The theorem inventory, scripts and documentation were
 produced with OpenAI assistance for researcher Anders Hellström; only
 Rocq kernel compilation establishes formal verification.
*)
From Stdlib Require Import Reals Lra Psatz Ring Field.
Require Import SequentialReport UnequalHistoryLinearPrediction
  EquicorrelationSpectral GaussianCovarianceDomain
  GaussianInnovationBounds.
Open Scope R_scope.

(** [gbb_total_balance] (theorem).
 Mathematical meaning: The observed-plus-predicted full-battery score total satisfies a covariance denominator conservation identity, a core algebraic bridge for any number of observed and future tests.
 Exact checked proposition: forall n k c s:R, sequential_d n c<>0 -> sequential_d n c*ht n k c s=sequential_d (n+k) c*s.
 Premises and side conditions: Every theorem states its denominator,
 sample-size and covariance-domain requirements. The proper signed
 Gaussian covariance domain additionally requires the full covariance
 matrix to be PSD or PD; symbolic negative correlations are interpreted
 probabilistically only when those spectral conditions hold.
 Proof/definition method: Derive from the single shared score-total
 conservation identity or canonical Schur eigenvalue and predictor
 identities using Stdlib ring, field and real-order proofs. Distinct
 refinements cover equality, inequality and singular-boundary cases.
 Library reuse: SequentialReport, UnequalHistoryLinearPrediction,
 GaussianInnovationBounds, GaussianCovarianceDomain and Stdlib.
 Boundary: Deterministic regression and covariance statements;
 no measure-theoretic conditional expectation or population-IQ
 distribution is established by these arithmetic identities.
*)
Theorem gbb_total_balance : forall n k c s:R, sequential_d n c<>0 -> sequential_d n c*ht n k c s=sequential_d (n+k) c*s.
Proof.
 intros n k c s Hd.
 unfold ht,hf,hp.
 rewrite sequential_denominator_add.
 field; exact Hd.
Qed.

(** [gbb_total_ratio] (theorem).
 Mathematical meaning: The observed-plus-predicted battery total is the history sum multiplied by the exact full-to-observed common-mode eigenvalue ratio.
 Exact checked proposition: forall n k c s:R, sequential_d n c<>0 -> ht n k c s=(sequential_d (n+k) c/sequential_d n c)*s.
 Premises and side conditions: Every theorem states its denominator,
 sample-size and covariance-domain requirements. The proper signed
 Gaussian covariance domain additionally requires the full covariance
 matrix to be PSD or PD; symbolic negative correlations are interpreted
 probabilistically only when those spectral conditions hold.
 Proof/definition method: Derive from the single shared score-total
 conservation identity or canonical Schur eigenvalue and predictor
 identities using Stdlib ring, field and real-order proofs. Distinct
 refinements cover equality, inequality and singular-boundary cases.
 Library reuse: SequentialReport, UnequalHistoryLinearPrediction,
 GaussianInnovationBounds, GaussianCovarianceDomain and Stdlib.
 Boundary: Deterministic regression and covariance statements;
 no measure-theoretic conditional expectation or population-IQ
 distribution is established by these arithmetic identities.
*)
Theorem gbb_total_ratio : forall n k c s:R, sequential_d n c<>0 -> ht n k c s=(sequential_d (n+k) c/sequential_d n c)*s.
Proof.
 intros n k c s Hd.
 unfold ht,hf,hp.
 rewrite sequential_denominator_add.
 field; exact Hd.
Qed.

(** [gbb_ratio_gain_difference] (theorem).
 Mathematical meaning: The full-to-observed covariance denominator ratio differs from one by the signed future-count prediction gain.
 Exact checked proposition: forall n k c:R, sequential_d n c<>0 -> sequential_d (n+k) c/sequential_d n c-1=k*c/sequential_d n c.
 Premises and side conditions: Every theorem states its denominator,
 sample-size and covariance-domain requirements. The proper signed
 Gaussian covariance domain additionally requires the full covariance
 matrix to be PSD or PD; symbolic negative correlations are interpreted
 probabilistically only when those spectral conditions hold.
 Proof/definition method: Derive from the single shared score-total
 conservation identity or canonical Schur eigenvalue and predictor
 identities using Stdlib ring, field and real-order proofs. Distinct
 refinements cover equality, inequality and singular-boundary cases.
 Library reuse: SequentialReport, UnequalHistoryLinearPrediction,
 GaussianInnovationBounds, GaussianCovarianceDomain and Stdlib.
 Boundary: Deterministic regression and covariance statements;
 no measure-theoretic conditional expectation or population-IQ
 distribution is established by these arithmetic identities.
*)
Theorem gbb_ratio_gain_difference : forall n k c:R, sequential_d n c<>0 -> sequential_d (n+k) c/sequential_d n c-1=k*c/sequential_d n c.
Proof.
 intros n k c Hd; rewrite sequential_denominator_add.
 field; exact Hd.
Qed.

(** [gbb_total_zero_at_full_singularity] (theorem).
 Mathematical meaning: When the full common covariance eigenvalue vanishes, the observed score sum plus all model-predicted future scores equals zero.
 Exact checked proposition: forall n k c s:R, 1<=n -> 0<k -> sequential_d (n+k) c=0 -> ht n k c s=0.
 Premises and side conditions: Every theorem states its denominator,
 sample-size and covariance-domain requirements. The proper signed
 Gaussian covariance domain additionally requires the full covariance
 matrix to be PSD or PD; symbolic negative correlations are interpreted
 probabilistically only when those spectral conditions hold.
 Proof/definition method: Derive from the single shared score-total
 conservation identity or canonical Schur eigenvalue and predictor
 identities using Stdlib ring, field and real-order proofs. Distinct
 refinements cover equality, inequality and singular-boundary cases.
 Library reuse: SequentialReport, UnequalHistoryLinearPrediction,
 GaussianInnovationBounds, GaussianCovarianceDomain and Stdlib.
 Boundary: Deterministic regression and covariance statements;
 no measure-theoretic conditional expectation or population-IQ
 distribution is established by these arithmetic identities.
*)
Theorem gbb_total_zero_at_full_singularity : forall n k c s:R, 1<=n -> 0<k -> sequential_d (n+k) c=0 -> ht n k c s=0.
Proof.
 intros n k c s Hn Hk Hzero.
 assert (Hd:0<sequential_d n c)
   by (apply (gib_observed_denominator_positive_at_full_singularity n k c); assumption).
 rewrite gbb_total_ratio by lra.
 rewrite Hzero; unfold Rdiv; ring.
Qed.

(** [gbb_future_sum_opposes_history_at_full_singularity] (theorem).
 Mathematical meaning: At the singular lower common-mode boundary the predicted future-score total is exactly the negative observed-score sum.
 Exact checked proposition: forall n k c s:R, 1<=n -> 0<k -> sequential_d (n+k) c=0 -> hf n k c s=-s.
 Premises and side conditions: Every theorem states its denominator,
 sample-size and covariance-domain requirements. The proper signed
 Gaussian covariance domain additionally requires the full covariance
 matrix to be PSD or PD; symbolic negative correlations are interpreted
 probabilistically only when those spectral conditions hold.
 Proof/definition method: Derive from the single shared score-total
 conservation identity or canonical Schur eigenvalue and predictor
 identities using Stdlib ring, field and real-order proofs. Distinct
 refinements cover equality, inequality and singular-boundary cases.
 Library reuse: SequentialReport, UnequalHistoryLinearPrediction,
 GaussianInnovationBounds, GaussianCovarianceDomain and Stdlib.
 Boundary: Deterministic regression and covariance statements;
 no measure-theoretic conditional expectation or population-IQ
 distribution is established by these arithmetic identities.
*)
Theorem gbb_future_sum_opposes_history_at_full_singularity : forall n k c s:R, 1<=n -> 0<k -> sequential_d (n+k) c=0 -> hf n k c s=-s.
Proof.
 intros n k c s Hn Hk Hzero.
 pose proof (gbb_total_zero_at_full_singularity n k c s Hn Hk Hzero) as Htotal.
 unfold ht in Htotal; lra.
Qed.

(** [gbb_inclusive_mean_zero_at_full_singularity] (theorem).
 Mathematical meaning: The predicted inclusive mean is zero at the full covariance lower singular boundary even for nonzero observed sums.
 Exact checked proposition: forall n k c s:R, 1<=n -> 0<k -> sequential_d (n+k) c=0 -> hm n k c s=0.
 Premises and side conditions: Every theorem states its denominator,
 sample-size and covariance-domain requirements. The proper signed
 Gaussian covariance domain additionally requires the full covariance
 matrix to be PSD or PD; symbolic negative correlations are interpreted
 probabilistically only when those spectral conditions hold.
 Proof/definition method: Derive from the single shared score-total
 conservation identity or canonical Schur eigenvalue and predictor
 identities using Stdlib ring, field and real-order proofs. Distinct
 refinements cover equality, inequality and singular-boundary cases.
 Library reuse: SequentialReport, UnequalHistoryLinearPrediction,
 GaussianInnovationBounds, GaussianCovarianceDomain and Stdlib.
 Boundary: Deterministic regression and covariance statements;
 no measure-theoretic conditional expectation or population-IQ
 distribution is established by these arithmetic identities.
*)
Theorem gbb_inclusive_mean_zero_at_full_singularity : forall n k c s:R, 1<=n -> 0<k -> sequential_d (n+k) c=0 -> hm n k c s=0.
Proof.
 intros n k c s Hn Hk Hzero.
 unfold hm.
 rewrite (gbb_total_zero_at_full_singularity n k c s Hn Hk Hzero).
 unfold Rdiv; ring.
Qed.

(** [gbb_total_gain_nonnegative_on_full_psd] (theorem).
 Mathematical meaning: A feasible full-battery common-mode eigenvalue yields a nonnegative ratio of full-to-observed eigenvalues.
 Exact checked proposition: forall n k c:R, 1<=n -> 0<k -> 0<=sequential_d (n+k) c -> 0<=sequential_d (n+k) c/sequential_d n c.
 Premises and side conditions: Every theorem states its denominator,
 sample-size and covariance-domain requirements. The proper signed
 Gaussian covariance domain additionally requires the full covariance
 matrix to be PSD or PD; symbolic negative correlations are interpreted
 probabilistically only when those spectral conditions hold.
 Proof/definition method: Derive from the single shared score-total
 conservation identity or canonical Schur eigenvalue and predictor
 identities using Stdlib ring, field and real-order proofs. Distinct
 refinements cover equality, inequality and singular-boundary cases.
 Library reuse: SequentialReport, UnequalHistoryLinearPrediction,
 GaussianInnovationBounds, GaussianCovarianceDomain and Stdlib.
 Boundary: Deterministic regression and covariance statements;
 no measure-theoretic conditional expectation or population-IQ
 distribution is established by these arithmetic identities.
*)
Theorem gbb_total_gain_nonnegative_on_full_psd : forall n k c:R, 1<=n -> 0<k -> 0<=sequential_d (n+k) c -> 0<=sequential_d (n+k) c/sequential_d n c.
Proof.
 intros n k c Hn Hk Hfull.
 assert (Hd:0<sequential_d n c)
  by (apply (gib_observed_denominator_positive_given_full_psd n k c); assumption).
 unfold Rdiv.
 apply Rmult_le_pos; [exact Hfull|].
 left; apply Rinv_0_lt_compat; exact Hd.
Qed.

(** [gbb_total_gain_positive_on_full_pd] (theorem).
 Mathematical meaning: A strictly feasible full-battery covariance yields a strictly positive full-to-observed common-mode gain.
 Exact checked proposition: forall n k c:R, 1<=n -> 0<k -> 0<sequential_d (n+k) c -> 0<sequential_d (n+k) c/sequential_d n c.
 Premises and side conditions: Every theorem states its denominator,
 sample-size and covariance-domain requirements. The proper signed
 Gaussian covariance domain additionally requires the full covariance
 matrix to be PSD or PD; symbolic negative correlations are interpreted
 probabilistically only when those spectral conditions hold.
 Proof/definition method: Derive from the single shared score-total
 conservation identity or canonical Schur eigenvalue and predictor
 identities using Stdlib ring, field and real-order proofs. Distinct
 refinements cover equality, inequality and singular-boundary cases.
 Library reuse: SequentialReport, UnequalHistoryLinearPrediction,
 GaussianInnovationBounds, GaussianCovarianceDomain and Stdlib.
 Boundary: Deterministic regression and covariance statements;
 no measure-theoretic conditional expectation or population-IQ
 distribution is established by these arithmetic identities.
*)
Theorem gbb_total_gain_positive_on_full_pd : forall n k c:R, 1<=n -> 0<k -> 0<sequential_d (n+k) c -> 0<sequential_d (n+k) c/sequential_d n c.
Proof.
 intros n k c Hn Hk Hfull.
 assert (Hd:0<sequential_d n c)
  by (apply (gib_observed_denominator_positive_given_full_pd n k c); assumption).
 unfold Rdiv.
 apply Rmult_lt_0_compat; [exact Hfull|].
 apply Rinv_0_lt_compat; exact Hd.
Qed.

(** [gbb_expected_total_nonnegative_full_psd] (theorem).
 Mathematical meaning: Under full covariance feasibility a nonnegative observed score sum cannot produce a negative predicted full-battery score total.
 Exact checked proposition: forall n k c s:R, 1<=n -> 0<k -> 0<=sequential_d (n+k) c -> 0<=s -> 0<=ht n k c s.
 Premises and side conditions: Every theorem states its denominator,
 sample-size and covariance-domain requirements. The proper signed
 Gaussian covariance domain additionally requires the full covariance
 matrix to be PSD or PD; symbolic negative correlations are interpreted
 probabilistically only when those spectral conditions hold.
 Proof/definition method: Derive from the single shared score-total
 conservation identity or canonical Schur eigenvalue and predictor
 identities using Stdlib ring, field and real-order proofs. Distinct
 refinements cover equality, inequality and singular-boundary cases.
 Library reuse: SequentialReport, UnequalHistoryLinearPrediction,
 GaussianInnovationBounds, GaussianCovarianceDomain and Stdlib.
 Boundary: Deterministic regression and covariance statements;
 no measure-theoretic conditional expectation or population-IQ
 distribution is established by these arithmetic identities.
*)
Theorem gbb_expected_total_nonnegative_full_psd : forall n k c s:R, 1<=n -> 0<k -> 0<=sequential_d (n+k) c -> 0<=s -> 0<=ht n k c s.
Proof.
 intros n k c s Hn Hk Hfull Hs.
 assert (Hd:0<sequential_d n c)
  by (apply (gib_observed_denominator_positive_given_full_psd n k c); assumption).
 rewrite gbb_total_ratio by lra.
 apply Rmult_le_pos; [apply gbb_total_gain_nonnegative_on_full_psd; assumption|exact Hs].
Qed.

(** [gbb_expected_total_positive_full_pd] (theorem).
 Mathematical meaning: Strict full covariance feasibility preserves the strictly positive sign of a nonzero positive observed total after future prediction.
 Exact checked proposition: forall n k c s:R, 1<=n -> 0<k -> 0<sequential_d (n+k) c -> 0<s -> 0<ht n k c s.
 Premises and side conditions: Every theorem states its denominator,
 sample-size and covariance-domain requirements. The proper signed
 Gaussian covariance domain additionally requires the full covariance
 matrix to be PSD or PD; symbolic negative correlations are interpreted
 probabilistically only when those spectral conditions hold.
 Proof/definition method: Derive from the single shared score-total
 conservation identity or canonical Schur eigenvalue and predictor
 identities using Stdlib ring, field and real-order proofs. Distinct
 refinements cover equality, inequality and singular-boundary cases.
 Library reuse: SequentialReport, UnequalHistoryLinearPrediction,
 GaussianInnovationBounds, GaussianCovarianceDomain and Stdlib.
 Boundary: Deterministic regression and covariance statements;
 no measure-theoretic conditional expectation or population-IQ
 distribution is established by these arithmetic identities.
*)
Theorem gbb_expected_total_positive_full_pd : forall n k c s:R, 1<=n -> 0<k -> 0<sequential_d (n+k) c -> 0<s -> 0<ht n k c s.
Proof.
 intros n k c s Hn Hk Hfull Hs.
 assert (Hd:0<sequential_d n c)
  by (apply (gib_observed_denominator_positive_given_full_pd n k c); assumption).
 rewrite gbb_total_ratio by lra.
 apply Rmult_lt_0_compat; [apply gbb_total_gain_positive_on_full_pd; assumption|exact Hs].
Qed.

(** [gbb_expected_total_nonpositive_full_psd] (theorem).
 Mathematical meaning: Under full covariance feasibility a nonpositive observed sum produces a nonpositive full predicted score total.
 Exact checked proposition: forall n k c s:R, 1<=n -> 0<k -> 0<=sequential_d (n+k) c -> s<=0 -> ht n k c s<=0.
 Premises and side conditions: Every theorem states its denominator,
 sample-size and covariance-domain requirements. The proper signed
 Gaussian covariance domain additionally requires the full covariance
 matrix to be PSD or PD; symbolic negative correlations are interpreted
 probabilistically only when those spectral conditions hold.
 Proof/definition method: Derive from the single shared score-total
 conservation identity or canonical Schur eigenvalue and predictor
 identities using Stdlib ring, field and real-order proofs. Distinct
 refinements cover equality, inequality and singular-boundary cases.
 Library reuse: SequentialReport, UnequalHistoryLinearPrediction,
 GaussianInnovationBounds, GaussianCovarianceDomain and Stdlib.
 Boundary: Deterministic regression and covariance statements;
 no measure-theoretic conditional expectation or population-IQ
 distribution is established by these arithmetic identities.
*)
Theorem gbb_expected_total_nonpositive_full_psd : forall n k c s:R, 1<=n -> 0<k -> 0<=sequential_d (n+k) c -> s<=0 -> ht n k c s<=0.
Proof.
 intros n k c s Hn Hk Hfull Hs.
 assert (Hd:0<sequential_d n c)
  by (apply (gib_observed_denominator_positive_given_full_psd n k c); assumption).
 rewrite gbb_total_ratio by lra.
 pose proof (gbb_total_gain_nonnegative_on_full_psd n k c Hn Hk Hfull) as Hgain.
 nra.
Qed.

(** [gbb_expected_total_negative_full_pd] (theorem).
 Mathematical meaning: Under strictly feasible full covariance a strictly negative history sum gives a strictly negative predicted battery total.
 Exact checked proposition: forall n k c s:R, 1<=n -> 0<k -> 0<sequential_d (n+k) c -> s<0 -> ht n k c s<0.
 Premises and side conditions: Every theorem states its denominator,
 sample-size and covariance-domain requirements. The proper signed
 Gaussian covariance domain additionally requires the full covariance
 matrix to be PSD or PD; symbolic negative correlations are interpreted
 probabilistically only when those spectral conditions hold.
 Proof/definition method: Derive from the single shared score-total
 conservation identity or canonical Schur eigenvalue and predictor
 identities using Stdlib ring, field and real-order proofs. Distinct
 refinements cover equality, inequality and singular-boundary cases.
 Library reuse: SequentialReport, UnequalHistoryLinearPrediction,
 GaussianInnovationBounds, GaussianCovarianceDomain and Stdlib.
 Boundary: Deterministic regression and covariance statements;
 no measure-theoretic conditional expectation or population-IQ
 distribution is established by these arithmetic identities.
*)
Theorem gbb_expected_total_negative_full_pd : forall n k c s:R, 1<=n -> 0<k -> 0<sequential_d (n+k) c -> s<0 -> ht n k c s<0.
Proof.
 intros n k c s Hn Hk Hfull Hs.
 assert (Hd:0<sequential_d n c)
  by (apply (gib_observed_denominator_positive_given_full_pd n k c); assumption).
 rewrite gbb_total_ratio by lra.
 pose proof (gbb_total_gain_positive_on_full_pd n k c Hn Hk Hfull) as Hgain.
 nra.
Qed.

(** [gbb_expected_total_strict_history_order] (theorem).
 Mathematical meaning: Strictly feasible full covariance makes the predicted total a strictly increasing function of its observed-history score sum.
 Exact checked proposition: forall n k c s t:R, 1<=n -> 0<k -> 0<sequential_d (n+k) c -> s<t -> ht n k c s<ht n k c t.
 Premises and side conditions: Every theorem states its denominator,
 sample-size and covariance-domain requirements. The proper signed
 Gaussian covariance domain additionally requires the full covariance
 matrix to be PSD or PD; symbolic negative correlations are interpreted
 probabilistically only when those spectral conditions hold.
 Proof/definition method: Derive from the single shared score-total
 conservation identity or canonical Schur eigenvalue and predictor
 identities using Stdlib ring, field and real-order proofs. Distinct
 refinements cover equality, inequality and singular-boundary cases.
 Library reuse: SequentialReport, UnequalHistoryLinearPrediction,
 GaussianInnovationBounds, GaussianCovarianceDomain and Stdlib.
 Boundary: Deterministic regression and covariance statements;
 no measure-theoretic conditional expectation or population-IQ
 distribution is established by these arithmetic identities.
*)
Theorem gbb_expected_total_strict_history_order : forall n k c s t:R, 1<=n -> 0<k -> 0<sequential_d (n+k) c -> s<t -> ht n k c s<ht n k c t.
Proof.
 intros n k c s t Hn Hk Hfull Hst.
 assert (Hd:0<sequential_d n c)
  by (apply (gib_observed_denominator_positive_given_full_pd n k c); assumption).
 rewrite (gbb_total_ratio n k c s) by lra.
 rewrite (gbb_total_ratio n k c t) by lra.
 apply Rmult_lt_compat_l; [apply gbb_total_gain_positive_on_full_pd; assumption|exact Hst].
Qed.

(** [gbb_expected_total_weak_history_order] (theorem).
 Mathematical meaning: Nonnegative full eigenvalue enforces weak monotonicity of the predicted total across observed score sums.
 Exact checked proposition: forall n k c s t:R, 1<=n -> 0<k -> 0<=sequential_d (n+k) c -> s<=t -> ht n k c s<=ht n k c t.
 Premises and side conditions: Every theorem states its denominator,
 sample-size and covariance-domain requirements. The proper signed
 Gaussian covariance domain additionally requires the full covariance
 matrix to be PSD or PD; symbolic negative correlations are interpreted
 probabilistically only when those spectral conditions hold.
 Proof/definition method: Derive from the single shared score-total
 conservation identity or canonical Schur eigenvalue and predictor
 identities using Stdlib ring, field and real-order proofs. Distinct
 refinements cover equality, inequality and singular-boundary cases.
 Library reuse: SequentialReport, UnequalHistoryLinearPrediction,
 GaussianInnovationBounds, GaussianCovarianceDomain and Stdlib.
 Boundary: Deterministic regression and covariance statements;
 no measure-theoretic conditional expectation or population-IQ
 distribution is established by these arithmetic identities.
*)
Theorem gbb_expected_total_weak_history_order : forall n k c s t:R, 1<=n -> 0<k -> 0<=sequential_d (n+k) c -> s<=t -> ht n k c s<=ht n k c t.
Proof.
 intros n k c s t Hn Hk Hfull Hst.
 assert (Hd:0<sequential_d n c)
  by (apply (gib_observed_denominator_positive_given_full_psd n k c); assumption).
 rewrite (gbb_total_ratio n k c s) by lra.
 rewrite (gbb_total_ratio n k c t) by lra.
 apply Rmult_le_compat_l; [apply gbb_total_gain_nonnegative_on_full_psd; assumption|exact Hst].
Qed.

(** [gbb_expected_total_zero_iff_zero_history_full_pd] (theorem).
 Mathematical meaning: In the strict covariance domain, the predicted battery total is zero precisely when the observed-history sum is zero.
 Exact checked proposition: forall n k c s:R, 1<=n -> 0<k -> 0<sequential_d (n+k) c -> (ht n k c s=0 <-> s=0).
 Premises and side conditions: Every theorem states its denominator,
 sample-size and covariance-domain requirements. The proper signed
 Gaussian covariance domain additionally requires the full covariance
 matrix to be PSD or PD; symbolic negative correlations are interpreted
 probabilistically only when those spectral conditions hold.
 Proof/definition method: Derive from the single shared score-total
 conservation identity or canonical Schur eigenvalue and predictor
 identities using Stdlib ring, field and real-order proofs. Distinct
 refinements cover equality, inequality and singular-boundary cases.
 Library reuse: SequentialReport, UnequalHistoryLinearPrediction,
 GaussianInnovationBounds, GaussianCovarianceDomain and Stdlib.
 Boundary: Deterministic regression and covariance statements;
 no measure-theoretic conditional expectation or population-IQ
 distribution is established by these arithmetic identities.
*)
Theorem gbb_expected_total_zero_iff_zero_history_full_pd : forall n k c s:R, 1<=n -> 0<k -> 0<sequential_d (n+k) c -> (ht n k c s=0 <-> s=0).
Proof.
 intros n k c s Hn Hk Hfull.
 assert (Hd:0<sequential_d n c)
  by (apply (gib_observed_denominator_positive_given_full_pd n k c); assumption).
 rewrite gbb_total_ratio by lra.
 pose proof (gbb_total_gain_positive_on_full_pd n k c Hn Hk Hfull) as Hgain.
 split; intro H; nra.
Qed.

(** [gbb_gain_above_one_positive_correlation] (theorem).
 Mathematical meaning: Adding future tests strictly expands the predicted total-versus-history gain when the common correlation is strictly positive.
 Exact checked proposition: forall n k c:R, 0<k -> 0<c -> 0<sequential_d n c -> 1<sequential_d (n+k) c/sequential_d n c.
 Premises and side conditions: Every theorem states its denominator,
 sample-size and covariance-domain requirements. The proper signed
 Gaussian covariance domain additionally requires the full covariance
 matrix to be PSD or PD; symbolic negative correlations are interpreted
 probabilistically only when those spectral conditions hold.
 Proof/definition method: Derive from the single shared score-total
 conservation identity or canonical Schur eigenvalue and predictor
 identities using Stdlib ring, field and real-order proofs. Distinct
 refinements cover equality, inequality and singular-boundary cases.
 Library reuse: SequentialReport, UnequalHistoryLinearPrediction,
 GaussianInnovationBounds, GaussianCovarianceDomain and Stdlib.
 Boundary: Deterministic regression and covariance statements;
 no measure-theoretic conditional expectation or population-IQ
 distribution is established by these arithmetic identities.
*)
Theorem gbb_gain_above_one_positive_correlation : forall n k c:R, 0<k -> 0<c -> 0<sequential_d n c -> 1<sequential_d (n+k) c/sequential_d n c.
Proof.
 intros n k c Hk Hc Hd.
 pose proof (gbb_ratio_gain_difference n k c (Rgt_not_eq _ _ Hd)) as Hdiff.
 assert (Hkc:0<k*c) by nra.
 assert (Hratio:0<k*c/sequential_d n c).
 { unfold Rdiv; apply Rmult_lt_0_compat; [exact Hkc|].
   apply Rinv_0_lt_compat; exact Hd. }
 lra.
Qed.

(** [gbb_gain_below_one_negative_correlation] (theorem).
 Mathematical meaning: Adding future tests reduces the full-battery gain below one at negative correlation and positive observed-block denominator.
 Exact checked proposition: forall n k c:R, 0<k -> c<0 -> 0<sequential_d n c -> sequential_d (n+k) c/sequential_d n c<1.
 Premises and side conditions: Every theorem states its denominator,
 sample-size and covariance-domain requirements. The proper signed
 Gaussian covariance domain additionally requires the full covariance
 matrix to be PSD or PD; symbolic negative correlations are interpreted
 probabilistically only when those spectral conditions hold.
 Proof/definition method: Derive from the single shared score-total
 conservation identity or canonical Schur eigenvalue and predictor
 identities using Stdlib ring, field and real-order proofs. Distinct
 refinements cover equality, inequality and singular-boundary cases.
 Library reuse: SequentialReport, UnequalHistoryLinearPrediction,
 GaussianInnovationBounds, GaussianCovarianceDomain and Stdlib.
 Boundary: Deterministic regression and covariance statements;
 no measure-theoretic conditional expectation or population-IQ
 distribution is established by these arithmetic identities.
*)
Theorem gbb_gain_below_one_negative_correlation : forall n k c:R, 0<k -> c<0 -> 0<sequential_d n c -> sequential_d (n+k) c/sequential_d n c<1.
Proof.
 intros n k c Hk Hc Hd.
 pose proof (gbb_ratio_gain_difference n k c (Rgt_not_eq _ _ Hd)) as Hdiff.
 assert (Hkc:k*c<0) by nra.
 assert (Hratio:k*c/sequential_d n c<0).
 { unfold Rdiv.
   replace 0 with (0 * /sequential_d n c) by ring.
   apply Rmult_lt_compat_r; [apply Rinv_0_lt_compat; exact Hd|exact Hkc]. }
 lra.
Qed.

(** [gbb_gain_one_zero_correlation] (theorem).
 Mathematical meaning: At zero equicorrelation the full-to-observed common-mode scaling ratio is exactly one.
 Exact checked proposition: forall n k:R, sequential_d (n+k) 0/sequential_d n 0=1.
 Premises and side conditions: Every theorem states its denominator,
 sample-size and covariance-domain requirements. The proper signed
 Gaussian covariance domain additionally requires the full covariance
 matrix to be PSD or PD; symbolic negative correlations are interpreted
 probabilistically only when those spectral conditions hold.
 Proof/definition method: Derive from the single shared score-total
 conservation identity or canonical Schur eigenvalue and predictor
 identities using Stdlib ring, field and real-order proofs. Distinct
 refinements cover equality, inequality and singular-boundary cases.
 Library reuse: SequentialReport, UnequalHistoryLinearPrediction,
 GaussianInnovationBounds, GaussianCovarianceDomain and Stdlib.
 Boundary: Deterministic regression and covariance statements;
 no measure-theoretic conditional expectation or population-IQ
 distribution is established by these arithmetic identities.
*)
Theorem gbb_gain_one_zero_correlation : forall n k:R, sequential_d (n+k) 0/sequential_d n 0=1.
Proof.
 intros n k.
 repeat rewrite sequential_denominator_at_zero_correlation.
 field.
Qed.

(** [gbb_gain_at_perfect_correlation] (theorem).
 Mathematical meaning: At perfect correlation the full-to-observed eigenvalue ratio equals the full-to-observed number of scores.
 Exact checked proposition: forall n k:R, 0<n -> sequential_d (n+k) 1/sequential_d n 1=(n+k)/n.
 Premises and side conditions: Every theorem states its denominator,
 sample-size and covariance-domain requirements. The proper signed
 Gaussian covariance domain additionally requires the full covariance
 matrix to be PSD or PD; symbolic negative correlations are interpreted
 probabilistically only when those spectral conditions hold.
 Proof/definition method: Derive from the single shared score-total
 conservation identity or canonical Schur eigenvalue and predictor
 identities using Stdlib ring, field and real-order proofs. Distinct
 refinements cover equality, inequality and singular-boundary cases.
 Library reuse: SequentialReport, UnequalHistoryLinearPrediction,
 GaussianInnovationBounds, GaussianCovarianceDomain and Stdlib.
 Boundary: Deterministic regression and covariance statements;
 no measure-theoretic conditional expectation or population-IQ
 distribution is established by these arithmetic identities.
*)
Theorem gbb_gain_at_perfect_correlation : forall n k:R, 0<n -> sequential_d (n+k) 1/sequential_d n 1=(n+k)/n.
Proof.
 intros n k Hn.
 repeat rewrite sequential_denominator_at_unit_correlation.
 reflexivity.
Qed.

(** [gbb_expected_total_above_history_positive_correlation] (theorem).
 Mathematical meaning: With positive correlation, a positive observed history sum yields a strictly larger observed-plus-predicted total.
 Exact checked proposition: forall n k c s:R, 1<=n -> 0<k -> 0<c -> 0<s -> s<ht n k c s.
 Premises and side conditions: Every theorem states its denominator,
 sample-size and covariance-domain requirements. The proper signed
 Gaussian covariance domain additionally requires the full covariance
 matrix to be PSD or PD; symbolic negative correlations are interpreted
 probabilistically only when those spectral conditions hold.
 Proof/definition method: Derive from the single shared score-total
 conservation identity or canonical Schur eigenvalue and predictor
 identities using Stdlib ring, field and real-order proofs. Distinct
 refinements cover equality, inequality and singular-boundary cases.
 Library reuse: SequentialReport, UnequalHistoryLinearPrediction,
 GaussianInnovationBounds, GaussianCovarianceDomain and Stdlib.
 Boundary: Deterministic regression and covariance statements;
 no measure-theoretic conditional expectation or population-IQ
 distribution is established by these arithmetic identities.
*)
Theorem gbb_expected_total_above_history_positive_correlation : forall n k c s:R, 1<=n -> 0<k -> 0<c -> 0<s -> s<ht n k c s.
Proof.
 intros n k c s Hn Hk Hc Hs.
 assert (Hd:0<sequential_d n c)
   by (apply sequential_denominator_positive_nonnegative_correlation; lra).
 pose proof (d052_mean_positive_gain n c s Hc Hd Hs) as Hp.
 unfold ht,hf; nra.
Qed.

(** [gbb_expected_total_below_history_negative_correlation] (theorem).
 Mathematical meaning: With negative common correlation, a positive observed sum decreases after adding the predicted future scores.
 Exact checked proposition: forall n k c s:R, 0<k -> c<0 -> 0<sequential_d n c -> 0<s -> ht n k c s<s.
 Premises and side conditions: Every theorem states its denominator,
 sample-size and covariance-domain requirements. The proper signed
 Gaussian covariance domain additionally requires the full covariance
 matrix to be PSD or PD; symbolic negative correlations are interpreted
 probabilistically only when those spectral conditions hold.
 Proof/definition method: Derive from the single shared score-total
 conservation identity or canonical Schur eigenvalue and predictor
 identities using Stdlib ring, field and real-order proofs. Distinct
 refinements cover equality, inequality and singular-boundary cases.
 Library reuse: SequentialReport, UnequalHistoryLinearPrediction,
 GaussianInnovationBounds, GaussianCovarianceDomain and Stdlib.
 Boundary: Deterministic regression and covariance statements;
 no measure-theoretic conditional expectation or population-IQ
 distribution is established by these arithmetic identities.
*)
Theorem gbb_expected_total_below_history_negative_correlation : forall n k c s:R, 0<k -> c<0 -> 0<sequential_d n c -> 0<s -> ht n k c s<s.
Proof.
 intros n k c s Hk Hc Hd Hs.
 pose proof (gib_signed_negative_predictor_positive_history n c s Hc Hd Hs) as Hp.
 unfold ht,hf; nra.
Qed.

(** [gbb_expected_total_between_zero_and_history_negative_psd] (theorem).
 Mathematical meaning: In the feasible negative-correlation domain the predicted full total from a positive history lies between zero and the observed sum.
 Exact checked proposition: forall n k c s:R, 1<=n -> 0<k -> c<0 -> 0<=sequential_d (n+k) c -> 0<s -> 0<=ht n k c s /\ ht n k c s<s.
 Premises and side conditions: Every theorem states its denominator,
 sample-size and covariance-domain requirements. The proper signed
 Gaussian covariance domain additionally requires the full covariance
 matrix to be PSD or PD; symbolic negative correlations are interpreted
 probabilistically only when those spectral conditions hold.
 Proof/definition method: Derive from the single shared score-total
 conservation identity or canonical Schur eigenvalue and predictor
 identities using Stdlib ring, field and real-order proofs. Distinct
 refinements cover equality, inequality and singular-boundary cases.
 Library reuse: SequentialReport, UnequalHistoryLinearPrediction,
 GaussianInnovationBounds, GaussianCovarianceDomain and Stdlib.
 Boundary: Deterministic regression and covariance statements;
 no measure-theoretic conditional expectation or population-IQ
 distribution is established by these arithmetic identities.
*)
Theorem gbb_expected_total_between_zero_and_history_negative_psd : forall n k c s:R, 1<=n -> 0<k -> c<0 -> 0<=sequential_d (n+k) c -> 0<s -> 0<=ht n k c s /\ ht n k c s<s.
Proof.
 intros n k c s Hn Hk Hc Hfull Hs.
 assert (Hd:0<sequential_d n c)
   by (apply (gib_observed_denominator_positive_given_full_psd n k c); assumption).
 split.
 - apply gbb_expected_total_nonnegative_full_psd; try assumption; lra.
 - apply gbb_expected_total_below_history_negative_correlation; assumption.
Qed.

(** [gbb_expected_total_strictly_between_zero_and_history_negative_pd] (theorem).
 Mathematical meaning: For negative correlation and strict positive-definite covariance, a positive observed sum yields a strictly intermediate predicted total.
 Exact checked proposition: forall n k c s:R, 1<=n -> 0<k -> c<0 -> 0<sequential_d (n+k) c -> 0<s -> 0<ht n k c s /\ ht n k c s<s.
 Premises and side conditions: Every theorem states its denominator,
 sample-size and covariance-domain requirements. The proper signed
 Gaussian covariance domain additionally requires the full covariance
 matrix to be PSD or PD; symbolic negative correlations are interpreted
 probabilistically only when those spectral conditions hold.
 Proof/definition method: Derive from the single shared score-total
 conservation identity or canonical Schur eigenvalue and predictor
 identities using Stdlib ring, field and real-order proofs. Distinct
 refinements cover equality, inequality and singular-boundary cases.
 Library reuse: SequentialReport, UnequalHistoryLinearPrediction,
 GaussianInnovationBounds, GaussianCovarianceDomain and Stdlib.
 Boundary: Deterministic regression and covariance statements;
 no measure-theoretic conditional expectation or population-IQ
 distribution is established by these arithmetic identities.
*)
Theorem gbb_expected_total_strictly_between_zero_and_history_negative_pd : forall n k c s:R, 1<=n -> 0<k -> c<0 -> 0<sequential_d (n+k) c -> 0<s -> 0<ht n k c s /\ ht n k c s<s.
Proof.
 intros n k c s Hn Hk Hc Hfull Hs.
 assert (Hd:0<sequential_d n c)
   by (apply (gib_observed_denominator_positive_given_full_pd n k c); assumption).
 split.
 - apply gbb_expected_total_positive_full_pd; assumption.
 - apply gbb_expected_total_below_history_negative_correlation; assumption.
Qed.

(** [gbb_expected_total_negative_between_history_and_zero_negative_pd] (theorem).
 Mathematical meaning: At negative correlation, a negative history sum is attenuated toward zero, while its predicted full total remains strictly negative.
 Exact checked proposition: forall n k c s:R, 1<=n -> 0<k -> c<0 -> 0<sequential_d (n+k) c -> s<0 -> s<ht n k c s /\ ht n k c s<0.
 Premises and side conditions: Every theorem states its denominator,
 sample-size and covariance-domain requirements. The proper signed
 Gaussian covariance domain additionally requires the full covariance
 matrix to be PSD or PD; symbolic negative correlations are interpreted
 probabilistically only when those spectral conditions hold.
 Proof/definition method: Derive from the single shared score-total
 conservation identity or canonical Schur eigenvalue and predictor
 identities using Stdlib ring, field and real-order proofs. Distinct
 refinements cover equality, inequality and singular-boundary cases.
 Library reuse: SequentialReport, UnequalHistoryLinearPrediction,
 GaussianInnovationBounds, GaussianCovarianceDomain and Stdlib.
 Boundary: Deterministic regression and covariance statements;
 no measure-theoretic conditional expectation or population-IQ
 distribution is established by these arithmetic identities.
*)
Theorem gbb_expected_total_negative_between_history_and_zero_negative_pd : forall n k c s:R, 1<=n -> 0<k -> c<0 -> 0<sequential_d (n+k) c -> s<0 -> s<ht n k c s /\ ht n k c s<0.
Proof.
 intros n k c s Hn Hk Hc Hfull Hs.
 assert (Hd:0<sequential_d n c)
   by (apply (gib_observed_denominator_positive_given_full_pd n k c); assumption).
 pose proof (gib_signed_negative_predictor_negative_history n c s Hc Hd Hs) as Hp.
 split.
 - unfold ht,hf; nra.
 - apply gbb_expected_total_negative_full_pd; assumption.
Qed.

(** [gbb_future_sum_negative_negative_corr_positive_history] (theorem).
 Mathematical meaning: At signed negative correlation, a positive observed sum predicts a negative sum across any positively sized future batch.
 Exact checked proposition: forall n k c s:R, 0<k -> c<0 -> 0<sequential_d n c -> 0<s -> hf n k c s<0.
 Premises and side conditions: Every theorem states its denominator,
 sample-size and covariance-domain requirements. The proper signed
 Gaussian covariance domain additionally requires the full covariance
 matrix to be PSD or PD; symbolic negative correlations are interpreted
 probabilistically only when those spectral conditions hold.
 Proof/definition method: Derive from the single shared score-total
 conservation identity or canonical Schur eigenvalue and predictor
 identities using Stdlib ring, field and real-order proofs. Distinct
 refinements cover equality, inequality and singular-boundary cases.
 Library reuse: SequentialReport, UnequalHistoryLinearPrediction,
 GaussianInnovationBounds, GaussianCovarianceDomain and Stdlib.
 Boundary: Deterministic regression and covariance statements;
 no measure-theoretic conditional expectation or population-IQ
 distribution is established by these arithmetic identities.
*)
Theorem gbb_future_sum_negative_negative_corr_positive_history : forall n k c s:R, 0<k -> c<0 -> 0<sequential_d n c -> 0<s -> hf n k c s<0.
Proof.
 intros n k c s Hk Hc Hd Hs.
 pose proof (gib_signed_negative_predictor_positive_history n c s Hc Hd Hs) as Hp.
 unfold hf; nra.
Qed.

(** [gbb_future_sum_positive_negative_corr_negative_history] (theorem).
 Mathematical meaning: At signed negative correlation, a negative observed sum predicts a positive sum across any positively sized future batch.
 Exact checked proposition: forall n k c s:R, 0<k -> c<0 -> 0<sequential_d n c -> s<0 -> 0<hf n k c s.
 Premises and side conditions: Every theorem states its denominator,
 sample-size and covariance-domain requirements. The proper signed
 Gaussian covariance domain additionally requires the full covariance
 matrix to be PSD or PD; symbolic negative correlations are interpreted
 probabilistically only when those spectral conditions hold.
 Proof/definition method: Derive from the single shared score-total
 conservation identity or canonical Schur eigenvalue and predictor
 identities using Stdlib ring, field and real-order proofs. Distinct
 refinements cover equality, inequality and singular-boundary cases.
 Library reuse: SequentialReport, UnequalHistoryLinearPrediction,
 GaussianInnovationBounds, GaussianCovarianceDomain and Stdlib.
 Boundary: Deterministic regression and covariance statements;
 no measure-theoretic conditional expectation or population-IQ
 distribution is established by these arithmetic identities.
*)
Theorem gbb_future_sum_positive_negative_corr_negative_history : forall n k c s:R, 0<k -> c<0 -> 0<sequential_d n c -> s<0 -> 0<hf n k c s.
Proof.
 intros n k c s Hk Hc Hd Hs.
 pose proof (gib_signed_negative_predictor_negative_history n c s Hc Hd Hs) as Hp.
 unfold hf; nra.
Qed.

(** [gbb_inclusive_mean_ratio] (theorem).
 Mathematical meaning: The predicted inclusive mean is the full-to-observed covariance eigenvalue ratio times the history sum divided by full battery size.
 Exact checked proposition: forall n k c s:R, sequential_d n c<>0 -> n+k<>0 -> hm n k c s=sequential_d (n+k) c*s/(sequential_d n c*(n+k)).
 Premises and side conditions: Every theorem states its denominator,
 sample-size and covariance-domain requirements. The proper signed
 Gaussian covariance domain additionally requires the full covariance
 matrix to be PSD or PD; symbolic negative correlations are interpreted
 probabilistically only when those spectral conditions hold.
 Proof/definition method: Derive from the single shared score-total
 conservation identity or canonical Schur eigenvalue and predictor
 identities using Stdlib ring, field and real-order proofs. Distinct
 refinements cover equality, inequality and singular-boundary cases.
 Library reuse: SequentialReport, UnequalHistoryLinearPrediction,
 GaussianInnovationBounds, GaussianCovarianceDomain and Stdlib.
 Boundary: Deterministic regression and covariance statements;
 no measure-theoretic conditional expectation or population-IQ
 distribution is established by these arithmetic identities.
*)
Theorem gbb_inclusive_mean_ratio : forall n k c s:R, sequential_d n c<>0 -> n+k<>0 -> hm n k c s=sequential_d (n+k) c*s/(sequential_d n c*(n+k)).
Proof.
 intros n k c s Hd Hsize.
 unfold hm.
 rewrite gbb_total_ratio by assumption.
 field; assumption.
Qed.

(** [gbb_inclusive_mean_nonnegative_full_psd] (theorem).
 Mathematical meaning: When the observed sum is nonnegative, full PSD covariance feasibility ensures a nonnegative inclusive predicted mean.
 Exact checked proposition: forall n k c s:R, 1<=n -> 0<k -> 0<=sequential_d (n+k) c -> 0<=s -> 0<=hm n k c s.
 Premises and side conditions: Every theorem states its denominator,
 sample-size and covariance-domain requirements. The proper signed
 Gaussian covariance domain additionally requires the full covariance
 matrix to be PSD or PD; symbolic negative correlations are interpreted
 probabilistically only when those spectral conditions hold.
 Proof/definition method: Derive from the single shared score-total
 conservation identity or canonical Schur eigenvalue and predictor
 identities using Stdlib ring, field and real-order proofs. Distinct
 refinements cover equality, inequality and singular-boundary cases.
 Library reuse: SequentialReport, UnequalHistoryLinearPrediction,
 GaussianInnovationBounds, GaussianCovarianceDomain and Stdlib.
 Boundary: Deterministic regression and covariance statements;
 no measure-theoretic conditional expectation or population-IQ
 distribution is established by these arithmetic identities.
*)
Theorem gbb_inclusive_mean_nonnegative_full_psd : forall n k c s:R, 1<=n -> 0<k -> 0<=sequential_d (n+k) c -> 0<=s -> 0<=hm n k c s.
Proof.
 intros n k c s Hn Hk Hfull Hs.
 unfold hm,Rdiv.
 apply Rmult_le_pos.
 - apply gbb_expected_total_nonnegative_full_psd; assumption.
 - left; apply Rinv_0_lt_compat; lra.
Qed.

(** [gbb_inclusive_mean_positive_full_pd] (theorem).
 Mathematical meaning: A positive observed sum under a strictly PD full covariance yields a strictly positive inclusive predicted mean.
 Exact checked proposition: forall n k c s:R, 1<=n -> 0<k -> 0<sequential_d (n+k) c -> 0<s -> 0<hm n k c s.
 Premises and side conditions: Every theorem states its denominator,
 sample-size and covariance-domain requirements. The proper signed
 Gaussian covariance domain additionally requires the full covariance
 matrix to be PSD or PD; symbolic negative correlations are interpreted
 probabilistically only when those spectral conditions hold.
 Proof/definition method: Derive from the single shared score-total
 conservation identity or canonical Schur eigenvalue and predictor
 identities using Stdlib ring, field and real-order proofs. Distinct
 refinements cover equality, inequality and singular-boundary cases.
 Library reuse: SequentialReport, UnequalHistoryLinearPrediction,
 GaussianInnovationBounds, GaussianCovarianceDomain and Stdlib.
 Boundary: Deterministic regression and covariance statements;
 no measure-theoretic conditional expectation or population-IQ
 distribution is established by these arithmetic identities.
*)
Theorem gbb_inclusive_mean_positive_full_pd : forall n k c s:R, 1<=n -> 0<k -> 0<sequential_d (n+k) c -> 0<s -> 0<hm n k c s.
Proof.
 intros n k c s Hn Hk Hfull Hs.
 unfold hm,Rdiv.
 apply Rmult_lt_0_compat.
 - apply gbb_expected_total_positive_full_pd; assumption.
 - apply Rinv_0_lt_compat; lra.
Qed.

(** [gbb_inclusive_mean_at_perfect_correlation] (theorem).
 Mathematical meaning: At perfect correlation the predicted inclusive score mean equals the mean of the initial observations, independent of how many additional tests are predicted.
 Exact checked proposition: forall n k s:R, 0<n -> 0<k -> hm n k 1 s=s/n.
 Premises and side conditions: Every theorem states its denominator,
 sample-size and covariance-domain requirements. The proper signed
 Gaussian covariance domain additionally requires the full covariance
 matrix to be PSD or PD; symbolic negative correlations are interpreted
 probabilistically only when those spectral conditions hold.
 Proof/definition method: Derive from the single shared score-total
 conservation identity or canonical Schur eigenvalue and predictor
 identities using Stdlib ring, field and real-order proofs. Distinct
 refinements cover equality, inequality and singular-boundary cases.
 Library reuse: SequentialReport, UnequalHistoryLinearPrediction,
 GaussianInnovationBounds, GaussianCovarianceDomain and Stdlib.
 Boundary: Deterministic regression and covariance statements;
 no measure-theoretic conditional expectation or population-IQ
 distribution is established by these arithmetic identities.
*)
Theorem gbb_inclusive_mean_at_perfect_correlation : forall n k s:R, 0<n -> 0<k -> hm n k 1 s=s/n.
Proof.
 intros n k s Hn Hk.
 unfold hm,ht,hf,hp.
 rewrite sequential_denominator_at_unit_correlation.
 field; lra.
Qed.

