(** Module: GaussianCovarianceDomain.v
 Purpose: Extend equicorrelated Gaussian-model covariance feasibility to
 conditional Schur residuals for strictly positive and NEGATIVE correlations.
 Mathematical representation: A block of r observed scores and k future
 scores has total equicorrelation d_{r+k}(c). The future conditional
 covariance Schur form has contrast eigenvalue 1-c and common eigenvalue
 (1-c)*d_{r+k}(c)/d_r(c), with exact finite-list consequences.
 Explicit hypotheses: r and k are positive scalar score counts, the
 observed block has d_r(c)>0, and the full covariance block has c<=1
 and d_{r+k}(c)>=0. Positive definiteness requires strict inequalities.
 Library use: Rocq Stdlib Reals/Field/Ring/Lra/Psatz and the canonical
 EquicorrelationSpectral/EquicorrelationVectors Cauchy-Schwarz bounds.
 No custom matrix arithmetic, summation, probability measure or new axioms.
 Limitations: Exact covariance feasibility and conditional Schur algebra
 are NECESSARY for Gaussian conditioning; a measure-theoretic
 normal-distribution/conditional-expectation theorem remains separate.
 Reproduction: scripts/compile_rocq.sh with pinned Rocq 9.2 and full
 strict theorem-level explanatory/source-order audit.
 AI disclosure: AI-assisted statement design, candidate proofs and comments;
 only exact kernel-accepted propositions count as checked.
*)
From Stdlib Require Import Reals Lra Psatz Ring Field List.
Require Import SequentialReport EquicorrelationSpectral EquicorrelationVectors
  UnequalHistoryLinearPrediction.
Open Scope R_scope.

(** [gcd_common_mode_eigenvalue] (theorem).
 Mathematical meaning: The future residual covariance's all-ones eigenvalue is the ratio of the full-battery and observed-battery common eigenvalues.
 Exact checked proposition: forall r k c, sequential_d r c<>0 -> (1-c)+k*c*(1-c)/sequential_d r c = (1-c)*sequential_d (r+k) c/sequential_d r c.
 Premises and side conditions: Future length k is strictly positive and
 the observed covariance d_r(c) is invertible. The admissible full
 equicorrelation domain uses c<=1 and d_(r+k)(c)>=0; strict positivity
 has the corresponding strict assumptions. Negative c is allowed.
 Proof/definition method: Reuse the canonical Schur factorization and
 finite-vector Cauchy-Schwarz, normalize rational expressions with Field,
 then use order algebra. No independent matrix or probability implementation.
 Library reuse: Rocq Stdlib Reals, Lra, Psatz, Ring, Field; existing
 EquicorrelationSpectral and EquicorrelationVectors theorems.
 Boundary: These are exact finite covariance and Schur-complement
 feasibility statements, not an independent normal-distribution or
 conditional-expectation theorem or psychometric observation.
*)
Theorem gcd_common_mode_eigenvalue : forall r k c, sequential_d r c<>0 ->
 (1-c)+k*c*(1-c)/sequential_d r c =
 (1-c)*sequential_d (r+k) c/sequential_d r c.
Proof.
 intros r k c Hr; unfold sequential_d in *; field; nra.
Qed.

(** [gcd_common_mode_sign] (theorem).
 Mathematical meaning: A full-battery PSD equicorrelation domain implies nonnegative conditional common-mode variance, including negative correlations.
 Exact checked proposition: forall r k c, c<=1 -> 0<sequential_d r c -> 0<=sequential_d (r+k) c -> 0<=(1-c)*sequential_d (r+k) c/sequential_d r c.
 Premises and side conditions: Future length k is strictly positive and
 the observed covariance d_r(c) is invertible. The admissible full
 equicorrelation domain uses c<=1 and d_(r+k)(c)>=0; strict positivity
 has the corresponding strict assumptions. Negative c is allowed.
 Proof/definition method: Reuse the canonical Schur factorization and
 finite-vector Cauchy-Schwarz, normalize rational expressions with Field,
 then use order algebra. No independent matrix or probability implementation.
 Library reuse: Rocq Stdlib Reals, Lra, Psatz, Ring, Field; existing
 EquicorrelationSpectral and EquicorrelationVectors theorems.
 Boundary: These are exact finite covariance and Schur-complement
 feasibility statements, not an independent normal-distribution or
 conditional-expectation theorem or psychometric observation.
*)
Theorem gcd_common_mode_sign : forall r k c, c<=1 -> 0<sequential_d r c -> 0<=sequential_d (r+k) c ->
 0<=(1-c)*sequential_d (r+k) c/sequential_d r c.
Proof.
 intros r k c Hc Hr Ht; unfold Rdiv; apply Rmult_le_pos; [nra|left; apply Rinv_0_lt_compat; nra].
Qed.

(** [gcd_common_mode_strict] (theorem).
 Mathematical meaning: Strict full-battery positivity implies strict conditional common-mode variance.
 Exact checked proposition: forall r k c, c<1 -> 0<sequential_d r c -> 0<sequential_d (r+k) c -> 0<(1-c)*sequential_d (r+k) c/sequential_d r c.
 Premises and side conditions: Future length k is strictly positive and
 the observed covariance d_r(c) is invertible. The admissible full
 equicorrelation domain uses c<=1 and d_(r+k)(c)>=0; strict positivity
 has the corresponding strict assumptions. Negative c is allowed.
 Proof/definition method: Reuse the canonical Schur factorization and
 finite-vector Cauchy-Schwarz, normalize rational expressions with Field,
 then use order algebra. No independent matrix or probability implementation.
 Library reuse: Rocq Stdlib Reals, Lra, Psatz, Ring, Field; existing
 EquicorrelationSpectral and EquicorrelationVectors theorems.
 Boundary: These are exact finite covariance and Schur-complement
 feasibility statements, not an independent normal-distribution or
 conditional-expectation theorem or psychometric observation.
*)
Theorem gcd_common_mode_strict : forall r k c, c<1 -> 0<sequential_d r c -> 0<sequential_d (r+k) c ->
 0<(1-c)*sequential_d (r+k) c/sequential_d r c.
Proof.
 intros r k c Hc Hr Ht; unfold Rdiv; apply Rmult_lt_0_compat; [nra|apply Rinv_0_lt_compat; nra].
Qed.

(** [gcd_schur_decomposition] (theorem).
 Mathematical meaning: The exact conditional Schur quadratic splits into orthogonal future-score contrast and common-score components.
 Exact checked proposition: forall r k c energy total, 0<k -> sequential_d r c<>0 -> equicorr_schur_energy r c energy total = (1-c)*(energy-total*total/k) + ((1-c)*sequential_d (r+k) c/sequential_d r c)*(total*total/k).
 Premises and side conditions: Future length k is strictly positive and
 the observed covariance d_r(c) is invertible. The admissible full
 equicorrelation domain uses c<=1 and d_(r+k)(c)>=0; strict positivity
 has the corresponding strict assumptions. Negative c is allowed.
 Proof/definition method: Reuse the canonical Schur factorization and
 finite-vector Cauchy-Schwarz, normalize rational expressions with Field,
 then use order algebra. No independent matrix or probability implementation.
 Library reuse: Rocq Stdlib Reals, Lra, Psatz, Ring, Field; existing
 EquicorrelationSpectral and EquicorrelationVectors theorems.
 Boundary: These are exact finite covariance and Schur-complement
 feasibility statements, not an independent normal-distribution or
 conditional-expectation theorem or psychometric observation.
*)
Theorem gcd_schur_decomposition : forall r k c energy total, 0<k -> sequential_d r c<>0 ->
 equicorr_schur_energy r c energy total =
 (1-c)*(energy-total*total/k) +
 ((1-c)*sequential_d (r+k) c/sequential_d r c)*(total*total/k).
Proof.
 intros r k c energy total Hk Hr;
 rewrite equicorr_schur_energy_factorization by assumption;
 unfold sequential_d in *; field; nra.
Qed.

(** [gcd_schur_psd_arbitrary_sign] (theorem).
 Mathematical meaning: Nonnegative finite conditional covariance holds throughout the *entire* admissible negative-to-positive equicorrelation interval, not only c>=0.
 Exact checked proposition: forall r k c energy total, 0<k -> c<=1 -> 0<sequential_d r c -> 0<=sequential_d (r+k) c -> 0<=energy-total*total/k -> 0<=equicorr_schur_energy r c energy total.
 Premises and side conditions: Future length k is strictly positive and
 the observed covariance d_r(c) is invertible. The admissible full
 equicorrelation domain uses c<=1 and d_(r+k)(c)>=0; strict positivity
 has the corresponding strict assumptions. Negative c is allowed.
 Proof/definition method: Reuse the canonical Schur factorization and
 finite-vector Cauchy-Schwarz, normalize rational expressions with Field,
 then use order algebra. No independent matrix or probability implementation.
 Library reuse: Rocq Stdlib Reals, Lra, Psatz, Ring, Field; existing
 EquicorrelationSpectral and EquicorrelationVectors theorems.
 Boundary: These are exact finite covariance and Schur-complement
 feasibility statements, not an independent normal-distribution or
 conditional-expectation theorem or psychometric observation.
*)
Theorem gcd_schur_psd_arbitrary_sign : forall r k c energy total, 0<k -> c<=1 ->
 0<sequential_d r c -> 0<=sequential_d (r+k) c ->
 0<=energy-total*total/k -> 0<=equicorr_schur_energy r c energy total.
Proof.
 intros r k c energy total Hk Hc Hr Ht Hfeasible.
 assert (Hnz : sequential_d r c <> 0) by lra.
 rewrite (gcd_schur_decomposition r k c energy total Hk Hnz).
 assert (Hsquare:0<=total*total/k).
 { unfold Rdiv; apply Rmult_le_pos.
   - apply Rle_0_sqr.
   - left; apply Rinv_0_lt_compat; lra. }
 assert (Hfactor:0<=(1-c)*sequential_d (r+k) c/sequential_d r c)
 by (apply (gcd_common_mode_sign r k c); assumption).
 apply Rplus_le_le_0_compat; apply Rmult_le_pos; nra.
Qed.

(** [gcd_schur_pd_arbitrary_sign] (theorem).
 Mathematical meaning: Under strict full-battery covariance feasibility, every nonzero feasible future vector has strictly positive conditional covariance energy.
 Exact checked proposition: forall r k c energy total, 0<k -> c<1 -> 0<sequential_d r c -> 0<sequential_d (r+k) c -> 0<energy -> 0<=energy-total*total/k -> 0<equicorr_schur_energy r c energy total.
 Premises and side conditions: Future length k is strictly positive and
 the observed covariance d_r(c) is invertible. The admissible full
 equicorrelation domain uses c<=1 and d_(r+k)(c)>=0; strict positivity
 has the corresponding strict assumptions. Negative c is allowed.
 Proof/definition method: Reuse the canonical Schur factorization and
 finite-vector Cauchy-Schwarz, normalize rational expressions with Field,
 then use order algebra. No independent matrix or probability implementation.
 Library reuse: Rocq Stdlib Reals, Lra, Psatz, Ring, Field; existing
 EquicorrelationSpectral and EquicorrelationVectors theorems.
 Boundary: These are exact finite covariance and Schur-complement
 feasibility statements, not an independent normal-distribution or
 conditional-expectation theorem or psychometric observation.
*)
Theorem gcd_schur_pd_arbitrary_sign : forall r k c energy total, 0<k -> c<1 ->
 0<sequential_d r c -> 0<sequential_d (r+k) c ->
 0<energy -> 0<=energy-total*total/k ->
 0<equicorr_schur_energy r c energy total.
Proof.
 intros r k c energy total Hk Hc Hr Ht He Hfeasible.
 assert (Hnz : sequential_d r c <> 0) by lra.
 rewrite (gcd_schur_decomposition r k c energy total Hk Hnz).
 assert (Hsquare:0<=total*total/k).
 { unfold Rdiv; apply Rmult_le_pos.
   - apply Rle_0_sqr.
   - left; apply Rinv_0_lt_compat; lra. }
 assert (Hfactor:0<(1-c)*sequential_d (r+k) c/sequential_d r c)
 by (apply (gcd_common_mode_strict r k c); assumption).
 (* The nonzero vector has either strictly positive contrast energy or
    strictly positive common-mode energy.  Treat these cases explicitly
    rather than asking nonlinear automation to invent this disjunction. *)
 destruct (Rle_lt_or_eq_dec _ _ Hfeasible) as [Hgap|Hz].
 - apply Rplus_lt_le_0_compat.
   + apply Rmult_lt_0_compat; lra.
   + apply Rmult_le_pos; lra.
 - assert (Hspos : 0 < total*total/k) by lra.
   replace ((1-c)*(energy-total*total/k) +
           ((1-c)*sequential_d (r+k) c/sequential_d r c)*
             (total*total/k))
     with (((1-c)*sequential_d (r+k) c/sequential_d r c)*
             (total*total/k) +
           (1-c)*(energy-total*total/k)) by ring.
   apply Rplus_lt_le_0_compat.
   + apply Rmult_lt_0_compat; lra.
   + apply Rmult_le_pos; lra.
Qed.

(** [gcd_schur_psd_list] (theorem).
 Mathematical meaning: The actual finite-vector conditional covariance matrix is PSD for both positive and admissible negative correlations.
 Exact checked proposition: forall r c (xs:list R), xs<>nil -> c<=1 -> 0<sequential_d r c -> 0<=sequential_d (r+INR(length xs)) c -> 0<=vector_schur_form r c xs.
 Premises and side conditions: Future length k is strictly positive and
 the observed covariance d_r(c) is invertible. The admissible full
 equicorrelation domain uses c<=1 and d_(r+k)(c)>=0; strict positivity
 has the corresponding strict assumptions. Negative c is allowed.
 Proof/definition method: Reuse the canonical Schur factorization and
 finite-vector Cauchy-Schwarz, normalize rational expressions with Field,
 then use order algebra. No independent matrix or probability implementation.
 Library reuse: Rocq Stdlib Reals, Lra, Psatz, Ring, Field; existing
 EquicorrelationSpectral and EquicorrelationVectors theorems.
 Boundary: These are exact finite covariance and Schur-complement
 feasibility statements, not an independent normal-distribution or
 conditional-expectation theorem or psychometric observation.
*)
Theorem gcd_schur_psd_list : forall r c (xs:list R), xs<>nil -> c<=1 ->
 0<sequential_d r c -> 0<=sequential_d (r+INR(length xs)) c ->
 0<=vector_schur_form r c xs.
Proof.
 intros r c xs Hxs Hc Hr Ht.
 unfold vector_schur_form.
 apply (gcd_schur_psd_arbitrary_sign r (INR(length xs)) c
        (vector_square_energy xs) (vector_real_sum xs)).
 - destruct xs as [|x xs]; [contradiction|]; simpl; apply vector_nat_to_real_successor_positive.
 - assumption.
 - assumption.
 - assumption.
 - apply vector_cauchy_feasibility; assumption.
Qed.

(** [gcd_schur_pd_list] (theorem).
 Mathematical meaning: The actual finite-vector conditional covariance matrix is positive definite when the full battery is positive definite.
 Exact checked proposition: forall r c (xs:list R), xs<>nil -> c<1 -> 0<sequential_d r c -> 0<sequential_d (r+INR(length xs)) c -> 0<vector_square_energy xs -> 0<vector_schur_form r c xs.
 Premises and side conditions: Future length k is strictly positive and
 the observed covariance d_r(c) is invertible. The admissible full
 equicorrelation domain uses c<=1 and d_(r+k)(c)>=0; strict positivity
 has the corresponding strict assumptions. Negative c is allowed.
 Proof/definition method: Reuse the canonical Schur factorization and
 finite-vector Cauchy-Schwarz, normalize rational expressions with Field,
 then use order algebra. No independent matrix or probability implementation.
 Library reuse: Rocq Stdlib Reals, Lra, Psatz, Ring, Field; existing
 EquicorrelationSpectral and EquicorrelationVectors theorems.
 Boundary: These are exact finite covariance and Schur-complement
 feasibility statements, not an independent normal-distribution or
 conditional-expectation theorem or psychometric observation.
*)
Theorem gcd_schur_pd_list : forall r c (xs:list R), xs<>nil -> c<1 ->
 0<sequential_d r c -> 0<sequential_d (r+INR(length xs)) c ->
 0<vector_square_energy xs -> 0<vector_schur_form r c xs.
Proof.
 intros r c xs Hxs Hc Hr Ht He.
 unfold vector_schur_form.
 apply (gcd_schur_pd_arbitrary_sign r (INR(length xs)) c
        (vector_square_energy xs) (vector_real_sum xs)).
 - destruct xs as [|x xs]; [contradiction|]; simpl; apply vector_nat_to_real_successor_positive.
 - assumption.
 - assumption.
 - assumption.
 - assumption.
 - apply vector_cauchy_feasibility; assumption.
Qed.

(** [gcd_schur_singular_common_boundary] (theorem).
 Mathematical meaning: At the admissible negative-correlation endpoint the future conditional sum direction is singular.
 Exact checked proposition: forall r k c x, sequential_d r c<>0 -> sequential_d (r+k) c=0 -> equicorr_schur_energy r c (k*x*x) (k*x)=0.
 Premises and side conditions: Future length k is strictly positive and
 the observed covariance d_r(c) is invertible. The admissible full
 equicorrelation domain uses c<=1 and d_(r+k)(c)>=0; strict positivity
 has the corresponding strict assumptions. Negative c is allowed.
 Proof/definition method: Reuse the canonical Schur factorization and
 finite-vector Cauchy-Schwarz, normalize rational expressions with Field,
 then use order algebra. No independent matrix or probability implementation.
 Library reuse: Rocq Stdlib Reals, Lra, Psatz, Ring, Field; existing
 EquicorrelationSpectral and EquicorrelationVectors theorems.
 Boundary: These are exact finite covariance and Schur-complement
 feasibility statements, not an independent normal-distribution or
 conditional-expectation theorem or psychometric observation.
*)
Theorem gcd_schur_singular_common_boundary : forall r k c x, sequential_d r c<>0 -> sequential_d (r+k) c=0 ->
 equicorr_schur_energy r c (k*x*x) (k*x)=0.
Proof.
 intros r k c x Hr Ht; rewrite equicorr_schur_common_mode_formula by assumption; rewrite Ht; field; lra.
Qed.

(** [gcd_total_domain_from_negative_endpoint] (theorem).
 Mathematical meaning: Positive observed and future battery sizes ensure a positive dimension for the conditional Schur decomposition.
 Exact checked proposition: forall r k c, 0<r -> 0<k -> c<1 -> 0<sequential_d r c -> 0<=sequential_d (r+k) c -> 0<r+k.
 Premises and side conditions: Future length k is strictly positive and
 the observed covariance d_r(c) is invertible. The admissible full
 equicorrelation domain uses c<=1 and d_(r+k)(c)>=0; strict positivity
 has the corresponding strict assumptions. Negative c is allowed.
 Proof/definition method: Reuse the canonical Schur factorization and
 finite-vector Cauchy-Schwarz, normalize rational expressions with Field,
 then use order algebra. No independent matrix or probability implementation.
 Library reuse: Rocq Stdlib Reals, Lra, Psatz, Ring, Field; existing
 EquicorrelationSpectral and EquicorrelationVectors theorems.
 Boundary: These are exact finite covariance and Schur-complement
 feasibility statements, not an independent normal-distribution or
 conditional-expectation theorem or psychometric observation.
*)
Theorem gcd_total_domain_from_negative_endpoint : forall r k c, 0<r -> 0<k -> c<1 ->
 0<sequential_d r c -> 0<=sequential_d (r+k) c ->
 0<r+k.
Proof.
 intros; lra.
Qed.

(** [gcd_schur_psd_iff_full_battery] (theorem).
 Mathematical meaning: A full-battery common eigenvalue condition and the contrast eigenvalue condition are jointly necessary and sufficient for PSD of every feasible conditional quadratic summary. This conversely rules out correlations that fail the full covariance domain.
 Exact checked proposition: forall r k c, 0<r -> 0<k -> 0<sequential_d r c -> ((forall energy total, 0<=energy-total*total/k -> 0<=equicorr_schur_energy r c energy total) <-> (c<=1 /\ 0<=sequential_d (r+k) c)).
 Premises and side conditions: The already-conditioned block has r>0 and
 d_r(c)>0. The future count k>0 and the universal quantified energy
 summaries satisfy the abstract Cauchy feasibility inequality. These
 algebraic summaries include a contrast witness even when k=1; hence this
 criterion is expressly NOT claimed as a 1D concrete-vector iff.
 Proof/definition method: Use orthogonal contrast/common-mode witnesses
 for necessity, the exact Schur common-mode formula, positive denominator
 cancellation and the previously proved signed-correlation sufficiency.
 Library reuse: EquicorrelationSpectral Schur factorization,
 GaussianCovarianceDomain sufficiency, Stdlib Reals/Field/Ring/Lra/Psatz.
 Boundary: Complete iff for the stated feasible real-energy summaries,
 not a Gaussian probability-space construction, conditional independence,
 or a regular conditional expectation theorem.
*)
Theorem gcd_schur_psd_iff_full_battery :
  forall r k c, 0<r -> 0<k -> 0<sequential_d r c ->
  ((forall energy total, 0<=energy-total*total/k ->
    0<=equicorr_schur_energy r c energy total) <->
   (c<=1 /\ 0<=sequential_d (r+k) c)).
Proof.
 intros r k c Hr Hk Hd; split.
 - intro Hform.
   assert (Hcontrast : 0 <= equicorr_schur_energy r c 1 0).
   { apply Hform.
     replace (1 - 0*0/k) with 1 by (field; lra).
     lra. }
   rewrite equicorr_schur_contrast_formula in Hcontrast by lra.
   assert (Hc : c <= 1) by lra.
   split; [exact Hc|].
   assert (Hcommon : 0 <=
       equicorr_schur_energy r c (k*1*1) (k*1)).
   { apply Hform.
     replace (k*1*1 - (k*1)*(k*1)/k) with 0
       by (field; lra).
     lra. }
   rewrite (equicorr_schur_common_mode_formula r k c 1)
     in Hcommon by lra.
   replace (k*(1-c)*sequential_d (r+k) c/
            sequential_d r c*1*1)
     with (k*(1-c)*sequential_d (r+k) c/
           sequential_d r c) in Hcommon by ring.
   assert (Hnumerator : 0 <= k*(1-c)*sequential_d (r+k) c).
   { replace (k*(1-c)*sequential_d (r+k) c)
       with ((k*(1-c)*sequential_d (r+k) c /
              sequential_d r c)*sequential_d r c)
       by (field; lra).
     apply Rmult_le_pos; lra. }
   destruct (Rlt_le_dec c 1) as [Hstrict|Heq].
   + apply (Rmult_le_reg_l (k*(1-c))); [nra|].
     replace (k*(1-c)*0) with 0 by ring.
     exact Hnumerator.
   + assert (Hequal : c=1) by lra.
     subst c; unfold sequential_d; nra.
 - intros [Hc Hfull] energy total Hfeasible.
   apply (gcd_schur_psd_arbitrary_sign r k c energy total);
     assumption.
Qed.

(** [gcd_schur_pd_iff_full_battery] (theorem).
 Mathematical meaning: A strictly positive full-battery common eigenvalue and contrast eigenvalue are jointly necessary and sufficient for positive conditional covariance on every nonzero feasible future-score summary.
 Exact checked proposition: forall r k c, 0<r -> 0<k -> 0<sequential_d r c -> ((forall energy total, 0<energy -> 0<=energy-total*total/k -> 0<equicorr_schur_energy r c energy total) <-> (c<1 /\ 0<sequential_d (r+k) c)).
 Premises and side conditions: The already-conditioned block has r>0 and
 d_r(c)>0. The future count k>0 and the universal quantified energy
 summaries satisfy the abstract Cauchy feasibility inequality. These
 algebraic summaries include a contrast witness even when k=1; hence this
 criterion is expressly NOT claimed as a 1D concrete-vector iff.
 Proof/definition method: Use orthogonal contrast/common-mode witnesses
 for necessity, the exact Schur common-mode formula, positive denominator
 cancellation and the previously proved signed-correlation sufficiency.
 Library reuse: EquicorrelationSpectral Schur factorization,
 GaussianCovarianceDomain sufficiency, Stdlib Reals/Field/Ring/Lra/Psatz.
 Boundary: Complete iff for the stated feasible real-energy summaries,
 not a Gaussian probability-space construction, conditional independence,
 or a regular conditional expectation theorem.
*)
Theorem gcd_schur_pd_iff_full_battery :
  forall r k c, 0<r -> 0<k -> 0<sequential_d r c ->
  ((forall energy total, 0<energy ->
    0<=energy-total*total/k ->
    0<equicorr_schur_energy r c energy total) <->
   (c<1 /\ 0<sequential_d (r+k) c)).
Proof.
 intros r k c Hr Hk Hd; split.
 - intro Hform.
   assert (Hcontrast : 0 < equicorr_schur_energy r c 1 0).
   { apply Hform; [lra|].
     replace (1 - 0*0/k) with 1 by (field; lra).
     lra. }
   rewrite equicorr_schur_contrast_formula in Hcontrast by lra.
   assert (Hc : c < 1) by lra.
   split; [exact Hc|].
   assert (Hcommon : 0 <
       equicorr_schur_energy r c (k*1*1) (k*1)).
   { apply Hform; [nra|].
     replace (k*1*1 - (k*1)*(k*1)/k) with 0
       by (field; lra).
     lra. }
   rewrite (equicorr_schur_common_mode_formula r k c 1)
     in Hcommon by lra.
   replace (k*(1-c)*sequential_d (r+k) c/
            sequential_d r c*1*1)
     with (k*(1-c)*sequential_d (r+k) c/
           sequential_d r c) in Hcommon by ring.
   assert (Hnumerator : 0 < k*(1-c)*sequential_d (r+k) c).
   { replace (k*(1-c)*sequential_d (r+k) c)
       with ((k*(1-c)*sequential_d (r+k) c /
              sequential_d r c)*sequential_d r c)
       by (field; lra).
     apply Rmult_lt_0_compat; assumption. }
   apply (Rmult_lt_reg_l (k*(1-c))); [nra|].
   replace (k*(1-c)*0) with 0 by ring.
   exact Hnumerator.
 - intros [Hc Hfull] energy total Hpositive Hfeasible.
   apply (gcd_schur_pd_arbitrary_sign r k c energy total);
     assumption.
Qed.

(** [gcd_schur_contrast_witness] (theorem).
 Mathematical meaning: A concrete future-score contrast [1,-1,0,...,0] realizes the conditional Schur contrast eigenvalue, and its energy is independent of the observed-block size.
 Exact checked proposition: forall r c k, sequential_d r c<>0 -> vector_schur_form r c (1::(-1)::repeat 0 k)=2*(1-c).
 Premises and side conditions: The conditioning covariance d_r(c) is
 strictly positive and observed count r>0. Concrete finite future test
 score lists have dimension S(S k), i.e. at least two; this restriction is
 necessary to witness a nontrivial contrast direction. The full covariance
 PSD/PD boundaries include admissible negative correlations.
 Proof/definition method: Construct exact common and contrast finite-list
 witnesses using existing vector_real_sum and vector_square_energy laws.
 Reuse the Schur common-mode factorization and signed-domain PSD/PD lemmas
 to prove both directions with strictly positive scalar cancellation.
 Library reuse: EquicorrelationVectors, EquicorrelationSpectral, Stdlib
 List.repeat, Reals, Ring, Field, Lra and Psatz. No bespoke sum or matrix.
 Boundary: Complete concrete finite-vector covariance domain, NOT a
 Gaussian joint probability distribution or conditional-expectation law.
*)
Theorem gcd_schur_contrast_witness :
 forall r c k, sequential_d r c<>0 ->
 vector_schur_form r c (1::(-1)::repeat 0 k)=2*(1-c).
Proof.
 intros r c k Hd.
 unfold vector_schur_form.
 assert (Hs : vector_real_sum (1::(-1)::repeat 0 k)=0).
 { change (1+((-1)+vector_real_sum (repeat 0 k))=0).
   rewrite vector_real_sum_repeat; ring. }
 assert (He : vector_square_energy (1::(-1)::repeat 0 k)=2).
 { change (1*1+((-1)*(-1)+vector_square_energy (repeat 0 k))=2).
   rewrite vector_square_energy_repeat; ring. }
 rewrite Hs, He.
 rewrite equicorr_schur_contrast_formula by exact Hd.
 ring.
Qed.

(** [gcd_schur_common_witness] (theorem).
 Mathematical meaning: A concrete all-ones future-score vector realizes the Schur common-direction eigenvalue in the signed-correlation full-battery model.
 Exact checked proposition: forall r c k, sequential_d r c<>0 -> vector_schur_form r c (repeat 1 (S k)) = INR(S k)*(1-c)*sequential_d (r+INR(S k)) c/ sequential_d r c.
 Premises and side conditions: The conditioning covariance d_r(c) is
 strictly positive and observed count r>0. Concrete finite future test
 score lists have dimension S(S k), i.e. at least two; this restriction is
 necessary to witness a nontrivial contrast direction. The full covariance
 PSD/PD boundaries include admissible negative correlations.
 Proof/definition method: Construct exact common and contrast finite-list
 witnesses using existing vector_real_sum and vector_square_energy laws.
 Reuse the Schur common-mode factorization and signed-domain PSD/PD lemmas
 to prove both directions with strictly positive scalar cancellation.
 Library reuse: EquicorrelationVectors, EquicorrelationSpectral, Stdlib
 List.repeat, Reals, Ring, Field, Lra and Psatz. No bespoke sum or matrix.
 Boundary: Complete concrete finite-vector covariance domain, NOT a
 Gaussian joint probability distribution or conditional-expectation law.
*)
Theorem gcd_schur_common_witness :
 forall r c k, sequential_d r c<>0 ->
 vector_schur_form r c (repeat 1 (S k)) =
 INR(S k)*(1-c)*sequential_d (r+INR(S k)) c/
 sequential_d r c.
Proof.
 intros r c k Hd.
 unfold vector_schur_form.
 rewrite vector_square_energy_repeat, vector_real_sum_repeat.
 rewrite (equicorr_schur_common_mode_formula
            r (INR(S k)) c 1) by exact Hd.
 unfold Rdiv; ring.
Qed.

(** [gcd_schur_concrete_psd_iff_full_battery] (theorem).
 Mathematical meaning: For every actual finite future-score vector of dimension at least two, signed-correlation Schur PSD is equivalent to the two correct full-battery eigenvalue inequalities; both necessity witnesses are concrete lists.
 Exact checked proposition: forall r k c, 0<r -> 0<sequential_d r c -> ((forall xs:list R, length xs=S(S k) -> 0<=vector_schur_form r c xs) <-> (c<=1 /\ 0<=sequential_d (r+INR(S(S k))) c)).
 Premises and side conditions: The conditioning covariance d_r(c) is
 strictly positive and observed count r>0. Concrete finite future test
 score lists have dimension S(S k), i.e. at least two; this restriction is
 necessary to witness a nontrivial contrast direction. The full covariance
 PSD/PD boundaries include admissible negative correlations.
 Proof/definition method: Construct exact common and contrast finite-list
 witnesses using existing vector_real_sum and vector_square_energy laws.
 Reuse the Schur common-mode factorization and signed-domain PSD/PD lemmas
 to prove both directions with strictly positive scalar cancellation.
 Library reuse: EquicorrelationVectors, EquicorrelationSpectral, Stdlib
 List.repeat, Reals, Ring, Field, Lra and Psatz. No bespoke sum or matrix.
 Boundary: Complete concrete finite-vector covariance domain, NOT a
 Gaussian joint probability distribution or conditional-expectation law.
*)
Theorem gcd_schur_concrete_psd_iff_full_battery :
 forall r k c, 0<r -> 0<sequential_d r c ->
 ((forall xs:list R, length xs=S(S k) ->
    0<=vector_schur_form r c xs) <->
   (c<=1 /\ 0<=sequential_d (r+INR(S(S k))) c)).
Proof.
 intros r k c Hr Hd; split.
 - intro Hform.
   assert (Hcontrast : 0<=
       vector_schur_form r c (1::(-1)::repeat 0 k)).
   { apply Hform.
     simpl length; rewrite repeat_length; reflexivity. }
   rewrite gcd_schur_contrast_witness in Hcontrast by lra.
   assert (Hc:c<=1) by lra.
   split; [exact Hc|].
   assert (Hcommon : 0<=
       vector_schur_form r c (repeat 1 (S(S k)))).
   { apply Hform; apply repeat_length. }
   rewrite gcd_schur_common_witness in Hcommon by lra.
   assert (Hdim : 0<INR(S(S k))).
   { apply vector_nat_to_real_successor_positive. }
   assert (Hnum:0<=
      INR(S(S k))*(1-c)*
      sequential_d (r+INR(S(S k))) c).
   { replace (INR(S(S k))*(1-c)*
              sequential_d (r+INR(S(S k))) c)
       with ((INR(S(S k))*(1-c)*
             sequential_d (r+INR(S(S k))) c/
             sequential_d r c)*sequential_d r c)
       by (field; lra).
     apply Rmult_le_pos; lra. }
   destruct (Rlt_le_dec c 1) as [Hstrict|Heq].
   + apply (Rmult_le_reg_l (INR(S(S k))*(1-c))); [nra|].
     replace (INR(S(S k))*(1-c)*0) with 0 by ring.
     exact Hnum.
   + assert (Hequal:c=1) by lra.
     subst c; unfold sequential_d; nra.
 - intros [Hc Hfull] xs Hlen.
   apply (gcd_schur_psd_list r c xs).
   + destruct xs as [|x xs]; [discriminate Hlen|discriminate].
   + exact Hc.
   + exact Hd.
   + rewrite Hlen; exact Hfull.
Qed.

(** [gcd_schur_concrete_pd_iff_full_battery] (theorem).
 Mathematical meaning: For actual future-score vectors of dimension at least two, strict positive definiteness of the conditional covariance is equivalent to strict full-battery common- and contrast-eigenvalue conditions.
 Exact checked proposition: forall r k c, 0<r -> 0<sequential_d r c -> ((forall xs:list R, length xs=S(S k) -> 0<vector_square_energy xs -> 0<vector_schur_form r c xs) <-> (c<1 /\ 0<sequential_d (r+INR(S(S k))) c)).
 Premises and side conditions: The conditioning covariance d_r(c) is
 strictly positive and observed count r>0. Concrete finite future test
 score lists have dimension S(S k), i.e. at least two; this restriction is
 necessary to witness a nontrivial contrast direction. The full covariance
 PSD/PD boundaries include admissible negative correlations.
 Proof/definition method: Construct exact common and contrast finite-list
 witnesses using existing vector_real_sum and vector_square_energy laws.
 Reuse the Schur common-mode factorization and signed-domain PSD/PD lemmas
 to prove both directions with strictly positive scalar cancellation.
 Library reuse: EquicorrelationVectors, EquicorrelationSpectral, Stdlib
 List.repeat, Reals, Ring, Field, Lra and Psatz. No bespoke sum or matrix.
 Boundary: Complete concrete finite-vector covariance domain, NOT a
 Gaussian joint probability distribution or conditional-expectation law.
*)
Theorem gcd_schur_concrete_pd_iff_full_battery :
 forall r k c, 0<r -> 0<sequential_d r c ->
 ((forall xs:list R, length xs=S(S k) ->
    0<vector_square_energy xs -> 0<vector_schur_form r c xs) <->
   (c<1 /\ 0<sequential_d (r+INR(S(S k))) c)).
Proof.
 intros r k c Hr Hd; split.
 - intro Hform.
   assert (Hcontrast: 0<
       vector_schur_form r c (1::(-1)::repeat 0 k)).
   { apply Hform.
     - simpl length; rewrite repeat_length; reflexivity.
     - change (0<1*1+((-1)*(-1)+vector_square_energy (repeat 0 k))).
       rewrite vector_square_energy_repeat; nra. }
   rewrite gcd_schur_contrast_witness in Hcontrast by lra.
   assert (Hc:c<1) by lra.
   split; [exact Hc|].
   assert (Hcommon:0<
       vector_schur_form r c (repeat 1 (S(S k)))).
   { apply Hform.
     - apply repeat_length.
     - rewrite vector_square_energy_repeat.
       pose proof (vector_nat_to_real_successor_positive (S k)).
       nra. }
   rewrite gcd_schur_common_witness in Hcommon by lra.
   assert (Hdim:0<INR(S(S k))).
   { apply vector_nat_to_real_successor_positive. }
   assert (Hnum:0<
      INR(S(S k))*(1-c)*
      sequential_d (r+INR(S(S k))) c).
   { replace (INR(S(S k))*(1-c)*
              sequential_d (r+INR(S(S k))) c)
       with ((INR(S(S k))*(1-c)*
             sequential_d (r+INR(S(S k))) c/
             sequential_d r c)*sequential_d r c)
       by (field; lra).
     apply Rmult_lt_0_compat; assumption. }
   apply (Rmult_lt_reg_l (INR(S(S k))*(1-c))); [nra|].
   replace (INR(S(S k))*(1-c)*0) with 0 by ring.
   exact Hnum.
 - intros [Hc Hfull] xs Hlen Henergy.
   apply (gcd_schur_pd_list r c xs).
   + destruct xs as [|x xs]; [discriminate Hlen|discriminate].
   + exact Hc.
   + exact Hd.
   + rewrite Hlen; exact Hfull.
   + exact Henergy.
Qed.

(** [gcd_single_future_variance_eigenvalue] (theorem).
 Mathematical meaning: For exactly one future score, the Schur conditional variance is the signed common-mode eigenvalue ratio (1-c)*d_(r+1)(c)/d_r(c). The rank-one expression reuses the existing residual-variance identity.
 Exact checked proposition: forall r c, sequential_d r c<>0 -> equicorr_schur_diagonal r c = (1-c)*sequential_d (r+1) c/sequential_d r c.
 Premises and side conditions: The observed count r>=1 and d_r(c)>0
 establish a nondegenerate observed covariance. The PSD/PD iff tests
 quantify exactly the one-dimensional future Schur covariance (variance).
 Signed c may be negative as far as the full r+1 covariance permits.
 Proof/definition method: Reuse SequentialReport's verified residual
 variance identity and scalar cancellation to prove a full necessity
 and sufficiency criterion; handle singular endpoints algebraically.
 Library reuse: EquicorrelationSpectral.equicorr_schur_diagonal,
 SequentialReport.sequential_residual_variance_identity, Stdlib Reals,
 Ring, Field, Lra, Psatz. No new covariance or probability implementation.
 Boundary: These are exact scalar Schur-covariance facts, not an
 independent construction of a Gaussian measure, conditional law, or
 conditional-expectation integral.
*)
Theorem gcd_single_future_variance_eigenvalue :
 forall r c, sequential_d r c<>0 ->
 equicorr_schur_diagonal r c =
 (1-c)*sequential_d (r+1) c/sequential_d r c.
Proof.
 intros r c Hr.
 unfold equicorr_schur_diagonal.
 rewrite sequential_residual_variance_identity by exact Hr.
 unfold sequential_d, Rdiv; ring.
Qed.

(** [gcd_single_future_psd_iff] (theorem).
 Mathematical meaning: For a single future test result and any observed count r>=1 with nondegenerate observed covariance, nonnegative conditional variance is equivalent to the full r+1 battery equicorrelation domain, including admissible negative correlation and singular boundaries.
 Exact checked proposition: forall r c, 1<=r -> 0<sequential_d r c -> (0<=equicorr_schur_diagonal r c <-> c<=1 /\ 0<=sequential_d (r+1) c).
 Premises and side conditions: The observed count r>=1 and d_r(c)>0
 establish a nondegenerate observed covariance. The PSD/PD iff tests
 quantify exactly the one-dimensional future Schur covariance (variance).
 Signed c may be negative as far as the full r+1 covariance permits.
 Proof/definition method: Reuse SequentialReport's verified residual
 variance identity and scalar cancellation to prove a full necessity
 and sufficiency criterion; handle singular endpoints algebraically.
 Library reuse: EquicorrelationSpectral.equicorr_schur_diagonal,
 SequentialReport.sequential_residual_variance_identity, Stdlib Reals,
 Ring, Field, Lra, Psatz. No new covariance or probability implementation.
 Boundary: These are exact scalar Schur-covariance facts, not an
 independent construction of a Gaussian measure, conditional law, or
 conditional-expectation integral.
*)
Theorem gcd_single_future_psd_iff :
 forall r c, 1<=r -> 0<sequential_d r c ->
 (0<=equicorr_schur_diagonal r c <->
  c<=1 /\ 0<=sequential_d (r+1) c).
Proof.
 intros r c Hr Hd; split.
 - intro Hvariance.
   rewrite gcd_single_future_variance_eigenvalue in Hvariance by lra.
   assert (Hprod:0<=(1-c)*sequential_d (r+1) c).
   { replace ((1-c)*sequential_d (r+1) c)
       with (((1-c)*sequential_d (r+1) c /
              sequential_d r c)*sequential_d r c)
         by (field; lra).
     apply Rmult_le_pos; lra. }
   assert (Hc : c<=1).
   { destruct (Rle_lt_dec c 1) as [Hle|Hgt]; [exact Hle|].
     assert (Htotal:0<sequential_d (r+1) c).
     { unfold sequential_d; nra. }
     nra. }
   split; [exact Hc|].
   destruct (Rlt_le_dec c 1) as [Hstrict|Hboundary].
   + assert (Hcoef:0<1-c) by lra.
     apply (Rmult_le_reg_l (1-c)); [exact Hcoef|].
     replace ((1-c)*0) with 0 by ring; exact Hprod.
   + assert (Heq:c=1) by lra.
     subst c; unfold sequential_d; nra.
 - intros [Hc Htotal].
   rewrite gcd_single_future_variance_eigenvalue by lra.
   unfold Rdiv.
   apply Rmult_le_pos.
   + apply Rmult_le_pos; lra.
   + left; apply Rinv_0_lt_compat; lra.
Qed.

(** [gcd_single_future_pd_iff] (theorem).
 Mathematical meaning: The single-future-test conditional covariance is strictly positive precisely on the strict full-battery equicorrelation domain; zero conditional variance occurs only at a singular endpoint.
 Exact checked proposition: forall r c, 1<=r -> 0<sequential_d r c -> (0<equicorr_schur_diagonal r c <-> c<1 /\ 0<sequential_d (r+1) c).
 Premises and side conditions: The observed count r>=1 and d_r(c)>0
 establish a nondegenerate observed covariance. The PSD/PD iff tests
 quantify exactly the one-dimensional future Schur covariance (variance).
 Signed c may be negative as far as the full r+1 covariance permits.
 Proof/definition method: Reuse SequentialReport's verified residual
 variance identity and scalar cancellation to prove a full necessity
 and sufficiency criterion; handle singular endpoints algebraically.
 Library reuse: EquicorrelationSpectral.equicorr_schur_diagonal,
 SequentialReport.sequential_residual_variance_identity, Stdlib Reals,
 Ring, Field, Lra, Psatz. No new covariance or probability implementation.
 Boundary: These are exact scalar Schur-covariance facts, not an
 independent construction of a Gaussian measure, conditional law, or
 conditional-expectation integral.
*)
Theorem gcd_single_future_pd_iff :
 forall r c, 1<=r -> 0<sequential_d r c ->
 (0<equicorr_schur_diagonal r c <->
  c<1 /\ 0<sequential_d (r+1) c).
Proof.
 intros r c Hr Hd; split.
 - intro Hvariance.
   rewrite gcd_single_future_variance_eigenvalue in Hvariance by lra.
   assert (Hprod:0<(1-c)*sequential_d (r+1) c).
   { replace ((1-c)*sequential_d (r+1) c)
       with (((1-c)*sequential_d (r+1) c/
              sequential_d r c)*sequential_d r c)
         by (field; lra).
     apply Rmult_lt_0_compat; lra. }
   assert (Hc:c<1).
   { destruct (Rlt_le_dec c 1) as [Hstrict|Hge]; [exact Hstrict|].
     assert (Htotal:0<sequential_d (r+1) c).
     { unfold sequential_d; nra. }
     nra. }
   split; [exact Hc|].
   apply (Rmult_lt_reg_l (1-c)); [lra|].
   replace ((1-c)*0) with 0 by ring; exact Hprod.
 - intros [Hc Htotal].
   rewrite gcd_single_future_variance_eigenvalue by lra.
   unfold Rdiv.
   apply Rmult_lt_0_compat.
   + apply Rmult_lt_0_compat; lra.
   + apply Rinv_0_lt_compat; lra.
Qed.

(** [gcd_single_future_lower_singularity] (theorem).
 Mathematical meaning: At the lower admissible equicorrelation endpoint of the full r+1 battery, the last score becomes a deterministic linear function of the first r observed scores in the Gaussian model; its algebraic residual Schur variance vanishes.
 Exact checked proposition: forall r c, sequential_d r c<>0 -> sequential_d (r+1) c=0 -> equicorr_schur_diagonal r c=0.
 Premises and side conditions: The observed count r>=1 and d_r(c)>0
 establish a nondegenerate observed covariance. The PSD/PD iff tests
 quantify exactly the one-dimensional future Schur covariance (variance).
 Signed c may be negative as far as the full r+1 covariance permits.
 Proof/definition method: Reuse SequentialReport's verified residual
 variance identity and scalar cancellation to prove a full necessity
 and sufficiency criterion; handle singular endpoints algebraically.
 Library reuse: EquicorrelationSpectral.equicorr_schur_diagonal,
 SequentialReport.sequential_residual_variance_identity, Stdlib Reals,
 Ring, Field, Lra, Psatz. No new covariance or probability implementation.
 Boundary: These are exact scalar Schur-covariance facts, not an
 independent construction of a Gaussian measure, conditional law, or
 conditional-expectation integral.
*)
Theorem gcd_single_future_lower_singularity :
 forall r c, sequential_d r c<>0 ->
 sequential_d (r+1) c=0 ->
 equicorr_schur_diagonal r c=0.
Proof.
 intros r c Hr Hsing.
 rewrite gcd_single_future_variance_eigenvalue by exact Hr.
 rewrite Hsing; unfold Rdiv; ring.
Qed.

(** [gcd_single_future_perfect_correlation_singularity] (theorem).
 Mathematical meaning: At perfect positive equicorrelation all scores coincide in the Gaussian model, and any previously observed score predicts the future one with zero Schur residual variance.
 Exact checked proposition: forall r, 0<r -> equicorr_schur_diagonal r 1=0.
 Premises and side conditions: The observed count r>=1 and d_r(c)>0
 establish a nondegenerate observed covariance. The PSD/PD iff tests
 quantify exactly the one-dimensional future Schur covariance (variance).
 Signed c may be negative as far as the full r+1 covariance permits.
 Proof/definition method: Reuse SequentialReport's verified residual
 variance identity and scalar cancellation to prove a full necessity
 and sufficiency criterion; handle singular endpoints algebraically.
 Library reuse: EquicorrelationSpectral.equicorr_schur_diagonal,
 SequentialReport.sequential_residual_variance_identity, Stdlib Reals,
 Ring, Field, Lra, Psatz. No new covariance or probability implementation.
 Boundary: These are exact scalar Schur-covariance facts, not an
 independent construction of a Gaussian measure, conditional law, or
 conditional-expectation integral.
*)
Theorem gcd_single_future_perfect_correlation_singularity :
 forall r, 0<r ->
 equicorr_schur_diagonal r 1=0.
Proof.
 intros r Hr.
 rewrite gcd_single_future_variance_eigenvalue.
 - unfold Rdiv; ring.
 - unfold sequential_d; nra.
Qed.


(** D051: additional deterministic consequences for signed Gaussian covariance and posterior updates.
 Every theorem is an exact algebraic implication of the canonical equicorrelation definitions; it is not a formal construction of a Gaussian probability space or of conditional expectation.
 Each result below is documented and will count as verified only if pinned Rocq CI accepts the exact commit. *)

(** [d051_denominator_split] (theorem).
 Mathematical meaning: Equicorrelation common-mode denominator decomposes into contrast and shared-factor energy.
 Exact checked proposition: forall n c:R, sequential_d n c = (1-c)+n*c.
 Premises and side conditions: Scores and observation counts are ideal real-valued symbolic parameters. Every inverse requires its explicitly stated nonzero denominator. The algebraic conclusions are valid for signed correlations wherever the assumptions hold; probabilistic feasibility requires the full PSD covariance domain separately.
 Proof/definition method: Reduce to the canonical rational covariance and sufficient-history formulas, then use Stdlib field and polynomial normalization. No bespoke sums, matrices, or distributions.
 Library reuse: SequentialReport.sequential_d, EquicorrelationSpectral Schur entries, UnequalHistoryLinearPrediction.hp; Stdlib Reals, Field and Psatz.
 Boundary: Deterministic necessary consequences of the Gaussian model; neither the existence of Gaussian random variables nor the measure-theoretic conditional-expectation identity is asserted here.
*)
Theorem d051_denominator_split : forall n c:R, sequential_d n c = (1-c)+n*c.
Proof.
  intros; cbv [hp sequential_d equicorr_schur_diagonal equicorr_schur_cross] in *; field; nra.
Qed.

(** [d051_denominator_two_blocks] (theorem).
 Mathematical meaning: Adding a block of k observations increments common-mode energy by k times the correlation.
 Exact checked proposition: forall n k c:R, sequential_d (n+k) c = sequential_d n c + k*c.
 Premises and side conditions: Scores and observation counts are ideal real-valued symbolic parameters. Every inverse requires its explicitly stated nonzero denominator. The algebraic conclusions are valid for signed correlations wherever the assumptions hold; probabilistic feasibility requires the full PSD covariance domain separately.
 Proof/definition method: Reduce to the canonical rational covariance and sufficient-history formulas, then use Stdlib field and polynomial normalization. No bespoke sums, matrices, or distributions.
 Library reuse: SequentialReport.sequential_d, EquicorrelationSpectral Schur entries, UnequalHistoryLinearPrediction.hp; Stdlib Reals, Field and Psatz.
 Boundary: Deterministic necessary consequences of the Gaussian model; neither the existence of Gaussian random variables nor the measure-theoretic conditional-expectation identity is asserted here.
*)
Theorem d051_denominator_two_blocks : forall n k c:R, sequential_d (n+k) c = sequential_d n c + k*c.
Proof.
  intros; cbv [hp sequential_d equicorr_schur_diagonal equicorr_schur_cross] in *; field; nra.
Qed.

(** [d051_denominator_three_blocks] (theorem).
 Mathematical meaning: Three-block common-mode energy has an exact total-increment decomposition.
 Exact checked proposition: forall n k l c:R, sequential_d (n+k+l) c = sequential_d n c+(k+l)*c.
 Premises and side conditions: Scores and observation counts are ideal real-valued symbolic parameters. Every inverse requires its explicitly stated nonzero denominator. The algebraic conclusions are valid for signed correlations wherever the assumptions hold; probabilistic feasibility requires the full PSD covariance domain separately.
 Proof/definition method: Reduce to the canonical rational covariance and sufficient-history formulas, then use Stdlib field and polynomial normalization. No bespoke sums, matrices, or distributions.
 Library reuse: SequentialReport.sequential_d, EquicorrelationSpectral Schur entries, UnequalHistoryLinearPrediction.hp; Stdlib Reals, Field and Psatz.
 Boundary: Deterministic necessary consequences of the Gaussian model; neither the existence of Gaussian random variables nor the measure-theoretic conditional-expectation identity is asserted here.
*)
Theorem d051_denominator_three_blocks : forall n k l c:R, sequential_d (n+k+l) c = sequential_d n c+(k+l)*c.
Proof.
  intros; cbv [hp sequential_d equicorr_schur_diagonal equicorr_schur_cross] in *; field; nra.
Qed.

(** [d051_denominator_three_stage] (theorem).
 Mathematical meaning: Three staged history lengths yield the same common-mode denominator as pooled history.
 Exact checked proposition: forall n k l c:R, sequential_d (n+k+l) c = sequential_d n c+k*c+l*c.
 Premises and side conditions: Scores and observation counts are ideal real-valued symbolic parameters. Every inverse requires its explicitly stated nonzero denominator. The algebraic conclusions are valid for signed correlations wherever the assumptions hold; probabilistic feasibility requires the full PSD covariance domain separately.
 Proof/definition method: Reduce to the canonical rational covariance and sufficient-history formulas, then use Stdlib field and polynomial normalization. No bespoke sums, matrices, or distributions.
 Library reuse: SequentialReport.sequential_d, EquicorrelationSpectral Schur entries, UnequalHistoryLinearPrediction.hp; Stdlib Reals, Field and Psatz.
 Boundary: Deterministic necessary consequences of the Gaussian model; neither the existence of Gaussian random variables nor the measure-theoretic conditional-expectation identity is asserted here.
*)
Theorem d051_denominator_three_stage : forall n k l c:R, sequential_d (n+k+l) c = sequential_d n c+k*c+l*c.
Proof.
  intros; cbv [hp sequential_d equicorr_schur_diagonal equicorr_schur_cross] in *; field; nra.
Qed.

(** [d051_denominator_four_stage] (theorem).
 Mathematical meaning: Four staged history increments can be pooled before computing covariance feasibility.
 Exact checked proposition: forall n k l m c:R, sequential_d (n+k+l+m) c = sequential_d n c+(k+l+m)*c.
 Premises and side conditions: Scores and observation counts are ideal real-valued symbolic parameters. Every inverse requires its explicitly stated nonzero denominator. The algebraic conclusions are valid for signed correlations wherever the assumptions hold; probabilistic feasibility requires the full PSD covariance domain separately.
 Proof/definition method: Reduce to the canonical rational covariance and sufficient-history formulas, then use Stdlib field and polynomial normalization. No bespoke sums, matrices, or distributions.
 Library reuse: SequentialReport.sequential_d, EquicorrelationSpectral Schur entries, UnequalHistoryLinearPrediction.hp; Stdlib Reals, Field and Psatz.
 Boundary: Deterministic necessary consequences of the Gaussian model; neither the existence of Gaussian random variables nor the measure-theoretic conditional-expectation identity is asserted here.
*)
Theorem d051_denominator_four_stage : forall n k l m c:R, sequential_d (n+k+l+m) c = sequential_d n c+(k+l+m)*c.
Proof.
  intros; cbv [hp sequential_d equicorr_schur_diagonal equicorr_schur_cross] in *; field; nra.
Qed.

(** [d051_denominator_difference] (theorem).
 Mathematical meaning: The change in the common eigenvalue identifies the sign of correlation.
 Exact checked proposition: forall n k c:R, sequential_d (n+k) c-sequential_d n c=k*c.
 Premises and side conditions: Scores and observation counts are ideal real-valued symbolic parameters. Every inverse requires its explicitly stated nonzero denominator. The algebraic conclusions are valid for signed correlations wherever the assumptions hold; probabilistic feasibility requires the full PSD covariance domain separately.
 Proof/definition method: Reduce to the canonical rational covariance and sufficient-history formulas, then use Stdlib field and polynomial normalization. No bespoke sums, matrices, or distributions.
 Library reuse: SequentialReport.sequential_d, EquicorrelationSpectral Schur entries, UnequalHistoryLinearPrediction.hp; Stdlib Reals, Field and Psatz.
 Boundary: Deterministic necessary consequences of the Gaussian model; neither the existence of Gaussian random variables nor the measure-theoretic conditional-expectation identity is asserted here.
*)
Theorem d051_denominator_difference : forall n k c:R, sequential_d (n+k) c-sequential_d n c=k*c.
Proof.
  intros; cbv [hp sequential_d equicorr_schur_diagonal equicorr_schur_cross] in *; field; nra.
Qed.

(** [d051_denominator_reference_shift] (theorem).
 Mathematical meaning: Two future-batch lengths change the common eigenvalue by their size contrast.
 Exact checked proposition: forall n k l c:R, sequential_d (n+k) c-sequential_d (n+l) c=(k-l)*c.
 Premises and side conditions: Scores and observation counts are ideal real-valued symbolic parameters. Every inverse requires its explicitly stated nonzero denominator. The algebraic conclusions are valid for signed correlations wherever the assumptions hold; probabilistic feasibility requires the full PSD covariance domain separately.
 Proof/definition method: Reduce to the canonical rational covariance and sufficient-history formulas, then use Stdlib field and polynomial normalization. No bespoke sums, matrices, or distributions.
 Library reuse: SequentialReport.sequential_d, EquicorrelationSpectral Schur entries, UnequalHistoryLinearPrediction.hp; Stdlib Reals, Field and Psatz.
 Boundary: Deterministic necessary consequences of the Gaussian model; neither the existence of Gaussian random variables nor the measure-theoretic conditional-expectation identity is asserted here.
*)
Theorem d051_denominator_reference_shift : forall n k l c:R, sequential_d (n+k) c-sequential_d (n+l) c=(k-l)*c.
Proof.
  intros; cbv [hp sequential_d equicorr_schur_diagonal equicorr_schur_cross] in *; field; nra.
Qed.

(** [d051_denominator_two_stage_difference] (theorem).
 Mathematical meaning: Common-eigenvalue changes can be computed after an existing conditioning step.
 Exact checked proposition: forall n k l c:R, sequential_d (n+k+l) c-sequential_d (n+k) c=l*c.
 Premises and side conditions: Scores and observation counts are ideal real-valued symbolic parameters. Every inverse requires its explicitly stated nonzero denominator. The algebraic conclusions are valid for signed correlations wherever the assumptions hold; probabilistic feasibility requires the full PSD covariance domain separately.
 Proof/definition method: Reduce to the canonical rational covariance and sufficient-history formulas, then use Stdlib field and polynomial normalization. No bespoke sums, matrices, or distributions.
 Library reuse: SequentialReport.sequential_d, EquicorrelationSpectral Schur entries, UnequalHistoryLinearPrediction.hp; Stdlib Reals, Field and Psatz.
 Boundary: Deterministic necessary consequences of the Gaussian model; neither the existence of Gaussian random variables nor the measure-theoretic conditional-expectation identity is asserted here.
*)
Theorem d051_denominator_two_stage_difference : forall n k l c:R, sequential_d (n+k+l) c-sequential_d (n+k) c=l*c.
Proof.
  intros; cbv [hp sequential_d equicorr_schur_diagonal equicorr_schur_cross] in *; field; nra.
Qed.

(** [d051_denominator_three_stage_difference] (theorem).
 Mathematical meaning: Common-eigenvalue increases telescope over two newly observed batches.
 Exact checked proposition: forall n k l c:R, sequential_d (n+k+l) c-sequential_d n c=(k+l)*c.
 Premises and side conditions: Scores and observation counts are ideal real-valued symbolic parameters. Every inverse requires its explicitly stated nonzero denominator. The algebraic conclusions are valid for signed correlations wherever the assumptions hold; probabilistic feasibility requires the full PSD covariance domain separately.
 Proof/definition method: Reduce to the canonical rational covariance and sufficient-history formulas, then use Stdlib field and polynomial normalization. No bespoke sums, matrices, or distributions.
 Library reuse: SequentialReport.sequential_d, EquicorrelationSpectral Schur entries, UnequalHistoryLinearPrediction.hp; Stdlib Reals, Field and Psatz.
 Boundary: Deterministic necessary consequences of the Gaussian model; neither the existence of Gaussian random variables nor the measure-theoretic conditional-expectation identity is asserted here.
*)
Theorem d051_denominator_three_stage_difference : forall n k l c:R, sequential_d (n+k+l) c-sequential_d n c=(k+l)*c.
Proof.
  intros; cbv [hp sequential_d equicorr_schur_diagonal equicorr_schur_cross] in *; field; nra.
Qed.

(** [d051_denominator_reflection] (theorem).
 Mathematical meaning: Symmetric history-size perturbations preserve the midpoint of the covariance eigenvalue.
 Exact checked proposition: forall n k c:R, sequential_d (n+k) c+sequential_d (n-k) c=2*sequential_d n c.
 Premises and side conditions: Scores and observation counts are ideal real-valued symbolic parameters. Every inverse requires its explicitly stated nonzero denominator. The algebraic conclusions are valid for signed correlations wherever the assumptions hold; probabilistic feasibility requires the full PSD covariance domain separately.
 Proof/definition method: Reduce to the canonical rational covariance and sufficient-history formulas, then use Stdlib field and polynomial normalization. No bespoke sums, matrices, or distributions.
 Library reuse: SequentialReport.sequential_d, EquicorrelationSpectral Schur entries, UnequalHistoryLinearPrediction.hp; Stdlib Reals, Field and Psatz.
 Boundary: Deterministic necessary consequences of the Gaussian model; neither the existence of Gaussian random variables nor the measure-theoretic conditional-expectation identity is asserted here.
*)
Theorem d051_denominator_reflection : forall n k c:R, sequential_d (n+k) c+sequential_d (n-k) c=2*sequential_d n c.
Proof.
  intros; cbv [hp sequential_d equicorr_schur_diagonal equicorr_schur_cross] in *; field; nra.
Qed.

(** [d051_denominator_double] (theorem).
 Mathematical meaning: Doubling test count gives a closed common-eigenvalue identity.
 Exact checked proposition: forall n c:R, sequential_d (2*n) c=2*sequential_d n c-(1-c).
 Premises and side conditions: Scores and observation counts are ideal real-valued symbolic parameters. Every inverse requires its explicitly stated nonzero denominator. The algebraic conclusions are valid for signed correlations wherever the assumptions hold; probabilistic feasibility requires the full PSD covariance domain separately.
 Proof/definition method: Reduce to the canonical rational covariance and sufficient-history formulas, then use Stdlib field and polynomial normalization. No bespoke sums, matrices, or distributions.
 Library reuse: SequentialReport.sequential_d, EquicorrelationSpectral Schur entries, UnequalHistoryLinearPrediction.hp; Stdlib Reals, Field and Psatz.
 Boundary: Deterministic necessary consequences of the Gaussian model; neither the existence of Gaussian random variables nor the measure-theoretic conditional-expectation identity is asserted here.
*)
Theorem d051_denominator_double : forall n c:R, sequential_d (2*n) c=2*sequential_d n c-(1-c).
Proof.
  intros; cbv [hp sequential_d equicorr_schur_diagonal equicorr_schur_cross] in *; field; nra.
Qed.

(** [d051_denominator_pool] (theorem).
 Mathematical meaning: Two separately computed common-mode denominators combine with one contrast correction.
 Exact checked proposition: forall n k c:R, sequential_d (n+k) c=sequential_d n c+sequential_d k c-(1-c).
 Premises and side conditions: Scores and observation counts are ideal real-valued symbolic parameters. Every inverse requires its explicitly stated nonzero denominator. The algebraic conclusions are valid for signed correlations wherever the assumptions hold; probabilistic feasibility requires the full PSD covariance domain separately.
 Proof/definition method: Reduce to the canonical rational covariance and sufficient-history formulas, then use Stdlib field and polynomial normalization. No bespoke sums, matrices, or distributions.
 Library reuse: SequentialReport.sequential_d, EquicorrelationSpectral Schur entries, UnequalHistoryLinearPrediction.hp; Stdlib Reals, Field and Psatz.
 Boundary: Deterministic necessary consequences of the Gaussian model; neither the existence of Gaussian random variables nor the measure-theoretic conditional-expectation identity is asserted here.
*)
Theorem d051_denominator_pool : forall n k c:R, sequential_d (n+k) c=sequential_d n c+sequential_d k c-(1-c).
Proof.
  intros; cbv [hp sequential_d equicorr_schur_diagonal equicorr_schur_cross] in *; field; nra.
Qed.

(** [d051_denominator_pool_three] (theorem).
 Mathematical meaning: Three independently evaluated battery denominators combine without double-counting contrast modes.
 Exact checked proposition: forall n k l c:R, sequential_d (n+k+l) c=sequential_d n c+sequential_d k c+sequential_d l c-2*(1-c).
 Premises and side conditions: Scores and observation counts are ideal real-valued symbolic parameters. Every inverse requires its explicitly stated nonzero denominator. The algebraic conclusions are valid for signed correlations wherever the assumptions hold; probabilistic feasibility requires the full PSD covariance domain separately.
 Proof/definition method: Reduce to the canonical rational covariance and sufficient-history formulas, then use Stdlib field and polynomial normalization. No bespoke sums, matrices, or distributions.
 Library reuse: SequentialReport.sequential_d, EquicorrelationSpectral Schur entries, UnequalHistoryLinearPrediction.hp; Stdlib Reals, Field and Psatz.
 Boundary: Deterministic necessary consequences of the Gaussian model; neither the existence of Gaussian random variables nor the measure-theoretic conditional-expectation identity is asserted here.
*)
Theorem d051_denominator_pool_three : forall n k l c:R, sequential_d (n+k+l) c=sequential_d n c+sequential_d k c+sequential_d l c-2*(1-c).
Proof.
  intros; cbv [hp sequential_d equicorr_schur_diagonal equicorr_schur_cross] in *; field; nra.
Qed.

(** [d051_denominator_contrast] (theorem).
 Mathematical meaning: The common eigenvalue is the dimension minus contrast-mode adjustment.
 Exact checked proposition: forall n c:R, sequential_d n c=n-(n-1)*(1-c).
 Premises and side conditions: Scores and observation counts are ideal real-valued symbolic parameters. Every inverse requires its explicitly stated nonzero denominator. The algebraic conclusions are valid for signed correlations wherever the assumptions hold; probabilistic feasibility requires the full PSD covariance domain separately.
 Proof/definition method: Reduce to the canonical rational covariance and sufficient-history formulas, then use Stdlib field and polynomial normalization. No bespoke sums, matrices, or distributions.
 Library reuse: SequentialReport.sequential_d, EquicorrelationSpectral Schur entries, UnequalHistoryLinearPrediction.hp; Stdlib Reals, Field and Psatz.
 Boundary: Deterministic necessary consequences of the Gaussian model; neither the existence of Gaussian random variables nor the measure-theoretic conditional-expectation identity is asserted here.
*)
Theorem d051_denominator_contrast : forall n c:R, sequential_d n c=n-(n-1)*(1-c).
Proof.
  intros; cbv [hp sequential_d equicorr_schur_diagonal equicorr_schur_cross] in *; field; nra.
Qed.

(** [d051_schur_cross_closed] (theorem).
 Mathematical meaning: Observed conditioning converts cross-covariance into a rational Gaussian residual covariance.
 Exact checked proposition: forall n c:R, sequential_d n c<>0 -> equicorr_schur_cross n c=c*(1-c)/sequential_d n c.
 Premises and side conditions: Scores and observation counts are ideal real-valued symbolic parameters. Every inverse requires its explicitly stated nonzero denominator. The algebraic conclusions are valid for signed correlations wherever the assumptions hold; probabilistic feasibility requires the full PSD covariance domain separately.
 Proof/definition method: Reduce to the canonical rational covariance and sufficient-history formulas, then use Stdlib field and polynomial normalization. No bespoke sums, matrices, or distributions.
 Library reuse: SequentialReport.sequential_d, EquicorrelationSpectral Schur entries, UnequalHistoryLinearPrediction.hp; Stdlib Reals, Field and Psatz.
 Boundary: Deterministic necessary consequences of the Gaussian model; neither the existence of Gaussian random variables nor the measure-theoretic conditional-expectation identity is asserted here.
*)
Theorem d051_schur_cross_closed : forall n c:R, sequential_d n c<>0 -> equicorr_schur_cross n c=c*(1-c)/sequential_d n c.
Proof.
  intros; cbv [hp sequential_d equicorr_schur_diagonal equicorr_schur_cross] in *; field; nra.
Qed.

(** [d051_schur_diagonal_closed] (theorem).
 Mathematical meaning: The exact future-score conditional variance is the residual contrast plus posterior common energy.
 Exact checked proposition: forall n c:R, sequential_d n c<>0 -> equicorr_schur_diagonal n c=(1-c)*(1+n*c)/sequential_d n c.
 Premises and side conditions: Scores and observation counts are ideal real-valued symbolic parameters. Every inverse requires its explicitly stated nonzero denominator. The algebraic conclusions are valid for signed correlations wherever the assumptions hold; probabilistic feasibility requires the full PSD covariance domain separately.
 Proof/definition method: Reduce to the canonical rational covariance and sufficient-history formulas, then use Stdlib field and polynomial normalization. No bespoke sums, matrices, or distributions.
 Library reuse: SequentialReport.sequential_d, EquicorrelationSpectral Schur entries, UnequalHistoryLinearPrediction.hp; Stdlib Reals, Field and Psatz.
 Boundary: Deterministic necessary consequences of the Gaussian model; neither the existence of Gaussian random variables nor the measure-theoretic conditional-expectation identity is asserted here.
*)
Theorem d051_schur_diagonal_closed : forall n c:R, sequential_d n c<>0 -> equicorr_schur_diagonal n c=(1-c)*(1+n*c)/sequential_d n c.
Proof.
  intros; cbv [hp sequential_d equicorr_schur_diagonal equicorr_schur_cross] in *; field; nra.
Qed.

(** [d051_schur_contrast_gap] (theorem).
 Mathematical meaning: Conditioning leaves future-score contrast variance unchanged.
 Exact checked proposition: forall n c:R, sequential_d n c<>0 -> equicorr_schur_diagonal n c-equicorr_schur_cross n c=1-c.
 Premises and side conditions: Scores and observation counts are ideal real-valued symbolic parameters. Every inverse requires its explicitly stated nonzero denominator. The algebraic conclusions are valid for signed correlations wherever the assumptions hold; probabilistic feasibility requires the full PSD covariance domain separately.
 Proof/definition method: Reduce to the canonical rational covariance and sufficient-history formulas, then use Stdlib field and polynomial normalization. No bespoke sums, matrices, or distributions.
 Library reuse: SequentialReport.sequential_d, EquicorrelationSpectral Schur entries, UnequalHistoryLinearPrediction.hp; Stdlib Reals, Field and Psatz.
 Boundary: Deterministic necessary consequences of the Gaussian model; neither the existence of Gaussian random variables nor the measure-theoretic conditional-expectation identity is asserted here.
*)
Theorem d051_schur_contrast_gap : forall n c:R, sequential_d n c<>0 -> equicorr_schur_diagonal n c-equicorr_schur_cross n c=1-c.
Proof.
  intros; cbv [hp sequential_d equicorr_schur_diagonal equicorr_schur_cross] in *; field; nra.
Qed.

(** [d051_schur_diagonal_decomposition] (theorem).
 Mathematical meaning: The diagonal of conditional covariance splits into idiosyncratic and common components.
 Exact checked proposition: forall n c:R, sequential_d n c<>0 -> equicorr_schur_diagonal n c=(1-c)+equicorr_schur_cross n c.
 Premises and side conditions: Scores and observation counts are ideal real-valued symbolic parameters. Every inverse requires its explicitly stated nonzero denominator. The algebraic conclusions are valid for signed correlations wherever the assumptions hold; probabilistic feasibility requires the full PSD covariance domain separately.
 Proof/definition method: Reduce to the canonical rational covariance and sufficient-history formulas, then use Stdlib field and polynomial normalization. No bespoke sums, matrices, or distributions.
 Library reuse: SequentialReport.sequential_d, EquicorrelationSpectral Schur entries, UnequalHistoryLinearPrediction.hp; Stdlib Reals, Field and Psatz.
 Boundary: Deterministic necessary consequences of the Gaussian model; neither the existence of Gaussian random variables nor the measure-theoretic conditional-expectation identity is asserted here.
*)
Theorem d051_schur_diagonal_decomposition : forall n c:R, sequential_d n c<>0 -> equicorr_schur_diagonal n c=(1-c)+equicorr_schur_cross n c.
Proof.
  intros; cbv [hp sequential_d equicorr_schur_diagonal equicorr_schur_cross] in *; field; nra.
Qed.

(** [d051_schur_common_mode] (theorem).
 Mathematical meaning: The k-future-score common eigenvalue is the full-to-observed covariance ratio.
 Exact checked proposition: forall n k c:R, sequential_d n c<>0 -> equicorr_schur_diagonal n c+(k-1)*equicorr_schur_cross n c=(1-c)*sequential_d (n+k) c/sequential_d n c.
 Premises and side conditions: Scores and observation counts are ideal real-valued symbolic parameters. Every inverse requires its explicitly stated nonzero denominator. The algebraic conclusions are valid for signed correlations wherever the assumptions hold; probabilistic feasibility requires the full PSD covariance domain separately.
 Proof/definition method: Reduce to the canonical rational covariance and sufficient-history formulas, then use Stdlib field and polynomial normalization. No bespoke sums, matrices, or distributions.
 Library reuse: SequentialReport.sequential_d, EquicorrelationSpectral Schur entries, UnequalHistoryLinearPrediction.hp; Stdlib Reals, Field and Psatz.
 Boundary: Deterministic necessary consequences of the Gaussian model; neither the existence of Gaussian random variables nor the measure-theoretic conditional-expectation identity is asserted here.
*)
Theorem d051_schur_common_mode : forall n k c:R, sequential_d n c<>0 -> equicorr_schur_diagonal n c+(k-1)*equicorr_schur_cross n c=(1-c)*sequential_d (n+k) c/sequential_d n c.
Proof.
  intros; cbv [hp sequential_d equicorr_schur_diagonal equicorr_schur_cross] in *; field; nra.
Qed.

(** [d051_schur_future_sum_variance] (theorem).
 Mathematical meaning: Predictive variance for the sum of k future scores is the common-mode eigenvalue times k.
 Exact checked proposition: forall n k c:R, sequential_d n c<>0 -> k*equicorr_schur_diagonal n c+k*(k-1)*equicorr_schur_cross n c=k*(1-c)*sequential_d (n+k) c/sequential_d n c.
 Premises and side conditions: Scores and observation counts are ideal real-valued symbolic parameters. Every inverse requires its explicitly stated nonzero denominator. The algebraic conclusions are valid for signed correlations wherever the assumptions hold; probabilistic feasibility requires the full PSD covariance domain separately.
 Proof/definition method: Reduce to the canonical rational covariance and sufficient-history formulas, then use Stdlib field and polynomial normalization. No bespoke sums, matrices, or distributions.
 Library reuse: SequentialReport.sequential_d, EquicorrelationSpectral Schur entries, UnequalHistoryLinearPrediction.hp; Stdlib Reals, Field and Psatz.
 Boundary: Deterministic necessary consequences of the Gaussian model; neither the existence of Gaussian random variables nor the measure-theoretic conditional-expectation identity is asserted here.
*)
Theorem d051_schur_future_sum_variance : forall n k c:R, sequential_d n c<>0 -> k*equicorr_schur_diagonal n c+k*(k-1)*equicorr_schur_cross n c=k*(1-c)*sequential_d (n+k) c/sequential_d n c.
Proof.
  intros; cbv [hp sequential_d equicorr_schur_diagonal equicorr_schur_cross] in *; field; nra.
Qed.

(** [d051_schur_future_mean_variance] (theorem).
 Mathematical meaning: Variance of the future-batch average scales as the common-mode eigenvalue divided by k.
 Exact checked proposition: forall n k c:R, k<>0 -> sequential_d n c<>0 -> (k*equicorr_schur_diagonal n c+k*(k-1)*equicorr_schur_cross n c)/(k*k)=(1-c)*sequential_d (n+k) c/(k*sequential_d n c).
 Premises and side conditions: Scores and observation counts are ideal real-valued symbolic parameters. Every inverse requires its explicitly stated nonzero denominator. The algebraic conclusions are valid for signed correlations wherever the assumptions hold; probabilistic feasibility requires the full PSD covariance domain separately.
 Proof/definition method: Reduce to the canonical rational covariance and sufficient-history formulas, then use Stdlib field and polynomial normalization. No bespoke sums, matrices, or distributions.
 Library reuse: SequentialReport.sequential_d, EquicorrelationSpectral Schur entries, UnequalHistoryLinearPrediction.hp; Stdlib Reals, Field and Psatz.
 Boundary: Deterministic necessary consequences of the Gaussian model; neither the existence of Gaussian random variables nor the measure-theoretic conditional-expectation identity is asserted here.
*)
Theorem d051_schur_future_mean_variance : forall n k c:R, k<>0 -> sequential_d n c<>0 -> (k*equicorr_schur_diagonal n c+k*(k-1)*equicorr_schur_cross n c)/(k*k)=(1-c)*sequential_d (n+k) c/(k*sequential_d n c).
Proof.
  intros; cbv [hp sequential_d equicorr_schur_diagonal equicorr_schur_cross] in *; field; nra.
Qed.

(** [d051_schur_first_diagonal] (theorem).
 Mathematical meaning: One observed score produces the usual two-dimensional Gaussian regression residual variance.
 Exact checked proposition: forall c:R, equicorr_schur_diagonal 1 c=1-c*c.
 Premises and side conditions: Scores and observation counts are ideal real-valued symbolic parameters. Every inverse requires its explicitly stated nonzero denominator. The algebraic conclusions are valid for signed correlations wherever the assumptions hold; probabilistic feasibility requires the full PSD covariance domain separately.
 Proof/definition method: Reduce to the canonical rational covariance and sufficient-history formulas, then use Stdlib field and polynomial normalization. No bespoke sums, matrices, or distributions.
 Library reuse: SequentialReport.sequential_d, EquicorrelationSpectral Schur entries, UnequalHistoryLinearPrediction.hp; Stdlib Reals, Field and Psatz.
 Boundary: Deterministic necessary consequences of the Gaussian model; neither the existence of Gaussian random variables nor the measure-theoretic conditional-expectation identity is asserted here.
*)
Theorem d051_schur_first_diagonal : forall c:R, equicorr_schur_diagonal 1 c=1-c*c.
Proof.
  intros; cbv [hp sequential_d equicorr_schur_diagonal equicorr_schur_cross] in *; field; nra.
Qed.

(** [d051_schur_first_cross] (theorem).
 Mathematical meaning: One observed score produces the exact future-pair cross-covariance.
 Exact checked proposition: forall c:R, equicorr_schur_cross 1 c=c*(1-c).
 Premises and side conditions: Scores and observation counts are ideal real-valued symbolic parameters. Every inverse requires its explicitly stated nonzero denominator. The algebraic conclusions are valid for signed correlations wherever the assumptions hold; probabilistic feasibility requires the full PSD covariance domain separately.
 Proof/definition method: Reduce to the canonical rational covariance and sufficient-history formulas, then use Stdlib field and polynomial normalization. No bespoke sums, matrices, or distributions.
 Library reuse: SequentialReport.sequential_d, EquicorrelationSpectral Schur entries, UnequalHistoryLinearPrediction.hp; Stdlib Reals, Field and Psatz.
 Boundary: Deterministic necessary consequences of the Gaussian model; neither the existence of Gaussian random variables nor the measure-theoretic conditional-expectation identity is asserted here.
*)
Theorem d051_schur_first_cross : forall c:R, equicorr_schur_cross 1 c=c*(1-c).
Proof.
  intros; cbv [hp sequential_d equicorr_schur_diagonal equicorr_schur_cross] in *; field; nra.
Qed.

(** [d051_schur_second_diagonal] (theorem).
 Mathematical meaning: Two observed scores give an explicit future residual variance including negative correlation.
 Exact checked proposition: forall c:R, 1+c<>0 -> equicorr_schur_diagonal 2 c=(1-c)*(1+2*c)/(1+c).
 Premises and side conditions: Scores and observation counts are ideal real-valued symbolic parameters. Every inverse requires its explicitly stated nonzero denominator. The algebraic conclusions are valid for signed correlations wherever the assumptions hold; probabilistic feasibility requires the full PSD covariance domain separately.
 Proof/definition method: Reduce to the canonical rational covariance and sufficient-history formulas, then use Stdlib field and polynomial normalization. No bespoke sums, matrices, or distributions.
 Library reuse: SequentialReport.sequential_d, EquicorrelationSpectral Schur entries, UnequalHistoryLinearPrediction.hp; Stdlib Reals, Field and Psatz.
 Boundary: Deterministic necessary consequences of the Gaussian model; neither the existence of Gaussian random variables nor the measure-theoretic conditional-expectation identity is asserted here.
*)
Theorem d051_schur_second_diagonal : forall c:R, 1+c<>0 -> equicorr_schur_diagonal 2 c=(1-c)*(1+2*c)/(1+c).
Proof.
  intros; cbv [hp sequential_d equicorr_schur_diagonal equicorr_schur_cross] in *; field; nra.
Qed.

(** [d051_schur_second_cross] (theorem).
 Mathematical meaning: Two observed scores yield an explicit signed cross-covariance.
 Exact checked proposition: forall c:R, 1+c<>0 -> equicorr_schur_cross 2 c=c*(1-c)/(1+c).
 Premises and side conditions: Scores and observation counts are ideal real-valued symbolic parameters. Every inverse requires its explicitly stated nonzero denominator. The algebraic conclusions are valid for signed correlations wherever the assumptions hold; probabilistic feasibility requires the full PSD covariance domain separately.
 Proof/definition method: Reduce to the canonical rational covariance and sufficient-history formulas, then use Stdlib field and polynomial normalization. No bespoke sums, matrices, or distributions.
 Library reuse: SequentialReport.sequential_d, EquicorrelationSpectral Schur entries, UnequalHistoryLinearPrediction.hp; Stdlib Reals, Field and Psatz.
 Boundary: Deterministic necessary consequences of the Gaussian model; neither the existence of Gaussian random variables nor the measure-theoretic conditional-expectation identity is asserted here.
*)
Theorem d051_schur_second_cross : forall c:R, 1+c<>0 -> equicorr_schur_cross 2 c=c*(1-c)/(1+c).
Proof.
  intros; cbv [hp sequential_d equicorr_schur_diagonal equicorr_schur_cross] in *; field; nra.
Qed.

(** [d051_mean_update] (theorem).
 Mathematical meaning: The posterior mean after a new data batch is an exact weighted update of the previous mean.
 Exact checked proposition: forall n k c s t:R, sequential_d n c<>0 -> sequential_d (n+k) c<>0 -> hp (n+k) c (s+t)=(sequential_d n c*hp n c s+c*t)/sequential_d (n+k) c.
 Premises and side conditions: Scores and observation counts are ideal real-valued symbolic parameters. Every inverse requires its explicitly stated nonzero denominator. The algebraic conclusions are valid for signed correlations wherever the assumptions hold; probabilistic feasibility requires the full PSD covariance domain separately.
 Proof/definition method: Reduce to the canonical rational covariance and sufficient-history formulas, then use Stdlib field and polynomial normalization. No bespoke sums, matrices, or distributions.
 Library reuse: SequentialReport.sequential_d, EquicorrelationSpectral Schur entries, UnequalHistoryLinearPrediction.hp; Stdlib Reals, Field and Psatz.
 Boundary: Deterministic necessary consequences of the Gaussian model; neither the existence of Gaussian random variables nor the measure-theoretic conditional-expectation identity is asserted here.
*)
Theorem d051_mean_update : forall n k c s t:R, sequential_d n c<>0 -> sequential_d (n+k) c<>0 -> hp (n+k) c (s+t)=(sequential_d n c*hp n c s+c*t)/sequential_d (n+k) c.
Proof.
  intros; cbv [hp sequential_d equicorr_schur_diagonal equicorr_schur_cross] in *; field; nra.
Qed.

(** [d051_mean_update_delta] (theorem).
 Mathematical meaning: The posterior-mean innovation is the new batch sum minus its previous conditional forecast.
 Exact checked proposition: forall n k c s t:R, sequential_d n c<>0 -> sequential_d (n+k) c<>0 -> hp (n+k) c (s+t)-hp n c s=c*(sequential_d n c*t-k*c*s)/(sequential_d n c*sequential_d (n+k) c).
 Premises and side conditions: Scores and observation counts are ideal real-valued symbolic parameters. Every inverse requires its explicitly stated nonzero denominator. The algebraic conclusions are valid for signed correlations wherever the assumptions hold; probabilistic feasibility requires the full PSD covariance domain separately.
 Proof/definition method: Reduce to the canonical rational covariance and sufficient-history formulas, then use Stdlib field and polynomial normalization. No bespoke sums, matrices, or distributions.
 Library reuse: SequentialReport.sequential_d, EquicorrelationSpectral Schur entries, UnequalHistoryLinearPrediction.hp; Stdlib Reals, Field and Psatz.
 Boundary: Deterministic necessary consequences of the Gaussian model; neither the existence of Gaussian random variables nor the measure-theoretic conditional-expectation identity is asserted here.
*)
Theorem d051_mean_update_delta : forall n k c s t:R, sequential_d n c<>0 -> sequential_d (n+k) c<>0 -> hp (n+k) c (s+t)-hp n c s=c*(sequential_d n c*t-k*c*s)/(sequential_d n c*sequential_d (n+k) c).
Proof.
  intros; cbv [hp sequential_d equicorr_schur_diagonal equicorr_schur_cross] in *; field; nra.
Qed.

(** [d051_mean_same_sum_update] (theorem).
 Mathematical meaning: Appending zero-sum observations shrinks the same observed score sum toward zero when c is positive.
 Exact checked proposition: forall n k c s:R, sequential_d n c<>0 -> sequential_d (n+k) c<>0 -> hp (n+k) c s=hp n c s-k*c*c*s/(sequential_d n c*sequential_d (n+k) c).
 Premises and side conditions: Scores and observation counts are ideal real-valued symbolic parameters. Every inverse requires its explicitly stated nonzero denominator. The algebraic conclusions are valid for signed correlations wherever the assumptions hold; probabilistic feasibility requires the full PSD covariance domain separately.
 Proof/definition method: Reduce to the canonical rational covariance and sufficient-history formulas, then use Stdlib field and polynomial normalization. No bespoke sums, matrices, or distributions.
 Library reuse: SequentialReport.sequential_d, EquicorrelationSpectral Schur entries, UnequalHistoryLinearPrediction.hp; Stdlib Reals, Field and Psatz.
 Boundary: Deterministic necessary consequences of the Gaussian model; neither the existence of Gaussian random variables nor the measure-theoretic conditional-expectation identity is asserted here.
*)
Theorem d051_mean_same_sum_update : forall n k c s:R, sequential_d n c<>0 -> sequential_d (n+k) c<>0 -> hp (n+k) c s=hp n c s-k*c*c*s/(sequential_d n c*sequential_d (n+k) c).
Proof.
  intros; cbv [hp sequential_d equicorr_schur_diagonal equicorr_schur_cross] in *; field; nra.
Qed.

(** [d051_mean_telescope] (theorem).
 Mathematical meaning: Pooling two added batches agrees with the direct Gaussian posterior mean from the initial history.
 Exact checked proposition: forall n k l c s t u:R, sequential_d n c<>0 -> sequential_d (n+k+l) c<>0 -> hp (n+k+l) c (s+t+u)=(sequential_d n c*hp n c s+c*(t+u))/sequential_d (n+k+l) c.
 Premises and side conditions: Scores and observation counts are ideal real-valued symbolic parameters. Every inverse requires its explicitly stated nonzero denominator. The algebraic conclusions are valid for signed correlations wherever the assumptions hold; probabilistic feasibility requires the full PSD covariance domain separately.
 Proof/definition method: Reduce to the canonical rational covariance and sufficient-history formulas, then use Stdlib field and polynomial normalization. No bespoke sums, matrices, or distributions.
 Library reuse: SequentialReport.sequential_d, EquicorrelationSpectral Schur entries, UnequalHistoryLinearPrediction.hp; Stdlib Reals, Field and Psatz.
 Boundary: Deterministic necessary consequences of the Gaussian model; neither the existence of Gaussian random variables nor the measure-theoretic conditional-expectation identity is asserted here.
*)
Theorem d051_mean_telescope : forall n k l c s t u:R, sequential_d n c<>0 -> sequential_d (n+k+l) c<>0 -> hp (n+k+l) c (s+t+u)=(sequential_d n c*hp n c s+c*(t+u))/sequential_d (n+k+l) c.
Proof.
  intros; cbv [hp sequential_d equicorr_schur_diagonal equicorr_schur_cross] in *; field; nra.
Qed.

(** [d051_mean_update_gain] (theorem).
 Mathematical meaning: The normalized Gaussian update has exact old-predictor and new-observation coefficients.
 Exact checked proposition: forall n k c s t:R, sequential_d n c<>0 -> sequential_d (n+k) c<>0 -> hp (n+k) c (s+t)=sequential_d n c/sequential_d (n+k) c*hp n c s+c*t/sequential_d (n+k) c.
 Premises and side conditions: Scores and observation counts are ideal real-valued symbolic parameters. Every inverse requires its explicitly stated nonzero denominator. The algebraic conclusions are valid for signed correlations wherever the assumptions hold; probabilistic feasibility requires the full PSD covariance domain separately.
 Proof/definition method: Reduce to the canonical rational covariance and sufficient-history formulas, then use Stdlib field and polynomial normalization. No bespoke sums, matrices, or distributions.
 Library reuse: SequentialReport.sequential_d, EquicorrelationSpectral Schur entries, UnequalHistoryLinearPrediction.hp; Stdlib Reals, Field and Psatz.
 Boundary: Deterministic necessary consequences of the Gaussian model; neither the existence of Gaussian random variables nor the measure-theoretic conditional-expectation identity is asserted here.
*)
Theorem d051_mean_update_gain : forall n k c s t:R, sequential_d n c<>0 -> sequential_d (n+k) c<>0 -> hp (n+k) c (s+t)=sequential_d n c/sequential_d (n+k) c*hp n c s+c*t/sequential_d (n+k) c.
Proof.
  intros; cbv [hp sequential_d equicorr_schur_diagonal equicorr_schur_cross] in *; field; nra.
Qed.

(** [d051_mean_increment_zero] (theorem).
 Mathematical meaning: A new batch equal to its predicted total is an exact posterior fixed point.
 Exact checked proposition: forall n k c s:R, sequential_d n c<>0 -> sequential_d (n+k) c<>0 -> hp (n+k) c (s+k*hp n c s)=hp n c s.
 Premises and side conditions: Scores and observation counts are ideal real-valued symbolic parameters. Every inverse requires its explicitly stated nonzero denominator. The algebraic conclusions are valid for signed correlations wherever the assumptions hold; probabilistic feasibility requires the full PSD covariance domain separately.
 Proof/definition method: Reduce to the canonical rational covariance and sufficient-history formulas, then use Stdlib field and polynomial normalization. No bespoke sums, matrices, or distributions.
 Library reuse: SequentialReport.sequential_d, EquicorrelationSpectral Schur entries, UnequalHistoryLinearPrediction.hp; Stdlib Reals, Field and Psatz.
 Boundary: Deterministic necessary consequences of the Gaussian model; neither the existence of Gaussian random variables nor the measure-theoretic conditional-expectation identity is asserted here.
*)
Theorem d051_mean_increment_zero : forall n k c s:R, sequential_d n c<>0 -> sequential_d (n+k) c<>0 -> hp (n+k) c (s+k*hp n c s)=hp n c s.
Proof.
  intros; cbv [hp sequential_d equicorr_schur_diagonal equicorr_schur_cross] in *; field; nra.
Qed.

(** [d051_mean_one_score_update] (theorem).
 Mathematical meaning: A single new score updates the Gaussian posterior mean with a one-step gain.
 Exact checked proposition: forall n c s x:R, sequential_d n c<>0 -> sequential_d (n+1) c<>0 -> hp (n+1) c (s+x)=(sequential_d n c*hp n c s+c*x)/sequential_d (n+1) c.
 Premises and side conditions: Scores and observation counts are ideal real-valued symbolic parameters. Every inverse requires its explicitly stated nonzero denominator. The algebraic conclusions are valid for signed correlations wherever the assumptions hold; probabilistic feasibility requires the full PSD covariance domain separately.
 Proof/definition method: Reduce to the canonical rational covariance and sufficient-history formulas, then use Stdlib field and polynomial normalization. No bespoke sums, matrices, or distributions.
 Library reuse: SequentialReport.sequential_d, EquicorrelationSpectral Schur entries, UnequalHistoryLinearPrediction.hp; Stdlib Reals, Field and Psatz.
 Boundary: Deterministic necessary consequences of the Gaussian model; neither the existence of Gaussian random variables nor the measure-theoretic conditional-expectation identity is asserted here.
*)
Theorem d051_mean_one_score_update : forall n c s x:R, sequential_d n c<>0 -> sequential_d (n+1) c<>0 -> hp (n+1) c (s+x)=(sequential_d n c*hp n c s+c*x)/sequential_d (n+1) c.
Proof.
  intros; cbv [hp sequential_d equicorr_schur_diagonal equicorr_schur_cross] in *; field; nra.
Qed.

(** [d051_mean_one_score_innovation] (theorem).
 Mathematical meaning: The single-observation posterior correction is proportional to its prediction innovation.
 Exact checked proposition: forall n c s x:R, sequential_d n c<>0 -> sequential_d (n+1) c<>0 -> hp (n+1) c (s+x)-hp n c s=c*(x-hp n c s)/sequential_d (n+1) c.
 Premises and side conditions: Scores and observation counts are ideal real-valued symbolic parameters. Every inverse requires its explicitly stated nonzero denominator. The algebraic conclusions are valid for signed correlations wherever the assumptions hold; probabilistic feasibility requires the full PSD covariance domain separately.
 Proof/definition method: Reduce to the canonical rational covariance and sufficient-history formulas, then use Stdlib field and polynomial normalization. No bespoke sums, matrices, or distributions.
 Library reuse: SequentialReport.sequential_d, EquicorrelationSpectral Schur entries, UnequalHistoryLinearPrediction.hp; Stdlib Reals, Field and Psatz.
 Boundary: Deterministic necessary consequences of the Gaussian model; neither the existence of Gaussian random variables nor the measure-theoretic conditional-expectation identity is asserted here.
*)
Theorem d051_mean_one_score_innovation : forall n c s x:R, sequential_d n c<>0 -> sequential_d (n+1) c<>0 -> hp (n+1) c (s+x)-hp n c s=c*(x-hp n c s)/sequential_d (n+1) c.
Proof.
  intros; cbv [hp sequential_d equicorr_schur_diagonal equicorr_schur_cross] in *; field; nra.
Qed.

(** [d051_mean_two_score_update] (theorem).
 Mathematical meaning: Two new scores can be assimilated by a single pooled posterior update.
 Exact checked proposition: forall n c s x y:R, sequential_d n c<>0 -> sequential_d (n+2) c<>0 -> hp (n+2) c (s+x+y)=(sequential_d n c*hp n c s+c*(x+y))/sequential_d (n+2) c.
 Premises and side conditions: Scores and observation counts are ideal real-valued symbolic parameters. Every inverse requires its explicitly stated nonzero denominator. The algebraic conclusions are valid for signed correlations wherever the assumptions hold; probabilistic feasibility requires the full PSD covariance domain separately.
 Proof/definition method: Reduce to the canonical rational covariance and sufficient-history formulas, then use Stdlib field and polynomial normalization. No bespoke sums, matrices, or distributions.
 Library reuse: SequentialReport.sequential_d, EquicorrelationSpectral Schur entries, UnequalHistoryLinearPrediction.hp; Stdlib Reals, Field and Psatz.
 Boundary: Deterministic necessary consequences of the Gaussian model; neither the existence of Gaussian random variables nor the measure-theoretic conditional-expectation identity is asserted here.
*)
Theorem d051_mean_two_score_update : forall n c s x y:R, sequential_d n c<>0 -> sequential_d (n+2) c<>0 -> hp (n+2) c (s+x+y)=(sequential_d n c*hp n c s+c*(x+y))/sequential_d (n+2) c.
Proof.
  intros; cbv [hp sequential_d equicorr_schur_diagonal equicorr_schur_cross] in *; field; nra.
Qed.

(** [d051_mean_two_score_innovation] (theorem).
 Mathematical meaning: The two-score update depends only on the aggregate deviation from the previous predictor.
 Exact checked proposition: forall n c s x y:R, sequential_d n c<>0 -> sequential_d (n+2) c<>0 -> hp (n+2) c (s+x+y)-hp n c s=c*(x+y-2*hp n c s)/sequential_d (n+2) c.
 Premises and side conditions: Scores and observation counts are ideal real-valued symbolic parameters. Every inverse requires its explicitly stated nonzero denominator. The algebraic conclusions are valid for signed correlations wherever the assumptions hold; probabilistic feasibility requires the full PSD covariance domain separately.
 Proof/definition method: Reduce to the canonical rational covariance and sufficient-history formulas, then use Stdlib field and polynomial normalization. No bespoke sums, matrices, or distributions.
 Library reuse: SequentialReport.sequential_d, EquicorrelationSpectral Schur entries, UnequalHistoryLinearPrediction.hp; Stdlib Reals, Field and Psatz.
 Boundary: Deterministic necessary consequences of the Gaussian model; neither the existence of Gaussian random variables nor the measure-theoretic conditional-expectation identity is asserted here.
*)
Theorem d051_mean_two_score_innovation : forall n c s x y:R, sequential_d n c<>0 -> sequential_d (n+2) c<>0 -> hp (n+2) c (s+x+y)-hp n c s=c*(x+y-2*hp n c s)/sequential_d (n+2) c.
Proof.
  intros; cbv [hp sequential_d equicorr_schur_diagonal equicorr_schur_cross] in *; field; nra.
Qed.
