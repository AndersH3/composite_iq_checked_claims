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
  UnequalHistoryLinearPrediction GaussianConditionalKernel.
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


(** [d051_d_at_zero] (theorem).
 Mathematical meaning: Zero previous observations leave precisely the contrast eigenvalue in the denominator.
 Exact checked proposition: forall c:R, sequential_d 0 c=1-c.
 Premises and side conditions: Algebraic score counts are real scalars, with signed correlation admitted only where explicitly used inverses are nonzero. For probabilistic readings the positive-semidefinite joint covariance domain must also be established. Nothing here implicitly grants a Gaussian joint distribution.
 Proof/definition method: Normalize canonical Schur complement, history-prediction and posterior variance formulas using Rocq Stdlib Field and polynomial algebra, with no new probability axioms or bespoke finite sums.
 Library reuse: SequentialReport, EquicorrelationSpectral, UnequalHistoryLinearPrediction, GaussianConditionalKernel and Rocq Stdlib Reals/Field/Psatz.
 Boundary: The result is deterministic regression or covariance algebra, not a proof of regular conditional probability, normality or measure-theoretic conditional expectation.
*)
Theorem d051_d_at_zero : forall c:R, sequential_d 0 c=1-c.
Proof.
  intros; cbv [hp sequential_prediction sequential_d equicorr_schur_diagonal equicorr_schur_cross gk_variance gk_d gk_mass gk_precision] in *; field; nra.
Qed.

(** [d051_d_at_one] (theorem).
 Mathematical meaning: The covariance of a single standardized score is independent of its off-diagonal correlation.
 Exact checked proposition: forall c:R, sequential_d 1 c=1.
 Premises and side conditions: Algebraic score counts are real scalars, with signed correlation admitted only where explicitly used inverses are nonzero. For probabilistic readings the positive-semidefinite joint covariance domain must also be established. Nothing here implicitly grants a Gaussian joint distribution.
 Proof/definition method: Normalize canonical Schur complement, history-prediction and posterior variance formulas using Rocq Stdlib Field and polynomial algebra, with no new probability axioms or bespoke finite sums.
 Library reuse: SequentialReport, EquicorrelationSpectral, UnequalHistoryLinearPrediction, GaussianConditionalKernel and Rocq Stdlib Reals/Field/Psatz.
 Boundary: The result is deterministic regression or covariance algebra, not a proof of regular conditional probability, normality or measure-theoretic conditional expectation.
*)
Theorem d051_d_at_one : forall c:R, sequential_d 1 c=1.
Proof.
  intros; cbv [hp sequential_prediction sequential_d equicorr_schur_diagonal equicorr_schur_cross gk_variance gk_d gk_mass gk_precision] in *; field; nra.
Qed.

(** [d051_d_at_two] (theorem).
 Mathematical meaning: The two-score common eigenvalue is the usual 1+c.
 Exact checked proposition: forall c:R, sequential_d 2 c=1+c.
 Premises and side conditions: Algebraic score counts are real scalars, with signed correlation admitted only where explicitly used inverses are nonzero. For probabilistic readings the positive-semidefinite joint covariance domain must also be established. Nothing here implicitly grants a Gaussian joint distribution.
 Proof/definition method: Normalize canonical Schur complement, history-prediction and posterior variance formulas using Rocq Stdlib Field and polynomial algebra, with no new probability axioms or bespoke finite sums.
 Library reuse: SequentialReport, EquicorrelationSpectral, UnequalHistoryLinearPrediction, GaussianConditionalKernel and Rocq Stdlib Reals/Field/Psatz.
 Boundary: The result is deterministic regression or covariance algebra, not a proof of regular conditional probability, normality or measure-theoretic conditional expectation.
*)
Theorem d051_d_at_two : forall c:R, sequential_d 2 c=1+c.
Proof.
  intros; cbv [hp sequential_prediction sequential_d equicorr_schur_diagonal equicorr_schur_cross gk_variance gk_d gk_mass gk_precision] in *; field; nra.
Qed.

(** [d051_d_at_three] (theorem).
 Mathematical meaning: Three-score common-mode covariance depends on twice the pairwise correlation.
 Exact checked proposition: forall c:R, sequential_d 3 c=1+2*c.
 Premises and side conditions: Algebraic score counts are real scalars, with signed correlation admitted only where explicitly used inverses are nonzero. For probabilistic readings the positive-semidefinite joint covariance domain must also be established. Nothing here implicitly grants a Gaussian joint distribution.
 Proof/definition method: Normalize canonical Schur complement, history-prediction and posterior variance formulas using Rocq Stdlib Field and polynomial algebra, with no new probability axioms or bespoke finite sums.
 Library reuse: SequentialReport, EquicorrelationSpectral, UnequalHistoryLinearPrediction, GaussianConditionalKernel and Rocq Stdlib Reals/Field/Psatz.
 Boundary: The result is deterministic regression or covariance algebra, not a proof of regular conditional probability, normality or measure-theoretic conditional expectation.
*)
Theorem d051_d_at_three : forall c:R, sequential_d 3 c=1+2*c.
Proof.
  intros; cbv [hp sequential_prediction sequential_d equicorr_schur_diagonal equicorr_schur_cross gk_variance gk_d gk_mass gk_precision] in *; field; nra.
Qed.

(** [d051_d_at_four] (theorem).
 Mathematical meaning: Four-score common-mode covariance depends on three pairwise cross-covariances.
 Exact checked proposition: forall c:R, sequential_d 4 c=1+3*c.
 Premises and side conditions: Algebraic score counts are real scalars, with signed correlation admitted only where explicitly used inverses are nonzero. For probabilistic readings the positive-semidefinite joint covariance domain must also be established. Nothing here implicitly grants a Gaussian joint distribution.
 Proof/definition method: Normalize canonical Schur complement, history-prediction and posterior variance formulas using Rocq Stdlib Field and polynomial algebra, with no new probability axioms or bespoke finite sums.
 Library reuse: SequentialReport, EquicorrelationSpectral, UnequalHistoryLinearPrediction, GaussianConditionalKernel and Rocq Stdlib Reals/Field/Psatz.
 Boundary: The result is deterministic regression or covariance algebra, not a proof of regular conditional probability, normality or measure-theoretic conditional expectation.
*)
Theorem d051_d_at_four : forall c:R, sequential_d 4 c=1+3*c.
Proof.
  intros; cbv [hp sequential_prediction sequential_d equicorr_schur_diagonal equicorr_schur_cross gk_variance gk_d gk_mass gk_precision] in *; field; nra.
Qed.

(** [d051_d_at_five] (theorem).
 Mathematical meaning: Five-score covariance has the explicit common eigenvalue used in finite-history certificates.
 Exact checked proposition: forall c:R, sequential_d 5 c=1+4*c.
 Premises and side conditions: Algebraic score counts are real scalars, with signed correlation admitted only where explicitly used inverses are nonzero. For probabilistic readings the positive-semidefinite joint covariance domain must also be established. Nothing here implicitly grants a Gaussian joint distribution.
 Proof/definition method: Normalize canonical Schur complement, history-prediction and posterior variance formulas using Rocq Stdlib Field and polynomial algebra, with no new probability axioms or bespoke finite sums.
 Library reuse: SequentialReport, EquicorrelationSpectral, UnequalHistoryLinearPrediction, GaussianConditionalKernel and Rocq Stdlib Reals/Field/Psatz.
 Boundary: The result is deterministic regression or covariance algebra, not a proof of regular conditional probability, normality or measure-theoretic conditional expectation.
*)
Theorem d051_d_at_five : forall c:R, sequential_d 5 c=1+4*c.
Proof.
  intros; cbv [hp sequential_prediction sequential_d equicorr_schur_diagonal equicorr_schur_cross gk_variance gk_d gk_mass gk_precision] in *; field; nra.
Qed.

(** [d051_d_successor] (theorem).
 Mathematical meaning: One new test shifts the covariance common mode by c.
 Exact checked proposition: forall n c:R, sequential_d (n+1) c=sequential_d n c+c.
 Premises and side conditions: Algebraic score counts are real scalars, with signed correlation admitted only where explicitly used inverses are nonzero. For probabilistic readings the positive-semidefinite joint covariance domain must also be established. Nothing here implicitly grants a Gaussian joint distribution.
 Proof/definition method: Normalize canonical Schur complement, history-prediction and posterior variance formulas using Rocq Stdlib Field and polynomial algebra, with no new probability axioms or bespoke finite sums.
 Library reuse: SequentialReport, EquicorrelationSpectral, UnequalHistoryLinearPrediction, GaussianConditionalKernel and Rocq Stdlib Reals/Field/Psatz.
 Boundary: The result is deterministic regression or covariance algebra, not a proof of regular conditional probability, normality or measure-theoretic conditional expectation.
*)
Theorem d051_d_successor : forall n c:R, sequential_d (n+1) c=sequential_d n c+c.
Proof.
  intros; cbv [hp sequential_prediction sequential_d equicorr_schur_diagonal equicorr_schur_cross gk_variance gk_d gk_mass gk_precision] in *; field; nra.
Qed.

(** [d051_d_two_successors] (theorem).
 Mathematical meaning: Two new tests shift the covariance common mode by two correlations.
 Exact checked proposition: forall n c:R, sequential_d (n+2) c=sequential_d n c+2*c.
 Premises and side conditions: Algebraic score counts are real scalars, with signed correlation admitted only where explicitly used inverses are nonzero. For probabilistic readings the positive-semidefinite joint covariance domain must also be established. Nothing here implicitly grants a Gaussian joint distribution.
 Proof/definition method: Normalize canonical Schur complement, history-prediction and posterior variance formulas using Rocq Stdlib Field and polynomial algebra, with no new probability axioms or bespoke finite sums.
 Library reuse: SequentialReport, EquicorrelationSpectral, UnequalHistoryLinearPrediction, GaussianConditionalKernel and Rocq Stdlib Reals/Field/Psatz.
 Boundary: The result is deterministic regression or covariance algebra, not a proof of regular conditional probability, normality or measure-theoretic conditional expectation.
*)
Theorem d051_d_two_successors : forall n c:R, sequential_d (n+2) c=sequential_d n c+2*c.
Proof.
  intros; cbv [hp sequential_prediction sequential_d equicorr_schur_diagonal equicorr_schur_cross gk_variance gk_d gk_mass gk_precision] in *; field; nra.
Qed.

(** [d051_d_three_successors] (theorem).
 Mathematical meaning: A three-test admission batch has an explicit common-mode eigenvalue update.
 Exact checked proposition: forall n c:R, sequential_d (n+3) c=sequential_d n c+3*c.
 Premises and side conditions: Algebraic score counts are real scalars, with signed correlation admitted only where explicitly used inverses are nonzero. For probabilistic readings the positive-semidefinite joint covariance domain must also be established. Nothing here implicitly grants a Gaussian joint distribution.
 Proof/definition method: Normalize canonical Schur complement, history-prediction and posterior variance formulas using Rocq Stdlib Field and polynomial algebra, with no new probability axioms or bespoke finite sums.
 Library reuse: SequentialReport, EquicorrelationSpectral, UnequalHistoryLinearPrediction, GaussianConditionalKernel and Rocq Stdlib Reals/Field/Psatz.
 Boundary: The result is deterministic regression or covariance algebra, not a proof of regular conditional probability, normality or measure-theoretic conditional expectation.
*)
Theorem d051_d_three_successors : forall n c:R, sequential_d (n+3) c=sequential_d n c+3*c.
Proof.
  intros; cbv [hp sequential_prediction sequential_d equicorr_schur_diagonal equicorr_schur_cross gk_variance gk_d gk_mass gk_precision] in *; field; nra.
Qed.

(** [d051_d_correlation_difference] (theorem).
 Mathematical meaning: The sensitivity of common eigenvalue to assumed correlation is proportional to batch length minus one.
 Exact checked proposition: forall n c d:R, sequential_d n c-sequential_d n d=(n-1)*(c-d).
 Premises and side conditions: Algebraic score counts are real scalars, with signed correlation admitted only where explicitly used inverses are nonzero. For probabilistic readings the positive-semidefinite joint covariance domain must also be established. Nothing here implicitly grants a Gaussian joint distribution.
 Proof/definition method: Normalize canonical Schur complement, history-prediction and posterior variance formulas using Rocq Stdlib Field and polynomial algebra, with no new probability axioms or bespoke finite sums.
 Library reuse: SequentialReport, EquicorrelationSpectral, UnequalHistoryLinearPrediction, GaussianConditionalKernel and Rocq Stdlib Reals/Field/Psatz.
 Boundary: The result is deterministic regression or covariance algebra, not a proof of regular conditional probability, normality or measure-theoretic conditional expectation.
*)
Theorem d051_d_correlation_difference : forall n c d:R, sequential_d n c-sequential_d n d=(n-1)*(c-d).
Proof.
  intros; cbv [hp sequential_prediction sequential_d equicorr_schur_diagonal equicorr_schur_cross gk_variance gk_d gk_mass gk_precision] in *; field; nra.
Qed.

(** [d051_d_correlation_perturbation] (theorem).
 Mathematical meaning: A change of the correlation parameter moves the common eigenvalue linearly.
 Exact checked proposition: forall n c h:R, sequential_d n (c+h)=sequential_d n c+(n-1)*h.
 Premises and side conditions: Algebraic score counts are real scalars, with signed correlation admitted only where explicitly used inverses are nonzero. For probabilistic readings the positive-semidefinite joint covariance domain must also be established. Nothing here implicitly grants a Gaussian joint distribution.
 Proof/definition method: Normalize canonical Schur complement, history-prediction and posterior variance formulas using Rocq Stdlib Field and polynomial algebra, with no new probability axioms or bespoke finite sums.
 Library reuse: SequentialReport, EquicorrelationSpectral, UnequalHistoryLinearPrediction, GaussianConditionalKernel and Rocq Stdlib Reals/Field/Psatz.
 Boundary: The result is deterministic regression or covariance algebra, not a proof of regular conditional probability, normality or measure-theoretic conditional expectation.
*)
Theorem d051_d_correlation_perturbation : forall n c h:R, sequential_d n (c+h)=sequential_d n c+(n-1)*h.
Proof.
  intros; cbv [hp sequential_prediction sequential_d equicorr_schur_diagonal equicorr_schur_cross gk_variance gk_d gk_mass gk_precision] in *; field; nra.
Qed.

(** [d051_d_correlation_interpolation] (theorem).
 Mathematical meaning: Common-mode covariance is affine under correlation sensitivity scenarios.
 Exact checked proposition: forall n c d t:R, sequential_d n (t*c+(1-t)*d)=t*sequential_d n c+(1-t)*sequential_d n d.
 Premises and side conditions: Algebraic score counts are real scalars, with signed correlation admitted only where explicitly used inverses are nonzero. For probabilistic readings the positive-semidefinite joint covariance domain must also be established. Nothing here implicitly grants a Gaussian joint distribution.
 Proof/definition method: Normalize canonical Schur complement, history-prediction and posterior variance formulas using Rocq Stdlib Field and polynomial algebra, with no new probability axioms or bespoke finite sums.
 Library reuse: SequentialReport, EquicorrelationSpectral, UnequalHistoryLinearPrediction, GaussianConditionalKernel and Rocq Stdlib Reals/Field/Psatz.
 Boundary: The result is deterministic regression or covariance algebra, not a proof of regular conditional probability, normality or measure-theoretic conditional expectation.
*)
Theorem d051_d_correlation_interpolation : forall n c d t:R, sequential_d n (t*c+(1-t)*d)=t*sequential_d n c+(1-t)*sequential_d n d.
Proof.
  intros; cbv [hp sequential_prediction sequential_d equicorr_schur_diagonal equicorr_schur_cross gk_variance gk_d gk_mass gk_precision] in *; field; nra.
Qed.

(** [d051_d_compensated_blocks] (theorem).
 Mathematical meaning: An added k-score block contributes precisely the excess over the single-score eigenvalue.
 Exact checked proposition: forall n k c:R, sequential_d (n+k) c=sequential_d n c+sequential_d (k+1) c-1.
 Premises and side conditions: Algebraic score counts are real scalars, with signed correlation admitted only where explicitly used inverses are nonzero. For probabilistic readings the positive-semidefinite joint covariance domain must also be established. Nothing here implicitly grants a Gaussian joint distribution.
 Proof/definition method: Normalize canonical Schur complement, history-prediction and posterior variance formulas using Rocq Stdlib Field and polynomial algebra, with no new probability axioms or bespoke finite sums.
 Library reuse: SequentialReport, EquicorrelationSpectral, UnequalHistoryLinearPrediction, GaussianConditionalKernel and Rocq Stdlib Reals/Field/Psatz.
 Boundary: The result is deterministic regression or covariance algebra, not a proof of regular conditional probability, normality or measure-theoretic conditional expectation.
*)
Theorem d051_d_compensated_blocks : forall n k c:R, sequential_d (n+k) c=sequential_d n c+sequential_d (k+1) c-1.
Proof.
  intros; cbv [hp sequential_prediction sequential_d equicorr_schur_diagonal equicorr_schur_cross gk_variance gk_d gk_mass gk_precision] in *; field; nra.
Qed.

(** [d051_d_mixed_zero] (theorem).
 Mathematical meaning: Equicorrelation has zero mixed second increment in independent block counts.
 Exact checked proposition: forall n k l c:R, sequential_d (n+k+l) c-sequential_d (n+k) c-sequential_d (n+l) c+sequential_d n c=0.
 Premises and side conditions: Algebraic score counts are real scalars, with signed correlation admitted only where explicitly used inverses are nonzero. For probabilistic readings the positive-semidefinite joint covariance domain must also be established. Nothing here implicitly grants a Gaussian joint distribution.
 Proof/definition method: Normalize canonical Schur complement, history-prediction and posterior variance formulas using Rocq Stdlib Field and polynomial algebra, with no new probability axioms or bespoke finite sums.
 Library reuse: SequentialReport, EquicorrelationSpectral, UnequalHistoryLinearPrediction, GaussianConditionalKernel and Rocq Stdlib Reals/Field/Psatz.
 Boundary: The result is deterministic regression or covariance algebra, not a proof of regular conditional probability, normality or measure-theoretic conditional expectation.
*)
Theorem d051_d_mixed_zero : forall n k l c:R, sequential_d (n+k+l) c-sequential_d (n+k) c-sequential_d (n+l) c+sequential_d n c=0.
Proof.
  intros; cbv [hp sequential_prediction sequential_d equicorr_schur_diagonal equicorr_schur_cross gk_variance gk_d gk_mass gk_precision] in *; field; nra.
Qed.

(** [d051_d_reverse_difference] (theorem).
 Mathematical meaning: Signed correlation determines the reverse history-size change in the common mode.
 Exact checked proposition: forall n k c:R, sequential_d n c-sequential_d (n+k) c=-(k*c).
 Premises and side conditions: Algebraic score counts are real scalars, with signed correlation admitted only where explicitly used inverses are nonzero. For probabilistic readings the positive-semidefinite joint covariance domain must also be established. Nothing here implicitly grants a Gaussian joint distribution.
 Proof/definition method: Normalize canonical Schur complement, history-prediction and posterior variance formulas using Rocq Stdlib Field and polynomial algebra, with no new probability axioms or bespoke finite sums.
 Library reuse: SequentialReport, EquicorrelationSpectral, UnequalHistoryLinearPrediction, GaussianConditionalKernel and Rocq Stdlib Reals/Field/Psatz.
 Boundary: The result is deterministic regression or covariance algebra, not a proof of regular conditional probability, normality or measure-theoretic conditional expectation.
*)
Theorem d051_d_reverse_difference : forall n k c:R, sequential_d n c-sequential_d (n+k) c=-(k*c).
Proof.
  intros; cbv [hp sequential_prediction sequential_d equicorr_schur_diagonal equicorr_schur_cross gk_variance gk_d gk_mass gk_precision] in *; field; nra.
Qed.

(** [d051_cov_independence_diag] (theorem).
 Mathematical meaning: Independent standardized future scores have conditional variance one for any history length.
 Exact checked proposition: forall n:R, equicorr_schur_diagonal n 0=1.
 Premises and side conditions: Algebraic score counts are real scalars, with signed correlation admitted only where explicitly used inverses are nonzero. For probabilistic readings the positive-semidefinite joint covariance domain must also be established. Nothing here implicitly grants a Gaussian joint distribution.
 Proof/definition method: Normalize canonical Schur complement, history-prediction and posterior variance formulas using Rocq Stdlib Field and polynomial algebra, with no new probability axioms or bespoke finite sums.
 Library reuse: SequentialReport, EquicorrelationSpectral, UnequalHistoryLinearPrediction, GaussianConditionalKernel and Rocq Stdlib Reals/Field/Psatz.
 Boundary: The result is deterministic regression or covariance algebra, not a proof of regular conditional probability, normality or measure-theoretic conditional expectation.
*)
Theorem d051_cov_independence_diag : forall n:R, equicorr_schur_diagonal n 0=1.
Proof.
  intros; cbv [hp sequential_prediction sequential_d equicorr_schur_diagonal equicorr_schur_cross gk_variance gk_d gk_mass gk_precision] in *; field; nra.
Qed.

(** [d051_cov_independence_cross] (theorem).
 Mathematical meaning: Independent standardized future scores have zero residual cross-covariance.
 Exact checked proposition: forall n:R, equicorr_schur_cross n 0=0.
 Premises and side conditions: Algebraic score counts are real scalars, with signed correlation admitted only where explicitly used inverses are nonzero. For probabilistic readings the positive-semidefinite joint covariance domain must also be established. Nothing here implicitly grants a Gaussian joint distribution.
 Proof/definition method: Normalize canonical Schur complement, history-prediction and posterior variance formulas using Rocq Stdlib Field and polynomial algebra, with no new probability axioms or bespoke finite sums.
 Library reuse: SequentialReport, EquicorrelationSpectral, UnequalHistoryLinearPrediction, GaussianConditionalKernel and Rocq Stdlib Reals/Field/Psatz.
 Boundary: The result is deterministic regression or covariance algebra, not a proof of regular conditional probability, normality or measure-theoretic conditional expectation.
*)
Theorem d051_cov_independence_cross : forall n:R, equicorr_schur_cross n 0=0.
Proof.
  intros; cbv [hp sequential_prediction sequential_d equicorr_schur_diagonal equicorr_schur_cross gk_variance gk_d gk_mass gk_precision] in *; field; nra.
Qed.

(** [d051_cov_zero_history_diag] (theorem).
 Mathematical meaning: With no observations the Schur diagonal equals the marginal score variance.
 Exact checked proposition: forall c:R, 1-c<>0 -> equicorr_schur_diagonal 0 c=1.
 Premises and side conditions: Algebraic score counts are real scalars, with signed correlation admitted only where explicitly used inverses are nonzero. For probabilistic readings the positive-semidefinite joint covariance domain must also be established. Nothing here implicitly grants a Gaussian joint distribution.
 Proof/definition method: Normalize canonical Schur complement, history-prediction and posterior variance formulas using Rocq Stdlib Field and polynomial algebra, with no new probability axioms or bespoke finite sums.
 Library reuse: SequentialReport, EquicorrelationSpectral, UnequalHistoryLinearPrediction, GaussianConditionalKernel and Rocq Stdlib Reals/Field/Psatz.
 Boundary: The result is deterministic regression or covariance algebra, not a proof of regular conditional probability, normality or measure-theoretic conditional expectation.
*)
Theorem d051_cov_zero_history_diag : forall c:R, 1-c<>0 -> equicorr_schur_diagonal 0 c=1.
Proof.
  intros; cbv [hp sequential_prediction sequential_d equicorr_schur_diagonal equicorr_schur_cross gk_variance gk_d gk_mass gk_precision] in *; field; nra.
Qed.

(** [d051_cov_zero_history_cross] (theorem).
 Mathematical meaning: With no observations the future cross covariance equals the common marginal covariance.
 Exact checked proposition: forall c:R, 1-c<>0 -> equicorr_schur_cross 0 c=c.
 Premises and side conditions: Algebraic score counts are real scalars, with signed correlation admitted only where explicitly used inverses are nonzero. For probabilistic readings the positive-semidefinite joint covariance domain must also be established. Nothing here implicitly grants a Gaussian joint distribution.
 Proof/definition method: Normalize canonical Schur complement, history-prediction and posterior variance formulas using Rocq Stdlib Field and polynomial algebra, with no new probability axioms or bespoke finite sums.
 Library reuse: SequentialReport, EquicorrelationSpectral, UnequalHistoryLinearPrediction, GaussianConditionalKernel and Rocq Stdlib Reals/Field/Psatz.
 Boundary: The result is deterministic regression or covariance algebra, not a proof of regular conditional probability, normality or measure-theoretic conditional expectation.
*)
Theorem d051_cov_zero_history_cross : forall c:R, 1-c<>0 -> equicorr_schur_cross 0 c=c.
Proof.
  intros; cbv [hp sequential_prediction sequential_d equicorr_schur_diagonal equicorr_schur_cross gk_variance gk_d gk_mass gk_precision] in *; field; nra.
Qed.

(** [d051_cov_third_diagonal] (theorem).
 Mathematical meaning: Three observed scores yield an exact conditional variance across the signed feasible domain.
 Exact checked proposition: forall c:R, 1+2*c<>0 -> equicorr_schur_diagonal 3 c=(1-c)*(1+3*c)/(1+2*c).
 Premises and side conditions: Algebraic score counts are real scalars, with signed correlation admitted only where explicitly used inverses are nonzero. For probabilistic readings the positive-semidefinite joint covariance domain must also be established. Nothing here implicitly grants a Gaussian joint distribution.
 Proof/definition method: Normalize canonical Schur complement, history-prediction and posterior variance formulas using Rocq Stdlib Field and polynomial algebra, with no new probability axioms or bespoke finite sums.
 Library reuse: SequentialReport, EquicorrelationSpectral, UnequalHistoryLinearPrediction, GaussianConditionalKernel and Rocq Stdlib Reals/Field/Psatz.
 Boundary: The result is deterministic regression or covariance algebra, not a proof of regular conditional probability, normality or measure-theoretic conditional expectation.
*)
Theorem d051_cov_third_diagonal : forall c:R, 1+2*c<>0 -> equicorr_schur_diagonal 3 c=(1-c)*(1+3*c)/(1+2*c).
Proof.
  intros; cbv [hp sequential_prediction sequential_d equicorr_schur_diagonal equicorr_schur_cross gk_variance gk_d gk_mass gk_precision] in *; field; nra.
Qed.

(** [d051_cov_third_cross] (theorem).
 Mathematical meaning: Three observed scores yield an exact conditional cross-covariance.
 Exact checked proposition: forall c:R, 1+2*c<>0 -> equicorr_schur_cross 3 c=c*(1-c)/(1+2*c).
 Premises and side conditions: Algebraic score counts are real scalars, with signed correlation admitted only where explicitly used inverses are nonzero. For probabilistic readings the positive-semidefinite joint covariance domain must also be established. Nothing here implicitly grants a Gaussian joint distribution.
 Proof/definition method: Normalize canonical Schur complement, history-prediction and posterior variance formulas using Rocq Stdlib Field and polynomial algebra, with no new probability axioms or bespoke finite sums.
 Library reuse: SequentialReport, EquicorrelationSpectral, UnequalHistoryLinearPrediction, GaussianConditionalKernel and Rocq Stdlib Reals/Field/Psatz.
 Boundary: The result is deterministic regression or covariance algebra, not a proof of regular conditional probability, normality or measure-theoretic conditional expectation.
*)
Theorem d051_cov_third_cross : forall c:R, 1+2*c<>0 -> equicorr_schur_cross 3 c=c*(1-c)/(1+2*c).
Proof.
  intros; cbv [hp sequential_prediction sequential_d equicorr_schur_diagonal equicorr_schur_cross gk_variance gk_d gk_mass gk_precision] in *; field; nra.
Qed.

(** [d051_cov_fourth_diagonal] (theorem).
 Mathematical meaning: Four observed scores give an explicit future-score conditional variance.
 Exact checked proposition: forall c:R, 1+3*c<>0 -> equicorr_schur_diagonal 4 c=(1-c)*(1+4*c)/(1+3*c).
 Premises and side conditions: Algebraic score counts are real scalars, with signed correlation admitted only where explicitly used inverses are nonzero. For probabilistic readings the positive-semidefinite joint covariance domain must also be established. Nothing here implicitly grants a Gaussian joint distribution.
 Proof/definition method: Normalize canonical Schur complement, history-prediction and posterior variance formulas using Rocq Stdlib Field and polynomial algebra, with no new probability axioms or bespoke finite sums.
 Library reuse: SequentialReport, EquicorrelationSpectral, UnequalHistoryLinearPrediction, GaussianConditionalKernel and Rocq Stdlib Reals/Field/Psatz.
 Boundary: The result is deterministic regression or covariance algebra, not a proof of regular conditional probability, normality or measure-theoretic conditional expectation.
*)
Theorem d051_cov_fourth_diagonal : forall c:R, 1+3*c<>0 -> equicorr_schur_diagonal 4 c=(1-c)*(1+4*c)/(1+3*c).
Proof.
  intros; cbv [hp sequential_prediction sequential_d equicorr_schur_diagonal equicorr_schur_cross gk_variance gk_d gk_mass gk_precision] in *; field; nra.
Qed.

(** [d051_cov_fourth_cross] (theorem).
 Mathematical meaning: Four observed scores give an explicit future-pair conditional covariance.
 Exact checked proposition: forall c:R, 1+3*c<>0 -> equicorr_schur_cross 4 c=c*(1-c)/(1+3*c).
 Premises and side conditions: Algebraic score counts are real scalars, with signed correlation admitted only where explicitly used inverses are nonzero. For probabilistic readings the positive-semidefinite joint covariance domain must also be established. Nothing here implicitly grants a Gaussian joint distribution.
 Proof/definition method: Normalize canonical Schur complement, history-prediction and posterior variance formulas using Rocq Stdlib Field and polynomial algebra, with no new probability axioms or bespoke finite sums.
 Library reuse: SequentialReport, EquicorrelationSpectral, UnequalHistoryLinearPrediction, GaussianConditionalKernel and Rocq Stdlib Reals/Field/Psatz.
 Boundary: The result is deterministic regression or covariance algebra, not a proof of regular conditional probability, normality or measure-theoretic conditional expectation.
*)
Theorem d051_cov_fourth_cross : forall c:R, 1+3*c<>0 -> equicorr_schur_cross 4 c=c*(1-c)/(1+3*c).
Proof.
  intros; cbv [hp sequential_prediction sequential_d equicorr_schur_diagonal equicorr_schur_cross gk_variance gk_d gk_mass gk_precision] in *; field; nra.
Qed.

(** [d051_cov_fifth_diagonal] (theorem).
 Mathematical meaning: Five observed scores give the exact one-future-score regression residual variance.
 Exact checked proposition: forall c:R, 1+4*c<>0 -> equicorr_schur_diagonal 5 c=(1-c)*(1+5*c)/(1+4*c).
 Premises and side conditions: Algebraic score counts are real scalars, with signed correlation admitted only where explicitly used inverses are nonzero. For probabilistic readings the positive-semidefinite joint covariance domain must also be established. Nothing here implicitly grants a Gaussian joint distribution.
 Proof/definition method: Normalize canonical Schur complement, history-prediction and posterior variance formulas using Rocq Stdlib Field and polynomial algebra, with no new probability axioms or bespoke finite sums.
 Library reuse: SequentialReport, EquicorrelationSpectral, UnequalHistoryLinearPrediction, GaussianConditionalKernel and Rocq Stdlib Reals/Field/Psatz.
 Boundary: The result is deterministic regression or covariance algebra, not a proof of regular conditional probability, normality or measure-theoretic conditional expectation.
*)
Theorem d051_cov_fifth_diagonal : forall c:R, 1+4*c<>0 -> equicorr_schur_diagonal 5 c=(1-c)*(1+5*c)/(1+4*c).
Proof.
  intros; cbv [hp sequential_prediction sequential_d equicorr_schur_diagonal equicorr_schur_cross gk_variance gk_d gk_mass gk_precision] in *; field; nra.
Qed.

(** [d051_cov_fifth_cross] (theorem).
 Mathematical meaning: Five observed scores give the cross covariance between residual future observations.
 Exact checked proposition: forall c:R, 1+4*c<>0 -> equicorr_schur_cross 5 c=c*(1-c)/(1+4*c).
 Premises and side conditions: Algebraic score counts are real scalars, with signed correlation admitted only where explicitly used inverses are nonzero. For probabilistic readings the positive-semidefinite joint covariance domain must also be established. Nothing here implicitly grants a Gaussian joint distribution.
 Proof/definition method: Normalize canonical Schur complement, history-prediction and posterior variance formulas using Rocq Stdlib Field and polynomial algebra, with no new probability axioms or bespoke finite sums.
 Library reuse: SequentialReport, EquicorrelationSpectral, UnequalHistoryLinearPrediction, GaussianConditionalKernel and Rocq Stdlib Reals/Field/Psatz.
 Boundary: The result is deterministic regression or covariance algebra, not a proof of regular conditional probability, normality or measure-theoretic conditional expectation.
*)
Theorem d051_cov_fifth_cross : forall c:R, 1+4*c<>0 -> equicorr_schur_cross 5 c=c*(1-c)/(1+4*c).
Proof.
  intros; cbv [hp sequential_prediction sequential_d equicorr_schur_diagonal equicorr_schur_cross gk_variance gk_d gk_mass gk_precision] in *; field; nra.
Qed.

(** [d051_cov_cross_weighted] (theorem).
 Mathematical meaning: The cross covariance times the observation eigenvalue equals the latent posterior shared covariance numerator.
 Exact checked proposition: forall n c:R, sequential_d n c<>0 -> sequential_d n c*equicorr_schur_cross n c=c*(1-c).
 Premises and side conditions: Algebraic score counts are real scalars, with signed correlation admitted only where explicitly used inverses are nonzero. For probabilistic readings the positive-semidefinite joint covariance domain must also be established. Nothing here implicitly grants a Gaussian joint distribution.
 Proof/definition method: Normalize canonical Schur complement, history-prediction and posterior variance formulas using Rocq Stdlib Field and polynomial algebra, with no new probability axioms or bespoke finite sums.
 Library reuse: SequentialReport, EquicorrelationSpectral, UnequalHistoryLinearPrediction, GaussianConditionalKernel and Rocq Stdlib Reals/Field/Psatz.
 Boundary: The result is deterministic regression or covariance algebra, not a proof of regular conditional probability, normality or measure-theoretic conditional expectation.
*)
Theorem d051_cov_cross_weighted : forall n c:R, sequential_d n c<>0 -> sequential_d n c*equicorr_schur_cross n c=c*(1-c).
Proof.
  intros; cbv [hp sequential_prediction sequential_d equicorr_schur_diagonal equicorr_schur_cross gk_variance gk_d gk_mass gk_precision] in *; field; nra.
Qed.

(** [d051_cov_diag_weighted] (theorem).
 Mathematical meaning: The residual score variance times observed common eigenvalue factors into contrast and next-score common modes.
 Exact checked proposition: forall n c:R, sequential_d n c<>0 -> sequential_d n c*equicorr_schur_diagonal n c=(1-c)*(1+n*c).
 Premises and side conditions: Algebraic score counts are real scalars, with signed correlation admitted only where explicitly used inverses are nonzero. For probabilistic readings the positive-semidefinite joint covariance domain must also be established. Nothing here implicitly grants a Gaussian joint distribution.
 Proof/definition method: Normalize canonical Schur complement, history-prediction and posterior variance formulas using Rocq Stdlib Field and polynomial algebra, with no new probability axioms or bespoke finite sums.
 Library reuse: SequentialReport, EquicorrelationSpectral, UnequalHistoryLinearPrediction, GaussianConditionalKernel and Rocq Stdlib Reals/Field/Psatz.
 Boundary: The result is deterministic regression or covariance algebra, not a proof of regular conditional probability, normality or measure-theoretic conditional expectation.
*)
Theorem d051_cov_diag_weighted : forall n c:R, sequential_d n c<>0 -> sequential_d n c*equicorr_schur_diagonal n c=(1-c)*(1+n*c).
Proof.
  intros; cbv [hp sequential_prediction sequential_d equicorr_schur_diagonal equicorr_schur_cross gk_variance gk_d gk_mass gk_precision] in *; field; nra.
Qed.

(** [d051_cov_two_future_common] (theorem).
 Mathematical meaning: The two-future-score common direction is the signed full-to-observed covariance ratio.
 Exact checked proposition: forall n c:R, sequential_d n c<>0 -> equicorr_schur_diagonal n c+equicorr_schur_cross n c=(1-c)*sequential_d (n+2) c/sequential_d n c.
 Premises and side conditions: Algebraic score counts are real scalars, with signed correlation admitted only where explicitly used inverses are nonzero. For probabilistic readings the positive-semidefinite joint covariance domain must also be established. Nothing here implicitly grants a Gaussian joint distribution.
 Proof/definition method: Normalize canonical Schur complement, history-prediction and posterior variance formulas using Rocq Stdlib Field and polynomial algebra, with no new probability axioms or bespoke finite sums.
 Library reuse: SequentialReport, EquicorrelationSpectral, UnequalHistoryLinearPrediction, GaussianConditionalKernel and Rocq Stdlib Reals/Field/Psatz.
 Boundary: The result is deterministic regression or covariance algebra, not a proof of regular conditional probability, normality or measure-theoretic conditional expectation.
*)
Theorem d051_cov_two_future_common : forall n c:R, sequential_d n c<>0 -> equicorr_schur_diagonal n c+equicorr_schur_cross n c=(1-c)*sequential_d (n+2) c/sequential_d n c.
Proof.
  intros; cbv [hp sequential_prediction sequential_d equicorr_schur_diagonal equicorr_schur_cross gk_variance gk_d gk_mass gk_precision] in *; field; nra.
Qed.

(** [d051_cov_three_future_common] (theorem).
 Mathematical meaning: The three-future-score common direction has a closed conditional eigenvalue.
 Exact checked proposition: forall n c:R, sequential_d n c<>0 -> equicorr_schur_diagonal n c+2*equicorr_schur_cross n c=(1-c)*sequential_d (n+3) c/sequential_d n c.
 Premises and side conditions: Algebraic score counts are real scalars, with signed correlation admitted only where explicitly used inverses are nonzero. For probabilistic readings the positive-semidefinite joint covariance domain must also be established. Nothing here implicitly grants a Gaussian joint distribution.
 Proof/definition method: Normalize canonical Schur complement, history-prediction and posterior variance formulas using Rocq Stdlib Field and polynomial algebra, with no new probability axioms or bespoke finite sums.
 Library reuse: SequentialReport, EquicorrelationSpectral, UnequalHistoryLinearPrediction, GaussianConditionalKernel and Rocq Stdlib Reals/Field/Psatz.
 Boundary: The result is deterministic regression or covariance algebra, not a proof of regular conditional probability, normality or measure-theoretic conditional expectation.
*)
Theorem d051_cov_three_future_common : forall n c:R, sequential_d n c<>0 -> equicorr_schur_diagonal n c+2*equicorr_schur_cross n c=(1-c)*sequential_d (n+3) c/sequential_d n c.
Proof.
  intros; cbv [hp sequential_prediction sequential_d equicorr_schur_diagonal equicorr_schur_cross gk_variance gk_d gk_mass gk_precision] in *; field; nra.
Qed.

(** [d051_cov_diagonal_variance_drop] (theorem).
 Mathematical meaning: Conditioning on another k scores reduces the diagonal conditional variance by the exact information increment.
 Exact checked proposition: forall n k c:R, sequential_d n c<>0 -> sequential_d (n+k) c<>0 -> equicorr_schur_diagonal n c-equicorr_schur_diagonal (n+k) c=k*c*c*(1-c)/(sequential_d n c*sequential_d (n+k) c).
 Premises and side conditions: Algebraic score counts are real scalars, with signed correlation admitted only where explicitly used inverses are nonzero. For probabilistic readings the positive-semidefinite joint covariance domain must also be established. Nothing here implicitly grants a Gaussian joint distribution.
 Proof/definition method: Normalize canonical Schur complement, history-prediction and posterior variance formulas using Rocq Stdlib Field and polynomial algebra, with no new probability axioms or bespoke finite sums.
 Library reuse: SequentialReport, EquicorrelationSpectral, UnequalHistoryLinearPrediction, GaussianConditionalKernel and Rocq Stdlib Reals/Field/Psatz.
 Boundary: The result is deterministic regression or covariance algebra, not a proof of regular conditional probability, normality or measure-theoretic conditional expectation.
*)
Theorem d051_cov_diagonal_variance_drop : forall n k c:R, sequential_d n c<>0 -> sequential_d (n+k) c<>0 -> equicorr_schur_diagonal n c-equicorr_schur_diagonal (n+k) c=k*c*c*(1-c)/(sequential_d n c*sequential_d (n+k) c).
Proof.
  intros; cbv [hp sequential_prediction sequential_d equicorr_schur_diagonal equicorr_schur_cross gk_variance gk_d gk_mass gk_precision] in *; field; nra.
Qed.

(** [d051_cov_cross_variance_drop] (theorem).
 Mathematical meaning: Added observations decrease the shared residual cross-covariance by the same exact information increment.
 Exact checked proposition: forall n k c:R, sequential_d n c<>0 -> sequential_d (n+k) c<>0 -> equicorr_schur_cross n c-equicorr_schur_cross (n+k) c=k*c*c*(1-c)/(sequential_d n c*sequential_d (n+k) c).
 Premises and side conditions: Algebraic score counts are real scalars, with signed correlation admitted only where explicitly used inverses are nonzero. For probabilistic readings the positive-semidefinite joint covariance domain must also be established. Nothing here implicitly grants a Gaussian joint distribution.
 Proof/definition method: Normalize canonical Schur complement, history-prediction and posterior variance formulas using Rocq Stdlib Field and polynomial algebra, with no new probability axioms or bespoke finite sums.
 Library reuse: SequentialReport, EquicorrelationSpectral, UnequalHistoryLinearPrediction, GaussianConditionalKernel and Rocq Stdlib Reals/Field/Psatz.
 Boundary: The result is deterministic regression or covariance algebra, not a proof of regular conditional probability, normality or measure-theoretic conditional expectation.
*)
Theorem d051_cov_cross_variance_drop : forall n k c:R, sequential_d n c<>0 -> sequential_d (n+k) c<>0 -> equicorr_schur_cross n c-equicorr_schur_cross (n+k) c=k*c*c*(1-c)/(sequential_d n c*sequential_d (n+k) c).
Proof.
  intros; cbv [hp sequential_prediction sequential_d equicorr_schur_diagonal equicorr_schur_cross gk_variance gk_d gk_mass gk_precision] in *; field; nra.
Qed.

(** [d051_cov_common_unfolded] (theorem).
 Mathematical meaning: The k-future-score conditional common-mode eigenvalue admits a fully explicit signed-correlation formula.
 Exact checked proposition: forall n k c:R, sequential_d n c<>0 -> equicorr_schur_diagonal n c+(k-1)*equicorr_schur_cross n c=(1-c)*(1+(n+k-1)*c)/sequential_d n c.
 Premises and side conditions: Algebraic score counts are real scalars, with signed correlation admitted only where explicitly used inverses are nonzero. For probabilistic readings the positive-semidefinite joint covariance domain must also be established. Nothing here implicitly grants a Gaussian joint distribution.
 Proof/definition method: Normalize canonical Schur complement, history-prediction and posterior variance formulas using Rocq Stdlib Field and polynomial algebra, with no new probability axioms or bespoke finite sums.
 Library reuse: SequentialReport, EquicorrelationSpectral, UnequalHistoryLinearPrediction, GaussianConditionalKernel and Rocq Stdlib Reals/Field/Psatz.
 Boundary: The result is deterministic regression or covariance algebra, not a proof of regular conditional probability, normality or measure-theoretic conditional expectation.
*)
Theorem d051_cov_common_unfolded : forall n k c:R, sequential_d n c<>0 -> equicorr_schur_diagonal n c+(k-1)*equicorr_schur_cross n c=(1-c)*(1+(n+k-1)*c)/sequential_d n c.
Proof.
  intros; cbv [hp sequential_prediction sequential_d equicorr_schur_diagonal equicorr_schur_cross gk_variance gk_d gk_mass gk_precision] in *; field; nra.
Qed.

(** [d051_cov_future_sum_contrast] (theorem).
 Mathematical meaning: The predicted future-score total decomposes into k idiosyncratic variances and k-squared shared covariance.
 Exact checked proposition: forall n k c:R, k*equicorr_schur_diagonal n c+k*(k-1)*equicorr_schur_cross n c=k*(1-c)+k*k*equicorr_schur_cross n c.
 Premises and side conditions: Algebraic score counts are real scalars, with signed correlation admitted only where explicitly used inverses are nonzero. For probabilistic readings the positive-semidefinite joint covariance domain must also be established. Nothing here implicitly grants a Gaussian joint distribution.
 Proof/definition method: Normalize canonical Schur complement, history-prediction and posterior variance formulas using Rocq Stdlib Field and polynomial algebra, with no new probability axioms or bespoke finite sums.
 Library reuse: SequentialReport, EquicorrelationSpectral, UnequalHistoryLinearPrediction, GaussianConditionalKernel and Rocq Stdlib Reals/Field/Psatz.
 Boundary: The result is deterministic regression or covariance algebra, not a proof of regular conditional probability, normality or measure-theoretic conditional expectation.
*)
Theorem d051_cov_future_sum_contrast : forall n k c:R, k*equicorr_schur_diagonal n c+k*(k-1)*equicorr_schur_cross n c=k*(1-c)+k*k*equicorr_schur_cross n c.
Proof.
  intros n k c.
  pose proof (equicorr_schur_diagonal_contrast_gap n c) as Hcontrast.
  assert (Hdiag : equicorr_schur_diagonal n c = (1-c)+equicorr_schur_cross n c) by lra.
  rewrite Hdiag; ring.
Qed.

(** [d051_cov_future_sum_closed] (theorem).
 Mathematical meaning: The full covariance of k future scores has a contrast/shared-factor decomposition.
 Exact checked proposition: forall n k c:R, sequential_d n c<>0 -> k*equicorr_schur_diagonal n c+k*(k-1)*equicorr_schur_cross n c=k*(1-c)+k*k*c*(1-c)/sequential_d n c.
 Premises and side conditions: Algebraic score counts are real scalars, with signed correlation admitted only where explicitly used inverses are nonzero. For probabilistic readings the positive-semidefinite joint covariance domain must also be established. Nothing here implicitly grants a Gaussian joint distribution.
 Proof/definition method: Normalize canonical Schur complement, history-prediction and posterior variance formulas using Rocq Stdlib Field and polynomial algebra, with no new probability axioms or bespoke finite sums.
 Library reuse: SequentialReport, EquicorrelationSpectral, UnequalHistoryLinearPrediction, GaussianConditionalKernel and Rocq Stdlib Reals/Field/Psatz.
 Boundary: The result is deterministic regression or covariance algebra, not a proof of regular conditional probability, normality or measure-theoretic conditional expectation.
*)
Theorem d051_cov_future_sum_closed : forall n k c:R, sequential_d n c<>0 -> k*equicorr_schur_diagonal n c+k*(k-1)*equicorr_schur_cross n c=k*(1-c)+k*k*c*(1-c)/sequential_d n c.
Proof.
  intros; cbv [hp sequential_prediction sequential_d equicorr_schur_diagonal equicorr_schur_cross gk_variance gk_d gk_mass gk_precision] in *; field; nra.
Qed.

(** [d051_cov_cross_pairs_closed] (theorem).
 Mathematical meaning: The sum over all ordered future-score cross pairs has an exact signed-correlation formula.
 Exact checked proposition: forall n k c:R, sequential_d n c<>0 -> k*(k-1)*equicorr_schur_cross n c=k*(k-1)*c*(1-c)/sequential_d n c.
 Premises and side conditions: Algebraic score counts are real scalars, with signed correlation admitted only where explicitly used inverses are nonzero. For probabilistic readings the positive-semidefinite joint covariance domain must also be established. Nothing here implicitly grants a Gaussian joint distribution.
 Proof/definition method: Normalize canonical Schur complement, history-prediction and posterior variance formulas using Rocq Stdlib Field and polynomial algebra, with no new probability axioms or bespoke finite sums.
 Library reuse: SequentialReport, EquicorrelationSpectral, UnequalHistoryLinearPrediction, GaussianConditionalKernel and Rocq Stdlib Reals/Field/Psatz.
 Boundary: The result is deterministic regression or covariance algebra, not a proof of regular conditional probability, normality or measure-theoretic conditional expectation.
*)
Theorem d051_cov_cross_pairs_closed : forall n k c:R, sequential_d n c<>0 -> k*(k-1)*equicorr_schur_cross n c=k*(k-1)*c*(1-c)/sequential_d n c.
Proof.
  intros; cbv [hp sequential_prediction sequential_d equicorr_schur_diagonal equicorr_schur_cross gk_variance gk_d gk_mass gk_precision] in *; field; nra.
Qed.

(** [d051_cov_two_score_contrast] (theorem).
 Mathematical meaning: The variance of a difference of two future scores depends only on the original contrast eigenvalue.
 Exact checked proposition: forall n c:R, sequential_d n c<>0 -> 2*equicorr_schur_diagonal n c-2*equicorr_schur_cross n c=2*(1-c).
 Premises and side conditions: Algebraic score counts are real scalars, with signed correlation admitted only where explicitly used inverses are nonzero. For probabilistic readings the positive-semidefinite joint covariance domain must also be established. Nothing here implicitly grants a Gaussian joint distribution.
 Proof/definition method: Normalize canonical Schur complement, history-prediction and posterior variance formulas using Rocq Stdlib Field and polynomial algebra, with no new probability axioms or bespoke finite sums.
 Library reuse: SequentialReport, EquicorrelationSpectral, UnequalHistoryLinearPrediction, GaussianConditionalKernel and Rocq Stdlib Reals/Field/Psatz.
 Boundary: The result is deterministic regression or covariance algebra, not a proof of regular conditional probability, normality or measure-theoretic conditional expectation.
*)
Theorem d051_cov_two_score_contrast : forall n c:R, sequential_d n c<>0 -> 2*equicorr_schur_diagonal n c-2*equicorr_schur_cross n c=2*(1-c).
Proof.
  intros; cbv [hp sequential_prediction sequential_d equicorr_schur_diagonal equicorr_schur_cross gk_variance gk_d gk_mass gk_precision] in *; field; nra.
Qed.

(** [d051_cov_three_score_contrast] (theorem).
 Mathematical meaning: Three independent future contrasts preserve total contrast-mode energy.
 Exact checked proposition: forall n c:R, sequential_d n c<>0 -> 3*equicorr_schur_diagonal n c-3*equicorr_schur_cross n c=3*(1-c).
 Premises and side conditions: Algebraic score counts are real scalars, with signed correlation admitted only where explicitly used inverses are nonzero. For probabilistic readings the positive-semidefinite joint covariance domain must also be established. Nothing here implicitly grants a Gaussian joint distribution.
 Proof/definition method: Normalize canonical Schur complement, history-prediction and posterior variance formulas using Rocq Stdlib Field and polynomial algebra, with no new probability axioms or bespoke finite sums.
 Library reuse: SequentialReport, EquicorrelationSpectral, UnequalHistoryLinearPrediction, GaussianConditionalKernel and Rocq Stdlib Reals/Field/Psatz.
 Boundary: The result is deterministic regression or covariance algebra, not a proof of regular conditional probability, normality or measure-theoretic conditional expectation.
*)
Theorem d051_cov_three_score_contrast : forall n c:R, sequential_d n c<>0 -> 3*equicorr_schur_diagonal n c-3*equicorr_schur_cross n c=3*(1-c).
Proof.
  intros; cbv [hp sequential_prediction sequential_d equicorr_schur_diagonal equicorr_schur_cross gk_variance gk_d gk_mass gk_precision] in *; field; nra.
Qed.

(** [d051_cov_cross_normalized] (theorem).
 Mathematical meaning: The contrast-normalized future covariance equals the common regression weight.
 Exact checked proposition: forall n c:R, sequential_d n c<>0 -> 1-c<>0 -> equicorr_schur_cross n c/(1-c)=c/sequential_d n c.
 Premises and side conditions: Algebraic score counts are real scalars, with signed correlation admitted only where explicitly used inverses are nonzero. For probabilistic readings the positive-semidefinite joint covariance domain must also be established. Nothing here implicitly grants a Gaussian joint distribution.
 Proof/definition method: Normalize canonical Schur complement, history-prediction and posterior variance formulas using Rocq Stdlib Field and polynomial algebra, with no new probability axioms or bespoke finite sums.
 Library reuse: SequentialReport, EquicorrelationSpectral, UnequalHistoryLinearPrediction, GaussianConditionalKernel and Rocq Stdlib Reals/Field/Psatz.
 Boundary: The result is deterministic regression or covariance algebra, not a proof of regular conditional probability, normality or measure-theoretic conditional expectation.
*)
Theorem d051_cov_cross_normalized : forall n c:R, sequential_d n c<>0 -> 1-c<>0 -> equicorr_schur_cross n c/(1-c)=c/sequential_d n c.
Proof.
  intros; cbv [hp sequential_prediction sequential_d equicorr_schur_diagonal equicorr_schur_cross gk_variance gk_d gk_mass gk_precision] in *; field; nra.
Qed.

(** [d051_mean_zero_batch_response] (theorem).
 Mathematical meaning: No newly observed score sum leads to a pure shrinkage of the previous conditional mean.
 Exact checked proposition: forall n k c s:R, sequential_d n c<>0 -> sequential_d (n+k) c<>0 -> hp (n+k) c s=sequential_d n c/sequential_d (n+k) c*hp n c s.
 Premises and side conditions: Algebraic score counts are real scalars, with signed correlation admitted only where explicitly used inverses are nonzero. For probabilistic readings the positive-semidefinite joint covariance domain must also be established. Nothing here implicitly grants a Gaussian joint distribution.
 Proof/definition method: Normalize canonical Schur complement, history-prediction and posterior variance formulas using Rocq Stdlib Field and polynomial algebra, with no new probability axioms or bespoke finite sums.
 Library reuse: SequentialReport, EquicorrelationSpectral, UnequalHistoryLinearPrediction, GaussianConditionalKernel and Rocq Stdlib Reals/Field/Psatz.
 Boundary: The result is deterministic regression or covariance algebra, not a proof of regular conditional probability, normality or measure-theoretic conditional expectation.
*)
Theorem d051_mean_zero_batch_response : forall n k c s:R, sequential_d n c<>0 -> sequential_d (n+k) c<>0 -> hp (n+k) c s=sequential_d n c/sequential_d (n+k) c*hp n c s.
Proof.
  intros; cbv [hp sequential_prediction sequential_d equicorr_schur_diagonal equicorr_schur_cross gk_variance gk_d gk_mass gk_precision] in *; field; nra.
Qed.

(** [d051_mean_weighted_update_balance] (theorem).
 Mathematical meaning: The Gaussian sufficient-statistic update obeys an exact denominator-weighted balance equation.
 Exact checked proposition: forall n k c s t:R, sequential_d n c<>0 -> sequential_d (n+k) c<>0 -> sequential_d (n+k) c*hp (n+k) c (s+t)=sequential_d n c*hp n c s+c*t.
 Premises and side conditions: Algebraic score counts are real scalars, with signed correlation admitted only where explicitly used inverses are nonzero. For probabilistic readings the positive-semidefinite joint covariance domain must also be established. Nothing here implicitly grants a Gaussian joint distribution.
 Proof/definition method: Normalize canonical Schur complement, history-prediction and posterior variance formulas using Rocq Stdlib Field and polynomial algebra, with no new probability axioms or bespoke finite sums.
 Library reuse: SequentialReport, EquicorrelationSpectral, UnequalHistoryLinearPrediction, GaussianConditionalKernel and Rocq Stdlib Reals/Field/Psatz.
 Boundary: The result is deterministic regression or covariance algebra, not a proof of regular conditional probability, normality or measure-theoretic conditional expectation.
*)
Theorem d051_mean_weighted_update_balance : forall n k c s t:R, sequential_d n c<>0 -> sequential_d (n+k) c<>0 -> sequential_d (n+k) c*hp (n+k) c (s+t)=sequential_d n c*hp n c s+c*t.
Proof.
  intros; cbv [hp sequential_prediction sequential_d equicorr_schur_diagonal equicorr_schur_cross gk_variance gk_d gk_mass gk_precision] in *; field; nra.
Qed.

(** [d051_mean_innovation_balance] (theorem).
 Mathematical meaning: The batch posterior correction equals the innovation multiplied by the common regression coefficient.
 Exact checked proposition: forall n k c s t:R, sequential_d n c<>0 -> sequential_d (n+k) c<>0 -> sequential_d (n+k) c*(hp (n+k) c (s+t)-hp n c s)=c*(t-k*hp n c s).
 Premises and side conditions: Algebraic score counts are real scalars, with signed correlation admitted only where explicitly used inverses are nonzero. For probabilistic readings the positive-semidefinite joint covariance domain must also be established. Nothing here implicitly grants a Gaussian joint distribution.
 Proof/definition method: Normalize canonical Schur complement, history-prediction and posterior variance formulas using Rocq Stdlib Field and polynomial algebra, with no new probability axioms or bespoke finite sums.
 Library reuse: SequentialReport, EquicorrelationSpectral, UnequalHistoryLinearPrediction, GaussianConditionalKernel and Rocq Stdlib Reals/Field/Psatz.
 Boundary: The result is deterministic regression or covariance algebra, not a proof of regular conditional probability, normality or measure-theoretic conditional expectation.
*)
Theorem d051_mean_innovation_balance : forall n k c s t:R, sequential_d n c<>0 -> sequential_d (n+k) c<>0 -> sequential_d (n+k) c*(hp (n+k) c (s+t)-hp n c s)=c*(t-k*hp n c s).
Proof.
  intros; cbv [hp sequential_prediction sequential_d equicorr_schur_diagonal equicorr_schur_cross gk_variance gk_d gk_mass gk_precision] in *; field; nra.
Qed.

(** [d051_mean_batch_innovation] (theorem).
 Mathematical meaning: The general k-score Bayesian mean update is expressible entirely in innovation form.
 Exact checked proposition: forall n k c s t:R, sequential_d n c<>0 -> sequential_d (n+k) c<>0 -> hp (n+k) c (s+t)=hp n c s+c*(t-k*hp n c s)/sequential_d (n+k) c.
 Premises and side conditions: Algebraic score counts are real scalars, with signed correlation admitted only where explicitly used inverses are nonzero. For probabilistic readings the positive-semidefinite joint covariance domain must also be established. Nothing here implicitly grants a Gaussian joint distribution.
 Proof/definition method: Normalize canonical Schur complement, history-prediction and posterior variance formulas using Rocq Stdlib Field and polynomial algebra, with no new probability axioms or bespoke finite sums.
 Library reuse: SequentialReport, EquicorrelationSpectral, UnequalHistoryLinearPrediction, GaussianConditionalKernel and Rocq Stdlib Reals/Field/Psatz.
 Boundary: The result is deterministic regression or covariance algebra, not a proof of regular conditional probability, normality or measure-theoretic conditional expectation.
*)
Theorem d051_mean_batch_innovation : forall n k c s t:R, sequential_d n c<>0 -> sequential_d (n+k) c<>0 -> hp (n+k) c (s+t)=hp n c s+c*(t-k*hp n c s)/sequential_d (n+k) c.
Proof.
  intros; cbv [hp sequential_prediction sequential_d equicorr_schur_diagonal equicorr_schur_cross gk_variance gk_d gk_mass gk_precision] in *; field; nra.
Qed.

(** [d051_mean_centered_batch] (theorem).
 Mathematical meaning: An innovation-centered batch updates the posterior mean only through its residual sum.
 Exact checked proposition: forall n k c s u:R, sequential_d n c<>0 -> sequential_d (n+k) c<>0 -> hp (n+k) c (s+k*hp n c s+u)=hp n c s+c*u/sequential_d (n+k) c.
 Premises and side conditions: Algebraic score counts are real scalars, with signed correlation admitted only where explicitly used inverses are nonzero. For probabilistic readings the positive-semidefinite joint covariance domain must also be established. Nothing here implicitly grants a Gaussian joint distribution.
 Proof/definition method: Normalize canonical Schur complement, history-prediction and posterior variance formulas using Rocq Stdlib Field and polynomial algebra, with no new probability axioms or bespoke finite sums.
 Library reuse: SequentialReport, EquicorrelationSpectral, UnequalHistoryLinearPrediction, GaussianConditionalKernel and Rocq Stdlib Reals/Field/Psatz.
 Boundary: The result is deterministic regression or covariance algebra, not a proof of regular conditional probability, normality or measure-theoretic conditional expectation.
*)
Theorem d051_mean_centered_batch : forall n k c s u:R, sequential_d n c<>0 -> sequential_d (n+k) c<>0 -> hp (n+k) c (s+k*hp n c s+u)=hp n c s+c*u/sequential_d (n+k) c.
Proof.
  intros; cbv [hp sequential_prediction sequential_d equicorr_schur_diagonal equicorr_schur_cross gk_variance gk_d gk_mass gk_precision] in *; field; nra.
Qed.

(** [d051_mean_first_observation] (theorem).
 Mathematical meaning: For one observed standardized score, the predicted latent common factor is c times that score.
 Exact checked proposition: forall c s:R, hp 1 c s=c*s.
 Premises and side conditions: Algebraic score counts are real scalars, with signed correlation admitted only where explicitly used inverses are nonzero. For probabilistic readings the positive-semidefinite joint covariance domain must also be established. Nothing here implicitly grants a Gaussian joint distribution.
 Proof/definition method: Normalize canonical Schur complement, history-prediction and posterior variance formulas using Rocq Stdlib Field and polynomial algebra, with no new probability axioms or bespoke finite sums.
 Library reuse: SequentialReport, EquicorrelationSpectral, UnequalHistoryLinearPrediction, GaussianConditionalKernel and Rocq Stdlib Reals/Field/Psatz.
 Boundary: The result is deterministic regression or covariance algebra, not a proof of regular conditional probability, normality or measure-theoretic conditional expectation.
*)
Theorem d051_mean_first_observation : forall c s:R, hp 1 c s=c*s.
Proof.
  intros; cbv [hp sequential_prediction sequential_d equicorr_schur_diagonal equicorr_schur_cross gk_variance gk_d gk_mass gk_precision] in *; field; nra.
Qed.

(** [d051_mean_second_observation] (theorem).
 Mathematical meaning: The sufficient-statistic regression coefficient for two observed scores is c/(1+c).
 Exact checked proposition: forall c s:R, 1+c<>0 -> hp 2 c s=c*s/(1+c).
 Premises and side conditions: Algebraic score counts are real scalars, with signed correlation admitted only where explicitly used inverses are nonzero. For probabilistic readings the positive-semidefinite joint covariance domain must also be established. Nothing here implicitly grants a Gaussian joint distribution.
 Proof/definition method: Normalize canonical Schur complement, history-prediction and posterior variance formulas using Rocq Stdlib Field and polynomial algebra, with no new probability axioms or bespoke finite sums.
 Library reuse: SequentialReport, EquicorrelationSpectral, UnequalHistoryLinearPrediction, GaussianConditionalKernel and Rocq Stdlib Reals/Field/Psatz.
 Boundary: The result is deterministic regression or covariance algebra, not a proof of regular conditional probability, normality or measure-theoretic conditional expectation.
*)
Theorem d051_mean_second_observation : forall c s:R, 1+c<>0 -> hp 2 c s=c*s/(1+c).
Proof.
  intros; cbv [hp sequential_prediction sequential_d equicorr_schur_diagonal equicorr_schur_cross gk_variance gk_d gk_mass gk_precision] in *; field; nra.
Qed.

(** [d051_mean_third_observation] (theorem).
 Mathematical meaning: The sufficient-statistic regression coefficient for three observed scores uses the correct covariance eigenvalue.
 Exact checked proposition: forall c s:R, 1+2*c<>0 -> hp 3 c s=c*s/(1+2*c).
 Premises and side conditions: Algebraic score counts are real scalars, with signed correlation admitted only where explicitly used inverses are nonzero. For probabilistic readings the positive-semidefinite joint covariance domain must also be established. Nothing here implicitly grants a Gaussian joint distribution.
 Proof/definition method: Normalize canonical Schur complement, history-prediction and posterior variance formulas using Rocq Stdlib Field and polynomial algebra, with no new probability axioms or bespoke finite sums.
 Library reuse: SequentialReport, EquicorrelationSpectral, UnequalHistoryLinearPrediction, GaussianConditionalKernel and Rocq Stdlib Reals/Field/Psatz.
 Boundary: The result is deterministic regression or covariance algebra, not a proof of regular conditional probability, normality or measure-theoretic conditional expectation.
*)
Theorem d051_mean_third_observation : forall c s:R, 1+2*c<>0 -> hp 3 c s=c*s/(1+2*c).
Proof.
  intros; cbv [hp sequential_prediction sequential_d equicorr_schur_diagonal equicorr_schur_cross gk_variance gk_d gk_mass gk_precision] in *; field; nra.
Qed.

(** [d051_mean_fourth_observation] (theorem).
 Mathematical meaning: The sufficient-statistic regression coefficient for four observed scores is explicit.
 Exact checked proposition: forall c s:R, 1+3*c<>0 -> hp 4 c s=c*s/(1+3*c).
 Premises and side conditions: Algebraic score counts are real scalars, with signed correlation admitted only where explicitly used inverses are nonzero. For probabilistic readings the positive-semidefinite joint covariance domain must also be established. Nothing here implicitly grants a Gaussian joint distribution.
 Proof/definition method: Normalize canonical Schur complement, history-prediction and posterior variance formulas using Rocq Stdlib Field and polynomial algebra, with no new probability axioms or bespoke finite sums.
 Library reuse: SequentialReport, EquicorrelationSpectral, UnequalHistoryLinearPrediction, GaussianConditionalKernel and Rocq Stdlib Reals/Field/Psatz.
 Boundary: The result is deterministic regression or covariance algebra, not a proof of regular conditional probability, normality or measure-theoretic conditional expectation.
*)
Theorem d051_mean_fourth_observation : forall c s:R, 1+3*c<>0 -> hp 4 c s=c*s/(1+3*c).
Proof.
  intros; cbv [hp sequential_prediction sequential_d equicorr_schur_diagonal equicorr_schur_cross gk_variance gk_d gk_mass gk_precision] in *; field; nra.
Qed.

(** [d051_mean_fifth_observation] (theorem).
 Mathematical meaning: The sufficient-statistic regression coefficient for five observed scores is explicit.
 Exact checked proposition: forall c s:R, 1+4*c<>0 -> hp 5 c s=c*s/(1+4*c).
 Premises and side conditions: Algebraic score counts are real scalars, with signed correlation admitted only where explicitly used inverses are nonzero. For probabilistic readings the positive-semidefinite joint covariance domain must also be established. Nothing here implicitly grants a Gaussian joint distribution.
 Proof/definition method: Normalize canonical Schur complement, history-prediction and posterior variance formulas using Rocq Stdlib Field and polynomial algebra, with no new probability axioms or bespoke finite sums.
 Library reuse: SequentialReport, EquicorrelationSpectral, UnequalHistoryLinearPrediction, GaussianConditionalKernel and Rocq Stdlib Reals/Field/Psatz.
 Boundary: The result is deterministic regression or covariance algebra, not a proof of regular conditional probability, normality or measure-theoretic conditional expectation.
*)
Theorem d051_mean_fifth_observation : forall c s:R, 1+4*c<>0 -> hp 5 c s=c*s/(1+4*c).
Proof.
  intros; cbv [hp sequential_prediction sequential_d equicorr_schur_diagonal equicorr_schur_cross gk_variance gk_d gk_mass gk_precision] in *; field; nra.
Qed.

(** [d051_mean_batch_response] (theorem).
 Mathematical meaning: The response to a future-batch sum at fixed total history length is linear in that sum.
 Exact checked proposition: forall n k c s t:R, sequential_d (n+k) c<>0 -> hp (n+k) c (s+t)-hp (n+k) c s=c*t/sequential_d (n+k) c.
 Premises and side conditions: Algebraic score counts are real scalars, with signed correlation admitted only where explicitly used inverses are nonzero. For probabilistic readings the positive-semidefinite joint covariance domain must also be established. Nothing here implicitly grants a Gaussian joint distribution.
 Proof/definition method: Normalize canonical Schur complement, history-prediction and posterior variance formulas using Rocq Stdlib Field and polynomial algebra, with no new probability axioms or bespoke finite sums.
 Library reuse: SequentialReport, EquicorrelationSpectral, UnequalHistoryLinearPrediction, GaussianConditionalKernel and Rocq Stdlib Reals/Field/Psatz.
 Boundary: The result is deterministic regression or covariance algebra, not a proof of regular conditional probability, normality or measure-theoretic conditional expectation.
*)
Theorem d051_mean_batch_response : forall n k c s t:R, sequential_d (n+k) c<>0 -> hp (n+k) c (s+t)-hp (n+k) c s=c*t/sequential_d (n+k) c.
Proof.
  intros; cbv [hp sequential_prediction sequential_d equicorr_schur_diagonal equicorr_schur_cross gk_variance gk_d gk_mass gk_precision] in *; field; nra.
Qed.

(** [d051_mean_third_stage] (theorem).
 Mathematical meaning: A final observation batch can update the already pooled two-stage predictor without changing the answer.
 Exact checked proposition: forall n k l c s t u:R, sequential_d (n+k) c<>0 -> sequential_d (n+k+l) c<>0 -> hp (n+k+l) c (s+t+u)=(sequential_d (n+k) c*hp (n+k) c (s+t)+c*u)/sequential_d (n+k+l) c.
 Premises and side conditions: Algebraic score counts are real scalars, with signed correlation admitted only where explicitly used inverses are nonzero. For probabilistic readings the positive-semidefinite joint covariance domain must also be established. Nothing here implicitly grants a Gaussian joint distribution.
 Proof/definition method: Normalize canonical Schur complement, history-prediction and posterior variance formulas using Rocq Stdlib Field and polynomial algebra, with no new probability axioms or bespoke finite sums.
 Library reuse: SequentialReport, EquicorrelationSpectral, UnequalHistoryLinearPrediction, GaussianConditionalKernel and Rocq Stdlib Reals/Field/Psatz.
 Boundary: The result is deterministic regression or covariance algebra, not a proof of regular conditional probability, normality or measure-theoretic conditional expectation.
*)
Theorem d051_mean_third_stage : forall n k l c s t u:R, sequential_d (n+k) c<>0 -> sequential_d (n+k+l) c<>0 -> hp (n+k+l) c (s+t+u)=(sequential_d (n+k) c*hp (n+k) c (s+t)+c*u)/sequential_d (n+k+l) c.
Proof.
  intros; cbv [hp sequential_prediction sequential_d equicorr_schur_diagonal equicorr_schur_cross gk_variance gk_d gk_mass gk_precision] in *; field; nra.
Qed.

(** [d051_mean_prediction_average] (theorem).
 Mathematical meaning: The predictor based on an arbitrary score sum equals the report's mean-based predictor when sample size is nonzero.
 Exact checked proposition: forall n c s:R, n<>0 -> sequential_d n c<>0 -> hp n c s=sequential_prediction n c (s/n).
 Premises and side conditions: Algebraic score counts are real scalars, with signed correlation admitted only where explicitly used inverses are nonzero. For probabilistic readings the positive-semidefinite joint covariance domain must also be established. Nothing here implicitly grants a Gaussian joint distribution.
 Proof/definition method: Normalize canonical Schur complement, history-prediction and posterior variance formulas using Rocq Stdlib Field and polynomial algebra, with no new probability axioms or bespoke finite sums.
 Library reuse: SequentialReport, EquicorrelationSpectral, UnequalHistoryLinearPrediction, GaussianConditionalKernel and Rocq Stdlib Reals/Field/Psatz.
 Boundary: The result is deterministic regression or covariance algebra, not a proof of regular conditional probability, normality or measure-theoretic conditional expectation.
*)
Theorem d051_mean_prediction_average : forall n c s:R, n<>0 -> sequential_d n c<>0 -> hp n c s=sequential_prediction n c (s/n).
Proof.
  intros; cbv [hp sequential_prediction sequential_d equicorr_schur_diagonal equicorr_schur_cross gk_variance gk_d gk_mass gk_precision] in *; field; nra.
Qed.

(** [d051_mean_one_score_gain] (theorem).
 Mathematical meaning: The one-observation conditioning recursion is an explicit innovation-gain step.
 Exact checked proposition: forall n c s x:R, sequential_d n c<>0 -> sequential_d (n+1) c<>0 -> hp (n+1) c (s+x)=hp n c s+c*(x-hp n c s)/sequential_d (n+1) c.
 Premises and side conditions: Algebraic score counts are real scalars, with signed correlation admitted only where explicitly used inverses are nonzero. For probabilistic readings the positive-semidefinite joint covariance domain must also be established. Nothing here implicitly grants a Gaussian joint distribution.
 Proof/definition method: Normalize canonical Schur complement, history-prediction and posterior variance formulas using Rocq Stdlib Field and polynomial algebra, with no new probability axioms or bespoke finite sums.
 Library reuse: SequentialReport, EquicorrelationSpectral, UnequalHistoryLinearPrediction, GaussianConditionalKernel and Rocq Stdlib Reals/Field/Psatz.
 Boundary: The result is deterministic regression or covariance algebra, not a proof of regular conditional probability, normality or measure-theoretic conditional expectation.
*)
Theorem d051_mean_one_score_gain : forall n c s x:R, sequential_d n c<>0 -> sequential_d (n+1) c<>0 -> hp (n+1) c (s+x)=hp n c s+c*(x-hp n c s)/sequential_d (n+1) c.
Proof.
  intros; cbv [hp sequential_prediction sequential_d equicorr_schur_diagonal equicorr_schur_cross gk_variance gk_d gk_mass gk_precision] in *; field; nra.
Qed.

(** [d051_mean_two_score_gain] (theorem).
 Mathematical meaning: Two-score conditioning can be written as a correction for both innovations at once.
 Exact checked proposition: forall n c s x y:R, sequential_d n c<>0 -> sequential_d (n+2) c<>0 -> hp (n+2) c (s+x+y)=hp n c s+c*(x+y-2*hp n c s)/sequential_d (n+2) c.
 Premises and side conditions: Algebraic score counts are real scalars, with signed correlation admitted only where explicitly used inverses are nonzero. For probabilistic readings the positive-semidefinite joint covariance domain must also be established. Nothing here implicitly grants a Gaussian joint distribution.
 Proof/definition method: Normalize canonical Schur complement, history-prediction and posterior variance formulas using Rocq Stdlib Field and polynomial algebra, with no new probability axioms or bespoke finite sums.
 Library reuse: SequentialReport, EquicorrelationSpectral, UnequalHistoryLinearPrediction, GaussianConditionalKernel and Rocq Stdlib Reals/Field/Psatz.
 Boundary: The result is deterministic regression or covariance algebra, not a proof of regular conditional probability, normality or measure-theoretic conditional expectation.
*)
Theorem d051_mean_two_score_gain : forall n c s x y:R, sequential_d n c<>0 -> sequential_d (n+2) c<>0 -> hp (n+2) c (s+x+y)=hp n c s+c*(x+y-2*hp n c s)/sequential_d (n+2) c.
Proof.
  intros; cbv [hp sequential_prediction sequential_d equicorr_schur_diagonal equicorr_schur_cross gk_variance gk_d gk_mass gk_precision] in *; field; nra.
Qed.

(** [d051_mean_future_two_batches_difference] (theorem).
 Mathematical meaning: The discrepancy between two alternative follow-up batteries has an exact common-denominator formula.
 Exact checked proposition: forall n k l c s t u:R, sequential_d (n+k) c<>0 -> sequential_d (n+l) c<>0 -> hp (n+k) c (s+t)-hp (n+l) c (s+u)=c*((s+t)*sequential_d (n+l) c-(s+u)*sequential_d (n+k) c)/(sequential_d (n+k) c*sequential_d (n+l) c).
 Premises and side conditions: Algebraic score counts are real scalars, with signed correlation admitted only where explicitly used inverses are nonzero. For probabilistic readings the positive-semidefinite joint covariance domain must also be established. Nothing here implicitly grants a Gaussian joint distribution.
 Proof/definition method: Normalize canonical Schur complement, history-prediction and posterior variance formulas using Rocq Stdlib Field and polynomial algebra, with no new probability axioms or bespoke finite sums.
 Library reuse: SequentialReport, EquicorrelationSpectral, UnequalHistoryLinearPrediction, GaussianConditionalKernel and Rocq Stdlib Reals/Field/Psatz.
 Boundary: The result is deterministic regression or covariance algebra, not a proof of regular conditional probability, normality or measure-theoretic conditional expectation.
*)
Theorem d051_mean_future_two_batches_difference : forall n k l c s t u:R, sequential_d (n+k) c<>0 -> sequential_d (n+l) c<>0 -> hp (n+k) c (s+t)-hp (n+l) c (s+u)=c*((s+t)*sequential_d (n+l) c-(s+u)*sequential_d (n+k) c)/(sequential_d (n+k) c*sequential_d (n+l) c).
Proof.
  intros; cbv [hp sequential_prediction sequential_d equicorr_schur_diagonal equicorr_schur_cross gk_variance gk_d gk_mass gk_precision] in *; field; nra.
Qed.

(** [d051_mean_one_score_residual] (theorem).
 Mathematical meaning: After assimilation of one new score, its residual is contracted by the denominator ratio.
 Exact checked proposition: forall n c s x:R, sequential_d n c<>0 -> sequential_d (n+1) c<>0 -> x-hp (n+1) c (s+x)=sequential_d n c*(x-hp n c s)/sequential_d (n+1) c.
 Premises and side conditions: Algebraic score counts are real scalars, with signed correlation admitted only where explicitly used inverses are nonzero. For probabilistic readings the positive-semidefinite joint covariance domain must also be established. Nothing here implicitly grants a Gaussian joint distribution.
 Proof/definition method: Normalize canonical Schur complement, history-prediction and posterior variance formulas using Rocq Stdlib Field and polynomial algebra, with no new probability axioms or bespoke finite sums.
 Library reuse: SequentialReport, EquicorrelationSpectral, UnequalHistoryLinearPrediction, GaussianConditionalKernel and Rocq Stdlib Reals/Field/Psatz.
 Boundary: The result is deterministic regression or covariance algebra, not a proof of regular conditional probability, normality or measure-theoretic conditional expectation.
*)
Theorem d051_mean_one_score_residual : forall n c s x:R, sequential_d n c<>0 -> sequential_d (n+1) c<>0 -> x-hp (n+1) c (s+x)=sequential_d n c*(x-hp n c s)/sequential_d (n+1) c.
Proof.
  intros; cbv [hp sequential_prediction sequential_d equicorr_schur_diagonal equicorr_schur_cross gk_variance gk_d gk_mass gk_precision] in *; field; nra.
Qed.

(** [d051_mean_batch_residual] (theorem).
 Mathematical meaning: The sum of post-update residuals is a denominator-scaled pre-update innovation.
 Exact checked proposition: forall n k c s t:R, sequential_d n c<>0 -> sequential_d (n+k) c<>0 -> t-k*hp (n+k) c (s+t)=sequential_d n c*(t-k*hp n c s)/sequential_d (n+k) c.
 Premises and side conditions: Algebraic score counts are real scalars, with signed correlation admitted only where explicitly used inverses are nonzero. For probabilistic readings the positive-semidefinite joint covariance domain must also be established. Nothing here implicitly grants a Gaussian joint distribution.
 Proof/definition method: Normalize canonical Schur complement, history-prediction and posterior variance formulas using Rocq Stdlib Field and polynomial algebra, with no new probability axioms or bespoke finite sums.
 Library reuse: SequentialReport, EquicorrelationSpectral, UnequalHistoryLinearPrediction, GaussianConditionalKernel and Rocq Stdlib Reals/Field/Psatz.
 Boundary: The result is deterministic regression or covariance algebra, not a proof of regular conditional probability, normality or measure-theoretic conditional expectation.
*)
Theorem d051_mean_batch_residual : forall n k c s t:R, sequential_d n c<>0 -> sequential_d (n+k) c<>0 -> t-k*hp (n+k) c (s+t)=sequential_d n c*(t-k*hp n c s)/sequential_d (n+k) c.
Proof.
  intros; cbv [hp sequential_prediction sequential_d equicorr_schur_diagonal equicorr_schur_cross gk_variance gk_d gk_mass gk_precision] in *; field; nra.
Qed.

(** [d051_mean_negative_single_update] (theorem).
 Mathematical meaning: A negative observation enters the posterior mean update with its expected signed coefficient.
 Exact checked proposition: forall n c s x:R, sequential_d n c<>0 -> sequential_d (n+1) c<>0 -> hp (n+1) c (s-x)=(sequential_d n c*hp n c s-c*x)/sequential_d (n+1) c.
 Premises and side conditions: Algebraic score counts are real scalars, with signed correlation admitted only where explicitly used inverses are nonzero. For probabilistic readings the positive-semidefinite joint covariance domain must also be established. Nothing here implicitly grants a Gaussian joint distribution.
 Proof/definition method: Normalize canonical Schur complement, history-prediction and posterior variance formulas using Rocq Stdlib Field and polynomial algebra, with no new probability axioms or bespoke finite sums.
 Library reuse: SequentialReport, EquicorrelationSpectral, UnequalHistoryLinearPrediction, GaussianConditionalKernel and Rocq Stdlib Reals/Field/Psatz.
 Boundary: The result is deterministic regression or covariance algebra, not a proof of regular conditional probability, normality or measure-theoretic conditional expectation.
*)
Theorem d051_mean_negative_single_update : forall n c s x:R, sequential_d n c<>0 -> sequential_d (n+1) c<>0 -> hp (n+1) c (s-x)=(sequential_d n c*hp n c s-c*x)/sequential_d (n+1) c.
Proof.
  intros; cbv [hp sequential_prediction sequential_d equicorr_schur_diagonal equicorr_schur_cross gk_variance gk_d gk_mass gk_precision] in *; field; nra.
Qed.

(** [d051_mean_second_stage_zero_sum] (theorem).
 Mathematical meaning: An additional zero-sum batch shrinks the already updated posterior mean by the correct factor.
 Exact checked proposition: forall n k l c s t:R, sequential_d (n+k) c<>0 -> sequential_d (n+k+l) c<>0 -> hp (n+k+l) c (s+t)=sequential_d (n+k) c*hp (n+k) c (s+t)/sequential_d (n+k+l) c.
 Premises and side conditions: Algebraic score counts are real scalars, with signed correlation admitted only where explicitly used inverses are nonzero. For probabilistic readings the positive-semidefinite joint covariance domain must also be established. Nothing here implicitly grants a Gaussian joint distribution.
 Proof/definition method: Normalize canonical Schur complement, history-prediction and posterior variance formulas using Rocq Stdlib Field and polynomial algebra, with no new probability axioms or bespoke finite sums.
 Library reuse: SequentialReport, EquicorrelationSpectral, UnequalHistoryLinearPrediction, GaussianConditionalKernel and Rocq Stdlib Reals/Field/Psatz.
 Boundary: The result is deterministic regression or covariance algebra, not a proof of regular conditional probability, normality or measure-theoretic conditional expectation.
*)
Theorem d051_mean_second_stage_zero_sum : forall n k l c s t:R, sequential_d (n+k) c<>0 -> sequential_d (n+k+l) c<>0 -> hp (n+k+l) c (s+t)=sequential_d (n+k) c*hp (n+k) c (s+t)/sequential_d (n+k+l) c.
Proof.
  intros; cbv [hp sequential_prediction sequential_d equicorr_schur_diagonal equicorr_schur_cross gk_variance gk_d gk_mass gk_precision] in *; field; nra.
Qed.

(** [d051_gk_shared_variance] (theorem).
 Mathematical meaning: The latent posterior variance agrees exactly with the Schur conditional covariance between distinct future scores.
 Exact checked proposition: forall xs:list R, forall c:R, gk_d xs c<>0 -> gk_variance xs c=equicorr_schur_cross (gk_mass xs) c.
 Premises and side conditions: Algebraic score counts are real scalars, with signed correlation admitted only where explicitly used inverses are nonzero. For probabilistic readings the positive-semidefinite joint covariance domain must also be established. Nothing here implicitly grants a Gaussian joint distribution.
 Proof/definition method: Normalize canonical Schur complement, history-prediction and posterior variance formulas using Rocq Stdlib Field and polynomial algebra, with no new probability axioms or bespoke finite sums.
 Library reuse: SequentialReport, EquicorrelationSpectral, UnequalHistoryLinearPrediction, GaussianConditionalKernel and Rocq Stdlib Reals/Field/Psatz.
 Boundary: The result is deterministic regression or covariance algebra, not a proof of regular conditional probability, normality or measure-theoretic conditional expectation.
*)
Theorem d051_gk_shared_variance : forall xs:list R, forall c:R, gk_d xs c<>0 -> gk_variance xs c=equicorr_schur_cross (gk_mass xs) c.
Proof.
  intros; cbv [hp sequential_prediction sequential_d equicorr_schur_diagonal equicorr_schur_cross gk_variance gk_d gk_mass gk_precision] in *; field; nra.
Qed.

(** [d051_gk_future_variance_decomposition] (theorem).
 Mathematical meaning: The future-score conditional variance is idiosyncratic variance plus posterior latent uncertainty.
 Exact checked proposition: forall xs:list R, forall c:R, gk_d xs c<>0 -> equicorr_schur_diagonal (gk_mass xs) c=(1-c)+gk_variance xs c.
 Premises and side conditions: Algebraic score counts are real scalars, with signed correlation admitted only where explicitly used inverses are nonzero. For probabilistic readings the positive-semidefinite joint covariance domain must also be established. Nothing here implicitly grants a Gaussian joint distribution.
 Proof/definition method: Normalize canonical Schur complement, history-prediction and posterior variance formulas using Rocq Stdlib Field and polynomial algebra, with no new probability axioms or bespoke finite sums.
 Library reuse: SequentialReport, EquicorrelationSpectral, UnequalHistoryLinearPrediction, GaussianConditionalKernel and Rocq Stdlib Reals/Field/Psatz.
 Boundary: The result is deterministic regression or covariance algebra, not a proof of regular conditional probability, normality or measure-theoretic conditional expectation.
*)
Theorem d051_gk_future_variance_decomposition : forall xs:list R, forall c:R, gk_d xs c<>0 -> equicorr_schur_diagonal (gk_mass xs) c=(1-c)+gk_variance xs c.
Proof.
  intros; cbv [hp sequential_prediction sequential_d equicorr_schur_diagonal equicorr_schur_cross gk_variance gk_d gk_mass gk_precision] in *; field; nra.
Qed.

(** [d051_gk_variance_reduction] (theorem).
 Mathematical meaning: The reduction in common-factor uncertainty is the observed-information Schur correction.
 Exact checked proposition: forall xs:list R, forall c:R, gk_d xs c<>0 -> gk_variance xs c=c-gk_mass xs*c*c/gk_d xs c.
 Premises and side conditions: Algebraic score counts are real scalars, with signed correlation admitted only where explicitly used inverses are nonzero. For probabilistic readings the positive-semidefinite joint covariance domain must also be established. Nothing here implicitly grants a Gaussian joint distribution.
 Proof/definition method: Normalize canonical Schur complement, history-prediction and posterior variance formulas using Rocq Stdlib Field and polynomial algebra, with no new probability axioms or bespoke finite sums.
 Library reuse: SequentialReport, EquicorrelationSpectral, UnequalHistoryLinearPrediction, GaussianConditionalKernel and Rocq Stdlib Reals/Field/Psatz.
 Boundary: The result is deterministic regression or covariance algebra, not a proof of regular conditional probability, normality or measure-theoretic conditional expectation.
*)
Theorem d051_gk_variance_reduction : forall xs:list R, forall c:R, gk_d xs c<>0 -> gk_variance xs c=c-gk_mass xs*c*c/gk_d xs c.
Proof.
  intros; cbv [hp sequential_prediction sequential_d equicorr_schur_diagonal equicorr_schur_cross gk_variance gk_d gk_mass gk_precision] in *; field; nra.
Qed.

(** [d051_gk_variance_zero_correlation] (theorem).
 Mathematical meaning: An independent-score common factor has zero posterior variance at c=0.
 Exact checked proposition: forall xs:list R, gk_variance xs 0=0.
 Premises and side conditions: Algebraic score counts are real scalars, with signed correlation admitted only where explicitly used inverses are nonzero. For probabilistic readings the positive-semidefinite joint covariance domain must also be established. Nothing here implicitly grants a Gaussian joint distribution.
 Proof/definition method: Normalize canonical Schur complement, history-prediction and posterior variance formulas using Rocq Stdlib Field and polynomial algebra, with no new probability axioms or bespoke finite sums.
 Library reuse: SequentialReport, EquicorrelationSpectral, UnequalHistoryLinearPrediction, GaussianConditionalKernel and Rocq Stdlib Reals/Field/Psatz.
 Boundary: The result is deterministic regression or covariance algebra, not a proof of regular conditional probability, normality or measure-theoretic conditional expectation.
*)
Theorem d051_gk_variance_zero_correlation : forall xs:list R, gk_variance xs 0=0.
Proof.
  intros; cbv [hp sequential_prediction sequential_d equicorr_schur_diagonal equicorr_schur_cross gk_variance gk_d gk_mass gk_precision] in *; field; nra.
Qed.

(** [d051_gk_variance_empty] (theorem).
 Mathematical meaning: With no scores observed, the latent posterior variance equals the prior variance.
 Exact checked proposition: forall c:R, 1-c<>0 -> gk_variance nil c=c.
 Premises and side conditions: Algebraic score counts are real scalars, with signed correlation admitted only where explicitly used inverses are nonzero. For probabilistic readings the positive-semidefinite joint covariance domain must also be established. Nothing here implicitly grants a Gaussian joint distribution.
 Proof/definition method: Normalize canonical Schur complement, history-prediction and posterior variance formulas using Rocq Stdlib Field and polynomial algebra, with no new probability axioms or bespoke finite sums.
 Library reuse: SequentialReport, EquicorrelationSpectral, UnequalHistoryLinearPrediction, GaussianConditionalKernel and Rocq Stdlib Reals/Field/Psatz.
 Boundary: The result is deterministic regression or covariance algebra, not a proof of regular conditional probability, normality or measure-theoretic conditional expectation.
*)
Theorem d051_gk_variance_empty : forall c:R, 1-c<>0 -> gk_variance nil c=c.
Proof.
  intros c Hc.
  unfold gk_variance, gk_d, gk_mass, sequential_d.
  simpl; field; nra.
Qed.

(** [d051_gk_precision_empty] (theorem).
 Mathematical meaning: The precision of an unobserved latent normal variable equals its prior precision.
 Exact checked proposition: forall c:R, c<>0 -> 1-c<>0 -> gk_precision nil c=/c.
 Premises and side conditions: Algebraic score counts are real scalars, with signed correlation admitted only where explicitly used inverses are nonzero. For probabilistic readings the positive-semidefinite joint covariance domain must also be established. Nothing here implicitly grants a Gaussian joint distribution.
 Proof/definition method: Normalize canonical Schur complement, history-prediction and posterior variance formulas using Rocq Stdlib Field and polynomial algebra, with no new probability axioms or bespoke finite sums.
 Library reuse: SequentialReport, EquicorrelationSpectral, UnequalHistoryLinearPrediction, GaussianConditionalKernel and Rocq Stdlib Reals/Field/Psatz.
 Boundary: The result is deterministic regression or covariance algebra, not a proof of regular conditional probability, normality or measure-theoretic conditional expectation.
*)
Theorem d051_gk_precision_empty : forall c:R, c<>0 -> 1-c<>0 -> gk_precision nil c=/c.
Proof.
  intros c Hc Hc1.
  unfold gk_precision, gk_mass.
  simpl; field; nra.
Qed.

(** [d051_gk_precision_scaled] (theorem).
 Mathematical meaning: Posterior precision times prior and residual variance factors equals the observed common-mode eigenvalue.
 Exact checked proposition: forall xs:list R, forall c:R, c<>0 -> 1-c<>0 -> gk_precision xs c*(c*(1-c))=gk_d xs c.
 Premises and side conditions: Algebraic score counts are real scalars, with signed correlation admitted only where explicitly used inverses are nonzero. For probabilistic readings the positive-semidefinite joint covariance domain must also be established. Nothing here implicitly grants a Gaussian joint distribution.
 Proof/definition method: Normalize canonical Schur complement, history-prediction and posterior variance formulas using Rocq Stdlib Field and polynomial algebra, with no new probability axioms or bespoke finite sums.
 Library reuse: SequentialReport, EquicorrelationSpectral, UnequalHistoryLinearPrediction, GaussianConditionalKernel and Rocq Stdlib Reals/Field/Psatz.
 Boundary: The result is deterministic regression or covariance algebra, not a proof of regular conditional probability, normality or measure-theoretic conditional expectation.
*)
Theorem d051_gk_precision_scaled : forall xs:list R, forall c:R, c<>0 -> 1-c<>0 -> gk_precision xs c*(c*(1-c))=gk_d xs c.
Proof.
  intros; cbv [hp sequential_prediction sequential_d equicorr_schur_diagonal equicorr_schur_cross gk_variance gk_d gk_mass gk_precision] in *; field; nra.
Qed.

(** [d051_gk_variance_times_precision] (theorem).
 Mathematical meaning: Posterior variance is the reciprocal of the updated precision in the admissible common-factor model.
 Exact checked proposition: forall xs:list R, forall c:R, 0<c -> c<1 -> gk_variance xs c*gk_precision xs c=1.
 Premises and side conditions: Algebraic score counts are real scalars, with signed correlation admitted only where explicitly used inverses are nonzero. For probabilistic readings the positive-semidefinite joint covariance domain must also be established. Nothing here implicitly grants a Gaussian joint distribution.
 Proof/definition method: Normalize canonical Schur complement, history-prediction and posterior variance formulas using Rocq Stdlib Field and polynomial algebra, with no new probability axioms or bespoke finite sums.
 Library reuse: SequentialReport, EquicorrelationSpectral, UnequalHistoryLinearPrediction, GaussianConditionalKernel and Rocq Stdlib Reals/Field/Psatz.
 Boundary: The result is deterministic regression or covariance algebra, not a proof of regular conditional probability, normality or measure-theoretic conditional expectation.
*)
Theorem d051_gk_variance_times_precision : forall xs:list R, forall c:R, 0<c -> c<1 -> gk_variance xs c*gk_precision xs c=1.
Proof.
  intros xs c Hc Hc1.
  rewrite Rmult_comm.
  apply gk_precision_variance; assumption.
Qed.


(** [d052_d_positive_strict] (theorem).
 Mathematical meaning: The covariance common eigenvalue stays strictly positive in the common-factor Gaussian regime with any nonnegative observation count.
 Exact checked proposition: forall n c:R, 0<=n -> 0<c -> c<1 -> 0<sequential_d n c.
 Premises and side conditions: The sign, covariance-domain, and invertibility requirements are explicit in each statement; real-valued counts are symbolic and a valid physical test count additionally requires integer nonnegativity. Signed correlations are allowed only with the full covariance block PSD when given a Gaussian interpretation.
 Proof/definition method: Reuse existing exact determinant/Schur identities, decompose conditional covariance and establish sign using Rocq Stdlib order algebra and monotonic division lemmas; no new Gaussian probability axioms.
 Library reuse: SequentialReport, EquicorrelationSpectral, GaussianCovarianceDomain D050/D051 identities, and Stdlib Reals, Lra, Psatz.
 Boundary: Theorems formalize deterministic covariance-domain consequences. Independence of a jointly Gaussian residual and its observed sigma-algebra remains an explicit unproved probability bridge.
*)
Theorem d052_d_positive_strict : forall n c:R, 0<=n -> 0<c -> c<1 -> 0<sequential_d n c.
Proof.
  intros; unfold sequential_d; nra.
Qed.

(** [d052_d_positive_closed] (theorem).
 Mathematical meaning: The common eigenvalue is positive even at the independent-score endpoint.
 Exact checked proposition: forall n c:R, 0<=n -> 0<=c -> c<1 -> 0<sequential_d n c.
 Premises and side conditions: The sign, covariance-domain, and invertibility requirements are explicit in each statement; real-valued counts are symbolic and a valid physical test count additionally requires integer nonnegativity. Signed correlations are allowed only with the full covariance block PSD when given a Gaussian interpretation.
 Proof/definition method: Reuse existing exact determinant/Schur identities, decompose conditional covariance and establish sign using Rocq Stdlib order algebra and monotonic division lemmas; no new Gaussian probability axioms.
 Library reuse: SequentialReport, EquicorrelationSpectral, GaussianCovarianceDomain D050/D051 identities, and Stdlib Reals, Lra, Psatz.
 Boundary: Theorems formalize deterministic covariance-domain consequences. Independence of a jointly Gaussian residual and its observed sigma-algebra remains an explicit unproved probability bridge.
*)
Theorem d052_d_positive_closed : forall n c:R, 0<=n -> 0<=c -> c<1 -> 0<sequential_d n c.
Proof.
  intros; unfold sequential_d; nra.
Qed.

(** [d052_d_increases_with_history] (theorem).
 Mathematical meaning: Adding observed scores strictly raises the common-mode eigenvalue for positive correlation.
 Exact checked proposition: forall n k c:R, 0<k -> 0<c -> sequential_d n c<sequential_d (n+k) c.
 Premises and side conditions: The sign, covariance-domain, and invertibility requirements are explicit in each statement; real-valued counts are symbolic and a valid physical test count additionally requires integer nonnegativity. Signed correlations are allowed only with the full covariance block PSD when given a Gaussian interpretation.
 Proof/definition method: Reuse existing exact determinant/Schur identities, decompose conditional covariance and establish sign using Rocq Stdlib order algebra and monotonic division lemmas; no new Gaussian probability axioms.
 Library reuse: SequentialReport, EquicorrelationSpectral, GaussianCovarianceDomain D050/D051 identities, and Stdlib Reals, Lra, Psatz.
 Boundary: Theorems formalize deterministic covariance-domain consequences. Independence of a jointly Gaussian residual and its observed sigma-algebra remains an explicit unproved probability bridge.
*)
Theorem d052_d_increases_with_history : forall n k c:R, 0<k -> 0<c -> sequential_d n c<sequential_d (n+k) c.
Proof.
  intros; unfold sequential_d; nra.
Qed.

(** [d052_d_decreases_signed] (theorem).
 Mathematical meaning: Under negative correlation, longer batteries have smaller common-mode eigenvalues, possibly reaching the singular boundary.
 Exact checked proposition: forall n k c:R, 0<k -> c<0 -> sequential_d (n+k) c<sequential_d n c.
 Premises and side conditions: The sign, covariance-domain, and invertibility requirements are explicit in each statement; real-valued counts are symbolic and a valid physical test count additionally requires integer nonnegativity. Signed correlations are allowed only with the full covariance block PSD when given a Gaussian interpretation.
 Proof/definition method: Reuse existing exact determinant/Schur identities, decompose conditional covariance and establish sign using Rocq Stdlib order algebra and monotonic division lemmas; no new Gaussian probability axioms.
 Library reuse: SequentialReport, EquicorrelationSpectral, GaussianCovarianceDomain D050/D051 identities, and Stdlib Reals, Lra, Psatz.
 Boundary: Theorems formalize deterministic covariance-domain consequences. Independence of a jointly Gaussian residual and its observed sigma-algebra remains an explicit unproved probability bridge.
*)
Theorem d052_d_decreases_signed : forall n k c:R, 0<k -> c<0 -> sequential_d (n+k) c<sequential_d n c.
Proof.
  intros; unfold sequential_d; nra.
Qed.

(** [d052_d_at_least_one] (theorem).
 Mathematical meaning: For nonnegative correlation, common covariance never drops below the unit marginal eigenvalue when a score is present.
 Exact checked proposition: forall n c:R, 1<=n -> 0<=c -> 1<=sequential_d n c.
 Premises and side conditions: The sign, covariance-domain, and invertibility requirements are explicit in each statement; real-valued counts are symbolic and a valid physical test count additionally requires integer nonnegativity. Signed correlations are allowed only with the full covariance block PSD when given a Gaussian interpretation.
 Proof/definition method: Reuse existing exact determinant/Schur identities, decompose conditional covariance and establish sign using Rocq Stdlib order algebra and monotonic division lemmas; no new Gaussian probability axioms.
 Library reuse: SequentialReport, EquicorrelationSpectral, GaussianCovarianceDomain D050/D051 identities, and Stdlib Reals, Lra, Psatz.
 Boundary: Theorems formalize deterministic covariance-domain consequences. Independence of a jointly Gaussian residual and its observed sigma-algebra remains an explicit unproved probability bridge.
*)
Theorem d052_d_at_least_one : forall n c:R, 1<=n -> 0<=c -> 1<=sequential_d n c.
Proof.
  intros; unfold sequential_d; nra.
Qed.

(** [d052_d_at_most_one_signed] (theorem).
 Mathematical meaning: For nonpositive correlation, common covariance does not exceed the marginal unit eigenvalue.
 Exact checked proposition: forall n c:R, 1<=n -> c<=0 -> sequential_d n c<=1.
 Premises and side conditions: The sign, covariance-domain, and invertibility requirements are explicit in each statement; real-valued counts are symbolic and a valid physical test count additionally requires integer nonnegativity. Signed correlations are allowed only with the full covariance block PSD when given a Gaussian interpretation.
 Proof/definition method: Reuse existing exact determinant/Schur identities, decompose conditional covariance and establish sign using Rocq Stdlib order algebra and monotonic division lemmas; no new Gaussian probability axioms.
 Library reuse: SequentialReport, EquicorrelationSpectral, GaussianCovarianceDomain D050/D051 identities, and Stdlib Reals, Lra, Psatz.
 Boundary: Theorems formalize deterministic covariance-domain consequences. Independence of a jointly Gaussian residual and its observed sigma-algebra remains an explicit unproved probability bridge.
*)
Theorem d052_d_at_most_one_signed : forall n c:R, 1<=n -> c<=0 -> sequential_d n c<=1.
Proof.
  intros; unfold sequential_d; nra.
Qed.

(** [d052_d_above_contrast] (theorem).
 Mathematical meaning: For common-factor dependence, the common covariance eigenvalue dominates the contrast eigenvalue.
 Exact checked proposition: forall n c:R, 0<=n -> 0<=c -> 1-c<=sequential_d n c.
 Premises and side conditions: The sign, covariance-domain, and invertibility requirements are explicit in each statement; real-valued counts are symbolic and a valid physical test count additionally requires integer nonnegativity. Signed correlations are allowed only with the full covariance block PSD when given a Gaussian interpretation.
 Proof/definition method: Reuse existing exact determinant/Schur identities, decompose conditional covariance and establish sign using Rocq Stdlib order algebra and monotonic division lemmas; no new Gaussian probability axioms.
 Library reuse: SequentialReport, EquicorrelationSpectral, GaussianCovarianceDomain D050/D051 identities, and Stdlib Reals, Lra, Psatz.
 Boundary: Theorems formalize deterministic covariance-domain consequences. Independence of a jointly Gaussian residual and its observed sigma-algebra remains an explicit unproved probability bridge.
*)
Theorem d052_d_above_contrast : forall n c:R, 0<=n -> 0<=c -> 1-c<=sequential_d n c.
Proof.
  intros; unfold sequential_d; nra.
Qed.

(** [d052_d_below_contrast_signed] (theorem).
 Mathematical meaning: With negative correlation, the common covariance eigenvalue lies below the contrast eigenvalue.
 Exact checked proposition: forall n c:R, 0<=n -> c<=0 -> sequential_d n c<=1-c.
 Premises and side conditions: The sign, covariance-domain, and invertibility requirements are explicit in each statement; real-valued counts are symbolic and a valid physical test count additionally requires integer nonnegativity. Signed correlations are allowed only with the full covariance block PSD when given a Gaussian interpretation.
 Proof/definition method: Reuse existing exact determinant/Schur identities, decompose conditional covariance and establish sign using Rocq Stdlib order algebra and monotonic division lemmas; no new Gaussian probability axioms.
 Library reuse: SequentialReport, EquicorrelationSpectral, GaussianCovarianceDomain D050/D051 identities, and Stdlib Reals, Lra, Psatz.
 Boundary: Theorems formalize deterministic covariance-domain consequences. Independence of a jointly Gaussian residual and its observed sigma-algebra remains an explicit unproved probability bridge.
*)
Theorem d052_d_below_contrast_signed : forall n c:R, 0<=n -> c<=0 -> sequential_d n c<=1-c.
Proof.
  intros; unfold sequential_d; nra.
Qed.

(** [d052_d_weak_increase] (theorem).
 Mathematical meaning: Nonnegative-correlation covariance feasibility persists monotonically under increased battery count in the direction of the common eigenvalue.
 Exact checked proposition: forall n k c:R, 0<=k -> 0<=c -> sequential_d n c<=sequential_d (n+k) c.
 Premises and side conditions: The sign, covariance-domain, and invertibility requirements are explicit in each statement; real-valued counts are symbolic and a valid physical test count additionally requires integer nonnegativity. Signed correlations are allowed only with the full covariance block PSD when given a Gaussian interpretation.
 Proof/definition method: Reuse existing exact determinant/Schur identities, decompose conditional covariance and establish sign using Rocq Stdlib order algebra and monotonic division lemmas; no new Gaussian probability axioms.
 Library reuse: SequentialReport, EquicorrelationSpectral, GaussianCovarianceDomain D050/D051 identities, and Stdlib Reals, Lra, Psatz.
 Boundary: Theorems formalize deterministic covariance-domain consequences. Independence of a jointly Gaussian residual and its observed sigma-algebra remains an explicit unproved probability bridge.
*)
Theorem d052_d_weak_increase : forall n k c:R, 0<=k -> 0<=c -> sequential_d n c<=sequential_d (n+k) c.
Proof.
  intros; unfold sequential_d; nra.
Qed.

(** [d052_d_weak_decrease_signed] (theorem).
 Mathematical meaning: Signed-correlation battery extension can only decrease the common eigenvalue when correlation is negative.
 Exact checked proposition: forall n k c:R, 0<=k -> c<=0 -> sequential_d (n+k) c<=sequential_d n c.
 Premises and side conditions: The sign, covariance-domain, and invertibility requirements are explicit in each statement; real-valued counts are symbolic and a valid physical test count additionally requires integer nonnegativity. Signed correlations are allowed only with the full covariance block PSD when given a Gaussian interpretation.
 Proof/definition method: Reuse existing exact determinant/Schur identities, decompose conditional covariance and establish sign using Rocq Stdlib order algebra and monotonic division lemmas; no new Gaussian probability axioms.
 Library reuse: SequentialReport, EquicorrelationSpectral, GaussianCovarianceDomain D050/D051 identities, and Stdlib Reals, Lra, Psatz.
 Boundary: Theorems formalize deterministic covariance-domain consequences. Independence of a jointly Gaussian residual and its observed sigma-algebra remains an explicit unproved probability bridge.
*)
Theorem d052_d_weak_decrease_signed : forall n k c:R, 0<=k -> c<=0 -> sequential_d (n+k) c<=sequential_d n c.
Proof.
  intros; unfold sequential_d; nra.
Qed.

(** [d052_cross_positive] (theorem).
 Mathematical meaning: In the common-factor regime the conditional covariance of distinct future scores is strictly positive.
 Exact checked proposition: forall n c:R, 0<c -> c<1 -> 0<sequential_d n c -> 0<equicorr_schur_cross n c.
 Premises and side conditions: The sign, covariance-domain, and invertibility requirements are explicit in each statement; real-valued counts are symbolic and a valid physical test count additionally requires integer nonnegativity. Signed correlations are allowed only with the full covariance block PSD when given a Gaussian interpretation.
 Proof/definition method: Reuse existing exact determinant/Schur identities, decompose conditional covariance and establish sign using Rocq Stdlib order algebra and monotonic division lemmas; no new Gaussian probability axioms.
 Library reuse: SequentialReport, EquicorrelationSpectral, GaussianCovarianceDomain D050/D051 identities, and Stdlib Reals, Lra, Psatz.
 Boundary: Theorems formalize deterministic covariance-domain consequences. Independence of a jointly Gaussian residual and its observed sigma-algebra remains an explicit unproved probability bridge.
*)
Theorem d052_cross_positive : forall n c:R, 0<c -> c<1 -> 0<sequential_d n c -> 0<equicorr_schur_cross n c.
Proof.
  intros n c Hc Hc1 Hd; rewrite d051_schur_cross_closed by lra; unfold Rdiv; apply Rmult_lt_0_compat; [nra|apply Rinv_0_lt_compat; nra].
Qed.

(** [d052_cross_nonnegative] (theorem).
 Mathematical meaning: The future off-diagonal covariance is nonnegative for any feasible nonnegative common correlation.
 Exact checked proposition: forall n c:R, 0<=c -> c<=1 -> 0<sequential_d n c -> 0<=equicorr_schur_cross n c.
 Premises and side conditions: The sign, covariance-domain, and invertibility requirements are explicit in each statement; real-valued counts are symbolic and a valid physical test count additionally requires integer nonnegativity. Signed correlations are allowed only with the full covariance block PSD when given a Gaussian interpretation.
 Proof/definition method: Reuse existing exact determinant/Schur identities, decompose conditional covariance and establish sign using Rocq Stdlib order algebra and monotonic division lemmas; no new Gaussian probability axioms.
 Library reuse: SequentialReport, EquicorrelationSpectral, GaussianCovarianceDomain D050/D051 identities, and Stdlib Reals, Lra, Psatz.
 Boundary: Theorems formalize deterministic covariance-domain consequences. Independence of a jointly Gaussian residual and its observed sigma-algebra remains an explicit unproved probability bridge.
*)
Theorem d052_cross_nonnegative : forall n c:R, 0<=c -> c<=1 -> 0<sequential_d n c -> 0<=equicorr_schur_cross n c.
Proof.
  intros n c Hc Hc1 Hd; rewrite d051_schur_cross_closed by lra; unfold Rdiv; apply Rmult_le_pos; [nra|left; apply Rinv_0_lt_compat; nra].
Qed.

(** [d052_diagonal_nonnegative] (theorem).
 Mathematical meaning: Full covariance feasibility for one additional score implies nonnegative Schur conditional variance.
 Exact checked proposition: forall n c:R, c<=1 -> 0<sequential_d n c -> 0<=sequential_d (n+1) c -> 0<=equicorr_schur_diagonal n c.
 Premises and side conditions: The sign, covariance-domain, and invertibility requirements are explicit in each statement; real-valued counts are symbolic and a valid physical test count additionally requires integer nonnegativity. Signed correlations are allowed only with the full covariance block PSD when given a Gaussian interpretation.
 Proof/definition method: Reuse existing exact determinant/Schur identities, decompose conditional covariance and establish sign using Rocq Stdlib order algebra and monotonic division lemmas; no new Gaussian probability axioms.
 Library reuse: SequentialReport, EquicorrelationSpectral, GaussianCovarianceDomain D050/D051 identities, and Stdlib Reals, Lra, Psatz.
 Boundary: Theorems formalize deterministic covariance-domain consequences. Independence of a jointly Gaussian residual and its observed sigma-algebra remains an explicit unproved probability bridge.
*)
Theorem d052_diagonal_nonnegative : forall n c:R, c<=1 -> 0<sequential_d n c -> 0<=sequential_d (n+1) c -> 0<=equicorr_schur_diagonal n c.
Proof.
  intros n c Hc Hd Hfull; rewrite (gcd_single_future_variance_eigenvalue n c) by lra; unfold Rdiv; apply Rmult_le_pos; [nra|left; apply Rinv_0_lt_compat; nra].
Qed.

(** [d052_diagonal_strict] (theorem).
 Mathematical meaning: Strict full covariance positivity gives positive conditional variance for one future score.
 Exact checked proposition: forall n c:R, c<1 -> 0<sequential_d n c -> 0<sequential_d (n+1) c -> 0<equicorr_schur_diagonal n c.
 Premises and side conditions: The sign, covariance-domain, and invertibility requirements are explicit in each statement; real-valued counts are symbolic and a valid physical test count additionally requires integer nonnegativity. Signed correlations are allowed only with the full covariance block PSD when given a Gaussian interpretation.
 Proof/definition method: Reuse existing exact determinant/Schur identities, decompose conditional covariance and establish sign using Rocq Stdlib order algebra and monotonic division lemmas; no new Gaussian probability axioms.
 Library reuse: SequentialReport, EquicorrelationSpectral, GaussianCovarianceDomain D050/D051 identities, and Stdlib Reals, Lra, Psatz.
 Boundary: Theorems formalize deterministic covariance-domain consequences. Independence of a jointly Gaussian residual and its observed sigma-algebra remains an explicit unproved probability bridge.
*)
Theorem d052_diagonal_strict : forall n c:R, c<1 -> 0<sequential_d n c -> 0<sequential_d (n+1) c -> 0<equicorr_schur_diagonal n c.
Proof.
  intros n c Hc Hd Hfull; rewrite (gcd_single_future_variance_eigenvalue n c) by lra; unfold Rdiv; apply Rmult_lt_0_compat; [nra|apply Rinv_0_lt_compat; nra].
Qed.

(** [d052_diagonal_upper_marginal] (theorem).
 Mathematical meaning: Conditioning cannot increase a marginal standardized score variance when the observed covariance block is positive.
 Exact checked proposition: forall n c:R, 0<=n -> 0<sequential_d n c -> equicorr_schur_diagonal n c<=1.
 Premises and side conditions: The sign, covariance-domain, and invertibility requirements are explicit in each statement; real-valued counts are symbolic and a valid physical test count additionally requires integer nonnegativity. Signed correlations are allowed only with the full covariance block PSD when given a Gaussian interpretation.
 Proof/definition method: Reuse existing exact determinant/Schur identities, decompose conditional covariance and establish sign using Rocq Stdlib order algebra and monotonic division lemmas; no new Gaussian probability axioms.
 Library reuse: SequentialReport, EquicorrelationSpectral, GaussianCovarianceDomain D050/D051 identities, and Stdlib Reals, Lra, Psatz.
 Boundary: Theorems formalize deterministic covariance-domain consequences. Independence of a jointly Gaussian residual and its observed sigma-algebra remains an explicit unproved probability bridge.
*)
Theorem d052_diagonal_upper_marginal : forall n c:R, 0<=n -> 0<sequential_d n c -> equicorr_schur_diagonal n c<=1.
Proof.
  intros n c Hn Hd; unfold equicorr_schur_diagonal; assert (H : 0<=n*c*c/sequential_d n c) by (unfold Rdiv; apply Rmult_le_pos; [nra|left; apply Rinv_0_lt_compat; nra]); lra.
Qed.

(** [d052_diagonal_strict_reduction] (theorem).
 Mathematical meaning: With nonzero correlation and a positive observed count, the conditional marginal variance strictly decreases.
 Exact checked proposition: forall n c:R, 0<n -> c<>0 -> 0<sequential_d n c -> equicorr_schur_diagonal n c<1.
 Premises and side conditions: The sign, covariance-domain, and invertibility requirements are explicit in each statement; real-valued counts are symbolic and a valid physical test count additionally requires integer nonnegativity. Signed correlations are allowed only with the full covariance block PSD when given a Gaussian interpretation.
 Proof/definition method: Reuse existing exact determinant/Schur identities, decompose conditional covariance and establish sign using Rocq Stdlib order algebra and monotonic division lemmas; no new Gaussian probability axioms.
 Library reuse: SequentialReport, EquicorrelationSpectral, GaussianCovarianceDomain D050/D051 identities, and Stdlib Reals, Lra, Psatz.
 Boundary: Theorems formalize deterministic covariance-domain consequences. Independence of a jointly Gaussian residual and its observed sigma-algebra remains an explicit unproved probability bridge.
*)
Theorem d052_diagonal_strict_reduction : forall n c:R, 0<n -> c<>0 -> 0<sequential_d n c -> equicorr_schur_diagonal n c<1.
Proof.
  intros n c Hn Hc Hd; unfold equicorr_schur_diagonal; assert (Hnum : 0 < n*c*c).
  { replace (n*c*c) with (n*(c*c)) by ring.
    apply Rmult_lt_0_compat; [exact Hn | nra]. }
  assert (H : 0<n*c*c/sequential_d n c).
  { unfold Rdiv; apply Rmult_lt_0_compat; [exact Hnum | apply Rinv_0_lt_compat; exact Hd]. }
  lra.
Qed.

(** [d052_contrast_nonnegative] (theorem).
 Mathematical meaning: All future-score contrast directions have nonnegative variance at correlations at most one.
 Exact checked proposition: forall n c:R, c<=1 -> 0<=equicorr_schur_diagonal n c-equicorr_schur_cross n c.
 Premises and side conditions: The sign, covariance-domain, and invertibility requirements are explicit in each statement; real-valued counts are symbolic and a valid physical test count additionally requires integer nonnegativity. Signed correlations are allowed only with the full covariance block PSD when given a Gaussian interpretation.
 Proof/definition method: Reuse existing exact determinant/Schur identities, decompose conditional covariance and establish sign using Rocq Stdlib order algebra and monotonic division lemmas; no new Gaussian probability axioms.
 Library reuse: SequentialReport, EquicorrelationSpectral, GaussianCovarianceDomain D050/D051 identities, and Stdlib Reals, Lra, Psatz.
 Boundary: Theorems formalize deterministic covariance-domain consequences. Independence of a jointly Gaussian residual and its observed sigma-algebra remains an explicit unproved probability bridge.
*)
Theorem d052_contrast_nonnegative : forall n c:R, c<=1 -> 0<=equicorr_schur_diagonal n c-equicorr_schur_cross n c.
Proof.
  intros n c Hc; rewrite equicorr_schur_diagonal_contrast_gap; lra.
Qed.

(** [d052_contrast_strict] (theorem).
 Mathematical meaning: Under strict upper correlation bound, nonzero contrast directions have positive variance.
 Exact checked proposition: forall n c:R, c<1 -> 0<equicorr_schur_diagonal n c-equicorr_schur_cross n c.
 Premises and side conditions: The sign, covariance-domain, and invertibility requirements are explicit in each statement; real-valued counts are symbolic and a valid physical test count additionally requires integer nonnegativity. Signed correlations are allowed only with the full covariance block PSD when given a Gaussian interpretation.
 Proof/definition method: Reuse existing exact determinant/Schur identities, decompose conditional covariance and establish sign using Rocq Stdlib order algebra and monotonic division lemmas; no new Gaussian probability axioms.
 Library reuse: SequentialReport, EquicorrelationSpectral, GaussianCovarianceDomain D050/D051 identities, and Stdlib Reals, Lra, Psatz.
 Boundary: Theorems formalize deterministic covariance-domain consequences. Independence of a jointly Gaussian residual and its observed sigma-algebra remains an explicit unproved probability bridge.
*)
Theorem d052_contrast_strict : forall n c:R, c<1 -> 0<equicorr_schur_diagonal n c-equicorr_schur_cross n c.
Proof.
  intros n c Hc; rewrite equicorr_schur_diagonal_contrast_gap; lra.
Qed.

(** [d052_cross_le_diagonal] (theorem).
 Mathematical meaning: Residual off-diagonal covariance cannot exceed its corresponding conditional diagonal whenever c<=1.
 Exact checked proposition: forall n c:R, c<=1 -> equicorr_schur_cross n c<=equicorr_schur_diagonal n c.
 Premises and side conditions: The sign, covariance-domain, and invertibility requirements are explicit in each statement; real-valued counts are symbolic and a valid physical test count additionally requires integer nonnegativity. Signed correlations are allowed only with the full covariance block PSD when given a Gaussian interpretation.
 Proof/definition method: Reuse existing exact determinant/Schur identities, decompose conditional covariance and establish sign using Rocq Stdlib order algebra and monotonic division lemmas; no new Gaussian probability axioms.
 Library reuse: SequentialReport, EquicorrelationSpectral, GaussianCovarianceDomain D050/D051 identities, and Stdlib Reals, Lra, Psatz.
 Boundary: Theorems formalize deterministic covariance-domain consequences. Independence of a jointly Gaussian residual and its observed sigma-algebra remains an explicit unproved probability bridge.
*)
Theorem d052_cross_le_diagonal : forall n c:R, c<=1 -> equicorr_schur_cross n c<=equicorr_schur_diagonal n c.
Proof.
  intros n c Hc; pose proof (equicorr_schur_diagonal_contrast_gap n c); lra.
Qed.

(** [d052_cross_lt_diagonal] (theorem).
 Mathematical meaning: Strictly admissible contrast modes force every off-diagonal future covariance below the conditional variance.
 Exact checked proposition: forall n c:R, c<1 -> equicorr_schur_cross n c<equicorr_schur_diagonal n c.
 Premises and side conditions: The sign, covariance-domain, and invertibility requirements are explicit in each statement; real-valued counts are symbolic and a valid physical test count additionally requires integer nonnegativity. Signed correlations are allowed only with the full covariance block PSD when given a Gaussian interpretation.
 Proof/definition method: Reuse existing exact determinant/Schur identities, decompose conditional covariance and establish sign using Rocq Stdlib order algebra and monotonic division lemmas; no new Gaussian probability axioms.
 Library reuse: SequentialReport, EquicorrelationSpectral, GaussianCovarianceDomain D050/D051 identities, and Stdlib Reals, Lra, Psatz.
 Boundary: Theorems formalize deterministic covariance-domain consequences. Independence of a jointly Gaussian residual and its observed sigma-algebra remains an explicit unproved probability bridge.
*)
Theorem d052_cross_lt_diagonal : forall n c:R, c<1 -> equicorr_schur_cross n c<equicorr_schur_diagonal n c.
Proof.
  intros n c Hc; pose proof (equicorr_schur_diagonal_contrast_gap n c); lra.
Qed.

(** [d052_common_mode_nonnegative] (theorem).
 Mathematical meaning: The common-mode direction of k future Gaussian residuals is PSD throughout the full signed covariance domain.
 Exact checked proposition: forall n k c:R, c<=1 -> 0<sequential_d n c -> 0<=sequential_d (n+k) c -> 0<=equicorr_schur_diagonal n c+(k-1)*equicorr_schur_cross n c.
 Premises and side conditions: The sign, covariance-domain, and invertibility requirements are explicit in each statement; real-valued counts are symbolic and a valid physical test count additionally requires integer nonnegativity. Signed correlations are allowed only with the full covariance block PSD when given a Gaussian interpretation.
 Proof/definition method: Reuse existing exact determinant/Schur identities, decompose conditional covariance and establish sign using Rocq Stdlib order algebra and monotonic division lemmas; no new Gaussian probability axioms.
 Library reuse: SequentialReport, EquicorrelationSpectral, GaussianCovarianceDomain D050/D051 identities, and Stdlib Reals, Lra, Psatz.
 Boundary: Theorems formalize deterministic covariance-domain consequences. Independence of a jointly Gaussian residual and its observed sigma-algebra remains an explicit unproved probability bridge.
*)
Theorem d052_common_mode_nonnegative : forall n k c:R, c<=1 -> 0<sequential_d n c -> 0<=sequential_d (n+k) c -> 0<=equicorr_schur_diagonal n c+(k-1)*equicorr_schur_cross n c.
Proof.
  intros n k c Hc Hd Hfull; rewrite d051_schur_common_mode by lra; apply gcd_common_mode_sign; assumption.
Qed.

(** [d052_common_mode_strict] (theorem).
 Mathematical meaning: Strict full covariance feasibility makes the future common-mode eigenvalue strictly positive.
 Exact checked proposition: forall n k c:R, c<1 -> 0<sequential_d n c -> 0<sequential_d (n+k) c -> 0<equicorr_schur_diagonal n c+(k-1)*equicorr_schur_cross n c.
 Premises and side conditions: The sign, covariance-domain, and invertibility requirements are explicit in each statement; real-valued counts are symbolic and a valid physical test count additionally requires integer nonnegativity. Signed correlations are allowed only with the full covariance block PSD when given a Gaussian interpretation.
 Proof/definition method: Reuse existing exact determinant/Schur identities, decompose conditional covariance and establish sign using Rocq Stdlib order algebra and monotonic division lemmas; no new Gaussian probability axioms.
 Library reuse: SequentialReport, EquicorrelationSpectral, GaussianCovarianceDomain D050/D051 identities, and Stdlib Reals, Lra, Psatz.
 Boundary: Theorems formalize deterministic covariance-domain consequences. Independence of a jointly Gaussian residual and its observed sigma-algebra remains an explicit unproved probability bridge.
*)
Theorem d052_common_mode_strict : forall n k c:R, c<1 -> 0<sequential_d n c -> 0<sequential_d (n+k) c -> 0<equicorr_schur_diagonal n c+(k-1)*equicorr_schur_cross n c.
Proof.
  intros n k c Hc Hd Hfull; rewrite d051_schur_common_mode by lra; apply gcd_common_mode_strict; assumption.
Qed.

(** [d052_future_sum_nonnegative] (theorem).
 Mathematical meaning: A future-batch total has nonnegative conditional variance in the signed full-covariance domain.
 Exact checked proposition: forall n k c:R, 0<=k -> c<=1 -> 0<sequential_d n c -> 0<=sequential_d (n+k) c -> 0<=k*equicorr_schur_diagonal n c+k*(k-1)*equicorr_schur_cross n c.
 Premises and side conditions: The sign, covariance-domain, and invertibility requirements are explicit in each statement; real-valued counts are symbolic and a valid physical test count additionally requires integer nonnegativity. Signed correlations are allowed only with the full covariance block PSD when given a Gaussian interpretation.
 Proof/definition method: Reuse existing exact determinant/Schur identities, decompose conditional covariance and establish sign using Rocq Stdlib order algebra and monotonic division lemmas; no new Gaussian probability axioms.
 Library reuse: SequentialReport, EquicorrelationSpectral, GaussianCovarianceDomain D050/D051 identities, and Stdlib Reals, Lra, Psatz.
 Boundary: Theorems formalize deterministic covariance-domain consequences. Independence of a jointly Gaussian residual and its observed sigma-algebra remains an explicit unproved probability bridge.
*)
Theorem d052_future_sum_nonnegative : forall n k c:R, 0<=k -> c<=1 -> 0<sequential_d n c -> 0<=sequential_d (n+k) c -> 0<=k*equicorr_schur_diagonal n c+k*(k-1)*equicorr_schur_cross n c.
Proof.
  intros n k c Hk Hc Hd Hfull.
  rewrite d051_schur_future_sum_variance by lra.
  replace (k*(1-c)*sequential_d (n+k) c/sequential_d n c)
    with (k*((1-c)*sequential_d (n+k) c/sequential_d n c)) by (field; lra).
  apply Rmult_le_pos; [assumption|apply gcd_common_mode_sign; assumption].
Qed.

(** [d052_future_sum_strict] (theorem).
 Mathematical meaning: A positive-length future-batch sum has positive conditional variance in the strict signed covariance domain.
 Exact checked proposition: forall n k c:R, 0<k -> c<1 -> 0<sequential_d n c -> 0<sequential_d (n+k) c -> 0<k*equicorr_schur_diagonal n c+k*(k-1)*equicorr_schur_cross n c.
 Premises and side conditions: The sign, covariance-domain, and invertibility requirements are explicit in each statement; real-valued counts are symbolic and a valid physical test count additionally requires integer nonnegativity. Signed correlations are allowed only with the full covariance block PSD when given a Gaussian interpretation.
 Proof/definition method: Reuse existing exact determinant/Schur identities, decompose conditional covariance and establish sign using Rocq Stdlib order algebra and monotonic division lemmas; no new Gaussian probability axioms.
 Library reuse: SequentialReport, EquicorrelationSpectral, GaussianCovarianceDomain D050/D051 identities, and Stdlib Reals, Lra, Psatz.
 Boundary: Theorems formalize deterministic covariance-domain consequences. Independence of a jointly Gaussian residual and its observed sigma-algebra remains an explicit unproved probability bridge.
*)
Theorem d052_future_sum_strict : forall n k c:R, 0<k -> c<1 -> 0<sequential_d n c -> 0<sequential_d (n+k) c -> 0<k*equicorr_schur_diagonal n c+k*(k-1)*equicorr_schur_cross n c.
Proof.
  intros n k c Hk Hc Hd Hfull.
  rewrite d051_schur_future_sum_variance by lra.
  replace (k*(1-c)*sequential_d (n+k) c/sequential_d n c)
    with (k*((1-c)*sequential_d (n+k) c/sequential_d n c)) by (field; lra).
  apply Rmult_lt_0_compat; [assumption|apply gcd_common_mode_strict; assumption].
Qed.

(** [d052_variance_monotone] (theorem).
 Mathematical meaning: Adding an admissible observation block does not increase predictive marginal variance.
 Exact checked proposition: forall n k c:R, 0<=k -> c<=1 -> 0<sequential_d n c -> 0<sequential_d (n+k) c -> equicorr_schur_diagonal (n+k) c<=equicorr_schur_diagonal n c.
 Premises and side conditions: The sign, covariance-domain, and invertibility requirements are explicit in each statement; real-valued counts are symbolic and a valid physical test count additionally requires integer nonnegativity. Signed correlations are allowed only with the full covariance block PSD when given a Gaussian interpretation.
 Proof/definition method: Reuse existing exact determinant/Schur identities, decompose conditional covariance and establish sign using Rocq Stdlib order algebra and monotonic division lemmas; no new Gaussian probability axioms.
 Library reuse: SequentialReport, EquicorrelationSpectral, GaussianCovarianceDomain D050/D051 identities, and Stdlib Reals, Lra, Psatz.
 Boundary: Theorems formalize deterministic covariance-domain consequences. Independence of a jointly Gaussian residual and its observed sigma-algebra remains an explicit unproved probability bridge.
*)
Theorem d052_variance_monotone : forall n k c:R, 0<=k -> c<=1 -> 0<sequential_d n c -> 0<sequential_d (n+k) c -> equicorr_schur_diagonal (n+k) c<=equicorr_schur_diagonal n c.
Proof.
  intros n k c Hk Hc Hd Hd2.
  pose proof
    (d051_cov_diagonal_variance_drop n k c
       (Rgt_not_eq _ _ Hd) (Rgt_not_eq _ _ Hd2)) as Hdiff.
  assert (Hnum : 0 <= k*c*c*(1-c)).
  { replace (k*c*c*(1-c)) with ((k*(c*c))*(1-c)) by ring.
    apply Rmult_le_pos.
    - apply Rmult_le_pos; [exact Hk | nra].
    - lra. }
  assert (Hden : 0 < sequential_d n c * sequential_d (n+k) c)
    by (apply Rmult_lt_0_compat; assumption).
  assert (Hq : 0 <= k*c*c*(1-c)/
                  (sequential_d n c*sequential_d (n+k) c)).
  { unfold Rdiv.
    apply Rmult_le_pos; [exact Hnum |].
    left; apply Rinv_0_lt_compat; exact Hden. }
  lra.
Qed.

(** [d052_cross_covariance_monotone] (theorem).
 Mathematical meaning: Adding observations reduces the shared residual cross-covariance even when the common correlation is negative.
 Exact checked proposition: forall n k c:R, 0<=k -> c<=1 -> 0<sequential_d n c -> 0<sequential_d (n+k) c -> equicorr_schur_cross (n+k) c<=equicorr_schur_cross n c.
 Premises and side conditions: The sign, covariance-domain, and invertibility requirements are explicit in each statement; real-valued counts are symbolic and a valid physical test count additionally requires integer nonnegativity. Signed correlations are allowed only with the full covariance block PSD when given a Gaussian interpretation.
 Proof/definition method: Reuse existing exact determinant/Schur identities, decompose conditional covariance and establish sign using Rocq Stdlib order algebra and monotonic division lemmas; no new Gaussian probability axioms.
 Library reuse: SequentialReport, EquicorrelationSpectral, GaussianCovarianceDomain D050/D051 identities, and Stdlib Reals, Lra, Psatz.
 Boundary: Theorems formalize deterministic covariance-domain consequences. Independence of a jointly Gaussian residual and its observed sigma-algebra remains an explicit unproved probability bridge.
*)
Theorem d052_cross_covariance_monotone : forall n k c:R, 0<=k -> c<=1 -> 0<sequential_d n c -> 0<sequential_d (n+k) c -> equicorr_schur_cross (n+k) c<=equicorr_schur_cross n c.
Proof.
  intros n k c Hk Hc Hd Hd2.
  pose proof (d052_variance_monotone n k c Hk Hc Hd Hd2) as Hvariance.
  pose proof (equicorr_schur_diagonal_contrast_gap n c) as Hcontrast_old.
  pose proof (equicorr_schur_diagonal_contrast_gap (n+k) c) as Hcontrast_new.
  lra.
Qed.

(** [d052_cross_below_prior] (theorem).
 Mathematical meaning: The conditional common covariance cannot exceed its prior value after observing a nonnegative number of scores.
 Exact checked proposition: forall n c:R, 0<=n -> 0<sequential_d n c -> equicorr_schur_cross n c<=c.
 Premises and side conditions: The sign, covariance-domain, and invertibility requirements are explicit in each statement; real-valued counts are symbolic and a valid physical test count additionally requires integer nonnegativity. Signed correlations are allowed only with the full covariance block PSD when given a Gaussian interpretation.
 Proof/definition method: Reuse existing exact determinant/Schur identities, decompose conditional covariance and establish sign using Rocq Stdlib order algebra and monotonic division lemmas; no new Gaussian probability axioms.
 Library reuse: SequentialReport, EquicorrelationSpectral, GaussianCovarianceDomain D050/D051 identities, and Stdlib Reals, Lra, Psatz.
 Boundary: Theorems formalize deterministic covariance-domain consequences. Independence of a jointly Gaussian residual and its observed sigma-algebra remains an explicit unproved probability bridge.
*)
Theorem d052_cross_below_prior : forall n c:R, 0<=n -> 0<sequential_d n c -> equicorr_schur_cross n c<=c.
Proof.
  intros n c Hn Hd; unfold equicorr_schur_cross; assert (H:0<=n*c*c/sequential_d n c) by (unfold Rdiv; apply Rmult_le_pos; [nra|left; apply Rinv_0_lt_compat; nra]); lra.
Qed.

(** [d052_cross_strict_below_prior] (theorem).
 Mathematical meaning: Conditioning on a positively sized battery with nonzero correlation strictly reduces shared covariance.
 Exact checked proposition: forall n c:R, 0<n -> c<>0 -> 0<sequential_d n c -> equicorr_schur_cross n c<c.
 Premises and side conditions: The sign, covariance-domain, and invertibility requirements are explicit in each statement; real-valued counts are symbolic and a valid physical test count additionally requires integer nonnegativity. Signed correlations are allowed only with the full covariance block PSD when given a Gaussian interpretation.
 Proof/definition method: Reuse existing exact determinant/Schur identities, decompose conditional covariance and establish sign using Rocq Stdlib order algebra and monotonic division lemmas; no new Gaussian probability axioms.
 Library reuse: SequentialReport, EquicorrelationSpectral, GaussianCovarianceDomain D050/D051 identities, and Stdlib Reals, Lra, Psatz.
 Boundary: Theorems formalize deterministic covariance-domain consequences. Independence of a jointly Gaussian residual and its observed sigma-algebra remains an explicit unproved probability bridge.
*)
Theorem d052_cross_strict_below_prior : forall n c:R, 0<n -> c<>0 -> 0<sequential_d n c -> equicorr_schur_cross n c<c.
Proof.
  intros n c Hn Hc Hd; unfold equicorr_schur_cross; assert (Hnum : 0 < n*c*c).
  { replace (n*c*c) with (n*(c*c)) by ring.
    apply Rmult_lt_0_compat; [exact Hn | nra]. }
  assert (H : 0<n*c*c/sequential_d n c).
  { unfold Rdiv; apply Rmult_lt_0_compat; [exact Hnum | apply Rinv_0_lt_compat; exact Hd]. }
  lra.
Qed.

(** [d052_mean_positive_gain] (theorem).
 Mathematical meaning: A strictly positive observed-score sum yields a positive Gaussian predictor under positive common correlation.
 Exact checked proposition: forall n c s:R, 0<c -> 0<sequential_d n c -> 0<s -> 0<hp n c s.
 Premises and side conditions: The sign, covariance-domain, and invertibility requirements are explicit in each statement; real-valued counts are symbolic and a valid physical test count additionally requires integer nonnegativity. Signed correlations are allowed only with the full covariance block PSD when given a Gaussian interpretation.
 Proof/definition method: Reuse existing exact determinant/Schur identities, decompose conditional covariance and establish sign using Rocq Stdlib order algebra and monotonic division lemmas; no new Gaussian probability axioms.
 Library reuse: SequentialReport, EquicorrelationSpectral, GaussianCovarianceDomain D050/D051 identities, and Stdlib Reals, Lra, Psatz.
 Boundary: Theorems formalize deterministic covariance-domain consequences. Independence of a jointly Gaussian residual and its observed sigma-algebra remains an explicit unproved probability bridge.
*)
Theorem d052_mean_positive_gain : forall n c s:R, 0<c -> 0<sequential_d n c -> 0<s -> 0<hp n c s.
Proof.
  intros n c s Hc Hd Hs; unfold hp; unfold Rdiv; apply Rmult_lt_0_compat; [nra|apply Rinv_0_lt_compat; nra].
Qed.

(** [d052_mean_nonnegative_gain] (theorem).
 Mathematical meaning: The Gaussian sufficient-history predictor preserves nonnegative score sums when the regression gain is nonnegative.
 Exact checked proposition: forall n c s:R, 0<=c -> 0<sequential_d n c -> 0<=s -> 0<=hp n c s.
 Premises and side conditions: The sign, covariance-domain, and invertibility requirements are explicit in each statement; real-valued counts are symbolic and a valid physical test count additionally requires integer nonnegativity. Signed correlations are allowed only with the full covariance block PSD when given a Gaussian interpretation.
 Proof/definition method: Reuse existing exact determinant/Schur identities, decompose conditional covariance and establish sign using Rocq Stdlib order algebra and monotonic division lemmas; no new Gaussian probability axioms.
 Library reuse: SequentialReport, EquicorrelationSpectral, GaussianCovarianceDomain D050/D051 identities, and Stdlib Reals, Lra, Psatz.
 Boundary: Theorems formalize deterministic covariance-domain consequences. Independence of a jointly Gaussian residual and its observed sigma-algebra remains an explicit unproved probability bridge.
*)
Theorem d052_mean_nonnegative_gain : forall n c s:R, 0<=c -> 0<sequential_d n c -> 0<=s -> 0<=hp n c s.
Proof.
  intros n c s Hc Hd Hs; unfold hp; unfold Rdiv; apply Rmult_le_pos; [nra|left; apply Rinv_0_lt_compat; nra].
Qed.

(** [gcd_psd_quadratic_zero_cross] (theorem).
 Mathematical meaning: A nonnegative quadratic polynomial whose
 constant term is zero cannot have a nonzero linear coefficient.
 This is the scalar null-direction principle for a positive-semidefinite
 covariance form: a zero-variance direction is uncorrelated with
 every other square-integrable linear contrast.
 Exact proposition: if a*t*t + 2*b*t is nonnegative for every real t,
 then b=0, without assuming a strictly positive eigenvalue.
 Premises and side conditions: Nonnegativity for all t, not simply for one value of t.
 Proof/definition method: The values t=1 and t=-1 establish a>=0. Evaluate at
 t=-b/(a+1), multiply by the positive square of the denominator,
 and conclude that (a+2)*b*b=0 using field arithmetic and order.
 Library reuse: Rocq Stdlib Rmult_le_pos, Rmult_integral, Field,
 Lra and Psatz; no hand-built covariance, pseudoinverse or measure API.
 Boundary: An exact PSD-nullspace lemma. It does not itself prove
 Gaussian independence or any conditional-expectation identity.
*)
Theorem gcd_psd_quadratic_zero_cross :
  forall a b : R,
    (forall t : R, 0 <= a*t*t + 2*b*t) ->
    b = 0.
Proof.
  intros a b Hquad.
  assert (Ha : 0 <= a).
  { pose proof (Hquad 1) as Hplus.
    pose proof (Hquad (-1)) as Hminus.
    nra. }
  assert (Hd : a+1 <> 0) by lra.
  assert (Hd2 : 0 <= (a+1)*(a+1)) by nra.
  pose proof (Hquad (-b/(a+1))) as Hmin.
  assert (Hidentity :
    (a*(-b/(a+1))*(-b/(a+1)) + 2*b*(-b/(a+1))) *
      ((a+1)*(a+1)) = -(a+2)*(b*b)).
  { field; lra. }
  assert (Hnonneg :
    0 <= (a*(-b/(a+1))*(-b/(a+1)) + 2*b*(-b/(a+1))) *
      ((a+1)*(a+1))).
  { apply Rmult_le_pos; assumption. }
  rewrite Hidentity in Hnonneg.
  assert (Hproduct_nonnegative : 0 <= (a+2)*(b*b)).
  { apply Rmult_le_pos; nra. }
  assert (Hproduct_zero : (a+2)*(b*b) = 0) by nra.
  apply Rmult_integral in Hproduct_zero as [Hcoefficient | Hsquare].
  - lra.
  - nra.
Qed.

(** [gcd_psd_null_covariance] (theorem).
 Mathematical meaning: If the quadratic form associated with a real
 symmetric two-by-two covariance block is PSD and the second diagonal
 variance is zero, then its cross covariance is zero.
 Exact proposition: universal nonnegativity of a*t*t+2*b*t+c and
 c=0 together imply b=0; the leading variance need not be positive.
 Premises and side conditions: Full PSD polynomial inequality for all real contrasts and
 an exact zero diagonal element, including singular covariance cases.
 Proof/definition method: Substitute the zero constant and reuse the previous checked
 scalar null-direction theorem; no independent PSD algorithm is added.
 Library reuse: [gcd_psd_quadratic_zero_cross] and Rocq Stdlib Psatz.
 Boundary: This algebraic fact supports the singular Gaussian residual
 covariance calculation, but cannot substitute for sigma-algebra
 independence or an event-integral conditional-expectation proof.
*)
Theorem gcd_psd_null_covariance :
  forall a b c : R,
    (forall t : R, 0 <= a*t*t + 2*b*t + c) ->
    c = 0 ->
    b = 0.
Proof.
  intros a b c Hquad Hzero.
  subst c.
  apply (gcd_psd_quadratic_zero_cross a b).
  intro t.
  specialize (Hquad t).
  nra.
Qed.


(** [gcd_psd_covariance_cauchy_schwarz] (theorem).
 Mathematical meaning: Every positive-semidefinite two-by-two covariance
 block satisfies the complete Cauchy--Schwarz inequality b^2 <= a*c.
 This remains valid when a=0 or c=0 and when b is negative.
 Exact proposition: for nonnegative diagonal variances a,c, nonnegativity
 of the quadratic form a*t^2+2*b*t+c for all real t entails b*b<=a*c.
 Premises and side conditions: Both diagonal entries are nonnegative;
 the entire quadratic form must be nonnegative for every real t.
 Proof/definition method: For a>0 evaluate the form at t=-b/a and
 multiply by the positive denominator. For a=0, a nonzero cross term
 makes the form negative at t=-(c+1)/(2*b), a contradiction.
 Library reuse: Stdlib Rle_lt_or_eq_dec, Req_EM_T, Field, Ring, Psatz.
 No Gaussian measure, new matrix structure, assumed independence or axiom.
 Boundary: This is a covariance inequality, not an assertion of
 conditional expectation or probabilistic independence.
*)
Theorem gcd_psd_covariance_cauchy_schwarz :
  forall a b c : R,
    0 <= a ->
    0 <= c ->
    (forall t : R, 0 <= a*t*t + 2*b*t + c) ->
    b*b <= a*c.
Proof.
  intros a b c Ha Hc Hquad.
  destruct (Rle_lt_or_eq_dec 0 a Ha) as [Hapos | Hazero].
  - pose proof (Hquad (-b/a)) as Hmin.
    assert (Hscaled :
      a*(a*(-b/a)*(-b/a) + 2*b*(-b/a) + c) = a*c-b*b).
    { field; lra. }
    assert (Hnonneg :
      0 <= a*(a*(-b/a)*(-b/a) + 2*b*(-b/a) + c)).
    { apply Rmult_le_pos; lra. }
    nra.
  - subst a.
    destruct (Req_EM_T b 0) as [Hbzero | Hbnonzero].
    + subst b; nra.
    + pose proof (Hquad (-(c+1)/(2*b))) as Hbad.
      assert (Hcancellation : 2*b*(-(c+1)/(2*b)) = -(c+1)).
      { field; lra. }
      nra.
Qed.

(** [gcd_psd_covariance_characterization] (theorem).
 Mathematical meaning: For nonnegative marginal variances, an arbitrary
 symmetric two-by-two covariance block is positive semidefinite exactly
 when its cross covariance satisfies b^2 <= a*c.
 Exact proposition: universal nonnegativity of a*t*t+2*b*t+c
 is equivalent to b*b<=a*c, with explicit a>=0, c>=0 premises.
 Premises and side conditions: Both diagonal entries must be
 nonnegative; no strict positivity or invertibility is required.
 Proof/definition method: Necessity reuses the preceding
 Cauchy--Schwarz theorem; sufficiency completes the square after
 multiplying by strictly positive a.
 When a=0 the squared bound implies b=0, so the form is c>=0.
 Library reuse: [gcd_psd_covariance_cauchy_schwarz] and Stdlib
 Ring, Rle_0_sqr, Lra and Psatz. No custom PSD matrix implementation is introduced.
 Boundary: Handles signed and singular covariance algebra, but cannot
 establish the Gaussian characteristic-function factorization or the
 defining event-integral conditional-expectation identity by itself.
*)
Theorem gcd_psd_covariance_characterization :
  forall a b c : R,
    0 <= a ->
    0 <= c ->
    ((forall t : R, 0 <= a*t*t + 2*b*t + c) <-> b*b <= a*c).
Proof.
  intros a b c Ha Hc.
  split.
  - intro Hquad.
    apply (gcd_psd_covariance_cauchy_schwarz a b c Ha Hc Hquad).
  - intros Hbound t.
    destruct (Rle_lt_or_eq_dec 0 a Ha) as [Hapos | Hazero].
    + assert (Hsquared : 0 <= (a*t+b)*(a*t+b)).
      { change (0 <= Rsqr (a*t+b)); apply Rle_0_sqr. }
      assert (Hidentity :
        a*(a*t*t + 2*b*t+c) =
          (a*t+b)*(a*t+b)+(a*c-b*b)) by ring.
      nra.
    + subst a.
      assert (Hbzero : b=0) by nra.
      subst b; nra.
Qed.


(** [gcd_gaussian_uncorrelated_laplace_kernel_factor] (theorem).
 Mathematical meaning: The Gaussian joint Laplace kernel separates into
 its two marginal kernels when the cross-covariance vanishes.
 Exact proposition: for arbitrary real variances a and b, covariance c,
 and transform coordinates t and s, c=0 implies factorization of the
 exponential of the bivariate covariance quadratic form.
 Premises and side conditions: Only c=0 is required for this algebraic
 statement; actual Gaussian probability laws additionally require the
 covariance matrix to be positive semidefinite and appropriate moments.
 Proof/definition method: Substitute the cross-covariance, normalize the
 real quadratic form with the maintained field tactic, and use Stdlib's
 existing exponential addition theorem [exp_plus].
 Library reuse: Stdlib Reals, Field, Lra and [exp_plus]; no hand-written
 exponential function, Gaussian measure, transform or independence axiom.
 Boundary: This checks the factorization of a REAL Laplace kernel,
 not the uniqueness of a probability law from its Laplace transform.
 It does not by itself prove independence of sigma-algebras or the
 universal Gaussian conditional expectation.
*)
Theorem gcd_gaussian_uncorrelated_laplace_kernel_factor :
  forall a b c t s : R,
    c = 0 ->
    exp ((a*t*t + 2*c*t*s + b*s*s)/2) =
    exp (a*t*t/2) * exp (b*s*s/2).
Proof.
  intros a b c t s Hcross.
  subst c.
  replace ((a*t*t + 2*0*t*s + b*s*s)/2)
    with (a*t*t/2 + b*s*s/2) by (field; lra).
  apply exp_plus.
Qed.

(** [gcd_psd_scalar_regression_residual_exists] (theorem).
 Mathematical meaning: A scalar observed variable with variance [a],
 cross covariance [b] with the future score, and future variance [c]
 admits a linear residual-orthogonalizing regression coefficient, even
 when the observed variance [a] vanishes.
 Exact proposition: Every positive-semidefinite quadratic covariance
 block has some [beta] satisfying [b = beta*a] and
 [0 <= c-beta*b]. The first identity is zero residual cross covariance;
 the second is nonnegative variance of the residual.
 Premises and side conditions: Both marginal variances are nonnegative
 and [a*t*t + 2*b*t + c] is nonnegative at every real [t].
 The degenerate case [a=0] forces [b=0], and [beta=0] is admissible.
 Proof/definition method: Reuse the existing, kernel-checked two-by-two covariance
 Cauchy--Schwarz bound, then use [field] and [nra] from Stdlib.
 Library reuse: [gcd_psd_covariance_cauchy_schwarz], Stdlib
 [Rle_lt_or_eq_dec], [field], [lra] and [nra]; no custom inverse.
 This does not reimplement a pseudoinverse, matrix library, Gaussian
 probability measure, or conditional expectation.
 Boundary: This is the exact algebraic residual existence statement
 for one observed coordinate; the implication from joint Gaussianity
 to independence of the residual and the observed sigma-algebra, and
 the event-integral conditional-expectation theorem, are separate.
*)
Theorem gcd_psd_scalar_regression_residual_exists :
  forall a b c : R,
    0 <= a ->
    0 <= c ->
    (forall t : R, 0 <= a*t*t + 2*b*t + c) ->
    exists beta : R,
      b = beta*a /\ 0 <= c - beta*b.
Proof.
  intros a b c Ha Hc Hquad.
  pose proof (gcd_psd_covariance_cauchy_schwarz a b c Ha Hc Hquad)
    as Hcs.
  destruct (Rle_lt_or_eq_dec 0 a Ha) as [Hapos | Hazero].
  - exists (b/a).
    split.
    + field; lra.
    + assert (Hfactor :
        a*(c - (b/a)*b) = a*c - b*b).
      { field; lra. }
      nra.
  - subst a.
    assert (Hbzero : b = 0) by nra.
    subst b.
    exists 0.
    split; nra.
Qed.

(** [gcd_psd_scalar_gaussian_laplace_factor_exists] (theorem).
 Mathematical meaning: Any scalar positive-semidefinite observed/future
 covariance block admits a regression residual whose formal joint
 Gaussian Laplace kernel factors into observed and residual kernels.
 This remains valid if the observed variance is zero and the regression
 coefficient is therefore not identified uniquely.
 Exact checked proposition: for nonnegative variances [a,c] and the
 universally PSD quadratic [a*t*t + 2*b*t + c], there is a coefficient
 [beta] such that [b=beta*a], the residual variance [c-beta*b] is
 nonnegative, and the transformed joint Gaussian exponential kernel
 equals the product of the two marginal exponential kernels for all
 real transform arguments [t,s].
 Proof method: Reuse the previously kernel-proved singular-robust scalar
 regression existence lemma and the Gaussian zero-cross-covariance
 Laplace-factor lemma, reducing the coordinate change to [ring].
 Library reuse: [gcd_psd_scalar_regression_residual_exists],
 [gcd_gaussian_uncorrelated_laplace_kernel_factor], Stdlib Ring.
 Boundary: This is an algebraic moment-generating/Laplace KERNEL
 factorization. It does not prove that a joint Gaussian probability
 measure exists, uniqueness of its Laplace transform, independence of
 generated sigma-algebras, or conditional expectation. Those
 measure-theoretic implications still require separate Rocq theorems.
*)
Theorem gcd_psd_scalar_gaussian_laplace_factor_exists :
  forall a b c : R,
    0 <= a ->
    0 <= c ->
    (forall q : R, 0 <= a*q*q + 2*b*q + c) ->
    exists beta : R,
      b = beta*a /\
      0 <= c - beta*b /\
      forall t s : R,
        exp ((a*(t-beta*s)*(t-beta*s) +
              2*b*(t-beta*s)*s + c*s*s)/2) =
        exp (a*t*t/2) * exp ((c-beta*b)*s*s/2).
Proof.
  intros a b c Ha Hc Hquad.
  destruct
    (gcd_psd_scalar_regression_residual_exists a b c Ha Hc Hquad)
    as [beta [Hcross Hres]].
  exists beta.
  repeat split; try assumption.
  intros t s.
  replace
    ((a*(t-beta*s)*(t-beta*s) +
      2*b*(t-beta*s)*s + c*s*s)/2)
    with ((a*t*t + 2*0*t*s + (c-beta*b)*s*s)/2).
  - apply gcd_gaussian_uncorrelated_laplace_kernel_factor.
    reflexivity.
  - rewrite Hcross.
    ring.
Qed.
