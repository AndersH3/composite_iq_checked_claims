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
Require Import SequentialReport EquicorrelationSpectral EquicorrelationVectors.
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
 nra.
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
