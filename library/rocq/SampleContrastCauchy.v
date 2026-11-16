(** Module: SampleContrastCauchy.v
 Purpose: Prove Cauchy-Schwarz feasibility and bounds for finite weighted
 test-score composites used by six Hoeflin/Ferguson, Towers and Sequential books.
 Mathematical representation: Canonical weighted list folds and centered
 cross-products from the shared finite-sample modules.
 Explicit hypotheses: Each listed weight is nonnegative and the total sample
 mass is strictly positive when normalized covariance inequalities are claimed.
 Library use: Stdlib Reals, Lra, Psatz, Ring, Field, List; existing FiniteSum,
 FiniteConditionalCovariance, ListPoolingAlgebra and FourContrastCovariance.
 Limitations: Deterministic empirical covariance constraints, not Gaussian
 conditioning, binomial independence, confidence coverage or empirical IQ evidence.
 Reproduction: Pinned Rocq 9.2, scripts/compile_rocq.sh and the documentation
 audit. No new recursive sums or probability axioms.
 AI disclosure: Statements, proofs, and comments are ChatGPT-assisted;
 successful kernel compilation, not generated prose, determines proof status.
*)
From Stdlib Require Import Reals Lra Psatz Ring Field List.
Require Import FiniteSum FiniteConditionalCovariance ListPoolingAlgebra
               FourContrastCovariance.
Open Scope R_scope.

(** [sample_centered_bridge] (theorem).
 Mathematical meaning: Existing finite-centered cross products and canonical batch covariance numerators are extensionally the same weighted list sum, even when a sample identifier occurs repeatedly.
 Exact checked proposition: forall (A:Type) (w f g:A->R) (xs:list A), batch_cov_numer w f g xs=finite_centered_cross xs w f g
 Premises and side conditions: Finite lists may contain duplicate occurrences. Each real weight is nonnegative when order is asserted and total exposure is positive for normalized covariance. No Gaussian or sampling assumptions are implicit.
 Proof/definition method: Unfold two transparent interfaces and use the previously proven finite_sum_ext and ring.
 Library reuse: The canonical FiniteSum and ListPoolingAlgebra sums, FiniteConditionalCovariance and FourContrastCovariance; maintained Rocq Stdlib real-order and ring tactics. No parallel estimator or probability axiom.
 Boundary: Exact deterministic weighted finite-sample inference only; no normal-distribution law, stochastic independence, confidence coverage or empirical IQ model has been established.
*)
Theorem sample_centered_bridge :
 forall (A:Type) (w f g:A->R) (xs:list A), batch_cov_numer w f g xs=finite_centered_cross xs w f g.
Proof.
 intros A w f g xs.
 unfold batch_cov_numer, batch_centered_cross,
   finite_centered_cross, finite_weighted_cross,
   finite_weighted_score, finite_weighted_mean,
   finite_weight_mass, batch_mean, batch_total, batch_mass.
 apply finite_sum_ext; intro x; ring.
Qed.

(** [sample_covariance_cauchy_schwarz] (theorem).
 Mathematical meaning: For nonnegative sample weights, squared sample covariance is bounded by the product of the two sample variances; it constrains feasible multi-test covariance estimates.
 Exact checked proposition: forall (A:Type) (w f g:A->R) (xs:list A), (forall x, In x xs -> 0<=w x) -> 0<batch_mass w xs -> batch_covariance w f g xs*batch_covariance w f g xs<=batch_variance w f xs*batch_variance w g xs
 Premises and side conditions: Finite lists may contain duplicate occurrences. Each real weight is nonnegative when order is asserted and total exposure is positive for normalized covariance. No Gaussian or sampling assumptions are implicit.
 Proof/definition method: Reuse finite_centered_cauchy_schwarz, convert its canonical centered numerators, and multiply the bound by the positive squared reciprocal exposure.
 Library reuse: The canonical FiniteSum and ListPoolingAlgebra sums, FiniteConditionalCovariance and FourContrastCovariance; maintained Rocq Stdlib real-order and ring tactics. No parallel estimator or probability axiom.
 Boundary: Exact deterministic weighted finite-sample inference only; no normal-distribution law, stochastic independence, confidence coverage or empirical IQ model has been established.
*)
Theorem sample_covariance_cauchy_schwarz :
 forall (A:Type) (w f g:A->R) (xs:list A), (forall x, In x xs -> 0<=w x) -> 0<batch_mass w xs -> batch_covariance w f g xs*batch_covariance w f g xs<=batch_variance w f xs*batch_variance w g xs.
Proof.
 intros A w f g xs Hw Hm.
 rewrite <- (batch_covariance_self_variance A w f xs).
 rewrite <- (batch_covariance_self_variance A w g xs).
 unfold batch_covariance, Rdiv.
 rewrite !sample_centered_bridge.
 pose proof (finite_centered_cauchy_schwarz A xs w f g Hw) as Hcs.
 assert (Hpos : 0 < / (batch_mass w xs)).
 { apply Rinv_0_lt_compat; exact Hm. }
 assert (Hscaled :
   (/ (batch_mass w xs) * / (batch_mass w xs)) *
       (finite_centered_cross xs w f g * finite_centered_cross xs w f g)
   <= (/ (batch_mass w xs) * / (batch_mass w xs)) *
       (finite_centered_cross xs w f f * finite_centered_cross xs w g g)).
 { apply Rmult_le_compat_l; [nra|exact Hcs]. }
 nra.
Qed.

(** [sample_contrast_cs_test1_test1] (theorem).
 Mathematical meaning: For the first test score contrast and the first test score contrast, a nonnegative-weight finite sample must satisfy the sharp squared covariance-versus-variance feasibility constraint. The coefficients determine a specific multi-test contrast pair relevant to finite composite-score stability checks.
 Exact checked proposition: forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->    batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 0 0) (four_batch_score x1 x2 x3 x4 1 0 0 0) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 0 0) (four_batch_score x1 x2 x3 x4 1 0 0 0) xs    <= batch_variance w (four_batch_score x1 x2 x3 x4 1 0 0 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 0 0 0) xs
 Premises and side conditions: Every listed outcome occurrence has nonnegative weight and the full sample mass is strictly positive. Repeated observations are counted with multiplicity. The two explicit score vectors are not assumed independent, jointly Gaussian or standardized.
 Proof/definition method: Specialize the shared kernel-checked finite-sample covariance Cauchy-Schwarz theorem to both explicit four-test score functions; no reproof or expansion of the weighted sum is performed.
 Library reuse: ListPoolingAlgebra and FourContrastCovariance own the covariance and contrast definitions; SampleContrastCauchy owns the general inequality; Rocq Stdlib real numbers and lists supply all operations.
 Boundary: Exact finite empirical covariance constraint on the named composites, not a separate distributional sampling law, population parameter estimate, chi-square pivot, normal tail or interval-coverage theorem.
*)
Theorem sample_contrast_cs_test1_test1 :
 forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->
   batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 0 0) (four_batch_score x1 x2 x3 x4 1 0 0 0) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 0 0) (four_batch_score x1 x2 x3 x4 1 0 0 0) xs
   <= batch_variance w (four_batch_score x1 x2 x3 x4 1 0 0 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 0 0 0) xs.
Proof.
 intros A w x1 x2 x3 x4 xs Hw Hm.
 exact (sample_covariance_cauchy_schwarz A w
   (four_batch_score x1 x2 x3 x4 1 0 0 0) (four_batch_score x1 x2 x3 x4 1 0 0 0) xs Hw Hm).
Qed.

(** [sample_contrast_cs_test1_test2] (theorem).
 Mathematical meaning: For the first test score contrast and the second test score contrast, a nonnegative-weight finite sample must satisfy the sharp squared covariance-versus-variance feasibility constraint. The coefficients determine a specific multi-test contrast pair relevant to finite composite-score stability checks.
 Exact checked proposition: forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->    batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 0 0) (four_batch_score x1 x2 x3 x4 0 1 0 0) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 0 0) (four_batch_score x1 x2 x3 x4 0 1 0 0) xs    <= batch_variance w (four_batch_score x1 x2 x3 x4 1 0 0 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 0 1 0 0) xs
 Premises and side conditions: Every listed outcome occurrence has nonnegative weight and the full sample mass is strictly positive. Repeated observations are counted with multiplicity. The two explicit score vectors are not assumed independent, jointly Gaussian or standardized.
 Proof/definition method: Specialize the shared kernel-checked finite-sample covariance Cauchy-Schwarz theorem to both explicit four-test score functions; no reproof or expansion of the weighted sum is performed.
 Library reuse: ListPoolingAlgebra and FourContrastCovariance own the covariance and contrast definitions; SampleContrastCauchy owns the general inequality; Rocq Stdlib real numbers and lists supply all operations.
 Boundary: Exact finite empirical covariance constraint on the named composites, not a separate distributional sampling law, population parameter estimate, chi-square pivot, normal tail or interval-coverage theorem.
*)
Theorem sample_contrast_cs_test1_test2 :
 forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->
   batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 0 0) (four_batch_score x1 x2 x3 x4 0 1 0 0) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 0 0) (four_batch_score x1 x2 x3 x4 0 1 0 0) xs
   <= batch_variance w (four_batch_score x1 x2 x3 x4 1 0 0 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 0 1 0 0) xs.
Proof.
 intros A w x1 x2 x3 x4 xs Hw Hm.
 exact (sample_covariance_cauchy_schwarz A w
   (four_batch_score x1 x2 x3 x4 1 0 0 0) (four_batch_score x1 x2 x3 x4 0 1 0 0) xs Hw Hm).
Qed.

(** [sample_contrast_cs_test1_test3] (theorem).
 Mathematical meaning: For the first test score contrast and the third test score contrast, a nonnegative-weight finite sample must satisfy the sharp squared covariance-versus-variance feasibility constraint. The coefficients determine a specific multi-test contrast pair relevant to finite composite-score stability checks.
 Exact checked proposition: forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->    batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 0 0) (four_batch_score x1 x2 x3 x4 0 0 1 0) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 0 0) (four_batch_score x1 x2 x3 x4 0 0 1 0) xs    <= batch_variance w (four_batch_score x1 x2 x3 x4 1 0 0 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 0 0 1 0) xs
 Premises and side conditions: Every listed outcome occurrence has nonnegative weight and the full sample mass is strictly positive. Repeated observations are counted with multiplicity. The two explicit score vectors are not assumed independent, jointly Gaussian or standardized.
 Proof/definition method: Specialize the shared kernel-checked finite-sample covariance Cauchy-Schwarz theorem to both explicit four-test score functions; no reproof or expansion of the weighted sum is performed.
 Library reuse: ListPoolingAlgebra and FourContrastCovariance own the covariance and contrast definitions; SampleContrastCauchy owns the general inequality; Rocq Stdlib real numbers and lists supply all operations.
 Boundary: Exact finite empirical covariance constraint on the named composites, not a separate distributional sampling law, population parameter estimate, chi-square pivot, normal tail or interval-coverage theorem.
*)
Theorem sample_contrast_cs_test1_test3 :
 forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->
   batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 0 0) (four_batch_score x1 x2 x3 x4 0 0 1 0) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 0 0) (four_batch_score x1 x2 x3 x4 0 0 1 0) xs
   <= batch_variance w (four_batch_score x1 x2 x3 x4 1 0 0 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 0 0 1 0) xs.
Proof.
 intros A w x1 x2 x3 x4 xs Hw Hm.
 exact (sample_covariance_cauchy_schwarz A w
   (four_batch_score x1 x2 x3 x4 1 0 0 0) (four_batch_score x1 x2 x3 x4 0 0 1 0) xs Hw Hm).
Qed.

(** [sample_contrast_cs_test1_test4] (theorem).
 Mathematical meaning: For the first test score contrast and the fourth test score contrast, a nonnegative-weight finite sample must satisfy the sharp squared covariance-versus-variance feasibility constraint. The coefficients determine a specific multi-test contrast pair relevant to finite composite-score stability checks.
 Exact checked proposition: forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->    batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 0 0) (four_batch_score x1 x2 x3 x4 0 0 0 1) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 0 0) (four_batch_score x1 x2 x3 x4 0 0 0 1) xs    <= batch_variance w (four_batch_score x1 x2 x3 x4 1 0 0 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 0 0 0 1) xs
 Premises and side conditions: Every listed outcome occurrence has nonnegative weight and the full sample mass is strictly positive. Repeated observations are counted with multiplicity. The two explicit score vectors are not assumed independent, jointly Gaussian or standardized.
 Proof/definition method: Specialize the shared kernel-checked finite-sample covariance Cauchy-Schwarz theorem to both explicit four-test score functions; no reproof or expansion of the weighted sum is performed.
 Library reuse: ListPoolingAlgebra and FourContrastCovariance own the covariance and contrast definitions; SampleContrastCauchy owns the general inequality; Rocq Stdlib real numbers and lists supply all operations.
 Boundary: Exact finite empirical covariance constraint on the named composites, not a separate distributional sampling law, population parameter estimate, chi-square pivot, normal tail or interval-coverage theorem.
*)
Theorem sample_contrast_cs_test1_test4 :
 forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->
   batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 0 0) (four_batch_score x1 x2 x3 x4 0 0 0 1) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 0 0) (four_batch_score x1 x2 x3 x4 0 0 0 1) xs
   <= batch_variance w (four_batch_score x1 x2 x3 x4 1 0 0 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 0 0 0 1) xs.
Proof.
 intros A w x1 x2 x3 x4 xs Hw Hm.
 exact (sample_covariance_cauchy_schwarz A w
   (four_batch_score x1 x2 x3 x4 1 0 0 0) (four_batch_score x1 x2 x3 x4 0 0 0 1) xs Hw Hm).
Qed.

(** [sample_contrast_cs_test1_difference12] (theorem).
 Mathematical meaning: For the first test score contrast and the first minus second test score contrast, a nonnegative-weight finite sample must satisfy the sharp squared covariance-versus-variance feasibility constraint. The coefficients determine a specific multi-test contrast pair relevant to finite composite-score stability checks.
 Exact checked proposition: forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->    batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 0 0) (four_batch_score x1 x2 x3 x4 1 (-1) 0 0) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 0 0) (four_batch_score x1 x2 x3 x4 1 (-1) 0 0) xs    <= batch_variance w (four_batch_score x1 x2 x3 x4 1 0 0 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 (-1) 0 0) xs
 Premises and side conditions: Every listed outcome occurrence has nonnegative weight and the full sample mass is strictly positive. Repeated observations are counted with multiplicity. The two explicit score vectors are not assumed independent, jointly Gaussian or standardized.
 Proof/definition method: Specialize the shared kernel-checked finite-sample covariance Cauchy-Schwarz theorem to both explicit four-test score functions; no reproof or expansion of the weighted sum is performed.
 Library reuse: ListPoolingAlgebra and FourContrastCovariance own the covariance and contrast definitions; SampleContrastCauchy owns the general inequality; Rocq Stdlib real numbers and lists supply all operations.
 Boundary: Exact finite empirical covariance constraint on the named composites, not a separate distributional sampling law, population parameter estimate, chi-square pivot, normal tail or interval-coverage theorem.
*)
Theorem sample_contrast_cs_test1_difference12 :
 forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->
   batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 0 0) (four_batch_score x1 x2 x3 x4 1 (-1) 0 0) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 0 0) (four_batch_score x1 x2 x3 x4 1 (-1) 0 0) xs
   <= batch_variance w (four_batch_score x1 x2 x3 x4 1 0 0 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 (-1) 0 0) xs.
Proof.
 intros A w x1 x2 x3 x4 xs Hw Hm.
 exact (sample_covariance_cauchy_schwarz A w
   (four_batch_score x1 x2 x3 x4 1 0 0 0) (four_batch_score x1 x2 x3 x4 1 (-1) 0 0) xs Hw Hm).
Qed.

(** [sample_contrast_cs_test1_difference13] (theorem).
 Mathematical meaning: For the first test score contrast and the first minus third test score contrast, a nonnegative-weight finite sample must satisfy the sharp squared covariance-versus-variance feasibility constraint. The coefficients determine a specific multi-test contrast pair relevant to finite composite-score stability checks.
 Exact checked proposition: forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->    batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 0 0) (four_batch_score x1 x2 x3 x4 1 0 (-1) 0) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 0 0) (four_batch_score x1 x2 x3 x4 1 0 (-1) 0) xs    <= batch_variance w (four_batch_score x1 x2 x3 x4 1 0 0 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 0 (-1) 0) xs
 Premises and side conditions: Every listed outcome occurrence has nonnegative weight and the full sample mass is strictly positive. Repeated observations are counted with multiplicity. The two explicit score vectors are not assumed independent, jointly Gaussian or standardized.
 Proof/definition method: Specialize the shared kernel-checked finite-sample covariance Cauchy-Schwarz theorem to both explicit four-test score functions; no reproof or expansion of the weighted sum is performed.
 Library reuse: ListPoolingAlgebra and FourContrastCovariance own the covariance and contrast definitions; SampleContrastCauchy owns the general inequality; Rocq Stdlib real numbers and lists supply all operations.
 Boundary: Exact finite empirical covariance constraint on the named composites, not a separate distributional sampling law, population parameter estimate, chi-square pivot, normal tail or interval-coverage theorem.
*)
Theorem sample_contrast_cs_test1_difference13 :
 forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->
   batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 0 0) (four_batch_score x1 x2 x3 x4 1 0 (-1) 0) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 0 0) (four_batch_score x1 x2 x3 x4 1 0 (-1) 0) xs
   <= batch_variance w (four_batch_score x1 x2 x3 x4 1 0 0 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 0 (-1) 0) xs.
Proof.
 intros A w x1 x2 x3 x4 xs Hw Hm.
 exact (sample_covariance_cauchy_schwarz A w
   (four_batch_score x1 x2 x3 x4 1 0 0 0) (four_batch_score x1 x2 x3 x4 1 0 (-1) 0) xs Hw Hm).
Qed.

(** [sample_contrast_cs_test1_difference14] (theorem).
 Mathematical meaning: For the first test score contrast and the first minus fourth test score contrast, a nonnegative-weight finite sample must satisfy the sharp squared covariance-versus-variance feasibility constraint. The coefficients determine a specific multi-test contrast pair relevant to finite composite-score stability checks.
 Exact checked proposition: forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->    batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 0 0) (four_batch_score x1 x2 x3 x4 1 0 0 (-1)) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 0 0) (four_batch_score x1 x2 x3 x4 1 0 0 (-1)) xs    <= batch_variance w (four_batch_score x1 x2 x3 x4 1 0 0 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 0 0 (-1)) xs
 Premises and side conditions: Every listed outcome occurrence has nonnegative weight and the full sample mass is strictly positive. Repeated observations are counted with multiplicity. The two explicit score vectors are not assumed independent, jointly Gaussian or standardized.
 Proof/definition method: Specialize the shared kernel-checked finite-sample covariance Cauchy-Schwarz theorem to both explicit four-test score functions; no reproof or expansion of the weighted sum is performed.
 Library reuse: ListPoolingAlgebra and FourContrastCovariance own the covariance and contrast definitions; SampleContrastCauchy owns the general inequality; Rocq Stdlib real numbers and lists supply all operations.
 Boundary: Exact finite empirical covariance constraint on the named composites, not a separate distributional sampling law, population parameter estimate, chi-square pivot, normal tail or interval-coverage theorem.
*)
Theorem sample_contrast_cs_test1_difference14 :
 forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->
   batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 0 0) (four_batch_score x1 x2 x3 x4 1 0 0 (-1)) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 0 0) (four_batch_score x1 x2 x3 x4 1 0 0 (-1)) xs
   <= batch_variance w (four_batch_score x1 x2 x3 x4 1 0 0 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 0 0 (-1)) xs.
Proof.
 intros A w x1 x2 x3 x4 xs Hw Hm.
 exact (sample_covariance_cauchy_schwarz A w
   (four_batch_score x1 x2 x3 x4 1 0 0 0) (four_batch_score x1 x2 x3 x4 1 0 0 (-1)) xs Hw Hm).
Qed.

(** [sample_contrast_cs_test1_difference23] (theorem).
 Mathematical meaning: For the first test score contrast and the second minus third test score contrast, a nonnegative-weight finite sample must satisfy the sharp squared covariance-versus-variance feasibility constraint. The coefficients determine a specific multi-test contrast pair relevant to finite composite-score stability checks.
 Exact checked proposition: forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->    batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 0 0) (four_batch_score x1 x2 x3 x4 0 1 (-1) 0) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 0 0) (four_batch_score x1 x2 x3 x4 0 1 (-1) 0) xs    <= batch_variance w (four_batch_score x1 x2 x3 x4 1 0 0 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 0 1 (-1) 0) xs
 Premises and side conditions: Every listed outcome occurrence has nonnegative weight and the full sample mass is strictly positive. Repeated observations are counted with multiplicity. The two explicit score vectors are not assumed independent, jointly Gaussian or standardized.
 Proof/definition method: Specialize the shared kernel-checked finite-sample covariance Cauchy-Schwarz theorem to both explicit four-test score functions; no reproof or expansion of the weighted sum is performed.
 Library reuse: ListPoolingAlgebra and FourContrastCovariance own the covariance and contrast definitions; SampleContrastCauchy owns the general inequality; Rocq Stdlib real numbers and lists supply all operations.
 Boundary: Exact finite empirical covariance constraint on the named composites, not a separate distributional sampling law, population parameter estimate, chi-square pivot, normal tail or interval-coverage theorem.
*)
Theorem sample_contrast_cs_test1_difference23 :
 forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->
   batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 0 0) (four_batch_score x1 x2 x3 x4 0 1 (-1) 0) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 0 0) (four_batch_score x1 x2 x3 x4 0 1 (-1) 0) xs
   <= batch_variance w (four_batch_score x1 x2 x3 x4 1 0 0 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 0 1 (-1) 0) xs.
Proof.
 intros A w x1 x2 x3 x4 xs Hw Hm.
 exact (sample_covariance_cauchy_schwarz A w
   (four_batch_score x1 x2 x3 x4 1 0 0 0) (four_batch_score x1 x2 x3 x4 0 1 (-1) 0) xs Hw Hm).
Qed.

(** [sample_contrast_cs_test1_difference24] (theorem).
 Mathematical meaning: For the first test score contrast and the second minus fourth test score contrast, a nonnegative-weight finite sample must satisfy the sharp squared covariance-versus-variance feasibility constraint. The coefficients determine a specific multi-test contrast pair relevant to finite composite-score stability checks.
 Exact checked proposition: forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->    batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 0 0) (four_batch_score x1 x2 x3 x4 0 1 0 (-1)) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 0 0) (four_batch_score x1 x2 x3 x4 0 1 0 (-1)) xs    <= batch_variance w (four_batch_score x1 x2 x3 x4 1 0 0 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 0 1 0 (-1)) xs
 Premises and side conditions: Every listed outcome occurrence has nonnegative weight and the full sample mass is strictly positive. Repeated observations are counted with multiplicity. The two explicit score vectors are not assumed independent, jointly Gaussian or standardized.
 Proof/definition method: Specialize the shared kernel-checked finite-sample covariance Cauchy-Schwarz theorem to both explicit four-test score functions; no reproof or expansion of the weighted sum is performed.
 Library reuse: ListPoolingAlgebra and FourContrastCovariance own the covariance and contrast definitions; SampleContrastCauchy owns the general inequality; Rocq Stdlib real numbers and lists supply all operations.
 Boundary: Exact finite empirical covariance constraint on the named composites, not a separate distributional sampling law, population parameter estimate, chi-square pivot, normal tail or interval-coverage theorem.
*)
Theorem sample_contrast_cs_test1_difference24 :
 forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->
   batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 0 0) (four_batch_score x1 x2 x3 x4 0 1 0 (-1)) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 0 0) (four_batch_score x1 x2 x3 x4 0 1 0 (-1)) xs
   <= batch_variance w (four_batch_score x1 x2 x3 x4 1 0 0 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 0 1 0 (-1)) xs.
Proof.
 intros A w x1 x2 x3 x4 xs Hw Hm.
 exact (sample_covariance_cauchy_schwarz A w
   (four_batch_score x1 x2 x3 x4 1 0 0 0) (four_batch_score x1 x2 x3 x4 0 1 0 (-1)) xs Hw Hm).
Qed.

(** [sample_contrast_cs_test1_difference34] (theorem).
 Mathematical meaning: For the first test score contrast and the third minus fourth test score contrast, a nonnegative-weight finite sample must satisfy the sharp squared covariance-versus-variance feasibility constraint. The coefficients determine a specific multi-test contrast pair relevant to finite composite-score stability checks.
 Exact checked proposition: forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->    batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 0 0) (four_batch_score x1 x2 x3 x4 0 0 1 (-1)) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 0 0) (four_batch_score x1 x2 x3 x4 0 0 1 (-1)) xs    <= batch_variance w (four_batch_score x1 x2 x3 x4 1 0 0 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 0 0 1 (-1)) xs
 Premises and side conditions: Every listed outcome occurrence has nonnegative weight and the full sample mass is strictly positive. Repeated observations are counted with multiplicity. The two explicit score vectors are not assumed independent, jointly Gaussian or standardized.
 Proof/definition method: Specialize the shared kernel-checked finite-sample covariance Cauchy-Schwarz theorem to both explicit four-test score functions; no reproof or expansion of the weighted sum is performed.
 Library reuse: ListPoolingAlgebra and FourContrastCovariance own the covariance and contrast definitions; SampleContrastCauchy owns the general inequality; Rocq Stdlib real numbers and lists supply all operations.
 Boundary: Exact finite empirical covariance constraint on the named composites, not a separate distributional sampling law, population parameter estimate, chi-square pivot, normal tail or interval-coverage theorem.
*)
Theorem sample_contrast_cs_test1_difference34 :
 forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->
   batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 0 0) (four_batch_score x1 x2 x3 x4 0 0 1 (-1)) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 0 0) (four_batch_score x1 x2 x3 x4 0 0 1 (-1)) xs
   <= batch_variance w (four_batch_score x1 x2 x3 x4 1 0 0 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 0 0 1 (-1)) xs.
Proof.
 intros A w x1 x2 x3 x4 xs Hw Hm.
 exact (sample_covariance_cauchy_schwarz A w
   (four_batch_score x1 x2 x3 x4 1 0 0 0) (four_batch_score x1 x2 x3 x4 0 0 1 (-1)) xs Hw Hm).
Qed.

(** [sample_contrast_cs_test1_triple123] (theorem).
 Mathematical meaning: For the first test score contrast and the first three tests score contrast, a nonnegative-weight finite sample must satisfy the sharp squared covariance-versus-variance feasibility constraint. The coefficients determine a specific multi-test contrast pair relevant to finite composite-score stability checks.
 Exact checked proposition: forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->    batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 0 0) (four_batch_score x1 x2 x3 x4 1 1 1 0) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 0 0) (four_batch_score x1 x2 x3 x4 1 1 1 0) xs    <= batch_variance w (four_batch_score x1 x2 x3 x4 1 0 0 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 1 1 0) xs
 Premises and side conditions: Every listed outcome occurrence has nonnegative weight and the full sample mass is strictly positive. Repeated observations are counted with multiplicity. The two explicit score vectors are not assumed independent, jointly Gaussian or standardized.
 Proof/definition method: Specialize the shared kernel-checked finite-sample covariance Cauchy-Schwarz theorem to both explicit four-test score functions; no reproof or expansion of the weighted sum is performed.
 Library reuse: ListPoolingAlgebra and FourContrastCovariance own the covariance and contrast definitions; SampleContrastCauchy owns the general inequality; Rocq Stdlib real numbers and lists supply all operations.
 Boundary: Exact finite empirical covariance constraint on the named composites, not a separate distributional sampling law, population parameter estimate, chi-square pivot, normal tail or interval-coverage theorem.
*)
Theorem sample_contrast_cs_test1_triple123 :
 forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->
   batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 0 0) (four_batch_score x1 x2 x3 x4 1 1 1 0) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 0 0) (four_batch_score x1 x2 x3 x4 1 1 1 0) xs
   <= batch_variance w (four_batch_score x1 x2 x3 x4 1 0 0 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 1 1 0) xs.
Proof.
 intros A w x1 x2 x3 x4 xs Hw Hm.
 exact (sample_covariance_cauchy_schwarz A w
   (four_batch_score x1 x2 x3 x4 1 0 0 0) (four_batch_score x1 x2 x3 x4 1 1 1 0) xs Hw Hm).
Qed.

(** [sample_contrast_cs_test1_triple124] (theorem).
 Mathematical meaning: For the first test score contrast and the tests one, two and four score contrast, a nonnegative-weight finite sample must satisfy the sharp squared covariance-versus-variance feasibility constraint. The coefficients determine a specific multi-test contrast pair relevant to finite composite-score stability checks.
 Exact checked proposition: forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->    batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 0 0) (four_batch_score x1 x2 x3 x4 1 1 0 1) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 0 0) (four_batch_score x1 x2 x3 x4 1 1 0 1) xs    <= batch_variance w (four_batch_score x1 x2 x3 x4 1 0 0 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 1 0 1) xs
 Premises and side conditions: Every listed outcome occurrence has nonnegative weight and the full sample mass is strictly positive. Repeated observations are counted with multiplicity. The two explicit score vectors are not assumed independent, jointly Gaussian or standardized.
 Proof/definition method: Specialize the shared kernel-checked finite-sample covariance Cauchy-Schwarz theorem to both explicit four-test score functions; no reproof or expansion of the weighted sum is performed.
 Library reuse: ListPoolingAlgebra and FourContrastCovariance own the covariance and contrast definitions; SampleContrastCauchy owns the general inequality; Rocq Stdlib real numbers and lists supply all operations.
 Boundary: Exact finite empirical covariance constraint on the named composites, not a separate distributional sampling law, population parameter estimate, chi-square pivot, normal tail or interval-coverage theorem.
*)
Theorem sample_contrast_cs_test1_triple124 :
 forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->
   batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 0 0) (four_batch_score x1 x2 x3 x4 1 1 0 1) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 0 0) (four_batch_score x1 x2 x3 x4 1 1 0 1) xs
   <= batch_variance w (four_batch_score x1 x2 x3 x4 1 0 0 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 1 0 1) xs.
Proof.
 intros A w x1 x2 x3 x4 xs Hw Hm.
 exact (sample_covariance_cauchy_schwarz A w
   (four_batch_score x1 x2 x3 x4 1 0 0 0) (four_batch_score x1 x2 x3 x4 1 1 0 1) xs Hw Hm).
Qed.

(** [sample_contrast_cs_test1_triple134] (theorem).
 Mathematical meaning: For the first test score contrast and the tests one, three and four score contrast, a nonnegative-weight finite sample must satisfy the sharp squared covariance-versus-variance feasibility constraint. The coefficients determine a specific multi-test contrast pair relevant to finite composite-score stability checks.
 Exact checked proposition: forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->    batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 0 0) (four_batch_score x1 x2 x3 x4 1 0 1 1) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 0 0) (four_batch_score x1 x2 x3 x4 1 0 1 1) xs    <= batch_variance w (four_batch_score x1 x2 x3 x4 1 0 0 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 0 1 1) xs
 Premises and side conditions: Every listed outcome occurrence has nonnegative weight and the full sample mass is strictly positive. Repeated observations are counted with multiplicity. The two explicit score vectors are not assumed independent, jointly Gaussian or standardized.
 Proof/definition method: Specialize the shared kernel-checked finite-sample covariance Cauchy-Schwarz theorem to both explicit four-test score functions; no reproof or expansion of the weighted sum is performed.
 Library reuse: ListPoolingAlgebra and FourContrastCovariance own the covariance and contrast definitions; SampleContrastCauchy owns the general inequality; Rocq Stdlib real numbers and lists supply all operations.
 Boundary: Exact finite empirical covariance constraint on the named composites, not a separate distributional sampling law, population parameter estimate, chi-square pivot, normal tail or interval-coverage theorem.
*)
Theorem sample_contrast_cs_test1_triple134 :
 forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->
   batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 0 0) (four_batch_score x1 x2 x3 x4 1 0 1 1) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 0 0) (four_batch_score x1 x2 x3 x4 1 0 1 1) xs
   <= batch_variance w (four_batch_score x1 x2 x3 x4 1 0 0 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 0 1 1) xs.
Proof.
 intros A w x1 x2 x3 x4 xs Hw Hm.
 exact (sample_covariance_cauchy_schwarz A w
   (four_batch_score x1 x2 x3 x4 1 0 0 0) (four_batch_score x1 x2 x3 x4 1 0 1 1) xs Hw Hm).
Qed.

(** [sample_contrast_cs_test1_triple234] (theorem).
 Mathematical meaning: For the first test score contrast and the last three tests score contrast, a nonnegative-weight finite sample must satisfy the sharp squared covariance-versus-variance feasibility constraint. The coefficients determine a specific multi-test contrast pair relevant to finite composite-score stability checks.
 Exact checked proposition: forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->    batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 0 0) (four_batch_score x1 x2 x3 x4 0 1 1 1) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 0 0) (four_batch_score x1 x2 x3 x4 0 1 1 1) xs    <= batch_variance w (four_batch_score x1 x2 x3 x4 1 0 0 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 0 1 1 1) xs
 Premises and side conditions: Every listed outcome occurrence has nonnegative weight and the full sample mass is strictly positive. Repeated observations are counted with multiplicity. The two explicit score vectors are not assumed independent, jointly Gaussian or standardized.
 Proof/definition method: Specialize the shared kernel-checked finite-sample covariance Cauchy-Schwarz theorem to both explicit four-test score functions; no reproof or expansion of the weighted sum is performed.
 Library reuse: ListPoolingAlgebra and FourContrastCovariance own the covariance and contrast definitions; SampleContrastCauchy owns the general inequality; Rocq Stdlib real numbers and lists supply all operations.
 Boundary: Exact finite empirical covariance constraint on the named composites, not a separate distributional sampling law, population parameter estimate, chi-square pivot, normal tail or interval-coverage theorem.
*)
Theorem sample_contrast_cs_test1_triple234 :
 forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->
   batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 0 0) (four_batch_score x1 x2 x3 x4 0 1 1 1) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 0 0) (four_batch_score x1 x2 x3 x4 0 1 1 1) xs
   <= batch_variance w (four_batch_score x1 x2 x3 x4 1 0 0 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 0 1 1 1) xs.
Proof.
 intros A w x1 x2 x3 x4 xs Hw Hm.
 exact (sample_covariance_cauchy_schwarz A w
   (four_batch_score x1 x2 x3 x4 1 0 0 0) (four_batch_score x1 x2 x3 x4 0 1 1 1) xs Hw Hm).
Qed.

(** [sample_contrast_cs_test1_allfour] (theorem).
 Mathematical meaning: For the first test score contrast and the all four tests score contrast, a nonnegative-weight finite sample must satisfy the sharp squared covariance-versus-variance feasibility constraint. The coefficients determine a specific multi-test contrast pair relevant to finite composite-score stability checks.
 Exact checked proposition: forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->    batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 0 0) (four_batch_score x1 x2 x3 x4 1 1 1 1) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 0 0) (four_batch_score x1 x2 x3 x4 1 1 1 1) xs    <= batch_variance w (four_batch_score x1 x2 x3 x4 1 0 0 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 1 1 1) xs
 Premises and side conditions: Every listed outcome occurrence has nonnegative weight and the full sample mass is strictly positive. Repeated observations are counted with multiplicity. The two explicit score vectors are not assumed independent, jointly Gaussian or standardized.
 Proof/definition method: Specialize the shared kernel-checked finite-sample covariance Cauchy-Schwarz theorem to both explicit four-test score functions; no reproof or expansion of the weighted sum is performed.
 Library reuse: ListPoolingAlgebra and FourContrastCovariance own the covariance and contrast definitions; SampleContrastCauchy owns the general inequality; Rocq Stdlib real numbers and lists supply all operations.
 Boundary: Exact finite empirical covariance constraint on the named composites, not a separate distributional sampling law, population parameter estimate, chi-square pivot, normal tail or interval-coverage theorem.
*)
Theorem sample_contrast_cs_test1_allfour :
 forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->
   batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 0 0) (four_batch_score x1 x2 x3 x4 1 1 1 1) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 0 0) (four_batch_score x1 x2 x3 x4 1 1 1 1) xs
   <= batch_variance w (four_batch_score x1 x2 x3 x4 1 0 0 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 1 1 1) xs.
Proof.
 intros A w x1 x2 x3 x4 xs Hw Hm.
 exact (sample_covariance_cauchy_schwarz A w
   (four_batch_score x1 x2 x3 x4 1 0 0 0) (four_batch_score x1 x2 x3 x4 1 1 1 1) xs Hw Hm).
Qed.

(** [sample_contrast_cs_test1_balanced12v34] (theorem).
 Mathematical meaning: For the first test score contrast and the difference between the two pairs score contrast, a nonnegative-weight finite sample must satisfy the sharp squared covariance-versus-variance feasibility constraint. The coefficients determine a specific multi-test contrast pair relevant to finite composite-score stability checks.
 Exact checked proposition: forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->    batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 0 0) (four_batch_score x1 x2 x3 x4 1 1 (-1) (-1)) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 0 0) (four_batch_score x1 x2 x3 x4 1 1 (-1) (-1)) xs    <= batch_variance w (four_batch_score x1 x2 x3 x4 1 0 0 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 1 (-1) (-1)) xs
 Premises and side conditions: Every listed outcome occurrence has nonnegative weight and the full sample mass is strictly positive. Repeated observations are counted with multiplicity. The two explicit score vectors are not assumed independent, jointly Gaussian or standardized.
 Proof/definition method: Specialize the shared kernel-checked finite-sample covariance Cauchy-Schwarz theorem to both explicit four-test score functions; no reproof or expansion of the weighted sum is performed.
 Library reuse: ListPoolingAlgebra and FourContrastCovariance own the covariance and contrast definitions; SampleContrastCauchy owns the general inequality; Rocq Stdlib real numbers and lists supply all operations.
 Boundary: Exact finite empirical covariance constraint on the named composites, not a separate distributional sampling law, population parameter estimate, chi-square pivot, normal tail or interval-coverage theorem.
*)
Theorem sample_contrast_cs_test1_balanced12v34 :
 forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->
   batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 0 0) (four_batch_score x1 x2 x3 x4 1 1 (-1) (-1)) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 0 0) (four_batch_score x1 x2 x3 x4 1 1 (-1) (-1)) xs
   <= batch_variance w (four_batch_score x1 x2 x3 x4 1 0 0 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 1 (-1) (-1)) xs.
Proof.
 intros A w x1 x2 x3 x4 xs Hw Hm.
 exact (sample_covariance_cauchy_schwarz A w
   (four_batch_score x1 x2 x3 x4 1 0 0 0) (four_batch_score x1 x2 x3 x4 1 1 (-1) (-1)) xs Hw Hm).
Qed.

(** [sample_contrast_cs_test2_test2] (theorem).
 Mathematical meaning: For the second test score contrast and the second test score contrast, a nonnegative-weight finite sample must satisfy the sharp squared covariance-versus-variance feasibility constraint. The coefficients determine a specific multi-test contrast pair relevant to finite composite-score stability checks.
 Exact checked proposition: forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->    batch_covariance w (four_batch_score x1 x2 x3 x4 0 1 0 0) (four_batch_score x1 x2 x3 x4 0 1 0 0) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 0 1 0 0) (four_batch_score x1 x2 x3 x4 0 1 0 0) xs    <= batch_variance w (four_batch_score x1 x2 x3 x4 0 1 0 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 0 1 0 0) xs
 Premises and side conditions: Every listed outcome occurrence has nonnegative weight and the full sample mass is strictly positive. Repeated observations are counted with multiplicity. The two explicit score vectors are not assumed independent, jointly Gaussian or standardized.
 Proof/definition method: Specialize the shared kernel-checked finite-sample covariance Cauchy-Schwarz theorem to both explicit four-test score functions; no reproof or expansion of the weighted sum is performed.
 Library reuse: ListPoolingAlgebra and FourContrastCovariance own the covariance and contrast definitions; SampleContrastCauchy owns the general inequality; Rocq Stdlib real numbers and lists supply all operations.
 Boundary: Exact finite empirical covariance constraint on the named composites, not a separate distributional sampling law, population parameter estimate, chi-square pivot, normal tail or interval-coverage theorem.
*)
Theorem sample_contrast_cs_test2_test2 :
 forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->
   batch_covariance w (four_batch_score x1 x2 x3 x4 0 1 0 0) (four_batch_score x1 x2 x3 x4 0 1 0 0) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 0 1 0 0) (four_batch_score x1 x2 x3 x4 0 1 0 0) xs
   <= batch_variance w (four_batch_score x1 x2 x3 x4 0 1 0 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 0 1 0 0) xs.
Proof.
 intros A w x1 x2 x3 x4 xs Hw Hm.
 exact (sample_covariance_cauchy_schwarz A w
   (four_batch_score x1 x2 x3 x4 0 1 0 0) (four_batch_score x1 x2 x3 x4 0 1 0 0) xs Hw Hm).
Qed.

(** [sample_contrast_cs_test2_test3] (theorem).
 Mathematical meaning: For the second test score contrast and the third test score contrast, a nonnegative-weight finite sample must satisfy the sharp squared covariance-versus-variance feasibility constraint. The coefficients determine a specific multi-test contrast pair relevant to finite composite-score stability checks.
 Exact checked proposition: forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->    batch_covariance w (four_batch_score x1 x2 x3 x4 0 1 0 0) (four_batch_score x1 x2 x3 x4 0 0 1 0) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 0 1 0 0) (four_batch_score x1 x2 x3 x4 0 0 1 0) xs    <= batch_variance w (four_batch_score x1 x2 x3 x4 0 1 0 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 0 0 1 0) xs
 Premises and side conditions: Every listed outcome occurrence has nonnegative weight and the full sample mass is strictly positive. Repeated observations are counted with multiplicity. The two explicit score vectors are not assumed independent, jointly Gaussian or standardized.
 Proof/definition method: Specialize the shared kernel-checked finite-sample covariance Cauchy-Schwarz theorem to both explicit four-test score functions; no reproof or expansion of the weighted sum is performed.
 Library reuse: ListPoolingAlgebra and FourContrastCovariance own the covariance and contrast definitions; SampleContrastCauchy owns the general inequality; Rocq Stdlib real numbers and lists supply all operations.
 Boundary: Exact finite empirical covariance constraint on the named composites, not a separate distributional sampling law, population parameter estimate, chi-square pivot, normal tail or interval-coverage theorem.
*)
Theorem sample_contrast_cs_test2_test3 :
 forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->
   batch_covariance w (four_batch_score x1 x2 x3 x4 0 1 0 0) (four_batch_score x1 x2 x3 x4 0 0 1 0) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 0 1 0 0) (four_batch_score x1 x2 x3 x4 0 0 1 0) xs
   <= batch_variance w (four_batch_score x1 x2 x3 x4 0 1 0 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 0 0 1 0) xs.
Proof.
 intros A w x1 x2 x3 x4 xs Hw Hm.
 exact (sample_covariance_cauchy_schwarz A w
   (four_batch_score x1 x2 x3 x4 0 1 0 0) (four_batch_score x1 x2 x3 x4 0 0 1 0) xs Hw Hm).
Qed.

(** [sample_contrast_cs_test2_test4] (theorem).
 Mathematical meaning: For the second test score contrast and the fourth test score contrast, a nonnegative-weight finite sample must satisfy the sharp squared covariance-versus-variance feasibility constraint. The coefficients determine a specific multi-test contrast pair relevant to finite composite-score stability checks.
 Exact checked proposition: forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->    batch_covariance w (four_batch_score x1 x2 x3 x4 0 1 0 0) (four_batch_score x1 x2 x3 x4 0 0 0 1) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 0 1 0 0) (four_batch_score x1 x2 x3 x4 0 0 0 1) xs    <= batch_variance w (four_batch_score x1 x2 x3 x4 0 1 0 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 0 0 0 1) xs
 Premises and side conditions: Every listed outcome occurrence has nonnegative weight and the full sample mass is strictly positive. Repeated observations are counted with multiplicity. The two explicit score vectors are not assumed independent, jointly Gaussian or standardized.
 Proof/definition method: Specialize the shared kernel-checked finite-sample covariance Cauchy-Schwarz theorem to both explicit four-test score functions; no reproof or expansion of the weighted sum is performed.
 Library reuse: ListPoolingAlgebra and FourContrastCovariance own the covariance and contrast definitions; SampleContrastCauchy owns the general inequality; Rocq Stdlib real numbers and lists supply all operations.
 Boundary: Exact finite empirical covariance constraint on the named composites, not a separate distributional sampling law, population parameter estimate, chi-square pivot, normal tail or interval-coverage theorem.
*)
Theorem sample_contrast_cs_test2_test4 :
 forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->
   batch_covariance w (four_batch_score x1 x2 x3 x4 0 1 0 0) (four_batch_score x1 x2 x3 x4 0 0 0 1) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 0 1 0 0) (four_batch_score x1 x2 x3 x4 0 0 0 1) xs
   <= batch_variance w (four_batch_score x1 x2 x3 x4 0 1 0 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 0 0 0 1) xs.
Proof.
 intros A w x1 x2 x3 x4 xs Hw Hm.
 exact (sample_covariance_cauchy_schwarz A w
   (four_batch_score x1 x2 x3 x4 0 1 0 0) (four_batch_score x1 x2 x3 x4 0 0 0 1) xs Hw Hm).
Qed.

(** [sample_contrast_cs_test2_difference12] (theorem).
 Mathematical meaning: For the second test score contrast and the first minus second test score contrast, a nonnegative-weight finite sample must satisfy the sharp squared covariance-versus-variance feasibility constraint. The coefficients determine a specific multi-test contrast pair relevant to finite composite-score stability checks.
 Exact checked proposition: forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->    batch_covariance w (four_batch_score x1 x2 x3 x4 0 1 0 0) (four_batch_score x1 x2 x3 x4 1 (-1) 0 0) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 0 1 0 0) (four_batch_score x1 x2 x3 x4 1 (-1) 0 0) xs    <= batch_variance w (four_batch_score x1 x2 x3 x4 0 1 0 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 (-1) 0 0) xs
 Premises and side conditions: Every listed outcome occurrence has nonnegative weight and the full sample mass is strictly positive. Repeated observations are counted with multiplicity. The two explicit score vectors are not assumed independent, jointly Gaussian or standardized.
 Proof/definition method: Specialize the shared kernel-checked finite-sample covariance Cauchy-Schwarz theorem to both explicit four-test score functions; no reproof or expansion of the weighted sum is performed.
 Library reuse: ListPoolingAlgebra and FourContrastCovariance own the covariance and contrast definitions; SampleContrastCauchy owns the general inequality; Rocq Stdlib real numbers and lists supply all operations.
 Boundary: Exact finite empirical covariance constraint on the named composites, not a separate distributional sampling law, population parameter estimate, chi-square pivot, normal tail or interval-coverage theorem.
*)
Theorem sample_contrast_cs_test2_difference12 :
 forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->
   batch_covariance w (four_batch_score x1 x2 x3 x4 0 1 0 0) (four_batch_score x1 x2 x3 x4 1 (-1) 0 0) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 0 1 0 0) (four_batch_score x1 x2 x3 x4 1 (-1) 0 0) xs
   <= batch_variance w (four_batch_score x1 x2 x3 x4 0 1 0 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 (-1) 0 0) xs.
Proof.
 intros A w x1 x2 x3 x4 xs Hw Hm.
 exact (sample_covariance_cauchy_schwarz A w
   (four_batch_score x1 x2 x3 x4 0 1 0 0) (four_batch_score x1 x2 x3 x4 1 (-1) 0 0) xs Hw Hm).
Qed.

(** [sample_contrast_cs_test2_difference13] (theorem).
 Mathematical meaning: For the second test score contrast and the first minus third test score contrast, a nonnegative-weight finite sample must satisfy the sharp squared covariance-versus-variance feasibility constraint. The coefficients determine a specific multi-test contrast pair relevant to finite composite-score stability checks.
 Exact checked proposition: forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->    batch_covariance w (four_batch_score x1 x2 x3 x4 0 1 0 0) (four_batch_score x1 x2 x3 x4 1 0 (-1) 0) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 0 1 0 0) (four_batch_score x1 x2 x3 x4 1 0 (-1) 0) xs    <= batch_variance w (four_batch_score x1 x2 x3 x4 0 1 0 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 0 (-1) 0) xs
 Premises and side conditions: Every listed outcome occurrence has nonnegative weight and the full sample mass is strictly positive. Repeated observations are counted with multiplicity. The two explicit score vectors are not assumed independent, jointly Gaussian or standardized.
 Proof/definition method: Specialize the shared kernel-checked finite-sample covariance Cauchy-Schwarz theorem to both explicit four-test score functions; no reproof or expansion of the weighted sum is performed.
 Library reuse: ListPoolingAlgebra and FourContrastCovariance own the covariance and contrast definitions; SampleContrastCauchy owns the general inequality; Rocq Stdlib real numbers and lists supply all operations.
 Boundary: Exact finite empirical covariance constraint on the named composites, not a separate distributional sampling law, population parameter estimate, chi-square pivot, normal tail or interval-coverage theorem.
*)
Theorem sample_contrast_cs_test2_difference13 :
 forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->
   batch_covariance w (four_batch_score x1 x2 x3 x4 0 1 0 0) (four_batch_score x1 x2 x3 x4 1 0 (-1) 0) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 0 1 0 0) (four_batch_score x1 x2 x3 x4 1 0 (-1) 0) xs
   <= batch_variance w (four_batch_score x1 x2 x3 x4 0 1 0 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 0 (-1) 0) xs.
Proof.
 intros A w x1 x2 x3 x4 xs Hw Hm.
 exact (sample_covariance_cauchy_schwarz A w
   (four_batch_score x1 x2 x3 x4 0 1 0 0) (four_batch_score x1 x2 x3 x4 1 0 (-1) 0) xs Hw Hm).
Qed.

(** [sample_contrast_cs_test2_difference14] (theorem).
 Mathematical meaning: For the second test score contrast and the first minus fourth test score contrast, a nonnegative-weight finite sample must satisfy the sharp squared covariance-versus-variance feasibility constraint. The coefficients determine a specific multi-test contrast pair relevant to finite composite-score stability checks.
 Exact checked proposition: forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->    batch_covariance w (four_batch_score x1 x2 x3 x4 0 1 0 0) (four_batch_score x1 x2 x3 x4 1 0 0 (-1)) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 0 1 0 0) (four_batch_score x1 x2 x3 x4 1 0 0 (-1)) xs    <= batch_variance w (four_batch_score x1 x2 x3 x4 0 1 0 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 0 0 (-1)) xs
 Premises and side conditions: Every listed outcome occurrence has nonnegative weight and the full sample mass is strictly positive. Repeated observations are counted with multiplicity. The two explicit score vectors are not assumed independent, jointly Gaussian or standardized.
 Proof/definition method: Specialize the shared kernel-checked finite-sample covariance Cauchy-Schwarz theorem to both explicit four-test score functions; no reproof or expansion of the weighted sum is performed.
 Library reuse: ListPoolingAlgebra and FourContrastCovariance own the covariance and contrast definitions; SampleContrastCauchy owns the general inequality; Rocq Stdlib real numbers and lists supply all operations.
 Boundary: Exact finite empirical covariance constraint on the named composites, not a separate distributional sampling law, population parameter estimate, chi-square pivot, normal tail or interval-coverage theorem.
*)
Theorem sample_contrast_cs_test2_difference14 :
 forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->
   batch_covariance w (four_batch_score x1 x2 x3 x4 0 1 0 0) (four_batch_score x1 x2 x3 x4 1 0 0 (-1)) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 0 1 0 0) (four_batch_score x1 x2 x3 x4 1 0 0 (-1)) xs
   <= batch_variance w (four_batch_score x1 x2 x3 x4 0 1 0 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 0 0 (-1)) xs.
Proof.
 intros A w x1 x2 x3 x4 xs Hw Hm.
 exact (sample_covariance_cauchy_schwarz A w
   (four_batch_score x1 x2 x3 x4 0 1 0 0) (four_batch_score x1 x2 x3 x4 1 0 0 (-1)) xs Hw Hm).
Qed.

(** [sample_contrast_cs_test2_difference23] (theorem).
 Mathematical meaning: For the second test score contrast and the second minus third test score contrast, a nonnegative-weight finite sample must satisfy the sharp squared covariance-versus-variance feasibility constraint. The coefficients determine a specific multi-test contrast pair relevant to finite composite-score stability checks.
 Exact checked proposition: forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->    batch_covariance w (four_batch_score x1 x2 x3 x4 0 1 0 0) (four_batch_score x1 x2 x3 x4 0 1 (-1) 0) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 0 1 0 0) (four_batch_score x1 x2 x3 x4 0 1 (-1) 0) xs    <= batch_variance w (four_batch_score x1 x2 x3 x4 0 1 0 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 0 1 (-1) 0) xs
 Premises and side conditions: Every listed outcome occurrence has nonnegative weight and the full sample mass is strictly positive. Repeated observations are counted with multiplicity. The two explicit score vectors are not assumed independent, jointly Gaussian or standardized.
 Proof/definition method: Specialize the shared kernel-checked finite-sample covariance Cauchy-Schwarz theorem to both explicit four-test score functions; no reproof or expansion of the weighted sum is performed.
 Library reuse: ListPoolingAlgebra and FourContrastCovariance own the covariance and contrast definitions; SampleContrastCauchy owns the general inequality; Rocq Stdlib real numbers and lists supply all operations.
 Boundary: Exact finite empirical covariance constraint on the named composites, not a separate distributional sampling law, population parameter estimate, chi-square pivot, normal tail or interval-coverage theorem.
*)
Theorem sample_contrast_cs_test2_difference23 :
 forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->
   batch_covariance w (four_batch_score x1 x2 x3 x4 0 1 0 0) (four_batch_score x1 x2 x3 x4 0 1 (-1) 0) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 0 1 0 0) (four_batch_score x1 x2 x3 x4 0 1 (-1) 0) xs
   <= batch_variance w (four_batch_score x1 x2 x3 x4 0 1 0 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 0 1 (-1) 0) xs.
Proof.
 intros A w x1 x2 x3 x4 xs Hw Hm.
 exact (sample_covariance_cauchy_schwarz A w
   (four_batch_score x1 x2 x3 x4 0 1 0 0) (four_batch_score x1 x2 x3 x4 0 1 (-1) 0) xs Hw Hm).
Qed.

(** [sample_contrast_cs_test2_difference24] (theorem).
 Mathematical meaning: For the second test score contrast and the second minus fourth test score contrast, a nonnegative-weight finite sample must satisfy the sharp squared covariance-versus-variance feasibility constraint. The coefficients determine a specific multi-test contrast pair relevant to finite composite-score stability checks.
 Exact checked proposition: forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->    batch_covariance w (four_batch_score x1 x2 x3 x4 0 1 0 0) (four_batch_score x1 x2 x3 x4 0 1 0 (-1)) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 0 1 0 0) (four_batch_score x1 x2 x3 x4 0 1 0 (-1)) xs    <= batch_variance w (four_batch_score x1 x2 x3 x4 0 1 0 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 0 1 0 (-1)) xs
 Premises and side conditions: Every listed outcome occurrence has nonnegative weight and the full sample mass is strictly positive. Repeated observations are counted with multiplicity. The two explicit score vectors are not assumed independent, jointly Gaussian or standardized.
 Proof/definition method: Specialize the shared kernel-checked finite-sample covariance Cauchy-Schwarz theorem to both explicit four-test score functions; no reproof or expansion of the weighted sum is performed.
 Library reuse: ListPoolingAlgebra and FourContrastCovariance own the covariance and contrast definitions; SampleContrastCauchy owns the general inequality; Rocq Stdlib real numbers and lists supply all operations.
 Boundary: Exact finite empirical covariance constraint on the named composites, not a separate distributional sampling law, population parameter estimate, chi-square pivot, normal tail or interval-coverage theorem.
*)
Theorem sample_contrast_cs_test2_difference24 :
 forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->
   batch_covariance w (four_batch_score x1 x2 x3 x4 0 1 0 0) (four_batch_score x1 x2 x3 x4 0 1 0 (-1)) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 0 1 0 0) (four_batch_score x1 x2 x3 x4 0 1 0 (-1)) xs
   <= batch_variance w (four_batch_score x1 x2 x3 x4 0 1 0 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 0 1 0 (-1)) xs.
Proof.
 intros A w x1 x2 x3 x4 xs Hw Hm.
 exact (sample_covariance_cauchy_schwarz A w
   (four_batch_score x1 x2 x3 x4 0 1 0 0) (four_batch_score x1 x2 x3 x4 0 1 0 (-1)) xs Hw Hm).
Qed.

(** [sample_contrast_cs_test2_difference34] (theorem).
 Mathematical meaning: For the second test score contrast and the third minus fourth test score contrast, a nonnegative-weight finite sample must satisfy the sharp squared covariance-versus-variance feasibility constraint. The coefficients determine a specific multi-test contrast pair relevant to finite composite-score stability checks.
 Exact checked proposition: forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->    batch_covariance w (four_batch_score x1 x2 x3 x4 0 1 0 0) (four_batch_score x1 x2 x3 x4 0 0 1 (-1)) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 0 1 0 0) (four_batch_score x1 x2 x3 x4 0 0 1 (-1)) xs    <= batch_variance w (four_batch_score x1 x2 x3 x4 0 1 0 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 0 0 1 (-1)) xs
 Premises and side conditions: Every listed outcome occurrence has nonnegative weight and the full sample mass is strictly positive. Repeated observations are counted with multiplicity. The two explicit score vectors are not assumed independent, jointly Gaussian or standardized.
 Proof/definition method: Specialize the shared kernel-checked finite-sample covariance Cauchy-Schwarz theorem to both explicit four-test score functions; no reproof or expansion of the weighted sum is performed.
 Library reuse: ListPoolingAlgebra and FourContrastCovariance own the covariance and contrast definitions; SampleContrastCauchy owns the general inequality; Rocq Stdlib real numbers and lists supply all operations.
 Boundary: Exact finite empirical covariance constraint on the named composites, not a separate distributional sampling law, population parameter estimate, chi-square pivot, normal tail or interval-coverage theorem.
*)
Theorem sample_contrast_cs_test2_difference34 :
 forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->
   batch_covariance w (four_batch_score x1 x2 x3 x4 0 1 0 0) (four_batch_score x1 x2 x3 x4 0 0 1 (-1)) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 0 1 0 0) (four_batch_score x1 x2 x3 x4 0 0 1 (-1)) xs
   <= batch_variance w (four_batch_score x1 x2 x3 x4 0 1 0 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 0 0 1 (-1)) xs.
Proof.
 intros A w x1 x2 x3 x4 xs Hw Hm.
 exact (sample_covariance_cauchy_schwarz A w
   (four_batch_score x1 x2 x3 x4 0 1 0 0) (four_batch_score x1 x2 x3 x4 0 0 1 (-1)) xs Hw Hm).
Qed.

(** [sample_contrast_cs_test2_triple123] (theorem).
 Mathematical meaning: For the second test score contrast and the first three tests score contrast, a nonnegative-weight finite sample must satisfy the sharp squared covariance-versus-variance feasibility constraint. The coefficients determine a specific multi-test contrast pair relevant to finite composite-score stability checks.
 Exact checked proposition: forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->    batch_covariance w (four_batch_score x1 x2 x3 x4 0 1 0 0) (four_batch_score x1 x2 x3 x4 1 1 1 0) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 0 1 0 0) (four_batch_score x1 x2 x3 x4 1 1 1 0) xs    <= batch_variance w (four_batch_score x1 x2 x3 x4 0 1 0 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 1 1 0) xs
 Premises and side conditions: Every listed outcome occurrence has nonnegative weight and the full sample mass is strictly positive. Repeated observations are counted with multiplicity. The two explicit score vectors are not assumed independent, jointly Gaussian or standardized.
 Proof/definition method: Specialize the shared kernel-checked finite-sample covariance Cauchy-Schwarz theorem to both explicit four-test score functions; no reproof or expansion of the weighted sum is performed.
 Library reuse: ListPoolingAlgebra and FourContrastCovariance own the covariance and contrast definitions; SampleContrastCauchy owns the general inequality; Rocq Stdlib real numbers and lists supply all operations.
 Boundary: Exact finite empirical covariance constraint on the named composites, not a separate distributional sampling law, population parameter estimate, chi-square pivot, normal tail or interval-coverage theorem.
*)
Theorem sample_contrast_cs_test2_triple123 :
 forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->
   batch_covariance w (four_batch_score x1 x2 x3 x4 0 1 0 0) (four_batch_score x1 x2 x3 x4 1 1 1 0) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 0 1 0 0) (four_batch_score x1 x2 x3 x4 1 1 1 0) xs
   <= batch_variance w (four_batch_score x1 x2 x3 x4 0 1 0 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 1 1 0) xs.
Proof.
 intros A w x1 x2 x3 x4 xs Hw Hm.
 exact (sample_covariance_cauchy_schwarz A w
   (four_batch_score x1 x2 x3 x4 0 1 0 0) (four_batch_score x1 x2 x3 x4 1 1 1 0) xs Hw Hm).
Qed.

(** [sample_contrast_cs_test2_triple124] (theorem).
 Mathematical meaning: For the second test score contrast and the tests one, two and four score contrast, a nonnegative-weight finite sample must satisfy the sharp squared covariance-versus-variance feasibility constraint. The coefficients determine a specific multi-test contrast pair relevant to finite composite-score stability checks.
 Exact checked proposition: forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->    batch_covariance w (four_batch_score x1 x2 x3 x4 0 1 0 0) (four_batch_score x1 x2 x3 x4 1 1 0 1) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 0 1 0 0) (four_batch_score x1 x2 x3 x4 1 1 0 1) xs    <= batch_variance w (four_batch_score x1 x2 x3 x4 0 1 0 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 1 0 1) xs
 Premises and side conditions: Every listed outcome occurrence has nonnegative weight and the full sample mass is strictly positive. Repeated observations are counted with multiplicity. The two explicit score vectors are not assumed independent, jointly Gaussian or standardized.
 Proof/definition method: Specialize the shared kernel-checked finite-sample covariance Cauchy-Schwarz theorem to both explicit four-test score functions; no reproof or expansion of the weighted sum is performed.
 Library reuse: ListPoolingAlgebra and FourContrastCovariance own the covariance and contrast definitions; SampleContrastCauchy owns the general inequality; Rocq Stdlib real numbers and lists supply all operations.
 Boundary: Exact finite empirical covariance constraint on the named composites, not a separate distributional sampling law, population parameter estimate, chi-square pivot, normal tail or interval-coverage theorem.
*)
Theorem sample_contrast_cs_test2_triple124 :
 forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->
   batch_covariance w (four_batch_score x1 x2 x3 x4 0 1 0 0) (four_batch_score x1 x2 x3 x4 1 1 0 1) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 0 1 0 0) (four_batch_score x1 x2 x3 x4 1 1 0 1) xs
   <= batch_variance w (four_batch_score x1 x2 x3 x4 0 1 0 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 1 0 1) xs.
Proof.
 intros A w x1 x2 x3 x4 xs Hw Hm.
 exact (sample_covariance_cauchy_schwarz A w
   (four_batch_score x1 x2 x3 x4 0 1 0 0) (four_batch_score x1 x2 x3 x4 1 1 0 1) xs Hw Hm).
Qed.

(** [sample_contrast_cs_test2_triple134] (theorem).
 Mathematical meaning: For the second test score contrast and the tests one, three and four score contrast, a nonnegative-weight finite sample must satisfy the sharp squared covariance-versus-variance feasibility constraint. The coefficients determine a specific multi-test contrast pair relevant to finite composite-score stability checks.
 Exact checked proposition: forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->    batch_covariance w (four_batch_score x1 x2 x3 x4 0 1 0 0) (four_batch_score x1 x2 x3 x4 1 0 1 1) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 0 1 0 0) (four_batch_score x1 x2 x3 x4 1 0 1 1) xs    <= batch_variance w (four_batch_score x1 x2 x3 x4 0 1 0 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 0 1 1) xs
 Premises and side conditions: Every listed outcome occurrence has nonnegative weight and the full sample mass is strictly positive. Repeated observations are counted with multiplicity. The two explicit score vectors are not assumed independent, jointly Gaussian or standardized.
 Proof/definition method: Specialize the shared kernel-checked finite-sample covariance Cauchy-Schwarz theorem to both explicit four-test score functions; no reproof or expansion of the weighted sum is performed.
 Library reuse: ListPoolingAlgebra and FourContrastCovariance own the covariance and contrast definitions; SampleContrastCauchy owns the general inequality; Rocq Stdlib real numbers and lists supply all operations.
 Boundary: Exact finite empirical covariance constraint on the named composites, not a separate distributional sampling law, population parameter estimate, chi-square pivot, normal tail or interval-coverage theorem.
*)
Theorem sample_contrast_cs_test2_triple134 :
 forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->
   batch_covariance w (four_batch_score x1 x2 x3 x4 0 1 0 0) (four_batch_score x1 x2 x3 x4 1 0 1 1) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 0 1 0 0) (four_batch_score x1 x2 x3 x4 1 0 1 1) xs
   <= batch_variance w (four_batch_score x1 x2 x3 x4 0 1 0 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 0 1 1) xs.
Proof.
 intros A w x1 x2 x3 x4 xs Hw Hm.
 exact (sample_covariance_cauchy_schwarz A w
   (four_batch_score x1 x2 x3 x4 0 1 0 0) (four_batch_score x1 x2 x3 x4 1 0 1 1) xs Hw Hm).
Qed.

(** [sample_contrast_cs_test2_triple234] (theorem).
 Mathematical meaning: For the second test score contrast and the last three tests score contrast, a nonnegative-weight finite sample must satisfy the sharp squared covariance-versus-variance feasibility constraint. The coefficients determine a specific multi-test contrast pair relevant to finite composite-score stability checks.
 Exact checked proposition: forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->    batch_covariance w (four_batch_score x1 x2 x3 x4 0 1 0 0) (four_batch_score x1 x2 x3 x4 0 1 1 1) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 0 1 0 0) (four_batch_score x1 x2 x3 x4 0 1 1 1) xs    <= batch_variance w (four_batch_score x1 x2 x3 x4 0 1 0 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 0 1 1 1) xs
 Premises and side conditions: Every listed outcome occurrence has nonnegative weight and the full sample mass is strictly positive. Repeated observations are counted with multiplicity. The two explicit score vectors are not assumed independent, jointly Gaussian or standardized.
 Proof/definition method: Specialize the shared kernel-checked finite-sample covariance Cauchy-Schwarz theorem to both explicit four-test score functions; no reproof or expansion of the weighted sum is performed.
 Library reuse: ListPoolingAlgebra and FourContrastCovariance own the covariance and contrast definitions; SampleContrastCauchy owns the general inequality; Rocq Stdlib real numbers and lists supply all operations.
 Boundary: Exact finite empirical covariance constraint on the named composites, not a separate distributional sampling law, population parameter estimate, chi-square pivot, normal tail or interval-coverage theorem.
*)
Theorem sample_contrast_cs_test2_triple234 :
 forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->
   batch_covariance w (four_batch_score x1 x2 x3 x4 0 1 0 0) (four_batch_score x1 x2 x3 x4 0 1 1 1) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 0 1 0 0) (four_batch_score x1 x2 x3 x4 0 1 1 1) xs
   <= batch_variance w (four_batch_score x1 x2 x3 x4 0 1 0 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 0 1 1 1) xs.
Proof.
 intros A w x1 x2 x3 x4 xs Hw Hm.
 exact (sample_covariance_cauchy_schwarz A w
   (four_batch_score x1 x2 x3 x4 0 1 0 0) (four_batch_score x1 x2 x3 x4 0 1 1 1) xs Hw Hm).
Qed.

(** [sample_contrast_cs_test2_allfour] (theorem).
 Mathematical meaning: For the second test score contrast and the all four tests score contrast, a nonnegative-weight finite sample must satisfy the sharp squared covariance-versus-variance feasibility constraint. The coefficients determine a specific multi-test contrast pair relevant to finite composite-score stability checks.
 Exact checked proposition: forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->    batch_covariance w (four_batch_score x1 x2 x3 x4 0 1 0 0) (four_batch_score x1 x2 x3 x4 1 1 1 1) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 0 1 0 0) (four_batch_score x1 x2 x3 x4 1 1 1 1) xs    <= batch_variance w (four_batch_score x1 x2 x3 x4 0 1 0 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 1 1 1) xs
 Premises and side conditions: Every listed outcome occurrence has nonnegative weight and the full sample mass is strictly positive. Repeated observations are counted with multiplicity. The two explicit score vectors are not assumed independent, jointly Gaussian or standardized.
 Proof/definition method: Specialize the shared kernel-checked finite-sample covariance Cauchy-Schwarz theorem to both explicit four-test score functions; no reproof or expansion of the weighted sum is performed.
 Library reuse: ListPoolingAlgebra and FourContrastCovariance own the covariance and contrast definitions; SampleContrastCauchy owns the general inequality; Rocq Stdlib real numbers and lists supply all operations.
 Boundary: Exact finite empirical covariance constraint on the named composites, not a separate distributional sampling law, population parameter estimate, chi-square pivot, normal tail or interval-coverage theorem.
*)
Theorem sample_contrast_cs_test2_allfour :
 forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->
   batch_covariance w (four_batch_score x1 x2 x3 x4 0 1 0 0) (four_batch_score x1 x2 x3 x4 1 1 1 1) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 0 1 0 0) (four_batch_score x1 x2 x3 x4 1 1 1 1) xs
   <= batch_variance w (four_batch_score x1 x2 x3 x4 0 1 0 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 1 1 1) xs.
Proof.
 intros A w x1 x2 x3 x4 xs Hw Hm.
 exact (sample_covariance_cauchy_schwarz A w
   (four_batch_score x1 x2 x3 x4 0 1 0 0) (four_batch_score x1 x2 x3 x4 1 1 1 1) xs Hw Hm).
Qed.

(** [sample_contrast_cs_test2_balanced12v34] (theorem).
 Mathematical meaning: For the second test score contrast and the difference between the two pairs score contrast, a nonnegative-weight finite sample must satisfy the sharp squared covariance-versus-variance feasibility constraint. The coefficients determine a specific multi-test contrast pair relevant to finite composite-score stability checks.
 Exact checked proposition: forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->    batch_covariance w (four_batch_score x1 x2 x3 x4 0 1 0 0) (four_batch_score x1 x2 x3 x4 1 1 (-1) (-1)) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 0 1 0 0) (four_batch_score x1 x2 x3 x4 1 1 (-1) (-1)) xs    <= batch_variance w (four_batch_score x1 x2 x3 x4 0 1 0 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 1 (-1) (-1)) xs
 Premises and side conditions: Every listed outcome occurrence has nonnegative weight and the full sample mass is strictly positive. Repeated observations are counted with multiplicity. The two explicit score vectors are not assumed independent, jointly Gaussian or standardized.
 Proof/definition method: Specialize the shared kernel-checked finite-sample covariance Cauchy-Schwarz theorem to both explicit four-test score functions; no reproof or expansion of the weighted sum is performed.
 Library reuse: ListPoolingAlgebra and FourContrastCovariance own the covariance and contrast definitions; SampleContrastCauchy owns the general inequality; Rocq Stdlib real numbers and lists supply all operations.
 Boundary: Exact finite empirical covariance constraint on the named composites, not a separate distributional sampling law, population parameter estimate, chi-square pivot, normal tail or interval-coverage theorem.
*)
Theorem sample_contrast_cs_test2_balanced12v34 :
 forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->
   batch_covariance w (four_batch_score x1 x2 x3 x4 0 1 0 0) (four_batch_score x1 x2 x3 x4 1 1 (-1) (-1)) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 0 1 0 0) (four_batch_score x1 x2 x3 x4 1 1 (-1) (-1)) xs
   <= batch_variance w (four_batch_score x1 x2 x3 x4 0 1 0 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 1 (-1) (-1)) xs.
Proof.
 intros A w x1 x2 x3 x4 xs Hw Hm.
 exact (sample_covariance_cauchy_schwarz A w
   (four_batch_score x1 x2 x3 x4 0 1 0 0) (four_batch_score x1 x2 x3 x4 1 1 (-1) (-1)) xs Hw Hm).
Qed.

(** [sample_contrast_cs_test3_test3] (theorem).
 Mathematical meaning: For the third test score contrast and the third test score contrast, a nonnegative-weight finite sample must satisfy the sharp squared covariance-versus-variance feasibility constraint. The coefficients determine a specific multi-test contrast pair relevant to finite composite-score stability checks.
 Exact checked proposition: forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->    batch_covariance w (four_batch_score x1 x2 x3 x4 0 0 1 0) (four_batch_score x1 x2 x3 x4 0 0 1 0) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 0 0 1 0) (four_batch_score x1 x2 x3 x4 0 0 1 0) xs    <= batch_variance w (four_batch_score x1 x2 x3 x4 0 0 1 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 0 0 1 0) xs
 Premises and side conditions: Every listed outcome occurrence has nonnegative weight and the full sample mass is strictly positive. Repeated observations are counted with multiplicity. The two explicit score vectors are not assumed independent, jointly Gaussian or standardized.
 Proof/definition method: Specialize the shared kernel-checked finite-sample covariance Cauchy-Schwarz theorem to both explicit four-test score functions; no reproof or expansion of the weighted sum is performed.
 Library reuse: ListPoolingAlgebra and FourContrastCovariance own the covariance and contrast definitions; SampleContrastCauchy owns the general inequality; Rocq Stdlib real numbers and lists supply all operations.
 Boundary: Exact finite empirical covariance constraint on the named composites, not a separate distributional sampling law, population parameter estimate, chi-square pivot, normal tail or interval-coverage theorem.
*)
Theorem sample_contrast_cs_test3_test3 :
 forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->
   batch_covariance w (four_batch_score x1 x2 x3 x4 0 0 1 0) (four_batch_score x1 x2 x3 x4 0 0 1 0) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 0 0 1 0) (four_batch_score x1 x2 x3 x4 0 0 1 0) xs
   <= batch_variance w (four_batch_score x1 x2 x3 x4 0 0 1 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 0 0 1 0) xs.
Proof.
 intros A w x1 x2 x3 x4 xs Hw Hm.
 exact (sample_covariance_cauchy_schwarz A w
   (four_batch_score x1 x2 x3 x4 0 0 1 0) (four_batch_score x1 x2 x3 x4 0 0 1 0) xs Hw Hm).
Qed.

(** [sample_contrast_cs_test3_test4] (theorem).
 Mathematical meaning: For the third test score contrast and the fourth test score contrast, a nonnegative-weight finite sample must satisfy the sharp squared covariance-versus-variance feasibility constraint. The coefficients determine a specific multi-test contrast pair relevant to finite composite-score stability checks.
 Exact checked proposition: forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->    batch_covariance w (four_batch_score x1 x2 x3 x4 0 0 1 0) (four_batch_score x1 x2 x3 x4 0 0 0 1) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 0 0 1 0) (four_batch_score x1 x2 x3 x4 0 0 0 1) xs    <= batch_variance w (four_batch_score x1 x2 x3 x4 0 0 1 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 0 0 0 1) xs
 Premises and side conditions: Every listed outcome occurrence has nonnegative weight and the full sample mass is strictly positive. Repeated observations are counted with multiplicity. The two explicit score vectors are not assumed independent, jointly Gaussian or standardized.
 Proof/definition method: Specialize the shared kernel-checked finite-sample covariance Cauchy-Schwarz theorem to both explicit four-test score functions; no reproof or expansion of the weighted sum is performed.
 Library reuse: ListPoolingAlgebra and FourContrastCovariance own the covariance and contrast definitions; SampleContrastCauchy owns the general inequality; Rocq Stdlib real numbers and lists supply all operations.
 Boundary: Exact finite empirical covariance constraint on the named composites, not a separate distributional sampling law, population parameter estimate, chi-square pivot, normal tail or interval-coverage theorem.
*)
Theorem sample_contrast_cs_test3_test4 :
 forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->
   batch_covariance w (four_batch_score x1 x2 x3 x4 0 0 1 0) (four_batch_score x1 x2 x3 x4 0 0 0 1) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 0 0 1 0) (four_batch_score x1 x2 x3 x4 0 0 0 1) xs
   <= batch_variance w (four_batch_score x1 x2 x3 x4 0 0 1 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 0 0 0 1) xs.
Proof.
 intros A w x1 x2 x3 x4 xs Hw Hm.
 exact (sample_covariance_cauchy_schwarz A w
   (four_batch_score x1 x2 x3 x4 0 0 1 0) (four_batch_score x1 x2 x3 x4 0 0 0 1) xs Hw Hm).
Qed.

(** [sample_contrast_cs_test3_difference12] (theorem).
 Mathematical meaning: For the third test score contrast and the first minus second test score contrast, a nonnegative-weight finite sample must satisfy the sharp squared covariance-versus-variance feasibility constraint. The coefficients determine a specific multi-test contrast pair relevant to finite composite-score stability checks.
 Exact checked proposition: forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->    batch_covariance w (four_batch_score x1 x2 x3 x4 0 0 1 0) (four_batch_score x1 x2 x3 x4 1 (-1) 0 0) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 0 0 1 0) (four_batch_score x1 x2 x3 x4 1 (-1) 0 0) xs    <= batch_variance w (four_batch_score x1 x2 x3 x4 0 0 1 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 (-1) 0 0) xs
 Premises and side conditions: Every listed outcome occurrence has nonnegative weight and the full sample mass is strictly positive. Repeated observations are counted with multiplicity. The two explicit score vectors are not assumed independent, jointly Gaussian or standardized.
 Proof/definition method: Specialize the shared kernel-checked finite-sample covariance Cauchy-Schwarz theorem to both explicit four-test score functions; no reproof or expansion of the weighted sum is performed.
 Library reuse: ListPoolingAlgebra and FourContrastCovariance own the covariance and contrast definitions; SampleContrastCauchy owns the general inequality; Rocq Stdlib real numbers and lists supply all operations.
 Boundary: Exact finite empirical covariance constraint on the named composites, not a separate distributional sampling law, population parameter estimate, chi-square pivot, normal tail or interval-coverage theorem.
*)
Theorem sample_contrast_cs_test3_difference12 :
 forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->
   batch_covariance w (four_batch_score x1 x2 x3 x4 0 0 1 0) (four_batch_score x1 x2 x3 x4 1 (-1) 0 0) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 0 0 1 0) (four_batch_score x1 x2 x3 x4 1 (-1) 0 0) xs
   <= batch_variance w (four_batch_score x1 x2 x3 x4 0 0 1 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 (-1) 0 0) xs.
Proof.
 intros A w x1 x2 x3 x4 xs Hw Hm.
 exact (sample_covariance_cauchy_schwarz A w
   (four_batch_score x1 x2 x3 x4 0 0 1 0) (four_batch_score x1 x2 x3 x4 1 (-1) 0 0) xs Hw Hm).
Qed.

(** [sample_contrast_cs_test3_difference13] (theorem).
 Mathematical meaning: For the third test score contrast and the first minus third test score contrast, a nonnegative-weight finite sample must satisfy the sharp squared covariance-versus-variance feasibility constraint. The coefficients determine a specific multi-test contrast pair relevant to finite composite-score stability checks.
 Exact checked proposition: forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->    batch_covariance w (four_batch_score x1 x2 x3 x4 0 0 1 0) (four_batch_score x1 x2 x3 x4 1 0 (-1) 0) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 0 0 1 0) (four_batch_score x1 x2 x3 x4 1 0 (-1) 0) xs    <= batch_variance w (four_batch_score x1 x2 x3 x4 0 0 1 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 0 (-1) 0) xs
 Premises and side conditions: Every listed outcome occurrence has nonnegative weight and the full sample mass is strictly positive. Repeated observations are counted with multiplicity. The two explicit score vectors are not assumed independent, jointly Gaussian or standardized.
 Proof/definition method: Specialize the shared kernel-checked finite-sample covariance Cauchy-Schwarz theorem to both explicit four-test score functions; no reproof or expansion of the weighted sum is performed.
 Library reuse: ListPoolingAlgebra and FourContrastCovariance own the covariance and contrast definitions; SampleContrastCauchy owns the general inequality; Rocq Stdlib real numbers and lists supply all operations.
 Boundary: Exact finite empirical covariance constraint on the named composites, not a separate distributional sampling law, population parameter estimate, chi-square pivot, normal tail or interval-coverage theorem.
*)
Theorem sample_contrast_cs_test3_difference13 :
 forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->
   batch_covariance w (four_batch_score x1 x2 x3 x4 0 0 1 0) (four_batch_score x1 x2 x3 x4 1 0 (-1) 0) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 0 0 1 0) (four_batch_score x1 x2 x3 x4 1 0 (-1) 0) xs
   <= batch_variance w (four_batch_score x1 x2 x3 x4 0 0 1 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 0 (-1) 0) xs.
Proof.
 intros A w x1 x2 x3 x4 xs Hw Hm.
 exact (sample_covariance_cauchy_schwarz A w
   (four_batch_score x1 x2 x3 x4 0 0 1 0) (four_batch_score x1 x2 x3 x4 1 0 (-1) 0) xs Hw Hm).
Qed.

(** [sample_contrast_cs_test3_difference14] (theorem).
 Mathematical meaning: For the third test score contrast and the first minus fourth test score contrast, a nonnegative-weight finite sample must satisfy the sharp squared covariance-versus-variance feasibility constraint. The coefficients determine a specific multi-test contrast pair relevant to finite composite-score stability checks.
 Exact checked proposition: forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->    batch_covariance w (four_batch_score x1 x2 x3 x4 0 0 1 0) (four_batch_score x1 x2 x3 x4 1 0 0 (-1)) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 0 0 1 0) (four_batch_score x1 x2 x3 x4 1 0 0 (-1)) xs    <= batch_variance w (four_batch_score x1 x2 x3 x4 0 0 1 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 0 0 (-1)) xs
 Premises and side conditions: Every listed outcome occurrence has nonnegative weight and the full sample mass is strictly positive. Repeated observations are counted with multiplicity. The two explicit score vectors are not assumed independent, jointly Gaussian or standardized.
 Proof/definition method: Specialize the shared kernel-checked finite-sample covariance Cauchy-Schwarz theorem to both explicit four-test score functions; no reproof or expansion of the weighted sum is performed.
 Library reuse: ListPoolingAlgebra and FourContrastCovariance own the covariance and contrast definitions; SampleContrastCauchy owns the general inequality; Rocq Stdlib real numbers and lists supply all operations.
 Boundary: Exact finite empirical covariance constraint on the named composites, not a separate distributional sampling law, population parameter estimate, chi-square pivot, normal tail or interval-coverage theorem.
*)
Theorem sample_contrast_cs_test3_difference14 :
 forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->
   batch_covariance w (four_batch_score x1 x2 x3 x4 0 0 1 0) (four_batch_score x1 x2 x3 x4 1 0 0 (-1)) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 0 0 1 0) (four_batch_score x1 x2 x3 x4 1 0 0 (-1)) xs
   <= batch_variance w (four_batch_score x1 x2 x3 x4 0 0 1 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 0 0 (-1)) xs.
Proof.
 intros A w x1 x2 x3 x4 xs Hw Hm.
 exact (sample_covariance_cauchy_schwarz A w
   (four_batch_score x1 x2 x3 x4 0 0 1 0) (four_batch_score x1 x2 x3 x4 1 0 0 (-1)) xs Hw Hm).
Qed.

(** [sample_contrast_cs_test3_difference23] (theorem).
 Mathematical meaning: For the third test score contrast and the second minus third test score contrast, a nonnegative-weight finite sample must satisfy the sharp squared covariance-versus-variance feasibility constraint. The coefficients determine a specific multi-test contrast pair relevant to finite composite-score stability checks.
 Exact checked proposition: forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->    batch_covariance w (four_batch_score x1 x2 x3 x4 0 0 1 0) (four_batch_score x1 x2 x3 x4 0 1 (-1) 0) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 0 0 1 0) (four_batch_score x1 x2 x3 x4 0 1 (-1) 0) xs    <= batch_variance w (four_batch_score x1 x2 x3 x4 0 0 1 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 0 1 (-1) 0) xs
 Premises and side conditions: Every listed outcome occurrence has nonnegative weight and the full sample mass is strictly positive. Repeated observations are counted with multiplicity. The two explicit score vectors are not assumed independent, jointly Gaussian or standardized.
 Proof/definition method: Specialize the shared kernel-checked finite-sample covariance Cauchy-Schwarz theorem to both explicit four-test score functions; no reproof or expansion of the weighted sum is performed.
 Library reuse: ListPoolingAlgebra and FourContrastCovariance own the covariance and contrast definitions; SampleContrastCauchy owns the general inequality; Rocq Stdlib real numbers and lists supply all operations.
 Boundary: Exact finite empirical covariance constraint on the named composites, not a separate distributional sampling law, population parameter estimate, chi-square pivot, normal tail or interval-coverage theorem.
*)
Theorem sample_contrast_cs_test3_difference23 :
 forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->
   batch_covariance w (four_batch_score x1 x2 x3 x4 0 0 1 0) (four_batch_score x1 x2 x3 x4 0 1 (-1) 0) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 0 0 1 0) (four_batch_score x1 x2 x3 x4 0 1 (-1) 0) xs
   <= batch_variance w (four_batch_score x1 x2 x3 x4 0 0 1 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 0 1 (-1) 0) xs.
Proof.
 intros A w x1 x2 x3 x4 xs Hw Hm.
 exact (sample_covariance_cauchy_schwarz A w
   (four_batch_score x1 x2 x3 x4 0 0 1 0) (four_batch_score x1 x2 x3 x4 0 1 (-1) 0) xs Hw Hm).
Qed.

(** [sample_contrast_cs_test3_difference24] (theorem).
 Mathematical meaning: For the third test score contrast and the second minus fourth test score contrast, a nonnegative-weight finite sample must satisfy the sharp squared covariance-versus-variance feasibility constraint. The coefficients determine a specific multi-test contrast pair relevant to finite composite-score stability checks.
 Exact checked proposition: forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->    batch_covariance w (four_batch_score x1 x2 x3 x4 0 0 1 0) (four_batch_score x1 x2 x3 x4 0 1 0 (-1)) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 0 0 1 0) (four_batch_score x1 x2 x3 x4 0 1 0 (-1)) xs    <= batch_variance w (four_batch_score x1 x2 x3 x4 0 0 1 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 0 1 0 (-1)) xs
 Premises and side conditions: Every listed outcome occurrence has nonnegative weight and the full sample mass is strictly positive. Repeated observations are counted with multiplicity. The two explicit score vectors are not assumed independent, jointly Gaussian or standardized.
 Proof/definition method: Specialize the shared kernel-checked finite-sample covariance Cauchy-Schwarz theorem to both explicit four-test score functions; no reproof or expansion of the weighted sum is performed.
 Library reuse: ListPoolingAlgebra and FourContrastCovariance own the covariance and contrast definitions; SampleContrastCauchy owns the general inequality; Rocq Stdlib real numbers and lists supply all operations.
 Boundary: Exact finite empirical covariance constraint on the named composites, not a separate distributional sampling law, population parameter estimate, chi-square pivot, normal tail or interval-coverage theorem.
*)
Theorem sample_contrast_cs_test3_difference24 :
 forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->
   batch_covariance w (four_batch_score x1 x2 x3 x4 0 0 1 0) (four_batch_score x1 x2 x3 x4 0 1 0 (-1)) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 0 0 1 0) (four_batch_score x1 x2 x3 x4 0 1 0 (-1)) xs
   <= batch_variance w (four_batch_score x1 x2 x3 x4 0 0 1 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 0 1 0 (-1)) xs.
Proof.
 intros A w x1 x2 x3 x4 xs Hw Hm.
 exact (sample_covariance_cauchy_schwarz A w
   (four_batch_score x1 x2 x3 x4 0 0 1 0) (four_batch_score x1 x2 x3 x4 0 1 0 (-1)) xs Hw Hm).
Qed.

(** [sample_contrast_cs_test3_difference34] (theorem).
 Mathematical meaning: For the third test score contrast and the third minus fourth test score contrast, a nonnegative-weight finite sample must satisfy the sharp squared covariance-versus-variance feasibility constraint. The coefficients determine a specific multi-test contrast pair relevant to finite composite-score stability checks.
 Exact checked proposition: forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->    batch_covariance w (four_batch_score x1 x2 x3 x4 0 0 1 0) (four_batch_score x1 x2 x3 x4 0 0 1 (-1)) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 0 0 1 0) (four_batch_score x1 x2 x3 x4 0 0 1 (-1)) xs    <= batch_variance w (four_batch_score x1 x2 x3 x4 0 0 1 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 0 0 1 (-1)) xs
 Premises and side conditions: Every listed outcome occurrence has nonnegative weight and the full sample mass is strictly positive. Repeated observations are counted with multiplicity. The two explicit score vectors are not assumed independent, jointly Gaussian or standardized.
 Proof/definition method: Specialize the shared kernel-checked finite-sample covariance Cauchy-Schwarz theorem to both explicit four-test score functions; no reproof or expansion of the weighted sum is performed.
 Library reuse: ListPoolingAlgebra and FourContrastCovariance own the covariance and contrast definitions; SampleContrastCauchy owns the general inequality; Rocq Stdlib real numbers and lists supply all operations.
 Boundary: Exact finite empirical covariance constraint on the named composites, not a separate distributional sampling law, population parameter estimate, chi-square pivot, normal tail or interval-coverage theorem.
*)
Theorem sample_contrast_cs_test3_difference34 :
 forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->
   batch_covariance w (four_batch_score x1 x2 x3 x4 0 0 1 0) (four_batch_score x1 x2 x3 x4 0 0 1 (-1)) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 0 0 1 0) (four_batch_score x1 x2 x3 x4 0 0 1 (-1)) xs
   <= batch_variance w (four_batch_score x1 x2 x3 x4 0 0 1 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 0 0 1 (-1)) xs.
Proof.
 intros A w x1 x2 x3 x4 xs Hw Hm.
 exact (sample_covariance_cauchy_schwarz A w
   (four_batch_score x1 x2 x3 x4 0 0 1 0) (four_batch_score x1 x2 x3 x4 0 0 1 (-1)) xs Hw Hm).
Qed.

(** [sample_contrast_cs_test3_triple123] (theorem).
 Mathematical meaning: For the third test score contrast and the first three tests score contrast, a nonnegative-weight finite sample must satisfy the sharp squared covariance-versus-variance feasibility constraint. The coefficients determine a specific multi-test contrast pair relevant to finite composite-score stability checks.
 Exact checked proposition: forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->    batch_covariance w (four_batch_score x1 x2 x3 x4 0 0 1 0) (four_batch_score x1 x2 x3 x4 1 1 1 0) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 0 0 1 0) (four_batch_score x1 x2 x3 x4 1 1 1 0) xs    <= batch_variance w (four_batch_score x1 x2 x3 x4 0 0 1 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 1 1 0) xs
 Premises and side conditions: Every listed outcome occurrence has nonnegative weight and the full sample mass is strictly positive. Repeated observations are counted with multiplicity. The two explicit score vectors are not assumed independent, jointly Gaussian or standardized.
 Proof/definition method: Specialize the shared kernel-checked finite-sample covariance Cauchy-Schwarz theorem to both explicit four-test score functions; no reproof or expansion of the weighted sum is performed.
 Library reuse: ListPoolingAlgebra and FourContrastCovariance own the covariance and contrast definitions; SampleContrastCauchy owns the general inequality; Rocq Stdlib real numbers and lists supply all operations.
 Boundary: Exact finite empirical covariance constraint on the named composites, not a separate distributional sampling law, population parameter estimate, chi-square pivot, normal tail or interval-coverage theorem.
*)
Theorem sample_contrast_cs_test3_triple123 :
 forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->
   batch_covariance w (four_batch_score x1 x2 x3 x4 0 0 1 0) (four_batch_score x1 x2 x3 x4 1 1 1 0) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 0 0 1 0) (four_batch_score x1 x2 x3 x4 1 1 1 0) xs
   <= batch_variance w (four_batch_score x1 x2 x3 x4 0 0 1 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 1 1 0) xs.
Proof.
 intros A w x1 x2 x3 x4 xs Hw Hm.
 exact (sample_covariance_cauchy_schwarz A w
   (four_batch_score x1 x2 x3 x4 0 0 1 0) (four_batch_score x1 x2 x3 x4 1 1 1 0) xs Hw Hm).
Qed.

(** [sample_contrast_cs_test3_triple124] (theorem).
 Mathematical meaning: For the third test score contrast and the tests one, two and four score contrast, a nonnegative-weight finite sample must satisfy the sharp squared covariance-versus-variance feasibility constraint. The coefficients determine a specific multi-test contrast pair relevant to finite composite-score stability checks.
 Exact checked proposition: forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->    batch_covariance w (four_batch_score x1 x2 x3 x4 0 0 1 0) (four_batch_score x1 x2 x3 x4 1 1 0 1) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 0 0 1 0) (four_batch_score x1 x2 x3 x4 1 1 0 1) xs    <= batch_variance w (four_batch_score x1 x2 x3 x4 0 0 1 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 1 0 1) xs
 Premises and side conditions: Every listed outcome occurrence has nonnegative weight and the full sample mass is strictly positive. Repeated observations are counted with multiplicity. The two explicit score vectors are not assumed independent, jointly Gaussian or standardized.
 Proof/definition method: Specialize the shared kernel-checked finite-sample covariance Cauchy-Schwarz theorem to both explicit four-test score functions; no reproof or expansion of the weighted sum is performed.
 Library reuse: ListPoolingAlgebra and FourContrastCovariance own the covariance and contrast definitions; SampleContrastCauchy owns the general inequality; Rocq Stdlib real numbers and lists supply all operations.
 Boundary: Exact finite empirical covariance constraint on the named composites, not a separate distributional sampling law, population parameter estimate, chi-square pivot, normal tail or interval-coverage theorem.
*)
Theorem sample_contrast_cs_test3_triple124 :
 forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->
   batch_covariance w (four_batch_score x1 x2 x3 x4 0 0 1 0) (four_batch_score x1 x2 x3 x4 1 1 0 1) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 0 0 1 0) (four_batch_score x1 x2 x3 x4 1 1 0 1) xs
   <= batch_variance w (four_batch_score x1 x2 x3 x4 0 0 1 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 1 0 1) xs.
Proof.
 intros A w x1 x2 x3 x4 xs Hw Hm.
 exact (sample_covariance_cauchy_schwarz A w
   (four_batch_score x1 x2 x3 x4 0 0 1 0) (four_batch_score x1 x2 x3 x4 1 1 0 1) xs Hw Hm).
Qed.

(** [sample_contrast_cs_test3_triple134] (theorem).
 Mathematical meaning: For the third test score contrast and the tests one, three and four score contrast, a nonnegative-weight finite sample must satisfy the sharp squared covariance-versus-variance feasibility constraint. The coefficients determine a specific multi-test contrast pair relevant to finite composite-score stability checks.
 Exact checked proposition: forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->    batch_covariance w (four_batch_score x1 x2 x3 x4 0 0 1 0) (four_batch_score x1 x2 x3 x4 1 0 1 1) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 0 0 1 0) (four_batch_score x1 x2 x3 x4 1 0 1 1) xs    <= batch_variance w (four_batch_score x1 x2 x3 x4 0 0 1 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 0 1 1) xs
 Premises and side conditions: Every listed outcome occurrence has nonnegative weight and the full sample mass is strictly positive. Repeated observations are counted with multiplicity. The two explicit score vectors are not assumed independent, jointly Gaussian or standardized.
 Proof/definition method: Specialize the shared kernel-checked finite-sample covariance Cauchy-Schwarz theorem to both explicit four-test score functions; no reproof or expansion of the weighted sum is performed.
 Library reuse: ListPoolingAlgebra and FourContrastCovariance own the covariance and contrast definitions; SampleContrastCauchy owns the general inequality; Rocq Stdlib real numbers and lists supply all operations.
 Boundary: Exact finite empirical covariance constraint on the named composites, not a separate distributional sampling law, population parameter estimate, chi-square pivot, normal tail or interval-coverage theorem.
*)
Theorem sample_contrast_cs_test3_triple134 :
 forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->
   batch_covariance w (four_batch_score x1 x2 x3 x4 0 0 1 0) (four_batch_score x1 x2 x3 x4 1 0 1 1) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 0 0 1 0) (four_batch_score x1 x2 x3 x4 1 0 1 1) xs
   <= batch_variance w (four_batch_score x1 x2 x3 x4 0 0 1 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 0 1 1) xs.
Proof.
 intros A w x1 x2 x3 x4 xs Hw Hm.
 exact (sample_covariance_cauchy_schwarz A w
   (four_batch_score x1 x2 x3 x4 0 0 1 0) (four_batch_score x1 x2 x3 x4 1 0 1 1) xs Hw Hm).
Qed.

(** [sample_contrast_cs_test3_triple234] (theorem).
 Mathematical meaning: For the third test score contrast and the last three tests score contrast, a nonnegative-weight finite sample must satisfy the sharp squared covariance-versus-variance feasibility constraint. The coefficients determine a specific multi-test contrast pair relevant to finite composite-score stability checks.
 Exact checked proposition: forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->    batch_covariance w (four_batch_score x1 x2 x3 x4 0 0 1 0) (four_batch_score x1 x2 x3 x4 0 1 1 1) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 0 0 1 0) (four_batch_score x1 x2 x3 x4 0 1 1 1) xs    <= batch_variance w (four_batch_score x1 x2 x3 x4 0 0 1 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 0 1 1 1) xs
 Premises and side conditions: Every listed outcome occurrence has nonnegative weight and the full sample mass is strictly positive. Repeated observations are counted with multiplicity. The two explicit score vectors are not assumed independent, jointly Gaussian or standardized.
 Proof/definition method: Specialize the shared kernel-checked finite-sample covariance Cauchy-Schwarz theorem to both explicit four-test score functions; no reproof or expansion of the weighted sum is performed.
 Library reuse: ListPoolingAlgebra and FourContrastCovariance own the covariance and contrast definitions; SampleContrastCauchy owns the general inequality; Rocq Stdlib real numbers and lists supply all operations.
 Boundary: Exact finite empirical covariance constraint on the named composites, not a separate distributional sampling law, population parameter estimate, chi-square pivot, normal tail or interval-coverage theorem.
*)
Theorem sample_contrast_cs_test3_triple234 :
 forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->
   batch_covariance w (four_batch_score x1 x2 x3 x4 0 0 1 0) (four_batch_score x1 x2 x3 x4 0 1 1 1) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 0 0 1 0) (four_batch_score x1 x2 x3 x4 0 1 1 1) xs
   <= batch_variance w (four_batch_score x1 x2 x3 x4 0 0 1 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 0 1 1 1) xs.
Proof.
 intros A w x1 x2 x3 x4 xs Hw Hm.
 exact (sample_covariance_cauchy_schwarz A w
   (four_batch_score x1 x2 x3 x4 0 0 1 0) (four_batch_score x1 x2 x3 x4 0 1 1 1) xs Hw Hm).
Qed.

(** [sample_contrast_cs_test3_allfour] (theorem).
 Mathematical meaning: For the third test score contrast and the all four tests score contrast, a nonnegative-weight finite sample must satisfy the sharp squared covariance-versus-variance feasibility constraint. The coefficients determine a specific multi-test contrast pair relevant to finite composite-score stability checks.
 Exact checked proposition: forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->    batch_covariance w (four_batch_score x1 x2 x3 x4 0 0 1 0) (four_batch_score x1 x2 x3 x4 1 1 1 1) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 0 0 1 0) (four_batch_score x1 x2 x3 x4 1 1 1 1) xs    <= batch_variance w (four_batch_score x1 x2 x3 x4 0 0 1 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 1 1 1) xs
 Premises and side conditions: Every listed outcome occurrence has nonnegative weight and the full sample mass is strictly positive. Repeated observations are counted with multiplicity. The two explicit score vectors are not assumed independent, jointly Gaussian or standardized.
 Proof/definition method: Specialize the shared kernel-checked finite-sample covariance Cauchy-Schwarz theorem to both explicit four-test score functions; no reproof or expansion of the weighted sum is performed.
 Library reuse: ListPoolingAlgebra and FourContrastCovariance own the covariance and contrast definitions; SampleContrastCauchy owns the general inequality; Rocq Stdlib real numbers and lists supply all operations.
 Boundary: Exact finite empirical covariance constraint on the named composites, not a separate distributional sampling law, population parameter estimate, chi-square pivot, normal tail or interval-coverage theorem.
*)
Theorem sample_contrast_cs_test3_allfour :
 forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->
   batch_covariance w (four_batch_score x1 x2 x3 x4 0 0 1 0) (four_batch_score x1 x2 x3 x4 1 1 1 1) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 0 0 1 0) (four_batch_score x1 x2 x3 x4 1 1 1 1) xs
   <= batch_variance w (four_batch_score x1 x2 x3 x4 0 0 1 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 1 1 1) xs.
Proof.
 intros A w x1 x2 x3 x4 xs Hw Hm.
 exact (sample_covariance_cauchy_schwarz A w
   (four_batch_score x1 x2 x3 x4 0 0 1 0) (four_batch_score x1 x2 x3 x4 1 1 1 1) xs Hw Hm).
Qed.

(** [sample_contrast_cs_test3_balanced12v34] (theorem).
 Mathematical meaning: For the third test score contrast and the difference between the two pairs score contrast, a nonnegative-weight finite sample must satisfy the sharp squared covariance-versus-variance feasibility constraint. The coefficients determine a specific multi-test contrast pair relevant to finite composite-score stability checks.
 Exact checked proposition: forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->    batch_covariance w (four_batch_score x1 x2 x3 x4 0 0 1 0) (four_batch_score x1 x2 x3 x4 1 1 (-1) (-1)) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 0 0 1 0) (four_batch_score x1 x2 x3 x4 1 1 (-1) (-1)) xs    <= batch_variance w (four_batch_score x1 x2 x3 x4 0 0 1 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 1 (-1) (-1)) xs
 Premises and side conditions: Every listed outcome occurrence has nonnegative weight and the full sample mass is strictly positive. Repeated observations are counted with multiplicity. The two explicit score vectors are not assumed independent, jointly Gaussian or standardized.
 Proof/definition method: Specialize the shared kernel-checked finite-sample covariance Cauchy-Schwarz theorem to both explicit four-test score functions; no reproof or expansion of the weighted sum is performed.
 Library reuse: ListPoolingAlgebra and FourContrastCovariance own the covariance and contrast definitions; SampleContrastCauchy owns the general inequality; Rocq Stdlib real numbers and lists supply all operations.
 Boundary: Exact finite empirical covariance constraint on the named composites, not a separate distributional sampling law, population parameter estimate, chi-square pivot, normal tail or interval-coverage theorem.
*)
Theorem sample_contrast_cs_test3_balanced12v34 :
 forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->
   batch_covariance w (four_batch_score x1 x2 x3 x4 0 0 1 0) (four_batch_score x1 x2 x3 x4 1 1 (-1) (-1)) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 0 0 1 0) (four_batch_score x1 x2 x3 x4 1 1 (-1) (-1)) xs
   <= batch_variance w (four_batch_score x1 x2 x3 x4 0 0 1 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 1 (-1) (-1)) xs.
Proof.
 intros A w x1 x2 x3 x4 xs Hw Hm.
 exact (sample_covariance_cauchy_schwarz A w
   (four_batch_score x1 x2 x3 x4 0 0 1 0) (four_batch_score x1 x2 x3 x4 1 1 (-1) (-1)) xs Hw Hm).
Qed.

(** [sample_contrast_cs_test4_test4] (theorem).
 Mathematical meaning: For the fourth test score contrast and the fourth test score contrast, a nonnegative-weight finite sample must satisfy the sharp squared covariance-versus-variance feasibility constraint. The coefficients determine a specific multi-test contrast pair relevant to finite composite-score stability checks.
 Exact checked proposition: forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->    batch_covariance w (four_batch_score x1 x2 x3 x4 0 0 0 1) (four_batch_score x1 x2 x3 x4 0 0 0 1) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 0 0 0 1) (four_batch_score x1 x2 x3 x4 0 0 0 1) xs    <= batch_variance w (four_batch_score x1 x2 x3 x4 0 0 0 1) xs * batch_variance w (four_batch_score x1 x2 x3 x4 0 0 0 1) xs
 Premises and side conditions: Every listed outcome occurrence has nonnegative weight and the full sample mass is strictly positive. Repeated observations are counted with multiplicity. The two explicit score vectors are not assumed independent, jointly Gaussian or standardized.
 Proof/definition method: Specialize the shared kernel-checked finite-sample covariance Cauchy-Schwarz theorem to both explicit four-test score functions; no reproof or expansion of the weighted sum is performed.
 Library reuse: ListPoolingAlgebra and FourContrastCovariance own the covariance and contrast definitions; SampleContrastCauchy owns the general inequality; Rocq Stdlib real numbers and lists supply all operations.
 Boundary: Exact finite empirical covariance constraint on the named composites, not a separate distributional sampling law, population parameter estimate, chi-square pivot, normal tail or interval-coverage theorem.
*)
Theorem sample_contrast_cs_test4_test4 :
 forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->
   batch_covariance w (four_batch_score x1 x2 x3 x4 0 0 0 1) (four_batch_score x1 x2 x3 x4 0 0 0 1) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 0 0 0 1) (four_batch_score x1 x2 x3 x4 0 0 0 1) xs
   <= batch_variance w (four_batch_score x1 x2 x3 x4 0 0 0 1) xs * batch_variance w (four_batch_score x1 x2 x3 x4 0 0 0 1) xs.
Proof.
 intros A w x1 x2 x3 x4 xs Hw Hm.
 exact (sample_covariance_cauchy_schwarz A w
   (four_batch_score x1 x2 x3 x4 0 0 0 1) (four_batch_score x1 x2 x3 x4 0 0 0 1) xs Hw Hm).
Qed.

(** [sample_contrast_cs_test4_difference12] (theorem).
 Mathematical meaning: For the fourth test score contrast and the first minus second test score contrast, a nonnegative-weight finite sample must satisfy the sharp squared covariance-versus-variance feasibility constraint. The coefficients determine a specific multi-test contrast pair relevant to finite composite-score stability checks.
 Exact checked proposition: forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->    batch_covariance w (four_batch_score x1 x2 x3 x4 0 0 0 1) (four_batch_score x1 x2 x3 x4 1 (-1) 0 0) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 0 0 0 1) (four_batch_score x1 x2 x3 x4 1 (-1) 0 0) xs    <= batch_variance w (four_batch_score x1 x2 x3 x4 0 0 0 1) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 (-1) 0 0) xs
 Premises and side conditions: Every listed outcome occurrence has nonnegative weight and the full sample mass is strictly positive. Repeated observations are counted with multiplicity. The two explicit score vectors are not assumed independent, jointly Gaussian or standardized.
 Proof/definition method: Specialize the shared kernel-checked finite-sample covariance Cauchy-Schwarz theorem to both explicit four-test score functions; no reproof or expansion of the weighted sum is performed.
 Library reuse: ListPoolingAlgebra and FourContrastCovariance own the covariance and contrast definitions; SampleContrastCauchy owns the general inequality; Rocq Stdlib real numbers and lists supply all operations.
 Boundary: Exact finite empirical covariance constraint on the named composites, not a separate distributional sampling law, population parameter estimate, chi-square pivot, normal tail or interval-coverage theorem.
*)
Theorem sample_contrast_cs_test4_difference12 :
 forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->
   batch_covariance w (four_batch_score x1 x2 x3 x4 0 0 0 1) (four_batch_score x1 x2 x3 x4 1 (-1) 0 0) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 0 0 0 1) (four_batch_score x1 x2 x3 x4 1 (-1) 0 0) xs
   <= batch_variance w (four_batch_score x1 x2 x3 x4 0 0 0 1) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 (-1) 0 0) xs.
Proof.
 intros A w x1 x2 x3 x4 xs Hw Hm.
 exact (sample_covariance_cauchy_schwarz A w
   (four_batch_score x1 x2 x3 x4 0 0 0 1) (four_batch_score x1 x2 x3 x4 1 (-1) 0 0) xs Hw Hm).
Qed.

(** [sample_contrast_cs_test4_difference13] (theorem).
 Mathematical meaning: For the fourth test score contrast and the first minus third test score contrast, a nonnegative-weight finite sample must satisfy the sharp squared covariance-versus-variance feasibility constraint. The coefficients determine a specific multi-test contrast pair relevant to finite composite-score stability checks.
 Exact checked proposition: forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->    batch_covariance w (four_batch_score x1 x2 x3 x4 0 0 0 1) (four_batch_score x1 x2 x3 x4 1 0 (-1) 0) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 0 0 0 1) (four_batch_score x1 x2 x3 x4 1 0 (-1) 0) xs    <= batch_variance w (four_batch_score x1 x2 x3 x4 0 0 0 1) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 0 (-1) 0) xs
 Premises and side conditions: Every listed outcome occurrence has nonnegative weight and the full sample mass is strictly positive. Repeated observations are counted with multiplicity. The two explicit score vectors are not assumed independent, jointly Gaussian or standardized.
 Proof/definition method: Specialize the shared kernel-checked finite-sample covariance Cauchy-Schwarz theorem to both explicit four-test score functions; no reproof or expansion of the weighted sum is performed.
 Library reuse: ListPoolingAlgebra and FourContrastCovariance own the covariance and contrast definitions; SampleContrastCauchy owns the general inequality; Rocq Stdlib real numbers and lists supply all operations.
 Boundary: Exact finite empirical covariance constraint on the named composites, not a separate distributional sampling law, population parameter estimate, chi-square pivot, normal tail or interval-coverage theorem.
*)
Theorem sample_contrast_cs_test4_difference13 :
 forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->
   batch_covariance w (four_batch_score x1 x2 x3 x4 0 0 0 1) (four_batch_score x1 x2 x3 x4 1 0 (-1) 0) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 0 0 0 1) (four_batch_score x1 x2 x3 x4 1 0 (-1) 0) xs
   <= batch_variance w (four_batch_score x1 x2 x3 x4 0 0 0 1) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 0 (-1) 0) xs.
Proof.
 intros A w x1 x2 x3 x4 xs Hw Hm.
 exact (sample_covariance_cauchy_schwarz A w
   (four_batch_score x1 x2 x3 x4 0 0 0 1) (four_batch_score x1 x2 x3 x4 1 0 (-1) 0) xs Hw Hm).
Qed.

(** [sample_contrast_cs_test4_difference14] (theorem).
 Mathematical meaning: For the fourth test score contrast and the first minus fourth test score contrast, a nonnegative-weight finite sample must satisfy the sharp squared covariance-versus-variance feasibility constraint. The coefficients determine a specific multi-test contrast pair relevant to finite composite-score stability checks.
 Exact checked proposition: forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->    batch_covariance w (four_batch_score x1 x2 x3 x4 0 0 0 1) (four_batch_score x1 x2 x3 x4 1 0 0 (-1)) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 0 0 0 1) (four_batch_score x1 x2 x3 x4 1 0 0 (-1)) xs    <= batch_variance w (four_batch_score x1 x2 x3 x4 0 0 0 1) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 0 0 (-1)) xs
 Premises and side conditions: Every listed outcome occurrence has nonnegative weight and the full sample mass is strictly positive. Repeated observations are counted with multiplicity. The two explicit score vectors are not assumed independent, jointly Gaussian or standardized.
 Proof/definition method: Specialize the shared kernel-checked finite-sample covariance Cauchy-Schwarz theorem to both explicit four-test score functions; no reproof or expansion of the weighted sum is performed.
 Library reuse: ListPoolingAlgebra and FourContrastCovariance own the covariance and contrast definitions; SampleContrastCauchy owns the general inequality; Rocq Stdlib real numbers and lists supply all operations.
 Boundary: Exact finite empirical covariance constraint on the named composites, not a separate distributional sampling law, population parameter estimate, chi-square pivot, normal tail or interval-coverage theorem.
*)
Theorem sample_contrast_cs_test4_difference14 :
 forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->
   batch_covariance w (four_batch_score x1 x2 x3 x4 0 0 0 1) (four_batch_score x1 x2 x3 x4 1 0 0 (-1)) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 0 0 0 1) (four_batch_score x1 x2 x3 x4 1 0 0 (-1)) xs
   <= batch_variance w (four_batch_score x1 x2 x3 x4 0 0 0 1) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 0 0 (-1)) xs.
Proof.
 intros A w x1 x2 x3 x4 xs Hw Hm.
 exact (sample_covariance_cauchy_schwarz A w
   (four_batch_score x1 x2 x3 x4 0 0 0 1) (four_batch_score x1 x2 x3 x4 1 0 0 (-1)) xs Hw Hm).
Qed.

(** [sample_contrast_cs_test4_difference23] (theorem).
 Mathematical meaning: For the fourth test score contrast and the second minus third test score contrast, a nonnegative-weight finite sample must satisfy the sharp squared covariance-versus-variance feasibility constraint. The coefficients determine a specific multi-test contrast pair relevant to finite composite-score stability checks.
 Exact checked proposition: forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->    batch_covariance w (four_batch_score x1 x2 x3 x4 0 0 0 1) (four_batch_score x1 x2 x3 x4 0 1 (-1) 0) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 0 0 0 1) (four_batch_score x1 x2 x3 x4 0 1 (-1) 0) xs    <= batch_variance w (four_batch_score x1 x2 x3 x4 0 0 0 1) xs * batch_variance w (four_batch_score x1 x2 x3 x4 0 1 (-1) 0) xs
 Premises and side conditions: Every listed outcome occurrence has nonnegative weight and the full sample mass is strictly positive. Repeated observations are counted with multiplicity. The two explicit score vectors are not assumed independent, jointly Gaussian or standardized.
 Proof/definition method: Specialize the shared kernel-checked finite-sample covariance Cauchy-Schwarz theorem to both explicit four-test score functions; no reproof or expansion of the weighted sum is performed.
 Library reuse: ListPoolingAlgebra and FourContrastCovariance own the covariance and contrast definitions; SampleContrastCauchy owns the general inequality; Rocq Stdlib real numbers and lists supply all operations.
 Boundary: Exact finite empirical covariance constraint on the named composites, not a separate distributional sampling law, population parameter estimate, chi-square pivot, normal tail or interval-coverage theorem.
*)
Theorem sample_contrast_cs_test4_difference23 :
 forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->
   batch_covariance w (four_batch_score x1 x2 x3 x4 0 0 0 1) (four_batch_score x1 x2 x3 x4 0 1 (-1) 0) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 0 0 0 1) (four_batch_score x1 x2 x3 x4 0 1 (-1) 0) xs
   <= batch_variance w (four_batch_score x1 x2 x3 x4 0 0 0 1) xs * batch_variance w (four_batch_score x1 x2 x3 x4 0 1 (-1) 0) xs.
Proof.
 intros A w x1 x2 x3 x4 xs Hw Hm.
 exact (sample_covariance_cauchy_schwarz A w
   (four_batch_score x1 x2 x3 x4 0 0 0 1) (four_batch_score x1 x2 x3 x4 0 1 (-1) 0) xs Hw Hm).
Qed.

(** [sample_contrast_cs_test4_difference24] (theorem).
 Mathematical meaning: For the fourth test score contrast and the second minus fourth test score contrast, a nonnegative-weight finite sample must satisfy the sharp squared covariance-versus-variance feasibility constraint. The coefficients determine a specific multi-test contrast pair relevant to finite composite-score stability checks.
 Exact checked proposition: forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->    batch_covariance w (four_batch_score x1 x2 x3 x4 0 0 0 1) (four_batch_score x1 x2 x3 x4 0 1 0 (-1)) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 0 0 0 1) (four_batch_score x1 x2 x3 x4 0 1 0 (-1)) xs    <= batch_variance w (four_batch_score x1 x2 x3 x4 0 0 0 1) xs * batch_variance w (four_batch_score x1 x2 x3 x4 0 1 0 (-1)) xs
 Premises and side conditions: Every listed outcome occurrence has nonnegative weight and the full sample mass is strictly positive. Repeated observations are counted with multiplicity. The two explicit score vectors are not assumed independent, jointly Gaussian or standardized.
 Proof/definition method: Specialize the shared kernel-checked finite-sample covariance Cauchy-Schwarz theorem to both explicit four-test score functions; no reproof or expansion of the weighted sum is performed.
 Library reuse: ListPoolingAlgebra and FourContrastCovariance own the covariance and contrast definitions; SampleContrastCauchy owns the general inequality; Rocq Stdlib real numbers and lists supply all operations.
 Boundary: Exact finite empirical covariance constraint on the named composites, not a separate distributional sampling law, population parameter estimate, chi-square pivot, normal tail or interval-coverage theorem.
*)
Theorem sample_contrast_cs_test4_difference24 :
 forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->
   batch_covariance w (four_batch_score x1 x2 x3 x4 0 0 0 1) (four_batch_score x1 x2 x3 x4 0 1 0 (-1)) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 0 0 0 1) (four_batch_score x1 x2 x3 x4 0 1 0 (-1)) xs
   <= batch_variance w (four_batch_score x1 x2 x3 x4 0 0 0 1) xs * batch_variance w (four_batch_score x1 x2 x3 x4 0 1 0 (-1)) xs.
Proof.
 intros A w x1 x2 x3 x4 xs Hw Hm.
 exact (sample_covariance_cauchy_schwarz A w
   (four_batch_score x1 x2 x3 x4 0 0 0 1) (four_batch_score x1 x2 x3 x4 0 1 0 (-1)) xs Hw Hm).
Qed.

(** [sample_contrast_cs_test4_difference34] (theorem).
 Mathematical meaning: For the fourth test score contrast and the third minus fourth test score contrast, a nonnegative-weight finite sample must satisfy the sharp squared covariance-versus-variance feasibility constraint. The coefficients determine a specific multi-test contrast pair relevant to finite composite-score stability checks.
 Exact checked proposition: forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->    batch_covariance w (four_batch_score x1 x2 x3 x4 0 0 0 1) (four_batch_score x1 x2 x3 x4 0 0 1 (-1)) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 0 0 0 1) (four_batch_score x1 x2 x3 x4 0 0 1 (-1)) xs    <= batch_variance w (four_batch_score x1 x2 x3 x4 0 0 0 1) xs * batch_variance w (four_batch_score x1 x2 x3 x4 0 0 1 (-1)) xs
 Premises and side conditions: Every listed outcome occurrence has nonnegative weight and the full sample mass is strictly positive. Repeated observations are counted with multiplicity. The two explicit score vectors are not assumed independent, jointly Gaussian or standardized.
 Proof/definition method: Specialize the shared kernel-checked finite-sample covariance Cauchy-Schwarz theorem to both explicit four-test score functions; no reproof or expansion of the weighted sum is performed.
 Library reuse: ListPoolingAlgebra and FourContrastCovariance own the covariance and contrast definitions; SampleContrastCauchy owns the general inequality; Rocq Stdlib real numbers and lists supply all operations.
 Boundary: Exact finite empirical covariance constraint on the named composites, not a separate distributional sampling law, population parameter estimate, chi-square pivot, normal tail or interval-coverage theorem.
*)
Theorem sample_contrast_cs_test4_difference34 :
 forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->
   batch_covariance w (four_batch_score x1 x2 x3 x4 0 0 0 1) (four_batch_score x1 x2 x3 x4 0 0 1 (-1)) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 0 0 0 1) (four_batch_score x1 x2 x3 x4 0 0 1 (-1)) xs
   <= batch_variance w (four_batch_score x1 x2 x3 x4 0 0 0 1) xs * batch_variance w (four_batch_score x1 x2 x3 x4 0 0 1 (-1)) xs.
Proof.
 intros A w x1 x2 x3 x4 xs Hw Hm.
 exact (sample_covariance_cauchy_schwarz A w
   (four_batch_score x1 x2 x3 x4 0 0 0 1) (four_batch_score x1 x2 x3 x4 0 0 1 (-1)) xs Hw Hm).
Qed.

(** [sample_contrast_cs_test4_triple123] (theorem).
 Mathematical meaning: For the fourth test score contrast and the first three tests score contrast, a nonnegative-weight finite sample must satisfy the sharp squared covariance-versus-variance feasibility constraint. The coefficients determine a specific multi-test contrast pair relevant to finite composite-score stability checks.
 Exact checked proposition: forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->    batch_covariance w (four_batch_score x1 x2 x3 x4 0 0 0 1) (four_batch_score x1 x2 x3 x4 1 1 1 0) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 0 0 0 1) (four_batch_score x1 x2 x3 x4 1 1 1 0) xs    <= batch_variance w (four_batch_score x1 x2 x3 x4 0 0 0 1) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 1 1 0) xs
 Premises and side conditions: Every listed outcome occurrence has nonnegative weight and the full sample mass is strictly positive. Repeated observations are counted with multiplicity. The two explicit score vectors are not assumed independent, jointly Gaussian or standardized.
 Proof/definition method: Specialize the shared kernel-checked finite-sample covariance Cauchy-Schwarz theorem to both explicit four-test score functions; no reproof or expansion of the weighted sum is performed.
 Library reuse: ListPoolingAlgebra and FourContrastCovariance own the covariance and contrast definitions; SampleContrastCauchy owns the general inequality; Rocq Stdlib real numbers and lists supply all operations.
 Boundary: Exact finite empirical covariance constraint on the named composites, not a separate distributional sampling law, population parameter estimate, chi-square pivot, normal tail or interval-coverage theorem.
*)
Theorem sample_contrast_cs_test4_triple123 :
 forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->
   batch_covariance w (four_batch_score x1 x2 x3 x4 0 0 0 1) (four_batch_score x1 x2 x3 x4 1 1 1 0) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 0 0 0 1) (four_batch_score x1 x2 x3 x4 1 1 1 0) xs
   <= batch_variance w (four_batch_score x1 x2 x3 x4 0 0 0 1) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 1 1 0) xs.
Proof.
 intros A w x1 x2 x3 x4 xs Hw Hm.
 exact (sample_covariance_cauchy_schwarz A w
   (four_batch_score x1 x2 x3 x4 0 0 0 1) (four_batch_score x1 x2 x3 x4 1 1 1 0) xs Hw Hm).
Qed.

(** [sample_contrast_cs_test4_triple124] (theorem).
 Mathematical meaning: For the fourth test score contrast and the tests one, two and four score contrast, a nonnegative-weight finite sample must satisfy the sharp squared covariance-versus-variance feasibility constraint. The coefficients determine a specific multi-test contrast pair relevant to finite composite-score stability checks.
 Exact checked proposition: forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->    batch_covariance w (four_batch_score x1 x2 x3 x4 0 0 0 1) (four_batch_score x1 x2 x3 x4 1 1 0 1) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 0 0 0 1) (four_batch_score x1 x2 x3 x4 1 1 0 1) xs    <= batch_variance w (four_batch_score x1 x2 x3 x4 0 0 0 1) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 1 0 1) xs
 Premises and side conditions: Every listed outcome occurrence has nonnegative weight and the full sample mass is strictly positive. Repeated observations are counted with multiplicity. The two explicit score vectors are not assumed independent, jointly Gaussian or standardized.
 Proof/definition method: Specialize the shared kernel-checked finite-sample covariance Cauchy-Schwarz theorem to both explicit four-test score functions; no reproof or expansion of the weighted sum is performed.
 Library reuse: ListPoolingAlgebra and FourContrastCovariance own the covariance and contrast definitions; SampleContrastCauchy owns the general inequality; Rocq Stdlib real numbers and lists supply all operations.
 Boundary: Exact finite empirical covariance constraint on the named composites, not a separate distributional sampling law, population parameter estimate, chi-square pivot, normal tail or interval-coverage theorem.
*)
Theorem sample_contrast_cs_test4_triple124 :
 forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->
   batch_covariance w (four_batch_score x1 x2 x3 x4 0 0 0 1) (four_batch_score x1 x2 x3 x4 1 1 0 1) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 0 0 0 1) (four_batch_score x1 x2 x3 x4 1 1 0 1) xs
   <= batch_variance w (four_batch_score x1 x2 x3 x4 0 0 0 1) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 1 0 1) xs.
Proof.
 intros A w x1 x2 x3 x4 xs Hw Hm.
 exact (sample_covariance_cauchy_schwarz A w
   (four_batch_score x1 x2 x3 x4 0 0 0 1) (four_batch_score x1 x2 x3 x4 1 1 0 1) xs Hw Hm).
Qed.

(** [sample_contrast_cs_test4_triple134] (theorem).
 Mathematical meaning: For the fourth test score contrast and the tests one, three and four score contrast, a nonnegative-weight finite sample must satisfy the sharp squared covariance-versus-variance feasibility constraint. The coefficients determine a specific multi-test contrast pair relevant to finite composite-score stability checks.
 Exact checked proposition: forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->    batch_covariance w (four_batch_score x1 x2 x3 x4 0 0 0 1) (four_batch_score x1 x2 x3 x4 1 0 1 1) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 0 0 0 1) (four_batch_score x1 x2 x3 x4 1 0 1 1) xs    <= batch_variance w (four_batch_score x1 x2 x3 x4 0 0 0 1) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 0 1 1) xs
 Premises and side conditions: Every listed outcome occurrence has nonnegative weight and the full sample mass is strictly positive. Repeated observations are counted with multiplicity. The two explicit score vectors are not assumed independent, jointly Gaussian or standardized.
 Proof/definition method: Specialize the shared kernel-checked finite-sample covariance Cauchy-Schwarz theorem to both explicit four-test score functions; no reproof or expansion of the weighted sum is performed.
 Library reuse: ListPoolingAlgebra and FourContrastCovariance own the covariance and contrast definitions; SampleContrastCauchy owns the general inequality; Rocq Stdlib real numbers and lists supply all operations.
 Boundary: Exact finite empirical covariance constraint on the named composites, not a separate distributional sampling law, population parameter estimate, chi-square pivot, normal tail or interval-coverage theorem.
*)
Theorem sample_contrast_cs_test4_triple134 :
 forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->
   batch_covariance w (four_batch_score x1 x2 x3 x4 0 0 0 1) (four_batch_score x1 x2 x3 x4 1 0 1 1) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 0 0 0 1) (four_batch_score x1 x2 x3 x4 1 0 1 1) xs
   <= batch_variance w (four_batch_score x1 x2 x3 x4 0 0 0 1) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 0 1 1) xs.
Proof.
 intros A w x1 x2 x3 x4 xs Hw Hm.
 exact (sample_covariance_cauchy_schwarz A w
   (four_batch_score x1 x2 x3 x4 0 0 0 1) (four_batch_score x1 x2 x3 x4 1 0 1 1) xs Hw Hm).
Qed.

(** [sample_contrast_cs_test4_triple234] (theorem).
 Mathematical meaning: For the fourth test score contrast and the last three tests score contrast, a nonnegative-weight finite sample must satisfy the sharp squared covariance-versus-variance feasibility constraint. The coefficients determine a specific multi-test contrast pair relevant to finite composite-score stability checks.
 Exact checked proposition: forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->    batch_covariance w (four_batch_score x1 x2 x3 x4 0 0 0 1) (four_batch_score x1 x2 x3 x4 0 1 1 1) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 0 0 0 1) (four_batch_score x1 x2 x3 x4 0 1 1 1) xs    <= batch_variance w (four_batch_score x1 x2 x3 x4 0 0 0 1) xs * batch_variance w (four_batch_score x1 x2 x3 x4 0 1 1 1) xs
 Premises and side conditions: Every listed outcome occurrence has nonnegative weight and the full sample mass is strictly positive. Repeated observations are counted with multiplicity. The two explicit score vectors are not assumed independent, jointly Gaussian or standardized.
 Proof/definition method: Specialize the shared kernel-checked finite-sample covariance Cauchy-Schwarz theorem to both explicit four-test score functions; no reproof or expansion of the weighted sum is performed.
 Library reuse: ListPoolingAlgebra and FourContrastCovariance own the covariance and contrast definitions; SampleContrastCauchy owns the general inequality; Rocq Stdlib real numbers and lists supply all operations.
 Boundary: Exact finite empirical covariance constraint on the named composites, not a separate distributional sampling law, population parameter estimate, chi-square pivot, normal tail or interval-coverage theorem.
*)
Theorem sample_contrast_cs_test4_triple234 :
 forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->
   batch_covariance w (four_batch_score x1 x2 x3 x4 0 0 0 1) (four_batch_score x1 x2 x3 x4 0 1 1 1) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 0 0 0 1) (four_batch_score x1 x2 x3 x4 0 1 1 1) xs
   <= batch_variance w (four_batch_score x1 x2 x3 x4 0 0 0 1) xs * batch_variance w (four_batch_score x1 x2 x3 x4 0 1 1 1) xs.
Proof.
 intros A w x1 x2 x3 x4 xs Hw Hm.
 exact (sample_covariance_cauchy_schwarz A w
   (four_batch_score x1 x2 x3 x4 0 0 0 1) (four_batch_score x1 x2 x3 x4 0 1 1 1) xs Hw Hm).
Qed.

(** [sample_contrast_cs_test4_allfour] (theorem).
 Mathematical meaning: For the fourth test score contrast and the all four tests score contrast, a nonnegative-weight finite sample must satisfy the sharp squared covariance-versus-variance feasibility constraint. The coefficients determine a specific multi-test contrast pair relevant to finite composite-score stability checks.
 Exact checked proposition: forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->    batch_covariance w (four_batch_score x1 x2 x3 x4 0 0 0 1) (four_batch_score x1 x2 x3 x4 1 1 1 1) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 0 0 0 1) (four_batch_score x1 x2 x3 x4 1 1 1 1) xs    <= batch_variance w (four_batch_score x1 x2 x3 x4 0 0 0 1) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 1 1 1) xs
 Premises and side conditions: Every listed outcome occurrence has nonnegative weight and the full sample mass is strictly positive. Repeated observations are counted with multiplicity. The two explicit score vectors are not assumed independent, jointly Gaussian or standardized.
 Proof/definition method: Specialize the shared kernel-checked finite-sample covariance Cauchy-Schwarz theorem to both explicit four-test score functions; no reproof or expansion of the weighted sum is performed.
 Library reuse: ListPoolingAlgebra and FourContrastCovariance own the covariance and contrast definitions; SampleContrastCauchy owns the general inequality; Rocq Stdlib real numbers and lists supply all operations.
 Boundary: Exact finite empirical covariance constraint on the named composites, not a separate distributional sampling law, population parameter estimate, chi-square pivot, normal tail or interval-coverage theorem.
*)
Theorem sample_contrast_cs_test4_allfour :
 forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->
   batch_covariance w (four_batch_score x1 x2 x3 x4 0 0 0 1) (four_batch_score x1 x2 x3 x4 1 1 1 1) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 0 0 0 1) (four_batch_score x1 x2 x3 x4 1 1 1 1) xs
   <= batch_variance w (four_batch_score x1 x2 x3 x4 0 0 0 1) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 1 1 1) xs.
Proof.
 intros A w x1 x2 x3 x4 xs Hw Hm.
 exact (sample_covariance_cauchy_schwarz A w
   (four_batch_score x1 x2 x3 x4 0 0 0 1) (four_batch_score x1 x2 x3 x4 1 1 1 1) xs Hw Hm).
Qed.

(** [sample_contrast_cs_test4_balanced12v34] (theorem).
 Mathematical meaning: For the fourth test score contrast and the difference between the two pairs score contrast, a nonnegative-weight finite sample must satisfy the sharp squared covariance-versus-variance feasibility constraint. The coefficients determine a specific multi-test contrast pair relevant to finite composite-score stability checks.
 Exact checked proposition: forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->    batch_covariance w (four_batch_score x1 x2 x3 x4 0 0 0 1) (four_batch_score x1 x2 x3 x4 1 1 (-1) (-1)) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 0 0 0 1) (four_batch_score x1 x2 x3 x4 1 1 (-1) (-1)) xs    <= batch_variance w (four_batch_score x1 x2 x3 x4 0 0 0 1) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 1 (-1) (-1)) xs
 Premises and side conditions: Every listed outcome occurrence has nonnegative weight and the full sample mass is strictly positive. Repeated observations are counted with multiplicity. The two explicit score vectors are not assumed independent, jointly Gaussian or standardized.
 Proof/definition method: Specialize the shared kernel-checked finite-sample covariance Cauchy-Schwarz theorem to both explicit four-test score functions; no reproof or expansion of the weighted sum is performed.
 Library reuse: ListPoolingAlgebra and FourContrastCovariance own the covariance and contrast definitions; SampleContrastCauchy owns the general inequality; Rocq Stdlib real numbers and lists supply all operations.
 Boundary: Exact finite empirical covariance constraint on the named composites, not a separate distributional sampling law, population parameter estimate, chi-square pivot, normal tail or interval-coverage theorem.
*)
Theorem sample_contrast_cs_test4_balanced12v34 :
 forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->
   batch_covariance w (four_batch_score x1 x2 x3 x4 0 0 0 1) (four_batch_score x1 x2 x3 x4 1 1 (-1) (-1)) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 0 0 0 1) (four_batch_score x1 x2 x3 x4 1 1 (-1) (-1)) xs
   <= batch_variance w (four_batch_score x1 x2 x3 x4 0 0 0 1) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 1 (-1) (-1)) xs.
Proof.
 intros A w x1 x2 x3 x4 xs Hw Hm.
 exact (sample_covariance_cauchy_schwarz A w
   (four_batch_score x1 x2 x3 x4 0 0 0 1) (four_batch_score x1 x2 x3 x4 1 1 (-1) (-1)) xs Hw Hm).
Qed.

(** [sample_contrast_cs_difference12_difference12] (theorem).
 Mathematical meaning: For the first minus second test score contrast and the first minus second test score contrast, a nonnegative-weight finite sample must satisfy the sharp squared covariance-versus-variance feasibility constraint. The coefficients determine a specific multi-test contrast pair relevant to finite composite-score stability checks.
 Exact checked proposition: forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->    batch_covariance w (four_batch_score x1 x2 x3 x4 1 (-1) 0 0) (four_batch_score x1 x2 x3 x4 1 (-1) 0 0) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 1 (-1) 0 0) (four_batch_score x1 x2 x3 x4 1 (-1) 0 0) xs    <= batch_variance w (four_batch_score x1 x2 x3 x4 1 (-1) 0 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 (-1) 0 0) xs
 Premises and side conditions: Every listed outcome occurrence has nonnegative weight and the full sample mass is strictly positive. Repeated observations are counted with multiplicity. The two explicit score vectors are not assumed independent, jointly Gaussian or standardized.
 Proof/definition method: Specialize the shared kernel-checked finite-sample covariance Cauchy-Schwarz theorem to both explicit four-test score functions; no reproof or expansion of the weighted sum is performed.
 Library reuse: ListPoolingAlgebra and FourContrastCovariance own the covariance and contrast definitions; SampleContrastCauchy owns the general inequality; Rocq Stdlib real numbers and lists supply all operations.
 Boundary: Exact finite empirical covariance constraint on the named composites, not a separate distributional sampling law, population parameter estimate, chi-square pivot, normal tail or interval-coverage theorem.
*)
Theorem sample_contrast_cs_difference12_difference12 :
 forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->
   batch_covariance w (four_batch_score x1 x2 x3 x4 1 (-1) 0 0) (four_batch_score x1 x2 x3 x4 1 (-1) 0 0) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 1 (-1) 0 0) (four_batch_score x1 x2 x3 x4 1 (-1) 0 0) xs
   <= batch_variance w (four_batch_score x1 x2 x3 x4 1 (-1) 0 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 (-1) 0 0) xs.
Proof.
 intros A w x1 x2 x3 x4 xs Hw Hm.
 exact (sample_covariance_cauchy_schwarz A w
   (four_batch_score x1 x2 x3 x4 1 (-1) 0 0) (four_batch_score x1 x2 x3 x4 1 (-1) 0 0) xs Hw Hm).
Qed.

(** [sample_contrast_cs_difference12_difference13] (theorem).
 Mathematical meaning: For the first minus second test score contrast and the first minus third test score contrast, a nonnegative-weight finite sample must satisfy the sharp squared covariance-versus-variance feasibility constraint. The coefficients determine a specific multi-test contrast pair relevant to finite composite-score stability checks.
 Exact checked proposition: forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->    batch_covariance w (four_batch_score x1 x2 x3 x4 1 (-1) 0 0) (four_batch_score x1 x2 x3 x4 1 0 (-1) 0) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 1 (-1) 0 0) (four_batch_score x1 x2 x3 x4 1 0 (-1) 0) xs    <= batch_variance w (four_batch_score x1 x2 x3 x4 1 (-1) 0 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 0 (-1) 0) xs
 Premises and side conditions: Every listed outcome occurrence has nonnegative weight and the full sample mass is strictly positive. Repeated observations are counted with multiplicity. The two explicit score vectors are not assumed independent, jointly Gaussian or standardized.
 Proof/definition method: Specialize the shared kernel-checked finite-sample covariance Cauchy-Schwarz theorem to both explicit four-test score functions; no reproof or expansion of the weighted sum is performed.
 Library reuse: ListPoolingAlgebra and FourContrastCovariance own the covariance and contrast definitions; SampleContrastCauchy owns the general inequality; Rocq Stdlib real numbers and lists supply all operations.
 Boundary: Exact finite empirical covariance constraint on the named composites, not a separate distributional sampling law, population parameter estimate, chi-square pivot, normal tail or interval-coverage theorem.
*)
Theorem sample_contrast_cs_difference12_difference13 :
 forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->
   batch_covariance w (four_batch_score x1 x2 x3 x4 1 (-1) 0 0) (four_batch_score x1 x2 x3 x4 1 0 (-1) 0) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 1 (-1) 0 0) (four_batch_score x1 x2 x3 x4 1 0 (-1) 0) xs
   <= batch_variance w (four_batch_score x1 x2 x3 x4 1 (-1) 0 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 0 (-1) 0) xs.
Proof.
 intros A w x1 x2 x3 x4 xs Hw Hm.
 exact (sample_covariance_cauchy_schwarz A w
   (four_batch_score x1 x2 x3 x4 1 (-1) 0 0) (four_batch_score x1 x2 x3 x4 1 0 (-1) 0) xs Hw Hm).
Qed.

(** [sample_contrast_cs_difference12_difference14] (theorem).
 Mathematical meaning: For the first minus second test score contrast and the first minus fourth test score contrast, a nonnegative-weight finite sample must satisfy the sharp squared covariance-versus-variance feasibility constraint. The coefficients determine a specific multi-test contrast pair relevant to finite composite-score stability checks.
 Exact checked proposition: forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->    batch_covariance w (four_batch_score x1 x2 x3 x4 1 (-1) 0 0) (four_batch_score x1 x2 x3 x4 1 0 0 (-1)) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 1 (-1) 0 0) (four_batch_score x1 x2 x3 x4 1 0 0 (-1)) xs    <= batch_variance w (four_batch_score x1 x2 x3 x4 1 (-1) 0 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 0 0 (-1)) xs
 Premises and side conditions: Every listed outcome occurrence has nonnegative weight and the full sample mass is strictly positive. Repeated observations are counted with multiplicity. The two explicit score vectors are not assumed independent, jointly Gaussian or standardized.
 Proof/definition method: Specialize the shared kernel-checked finite-sample covariance Cauchy-Schwarz theorem to both explicit four-test score functions; no reproof or expansion of the weighted sum is performed.
 Library reuse: ListPoolingAlgebra and FourContrastCovariance own the covariance and contrast definitions; SampleContrastCauchy owns the general inequality; Rocq Stdlib real numbers and lists supply all operations.
 Boundary: Exact finite empirical covariance constraint on the named composites, not a separate distributional sampling law, population parameter estimate, chi-square pivot, normal tail or interval-coverage theorem.
*)
Theorem sample_contrast_cs_difference12_difference14 :
 forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->
   batch_covariance w (four_batch_score x1 x2 x3 x4 1 (-1) 0 0) (four_batch_score x1 x2 x3 x4 1 0 0 (-1)) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 1 (-1) 0 0) (four_batch_score x1 x2 x3 x4 1 0 0 (-1)) xs
   <= batch_variance w (four_batch_score x1 x2 x3 x4 1 (-1) 0 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 0 0 (-1)) xs.
Proof.
 intros A w x1 x2 x3 x4 xs Hw Hm.
 exact (sample_covariance_cauchy_schwarz A w
   (four_batch_score x1 x2 x3 x4 1 (-1) 0 0) (four_batch_score x1 x2 x3 x4 1 0 0 (-1)) xs Hw Hm).
Qed.

(** [sample_contrast_cs_difference12_difference23] (theorem).
 Mathematical meaning: For the first minus second test score contrast and the second minus third test score contrast, a nonnegative-weight finite sample must satisfy the sharp squared covariance-versus-variance feasibility constraint. The coefficients determine a specific multi-test contrast pair relevant to finite composite-score stability checks.
 Exact checked proposition: forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->    batch_covariance w (four_batch_score x1 x2 x3 x4 1 (-1) 0 0) (four_batch_score x1 x2 x3 x4 0 1 (-1) 0) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 1 (-1) 0 0) (four_batch_score x1 x2 x3 x4 0 1 (-1) 0) xs    <= batch_variance w (four_batch_score x1 x2 x3 x4 1 (-1) 0 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 0 1 (-1) 0) xs
 Premises and side conditions: Every listed outcome occurrence has nonnegative weight and the full sample mass is strictly positive. Repeated observations are counted with multiplicity. The two explicit score vectors are not assumed independent, jointly Gaussian or standardized.
 Proof/definition method: Specialize the shared kernel-checked finite-sample covariance Cauchy-Schwarz theorem to both explicit four-test score functions; no reproof or expansion of the weighted sum is performed.
 Library reuse: ListPoolingAlgebra and FourContrastCovariance own the covariance and contrast definitions; SampleContrastCauchy owns the general inequality; Rocq Stdlib real numbers and lists supply all operations.
 Boundary: Exact finite empirical covariance constraint on the named composites, not a separate distributional sampling law, population parameter estimate, chi-square pivot, normal tail or interval-coverage theorem.
*)
Theorem sample_contrast_cs_difference12_difference23 :
 forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->
   batch_covariance w (four_batch_score x1 x2 x3 x4 1 (-1) 0 0) (four_batch_score x1 x2 x3 x4 0 1 (-1) 0) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 1 (-1) 0 0) (four_batch_score x1 x2 x3 x4 0 1 (-1) 0) xs
   <= batch_variance w (four_batch_score x1 x2 x3 x4 1 (-1) 0 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 0 1 (-1) 0) xs.
Proof.
 intros A w x1 x2 x3 x4 xs Hw Hm.
 exact (sample_covariance_cauchy_schwarz A w
   (four_batch_score x1 x2 x3 x4 1 (-1) 0 0) (four_batch_score x1 x2 x3 x4 0 1 (-1) 0) xs Hw Hm).
Qed.

(** [sample_contrast_cs_difference12_difference24] (theorem).
 Mathematical meaning: For the first minus second test score contrast and the second minus fourth test score contrast, a nonnegative-weight finite sample must satisfy the sharp squared covariance-versus-variance feasibility constraint. The coefficients determine a specific multi-test contrast pair relevant to finite composite-score stability checks.
 Exact checked proposition: forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->    batch_covariance w (four_batch_score x1 x2 x3 x4 1 (-1) 0 0) (four_batch_score x1 x2 x3 x4 0 1 0 (-1)) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 1 (-1) 0 0) (four_batch_score x1 x2 x3 x4 0 1 0 (-1)) xs    <= batch_variance w (four_batch_score x1 x2 x3 x4 1 (-1) 0 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 0 1 0 (-1)) xs
 Premises and side conditions: Every listed outcome occurrence has nonnegative weight and the full sample mass is strictly positive. Repeated observations are counted with multiplicity. The two explicit score vectors are not assumed independent, jointly Gaussian or standardized.
 Proof/definition method: Specialize the shared kernel-checked finite-sample covariance Cauchy-Schwarz theorem to both explicit four-test score functions; no reproof or expansion of the weighted sum is performed.
 Library reuse: ListPoolingAlgebra and FourContrastCovariance own the covariance and contrast definitions; SampleContrastCauchy owns the general inequality; Rocq Stdlib real numbers and lists supply all operations.
 Boundary: Exact finite empirical covariance constraint on the named composites, not a separate distributional sampling law, population parameter estimate, chi-square pivot, normal tail or interval-coverage theorem.
*)
Theorem sample_contrast_cs_difference12_difference24 :
 forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->
   batch_covariance w (four_batch_score x1 x2 x3 x4 1 (-1) 0 0) (four_batch_score x1 x2 x3 x4 0 1 0 (-1)) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 1 (-1) 0 0) (four_batch_score x1 x2 x3 x4 0 1 0 (-1)) xs
   <= batch_variance w (four_batch_score x1 x2 x3 x4 1 (-1) 0 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 0 1 0 (-1)) xs.
Proof.
 intros A w x1 x2 x3 x4 xs Hw Hm.
 exact (sample_covariance_cauchy_schwarz A w
   (four_batch_score x1 x2 x3 x4 1 (-1) 0 0) (four_batch_score x1 x2 x3 x4 0 1 0 (-1)) xs Hw Hm).
Qed.

(** [sample_contrast_cs_difference12_difference34] (theorem).
 Mathematical meaning: For the first minus second test score contrast and the third minus fourth test score contrast, a nonnegative-weight finite sample must satisfy the sharp squared covariance-versus-variance feasibility constraint. The coefficients determine a specific multi-test contrast pair relevant to finite composite-score stability checks.
 Exact checked proposition: forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->    batch_covariance w (four_batch_score x1 x2 x3 x4 1 (-1) 0 0) (four_batch_score x1 x2 x3 x4 0 0 1 (-1)) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 1 (-1) 0 0) (four_batch_score x1 x2 x3 x4 0 0 1 (-1)) xs    <= batch_variance w (four_batch_score x1 x2 x3 x4 1 (-1) 0 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 0 0 1 (-1)) xs
 Premises and side conditions: Every listed outcome occurrence has nonnegative weight and the full sample mass is strictly positive. Repeated observations are counted with multiplicity. The two explicit score vectors are not assumed independent, jointly Gaussian or standardized.
 Proof/definition method: Specialize the shared kernel-checked finite-sample covariance Cauchy-Schwarz theorem to both explicit four-test score functions; no reproof or expansion of the weighted sum is performed.
 Library reuse: ListPoolingAlgebra and FourContrastCovariance own the covariance and contrast definitions; SampleContrastCauchy owns the general inequality; Rocq Stdlib real numbers and lists supply all operations.
 Boundary: Exact finite empirical covariance constraint on the named composites, not a separate distributional sampling law, population parameter estimate, chi-square pivot, normal tail or interval-coverage theorem.
*)
Theorem sample_contrast_cs_difference12_difference34 :
 forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->
   batch_covariance w (four_batch_score x1 x2 x3 x4 1 (-1) 0 0) (four_batch_score x1 x2 x3 x4 0 0 1 (-1)) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 1 (-1) 0 0) (four_batch_score x1 x2 x3 x4 0 0 1 (-1)) xs
   <= batch_variance w (four_batch_score x1 x2 x3 x4 1 (-1) 0 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 0 0 1 (-1)) xs.
Proof.
 intros A w x1 x2 x3 x4 xs Hw Hm.
 exact (sample_covariance_cauchy_schwarz A w
   (four_batch_score x1 x2 x3 x4 1 (-1) 0 0) (four_batch_score x1 x2 x3 x4 0 0 1 (-1)) xs Hw Hm).
Qed.

(** [sample_contrast_cs_difference12_triple123] (theorem).
 Mathematical meaning: For the first minus second test score contrast and the first three tests score contrast, a nonnegative-weight finite sample must satisfy the sharp squared covariance-versus-variance feasibility constraint. The coefficients determine a specific multi-test contrast pair relevant to finite composite-score stability checks.
 Exact checked proposition: forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->    batch_covariance w (four_batch_score x1 x2 x3 x4 1 (-1) 0 0) (four_batch_score x1 x2 x3 x4 1 1 1 0) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 1 (-1) 0 0) (four_batch_score x1 x2 x3 x4 1 1 1 0) xs    <= batch_variance w (four_batch_score x1 x2 x3 x4 1 (-1) 0 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 1 1 0) xs
 Premises and side conditions: Every listed outcome occurrence has nonnegative weight and the full sample mass is strictly positive. Repeated observations are counted with multiplicity. The two explicit score vectors are not assumed independent, jointly Gaussian or standardized.
 Proof/definition method: Specialize the shared kernel-checked finite-sample covariance Cauchy-Schwarz theorem to both explicit four-test score functions; no reproof or expansion of the weighted sum is performed.
 Library reuse: ListPoolingAlgebra and FourContrastCovariance own the covariance and contrast definitions; SampleContrastCauchy owns the general inequality; Rocq Stdlib real numbers and lists supply all operations.
 Boundary: Exact finite empirical covariance constraint on the named composites, not a separate distributional sampling law, population parameter estimate, chi-square pivot, normal tail or interval-coverage theorem.
*)
Theorem sample_contrast_cs_difference12_triple123 :
 forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->
   batch_covariance w (four_batch_score x1 x2 x3 x4 1 (-1) 0 0) (four_batch_score x1 x2 x3 x4 1 1 1 0) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 1 (-1) 0 0) (four_batch_score x1 x2 x3 x4 1 1 1 0) xs
   <= batch_variance w (four_batch_score x1 x2 x3 x4 1 (-1) 0 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 1 1 0) xs.
Proof.
 intros A w x1 x2 x3 x4 xs Hw Hm.
 exact (sample_covariance_cauchy_schwarz A w
   (four_batch_score x1 x2 x3 x4 1 (-1) 0 0) (four_batch_score x1 x2 x3 x4 1 1 1 0) xs Hw Hm).
Qed.

(** [sample_contrast_cs_difference12_triple124] (theorem).
 Mathematical meaning: For the first minus second test score contrast and the tests one, two and four score contrast, a nonnegative-weight finite sample must satisfy the sharp squared covariance-versus-variance feasibility constraint. The coefficients determine a specific multi-test contrast pair relevant to finite composite-score stability checks.
 Exact checked proposition: forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->    batch_covariance w (four_batch_score x1 x2 x3 x4 1 (-1) 0 0) (four_batch_score x1 x2 x3 x4 1 1 0 1) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 1 (-1) 0 0) (four_batch_score x1 x2 x3 x4 1 1 0 1) xs    <= batch_variance w (four_batch_score x1 x2 x3 x4 1 (-1) 0 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 1 0 1) xs
 Premises and side conditions: Every listed outcome occurrence has nonnegative weight and the full sample mass is strictly positive. Repeated observations are counted with multiplicity. The two explicit score vectors are not assumed independent, jointly Gaussian or standardized.
 Proof/definition method: Specialize the shared kernel-checked finite-sample covariance Cauchy-Schwarz theorem to both explicit four-test score functions; no reproof or expansion of the weighted sum is performed.
 Library reuse: ListPoolingAlgebra and FourContrastCovariance own the covariance and contrast definitions; SampleContrastCauchy owns the general inequality; Rocq Stdlib real numbers and lists supply all operations.
 Boundary: Exact finite empirical covariance constraint on the named composites, not a separate distributional sampling law, population parameter estimate, chi-square pivot, normal tail or interval-coverage theorem.
*)
Theorem sample_contrast_cs_difference12_triple124 :
 forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->
   batch_covariance w (four_batch_score x1 x2 x3 x4 1 (-1) 0 0) (four_batch_score x1 x2 x3 x4 1 1 0 1) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 1 (-1) 0 0) (four_batch_score x1 x2 x3 x4 1 1 0 1) xs
   <= batch_variance w (four_batch_score x1 x2 x3 x4 1 (-1) 0 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 1 0 1) xs.
Proof.
 intros A w x1 x2 x3 x4 xs Hw Hm.
 exact (sample_covariance_cauchy_schwarz A w
   (four_batch_score x1 x2 x3 x4 1 (-1) 0 0) (four_batch_score x1 x2 x3 x4 1 1 0 1) xs Hw Hm).
Qed.

(** [sample_contrast_cs_difference12_triple134] (theorem).
 Mathematical meaning: For the first minus second test score contrast and the tests one, three and four score contrast, a nonnegative-weight finite sample must satisfy the sharp squared covariance-versus-variance feasibility constraint. The coefficients determine a specific multi-test contrast pair relevant to finite composite-score stability checks.
 Exact checked proposition: forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->    batch_covariance w (four_batch_score x1 x2 x3 x4 1 (-1) 0 0) (four_batch_score x1 x2 x3 x4 1 0 1 1) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 1 (-1) 0 0) (four_batch_score x1 x2 x3 x4 1 0 1 1) xs    <= batch_variance w (four_batch_score x1 x2 x3 x4 1 (-1) 0 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 0 1 1) xs
 Premises and side conditions: Every listed outcome occurrence has nonnegative weight and the full sample mass is strictly positive. Repeated observations are counted with multiplicity. The two explicit score vectors are not assumed independent, jointly Gaussian or standardized.
 Proof/definition method: Specialize the shared kernel-checked finite-sample covariance Cauchy-Schwarz theorem to both explicit four-test score functions; no reproof or expansion of the weighted sum is performed.
 Library reuse: ListPoolingAlgebra and FourContrastCovariance own the covariance and contrast definitions; SampleContrastCauchy owns the general inequality; Rocq Stdlib real numbers and lists supply all operations.
 Boundary: Exact finite empirical covariance constraint on the named composites, not a separate distributional sampling law, population parameter estimate, chi-square pivot, normal tail or interval-coverage theorem.
*)
Theorem sample_contrast_cs_difference12_triple134 :
 forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->
   batch_covariance w (four_batch_score x1 x2 x3 x4 1 (-1) 0 0) (four_batch_score x1 x2 x3 x4 1 0 1 1) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 1 (-1) 0 0) (four_batch_score x1 x2 x3 x4 1 0 1 1) xs
   <= batch_variance w (four_batch_score x1 x2 x3 x4 1 (-1) 0 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 0 1 1) xs.
Proof.
 intros A w x1 x2 x3 x4 xs Hw Hm.
 exact (sample_covariance_cauchy_schwarz A w
   (four_batch_score x1 x2 x3 x4 1 (-1) 0 0) (four_batch_score x1 x2 x3 x4 1 0 1 1) xs Hw Hm).
Qed.

(** [sample_contrast_cs_difference12_triple234] (theorem).
 Mathematical meaning: For the first minus second test score contrast and the last three tests score contrast, a nonnegative-weight finite sample must satisfy the sharp squared covariance-versus-variance feasibility constraint. The coefficients determine a specific multi-test contrast pair relevant to finite composite-score stability checks.
 Exact checked proposition: forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->    batch_covariance w (four_batch_score x1 x2 x3 x4 1 (-1) 0 0) (four_batch_score x1 x2 x3 x4 0 1 1 1) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 1 (-1) 0 0) (four_batch_score x1 x2 x3 x4 0 1 1 1) xs    <= batch_variance w (four_batch_score x1 x2 x3 x4 1 (-1) 0 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 0 1 1 1) xs
 Premises and side conditions: Every listed outcome occurrence has nonnegative weight and the full sample mass is strictly positive. Repeated observations are counted with multiplicity. The two explicit score vectors are not assumed independent, jointly Gaussian or standardized.
 Proof/definition method: Specialize the shared kernel-checked finite-sample covariance Cauchy-Schwarz theorem to both explicit four-test score functions; no reproof or expansion of the weighted sum is performed.
 Library reuse: ListPoolingAlgebra and FourContrastCovariance own the covariance and contrast definitions; SampleContrastCauchy owns the general inequality; Rocq Stdlib real numbers and lists supply all operations.
 Boundary: Exact finite empirical covariance constraint on the named composites, not a separate distributional sampling law, population parameter estimate, chi-square pivot, normal tail or interval-coverage theorem.
*)
Theorem sample_contrast_cs_difference12_triple234 :
 forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->
   batch_covariance w (four_batch_score x1 x2 x3 x4 1 (-1) 0 0) (four_batch_score x1 x2 x3 x4 0 1 1 1) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 1 (-1) 0 0) (four_batch_score x1 x2 x3 x4 0 1 1 1) xs
   <= batch_variance w (four_batch_score x1 x2 x3 x4 1 (-1) 0 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 0 1 1 1) xs.
Proof.
 intros A w x1 x2 x3 x4 xs Hw Hm.
 exact (sample_covariance_cauchy_schwarz A w
   (four_batch_score x1 x2 x3 x4 1 (-1) 0 0) (four_batch_score x1 x2 x3 x4 0 1 1 1) xs Hw Hm).
Qed.

(** [sample_contrast_cs_difference12_allfour] (theorem).
 Mathematical meaning: For the first minus second test score contrast and the all four tests score contrast, a nonnegative-weight finite sample must satisfy the sharp squared covariance-versus-variance feasibility constraint. The coefficients determine a specific multi-test contrast pair relevant to finite composite-score stability checks.
 Exact checked proposition: forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->    batch_covariance w (four_batch_score x1 x2 x3 x4 1 (-1) 0 0) (four_batch_score x1 x2 x3 x4 1 1 1 1) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 1 (-1) 0 0) (four_batch_score x1 x2 x3 x4 1 1 1 1) xs    <= batch_variance w (four_batch_score x1 x2 x3 x4 1 (-1) 0 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 1 1 1) xs
 Premises and side conditions: Every listed outcome occurrence has nonnegative weight and the full sample mass is strictly positive. Repeated observations are counted with multiplicity. The two explicit score vectors are not assumed independent, jointly Gaussian or standardized.
 Proof/definition method: Specialize the shared kernel-checked finite-sample covariance Cauchy-Schwarz theorem to both explicit four-test score functions; no reproof or expansion of the weighted sum is performed.
 Library reuse: ListPoolingAlgebra and FourContrastCovariance own the covariance and contrast definitions; SampleContrastCauchy owns the general inequality; Rocq Stdlib real numbers and lists supply all operations.
 Boundary: Exact finite empirical covariance constraint on the named composites, not a separate distributional sampling law, population parameter estimate, chi-square pivot, normal tail or interval-coverage theorem.
*)
Theorem sample_contrast_cs_difference12_allfour :
 forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->
   batch_covariance w (four_batch_score x1 x2 x3 x4 1 (-1) 0 0) (four_batch_score x1 x2 x3 x4 1 1 1 1) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 1 (-1) 0 0) (four_batch_score x1 x2 x3 x4 1 1 1 1) xs
   <= batch_variance w (four_batch_score x1 x2 x3 x4 1 (-1) 0 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 1 1 1) xs.
Proof.
 intros A w x1 x2 x3 x4 xs Hw Hm.
 exact (sample_covariance_cauchy_schwarz A w
   (four_batch_score x1 x2 x3 x4 1 (-1) 0 0) (four_batch_score x1 x2 x3 x4 1 1 1 1) xs Hw Hm).
Qed.

(** [sample_contrast_cs_difference12_balanced12v34] (theorem).
 Mathematical meaning: For the first minus second test score contrast and the difference between the two pairs score contrast, a nonnegative-weight finite sample must satisfy the sharp squared covariance-versus-variance feasibility constraint. The coefficients determine a specific multi-test contrast pair relevant to finite composite-score stability checks.
 Exact checked proposition: forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->    batch_covariance w (four_batch_score x1 x2 x3 x4 1 (-1) 0 0) (four_batch_score x1 x2 x3 x4 1 1 (-1) (-1)) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 1 (-1) 0 0) (four_batch_score x1 x2 x3 x4 1 1 (-1) (-1)) xs    <= batch_variance w (four_batch_score x1 x2 x3 x4 1 (-1) 0 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 1 (-1) (-1)) xs
 Premises and side conditions: Every listed outcome occurrence has nonnegative weight and the full sample mass is strictly positive. Repeated observations are counted with multiplicity. The two explicit score vectors are not assumed independent, jointly Gaussian or standardized.
 Proof/definition method: Specialize the shared kernel-checked finite-sample covariance Cauchy-Schwarz theorem to both explicit four-test score functions; no reproof or expansion of the weighted sum is performed.
 Library reuse: ListPoolingAlgebra and FourContrastCovariance own the covariance and contrast definitions; SampleContrastCauchy owns the general inequality; Rocq Stdlib real numbers and lists supply all operations.
 Boundary: Exact finite empirical covariance constraint on the named composites, not a separate distributional sampling law, population parameter estimate, chi-square pivot, normal tail or interval-coverage theorem.
*)
Theorem sample_contrast_cs_difference12_balanced12v34 :
 forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->
   batch_covariance w (four_batch_score x1 x2 x3 x4 1 (-1) 0 0) (four_batch_score x1 x2 x3 x4 1 1 (-1) (-1)) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 1 (-1) 0 0) (four_batch_score x1 x2 x3 x4 1 1 (-1) (-1)) xs
   <= batch_variance w (four_batch_score x1 x2 x3 x4 1 (-1) 0 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 1 (-1) (-1)) xs.
Proof.
 intros A w x1 x2 x3 x4 xs Hw Hm.
 exact (sample_covariance_cauchy_schwarz A w
   (four_batch_score x1 x2 x3 x4 1 (-1) 0 0) (four_batch_score x1 x2 x3 x4 1 1 (-1) (-1)) xs Hw Hm).
Qed.

(** [sample_contrast_cs_difference13_difference13] (theorem).
 Mathematical meaning: For the first minus third test score contrast and the first minus third test score contrast, a nonnegative-weight finite sample must satisfy the sharp squared covariance-versus-variance feasibility constraint. The coefficients determine a specific multi-test contrast pair relevant to finite composite-score stability checks.
 Exact checked proposition: forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->    batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 (-1) 0) (four_batch_score x1 x2 x3 x4 1 0 (-1) 0) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 (-1) 0) (four_batch_score x1 x2 x3 x4 1 0 (-1) 0) xs    <= batch_variance w (four_batch_score x1 x2 x3 x4 1 0 (-1) 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 0 (-1) 0) xs
 Premises and side conditions: Every listed outcome occurrence has nonnegative weight and the full sample mass is strictly positive. Repeated observations are counted with multiplicity. The two explicit score vectors are not assumed independent, jointly Gaussian or standardized.
 Proof/definition method: Specialize the shared kernel-checked finite-sample covariance Cauchy-Schwarz theorem to both explicit four-test score functions; no reproof or expansion of the weighted sum is performed.
 Library reuse: ListPoolingAlgebra and FourContrastCovariance own the covariance and contrast definitions; SampleContrastCauchy owns the general inequality; Rocq Stdlib real numbers and lists supply all operations.
 Boundary: Exact finite empirical covariance constraint on the named composites, not a separate distributional sampling law, population parameter estimate, chi-square pivot, normal tail or interval-coverage theorem.
*)
Theorem sample_contrast_cs_difference13_difference13 :
 forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->
   batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 (-1) 0) (four_batch_score x1 x2 x3 x4 1 0 (-1) 0) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 (-1) 0) (four_batch_score x1 x2 x3 x4 1 0 (-1) 0) xs
   <= batch_variance w (four_batch_score x1 x2 x3 x4 1 0 (-1) 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 0 (-1) 0) xs.
Proof.
 intros A w x1 x2 x3 x4 xs Hw Hm.
 exact (sample_covariance_cauchy_schwarz A w
   (four_batch_score x1 x2 x3 x4 1 0 (-1) 0) (four_batch_score x1 x2 x3 x4 1 0 (-1) 0) xs Hw Hm).
Qed.

(** [sample_contrast_cs_difference13_difference14] (theorem).
 Mathematical meaning: For the first minus third test score contrast and the first minus fourth test score contrast, a nonnegative-weight finite sample must satisfy the sharp squared covariance-versus-variance feasibility constraint. The coefficients determine a specific multi-test contrast pair relevant to finite composite-score stability checks.
 Exact checked proposition: forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->    batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 (-1) 0) (four_batch_score x1 x2 x3 x4 1 0 0 (-1)) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 (-1) 0) (four_batch_score x1 x2 x3 x4 1 0 0 (-1)) xs    <= batch_variance w (four_batch_score x1 x2 x3 x4 1 0 (-1) 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 0 0 (-1)) xs
 Premises and side conditions: Every listed outcome occurrence has nonnegative weight and the full sample mass is strictly positive. Repeated observations are counted with multiplicity. The two explicit score vectors are not assumed independent, jointly Gaussian or standardized.
 Proof/definition method: Specialize the shared kernel-checked finite-sample covariance Cauchy-Schwarz theorem to both explicit four-test score functions; no reproof or expansion of the weighted sum is performed.
 Library reuse: ListPoolingAlgebra and FourContrastCovariance own the covariance and contrast definitions; SampleContrastCauchy owns the general inequality; Rocq Stdlib real numbers and lists supply all operations.
 Boundary: Exact finite empirical covariance constraint on the named composites, not a separate distributional sampling law, population parameter estimate, chi-square pivot, normal tail or interval-coverage theorem.
*)
Theorem sample_contrast_cs_difference13_difference14 :
 forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->
   batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 (-1) 0) (four_batch_score x1 x2 x3 x4 1 0 0 (-1)) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 (-1) 0) (four_batch_score x1 x2 x3 x4 1 0 0 (-1)) xs
   <= batch_variance w (four_batch_score x1 x2 x3 x4 1 0 (-1) 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 0 0 (-1)) xs.
Proof.
 intros A w x1 x2 x3 x4 xs Hw Hm.
 exact (sample_covariance_cauchy_schwarz A w
   (four_batch_score x1 x2 x3 x4 1 0 (-1) 0) (four_batch_score x1 x2 x3 x4 1 0 0 (-1)) xs Hw Hm).
Qed.

(** [sample_contrast_cs_difference13_difference23] (theorem).
 Mathematical meaning: For the first minus third test score contrast and the second minus third test score contrast, a nonnegative-weight finite sample must satisfy the sharp squared covariance-versus-variance feasibility constraint. The coefficients determine a specific multi-test contrast pair relevant to finite composite-score stability checks.
 Exact checked proposition: forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->    batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 (-1) 0) (four_batch_score x1 x2 x3 x4 0 1 (-1) 0) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 (-1) 0) (four_batch_score x1 x2 x3 x4 0 1 (-1) 0) xs    <= batch_variance w (four_batch_score x1 x2 x3 x4 1 0 (-1) 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 0 1 (-1) 0) xs
 Premises and side conditions: Every listed outcome occurrence has nonnegative weight and the full sample mass is strictly positive. Repeated observations are counted with multiplicity. The two explicit score vectors are not assumed independent, jointly Gaussian or standardized.
 Proof/definition method: Specialize the shared kernel-checked finite-sample covariance Cauchy-Schwarz theorem to both explicit four-test score functions; no reproof or expansion of the weighted sum is performed.
 Library reuse: ListPoolingAlgebra and FourContrastCovariance own the covariance and contrast definitions; SampleContrastCauchy owns the general inequality; Rocq Stdlib real numbers and lists supply all operations.
 Boundary: Exact finite empirical covariance constraint on the named composites, not a separate distributional sampling law, population parameter estimate, chi-square pivot, normal tail or interval-coverage theorem.
*)
Theorem sample_contrast_cs_difference13_difference23 :
 forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->
   batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 (-1) 0) (four_batch_score x1 x2 x3 x4 0 1 (-1) 0) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 (-1) 0) (four_batch_score x1 x2 x3 x4 0 1 (-1) 0) xs
   <= batch_variance w (four_batch_score x1 x2 x3 x4 1 0 (-1) 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 0 1 (-1) 0) xs.
Proof.
 intros A w x1 x2 x3 x4 xs Hw Hm.
 exact (sample_covariance_cauchy_schwarz A w
   (four_batch_score x1 x2 x3 x4 1 0 (-1) 0) (four_batch_score x1 x2 x3 x4 0 1 (-1) 0) xs Hw Hm).
Qed.

(** [sample_contrast_cs_difference13_difference24] (theorem).
 Mathematical meaning: For the first minus third test score contrast and the second minus fourth test score contrast, a nonnegative-weight finite sample must satisfy the sharp squared covariance-versus-variance feasibility constraint. The coefficients determine a specific multi-test contrast pair relevant to finite composite-score stability checks.
 Exact checked proposition: forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->    batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 (-1) 0) (four_batch_score x1 x2 x3 x4 0 1 0 (-1)) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 (-1) 0) (four_batch_score x1 x2 x3 x4 0 1 0 (-1)) xs    <= batch_variance w (four_batch_score x1 x2 x3 x4 1 0 (-1) 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 0 1 0 (-1)) xs
 Premises and side conditions: Every listed outcome occurrence has nonnegative weight and the full sample mass is strictly positive. Repeated observations are counted with multiplicity. The two explicit score vectors are not assumed independent, jointly Gaussian or standardized.
 Proof/definition method: Specialize the shared kernel-checked finite-sample covariance Cauchy-Schwarz theorem to both explicit four-test score functions; no reproof or expansion of the weighted sum is performed.
 Library reuse: ListPoolingAlgebra and FourContrastCovariance own the covariance and contrast definitions; SampleContrastCauchy owns the general inequality; Rocq Stdlib real numbers and lists supply all operations.
 Boundary: Exact finite empirical covariance constraint on the named composites, not a separate distributional sampling law, population parameter estimate, chi-square pivot, normal tail or interval-coverage theorem.
*)
Theorem sample_contrast_cs_difference13_difference24 :
 forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->
   batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 (-1) 0) (four_batch_score x1 x2 x3 x4 0 1 0 (-1)) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 (-1) 0) (four_batch_score x1 x2 x3 x4 0 1 0 (-1)) xs
   <= batch_variance w (four_batch_score x1 x2 x3 x4 1 0 (-1) 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 0 1 0 (-1)) xs.
Proof.
 intros A w x1 x2 x3 x4 xs Hw Hm.
 exact (sample_covariance_cauchy_schwarz A w
   (four_batch_score x1 x2 x3 x4 1 0 (-1) 0) (four_batch_score x1 x2 x3 x4 0 1 0 (-1)) xs Hw Hm).
Qed.

(** [sample_contrast_cs_difference13_difference34] (theorem).
 Mathematical meaning: For the first minus third test score contrast and the third minus fourth test score contrast, a nonnegative-weight finite sample must satisfy the sharp squared covariance-versus-variance feasibility constraint. The coefficients determine a specific multi-test contrast pair relevant to finite composite-score stability checks.
 Exact checked proposition: forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->    batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 (-1) 0) (four_batch_score x1 x2 x3 x4 0 0 1 (-1)) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 (-1) 0) (four_batch_score x1 x2 x3 x4 0 0 1 (-1)) xs    <= batch_variance w (four_batch_score x1 x2 x3 x4 1 0 (-1) 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 0 0 1 (-1)) xs
 Premises and side conditions: Every listed outcome occurrence has nonnegative weight and the full sample mass is strictly positive. Repeated observations are counted with multiplicity. The two explicit score vectors are not assumed independent, jointly Gaussian or standardized.
 Proof/definition method: Specialize the shared kernel-checked finite-sample covariance Cauchy-Schwarz theorem to both explicit four-test score functions; no reproof or expansion of the weighted sum is performed.
 Library reuse: ListPoolingAlgebra and FourContrastCovariance own the covariance and contrast definitions; SampleContrastCauchy owns the general inequality; Rocq Stdlib real numbers and lists supply all operations.
 Boundary: Exact finite empirical covariance constraint on the named composites, not a separate distributional sampling law, population parameter estimate, chi-square pivot, normal tail or interval-coverage theorem.
*)
Theorem sample_contrast_cs_difference13_difference34 :
 forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->
   batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 (-1) 0) (four_batch_score x1 x2 x3 x4 0 0 1 (-1)) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 (-1) 0) (four_batch_score x1 x2 x3 x4 0 0 1 (-1)) xs
   <= batch_variance w (four_batch_score x1 x2 x3 x4 1 0 (-1) 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 0 0 1 (-1)) xs.
Proof.
 intros A w x1 x2 x3 x4 xs Hw Hm.
 exact (sample_covariance_cauchy_schwarz A w
   (four_batch_score x1 x2 x3 x4 1 0 (-1) 0) (four_batch_score x1 x2 x3 x4 0 0 1 (-1)) xs Hw Hm).
Qed.

(** [sample_contrast_cs_difference13_triple123] (theorem).
 Mathematical meaning: For the first minus third test score contrast and the first three tests score contrast, a nonnegative-weight finite sample must satisfy the sharp squared covariance-versus-variance feasibility constraint. The coefficients determine a specific multi-test contrast pair relevant to finite composite-score stability checks.
 Exact checked proposition: forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->    batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 (-1) 0) (four_batch_score x1 x2 x3 x4 1 1 1 0) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 (-1) 0) (four_batch_score x1 x2 x3 x4 1 1 1 0) xs    <= batch_variance w (four_batch_score x1 x2 x3 x4 1 0 (-1) 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 1 1 0) xs
 Premises and side conditions: Every listed outcome occurrence has nonnegative weight and the full sample mass is strictly positive. Repeated observations are counted with multiplicity. The two explicit score vectors are not assumed independent, jointly Gaussian or standardized.
 Proof/definition method: Specialize the shared kernel-checked finite-sample covariance Cauchy-Schwarz theorem to both explicit four-test score functions; no reproof or expansion of the weighted sum is performed.
 Library reuse: ListPoolingAlgebra and FourContrastCovariance own the covariance and contrast definitions; SampleContrastCauchy owns the general inequality; Rocq Stdlib real numbers and lists supply all operations.
 Boundary: Exact finite empirical covariance constraint on the named composites, not a separate distributional sampling law, population parameter estimate, chi-square pivot, normal tail or interval-coverage theorem.
*)
Theorem sample_contrast_cs_difference13_triple123 :
 forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->
   batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 (-1) 0) (four_batch_score x1 x2 x3 x4 1 1 1 0) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 (-1) 0) (four_batch_score x1 x2 x3 x4 1 1 1 0) xs
   <= batch_variance w (four_batch_score x1 x2 x3 x4 1 0 (-1) 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 1 1 0) xs.
Proof.
 intros A w x1 x2 x3 x4 xs Hw Hm.
 exact (sample_covariance_cauchy_schwarz A w
   (four_batch_score x1 x2 x3 x4 1 0 (-1) 0) (four_batch_score x1 x2 x3 x4 1 1 1 0) xs Hw Hm).
Qed.

(** [sample_contrast_cs_difference13_triple124] (theorem).
 Mathematical meaning: For the first minus third test score contrast and the tests one, two and four score contrast, a nonnegative-weight finite sample must satisfy the sharp squared covariance-versus-variance feasibility constraint. The coefficients determine a specific multi-test contrast pair relevant to finite composite-score stability checks.
 Exact checked proposition: forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->    batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 (-1) 0) (four_batch_score x1 x2 x3 x4 1 1 0 1) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 (-1) 0) (four_batch_score x1 x2 x3 x4 1 1 0 1) xs    <= batch_variance w (four_batch_score x1 x2 x3 x4 1 0 (-1) 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 1 0 1) xs
 Premises and side conditions: Every listed outcome occurrence has nonnegative weight and the full sample mass is strictly positive. Repeated observations are counted with multiplicity. The two explicit score vectors are not assumed independent, jointly Gaussian or standardized.
 Proof/definition method: Specialize the shared kernel-checked finite-sample covariance Cauchy-Schwarz theorem to both explicit four-test score functions; no reproof or expansion of the weighted sum is performed.
 Library reuse: ListPoolingAlgebra and FourContrastCovariance own the covariance and contrast definitions; SampleContrastCauchy owns the general inequality; Rocq Stdlib real numbers and lists supply all operations.
 Boundary: Exact finite empirical covariance constraint on the named composites, not a separate distributional sampling law, population parameter estimate, chi-square pivot, normal tail or interval-coverage theorem.
*)
Theorem sample_contrast_cs_difference13_triple124 :
 forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->
   batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 (-1) 0) (four_batch_score x1 x2 x3 x4 1 1 0 1) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 (-1) 0) (four_batch_score x1 x2 x3 x4 1 1 0 1) xs
   <= batch_variance w (four_batch_score x1 x2 x3 x4 1 0 (-1) 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 1 0 1) xs.
Proof.
 intros A w x1 x2 x3 x4 xs Hw Hm.
 exact (sample_covariance_cauchy_schwarz A w
   (four_batch_score x1 x2 x3 x4 1 0 (-1) 0) (four_batch_score x1 x2 x3 x4 1 1 0 1) xs Hw Hm).
Qed.

(** [sample_contrast_cs_difference13_triple134] (theorem).
 Mathematical meaning: For the first minus third test score contrast and the tests one, three and four score contrast, a nonnegative-weight finite sample must satisfy the sharp squared covariance-versus-variance feasibility constraint. The coefficients determine a specific multi-test contrast pair relevant to finite composite-score stability checks.
 Exact checked proposition: forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->    batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 (-1) 0) (four_batch_score x1 x2 x3 x4 1 0 1 1) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 (-1) 0) (four_batch_score x1 x2 x3 x4 1 0 1 1) xs    <= batch_variance w (four_batch_score x1 x2 x3 x4 1 0 (-1) 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 0 1 1) xs
 Premises and side conditions: Every listed outcome occurrence has nonnegative weight and the full sample mass is strictly positive. Repeated observations are counted with multiplicity. The two explicit score vectors are not assumed independent, jointly Gaussian or standardized.
 Proof/definition method: Specialize the shared kernel-checked finite-sample covariance Cauchy-Schwarz theorem to both explicit four-test score functions; no reproof or expansion of the weighted sum is performed.
 Library reuse: ListPoolingAlgebra and FourContrastCovariance own the covariance and contrast definitions; SampleContrastCauchy owns the general inequality; Rocq Stdlib real numbers and lists supply all operations.
 Boundary: Exact finite empirical covariance constraint on the named composites, not a separate distributional sampling law, population parameter estimate, chi-square pivot, normal tail or interval-coverage theorem.
*)
Theorem sample_contrast_cs_difference13_triple134 :
 forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->
   batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 (-1) 0) (four_batch_score x1 x2 x3 x4 1 0 1 1) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 (-1) 0) (four_batch_score x1 x2 x3 x4 1 0 1 1) xs
   <= batch_variance w (four_batch_score x1 x2 x3 x4 1 0 (-1) 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 0 1 1) xs.
Proof.
 intros A w x1 x2 x3 x4 xs Hw Hm.
 exact (sample_covariance_cauchy_schwarz A w
   (four_batch_score x1 x2 x3 x4 1 0 (-1) 0) (four_batch_score x1 x2 x3 x4 1 0 1 1) xs Hw Hm).
Qed.

(** [sample_contrast_cs_difference13_triple234] (theorem).
 Mathematical meaning: For the first minus third test score contrast and the last three tests score contrast, a nonnegative-weight finite sample must satisfy the sharp squared covariance-versus-variance feasibility constraint. The coefficients determine a specific multi-test contrast pair relevant to finite composite-score stability checks.
 Exact checked proposition: forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->    batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 (-1) 0) (four_batch_score x1 x2 x3 x4 0 1 1 1) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 (-1) 0) (four_batch_score x1 x2 x3 x4 0 1 1 1) xs    <= batch_variance w (four_batch_score x1 x2 x3 x4 1 0 (-1) 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 0 1 1 1) xs
 Premises and side conditions: Every listed outcome occurrence has nonnegative weight and the full sample mass is strictly positive. Repeated observations are counted with multiplicity. The two explicit score vectors are not assumed independent, jointly Gaussian or standardized.
 Proof/definition method: Specialize the shared kernel-checked finite-sample covariance Cauchy-Schwarz theorem to both explicit four-test score functions; no reproof or expansion of the weighted sum is performed.
 Library reuse: ListPoolingAlgebra and FourContrastCovariance own the covariance and contrast definitions; SampleContrastCauchy owns the general inequality; Rocq Stdlib real numbers and lists supply all operations.
 Boundary: Exact finite empirical covariance constraint on the named composites, not a separate distributional sampling law, population parameter estimate, chi-square pivot, normal tail or interval-coverage theorem.
*)
Theorem sample_contrast_cs_difference13_triple234 :
 forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->
   batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 (-1) 0) (four_batch_score x1 x2 x3 x4 0 1 1 1) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 (-1) 0) (four_batch_score x1 x2 x3 x4 0 1 1 1) xs
   <= batch_variance w (four_batch_score x1 x2 x3 x4 1 0 (-1) 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 0 1 1 1) xs.
Proof.
 intros A w x1 x2 x3 x4 xs Hw Hm.
 exact (sample_covariance_cauchy_schwarz A w
   (four_batch_score x1 x2 x3 x4 1 0 (-1) 0) (four_batch_score x1 x2 x3 x4 0 1 1 1) xs Hw Hm).
Qed.

(** [sample_contrast_cs_difference13_allfour] (theorem).
 Mathematical meaning: For the first minus third test score contrast and the all four tests score contrast, a nonnegative-weight finite sample must satisfy the sharp squared covariance-versus-variance feasibility constraint. The coefficients determine a specific multi-test contrast pair relevant to finite composite-score stability checks.
 Exact checked proposition: forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->    batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 (-1) 0) (four_batch_score x1 x2 x3 x4 1 1 1 1) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 (-1) 0) (four_batch_score x1 x2 x3 x4 1 1 1 1) xs    <= batch_variance w (four_batch_score x1 x2 x3 x4 1 0 (-1) 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 1 1 1) xs
 Premises and side conditions: Every listed outcome occurrence has nonnegative weight and the full sample mass is strictly positive. Repeated observations are counted with multiplicity. The two explicit score vectors are not assumed independent, jointly Gaussian or standardized.
 Proof/definition method: Specialize the shared kernel-checked finite-sample covariance Cauchy-Schwarz theorem to both explicit four-test score functions; no reproof or expansion of the weighted sum is performed.
 Library reuse: ListPoolingAlgebra and FourContrastCovariance own the covariance and contrast definitions; SampleContrastCauchy owns the general inequality; Rocq Stdlib real numbers and lists supply all operations.
 Boundary: Exact finite empirical covariance constraint on the named composites, not a separate distributional sampling law, population parameter estimate, chi-square pivot, normal tail or interval-coverage theorem.
*)
Theorem sample_contrast_cs_difference13_allfour :
 forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->
   batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 (-1) 0) (four_batch_score x1 x2 x3 x4 1 1 1 1) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 (-1) 0) (four_batch_score x1 x2 x3 x4 1 1 1 1) xs
   <= batch_variance w (four_batch_score x1 x2 x3 x4 1 0 (-1) 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 1 1 1) xs.
Proof.
 intros A w x1 x2 x3 x4 xs Hw Hm.
 exact (sample_covariance_cauchy_schwarz A w
   (four_batch_score x1 x2 x3 x4 1 0 (-1) 0) (four_batch_score x1 x2 x3 x4 1 1 1 1) xs Hw Hm).
Qed.

(** [sample_contrast_cs_difference13_balanced12v34] (theorem).
 Mathematical meaning: For the first minus third test score contrast and the difference between the two pairs score contrast, a nonnegative-weight finite sample must satisfy the sharp squared covariance-versus-variance feasibility constraint. The coefficients determine a specific multi-test contrast pair relevant to finite composite-score stability checks.
 Exact checked proposition: forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->    batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 (-1) 0) (four_batch_score x1 x2 x3 x4 1 1 (-1) (-1)) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 (-1) 0) (four_batch_score x1 x2 x3 x4 1 1 (-1) (-1)) xs    <= batch_variance w (four_batch_score x1 x2 x3 x4 1 0 (-1) 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 1 (-1) (-1)) xs
 Premises and side conditions: Every listed outcome occurrence has nonnegative weight and the full sample mass is strictly positive. Repeated observations are counted with multiplicity. The two explicit score vectors are not assumed independent, jointly Gaussian or standardized.
 Proof/definition method: Specialize the shared kernel-checked finite-sample covariance Cauchy-Schwarz theorem to both explicit four-test score functions; no reproof or expansion of the weighted sum is performed.
 Library reuse: ListPoolingAlgebra and FourContrastCovariance own the covariance and contrast definitions; SampleContrastCauchy owns the general inequality; Rocq Stdlib real numbers and lists supply all operations.
 Boundary: Exact finite empirical covariance constraint on the named composites, not a separate distributional sampling law, population parameter estimate, chi-square pivot, normal tail or interval-coverage theorem.
*)
Theorem sample_contrast_cs_difference13_balanced12v34 :
 forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->
   batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 (-1) 0) (four_batch_score x1 x2 x3 x4 1 1 (-1) (-1)) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 (-1) 0) (four_batch_score x1 x2 x3 x4 1 1 (-1) (-1)) xs
   <= batch_variance w (four_batch_score x1 x2 x3 x4 1 0 (-1) 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 1 (-1) (-1)) xs.
Proof.
 intros A w x1 x2 x3 x4 xs Hw Hm.
 exact (sample_covariance_cauchy_schwarz A w
   (four_batch_score x1 x2 x3 x4 1 0 (-1) 0) (four_batch_score x1 x2 x3 x4 1 1 (-1) (-1)) xs Hw Hm).
Qed.

(** [sample_contrast_cs_difference14_difference14] (theorem).
 Mathematical meaning: For the first minus fourth test score contrast and the first minus fourth test score contrast, a nonnegative-weight finite sample must satisfy the sharp squared covariance-versus-variance feasibility constraint. The coefficients determine a specific multi-test contrast pair relevant to finite composite-score stability checks.
 Exact checked proposition: forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->    batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 0 (-1)) (four_batch_score x1 x2 x3 x4 1 0 0 (-1)) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 0 (-1)) (four_batch_score x1 x2 x3 x4 1 0 0 (-1)) xs    <= batch_variance w (four_batch_score x1 x2 x3 x4 1 0 0 (-1)) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 0 0 (-1)) xs
 Premises and side conditions: Every listed outcome occurrence has nonnegative weight and the full sample mass is strictly positive. Repeated observations are counted with multiplicity. The two explicit score vectors are not assumed independent, jointly Gaussian or standardized.
 Proof/definition method: Specialize the shared kernel-checked finite-sample covariance Cauchy-Schwarz theorem to both explicit four-test score functions; no reproof or expansion of the weighted sum is performed.
 Library reuse: ListPoolingAlgebra and FourContrastCovariance own the covariance and contrast definitions; SampleContrastCauchy owns the general inequality; Rocq Stdlib real numbers and lists supply all operations.
 Boundary: Exact finite empirical covariance constraint on the named composites, not a separate distributional sampling law, population parameter estimate, chi-square pivot, normal tail or interval-coverage theorem.
*)
Theorem sample_contrast_cs_difference14_difference14 :
 forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->
   batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 0 (-1)) (four_batch_score x1 x2 x3 x4 1 0 0 (-1)) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 0 (-1)) (four_batch_score x1 x2 x3 x4 1 0 0 (-1)) xs
   <= batch_variance w (four_batch_score x1 x2 x3 x4 1 0 0 (-1)) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 0 0 (-1)) xs.
Proof.
 intros A w x1 x2 x3 x4 xs Hw Hm.
 exact (sample_covariance_cauchy_schwarz A w
   (four_batch_score x1 x2 x3 x4 1 0 0 (-1)) (four_batch_score x1 x2 x3 x4 1 0 0 (-1)) xs Hw Hm).
Qed.

(** [sample_contrast_cs_difference14_difference23] (theorem).
 Mathematical meaning: For the first minus fourth test score contrast and the second minus third test score contrast, a nonnegative-weight finite sample must satisfy the sharp squared covariance-versus-variance feasibility constraint. The coefficients determine a specific multi-test contrast pair relevant to finite composite-score stability checks.
 Exact checked proposition: forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->    batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 0 (-1)) (four_batch_score x1 x2 x3 x4 0 1 (-1) 0) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 0 (-1)) (four_batch_score x1 x2 x3 x4 0 1 (-1) 0) xs    <= batch_variance w (four_batch_score x1 x2 x3 x4 1 0 0 (-1)) xs * batch_variance w (four_batch_score x1 x2 x3 x4 0 1 (-1) 0) xs
 Premises and side conditions: Every listed outcome occurrence has nonnegative weight and the full sample mass is strictly positive. Repeated observations are counted with multiplicity. The two explicit score vectors are not assumed independent, jointly Gaussian or standardized.
 Proof/definition method: Specialize the shared kernel-checked finite-sample covariance Cauchy-Schwarz theorem to both explicit four-test score functions; no reproof or expansion of the weighted sum is performed.
 Library reuse: ListPoolingAlgebra and FourContrastCovariance own the covariance and contrast definitions; SampleContrastCauchy owns the general inequality; Rocq Stdlib real numbers and lists supply all operations.
 Boundary: Exact finite empirical covariance constraint on the named composites, not a separate distributional sampling law, population parameter estimate, chi-square pivot, normal tail or interval-coverage theorem.
*)
Theorem sample_contrast_cs_difference14_difference23 :
 forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->
   batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 0 (-1)) (four_batch_score x1 x2 x3 x4 0 1 (-1) 0) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 0 (-1)) (four_batch_score x1 x2 x3 x4 0 1 (-1) 0) xs
   <= batch_variance w (four_batch_score x1 x2 x3 x4 1 0 0 (-1)) xs * batch_variance w (four_batch_score x1 x2 x3 x4 0 1 (-1) 0) xs.
Proof.
 intros A w x1 x2 x3 x4 xs Hw Hm.
 exact (sample_covariance_cauchy_schwarz A w
   (four_batch_score x1 x2 x3 x4 1 0 0 (-1)) (four_batch_score x1 x2 x3 x4 0 1 (-1) 0) xs Hw Hm).
Qed.

(** [sample_contrast_cs_difference14_difference24] (theorem).
 Mathematical meaning: For the first minus fourth test score contrast and the second minus fourth test score contrast, a nonnegative-weight finite sample must satisfy the sharp squared covariance-versus-variance feasibility constraint. The coefficients determine a specific multi-test contrast pair relevant to finite composite-score stability checks.
 Exact checked proposition: forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->    batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 0 (-1)) (four_batch_score x1 x2 x3 x4 0 1 0 (-1)) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 0 (-1)) (four_batch_score x1 x2 x3 x4 0 1 0 (-1)) xs    <= batch_variance w (four_batch_score x1 x2 x3 x4 1 0 0 (-1)) xs * batch_variance w (four_batch_score x1 x2 x3 x4 0 1 0 (-1)) xs
 Premises and side conditions: Every listed outcome occurrence has nonnegative weight and the full sample mass is strictly positive. Repeated observations are counted with multiplicity. The two explicit score vectors are not assumed independent, jointly Gaussian or standardized.
 Proof/definition method: Specialize the shared kernel-checked finite-sample covariance Cauchy-Schwarz theorem to both explicit four-test score functions; no reproof or expansion of the weighted sum is performed.
 Library reuse: ListPoolingAlgebra and FourContrastCovariance own the covariance and contrast definitions; SampleContrastCauchy owns the general inequality; Rocq Stdlib real numbers and lists supply all operations.
 Boundary: Exact finite empirical covariance constraint on the named composites, not a separate distributional sampling law, population parameter estimate, chi-square pivot, normal tail or interval-coverage theorem.
*)
Theorem sample_contrast_cs_difference14_difference24 :
 forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->
   batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 0 (-1)) (four_batch_score x1 x2 x3 x4 0 1 0 (-1)) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 0 (-1)) (four_batch_score x1 x2 x3 x4 0 1 0 (-1)) xs
   <= batch_variance w (four_batch_score x1 x2 x3 x4 1 0 0 (-1)) xs * batch_variance w (four_batch_score x1 x2 x3 x4 0 1 0 (-1)) xs.
Proof.
 intros A w x1 x2 x3 x4 xs Hw Hm.
 exact (sample_covariance_cauchy_schwarz A w
   (four_batch_score x1 x2 x3 x4 1 0 0 (-1)) (four_batch_score x1 x2 x3 x4 0 1 0 (-1)) xs Hw Hm).
Qed.

(** [sample_contrast_cs_difference14_difference34] (theorem).
 Mathematical meaning: For the first minus fourth test score contrast and the third minus fourth test score contrast, a nonnegative-weight finite sample must satisfy the sharp squared covariance-versus-variance feasibility constraint. The coefficients determine a specific multi-test contrast pair relevant to finite composite-score stability checks.
 Exact checked proposition: forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->    batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 0 (-1)) (four_batch_score x1 x2 x3 x4 0 0 1 (-1)) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 0 (-1)) (four_batch_score x1 x2 x3 x4 0 0 1 (-1)) xs    <= batch_variance w (four_batch_score x1 x2 x3 x4 1 0 0 (-1)) xs * batch_variance w (four_batch_score x1 x2 x3 x4 0 0 1 (-1)) xs
 Premises and side conditions: Every listed outcome occurrence has nonnegative weight and the full sample mass is strictly positive. Repeated observations are counted with multiplicity. The two explicit score vectors are not assumed independent, jointly Gaussian or standardized.
 Proof/definition method: Specialize the shared kernel-checked finite-sample covariance Cauchy-Schwarz theorem to both explicit four-test score functions; no reproof or expansion of the weighted sum is performed.
 Library reuse: ListPoolingAlgebra and FourContrastCovariance own the covariance and contrast definitions; SampleContrastCauchy owns the general inequality; Rocq Stdlib real numbers and lists supply all operations.
 Boundary: Exact finite empirical covariance constraint on the named composites, not a separate distributional sampling law, population parameter estimate, chi-square pivot, normal tail or interval-coverage theorem.
*)
Theorem sample_contrast_cs_difference14_difference34 :
 forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->
   batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 0 (-1)) (four_batch_score x1 x2 x3 x4 0 0 1 (-1)) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 0 (-1)) (four_batch_score x1 x2 x3 x4 0 0 1 (-1)) xs
   <= batch_variance w (four_batch_score x1 x2 x3 x4 1 0 0 (-1)) xs * batch_variance w (four_batch_score x1 x2 x3 x4 0 0 1 (-1)) xs.
Proof.
 intros A w x1 x2 x3 x4 xs Hw Hm.
 exact (sample_covariance_cauchy_schwarz A w
   (four_batch_score x1 x2 x3 x4 1 0 0 (-1)) (four_batch_score x1 x2 x3 x4 0 0 1 (-1)) xs Hw Hm).
Qed.

(** [sample_contrast_cs_difference14_triple123] (theorem).
 Mathematical meaning: For the first minus fourth test score contrast and the first three tests score contrast, a nonnegative-weight finite sample must satisfy the sharp squared covariance-versus-variance feasibility constraint. The coefficients determine a specific multi-test contrast pair relevant to finite composite-score stability checks.
 Exact checked proposition: forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->    batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 0 (-1)) (four_batch_score x1 x2 x3 x4 1 1 1 0) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 0 (-1)) (four_batch_score x1 x2 x3 x4 1 1 1 0) xs    <= batch_variance w (four_batch_score x1 x2 x3 x4 1 0 0 (-1)) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 1 1 0) xs
 Premises and side conditions: Every listed outcome occurrence has nonnegative weight and the full sample mass is strictly positive. Repeated observations are counted with multiplicity. The two explicit score vectors are not assumed independent, jointly Gaussian or standardized.
 Proof/definition method: Specialize the shared kernel-checked finite-sample covariance Cauchy-Schwarz theorem to both explicit four-test score functions; no reproof or expansion of the weighted sum is performed.
 Library reuse: ListPoolingAlgebra and FourContrastCovariance own the covariance and contrast definitions; SampleContrastCauchy owns the general inequality; Rocq Stdlib real numbers and lists supply all operations.
 Boundary: Exact finite empirical covariance constraint on the named composites, not a separate distributional sampling law, population parameter estimate, chi-square pivot, normal tail or interval-coverage theorem.
*)
Theorem sample_contrast_cs_difference14_triple123 :
 forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->
   batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 0 (-1)) (four_batch_score x1 x2 x3 x4 1 1 1 0) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 0 (-1)) (four_batch_score x1 x2 x3 x4 1 1 1 0) xs
   <= batch_variance w (four_batch_score x1 x2 x3 x4 1 0 0 (-1)) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 1 1 0) xs.
Proof.
 intros A w x1 x2 x3 x4 xs Hw Hm.
 exact (sample_covariance_cauchy_schwarz A w
   (four_batch_score x1 x2 x3 x4 1 0 0 (-1)) (four_batch_score x1 x2 x3 x4 1 1 1 0) xs Hw Hm).
Qed.

(** [sample_contrast_cs_difference14_triple124] (theorem).
 Mathematical meaning: For the first minus fourth test score contrast and the tests one, two and four score contrast, a nonnegative-weight finite sample must satisfy the sharp squared covariance-versus-variance feasibility constraint. The coefficients determine a specific multi-test contrast pair relevant to finite composite-score stability checks.
 Exact checked proposition: forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->    batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 0 (-1)) (four_batch_score x1 x2 x3 x4 1 1 0 1) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 0 (-1)) (four_batch_score x1 x2 x3 x4 1 1 0 1) xs    <= batch_variance w (four_batch_score x1 x2 x3 x4 1 0 0 (-1)) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 1 0 1) xs
 Premises and side conditions: Every listed outcome occurrence has nonnegative weight and the full sample mass is strictly positive. Repeated observations are counted with multiplicity. The two explicit score vectors are not assumed independent, jointly Gaussian or standardized.
 Proof/definition method: Specialize the shared kernel-checked finite-sample covariance Cauchy-Schwarz theorem to both explicit four-test score functions; no reproof or expansion of the weighted sum is performed.
 Library reuse: ListPoolingAlgebra and FourContrastCovariance own the covariance and contrast definitions; SampleContrastCauchy owns the general inequality; Rocq Stdlib real numbers and lists supply all operations.
 Boundary: Exact finite empirical covariance constraint on the named composites, not a separate distributional sampling law, population parameter estimate, chi-square pivot, normal tail or interval-coverage theorem.
*)
Theorem sample_contrast_cs_difference14_triple124 :
 forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->
   batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 0 (-1)) (four_batch_score x1 x2 x3 x4 1 1 0 1) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 0 (-1)) (four_batch_score x1 x2 x3 x4 1 1 0 1) xs
   <= batch_variance w (four_batch_score x1 x2 x3 x4 1 0 0 (-1)) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 1 0 1) xs.
Proof.
 intros A w x1 x2 x3 x4 xs Hw Hm.
 exact (sample_covariance_cauchy_schwarz A w
   (four_batch_score x1 x2 x3 x4 1 0 0 (-1)) (four_batch_score x1 x2 x3 x4 1 1 0 1) xs Hw Hm).
Qed.

(** [sample_contrast_cs_difference14_triple134] (theorem).
 Mathematical meaning: For the first minus fourth test score contrast and the tests one, three and four score contrast, a nonnegative-weight finite sample must satisfy the sharp squared covariance-versus-variance feasibility constraint. The coefficients determine a specific multi-test contrast pair relevant to finite composite-score stability checks.
 Exact checked proposition: forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->    batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 0 (-1)) (four_batch_score x1 x2 x3 x4 1 0 1 1) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 0 (-1)) (four_batch_score x1 x2 x3 x4 1 0 1 1) xs    <= batch_variance w (four_batch_score x1 x2 x3 x4 1 0 0 (-1)) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 0 1 1) xs
 Premises and side conditions: Every listed outcome occurrence has nonnegative weight and the full sample mass is strictly positive. Repeated observations are counted with multiplicity. The two explicit score vectors are not assumed independent, jointly Gaussian or standardized.
 Proof/definition method: Specialize the shared kernel-checked finite-sample covariance Cauchy-Schwarz theorem to both explicit four-test score functions; no reproof or expansion of the weighted sum is performed.
 Library reuse: ListPoolingAlgebra and FourContrastCovariance own the covariance and contrast definitions; SampleContrastCauchy owns the general inequality; Rocq Stdlib real numbers and lists supply all operations.
 Boundary: Exact finite empirical covariance constraint on the named composites, not a separate distributional sampling law, population parameter estimate, chi-square pivot, normal tail or interval-coverage theorem.
*)
Theorem sample_contrast_cs_difference14_triple134 :
 forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->
   batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 0 (-1)) (four_batch_score x1 x2 x3 x4 1 0 1 1) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 0 (-1)) (four_batch_score x1 x2 x3 x4 1 0 1 1) xs
   <= batch_variance w (four_batch_score x1 x2 x3 x4 1 0 0 (-1)) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 0 1 1) xs.
Proof.
 intros A w x1 x2 x3 x4 xs Hw Hm.
 exact (sample_covariance_cauchy_schwarz A w
   (four_batch_score x1 x2 x3 x4 1 0 0 (-1)) (four_batch_score x1 x2 x3 x4 1 0 1 1) xs Hw Hm).
Qed.

(** [sample_contrast_cs_difference14_triple234] (theorem).
 Mathematical meaning: For the first minus fourth test score contrast and the last three tests score contrast, a nonnegative-weight finite sample must satisfy the sharp squared covariance-versus-variance feasibility constraint. The coefficients determine a specific multi-test contrast pair relevant to finite composite-score stability checks.
 Exact checked proposition: forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->    batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 0 (-1)) (four_batch_score x1 x2 x3 x4 0 1 1 1) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 0 (-1)) (four_batch_score x1 x2 x3 x4 0 1 1 1) xs    <= batch_variance w (four_batch_score x1 x2 x3 x4 1 0 0 (-1)) xs * batch_variance w (four_batch_score x1 x2 x3 x4 0 1 1 1) xs
 Premises and side conditions: Every listed outcome occurrence has nonnegative weight and the full sample mass is strictly positive. Repeated observations are counted with multiplicity. The two explicit score vectors are not assumed independent, jointly Gaussian or standardized.
 Proof/definition method: Specialize the shared kernel-checked finite-sample covariance Cauchy-Schwarz theorem to both explicit four-test score functions; no reproof or expansion of the weighted sum is performed.
 Library reuse: ListPoolingAlgebra and FourContrastCovariance own the covariance and contrast definitions; SampleContrastCauchy owns the general inequality; Rocq Stdlib real numbers and lists supply all operations.
 Boundary: Exact finite empirical covariance constraint on the named composites, not a separate distributional sampling law, population parameter estimate, chi-square pivot, normal tail or interval-coverage theorem.
*)
Theorem sample_contrast_cs_difference14_triple234 :
 forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->
   batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 0 (-1)) (four_batch_score x1 x2 x3 x4 0 1 1 1) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 0 (-1)) (four_batch_score x1 x2 x3 x4 0 1 1 1) xs
   <= batch_variance w (four_batch_score x1 x2 x3 x4 1 0 0 (-1)) xs * batch_variance w (four_batch_score x1 x2 x3 x4 0 1 1 1) xs.
Proof.
 intros A w x1 x2 x3 x4 xs Hw Hm.
 exact (sample_covariance_cauchy_schwarz A w
   (four_batch_score x1 x2 x3 x4 1 0 0 (-1)) (four_batch_score x1 x2 x3 x4 0 1 1 1) xs Hw Hm).
Qed.

(** [sample_contrast_cs_difference14_allfour] (theorem).
 Mathematical meaning: For the first minus fourth test score contrast and the all four tests score contrast, a nonnegative-weight finite sample must satisfy the sharp squared covariance-versus-variance feasibility constraint. The coefficients determine a specific multi-test contrast pair relevant to finite composite-score stability checks.
 Exact checked proposition: forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->    batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 0 (-1)) (four_batch_score x1 x2 x3 x4 1 1 1 1) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 0 (-1)) (four_batch_score x1 x2 x3 x4 1 1 1 1) xs    <= batch_variance w (four_batch_score x1 x2 x3 x4 1 0 0 (-1)) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 1 1 1) xs
 Premises and side conditions: Every listed outcome occurrence has nonnegative weight and the full sample mass is strictly positive. Repeated observations are counted with multiplicity. The two explicit score vectors are not assumed independent, jointly Gaussian or standardized.
 Proof/definition method: Specialize the shared kernel-checked finite-sample covariance Cauchy-Schwarz theorem to both explicit four-test score functions; no reproof or expansion of the weighted sum is performed.
 Library reuse: ListPoolingAlgebra and FourContrastCovariance own the covariance and contrast definitions; SampleContrastCauchy owns the general inequality; Rocq Stdlib real numbers and lists supply all operations.
 Boundary: Exact finite empirical covariance constraint on the named composites, not a separate distributional sampling law, population parameter estimate, chi-square pivot, normal tail or interval-coverage theorem.
*)
Theorem sample_contrast_cs_difference14_allfour :
 forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->
   batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 0 (-1)) (four_batch_score x1 x2 x3 x4 1 1 1 1) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 0 (-1)) (four_batch_score x1 x2 x3 x4 1 1 1 1) xs
   <= batch_variance w (four_batch_score x1 x2 x3 x4 1 0 0 (-1)) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 1 1 1) xs.
Proof.
 intros A w x1 x2 x3 x4 xs Hw Hm.
 exact (sample_covariance_cauchy_schwarz A w
   (four_batch_score x1 x2 x3 x4 1 0 0 (-1)) (four_batch_score x1 x2 x3 x4 1 1 1 1) xs Hw Hm).
Qed.

(** [sample_contrast_cs_difference14_balanced12v34] (theorem).
 Mathematical meaning: For the first minus fourth test score contrast and the difference between the two pairs score contrast, a nonnegative-weight finite sample must satisfy the sharp squared covariance-versus-variance feasibility constraint. The coefficients determine a specific multi-test contrast pair relevant to finite composite-score stability checks.
 Exact checked proposition: forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->    batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 0 (-1)) (four_batch_score x1 x2 x3 x4 1 1 (-1) (-1)) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 0 (-1)) (four_batch_score x1 x2 x3 x4 1 1 (-1) (-1)) xs    <= batch_variance w (four_batch_score x1 x2 x3 x4 1 0 0 (-1)) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 1 (-1) (-1)) xs
 Premises and side conditions: Every listed outcome occurrence has nonnegative weight and the full sample mass is strictly positive. Repeated observations are counted with multiplicity. The two explicit score vectors are not assumed independent, jointly Gaussian or standardized.
 Proof/definition method: Specialize the shared kernel-checked finite-sample covariance Cauchy-Schwarz theorem to both explicit four-test score functions; no reproof or expansion of the weighted sum is performed.
 Library reuse: ListPoolingAlgebra and FourContrastCovariance own the covariance and contrast definitions; SampleContrastCauchy owns the general inequality; Rocq Stdlib real numbers and lists supply all operations.
 Boundary: Exact finite empirical covariance constraint on the named composites, not a separate distributional sampling law, population parameter estimate, chi-square pivot, normal tail or interval-coverage theorem.
*)
Theorem sample_contrast_cs_difference14_balanced12v34 :
 forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->
   batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 0 (-1)) (four_batch_score x1 x2 x3 x4 1 1 (-1) (-1)) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 0 (-1)) (four_batch_score x1 x2 x3 x4 1 1 (-1) (-1)) xs
   <= batch_variance w (four_batch_score x1 x2 x3 x4 1 0 0 (-1)) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 1 (-1) (-1)) xs.
Proof.
 intros A w x1 x2 x3 x4 xs Hw Hm.
 exact (sample_covariance_cauchy_schwarz A w
   (four_batch_score x1 x2 x3 x4 1 0 0 (-1)) (four_batch_score x1 x2 x3 x4 1 1 (-1) (-1)) xs Hw Hm).
Qed.

(** [sample_contrast_cs_difference23_difference23] (theorem).
 Mathematical meaning: For the second minus third test score contrast and the second minus third test score contrast, a nonnegative-weight finite sample must satisfy the sharp squared covariance-versus-variance feasibility constraint. The coefficients determine a specific multi-test contrast pair relevant to finite composite-score stability checks.
 Exact checked proposition: forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->    batch_covariance w (four_batch_score x1 x2 x3 x4 0 1 (-1) 0) (four_batch_score x1 x2 x3 x4 0 1 (-1) 0) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 0 1 (-1) 0) (four_batch_score x1 x2 x3 x4 0 1 (-1) 0) xs    <= batch_variance w (four_batch_score x1 x2 x3 x4 0 1 (-1) 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 0 1 (-1) 0) xs
 Premises and side conditions: Every listed outcome occurrence has nonnegative weight and the full sample mass is strictly positive. Repeated observations are counted with multiplicity. The two explicit score vectors are not assumed independent, jointly Gaussian or standardized.
 Proof/definition method: Specialize the shared kernel-checked finite-sample covariance Cauchy-Schwarz theorem to both explicit four-test score functions; no reproof or expansion of the weighted sum is performed.
 Library reuse: ListPoolingAlgebra and FourContrastCovariance own the covariance and contrast definitions; SampleContrastCauchy owns the general inequality; Rocq Stdlib real numbers and lists supply all operations.
 Boundary: Exact finite empirical covariance constraint on the named composites, not a separate distributional sampling law, population parameter estimate, chi-square pivot, normal tail or interval-coverage theorem.
*)
Theorem sample_contrast_cs_difference23_difference23 :
 forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->
   batch_covariance w (four_batch_score x1 x2 x3 x4 0 1 (-1) 0) (four_batch_score x1 x2 x3 x4 0 1 (-1) 0) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 0 1 (-1) 0) (four_batch_score x1 x2 x3 x4 0 1 (-1) 0) xs
   <= batch_variance w (four_batch_score x1 x2 x3 x4 0 1 (-1) 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 0 1 (-1) 0) xs.
Proof.
 intros A w x1 x2 x3 x4 xs Hw Hm.
 exact (sample_covariance_cauchy_schwarz A w
   (four_batch_score x1 x2 x3 x4 0 1 (-1) 0) (four_batch_score x1 x2 x3 x4 0 1 (-1) 0) xs Hw Hm).
Qed.

(** [sample_contrast_cs_difference23_difference24] (theorem).
 Mathematical meaning: For the second minus third test score contrast and the second minus fourth test score contrast, a nonnegative-weight finite sample must satisfy the sharp squared covariance-versus-variance feasibility constraint. The coefficients determine a specific multi-test contrast pair relevant to finite composite-score stability checks.
 Exact checked proposition: forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->    batch_covariance w (four_batch_score x1 x2 x3 x4 0 1 (-1) 0) (four_batch_score x1 x2 x3 x4 0 1 0 (-1)) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 0 1 (-1) 0) (four_batch_score x1 x2 x3 x4 0 1 0 (-1)) xs    <= batch_variance w (four_batch_score x1 x2 x3 x4 0 1 (-1) 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 0 1 0 (-1)) xs
 Premises and side conditions: Every listed outcome occurrence has nonnegative weight and the full sample mass is strictly positive. Repeated observations are counted with multiplicity. The two explicit score vectors are not assumed independent, jointly Gaussian or standardized.
 Proof/definition method: Specialize the shared kernel-checked finite-sample covariance Cauchy-Schwarz theorem to both explicit four-test score functions; no reproof or expansion of the weighted sum is performed.
 Library reuse: ListPoolingAlgebra and FourContrastCovariance own the covariance and contrast definitions; SampleContrastCauchy owns the general inequality; Rocq Stdlib real numbers and lists supply all operations.
 Boundary: Exact finite empirical covariance constraint on the named composites, not a separate distributional sampling law, population parameter estimate, chi-square pivot, normal tail or interval-coverage theorem.
*)
Theorem sample_contrast_cs_difference23_difference24 :
 forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->
   batch_covariance w (four_batch_score x1 x2 x3 x4 0 1 (-1) 0) (four_batch_score x1 x2 x3 x4 0 1 0 (-1)) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 0 1 (-1) 0) (four_batch_score x1 x2 x3 x4 0 1 0 (-1)) xs
   <= batch_variance w (four_batch_score x1 x2 x3 x4 0 1 (-1) 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 0 1 0 (-1)) xs.
Proof.
 intros A w x1 x2 x3 x4 xs Hw Hm.
 exact (sample_covariance_cauchy_schwarz A w
   (four_batch_score x1 x2 x3 x4 0 1 (-1) 0) (four_batch_score x1 x2 x3 x4 0 1 0 (-1)) xs Hw Hm).
Qed.

(** [sample_contrast_cs_difference23_difference34] (theorem).
 Mathematical meaning: For the second minus third test score contrast and the third minus fourth test score contrast, a nonnegative-weight finite sample must satisfy the sharp squared covariance-versus-variance feasibility constraint. The coefficients determine a specific multi-test contrast pair relevant to finite composite-score stability checks.
 Exact checked proposition: forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->    batch_covariance w (four_batch_score x1 x2 x3 x4 0 1 (-1) 0) (four_batch_score x1 x2 x3 x4 0 0 1 (-1)) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 0 1 (-1) 0) (four_batch_score x1 x2 x3 x4 0 0 1 (-1)) xs    <= batch_variance w (four_batch_score x1 x2 x3 x4 0 1 (-1) 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 0 0 1 (-1)) xs
 Premises and side conditions: Every listed outcome occurrence has nonnegative weight and the full sample mass is strictly positive. Repeated observations are counted with multiplicity. The two explicit score vectors are not assumed independent, jointly Gaussian or standardized.
 Proof/definition method: Specialize the shared kernel-checked finite-sample covariance Cauchy-Schwarz theorem to both explicit four-test score functions; no reproof or expansion of the weighted sum is performed.
 Library reuse: ListPoolingAlgebra and FourContrastCovariance own the covariance and contrast definitions; SampleContrastCauchy owns the general inequality; Rocq Stdlib real numbers and lists supply all operations.
 Boundary: Exact finite empirical covariance constraint on the named composites, not a separate distributional sampling law, population parameter estimate, chi-square pivot, normal tail or interval-coverage theorem.
*)
Theorem sample_contrast_cs_difference23_difference34 :
 forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->
   batch_covariance w (four_batch_score x1 x2 x3 x4 0 1 (-1) 0) (four_batch_score x1 x2 x3 x4 0 0 1 (-1)) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 0 1 (-1) 0) (four_batch_score x1 x2 x3 x4 0 0 1 (-1)) xs
   <= batch_variance w (four_batch_score x1 x2 x3 x4 0 1 (-1) 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 0 0 1 (-1)) xs.
Proof.
 intros A w x1 x2 x3 x4 xs Hw Hm.
 exact (sample_covariance_cauchy_schwarz A w
   (four_batch_score x1 x2 x3 x4 0 1 (-1) 0) (four_batch_score x1 x2 x3 x4 0 0 1 (-1)) xs Hw Hm).
Qed.

(** [sample_contrast_cs_difference23_triple123] (theorem).
 Mathematical meaning: For the second minus third test score contrast and the first three tests score contrast, a nonnegative-weight finite sample must satisfy the sharp squared covariance-versus-variance feasibility constraint. The coefficients determine a specific multi-test contrast pair relevant to finite composite-score stability checks.
 Exact checked proposition: forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->    batch_covariance w (four_batch_score x1 x2 x3 x4 0 1 (-1) 0) (four_batch_score x1 x2 x3 x4 1 1 1 0) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 0 1 (-1) 0) (four_batch_score x1 x2 x3 x4 1 1 1 0) xs    <= batch_variance w (four_batch_score x1 x2 x3 x4 0 1 (-1) 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 1 1 0) xs
 Premises and side conditions: Every listed outcome occurrence has nonnegative weight and the full sample mass is strictly positive. Repeated observations are counted with multiplicity. The two explicit score vectors are not assumed independent, jointly Gaussian or standardized.
 Proof/definition method: Specialize the shared kernel-checked finite-sample covariance Cauchy-Schwarz theorem to both explicit four-test score functions; no reproof or expansion of the weighted sum is performed.
 Library reuse: ListPoolingAlgebra and FourContrastCovariance own the covariance and contrast definitions; SampleContrastCauchy owns the general inequality; Rocq Stdlib real numbers and lists supply all operations.
 Boundary: Exact finite empirical covariance constraint on the named composites, not a separate distributional sampling law, population parameter estimate, chi-square pivot, normal tail or interval-coverage theorem.
*)
Theorem sample_contrast_cs_difference23_triple123 :
 forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->
   batch_covariance w (four_batch_score x1 x2 x3 x4 0 1 (-1) 0) (four_batch_score x1 x2 x3 x4 1 1 1 0) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 0 1 (-1) 0) (four_batch_score x1 x2 x3 x4 1 1 1 0) xs
   <= batch_variance w (four_batch_score x1 x2 x3 x4 0 1 (-1) 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 1 1 0) xs.
Proof.
 intros A w x1 x2 x3 x4 xs Hw Hm.
 exact (sample_covariance_cauchy_schwarz A w
   (four_batch_score x1 x2 x3 x4 0 1 (-1) 0) (four_batch_score x1 x2 x3 x4 1 1 1 0) xs Hw Hm).
Qed.

(** [sample_contrast_cs_difference23_triple124] (theorem).
 Mathematical meaning: For the second minus third test score contrast and the tests one, two and four score contrast, a nonnegative-weight finite sample must satisfy the sharp squared covariance-versus-variance feasibility constraint. The coefficients determine a specific multi-test contrast pair relevant to finite composite-score stability checks.
 Exact checked proposition: forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->    batch_covariance w (four_batch_score x1 x2 x3 x4 0 1 (-1) 0) (four_batch_score x1 x2 x3 x4 1 1 0 1) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 0 1 (-1) 0) (four_batch_score x1 x2 x3 x4 1 1 0 1) xs    <= batch_variance w (four_batch_score x1 x2 x3 x4 0 1 (-1) 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 1 0 1) xs
 Premises and side conditions: Every listed outcome occurrence has nonnegative weight and the full sample mass is strictly positive. Repeated observations are counted with multiplicity. The two explicit score vectors are not assumed independent, jointly Gaussian or standardized.
 Proof/definition method: Specialize the shared kernel-checked finite-sample covariance Cauchy-Schwarz theorem to both explicit four-test score functions; no reproof or expansion of the weighted sum is performed.
 Library reuse: ListPoolingAlgebra and FourContrastCovariance own the covariance and contrast definitions; SampleContrastCauchy owns the general inequality; Rocq Stdlib real numbers and lists supply all operations.
 Boundary: Exact finite empirical covariance constraint on the named composites, not a separate distributional sampling law, population parameter estimate, chi-square pivot, normal tail or interval-coverage theorem.
*)
Theorem sample_contrast_cs_difference23_triple124 :
 forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->
   batch_covariance w (four_batch_score x1 x2 x3 x4 0 1 (-1) 0) (four_batch_score x1 x2 x3 x4 1 1 0 1) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 0 1 (-1) 0) (four_batch_score x1 x2 x3 x4 1 1 0 1) xs
   <= batch_variance w (four_batch_score x1 x2 x3 x4 0 1 (-1) 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 1 0 1) xs.
Proof.
 intros A w x1 x2 x3 x4 xs Hw Hm.
 exact (sample_covariance_cauchy_schwarz A w
   (four_batch_score x1 x2 x3 x4 0 1 (-1) 0) (four_batch_score x1 x2 x3 x4 1 1 0 1) xs Hw Hm).
Qed.

(** [sample_contrast_cs_difference23_triple134] (theorem).
 Mathematical meaning: For the second minus third test score contrast and the tests one, three and four score contrast, a nonnegative-weight finite sample must satisfy the sharp squared covariance-versus-variance feasibility constraint. The coefficients determine a specific multi-test contrast pair relevant to finite composite-score stability checks.
 Exact checked proposition: forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->    batch_covariance w (four_batch_score x1 x2 x3 x4 0 1 (-1) 0) (four_batch_score x1 x2 x3 x4 1 0 1 1) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 0 1 (-1) 0) (four_batch_score x1 x2 x3 x4 1 0 1 1) xs    <= batch_variance w (four_batch_score x1 x2 x3 x4 0 1 (-1) 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 0 1 1) xs
 Premises and side conditions: Every listed outcome occurrence has nonnegative weight and the full sample mass is strictly positive. Repeated observations are counted with multiplicity. The two explicit score vectors are not assumed independent, jointly Gaussian or standardized.
 Proof/definition method: Specialize the shared kernel-checked finite-sample covariance Cauchy-Schwarz theorem to both explicit four-test score functions; no reproof or expansion of the weighted sum is performed.
 Library reuse: ListPoolingAlgebra and FourContrastCovariance own the covariance and contrast definitions; SampleContrastCauchy owns the general inequality; Rocq Stdlib real numbers and lists supply all operations.
 Boundary: Exact finite empirical covariance constraint on the named composites, not a separate distributional sampling law, population parameter estimate, chi-square pivot, normal tail or interval-coverage theorem.
*)
Theorem sample_contrast_cs_difference23_triple134 :
 forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->
   batch_covariance w (four_batch_score x1 x2 x3 x4 0 1 (-1) 0) (four_batch_score x1 x2 x3 x4 1 0 1 1) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 0 1 (-1) 0) (four_batch_score x1 x2 x3 x4 1 0 1 1) xs
   <= batch_variance w (four_batch_score x1 x2 x3 x4 0 1 (-1) 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 0 1 1) xs.
Proof.
 intros A w x1 x2 x3 x4 xs Hw Hm.
 exact (sample_covariance_cauchy_schwarz A w
   (four_batch_score x1 x2 x3 x4 0 1 (-1) 0) (four_batch_score x1 x2 x3 x4 1 0 1 1) xs Hw Hm).
Qed.

(** [sample_contrast_cs_difference23_triple234] (theorem).
 Mathematical meaning: For the second minus third test score contrast and the last three tests score contrast, a nonnegative-weight finite sample must satisfy the sharp squared covariance-versus-variance feasibility constraint. The coefficients determine a specific multi-test contrast pair relevant to finite composite-score stability checks.
 Exact checked proposition: forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->    batch_covariance w (four_batch_score x1 x2 x3 x4 0 1 (-1) 0) (four_batch_score x1 x2 x3 x4 0 1 1 1) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 0 1 (-1) 0) (four_batch_score x1 x2 x3 x4 0 1 1 1) xs    <= batch_variance w (four_batch_score x1 x2 x3 x4 0 1 (-1) 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 0 1 1 1) xs
 Premises and side conditions: Every listed outcome occurrence has nonnegative weight and the full sample mass is strictly positive. Repeated observations are counted with multiplicity. The two explicit score vectors are not assumed independent, jointly Gaussian or standardized.
 Proof/definition method: Specialize the shared kernel-checked finite-sample covariance Cauchy-Schwarz theorem to both explicit four-test score functions; no reproof or expansion of the weighted sum is performed.
 Library reuse: ListPoolingAlgebra and FourContrastCovariance own the covariance and contrast definitions; SampleContrastCauchy owns the general inequality; Rocq Stdlib real numbers and lists supply all operations.
 Boundary: Exact finite empirical covariance constraint on the named composites, not a separate distributional sampling law, population parameter estimate, chi-square pivot, normal tail or interval-coverage theorem.
*)
Theorem sample_contrast_cs_difference23_triple234 :
 forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->
   batch_covariance w (four_batch_score x1 x2 x3 x4 0 1 (-1) 0) (four_batch_score x1 x2 x3 x4 0 1 1 1) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 0 1 (-1) 0) (four_batch_score x1 x2 x3 x4 0 1 1 1) xs
   <= batch_variance w (four_batch_score x1 x2 x3 x4 0 1 (-1) 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 0 1 1 1) xs.
Proof.
 intros A w x1 x2 x3 x4 xs Hw Hm.
 exact (sample_covariance_cauchy_schwarz A w
   (four_batch_score x1 x2 x3 x4 0 1 (-1) 0) (four_batch_score x1 x2 x3 x4 0 1 1 1) xs Hw Hm).
Qed.

(** [sample_contrast_cs_difference23_allfour] (theorem).
 Mathematical meaning: For the second minus third test score contrast and the all four tests score contrast, a nonnegative-weight finite sample must satisfy the sharp squared covariance-versus-variance feasibility constraint. The coefficients determine a specific multi-test contrast pair relevant to finite composite-score stability checks.
 Exact checked proposition: forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->    batch_covariance w (four_batch_score x1 x2 x3 x4 0 1 (-1) 0) (four_batch_score x1 x2 x3 x4 1 1 1 1) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 0 1 (-1) 0) (four_batch_score x1 x2 x3 x4 1 1 1 1) xs    <= batch_variance w (four_batch_score x1 x2 x3 x4 0 1 (-1) 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 1 1 1) xs
 Premises and side conditions: Every listed outcome occurrence has nonnegative weight and the full sample mass is strictly positive. Repeated observations are counted with multiplicity. The two explicit score vectors are not assumed independent, jointly Gaussian or standardized.
 Proof/definition method: Specialize the shared kernel-checked finite-sample covariance Cauchy-Schwarz theorem to both explicit four-test score functions; no reproof or expansion of the weighted sum is performed.
 Library reuse: ListPoolingAlgebra and FourContrastCovariance own the covariance and contrast definitions; SampleContrastCauchy owns the general inequality; Rocq Stdlib real numbers and lists supply all operations.
 Boundary: Exact finite empirical covariance constraint on the named composites, not a separate distributional sampling law, population parameter estimate, chi-square pivot, normal tail or interval-coverage theorem.
*)
Theorem sample_contrast_cs_difference23_allfour :
 forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->
   batch_covariance w (four_batch_score x1 x2 x3 x4 0 1 (-1) 0) (four_batch_score x1 x2 x3 x4 1 1 1 1) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 0 1 (-1) 0) (four_batch_score x1 x2 x3 x4 1 1 1 1) xs
   <= batch_variance w (four_batch_score x1 x2 x3 x4 0 1 (-1) 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 1 1 1) xs.
Proof.
 intros A w x1 x2 x3 x4 xs Hw Hm.
 exact (sample_covariance_cauchy_schwarz A w
   (four_batch_score x1 x2 x3 x4 0 1 (-1) 0) (four_batch_score x1 x2 x3 x4 1 1 1 1) xs Hw Hm).
Qed.

(** [sample_contrast_cs_difference23_balanced12v34] (theorem).
 Mathematical meaning: For the second minus third test score contrast and the difference between the two pairs score contrast, a nonnegative-weight finite sample must satisfy the sharp squared covariance-versus-variance feasibility constraint. The coefficients determine a specific multi-test contrast pair relevant to finite composite-score stability checks.
 Exact checked proposition: forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->    batch_covariance w (four_batch_score x1 x2 x3 x4 0 1 (-1) 0) (four_batch_score x1 x2 x3 x4 1 1 (-1) (-1)) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 0 1 (-1) 0) (four_batch_score x1 x2 x3 x4 1 1 (-1) (-1)) xs    <= batch_variance w (four_batch_score x1 x2 x3 x4 0 1 (-1) 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 1 (-1) (-1)) xs
 Premises and side conditions: Every listed outcome occurrence has nonnegative weight and the full sample mass is strictly positive. Repeated observations are counted with multiplicity. The two explicit score vectors are not assumed independent, jointly Gaussian or standardized.
 Proof/definition method: Specialize the shared kernel-checked finite-sample covariance Cauchy-Schwarz theorem to both explicit four-test score functions; no reproof or expansion of the weighted sum is performed.
 Library reuse: ListPoolingAlgebra and FourContrastCovariance own the covariance and contrast definitions; SampleContrastCauchy owns the general inequality; Rocq Stdlib real numbers and lists supply all operations.
 Boundary: Exact finite empirical covariance constraint on the named composites, not a separate distributional sampling law, population parameter estimate, chi-square pivot, normal tail or interval-coverage theorem.
*)
Theorem sample_contrast_cs_difference23_balanced12v34 :
 forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->
   batch_covariance w (four_batch_score x1 x2 x3 x4 0 1 (-1) 0) (four_batch_score x1 x2 x3 x4 1 1 (-1) (-1)) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 0 1 (-1) 0) (four_batch_score x1 x2 x3 x4 1 1 (-1) (-1)) xs
   <= batch_variance w (four_batch_score x1 x2 x3 x4 0 1 (-1) 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 1 (-1) (-1)) xs.
Proof.
 intros A w x1 x2 x3 x4 xs Hw Hm.
 exact (sample_covariance_cauchy_schwarz A w
   (four_batch_score x1 x2 x3 x4 0 1 (-1) 0) (four_batch_score x1 x2 x3 x4 1 1 (-1) (-1)) xs Hw Hm).
Qed.

(** [sample_contrast_cs_difference24_difference24] (theorem).
 Mathematical meaning: For the second minus fourth test score contrast and the second minus fourth test score contrast, a nonnegative-weight finite sample must satisfy the sharp squared covariance-versus-variance feasibility constraint. The coefficients determine a specific multi-test contrast pair relevant to finite composite-score stability checks.
 Exact checked proposition: forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->    batch_covariance w (four_batch_score x1 x2 x3 x4 0 1 0 (-1)) (four_batch_score x1 x2 x3 x4 0 1 0 (-1)) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 0 1 0 (-1)) (four_batch_score x1 x2 x3 x4 0 1 0 (-1)) xs    <= batch_variance w (four_batch_score x1 x2 x3 x4 0 1 0 (-1)) xs * batch_variance w (four_batch_score x1 x2 x3 x4 0 1 0 (-1)) xs
 Premises and side conditions: Every listed outcome occurrence has nonnegative weight and the full sample mass is strictly positive. Repeated observations are counted with multiplicity. The two explicit score vectors are not assumed independent, jointly Gaussian or standardized.
 Proof/definition method: Specialize the shared kernel-checked finite-sample covariance Cauchy-Schwarz theorem to both explicit four-test score functions; no reproof or expansion of the weighted sum is performed.
 Library reuse: ListPoolingAlgebra and FourContrastCovariance own the covariance and contrast definitions; SampleContrastCauchy owns the general inequality; Rocq Stdlib real numbers and lists supply all operations.
 Boundary: Exact finite empirical covariance constraint on the named composites, not a separate distributional sampling law, population parameter estimate, chi-square pivot, normal tail or interval-coverage theorem.
*)
Theorem sample_contrast_cs_difference24_difference24 :
 forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->
   batch_covariance w (four_batch_score x1 x2 x3 x4 0 1 0 (-1)) (four_batch_score x1 x2 x3 x4 0 1 0 (-1)) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 0 1 0 (-1)) (four_batch_score x1 x2 x3 x4 0 1 0 (-1)) xs
   <= batch_variance w (four_batch_score x1 x2 x3 x4 0 1 0 (-1)) xs * batch_variance w (four_batch_score x1 x2 x3 x4 0 1 0 (-1)) xs.
Proof.
 intros A w x1 x2 x3 x4 xs Hw Hm.
 exact (sample_covariance_cauchy_schwarz A w
   (four_batch_score x1 x2 x3 x4 0 1 0 (-1)) (four_batch_score x1 x2 x3 x4 0 1 0 (-1)) xs Hw Hm).
Qed.

(** [sample_contrast_cs_difference24_difference34] (theorem).
 Mathematical meaning: For the second minus fourth test score contrast and the third minus fourth test score contrast, a nonnegative-weight finite sample must satisfy the sharp squared covariance-versus-variance feasibility constraint. The coefficients determine a specific multi-test contrast pair relevant to finite composite-score stability checks.
 Exact checked proposition: forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->    batch_covariance w (four_batch_score x1 x2 x3 x4 0 1 0 (-1)) (four_batch_score x1 x2 x3 x4 0 0 1 (-1)) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 0 1 0 (-1)) (four_batch_score x1 x2 x3 x4 0 0 1 (-1)) xs    <= batch_variance w (four_batch_score x1 x2 x3 x4 0 1 0 (-1)) xs * batch_variance w (four_batch_score x1 x2 x3 x4 0 0 1 (-1)) xs
 Premises and side conditions: Every listed outcome occurrence has nonnegative weight and the full sample mass is strictly positive. Repeated observations are counted with multiplicity. The two explicit score vectors are not assumed independent, jointly Gaussian or standardized.
 Proof/definition method: Specialize the shared kernel-checked finite-sample covariance Cauchy-Schwarz theorem to both explicit four-test score functions; no reproof or expansion of the weighted sum is performed.
 Library reuse: ListPoolingAlgebra and FourContrastCovariance own the covariance and contrast definitions; SampleContrastCauchy owns the general inequality; Rocq Stdlib real numbers and lists supply all operations.
 Boundary: Exact finite empirical covariance constraint on the named composites, not a separate distributional sampling law, population parameter estimate, chi-square pivot, normal tail or interval-coverage theorem.
*)
Theorem sample_contrast_cs_difference24_difference34 :
 forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->
   batch_covariance w (four_batch_score x1 x2 x3 x4 0 1 0 (-1)) (four_batch_score x1 x2 x3 x4 0 0 1 (-1)) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 0 1 0 (-1)) (four_batch_score x1 x2 x3 x4 0 0 1 (-1)) xs
   <= batch_variance w (four_batch_score x1 x2 x3 x4 0 1 0 (-1)) xs * batch_variance w (four_batch_score x1 x2 x3 x4 0 0 1 (-1)) xs.
Proof.
 intros A w x1 x2 x3 x4 xs Hw Hm.
 exact (sample_covariance_cauchy_schwarz A w
   (four_batch_score x1 x2 x3 x4 0 1 0 (-1)) (four_batch_score x1 x2 x3 x4 0 0 1 (-1)) xs Hw Hm).
Qed.

(** [sample_contrast_cs_difference24_triple123] (theorem).
 Mathematical meaning: For the second minus fourth test score contrast and the first three tests score contrast, a nonnegative-weight finite sample must satisfy the sharp squared covariance-versus-variance feasibility constraint. The coefficients determine a specific multi-test contrast pair relevant to finite composite-score stability checks.
 Exact checked proposition: forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->    batch_covariance w (four_batch_score x1 x2 x3 x4 0 1 0 (-1)) (four_batch_score x1 x2 x3 x4 1 1 1 0) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 0 1 0 (-1)) (four_batch_score x1 x2 x3 x4 1 1 1 0) xs    <= batch_variance w (four_batch_score x1 x2 x3 x4 0 1 0 (-1)) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 1 1 0) xs
 Premises and side conditions: Every listed outcome occurrence has nonnegative weight and the full sample mass is strictly positive. Repeated observations are counted with multiplicity. The two explicit score vectors are not assumed independent, jointly Gaussian or standardized.
 Proof/definition method: Specialize the shared kernel-checked finite-sample covariance Cauchy-Schwarz theorem to both explicit four-test score functions; no reproof or expansion of the weighted sum is performed.
 Library reuse: ListPoolingAlgebra and FourContrastCovariance own the covariance and contrast definitions; SampleContrastCauchy owns the general inequality; Rocq Stdlib real numbers and lists supply all operations.
 Boundary: Exact finite empirical covariance constraint on the named composites, not a separate distributional sampling law, population parameter estimate, chi-square pivot, normal tail or interval-coverage theorem.
*)
Theorem sample_contrast_cs_difference24_triple123 :
 forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->
   batch_covariance w (four_batch_score x1 x2 x3 x4 0 1 0 (-1)) (four_batch_score x1 x2 x3 x4 1 1 1 0) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 0 1 0 (-1)) (four_batch_score x1 x2 x3 x4 1 1 1 0) xs
   <= batch_variance w (four_batch_score x1 x2 x3 x4 0 1 0 (-1)) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 1 1 0) xs.
Proof.
 intros A w x1 x2 x3 x4 xs Hw Hm.
 exact (sample_covariance_cauchy_schwarz A w
   (four_batch_score x1 x2 x3 x4 0 1 0 (-1)) (four_batch_score x1 x2 x3 x4 1 1 1 0) xs Hw Hm).
Qed.

(** [sample_contrast_cs_difference24_triple124] (theorem).
 Mathematical meaning: For the second minus fourth test score contrast and the tests one, two and four score contrast, a nonnegative-weight finite sample must satisfy the sharp squared covariance-versus-variance feasibility constraint. The coefficients determine a specific multi-test contrast pair relevant to finite composite-score stability checks.
 Exact checked proposition: forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->    batch_covariance w (four_batch_score x1 x2 x3 x4 0 1 0 (-1)) (four_batch_score x1 x2 x3 x4 1 1 0 1) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 0 1 0 (-1)) (four_batch_score x1 x2 x3 x4 1 1 0 1) xs    <= batch_variance w (four_batch_score x1 x2 x3 x4 0 1 0 (-1)) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 1 0 1) xs
 Premises and side conditions: Every listed outcome occurrence has nonnegative weight and the full sample mass is strictly positive. Repeated observations are counted with multiplicity. The two explicit score vectors are not assumed independent, jointly Gaussian or standardized.
 Proof/definition method: Specialize the shared kernel-checked finite-sample covariance Cauchy-Schwarz theorem to both explicit four-test score functions; no reproof or expansion of the weighted sum is performed.
 Library reuse: ListPoolingAlgebra and FourContrastCovariance own the covariance and contrast definitions; SampleContrastCauchy owns the general inequality; Rocq Stdlib real numbers and lists supply all operations.
 Boundary: Exact finite empirical covariance constraint on the named composites, not a separate distributional sampling law, population parameter estimate, chi-square pivot, normal tail or interval-coverage theorem.
*)
Theorem sample_contrast_cs_difference24_triple124 :
 forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->
   batch_covariance w (four_batch_score x1 x2 x3 x4 0 1 0 (-1)) (four_batch_score x1 x2 x3 x4 1 1 0 1) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 0 1 0 (-1)) (four_batch_score x1 x2 x3 x4 1 1 0 1) xs
   <= batch_variance w (four_batch_score x1 x2 x3 x4 0 1 0 (-1)) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 1 0 1) xs.
Proof.
 intros A w x1 x2 x3 x4 xs Hw Hm.
 exact (sample_covariance_cauchy_schwarz A w
   (four_batch_score x1 x2 x3 x4 0 1 0 (-1)) (four_batch_score x1 x2 x3 x4 1 1 0 1) xs Hw Hm).
Qed.

(** [sample_contrast_cs_difference24_triple134] (theorem).
 Mathematical meaning: For the second minus fourth test score contrast and the tests one, three and four score contrast, a nonnegative-weight finite sample must satisfy the sharp squared covariance-versus-variance feasibility constraint. The coefficients determine a specific multi-test contrast pair relevant to finite composite-score stability checks.
 Exact checked proposition: forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->    batch_covariance w (four_batch_score x1 x2 x3 x4 0 1 0 (-1)) (four_batch_score x1 x2 x3 x4 1 0 1 1) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 0 1 0 (-1)) (four_batch_score x1 x2 x3 x4 1 0 1 1) xs    <= batch_variance w (four_batch_score x1 x2 x3 x4 0 1 0 (-1)) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 0 1 1) xs
 Premises and side conditions: Every listed outcome occurrence has nonnegative weight and the full sample mass is strictly positive. Repeated observations are counted with multiplicity. The two explicit score vectors are not assumed independent, jointly Gaussian or standardized.
 Proof/definition method: Specialize the shared kernel-checked finite-sample covariance Cauchy-Schwarz theorem to both explicit four-test score functions; no reproof or expansion of the weighted sum is performed.
 Library reuse: ListPoolingAlgebra and FourContrastCovariance own the covariance and contrast definitions; SampleContrastCauchy owns the general inequality; Rocq Stdlib real numbers and lists supply all operations.
 Boundary: Exact finite empirical covariance constraint on the named composites, not a separate distributional sampling law, population parameter estimate, chi-square pivot, normal tail or interval-coverage theorem.
*)
Theorem sample_contrast_cs_difference24_triple134 :
 forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->
   batch_covariance w (four_batch_score x1 x2 x3 x4 0 1 0 (-1)) (four_batch_score x1 x2 x3 x4 1 0 1 1) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 0 1 0 (-1)) (four_batch_score x1 x2 x3 x4 1 0 1 1) xs
   <= batch_variance w (four_batch_score x1 x2 x3 x4 0 1 0 (-1)) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 0 1 1) xs.
Proof.
 intros A w x1 x2 x3 x4 xs Hw Hm.
 exact (sample_covariance_cauchy_schwarz A w
   (four_batch_score x1 x2 x3 x4 0 1 0 (-1)) (four_batch_score x1 x2 x3 x4 1 0 1 1) xs Hw Hm).
Qed.

(** [sample_contrast_cs_difference24_triple234] (theorem).
 Mathematical meaning: For the second minus fourth test score contrast and the last three tests score contrast, a nonnegative-weight finite sample must satisfy the sharp squared covariance-versus-variance feasibility constraint. The coefficients determine a specific multi-test contrast pair relevant to finite composite-score stability checks.
 Exact checked proposition: forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->    batch_covariance w (four_batch_score x1 x2 x3 x4 0 1 0 (-1)) (four_batch_score x1 x2 x3 x4 0 1 1 1) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 0 1 0 (-1)) (four_batch_score x1 x2 x3 x4 0 1 1 1) xs    <= batch_variance w (four_batch_score x1 x2 x3 x4 0 1 0 (-1)) xs * batch_variance w (four_batch_score x1 x2 x3 x4 0 1 1 1) xs
 Premises and side conditions: Every listed outcome occurrence has nonnegative weight and the full sample mass is strictly positive. Repeated observations are counted with multiplicity. The two explicit score vectors are not assumed independent, jointly Gaussian or standardized.
 Proof/definition method: Specialize the shared kernel-checked finite-sample covariance Cauchy-Schwarz theorem to both explicit four-test score functions; no reproof or expansion of the weighted sum is performed.
 Library reuse: ListPoolingAlgebra and FourContrastCovariance own the covariance and contrast definitions; SampleContrastCauchy owns the general inequality; Rocq Stdlib real numbers and lists supply all operations.
 Boundary: Exact finite empirical covariance constraint on the named composites, not a separate distributional sampling law, population parameter estimate, chi-square pivot, normal tail or interval-coverage theorem.
*)
Theorem sample_contrast_cs_difference24_triple234 :
 forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->
   batch_covariance w (four_batch_score x1 x2 x3 x4 0 1 0 (-1)) (four_batch_score x1 x2 x3 x4 0 1 1 1) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 0 1 0 (-1)) (four_batch_score x1 x2 x3 x4 0 1 1 1) xs
   <= batch_variance w (four_batch_score x1 x2 x3 x4 0 1 0 (-1)) xs * batch_variance w (four_batch_score x1 x2 x3 x4 0 1 1 1) xs.
Proof.
 intros A w x1 x2 x3 x4 xs Hw Hm.
 exact (sample_covariance_cauchy_schwarz A w
   (four_batch_score x1 x2 x3 x4 0 1 0 (-1)) (four_batch_score x1 x2 x3 x4 0 1 1 1) xs Hw Hm).
Qed.

(** [sample_contrast_cs_difference24_allfour] (theorem).
 Mathematical meaning: For the second minus fourth test score contrast and the all four tests score contrast, a nonnegative-weight finite sample must satisfy the sharp squared covariance-versus-variance feasibility constraint. The coefficients determine a specific multi-test contrast pair relevant to finite composite-score stability checks.
 Exact checked proposition: forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->    batch_covariance w (four_batch_score x1 x2 x3 x4 0 1 0 (-1)) (four_batch_score x1 x2 x3 x4 1 1 1 1) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 0 1 0 (-1)) (four_batch_score x1 x2 x3 x4 1 1 1 1) xs    <= batch_variance w (four_batch_score x1 x2 x3 x4 0 1 0 (-1)) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 1 1 1) xs
 Premises and side conditions: Every listed outcome occurrence has nonnegative weight and the full sample mass is strictly positive. Repeated observations are counted with multiplicity. The two explicit score vectors are not assumed independent, jointly Gaussian or standardized.
 Proof/definition method: Specialize the shared kernel-checked finite-sample covariance Cauchy-Schwarz theorem to both explicit four-test score functions; no reproof or expansion of the weighted sum is performed.
 Library reuse: ListPoolingAlgebra and FourContrastCovariance own the covariance and contrast definitions; SampleContrastCauchy owns the general inequality; Rocq Stdlib real numbers and lists supply all operations.
 Boundary: Exact finite empirical covariance constraint on the named composites, not a separate distributional sampling law, population parameter estimate, chi-square pivot, normal tail or interval-coverage theorem.
*)
Theorem sample_contrast_cs_difference24_allfour :
 forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->
   batch_covariance w (four_batch_score x1 x2 x3 x4 0 1 0 (-1)) (four_batch_score x1 x2 x3 x4 1 1 1 1) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 0 1 0 (-1)) (four_batch_score x1 x2 x3 x4 1 1 1 1) xs
   <= batch_variance w (four_batch_score x1 x2 x3 x4 0 1 0 (-1)) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 1 1 1) xs.
Proof.
 intros A w x1 x2 x3 x4 xs Hw Hm.
 exact (sample_covariance_cauchy_schwarz A w
   (four_batch_score x1 x2 x3 x4 0 1 0 (-1)) (four_batch_score x1 x2 x3 x4 1 1 1 1) xs Hw Hm).
Qed.

(** [sample_contrast_cs_difference24_balanced12v34] (theorem).
 Mathematical meaning: For the second minus fourth test score contrast and the difference between the two pairs score contrast, a nonnegative-weight finite sample must satisfy the sharp squared covariance-versus-variance feasibility constraint. The coefficients determine a specific multi-test contrast pair relevant to finite composite-score stability checks.
 Exact checked proposition: forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->    batch_covariance w (four_batch_score x1 x2 x3 x4 0 1 0 (-1)) (four_batch_score x1 x2 x3 x4 1 1 (-1) (-1)) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 0 1 0 (-1)) (four_batch_score x1 x2 x3 x4 1 1 (-1) (-1)) xs    <= batch_variance w (four_batch_score x1 x2 x3 x4 0 1 0 (-1)) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 1 (-1) (-1)) xs
 Premises and side conditions: Every listed outcome occurrence has nonnegative weight and the full sample mass is strictly positive. Repeated observations are counted with multiplicity. The two explicit score vectors are not assumed independent, jointly Gaussian or standardized.
 Proof/definition method: Specialize the shared kernel-checked finite-sample covariance Cauchy-Schwarz theorem to both explicit four-test score functions; no reproof or expansion of the weighted sum is performed.
 Library reuse: ListPoolingAlgebra and FourContrastCovariance own the covariance and contrast definitions; SampleContrastCauchy owns the general inequality; Rocq Stdlib real numbers and lists supply all operations.
 Boundary: Exact finite empirical covariance constraint on the named composites, not a separate distributional sampling law, population parameter estimate, chi-square pivot, normal tail or interval-coverage theorem.
*)
Theorem sample_contrast_cs_difference24_balanced12v34 :
 forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->
   batch_covariance w (four_batch_score x1 x2 x3 x4 0 1 0 (-1)) (four_batch_score x1 x2 x3 x4 1 1 (-1) (-1)) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 0 1 0 (-1)) (four_batch_score x1 x2 x3 x4 1 1 (-1) (-1)) xs
   <= batch_variance w (four_batch_score x1 x2 x3 x4 0 1 0 (-1)) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 1 (-1) (-1)) xs.
Proof.
 intros A w x1 x2 x3 x4 xs Hw Hm.
 exact (sample_covariance_cauchy_schwarz A w
   (four_batch_score x1 x2 x3 x4 0 1 0 (-1)) (four_batch_score x1 x2 x3 x4 1 1 (-1) (-1)) xs Hw Hm).
Qed.

(** [sample_contrast_cs_difference34_difference34] (theorem).
 Mathematical meaning: For the third minus fourth test score contrast and the third minus fourth test score contrast, a nonnegative-weight finite sample must satisfy the sharp squared covariance-versus-variance feasibility constraint. The coefficients determine a specific multi-test contrast pair relevant to finite composite-score stability checks.
 Exact checked proposition: forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->    batch_covariance w (four_batch_score x1 x2 x3 x4 0 0 1 (-1)) (four_batch_score x1 x2 x3 x4 0 0 1 (-1)) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 0 0 1 (-1)) (four_batch_score x1 x2 x3 x4 0 0 1 (-1)) xs    <= batch_variance w (four_batch_score x1 x2 x3 x4 0 0 1 (-1)) xs * batch_variance w (four_batch_score x1 x2 x3 x4 0 0 1 (-1)) xs
 Premises and side conditions: Every listed outcome occurrence has nonnegative weight and the full sample mass is strictly positive. Repeated observations are counted with multiplicity. The two explicit score vectors are not assumed independent, jointly Gaussian or standardized.
 Proof/definition method: Specialize the shared kernel-checked finite-sample covariance Cauchy-Schwarz theorem to both explicit four-test score functions; no reproof or expansion of the weighted sum is performed.
 Library reuse: ListPoolingAlgebra and FourContrastCovariance own the covariance and contrast definitions; SampleContrastCauchy owns the general inequality; Rocq Stdlib real numbers and lists supply all operations.
 Boundary: Exact finite empirical covariance constraint on the named composites, not a separate distributional sampling law, population parameter estimate, chi-square pivot, normal tail or interval-coverage theorem.
*)
Theorem sample_contrast_cs_difference34_difference34 :
 forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->
   batch_covariance w (four_batch_score x1 x2 x3 x4 0 0 1 (-1)) (four_batch_score x1 x2 x3 x4 0 0 1 (-1)) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 0 0 1 (-1)) (four_batch_score x1 x2 x3 x4 0 0 1 (-1)) xs
   <= batch_variance w (four_batch_score x1 x2 x3 x4 0 0 1 (-1)) xs * batch_variance w (four_batch_score x1 x2 x3 x4 0 0 1 (-1)) xs.
Proof.
 intros A w x1 x2 x3 x4 xs Hw Hm.
 exact (sample_covariance_cauchy_schwarz A w
   (four_batch_score x1 x2 x3 x4 0 0 1 (-1)) (four_batch_score x1 x2 x3 x4 0 0 1 (-1)) xs Hw Hm).
Qed.

(** [sample_contrast_cs_difference34_triple123] (theorem).
 Mathematical meaning: For the third minus fourth test score contrast and the first three tests score contrast, a nonnegative-weight finite sample must satisfy the sharp squared covariance-versus-variance feasibility constraint. The coefficients determine a specific multi-test contrast pair relevant to finite composite-score stability checks.
 Exact checked proposition: forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->    batch_covariance w (four_batch_score x1 x2 x3 x4 0 0 1 (-1)) (four_batch_score x1 x2 x3 x4 1 1 1 0) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 0 0 1 (-1)) (four_batch_score x1 x2 x3 x4 1 1 1 0) xs    <= batch_variance w (four_batch_score x1 x2 x3 x4 0 0 1 (-1)) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 1 1 0) xs
 Premises and side conditions: Every listed outcome occurrence has nonnegative weight and the full sample mass is strictly positive. Repeated observations are counted with multiplicity. The two explicit score vectors are not assumed independent, jointly Gaussian or standardized.
 Proof/definition method: Specialize the shared kernel-checked finite-sample covariance Cauchy-Schwarz theorem to both explicit four-test score functions; no reproof or expansion of the weighted sum is performed.
 Library reuse: ListPoolingAlgebra and FourContrastCovariance own the covariance and contrast definitions; SampleContrastCauchy owns the general inequality; Rocq Stdlib real numbers and lists supply all operations.
 Boundary: Exact finite empirical covariance constraint on the named composites, not a separate distributional sampling law, population parameter estimate, chi-square pivot, normal tail or interval-coverage theorem.
*)
Theorem sample_contrast_cs_difference34_triple123 :
 forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->
   batch_covariance w (four_batch_score x1 x2 x3 x4 0 0 1 (-1)) (four_batch_score x1 x2 x3 x4 1 1 1 0) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 0 0 1 (-1)) (four_batch_score x1 x2 x3 x4 1 1 1 0) xs
   <= batch_variance w (four_batch_score x1 x2 x3 x4 0 0 1 (-1)) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 1 1 0) xs.
Proof.
 intros A w x1 x2 x3 x4 xs Hw Hm.
 exact (sample_covariance_cauchy_schwarz A w
   (four_batch_score x1 x2 x3 x4 0 0 1 (-1)) (four_batch_score x1 x2 x3 x4 1 1 1 0) xs Hw Hm).
Qed.

(** [sample_contrast_cs_difference34_triple124] (theorem).
 Mathematical meaning: For the third minus fourth test score contrast and the tests one, two and four score contrast, a nonnegative-weight finite sample must satisfy the sharp squared covariance-versus-variance feasibility constraint. The coefficients determine a specific multi-test contrast pair relevant to finite composite-score stability checks.
 Exact checked proposition: forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->    batch_covariance w (four_batch_score x1 x2 x3 x4 0 0 1 (-1)) (four_batch_score x1 x2 x3 x4 1 1 0 1) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 0 0 1 (-1)) (four_batch_score x1 x2 x3 x4 1 1 0 1) xs    <= batch_variance w (four_batch_score x1 x2 x3 x4 0 0 1 (-1)) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 1 0 1) xs
 Premises and side conditions: Every listed outcome occurrence has nonnegative weight and the full sample mass is strictly positive. Repeated observations are counted with multiplicity. The two explicit score vectors are not assumed independent, jointly Gaussian or standardized.
 Proof/definition method: Specialize the shared kernel-checked finite-sample covariance Cauchy-Schwarz theorem to both explicit four-test score functions; no reproof or expansion of the weighted sum is performed.
 Library reuse: ListPoolingAlgebra and FourContrastCovariance own the covariance and contrast definitions; SampleContrastCauchy owns the general inequality; Rocq Stdlib real numbers and lists supply all operations.
 Boundary: Exact finite empirical covariance constraint on the named composites, not a separate distributional sampling law, population parameter estimate, chi-square pivot, normal tail or interval-coverage theorem.
*)
Theorem sample_contrast_cs_difference34_triple124 :
 forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->
   batch_covariance w (four_batch_score x1 x2 x3 x4 0 0 1 (-1)) (four_batch_score x1 x2 x3 x4 1 1 0 1) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 0 0 1 (-1)) (four_batch_score x1 x2 x3 x4 1 1 0 1) xs
   <= batch_variance w (four_batch_score x1 x2 x3 x4 0 0 1 (-1)) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 1 0 1) xs.
Proof.
 intros A w x1 x2 x3 x4 xs Hw Hm.
 exact (sample_covariance_cauchy_schwarz A w
   (four_batch_score x1 x2 x3 x4 0 0 1 (-1)) (four_batch_score x1 x2 x3 x4 1 1 0 1) xs Hw Hm).
Qed.

(** [sample_contrast_cs_difference34_triple134] (theorem).
 Mathematical meaning: For the third minus fourth test score contrast and the tests one, three and four score contrast, a nonnegative-weight finite sample must satisfy the sharp squared covariance-versus-variance feasibility constraint. The coefficients determine a specific multi-test contrast pair relevant to finite composite-score stability checks.
 Exact checked proposition: forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->    batch_covariance w (four_batch_score x1 x2 x3 x4 0 0 1 (-1)) (four_batch_score x1 x2 x3 x4 1 0 1 1) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 0 0 1 (-1)) (four_batch_score x1 x2 x3 x4 1 0 1 1) xs    <= batch_variance w (four_batch_score x1 x2 x3 x4 0 0 1 (-1)) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 0 1 1) xs
 Premises and side conditions: Every listed outcome occurrence has nonnegative weight and the full sample mass is strictly positive. Repeated observations are counted with multiplicity. The two explicit score vectors are not assumed independent, jointly Gaussian or standardized.
 Proof/definition method: Specialize the shared kernel-checked finite-sample covariance Cauchy-Schwarz theorem to both explicit four-test score functions; no reproof or expansion of the weighted sum is performed.
 Library reuse: ListPoolingAlgebra and FourContrastCovariance own the covariance and contrast definitions; SampleContrastCauchy owns the general inequality; Rocq Stdlib real numbers and lists supply all operations.
 Boundary: Exact finite empirical covariance constraint on the named composites, not a separate distributional sampling law, population parameter estimate, chi-square pivot, normal tail or interval-coverage theorem.
*)
Theorem sample_contrast_cs_difference34_triple134 :
 forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->
   batch_covariance w (four_batch_score x1 x2 x3 x4 0 0 1 (-1)) (four_batch_score x1 x2 x3 x4 1 0 1 1) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 0 0 1 (-1)) (four_batch_score x1 x2 x3 x4 1 0 1 1) xs
   <= batch_variance w (four_batch_score x1 x2 x3 x4 0 0 1 (-1)) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 0 1 1) xs.
Proof.
 intros A w x1 x2 x3 x4 xs Hw Hm.
 exact (sample_covariance_cauchy_schwarz A w
   (four_batch_score x1 x2 x3 x4 0 0 1 (-1)) (four_batch_score x1 x2 x3 x4 1 0 1 1) xs Hw Hm).
Qed.

(** [sample_contrast_cs_difference34_triple234] (theorem).
 Mathematical meaning: For the third minus fourth test score contrast and the last three tests score contrast, a nonnegative-weight finite sample must satisfy the sharp squared covariance-versus-variance feasibility constraint. The coefficients determine a specific multi-test contrast pair relevant to finite composite-score stability checks.
 Exact checked proposition: forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->    batch_covariance w (four_batch_score x1 x2 x3 x4 0 0 1 (-1)) (four_batch_score x1 x2 x3 x4 0 1 1 1) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 0 0 1 (-1)) (four_batch_score x1 x2 x3 x4 0 1 1 1) xs    <= batch_variance w (four_batch_score x1 x2 x3 x4 0 0 1 (-1)) xs * batch_variance w (four_batch_score x1 x2 x3 x4 0 1 1 1) xs
 Premises and side conditions: Every listed outcome occurrence has nonnegative weight and the full sample mass is strictly positive. Repeated observations are counted with multiplicity. The two explicit score vectors are not assumed independent, jointly Gaussian or standardized.
 Proof/definition method: Specialize the shared kernel-checked finite-sample covariance Cauchy-Schwarz theorem to both explicit four-test score functions; no reproof or expansion of the weighted sum is performed.
 Library reuse: ListPoolingAlgebra and FourContrastCovariance own the covariance and contrast definitions; SampleContrastCauchy owns the general inequality; Rocq Stdlib real numbers and lists supply all operations.
 Boundary: Exact finite empirical covariance constraint on the named composites, not a separate distributional sampling law, population parameter estimate, chi-square pivot, normal tail or interval-coverage theorem.
*)
Theorem sample_contrast_cs_difference34_triple234 :
 forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->
   batch_covariance w (four_batch_score x1 x2 x3 x4 0 0 1 (-1)) (four_batch_score x1 x2 x3 x4 0 1 1 1) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 0 0 1 (-1)) (four_batch_score x1 x2 x3 x4 0 1 1 1) xs
   <= batch_variance w (four_batch_score x1 x2 x3 x4 0 0 1 (-1)) xs * batch_variance w (four_batch_score x1 x2 x3 x4 0 1 1 1) xs.
Proof.
 intros A w x1 x2 x3 x4 xs Hw Hm.
 exact (sample_covariance_cauchy_schwarz A w
   (four_batch_score x1 x2 x3 x4 0 0 1 (-1)) (four_batch_score x1 x2 x3 x4 0 1 1 1) xs Hw Hm).
Qed.

(** [sample_contrast_cs_difference34_allfour] (theorem).
 Mathematical meaning: For the third minus fourth test score contrast and the all four tests score contrast, a nonnegative-weight finite sample must satisfy the sharp squared covariance-versus-variance feasibility constraint. The coefficients determine a specific multi-test contrast pair relevant to finite composite-score stability checks.
 Exact checked proposition: forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->    batch_covariance w (four_batch_score x1 x2 x3 x4 0 0 1 (-1)) (four_batch_score x1 x2 x3 x4 1 1 1 1) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 0 0 1 (-1)) (four_batch_score x1 x2 x3 x4 1 1 1 1) xs    <= batch_variance w (four_batch_score x1 x2 x3 x4 0 0 1 (-1)) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 1 1 1) xs
 Premises and side conditions: Every listed outcome occurrence has nonnegative weight and the full sample mass is strictly positive. Repeated observations are counted with multiplicity. The two explicit score vectors are not assumed independent, jointly Gaussian or standardized.
 Proof/definition method: Specialize the shared kernel-checked finite-sample covariance Cauchy-Schwarz theorem to both explicit four-test score functions; no reproof or expansion of the weighted sum is performed.
 Library reuse: ListPoolingAlgebra and FourContrastCovariance own the covariance and contrast definitions; SampleContrastCauchy owns the general inequality; Rocq Stdlib real numbers and lists supply all operations.
 Boundary: Exact finite empirical covariance constraint on the named composites, not a separate distributional sampling law, population parameter estimate, chi-square pivot, normal tail or interval-coverage theorem.
*)
Theorem sample_contrast_cs_difference34_allfour :
 forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->
   batch_covariance w (four_batch_score x1 x2 x3 x4 0 0 1 (-1)) (four_batch_score x1 x2 x3 x4 1 1 1 1) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 0 0 1 (-1)) (four_batch_score x1 x2 x3 x4 1 1 1 1) xs
   <= batch_variance w (four_batch_score x1 x2 x3 x4 0 0 1 (-1)) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 1 1 1) xs.
Proof.
 intros A w x1 x2 x3 x4 xs Hw Hm.
 exact (sample_covariance_cauchy_schwarz A w
   (four_batch_score x1 x2 x3 x4 0 0 1 (-1)) (four_batch_score x1 x2 x3 x4 1 1 1 1) xs Hw Hm).
Qed.

(** [sample_contrast_cs_difference34_balanced12v34] (theorem).
 Mathematical meaning: For the third minus fourth test score contrast and the difference between the two pairs score contrast, a nonnegative-weight finite sample must satisfy the sharp squared covariance-versus-variance feasibility constraint. The coefficients determine a specific multi-test contrast pair relevant to finite composite-score stability checks.
 Exact checked proposition: forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->    batch_covariance w (four_batch_score x1 x2 x3 x4 0 0 1 (-1)) (four_batch_score x1 x2 x3 x4 1 1 (-1) (-1)) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 0 0 1 (-1)) (four_batch_score x1 x2 x3 x4 1 1 (-1) (-1)) xs    <= batch_variance w (four_batch_score x1 x2 x3 x4 0 0 1 (-1)) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 1 (-1) (-1)) xs
 Premises and side conditions: Every listed outcome occurrence has nonnegative weight and the full sample mass is strictly positive. Repeated observations are counted with multiplicity. The two explicit score vectors are not assumed independent, jointly Gaussian or standardized.
 Proof/definition method: Specialize the shared kernel-checked finite-sample covariance Cauchy-Schwarz theorem to both explicit four-test score functions; no reproof or expansion of the weighted sum is performed.
 Library reuse: ListPoolingAlgebra and FourContrastCovariance own the covariance and contrast definitions; SampleContrastCauchy owns the general inequality; Rocq Stdlib real numbers and lists supply all operations.
 Boundary: Exact finite empirical covariance constraint on the named composites, not a separate distributional sampling law, population parameter estimate, chi-square pivot, normal tail or interval-coverage theorem.
*)
Theorem sample_contrast_cs_difference34_balanced12v34 :
 forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->
   batch_covariance w (four_batch_score x1 x2 x3 x4 0 0 1 (-1)) (four_batch_score x1 x2 x3 x4 1 1 (-1) (-1)) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 0 0 1 (-1)) (four_batch_score x1 x2 x3 x4 1 1 (-1) (-1)) xs
   <= batch_variance w (four_batch_score x1 x2 x3 x4 0 0 1 (-1)) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 1 (-1) (-1)) xs.
Proof.
 intros A w x1 x2 x3 x4 xs Hw Hm.
 exact (sample_covariance_cauchy_schwarz A w
   (four_batch_score x1 x2 x3 x4 0 0 1 (-1)) (four_batch_score x1 x2 x3 x4 1 1 (-1) (-1)) xs Hw Hm).
Qed.

(** [sample_contrast_cs_triple123_triple123] (theorem).
 Mathematical meaning: For the first three tests score contrast and the first three tests score contrast, a nonnegative-weight finite sample must satisfy the sharp squared covariance-versus-variance feasibility constraint. The coefficients determine a specific multi-test contrast pair relevant to finite composite-score stability checks.
 Exact checked proposition: forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->    batch_covariance w (four_batch_score x1 x2 x3 x4 1 1 1 0) (four_batch_score x1 x2 x3 x4 1 1 1 0) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 1 1 1 0) (four_batch_score x1 x2 x3 x4 1 1 1 0) xs    <= batch_variance w (four_batch_score x1 x2 x3 x4 1 1 1 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 1 1 0) xs
 Premises and side conditions: Every listed outcome occurrence has nonnegative weight and the full sample mass is strictly positive. Repeated observations are counted with multiplicity. The two explicit score vectors are not assumed independent, jointly Gaussian or standardized.
 Proof/definition method: Specialize the shared kernel-checked finite-sample covariance Cauchy-Schwarz theorem to both explicit four-test score functions; no reproof or expansion of the weighted sum is performed.
 Library reuse: ListPoolingAlgebra and FourContrastCovariance own the covariance and contrast definitions; SampleContrastCauchy owns the general inequality; Rocq Stdlib real numbers and lists supply all operations.
 Boundary: Exact finite empirical covariance constraint on the named composites, not a separate distributional sampling law, population parameter estimate, chi-square pivot, normal tail or interval-coverage theorem.
*)
Theorem sample_contrast_cs_triple123_triple123 :
 forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->
   batch_covariance w (four_batch_score x1 x2 x3 x4 1 1 1 0) (four_batch_score x1 x2 x3 x4 1 1 1 0) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 1 1 1 0) (four_batch_score x1 x2 x3 x4 1 1 1 0) xs
   <= batch_variance w (four_batch_score x1 x2 x3 x4 1 1 1 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 1 1 0) xs.
Proof.
 intros A w x1 x2 x3 x4 xs Hw Hm.
 exact (sample_covariance_cauchy_schwarz A w
   (four_batch_score x1 x2 x3 x4 1 1 1 0) (four_batch_score x1 x2 x3 x4 1 1 1 0) xs Hw Hm).
Qed.

(** [sample_contrast_cs_triple123_triple124] (theorem).
 Mathematical meaning: For the first three tests score contrast and the tests one, two and four score contrast, a nonnegative-weight finite sample must satisfy the sharp squared covariance-versus-variance feasibility constraint. The coefficients determine a specific multi-test contrast pair relevant to finite composite-score stability checks.
 Exact checked proposition: forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->    batch_covariance w (four_batch_score x1 x2 x3 x4 1 1 1 0) (four_batch_score x1 x2 x3 x4 1 1 0 1) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 1 1 1 0) (four_batch_score x1 x2 x3 x4 1 1 0 1) xs    <= batch_variance w (four_batch_score x1 x2 x3 x4 1 1 1 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 1 0 1) xs
 Premises and side conditions: Every listed outcome occurrence has nonnegative weight and the full sample mass is strictly positive. Repeated observations are counted with multiplicity. The two explicit score vectors are not assumed independent, jointly Gaussian or standardized.
 Proof/definition method: Specialize the shared kernel-checked finite-sample covariance Cauchy-Schwarz theorem to both explicit four-test score functions; no reproof or expansion of the weighted sum is performed.
 Library reuse: ListPoolingAlgebra and FourContrastCovariance own the covariance and contrast definitions; SampleContrastCauchy owns the general inequality; Rocq Stdlib real numbers and lists supply all operations.
 Boundary: Exact finite empirical covariance constraint on the named composites, not a separate distributional sampling law, population parameter estimate, chi-square pivot, normal tail or interval-coverage theorem.
*)
Theorem sample_contrast_cs_triple123_triple124 :
 forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->
   batch_covariance w (four_batch_score x1 x2 x3 x4 1 1 1 0) (four_batch_score x1 x2 x3 x4 1 1 0 1) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 1 1 1 0) (four_batch_score x1 x2 x3 x4 1 1 0 1) xs
   <= batch_variance w (four_batch_score x1 x2 x3 x4 1 1 1 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 1 0 1) xs.
Proof.
 intros A w x1 x2 x3 x4 xs Hw Hm.
 exact (sample_covariance_cauchy_schwarz A w
   (four_batch_score x1 x2 x3 x4 1 1 1 0) (four_batch_score x1 x2 x3 x4 1 1 0 1) xs Hw Hm).
Qed.

(** [sample_contrast_cs_triple123_triple134] (theorem).
 Mathematical meaning: For the first three tests score contrast and the tests one, three and four score contrast, a nonnegative-weight finite sample must satisfy the sharp squared covariance-versus-variance feasibility constraint. The coefficients determine a specific multi-test contrast pair relevant to finite composite-score stability checks.
 Exact checked proposition: forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->    batch_covariance w (four_batch_score x1 x2 x3 x4 1 1 1 0) (four_batch_score x1 x2 x3 x4 1 0 1 1) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 1 1 1 0) (four_batch_score x1 x2 x3 x4 1 0 1 1) xs    <= batch_variance w (four_batch_score x1 x2 x3 x4 1 1 1 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 0 1 1) xs
 Premises and side conditions: Every listed outcome occurrence has nonnegative weight and the full sample mass is strictly positive. Repeated observations are counted with multiplicity. The two explicit score vectors are not assumed independent, jointly Gaussian or standardized.
 Proof/definition method: Specialize the shared kernel-checked finite-sample covariance Cauchy-Schwarz theorem to both explicit four-test score functions; no reproof or expansion of the weighted sum is performed.
 Library reuse: ListPoolingAlgebra and FourContrastCovariance own the covariance and contrast definitions; SampleContrastCauchy owns the general inequality; Rocq Stdlib real numbers and lists supply all operations.
 Boundary: Exact finite empirical covariance constraint on the named composites, not a separate distributional sampling law, population parameter estimate, chi-square pivot, normal tail or interval-coverage theorem.
*)
Theorem sample_contrast_cs_triple123_triple134 :
 forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->
   batch_covariance w (four_batch_score x1 x2 x3 x4 1 1 1 0) (four_batch_score x1 x2 x3 x4 1 0 1 1) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 1 1 1 0) (four_batch_score x1 x2 x3 x4 1 0 1 1) xs
   <= batch_variance w (four_batch_score x1 x2 x3 x4 1 1 1 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 0 1 1) xs.
Proof.
 intros A w x1 x2 x3 x4 xs Hw Hm.
 exact (sample_covariance_cauchy_schwarz A w
   (four_batch_score x1 x2 x3 x4 1 1 1 0) (four_batch_score x1 x2 x3 x4 1 0 1 1) xs Hw Hm).
Qed.

(** [sample_contrast_cs_triple123_triple234] (theorem).
 Mathematical meaning: For the first three tests score contrast and the last three tests score contrast, a nonnegative-weight finite sample must satisfy the sharp squared covariance-versus-variance feasibility constraint. The coefficients determine a specific multi-test contrast pair relevant to finite composite-score stability checks.
 Exact checked proposition: forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->    batch_covariance w (four_batch_score x1 x2 x3 x4 1 1 1 0) (four_batch_score x1 x2 x3 x4 0 1 1 1) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 1 1 1 0) (four_batch_score x1 x2 x3 x4 0 1 1 1) xs    <= batch_variance w (four_batch_score x1 x2 x3 x4 1 1 1 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 0 1 1 1) xs
 Premises and side conditions: Every listed outcome occurrence has nonnegative weight and the full sample mass is strictly positive. Repeated observations are counted with multiplicity. The two explicit score vectors are not assumed independent, jointly Gaussian or standardized.
 Proof/definition method: Specialize the shared kernel-checked finite-sample covariance Cauchy-Schwarz theorem to both explicit four-test score functions; no reproof or expansion of the weighted sum is performed.
 Library reuse: ListPoolingAlgebra and FourContrastCovariance own the covariance and contrast definitions; SampleContrastCauchy owns the general inequality; Rocq Stdlib real numbers and lists supply all operations.
 Boundary: Exact finite empirical covariance constraint on the named composites, not a separate distributional sampling law, population parameter estimate, chi-square pivot, normal tail or interval-coverage theorem.
*)
Theorem sample_contrast_cs_triple123_triple234 :
 forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->
   batch_covariance w (four_batch_score x1 x2 x3 x4 1 1 1 0) (four_batch_score x1 x2 x3 x4 0 1 1 1) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 1 1 1 0) (four_batch_score x1 x2 x3 x4 0 1 1 1) xs
   <= batch_variance w (four_batch_score x1 x2 x3 x4 1 1 1 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 0 1 1 1) xs.
Proof.
 intros A w x1 x2 x3 x4 xs Hw Hm.
 exact (sample_covariance_cauchy_schwarz A w
   (four_batch_score x1 x2 x3 x4 1 1 1 0) (four_batch_score x1 x2 x3 x4 0 1 1 1) xs Hw Hm).
Qed.

(** [sample_contrast_cs_triple123_allfour] (theorem).
 Mathematical meaning: For the first three tests score contrast and the all four tests score contrast, a nonnegative-weight finite sample must satisfy the sharp squared covariance-versus-variance feasibility constraint. The coefficients determine a specific multi-test contrast pair relevant to finite composite-score stability checks.
 Exact checked proposition: forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->    batch_covariance w (four_batch_score x1 x2 x3 x4 1 1 1 0) (four_batch_score x1 x2 x3 x4 1 1 1 1) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 1 1 1 0) (four_batch_score x1 x2 x3 x4 1 1 1 1) xs    <= batch_variance w (four_batch_score x1 x2 x3 x4 1 1 1 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 1 1 1) xs
 Premises and side conditions: Every listed outcome occurrence has nonnegative weight and the full sample mass is strictly positive. Repeated observations are counted with multiplicity. The two explicit score vectors are not assumed independent, jointly Gaussian or standardized.
 Proof/definition method: Specialize the shared kernel-checked finite-sample covariance Cauchy-Schwarz theorem to both explicit four-test score functions; no reproof or expansion of the weighted sum is performed.
 Library reuse: ListPoolingAlgebra and FourContrastCovariance own the covariance and contrast definitions; SampleContrastCauchy owns the general inequality; Rocq Stdlib real numbers and lists supply all operations.
 Boundary: Exact finite empirical covariance constraint on the named composites, not a separate distributional sampling law, population parameter estimate, chi-square pivot, normal tail or interval-coverage theorem.
*)
Theorem sample_contrast_cs_triple123_allfour :
 forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->
   batch_covariance w (four_batch_score x1 x2 x3 x4 1 1 1 0) (four_batch_score x1 x2 x3 x4 1 1 1 1) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 1 1 1 0) (four_batch_score x1 x2 x3 x4 1 1 1 1) xs
   <= batch_variance w (four_batch_score x1 x2 x3 x4 1 1 1 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 1 1 1) xs.
Proof.
 intros A w x1 x2 x3 x4 xs Hw Hm.
 exact (sample_covariance_cauchy_schwarz A w
   (four_batch_score x1 x2 x3 x4 1 1 1 0) (four_batch_score x1 x2 x3 x4 1 1 1 1) xs Hw Hm).
Qed.

(** [sample_contrast_cs_triple123_balanced12v34] (theorem).
 Mathematical meaning: For the first three tests score contrast and the difference between the two pairs score contrast, a nonnegative-weight finite sample must satisfy the sharp squared covariance-versus-variance feasibility constraint. The coefficients determine a specific multi-test contrast pair relevant to finite composite-score stability checks.
 Exact checked proposition: forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->    batch_covariance w (four_batch_score x1 x2 x3 x4 1 1 1 0) (four_batch_score x1 x2 x3 x4 1 1 (-1) (-1)) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 1 1 1 0) (four_batch_score x1 x2 x3 x4 1 1 (-1) (-1)) xs    <= batch_variance w (four_batch_score x1 x2 x3 x4 1 1 1 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 1 (-1) (-1)) xs
 Premises and side conditions: Every listed outcome occurrence has nonnegative weight and the full sample mass is strictly positive. Repeated observations are counted with multiplicity. The two explicit score vectors are not assumed independent, jointly Gaussian or standardized.
 Proof/definition method: Specialize the shared kernel-checked finite-sample covariance Cauchy-Schwarz theorem to both explicit four-test score functions; no reproof or expansion of the weighted sum is performed.
 Library reuse: ListPoolingAlgebra and FourContrastCovariance own the covariance and contrast definitions; SampleContrastCauchy owns the general inequality; Rocq Stdlib real numbers and lists supply all operations.
 Boundary: Exact finite empirical covariance constraint on the named composites, not a separate distributional sampling law, population parameter estimate, chi-square pivot, normal tail or interval-coverage theorem.
*)
Theorem sample_contrast_cs_triple123_balanced12v34 :
 forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->
   batch_covariance w (four_batch_score x1 x2 x3 x4 1 1 1 0) (four_batch_score x1 x2 x3 x4 1 1 (-1) (-1)) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 1 1 1 0) (four_batch_score x1 x2 x3 x4 1 1 (-1) (-1)) xs
   <= batch_variance w (four_batch_score x1 x2 x3 x4 1 1 1 0) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 1 (-1) (-1)) xs.
Proof.
 intros A w x1 x2 x3 x4 xs Hw Hm.
 exact (sample_covariance_cauchy_schwarz A w
   (four_batch_score x1 x2 x3 x4 1 1 1 0) (four_batch_score x1 x2 x3 x4 1 1 (-1) (-1)) xs Hw Hm).
Qed.

(** [sample_contrast_cs_triple124_triple124] (theorem).
 Mathematical meaning: For the tests one, two and four score contrast and the tests one, two and four score contrast, a nonnegative-weight finite sample must satisfy the sharp squared covariance-versus-variance feasibility constraint. The coefficients determine a specific multi-test contrast pair relevant to finite composite-score stability checks.
 Exact checked proposition: forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->    batch_covariance w (four_batch_score x1 x2 x3 x4 1 1 0 1) (four_batch_score x1 x2 x3 x4 1 1 0 1) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 1 1 0 1) (four_batch_score x1 x2 x3 x4 1 1 0 1) xs    <= batch_variance w (four_batch_score x1 x2 x3 x4 1 1 0 1) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 1 0 1) xs
 Premises and side conditions: Every listed outcome occurrence has nonnegative weight and the full sample mass is strictly positive. Repeated observations are counted with multiplicity. The two explicit score vectors are not assumed independent, jointly Gaussian or standardized.
 Proof/definition method: Specialize the shared kernel-checked finite-sample covariance Cauchy-Schwarz theorem to both explicit four-test score functions; no reproof or expansion of the weighted sum is performed.
 Library reuse: ListPoolingAlgebra and FourContrastCovariance own the covariance and contrast definitions; SampleContrastCauchy owns the general inequality; Rocq Stdlib real numbers and lists supply all operations.
 Boundary: Exact finite empirical covariance constraint on the named composites, not a separate distributional sampling law, population parameter estimate, chi-square pivot, normal tail or interval-coverage theorem.
*)
Theorem sample_contrast_cs_triple124_triple124 :
 forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->
   batch_covariance w (four_batch_score x1 x2 x3 x4 1 1 0 1) (four_batch_score x1 x2 x3 x4 1 1 0 1) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 1 1 0 1) (four_batch_score x1 x2 x3 x4 1 1 0 1) xs
   <= batch_variance w (four_batch_score x1 x2 x3 x4 1 1 0 1) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 1 0 1) xs.
Proof.
 intros A w x1 x2 x3 x4 xs Hw Hm.
 exact (sample_covariance_cauchy_schwarz A w
   (four_batch_score x1 x2 x3 x4 1 1 0 1) (four_batch_score x1 x2 x3 x4 1 1 0 1) xs Hw Hm).
Qed.

(** [sample_contrast_cs_triple124_triple134] (theorem).
 Mathematical meaning: For the tests one, two and four score contrast and the tests one, three and four score contrast, a nonnegative-weight finite sample must satisfy the sharp squared covariance-versus-variance feasibility constraint. The coefficients determine a specific multi-test contrast pair relevant to finite composite-score stability checks.
 Exact checked proposition: forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->    batch_covariance w (four_batch_score x1 x2 x3 x4 1 1 0 1) (four_batch_score x1 x2 x3 x4 1 0 1 1) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 1 1 0 1) (four_batch_score x1 x2 x3 x4 1 0 1 1) xs    <= batch_variance w (four_batch_score x1 x2 x3 x4 1 1 0 1) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 0 1 1) xs
 Premises and side conditions: Every listed outcome occurrence has nonnegative weight and the full sample mass is strictly positive. Repeated observations are counted with multiplicity. The two explicit score vectors are not assumed independent, jointly Gaussian or standardized.
 Proof/definition method: Specialize the shared kernel-checked finite-sample covariance Cauchy-Schwarz theorem to both explicit four-test score functions; no reproof or expansion of the weighted sum is performed.
 Library reuse: ListPoolingAlgebra and FourContrastCovariance own the covariance and contrast definitions; SampleContrastCauchy owns the general inequality; Rocq Stdlib real numbers and lists supply all operations.
 Boundary: Exact finite empirical covariance constraint on the named composites, not a separate distributional sampling law, population parameter estimate, chi-square pivot, normal tail or interval-coverage theorem.
*)
Theorem sample_contrast_cs_triple124_triple134 :
 forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->
   batch_covariance w (four_batch_score x1 x2 x3 x4 1 1 0 1) (four_batch_score x1 x2 x3 x4 1 0 1 1) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 1 1 0 1) (four_batch_score x1 x2 x3 x4 1 0 1 1) xs
   <= batch_variance w (four_batch_score x1 x2 x3 x4 1 1 0 1) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 0 1 1) xs.
Proof.
 intros A w x1 x2 x3 x4 xs Hw Hm.
 exact (sample_covariance_cauchy_schwarz A w
   (four_batch_score x1 x2 x3 x4 1 1 0 1) (four_batch_score x1 x2 x3 x4 1 0 1 1) xs Hw Hm).
Qed.

(** [sample_contrast_cs_triple124_triple234] (theorem).
 Mathematical meaning: For the tests one, two and four score contrast and the last three tests score contrast, a nonnegative-weight finite sample must satisfy the sharp squared covariance-versus-variance feasibility constraint. The coefficients determine a specific multi-test contrast pair relevant to finite composite-score stability checks.
 Exact checked proposition: forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->    batch_covariance w (four_batch_score x1 x2 x3 x4 1 1 0 1) (four_batch_score x1 x2 x3 x4 0 1 1 1) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 1 1 0 1) (four_batch_score x1 x2 x3 x4 0 1 1 1) xs    <= batch_variance w (four_batch_score x1 x2 x3 x4 1 1 0 1) xs * batch_variance w (four_batch_score x1 x2 x3 x4 0 1 1 1) xs
 Premises and side conditions: Every listed outcome occurrence has nonnegative weight and the full sample mass is strictly positive. Repeated observations are counted with multiplicity. The two explicit score vectors are not assumed independent, jointly Gaussian or standardized.
 Proof/definition method: Specialize the shared kernel-checked finite-sample covariance Cauchy-Schwarz theorem to both explicit four-test score functions; no reproof or expansion of the weighted sum is performed.
 Library reuse: ListPoolingAlgebra and FourContrastCovariance own the covariance and contrast definitions; SampleContrastCauchy owns the general inequality; Rocq Stdlib real numbers and lists supply all operations.
 Boundary: Exact finite empirical covariance constraint on the named composites, not a separate distributional sampling law, population parameter estimate, chi-square pivot, normal tail or interval-coverage theorem.
*)
Theorem sample_contrast_cs_triple124_triple234 :
 forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->
   batch_covariance w (four_batch_score x1 x2 x3 x4 1 1 0 1) (four_batch_score x1 x2 x3 x4 0 1 1 1) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 1 1 0 1) (four_batch_score x1 x2 x3 x4 0 1 1 1) xs
   <= batch_variance w (four_batch_score x1 x2 x3 x4 1 1 0 1) xs * batch_variance w (four_batch_score x1 x2 x3 x4 0 1 1 1) xs.
Proof.
 intros A w x1 x2 x3 x4 xs Hw Hm.
 exact (sample_covariance_cauchy_schwarz A w
   (four_batch_score x1 x2 x3 x4 1 1 0 1) (four_batch_score x1 x2 x3 x4 0 1 1 1) xs Hw Hm).
Qed.

(** [sample_contrast_cs_triple124_allfour] (theorem).
 Mathematical meaning: For the tests one, two and four score contrast and the all four tests score contrast, a nonnegative-weight finite sample must satisfy the sharp squared covariance-versus-variance feasibility constraint. The coefficients determine a specific multi-test contrast pair relevant to finite composite-score stability checks.
 Exact checked proposition: forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->    batch_covariance w (four_batch_score x1 x2 x3 x4 1 1 0 1) (four_batch_score x1 x2 x3 x4 1 1 1 1) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 1 1 0 1) (four_batch_score x1 x2 x3 x4 1 1 1 1) xs    <= batch_variance w (four_batch_score x1 x2 x3 x4 1 1 0 1) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 1 1 1) xs
 Premises and side conditions: Every listed outcome occurrence has nonnegative weight and the full sample mass is strictly positive. Repeated observations are counted with multiplicity. The two explicit score vectors are not assumed independent, jointly Gaussian or standardized.
 Proof/definition method: Specialize the shared kernel-checked finite-sample covariance Cauchy-Schwarz theorem to both explicit four-test score functions; no reproof or expansion of the weighted sum is performed.
 Library reuse: ListPoolingAlgebra and FourContrastCovariance own the covariance and contrast definitions; SampleContrastCauchy owns the general inequality; Rocq Stdlib real numbers and lists supply all operations.
 Boundary: Exact finite empirical covariance constraint on the named composites, not a separate distributional sampling law, population parameter estimate, chi-square pivot, normal tail or interval-coverage theorem.
*)
Theorem sample_contrast_cs_triple124_allfour :
 forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->
   batch_covariance w (four_batch_score x1 x2 x3 x4 1 1 0 1) (four_batch_score x1 x2 x3 x4 1 1 1 1) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 1 1 0 1) (four_batch_score x1 x2 x3 x4 1 1 1 1) xs
   <= batch_variance w (four_batch_score x1 x2 x3 x4 1 1 0 1) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 1 1 1) xs.
Proof.
 intros A w x1 x2 x3 x4 xs Hw Hm.
 exact (sample_covariance_cauchy_schwarz A w
   (four_batch_score x1 x2 x3 x4 1 1 0 1) (four_batch_score x1 x2 x3 x4 1 1 1 1) xs Hw Hm).
Qed.

(** [sample_contrast_cs_triple124_balanced12v34] (theorem).
 Mathematical meaning: For the tests one, two and four score contrast and the difference between the two pairs score contrast, a nonnegative-weight finite sample must satisfy the sharp squared covariance-versus-variance feasibility constraint. The coefficients determine a specific multi-test contrast pair relevant to finite composite-score stability checks.
 Exact checked proposition: forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->    batch_covariance w (four_batch_score x1 x2 x3 x4 1 1 0 1) (four_batch_score x1 x2 x3 x4 1 1 (-1) (-1)) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 1 1 0 1) (four_batch_score x1 x2 x3 x4 1 1 (-1) (-1)) xs    <= batch_variance w (four_batch_score x1 x2 x3 x4 1 1 0 1) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 1 (-1) (-1)) xs
 Premises and side conditions: Every listed outcome occurrence has nonnegative weight and the full sample mass is strictly positive. Repeated observations are counted with multiplicity. The two explicit score vectors are not assumed independent, jointly Gaussian or standardized.
 Proof/definition method: Specialize the shared kernel-checked finite-sample covariance Cauchy-Schwarz theorem to both explicit four-test score functions; no reproof or expansion of the weighted sum is performed.
 Library reuse: ListPoolingAlgebra and FourContrastCovariance own the covariance and contrast definitions; SampleContrastCauchy owns the general inequality; Rocq Stdlib real numbers and lists supply all operations.
 Boundary: Exact finite empirical covariance constraint on the named composites, not a separate distributional sampling law, population parameter estimate, chi-square pivot, normal tail or interval-coverage theorem.
*)
Theorem sample_contrast_cs_triple124_balanced12v34 :
 forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->
   batch_covariance w (four_batch_score x1 x2 x3 x4 1 1 0 1) (four_batch_score x1 x2 x3 x4 1 1 (-1) (-1)) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 1 1 0 1) (four_batch_score x1 x2 x3 x4 1 1 (-1) (-1)) xs
   <= batch_variance w (four_batch_score x1 x2 x3 x4 1 1 0 1) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 1 (-1) (-1)) xs.
Proof.
 intros A w x1 x2 x3 x4 xs Hw Hm.
 exact (sample_covariance_cauchy_schwarz A w
   (four_batch_score x1 x2 x3 x4 1 1 0 1) (four_batch_score x1 x2 x3 x4 1 1 (-1) (-1)) xs Hw Hm).
Qed.

(** [sample_contrast_cs_triple134_triple134] (theorem).
 Mathematical meaning: For the tests one, three and four score contrast and the tests one, three and four score contrast, a nonnegative-weight finite sample must satisfy the sharp squared covariance-versus-variance feasibility constraint. The coefficients determine a specific multi-test contrast pair relevant to finite composite-score stability checks.
 Exact checked proposition: forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->    batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 1 1) (four_batch_score x1 x2 x3 x4 1 0 1 1) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 1 1) (four_batch_score x1 x2 x3 x4 1 0 1 1) xs    <= batch_variance w (four_batch_score x1 x2 x3 x4 1 0 1 1) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 0 1 1) xs
 Premises and side conditions: Every listed outcome occurrence has nonnegative weight and the full sample mass is strictly positive. Repeated observations are counted with multiplicity. The two explicit score vectors are not assumed independent, jointly Gaussian or standardized.
 Proof/definition method: Specialize the shared kernel-checked finite-sample covariance Cauchy-Schwarz theorem to both explicit four-test score functions; no reproof or expansion of the weighted sum is performed.
 Library reuse: ListPoolingAlgebra and FourContrastCovariance own the covariance and contrast definitions; SampleContrastCauchy owns the general inequality; Rocq Stdlib real numbers and lists supply all operations.
 Boundary: Exact finite empirical covariance constraint on the named composites, not a separate distributional sampling law, population parameter estimate, chi-square pivot, normal tail or interval-coverage theorem.
*)
Theorem sample_contrast_cs_triple134_triple134 :
 forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->
   batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 1 1) (four_batch_score x1 x2 x3 x4 1 0 1 1) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 1 1) (four_batch_score x1 x2 x3 x4 1 0 1 1) xs
   <= batch_variance w (four_batch_score x1 x2 x3 x4 1 0 1 1) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 0 1 1) xs.
Proof.
 intros A w x1 x2 x3 x4 xs Hw Hm.
 exact (sample_covariance_cauchy_schwarz A w
   (four_batch_score x1 x2 x3 x4 1 0 1 1) (four_batch_score x1 x2 x3 x4 1 0 1 1) xs Hw Hm).
Qed.

(** [sample_contrast_cs_triple134_triple234] (theorem).
 Mathematical meaning: For the tests one, three and four score contrast and the last three tests score contrast, a nonnegative-weight finite sample must satisfy the sharp squared covariance-versus-variance feasibility constraint. The coefficients determine a specific multi-test contrast pair relevant to finite composite-score stability checks.
 Exact checked proposition: forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->    batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 1 1) (four_batch_score x1 x2 x3 x4 0 1 1 1) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 1 1) (four_batch_score x1 x2 x3 x4 0 1 1 1) xs    <= batch_variance w (four_batch_score x1 x2 x3 x4 1 0 1 1) xs * batch_variance w (four_batch_score x1 x2 x3 x4 0 1 1 1) xs
 Premises and side conditions: Every listed outcome occurrence has nonnegative weight and the full sample mass is strictly positive. Repeated observations are counted with multiplicity. The two explicit score vectors are not assumed independent, jointly Gaussian or standardized.
 Proof/definition method: Specialize the shared kernel-checked finite-sample covariance Cauchy-Schwarz theorem to both explicit four-test score functions; no reproof or expansion of the weighted sum is performed.
 Library reuse: ListPoolingAlgebra and FourContrastCovariance own the covariance and contrast definitions; SampleContrastCauchy owns the general inequality; Rocq Stdlib real numbers and lists supply all operations.
 Boundary: Exact finite empirical covariance constraint on the named composites, not a separate distributional sampling law, population parameter estimate, chi-square pivot, normal tail or interval-coverage theorem.
*)
Theorem sample_contrast_cs_triple134_triple234 :
 forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->
   batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 1 1) (four_batch_score x1 x2 x3 x4 0 1 1 1) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 1 1) (four_batch_score x1 x2 x3 x4 0 1 1 1) xs
   <= batch_variance w (four_batch_score x1 x2 x3 x4 1 0 1 1) xs * batch_variance w (four_batch_score x1 x2 x3 x4 0 1 1 1) xs.
Proof.
 intros A w x1 x2 x3 x4 xs Hw Hm.
 exact (sample_covariance_cauchy_schwarz A w
   (four_batch_score x1 x2 x3 x4 1 0 1 1) (four_batch_score x1 x2 x3 x4 0 1 1 1) xs Hw Hm).
Qed.

(** [sample_contrast_cs_triple134_allfour] (theorem).
 Mathematical meaning: For the tests one, three and four score contrast and the all four tests score contrast, a nonnegative-weight finite sample must satisfy the sharp squared covariance-versus-variance feasibility constraint. The coefficients determine a specific multi-test contrast pair relevant to finite composite-score stability checks.
 Exact checked proposition: forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->    batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 1 1) (four_batch_score x1 x2 x3 x4 1 1 1 1) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 1 1) (four_batch_score x1 x2 x3 x4 1 1 1 1) xs    <= batch_variance w (four_batch_score x1 x2 x3 x4 1 0 1 1) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 1 1 1) xs
 Premises and side conditions: Every listed outcome occurrence has nonnegative weight and the full sample mass is strictly positive. Repeated observations are counted with multiplicity. The two explicit score vectors are not assumed independent, jointly Gaussian or standardized.
 Proof/definition method: Specialize the shared kernel-checked finite-sample covariance Cauchy-Schwarz theorem to both explicit four-test score functions; no reproof or expansion of the weighted sum is performed.
 Library reuse: ListPoolingAlgebra and FourContrastCovariance own the covariance and contrast definitions; SampleContrastCauchy owns the general inequality; Rocq Stdlib real numbers and lists supply all operations.
 Boundary: Exact finite empirical covariance constraint on the named composites, not a separate distributional sampling law, population parameter estimate, chi-square pivot, normal tail or interval-coverage theorem.
*)
Theorem sample_contrast_cs_triple134_allfour :
 forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->
   batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 1 1) (four_batch_score x1 x2 x3 x4 1 1 1 1) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 1 1) (four_batch_score x1 x2 x3 x4 1 1 1 1) xs
   <= batch_variance w (four_batch_score x1 x2 x3 x4 1 0 1 1) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 1 1 1) xs.
Proof.
 intros A w x1 x2 x3 x4 xs Hw Hm.
 exact (sample_covariance_cauchy_schwarz A w
   (four_batch_score x1 x2 x3 x4 1 0 1 1) (four_batch_score x1 x2 x3 x4 1 1 1 1) xs Hw Hm).
Qed.

(** [sample_contrast_cs_triple134_balanced12v34] (theorem).
 Mathematical meaning: For the tests one, three and four score contrast and the difference between the two pairs score contrast, a nonnegative-weight finite sample must satisfy the sharp squared covariance-versus-variance feasibility constraint. The coefficients determine a specific multi-test contrast pair relevant to finite composite-score stability checks.
 Exact checked proposition: forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->    batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 1 1) (four_batch_score x1 x2 x3 x4 1 1 (-1) (-1)) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 1 1) (four_batch_score x1 x2 x3 x4 1 1 (-1) (-1)) xs    <= batch_variance w (four_batch_score x1 x2 x3 x4 1 0 1 1) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 1 (-1) (-1)) xs
 Premises and side conditions: Every listed outcome occurrence has nonnegative weight and the full sample mass is strictly positive. Repeated observations are counted with multiplicity. The two explicit score vectors are not assumed independent, jointly Gaussian or standardized.
 Proof/definition method: Specialize the shared kernel-checked finite-sample covariance Cauchy-Schwarz theorem to both explicit four-test score functions; no reproof or expansion of the weighted sum is performed.
 Library reuse: ListPoolingAlgebra and FourContrastCovariance own the covariance and contrast definitions; SampleContrastCauchy owns the general inequality; Rocq Stdlib real numbers and lists supply all operations.
 Boundary: Exact finite empirical covariance constraint on the named composites, not a separate distributional sampling law, population parameter estimate, chi-square pivot, normal tail or interval-coverage theorem.
*)
Theorem sample_contrast_cs_triple134_balanced12v34 :
 forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->
   batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 1 1) (four_batch_score x1 x2 x3 x4 1 1 (-1) (-1)) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 1 0 1 1) (four_batch_score x1 x2 x3 x4 1 1 (-1) (-1)) xs
   <= batch_variance w (four_batch_score x1 x2 x3 x4 1 0 1 1) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 1 (-1) (-1)) xs.
Proof.
 intros A w x1 x2 x3 x4 xs Hw Hm.
 exact (sample_covariance_cauchy_schwarz A w
   (four_batch_score x1 x2 x3 x4 1 0 1 1) (four_batch_score x1 x2 x3 x4 1 1 (-1) (-1)) xs Hw Hm).
Qed.

(** [sample_contrast_cs_triple234_triple234] (theorem).
 Mathematical meaning: For the last three tests score contrast and the last three tests score contrast, a nonnegative-weight finite sample must satisfy the sharp squared covariance-versus-variance feasibility constraint. The coefficients determine a specific multi-test contrast pair relevant to finite composite-score stability checks.
 Exact checked proposition: forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->    batch_covariance w (four_batch_score x1 x2 x3 x4 0 1 1 1) (four_batch_score x1 x2 x3 x4 0 1 1 1) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 0 1 1 1) (four_batch_score x1 x2 x3 x4 0 1 1 1) xs    <= batch_variance w (four_batch_score x1 x2 x3 x4 0 1 1 1) xs * batch_variance w (four_batch_score x1 x2 x3 x4 0 1 1 1) xs
 Premises and side conditions: Every listed outcome occurrence has nonnegative weight and the full sample mass is strictly positive. Repeated observations are counted with multiplicity. The two explicit score vectors are not assumed independent, jointly Gaussian or standardized.
 Proof/definition method: Specialize the shared kernel-checked finite-sample covariance Cauchy-Schwarz theorem to both explicit four-test score functions; no reproof or expansion of the weighted sum is performed.
 Library reuse: ListPoolingAlgebra and FourContrastCovariance own the covariance and contrast definitions; SampleContrastCauchy owns the general inequality; Rocq Stdlib real numbers and lists supply all operations.
 Boundary: Exact finite empirical covariance constraint on the named composites, not a separate distributional sampling law, population parameter estimate, chi-square pivot, normal tail or interval-coverage theorem.
*)
Theorem sample_contrast_cs_triple234_triple234 :
 forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->
   batch_covariance w (four_batch_score x1 x2 x3 x4 0 1 1 1) (four_batch_score x1 x2 x3 x4 0 1 1 1) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 0 1 1 1) (four_batch_score x1 x2 x3 x4 0 1 1 1) xs
   <= batch_variance w (four_batch_score x1 x2 x3 x4 0 1 1 1) xs * batch_variance w (four_batch_score x1 x2 x3 x4 0 1 1 1) xs.
Proof.
 intros A w x1 x2 x3 x4 xs Hw Hm.
 exact (sample_covariance_cauchy_schwarz A w
   (four_batch_score x1 x2 x3 x4 0 1 1 1) (four_batch_score x1 x2 x3 x4 0 1 1 1) xs Hw Hm).
Qed.

(** [sample_contrast_cs_triple234_allfour] (theorem).
 Mathematical meaning: For the last three tests score contrast and the all four tests score contrast, a nonnegative-weight finite sample must satisfy the sharp squared covariance-versus-variance feasibility constraint. The coefficients determine a specific multi-test contrast pair relevant to finite composite-score stability checks.
 Exact checked proposition: forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->    batch_covariance w (four_batch_score x1 x2 x3 x4 0 1 1 1) (four_batch_score x1 x2 x3 x4 1 1 1 1) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 0 1 1 1) (four_batch_score x1 x2 x3 x4 1 1 1 1) xs    <= batch_variance w (four_batch_score x1 x2 x3 x4 0 1 1 1) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 1 1 1) xs
 Premises and side conditions: Every listed outcome occurrence has nonnegative weight and the full sample mass is strictly positive. Repeated observations are counted with multiplicity. The two explicit score vectors are not assumed independent, jointly Gaussian or standardized.
 Proof/definition method: Specialize the shared kernel-checked finite-sample covariance Cauchy-Schwarz theorem to both explicit four-test score functions; no reproof or expansion of the weighted sum is performed.
 Library reuse: ListPoolingAlgebra and FourContrastCovariance own the covariance and contrast definitions; SampleContrastCauchy owns the general inequality; Rocq Stdlib real numbers and lists supply all operations.
 Boundary: Exact finite empirical covariance constraint on the named composites, not a separate distributional sampling law, population parameter estimate, chi-square pivot, normal tail or interval-coverage theorem.
*)
Theorem sample_contrast_cs_triple234_allfour :
 forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->
   batch_covariance w (four_batch_score x1 x2 x3 x4 0 1 1 1) (four_batch_score x1 x2 x3 x4 1 1 1 1) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 0 1 1 1) (four_batch_score x1 x2 x3 x4 1 1 1 1) xs
   <= batch_variance w (four_batch_score x1 x2 x3 x4 0 1 1 1) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 1 1 1) xs.
Proof.
 intros A w x1 x2 x3 x4 xs Hw Hm.
 exact (sample_covariance_cauchy_schwarz A w
   (four_batch_score x1 x2 x3 x4 0 1 1 1) (four_batch_score x1 x2 x3 x4 1 1 1 1) xs Hw Hm).
Qed.

(** [sample_contrast_cs_triple234_balanced12v34] (theorem).
 Mathematical meaning: For the last three tests score contrast and the difference between the two pairs score contrast, a nonnegative-weight finite sample must satisfy the sharp squared covariance-versus-variance feasibility constraint. The coefficients determine a specific multi-test contrast pair relevant to finite composite-score stability checks.
 Exact checked proposition: forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->    batch_covariance w (four_batch_score x1 x2 x3 x4 0 1 1 1) (four_batch_score x1 x2 x3 x4 1 1 (-1) (-1)) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 0 1 1 1) (four_batch_score x1 x2 x3 x4 1 1 (-1) (-1)) xs    <= batch_variance w (four_batch_score x1 x2 x3 x4 0 1 1 1) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 1 (-1) (-1)) xs
 Premises and side conditions: Every listed outcome occurrence has nonnegative weight and the full sample mass is strictly positive. Repeated observations are counted with multiplicity. The two explicit score vectors are not assumed independent, jointly Gaussian or standardized.
 Proof/definition method: Specialize the shared kernel-checked finite-sample covariance Cauchy-Schwarz theorem to both explicit four-test score functions; no reproof or expansion of the weighted sum is performed.
 Library reuse: ListPoolingAlgebra and FourContrastCovariance own the covariance and contrast definitions; SampleContrastCauchy owns the general inequality; Rocq Stdlib real numbers and lists supply all operations.
 Boundary: Exact finite empirical covariance constraint on the named composites, not a separate distributional sampling law, population parameter estimate, chi-square pivot, normal tail or interval-coverage theorem.
*)
Theorem sample_contrast_cs_triple234_balanced12v34 :
 forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->
   batch_covariance w (four_batch_score x1 x2 x3 x4 0 1 1 1) (four_batch_score x1 x2 x3 x4 1 1 (-1) (-1)) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 0 1 1 1) (four_batch_score x1 x2 x3 x4 1 1 (-1) (-1)) xs
   <= batch_variance w (four_batch_score x1 x2 x3 x4 0 1 1 1) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 1 (-1) (-1)) xs.
Proof.
 intros A w x1 x2 x3 x4 xs Hw Hm.
 exact (sample_covariance_cauchy_schwarz A w
   (four_batch_score x1 x2 x3 x4 0 1 1 1) (four_batch_score x1 x2 x3 x4 1 1 (-1) (-1)) xs Hw Hm).
Qed.

(** [sample_contrast_cs_allfour_allfour] (theorem).
 Mathematical meaning: For the all four tests score contrast and the all four tests score contrast, a nonnegative-weight finite sample must satisfy the sharp squared covariance-versus-variance feasibility constraint. The coefficients determine a specific multi-test contrast pair relevant to finite composite-score stability checks.
 Exact checked proposition: forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->    batch_covariance w (four_batch_score x1 x2 x3 x4 1 1 1 1) (four_batch_score x1 x2 x3 x4 1 1 1 1) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 1 1 1 1) (four_batch_score x1 x2 x3 x4 1 1 1 1) xs    <= batch_variance w (four_batch_score x1 x2 x3 x4 1 1 1 1) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 1 1 1) xs
 Premises and side conditions: Every listed outcome occurrence has nonnegative weight and the full sample mass is strictly positive. Repeated observations are counted with multiplicity. The two explicit score vectors are not assumed independent, jointly Gaussian or standardized.
 Proof/definition method: Specialize the shared kernel-checked finite-sample covariance Cauchy-Schwarz theorem to both explicit four-test score functions; no reproof or expansion of the weighted sum is performed.
 Library reuse: ListPoolingAlgebra and FourContrastCovariance own the covariance and contrast definitions; SampleContrastCauchy owns the general inequality; Rocq Stdlib real numbers and lists supply all operations.
 Boundary: Exact finite empirical covariance constraint on the named composites, not a separate distributional sampling law, population parameter estimate, chi-square pivot, normal tail or interval-coverage theorem.
*)
Theorem sample_contrast_cs_allfour_allfour :
 forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->
   batch_covariance w (four_batch_score x1 x2 x3 x4 1 1 1 1) (four_batch_score x1 x2 x3 x4 1 1 1 1) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 1 1 1 1) (four_batch_score x1 x2 x3 x4 1 1 1 1) xs
   <= batch_variance w (four_batch_score x1 x2 x3 x4 1 1 1 1) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 1 1 1) xs.
Proof.
 intros A w x1 x2 x3 x4 xs Hw Hm.
 exact (sample_covariance_cauchy_schwarz A w
   (four_batch_score x1 x2 x3 x4 1 1 1 1) (four_batch_score x1 x2 x3 x4 1 1 1 1) xs Hw Hm).
Qed.

(** [sample_contrast_cs_allfour_balanced12v34] (theorem).
 Mathematical meaning: For the all four tests score contrast and the difference between the two pairs score contrast, a nonnegative-weight finite sample must satisfy the sharp squared covariance-versus-variance feasibility constraint. The coefficients determine a specific multi-test contrast pair relevant to finite composite-score stability checks.
 Exact checked proposition: forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->    batch_covariance w (four_batch_score x1 x2 x3 x4 1 1 1 1) (four_batch_score x1 x2 x3 x4 1 1 (-1) (-1)) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 1 1 1 1) (four_batch_score x1 x2 x3 x4 1 1 (-1) (-1)) xs    <= batch_variance w (four_batch_score x1 x2 x3 x4 1 1 1 1) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 1 (-1) (-1)) xs
 Premises and side conditions: Every listed outcome occurrence has nonnegative weight and the full sample mass is strictly positive. Repeated observations are counted with multiplicity. The two explicit score vectors are not assumed independent, jointly Gaussian or standardized.
 Proof/definition method: Specialize the shared kernel-checked finite-sample covariance Cauchy-Schwarz theorem to both explicit four-test score functions; no reproof or expansion of the weighted sum is performed.
 Library reuse: ListPoolingAlgebra and FourContrastCovariance own the covariance and contrast definitions; SampleContrastCauchy owns the general inequality; Rocq Stdlib real numbers and lists supply all operations.
 Boundary: Exact finite empirical covariance constraint on the named composites, not a separate distributional sampling law, population parameter estimate, chi-square pivot, normal tail or interval-coverage theorem.
*)
Theorem sample_contrast_cs_allfour_balanced12v34 :
 forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->
   batch_covariance w (four_batch_score x1 x2 x3 x4 1 1 1 1) (four_batch_score x1 x2 x3 x4 1 1 (-1) (-1)) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 1 1 1 1) (four_batch_score x1 x2 x3 x4 1 1 (-1) (-1)) xs
   <= batch_variance w (four_batch_score x1 x2 x3 x4 1 1 1 1) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 1 (-1) (-1)) xs.
Proof.
 intros A w x1 x2 x3 x4 xs Hw Hm.
 exact (sample_covariance_cauchy_schwarz A w
   (four_batch_score x1 x2 x3 x4 1 1 1 1) (four_batch_score x1 x2 x3 x4 1 1 (-1) (-1)) xs Hw Hm).
Qed.

(** [sample_contrast_cs_balanced12v34_balanced12v34] (theorem).
 Mathematical meaning: For the difference between the two pairs score contrast and the difference between the two pairs score contrast, a nonnegative-weight finite sample must satisfy the sharp squared covariance-versus-variance feasibility constraint. The coefficients determine a specific multi-test contrast pair relevant to finite composite-score stability checks.
 Exact checked proposition: forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->    batch_covariance w (four_batch_score x1 x2 x3 x4 1 1 (-1) (-1)) (four_batch_score x1 x2 x3 x4 1 1 (-1) (-1)) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 1 1 (-1) (-1)) (four_batch_score x1 x2 x3 x4 1 1 (-1) (-1)) xs    <= batch_variance w (four_batch_score x1 x2 x3 x4 1 1 (-1) (-1)) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 1 (-1) (-1)) xs
 Premises and side conditions: Every listed outcome occurrence has nonnegative weight and the full sample mass is strictly positive. Repeated observations are counted with multiplicity. The two explicit score vectors are not assumed independent, jointly Gaussian or standardized.
 Proof/definition method: Specialize the shared kernel-checked finite-sample covariance Cauchy-Schwarz theorem to both explicit four-test score functions; no reproof or expansion of the weighted sum is performed.
 Library reuse: ListPoolingAlgebra and FourContrastCovariance own the covariance and contrast definitions; SampleContrastCauchy owns the general inequality; Rocq Stdlib real numbers and lists supply all operations.
 Boundary: Exact finite empirical covariance constraint on the named composites, not a separate distributional sampling law, population parameter estimate, chi-square pivot, normal tail or interval-coverage theorem.
*)
Theorem sample_contrast_cs_balanced12v34_balanced12v34 :
 forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A), (forall t, In t xs -> 0<=w t) -> 0<batch_mass w xs ->
   batch_covariance w (four_batch_score x1 x2 x3 x4 1 1 (-1) (-1)) (four_batch_score x1 x2 x3 x4 1 1 (-1) (-1)) xs * batch_covariance w (four_batch_score x1 x2 x3 x4 1 1 (-1) (-1)) (four_batch_score x1 x2 x3 x4 1 1 (-1) (-1)) xs
   <= batch_variance w (four_batch_score x1 x2 x3 x4 1 1 (-1) (-1)) xs * batch_variance w (four_batch_score x1 x2 x3 x4 1 1 (-1) (-1)) xs.
Proof.
 intros A w x1 x2 x3 x4 xs Hw Hm.
 exact (sample_covariance_cauchy_schwarz A w
   (four_batch_score x1 x2 x3 x4 1 1 (-1) (-1)) (four_batch_score x1 x2 x3 x4 1 1 (-1) (-1)) xs Hw Hm).
Qed.

