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

