(** Module: GaussianFiniteHistoryPosterior.v
 Purpose: Formalize n-observation Gaussian posterior sufficient statistics,
 exact information gains and arbitrary nonempty appended histories.
 Mathematical representation: GaussianConditionalKernel defines a real
 latent signal with common-factor variance c, observed score history
 xs:list R, posterior center, posterior variance, precision and density
 kernel. Finite-history concatenation represents another observation
 batch, including arbitrarily unequal observed scores. Every update
 uses the canonical gk_* definitions without new probability axioms.
 Explicit hypotheses: 0<c<1 supplies positive Gaussian signal and
 residual variance; all nonzero denominator and nonempty-history
 conditions are stated in the precise propositions that need them.
 Library use: Reuse FiniteSum.finite_sum_app, vector_real_sum_append,
 Stdlib.List.length_app, plus_INR, GaussianConditionalKernel and
 previously proved Gaussian innovation and covariance lemmas.
 Limitations: Results establish exact Gaussian density algebra,
 sufficient-statistic identity and variance/precision ordering only;
 the normalization integral, Gaussian joint law existence and actual
 conditional expectation are separate unproved bridge obligations.
 Reproduction: Rocq 9.2 with scripts/compile_rocq.sh, CI kernel-check;
 source-order review in rocq/PROOF_REFACTOR_GAUSSIAN.md.
 AI disclosure: Researcher/requester Anders Hellström; theorem
 statements, source documentation and proof scripts were AI assisted.
*)
From Stdlib Require Import Reals Lra Psatz Ring Field List.
Require Import FiniteSum EquicorrelationVectors
  SequentialReport GaussianConditionalKernel GaussianInnovationBounds
  GaussianCovarianceDomain.
Import ListNotations.
Open Scope R_scope.

(** [gsp_mass_append] (theorem).
 Mathematical meaning: Observed history counts embedded in the reals add exactly under finite-history concatenation.
 Exact checked proposition: forall xs ys:list R, gk_mass (xs++ys)=gk_mass xs+gk_mass ys.
 Premises and side conditions: The model uses an arbitrary finite
 observed-score list; positivity and nonempty-block conditions are
 stated explicitly for the normal common-factor model 0<c<1.
 No independent measure-theoretic normality or conditional expectation
 premise is smuggled into an algebraic theorem.
 Proof/definition method: Reuse the canonical list sum and length
 lemmas, original Gaussian posterior center/precision/variance,
 original Schur covariance reduction and Stdlib ring/field/order
 tactics. Sign and equality cases derive from one shared variance
 and posterior-innovation identity rather than duplicated formulas.
 Library reuse: FiniteSum, EquicorrelationVectors,
 GaussianConditionalKernel, GaussianInnovationBounds and Stdlib.
 Boundary: Exact pointwise Gaussian regression/kernels and
 information-order properties; no proof of normalized probability
 measures, independence or conditional expectation is claimed.
*)
Theorem gsp_mass_append : forall xs ys:list R, gk_mass (xs++ys)=gk_mass xs+gk_mass ys.
Proof.
 intros xs ys.
 unfold gk_mass.
 rewrite length_app, plus_INR.
 reflexivity.
Qed.

(** [gsp_sum_append] (theorem).
 Mathematical meaning: The sufficient-history score-sum statistic is additive under concatenation.
 Exact checked proposition: forall xs ys:list R, gk_sum (xs++ys)=gk_sum xs+gk_sum ys.
 Premises and side conditions: The model uses an arbitrary finite
 observed-score list; positivity and nonempty-block conditions are
 stated explicitly for the normal common-factor model 0<c<1.
 No independent measure-theoretic normality or conditional expectation
 premise is smuggled into an algebraic theorem.
 Proof/definition method: Reuse the canonical list sum and length
 lemmas, original Gaussian posterior center/precision/variance,
 original Schur covariance reduction and Stdlib ring/field/order
 tactics. Sign and equality cases derive from one shared variance
 and posterior-innovation identity rather than duplicated formulas.
 Library reuse: FiniteSum, EquicorrelationVectors,
 GaussianConditionalKernel, GaussianInnovationBounds and Stdlib.
 Boundary: Exact pointwise Gaussian regression/kernels and
 information-order properties; no proof of normalized probability
 measures, independence or conditional expectation is claimed.
*)
Theorem gsp_sum_append : forall xs ys:list R, gk_sum (xs++ys)=gk_sum xs+gk_sum ys.
Proof.
 intros xs ys; unfold gk_sum; apply vector_real_sum_append.
Qed.

(** [gsp_residual_energy_append] (theorem).
 Mathematical meaning: The Gaussian likelihood residual quadratic energy decomposes exactly across independent observed data blocks.
 Exact checked proposition: forall xs ys:list R, forall theta:R, gk_residual_energy (xs++ys) theta=gk_residual_energy xs theta+gk_residual_energy ys theta.
 Premises and side conditions: The model uses an arbitrary finite
 observed-score list; positivity and nonempty-block conditions are
 stated explicitly for the normal common-factor model 0<c<1.
 No independent measure-theoretic normality or conditional expectation
 premise is smuggled into an algebraic theorem.
 Proof/definition method: Reuse the canonical list sum and length
 lemmas, original Gaussian posterior center/precision/variance,
 original Schur covariance reduction and Stdlib ring/field/order
 tactics. Sign and equality cases derive from one shared variance
 and posterior-innovation identity rather than duplicated formulas.
 Library reuse: FiniteSum, EquicorrelationVectors,
 GaussianConditionalKernel, GaussianInnovationBounds and Stdlib.
 Boundary: Exact pointwise Gaussian regression/kernels and
 information-order properties; no proof of normalized probability
 measures, independence or conditional expectation is claimed.
*)
Theorem gsp_residual_energy_append : forall xs ys:list R, forall theta:R, gk_residual_energy (xs++ys) theta=gk_residual_energy xs theta+gk_residual_energy ys theta.
Proof.
 intros xs ys theta.
 unfold gk_residual_energy,vector_center_energy.
 apply finite_sum_app.
Qed.

(** [gsp_denominator_append] (theorem).
 Mathematical meaning: Appending an arbitrary finite history changes the equicorrelation denominator by its size times c.
 Exact checked proposition: forall xs ys:list R, forall c:R, gk_d (xs++ys) c=gk_d xs c+gk_mass ys*c.
 Premises and side conditions: The model uses an arbitrary finite
 observed-score list; positivity and nonempty-block conditions are
 stated explicitly for the normal common-factor model 0<c<1.
 No independent measure-theoretic normality or conditional expectation
 premise is smuggled into an algebraic theorem.
 Proof/definition method: Reuse the canonical list sum and length
 lemmas, original Gaussian posterior center/precision/variance,
 original Schur covariance reduction and Stdlib ring/field/order
 tactics. Sign and equality cases derive from one shared variance
 and posterior-innovation identity rather than duplicated formulas.
 Library reuse: FiniteSum, EquicorrelationVectors,
 GaussianConditionalKernel, GaussianInnovationBounds and Stdlib.
 Boundary: Exact pointwise Gaussian regression/kernels and
 information-order properties; no proof of normalized probability
 measures, independence or conditional expectation is claimed.
*)
Theorem gsp_denominator_append : forall xs ys:list R, forall c:R, gk_d (xs++ys) c=gk_d xs c+gk_mass ys*c.
Proof.
 intros xs ys c; unfold gk_d.
 rewrite gsp_mass_append.
 apply sequential_denominator_add.
Qed.

(** [gsp_precision_append] (theorem).
 Mathematical meaning: The Gaussian common-factor posterior precision increases additively with newly observed finite-history size.
 Exact checked proposition: forall xs ys:list R, forall c:R, gk_precision (xs++ys) c=gk_precision xs c+gk_mass ys/(1-c).
 Premises and side conditions: The model uses an arbitrary finite
 observed-score list; positivity and nonempty-block conditions are
 stated explicitly for the normal common-factor model 0<c<1.
 No independent measure-theoretic normality or conditional expectation
 premise is smuggled into an algebraic theorem.
 Proof/definition method: Reuse the canonical list sum and length
 lemmas, original Gaussian posterior center/precision/variance,
 original Schur covariance reduction and Stdlib ring/field/order
 tactics. Sign and equality cases derive from one shared variance
 and posterior-innovation identity rather than duplicated formulas.
 Library reuse: FiniteSum, EquicorrelationVectors,
 GaussianConditionalKernel, GaussianInnovationBounds and Stdlib.
 Boundary: Exact pointwise Gaussian regression/kernels and
 information-order properties; no proof of normalized probability
 measures, independence or conditional expectation is claimed.
*)
Theorem gsp_precision_append : forall xs ys:list R, forall c:R, gk_precision (xs++ys) c=gk_precision xs c+gk_mass ys/(1-c).
Proof.
 intros xs ys c.
 unfold gk_precision.
 rewrite gsp_mass_append.
 unfold Rdiv; ring.
Qed.

(** [gsp_precision_three_batches] (theorem).
 Mathematical meaning: Gaussian posterior precision accumulates new information additively over two arbitrary successive observed batches.
 Exact checked proposition: forall xs ys zs:list R, forall c:R, gk_precision (xs++ys++zs) c=gk_precision xs c+(gk_mass ys+gk_mass zs)/(1-c).
 Premises and side conditions: The model uses an arbitrary finite
 observed-score list; positivity and nonempty-block conditions are
 stated explicitly for the normal common-factor model 0<c<1.
 No independent measure-theoretic normality or conditional expectation
 premise is smuggled into an algebraic theorem.
 Proof/definition method: Reuse the canonical list sum and length
 lemmas, original Gaussian posterior center/precision/variance,
 original Schur covariance reduction and Stdlib ring/field/order
 tactics. Sign and equality cases derive from one shared variance
 and posterior-innovation identity rather than duplicated formulas.
 Library reuse: FiniteSum, EquicorrelationVectors,
 GaussianConditionalKernel, GaussianInnovationBounds and Stdlib.
 Boundary: Exact pointwise Gaussian regression/kernels and
 information-order properties; no proof of normalized probability
 measures, independence or conditional expectation is claimed.
*)
Theorem gsp_precision_three_batches : forall xs ys zs:list R, forall c:R, gk_precision (xs++ys++zs) c=gk_precision xs c+(gk_mass ys+gk_mass zs)/(1-c).
Proof.
 intros xs ys zs c.
 rewrite gsp_precision_append.
 rewrite gsp_mass_append.
 unfold Rdiv; ring.
Qed.

(** [gsp_center_append_sum_formula] (theorem).
 Mathematical meaning: The exact new posterior mean candidate depends on appended score values only through their total sum.
 Exact checked proposition: forall xs ys:list R, forall c:R, gk_center (xs++ys) c=c*(gk_sum xs+gk_sum ys)/gk_d (xs++ys) c.
 Premises and side conditions: The model uses an arbitrary finite
 observed-score list; positivity and nonempty-block conditions are
 stated explicitly for the normal common-factor model 0<c<1.
 No independent measure-theoretic normality or conditional expectation
 premise is smuggled into an algebraic theorem.
 Proof/definition method: Reuse the canonical list sum and length
 lemmas, original Gaussian posterior center/precision/variance,
 original Schur covariance reduction and Stdlib ring/field/order
 tactics. Sign and equality cases derive from one shared variance
 and posterior-innovation identity rather than duplicated formulas.
 Library reuse: FiniteSum, EquicorrelationVectors,
 GaussianConditionalKernel, GaussianInnovationBounds and Stdlib.
 Boundary: Exact pointwise Gaussian regression/kernels and
 information-order properties; no proof of normalized probability
 measures, independence or conditional expectation is claimed.
*)
Theorem gsp_center_append_sum_formula : forall xs ys:list R, forall c:R, gk_center (xs++ys) c=c*(gk_sum xs+gk_sum ys)/gk_d (xs++ys) c.
Proof.
 intros xs ys c.
 unfold gk_center.
 rewrite gsp_sum_append.
 reflexivity.
Qed.

(** [gsp_center_append_weighted_update] (theorem).
 Mathematical meaning: The Gaussian posterior mean candidate satisfies the exact normalized history-and-new-batch update equation.
 Exact checked proposition: forall xs ys:list R, forall c:R, 0<c -> c<1 -> gk_center (xs++ys) c=(gk_d xs c*gk_center xs c+c*gk_sum ys)/gk_d (xs++ys) c.
 Premises and side conditions: The model uses an arbitrary finite
 observed-score list; positivity and nonempty-block conditions are
 stated explicitly for the normal common-factor model 0<c<1.
 No independent measure-theoretic normality or conditional expectation
 premise is smuggled into an algebraic theorem.
 Proof/definition method: Reuse the canonical list sum and length
 lemmas, original Gaussian posterior center/precision/variance,
 original Schur covariance reduction and Stdlib ring/field/order
 tactics. Sign and equality cases derive from one shared variance
 and posterior-innovation identity rather than duplicated formulas.
 Library reuse: FiniteSum, EquicorrelationVectors,
 GaussianConditionalKernel, GaussianInnovationBounds and Stdlib.
 Boundary: Exact pointwise Gaussian regression/kernels and
 information-order properties; no proof of normalized probability
 measures, independence or conditional expectation is claimed.
*)
Theorem gsp_center_append_weighted_update : forall xs ys:list R, forall c:R, 0<c -> c<1 -> gk_center (xs++ys) c=(gk_d xs c*gk_center xs c+c*gk_sum ys)/gk_d (xs++ys) c.
Proof.
 intros xs ys c Hc Hu.
 assert (Hd:0<gk_d xs c)
   by (apply gk_d_positive; try assumption; apply gk_mass_nonnegative).
 assert (Hdall:0<gk_d (xs++ys) c)
   by (apply gk_d_positive; try assumption; apply gk_mass_nonnegative).
 unfold gk_center.
 rewrite gsp_sum_append.
 rewrite gsp_denominator_append.
 rewrite gsp_denominator_append in Hdall.
 field; nra.
Qed.

(** [gsp_center_append_innovation] (theorem).
 Mathematical meaning: The exact change in the Gaussian posterior center equals a gain times the sum of incoming score innovations.
 Exact checked proposition: forall xs ys:list R, forall c:R, 0<c -> c<1 -> gk_center (xs++ys) c-gk_center xs c=c*(gk_sum ys-gk_mass ys*gk_center xs c)/gk_d (xs++ys) c.
 Premises and side conditions: The model uses an arbitrary finite
 observed-score list; positivity and nonempty-block conditions are
 stated explicitly for the normal common-factor model 0<c<1.
 No independent measure-theoretic normality or conditional expectation
 premise is smuggled into an algebraic theorem.
 Proof/definition method: Reuse the canonical list sum and length
 lemmas, original Gaussian posterior center/precision/variance,
 original Schur covariance reduction and Stdlib ring/field/order
 tactics. Sign and equality cases derive from one shared variance
 and posterior-innovation identity rather than duplicated formulas.
 Library reuse: FiniteSum, EquicorrelationVectors,
 GaussianConditionalKernel, GaussianInnovationBounds and Stdlib.
 Boundary: Exact pointwise Gaussian regression/kernels and
 information-order properties; no proof of normalized probability
 measures, independence or conditional expectation is claimed.
*)
Theorem gsp_center_append_innovation : forall xs ys:list R, forall c:R, 0<c -> c<1 -> gk_center (xs++ys) c-gk_center xs c=c*(gk_sum ys-gk_mass ys*gk_center xs c)/gk_d (xs++ys) c.
Proof.
 intros xs ys c Hc Hu.
 assert (Hd:0<gk_d xs c)
   by (apply gk_d_positive; try assumption; apply gk_mass_nonnegative).
 assert (Hdall:0<gk_d (xs++ys) c)
   by (apply gk_d_positive; try assumption; apply gk_mass_nonnegative).
 unfold gk_center.
 rewrite gsp_sum_append.
 rewrite gsp_denominator_append.
 rewrite gsp_denominator_append in Hdall.
 field; nra.
Qed.

(** [gsp_variance_drop_identity] (theorem).
 Mathematical meaning: The information in a newly appended finite-history block yields an exact posterior variance-reduction formula.
 Exact checked proposition: forall xs ys:list R, forall c:R, 0<c -> c<1 -> gk_variance xs c-gk_variance (xs++ys) c=gk_mass ys*c*c*(1-c)/(gk_d xs c*gk_d (xs++ys) c).
 Premises and side conditions: The model uses an arbitrary finite
 observed-score list; positivity and nonempty-block conditions are
 stated explicitly for the normal common-factor model 0<c<1.
 No independent measure-theoretic normality or conditional expectation
 premise is smuggled into an algebraic theorem.
 Proof/definition method: Reuse the canonical list sum and length
 lemmas, original Gaussian posterior center/precision/variance,
 original Schur covariance reduction and Stdlib ring/field/order
 tactics. Sign and equality cases derive from one shared variance
 and posterior-innovation identity rather than duplicated formulas.
 Library reuse: FiniteSum, EquicorrelationVectors,
 GaussianConditionalKernel, GaussianInnovationBounds and Stdlib.
 Boundary: Exact pointwise Gaussian regression/kernels and
 information-order properties; no proof of normalized probability
 measures, independence or conditional expectation is claimed.
*)
Theorem gsp_variance_drop_identity : forall xs ys:list R, forall c:R, 0<c -> c<1 -> gk_variance xs c-gk_variance (xs++ys) c=gk_mass ys*c*c*(1-c)/(gk_d xs c*gk_d (xs++ys) c).
Proof.
 intros xs ys c Hc Hu.
 assert (Hd:0<gk_d xs c)
   by (apply gk_d_positive; try assumption; apply gk_mass_nonnegative).
 assert (Hdall:0<gk_d (xs++ys) c)
   by (apply gk_d_positive; try assumption; apply gk_mass_nonnegative).
 unfold gk_variance.
 rewrite gsp_denominator_append.
 rewrite gsp_denominator_append in Hdall.
 field; nra.
Qed.

(** [gsp_denominator_non_decreasing] (theorem).
 Mathematical meaning: At nonnegative common correlation, appending any score history cannot reduce the common-mode covariance eigenvalue.
 Exact checked proposition: forall xs ys:list R, forall c:R, 0<=c -> gk_d xs c<=gk_d (xs++ys) c.
 Premises and side conditions: The model uses an arbitrary finite
 observed-score list; positivity and nonempty-block conditions are
 stated explicitly for the normal common-factor model 0<c<1.
 No independent measure-theoretic normality or conditional expectation
 premise is smuggled into an algebraic theorem.
 Proof/definition method: Reuse the canonical list sum and length
 lemmas, original Gaussian posterior center/precision/variance,
 original Schur covariance reduction and Stdlib ring/field/order
 tactics. Sign and equality cases derive from one shared variance
 and posterior-innovation identity rather than duplicated formulas.
 Library reuse: FiniteSum, EquicorrelationVectors,
 GaussianConditionalKernel, GaussianInnovationBounds and Stdlib.
 Boundary: Exact pointwise Gaussian regression/kernels and
 information-order properties; no proof of normalized probability
 measures, independence or conditional expectation is claimed.
*)
Theorem gsp_denominator_non_decreasing : forall xs ys:list R, forall c:R, 0<=c -> gk_d xs c<=gk_d (xs++ys) c.
Proof.
 intros xs ys c Hc.
 rewrite gsp_denominator_append.
 pose proof (gk_mass_nonnegative ys) as Hmass.
 nra.
Qed.

(** [gsp_denominator_strict_increase_nonempty] (theorem).
 Mathematical meaning: Appending at least one observed score strictly increases the covariance common-mode denominator for positive correlation.
 Exact checked proposition: forall xs ys:list R, forall c:R, 0<c -> ys<>nil -> gk_d xs c<gk_d (xs++ys) c.
 Premises and side conditions: The model uses an arbitrary finite
 observed-score list; positivity and nonempty-block conditions are
 stated explicitly for the normal common-factor model 0<c<1.
 No independent measure-theoretic normality or conditional expectation
 premise is smuggled into an algebraic theorem.
 Proof/definition method: Reuse the canonical list sum and length
 lemmas, original Gaussian posterior center/precision/variance,
 original Schur covariance reduction and Stdlib ring/field/order
 tactics. Sign and equality cases derive from one shared variance
 and posterior-innovation identity rather than duplicated formulas.
 Library reuse: FiniteSum, EquicorrelationVectors,
 GaussianConditionalKernel, GaussianInnovationBounds and Stdlib.
 Boundary: Exact pointwise Gaussian regression/kernels and
 information-order properties; no proof of normalized probability
 measures, independence or conditional expectation is claimed.
*)
Theorem gsp_denominator_strict_increase_nonempty : forall xs ys:list R, forall c:R, 0<c -> ys<>nil -> gk_d xs c<gk_d (xs++ys) c.
Proof.
 intros xs ys c Hc Hys.
 rewrite gsp_denominator_append.
 pose proof (gk_mass_nonnegative ys) as Hmass.
 pose proof (gk_mass_nonzero ys Hys) as Hnonzero.
 assert (Hpositive:0<gk_mass ys) by lra.
 nra.
Qed.

(** [gsp_precision_non_decreasing] (theorem).
 Mathematical meaning: Posterior precision for a finite common-factor Gaussian history is monotone under additional observations whenever residual noise variance is positive.
 Exact checked proposition: forall xs ys:list R, forall c:R, c<1 -> gk_precision xs c<=gk_precision (xs++ys) c.
 Premises and side conditions: The model uses an arbitrary finite
 observed-score list; positivity and nonempty-block conditions are
 stated explicitly for the normal common-factor model 0<c<1.
 No independent measure-theoretic normality or conditional expectation
 premise is smuggled into an algebraic theorem.
 Proof/definition method: Reuse the canonical list sum and length
 lemmas, original Gaussian posterior center/precision/variance,
 original Schur covariance reduction and Stdlib ring/field/order
 tactics. Sign and equality cases derive from one shared variance
 and posterior-innovation identity rather than duplicated formulas.
 Library reuse: FiniteSum, EquicorrelationVectors,
 GaussianConditionalKernel, GaussianInnovationBounds and Stdlib.
 Boundary: Exact pointwise Gaussian regression/kernels and
 information-order properties; no proof of normalized probability
 measures, independence or conditional expectation is claimed.
*)
Theorem gsp_precision_non_decreasing : forall xs ys:list R, forall c:R, c<1 -> gk_precision xs c<=gk_precision (xs++ys) c.
Proof.
 intros xs ys c Hc.
 rewrite gsp_precision_append.
 pose proof (gk_mass_nonnegative ys) as Hmass.
 assert (Hinv:0</(1-c)) by (apply Rinv_0_lt_compat; lra).
 unfold Rdiv; nra.
Qed.

(** [gsp_precision_strict_increase_nonempty] (theorem).
 Mathematical meaning: Every nonempty appended history strictly increases common-factor posterior precision when 0<c<1.
 Exact checked proposition: forall xs ys:list R, forall c:R, 0<c -> c<1 -> ys<>nil -> gk_precision xs c<gk_precision (xs++ys) c.
 Premises and side conditions: The model uses an arbitrary finite
 observed-score list; positivity and nonempty-block conditions are
 stated explicitly for the normal common-factor model 0<c<1.
 No independent measure-theoretic normality or conditional expectation
 premise is smuggled into an algebraic theorem.
 Proof/definition method: Reuse the canonical list sum and length
 lemmas, original Gaussian posterior center/precision/variance,
 original Schur covariance reduction and Stdlib ring/field/order
 tactics. Sign and equality cases derive from one shared variance
 and posterior-innovation identity rather than duplicated formulas.
 Library reuse: FiniteSum, EquicorrelationVectors,
 GaussianConditionalKernel, GaussianInnovationBounds and Stdlib.
 Boundary: Exact pointwise Gaussian regression/kernels and
 information-order properties; no proof of normalized probability
 measures, independence or conditional expectation is claimed.
*)
Theorem gsp_precision_strict_increase_nonempty : forall xs ys:list R, forall c:R, 0<c -> c<1 -> ys<>nil -> gk_precision xs c<gk_precision (xs++ys) c.
Proof.
 intros xs ys c Hc Hu Hys.
 rewrite gsp_precision_append.
 pose proof (gk_mass_nonnegative ys) as Hmass.
 pose proof (gk_mass_nonzero ys Hys) as Hnonzero.
 assert (Hpositive:0<gk_mass ys) by lra.
 assert (Hinv:0</(1-c)) by (apply Rinv_0_lt_compat; lra).
 unfold Rdiv; nra.
Qed.

(** [gsp_variance_non_increasing] (theorem).
 Mathematical meaning: Adding an arbitrary finite history cannot increase the common-factor posterior variance in the proper Gaussian signal-noise domain.
 Exact checked proposition: forall xs ys:list R, forall c:R, 0<c -> c<1 -> gk_variance (xs++ys) c<=gk_variance xs c.
 Premises and side conditions: The model uses an arbitrary finite
 observed-score list; positivity and nonempty-block conditions are
 stated explicitly for the normal common-factor model 0<c<1.
 No independent measure-theoretic normality or conditional expectation
 premise is smuggled into an algebraic theorem.
 Proof/definition method: Reuse the canonical list sum and length
 lemmas, original Gaussian posterior center/precision/variance,
 original Schur covariance reduction and Stdlib ring/field/order
 tactics. Sign and equality cases derive from one shared variance
 and posterior-innovation identity rather than duplicated formulas.
 Library reuse: FiniteSum, EquicorrelationVectors,
 GaussianConditionalKernel, GaussianInnovationBounds and Stdlib.
 Boundary: Exact pointwise Gaussian regression/kernels and
 information-order properties; no proof of normalized probability
 measures, independence or conditional expectation is claimed.
*)
Theorem gsp_variance_non_increasing : forall xs ys:list R, forall c:R, 0<c -> c<1 -> gk_variance (xs++ys) c<=gk_variance xs c.
Proof.
 intros xs ys c Hc Hu.
 pose proof (gsp_variance_drop_identity xs ys c Hc Hu) as Hdrop.
 assert (Hmass:0<=gk_mass ys) by apply gk_mass_nonnegative.
 assert (Hnum:0<=gk_mass ys*c*c*(1-c)).
 { replace (gk_mass ys*c*c*(1-c)) with ((gk_mass ys*(c*c))*(1-c)) by ring.
   apply Rmult_le_pos.
   - apply Rmult_le_pos; [exact Hmass|nra].
   - lra. }
 assert (Hd:0<gk_d xs c)
   by (apply gk_d_positive; try assumption; apply gk_mass_nonnegative).
 assert (Hdall:0<gk_d (xs++ys) c)
   by (apply gk_d_positive; try assumption; apply gk_mass_nonnegative).
 assert (Hden:0<gk_d xs c*gk_d (xs++ys) c)
   by (apply Rmult_lt_0_compat; assumption).
 assert (Hq:0<=gk_mass ys*c*c*(1-c)/(gk_d xs c*gk_d (xs++ys) c)).
 { unfold Rdiv; apply Rmult_le_pos; [exact Hnum|].
   left; apply Rinv_0_lt_compat; exact Hden. }
 lra.
Qed.

(** [gsp_variance_strict_decrease_nonempty] (theorem).
 Mathematical meaning: Every newly observed nonempty block strictly lowers the latent-factor posterior variance for 0<c<1.
 Exact checked proposition: forall xs ys:list R, forall c:R, 0<c -> c<1 -> ys<>nil -> gk_variance (xs++ys) c<gk_variance xs c.
 Premises and side conditions: The model uses an arbitrary finite
 observed-score list; positivity and nonempty-block conditions are
 stated explicitly for the normal common-factor model 0<c<1.
 No independent measure-theoretic normality or conditional expectation
 premise is smuggled into an algebraic theorem.
 Proof/definition method: Reuse the canonical list sum and length
 lemmas, original Gaussian posterior center/precision/variance,
 original Schur covariance reduction and Stdlib ring/field/order
 tactics. Sign and equality cases derive from one shared variance
 and posterior-innovation identity rather than duplicated formulas.
 Library reuse: FiniteSum, EquicorrelationVectors,
 GaussianConditionalKernel, GaussianInnovationBounds and Stdlib.
 Boundary: Exact pointwise Gaussian regression/kernels and
 information-order properties; no proof of normalized probability
 measures, independence or conditional expectation is claimed.
*)
Theorem gsp_variance_strict_decrease_nonempty : forall xs ys:list R, forall c:R, 0<c -> c<1 -> ys<>nil -> gk_variance (xs++ys) c<gk_variance xs c.
Proof.
 intros xs ys c Hc Hu Hys.
 pose proof (gsp_variance_drop_identity xs ys c Hc Hu) as Hdrop.
 pose proof (gk_mass_nonnegative ys) as Hmass.
 pose proof (gk_mass_nonzero ys Hys) as Hnonzero.
 assert (Hpositive:0<gk_mass ys) by lra.
 assert (Hnum:0<gk_mass ys*c*c*(1-c)).
 { replace (gk_mass ys*c*c*(1-c)) with ((gk_mass ys*(c*c))*(1-c)) by ring.
   apply Rmult_lt_0_compat.
   - apply Rmult_lt_0_compat; [exact Hpositive|nra].
   - lra. }
 assert (Hd:0<gk_d xs c)
   by (apply gk_d_positive; try assumption; apply gk_mass_nonnegative).
 assert (Hdall:0<gk_d (xs++ys) c)
   by (apply gk_d_positive; try assumption; apply gk_mass_nonnegative).
 assert (Hden:0<gk_d xs c*gk_d (xs++ys) c)
   by (apply Rmult_lt_0_compat; assumption).
 assert (Hq:0<gk_mass ys*c*c*(1-c)/(gk_d xs c*gk_d (xs++ys) c)).
 { unfold Rdiv; apply Rmult_lt_0_compat; [exact Hnum|].
   apply Rinv_0_lt_compat; exact Hden. }
 lra.
Qed.

(** [gsp_center_zero_at_zero_sum] (theorem).
 Mathematical meaning: An exactly centered finite observed-score history yields a zero Gaussian latent posterior center for every correlation input.
 Exact checked proposition: forall xs:list R, forall c:R, gk_sum xs=0 -> gk_center xs c=0.
 Premises and side conditions: The model uses an arbitrary finite
 observed-score list; positivity and nonempty-block conditions are
 stated explicitly for the normal common-factor model 0<c<1.
 No independent measure-theoretic normality or conditional expectation
 premise is smuggled into an algebraic theorem.
 Proof/definition method: Reuse the canonical list sum and length
 lemmas, original Gaussian posterior center/precision/variance,
 original Schur covariance reduction and Stdlib ring/field/order
 tactics. Sign and equality cases derive from one shared variance
 and posterior-innovation identity rather than duplicated formulas.
 Library reuse: FiniteSum, EquicorrelationVectors,
 GaussianConditionalKernel, GaussianInnovationBounds and Stdlib.
 Boundary: Exact pointwise Gaussian regression/kernels and
 information-order properties; no proof of normalized probability
 measures, independence or conditional expectation is claimed.
*)
Theorem gsp_center_zero_at_zero_sum : forall xs:list R, forall c:R, gk_sum xs=0 -> gk_center xs c=0.
Proof.
 intros xs c Hzero.
 unfold gk_center.
 rewrite Hzero.
 unfold Rdiv; ring.
Qed.

(** [gsp_center_nonnegative_for_nonnegative_sum] (theorem).
 Mathematical meaning: In the positive-correlation signal-noise model, a nonnegative observed sum produces a nonnegative Gaussian posterior center.
 Exact checked proposition: forall xs:list R, forall c:R, 0<c -> c<1 -> 0<=gk_sum xs -> 0<=gk_center xs c.
 Premises and side conditions: The model uses an arbitrary finite
 observed-score list; positivity and nonempty-block conditions are
 stated explicitly for the normal common-factor model 0<c<1.
 No independent measure-theoretic normality or conditional expectation
 premise is smuggled into an algebraic theorem.
 Proof/definition method: Reuse the canonical list sum and length
 lemmas, original Gaussian posterior center/precision/variance,
 original Schur covariance reduction and Stdlib ring/field/order
 tactics. Sign and equality cases derive from one shared variance
 and posterior-innovation identity rather than duplicated formulas.
 Library reuse: FiniteSum, EquicorrelationVectors,
 GaussianConditionalKernel, GaussianInnovationBounds and Stdlib.
 Boundary: Exact pointwise Gaussian regression/kernels and
 information-order properties; no proof of normalized probability
 measures, independence or conditional expectation is claimed.
*)
Theorem gsp_center_nonnegative_for_nonnegative_sum : forall xs:list R, forall c:R, 0<c -> c<1 -> 0<=gk_sum xs -> 0<=gk_center xs c.
Proof.
 intros xs c Hc Hu Hs.
 rewrite gk_center_matches_unequal_history.
 apply d052_mean_nonnegative_gain; try lra.
 apply gk_d_positive; try assumption; apply gk_mass_nonnegative.
Qed.

(** [gsp_center_positive_for_positive_sum] (theorem).
 Mathematical meaning: For positive correlation, a positive observed sum yields a strictly positive Gaussian posterior center.
 Exact checked proposition: forall xs:list R, forall c:R, 0<c -> c<1 -> 0<gk_sum xs -> 0<gk_center xs c.
 Premises and side conditions: The model uses an arbitrary finite
 observed-score list; positivity and nonempty-block conditions are
 stated explicitly for the normal common-factor model 0<c<1.
 No independent measure-theoretic normality or conditional expectation
 premise is smuggled into an algebraic theorem.
 Proof/definition method: Reuse the canonical list sum and length
 lemmas, original Gaussian posterior center/precision/variance,
 original Schur covariance reduction and Stdlib ring/field/order
 tactics. Sign and equality cases derive from one shared variance
 and posterior-innovation identity rather than duplicated formulas.
 Library reuse: FiniteSum, EquicorrelationVectors,
 GaussianConditionalKernel, GaussianInnovationBounds and Stdlib.
 Boundary: Exact pointwise Gaussian regression/kernels and
 information-order properties; no proof of normalized probability
 measures, independence or conditional expectation is claimed.
*)
Theorem gsp_center_positive_for_positive_sum : forall xs:list R, forall c:R, 0<c -> c<1 -> 0<gk_sum xs -> 0<gk_center xs c.
Proof.
 intros xs c Hc Hu Hs.
 rewrite gk_center_matches_unequal_history.
 apply d052_mean_positive_gain; try assumption.
 apply gk_d_positive; try assumption; apply gk_mass_nonnegative.
Qed.

(** [gsp_center_negative_for_negative_sum] (theorem).
 Mathematical meaning: For positive correlation, a negative observed sum yields a strictly negative Gaussian posterior center.
 Exact checked proposition: forall xs:list R, forall c:R, 0<c -> c<1 -> gk_sum xs<0 -> gk_center xs c<0.
 Premises and side conditions: The model uses an arbitrary finite
 observed-score list; positivity and nonempty-block conditions are
 stated explicitly for the normal common-factor model 0<c<1.
 No independent measure-theoretic normality or conditional expectation
 premise is smuggled into an algebraic theorem.
 Proof/definition method: Reuse the canonical list sum and length
 lemmas, original Gaussian posterior center/precision/variance,
 original Schur covariance reduction and Stdlib ring/field/order
 tactics. Sign and equality cases derive from one shared variance
 and posterior-innovation identity rather than duplicated formulas.
 Library reuse: FiniteSum, EquicorrelationVectors,
 GaussianConditionalKernel, GaussianInnovationBounds and Stdlib.
 Boundary: Exact pointwise Gaussian regression/kernels and
 information-order properties; no proof of normalized probability
 measures, independence or conditional expectation is claimed.
*)
Theorem gsp_center_negative_for_negative_sum : forall xs:list R, forall c:R, 0<c -> c<1 -> gk_sum xs<0 -> gk_center xs c<0.
Proof.
 intros xs c Hc Hu Hs.
 rewrite gk_center_matches_unequal_history.
 apply gib_signed_positive_predictor_negative_history; try assumption.
 apply gk_d_positive; try assumption; apply gk_mass_nonnegative.
Qed.

(** [gsp_precision_same_history_length] (theorem).
 Mathematical meaning: Gaussian posterior precision is entirely determined by observed-history size and c, not by the observed numeric score values.
 Exact checked proposition: forall xs ys:list R, forall c:R, length xs=length ys -> gk_precision xs c=gk_precision ys c.
 Premises and side conditions: The model uses an arbitrary finite
 observed-score list; positivity and nonempty-block conditions are
 stated explicitly for the normal common-factor model 0<c<1.
 No independent measure-theoretic normality or conditional expectation
 premise is smuggled into an algebraic theorem.
 Proof/definition method: Reuse the canonical list sum and length
 lemmas, original Gaussian posterior center/precision/variance,
 original Schur covariance reduction and Stdlib ring/field/order
 tactics. Sign and equality cases derive from one shared variance
 and posterior-innovation identity rather than duplicated formulas.
 Library reuse: FiniteSum, EquicorrelationVectors,
 GaussianConditionalKernel, GaussianInnovationBounds and Stdlib.
 Boundary: Exact pointwise Gaussian regression/kernels and
 information-order properties; no proof of normalized probability
 measures, independence or conditional expectation is claimed.
*)
Theorem gsp_precision_same_history_length : forall xs ys:list R, forall c:R, length xs=length ys -> gk_precision xs c=gk_precision ys c.
Proof.
 intros xs ys c Hlen.
 unfold gk_precision,gk_mass.
 rewrite Hlen; reflexivity.
Qed.

(** [gsp_variance_same_history_length] (theorem).
 Mathematical meaning: The latent Gaussian posterior variance is entirely determined by history length and common correlation.
 Exact checked proposition: forall xs ys:list R, forall c:R, length xs=length ys -> gk_variance xs c=gk_variance ys c.
 Premises and side conditions: The model uses an arbitrary finite
 observed-score list; positivity and nonempty-block conditions are
 stated explicitly for the normal common-factor model 0<c<1.
 No independent measure-theoretic normality or conditional expectation
 premise is smuggled into an algebraic theorem.
 Proof/definition method: Reuse the canonical list sum and length
 lemmas, original Gaussian posterior center/precision/variance,
 original Schur covariance reduction and Stdlib ring/field/order
 tactics. Sign and equality cases derive from one shared variance
 and posterior-innovation identity rather than duplicated formulas.
 Library reuse: FiniteSum, EquicorrelationVectors,
 GaussianConditionalKernel, GaussianInnovationBounds and Stdlib.
 Boundary: Exact pointwise Gaussian regression/kernels and
 information-order properties; no proof of normalized probability
 measures, independence or conditional expectation is claimed.
*)
Theorem gsp_variance_same_history_length : forall xs ys:list R, forall c:R, length xs=length ys -> gk_variance xs c=gk_variance ys c.
Proof.
 intros xs ys c Hlen.
 unfold gk_variance,gk_d,gk_mass.
 rewrite Hlen; reflexivity.
Qed.

(** [gsp_center_same_length_and_sum] (theorem).
 Mathematical meaning: The posterior mean candidate is a sufficient-statistic function of the observed history length and sum.
 Exact checked proposition: forall xs ys:list R, forall c:R, length xs=length ys -> gk_sum xs=gk_sum ys -> gk_center xs c=gk_center ys c.
 Premises and side conditions: The model uses an arbitrary finite
 observed-score list; positivity and nonempty-block conditions are
 stated explicitly for the normal common-factor model 0<c<1.
 No independent measure-theoretic normality or conditional expectation
 premise is smuggled into an algebraic theorem.
 Proof/definition method: Reuse the canonical list sum and length
 lemmas, original Gaussian posterior center/precision/variance,
 original Schur covariance reduction and Stdlib ring/field/order
 tactics. Sign and equality cases derive from one shared variance
 and posterior-innovation identity rather than duplicated formulas.
 Library reuse: FiniteSum, EquicorrelationVectors,
 GaussianConditionalKernel, GaussianInnovationBounds and Stdlib.
 Boundary: Exact pointwise Gaussian regression/kernels and
 information-order properties; no proof of normalized probability
 measures, independence or conditional expectation is claimed.
*)
Theorem gsp_center_same_length_and_sum : forall xs ys:list R, forall c:R, length xs=length ys -> gk_sum xs=gk_sum ys -> gk_center xs c=gk_center ys c.
Proof.
 intros xs ys c Hlen Hsum.
 unfold gk_center,gk_d,gk_mass.
 rewrite Hlen,Hsum; reflexivity.
Qed.

(** [gsp_posterior_quadratic_same_sufficient_statistics] (theorem).
 Mathematical meaning: Two histories of equal length and score sum induce identical centered Gaussian posterior quadratic functions, regardless of their score energies.
 Exact checked proposition: forall xs ys:list R, forall c theta:R, length xs=length ys -> gk_sum xs=gk_sum ys -> gk_posterior_quadratic xs c theta=gk_posterior_quadratic ys c theta.
 Premises and side conditions: The model uses an arbitrary finite
 observed-score list; positivity and nonempty-block conditions are
 stated explicitly for the normal common-factor model 0<c<1.
 No independent measure-theoretic normality or conditional expectation
 premise is smuggled into an algebraic theorem.
 Proof/definition method: Reuse the canonical list sum and length
 lemmas, original Gaussian posterior center/precision/variance,
 original Schur covariance reduction and Stdlib ring/field/order
 tactics. Sign and equality cases derive from one shared variance
 and posterior-innovation identity rather than duplicated formulas.
 Library reuse: FiniteSum, EquicorrelationVectors,
 GaussianConditionalKernel, GaussianInnovationBounds and Stdlib.
 Boundary: Exact pointwise Gaussian regression/kernels and
 information-order properties; no proof of normalized probability
 measures, independence or conditional expectation is claimed.
*)
Theorem gsp_posterior_quadratic_same_sufficient_statistics : forall xs ys:list R, forall c theta:R, length xs=length ys -> gk_sum xs=gk_sum ys -> gk_posterior_quadratic xs c theta=gk_posterior_quadratic ys c theta.
Proof.
 intros xs ys c theta Hlen Hsum.
 unfold gk_posterior_quadratic.
 rewrite (gsp_precision_same_history_length xs ys c Hlen).
 rewrite (gsp_center_same_length_and_sum xs ys c Hlen Hsum).
 reflexivity.
Qed.

(** [gsp_posterior_kernel_same_sufficient_statistics] (theorem).
 Mathematical meaning: The entire unnormalized Gaussian posterior kernel is identical for histories with the same count and score sum.
 Exact checked proposition: forall xs ys:list R, forall c theta:R, length xs=length ys -> gk_sum xs=gk_sum ys -> gk_posterior_kernel xs c theta=gk_posterior_kernel ys c theta.
 Premises and side conditions: The model uses an arbitrary finite
 observed-score list; positivity and nonempty-block conditions are
 stated explicitly for the normal common-factor model 0<c<1.
 No independent measure-theoretic normality or conditional expectation
 premise is smuggled into an algebraic theorem.
 Proof/definition method: Reuse the canonical list sum and length
 lemmas, original Gaussian posterior center/precision/variance,
 original Schur covariance reduction and Stdlib ring/field/order
 tactics. Sign and equality cases derive from one shared variance
 and posterior-innovation identity rather than duplicated formulas.
 Library reuse: FiniteSum, EquicorrelationVectors,
 GaussianConditionalKernel, GaussianInnovationBounds and Stdlib.
 Boundary: Exact pointwise Gaussian regression/kernels and
 information-order properties; no proof of normalized probability
 measures, independence or conditional expectation is claimed.
*)
Theorem gsp_posterior_kernel_same_sufficient_statistics : forall xs ys:list R, forall c theta:R, length xs=length ys -> gk_sum xs=gk_sum ys -> gk_posterior_kernel xs c theta=gk_posterior_kernel ys c theta.
Proof.
 intros xs ys c theta Hlen Hsum.
 unfold gk_posterior_kernel.
 rewrite (gsp_posterior_quadratic_same_sufficient_statistics xs ys c theta Hlen Hsum).
 reflexivity.
Qed.

(** [gsp_joint_quadratic_energy_shift] (theorem).
 Mathematical meaning: If two histories have the same count and sum, their joint Gaussian latent likelihood quadratics differ only by a theta-independent energy constant.
 Exact checked proposition: forall xs ys:list R, forall c theta:R, length xs=length ys -> gk_sum xs=gk_sum ys -> gk_joint_quadratic xs c theta-gk_joint_quadratic ys c theta=(vector_square_energy xs-vector_square_energy ys)/(1-c).
 Premises and side conditions: The model uses an arbitrary finite
 observed-score list; positivity and nonempty-block conditions are
 stated explicitly for the normal common-factor model 0<c<1.
 No independent measure-theoretic normality or conditional expectation
 premise is smuggled into an algebraic theorem.
 Proof/definition method: Reuse the canonical list sum and length
 lemmas, original Gaussian posterior center/precision/variance,
 original Schur covariance reduction and Stdlib ring/field/order
 tactics. Sign and equality cases derive from one shared variance
 and posterior-innovation identity rather than duplicated formulas.
 Library reuse: FiniteSum, EquicorrelationVectors,
 GaussianConditionalKernel, GaussianInnovationBounds and Stdlib.
 Boundary: Exact pointwise Gaussian regression/kernels and
 information-order properties; no proof of normalized probability
 measures, independence or conditional expectation is claimed.
*)
Theorem gsp_joint_quadratic_energy_shift : forall xs ys:list R, forall c theta:R, length xs=length ys -> gk_sum xs=gk_sum ys -> gk_joint_quadratic xs c theta-gk_joint_quadratic ys c theta=(vector_square_energy xs-vector_square_energy ys)/(1-c).
Proof.
 intros xs ys c theta Hlen Hsum.
 repeat rewrite gk_joint_quadratic_expansion.
 unfold gk_mass.
 rewrite Hlen,Hsum.
 unfold Rdiv; ring.
Qed.

(** [gsp_center_append_zero_sum_attenuation] (theorem).
 Mathematical meaning: When newly appended observations sum to zero, the old Gaussian posterior center is attenuated by the observed-to-total common-mode denominator ratio.
 Exact checked proposition: forall xs ys:list R, forall c:R, 0<c -> c<1 -> gk_sum ys=0 -> gk_center (xs++ys) c=(gk_d xs c/gk_d (xs++ys) c)*gk_center xs c.
 Premises and side conditions: The model uses an arbitrary finite
 observed-score list; positivity and nonempty-block conditions are
 stated explicitly for the normal common-factor model 0<c<1.
 No independent measure-theoretic normality or conditional expectation
 premise is smuggled into an algebraic theorem.
 Proof/definition method: Reuse the canonical list sum and length
 lemmas, original Gaussian posterior center/precision/variance,
 original Schur covariance reduction and Stdlib ring/field/order
 tactics. Sign and equality cases derive from one shared variance
 and posterior-innovation identity rather than duplicated formulas.
 Library reuse: FiniteSum, EquicorrelationVectors,
 GaussianConditionalKernel, GaussianInnovationBounds and Stdlib.
 Boundary: Exact pointwise Gaussian regression/kernels and
 information-order properties; no proof of normalized probability
 measures, independence or conditional expectation is claimed.
*)
Theorem gsp_center_append_zero_sum_attenuation : forall xs ys:list R, forall c:R, 0<c -> c<1 -> gk_sum ys=0 -> gk_center (xs++ys) c=(gk_d xs c/gk_d (xs++ys) c)*gk_center xs c.
Proof.
 intros xs ys c Hc Hu Hzero.
 rewrite (gsp_center_append_weighted_update xs ys c Hc Hu).
 rewrite Hzero.
 unfold Rdiv; ring.
Qed.

(** [gsp_denominator_strict_append_iff_nonempty] (theorem).
 Mathematical meaning: For positive common correlation, observing an additional block strictly increases the covariance common-mode eigenvalue exactly when the block is nonempty.
 Exact checked proposition: forall xs ys:list R, forall c:R, 0<c -> (gk_d xs c<gk_d (xs++ys) c <-> ys<>nil).
 Premises and side conditions: The model uses an arbitrary finite
 observed-score list; positivity and nonempty-block conditions are
 stated explicitly for the normal common-factor model 0<c<1.
 No independent measure-theoretic normality or conditional expectation
 premise is smuggled into an algebraic theorem.
 Proof/definition method: Reuse the canonical list sum and length
 lemmas, original Gaussian posterior center/precision/variance,
 original Schur covariance reduction and Stdlib ring/field/order
 tactics. Sign and equality cases derive from one shared variance
 and posterior-innovation identity rather than duplicated formulas.
 Library reuse: FiniteSum, EquicorrelationVectors,
 GaussianConditionalKernel, GaussianInnovationBounds and Stdlib.
 Boundary: Exact pointwise Gaussian regression/kernels and
 information-order properties; no proof of normalized probability
 measures, independence or conditional expectation is claimed.
*)
Theorem gsp_denominator_strict_append_iff_nonempty : forall xs ys:list R, forall c:R, 0<c -> (gk_d xs c<gk_d (xs++ys) c <-> ys<>nil).
Proof.
 intros xs ys c Hc.
 split.
 - intro Hlt; intro Hnil; subst ys.
   rewrite app_nil_r in Hlt; lra.
 - intro Hys; apply gsp_denominator_strict_increase_nonempty; assumption.
Qed.

(** [gsp_precision_strict_append_iff_nonempty] (theorem).
 Mathematical meaning: For proper positive correlation, posterior precision strictly increases if and only if at least one observation is appended.
 Exact checked proposition: forall xs ys:list R, forall c:R, 0<c -> c<1 -> (gk_precision xs c<gk_precision (xs++ys) c <-> ys<>nil).
 Premises and side conditions: The model uses an arbitrary finite
 observed-score list; positivity and nonempty-block conditions are
 stated explicitly for the normal common-factor model 0<c<1.
 No independent measure-theoretic normality or conditional expectation
 premise is smuggled into an algebraic theorem.
 Proof/definition method: Reuse the canonical list sum and length
 lemmas, original Gaussian posterior center/precision/variance,
 original Schur covariance reduction and Stdlib ring/field/order
 tactics. Sign and equality cases derive from one shared variance
 and posterior-innovation identity rather than duplicated formulas.
 Library reuse: FiniteSum, EquicorrelationVectors,
 GaussianConditionalKernel, GaussianInnovationBounds and Stdlib.
 Boundary: Exact pointwise Gaussian regression/kernels and
 information-order properties; no proof of normalized probability
 measures, independence or conditional expectation is claimed.
*)
Theorem gsp_precision_strict_append_iff_nonempty : forall xs ys:list R, forall c:R, 0<c -> c<1 -> (gk_precision xs c<gk_precision (xs++ys) c <-> ys<>nil).
Proof.
 intros xs ys c Hc Hu.
 split.
 - intro Hlt; intro Hnil; subst ys.
   rewrite app_nil_r in Hlt; lra.
 - intro Hys; apply gsp_precision_strict_increase_nonempty; assumption.
Qed.

(** [gsp_variance_strict_append_iff_nonempty] (theorem).
 Mathematical meaning: For proper signal/noise parameters, posterior variance strictly decreases precisely when the appended history is nonempty.
 Exact checked proposition: forall xs ys:list R, forall c:R, 0<c -> c<1 -> (gk_variance (xs++ys) c<gk_variance xs c <-> ys<>nil).
 Premises and side conditions: The model uses an arbitrary finite
 observed-score list; positivity and nonempty-block conditions are
 stated explicitly for the normal common-factor model 0<c<1.
 No independent measure-theoretic normality or conditional expectation
 premise is smuggled into an algebraic theorem.
 Proof/definition method: Reuse the canonical list sum and length
 lemmas, original Gaussian posterior center/precision/variance,
 original Schur covariance reduction and Stdlib ring/field/order
 tactics. Sign and equality cases derive from one shared variance
 and posterior-innovation identity rather than duplicated formulas.
 Library reuse: FiniteSum, EquicorrelationVectors,
 GaussianConditionalKernel, GaussianInnovationBounds and Stdlib.
 Boundary: Exact pointwise Gaussian regression/kernels and
 information-order properties; no proof of normalized probability
 measures, independence or conditional expectation is claimed.
*)
Theorem gsp_variance_strict_append_iff_nonempty : forall xs ys:list R, forall c:R, 0<c -> c<1 -> (gk_variance (xs++ys) c<gk_variance xs c <-> ys<>nil).
Proof.
 intros xs ys c Hc Hu.
 split.
 - intro Hlt; intro Hnil; subst ys.
   rewrite app_nil_r in Hlt; lra.
 - intro Hys; apply gsp_variance_strict_decrease_nonempty; assumption.
Qed.

(** [gsp_center_append_positive_innovation_increases] (theorem).
 Mathematical meaning: A positive incoming score innovation strictly increases the Gaussian posterior center for 0<c<1.
 Exact checked proposition: forall xs ys:list R, forall c:R, 0<c -> c<1 -> 0<gk_sum ys-gk_mass ys*gk_center xs c -> gk_center xs c<gk_center (xs++ys) c.
 Premises and side conditions: The model uses an arbitrary finite
 observed-score list; positivity and nonempty-block conditions are
 stated explicitly for the normal common-factor model 0<c<1.
 No independent measure-theoretic normality or conditional expectation
 premise is smuggled into an algebraic theorem.
 Proof/definition method: Reuse the canonical list sum and length
 lemmas, original Gaussian posterior center/precision/variance,
 original Schur covariance reduction and Stdlib ring/field/order
 tactics. Sign and equality cases derive from one shared variance
 and posterior-innovation identity rather than duplicated formulas.
 Library reuse: FiniteSum, EquicorrelationVectors,
 GaussianConditionalKernel, GaussianInnovationBounds and Stdlib.
 Boundary: Exact pointwise Gaussian regression/kernels and
 information-order properties; no proof of normalized probability
 measures, independence or conditional expectation is claimed.
*)
Theorem gsp_center_append_positive_innovation_increases : forall xs ys:list R, forall c:R, 0<c -> c<1 -> 0<gk_sum ys-gk_mass ys*gk_center xs c -> gk_center xs c<gk_center (xs++ys) c.
Proof.
 intros xs ys c Hc Hu Hinnov.
 pose proof (gsp_center_append_innovation xs ys c Hc Hu) as Hdelta.
 assert (Hdall:0<gk_d (xs++ys) c)
   by (apply gk_d_positive; try assumption; apply gk_mass_nonnegative).
 assert (Hnum:0<c*(gk_sum ys-gk_mass ys*gk_center xs c)) by nra.
 assert (Hq:0<c*(gk_sum ys-gk_mass ys*gk_center xs c)/gk_d (xs++ys) c).
 { unfold Rdiv; apply Rmult_lt_0_compat; [exact Hnum|].
   apply Rinv_0_lt_compat; exact Hdall. }
 lra.
Qed.

(** [gsp_center_append_negative_innovation_decreases] (theorem).
 Mathematical meaning: A negative incoming score innovation strictly decreases the Gaussian posterior center for 0<c<1.
 Exact checked proposition: forall xs ys:list R, forall c:R, 0<c -> c<1 -> gk_sum ys-gk_mass ys*gk_center xs c<0 -> gk_center (xs++ys) c<gk_center xs c.
 Premises and side conditions: The model uses an arbitrary finite
 observed-score list; positivity and nonempty-block conditions are
 stated explicitly for the normal common-factor model 0<c<1.
 No independent measure-theoretic normality or conditional expectation
 premise is smuggled into an algebraic theorem.
 Proof/definition method: Reuse the canonical list sum and length
 lemmas, original Gaussian posterior center/precision/variance,
 original Schur covariance reduction and Stdlib ring/field/order
 tactics. Sign and equality cases derive from one shared variance
 and posterior-innovation identity rather than duplicated formulas.
 Library reuse: FiniteSum, EquicorrelationVectors,
 GaussianConditionalKernel, GaussianInnovationBounds and Stdlib.
 Boundary: Exact pointwise Gaussian regression/kernels and
 information-order properties; no proof of normalized probability
 measures, independence or conditional expectation is claimed.
*)
Theorem gsp_center_append_negative_innovation_decreases : forall xs ys:list R, forall c:R, 0<c -> c<1 -> gk_sum ys-gk_mass ys*gk_center xs c<0 -> gk_center (xs++ys) c<gk_center xs c.
Proof.
 intros xs ys c Hc Hu Hinnov.
 pose proof (gsp_center_append_innovation xs ys c Hc Hu) as Hdelta.
 assert (Hdall:0<gk_d (xs++ys) c)
   by (apply gk_d_positive; try assumption; apply gk_mass_nonnegative).
 assert (Hnum:c*(gk_sum ys-gk_mass ys*gk_center xs c)<0) by nra.
 assert (Hq:c*(gk_sum ys-gk_mass ys*gk_center xs c)/gk_d (xs++ys) c<0).
 { unfold Rdiv.
   replace 0 with (0 * /gk_d (xs++ys) c) by ring.
   apply Rmult_lt_compat_r; [apply Rinv_0_lt_compat; exact Hdall|exact Hnum]. }
 lra.
Qed.

