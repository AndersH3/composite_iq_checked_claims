(** Module: PooledMomentsAlgebra.v
 Purpose: Prove the exact two-group within/between sample variance
 decomposition used in all three simulation reports' pooled replicates.
 Mathematical representation: Real positive group counts n,m, means a,b,
 within-group centered sums u,v, and the pooled weighted mean are
 combined by standard corrected-sum-of-squares formulas.
 Explicit hypotheses: All grouped-variance theorems require positive
 counts, and unbiased variance division requires total count strictly >1.
 No claim assumes independence just to prove an algebraic identity.
 Library use: Rocq Stdlib Reals, Lra, Field, Psatz and Ring; no new
 finite-list sum, general matrix inverse, Gaussian or binomial implementation.
 Limitations: This module proves the exact two-batch ANOVA algebra (a bridge
 for G12); arbitrary-list group induction and stochastic sample laws are
 separate obligations and are not silently inferred.
 Reproduction: scripts/compile_rocq.sh and pinned Rocq Prover 9.2.
 AI disclosure: AI-assisted mathematical specifications, proof scripts
 and source documentation; correctness is decided by Rocq kernel checking.
*)
From Stdlib Require Import Reals Lra Psatz Ring Field.
Open Scope R_scope.

(** [pooled_mass] (definition).
 Mathematical meaning: Combined group sample weight for two finite data batches.
 Exact declaration: pooled_mass (n m:R) : R := n+m.
 Premises and side conditions: This scalar expression has a defined
 real value even at zero inputs, but probability/sample interpretations
 require the theorem-specific positive total sample-size hypotheses.
 Proof/definition method: Simple real arithmetic, not a new finite sum,
 covariance-matrix, random-variable or statistical test implementation.
 Library reuse: Stdlib Reals, Lra, Ring, Field and Psatz.
 Boundary: Deterministic batch-summary algebra, not a stochastic
 sampling theorem, empirical IQ variance or a Monte Carlo guarantee.
*)
Definition pooled_mass (n m:R) : R:=n+m.

(** [pooled_mean] (definition).
 Mathematical meaning: Combined arithmetic mean of groups with sizes n,m and means a,b.
 Exact declaration: pooled_mean (n m a b:R) : R := (n*a+m*b)/pooled_mass n m.
 Premises and side conditions: This scalar expression has a defined
 real value even at zero inputs, but probability/sample interpretations
 require the theorem-specific positive total sample-size hypotheses.
 Proof/definition method: Simple real arithmetic, not a new finite sum,
 covariance-matrix, random-variable or statistical test implementation.
 Library reuse: Stdlib Reals, Lra, Ring, Field and Psatz.
 Boundary: Deterministic batch-summary algebra, not a stochastic
 sampling theorem, empirical IQ variance or a Monte Carlo guarantee.
*)
Definition pooled_mean (n m a b:R) : R:=(n*a+m*b)/pooled_mass n m.

(** [pooled_between] (definition).
 Mathematical meaning: Exact between-group corrected sum of squares in pooled variance.
 Exact declaration: pooled_between (n m a b:R) : R := n*m*(a-b)*(a-b)/pooled_mass n m.
 Premises and side conditions: This scalar expression has a defined
 real value even at zero inputs, but probability/sample interpretations
 require the theorem-specific positive total sample-size hypotheses.
 Proof/definition method: Simple real arithmetic, not a new finite sum,
 covariance-matrix, random-variable or statistical test implementation.
 Library reuse: Stdlib Reals, Lra, Ring, Field and Psatz.
 Boundary: Deterministic batch-summary algebra, not a stochastic
 sampling theorem, empirical IQ variance or a Monte Carlo guarantee.
*)
Definition pooled_between (n m a b:R) : R:=n*m*(a-b)*(a-b)/pooled_mass n m.

(** [pooled_ss] (definition).
 Mathematical meaning: Full pooled centered sum of squares from within-group sums u,v.
 Exact declaration: pooled_ss (n m u v a b:R) : R := u+v+pooled_between n m a b.
 Premises and side conditions: This scalar expression has a defined
 real value even at zero inputs, but probability/sample interpretations
 require the theorem-specific positive total sample-size hypotheses.
 Proof/definition method: Simple real arithmetic, not a new finite sum,
 covariance-matrix, random-variable or statistical test implementation.
 Library reuse: Stdlib Reals, Lra, Ring, Field and Psatz.
 Boundary: Deterministic batch-summary algebra, not a stochastic
 sampling theorem, empirical IQ variance or a Monte Carlo guarantee.
*)
Definition pooled_ss (n m u v a b:R) : R:=u+v+pooled_between n m a b.

(** [pooled_unbiased_variance] (definition).
 Mathematical meaning: Pooled unbiased sample-variance formula, for a combined size over one.
 Exact declaration: pooled_unbiased_variance (n m u v a b:R) : R := pooled_ss n m u v a b/(pooled_mass n m-1).
 Premises and side conditions: This scalar expression has a defined
 real value even at zero inputs, but probability/sample interpretations
 require the theorem-specific positive total sample-size hypotheses.
 Proof/definition method: Simple real arithmetic, not a new finite sum,
 covariance-matrix, random-variable or statistical test implementation.
 Library reuse: Stdlib Reals, Lra, Ring, Field and Psatz.
 Boundary: Deterministic batch-summary algebra, not a stochastic
 sampling theorem, empirical IQ variance or a Monte Carlo guarantee.
*)
Definition pooled_unbiased_variance (n m u v a b:R) : R:=pooled_ss n m u v a b/(pooled_mass n m-1).

(** [pooled_mass_commutative] (theorem).
 Mathematical meaning: The total sample count is independent of batch order.
 Exact proposition: forall n m, pooled_mass n m=pooled_mass m n.
 Premises and side conditions: Positive group sizes and all nonzero
 denominator conditions are explicit. Within-group residual sums have
 nonnegative values only when stipulated; Gaussianity and independent
 sampling are never silently assumed as needed for real algebra.
 Proof/definition method: Reuse the corrected pooled-sum identities and
 Rocq Stdlib real Field, Ring, Lra, Psatz and inverse/order lemmas.
 Library reuse: Canonical numerical algebra rather than a new sum fold,
 a duplicate probability distribution, or a hand-written matrix engine.
 Boundary: Exact two-group ANOVA/variance identity as used in simulation
 appendices; does not prove a chi-square pivot or any empirical model.
*)
Theorem pooled_mass_commutative: forall n m, pooled_mass n m=pooled_mass m n.
Proof.
  intros; unfold pooled_mass; ring.
Qed.

(** [pooled_mass_positive] (theorem).
 Mathematical meaning: Two strictly positive group weights have a strictly positive combined mass.
 Exact proposition: forall n m, 0<n -> 0<m -> 0<pooled_mass n m.
 Premises and side conditions: Positive group sizes and all nonzero
 denominator conditions are explicit. Within-group residual sums have
 nonnegative values only when stipulated; Gaussianity and independent
 sampling are never silently assumed as needed for real algebra.
 Proof/definition method: Reuse the corrected pooled-sum identities and
 Rocq Stdlib real Field, Ring, Lra, Psatz and inverse/order lemmas.
 Library reuse: Canonical numerical algebra rather than a new sum fold,
 a duplicate probability distribution, or a hand-written matrix engine.
 Boundary: Exact two-group ANOVA/variance identity as used in simulation
 appendices; does not prove a chi-square pivot or any empirical model.
*)
Theorem pooled_mass_positive: forall n m, 0<n -> 0<m -> 0<pooled_mass n m.
Proof.
  intros n m Hn Hm; unfold pooled_mass; lra.
Qed.

(** [pooled_mean_swap] (theorem).
 Mathematical meaning: Swapping the two groups leaves their pooled mean unchanged.
 Exact proposition: forall n m a b, pooled_mean n m a b=pooled_mean m n b a.
 Premises and side conditions: Positive group sizes and all nonzero
 denominator conditions are explicit. Within-group residual sums have
 nonnegative values only when stipulated; Gaussianity and independent
 sampling are never silently assumed as needed for real algebra.
 Proof/definition method: Reuse the corrected pooled-sum identities and
 Rocq Stdlib real Field, Ring, Lra, Psatz and inverse/order lemmas.
 Library reuse: Canonical numerical algebra rather than a new sum fold,
 a duplicate probability distribution, or a hand-written matrix engine.
 Boundary: Exact two-group ANOVA/variance identity as used in simulation
 appendices; does not prove a chi-square pivot or any empirical model.
*)
Theorem pooled_mean_swap: forall n m a b, pooled_mean n m a b=pooled_mean m n b a.
Proof.
  intros n m a b; unfold pooled_mean,pooled_mass,Rdiv; replace (m+n) with (n+m) by ring; ring.
Qed.

(** [pooled_mean_constant] (theorem).
 Mathematical meaning: Pooling groups with identical means leaves the common mean unchanged.
 Exact proposition: forall n m a, 0<pooled_mass n m -> pooled_mean n m a a=a.
 Premises and side conditions: Positive group sizes and all nonzero
 denominator conditions are explicit. Within-group residual sums have
 nonnegative values only when stipulated; Gaussianity and independent
 sampling are never silently assumed as needed for real algebra.
 Proof/definition method: Reuse the corrected pooled-sum identities and
 Rocq Stdlib real Field, Ring, Lra, Psatz and inverse/order lemmas.
 Library reuse: Canonical numerical algebra rather than a new sum fold,
 a duplicate probability distribution, or a hand-written matrix engine.
 Boundary: Exact two-group ANOVA/variance identity as used in simulation
 appendices; does not prove a chi-square pivot or any empirical model.
*)
Theorem pooled_mean_constant: forall n m a, 0<pooled_mass n m -> pooled_mean n m a a=a.
Proof.
  intros n m a H; unfold pooled_mean,pooled_mass in *; field; lra.
Qed.

(** [pooled_mean_mass_identity] (theorem).
 Mathematical meaning: Multiplying pooled mean by combined sample size reconstructs the original weighted sum.
 Exact proposition: forall n m a b, 0<pooled_mass n m -> pooled_mass n m*pooled_mean n m a b=n*a+m*b.
 Premises and side conditions: Positive group sizes and all nonzero
 denominator conditions are explicit. Within-group residual sums have
 nonnegative values only when stipulated; Gaussianity and independent
 sampling are never silently assumed as needed for real algebra.
 Proof/definition method: Reuse the corrected pooled-sum identities and
 Rocq Stdlib real Field, Ring, Lra, Psatz and inverse/order lemmas.
 Library reuse: Canonical numerical algebra rather than a new sum fold,
 a duplicate probability distribution, or a hand-written matrix engine.
 Boundary: Exact two-group ANOVA/variance identity as used in simulation
 appendices; does not prove a chi-square pivot or any empirical model.
*)
Theorem pooled_mean_mass_identity: forall n m a b, 0<pooled_mass n m -> pooled_mass n m*pooled_mean n m a b=n*a+m*b.
Proof.
  intros n m a b H; unfold pooled_mean; field; lra.
Qed.

(** [pooled_mean_translation] (theorem).
 Mathematical meaning: Adding a common constant to both group means shifts pooled mean by exactly that constant.
 Exact proposition: forall n m a b c, 0<pooled_mass n m -> pooled_mean n m (a+c) (b+c)=pooled_mean n m a b+c.
 Premises and side conditions: Positive group sizes and all nonzero
 denominator conditions are explicit. Within-group residual sums have
 nonnegative values only when stipulated; Gaussianity and independent
 sampling are never silently assumed as needed for real algebra.
 Proof/definition method: Reuse the corrected pooled-sum identities and
 Rocq Stdlib real Field, Ring, Lra, Psatz and inverse/order lemmas.
 Library reuse: Canonical numerical algebra rather than a new sum fold,
 a duplicate probability distribution, or a hand-written matrix engine.
 Boundary: Exact two-group ANOVA/variance identity as used in simulation
 appendices; does not prove a chi-square pivot or any empirical model.
*)
Theorem pooled_mean_translation: forall n m a b c, 0<pooled_mass n m -> pooled_mean n m (a+c) (b+c)=pooled_mean n m a b+c.
Proof.
  intros n m a b c H; unfold pooled_mean,pooled_mass in *; field; lra.
Qed.

(** [pooled_mean_scale] (theorem).
 Mathematical meaning: Multiplying both group means by a common scalar scales their pooled mean by that scalar.
 Exact proposition: forall n m a b t, 0<pooled_mass n m -> pooled_mean n m (t*a) (t*b)=t*pooled_mean n m a b.
 Premises and side conditions: Positive group sizes and all nonzero
 denominator conditions are explicit. Within-group residual sums have
 nonnegative values only when stipulated; Gaussianity and independent
 sampling are never silently assumed as needed for real algebra.
 Proof/definition method: Reuse the corrected pooled-sum identities and
 Rocq Stdlib real Field, Ring, Lra, Psatz and inverse/order lemmas.
 Library reuse: Canonical numerical algebra rather than a new sum fold,
 a duplicate probability distribution, or a hand-written matrix engine.
 Boundary: Exact two-group ANOVA/variance identity as used in simulation
 appendices; does not prove a chi-square pivot or any empirical model.
*)
Theorem pooled_mean_scale: forall n m a b t, 0<pooled_mass n m -> pooled_mean n m (t*a) (t*b)=t*pooled_mean n m a b.
Proof.
  intros n m a b t H; unfold pooled_mean,pooled_mass in *; field; lra.
Qed.

(** [pooled_mean_left_shift] (theorem).
 Mathematical meaning: The pooled mean's displacement from the first group mean is the second group's weighted difference.
 Exact proposition: forall n m a b, 0<pooled_mass n m -> pooled_mean n m a b-a=m*(b-a)/pooled_mass n m.
 Premises and side conditions: Positive group sizes and all nonzero
 denominator conditions are explicit. Within-group residual sums have
 nonnegative values only when stipulated; Gaussianity and independent
 sampling are never silently assumed as needed for real algebra.
 Proof/definition method: Reuse the corrected pooled-sum identities and
 Rocq Stdlib real Field, Ring, Lra, Psatz and inverse/order lemmas.
 Library reuse: Canonical numerical algebra rather than a new sum fold,
 a duplicate probability distribution, or a hand-written matrix engine.
 Boundary: Exact two-group ANOVA/variance identity as used in simulation
 appendices; does not prove a chi-square pivot or any empirical model.
*)
Theorem pooled_mean_left_shift: forall n m a b, 0<pooled_mass n m -> pooled_mean n m a b-a=m*(b-a)/pooled_mass n m.
Proof.
  intros n m a b H; unfold pooled_mean,pooled_mass in *; field; lra.
Qed.

(** [pooled_mean_right_shift] (theorem).
 Mathematical meaning: The pooled mean's displacement from the second group mean is the first group's weighted difference.
 Exact proposition: forall n m a b, 0<pooled_mass n m -> pooled_mean n m a b-b=n*(a-b)/pooled_mass n m.
 Premises and side conditions: Positive group sizes and all nonzero
 denominator conditions are explicit. Within-group residual sums have
 nonnegative values only when stipulated; Gaussianity and independent
 sampling are never silently assumed as needed for real algebra.
 Proof/definition method: Reuse the corrected pooled-sum identities and
 Rocq Stdlib real Field, Ring, Lra, Psatz and inverse/order lemmas.
 Library reuse: Canonical numerical algebra rather than a new sum fold,
 a duplicate probability distribution, or a hand-written matrix engine.
 Boundary: Exact two-group ANOVA/variance identity as used in simulation
 appendices; does not prove a chi-square pivot or any empirical model.
*)
Theorem pooled_mean_right_shift: forall n m a b, 0<pooled_mass n m -> pooled_mean n m a b-b=n*(a-b)/pooled_mass n m.
Proof.
  intros n m a b H; unfold pooled_mean,pooled_mass in *; field; lra.
Qed.

(** [pooled_mean_centered_mass_zero] (theorem).
 Mathematical meaning: Centered deviations of both group means cancel after weighting by their respective sample sizes.
 Exact proposition: forall n m a b, 0<pooled_mass n m -> n*(a-pooled_mean n m a b)+m*(b-pooled_mean n m a b)=0.
 Premises and side conditions: Positive group sizes and all nonzero
 denominator conditions are explicit. Within-group residual sums have
 nonnegative values only when stipulated; Gaussianity and independent
 sampling are never silently assumed as needed for real algebra.
 Proof/definition method: Reuse the corrected pooled-sum identities and
 Rocq Stdlib real Field, Ring, Lra, Psatz and inverse/order lemmas.
 Library reuse: Canonical numerical algebra rather than a new sum fold,
 a duplicate probability distribution, or a hand-written matrix engine.
 Boundary: Exact two-group ANOVA/variance identity as used in simulation
 appendices; does not prove a chi-square pivot or any empirical model.
*)
Theorem pooled_mean_centered_mass_zero: forall n m a b, 0<pooled_mass n m -> n*(a-pooled_mean n m a b)+m*(b-pooled_mean n m a b)=0.
Proof.
  intros n m a b H; pose proof (pooled_mean_mass_identity n m a b H); unfold pooled_mass in *; nra.
Qed.

(** [pooled_mean_between_bounds] (theorem).
 Mathematical meaning: For nonnegative group sizes, a pooled mean lies between two ordered component means.
 Exact proposition: forall n m a b, 0<n -> 0<m -> a<=b -> a<=pooled_mean n m a b<=b.
 Premises and side conditions: Positive group sizes and all nonzero
 denominator conditions are explicit. Within-group residual sums have
 nonnegative values only when stipulated; Gaussianity and independent
 sampling are never silently assumed as needed for real algebra.
 Proof/definition method: Reuse the corrected pooled-sum identities and
 Rocq Stdlib real Field, Ring, Lra, Psatz and inverse/order lemmas.
 Library reuse: Canonical numerical algebra rather than a new sum fold,
 a duplicate probability distribution, or a hand-written matrix engine.
 Boundary: Exact two-group ANOVA/variance identity as used in simulation
 appendices; does not prove a chi-square pivot or any empirical model.
*)
Theorem pooled_mean_between_bounds: forall n m a b, 0<n -> 0<m -> a<=b -> a<=pooled_mean n m a b<=b.
Proof.
  intros n m a b Hn Hm Hab. assert (Hmass:0<pooled_mass n m) by (apply pooled_mass_positive; assumption). pose proof (pooled_mean_mass_identity n m a b Hmass) as Hidentity. unfold pooled_mass in *; split; nra.
Qed.

(** [pooled_mean_strict_between] (theorem).
 Mathematical meaning: When both groups are present and their means differ, the pooled mean lies strictly between them.
 Exact proposition: forall n m a b, 0<n -> 0<m -> a<b -> a<pooled_mean n m a b<b.
 Premises and side conditions: Positive group sizes and all nonzero
 denominator conditions are explicit. Within-group residual sums have
 nonnegative values only when stipulated; Gaussianity and independent
 sampling are never silently assumed as needed for real algebra.
 Proof/definition method: Reuse the corrected pooled-sum identities and
 Rocq Stdlib real Field, Ring, Lra, Psatz and inverse/order lemmas.
 Library reuse: Canonical numerical algebra rather than a new sum fold,
 a duplicate probability distribution, or a hand-written matrix engine.
 Boundary: Exact two-group ANOVA/variance identity as used in simulation
 appendices; does not prove a chi-square pivot or any empirical model.
*)
Theorem pooled_mean_strict_between: forall n m a b, 0<n -> 0<m -> a<b -> a<pooled_mean n m a b<b.
Proof.
  intros n m a b Hn Hm Hab. assert (Hmass:0<pooled_mass n m) by (apply pooled_mass_positive; assumption). pose proof (pooled_mean_mass_identity n m a b Hmass) as Hidentity. unfold pooled_mass in *; split; nra.
Qed.

(** [pooled_mean_three_group_formula] (theorem).
 Mathematical meaning: Merging the first two groups and then a third reproduces the exact three-group weighted mean.
 Exact proposition: forall n m k a b c, 0<n -> 0<m -> 0<k -> pooled_mean (n+m) k (pooled_mean n m a b) c=(n*a+m*b+k*c)/(n+m+k).
 Premises and side conditions: Positive group sizes and all nonzero
 denominator conditions are explicit. Within-group residual sums have
 nonnegative values only when stipulated; Gaussianity and independent
 sampling are never silently assumed as needed for real algebra.
 Proof/definition method: Reuse the corrected pooled-sum identities and
 Rocq Stdlib real Field, Ring, Lra, Psatz and inverse/order lemmas.
 Library reuse: Canonical numerical algebra rather than a new sum fold,
 a duplicate probability distribution, or a hand-written matrix engine.
 Boundary: Exact two-group ANOVA/variance identity as used in simulation
 appendices; does not prove a chi-square pivot or any empirical model.
*)
Theorem pooled_mean_three_group_formula: forall n m k a b c, 0<n -> 0<m -> 0<k -> pooled_mean (n+m) k (pooled_mean n m a b) c=(n*a+m*b+k*c)/(n+m+k).
Proof.
  intros n m k a b c Hn Hm Hk; unfold pooled_mean,pooled_mass; field; nra.
Qed.

(** [pooled_mean_associative] (theorem).
 Mathematical meaning: The pooled mean does not depend on which adjacent pair of positive-size groups is merged first.
 Exact proposition: forall n m k a b c, 0<n -> 0<m -> 0<k -> pooled_mean (n+m) k (pooled_mean n m a b) c = pooled_mean n (m+k) a (pooled_mean m k b c).
 Premises and side conditions: Positive group sizes and all nonzero
 denominator conditions are explicit. Within-group residual sums have
 nonnegative values only when stipulated; Gaussianity and independent
 sampling are never silently assumed as needed for real algebra.
 Proof/definition method: Reuse the corrected pooled-sum identities and
 Rocq Stdlib real Field, Ring, Lra, Psatz and inverse/order lemmas.
 Library reuse: Canonical numerical algebra rather than a new sum fold,
 a duplicate probability distribution, or a hand-written matrix engine.
 Boundary: Exact two-group ANOVA/variance identity as used in simulation
 appendices; does not prove a chi-square pivot or any empirical model.
*)
Theorem pooled_mean_associative: forall n m k a b c, 0<n -> 0<m -> 0<k -> pooled_mean (n+m) k (pooled_mean n m a b) c = pooled_mean n (m+k) a (pooled_mean m k b c).
Proof.
  intros n m k a b c Hn Hm Hk; unfold pooled_mean,pooled_mass; field; nra.
Qed.

(** [pooled_between_swap] (theorem).
 Mathematical meaning: The between-group sum of squares is invariant under swapping batches.
 Exact proposition: forall n m a b, pooled_between n m a b=pooled_between m n b a.
 Premises and side conditions: Positive group sizes and all nonzero
 denominator conditions are explicit. Within-group residual sums have
 nonnegative values only when stipulated; Gaussianity and independent
 sampling are never silently assumed as needed for real algebra.
 Proof/definition method: Reuse the corrected pooled-sum identities and
 Rocq Stdlib real Field, Ring, Lra, Psatz and inverse/order lemmas.
 Library reuse: Canonical numerical algebra rather than a new sum fold,
 a duplicate probability distribution, or a hand-written matrix engine.
 Boundary: Exact two-group ANOVA/variance identity as used in simulation
 appendices; does not prove a chi-square pivot or any empirical model.
*)
Theorem pooled_between_swap: forall n m a b, pooled_between n m a b=pooled_between m n b a.
Proof.
  intros n m a b; unfold pooled_between,pooled_mass,Rdiv; replace (m+n) with (n+m) by ring; ring.
Qed.

(** [pooled_between_constant_means] (theorem).
 Mathematical meaning: Groups with the same mean contribute no between-group sum of squares.
 Exact proposition: forall n m a, pooled_between n m a a=0.
 Premises and side conditions: Positive group sizes and all nonzero
 denominator conditions are explicit. Within-group residual sums have
 nonnegative values only when stipulated; Gaussianity and independent
 sampling are never silently assumed as needed for real algebra.
 Proof/definition method: Reuse the corrected pooled-sum identities and
 Rocq Stdlib real Field, Ring, Lra, Psatz and inverse/order lemmas.
 Library reuse: Canonical numerical algebra rather than a new sum fold,
 a duplicate probability distribution, or a hand-written matrix engine.
 Boundary: Exact two-group ANOVA/variance identity as used in simulation
 appendices; does not prove a chi-square pivot or any empirical model.
*)
Theorem pooled_between_constant_means: forall n m a, pooled_between n m a a=0.
Proof.
  intros; unfold pooled_between,pooled_mass,Rdiv; ring.
Qed.

(** [pooled_between_translation] (theorem).
 Mathematical meaning: Common translation of both group means leaves the between-group variability invariant.
 Exact proposition: forall n m a b c, pooled_between n m (a+c) (b+c)=pooled_between n m a b.
 Premises and side conditions: Positive group sizes and all nonzero
 denominator conditions are explicit. Within-group residual sums have
 nonnegative values only when stipulated; Gaussianity and independent
 sampling are never silently assumed as needed for real algebra.
 Proof/definition method: Reuse the corrected pooled-sum identities and
 Rocq Stdlib real Field, Ring, Lra, Psatz and inverse/order lemmas.
 Library reuse: Canonical numerical algebra rather than a new sum fold,
 a duplicate probability distribution, or a hand-written matrix engine.
 Boundary: Exact two-group ANOVA/variance identity as used in simulation
 appendices; does not prove a chi-square pivot or any empirical model.
*)
Theorem pooled_between_translation: forall n m a b c, pooled_between n m (a+c) (b+c)=pooled_between n m a b.
Proof.
  intros; unfold pooled_between,pooled_mass,Rdiv; ring.
Qed.

(** [pooled_between_scale] (theorem).
 Mathematical meaning: The between-group sum of squares scales quadratically with the measurement unit.
 Exact proposition: forall n m a b t, pooled_between n m (t*a) (t*b)=t*t*pooled_between n m a b.
 Premises and side conditions: Positive group sizes and all nonzero
 denominator conditions are explicit. Within-group residual sums have
 nonnegative values only when stipulated; Gaussianity and independent
 sampling are never silently assumed as needed for real algebra.
 Proof/definition method: Reuse the corrected pooled-sum identities and
 Rocq Stdlib real Field, Ring, Lra, Psatz and inverse/order lemmas.
 Library reuse: Canonical numerical algebra rather than a new sum fold,
 a duplicate probability distribution, or a hand-written matrix engine.
 Boundary: Exact two-group ANOVA/variance identity as used in simulation
 appendices; does not prove a chi-square pivot or any empirical model.
*)
Theorem pooled_between_scale: forall n m a b t, pooled_between n m (t*a) (t*b)=t*t*pooled_between n m a b.
Proof.
  intros; unfold pooled_between,pooled_mass,Rdiv; ring.
Qed.

(** [pooled_between_nonnegative] (theorem).
 Mathematical meaning: With positive group counts, the between-group corrected sum of squares is nonnegative.
 Exact proposition: forall n m a b, 0<n -> 0<m -> 0<=pooled_between n m a b.
 Premises and side conditions: Positive group sizes and all nonzero
 denominator conditions are explicit. Within-group residual sums have
 nonnegative values only when stipulated; Gaussianity and independent
 sampling are never silently assumed as needed for real algebra.
 Proof/definition method: Reuse the corrected pooled-sum identities and
 Rocq Stdlib real Field, Ring, Lra, Psatz and inverse/order lemmas.
 Library reuse: Canonical numerical algebra rather than a new sum fold,
 a duplicate probability distribution, or a hand-written matrix engine.
 Boundary: Exact two-group ANOVA/variance identity as used in simulation
 appendices; does not prove a chi-square pivot or any empirical model.
*)
Theorem pooled_between_nonnegative: forall n m a b, 0<n -> 0<m -> 0<=pooled_between n m a b.
Proof.
  intros n m a b Hn Hm. unfold pooled_between,Rdiv. assert (Hs:0<=(a-b)*(a-b)) by nra. assert (Hnm:0<=n*m) by nra. assert (Hnum:0<=n*m*((a-b)*(a-b))) by (apply Rmult_le_pos; assumption). assert (Hinv:0</pooled_mass n m) by (apply Rinv_0_lt_compat; apply pooled_mass_positive; assumption). nra.
Qed.

(** [pooled_between_positive_ordered] (theorem).
 Mathematical meaning: Two positive-size groups with different ordered means produce strictly positive between-group variation.
 Exact proposition: forall n m a b, 0<n -> 0<m -> a<b -> 0<pooled_between n m a b.
 Premises and side conditions: Positive group sizes and all nonzero
 denominator conditions are explicit. Within-group residual sums have
 nonnegative values only when stipulated; Gaussianity and independent
 sampling are never silently assumed as needed for real algebra.
 Proof/definition method: Reuse the corrected pooled-sum identities and
 Rocq Stdlib real Field, Ring, Lra, Psatz and inverse/order lemmas.
 Library reuse: Canonical numerical algebra rather than a new sum fold,
 a duplicate probability distribution, or a hand-written matrix engine.
 Boundary: Exact two-group ANOVA/variance identity as used in simulation
 appendices; does not prove a chi-square pivot or any empirical model.
*)
Theorem pooled_between_positive_ordered: forall n m a b, 0<n -> 0<m -> a<b -> 0<pooled_between n m a b.
Proof.
  intros n m a b Hn Hm Hab. unfold pooled_between,Rdiv. assert (Hs:0<(a-b)*(a-b)) by nra. assert (Hnm:0<n*m) by nra. assert (Hnum:0<n*m*((a-b)*(a-b))) by (apply Rmult_lt_0_compat; assumption). assert (Hinv:0</pooled_mass n m) by (apply Rinv_0_lt_compat; apply pooled_mass_positive; assumption). nra.
Qed.

(** [pooled_between_centered_identity] (theorem).
 Mathematical meaning: The between-group correction equals the two centered weighted squared deviations from the pooled mean.
 Exact proposition: forall n m a b, 0<n -> 0<m -> n*(a-pooled_mean n m a b)*(a-pooled_mean n m a b)+m*(b-pooled_mean n m a b)*(b-pooled_mean n m a b)=pooled_between n m a b.
 Premises and side conditions: Positive group sizes and all nonzero
 denominator conditions are explicit. Within-group residual sums have
 nonnegative values only when stipulated; Gaussianity and independent
 sampling are never silently assumed as needed for real algebra.
 Proof/definition method: Reuse the corrected pooled-sum identities and
 Rocq Stdlib real Field, Ring, Lra, Psatz and inverse/order lemmas.
 Library reuse: Canonical numerical algebra rather than a new sum fold,
 a duplicate probability distribution, or a hand-written matrix engine.
 Boundary: Exact two-group ANOVA/variance identity as used in simulation
 appendices; does not prove a chi-square pivot or any empirical model.
*)
Theorem pooled_between_centered_identity: forall n m a b, 0<n -> 0<m -> n*(a-pooled_mean n m a b)*(a-pooled_mean n m a b)+m*(b-pooled_mean n m a b)*(b-pooled_mean n m a b)=pooled_between n m a b.
Proof.
  intros n m a b Hn Hm. unfold pooled_between,pooled_mean,pooled_mass; field; nra.
Qed.

(** [pooled_between_raw_second_moment] (theorem).
 Mathematical meaning: The between-group correction is raw weighted second moment minus the squared weighted grand mean.
 Exact proposition: forall n m a b, 0<n -> 0<m -> n*a*a+m*b*b-pooled_mass n m*pooled_mean n m a b*pooled_mean n m a b =pooled_between n m a b.
 Premises and side conditions: Positive group sizes and all nonzero
 denominator conditions are explicit. Within-group residual sums have
 nonnegative values only when stipulated; Gaussianity and independent
 sampling are never silently assumed as needed for real algebra.
 Proof/definition method: Reuse the corrected pooled-sum identities and
 Rocq Stdlib real Field, Ring, Lra, Psatz and inverse/order lemmas.
 Library reuse: Canonical numerical algebra rather than a new sum fold,
 a duplicate probability distribution, or a hand-written matrix engine.
 Boundary: Exact two-group ANOVA/variance identity as used in simulation
 appendices; does not prove a chi-square pivot or any empirical model.
*)
Theorem pooled_between_raw_second_moment: forall n m a b, 0<n -> 0<m -> n*a*a+m*b*b-pooled_mass n m*pooled_mean n m a b*pooled_mean n m a b =pooled_between n m a b.
Proof.
  intros n m a b Hn Hm; unfold pooled_between,pooled_mean,pooled_mass; field; nra.
Qed.

(** [pooled_between_upper_bound] (theorem).
 Mathematical meaning: The between-group correction is at most one quarter of total sample size times squared mean difference.
 Exact proposition: forall n m a b, 0<n -> 0<m -> pooled_between n m a b<=pooled_mass n m*(a-b)*(a-b)/4.
 Premises and side conditions: Positive group sizes and all nonzero
 denominator conditions are explicit. Within-group residual sums have
 nonnegative values only when stipulated; Gaussianity and independent
 sampling are never silently assumed as needed for real algebra.
 Proof/definition method: Reuse the corrected pooled-sum identities and
 Rocq Stdlib real Field, Ring, Lra, Psatz and inverse/order lemmas.
 Library reuse: Canonical numerical algebra rather than a new sum fold,
 a duplicate probability distribution, or a hand-written matrix engine.
 Boundary: Exact two-group ANOVA/variance identity as used in simulation
 appendices; does not prove a chi-square pivot or any empirical model.
*)
Theorem pooled_between_upper_bound: forall n m a b, 0<n -> 0<m -> pooled_between n m a b<=pooled_mass n m*(a-b)*(a-b)/4.
Proof.
  intros n m a b Hn Hm. assert (Hd:0<pooled_mass n m) by (apply pooled_mass_positive; assumption). unfold pooled_between,pooled_mass,Rdiv in *. assert (Hsq:0<=(a-b)*(a-b)) by nra. assert (Hnm:4*n*m <= (n+m)*(n+m)) by nra. assert (Hin:0</(n+m)) by (apply Rinv_0_lt_compat; lra). assert (Hfactor:0<=((n+m)*(n+m)-4*n*m)*((a-b)*(a-b))) by (apply Rmult_le_pos; nra). nra.
Qed.

(** [pooled_ss_above_within] (theorem).
 Mathematical meaning: The total sum of squares is at least the sum of the within-group centered sums when group counts are positive.
 Exact proposition: forall n m u v a b, 0<n -> 0<m -> u+v<=pooled_ss n m u v a b.
 Premises and side conditions: Positive group sizes and all nonzero
 denominator conditions are explicit. Within-group residual sums have
 nonnegative values only when stipulated; Gaussianity and independent
 sampling are never silently assumed as needed for real algebra.
 Proof/definition method: Reuse the corrected pooled-sum identities and
 Rocq Stdlib real Field, Ring, Lra, Psatz and inverse/order lemmas.
 Library reuse: Canonical numerical algebra rather than a new sum fold,
 a duplicate probability distribution, or a hand-written matrix engine.
 Boundary: Exact two-group ANOVA/variance identity as used in simulation
 appendices; does not prove a chi-square pivot or any empirical model.
*)
Theorem pooled_ss_above_within: forall n m u v a b, 0<n -> 0<m -> u+v<=pooled_ss n m u v a b.
Proof.
  intros n m u v a b Hn Hm. unfold pooled_ss. pose proof (pooled_between_nonnegative n m a b Hn Hm). lra.
Qed.

(** [pooled_ss_nonnegative] (theorem).
 Mathematical meaning: Nonnegative within-group sums and positive group sizes yield a nonnegative total centered sum of squares.
 Exact proposition: forall n m u v a b, 0<n -> 0<m -> 0<=u -> 0<=v -> 0<=pooled_ss n m u v a b.
 Premises and side conditions: Positive group sizes and all nonzero
 denominator conditions are explicit. Within-group residual sums have
 nonnegative values only when stipulated; Gaussianity and independent
 sampling are never silently assumed as needed for real algebra.
 Proof/definition method: Reuse the corrected pooled-sum identities and
 Rocq Stdlib real Field, Ring, Lra, Psatz and inverse/order lemmas.
 Library reuse: Canonical numerical algebra rather than a new sum fold,
 a duplicate probability distribution, or a hand-written matrix engine.
 Boundary: Exact two-group ANOVA/variance identity as used in simulation
 appendices; does not prove a chi-square pivot or any empirical model.
*)
Theorem pooled_ss_nonnegative: forall n m u v a b, 0<n -> 0<m -> 0<=u -> 0<=v -> 0<=pooled_ss n m u v a b.
Proof.
  intros n m u v a b Hn Hm Hu Hv; unfold pooled_ss; pose proof (pooled_between_nonnegative n m a b Hn Hm); lra.
Qed.

(** [pooled_ss_translation] (theorem).
 Mathematical meaning: The corrected pooled sum of squares is translation-invariant in the group means.
 Exact proposition: forall n m u v a b c, pooled_ss n m u v (a+c) (b+c)=pooled_ss n m u v a b.
 Premises and side conditions: Positive group sizes and all nonzero
 denominator conditions are explicit. Within-group residual sums have
 nonnegative values only when stipulated; Gaussianity and independent
 sampling are never silently assumed as needed for real algebra.
 Proof/definition method: Reuse the corrected pooled-sum identities and
 Rocq Stdlib real Field, Ring, Lra, Psatz and inverse/order lemmas.
 Library reuse: Canonical numerical algebra rather than a new sum fold,
 a duplicate probability distribution, or a hand-written matrix engine.
 Boundary: Exact two-group ANOVA/variance identity as used in simulation
 appendices; does not prove a chi-square pivot or any empirical model.
*)
Theorem pooled_ss_translation: forall n m u v a b c, pooled_ss n m u v (a+c) (b+c)=pooled_ss n m u v a b.
Proof.
  intros; unfold pooled_ss; rewrite pooled_between_translation; reflexivity.
Qed.

(** [pooled_ss_within_additivity] (theorem).
 Mathematical meaning: Increasing either group's centered sum of squares increases the pooled total by exactly that increment.
 Exact proposition: forall n m u v a b d, pooled_ss n m (u+d) v a b = pooled_ss n m u v a b+d.
 Premises and side conditions: Positive group sizes and all nonzero
 denominator conditions are explicit. Within-group residual sums have
 nonnegative values only when stipulated; Gaussianity and independent
 sampling are never silently assumed as needed for real algebra.
 Proof/definition method: Reuse the corrected pooled-sum identities and
 Rocq Stdlib real Field, Ring, Lra, Psatz and inverse/order lemmas.
 Library reuse: Canonical numerical algebra rather than a new sum fold,
 a duplicate probability distribution, or a hand-written matrix engine.
 Boundary: Exact two-group ANOVA/variance identity as used in simulation
 appendices; does not prove a chi-square pivot or any empirical model.
*)
Theorem pooled_ss_within_additivity: forall n m u v a b d, pooled_ss n m (u+d) v a b = pooled_ss n m u v a b+d.
Proof.
  intros; unfold pooled_ss; ring.
Qed.

(** [pooled_variance_denominator_identity] (theorem).
 Mathematical meaning: The pooled sample variance multiplied by its degrees of freedom exactly reconstructs the pooled sum of squares.
 Exact proposition: forall n m u v a b, 1<pooled_mass n m -> (pooled_mass n m-1)*pooled_unbiased_variance n m u v a b = pooled_ss n m u v a b.
 Premises and side conditions: Positive group sizes and all nonzero
 denominator conditions are explicit. Within-group residual sums have
 nonnegative values only when stipulated; Gaussianity and independent
 sampling are never silently assumed as needed for real algebra.
 Proof/definition method: Reuse the corrected pooled-sum identities and
 Rocq Stdlib real Field, Ring, Lra, Psatz and inverse/order lemmas.
 Library reuse: Canonical numerical algebra rather than a new sum fold,
 a duplicate probability distribution, or a hand-written matrix engine.
 Boundary: Exact two-group ANOVA/variance identity as used in simulation
 appendices; does not prove a chi-square pivot or any empirical model.
*)
Theorem pooled_variance_denominator_identity: forall n m u v a b, 1<pooled_mass n m -> (pooled_mass n m-1)*pooled_unbiased_variance n m u v a b = pooled_ss n m u v a b.
Proof.
  intros n m u v a b H. unfold pooled_unbiased_variance; field; lra.
Qed.

(** [pooled_variance_nonnegative] (theorem).
 Mathematical meaning: A combined battery of more than one observation with nonnegative within sums has nonnegative pooled variance.
 Exact proposition: forall n m u v a b, 0<n -> 0<m -> 1<pooled_mass n m -> 0<=u -> 0<=v -> 0<=pooled_unbiased_variance n m u v a b.
 Premises and side conditions: Positive group sizes and all nonzero
 denominator conditions are explicit. Within-group residual sums have
 nonnegative values only when stipulated; Gaussianity and independent
 sampling are never silently assumed as needed for real algebra.
 Proof/definition method: Reuse the corrected pooled-sum identities and
 Rocq Stdlib real Field, Ring, Lra, Psatz and inverse/order lemmas.
 Library reuse: Canonical numerical algebra rather than a new sum fold,
 a duplicate probability distribution, or a hand-written matrix engine.
 Boundary: Exact two-group ANOVA/variance identity as used in simulation
 appendices; does not prove a chi-square pivot or any empirical model.
*)
Theorem pooled_variance_nonnegative: forall n m u v a b, 0<n -> 0<m -> 1<pooled_mass n m -> 0<=u -> 0<=v -> 0<=pooled_unbiased_variance n m u v a b.
Proof.
  intros n m u v a b Hn Hm Htotal Hu Hv. unfold pooled_unbiased_variance,Rdiv. apply Rmult_le_pos. - apply pooled_ss_nonnegative; assumption. - left; apply Rinv_0_lt_compat; lra.
Qed.

(** [pooled_variance_increases_with_within] (theorem).
 Mathematical meaning: For fixed sample sizes and group means, increasing the within-group squared residual sum increases pooled sample variance.
 Exact proposition: forall n m u v u' a b, 1<pooled_mass n m -> u<=u' -> pooled_unbiased_variance n m u v a b<=pooled_unbiased_variance n m u' v a b.
 Premises and side conditions: Positive group sizes and all nonzero
 denominator conditions are explicit. Within-group residual sums have
 nonnegative values only when stipulated; Gaussianity and independent
 sampling are never silently assumed as needed for real algebra.
 Proof/definition method: Reuse the corrected pooled-sum identities and
 Rocq Stdlib real Field, Ring, Lra, Psatz and inverse/order lemmas.
 Library reuse: Canonical numerical algebra rather than a new sum fold,
 a duplicate probability distribution, or a hand-written matrix engine.
 Boundary: Exact two-group ANOVA/variance identity as used in simulation
 appendices; does not prove a chi-square pivot or any empirical model.
*)
Theorem pooled_variance_increases_with_within: forall n m u v u' a b, 1<pooled_mass n m -> u<=u' -> pooled_unbiased_variance n m u v a b<=pooled_unbiased_variance n m u' v a b.
Proof.
  intros n m u v u' a b Hmass Hu. unfold pooled_unbiased_variance,pooled_ss,Rdiv. assert (Hi:0</(pooled_mass n m-1)) by (apply Rinv_0_lt_compat; lra). nra.
Qed.

(** [pooled_variance_two_batch_formula] (theorem).
 Mathematical meaning: The explicit two-batch unbiased variance is within-sum plus between correction divided by total degrees of freedom.
 Exact proposition: forall n m u v a b, 0<n -> 0<m -> 1<pooled_mass n m -> pooled_unbiased_variance n m u v a b = (u+v+n*m*(a-b)*(a-b)/(n+m))/(n+m-1).
 Premises and side conditions: Positive group sizes and all nonzero
 denominator conditions are explicit. Within-group residual sums have
 nonnegative values only when stipulated; Gaussianity and independent
 sampling are never silently assumed as needed for real algebra.
 Proof/definition method: Reuse the corrected pooled-sum identities and
 Rocq Stdlib real Field, Ring, Lra, Psatz and inverse/order lemmas.
 Library reuse: Canonical numerical algebra rather than a new sum fold,
 a duplicate probability distribution, or a hand-written matrix engine.
 Boundary: Exact two-group ANOVA/variance identity as used in simulation
 appendices; does not prove a chi-square pivot or any empirical model.
*)
Theorem pooled_variance_two_batch_formula: forall n m u v a b, 0<n -> 0<m -> 1<pooled_mass n m -> pooled_unbiased_variance n m u v a b = (u+v+n*m*(a-b)*(a-b)/(n+m))/(n+m-1).
Proof.
  intros n m u v a b Hn Hm Ht; unfold pooled_unbiased_variance,pooled_ss,pooled_between,pooled_mass; reflexivity.
Qed.

