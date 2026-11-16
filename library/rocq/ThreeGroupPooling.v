(** Module: ThreeGroupPooling.v
 Purpose: Extend the six-report simulation appendix's two-group sample variance
 decomposition to genuine three-batch weighted moments, mean and centered SS.
 Mathematical representation: Real replicate sizes n,m,k with means a,b,c
 and within-batch corrected SS u,v,w; pooled center and dispersion are
 explicitly defined using the established real arithmetic operations.
 Explicit hypotheses: Positivity of counts and variance denominators is
 explicit in each mathematical claim; zero-count handling is not elided.
 Library use: Rocq Stdlib Reals, Lra, Psatz, Ring, Field and existing
 PooledMomentsAlgebra.v for canonical two-batch identities; no new sums.
 Limitations: Deterministic exact sample-moment identities only; no
 chi-square pivot, Gaussian draw independence, or empirical model validation.
 Reproduction: Run scripts/compile_rocq.sh with pinned Rocq 9.2.
 AI disclosure: AI assisted the proof construction and comments. Only
 kernel checking of the exact final source establishes theorem correctness.
*)
From Stdlib Require Import Reals Lra Psatz Ring Field.
Require Import PooledMomentsAlgebra.
Open Scope R_scope.
(** [three_mass] (definition).
 Mathematical meaning: The combined real sample weight of all three groups.
 Exact definition: This is a transparent real expression in subgroup summaries.
 Premises and side conditions: Statistical interpretation requires positive
 subgroup counts; the total function itself makes no distributional claim.
 Proof/definition method: Reuse real arithmetic and a small explicit
 weighted formula rather than implementing a new recursive sum.
 Library reuse: Stdlib Reals and canonical PooledMomentsAlgebra.
 Boundary: This is deterministic scalar algebra and not sampling theory.
*)
Definition three_mass (n m k:R) : R := n+m+k.
(** [three_numerator] (definition).
 Mathematical meaning: The aggregate weighted sum of three group mean scores.
 Exact definition: This is a transparent real expression in subgroup summaries.
 Premises and side conditions: Statistical interpretation requires positive
 subgroup counts; the total function itself makes no distributional claim.
 Proof/definition method: Reuse real arithmetic and a small explicit
 weighted formula rather than implementing a new recursive sum.
 Library reuse: Stdlib Reals and canonical PooledMomentsAlgebra.
 Boundary: This is deterministic scalar algebra and not sampling theory.
*)
Definition three_numerator (n m k a b c:R) : R := n*a+m*b+k*c.
(** [three_mean] (definition).
 Mathematical meaning: The sample-size-weighted mean of the three groups.
 Exact definition: This is a transparent real expression in subgroup summaries.
 Premises and side conditions: Statistical interpretation requires positive
 subgroup counts; the total function itself makes no distributional claim.
 Proof/definition method: Reuse real arithmetic and a small explicit
 weighted formula rather than implementing a new recursive sum.
 Library reuse: Stdlib Reals and canonical PooledMomentsAlgebra.
 Boundary: This is deterministic scalar algebra and not sampling theory.
*)
Definition three_mean (n m k a b c:R) : R := three_numerator n m k a b c / three_mass n m k.
(** [three_raw_second] (definition).
 Mathematical meaning: The aggregate weighted uncentered second moment of group means.
 Exact definition: This is a transparent real expression in subgroup summaries.
 Premises and side conditions: Statistical interpretation requires positive
 subgroup counts; the total function itself makes no distributional claim.
 Proof/definition method: Reuse real arithmetic and a small explicit
 weighted formula rather than implementing a new recursive sum.
 Library reuse: Stdlib Reals and canonical PooledMomentsAlgebra.
 Boundary: This is deterministic scalar algebra and not sampling theory.
*)
Definition three_raw_second (n m k a b c:R) : R := n*a*a+m*b*b+k*c*c.
(** [three_dispersion] (definition).
 Mathematical meaning: The between-replicate centered sum of squares around the pooled mean.
 Exact definition: This is a transparent real expression in subgroup summaries.
 Premises and side conditions: Statistical interpretation requires positive
 subgroup counts; the total function itself makes no distributional claim.
 Proof/definition method: Reuse real arithmetic and a small explicit
 weighted formula rather than implementing a new recursive sum.
 Library reuse: Stdlib Reals and canonical PooledMomentsAlgebra.
 Boundary: This is deterministic scalar algebra and not sampling theory.
*)
Definition three_dispersion (n m k a b c:R) : R :=
  let t := three_mean n m k a b c in
  n*(a-t)*(a-t)+m*(b-t)*(b-t)+k*(c-t)*(c-t).
(** [three_ss] (definition).
 Mathematical meaning: The pooled centered sum of squares, including within- and between-group variation.
 Exact definition: This is a transparent real expression in subgroup summaries.
 Premises and side conditions: Statistical interpretation requires positive
 subgroup counts; the total function itself makes no distributional claim.
 Proof/definition method: Reuse real arithmetic and a small explicit
 weighted formula rather than implementing a new recursive sum.
 Library reuse: Stdlib Reals and canonical PooledMomentsAlgebra.
 Boundary: This is deterministic scalar algebra and not sampling theory.
*)
Definition three_ss (n m k u v w a b c:R) : R :=
  u+v+w+three_dispersion n m k a b c.
(** [three_variance] (definition).
 Mathematical meaning: The corrected pooled sample variance with denominator total minus one.
 Exact definition: This is a transparent real expression in subgroup summaries.
 Premises and side conditions: Statistical interpretation requires positive
 subgroup counts; the total function itself makes no distributional claim.
 Proof/definition method: Reuse real arithmetic and a small explicit
 weighted formula rather than implementing a new recursive sum.
 Library reuse: Stdlib Reals and canonical PooledMomentsAlgebra.
 Boundary: This is deterministic scalar algebra and not sampling theory.
*)
Definition three_variance (n m k u v w a b c:R) : R :=
  three_ss n m k u v w a b c / (three_mass n m k-1).

(** [three_mass_comm] (theorem).
 Mathematical meaning: The total size of three replicate groups is unchanged by exchanging the first two sizes.
 Exact claim: This is an equality or sharp sign restriction on pooled
 three-replicate real sample summaries relevant to the simulation reports.
 Premises and side conditions: Any needed positive sample total, nonnegative
 weights and positive variance denominator are explicitly quantified in
 the proposition. No independence or Gaussianity is implicit.
 Proof/definition method: Normalize the group summary expressions and use
 the established scalar identities, Rocq Stdlib ring/field or ordered real
 arithmetic; the proof has no oracle or unproved external hypothesis.
 Library reuse: Canonical Reals, Ring, Field, Lra, Psatz and the existing
 PooledMomentsAlgebra module; no replacement finite-sum implementation.
 Boundary: Exact pooled arithmetic for fixed real batch summaries, not
 binomial/chi-square laws, Gaussian confidence coverage or human IQ claims.
*)
Theorem three_mass_comm : forall n m k, three_mass n m k = three_mass m n k.
Proof.
  intros; unfold three_mass; ring.
Qed.

(** [three_mass_rotate] (theorem).
 Mathematical meaning: Cyclic order of replicate groups does not affect combined sample size.
 Exact claim: This is an equality or sharp sign restriction on pooled
 three-replicate real sample summaries relevant to the simulation reports.
 Premises and side conditions: Any needed positive sample total, nonnegative
 weights and positive variance denominator are explicitly quantified in
 the proposition. No independence or Gaussianity is implicit.
 Proof/definition method: Normalize the group summary expressions and use
 the established scalar identities, Rocq Stdlib ring/field or ordered real
 arithmetic; the proof has no oracle or unproved external hypothesis.
 Library reuse: Canonical Reals, Ring, Field, Lra, Psatz and the existing
 PooledMomentsAlgebra module; no replacement finite-sum implementation.
 Boundary: Exact pooled arithmetic for fixed real batch summaries, not
 binomial/chi-square laws, Gaussian confidence coverage or human IQ claims.
*)
Theorem three_mass_rotate : forall n m k, three_mass n m k = three_mass m k n.
Proof.
  intros; unfold three_mass; ring.
Qed.

(** [three_mass_positive] (theorem).
 Mathematical meaning: Three positive replicate counts have a positive pooled denominator.
 Exact claim: This is an equality or sharp sign restriction on pooled
 three-replicate real sample summaries relevant to the simulation reports.
 Premises and side conditions: Any needed positive sample total, nonnegative
 weights and positive variance denominator are explicitly quantified in
 the proposition. No independence or Gaussianity is implicit.
 Proof/definition method: Normalize the group summary expressions and use
 the established scalar identities, Rocq Stdlib ring/field or ordered real
 arithmetic; the proof has no oracle or unproved external hypothesis.
 Library reuse: Canonical Reals, Ring, Field, Lra, Psatz and the existing
 PooledMomentsAlgebra module; no replacement finite-sum implementation.
 Boundary: Exact pooled arithmetic for fixed real batch summaries, not
 binomial/chi-square laws, Gaussian confidence coverage or human IQ claims.
*)
Theorem three_mass_positive : forall n m k, 0<n -> 0<m -> 0<k -> 0<three_mass n m k.
Proof.
  intros; unfold three_mass; lra.
Qed.

(** [three_mass_lower_first] (theorem).
 Mathematical meaning: Total replication size bounds the first batch count.
 Exact claim: This is an equality or sharp sign restriction on pooled
 three-replicate real sample summaries relevant to the simulation reports.
 Premises and side conditions: Any needed positive sample total, nonnegative
 weights and positive variance denominator are explicitly quantified in
 the proposition. No independence or Gaussianity is implicit.
 Proof/definition method: Normalize the group summary expressions and use
 the established scalar identities, Rocq Stdlib ring/field or ordered real
 arithmetic; the proof has no oracle or unproved external hypothesis.
 Library reuse: Canonical Reals, Ring, Field, Lra, Psatz and the existing
 PooledMomentsAlgebra module; no replacement finite-sum implementation.
 Boundary: Exact pooled arithmetic for fixed real batch summaries, not
 binomial/chi-square laws, Gaussian confidence coverage or human IQ claims.
*)
Theorem three_mass_lower_first : forall n m k, 0<=m -> 0<=k -> n<=three_mass n m k.
Proof.
  intros; unfold three_mass; lra.
Qed.

(** [three_mass_strict_first] (theorem).
 Mathematical meaning: Adding two positive replicate counts strictly raises the total.
 Exact claim: This is an equality or sharp sign restriction on pooled
 three-replicate real sample summaries relevant to the simulation reports.
 Premises and side conditions: Any needed positive sample total, nonnegative
 weights and positive variance denominator are explicitly quantified in
 the proposition. No independence or Gaussianity is implicit.
 Proof/definition method: Normalize the group summary expressions and use
 the established scalar identities, Rocq Stdlib ring/field or ordered real
 arithmetic; the proof has no oracle or unproved external hypothesis.
 Library reuse: Canonical Reals, Ring, Field, Lra, Psatz and the existing
 PooledMomentsAlgebra module; no replacement finite-sum implementation.
 Boundary: Exact pooled arithmetic for fixed real batch summaries, not
 binomial/chi-square laws, Gaussian confidence coverage or human IQ claims.
*)
Theorem three_mass_strict_first : forall n m k, 0<m -> 0<k -> n<three_mass n m k.
Proof.
  intros; unfold three_mass; lra.
Qed.

(** [three_numerator_comm] (theorem).
 Mathematical meaning: Raw weighted score sum is invariant under exchanging corresponding replicates.
 Exact claim: This is an equality or sharp sign restriction on pooled
 three-replicate real sample summaries relevant to the simulation reports.
 Premises and side conditions: Any needed positive sample total, nonnegative
 weights and positive variance denominator are explicitly quantified in
 the proposition. No independence or Gaussianity is implicit.
 Proof/definition method: Normalize the group summary expressions and use
 the established scalar identities, Rocq Stdlib ring/field or ordered real
 arithmetic; the proof has no oracle or unproved external hypothesis.
 Library reuse: Canonical Reals, Ring, Field, Lra, Psatz and the existing
 PooledMomentsAlgebra module; no replacement finite-sum implementation.
 Boundary: Exact pooled arithmetic for fixed real batch summaries, not
 binomial/chi-square laws, Gaussian confidence coverage or human IQ claims.
*)
Theorem three_numerator_comm : forall n m k a b c, three_numerator n m k a b c = three_numerator m n k b a c.
Proof.
  intros; unfold three_numerator; ring.
Qed.

(** [three_numerator_rotate] (theorem).
 Mathematical meaning: Cyclic relabeling preserves the weighted score sum.
 Exact claim: This is an equality or sharp sign restriction on pooled
 three-replicate real sample summaries relevant to the simulation reports.
 Premises and side conditions: Any needed positive sample total, nonnegative
 weights and positive variance denominator are explicitly quantified in
 the proposition. No independence or Gaussianity is implicit.
 Proof/definition method: Normalize the group summary expressions and use
 the established scalar identities, Rocq Stdlib ring/field or ordered real
 arithmetic; the proof has no oracle or unproved external hypothesis.
 Library reuse: Canonical Reals, Ring, Field, Lra, Psatz and the existing
 PooledMomentsAlgebra module; no replacement finite-sum implementation.
 Boundary: Exact pooled arithmetic for fixed real batch summaries, not
 binomial/chi-square laws, Gaussian confidence coverage or human IQ claims.
*)
Theorem three_numerator_rotate : forall n m k a b c, three_numerator n m k a b c = three_numerator m k n b c a.
Proof.
  intros; unfold three_numerator; ring.
Qed.

(** [three_numerator_translation] (theorem).
 Mathematical meaning: Translation of all three group means shifts the weighted sum by total mass times the offset.
 Exact claim: This is an equality or sharp sign restriction on pooled
 three-replicate real sample summaries relevant to the simulation reports.
 Premises and side conditions: Any needed positive sample total, nonnegative
 weights and positive variance denominator are explicitly quantified in
 the proposition. No independence or Gaussianity is implicit.
 Proof/definition method: Normalize the group summary expressions and use
 the established scalar identities, Rocq Stdlib ring/field or ordered real
 arithmetic; the proof has no oracle or unproved external hypothesis.
 Library reuse: Canonical Reals, Ring, Field, Lra, Psatz and the existing
 PooledMomentsAlgebra module; no replacement finite-sum implementation.
 Boundary: Exact pooled arithmetic for fixed real batch summaries, not
 binomial/chi-square laws, Gaussian confidence coverage or human IQ claims.
*)
Theorem three_numerator_translation : forall n m k a b c t, three_numerator n m k (a+t) (b+t) (c+t) = three_numerator n m k a b c + t*three_mass n m k.
Proof.
  intros; unfold three_numerator, three_mass; ring.
Qed.

(** [three_numerator_scale] (theorem).
 Mathematical meaning: Scaling all group means scales the aggregate weighted sum.
 Exact claim: This is an equality or sharp sign restriction on pooled
 three-replicate real sample summaries relevant to the simulation reports.
 Premises and side conditions: Any needed positive sample total, nonnegative
 weights and positive variance denominator are explicitly quantified in
 the proposition. No independence or Gaussianity is implicit.
 Proof/definition method: Normalize the group summary expressions and use
 the established scalar identities, Rocq Stdlib ring/field or ordered real
 arithmetic; the proof has no oracle or unproved external hypothesis.
 Library reuse: Canonical Reals, Ring, Field, Lra, Psatz and the existing
 PooledMomentsAlgebra module; no replacement finite-sum implementation.
 Boundary: Exact pooled arithmetic for fixed real batch summaries, not
 binomial/chi-square laws, Gaussian confidence coverage or human IQ claims.
*)
Theorem three_numerator_scale : forall n m k a b c t, three_numerator n m k (t*a) (t*b) (t*c) = t*three_numerator n m k a b c.
Proof.
  intros; unfold three_numerator; ring.
Qed.

(** [three_numerator_zero] (theorem).
 Mathematical meaning: Zero-mean groups have zero pooled weighted score numerator.
 Exact claim: This is an equality or sharp sign restriction on pooled
 three-replicate real sample summaries relevant to the simulation reports.
 Premises and side conditions: Any needed positive sample total, nonnegative
 weights and positive variance denominator are explicitly quantified in
 the proposition. No independence or Gaussianity is implicit.
 Proof/definition method: Normalize the group summary expressions and use
 the established scalar identities, Rocq Stdlib ring/field or ordered real
 arithmetic; the proof has no oracle or unproved external hypothesis.
 Library reuse: Canonical Reals, Ring, Field, Lra, Psatz and the existing
 PooledMomentsAlgebra module; no replacement finite-sum implementation.
 Boundary: Exact pooled arithmetic for fixed real batch summaries, not
 binomial/chi-square laws, Gaussian confidence coverage or human IQ claims.
*)
Theorem three_numerator_zero : forall n m k, three_numerator n m k 0 0 0 = 0.
Proof.
  intros; unfold three_numerator; ring.
Qed.

(** [three_numerator_constant] (theorem).
 Mathematical meaning: The weighted sum of three identical group means equals their common mean times the total size.
 Exact claim: This is an equality or sharp sign restriction on pooled
 three-replicate real sample summaries relevant to the simulation reports.
 Premises and side conditions: Any needed positive sample total, nonnegative
 weights and positive variance denominator are explicitly quantified in
 the proposition. No independence or Gaussianity is implicit.
 Proof/definition method: Normalize the group summary expressions and use
 the established scalar identities, Rocq Stdlib ring/field or ordered real
 arithmetic; the proof has no oracle or unproved external hypothesis.
 Library reuse: Canonical Reals, Ring, Field, Lra, Psatz and the existing
 PooledMomentsAlgebra module; no replacement finite-sum implementation.
 Boundary: Exact pooled arithmetic for fixed real batch summaries, not
 binomial/chi-square laws, Gaussian confidence coverage or human IQ claims.
*)
Theorem three_numerator_constant : forall n m k a, three_numerator n m k a a a = three_mass n m k*a.
Proof.
  intros; unfold three_numerator, three_mass; ring.
Qed.

(** [three_mean_comm] (theorem).
 Mathematical meaning: Pooled three-group mean is invariant under exchange of first and second groups.
 Exact claim: This is an equality or sharp sign restriction on pooled
 three-replicate real sample summaries relevant to the simulation reports.
 Premises and side conditions: Any needed positive sample total, nonnegative
 weights and positive variance denominator are explicitly quantified in
 the proposition. No independence or Gaussianity is implicit.
 Proof/definition method: Normalize the group summary expressions and use
 the established scalar identities, Rocq Stdlib ring/field or ordered real
 arithmetic; the proof has no oracle or unproved external hypothesis.
 Library reuse: Canonical Reals, Ring, Field, Lra, Psatz and the existing
 PooledMomentsAlgebra module; no replacement finite-sum implementation.
 Boundary: Exact pooled arithmetic for fixed real batch summaries, not
 binomial/chi-square laws, Gaussian confidence coverage or human IQ claims.
*)
Theorem three_mean_comm : forall n m k a b c, three_mean n m k a b c = three_mean m n k b a c.
Proof.
  intros; unfold three_mean,three_mass,three_numerator; replace (m+n+k) with (n+m+k) by ring; replace (m*b+n*a+k*c) with (n*a+m*b+k*c) by ring; reflexivity.
Qed.

(** [three_mean_rotate] (theorem).
 Mathematical meaning: Cyclic permutations of complete group summaries preserve the pooled mean.
 Exact claim: This is an equality or sharp sign restriction on pooled
 three-replicate real sample summaries relevant to the simulation reports.
 Premises and side conditions: Any needed positive sample total, nonnegative
 weights and positive variance denominator are explicitly quantified in
 the proposition. No independence or Gaussianity is implicit.
 Proof/definition method: Normalize the group summary expressions and use
 the established scalar identities, Rocq Stdlib ring/field or ordered real
 arithmetic; the proof has no oracle or unproved external hypothesis.
 Library reuse: Canonical Reals, Ring, Field, Lra, Psatz and the existing
 PooledMomentsAlgebra module; no replacement finite-sum implementation.
 Boundary: Exact pooled arithmetic for fixed real batch summaries, not
 binomial/chi-square laws, Gaussian confidence coverage or human IQ claims.
*)
Theorem three_mean_rotate : forall n m k a b c, three_mean n m k a b c = three_mean m k n b c a.
Proof.
  intros; unfold three_mean,three_mass,three_numerator; replace (m+k+n) with (n+m+k) by ring; replace (m*b+k*c+n*a) with (n*a+m*b+k*c) by ring; reflexivity.
Qed.

(** [three_mean_constant] (theorem).
 Mathematical meaning: A pooled mean of identical subgroup centers equals that common center.
 Exact claim: This is an equality or sharp sign restriction on pooled
 three-replicate real sample summaries relevant to the simulation reports.
 Premises and side conditions: Any needed positive sample total, nonnegative
 weights and positive variance denominator are explicitly quantified in
 the proposition. No independence or Gaussianity is implicit.
 Proof/definition method: Normalize the group summary expressions and use
 the established scalar identities, Rocq Stdlib ring/field or ordered real
 arithmetic; the proof has no oracle or unproved external hypothesis.
 Library reuse: Canonical Reals, Ring, Field, Lra, Psatz and the existing
 PooledMomentsAlgebra module; no replacement finite-sum implementation.
 Boundary: Exact pooled arithmetic for fixed real batch summaries, not
 binomial/chi-square laws, Gaussian confidence coverage or human IQ claims.
*)
Theorem three_mean_constant : forall n m k a, 0<three_mass n m k -> three_mean n m k a a a = a.
Proof.
  intros n m k a H; unfold three_mean; rewrite three_numerator_constant; field; lra.
Qed.

(** [three_mean_translation] (theorem).
 Mathematical meaning: Shifting all three subgroup means by a common offset shifts the pooled mean by exactly that offset.
 Exact claim: This is an equality or sharp sign restriction on pooled
 three-replicate real sample summaries relevant to the simulation reports.
 Premises and side conditions: Any needed positive sample total, nonnegative
 weights and positive variance denominator are explicitly quantified in
 the proposition. No independence or Gaussianity is implicit.
 Proof/definition method: Normalize the group summary expressions and use
 the established scalar identities, Rocq Stdlib ring/field or ordered real
 arithmetic; the proof has no oracle or unproved external hypothesis.
 Library reuse: Canonical Reals, Ring, Field, Lra, Psatz and the existing
 PooledMomentsAlgebra module; no replacement finite-sum implementation.
 Boundary: Exact pooled arithmetic for fixed real batch summaries, not
 binomial/chi-square laws, Gaussian confidence coverage or human IQ claims.
*)
Theorem three_mean_translation : forall n m k a b c t, 0<three_mass n m k -> three_mean n m k (a+t) (b+t) (c+t) = three_mean n m k a b c+t.
Proof.
  intros n m k a b c t H; unfold three_mean; rewrite three_numerator_translation; field; lra.
Qed.

(** [three_mean_scale] (theorem).
 Mathematical meaning: Scaling all three subgroup means is equivariant under the pooled average.
 Exact claim: This is an equality or sharp sign restriction on pooled
 three-replicate real sample summaries relevant to the simulation reports.
 Premises and side conditions: Any needed positive sample total, nonnegative
 weights and positive variance denominator are explicitly quantified in
 the proposition. No independence or Gaussianity is implicit.
 Proof/definition method: Normalize the group summary expressions and use
 the established scalar identities, Rocq Stdlib ring/field or ordered real
 arithmetic; the proof has no oracle or unproved external hypothesis.
 Library reuse: Canonical Reals, Ring, Field, Lra, Psatz and the existing
 PooledMomentsAlgebra module; no replacement finite-sum implementation.
 Boundary: Exact pooled arithmetic for fixed real batch summaries, not
 binomial/chi-square laws, Gaussian confidence coverage or human IQ claims.
*)
Theorem three_mean_scale : forall n m k a b c t, three_mean n m k (t*a) (t*b) (t*c) = t*three_mean n m k a b c.
Proof.
  intros; unfold three_mean; rewrite three_numerator_scale; unfold Rdiv; ring.
Qed.

(** [three_mean_mass_identity] (theorem).
 Mathematical meaning: The pooled mean recovers the weighted raw score sum after multiplication by total sample count.
 Exact claim: This is an equality or sharp sign restriction on pooled
 three-replicate real sample summaries relevant to the simulation reports.
 Premises and side conditions: Any needed positive sample total, nonnegative
 weights and positive variance denominator are explicitly quantified in
 the proposition. No independence or Gaussianity is implicit.
 Proof/definition method: Normalize the group summary expressions and use
 the established scalar identities, Rocq Stdlib ring/field or ordered real
 arithmetic; the proof has no oracle or unproved external hypothesis.
 Library reuse: Canonical Reals, Ring, Field, Lra, Psatz and the existing
 PooledMomentsAlgebra module; no replacement finite-sum implementation.
 Boundary: Exact pooled arithmetic for fixed real batch summaries, not
 binomial/chi-square laws, Gaussian confidence coverage or human IQ claims.
*)
Theorem three_mean_mass_identity : forall n m k a b c, 0<three_mass n m k -> three_mass n m k * three_mean n m k a b c = three_numerator n m k a b c.
Proof.
  intros n m k a b c H; unfold three_mean; field; lra.
Qed.

(** [three_mean_centered_balance] (theorem).
 Mathematical meaning: The weighted deviations of replicate centers from their pooled mean sum to zero.
 Exact claim: This is an equality or sharp sign restriction on pooled
 three-replicate real sample summaries relevant to the simulation reports.
 Premises and side conditions: Any needed positive sample total, nonnegative
 weights and positive variance denominator are explicitly quantified in
 the proposition. No independence or Gaussianity is implicit.
 Proof/definition method: Normalize the group summary expressions and use
 the established scalar identities, Rocq Stdlib ring/field or ordered real
 arithmetic; the proof has no oracle or unproved external hypothesis.
 Library reuse: Canonical Reals, Ring, Field, Lra, Psatz and the existing
 PooledMomentsAlgebra module; no replacement finite-sum implementation.
 Boundary: Exact pooled arithmetic for fixed real batch summaries, not
 binomial/chi-square laws, Gaussian confidence coverage or human IQ claims.
*)
Theorem three_mean_centered_balance : forall n m k a b c, 0<three_mass n m k -> n*(a-three_mean n m k a b c)+m*(b-three_mean n m k a b c)+k*(c-three_mean n m k a b c)=0.
Proof.
  intros n m k a b c H; pose proof (three_mean_mass_identity n m k a b c H) as Q; unfold three_numerator,three_mass in Q; nra.
Qed.

(** [three_mean_zero_center] (theorem).
 Mathematical meaning: A positive-size pooled mean is zero exactly when the combined weighted numerator is zero.
 Exact claim: This is an equality or sharp sign restriction on pooled
 three-replicate real sample summaries relevant to the simulation reports.
 Premises and side conditions: Any needed positive sample total, nonnegative
 weights and positive variance denominator are explicitly quantified in
 the proposition. No independence or Gaussianity is implicit.
 Proof/definition method: Normalize the group summary expressions and use
 the established scalar identities, Rocq Stdlib ring/field or ordered real
 arithmetic; the proof has no oracle or unproved external hypothesis.
 Library reuse: Canonical Reals, Ring, Field, Lra, Psatz and the existing
 PooledMomentsAlgebra module; no replacement finite-sum implementation.
 Boundary: Exact pooled arithmetic for fixed real batch summaries, not
 binomial/chi-square laws, Gaussian confidence coverage or human IQ claims.
*)
Theorem three_mean_zero_center : forall n m k a b c, 0<three_mass n m k -> (three_mean n m k a b c=0 <-> three_numerator n m k a b c=0).
Proof.
  intros n m k a b c H; split; intro Q.
  - pose proof (three_mean_mass_identity n m k a b c H) as E.
    rewrite Q in E. nra.
  - unfold three_mean. rewrite Q. field; lra.
Qed.

(** [three_raw_second_comm] (theorem).
 Mathematical meaning: Second-moment numerator is invariant under exchange of complete group summaries.
 Exact claim: This is an equality or sharp sign restriction on pooled
 three-replicate real sample summaries relevant to the simulation reports.
 Premises and side conditions: Any needed positive sample total, nonnegative
 weights and positive variance denominator are explicitly quantified in
 the proposition. No independence or Gaussianity is implicit.
 Proof/definition method: Normalize the group summary expressions and use
 the established scalar identities, Rocq Stdlib ring/field or ordered real
 arithmetic; the proof has no oracle or unproved external hypothesis.
 Library reuse: Canonical Reals, Ring, Field, Lra, Psatz and the existing
 PooledMomentsAlgebra module; no replacement finite-sum implementation.
 Boundary: Exact pooled arithmetic for fixed real batch summaries, not
 binomial/chi-square laws, Gaussian confidence coverage or human IQ claims.
*)
Theorem three_raw_second_comm : forall n m k a b c, three_raw_second n m k a b c = three_raw_second m n k b a c.
Proof.
  intros; unfold three_raw_second; ring.
Qed.

(** [three_raw_second_rotate] (theorem).
 Mathematical meaning: Second-moment numerator is invariant under cyclic relabeling.
 Exact claim: This is an equality or sharp sign restriction on pooled
 three-replicate real sample summaries relevant to the simulation reports.
 Premises and side conditions: Any needed positive sample total, nonnegative
 weights and positive variance denominator are explicitly quantified in
 the proposition. No independence or Gaussianity is implicit.
 Proof/definition method: Normalize the group summary expressions and use
 the established scalar identities, Rocq Stdlib ring/field or ordered real
 arithmetic; the proof has no oracle or unproved external hypothesis.
 Library reuse: Canonical Reals, Ring, Field, Lra, Psatz and the existing
 PooledMomentsAlgebra module; no replacement finite-sum implementation.
 Boundary: Exact pooled arithmetic for fixed real batch summaries, not
 binomial/chi-square laws, Gaussian confidence coverage or human IQ claims.
*)
Theorem three_raw_second_rotate : forall n m k a b c, three_raw_second n m k a b c = three_raw_second m k n b c a.
Proof.
  intros; unfold three_raw_second; ring.
Qed.

(** [three_raw_second_scale] (theorem).
 Mathematical meaning: A common scaling squares in the uncentered weighted second moment.
 Exact claim: This is an equality or sharp sign restriction on pooled
 three-replicate real sample summaries relevant to the simulation reports.
 Premises and side conditions: Any needed positive sample total, nonnegative
 weights and positive variance denominator are explicitly quantified in
 the proposition. No independence or Gaussianity is implicit.
 Proof/definition method: Normalize the group summary expressions and use
 the established scalar identities, Rocq Stdlib ring/field or ordered real
 arithmetic; the proof has no oracle or unproved external hypothesis.
 Library reuse: Canonical Reals, Ring, Field, Lra, Psatz and the existing
 PooledMomentsAlgebra module; no replacement finite-sum implementation.
 Boundary: Exact pooled arithmetic for fixed real batch summaries, not
 binomial/chi-square laws, Gaussian confidence coverage or human IQ claims.
*)
Theorem three_raw_second_scale : forall n m k a b c t, three_raw_second n m k (t*a) (t*b) (t*c)=t*t*three_raw_second n m k a b c.
Proof.
  intros; unfold three_raw_second; ring.
Qed.

(** [three_raw_second_nonnegative] (theorem).
 Mathematical meaning: A nonnegative weighted sum of real squares is nonnegative.
 Exact claim: This is an equality or sharp sign restriction on pooled
 three-replicate real sample summaries relevant to the simulation reports.
 Premises and side conditions: Any needed positive sample total, nonnegative
 weights and positive variance denominator are explicitly quantified in
 the proposition. No independence or Gaussianity is implicit.
 Proof/definition method: Normalize the group summary expressions and use
 the established scalar identities, Rocq Stdlib ring/field or ordered real
 arithmetic; the proof has no oracle or unproved external hypothesis.
 Library reuse: Canonical Reals, Ring, Field, Lra, Psatz and the existing
 PooledMomentsAlgebra module; no replacement finite-sum implementation.
 Boundary: Exact pooled arithmetic for fixed real batch summaries, not
 binomial/chi-square laws, Gaussian confidence coverage or human IQ claims.
*)
Theorem three_raw_second_nonnegative : forall n m k a b c, 0<=n -> 0<=m -> 0<=k -> 0<=three_raw_second n m k a b c.
Proof.
  intros; unfold three_raw_second; nra.
Qed.

(** [three_raw_second_constant] (theorem).
 Mathematical meaning: Identical group means produce the expected raw weighted second moment.
 Exact claim: This is an equality or sharp sign restriction on pooled
 three-replicate real sample summaries relevant to the simulation reports.
 Premises and side conditions: Any needed positive sample total, nonnegative
 weights and positive variance denominator are explicitly quantified in
 the proposition. No independence or Gaussianity is implicit.
 Proof/definition method: Normalize the group summary expressions and use
 the established scalar identities, Rocq Stdlib ring/field or ordered real
 arithmetic; the proof has no oracle or unproved external hypothesis.
 Library reuse: Canonical Reals, Ring, Field, Lra, Psatz and the existing
 PooledMomentsAlgebra module; no replacement finite-sum implementation.
 Boundary: Exact pooled arithmetic for fixed real batch summaries, not
 binomial/chi-square laws, Gaussian confidence coverage or human IQ claims.
*)
Theorem three_raw_second_constant : forall n m k a, three_raw_second n m k a a a=three_mass n m k*a*a.
Proof.
  intros; unfold three_raw_second,three_mass; ring.
Qed.

(** [three_dispersion_nonnegative] (theorem).
 Mathematical meaning: Within-composite dispersion among subgroup centers is a nonnegative weighted sum of squares.
 Exact claim: This is an equality or sharp sign restriction on pooled
 three-replicate real sample summaries relevant to the simulation reports.
 Premises and side conditions: Any needed positive sample total, nonnegative
 weights and positive variance denominator are explicitly quantified in
 the proposition. No independence or Gaussianity is implicit.
 Proof/definition method: Normalize the group summary expressions and use
 the established scalar identities, Rocq Stdlib ring/field or ordered real
 arithmetic; the proof has no oracle or unproved external hypothesis.
 Library reuse: Canonical Reals, Ring, Field, Lra, Psatz and the existing
 PooledMomentsAlgebra module; no replacement finite-sum implementation.
 Boundary: Exact pooled arithmetic for fixed real batch summaries, not
 binomial/chi-square laws, Gaussian confidence coverage or human IQ claims.
*)
Theorem three_dispersion_nonnegative : forall n m k a b c, 0<=n -> 0<=m -> 0<=k -> 0<=three_dispersion n m k a b c.
Proof.
  intros n m k a b c Hn Hm Hk.
  unfold three_dispersion.
  set (t := three_mean n m k a b c).
  assert (Ha : 0 <= n*(a-t)*(a-t)).
  { replace (n*(a-t)*(a-t)) with (n*((a-t)*(a-t))) by ring.
    apply Rmult_le_pos; [exact Hn | apply Rle_0_sqr]. }
  assert (Hb : 0 <= m*(b-t)*(b-t)).
  { replace (m*(b-t)*(b-t)) with (m*((b-t)*(b-t))) by ring.
    apply Rmult_le_pos; [exact Hm | apply Rle_0_sqr]. }
  assert (Hc : 0 <= k*(c-t)*(c-t)).
  { replace (k*(c-t)*(c-t)) with (k*((c-t)*(c-t))) by ring.
    apply Rmult_le_pos; [exact Hk | apply Rle_0_sqr]. }
  nra.
Qed.

(** [three_dispersion_constant] (theorem).
 Mathematical meaning: No between-group dispersion remains when all three means coincide.
 Exact claim: This is an equality or sharp sign restriction on pooled
 three-replicate real sample summaries relevant to the simulation reports.
 Premises and side conditions: Any needed positive sample total, nonnegative
 weights and positive variance denominator are explicitly quantified in
 the proposition. No independence or Gaussianity is implicit.
 Proof/definition method: Normalize the group summary expressions and use
 the established scalar identities, Rocq Stdlib ring/field or ordered real
 arithmetic; the proof has no oracle or unproved external hypothesis.
 Library reuse: Canonical Reals, Ring, Field, Lra, Psatz and the existing
 PooledMomentsAlgebra module; no replacement finite-sum implementation.
 Boundary: Exact pooled arithmetic for fixed real batch summaries, not
 binomial/chi-square laws, Gaussian confidence coverage or human IQ claims.
*)
Theorem three_dispersion_constant : forall n m k a, 0<three_mass n m k -> three_dispersion n m k a a a=0.
Proof.
  intros n m k a H; unfold three_dispersion; rewrite three_mean_constant by exact H; ring.
Qed.

(** [three_dispersion_zero_means] (theorem).
 Mathematical meaning: The zero-mean special case produces a zero between-group sum of squares.
 Exact claim: This is an equality or sharp sign restriction on pooled
 three-replicate real sample summaries relevant to the simulation reports.
 Premises and side conditions: Any needed positive sample total, nonnegative
 weights and positive variance denominator are explicitly quantified in
 the proposition. No independence or Gaussianity is implicit.
 Proof/definition method: Normalize the group summary expressions and use
 the established scalar identities, Rocq Stdlib ring/field or ordered real
 arithmetic; the proof has no oracle or unproved external hypothesis.
 Library reuse: Canonical Reals, Ring, Field, Lra, Psatz and the existing
 PooledMomentsAlgebra module; no replacement finite-sum implementation.
 Boundary: Exact pooled arithmetic for fixed real batch summaries, not
 binomial/chi-square laws, Gaussian confidence coverage or human IQ claims.
*)
Theorem three_dispersion_zero_means : forall n m k, 0<three_mass n m k -> three_dispersion n m k 0 0 0=0.
Proof.
  intros; apply three_dispersion_constant; assumption.
Qed.

(** [three_ss_above_within] (theorem).
 Mathematical meaning: Pooling cannot remove the nonnegative between-group contribution to the sum of squares.
 Exact claim: This is an equality or sharp sign restriction on pooled
 three-replicate real sample summaries relevant to the simulation reports.
 Premises and side conditions: Any needed positive sample total, nonnegative
 weights and positive variance denominator are explicitly quantified in
 the proposition. No independence or Gaussianity is implicit.
 Proof/definition method: Normalize the group summary expressions and use
 the established scalar identities, Rocq Stdlib ring/field or ordered real
 arithmetic; the proof has no oracle or unproved external hypothesis.
 Library reuse: Canonical Reals, Ring, Field, Lra, Psatz and the existing
 PooledMomentsAlgebra module; no replacement finite-sum implementation.
 Boundary: Exact pooled arithmetic for fixed real batch summaries, not
 binomial/chi-square laws, Gaussian confidence coverage or human IQ claims.
*)
Theorem three_ss_above_within : forall n m k u v w a b c, 0<=n -> 0<=m -> 0<=k -> u+v+w<=three_ss n m k u v w a b c.
Proof.
  intros n m k u v w a b c Hn Hm Hk; unfold three_ss; pose proof (three_dispersion_nonnegative n m k a b c Hn Hm Hk) as H; nra.
Qed.

(** [three_ss_nonnegative] (theorem).
 Mathematical meaning: Nonnegative within-batch sums plus nonnegative between-batch dispersion have nonnegative pooled SS.
 Exact claim: This is an equality or sharp sign restriction on pooled
 three-replicate real sample summaries relevant to the simulation reports.
 Premises and side conditions: Any needed positive sample total, nonnegative
 weights and positive variance denominator are explicitly quantified in
 the proposition. No independence or Gaussianity is implicit.
 Proof/definition method: Normalize the group summary expressions and use
 the established scalar identities, Rocq Stdlib ring/field or ordered real
 arithmetic; the proof has no oracle or unproved external hypothesis.
 Library reuse: Canonical Reals, Ring, Field, Lra, Psatz and the existing
 PooledMomentsAlgebra module; no replacement finite-sum implementation.
 Boundary: Exact pooled arithmetic for fixed real batch summaries, not
 binomial/chi-square laws, Gaussian confidence coverage or human IQ claims.
*)
Theorem three_ss_nonnegative : forall n m k u v w a b c, 0<=n -> 0<=m -> 0<=k -> 0<=u -> 0<=v -> 0<=w -> 0<=three_ss n m k u v w a b c.
Proof.
  intros n m k u v w a b c Hn Hm Hk Hu Hv Hw; unfold three_ss; pose proof (three_dispersion_nonnegative n m k a b c Hn Hm Hk) as H; nra.
Qed.

(** [three_ss_within_increment] (theorem).
 Mathematical meaning: Increasing one batch's corrected sum of squares increases pooled SS by the same amount.
 Exact claim: This is an equality or sharp sign restriction on pooled
 three-replicate real sample summaries relevant to the simulation reports.
 Premises and side conditions: Any needed positive sample total, nonnegative
 weights and positive variance denominator are explicitly quantified in
 the proposition. No independence or Gaussianity is implicit.
 Proof/definition method: Normalize the group summary expressions and use
 the established scalar identities, Rocq Stdlib ring/field or ordered real
 arithmetic; the proof has no oracle or unproved external hypothesis.
 Library reuse: Canonical Reals, Ring, Field, Lra, Psatz and the existing
 PooledMomentsAlgebra module; no replacement finite-sum implementation.
 Boundary: Exact pooled arithmetic for fixed real batch summaries, not
 binomial/chi-square laws, Gaussian confidence coverage or human IQ claims.
*)
Theorem three_ss_within_increment : forall n m k u v w a b c t, three_ss n m k (u+t) v w a b c = three_ss n m k u v w a b c+t.
Proof.
  intros; unfold three_ss; ring.
Qed.

(** [three_ss_second_increment] (theorem).
 Mathematical meaning: The second group's within-batch SS contributes additively.
 Exact claim: This is an equality or sharp sign restriction on pooled
 three-replicate real sample summaries relevant to the simulation reports.
 Premises and side conditions: Any needed positive sample total, nonnegative
 weights and positive variance denominator are explicitly quantified in
 the proposition. No independence or Gaussianity is implicit.
 Proof/definition method: Normalize the group summary expressions and use
 the established scalar identities, Rocq Stdlib ring/field or ordered real
 arithmetic; the proof has no oracle or unproved external hypothesis.
 Library reuse: Canonical Reals, Ring, Field, Lra, Psatz and the existing
 PooledMomentsAlgebra module; no replacement finite-sum implementation.
 Boundary: Exact pooled arithmetic for fixed real batch summaries, not
 binomial/chi-square laws, Gaussian confidence coverage or human IQ claims.
*)
Theorem three_ss_second_increment : forall n m k u v w a b c t, three_ss n m k u (v+t) w a b c = three_ss n m k u v w a b c+t.
Proof.
  intros; unfold three_ss; ring.
Qed.

(** [three_ss_third_increment] (theorem).
 Mathematical meaning: The third group's within-batch SS contributes additively.
 Exact claim: This is an equality or sharp sign restriction on pooled
 three-replicate real sample summaries relevant to the simulation reports.
 Premises and side conditions: Any needed positive sample total, nonnegative
 weights and positive variance denominator are explicitly quantified in
 the proposition. No independence or Gaussianity is implicit.
 Proof/definition method: Normalize the group summary expressions and use
 the established scalar identities, Rocq Stdlib ring/field or ordered real
 arithmetic; the proof has no oracle or unproved external hypothesis.
 Library reuse: Canonical Reals, Ring, Field, Lra, Psatz and the existing
 PooledMomentsAlgebra module; no replacement finite-sum implementation.
 Boundary: Exact pooled arithmetic for fixed real batch summaries, not
 binomial/chi-square laws, Gaussian confidence coverage or human IQ claims.
*)
Theorem three_ss_third_increment : forall n m k u v w a b c t, three_ss n m k u v (w+t) a b c = three_ss n m k u v w a b c+t.
Proof.
  intros; unfold three_ss; ring.
Qed.

(** [three_ss_within_swap] (theorem).
 Mathematical meaning: Exchanging first and second replicate summaries leaves pooled SS invariant.
 Exact claim: This is an equality or sharp sign restriction on pooled
 three-replicate real sample summaries relevant to the simulation reports.
 Premises and side conditions: Any needed positive sample total, nonnegative
 weights and positive variance denominator are explicitly quantified in
 the proposition. No independence or Gaussianity is implicit.
 Proof/definition method: Normalize the group summary expressions and use
 the established scalar identities, Rocq Stdlib ring/field or ordered real
 arithmetic; the proof has no oracle or unproved external hypothesis.
 Library reuse: Canonical Reals, Ring, Field, Lra, Psatz and the existing
 PooledMomentsAlgebra module; no replacement finite-sum implementation.
 Boundary: Exact pooled arithmetic for fixed real batch summaries, not
 binomial/chi-square laws, Gaussian confidence coverage or human IQ claims.
*)
Theorem three_ss_within_swap : forall n m k u v w a b c, three_ss n m k u v w a b c = three_ss m n k v u w b a c.
Proof.
  intros; unfold three_ss,three_dispersion; rewrite three_mean_comm; ring.
Qed.

(** [three_ss_zero_within_equal] (theorem).
 Mathematical meaning: Three constant equal-valued groups produce zero total centered SS.
 Exact claim: This is an equality or sharp sign restriction on pooled
 three-replicate real sample summaries relevant to the simulation reports.
 Premises and side conditions: Any needed positive sample total, nonnegative
 weights and positive variance denominator are explicitly quantified in
 the proposition. No independence or Gaussianity is implicit.
 Proof/definition method: Normalize the group summary expressions and use
 the established scalar identities, Rocq Stdlib ring/field or ordered real
 arithmetic; the proof has no oracle or unproved external hypothesis.
 Library reuse: Canonical Reals, Ring, Field, Lra, Psatz and the existing
 PooledMomentsAlgebra module; no replacement finite-sum implementation.
 Boundary: Exact pooled arithmetic for fixed real batch summaries, not
 binomial/chi-square laws, Gaussian confidence coverage or human IQ claims.
*)
Theorem three_ss_zero_within_equal : forall n m k a, 0<three_mass n m k -> three_ss n m k 0 0 0 a a a=0.
Proof.
  intros n m k a H; unfold three_ss; rewrite three_dispersion_constant by exact H; ring.
Qed.
