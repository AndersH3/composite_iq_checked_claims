(** Module: ConditionalRatioStability.v
 Purpose: Certify exact conditional admission ratios, denominator sensitivity
 and valid probability bounds used by the Towers and simulation reports.
 Mathematical representation: A generic real intersection mass j and positive
 conditioning mass p have scalar rate j/p. We prove its algebraic relationships
 without implementing a second finite event or probability-measure engine.
 Explicit hypotheses: Strict positivity of all denominators and the
 sign/order of event masses are explicit at each theorem; no conditional
 frequency with zero sample count is silently defined as probability.
 Library use: Rocq Stdlib Reals, Field, Ring, Lra and Psatz. For event sums,
 the established FiniteUnion/Admissions modules remain canonical.
 Limitations: Exact real ratio and sensitivity identities only; no Gaussian
 tail, random-denominator binomial law or unproved numerical error certificate.
 Reproduction: rocq compile ConditionalRatioStability.v using Rocq 9.2.
 AI disclosure: OpenAI ChatGPT assisted proof development and documentation;
 kernel acceptance, not an AI assertion, establishes formal validity.
*)
From Stdlib Require Import Reals Lra Psatz Ring Field.
Open Scope R_scope.

(** [conditional_ratio] (definition).
 Mathematical meaning: The generic ratio between a joint event mass and a
 positive conditioning mass, used for admissions and selected-trial counts.
 Exact declaration: conditional_ratio j p := j/p.
 Premises and side conditions: The definition is total in real arithmetic;
 theorems that interpret it as a conditional rate separately assume p>0.
 Proof/definition method: This is Stdlib real division, not a new
 probability model, event enumeration, normalization or integral.
 Library reuse: Rocq Stdlib Reals, Field, Lra and Psatz.
 Boundary: No Gaussian or empirical test-probability assumption is encoded.
*)
Definition conditional_ratio (j p:R):R:=j/p.

(** [conditional_ratio_cancel] (theorem).
 Mathematical meaning: Multiplying a conditional ratio by its strictly positive conditioning mass recovers the intersection mass.
 Exact proposition: forall j p, 0<p -> conditional_ratio j p *p=j.
 Premises and side conditions: Conditional rates are used only under the
 explicitly stated positive conditioning mass and signs/order of joint
 masses. Division by zero is never interpreted as an event probability;
 real-algebra theorems do not require or imply Gaussianity.
 Proof/definition method: Algebraic denominator cancellation and earlier
 ratio lemmas with Rocq Stdlib Field, Ring, Psatz and Lra tactics.
 Library reuse: Stdlib rational-function simplification and order; these
 are reusable scalar corollaries, not a duplicate conditional-event engine.
 Boundary: Exact deterministic conditional-ratio algebra; not distribution
 theory, independent Monte Carlo replicates, binomial conditional coverage,
 or empirical population admission calibration.
*)
Theorem conditional_ratio_cancel: forall j p, 0<p -> conditional_ratio j p *p=j.
Proof.
  intros j p Hp; unfold conditional_ratio; field; lra.
Qed.

(** [conditional_ratio_nonnegative] (theorem).
 Mathematical meaning: Any nonnegative intersection mass has a nonnegative conditional ratio.
 Exact proposition: forall j p, 0<p -> 0<=j -> 0<=conditional_ratio j p.
 Premises and side conditions: Conditional rates are used only under the
 explicitly stated positive conditioning mass and signs/order of joint
 masses. Division by zero is never interpreted as an event probability;
 real-algebra theorems do not require or imply Gaussianity.
 Proof/definition method: Algebraic denominator cancellation and earlier
 ratio lemmas with Rocq Stdlib Field, Ring, Psatz and Lra tactics.
 Library reuse: Stdlib rational-function simplification and order; these
 are reusable scalar corollaries, not a duplicate conditional-event engine.
 Boundary: Exact deterministic conditional-ratio algebra; not distribution
 theory, independent Monte Carlo replicates, binomial conditional coverage,
 or empirical population admission calibration.
*)
Theorem conditional_ratio_nonnegative: forall j p, 0<p -> 0<=j -> 0<=conditional_ratio j p.
Proof.
  intros j p Hp Hj. unfold conditional_ratio,Rdiv. apply Rmult_le_pos; [exact Hj|left; apply Rinv_0_lt_compat; exact Hp].
Qed.

(** [conditional_ratio_positive] (theorem).
 Mathematical meaning: Strictly positive intersection mass yields strictly positive conditioning rate.
 Exact proposition: forall j p, 0<p -> 0<j -> 0<conditional_ratio j p.
 Premises and side conditions: Conditional rates are used only under the
 explicitly stated positive conditioning mass and signs/order of joint
 masses. Division by zero is never interpreted as an event probability;
 real-algebra theorems do not require or imply Gaussianity.
 Proof/definition method: Algebraic denominator cancellation and earlier
 ratio lemmas with Rocq Stdlib Field, Ring, Psatz and Lra tactics.
 Library reuse: Stdlib rational-function simplification and order; these
 are reusable scalar corollaries, not a duplicate conditional-event engine.
 Boundary: Exact deterministic conditional-ratio algebra; not distribution
 theory, independent Monte Carlo replicates, binomial conditional coverage,
 or empirical population admission calibration.
*)
Theorem conditional_ratio_positive: forall j p, 0<p -> 0<j -> 0<conditional_ratio j p.
Proof.
  intros j p Hp Hj. unfold conditional_ratio,Rdiv. apply Rmult_lt_0_compat; [exact Hj|apply Rinv_0_lt_compat; exact Hp].
Qed.

(** [conditional_ratio_zero] (theorem).
 Mathematical meaning: An impossible event inside a positive conditioning set has conditional probability zero.
 Exact proposition: forall p, 0<p -> conditional_ratio 0 p=0.
 Premises and side conditions: Conditional rates are used only under the
 explicitly stated positive conditioning mass and signs/order of joint
 masses. Division by zero is never interpreted as an event probability;
 real-algebra theorems do not require or imply Gaussianity.
 Proof/definition method: Algebraic denominator cancellation and earlier
 ratio lemmas with Rocq Stdlib Field, Ring, Psatz and Lra tactics.
 Library reuse: Stdlib rational-function simplification and order; these
 are reusable scalar corollaries, not a duplicate conditional-event engine.
 Boundary: Exact deterministic conditional-ratio algebra; not distribution
 theory, independent Monte Carlo replicates, binomial conditional coverage,
 or empirical population admission calibration.
*)
Theorem conditional_ratio_zero: forall p, 0<p -> conditional_ratio 0 p=0.
Proof.
  intros p Hp; unfold conditional_ratio,Rdiv; ring.
Qed.

(** [conditional_ratio_self] (theorem).
 Mathematical meaning: Every positive-mass event has conditional probability one given itself.
 Exact proposition: forall p, 0<p -> conditional_ratio p p=1.
 Premises and side conditions: Conditional rates are used only under the
 explicitly stated positive conditioning mass and signs/order of joint
 masses. Division by zero is never interpreted as an event probability;
 real-algebra theorems do not require or imply Gaussianity.
 Proof/definition method: Algebraic denominator cancellation and earlier
 ratio lemmas with Rocq Stdlib Field, Ring, Psatz and Lra tactics.
 Library reuse: Stdlib rational-function simplification and order; these
 are reusable scalar corollaries, not a duplicate conditional-event engine.
 Boundary: Exact deterministic conditional-ratio algebra; not distribution
 theory, independent Monte Carlo replicates, binomial conditional coverage,
 or empirical population admission calibration.
*)
Theorem conditional_ratio_self: forall p, 0<p -> conditional_ratio p p=1.
Proof.
  intros p Hp; unfold conditional_ratio; field; lra.
Qed.

(** [conditional_ratio_complement] (theorem).
 Mathematical meaning: Conditional success and conditional failure probabilities sum to one.
 Exact proposition: forall j p, 0<p -> conditional_ratio (p-j) p = 1-conditional_ratio j p.
 Premises and side conditions: Conditional rates are used only under the
 explicitly stated positive conditioning mass and signs/order of joint
 masses. Division by zero is never interpreted as an event probability;
 real-algebra theorems do not require or imply Gaussianity.
 Proof/definition method: Algebraic denominator cancellation and earlier
 ratio lemmas with Rocq Stdlib Field, Ring, Psatz and Lra tactics.
 Library reuse: Stdlib rational-function simplification and order; these
 are reusable scalar corollaries, not a duplicate conditional-event engine.
 Boundary: Exact deterministic conditional-ratio algebra; not distribution
 theory, independent Monte Carlo replicates, binomial conditional coverage,
 or empirical population admission calibration.
*)
Theorem conditional_ratio_complement: forall j p, 0<p -> conditional_ratio (p-j) p = 1-conditional_ratio j p.
Proof.
  intros j p Hp; unfold conditional_ratio; field; lra.
Qed.

(** [conditional_ratio_partition] (theorem).
 Mathematical meaning: The conditional joint and exclusive masses exhaust the entire conditioning event.
 Exact proposition: forall j p, 0<p -> conditional_ratio j p+conditional_ratio (p-j) p=1.
 Premises and side conditions: Conditional rates are used only under the
 explicitly stated positive conditioning mass and signs/order of joint
 masses. Division by zero is never interpreted as an event probability;
 real-algebra theorems do not require or imply Gaussianity.
 Proof/definition method: Algebraic denominator cancellation and earlier
 ratio lemmas with Rocq Stdlib Field, Ring, Psatz and Lra tactics.
 Library reuse: Stdlib rational-function simplification and order; these
 are reusable scalar corollaries, not a duplicate conditional-event engine.
 Boundary: Exact deterministic conditional-ratio algebra; not distribution
 theory, independent Monte Carlo replicates, binomial conditional coverage,
 or empirical population admission calibration.
*)
Theorem conditional_ratio_partition: forall j p, 0<p -> conditional_ratio j p+conditional_ratio (p-j) p=1.
Proof.
  intros j p Hp; rewrite conditional_ratio_complement by assumption; ring.
Qed.

(** [conditional_ratio_le_one] (theorem).
 Mathematical meaning: A nonnegative intersection bounded by its conditioning event gives rate at most one.
 Exact proposition: forall j p, 0<p -> j<=p -> conditional_ratio j p<=1.
 Premises and side conditions: Conditional rates are used only under the
 explicitly stated positive conditioning mass and signs/order of joint
 masses. Division by zero is never interpreted as an event probability;
 real-algebra theorems do not require or imply Gaussianity.
 Proof/definition method: Algebraic denominator cancellation and earlier
 ratio lemmas with Rocq Stdlib Field, Ring, Psatz and Lra tactics.
 Library reuse: Stdlib rational-function simplification and order; these
 are reusable scalar corollaries, not a duplicate conditional-event engine.
 Boundary: Exact deterministic conditional-ratio algebra; not distribution
 theory, independent Monte Carlo replicates, binomial conditional coverage,
 or empirical population admission calibration.
*)
Theorem conditional_ratio_le_one: forall j p, 0<p -> j<=p -> conditional_ratio j p<=1.
Proof.
  intros j p Hp Hj. pose proof (conditional_ratio_cancel j p Hp) as Hc. nra.
Qed.

(** [conditional_ratio_unit_interval] (theorem).
 Mathematical meaning: Every valid positive-mass conditional probability belongs to the unit interval.
 Exact proposition: forall j p, 0<p -> 0<=j -> j<=p -> 0<=conditional_ratio j p<=1.
 Premises and side conditions: Conditional rates are used only under the
 explicitly stated positive conditioning mass and signs/order of joint
 masses. Division by zero is never interpreted as an event probability;
 real-algebra theorems do not require or imply Gaussianity.
 Proof/definition method: Algebraic denominator cancellation and earlier
 ratio lemmas with Rocq Stdlib Field, Ring, Psatz and Lra tactics.
 Library reuse: Stdlib rational-function simplification and order; these
 are reusable scalar corollaries, not a duplicate conditional-event engine.
 Boundary: Exact deterministic conditional-ratio algebra; not distribution
 theory, independent Monte Carlo replicates, binomial conditional coverage,
 or empirical population admission calibration.
*)
Theorem conditional_ratio_unit_interval: forall j p, 0<p -> 0<=j -> j<=p -> 0<=conditional_ratio j p<=1.
Proof.
  intros j p Hp Hj Hbound; split; [apply conditional_ratio_nonnegative; assumption|apply conditional_ratio_le_one; assumption].
Qed.

(** [conditional_ratio_strict_below_one] (theorem).
 Mathematical meaning: A strictly positive exclusive residual yields a conditional event rate strictly below one.
 Exact proposition: forall j p, 0<p -> j<p -> conditional_ratio j p<1.
 Premises and side conditions: Conditional rates are used only under the
 explicitly stated positive conditioning mass and signs/order of joint
 masses. Division by zero is never interpreted as an event probability;
 real-algebra theorems do not require or imply Gaussianity.
 Proof/definition method: Algebraic denominator cancellation and earlier
 ratio lemmas with Rocq Stdlib Field, Ring, Psatz and Lra tactics.
 Library reuse: Stdlib rational-function simplification and order; these
 are reusable scalar corollaries, not a duplicate conditional-event engine.
 Boundary: Exact deterministic conditional-ratio algebra; not distribution
 theory, independent Monte Carlo replicates, binomial conditional coverage,
 or empirical population admission calibration.
*)
Theorem conditional_ratio_strict_below_one: forall j p, 0<p -> j<p -> conditional_ratio j p<1.
Proof.
  intros j p Hp Hj. pose proof (conditional_ratio_cancel j p Hp) as Hc. nra.
Qed.

(** [conditional_ratio_one_implies_equal_masses] (theorem).
 Mathematical meaning: Conditional probability exactly one forces equality of joint and conditioning masses.
 Exact proposition: forall j p, 0<p -> conditional_ratio j p=1 -> j=p.
 Premises and side conditions: Conditional rates are used only under the
 explicitly stated positive conditioning mass and signs/order of joint
 masses. Division by zero is never interpreted as an event probability;
 real-algebra theorems do not require or imply Gaussianity.
 Proof/definition method: Algebraic denominator cancellation and earlier
 ratio lemmas with Rocq Stdlib Field, Ring, Psatz and Lra tactics.
 Library reuse: Stdlib rational-function simplification and order; these
 are reusable scalar corollaries, not a duplicate conditional-event engine.
 Boundary: Exact deterministic conditional-ratio algebra; not distribution
 theory, independent Monte Carlo replicates, binomial conditional coverage,
 or empirical population admission calibration.
*)
Theorem conditional_ratio_one_implies_equal_masses: forall j p, 0<p -> conditional_ratio j p=1 -> j=p.
Proof.
  intros j p Hp H; pose proof (conditional_ratio_cancel j p Hp); nra.
Qed.

(** [conditional_ratio_zero_implies_zero_joint] (theorem).
 Mathematical meaning: A zero conditional probability within a positive event implies zero intersection mass.
 Exact proposition: forall j p, 0<p -> conditional_ratio j p=0 -> j=0.
 Premises and side conditions: Conditional rates are used only under the
 explicitly stated positive conditioning mass and signs/order of joint
 masses. Division by zero is never interpreted as an event probability;
 real-algebra theorems do not require or imply Gaussianity.
 Proof/definition method: Algebraic denominator cancellation and earlier
 ratio lemmas with Rocq Stdlib Field, Ring, Psatz and Lra tactics.
 Library reuse: Stdlib rational-function simplification and order; these
 are reusable scalar corollaries, not a duplicate conditional-event engine.
 Boundary: Exact deterministic conditional-ratio algebra; not distribution
 theory, independent Monte Carlo replicates, binomial conditional coverage,
 or empirical population admission calibration.
*)
Theorem conditional_ratio_zero_implies_zero_joint: forall j p, 0<p -> conditional_ratio j p=0 -> j=0.
Proof.
  intros j p Hp H; pose proof (conditional_ratio_cancel j p Hp); nra.
Qed.

(** [conditional_ratio_half_iff] (theorem).
 Mathematical meaning: Passing among exactly half of those conditioned is equivalent to twice the intersection mass equalling total conditioning mass.
 Exact proposition: forall j p, 0<p -> (conditional_ratio j p=1/2 <-> 2*j=p).
 Premises and side conditions: Conditional rates are used only under the
 explicitly stated positive conditioning mass and signs/order of joint
 masses. Division by zero is never interpreted as an event probability;
 real-algebra theorems do not require or imply Gaussianity.
 Proof/definition method: Algebraic denominator cancellation and earlier
 ratio lemmas with Rocq Stdlib Field, Ring, Psatz and Lra tactics.
 Library reuse: Stdlib rational-function simplification and order; these
 are reusable scalar corollaries, not a duplicate conditional-event engine.
 Boundary: Exact deterministic conditional-ratio algebra; not distribution
 theory, independent Monte Carlo replicates, binomial conditional coverage,
 or empirical population admission calibration.
*)
Theorem conditional_ratio_half_iff: forall j p, 0<p -> (conditional_ratio j p=1/2 <-> 2*j=p).
Proof.
  intros j p Hp. pose proof (conditional_ratio_cancel j p Hp) as Hc. split; intro H; nra.
Qed.

(** [conditional_ratio_at_least_half] (theorem).
 Mathematical meaning: At least half of a conditioning group pass exactly when twice the intersection mass exceeds the group mass.
 Exact proposition: forall j p, 0<p -> (1/2<=conditional_ratio j p <-> p<=2*j).
 Premises and side conditions: Conditional rates are used only under the
 explicitly stated positive conditioning mass and signs/order of joint
 masses. Division by zero is never interpreted as an event probability;
 real-algebra theorems do not require or imply Gaussianity.
 Proof/definition method: Algebraic denominator cancellation and earlier
 ratio lemmas with Rocq Stdlib Field, Ring, Psatz and Lra tactics.
 Library reuse: Stdlib rational-function simplification and order; these
 are reusable scalar corollaries, not a duplicate conditional-event engine.
 Boundary: Exact deterministic conditional-ratio algebra; not distribution
 theory, independent Monte Carlo replicates, binomial conditional coverage,
 or empirical population admission calibration.
*)
Theorem conditional_ratio_at_least_half: forall j p, 0<p -> (1/2<=conditional_ratio j p <-> p<=2*j).
Proof.
  intros j p Hp. pose proof (conditional_ratio_cancel j p Hp) as Hc. split; intro H; nra.
Qed.

(** [conditional_ratio_at_most_half] (theorem).
 Mathematical meaning: At most half of a conditioning group pass exactly when twice the joint mass is bounded by the group mass.
 Exact proposition: forall j p, 0<p -> (conditional_ratio j p<=1/2 <-> 2*j<=p).
 Premises and side conditions: Conditional rates are used only under the
 explicitly stated positive conditioning mass and signs/order of joint
 masses. Division by zero is never interpreted as an event probability;
 real-algebra theorems do not require or imply Gaussianity.
 Proof/definition method: Algebraic denominator cancellation and earlier
 ratio lemmas with Rocq Stdlib Field, Ring, Psatz and Lra tactics.
 Library reuse: Stdlib rational-function simplification and order; these
 are reusable scalar corollaries, not a duplicate conditional-event engine.
 Boundary: Exact deterministic conditional-ratio algebra; not distribution
 theory, independent Monte Carlo replicates, binomial conditional coverage,
 or empirical population admission calibration.
*)
Theorem conditional_ratio_at_most_half: forall j p, 0<p -> (conditional_ratio j p<=1/2 <-> 2*j<=p).
Proof.
  intros j p Hp. pose proof (conditional_ratio_cancel j p Hp) as Hc. split; intro H; nra.
Qed.

(** [conditional_ratio_numerator_additive] (theorem).
 Mathematical meaning: Conditional rates are additive over algebraically disjoint intersection contributions.
 Exact proposition: forall a b p, 0<p -> conditional_ratio (a+b) p=conditional_ratio a p+conditional_ratio b p.
 Premises and side conditions: Conditional rates are used only under the
 explicitly stated positive conditioning mass and signs/order of joint
 masses. Division by zero is never interpreted as an event probability;
 real-algebra theorems do not require or imply Gaussianity.
 Proof/definition method: Algebraic denominator cancellation and earlier
 ratio lemmas with Rocq Stdlib Field, Ring, Psatz and Lra tactics.
 Library reuse: Stdlib rational-function simplification and order; these
 are reusable scalar corollaries, not a duplicate conditional-event engine.
 Boundary: Exact deterministic conditional-ratio algebra; not distribution
 theory, independent Monte Carlo replicates, binomial conditional coverage,
 or empirical population admission calibration.
*)
Theorem conditional_ratio_numerator_additive: forall a b p, 0<p -> conditional_ratio (a+b) p=conditional_ratio a p+conditional_ratio b p.
Proof.
  intros a b p Hp; unfold conditional_ratio; field; lra.
Qed.

(** [conditional_ratio_numerator_homogeneous] (theorem).
 Mathematical meaning: Scaling the intersection numerator scales the conditional rate by the same factor.
 Exact proposition: forall a j p, 0<p -> conditional_ratio (a*j) p=a*conditional_ratio j p.
 Premises and side conditions: Conditional rates are used only under the
 explicitly stated positive conditioning mass and signs/order of joint
 masses. Division by zero is never interpreted as an event probability;
 real-algebra theorems do not require or imply Gaussianity.
 Proof/definition method: Algebraic denominator cancellation and earlier
 ratio lemmas with Rocq Stdlib Field, Ring, Psatz and Lra tactics.
 Library reuse: Stdlib rational-function simplification and order; these
 are reusable scalar corollaries, not a duplicate conditional-event engine.
 Boundary: Exact deterministic conditional-ratio algebra; not distribution
 theory, independent Monte Carlo replicates, binomial conditional coverage,
 or empirical population admission calibration.
*)
Theorem conditional_ratio_numerator_homogeneous: forall a j p, 0<p -> conditional_ratio (a*j) p=a*conditional_ratio j p.
Proof.
  intros a j p Hp; unfold conditional_ratio; field; lra.
Qed.

(** [conditional_ratio_common_scale_invariant] (theorem).
 Mathematical meaning: Multiplying both a joint mass and its conditioning mass by a positive weight leaves conditional probability unchanged.
 Exact proposition: forall t j p, 0<t -> 0<p -> conditional_ratio (t*j) (t*p)=conditional_ratio j p.
 Premises and side conditions: Conditional rates are used only under the
 explicitly stated positive conditioning mass and signs/order of joint
 masses. Division by zero is never interpreted as an event probability;
 real-algebra theorems do not require or imply Gaussianity.
 Proof/definition method: Algebraic denominator cancellation and earlier
 ratio lemmas with Rocq Stdlib Field, Ring, Psatz and Lra tactics.
 Library reuse: Stdlib rational-function simplification and order; these
 are reusable scalar corollaries, not a duplicate conditional-event engine.
 Boundary: Exact deterministic conditional-ratio algebra; not distribution
 theory, independent Monte Carlo replicates, binomial conditional coverage,
 or empirical population admission calibration.
*)
Theorem conditional_ratio_common_scale_invariant: forall t j p, 0<t -> 0<p -> conditional_ratio (t*j) (t*p)=conditional_ratio j p.
Proof.
  intros t j p Ht Hp; unfold conditional_ratio; field; nra.
Qed.

(** [conditional_ratio_same_denom_difference] (theorem).
 Mathematical meaning: At a fixed positive conditioning mass, the difference of conditional probabilities is the joint-mass difference divided by the denominator.
 Exact proposition: forall a b p, 0<p -> conditional_ratio a p-conditional_ratio b p=(a-b)/p.
 Premises and side conditions: Conditional rates are used only under the
 explicitly stated positive conditioning mass and signs/order of joint
 masses. Division by zero is never interpreted as an event probability;
 real-algebra theorems do not require or imply Gaussianity.
 Proof/definition method: Algebraic denominator cancellation and earlier
 ratio lemmas with Rocq Stdlib Field, Ring, Psatz and Lra tactics.
 Library reuse: Stdlib rational-function simplification and order; these
 are reusable scalar corollaries, not a duplicate conditional-event engine.
 Boundary: Exact deterministic conditional-ratio algebra; not distribution
 theory, independent Monte Carlo replicates, binomial conditional coverage,
 or empirical population admission calibration.
*)
Theorem conditional_ratio_same_denom_difference: forall a b p, 0<p -> conditional_ratio a p-conditional_ratio b p=(a-b)/p.
Proof.
  intros a b p Hp; unfold conditional_ratio; field; lra.
Qed.

(** [conditional_ratio_denom_difference] (theorem).
 Mathematical meaning: For a fixed joint mass, changing the conditioning denominator has an exact rational sensitivity formula.
 Exact proposition: forall j p q, 0<p -> 0<q -> conditional_ratio j p-conditional_ratio j q=j*(q-p)/(p*q).
 Premises and side conditions: Conditional rates are used only under the
 explicitly stated positive conditioning mass and signs/order of joint
 masses. Division by zero is never interpreted as an event probability;
 real-algebra theorems do not require or imply Gaussianity.
 Proof/definition method: Algebraic denominator cancellation and earlier
 ratio lemmas with Rocq Stdlib Field, Ring, Psatz and Lra tactics.
 Library reuse: Stdlib rational-function simplification and order; these
 are reusable scalar corollaries, not a duplicate conditional-event engine.
 Boundary: Exact deterministic conditional-ratio algebra; not distribution
 theory, independent Monte Carlo replicates, binomial conditional coverage,
 or empirical population admission calibration.
*)
Theorem conditional_ratio_denom_difference: forall j p q, 0<p -> 0<q -> conditional_ratio j p-conditional_ratio j q=j*(q-p)/(p*q).
Proof.
  intros j p q Hp Hq; unfold conditional_ratio; field; nra.
Qed.

(** [conditional_ratio_numerator_monotone] (theorem).
 Mathematical meaning: Increasing joint mass while fixing positive conditioning mass cannot decrease conditional qualification.
 Exact proposition: forall a b p, 0<p -> a<=b -> conditional_ratio a p<=conditional_ratio b p.
 Premises and side conditions: Conditional rates are used only under the
 explicitly stated positive conditioning mass and signs/order of joint
 masses. Division by zero is never interpreted as an event probability;
 real-algebra theorems do not require or imply Gaussianity.
 Proof/definition method: Algebraic denominator cancellation and earlier
 ratio lemmas with Rocq Stdlib Field, Ring, Psatz and Lra tactics.
 Library reuse: Stdlib rational-function simplification and order; these
 are reusable scalar corollaries, not a duplicate conditional-event engine.
 Boundary: Exact deterministic conditional-ratio algebra; not distribution
 theory, independent Monte Carlo replicates, binomial conditional coverage,
 or empirical population admission calibration.
*)
Theorem conditional_ratio_numerator_monotone: forall a b p, 0<p -> a<=b -> conditional_ratio a p<=conditional_ratio b p.
Proof.
  intros a b p Hp Hab. pose proof (conditional_ratio_cancel a p Hp) as Ha. pose proof (conditional_ratio_cancel b p Hp) as Hb. nra.
Qed.

(** [conditional_ratio_numerator_strict] (theorem).
 Mathematical meaning: A strict increase in intersection mass strictly increases the conditional rate when conditioning mass stays fixed.
 Exact proposition: forall a b p, 0<p -> a<b -> conditional_ratio a p<conditional_ratio b p.
 Premises and side conditions: Conditional rates are used only under the
 explicitly stated positive conditioning mass and signs/order of joint
 masses. Division by zero is never interpreted as an event probability;
 real-algebra theorems do not require or imply Gaussianity.
 Proof/definition method: Algebraic denominator cancellation and earlier
 ratio lemmas with Rocq Stdlib Field, Ring, Psatz and Lra tactics.
 Library reuse: Stdlib rational-function simplification and order; these
 are reusable scalar corollaries, not a duplicate conditional-event engine.
 Boundary: Exact deterministic conditional-ratio algebra; not distribution
 theory, independent Monte Carlo replicates, binomial conditional coverage,
 or empirical population admission calibration.
*)
Theorem conditional_ratio_numerator_strict: forall a b p, 0<p -> a<b -> conditional_ratio a p<conditional_ratio b p.
Proof.
  intros a b p Hp Hab. pose proof (conditional_ratio_cancel a p Hp) as Ha. pose proof (conditional_ratio_cancel b p Hp) as Hb. nra.
Qed.

(** [conditional_ratio_denom_antitone] (theorem).
 Mathematical meaning: For a fixed nonnegative joint mass, enlarging the conditioning group cannot increase the conditional rate.
 Exact proposition: forall j p q, 0<=j -> 0<p -> p<=q -> conditional_ratio j q<=conditional_ratio j p.
 Premises and side conditions: Conditional rates are used only under the
 explicitly stated positive conditioning mass and signs/order of joint
 masses. Division by zero is never interpreted as an event probability;
 real-algebra theorems do not require or imply Gaussianity.
 Proof/definition method: Algebraic denominator cancellation and earlier
 ratio lemmas with Rocq Stdlib Field, Ring, Psatz and Lra tactics.
 Library reuse: Stdlib rational-function simplification and order; these
 are reusable scalar corollaries, not a duplicate conditional-event engine.
 Boundary: Exact deterministic conditional-ratio algebra; not distribution
 theory, independent Monte Carlo replicates, binomial conditional coverage,
 or empirical population admission calibration.
*)
Theorem conditional_ratio_denom_antitone: forall j p q, 0<=j -> 0<p -> p<=q -> conditional_ratio j q<=conditional_ratio j p.
Proof.
  intros j p q Hj Hp Hpq. assert (Hq:0<q) by lra. pose proof (conditional_ratio_denom_difference j p q Hp Hq) as Hd. assert (Hfrac:0<=j*(q-p)/(p*q)) by (unfold Rdiv; apply Rmult_le_pos; [nra|left; apply Rinv_0_lt_compat; nra]). lra.
Qed.

(** [conditional_ratio_denom_strict] (theorem).
 Mathematical meaning: Strictly enlarging a positive conditioning set strictly lowers its nonzero joint fraction.
 Exact proposition: forall j p q, 0<j -> 0<p -> p<q -> conditional_ratio j q<conditional_ratio j p.
 Premises and side conditions: Conditional rates are used only under the
 explicitly stated positive conditioning mass and signs/order of joint
 masses. Division by zero is never interpreted as an event probability;
 real-algebra theorems do not require or imply Gaussianity.
 Proof/definition method: Algebraic denominator cancellation and earlier
 ratio lemmas with Rocq Stdlib Field, Ring, Psatz and Lra tactics.
 Library reuse: Stdlib rational-function simplification and order; these
 are reusable scalar corollaries, not a duplicate conditional-event engine.
 Boundary: Exact deterministic conditional-ratio algebra; not distribution
 theory, independent Monte Carlo replicates, binomial conditional coverage,
 or empirical population admission calibration.
*)
Theorem conditional_ratio_denom_strict: forall j p q, 0<j -> 0<p -> p<q -> conditional_ratio j q<conditional_ratio j p.
Proof.
  intros j p q Hj Hp Hpq. assert (Hq:0<q) by lra. pose proof (conditional_ratio_denom_difference j p q Hp Hq) as Hd. assert (Hfrac:0<j*(q-p)/(p*q)) by (unfold Rdiv; apply Rmult_lt_0_compat; [nra|apply Rinv_0_lt_compat; nra]). lra.
Qed.

(** [conditional_ratio_rate_complement_monotone] (theorem).
 Mathematical meaning: Increasing the intersection rate decreases its complement within a fixed positive denominator.
 Exact proposition: forall a b p, 0<p -> a<=b -> conditional_ratio (p-b) p<=conditional_ratio (p-a) p.
 Premises and side conditions: Conditional rates are used only under the
 explicitly stated positive conditioning mass and signs/order of joint
 masses. Division by zero is never interpreted as an event probability;
 real-algebra theorems do not require or imply Gaussianity.
 Proof/definition method: Algebraic denominator cancellation and earlier
 ratio lemmas with Rocq Stdlib Field, Ring, Psatz and Lra tactics.
 Library reuse: Stdlib rational-function simplification and order; these
 are reusable scalar corollaries, not a duplicate conditional-event engine.
 Boundary: Exact deterministic conditional-ratio algebra; not distribution
 theory, independent Monte Carlo replicates, binomial conditional coverage,
 or empirical population admission calibration.
*)
Theorem conditional_ratio_rate_complement_monotone: forall a b p, 0<p -> a<=b -> conditional_ratio (p-b) p<=conditional_ratio (p-a) p.
Proof.
  intros a b p Hp Hab. apply conditional_ratio_numerator_monotone; lra.
Qed.

(** [conditional_ratio_rate_complement_strict] (theorem).
 Mathematical meaning: A strict increase in passed joint mass strictly reduces the conditional failure rate.
 Exact proposition: forall a b p, 0<p -> a<b -> conditional_ratio (p-b) p<conditional_ratio (p-a) p.
 Premises and side conditions: Conditional rates are used only under the
 explicitly stated positive conditioning mass and signs/order of joint
 masses. Division by zero is never interpreted as an event probability;
 real-algebra theorems do not require or imply Gaussianity.
 Proof/definition method: Algebraic denominator cancellation and earlier
 ratio lemmas with Rocq Stdlib Field, Ring, Psatz and Lra tactics.
 Library reuse: Stdlib rational-function simplification and order; these
 are reusable scalar corollaries, not a duplicate conditional-event engine.
 Boundary: Exact deterministic conditional-ratio algebra; not distribution
 theory, independent Monte Carlo replicates, binomial conditional coverage,
 or empirical population admission calibration.
*)
Theorem conditional_ratio_rate_complement_strict: forall a b p, 0<p -> a<b -> conditional_ratio (p-b) p<conditional_ratio (p-a) p.
Proof.
  intros a b p Hp Hab. apply conditional_ratio_numerator_strict; lra.
Qed.

(** [conditional_ratio_cross_product_identity] (theorem).
 Mathematical meaning: Conditional ratio equality is equivalent to equality of the two cross-products of positive denominators.
 Exact proposition: forall a b p q, 0<p -> 0<q -> (conditional_ratio a p=conditional_ratio b q <-> a*q=b*p).
 Premises and side conditions: Conditional rates are used only under the
 explicitly stated positive conditioning mass and signs/order of joint
 masses. Division by zero is never interpreted as an event probability;
 real-algebra theorems do not require or imply Gaussianity.
 Proof/definition method: Algebraic denominator cancellation and earlier
 ratio lemmas with Rocq Stdlib Field, Ring, Psatz and Lra tactics.
 Library reuse: Stdlib rational-function simplification and order; these
 are reusable scalar corollaries, not a duplicate conditional-event engine.
 Boundary: Exact deterministic conditional-ratio algebra; not distribution
 theory, independent Monte Carlo replicates, binomial conditional coverage,
 or empirical population admission calibration.
*)
Theorem conditional_ratio_cross_product_identity: forall a b p q, 0<p -> 0<q -> (conditional_ratio a p=conditional_ratio b q <-> a*q=b*p).
Proof.
  intros a b p q Hp Hq. pose proof (conditional_ratio_cancel a p Hp) as Ha. pose proof (conditional_ratio_cancel b q Hq) as Hb. split; intro H. - subst; nra. - assert (Hpq:0<p*q) by nra. nra.
Qed.

(** [conditional_ratio_joint_product_reconstruction] (theorem).
 Mathematical meaning: Knowing a conditional rate and a positive conditioning mass determines the joint probability exactly.
 Exact proposition: forall j p q, 0<p -> conditional_ratio j p=q -> j=q*p.
 Premises and side conditions: Conditional rates are used only under the
 explicitly stated positive conditioning mass and signs/order of joint
 masses. Division by zero is never interpreted as an event probability;
 real-algebra theorems do not require or imply Gaussianity.
 Proof/definition method: Algebraic denominator cancellation and earlier
 ratio lemmas with Rocq Stdlib Field, Ring, Psatz and Lra tactics.
 Library reuse: Stdlib rational-function simplification and order; these
 are reusable scalar corollaries, not a duplicate conditional-event engine.
 Boundary: Exact deterministic conditional-ratio algebra; not distribution
 theory, independent Monte Carlo replicates, binomial conditional coverage,
 or empirical population admission calibration.
*)
Theorem conditional_ratio_joint_product_reconstruction: forall j p q, 0<p -> conditional_ratio j p=q -> j=q*p.
Proof.
  intros j p q Hp Hq. pose proof (conditional_ratio_cancel j p Hp) as Hc. rewrite Hq in Hc; lra.
Qed.

(** [conditional_ratio_threeway_chain] (theorem).
 Mathematical meaning: A nested conditional fraction factors through any positive intermediate event mass.
 Exact proposition: forall a b c, 0<b -> 0<c -> conditional_ratio a c = conditional_ratio a b * conditional_ratio b c.
 Premises and side conditions: Conditional rates are used only under the
 explicitly stated positive conditioning mass and signs/order of joint
 masses. Division by zero is never interpreted as an event probability;
 real-algebra theorems do not require or imply Gaussianity.
 Proof/definition method: Algebraic denominator cancellation and earlier
 ratio lemmas with Rocq Stdlib Field, Ring, Psatz and Lra tactics.
 Library reuse: Stdlib rational-function simplification and order; these
 are reusable scalar corollaries, not a duplicate conditional-event engine.
 Boundary: Exact deterministic conditional-ratio algebra; not distribution
 theory, independent Monte Carlo replicates, binomial conditional coverage,
 or empirical population admission calibration.
*)
Theorem conditional_ratio_threeway_chain: forall a b c, 0<b -> 0<c -> conditional_ratio a c = conditional_ratio a b * conditional_ratio b c.
Proof.
  intros a b c Hb Hc; unfold conditional_ratio; field; nra.
Qed.

(** [conditional_ratio_rescaling_equal_relative] (theorem).
 Mathematical meaning: If both a joint mass and a conditioning mass change by the same positive multiplicative factor, their conditional probability is unchanged.
 Exact proposition: forall t u j p, 0<t -> 0<u -> 0<p -> conditional_ratio (t*u*j) (t*u*p)=conditional_ratio j p.
 Premises and side conditions: Conditional rates are used only under the
 explicitly stated positive conditioning mass and signs/order of joint
 masses. Division by zero is never interpreted as an event probability;
 real-algebra theorems do not require or imply Gaussianity.
 Proof/definition method: Algebraic denominator cancellation and earlier
 ratio lemmas with Rocq Stdlib Field, Ring, Psatz and Lra tactics.
 Library reuse: Stdlib rational-function simplification and order; these
 are reusable scalar corollaries, not a duplicate conditional-event engine.
 Boundary: Exact deterministic conditional-ratio algebra; not distribution
 theory, independent Monte Carlo replicates, binomial conditional coverage,
 or empirical population admission calibration.
*)
Theorem conditional_ratio_rescaling_equal_relative: forall t u j p, 0<t -> 0<u -> 0<p -> conditional_ratio (t*u*j) (t*u*p)=conditional_ratio j p.
Proof.
  intros t u j p Ht Hu Hp. unfold conditional_ratio; field; nra.
Qed.

