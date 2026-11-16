(** Module: TwoRatePrecision.v
 Purpose: Quantify heterogeneity, expected counts and Bernoulli variance
 across different test pass rates and unequal simulation replicate sizes.
 Mathematical representation: Real event rates p,q and nonnegative trial
 sizes n,m; contrasts and count moments are the canonical low-order
 expressions from SamplingPrecision without reinventing a probability law.
 Explicit hypotheses: Rate ranges and nonnegative counts appear in each
 inequality; algebraic equalities hold for arbitrary real arguments.
 Library use: Rocq Stdlib Reals, Ring, Field, Lra, Psatz; reuse
 SamplingPrecision for variance definitions and sharp bounds.
 Limitations: Moment/precision identities for hypothetical independent
 Bernoulli models, NOT a proof that PRNG outputs are independent nor
 that binomial distributions, Wilson coverage or Gaussian tails hold.
 Reproduction: scripts/compile_rocq.sh, kernel Rocq 9.2.
 AI disclosure: AI assisted comments and proofs, subject to Rocq checking.
*)
From Stdlib Require Import Reals Lra Psatz Ring Field.
Require Import SamplingPrecision.
Open Scope R_scope.

(** [rate_gap] (definition).
 Mathematical meaning: The oriented difference of two marginal success probabilities.
 Exact expression: Reuses the canonical real-valued Bernoulli moment
 quantities and trial weights already established in SamplingPrecision.
 Premises and side conditions: A statistical probability interpretation
 requires 0<=p,q<=1, and nonnegative finite sample counts as applicable.
 Proof/definition method: Ordinary real scalar arithmetic and
 existing Bernoulli moment definitions; no bespoke probability package.
 Library reuse: SamplingPrecision and Rocq Stdlib Reals, Ring, Psatz.
 Boundary: This does not construct random variables or show independence.
*)
Definition rate_gap (p q:R) : R := p-q.

(** [rate_var] (definition).
 Mathematical meaning: Formal variance of a contrast between two independent one-trial indicators.
 Exact expression: Reuses the canonical real-valued Bernoulli moment
 quantities and trial weights already established in SamplingPrecision.
 Premises and side conditions: A statistical probability interpretation
 requires 0<=p,q<=1, and nonnegative finite sample counts as applicable.
 Proof/definition method: Ordinary real scalar arithmetic and
 existing Bernoulli moment definitions; no bespoke probability package.
 Library reuse: SamplingPrecision and Rocq Stdlib Reals, Ring, Psatz.
 Boundary: This does not construct random variables or show independence.
*)
Definition rate_var (p q:R) : R := sampling_bernoulli_variance p+sampling_bernoulli_variance q.

(** [rate_count] (definition).
 Mathematical meaning: Combined expected successes across two batches with potentially different success rates.
 Exact expression: Reuses the canonical real-valued Bernoulli moment
 quantities and trial weights already established in SamplingPrecision.
 Premises and side conditions: A statistical probability interpretation
 requires 0<=p,q<=1, and nonnegative finite sample counts as applicable.
 Proof/definition method: Ordinary real scalar arithmetic and
 existing Bernoulli moment definitions; no bespoke probability package.
 Library reuse: SamplingPrecision and Rocq Stdlib Reals, Ring, Psatz.
 Boundary: This does not construct random variables or show independence.
*)
Definition rate_count (n m p q:R) : R := n*p+m*q.

(** [rate_count_variance] (definition).
 Mathematical meaning: Formal sum of two rate-dependent binomial-count variances under an independent-draw model.
 Exact expression: Reuses the canonical real-valued Bernoulli moment
 quantities and trial weights already established in SamplingPrecision.
 Premises and side conditions: A statistical probability interpretation
 requires 0<=p,q<=1, and nonnegative finite sample counts as applicable.
 Proof/definition method: Ordinary real scalar arithmetic and
 existing Bernoulli moment definitions; no bespoke probability package.
 Library reuse: SamplingPrecision and Rocq Stdlib Reals, Ring, Psatz.
 Boundary: This does not construct random variables or show independence.
*)
Definition rate_count_variance (n m p q:R) : R := n*sampling_bernoulli_variance p+m*sampling_bernoulli_variance q.

(** [rate_gap_antisym] (theorem).
 Mathematical meaning: Swapping event rates reverses the signed difference.
 Exact proposition: The displayed universal claim is about exact real
 Bernoulli-rate/moment algebra supporting simulation count diagnostics.
 Premises and side conditions: Every required probability range and
 sample-count ordering appears explicitly in this proposition. The
 conclusion never assumes distributional validity from sample output.
 Proof/definition method: Rewrite the reused Bernoulli expressions and
 apply maintained ring, field, and ordered-real solvers or previously
 proven SamplingPrecision bounds; no new distribution algorithm.
 Library reuse: SamplingPrecision, Reals, Ring, Lra, Psatz and Field.
 Boundary: Algebraic variance and expectation *targets* for hypothetical
 independent Bernoulli samples; binomial distribution and coverage are
 separate theorems, and no empirical IQ model is validated.
*)
Theorem rate_gap_antisym : forall p q, rate_gap p q = -rate_gap q p.
Proof.
  intros; unfold rate_gap; ring.
Qed.

(** [rate_gap_zero_iff] (theorem).
 Mathematical meaning: The gap is zero exactly when both rates agree.
 Exact proposition: The displayed universal claim is about exact real
 Bernoulli-rate/moment algebra supporting simulation count diagnostics.
 Premises and side conditions: Every required probability range and
 sample-count ordering appears explicitly in this proposition. The
 conclusion never assumes distributional validity from sample output.
 Proof/definition method: Rewrite the reused Bernoulli expressions and
 apply maintained ring, field, and ordered-real solvers or previously
 proven SamplingPrecision bounds; no new distribution algorithm.
 Library reuse: SamplingPrecision, Reals, Ring, Lra, Psatz and Field.
 Boundary: Algebraic variance and expectation *targets* for hypothetical
 independent Bernoulli samples; binomial distribution and coverage are
 separate theorems, and no empirical IQ model is validated.
*)
Theorem rate_gap_zero_iff : forall p q, rate_gap p q=0 <-> p=q.
Proof.
  intros; unfold rate_gap; split; intro H; lra.
Qed.

(** [rate_gap_transitivity] (theorem).
 Mathematical meaning: Differences in selection rates telescope across three populations.
 Exact proposition: The displayed universal claim is about exact real
 Bernoulli-rate/moment algebra supporting simulation count diagnostics.
 Premises and side conditions: Every required probability range and
 sample-count ordering appears explicitly in this proposition. The
 conclusion never assumes distributional validity from sample output.
 Proof/definition method: Rewrite the reused Bernoulli expressions and
 apply maintained ring, field, and ordered-real solvers or previously
 proven SamplingPrecision bounds; no new distribution algorithm.
 Library reuse: SamplingPrecision, Reals, Ring, Lra, Psatz and Field.
 Boundary: Algebraic variance and expectation *targets* for hypothetical
 independent Bernoulli samples; binomial distribution and coverage are
 separate theorems, and no empirical IQ model is validated.
*)
Theorem rate_gap_transitivity : forall p q r, rate_gap p r = rate_gap p q+rate_gap q r.
Proof.
  intros; unfold rate_gap; ring.
Qed.

(** [rate_gap_complement] (theorem).
 Mathematical meaning: Complementary failure rates reverse success-rate differences.
 Exact proposition: The displayed universal claim is about exact real
 Bernoulli-rate/moment algebra supporting simulation count diagnostics.
 Premises and side conditions: Every required probability range and
 sample-count ordering appears explicitly in this proposition. The
 conclusion never assumes distributional validity from sample output.
 Proof/definition method: Rewrite the reused Bernoulli expressions and
 apply maintained ring, field, and ordered-real solvers or previously
 proven SamplingPrecision bounds; no new distribution algorithm.
 Library reuse: SamplingPrecision, Reals, Ring, Lra, Psatz and Field.
 Boundary: Algebraic variance and expectation *targets* for hypothetical
 independent Bernoulli samples; binomial distribution and coverage are
 separate theorems, and no empirical IQ model is validated.
*)
Theorem rate_gap_complement : forall p q, rate_gap (1-p) (1-q) = -rate_gap p q.
Proof.
  intros; unfold rate_gap; ring.
Qed.

(** [rate_gap_translation] (theorem).
 Mathematical meaning: Adding a common shift does not change the rate contrast.
 Exact proposition: The displayed universal claim is about exact real
 Bernoulli-rate/moment algebra supporting simulation count diagnostics.
 Premises and side conditions: Every required probability range and
 sample-count ordering appears explicitly in this proposition. The
 conclusion never assumes distributional validity from sample output.
 Proof/definition method: Rewrite the reused Bernoulli expressions and
 apply maintained ring, field, and ordered-real solvers or previously
 proven SamplingPrecision bounds; no new distribution algorithm.
 Library reuse: SamplingPrecision, Reals, Ring, Lra, Psatz and Field.
 Boundary: Algebraic variance and expectation *targets* for hypothetical
 independent Bernoulli samples; binomial distribution and coverage are
 separate theorems, and no empirical IQ model is validated.
*)
Theorem rate_gap_translation : forall p q t, rate_gap (p+t) (q+t) = rate_gap p q.
Proof.
  intros; unfold rate_gap; ring.
Qed.

(** [rate_gap_scale] (theorem).
 Mathematical meaning: Changing the unit of both rates scales the contrast.
 Exact proposition: The displayed universal claim is about exact real
 Bernoulli-rate/moment algebra supporting simulation count diagnostics.
 Premises and side conditions: Every required probability range and
 sample-count ordering appears explicitly in this proposition. The
 conclusion never assumes distributional validity from sample output.
 Proof/definition method: Rewrite the reused Bernoulli expressions and
 apply maintained ring, field, and ordered-real solvers or previously
 proven SamplingPrecision bounds; no new distribution algorithm.
 Library reuse: SamplingPrecision, Reals, Ring, Lra, Psatz and Field.
 Boundary: Algebraic variance and expectation *targets* for hypothetical
 independent Bernoulli samples; binomial distribution and coverage are
 separate theorems, and no empirical IQ model is validated.
*)
Theorem rate_gap_scale : forall p q t, rate_gap (t*p) (t*q)=t*rate_gap p q.
Proof.
  intros; unfold rate_gap; ring.
Qed.

(** [rate_gap_nonnegative_iff] (theorem).
 Mathematical meaning: The sign of the gap exactly encodes the ordering of admission rates.
 Exact proposition: The displayed universal claim is about exact real
 Bernoulli-rate/moment algebra supporting simulation count diagnostics.
 Premises and side conditions: Every required probability range and
 sample-count ordering appears explicitly in this proposition. The
 conclusion never assumes distributional validity from sample output.
 Proof/definition method: Rewrite the reused Bernoulli expressions and
 apply maintained ring, field, and ordered-real solvers or previously
 proven SamplingPrecision bounds; no new distribution algorithm.
 Library reuse: SamplingPrecision, Reals, Ring, Lra, Psatz and Field.
 Boundary: Algebraic variance and expectation *targets* for hypothetical
 independent Bernoulli samples; binomial distribution and coverage are
 separate theorems, and no empirical IQ model is validated.
*)
Theorem rate_gap_nonnegative_iff : forall p q, 0<=rate_gap p q <-> q<=p.
Proof.
  intros; unfold rate_gap; split; intro H; lra.
Qed.

(** [rate_gap_strict_iff] (theorem).
 Mathematical meaning: Positive rate gaps precisely correspond to higher first-event probability.
 Exact proposition: The displayed universal claim is about exact real
 Bernoulli-rate/moment algebra supporting simulation count diagnostics.
 Premises and side conditions: Every required probability range and
 sample-count ordering appears explicitly in this proposition. The
 conclusion never assumes distributional validity from sample output.
 Proof/definition method: Rewrite the reused Bernoulli expressions and
 apply maintained ring, field, and ordered-real solvers or previously
 proven SamplingPrecision bounds; no new distribution algorithm.
 Library reuse: SamplingPrecision, Reals, Ring, Lra, Psatz and Field.
 Boundary: Algebraic variance and expectation *targets* for hypothetical
 independent Bernoulli samples; binomial distribution and coverage are
 separate theorems, and no empirical IQ model is validated.
*)
Theorem rate_gap_strict_iff : forall p q, 0<rate_gap p q <-> q<p.
Proof.
  intros; unfold rate_gap; split; intro H; lra.
Qed.

(** [rate_gap_sum_zero] (theorem).
 Mathematical meaning: Oppositely oriented rate differences cancel.
 Exact proposition: The displayed universal claim is about exact real
 Bernoulli-rate/moment algebra supporting simulation count diagnostics.
 Premises and side conditions: Every required probability range and
 sample-count ordering appears explicitly in this proposition. The
 conclusion never assumes distributional validity from sample output.
 Proof/definition method: Rewrite the reused Bernoulli expressions and
 apply maintained ring, field, and ordered-real solvers or previously
 proven SamplingPrecision bounds; no new distribution algorithm.
 Library reuse: SamplingPrecision, Reals, Ring, Lra, Psatz and Field.
 Boundary: Algebraic variance and expectation *targets* for hypothetical
 independent Bernoulli samples; binomial distribution and coverage are
 separate theorems, and no empirical IQ model is validated.
*)
Theorem rate_gap_sum_zero : forall p q, rate_gap p q+rate_gap q p=0.
Proof.
  intros; unfold rate_gap; ring.
Qed.

(** [rate_gap_mix_reverse] (theorem).
 Mathematical meaning: A success-minus-failure contrast equals excess of the rate sum over one.
 Exact proposition: The displayed universal claim is about exact real
 Bernoulli-rate/moment algebra supporting simulation count diagnostics.
 Premises and side conditions: Every required probability range and
 sample-count ordering appears explicitly in this proposition. The
 conclusion never assumes distributional validity from sample output.
 Proof/definition method: Rewrite the reused Bernoulli expressions and
 apply maintained ring, field, and ordered-real solvers or previously
 proven SamplingPrecision bounds; no new distribution algorithm.
 Library reuse: SamplingPrecision, Reals, Ring, Lra, Psatz and Field.
 Boundary: Algebraic variance and expectation *targets* for hypothetical
 independent Bernoulli samples; binomial distribution and coverage are
 separate theorems, and no empirical IQ model is validated.
*)
Theorem rate_gap_mix_reverse : forall p q, rate_gap p (1-q)=p+q-1.
Proof.
  intros; unfold rate_gap; ring.
Qed.

(** [rate_gap_difference] (theorem).
 Mathematical meaning: The change in a rate gap equals the difference of individual rate shifts.
 Exact proposition: The displayed universal claim is about exact real
 Bernoulli-rate/moment algebra supporting simulation count diagnostics.
 Premises and side conditions: Every required probability range and
 sample-count ordering appears explicitly in this proposition. The
 conclusion never assumes distributional validity from sample output.
 Proof/definition method: Rewrite the reused Bernoulli expressions and
 apply maintained ring, field, and ordered-real solvers or previously
 proven SamplingPrecision bounds; no new distribution algorithm.
 Library reuse: SamplingPrecision, Reals, Ring, Lra, Psatz and Field.
 Boundary: Algebraic variance and expectation *targets* for hypothetical
 independent Bernoulli samples; binomial distribution and coverage are
 separate theorems, and no empirical IQ model is validated.
*)
Theorem rate_gap_difference : forall p q r s, rate_gap p q-rate_gap r s=(p-r)-(q-s).
Proof.
  intros; unfold rate_gap; ring.
Qed.

(** [rate_gap_count_balance] (theorem).
 Mathematical meaning: A common sample count scales the probability-gap numerator.
 Exact proposition: The displayed universal claim is about exact real
 Bernoulli-rate/moment algebra supporting simulation count diagnostics.
 Premises and side conditions: Every required probability range and
 sample-count ordering appears explicitly in this proposition. The
 conclusion never assumes distributional validity from sample output.
 Proof/definition method: Rewrite the reused Bernoulli expressions and
 apply maintained ring, field, and ordered-real solvers or previously
 proven SamplingPrecision bounds; no new distribution algorithm.
 Library reuse: SamplingPrecision, Reals, Ring, Lra, Psatz and Field.
 Boundary: Algebraic variance and expectation *targets* for hypothetical
 independent Bernoulli samples; binomial distribution and coverage are
 separate theorems, and no empirical IQ model is validated.
*)
Theorem rate_gap_count_balance : forall n p q, n*rate_gap p q=n*p-n*q.
Proof.
  intros; unfold rate_gap; ring.
Qed.

(** [rate_var_sym] (theorem).
 Mathematical meaning: The two-event Bernoulli contrast variance is symmetric in the two marginal rates.
 Exact proposition: The displayed universal claim is about exact real
 Bernoulli-rate/moment algebra supporting simulation count diagnostics.
 Premises and side conditions: Every required probability range and
 sample-count ordering appears explicitly in this proposition. The
 conclusion never assumes distributional validity from sample output.
 Proof/definition method: Rewrite the reused Bernoulli expressions and
 apply maintained ring, field, and ordered-real solvers or previously
 proven SamplingPrecision bounds; no new distribution algorithm.
 Library reuse: SamplingPrecision, Reals, Ring, Lra, Psatz and Field.
 Boundary: Algebraic variance and expectation *targets* for hypothetical
 independent Bernoulli samples; binomial distribution and coverage are
 separate theorems, and no empirical IQ model is validated.
*)
Theorem rate_var_sym : forall p q, rate_var p q=rate_var q p.
Proof.
  intros; unfold rate_var; ring.
Qed.

(** [rate_var_complement_left] (theorem).
 Mathematical meaning: Complementing only the first event does not change Bernoulli variance.
 Exact proposition: The displayed universal claim is about exact real
 Bernoulli-rate/moment algebra supporting simulation count diagnostics.
 Premises and side conditions: Every required probability range and
 sample-count ordering appears explicitly in this proposition. The
 conclusion never assumes distributional validity from sample output.
 Proof/definition method: Rewrite the reused Bernoulli expressions and
 apply maintained ring, field, and ordered-real solvers or previously
 proven SamplingPrecision bounds; no new distribution algorithm.
 Library reuse: SamplingPrecision, Reals, Ring, Lra, Psatz and Field.
 Boundary: Algebraic variance and expectation *targets* for hypothetical
 independent Bernoulli samples; binomial distribution and coverage are
 separate theorems, and no empirical IQ model is validated.
*)
Theorem rate_var_complement_left : forall p q, rate_var (1-p) q=rate_var p q.
Proof.
  intros; unfold rate_var,sampling_bernoulli_variance; ring.
Qed.

(** [rate_var_complement_right] (theorem).
 Mathematical meaning: Complementing only the second event preserves its Bernoulli variance contribution.
 Exact proposition: The displayed universal claim is about exact real
 Bernoulli-rate/moment algebra supporting simulation count diagnostics.
 Premises and side conditions: Every required probability range and
 sample-count ordering appears explicitly in this proposition. The
 conclusion never assumes distributional validity from sample output.
 Proof/definition method: Rewrite the reused Bernoulli expressions and
 apply maintained ring, field, and ordered-real solvers or previously
 proven SamplingPrecision bounds; no new distribution algorithm.
 Library reuse: SamplingPrecision, Reals, Ring, Lra, Psatz and Field.
 Boundary: Algebraic variance and expectation *targets* for hypothetical
 independent Bernoulli samples; binomial distribution and coverage are
 separate theorems, and no empirical IQ model is validated.
*)
Theorem rate_var_complement_right : forall p q, rate_var p (1-q)=rate_var p q.
Proof.
  intros; unfold rate_var,sampling_bernoulli_variance; ring.
Qed.

(** [rate_var_complement_both] (theorem).
 Mathematical meaning: Complementing both margins preserves total Bernoulli variability.
 Exact proposition: The displayed universal claim is about exact real
 Bernoulli-rate/moment algebra supporting simulation count diagnostics.
 Premises and side conditions: Every required probability range and
 sample-count ordering appears explicitly in this proposition. The
 conclusion never assumes distributional validity from sample output.
 Proof/definition method: Rewrite the reused Bernoulli expressions and
 apply maintained ring, field, and ordered-real solvers or previously
 proven SamplingPrecision bounds; no new distribution algorithm.
 Library reuse: SamplingPrecision, Reals, Ring, Lra, Psatz and Field.
 Boundary: Algebraic variance and expectation *targets* for hypothetical
 independent Bernoulli samples; binomial distribution and coverage are
 separate theorems, and no empirical IQ model is validated.
*)
Theorem rate_var_complement_both : forall p q, rate_var (1-p) (1-q)=rate_var p q.
Proof.
  intros; unfold rate_var,sampling_bernoulli_variance; ring.
Qed.

(** [rate_var_zero_endpoints] (theorem).
 Mathematical meaning: Two deterministic indicators, one impossible and one certain, have zero Bernoulli contrast variance.
 Exact proposition: The displayed universal claim is about exact real
 Bernoulli-rate/moment algebra supporting simulation count diagnostics.
 Premises and side conditions: Every required probability range and
 sample-count ordering appears explicitly in this proposition. The
 conclusion never assumes distributional validity from sample output.
 Proof/definition method: Rewrite the reused Bernoulli expressions and
 apply maintained ring, field, and ordered-real solvers or previously
 proven SamplingPrecision bounds; no new distribution algorithm.
 Library reuse: SamplingPrecision, Reals, Ring, Lra, Psatz and Field.
 Boundary: Algebraic variance and expectation *targets* for hypothetical
 independent Bernoulli samples; binomial distribution and coverage are
 separate theorems, and no empirical IQ model is validated.
*)
Theorem rate_var_zero_endpoints : rate_var 0 1=0.
Proof.
  unfold rate_var,sampling_bernoulli_variance; ring.
Qed.

(** [rate_var_equal_halves] (theorem).
 Mathematical meaning: Two balanced Bernoulli margins attain their maximal combined variance.
 Exact proposition: The displayed universal claim is about exact real
 Bernoulli-rate/moment algebra supporting simulation count diagnostics.
 Premises and side conditions: Every required probability range and
 sample-count ordering appears explicitly in this proposition. The
 conclusion never assumes distributional validity from sample output.
 Proof/definition method: Rewrite the reused Bernoulli expressions and
 apply maintained ring, field, and ordered-real solvers or previously
 proven SamplingPrecision bounds; no new distribution algorithm.
 Library reuse: SamplingPrecision, Reals, Ring, Lra, Psatz and Field.
 Boundary: Algebraic variance and expectation *targets* for hypothetical
 independent Bernoulli samples; binomial distribution and coverage are
 separate theorems, and no empirical IQ model is validated.
*)
Theorem rate_var_equal_halves : rate_var (1/2) (1/2)=1/2.
Proof.
  unfold rate_var,sampling_bernoulli_variance; field.
Qed.

(** [rate_var_nonnegative] (theorem).
 Mathematical meaning: The sum of two Bernoulli variances is nonnegative for admissible event rates.
 Exact proposition: The displayed universal claim is about exact real
 Bernoulli-rate/moment algebra supporting simulation count diagnostics.
 Premises and side conditions: Every required probability range and
 sample-count ordering appears explicitly in this proposition. The
 conclusion never assumes distributional validity from sample output.
 Proof/definition method: Rewrite the reused Bernoulli expressions and
 apply maintained ring, field, and ordered-real solvers or previously
 proven SamplingPrecision bounds; no new distribution algorithm.
 Library reuse: SamplingPrecision, Reals, Ring, Lra, Psatz and Field.
 Boundary: Algebraic variance and expectation *targets* for hypothetical
 independent Bernoulli samples; binomial distribution and coverage are
 separate theorems, and no empirical IQ model is validated.
*)
Theorem rate_var_nonnegative : forall p q, 0<=p -> p<=1 -> 0<=q -> q<=1 -> 0<=rate_var p q.
Proof.
  intros p q Hp Hpu Hq Hqu; unfold rate_var; pose proof (sampling_variance_nonnegative p Hp Hpu) as A; pose proof (sampling_variance_nonnegative q Hq Hqu) as B; lra.
Qed.

(** [rate_var_strict_if_first] (theorem).
 Mathematical meaning: One nondegenerate Bernoulli margin already makes the contrast variance positive.
 Exact proposition: The displayed universal claim is about exact real
 Bernoulli-rate/moment algebra supporting simulation count diagnostics.
 Premises and side conditions: Every required probability range and
 sample-count ordering appears explicitly in this proposition. The
 conclusion never assumes distributional validity from sample output.
 Proof/definition method: Rewrite the reused Bernoulli expressions and
 apply maintained ring, field, and ordered-real solvers or previously
 proven SamplingPrecision bounds; no new distribution algorithm.
 Library reuse: SamplingPrecision, Reals, Ring, Lra, Psatz and Field.
 Boundary: Algebraic variance and expectation *targets* for hypothetical
 independent Bernoulli samples; binomial distribution and coverage are
 separate theorems, and no empirical IQ model is validated.
*)
Theorem rate_var_strict_if_first : forall p q, 0<p -> p<1 -> 0<=q -> q<=1 -> 0<rate_var p q.
Proof.
  intros p q Hp Hpu Hq Hqu; unfold rate_var; pose proof (sampling_variance_strictly_positive p Hp Hpu) as A; pose proof (sampling_variance_nonnegative q Hq Hqu) as B; lra.
Qed.

(** [rate_var_max] (theorem).
 Mathematical meaning: The exact universal sum-of-two-Bernoulli-variances upper bound is one half.
 Exact proposition: The displayed universal claim is about exact real
 Bernoulli-rate/moment algebra supporting simulation count diagnostics.
 Premises and side conditions: Every required probability range and
 sample-count ordering appears explicitly in this proposition. The
 conclusion never assumes distributional validity from sample output.
 Proof/definition method: Rewrite the reused Bernoulli expressions and
 apply maintained ring, field, and ordered-real solvers or previously
 proven SamplingPrecision bounds; no new distribution algorithm.
 Library reuse: SamplingPrecision, Reals, Ring, Lra, Psatz and Field.
 Boundary: Algebraic variance and expectation *targets* for hypothetical
 independent Bernoulli samples; binomial distribution and coverage are
 separate theorems, and no empirical IQ model is validated.
*)
Theorem rate_var_max : forall p q, rate_var p q<=1/2.
Proof.
  intros p q; unfold rate_var; pose proof (sampling_variance_maximum p) as A; pose proof (sampling_variance_maximum q) as B; lra.
Qed.

(** [rate_var_midpoint_gap] (theorem).
 Mathematical meaning: The loss from maximal contrast precision is the sum of the squared deviations from balanced success rates.
 Exact proposition: The displayed universal claim is about exact real
 Bernoulli-rate/moment algebra supporting simulation count diagnostics.
 Premises and side conditions: Every required probability range and
 sample-count ordering appears explicitly in this proposition. The
 conclusion never assumes distributional validity from sample output.
 Proof/definition method: Rewrite the reused Bernoulli expressions and
 apply maintained ring, field, and ordered-real solvers or previously
 proven SamplingPrecision bounds; no new distribution algorithm.
 Library reuse: SamplingPrecision, Reals, Ring, Lra, Psatz and Field.
 Boundary: Algebraic variance and expectation *targets* for hypothetical
 independent Bernoulli samples; binomial distribution and coverage are
 separate theorems, and no empirical IQ model is validated.
*)
Theorem rate_var_midpoint_gap : forall p q, 1/2-rate_var p q=(p-1/2)*(p-1/2)+(q-1/2)*(q-1/2).
Proof.
  intros; unfold rate_var,sampling_bernoulli_variance; ring.
Qed.

(** [rate_var_shift_first] (theorem).
 Mathematical meaning: Changing the first marginal rate changes contrast variance by a sharp polynomial gap.
 Exact proposition: The displayed universal claim is about exact real
 Bernoulli-rate/moment algebra supporting simulation count diagnostics.
 Premises and side conditions: Every required probability range and
 sample-count ordering appears explicitly in this proposition. The
 conclusion never assumes distributional validity from sample output.
 Proof/definition method: Rewrite the reused Bernoulli expressions and
 apply maintained ring, field, and ordered-real solvers or previously
 proven SamplingPrecision bounds; no new distribution algorithm.
 Library reuse: SamplingPrecision, Reals, Ring, Lra, Psatz and Field.
 Boundary: Algebraic variance and expectation *targets* for hypothetical
 independent Bernoulli samples; binomial distribution and coverage are
 separate theorems, and no empirical IQ model is validated.
*)
Theorem rate_var_shift_first : forall p q r, rate_var r q-rate_var p q=(r-p)*(1-r-p).
Proof.
  intros; unfold rate_var,sampling_bernoulli_variance; ring.
Qed.

(** [rate_var_shift_second] (theorem).
 Mathematical meaning: Changing the second marginal gives the corresponding exact precision sensitivity.
 Exact proposition: The displayed universal claim is about exact real
 Bernoulli-rate/moment algebra supporting simulation count diagnostics.
 Premises and side conditions: Every required probability range and
 sample-count ordering appears explicitly in this proposition. The
 conclusion never assumes distributional validity from sample output.
 Proof/definition method: Rewrite the reused Bernoulli expressions and
 apply maintained ring, field, and ordered-real solvers or previously
 proven SamplingPrecision bounds; no new distribution algorithm.
 Library reuse: SamplingPrecision, Reals, Ring, Lra, Psatz and Field.
 Boundary: Algebraic variance and expectation *targets* for hypothetical
 independent Bernoulli samples; binomial distribution and coverage are
 separate theorems, and no empirical IQ model is validated.
*)
Theorem rate_var_shift_second : forall p q r, rate_var p r-rate_var p q=(r-q)*(1-r-q).
Proof.
  intros; unfold rate_var,sampling_bernoulli_variance; ring.
Qed.

(** [rate_var_increasing_lower_first] (theorem).
 Mathematical meaning: Below one-half, an increased first marginal rate increases Bernoulli contrast variability.
 Exact proposition: The displayed universal claim is about exact real
 Bernoulli-rate/moment algebra supporting simulation count diagnostics.
 Premises and side conditions: Every required probability range and
 sample-count ordering appears explicitly in this proposition. The
 conclusion never assumes distributional validity from sample output.
 Proof/definition method: Rewrite the reused Bernoulli expressions and
 apply maintained ring, field, and ordered-real solvers or previously
 proven SamplingPrecision bounds; no new distribution algorithm.
 Library reuse: SamplingPrecision, Reals, Ring, Lra, Psatz and Field.
 Boundary: Algebraic variance and expectation *targets* for hypothetical
 independent Bernoulli samples; binomial distribution and coverage are
 separate theorems, and no empirical IQ model is validated.
*)
Theorem rate_var_increasing_lower_first : forall p q r, 0<=p -> p<=r -> r<=1/2 -> rate_var p q<=rate_var r q.
Proof.
  intros p q r Hp Hpr Hr; unfold rate_var; pose proof (sampling_variance_monotone_lower_half p r Hp Hpr Hr) as H; lra.
Qed.

(** [rate_var_decreasing_upper_first] (theorem).
 Mathematical meaning: Above one-half, increasing the first event rate reduces its Bernoulli variability.
 Exact proposition: The displayed universal claim is about exact real
 Bernoulli-rate/moment algebra supporting simulation count diagnostics.
 Premises and side conditions: Every required probability range and
 sample-count ordering appears explicitly in this proposition. The
 conclusion never assumes distributional validity from sample output.
 Proof/definition method: Rewrite the reused Bernoulli expressions and
 apply maintained ring, field, and ordered-real solvers or previously
 proven SamplingPrecision bounds; no new distribution algorithm.
 Library reuse: SamplingPrecision, Reals, Ring, Lra, Psatz and Field.
 Boundary: Algebraic variance and expectation *targets* for hypothetical
 independent Bernoulli samples; binomial distribution and coverage are
 separate theorems, and no empirical IQ model is validated.
*)
Theorem rate_var_decreasing_upper_first : forall p q r, 1/2<=p -> p<=r -> r<=1 -> rate_var r q<=rate_var p q.
Proof.
  intros p q r Hp Hpr Hr; unfold rate_var; pose proof (sampling_variance_monotone_upper_half p r Hp Hpr Hr) as H; lra.
Qed.

(** [rate_var_increasing_lower_second] (theorem).
 Mathematical meaning: Below one-half, raising the second event rate increases the comparison variance.
 Exact proposition: The displayed universal claim is about exact real
 Bernoulli-rate/moment algebra supporting simulation count diagnostics.
 Premises and side conditions: Every required probability range and
 sample-count ordering appears explicitly in this proposition. The
 conclusion never assumes distributional validity from sample output.
 Proof/definition method: Rewrite the reused Bernoulli expressions and
 apply maintained ring, field, and ordered-real solvers or previously
 proven SamplingPrecision bounds; no new distribution algorithm.
 Library reuse: SamplingPrecision, Reals, Ring, Lra, Psatz and Field.
 Boundary: Algebraic variance and expectation *targets* for hypothetical
 independent Bernoulli samples; binomial distribution and coverage are
 separate theorems, and no empirical IQ model is validated.
*)
Theorem rate_var_increasing_lower_second : forall p q r, 0<=q -> q<=r -> r<=1/2 -> rate_var p q<=rate_var p r.
Proof.
  intros p q r Hq Hqr Hr; unfold rate_var; pose proof (sampling_variance_monotone_lower_half q r Hq Hqr Hr) as H; lra.
Qed.

(** [rate_var_decreasing_upper_second] (theorem).
 Mathematical meaning: Above one-half, increasing the second rate reduces Bernoulli variability.
 Exact proposition: The displayed universal claim is about exact real
 Bernoulli-rate/moment algebra supporting simulation count diagnostics.
 Premises and side conditions: Every required probability range and
 sample-count ordering appears explicitly in this proposition. The
 conclusion never assumes distributional validity from sample output.
 Proof/definition method: Rewrite the reused Bernoulli expressions and
 apply maintained ring, field, and ordered-real solvers or previously
 proven SamplingPrecision bounds; no new distribution algorithm.
 Library reuse: SamplingPrecision, Reals, Ring, Lra, Psatz and Field.
 Boundary: Algebraic variance and expectation *targets* for hypothetical
 independent Bernoulli samples; binomial distribution and coverage are
 separate theorems, and no empirical IQ model is validated.
*)
Theorem rate_var_decreasing_upper_second : forall p q r, 1/2<=q -> q<=r -> r<=1 -> rate_var p r<=rate_var p q.
Proof.
  intros p q r Hq Hqr Hr; unfold rate_var; pose proof (sampling_variance_monotone_upper_half q r Hq Hqr Hr) as H; lra.
Qed.

(** [rate_count_add_first] (theorem).
 Mathematical meaning: Expected counts are additive in identical first-rate replicate blocks.
 Exact proposition: The displayed universal claim is about exact real
 Bernoulli-rate/moment algebra supporting simulation count diagnostics.
 Premises and side conditions: Every required probability range and
 sample-count ordering appears explicitly in this proposition. The
 conclusion never assumes distributional validity from sample output.
 Proof/definition method: Rewrite the reused Bernoulli expressions and
 apply maintained ring, field, and ordered-real solvers or previously
 proven SamplingPrecision bounds; no new distribution algorithm.
 Library reuse: SamplingPrecision, Reals, Ring, Lra, Psatz and Field.
 Boundary: Algebraic variance and expectation *targets* for hypothetical
 independent Bernoulli samples; binomial distribution and coverage are
 separate theorems, and no empirical IQ model is validated.
*)
Theorem rate_count_add_first : forall n m p q, rate_count (n+m) 0 p q=rate_count n 0 p q+rate_count m 0 p q.
Proof.
  intros; unfold rate_count; ring.
Qed.

(** [rate_count_add_second] (theorem).
 Mathematical meaning: Expected counts are additive in identical second-rate replicate blocks.
 Exact proposition: The displayed universal claim is about exact real
 Bernoulli-rate/moment algebra supporting simulation count diagnostics.
 Premises and side conditions: Every required probability range and
 sample-count ordering appears explicitly in this proposition. The
 conclusion never assumes distributional validity from sample output.
 Proof/definition method: Rewrite the reused Bernoulli expressions and
 apply maintained ring, field, and ordered-real solvers or previously
 proven SamplingPrecision bounds; no new distribution algorithm.
 Library reuse: SamplingPrecision, Reals, Ring, Lra, Psatz and Field.
 Boundary: Algebraic variance and expectation *targets* for hypothetical
 independent Bernoulli samples; binomial distribution and coverage are
 separate theorems, and no empirical IQ model is validated.
*)
Theorem rate_count_add_second : forall n m p q, rate_count 0 (n+m) p q=rate_count 0 n p q+rate_count 0 m p q.
Proof.
  intros; unfold rate_count; ring.
Qed.

(** [rate_count_comm] (theorem).
 Mathematical meaning: Combined expected successes are independent of batch ordering.
 Exact proposition: The displayed universal claim is about exact real
 Bernoulli-rate/moment algebra supporting simulation count diagnostics.
 Premises and side conditions: Every required probability range and
 sample-count ordering appears explicitly in this proposition. The
 conclusion never assumes distributional validity from sample output.
 Proof/definition method: Rewrite the reused Bernoulli expressions and
 apply maintained ring, field, and ordered-real solvers or previously
 proven SamplingPrecision bounds; no new distribution algorithm.
 Library reuse: SamplingPrecision, Reals, Ring, Lra, Psatz and Field.
 Boundary: Algebraic variance and expectation *targets* for hypothetical
 independent Bernoulli samples; binomial distribution and coverage are
 separate theorems, and no empirical IQ model is validated.
*)
Theorem rate_count_comm : forall n m p q, rate_count n m p q=rate_count m n q p.
Proof.
  intros; unfold rate_count; ring.
Qed.

(** [rate_count_complement] (theorem).
 Mathematical meaning: Expected successes plus expected failures equal the total number of trials.
 Exact proposition: The displayed universal claim is about exact real
 Bernoulli-rate/moment algebra supporting simulation count diagnostics.
 Premises and side conditions: Every required probability range and
 sample-count ordering appears explicitly in this proposition. The
 conclusion never assumes distributional validity from sample output.
 Proof/definition method: Rewrite the reused Bernoulli expressions and
 apply maintained ring, field, and ordered-real solvers or previously
 proven SamplingPrecision bounds; no new distribution algorithm.
 Library reuse: SamplingPrecision, Reals, Ring, Lra, Psatz and Field.
 Boundary: Algebraic variance and expectation *targets* for hypothetical
 independent Bernoulli samples; binomial distribution and coverage are
 separate theorems, and no empirical IQ model is validated.
*)
Theorem rate_count_complement : forall n m p q, rate_count n m (1-p) (1-q)=(n+m)-rate_count n m p q.
Proof.
  intros; unfold rate_count; ring.
Qed.

(** [rate_count_shift] (theorem).
 Mathematical meaning: A common increase in event probabilities raises the expected pooled count proportionally to total sample size.
 Exact proposition: The displayed universal claim is about exact real
 Bernoulli-rate/moment algebra supporting simulation count diagnostics.
 Premises and side conditions: Every required probability range and
 sample-count ordering appears explicitly in this proposition. The
 conclusion never assumes distributional validity from sample output.
 Proof/definition method: Rewrite the reused Bernoulli expressions and
 apply maintained ring, field, and ordered-real solvers or previously
 proven SamplingPrecision bounds; no new distribution algorithm.
 Library reuse: SamplingPrecision, Reals, Ring, Lra, Psatz and Field.
 Boundary: Algebraic variance and expectation *targets* for hypothetical
 independent Bernoulli samples; binomial distribution and coverage are
 separate theorems, and no empirical IQ model is validated.
*)
Theorem rate_count_shift : forall n m p q t, rate_count n m (p+t) (q+t)=rate_count n m p q+t*(n+m).
Proof.
  intros; unfold rate_count; ring.
Qed.

(** [rate_count_scale] (theorem).
 Mathematical meaning: Scaling event probabilities scales the formal expectation numerator.
 Exact proposition: The displayed universal claim is about exact real
 Bernoulli-rate/moment algebra supporting simulation count diagnostics.
 Premises and side conditions: Every required probability range and
 sample-count ordering appears explicitly in this proposition. The
 conclusion never assumes distributional validity from sample output.
 Proof/definition method: Rewrite the reused Bernoulli expressions and
 apply maintained ring, field, and ordered-real solvers or previously
 proven SamplingPrecision bounds; no new distribution algorithm.
 Library reuse: SamplingPrecision, Reals, Ring, Lra, Psatz and Field.
 Boundary: Algebraic variance and expectation *targets* for hypothetical
 independent Bernoulli samples; binomial distribution and coverage are
 separate theorems, and no empirical IQ model is validated.
*)
Theorem rate_count_scale : forall n m p q t, rate_count n m (t*p) (t*q)=t*rate_count n m p q.
Proof.
  intros; unfold rate_count; ring.
Qed.

(** [rate_count_within_bounds] (theorem).
 Mathematical meaning: Combined expected event counts remain within sample size when rates are probabilities.
 Exact proposition: The displayed universal claim is about exact real
 Bernoulli-rate/moment algebra supporting simulation count diagnostics.
 Premises and side conditions: Every required probability range and
 sample-count ordering appears explicitly in this proposition. The
 conclusion never assumes distributional validity from sample output.
 Proof/definition method: Rewrite the reused Bernoulli expressions and
 apply maintained ring, field, and ordered-real solvers or previously
 proven SamplingPrecision bounds; no new distribution algorithm.
 Library reuse: SamplingPrecision, Reals, Ring, Lra, Psatz and Field.
 Boundary: Algebraic variance and expectation *targets* for hypothetical
 independent Bernoulli samples; binomial distribution and coverage are
 separate theorems, and no empirical IQ model is validated.
*)
Theorem rate_count_within_bounds : forall n m p q, 0<=n -> 0<=m -> 0<=p -> p<=1 -> 0<=q -> q<=1 -> 0<=rate_count n m p q<=n+m.
Proof.
  intros; unfold rate_count; nra.
Qed.

(** [rate_count_nonnegative] (theorem).
 Mathematical meaning: Nonnegative rates and sample sizes have nonnegative expected counts.
 Exact proposition: The displayed universal claim is about exact real
 Bernoulli-rate/moment algebra supporting simulation count diagnostics.
 Premises and side conditions: Every required probability range and
 sample-count ordering appears explicitly in this proposition. The
 conclusion never assumes distributional validity from sample output.
 Proof/definition method: Rewrite the reused Bernoulli expressions and
 apply maintained ring, field, and ordered-real solvers or previously
 proven SamplingPrecision bounds; no new distribution algorithm.
 Library reuse: SamplingPrecision, Reals, Ring, Lra, Psatz and Field.
 Boundary: Algebraic variance and expectation *targets* for hypothetical
 independent Bernoulli samples; binomial distribution and coverage are
 separate theorems, and no empirical IQ model is validated.
*)
Theorem rate_count_nonnegative : forall n m p q, 0<=n -> 0<=m -> 0<=p -> 0<=q -> 0<=rate_count n m p q.
Proof.
  intros; unfold rate_count; nra.
Qed.

(** [rate_count_zero_rates] (theorem).
 Mathematical meaning: Two groups with impossible events have zero expected successes.
 Exact proposition: The displayed universal claim is about exact real
 Bernoulli-rate/moment algebra supporting simulation count diagnostics.
 Premises and side conditions: Every required probability range and
 sample-count ordering appears explicitly in this proposition. The
 conclusion never assumes distributional validity from sample output.
 Proof/definition method: Rewrite the reused Bernoulli expressions and
 apply maintained ring, field, and ordered-real solvers or previously
 proven SamplingPrecision bounds; no new distribution algorithm.
 Library reuse: SamplingPrecision, Reals, Ring, Lra, Psatz and Field.
 Boundary: Algebraic variance and expectation *targets* for hypothetical
 independent Bernoulli samples; binomial distribution and coverage are
 separate theorems, and no empirical IQ model is validated.
*)
Theorem rate_count_zero_rates : forall n m, rate_count n m 0 0=0.
Proof.
  intros; unfold rate_count; ring.
Qed.

(** [rate_count_all_rates] (theorem).
 Mathematical meaning: Two groups with certain events have expected counts equal to total size.
 Exact proposition: The displayed universal claim is about exact real
 Bernoulli-rate/moment algebra supporting simulation count diagnostics.
 Premises and side conditions: Every required probability range and
 sample-count ordering appears explicitly in this proposition. The
 conclusion never assumes distributional validity from sample output.
 Proof/definition method: Rewrite the reused Bernoulli expressions and
 apply maintained ring, field, and ordered-real solvers or previously
 proven SamplingPrecision bounds; no new distribution algorithm.
 Library reuse: SamplingPrecision, Reals, Ring, Lra, Psatz and Field.
 Boundary: Algebraic variance and expectation *targets* for hypothetical
 independent Bernoulli samples; binomial distribution and coverage are
 separate theorems, and no empirical IQ model is validated.
*)
Theorem rate_count_all_rates : forall n m, rate_count n m 1 1=n+m.
Proof.
  intros; unfold rate_count; ring.
Qed.

(** [rate_count_common_rate] (theorem).
 Mathematical meaning: Identical event rates combine as total size times common rate.
 Exact proposition: The displayed universal claim is about exact real
 Bernoulli-rate/moment algebra supporting simulation count diagnostics.
 Premises and side conditions: Every required probability range and
 sample-count ordering appears explicitly in this proposition. The
 conclusion never assumes distributional validity from sample output.
 Proof/definition method: Rewrite the reused Bernoulli expressions and
 apply maintained ring, field, and ordered-real solvers or previously
 proven SamplingPrecision bounds; no new distribution algorithm.
 Library reuse: SamplingPrecision, Reals, Ring, Lra, Psatz and Field.
 Boundary: Algebraic variance and expectation *targets* for hypothetical
 independent Bernoulli samples; binomial distribution and coverage are
 separate theorems, and no empirical IQ model is validated.
*)
Theorem rate_count_common_rate : forall n m p, rate_count n m p p=(n+m)*p.
Proof.
  intros; unfold rate_count; ring.
Qed.

(** [rate_count_disparity] (theorem).
 Mathematical meaning: The difference in expected successes of identical-sized trial groups equals the size times the rate gap.
 Exact proposition: The displayed universal claim is about exact real
 Bernoulli-rate/moment algebra supporting simulation count diagnostics.
 Premises and side conditions: Every required probability range and
 sample-count ordering appears explicitly in this proposition. The
 conclusion never assumes distributional validity from sample output.
 Proof/definition method: Rewrite the reused Bernoulli expressions and
 apply maintained ring, field, and ordered-real solvers or previously
 proven SamplingPrecision bounds; no new distribution algorithm.
 Library reuse: SamplingPrecision, Reals, Ring, Lra, Psatz and Field.
 Boundary: Algebraic variance and expectation *targets* for hypothetical
 independent Bernoulli samples; binomial distribution and coverage are
 separate theorems, and no empirical IQ model is validated.
*)
Theorem rate_count_disparity : forall n m p q, n*rate_gap p q = rate_count n 0 p q-rate_count n 0 q p.
Proof.
  intros; unfold rate_gap,rate_count; ring.
Qed.

(** [rate_count_variance_comm] (theorem).
 Mathematical meaning: Sum of independently assigned Bernoulli count variance contributions is symmetric across batches.
 Exact proposition: The displayed universal claim is about exact real
 Bernoulli-rate/moment algebra supporting simulation count diagnostics.
 Premises and side conditions: Every required probability range and
 sample-count ordering appears explicitly in this proposition. The
 conclusion never assumes distributional validity from sample output.
 Proof/definition method: Rewrite the reused Bernoulli expressions and
 apply maintained ring, field, and ordered-real solvers or previously
 proven SamplingPrecision bounds; no new distribution algorithm.
 Library reuse: SamplingPrecision, Reals, Ring, Lra, Psatz and Field.
 Boundary: Algebraic variance and expectation *targets* for hypothetical
 independent Bernoulli samples; binomial distribution and coverage are
 separate theorems, and no empirical IQ model is validated.
*)
Theorem rate_count_variance_comm : forall n m p q, rate_count_variance n m p q=rate_count_variance m n q p.
Proof.
  intros; unfold rate_count_variance; ring.
Qed.

(** [rate_count_variance_complement] (theorem).
 Mathematical meaning: Complementing successes into failures leaves Bernoulli count variance expressions unchanged.
 Exact proposition: The displayed universal claim is about exact real
 Bernoulli-rate/moment algebra supporting simulation count diagnostics.
 Premises and side conditions: Every required probability range and
 sample-count ordering appears explicitly in this proposition. The
 conclusion never assumes distributional validity from sample output.
 Proof/definition method: Rewrite the reused Bernoulli expressions and
 apply maintained ring, field, and ordered-real solvers or previously
 proven SamplingPrecision bounds; no new distribution algorithm.
 Library reuse: SamplingPrecision, Reals, Ring, Lra, Psatz and Field.
 Boundary: Algebraic variance and expectation *targets* for hypothetical
 independent Bernoulli samples; binomial distribution and coverage are
 separate theorems, and no empirical IQ model is validated.
*)
Theorem rate_count_variance_complement : forall n m p q, rate_count_variance n m (1-p) (1-q)=rate_count_variance n m p q.
Proof.
  intros; unfold rate_count_variance,sampling_bernoulli_variance; ring.
Qed.

(** [rate_count_variance_add_size] (theorem).
 Mathematical meaning: Variance numerators add for additional independent first-rate batch size.
 Exact proposition: The displayed universal claim is about exact real
 Bernoulli-rate/moment algebra supporting simulation count diagnostics.
 Premises and side conditions: Every required probability range and
 sample-count ordering appears explicitly in this proposition. The
 conclusion never assumes distributional validity from sample output.
 Proof/definition method: Rewrite the reused Bernoulli expressions and
 apply maintained ring, field, and ordered-real solvers or previously
 proven SamplingPrecision bounds; no new distribution algorithm.
 Library reuse: SamplingPrecision, Reals, Ring, Lra, Psatz and Field.
 Boundary: Algebraic variance and expectation *targets* for hypothetical
 independent Bernoulli samples; binomial distribution and coverage are
 separate theorems, and no empirical IQ model is validated.
*)
Theorem rate_count_variance_add_size : forall n m k p q, rate_count_variance (n+k) m p q=rate_count_variance n m p q+rate_count_variance k 0 p q.
Proof.
  intros; unfold rate_count_variance; ring.
Qed.

(** [rate_count_variance_nonnegative] (theorem).
 Mathematical meaning: Independent-Bernoulli variance expression is nonnegative for feasible rates.
 Exact proposition: The displayed universal claim is about exact real
 Bernoulli-rate/moment algebra supporting simulation count diagnostics.
 Premises and side conditions: Every required probability range and
 sample-count ordering appears explicitly in this proposition. The
 conclusion never assumes distributional validity from sample output.
 Proof/definition method: Rewrite the reused Bernoulli expressions and
 apply maintained ring, field, and ordered-real solvers or previously
 proven SamplingPrecision bounds; no new distribution algorithm.
 Library reuse: SamplingPrecision, Reals, Ring, Lra, Psatz and Field.
 Boundary: Algebraic variance and expectation *targets* for hypothetical
 independent Bernoulli samples; binomial distribution and coverage are
 separate theorems, and no empirical IQ model is validated.
*)
Theorem rate_count_variance_nonnegative : forall n m p q, 0<=n -> 0<=m -> 0<=p -> p<=1 -> 0<=q -> q<=1 -> 0<=rate_count_variance n m p q.
Proof.
  intros n m p q Hn Hm Hp Hp1 Hq Hq1; unfold rate_count_variance; pose proof (sampling_variance_nonnegative p Hp Hp1) as A; pose proof (sampling_variance_nonnegative q Hq Hq1) as B; nra.
Qed.

(** [rate_count_variance_bound] (theorem).
 Mathematical meaning: The heterogeneously pooled Bernoulli count variance is no larger than one quarter of the total trial count.
 Exact proposition: The displayed universal claim is about exact real
 Bernoulli-rate/moment algebra supporting simulation count diagnostics.
 Premises and side conditions: Every required probability range and
 sample-count ordering appears explicitly in this proposition. The
 conclusion never assumes distributional validity from sample output.
 Proof/definition method: Rewrite the reused Bernoulli expressions and
 apply maintained ring, field, and ordered-real solvers or previously
 proven SamplingPrecision bounds; no new distribution algorithm.
 Library reuse: SamplingPrecision, Reals, Ring, Lra, Psatz and Field.
 Boundary: Algebraic variance and expectation *targets* for hypothetical
 independent Bernoulli samples; binomial distribution and coverage are
 separate theorems, and no empirical IQ model is validated.
*)
Theorem rate_count_variance_bound : forall n m p q, 0<=n -> 0<=m -> rate_count_variance n m p q <= (n+m)/4.
Proof.
  intros n m p q Hn Hm; unfold rate_count_variance; pose proof (sampling_variance_maximum p) as A; pose proof (sampling_variance_maximum q) as B; nra.
Qed.

(** [rate_count_variance_zero_deterministic] (theorem).
 Mathematical meaning: Two groups of deterministic outcomes have zero binomial variance numerator.
 Exact proposition: The displayed universal claim is about exact real
 Bernoulli-rate/moment algebra supporting simulation count diagnostics.
 Premises and side conditions: Every required probability range and
 sample-count ordering appears explicitly in this proposition. The
 conclusion never assumes distributional validity from sample output.
 Proof/definition method: Rewrite the reused Bernoulli expressions and
 apply maintained ring, field, and ordered-real solvers or previously
 proven SamplingPrecision bounds; no new distribution algorithm.
 Library reuse: SamplingPrecision, Reals, Ring, Lra, Psatz and Field.
 Boundary: Algebraic variance and expectation *targets* for hypothetical
 independent Bernoulli samples; binomial distribution and coverage are
 separate theorems, and no empirical IQ model is validated.
*)
Theorem rate_count_variance_zero_deterministic : forall n m, rate_count_variance n m 0 1=0.
Proof.
  intros; unfold rate_count_variance,sampling_bernoulli_variance; ring.
Qed.

(** [rate_count_variance_equal_rate] (theorem).
 Mathematical meaning: Equal success rates recover the single-rate Bernoulli count variance expression.
 Exact proposition: The displayed universal claim is about exact real
 Bernoulli-rate/moment algebra supporting simulation count diagnostics.
 Premises and side conditions: Every required probability range and
 sample-count ordering appears explicitly in this proposition. The
 conclusion never assumes distributional validity from sample output.
 Proof/definition method: Rewrite the reused Bernoulli expressions and
 apply maintained ring, field, and ordered-real solvers or previously
 proven SamplingPrecision bounds; no new distribution algorithm.
 Library reuse: SamplingPrecision, Reals, Ring, Lra, Psatz and Field.
 Boundary: Algebraic variance and expectation *targets* for hypothetical
 independent Bernoulli samples; binomial distribution and coverage are
 separate theorems, and no empirical IQ model is validated.
*)
Theorem rate_count_variance_equal_rate : forall n m p, rate_count_variance n m p p=(n+m)*sampling_bernoulli_variance p.
Proof.
  intros; unfold rate_count_variance; ring.
Qed.

(** [rate_var_equal_rate] (theorem).
 Mathematical meaning: The two-margin contrast variance is twice the one-margin Bernoulli variance when both pass rates coincide.
 Exact proposition: This universal real formula is a quantitative
 sampling-size, marginal-rate or heterogeneity bound from the six reports.
 Premises and side conditions: All nonnegativity, probability unit-interval,
 strictness and sample size requirements are stated as explicit hypotheses.
 Proof/definition method: Use previously checked SamplingPrecision results
 or standard real algebra and ring to derive this exact formula. No claim
 presupposes a Gaussian law, binomial PMF or asymptotic approximation.
 Library reuse: SamplingPrecision, canonical Reals, Ring, Lra, Psatz, Field.
 Boundary: Precise deterministic expectation/variance expressions for
 hypothetical Bernoulli sampling, not an actual PRNG independence theorem
 or a statement about observed people or normal confidence interval coverage.
*)
Theorem rate_var_equal_rate : forall p, rate_var p p=2*sampling_bernoulli_variance p.
Proof.
  intros; unfold rate_var; ring.
Qed.

(** [rate_var_one_certain] (theorem).
 Mathematical meaning: A deterministic second event contributes no additional variance.
 Exact proposition: This universal real formula is a quantitative
 sampling-size, marginal-rate or heterogeneity bound from the six reports.
 Premises and side conditions: All nonnegativity, probability unit-interval,
 strictness and sample size requirements are stated as explicit hypotheses.
 Proof/definition method: Use previously checked SamplingPrecision results
 or standard real algebra and ring to derive this exact formula. No claim
 presupposes a Gaussian law, binomial PMF or asymptotic approximation.
 Library reuse: SamplingPrecision, canonical Reals, Ring, Lra, Psatz, Field.
 Boundary: Precise deterministic expectation/variance expressions for
 hypothetical Bernoulli sampling, not an actual PRNG independence theorem
 or a statement about observed people or normal confidence interval coverage.
*)
Theorem rate_var_one_certain : forall p, rate_var p 1=sampling_bernoulli_variance p.
Proof.
  intros; unfold rate_var,sampling_bernoulli_variance; ring.
Qed.

(** [rate_var_one_impossible] (theorem).
 Mathematical meaning: An impossible second event contributes no additional variance.
 Exact proposition: This universal real formula is a quantitative
 sampling-size, marginal-rate or heterogeneity bound from the six reports.
 Premises and side conditions: All nonnegativity, probability unit-interval,
 strictness and sample size requirements are stated as explicit hypotheses.
 Proof/definition method: Use previously checked SamplingPrecision results
 or standard real algebra and ring to derive this exact formula. No claim
 presupposes a Gaussian law, binomial PMF or asymptotic approximation.
 Library reuse: SamplingPrecision, canonical Reals, Ring, Lra, Psatz, Field.
 Boundary: Precise deterministic expectation/variance expressions for
 hypothetical Bernoulli sampling, not an actual PRNG independence theorem
 or a statement about observed people or normal confidence interval coverage.
*)
Theorem rate_var_one_impossible : forall p, rate_var p 0=sampling_bernoulli_variance p.
Proof.
  intros; unfold rate_var,sampling_bernoulli_variance; ring.
Qed.

(** [rate_var_first_balanced] (theorem).
 Mathematical meaning: A balanced first margin contributes exactly the maximal Bernoulli variance one quarter.
 Exact proposition: This universal real formula is a quantitative
 sampling-size, marginal-rate or heterogeneity bound from the six reports.
 Premises and side conditions: All nonnegativity, probability unit-interval,
 strictness and sample size requirements are stated as explicit hypotheses.
 Proof/definition method: Use previously checked SamplingPrecision results
 or standard real algebra and ring to derive this exact formula. No claim
 presupposes a Gaussian law, binomial PMF or asymptotic approximation.
 Library reuse: SamplingPrecision, canonical Reals, Ring, Lra, Psatz, Field.
 Boundary: Precise deterministic expectation/variance expressions for
 hypothetical Bernoulli sampling, not an actual PRNG independence theorem
 or a statement about observed people or normal confidence interval coverage.
*)
Theorem rate_var_first_balanced : forall q, rate_var (1/2) q=1/4+sampling_bernoulli_variance q.
Proof.
  intros; unfold rate_var,sampling_bernoulli_variance; ring.
Qed.

(** [rate_var_second_balanced] (theorem).
 Mathematical meaning: A balanced second margin contributes one quarter to the total comparison variance.
 Exact proposition: This universal real formula is a quantitative
 sampling-size, marginal-rate or heterogeneity bound from the six reports.
 Premises and side conditions: All nonnegativity, probability unit-interval,
 strictness and sample size requirements are stated as explicit hypotheses.
 Proof/definition method: Use previously checked SamplingPrecision results
 or standard real algebra and ring to derive this exact formula. No claim
 presupposes a Gaussian law, binomial PMF or asymptotic approximation.
 Library reuse: SamplingPrecision, canonical Reals, Ring, Lra, Psatz, Field.
 Boundary: Precise deterministic expectation/variance expressions for
 hypothetical Bernoulli sampling, not an actual PRNG independence theorem
 or a statement about observed people or normal confidence interval coverage.
*)
Theorem rate_var_second_balanced : forall p, rate_var p (1/2)=sampling_bernoulli_variance p+1/4.
Proof.
  intros; unfold rate_var,sampling_bernoulli_variance; ring.
Qed.

(** [rate_var_maximum_only_balanced] (theorem).
 Mathematical meaning: Both event rates must be balanced to attain the maximal combined Bernoulli variance.
 Exact proposition: This universal real formula is a quantitative
 sampling-size, marginal-rate or heterogeneity bound from the six reports.
 Premises and side conditions: All nonnegativity, probability unit-interval,
 strictness and sample size requirements are stated as explicit hypotheses.
 Proof/definition method: Use previously checked SamplingPrecision results
 or standard real algebra and ring to derive this exact formula. No claim
 presupposes a Gaussian law, binomial PMF or asymptotic approximation.
 Library reuse: SamplingPrecision, canonical Reals, Ring, Lra, Psatz, Field.
 Boundary: Precise deterministic expectation/variance expressions for
 hypothetical Bernoulli sampling, not an actual PRNG independence theorem
 or a statement about observed people or normal confidence interval coverage.
*)
Theorem rate_var_maximum_only_balanced : forall p q, rate_var p q=1/2 -> p=1/2 /\ q=1/2.
Proof.
  intros p q H; pose proof (rate_var_midpoint_gap p q) as E; rewrite H in E; nra.
Qed.

(** [rate_var_zero_if_both_impossible] (theorem).
 Mathematical meaning: If neither event can occur, the contrast has zero Bernoulli variance.
 Exact proposition: This universal real formula is a quantitative
 sampling-size, marginal-rate or heterogeneity bound from the six reports.
 Premises and side conditions: All nonnegativity, probability unit-interval,
 strictness and sample size requirements are stated as explicit hypotheses.
 Proof/definition method: Use previously checked SamplingPrecision results
 or standard real algebra and ring to derive this exact formula. No claim
 presupposes a Gaussian law, binomial PMF or asymptotic approximation.
 Library reuse: SamplingPrecision, canonical Reals, Ring, Lra, Psatz, Field.
 Boundary: Precise deterministic expectation/variance expressions for
 hypothetical Bernoulli sampling, not an actual PRNG independence theorem
 or a statement about observed people or normal confidence interval coverage.
*)
Theorem rate_var_zero_if_both_impossible : rate_var 0 0=0.
Proof.
  unfold rate_var,sampling_bernoulli_variance; ring.
Qed.

(** [rate_var_zero_if_both_certain] (theorem).
 Mathematical meaning: If both events are certain, the contrast has zero Bernoulli variance.
 Exact proposition: This universal real formula is a quantitative
 sampling-size, marginal-rate or heterogeneity bound from the six reports.
 Premises and side conditions: All nonnegativity, probability unit-interval,
 strictness and sample size requirements are stated as explicit hypotheses.
 Proof/definition method: Use previously checked SamplingPrecision results
 or standard real algebra and ring to derive this exact formula. No claim
 presupposes a Gaussian law, binomial PMF or asymptotic approximation.
 Library reuse: SamplingPrecision, canonical Reals, Ring, Lra, Psatz, Field.
 Boundary: Precise deterministic expectation/variance expressions for
 hypothetical Bernoulli sampling, not an actual PRNG independence theorem
 or a statement about observed people or normal confidence interval coverage.
*)
Theorem rate_var_zero_if_both_certain : rate_var 1 1=0.
Proof.
  unfold rate_var,sampling_bernoulli_variance; ring.
Qed.

(** [rate_count_first_rate_shift] (theorem).
 Mathematical meaning: Changing the first event probability changes expected successes in proportion to the first sample size.
 Exact proposition: This universal real formula is a quantitative
 sampling-size, marginal-rate or heterogeneity bound from the six reports.
 Premises and side conditions: All nonnegativity, probability unit-interval,
 strictness and sample size requirements are stated as explicit hypotheses.
 Proof/definition method: Use previously checked SamplingPrecision results
 or standard real algebra and ring to derive this exact formula. No claim
 presupposes a Gaussian law, binomial PMF or asymptotic approximation.
 Library reuse: SamplingPrecision, canonical Reals, Ring, Lra, Psatz, Field.
 Boundary: Precise deterministic expectation/variance expressions for
 hypothetical Bernoulli sampling, not an actual PRNG independence theorem
 or a statement about observed people or normal confidence interval coverage.
*)
Theorem rate_count_first_rate_shift : forall n m p q r, rate_count n m r q-rate_count n m p q=n*(r-p).
Proof.
  intros; unfold rate_count; ring.
Qed.

(** [rate_count_second_rate_shift] (theorem).
 Mathematical meaning: Changing the second probability changes expected successes according to the second trial count.
 Exact proposition: This universal real formula is a quantitative
 sampling-size, marginal-rate or heterogeneity bound from the six reports.
 Premises and side conditions: All nonnegativity, probability unit-interval,
 strictness and sample size requirements are stated as explicit hypotheses.
 Proof/definition method: Use previously checked SamplingPrecision results
 or standard real algebra and ring to derive this exact formula. No claim
 presupposes a Gaussian law, binomial PMF or asymptotic approximation.
 Library reuse: SamplingPrecision, canonical Reals, Ring, Lra, Psatz, Field.
 Boundary: Precise deterministic expectation/variance expressions for
 hypothetical Bernoulli sampling, not an actual PRNG independence theorem
 or a statement about observed people or normal confidence interval coverage.
*)
Theorem rate_count_second_rate_shift : forall n m p q r, rate_count n m p r-rate_count n m p q=m*(r-q).
Proof.
  intros; unfold rate_count; ring.
Qed.

(** [rate_count_add_first_size] (theorem).
 Mathematical meaning: Adding k trials at the first rate increases the expected count by k times that rate.
 Exact proposition: This universal real formula is a quantitative
 sampling-size, marginal-rate or heterogeneity bound from the six reports.
 Premises and side conditions: All nonnegativity, probability unit-interval,
 strictness and sample size requirements are stated as explicit hypotheses.
 Proof/definition method: Use previously checked SamplingPrecision results
 or standard real algebra and ring to derive this exact formula. No claim
 presupposes a Gaussian law, binomial PMF or asymptotic approximation.
 Library reuse: SamplingPrecision, canonical Reals, Ring, Lra, Psatz, Field.
 Boundary: Precise deterministic expectation/variance expressions for
 hypothetical Bernoulli sampling, not an actual PRNG independence theorem
 or a statement about observed people or normal confidence interval coverage.
*)
Theorem rate_count_add_first_size : forall n m k p q, rate_count (n+k) m p q=rate_count n m p q+k*p.
Proof.
  intros; unfold rate_count; ring.
Qed.

(** [rate_count_add_second_size] (theorem).
 Mathematical meaning: Adding a second-group trial batch increases the expected count by its expected successes.
 Exact proposition: This universal real formula is a quantitative
 sampling-size, marginal-rate or heterogeneity bound from the six reports.
 Premises and side conditions: All nonnegativity, probability unit-interval,
 strictness and sample size requirements are stated as explicit hypotheses.
 Proof/definition method: Use previously checked SamplingPrecision results
 or standard real algebra and ring to derive this exact formula. No claim
 presupposes a Gaussian law, binomial PMF or asymptotic approximation.
 Library reuse: SamplingPrecision, canonical Reals, Ring, Lra, Psatz, Field.
 Boundary: Precise deterministic expectation/variance expressions for
 hypothetical Bernoulli sampling, not an actual PRNG independence theorem
 or a statement about observed people or normal confidence interval coverage.
*)
Theorem rate_count_add_second_size : forall n m k p q, rate_count n (m+k) p q=rate_count n m p q+k*q.
Proof.
  intros; unfold rate_count; ring.
Qed.

(** [rate_count_rate_monotone_first] (theorem).
 Mathematical meaning: Expected successes are nondecreasing in the first event rate at nonnegative sample size.
 Exact proposition: This universal real formula is a quantitative
 sampling-size, marginal-rate or heterogeneity bound from the six reports.
 Premises and side conditions: All nonnegativity, probability unit-interval,
 strictness and sample size requirements are stated as explicit hypotheses.
 Proof/definition method: Use previously checked SamplingPrecision results
 or standard real algebra and ring to derive this exact formula. No claim
 presupposes a Gaussian law, binomial PMF or asymptotic approximation.
 Library reuse: SamplingPrecision, canonical Reals, Ring, Lra, Psatz, Field.
 Boundary: Precise deterministic expectation/variance expressions for
 hypothetical Bernoulli sampling, not an actual PRNG independence theorem
 or a statement about observed people or normal confidence interval coverage.
*)
Theorem rate_count_rate_monotone_first : forall n m p q r, 0<=n -> p<=r -> rate_count n m p q<=rate_count n m r q.
Proof.
  intros; unfold rate_count; nra.
Qed.

(** [rate_count_rate_monotone_second] (theorem).
 Mathematical meaning: Expected successes are nondecreasing in the second event rate.
 Exact proposition: This universal real formula is a quantitative
 sampling-size, marginal-rate or heterogeneity bound from the six reports.
 Premises and side conditions: All nonnegativity, probability unit-interval,
 strictness and sample size requirements are stated as explicit hypotheses.
 Proof/definition method: Use previously checked SamplingPrecision results
 or standard real algebra and ring to derive this exact formula. No claim
 presupposes a Gaussian law, binomial PMF or asymptotic approximation.
 Library reuse: SamplingPrecision, canonical Reals, Ring, Lra, Psatz, Field.
 Boundary: Precise deterministic expectation/variance expressions for
 hypothetical Bernoulli sampling, not an actual PRNG independence theorem
 or a statement about observed people or normal confidence interval coverage.
*)
Theorem rate_count_rate_monotone_second : forall n m p q r, 0<=m -> q<=r -> rate_count n m p q<=rate_count n m p r.
Proof.
  intros; unfold rate_count; nra.
Qed.

(** [rate_count_variance_zero_all_impossible] (theorem).
 Mathematical meaning: Both impossible outcomes yield zero count variance expression.
 Exact proposition: This universal real formula is a quantitative
 sampling-size, marginal-rate or heterogeneity bound from the six reports.
 Premises and side conditions: All nonnegativity, probability unit-interval,
 strictness and sample size requirements are stated as explicit hypotheses.
 Proof/definition method: Use previously checked SamplingPrecision results
 or standard real algebra and ring to derive this exact formula. No claim
 presupposes a Gaussian law, binomial PMF or asymptotic approximation.
 Library reuse: SamplingPrecision, canonical Reals, Ring, Lra, Psatz, Field.
 Boundary: Precise deterministic expectation/variance expressions for
 hypothetical Bernoulli sampling, not an actual PRNG independence theorem
 or a statement about observed people or normal confidence interval coverage.
*)
Theorem rate_count_variance_zero_all_impossible : forall n m, rate_count_variance n m 0 0=0.
Proof.
  intros; unfold rate_count_variance,sampling_bernoulli_variance; ring.
Qed.

(** [rate_count_variance_zero_all_certain] (theorem).
 Mathematical meaning: Both certain outcomes yield zero Bernoulli count variance expression.
 Exact proposition: This universal real formula is a quantitative
 sampling-size, marginal-rate or heterogeneity bound from the six reports.
 Premises and side conditions: All nonnegativity, probability unit-interval,
 strictness and sample size requirements are stated as explicit hypotheses.
 Proof/definition method: Use previously checked SamplingPrecision results
 or standard real algebra and ring to derive this exact formula. No claim
 presupposes a Gaussian law, binomial PMF or asymptotic approximation.
 Library reuse: SamplingPrecision, canonical Reals, Ring, Lra, Psatz, Field.
 Boundary: Precise deterministic expectation/variance expressions for
 hypothetical Bernoulli sampling, not an actual PRNG independence theorem
 or a statement about observed people or normal confidence interval coverage.
*)
Theorem rate_count_variance_zero_all_certain : forall n m, rate_count_variance n m 1 1=0.
Proof.
  intros; unfold rate_count_variance,sampling_bernoulli_variance; ring.
Qed.

(** [rate_count_variance_balanced] (theorem).
 Mathematical meaning: Balanced success probabilities attain the sharp count-variance upper bound.
 Exact proposition: This universal real formula is a quantitative
 sampling-size, marginal-rate or heterogeneity bound from the six reports.
 Premises and side conditions: All nonnegativity, probability unit-interval,
 strictness and sample size requirements are stated as explicit hypotheses.
 Proof/definition method: Use previously checked SamplingPrecision results
 or standard real algebra and ring to derive this exact formula. No claim
 presupposes a Gaussian law, binomial PMF or asymptotic approximation.
 Library reuse: SamplingPrecision, canonical Reals, Ring, Lra, Psatz, Field.
 Boundary: Precise deterministic expectation/variance expressions for
 hypothetical Bernoulli sampling, not an actual PRNG independence theorem
 or a statement about observed people or normal confidence interval coverage.
*)
Theorem rate_count_variance_balanced : forall n m, rate_count_variance n m (1/2) (1/2)=(n+m)/4.
Proof.
  intros; unfold rate_count_variance,sampling_bernoulli_variance; ring.
Qed.

(** [rate_count_variance_gap_max] (theorem).
 Mathematical meaning: The exact heterogeneity gap from the maximum variance is a weighted sum of squared marginal imbalances.
 Exact proposition: This universal real formula is a quantitative
 sampling-size, marginal-rate or heterogeneity bound from the six reports.
 Premises and side conditions: All nonnegativity, probability unit-interval,
 strictness and sample size requirements are stated as explicit hypotheses.
 Proof/definition method: Use previously checked SamplingPrecision results
 or standard real algebra and ring to derive this exact formula. No claim
 presupposes a Gaussian law, binomial PMF or asymptotic approximation.
 Library reuse: SamplingPrecision, canonical Reals, Ring, Lra, Psatz, Field.
 Boundary: Precise deterministic expectation/variance expressions for
 hypothetical Bernoulli sampling, not an actual PRNG independence theorem
 or a statement about observed people or normal confidence interval coverage.
*)
Theorem rate_count_variance_gap_max : forall n m p q, (n+m)/4-rate_count_variance n m p q=n*(p-1/2)*(p-1/2)+m*(q-1/2)*(q-1/2).
Proof.
  intros; unfold rate_count_variance,sampling_bernoulli_variance; ring.
Qed.

(** [rate_count_variance_first_rate_difference] (theorem).
 Mathematical meaning: A first-event rate change has an exact count-variance sensitivity polynomial.
 Exact proposition: This universal real formula is a quantitative
 sampling-size, marginal-rate or heterogeneity bound from the six reports.
 Premises and side conditions: All nonnegativity, probability unit-interval,
 strictness and sample size requirements are stated as explicit hypotheses.
 Proof/definition method: Use previously checked SamplingPrecision results
 or standard real algebra and ring to derive this exact formula. No claim
 presupposes a Gaussian law, binomial PMF or asymptotic approximation.
 Library reuse: SamplingPrecision, canonical Reals, Ring, Lra, Psatz, Field.
 Boundary: Precise deterministic expectation/variance expressions for
 hypothetical Bernoulli sampling, not an actual PRNG independence theorem
 or a statement about observed people or normal confidence interval coverage.
*)
Theorem rate_count_variance_first_rate_difference : forall n m p q r, rate_count_variance n m r q-rate_count_variance n m p q=n*(r-p)*(1-r-p).
Proof.
  intros; unfold rate_count_variance,sampling_bernoulli_variance; ring.
Qed.

(** [rate_count_variance_second_rate_difference] (theorem).
 Mathematical meaning: Second-event rate changes obey the corresponding exact variance sensitivity expression.
 Exact proposition: This universal real formula is a quantitative
 sampling-size, marginal-rate or heterogeneity bound from the six reports.
 Premises and side conditions: All nonnegativity, probability unit-interval,
 strictness and sample size requirements are stated as explicit hypotheses.
 Proof/definition method: Use previously checked SamplingPrecision results
 or standard real algebra and ring to derive this exact formula. No claim
 presupposes a Gaussian law, binomial PMF or asymptotic approximation.
 Library reuse: SamplingPrecision, canonical Reals, Ring, Lra, Psatz, Field.
 Boundary: Precise deterministic expectation/variance expressions for
 hypothetical Bernoulli sampling, not an actual PRNG independence theorem
 or a statement about observed people or normal confidence interval coverage.
*)
Theorem rate_count_variance_second_rate_difference : forall n m p q r, rate_count_variance n m p r-rate_count_variance n m p q=m*(r-q)*(1-r-q).
Proof.
  intros; unfold rate_count_variance,sampling_bernoulli_variance; ring.
Qed.

(** [rate_count_variance_add_second_size] (theorem).
 Mathematical meaning: Variance targets are additive when adding independent second-rate trials.
 Exact proposition: This universal real formula is a quantitative
 sampling-size, marginal-rate or heterogeneity bound from the six reports.
 Premises and side conditions: All nonnegativity, probability unit-interval,
 strictness and sample size requirements are stated as explicit hypotheses.
 Proof/definition method: Use previously checked SamplingPrecision results
 or standard real algebra and ring to derive this exact formula. No claim
 presupposes a Gaussian law, binomial PMF or asymptotic approximation.
 Library reuse: SamplingPrecision, canonical Reals, Ring, Lra, Psatz, Field.
 Boundary: Precise deterministic expectation/variance expressions for
 hypothetical Bernoulli sampling, not an actual PRNG independence theorem
 or a statement about observed people or normal confidence interval coverage.
*)
Theorem rate_count_variance_add_second_size : forall n m k p q, rate_count_variance n (m+k) p q=rate_count_variance n m p q+k*sampling_bernoulli_variance q.
Proof.
  intros; unfold rate_count_variance; ring.
Qed.

(** [rate_count_variance_complement_first] (theorem).
 Mathematical meaning: Complementing the first Bernoulli outcome preserves its count variance.
 Exact proposition: This universal real formula is a quantitative
 sampling-size, marginal-rate or heterogeneity bound from the six reports.
 Premises and side conditions: All nonnegativity, probability unit-interval,
 strictness and sample size requirements are stated as explicit hypotheses.
 Proof/definition method: Use previously checked SamplingPrecision results
 or standard real algebra and ring to derive this exact formula. No claim
 presupposes a Gaussian law, binomial PMF or asymptotic approximation.
 Library reuse: SamplingPrecision, canonical Reals, Ring, Lra, Psatz, Field.
 Boundary: Precise deterministic expectation/variance expressions for
 hypothetical Bernoulli sampling, not an actual PRNG independence theorem
 or a statement about observed people or normal confidence interval coverage.
*)
Theorem rate_count_variance_complement_first : forall n m p q, rate_count_variance n m (1-p) q=rate_count_variance n m p q.
Proof.
  intros; unfold rate_count_variance,sampling_bernoulli_variance; ring.
Qed.

(** [rate_count_variance_complement_second] (theorem).
 Mathematical meaning: Complementing the second Bernoulli outcome preserves its count variance.
 Exact proposition: This universal real formula is a quantitative
 sampling-size, marginal-rate or heterogeneity bound from the six reports.
 Premises and side conditions: All nonnegativity, probability unit-interval,
 strictness and sample size requirements are stated as explicit hypotheses.
 Proof/definition method: Use previously checked SamplingPrecision results
 or standard real algebra and ring to derive this exact formula. No claim
 presupposes a Gaussian law, binomial PMF or asymptotic approximation.
 Library reuse: SamplingPrecision, canonical Reals, Ring, Lra, Psatz, Field.
 Boundary: Precise deterministic expectation/variance expressions for
 hypothetical Bernoulli sampling, not an actual PRNG independence theorem
 or a statement about observed people or normal confidence interval coverage.
*)
Theorem rate_count_variance_complement_second : forall n m p q, rate_count_variance n m p (1-q)=rate_count_variance n m p q.
Proof.
  intros; unfold rate_count_variance,sampling_bernoulli_variance; ring.
Qed.

(** [rate_count_variance_below_count] (theorem).
 Mathematical meaning: For event rates in [0,1], the binomial count variance expression does not exceed the expected success count.
 Exact proposition: This universal real formula is a quantitative
 sampling-size, marginal-rate or heterogeneity bound from the six reports.
 Premises and side conditions: All nonnegativity, probability unit-interval,
 strictness and sample size requirements are stated as explicit hypotheses.
 Proof/definition method: Use previously checked SamplingPrecision results
 or standard real algebra and ring to derive this exact formula. No claim
 presupposes a Gaussian law, binomial PMF or asymptotic approximation.
 Library reuse: SamplingPrecision, canonical Reals, Ring, Lra, Psatz, Field.
 Boundary: Precise deterministic expectation/variance expressions for
 hypothetical Bernoulli sampling, not an actual PRNG independence theorem
 or a statement about observed people or normal confidence interval coverage.
*)
Theorem rate_count_variance_below_count : forall n m p q, 0<=n -> 0<=m -> 0<=p -> p<=1 -> 0<=q -> q<=1 -> rate_count_variance n m p q<=rate_count n m p q.
Proof.
  intros n m p q Hn Hm Hp Hp1 Hq Hq1; unfold rate_count_variance,rate_count; pose proof (sampling_variance_below_success_probability p Hp Hp1) as A; pose proof (sampling_variance_below_success_probability q Hq Hq1) as B; nra.
Qed.

(** [rate_count_variance_below_failures] (theorem).
 Mathematical meaning: For feasible event rates, the variance expression is bounded by the expected number of failures as well.
 Exact proposition: This universal real formula is a quantitative
 sampling-size, marginal-rate or heterogeneity bound from the six reports.
 Premises and side conditions: All nonnegativity, probability unit-interval,
 strictness and sample size requirements are stated as explicit hypotheses.
 Proof/definition method: Use previously checked SamplingPrecision results
 or standard real algebra and ring to derive this exact formula. No claim
 presupposes a Gaussian law, binomial PMF or asymptotic approximation.
 Library reuse: SamplingPrecision, canonical Reals, Ring, Lra, Psatz, Field.
 Boundary: Precise deterministic expectation/variance expressions for
 hypothetical Bernoulli sampling, not an actual PRNG independence theorem
 or a statement about observed people or normal confidence interval coverage.
*)
Theorem rate_count_variance_below_failures : forall n m p q, 0<=n -> 0<=m -> 0<=p -> p<=1 -> 0<=q -> q<=1 -> rate_count_variance n m p q<=rate_count n m (1-p) (1-q).
Proof.
  intros n m p q Hn Hm Hp Hp1 Hq Hq1; unfold rate_count_variance,rate_count; pose proof (sampling_variance_below_failure_probability p Hp Hp1) as A; pose proof (sampling_variance_below_failure_probability q Hq Hq1) as B; nra.
Qed.
