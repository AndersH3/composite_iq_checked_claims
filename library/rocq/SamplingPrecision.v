(** Module: SamplingPrecision.v
 Purpose: Establish exact real and Bernoulli-moment calculations needed
 in the simulation reports' sample variance, expected rare count, pooled
 sample-size, standard-error and finite-resolution discussion.
 Mathematical representation: Sample size n and event probability p are
 real inputs. Variance and standard-error targets are explicit scalar
 expressions, with nondegeneracy and sample-size conditions in theorems.
 Explicit hypotheses: Every sampling formula is CONDITIONAL on the
 separately unproved independent Bernoulli sampling premise; n>0 and
 0<p<=1 are explicitly stipulated whenever a denominator is inverted.
 Library use: Rocq Stdlib Reals, Lra, Psatz, Field and Ring. No custom
 binomial PMF, combinatorics, integration or numerical square-root engine.
 Limitations: Verifies exact algebra of Bernoulli moments, not the theorem
 that independent Bernoulli observations have a binomial count law, not
 confidence-interval coverage and not a valid real IQ population model.
 Reproduction: rocq compile SamplingPrecision.v with Rocq Prover 9.2.
 AI disclosure: OpenAI ChatGPT assisted statement design, documentation,
 source refactoring and proof scripts. Only kernel compilation certifies them.
*)
From Stdlib Require Import Reals Lra Psatz Ring Field.
Open Scope R_scope.

(** [sampling_bernoulli_variance] (definition).
 Mathematical meaning: Ideal Bernoulli variance factor from a supplied event probability p.
 Exact declaration: sampling_bernoulli_variance (p:R) : R := p*(1-p).
 Premises and side conditions: Total real algebra here does not in
 itself assert independence, distributional coverage, or a physical count.
 Theorems provide explicit positive-denominator and probability bounds.
 Proof/definition method: Direct reuse of ordinary real arithmetic.
 Library reuse: Rocq Stdlib Reals, Lra, Psatz, Ring and Field; there is
 no custom summation or reconstruction of a Bernoulli distribution.
 Boundary: Algebraic ideal-sampling moment targets, not stochastic
 Bernoulli independence, Monte Carlo reliability or IQ calibration.
*)
Definition sampling_bernoulli_variance (p:R) : R:=p*(1-p).

(** [sampling_count_variance] (definition).
 Mathematical meaning: Ideal independent-Bernoulli success-count variance target, *conditional* on the sampling model.
 Exact declaration: sampling_count_variance (n p:R) : R := n*sampling_bernoulli_variance p.
 Premises and side conditions: Total real algebra here does not in
 itself assert independence, distributional coverage, or a physical count.
 Theorems provide explicit positive-denominator and probability bounds.
 Proof/definition method: Direct reuse of ordinary real arithmetic.
 Library reuse: Rocq Stdlib Reals, Lra, Psatz, Ring and Field; there is
 no custom summation or reconstruction of a Bernoulli distribution.
 Boundary: Algebraic ideal-sampling moment targets, not stochastic
 Bernoulli independence, Monte Carlo reliability or IQ calibration.
*)
Definition sampling_count_variance (n p:R) : R:=n*sampling_bernoulli_variance p.

(** [sampling_mean_count] (definition).
 Mathematical meaning: The target expected count under n ideal independent Bernoulli observations.
 Exact declaration: sampling_mean_count (n p:R) : R := n*p.
 Premises and side conditions: Total real algebra here does not in
 itself assert independence, distributional coverage, or a physical count.
 Theorems provide explicit positive-denominator and probability bounds.
 Proof/definition method: Direct reuse of ordinary real arithmetic.
 Library reuse: Rocq Stdlib Reals, Lra, Psatz, Ring and Field; there is
 no custom summation or reconstruction of a Bernoulli distribution.
 Boundary: Algebraic ideal-sampling moment targets, not stochastic
 Bernoulli independence, Monte Carlo reliability or IQ calibration.
*)
Definition sampling_mean_count (n p:R) : R:=n*p.

(** [sampling_frequency_variance] (definition).
 Mathematical meaning: Ideal event-frequency variance target for positive real sample size.
 Exact declaration: sampling_frequency_variance (n p:R) : R := sampling_bernoulli_variance p/n.
 Premises and side conditions: Total real algebra here does not in
 itself assert independence, distributional coverage, or a physical count.
 Theorems provide explicit positive-denominator and probability bounds.
 Proof/definition method: Direct reuse of ordinary real arithmetic.
 Library reuse: Rocq Stdlib Reals, Lra, Psatz, Ring and Field; there is
 no custom summation or reconstruction of a Bernoulli distribution.
 Boundary: Algebraic ideal-sampling moment targets, not stochastic
 Bernoulli independence, Monte Carlo reliability or IQ calibration.
*)
Definition sampling_frequency_variance (n p:R) : R:=sampling_bernoulli_variance p/n.

(** [sampling_relative_variance] (definition).
 Mathematical meaning: Squared relative standard error of the ideal Bernoulli sample fraction.
 Exact declaration: sampling_relative_variance (n p:R) : R := (1-p)/(n*p).
 Premises and side conditions: Total real algebra here does not in
 itself assert independence, distributional coverage, or a physical count.
 Theorems provide explicit positive-denominator and probability bounds.
 Proof/definition method: Direct reuse of ordinary real arithmetic.
 Library reuse: Rocq Stdlib Reals, Lra, Psatz, Ring and Field; there is
 no custom summation or reconstruction of a Bernoulli distribution.
 Boundary: Algebraic ideal-sampling moment targets, not stochastic
 Bernoulli independence, Monte Carlo reliability or IQ calibration.
*)
Definition sampling_relative_variance (n p:R) : R:=(1-p)/(n*p).

(** [sampling_variance_complement] (theorem).
 Mathematical meaning: The Bernoulli variance is invariant under exchanging successes and failures.
 Exact proposition: forall p, sampling_bernoulli_variance (1-p)=sampling_bernoulli_variance p.
 Premises and side conditions: All probability-domain, sample-size
 positivity, division and nondegeneracy restrictions needed here are
 written in the signature; independence of physical or pseudorandom
 observations is NOT inferred from the scalar moment expressions.
 Proof/definition method: Reuse earlier established variance identities,
 Rocq Stdlib real ring, nonlinear arithmetic and Field lemmas.
 Library reuse: Canonical Stdlib R, Lra, Psatz, Ring, Field, real inverse
 and ordering laws; no independent binomial mass function is created.
 Boundary: Conditional Bernoulli precision algebra only. This neither
 derives a binomial random-variable law nor exact confidence coverage,
 validates a simulation PRNG, or establishes empirical IQ distributions.
*)
Theorem sampling_variance_complement: forall p, sampling_bernoulli_variance (1-p)=sampling_bernoulli_variance p.
Proof.
  intro p; unfold sampling_bernoulli_variance; field; nra.
Qed.

(** [sampling_variance_nonnegative] (theorem).
 Mathematical meaning: Every admissible event probability determines a nonnegative Bernoulli variance target.
 Exact proposition: forall p, 0<=p -> p<=1 -> 0<=sampling_bernoulli_variance p.
 Premises and side conditions: All probability-domain, sample-size
 positivity, division and nondegeneracy restrictions needed here are
 written in the signature; independence of physical or pseudorandom
 observations is NOT inferred from the scalar moment expressions.
 Proof/definition method: Reuse earlier established variance identities,
 Rocq Stdlib real ring, nonlinear arithmetic and Field lemmas.
 Library reuse: Canonical Stdlib R, Lra, Psatz, Ring, Field, real inverse
 and ordering laws; no independent binomial mass function is created.
 Boundary: Conditional Bernoulli precision algebra only. This neither
 derives a binomial random-variable law nor exact confidence coverage,
 validates a simulation PRNG, or establishes empirical IQ distributions.
*)
Theorem sampling_variance_nonnegative: forall p, 0<=p -> p<=1 -> 0<=sampling_bernoulli_variance p.
Proof.
  intros p Hl Hu; unfold sampling_bernoulli_variance; nra.
Qed.

(** [sampling_variance_strictly_positive] (theorem).
 Mathematical meaning: A nondegenerate Bernoulli event has strictly positive variance.
 Exact proposition: forall p, 0<p -> p<1 -> 0<sampling_bernoulli_variance p.
 Premises and side conditions: All probability-domain, sample-size
 positivity, division and nondegeneracy restrictions needed here are
 written in the signature; independence of physical or pseudorandom
 observations is NOT inferred from the scalar moment expressions.
 Proof/definition method: Reuse earlier established variance identities,
 Rocq Stdlib real ring, nonlinear arithmetic and Field lemmas.
 Library reuse: Canonical Stdlib R, Lra, Psatz, Ring, Field, real inverse
 and ordering laws; no independent binomial mass function is created.
 Boundary: Conditional Bernoulli precision algebra only. This neither
 derives a binomial random-variable law nor exact confidence coverage,
 validates a simulation PRNG, or establishes empirical IQ distributions.
*)
Theorem sampling_variance_strictly_positive: forall p, 0<p -> p<1 -> 0<sampling_bernoulli_variance p.
Proof.
  intros p Hl Hu; unfold sampling_bernoulli_variance; nra.
Qed.

(** [sampling_variance_zero_iff_extreme] (theorem).
 Mathematical meaning: The variance target vanishes exactly for impossible or certain events within the unit probability interval.
 Exact proposition: forall p, 0<=p -> p<=1 -> (sampling_bernoulli_variance p=0 <-> p=0 \/ p=1).
 Premises and side conditions: All probability-domain, sample-size
 positivity, division and nondegeneracy restrictions needed here are
 written in the signature; independence of physical or pseudorandom
 observations is NOT inferred from the scalar moment expressions.
 Proof/definition method: Reuse earlier established variance identities,
 Rocq Stdlib real ring, nonlinear arithmetic and Field lemmas.
 Library reuse: Canonical Stdlib R, Lra, Psatz, Ring, Field, real inverse
 and ordering laws; no independent binomial mass function is created.
 Boundary: Conditional Bernoulli precision algebra only. This neither
 derives a binomial random-variable law nor exact confidence coverage,
 validates a simulation PRNG, or establishes empirical IQ distributions.
*)
Theorem sampling_variance_zero_iff_extreme: forall p, 0<=p -> p<=1 -> (sampling_bernoulli_variance p=0 <-> p=0 \/ p=1).
Proof.
  intros p Hl Hu; unfold sampling_bernoulli_variance; split; intro H. - apply Rmult_integral in H. destruct H as [H|H]; [left; exact H|right; lra]. - destruct H as [H|H]; subst; ring.
Qed.

(** [sampling_variance_maximum] (theorem).
 Mathematical meaning: Bernoulli variance cannot exceed a quarter, with the bound independent of sample size.
 Exact proposition: forall p, sampling_bernoulli_variance p<=1/4.
 Premises and side conditions: All probability-domain, sample-size
 positivity, division and nondegeneracy restrictions needed here are
 written in the signature; independence of physical or pseudorandom
 observations is NOT inferred from the scalar moment expressions.
 Proof/definition method: Reuse earlier established variance identities,
 Rocq Stdlib real ring, nonlinear arithmetic and Field lemmas.
 Library reuse: Canonical Stdlib R, Lra, Psatz, Ring, Field, real inverse
 and ordering laws; no independent binomial mass function is created.
 Boundary: Conditional Bernoulli precision algebra only. This neither
 derives a binomial random-variable law nor exact confidence coverage,
 validates a simulation PRNG, or establishes empirical IQ distributions.
*)
Theorem sampling_variance_maximum: forall p, sampling_bernoulli_variance p<=1/4.
Proof.
  intro p. pose proof (Rle_0_sqr (p-1/2)) as Hsquare. unfold Rsqr in Hsquare. unfold sampling_bernoulli_variance. nra.
Qed.

(** [sampling_variance_maximum_attained] (theorem).
 Mathematical meaning: A balanced event with probability one half achieves the maximal Bernoulli variance.
 Exact proposition: sampling_bernoulli_variance (1/2)=1/4.
 Premises and side conditions: All probability-domain, sample-size
 positivity, division and nondegeneracy restrictions needed here are
 written in the signature; independence of physical or pseudorandom
 observations is NOT inferred from the scalar moment expressions.
 Proof/definition method: Reuse earlier established variance identities,
 Rocq Stdlib real ring, nonlinear arithmetic and Field lemmas.
 Library reuse: Canonical Stdlib R, Lra, Psatz, Ring, Field, real inverse
 and ordering laws; no independent binomial mass function is created.
 Boundary: Conditional Bernoulli precision algebra only. This neither
 derives a binomial random-variable law nor exact confidence coverage,
 validates a simulation PRNG, or establishes empirical IQ distributions.
*)
Theorem sampling_variance_maximum_attained: sampling_bernoulli_variance (1/2)=1/4.
Proof.
  unfold sampling_bernoulli_variance; field; nra.
Qed.

(** [sampling_variance_maximum_unique] (theorem).
 Mathematical meaning: Only a balanced Bernoulli event attains the variance upper bound.
 Exact proposition: forall p, sampling_bernoulli_variance p=1/4 -> p=1/2.
 Premises and side conditions: All probability-domain, sample-size
 positivity, division and nondegeneracy restrictions needed here are
 written in the signature; independence of physical or pseudorandom
 observations is NOT inferred from the scalar moment expressions.
 Proof/definition method: Reuse earlier established variance identities,
 Rocq Stdlib real ring, nonlinear arithmetic and Field lemmas.
 Library reuse: Canonical Stdlib R, Lra, Psatz, Ring, Field, real inverse
 and ordering laws; no independent binomial mass function is created.
 Boundary: Conditional Bernoulli precision algebra only. This neither
 derives a binomial random-variable law nor exact confidence coverage,
 validates a simulation PRNG, or establishes empirical IQ distributions.
*)
Theorem sampling_variance_maximum_unique: forall p, sampling_bernoulli_variance p=1/4 -> p=1/2.
Proof.
  intros p H. unfold sampling_bernoulli_variance in H. assert (Hs:(p-1/2)*(p-1/2)=0) by nra. apply Rmult_integral in Hs. destruct Hs as [Hleft|Hright]; lra.
Qed.

(** [sampling_variance_midpoint_gap] (theorem).
 Mathematical meaning: The loss in Bernoulli variance relative to its maximum is exactly squared distance from probability one half.
 Exact proposition: forall p, 1/4-sampling_bernoulli_variance p=(p-1/2)*(p-1/2).
 Premises and side conditions: All probability-domain, sample-size
 positivity, division and nondegeneracy restrictions needed here are
 written in the signature; independence of physical or pseudorandom
 observations is NOT inferred from the scalar moment expressions.
 Proof/definition method: Reuse earlier established variance identities,
 Rocq Stdlib real ring, nonlinear arithmetic and Field lemmas.
 Library reuse: Canonical Stdlib R, Lra, Psatz, Ring, Field, real inverse
 and ordering laws; no independent binomial mass function is created.
 Boundary: Conditional Bernoulli precision algebra only. This neither
 derives a binomial random-variable law nor exact confidence coverage,
 validates a simulation PRNG, or establishes empirical IQ distributions.
*)
Theorem sampling_variance_midpoint_gap: forall p, 1/4-sampling_bernoulli_variance p=(p-1/2)*(p-1/2).
Proof.
  intro p; unfold sampling_bernoulli_variance; field; nra.
Qed.

(** [sampling_variance_comparison] (theorem).
 Mathematical meaning: The exact change in Bernoulli variance factors by probability difference and complement of the probability sum.
 Exact proposition: forall p q, sampling_bernoulli_variance q-sampling_bernoulli_variance p=(q-p)*(1-p-q).
 Premises and side conditions: All probability-domain, sample-size
 positivity, division and nondegeneracy restrictions needed here are
 written in the signature; independence of physical or pseudorandom
 observations is NOT inferred from the scalar moment expressions.
 Proof/definition method: Reuse earlier established variance identities,
 Rocq Stdlib real ring, nonlinear arithmetic and Field lemmas.
 Library reuse: Canonical Stdlib R, Lra, Psatz, Ring, Field, real inverse
 and ordering laws; no independent binomial mass function is created.
 Boundary: Conditional Bernoulli precision algebra only. This neither
 derives a binomial random-variable law nor exact confidence coverage,
 validates a simulation PRNG, or establishes empirical IQ distributions.
*)
Theorem sampling_variance_comparison: forall p q, sampling_bernoulli_variance q-sampling_bernoulli_variance p=(q-p)*(1-p-q).
Proof.
  intros p q; unfold sampling_bernoulli_variance; field; nra.
Qed.

(** [sampling_variance_monotone_lower_half] (theorem).
 Mathematical meaning: Increasing the event rate below one half cannot decrease its sampling variance.
 Exact proposition: forall p q, 0<=p -> p<=q -> q<=1/2 -> sampling_bernoulli_variance p<=sampling_bernoulli_variance q.
 Premises and side conditions: All probability-domain, sample-size
 positivity, division and nondegeneracy restrictions needed here are
 written in the signature; independence of physical or pseudorandom
 observations is NOT inferred from the scalar moment expressions.
 Proof/definition method: Reuse earlier established variance identities,
 Rocq Stdlib real ring, nonlinear arithmetic and Field lemmas.
 Library reuse: Canonical Stdlib R, Lra, Psatz, Ring, Field, real inverse
 and ordering laws; no independent binomial mass function is created.
 Boundary: Conditional Bernoulli precision algebra only. This neither
 derives a binomial random-variable law nor exact confidence coverage,
 validates a simulation PRNG, or establishes empirical IQ distributions.
*)
Theorem sampling_variance_monotone_lower_half: forall p q, 0<=p -> p<=q -> q<=1/2 -> sampling_bernoulli_variance p<=sampling_bernoulli_variance q.
Proof.
  intros p q H0 Hpq Hq. pose proof (sampling_variance_comparison p q) as Hgap. nra.
Qed.

(** [sampling_variance_strict_lower_half] (theorem).
 Mathematical meaning: A strict rise in probability below one half strictly increases the ideal Bernoulli variance.
 Exact proposition: forall p q, 0<=p -> p<q -> q<=1/2 -> sampling_bernoulli_variance p<sampling_bernoulli_variance q.
 Premises and side conditions: All probability-domain, sample-size
 positivity, division and nondegeneracy restrictions needed here are
 written in the signature; independence of physical or pseudorandom
 observations is NOT inferred from the scalar moment expressions.
 Proof/definition method: Reuse earlier established variance identities,
 Rocq Stdlib real ring, nonlinear arithmetic and Field lemmas.
 Library reuse: Canonical Stdlib R, Lra, Psatz, Ring, Field, real inverse
 and ordering laws; no independent binomial mass function is created.
 Boundary: Conditional Bernoulli precision algebra only. This neither
 derives a binomial random-variable law nor exact confidence coverage,
 validates a simulation PRNG, or establishes empirical IQ distributions.
*)
Theorem sampling_variance_strict_lower_half: forall p q, 0<=p -> p<q -> q<=1/2 -> sampling_bernoulli_variance p<sampling_bernoulli_variance q.
Proof.
  intros p q H0 Hpq Hq. pose proof (sampling_variance_comparison p q) as Hid. assert (Hpos:0<(q-p)*(1-p-q)) by nra. nra.
Qed.

(** [sampling_variance_monotone_upper_half] (theorem).
 Mathematical meaning: Increasing the event rate above one half cannot increase its sampling variance.
 Exact proposition: forall p q, 1/2<=p -> p<=q -> q<=1 -> sampling_bernoulli_variance q<=sampling_bernoulli_variance p.
 Premises and side conditions: All probability-domain, sample-size
 positivity, division and nondegeneracy restrictions needed here are
 written in the signature; independence of physical or pseudorandom
 observations is NOT inferred from the scalar moment expressions.
 Proof/definition method: Reuse earlier established variance identities,
 Rocq Stdlib real ring, nonlinear arithmetic and Field lemmas.
 Library reuse: Canonical Stdlib R, Lra, Psatz, Ring, Field, real inverse
 and ordering laws; no independent binomial mass function is created.
 Boundary: Conditional Bernoulli precision algebra only. This neither
 derives a binomial random-variable law nor exact confidence coverage,
 validates a simulation PRNG, or establishes empirical IQ distributions.
*)
Theorem sampling_variance_monotone_upper_half: forall p q, 1/2<=p -> p<=q -> q<=1 -> sampling_bernoulli_variance q<=sampling_bernoulli_variance p.
Proof.
  intros p q Hp Hpq Hq. pose proof (sampling_variance_comparison p q) as Hid. nra.
Qed.

(** [sampling_variance_strict_upper_half] (theorem).
 Mathematical meaning: Moving farther above one half strictly decreases the Bernoulli variance.
 Exact proposition: forall p q, 1/2<=p -> p<q -> q<=1 -> sampling_bernoulli_variance q<sampling_bernoulli_variance p.
 Premises and side conditions: All probability-domain, sample-size
 positivity, division and nondegeneracy restrictions needed here are
 written in the signature; independence of physical or pseudorandom
 observations is NOT inferred from the scalar moment expressions.
 Proof/definition method: Reuse earlier established variance identities,
 Rocq Stdlib real ring, nonlinear arithmetic and Field lemmas.
 Library reuse: Canonical Stdlib R, Lra, Psatz, Ring, Field, real inverse
 and ordering laws; no independent binomial mass function is created.
 Boundary: Conditional Bernoulli precision algebra only. This neither
 derives a binomial random-variable law nor exact confidence coverage,
 validates a simulation PRNG, or establishes empirical IQ distributions.
*)
Theorem sampling_variance_strict_upper_half: forall p q, 1/2<=p -> p<q -> q<=1 -> sampling_bernoulli_variance q<sampling_bernoulli_variance p.
Proof.
  intros p q Hp Hpq Hq. pose proof (sampling_variance_comparison p q) as Hid. assert (Hneg:(q-p)*(1-p-q)<0) by nra. nra.
Qed.

(** [sampling_variance_below_success_probability] (theorem).
 Mathematical meaning: The count variance factor is no greater than the event probability.
 Exact proposition: forall p, 0<=p -> p<=1 -> sampling_bernoulli_variance p<=p.
 Premises and side conditions: All probability-domain, sample-size
 positivity, division and nondegeneracy restrictions needed here are
 written in the signature; independence of physical or pseudorandom
 observations is NOT inferred from the scalar moment expressions.
 Proof/definition method: Reuse earlier established variance identities,
 Rocq Stdlib real ring, nonlinear arithmetic and Field lemmas.
 Library reuse: Canonical Stdlib R, Lra, Psatz, Ring, Field, real inverse
 and ordering laws; no independent binomial mass function is created.
 Boundary: Conditional Bernoulli precision algebra only. This neither
 derives a binomial random-variable law nor exact confidence coverage,
 validates a simulation PRNG, or establishes empirical IQ distributions.
*)
Theorem sampling_variance_below_success_probability: forall p, 0<=p -> p<=1 -> sampling_bernoulli_variance p<=p.
Proof.
  intros p H0 H1; unfold sampling_bernoulli_variance; nra.
Qed.

(** [sampling_variance_below_failure_probability] (theorem).
 Mathematical meaning: The variance factor is also no greater than the failure probability.
 Exact proposition: forall p, 0<=p -> p<=1 -> sampling_bernoulli_variance p<=1-p.
 Premises and side conditions: All probability-domain, sample-size
 positivity, division and nondegeneracy restrictions needed here are
 written in the signature; independence of physical or pseudorandom
 observations is NOT inferred from the scalar moment expressions.
 Proof/definition method: Reuse earlier established variance identities,
 Rocq Stdlib real ring, nonlinear arithmetic and Field lemmas.
 Library reuse: Canonical Stdlib R, Lra, Psatz, Ring, Field, real inverse
 and ordering laws; no independent binomial mass function is created.
 Boundary: Conditional Bernoulli precision algebra only. This neither
 derives a binomial random-variable law nor exact confidence coverage,
 validates a simulation PRNG, or establishes empirical IQ distributions.
*)
Theorem sampling_variance_below_failure_probability: forall p, 0<=p -> p<=1 -> sampling_bernoulli_variance p<=1-p.
Proof.
  intros p H0 H1; unfold sampling_bernoulli_variance; nra.
Qed.

(** [sampling_count_variance_nonnegative] (theorem).
 Mathematical meaning: With nonnegative sample size and a valid probability, the ideal count variance is nonnegative.
 Exact proposition: forall n p, 0<=n -> 0<=p -> p<=1 -> 0<=sampling_count_variance n p.
 Premises and side conditions: All probability-domain, sample-size
 positivity, division and nondegeneracy restrictions needed here are
 written in the signature; independence of physical or pseudorandom
 observations is NOT inferred from the scalar moment expressions.
 Proof/definition method: Reuse earlier established variance identities,
 Rocq Stdlib real ring, nonlinear arithmetic and Field lemmas.
 Library reuse: Canonical Stdlib R, Lra, Psatz, Ring, Field, real inverse
 and ordering laws; no independent binomial mass function is created.
 Boundary: Conditional Bernoulli precision algebra only. This neither
 derives a binomial random-variable law nor exact confidence coverage,
 validates a simulation PRNG, or establishes empirical IQ distributions.
*)
Theorem sampling_count_variance_nonnegative: forall n p, 0<=n -> 0<=p -> p<=1 -> 0<=sampling_count_variance n p.
Proof.
  intros n p Hn Hp H1; unfold sampling_count_variance. apply Rmult_le_pos; [exact Hn|apply sampling_variance_nonnegative; assumption].
Qed.

(** [sampling_count_variance_strict_positive] (theorem).
 Mathematical meaning: With positive sample size and nondegenerate event probability, the ideal count variance is positive.
 Exact proposition: forall n p, 0<n -> 0<p -> p<1 -> 0<sampling_count_variance n p.
 Premises and side conditions: All probability-domain, sample-size
 positivity, division and nondegeneracy restrictions needed here are
 written in the signature; independence of physical or pseudorandom
 observations is NOT inferred from the scalar moment expressions.
 Proof/definition method: Reuse earlier established variance identities,
 Rocq Stdlib real ring, nonlinear arithmetic and Field lemmas.
 Library reuse: Canonical Stdlib R, Lra, Psatz, Ring, Field, real inverse
 and ordering laws; no independent binomial mass function is created.
 Boundary: Conditional Bernoulli precision algebra only. This neither
 derives a binomial random-variable law nor exact confidence coverage,
 validates a simulation PRNG, or establishes empirical IQ distributions.
*)
Theorem sampling_count_variance_strict_positive: forall n p, 0<n -> 0<p -> p<1 -> 0<sampling_count_variance n p.
Proof.
  intros n p Hn Hp H1; unfold sampling_count_variance; apply Rmult_lt_0_compat; [exact Hn|apply sampling_variance_strictly_positive; assumption].
Qed.

(** [sampling_count_variance_additive] (theorem).
 Mathematical meaning: The total variance target for two independent equal-rate batches is the sum of their count variance targets.
 Exact proposition: forall n m p, sampling_count_variance (n+m) p = sampling_count_variance n p + sampling_count_variance m p.
 Premises and side conditions: All probability-domain, sample-size
 positivity, division and nondegeneracy restrictions needed here are
 written in the signature; independence of physical or pseudorandom
 observations is NOT inferred from the scalar moment expressions.
 Proof/definition method: Reuse earlier established variance identities,
 Rocq Stdlib real ring, nonlinear arithmetic and Field lemmas.
 Library reuse: Canonical Stdlib R, Lra, Psatz, Ring, Field, real inverse
 and ordering laws; no independent binomial mass function is created.
 Boundary: Conditional Bernoulli precision algebra only. This neither
 derives a binomial random-variable law nor exact confidence coverage,
 validates a simulation PRNG, or establishes empirical IQ distributions.
*)
Theorem sampling_count_variance_additive: forall n m p, sampling_count_variance (n+m) p = sampling_count_variance n p + sampling_count_variance m p.
Proof.
  intros; unfold sampling_count_variance; ring.
Qed.

(** [sampling_count_variance_monotone_size] (theorem).
 Mathematical meaning: The ideal success-count variance cannot decrease when more independent draws are added.
 Exact proposition: forall n m p, n<=m -> 0<=p -> p<=1 -> sampling_count_variance n p<=sampling_count_variance m p.
 Premises and side conditions: All probability-domain, sample-size
 positivity, division and nondegeneracy restrictions needed here are
 written in the signature; independence of physical or pseudorandom
 observations is NOT inferred from the scalar moment expressions.
 Proof/definition method: Reuse earlier established variance identities,
 Rocq Stdlib real ring, nonlinear arithmetic and Field lemmas.
 Library reuse: Canonical Stdlib R, Lra, Psatz, Ring, Field, real inverse
 and ordering laws; no independent binomial mass function is created.
 Boundary: Conditional Bernoulli precision algebra only. This neither
 derives a binomial random-variable law nor exact confidence coverage,
 validates a simulation PRNG, or establishes empirical IQ distributions.
*)
Theorem sampling_count_variance_monotone_size: forall n m p, n<=m -> 0<=p -> p<=1 -> sampling_count_variance n p<=sampling_count_variance m p.
Proof.
  intros n m p Hnm Hp H1. unfold sampling_count_variance. pose proof (sampling_variance_nonnegative p Hp H1); nra.
Qed.

(** [sampling_count_variance_strict_size] (theorem).
 Mathematical meaning: For a nondegenerate event, increasing independent sample count strictly increases count variance.
 Exact proposition: forall n m p, n<m -> 0<p -> p<1 -> sampling_count_variance n p<sampling_count_variance m p.
 Premises and side conditions: All probability-domain, sample-size
 positivity, division and nondegeneracy restrictions needed here are
 written in the signature; independence of physical or pseudorandom
 observations is NOT inferred from the scalar moment expressions.
 Proof/definition method: Reuse earlier established variance identities,
 Rocq Stdlib real ring, nonlinear arithmetic and Field lemmas.
 Library reuse: Canonical Stdlib R, Lra, Psatz, Ring, Field, real inverse
 and ordering laws; no independent binomial mass function is created.
 Boundary: Conditional Bernoulli precision algebra only. This neither
 derives a binomial random-variable law nor exact confidence coverage,
 validates a simulation PRNG, or establishes empirical IQ distributions.
*)
Theorem sampling_count_variance_strict_size: forall n m p, n<m -> 0<p -> p<1 -> sampling_count_variance n p<sampling_count_variance m p.
Proof.
  intros n m p Hnm Hp H1. unfold sampling_count_variance. pose proof (sampling_variance_strictly_positive p Hp H1); nra.
Qed.

(** [sampling_count_variance_maximum] (theorem).
 Mathematical meaning: The variance of an ideal Bernoulli count is at most one quarter of the number of draws.
 Exact proposition: forall n p, 0<=n -> sampling_count_variance n p<=n/4.
 Premises and side conditions: All probability-domain, sample-size
 positivity, division and nondegeneracy restrictions needed here are
 written in the signature; independence of physical or pseudorandom
 observations is NOT inferred from the scalar moment expressions.
 Proof/definition method: Reuse earlier established variance identities,
 Rocq Stdlib real ring, nonlinear arithmetic and Field lemmas.
 Library reuse: Canonical Stdlib R, Lra, Psatz, Ring, Field, real inverse
 and ordering laws; no independent binomial mass function is created.
 Boundary: Conditional Bernoulli precision algebra only. This neither
 derives a binomial random-variable law nor exact confidence coverage,
 validates a simulation PRNG, or establishes empirical IQ distributions.
*)
Theorem sampling_count_variance_maximum: forall n p, 0<=n -> sampling_count_variance n p<=n/4.
Proof.
  intros n p Hn. unfold sampling_count_variance. pose proof (sampling_variance_maximum p); nra.
Qed.

(** [sampling_count_variance_le_expected_count] (theorem).
 Mathematical meaning: For a valid event probability, ideal success-count variance does not exceed expected successes.
 Exact proposition: forall n p, 0<=n -> 0<=p -> p<=1 -> sampling_count_variance n p<=sampling_mean_count n p.
 Premises and side conditions: All probability-domain, sample-size
 positivity, division and nondegeneracy restrictions needed here are
 written in the signature; independence of physical or pseudorandom
 observations is NOT inferred from the scalar moment expressions.
 Proof/definition method: Reuse earlier established variance identities,
 Rocq Stdlib real ring, nonlinear arithmetic and Field lemmas.
 Library reuse: Canonical Stdlib R, Lra, Psatz, Ring, Field, real inverse
 and ordering laws; no independent binomial mass function is created.
 Boundary: Conditional Bernoulli precision algebra only. This neither
 derives a binomial random-variable law nor exact confidence coverage,
 validates a simulation PRNG, or establishes empirical IQ distributions.
*)
Theorem sampling_count_variance_le_expected_count: forall n p, 0<=n -> 0<=p -> p<=1 -> sampling_count_variance n p<=sampling_mean_count n p.
Proof.
  intros n p Hn Hp H1; unfold sampling_count_variance,sampling_bernoulli_variance,sampling_mean_count; nra.
Qed.

(** [sampling_count_variance_le_expected_failures] (theorem).
 Mathematical meaning: Count variance is also bounded by the expected number of failures.
 Exact proposition: forall n p, 0<=n -> 0<=p -> p<=1 -> sampling_count_variance n p<=n*(1-p).
 Premises and side conditions: All probability-domain, sample-size
 positivity, division and nondegeneracy restrictions needed here are
 written in the signature; independence of physical or pseudorandom
 observations is NOT inferred from the scalar moment expressions.
 Proof/definition method: Reuse earlier established variance identities,
 Rocq Stdlib real ring, nonlinear arithmetic and Field lemmas.
 Library reuse: Canonical Stdlib R, Lra, Psatz, Ring, Field, real inverse
 and ordering laws; no independent binomial mass function is created.
 Boundary: Conditional Bernoulli precision algebra only. This neither
 derives a binomial random-variable law nor exact confidence coverage,
 validates a simulation PRNG, or establishes empirical IQ distributions.
*)
Theorem sampling_count_variance_le_expected_failures: forall n p, 0<=n -> 0<=p -> p<=1 -> sampling_count_variance n p<=n*(1-p).
Proof.
  intros n p Hn Hp H1. unfold sampling_count_variance,sampling_bernoulli_variance. assert (Hsq:0<=(1-p)*(1-p)) by nra. assert (Hprod:0<=n*((1-p)*(1-p))) by (apply Rmult_le_pos; assumption). nra.
Qed.

(** [sampling_mean_count_additive] (theorem).
 Mathematical meaning: Expected independent event counts are additive over replicate sizes.
 Exact proposition: forall n m p, sampling_mean_count (n+m) p = sampling_mean_count n p+sampling_mean_count m p.
 Premises and side conditions: All probability-domain, sample-size
 positivity, division and nondegeneracy restrictions needed here are
 written in the signature; independence of physical or pseudorandom
 observations is NOT inferred from the scalar moment expressions.
 Proof/definition method: Reuse earlier established variance identities,
 Rocq Stdlib real ring, nonlinear arithmetic and Field lemmas.
 Library reuse: Canonical Stdlib R, Lra, Psatz, Ring, Field, real inverse
 and ordering laws; no independent binomial mass function is created.
 Boundary: Conditional Bernoulli precision algebra only. This neither
 derives a binomial random-variable law nor exact confidence coverage,
 validates a simulation PRNG, or establishes empirical IQ distributions.
*)
Theorem sampling_mean_count_additive: forall n m p, sampling_mean_count (n+m) p = sampling_mean_count n p+sampling_mean_count m p.
Proof.
  intros; unfold sampling_mean_count; ring.
Qed.

(** [sampling_mean_count_success_failure_partition] (theorem).
 Mathematical meaning: Expected successes and expected failures add to total sample size.
 Exact proposition: forall n p, sampling_mean_count n p+sampling_mean_count n (1-p)=n.
 Premises and side conditions: All probability-domain, sample-size
 positivity, division and nondegeneracy restrictions needed here are
 written in the signature; independence of physical or pseudorandom
 observations is NOT inferred from the scalar moment expressions.
 Proof/definition method: Reuse earlier established variance identities,
 Rocq Stdlib real ring, nonlinear arithmetic and Field lemmas.
 Library reuse: Canonical Stdlib R, Lra, Psatz, Ring, Field, real inverse
 and ordering laws; no independent binomial mass function is created.
 Boundary: Conditional Bernoulli precision algebra only. This neither
 derives a binomial random-variable law nor exact confidence coverage,
 validates a simulation PRNG, or establishes empirical IQ distributions.
*)
Theorem sampling_mean_count_success_failure_partition: forall n p, sampling_mean_count n p+sampling_mean_count n (1-p)=n.
Proof.
  intros; unfold sampling_mean_count; ring.
Qed.

(** [sampling_mean_count_within_sample_size] (theorem).
 Mathematical meaning: The ideal expected success count lies between zero and sample size.
 Exact proposition: forall n p, 0<=n -> 0<=p -> p<=1 -> 0<=sampling_mean_count n p<=n.
 Premises and side conditions: All probability-domain, sample-size
 positivity, division and nondegeneracy restrictions needed here are
 written in the signature; independence of physical or pseudorandom
 observations is NOT inferred from the scalar moment expressions.
 Proof/definition method: Reuse earlier established variance identities,
 Rocq Stdlib real ring, nonlinear arithmetic and Field lemmas.
 Library reuse: Canonical Stdlib R, Lra, Psatz, Ring, Field, real inverse
 and ordering laws; no independent binomial mass function is created.
 Boundary: Conditional Bernoulli precision algebra only. This neither
 derives a binomial random-variable law nor exact confidence coverage,
 validates a simulation PRNG, or establishes empirical IQ distributions.
*)
Theorem sampling_mean_count_within_sample_size: forall n p, 0<=n -> 0<=p -> p<=1 -> 0<=sampling_mean_count n p<=n.
Proof.
  intros n p Hn Hp H1; unfold sampling_mean_count; nra.
Qed.

(** [sampling_mean_count_monotone_rate] (theorem).
 Mathematical meaning: For fixed nonnegative sample size, increasing population event probability increases expected successes.
 Exact proposition: forall n p q, 0<=n -> p<=q -> sampling_mean_count n p<=sampling_mean_count n q.
 Premises and side conditions: All probability-domain, sample-size
 positivity, division and nondegeneracy restrictions needed here are
 written in the signature; independence of physical or pseudorandom
 observations is NOT inferred from the scalar moment expressions.
 Proof/definition method: Reuse earlier established variance identities,
 Rocq Stdlib real ring, nonlinear arithmetic and Field lemmas.
 Library reuse: Canonical Stdlib R, Lra, Psatz, Ring, Field, real inverse
 and ordering laws; no independent binomial mass function is created.
 Boundary: Conditional Bernoulli precision algebra only. This neither
 derives a binomial random-variable law nor exact confidence coverage,
 validates a simulation PRNG, or establishes empirical IQ distributions.
*)
Theorem sampling_mean_count_monotone_rate: forall n p q, 0<=n -> p<=q -> sampling_mean_count n p<=sampling_mean_count n q.
Proof.
  intros n p q Hn Hpq; unfold sampling_mean_count; nra.
Qed.

(** [sampling_frequency_variance_nonnegative] (theorem).
 Mathematical meaning: The Bernoulli frequency variance is nonnegative for positive sample size and valid event probability.
 Exact proposition: forall n p, 0<n -> 0<=p -> p<=1 -> 0<=sampling_frequency_variance n p.
 Premises and side conditions: All probability-domain, sample-size
 positivity, division and nondegeneracy restrictions needed here are
 written in the signature; independence of physical or pseudorandom
 observations is NOT inferred from the scalar moment expressions.
 Proof/definition method: Reuse earlier established variance identities,
 Rocq Stdlib real ring, nonlinear arithmetic and Field lemmas.
 Library reuse: Canonical Stdlib R, Lra, Psatz, Ring, Field, real inverse
 and ordering laws; no independent binomial mass function is created.
 Boundary: Conditional Bernoulli precision algebra only. This neither
 derives a binomial random-variable law nor exact confidence coverage,
 validates a simulation PRNG, or establishes empirical IQ distributions.
*)
Theorem sampling_frequency_variance_nonnegative: forall n p, 0<n -> 0<=p -> p<=1 -> 0<=sampling_frequency_variance n p.
Proof.
  intros n p Hn Hp H1; unfold sampling_frequency_variance,Rdiv. apply Rmult_le_pos. - apply sampling_variance_nonnegative; assumption. - left; apply Rinv_0_lt_compat; assumption.
Qed.

(** [sampling_frequency_variance_upper_bound] (theorem).
 Mathematical meaning: The exact variance of the ideal event-frequency estimate is at most 1/(4n).
 Exact proposition: forall n p, 0<n -> sampling_frequency_variance n p<=1/(4*n).
 Premises and side conditions: All probability-domain, sample-size
 positivity, division and nondegeneracy restrictions needed here are
 written in the signature; independence of physical or pseudorandom
 observations is NOT inferred from the scalar moment expressions.
 Proof/definition method: Reuse earlier established variance identities,
 Rocq Stdlib real ring, nonlinear arithmetic and Field lemmas.
 Library reuse: Canonical Stdlib R, Lra, Psatz, Ring, Field, real inverse
 and ordering laws; no independent binomial mass function is created.
 Boundary: Conditional Bernoulli precision algebra only. This neither
 derives a binomial random-variable law nor exact confidence coverage,
 validates a simulation PRNG, or establishes empirical IQ distributions.
*)
Theorem sampling_frequency_variance_upper_bound: forall n p, 0<n -> sampling_frequency_variance n p<=1/(4*n).
Proof.
  intros n p Hn. unfold sampling_frequency_variance. pose proof (sampling_variance_maximum p) as Hb. assert (Hi:0</n) by (apply Rinv_0_lt_compat; exact Hn). unfold Rdiv. assert (He: / (4*n) = (/4)*(/n)) by (field; nra). rewrite He. nra.
Qed.

(** [sampling_frequency_variance_monotone_size] (theorem).
 Mathematical meaning: For a fixed event rate, increasing sample size decreases or preserves proportion variance.
 Exact proposition: forall n m p, 0<n -> n<=m -> 0<=p -> p<=1 -> sampling_frequency_variance m p<=sampling_frequency_variance n p.
 Premises and side conditions: All probability-domain, sample-size
 positivity, division and nondegeneracy restrictions needed here are
 written in the signature; independence of physical or pseudorandom
 observations is NOT inferred from the scalar moment expressions.
 Proof/definition method: Reuse earlier established variance identities,
 Rocq Stdlib real ring, nonlinear arithmetic and Field lemmas.
 Library reuse: Canonical Stdlib R, Lra, Psatz, Ring, Field, real inverse
 and ordering laws; no independent binomial mass function is created.
 Boundary: Conditional Bernoulli precision algebra only. This neither
 derives a binomial random-variable law nor exact confidence coverage,
 validates a simulation PRNG, or establishes empirical IQ distributions.
*)
Theorem sampling_frequency_variance_monotone_size: forall n m p, 0<n -> n<=m -> 0<=p -> p<=1 -> sampling_frequency_variance m p<=sampling_frequency_variance n p.
Proof.
  intros n m p Hn Hnm Hp Hu. unfold sampling_frequency_variance. pose proof (sampling_variance_nonnegative p Hp Hu) as Hv. assert (Hm:0<m) by lra. assert (Hi:0<=sampling_bernoulli_variance p) by exact Hv. assert (Hin:/m<=/n) by (apply Rinv_le_contravar; nra). unfold Rdiv. nra.
Qed.

(** [sampling_frequency_variance_strict_size] (theorem).
 Mathematical meaning: At an interior event rate, a strictly larger sample reduces proportion variance strictly.
 Exact proposition: forall n m p, 0<n -> n<m -> 0<p -> p<1 -> sampling_frequency_variance m p<sampling_frequency_variance n p.
 Premises and side conditions: All probability-domain, sample-size
 positivity, division and nondegeneracy restrictions needed here are
 written in the signature; independence of physical or pseudorandom
 observations is NOT inferred from the scalar moment expressions.
 Proof/definition method: Reuse earlier established variance identities,
 Rocq Stdlib real ring, nonlinear arithmetic and Field lemmas.
 Library reuse: Canonical Stdlib R, Lra, Psatz, Ring, Field, real inverse
 and ordering laws; no independent binomial mass function is created.
 Boundary: Conditional Bernoulli precision algebra only. This neither
 derives a binomial random-variable law nor exact confidence coverage,
 validates a simulation PRNG, or establishes empirical IQ distributions.
*)
Theorem sampling_frequency_variance_strict_size: forall n m p, 0<n -> n<m -> 0<p -> p<1 -> sampling_frequency_variance m p<sampling_frequency_variance n p.
Proof.
  intros n m p Hn Hnm Hp Hu. unfold sampling_frequency_variance. pose proof (sampling_variance_strictly_positive p Hp Hu) as Hv. assert (Hm:0<m) by lra. assert (Hin:/m</n) by (apply Rinv_lt_contravar; nra). unfold Rdiv. nra.
Qed.

(** [sampling_frequency_variance_double] (theorem).
 Mathematical meaning: Doubling independent sample size halves the proportion-variance target.
 Exact proposition: forall n p, 0<n -> sampling_frequency_variance (2*n) p = sampling_frequency_variance n p/2.
 Premises and side conditions: All probability-domain, sample-size
 positivity, division and nondegeneracy restrictions needed here are
 written in the signature; independence of physical or pseudorandom
 observations is NOT inferred from the scalar moment expressions.
 Proof/definition method: Reuse earlier established variance identities,
 Rocq Stdlib real ring, nonlinear arithmetic and Field lemmas.
 Library reuse: Canonical Stdlib R, Lra, Psatz, Ring, Field, real inverse
 and ordering laws; no independent binomial mass function is created.
 Boundary: Conditional Bernoulli precision algebra only. This neither
 derives a binomial random-variable law nor exact confidence coverage,
 validates a simulation PRNG, or establishes empirical IQ distributions.
*)
Theorem sampling_frequency_variance_double: forall n p, 0<n -> sampling_frequency_variance (2*n) p = sampling_frequency_variance n p/2.
Proof.
  intros n p Hn; unfold sampling_frequency_variance; field; nra.
Qed.

(** [sampling_frequency_variance_quadruple] (theorem).
 Mathematical meaning: Quadrupling independent sample size quarters the proportion-variance target.
 Exact proposition: forall n p, 0<n -> sampling_frequency_variance (4*n) p = sampling_frequency_variance n p/4.
 Premises and side conditions: All probability-domain, sample-size
 positivity, division and nondegeneracy restrictions needed here are
 written in the signature; independence of physical or pseudorandom
 observations is NOT inferred from the scalar moment expressions.
 Proof/definition method: Reuse earlier established variance identities,
 Rocq Stdlib real ring, nonlinear arithmetic and Field lemmas.
 Library reuse: Canonical Stdlib R, Lra, Psatz, Ring, Field, real inverse
 and ordering laws; no independent binomial mass function is created.
 Boundary: Conditional Bernoulli precision algebra only. This neither
 derives a binomial random-variable law nor exact confidence coverage,
 validates a simulation PRNG, or establishes empirical IQ distributions.
*)
Theorem sampling_frequency_variance_quadruple: forall n p, 0<n -> sampling_frequency_variance (4*n) p = sampling_frequency_variance n p/4.
Proof.
  intros n p Hn; unfold sampling_frequency_variance; field; nra.
Qed.

(** [sampling_frequency_variance_rate_difference] (theorem).
 Mathematical meaning: The frequency variance response to a change in event rate is exactly the Bernoulli variance difference divided by sample size.
 Exact proposition: forall n p q, 0<n -> sampling_frequency_variance n q-sampling_frequency_variance n p = (q-p)*(1-p-q)/n.
 Premises and side conditions: All probability-domain, sample-size
 positivity, division and nondegeneracy restrictions needed here are
 written in the signature; independence of physical or pseudorandom
 observations is NOT inferred from the scalar moment expressions.
 Proof/definition method: Reuse earlier established variance identities,
 Rocq Stdlib real ring, nonlinear arithmetic and Field lemmas.
 Library reuse: Canonical Stdlib R, Lra, Psatz, Ring, Field, real inverse
 and ordering laws; no independent binomial mass function is created.
 Boundary: Conditional Bernoulli precision algebra only. This neither
 derives a binomial random-variable law nor exact confidence coverage,
 validates a simulation PRNG, or establishes empirical IQ distributions.
*)
Theorem sampling_frequency_variance_rate_difference: forall n p q, 0<n -> sampling_frequency_variance n q-sampling_frequency_variance n p = (q-p)*(1-p-q)/n.
Proof.
  intros n p q Hn. unfold sampling_frequency_variance,sampling_bernoulli_variance; field; nra.
Qed.

(** [sampling_relative_variance_positive] (theorem).
 Mathematical meaning: A rare but nonzero event yields strictly positive squared relative sampling error.
 Exact proposition: forall n p, 0<n -> 0<p -> p<1 -> 0<sampling_relative_variance n p.
 Premises and side conditions: All probability-domain, sample-size
 positivity, division and nondegeneracy restrictions needed here are
 written in the signature; independence of physical or pseudorandom
 observations is NOT inferred from the scalar moment expressions.
 Proof/definition method: Reuse earlier established variance identities,
 Rocq Stdlib real ring, nonlinear arithmetic and Field lemmas.
 Library reuse: Canonical Stdlib R, Lra, Psatz, Ring, Field, real inverse
 and ordering laws; no independent binomial mass function is created.
 Boundary: Conditional Bernoulli precision algebra only. This neither
 derives a binomial random-variable law nor exact confidence coverage,
 validates a simulation PRNG, or establishes empirical IQ distributions.
*)
Theorem sampling_relative_variance_positive: forall n p, 0<n -> 0<p -> p<1 -> 0<sampling_relative_variance n p.
Proof.
  intros n p Hn Hp Hu. unfold sampling_relative_variance,Rdiv. apply Rmult_lt_0_compat; [lra|apply Rinv_0_lt_compat; nra].
Qed.

(** [sampling_relative_variance_zero_at_certain_event] (theorem).
 Mathematical meaning: A certain event has no relative Bernoulli sampling uncertainty.
 Exact proposition: forall n, sampling_relative_variance n 1=0.
 Premises and side conditions: All probability-domain, sample-size
 positivity, division and nondegeneracy restrictions needed here are
 written in the signature; independence of physical or pseudorandom
 observations is NOT inferred from the scalar moment expressions.
 Proof/definition method: Reuse earlier established variance identities,
 Rocq Stdlib real ring, nonlinear arithmetic and Field lemmas.
 Library reuse: Canonical Stdlib R, Lra, Psatz, Ring, Field, real inverse
 and ordering laws; no independent binomial mass function is created.
 Boundary: Conditional Bernoulli precision algebra only. This neither
 derives a binomial random-variable law nor exact confidence coverage,
 validates a simulation PRNG, or establishes empirical IQ distributions.
*)
Theorem sampling_relative_variance_zero_at_certain_event: forall n, sampling_relative_variance n 1=0.
Proof.
  intro n; unfold sampling_relative_variance,Rdiv; ring.
Qed.

(** [sampling_relative_variance_double] (theorem).
 Mathematical meaning: Doubling the independent trial count halves squared relative standard error.
 Exact proposition: forall n p, 0<n -> 0<p -> sampling_relative_variance (2*n) p=sampling_relative_variance n p/2.
 Premises and side conditions: All probability-domain, sample-size
 positivity, division and nondegeneracy restrictions needed here are
 written in the signature; independence of physical or pseudorandom
 observations is NOT inferred from the scalar moment expressions.
 Proof/definition method: Reuse earlier established variance identities,
 Rocq Stdlib real ring, nonlinear arithmetic and Field lemmas.
 Library reuse: Canonical Stdlib R, Lra, Psatz, Ring, Field, real inverse
 and ordering laws; no independent binomial mass function is created.
 Boundary: Conditional Bernoulli precision algebra only. This neither
 derives a binomial random-variable law nor exact confidence coverage,
 validates a simulation PRNG, or establishes empirical IQ distributions.
*)
Theorem sampling_relative_variance_double: forall n p, 0<n -> 0<p -> sampling_relative_variance (2*n) p=sampling_relative_variance n p/2.
Proof.
  intros n p Hn Hp; unfold sampling_relative_variance; field; nra.
Qed.

(** [sampling_relative_variance_quadruple] (theorem).
 Mathematical meaning: Quadrupling sample size reduces squared relative error by a factor of four.
 Exact proposition: forall n p, 0<n -> 0<p -> sampling_relative_variance (4*n) p=sampling_relative_variance n p/4.
 Premises and side conditions: All probability-domain, sample-size
 positivity, division and nondegeneracy restrictions needed here are
 written in the signature; independence of physical or pseudorandom
 observations is NOT inferred from the scalar moment expressions.
 Proof/definition method: Reuse earlier established variance identities,
 Rocq Stdlib real ring, nonlinear arithmetic and Field lemmas.
 Library reuse: Canonical Stdlib R, Lra, Psatz, Ring, Field, real inverse
 and ordering laws; no independent binomial mass function is created.
 Boundary: Conditional Bernoulli precision algebra only. This neither
 derives a binomial random-variable law nor exact confidence coverage,
 validates a simulation PRNG, or establishes empirical IQ distributions.
*)
Theorem sampling_relative_variance_quadruple: forall n p, 0<n -> 0<p -> sampling_relative_variance (4*n) p=sampling_relative_variance n p/4.
Proof.
  intros n p Hn Hp; unfold sampling_relative_variance; field; nra.
Qed.

(** [sampling_relative_variance_as_frequency_ratio] (theorem).
 Mathematical meaning: Squared relative standard error equals frequency variance divided by squared true event probability.
 Exact proposition: forall n p, 0<n -> 0<p -> sampling_relative_variance n p = sampling_frequency_variance n p/(p*p).
 Premises and side conditions: All probability-domain, sample-size
 positivity, division and nondegeneracy restrictions needed here are
 written in the signature; independence of physical or pseudorandom
 observations is NOT inferred from the scalar moment expressions.
 Proof/definition method: Reuse earlier established variance identities,
 Rocq Stdlib real ring, nonlinear arithmetic and Field lemmas.
 Library reuse: Canonical Stdlib R, Lra, Psatz, Ring, Field, real inverse
 and ordering laws; no independent binomial mass function is created.
 Boundary: Conditional Bernoulli precision algebra only. This neither
 derives a binomial random-variable law nor exact confidence coverage,
 validates a simulation PRNG, or establishes empirical IQ distributions.
*)
Theorem sampling_relative_variance_as_frequency_ratio: forall n p, 0<n -> 0<p -> sampling_relative_variance n p = sampling_frequency_variance n p/(p*p).
Proof.
  intros n p Hn Hp; unfold sampling_relative_variance,sampling_frequency_variance,sampling_bernoulli_variance; field; nra.
Qed.

(** [sampling_relative_variance_rate_difference] (theorem).
 Mathematical meaning: Squared relative uncertainty falls as the positive event rate rises, at fixed sample size.
 Exact proposition: forall n p q, 0<n -> 0<p -> 0<q -> sampling_relative_variance n p-sampling_relative_variance n q = (q-p)/(n*p*q).
 Premises and side conditions: All probability-domain, sample-size
 positivity, division and nondegeneracy restrictions needed here are
 written in the signature; independence of physical or pseudorandom
 observations is NOT inferred from the scalar moment expressions.
 Proof/definition method: Reuse earlier established variance identities,
 Rocq Stdlib real ring, nonlinear arithmetic and Field lemmas.
 Library reuse: Canonical Stdlib R, Lra, Psatz, Ring, Field, real inverse
 and ordering laws; no independent binomial mass function is created.
 Boundary: Conditional Bernoulli precision algebra only. This neither
 derives a binomial random-variable law nor exact confidence coverage,
 validates a simulation PRNG, or establishes empirical IQ distributions.
*)
Theorem sampling_relative_variance_rate_difference: forall n p q, 0<n -> 0<p -> 0<q -> sampling_relative_variance n p-sampling_relative_variance n q = (q-p)/(n*p*q).
Proof.
  intros n p q Hn Hp Hq; unfold sampling_relative_variance; field; nra.
Qed.

(** [sampling_relative_variance_rate_monotone] (theorem).
 Mathematical meaning: Higher positive event probabilities yield smaller relative precision variance for the same sample size.
 Exact proposition: forall n p q, 0<n -> 0<p -> p<=q -> sampling_relative_variance n q<=sampling_relative_variance n p.
 Premises and side conditions: All probability-domain, sample-size
 positivity, division and nondegeneracy restrictions needed here are
 written in the signature; independence of physical or pseudorandom
 observations is NOT inferred from the scalar moment expressions.
 Proof/definition method: Reuse earlier established variance identities,
 Rocq Stdlib real ring, nonlinear arithmetic and Field lemmas.
 Library reuse: Canonical Stdlib R, Lra, Psatz, Ring, Field, real inverse
 and ordering laws; no independent binomial mass function is created.
 Boundary: Conditional Bernoulli precision algebra only. This neither
 derives a binomial random-variable law nor exact confidence coverage,
 validates a simulation PRNG, or establishes empirical IQ distributions.
*)
Theorem sampling_relative_variance_rate_monotone: forall n p q, 0<n -> 0<p -> p<=q -> sampling_relative_variance n q<=sampling_relative_variance n p.
Proof.
  intros n p q Hn Hp Hpq. assert (Hq:0<q) by lra. pose proof (sampling_relative_variance_rate_difference n p q Hn Hp Hq) as Hid. assert (Hden:0<n*p*q) by nra. assert (Hfrac:0<= (q-p)/(n*p*q)) by (unfold Rdiv; apply Rmult_le_pos; [lra|left; apply Rinv_0_lt_compat; exact Hden]). lra.
Qed.

(** [sampling_relative_variance_rate_strict] (theorem).
 Mathematical meaning: Strictly rarer nonzero events always have worse relative precision at a fixed number of independent trials.
 Exact proposition: forall n p q, 0<n -> 0<p -> p<q -> sampling_relative_variance n q<sampling_relative_variance n p.
 Premises and side conditions: All probability-domain, sample-size
 positivity, division and nondegeneracy restrictions needed here are
 written in the signature; independence of physical or pseudorandom
 observations is NOT inferred from the scalar moment expressions.
 Proof/definition method: Reuse earlier established variance identities,
 Rocq Stdlib real ring, nonlinear arithmetic and Field lemmas.
 Library reuse: Canonical Stdlib R, Lra, Psatz, Ring, Field, real inverse
 and ordering laws; no independent binomial mass function is created.
 Boundary: Conditional Bernoulli precision algebra only. This neither
 derives a binomial random-variable law nor exact confidence coverage,
 validates a simulation PRNG, or establishes empirical IQ distributions.
*)
Theorem sampling_relative_variance_rate_strict: forall n p q, 0<n -> 0<p -> p<q -> sampling_relative_variance n q<sampling_relative_variance n p.
Proof.
  intros n p q Hn Hp Hpq. assert (Hq:0<q) by lra. pose proof (sampling_relative_variance_rate_difference n p q Hn Hp Hq) as Hid. assert (Hden:0<n*p*q) by nra. assert (Hfrac:0< (q-p)/(n*p*q)) by (unfold Rdiv; apply Rmult_lt_0_compat; [lra|apply Rinv_0_lt_compat; exact Hden]). lra.
Qed.

(** [sampling_relative_variance_coarse_bound] (theorem).
 Mathematical meaning: For p at most one, squared relative error is no greater than inverse expected successes.
 Exact proposition: forall n p, 0<n -> 0<p -> p<=1 -> sampling_relative_variance n p<=1/(n*p).
 Premises and side conditions: All probability-domain, sample-size
 positivity, division and nondegeneracy restrictions needed here are
 written in the signature; independence of physical or pseudorandom
 observations is NOT inferred from the scalar moment expressions.
 Proof/definition method: Reuse earlier established variance identities,
 Rocq Stdlib real ring, nonlinear arithmetic and Field lemmas.
 Library reuse: Canonical Stdlib R, Lra, Psatz, Ring, Field, real inverse
 and ordering laws; no independent binomial mass function is created.
 Boundary: Conditional Bernoulli precision algebra only. This neither
 derives a binomial random-variable law nor exact confidence coverage,
 validates a simulation PRNG, or establishes empirical IQ distributions.
*)
Theorem sampling_relative_variance_coarse_bound: forall n p, 0<n -> 0<p -> p<=1 -> sampling_relative_variance n p<=1/(n*p).
Proof.
  intros n p Hn Hp Hu. unfold sampling_relative_variance. assert (Hinv:0</(n*p)) by (apply Rinv_0_lt_compat; nra). unfold Rdiv. nra.
Qed.

(** [sampling_frequency_variance_zero_at_impossible_event] (theorem).
 Mathematical meaning: A zero-probability event contributes no event-frequency variance.
 Exact proposition: forall n, sampling_frequency_variance n 0=0.
 Premises and side conditions: All probability-domain, sample-size
 positivity, division and nondegeneracy restrictions needed here are
 written in the signature; independence of physical or pseudorandom
 observations is NOT inferred from the scalar moment expressions.
 Proof/definition method: Reuse earlier established variance identities,
 Rocq Stdlib real ring, nonlinear arithmetic and Field lemmas.
 Library reuse: Canonical Stdlib R, Lra, Psatz, Ring, Field, real inverse
 and ordering laws; no independent binomial mass function is created.
 Boundary: Conditional Bernoulli precision algebra only. This neither
 derives a binomial random-variable law nor exact confidence coverage,
 validates a simulation PRNG, or establishes empirical IQ distributions.
*)
Theorem sampling_frequency_variance_zero_at_impossible_event: forall n, sampling_frequency_variance n 0=0.
Proof.
  intro n; unfold sampling_frequency_variance,sampling_bernoulli_variance,Rdiv; ring.
Qed.

(** [sampling_frequency_variance_zero_at_certain_event] (theorem).
 Mathematical meaning: A certain event contributes no event-frequency variance.
 Exact proposition: forall n, sampling_frequency_variance n 1=0.
 Premises and side conditions: All probability-domain, sample-size
 positivity, division and nondegeneracy restrictions needed here are
 written in the signature; independence of physical or pseudorandom
 observations is NOT inferred from the scalar moment expressions.
 Proof/definition method: Reuse earlier established variance identities,
 Rocq Stdlib real ring, nonlinear arithmetic and Field lemmas.
 Library reuse: Canonical Stdlib R, Lra, Psatz, Ring, Field, real inverse
 and ordering laws; no independent binomial mass function is created.
 Boundary: Conditional Bernoulli precision algebra only. This neither
 derives a binomial random-variable law nor exact confidence coverage,
 validates a simulation PRNG, or establishes empirical IQ distributions.
*)
Theorem sampling_frequency_variance_zero_at_certain_event: forall n, sampling_frequency_variance n 1=0.
Proof.
  intro n; unfold sampling_frequency_variance,sampling_bernoulli_variance,Rdiv; ring.
Qed.

