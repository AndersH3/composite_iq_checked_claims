(** Module: SequentialSensitivity.v
    Purpose: Check the sequential conditional-means report's exact sensitivity
    of equicorrelation conditioning, prediction, variance and inclusive means
    to battery size, correlation and new observations.
    Mathematical representation: Reuse SequentialReport's real-valued count
    formulas and denominator; each count is a real embedding of an integer
    battery size under explicitly stated nonzero/positivity premises.
    Explicit hypotheses: Division premises, nonnegative or positive counts,
    and correlation intervals are attached to every relevant proposition.
    Library use: Stdlib.Reals, Lra, Psatz, Field, Ring, and the canonical
    specialized SequentialReport theorems. No new sums or matrix operations.
    Limitations: These are exact real algebra and feasible fixed regression
    coefficients, not existence or conditional distribution of Gaussian
    random variables, validity of psychometric assumptions, or erfc accuracy.
    Reproduction: scripts/compile_rocq.sh with Rocq Prover 9.2; kernel checks
    follow the tracked dependencies after SequentialReport.v.
  *)
From Stdlib Require Import Reals Lra Psatz Field.
Require Import SequentialReport.
Open Scope R_scope.

(**
 [sensitivity_beta] (definition) — Effective weight assigned to a common
 observed standardized score in the equicorrelated linear regression formula.
 Mathematical meaning: This is the scalar regression loading r*c/d_r.
 Exact declaration: sensitivity_beta r c = r*c/sequential_d r c.
 Premises and side conditions: The resulting coefficient has a statistical
 interpretation only for a nonempty admissible covariance block; divisions
 are not claimed invertible in this transparent total real definition.
 Proof/definition method: A one-line specialization of the report's existing
 denominator; no new conditional expectation or stochastic model.
 Library reuse: SequentialReport.sequential_d, Stdlib.Reals.
 Boundary: No Gaussian conditional expectation or IQ population claim.
 *)
Definition sensitivity_beta (r c : R) : R := r*c / sequential_d r c.

(**
 [sensitivity_denominator_decomposition] (theorem) — The conditioning denominator splits into idiosyncratic and common-factor contributions.
 Mathematical meaning: The conditioning denominator splits into idiosyncratic and common-factor contributions.
 Exact checked proposition: forall n c, sequential_d n c = (1-c) + n*c.
 Premises and side conditions: Exactly the positivity, correlation range and
 nonzero denominator assumptions written in the declaration; no hidden
 Gaussian, empirical IQ, or measure-theoretic hypotheses are supplied.
 Proof/definition method: Use maintained real ring and nonlinear arithmetic decision tactics; no ad hoc recursion.
 Library reuse: Stdlib.Reals, Lra, Psatz, Field and
 SequentialReport.sequential_d / existing checked regression identities.
 Boundary: Kernel verification checks deterministic real algebra only; it
 does not construct a Gaussian distribution or certified normal tail.
 *)
Theorem sensitivity_denominator_decomposition :
  forall n c, sequential_d n c = (1-c) + n*c.
Proof.
  intros n c; unfold sequential_d; ring.
Qed.

(**
 [sensitivity_denominator_count_gap] (theorem) — The change in the denominator under a changed battery size is exactly the added count times correlation.
 Mathematical meaning: The change in the denominator under a changed battery size is exactly the added count times correlation.
 Exact checked proposition: forall n m c, sequential_d n c - sequential_d m c = (n-m)*c.
 Premises and side conditions: Exactly the positivity, correlation range and
 nonzero denominator assumptions written in the declaration; no hidden
 Gaussian, empirical IQ, or measure-theoretic hypotheses are supplied.
 Proof/definition method: Use maintained real ring and nonlinear arithmetic decision tactics; no ad hoc recursion.
 Library reuse: Stdlib.Reals, Lra, Psatz, Field and
 SequentialReport.sequential_d / existing checked regression identities.
 Boundary: Kernel verification checks deterministic real algebra only; it
 does not construct a Gaussian distribution or certified normal tail.
 *)
Theorem sensitivity_denominator_count_gap :
  forall n m c, sequential_d n c - sequential_d m c = (n-m)*c.
Proof.
  intros n m c; unfold sequential_d; ring.
Qed.

(**
 [sensitivity_denominator_correlation_gap] (theorem) — Changing the common correlation changes the conditioning denominator by the number of off-diagonal observations.
 Mathematical meaning: Changing the common correlation changes the conditioning denominator by the number of off-diagonal observations.
 Exact checked proposition: forall n c1 c2, sequential_d n c2 - sequential_d n c1 = (n-1)*(c2-c1).
 Premises and side conditions: Exactly the positivity, correlation range and
 nonzero denominator assumptions written in the declaration; no hidden
 Gaussian, empirical IQ, or measure-theoretic hypotheses are supplied.
 Proof/definition method: Use maintained real ring and nonlinear arithmetic decision tactics; no ad hoc recursion.
 Library reuse: Stdlib.Reals, Lra, Psatz, Field and
 SequentialReport.sequential_d / existing checked regression identities.
 Boundary: Kernel verification checks deterministic real algebra only; it
 does not construct a Gaussian distribution or certified normal tail.
 *)
Theorem sensitivity_denominator_correlation_gap :
  forall n c1 c2, sequential_d n c2 - sequential_d n c1 = (n-1)*(c2-c1).
Proof.
  intros n c1 c2; unfold sequential_d; ring.
Qed.

(**
 [sensitivity_denominator_lower_bound] (theorem) — For nonnegative correlation the conditioning denominator is at least one.
 Mathematical meaning: For nonnegative correlation the conditioning denominator is at least one.
 Exact checked proposition: forall n c, 1 <= n -> 0 <= c -> 1 <= sequential_d n c.
 Premises and side conditions: Exactly the positivity, correlation range and
 nonzero denominator assumptions written in the declaration; no hidden
 Gaussian, empirical IQ, or measure-theoretic hypotheses are supplied.
 Proof/definition method: Use maintained real ring and nonlinear arithmetic decision tactics; no ad hoc recursion.
 Library reuse: Stdlib.Reals, Lra, Psatz, Field and
 SequentialReport.sequential_d / existing checked regression identities.
 Boundary: Kernel verification checks deterministic real algebra only; it
 does not construct a Gaussian distribution or certified normal tail.
 *)
Theorem sensitivity_denominator_lower_bound :
  forall n c, 1 <= n -> 0 <= c -> 1 <= sequential_d n c.
Proof.
  intros n c Hn Hc; unfold sequential_d; nra.
Qed.

(**
 [sensitivity_denominator_upper_bound] (theorem) — At most unit correlation bounds the conditioning denominator by the battery size.
 Mathematical meaning: At most unit correlation bounds the conditioning denominator by the battery size.
 Exact checked proposition: forall n c, 1 <= n -> c <= 1 -> sequential_d n c <= n.
 Premises and side conditions: Exactly the positivity, correlation range and
 nonzero denominator assumptions written in the declaration; no hidden
 Gaussian, empirical IQ, or measure-theoretic hypotheses are supplied.
 Proof/definition method: Use maintained real ring and nonlinear arithmetic decision tactics; no ad hoc recursion.
 Library reuse: Stdlib.Reals, Lra, Psatz, Field and
 SequentialReport.sequential_d / existing checked regression identities.
 Boundary: Kernel verification checks deterministic real algebra only; it
 does not construct a Gaussian distribution or certified normal tail.
 *)
Theorem sensitivity_denominator_upper_bound :
  forall n c, 1 <= n -> c <= 1 -> sequential_d n c <= n.
Proof.
  intros n c Hn Hc; unfold sequential_d; nra.
Qed.

(**
 [sensitivity_denominator_strict_lower] (theorem) — With at least two observations and positive common correlation the denominator strictly exceeds one.
 Mathematical meaning: With at least two observations and positive common correlation the denominator strictly exceeds one.
 Exact checked proposition: forall n c, 1 < n -> 0 < c -> 1 < sequential_d n c.
 Premises and side conditions: Exactly the positivity, correlation range and
 nonzero denominator assumptions written in the declaration; no hidden
 Gaussian, empirical IQ, or measure-theoretic hypotheses are supplied.
 Proof/definition method: Use maintained real ring and nonlinear arithmetic decision tactics; no ad hoc recursion.
 Library reuse: Stdlib.Reals, Lra, Psatz, Field and
 SequentialReport.sequential_d / existing checked regression identities.
 Boundary: Kernel verification checks deterministic real algebra only; it
 does not construct a Gaussian distribution or certified normal tail.
 *)
Theorem sensitivity_denominator_strict_lower :
  forall n c, 1 < n -> 0 < c -> 1 < sequential_d n c.
Proof.
  intros n c Hn Hc; unfold sequential_d; nra.
Qed.

(**
 [sensitivity_denominator_strict_upper] (theorem) — An imperfectly correlated battery of size above one has a denominator strictly smaller than its size.
 Mathematical meaning: An imperfectly correlated battery of size above one has a denominator strictly smaller than its size.
 Exact checked proposition: forall n c, 1 < n -> c < 1 -> sequential_d n c < n.
 Premises and side conditions: Exactly the positivity, correlation range and
 nonzero denominator assumptions written in the declaration; no hidden
 Gaussian, empirical IQ, or measure-theoretic hypotheses are supplied.
 Proof/definition method: Use maintained real ring and nonlinear arithmetic decision tactics; no ad hoc recursion.
 Library reuse: Stdlib.Reals, Lra, Psatz, Field and
 SequentialReport.sequential_d / existing checked regression identities.
 Boundary: Kernel verification checks deterministic real algebra only; it
 does not construct a Gaussian distribution or certified normal tail.
 *)
Theorem sensitivity_denominator_strict_upper :
  forall n c, 1 < n -> c < 1 -> sequential_d n c < n.
Proof.
  intros n c Hn Hc; unfold sequential_d; nra.
Qed.

(**
 [sensitivity_denominator_count_order] (theorem) — Additional nonnegative-count observations weakly increase the denominator at nonnegative correlation.
 Mathematical meaning: Additional nonnegative-count observations weakly increase the denominator at nonnegative correlation.
 Exact checked proposition: forall n k c, 0 <= k -> 0 <= c -> sequential_d n c <= sequential_d (n+k) c.
 Premises and side conditions: Exactly the positivity, correlation range and
 nonzero denominator assumptions written in the declaration; no hidden
 Gaussian, empirical IQ, or measure-theoretic hypotheses are supplied.
 Proof/definition method: Use maintained real ring and nonlinear arithmetic decision tactics; no ad hoc recursion.
 Library reuse: Stdlib.Reals, Lra, Psatz, Field and
 SequentialReport.sequential_d / existing checked regression identities.
 Boundary: Kernel verification checks deterministic real algebra only; it
 does not construct a Gaussian distribution or certified normal tail.
 *)
Theorem sensitivity_denominator_count_order :
  forall n k c, 0 <= k -> 0 <= c -> sequential_d n c <= sequential_d (n+k) c.
Proof.
  intros n k c Hk Hc; unfold sequential_d; nra.
Qed.

(**
 [sensitivity_denominator_correlation_order] (theorem) — For a battery of at least one observation the denominator is monotone in correlation.
 Mathematical meaning: For a battery of at least one observation the denominator is monotone in correlation.
 Exact checked proposition: forall n c1 c2, 1 <= n -> c1 <= c2 -> sequential_d n c1 <= sequential_d n c2.
 Premises and side conditions: Exactly the positivity, correlation range and
 nonzero denominator assumptions written in the declaration; no hidden
 Gaussian, empirical IQ, or measure-theoretic hypotheses are supplied.
 Proof/definition method: Use maintained real ring and nonlinear arithmetic decision tactics; no ad hoc recursion.
 Library reuse: Stdlib.Reals, Lra, Psatz, Field and
 SequentialReport.sequential_d / existing checked regression identities.
 Boundary: Kernel verification checks deterministic real algebra only; it
 does not construct a Gaussian distribution or certified normal tail.
 *)
Theorem sensitivity_denominator_correlation_order :
  forall n c1 c2, 1 <= n -> c1 <= c2 -> sequential_d n c1 <= sequential_d n c2.
Proof.
  intros n c1 c2 Hn Hc; unfold sequential_d; nra.
Qed.

(**
 [sensitivity_denominator_affine_interpolation] (theorem) — The denominator is affine under correlation mixtures, allowing algebraic interpolation of admissible models.
 Mathematical meaning: The denominator is affine under correlation mixtures, allowing algebraic interpolation of admissible models.
 Exact checked proposition: forall n c1 c2 t, sequential_d n ((1-t)*c1+t*c2) = (1-t)*sequential_d n c1+t*sequential_d n c2.
 Premises and side conditions: Exactly the positivity, correlation range and
 nonzero denominator assumptions written in the declaration; no hidden
 Gaussian, empirical IQ, or measure-theoretic hypotheses are supplied.
 Proof/definition method: Use maintained real ring and nonlinear arithmetic decision tactics; no ad hoc recursion.
 Library reuse: Stdlib.Reals, Lra, Psatz, Field and
 SequentialReport.sequential_d / existing checked regression identities.
 Boundary: Kernel verification checks deterministic real algebra only; it
 does not construct a Gaussian distribution or certified normal tail.
 *)
Theorem sensitivity_denominator_affine_interpolation :
  forall n c1 c2 t, sequential_d n ((1-t)*c1+t*c2) = (1-t)*sequential_d n c1+t*sequential_d n c2.
Proof.
  intros n c1 c2 t; unfold sequential_d; ring.
Qed.

(**
 [sensitivity_beta_prediction_factorization] (theorem) — The report's prediction is exactly the regression weight times the observed standardized score.
 Mathematical meaning: The report's prediction is exactly the regression weight times the observed standardized score.
 Exact checked proposition: forall r c a, sequential_prediction r c a = sensitivity_beta r c * a.
 Premises and side conditions: Exactly the positivity, correlation range and
 nonzero denominator assumptions written in the declaration; no hidden
 Gaussian, empirical IQ, or measure-theoretic hypotheses are supplied.
 Proof/definition method: Apply standard real-division positivity and the prior exact gap identities.
 Library reuse: Stdlib.Reals, Lra, Psatz, Field and
 SequentialReport.sequential_d / existing checked regression identities.
 Boundary: Kernel verification checks deterministic real algebra only; it
 does not construct a Gaussian distribution or certified normal tail.
 *)
Theorem sensitivity_beta_prediction_factorization :
  forall r c a, sequential_prediction r c a = sensitivity_beta r c * a.
Proof.
  intros r c a; unfold sequential_prediction, sensitivity_beta, Rdiv; ring.
Qed.

(**
 [sensitivity_beta_complement] (theorem) — The unpredicted fraction of a standardized observation is one minus correlation divided by the conditioning denominator.
 Mathematical meaning: The unpredicted fraction of a standardized observation is one minus correlation divided by the conditioning denominator.
 Exact checked proposition: forall r c, sequential_d r c <> 0 -> 1-sensitivity_beta r c = (1-c)/sequential_d r c.
 Premises and side conditions: Exactly the positivity, correlation range and
 nonzero denominator assumptions written in the declaration; no hidden
 Gaussian, empirical IQ, or measure-theoretic hypotheses are supplied.
 Proof/definition method: Normalize exact rational formulas with Stdlib.Field and algebraic side-condition checking.
 Library reuse: Stdlib.Reals, Lra, Psatz, Field and
 SequentialReport.sequential_d / existing checked regression identities.
 Boundary: Kernel verification checks deterministic real algebra only; it
 does not construct a Gaussian distribution or certified normal tail.
 *)
Theorem sensitivity_beta_complement :
  forall r c, sequential_d r c <> 0 -> 1-sensitivity_beta r c = (1-c)/sequential_d r c.
Proof.
  intros r c Hd; unfold sensitivity_beta, sequential_d in *; field; nra.
Qed.

(**
 [sensitivity_beta_independent] (theorem) — Zero cross-test correlation makes the fixed linear regression weight zero.
 Mathematical meaning: Zero cross-test correlation makes the fixed linear regression weight zero.
 Exact checked proposition: forall r, sensitivity_beta r 0 = 0.
 Premises and side conditions: Exactly the positivity, correlation range and
 nonzero denominator assumptions written in the declaration; no hidden
 Gaussian, empirical IQ, or measure-theoretic hypotheses are supplied.
 Proof/definition method: Normalize exact rational formulas with Stdlib.Field and algebraic side-condition checking.
 Library reuse: Stdlib.Reals, Lra, Psatz, Field and
 SequentialReport.sequential_d / existing checked regression identities.
 Boundary: Kernel verification checks deterministic real algebra only; it
 does not construct a Gaussian distribution or certified normal tail.
 *)
Theorem sensitivity_beta_independent :
  forall r, sensitivity_beta r 0 = 0.
Proof.
  intros r; unfold sensitivity_beta, sequential_d; field.
Qed.

(**
 [sensitivity_beta_perfect] (theorem) — At perfect correlation a nonempty initial battery predicts with unit weight.
 Mathematical meaning: At perfect correlation a nonempty initial battery predicts with unit weight.
 Exact checked proposition: forall r, r <> 0 -> sensitivity_beta r 1 = 1.
 Premises and side conditions: Exactly the positivity, correlation range and
 nonzero denominator assumptions written in the declaration; no hidden
 Gaussian, empirical IQ, or measure-theoretic hypotheses are supplied.
 Proof/definition method: Normalize exact rational formulas with Stdlib.Field and algebraic side-condition checking.
 Library reuse: Stdlib.Reals, Lra, Psatz, Field and
 SequentialReport.sequential_d / existing checked regression identities.
 Boundary: Kernel verification checks deterministic real algebra only; it
 does not construct a Gaussian distribution or certified normal tail.
 *)
Theorem sensitivity_beta_perfect :
  forall r, r <> 0 -> sensitivity_beta r 1 = 1.
Proof.
  intros r Hr; unfold sensitivity_beta, sequential_d; field; nra.
Qed.

(**
 [sensitivity_beta_single] (theorem) — With a single initial score the exact linear prediction weight equals correlation.
 Mathematical meaning: With a single initial score the exact linear prediction weight equals correlation.
 Exact checked proposition: forall c, sensitivity_beta 1 c = c.
 Premises and side conditions: Exactly the positivity, correlation range and
 nonzero denominator assumptions written in the declaration; no hidden
 Gaussian, empirical IQ, or measure-theoretic hypotheses are supplied.
 Proof/definition method: Normalize exact rational formulas with Stdlib.Field and algebraic side-condition checking.
 Library reuse: Stdlib.Reals, Lra, Psatz, Field and
 SequentialReport.sequential_d / existing checked regression identities.
 Boundary: Kernel verification checks deterministic real algebra only; it
 does not construct a Gaussian distribution or certified normal tail.
 *)
Theorem sensitivity_beta_single :
  forall c, sensitivity_beta 1 c = c.
Proof.
  intros c; unfold sensitivity_beta, sequential_d; field.
Qed.

(**
 [sensitivity_beta_nonnegative] (theorem) — A nonnegative correlation and nonempty battery give a nonnegative linear prediction coefficient.
 Mathematical meaning: A nonnegative correlation and nonempty battery give a nonnegative linear prediction coefficient.
 Exact checked proposition: forall r c, 1 <= r -> 0 <= c -> 0 <= sensitivity_beta r c.
 Premises and side conditions: Exactly the positivity, correlation range and
 nonzero denominator assumptions written in the declaration; no hidden
 Gaussian, empirical IQ, or measure-theoretic hypotheses are supplied.
 Proof/definition method: Apply standard real-division positivity and the prior exact gap identities.
 Library reuse: Stdlib.Reals, Lra, Psatz, Field and
 SequentialReport.sequential_d / existing checked regression identities.
 Boundary: Kernel verification checks deterministic real algebra only; it
 does not construct a Gaussian distribution or certified normal tail.
 *)
Theorem sensitivity_beta_nonnegative :
  forall r c, 1 <= r -> 0 <= c -> 0 <= sensitivity_beta r c.
Proof.
  intros r c Hr Hc.
  assert (Hd : 0 < sequential_d r c)
    by (apply sequential_denominator_positive_nonnegative_correlation; lra).
  unfold sensitivity_beta, Rdiv.
  apply Rmult_le_pos; [nra|].
  apply Rlt_le, Rinv_0_lt_compat; exact Hd.
Qed.

(**
 [sensitivity_beta_at_most_one] (theorem) — For admissible nonnegative correlation, the regression weight cannot exceed one.
 Mathematical meaning: For admissible nonnegative correlation, the regression weight cannot exceed one.
 Exact checked proposition: forall r c, 1 <= r -> 0 <= c -> c <= 1 -> sensitivity_beta r c <= 1.
 Premises and side conditions: Exactly the positivity, correlation range and
 nonzero denominator assumptions written in the declaration; no hidden
 Gaussian, empirical IQ, or measure-theoretic hypotheses are supplied.
 Proof/definition method: Apply standard real-division positivity and the prior exact gap identities.
 Library reuse: Stdlib.Reals, Lra, Psatz, Field and
 SequentialReport.sequential_d / existing checked regression identities.
 Boundary: Kernel verification checks deterministic real algebra only; it
 does not construct a Gaussian distribution or certified normal tail.
 *)
Theorem sensitivity_beta_at_most_one :
  forall r c, 1 <= r -> 0 <= c -> c <= 1 -> sensitivity_beta r c <= 1.
Proof.
  intros r c Hr Hc Hcu.
  assert (Hd : 0 < sequential_d r c)
    by (apply sequential_denominator_positive_nonnegative_correlation; lra).
  pose proof (sensitivity_beta_complement r c (Rgt_not_eq _ _ Hd)) as Hgap.
  assert (Hnonneg : 0 <= (1-c)/sequential_d r c).
  { apply Rdiv_le_0_compat; nra. }
  lra.
Qed.

(**
 [sensitivity_beta_strict_positive] (theorem) — Positive correlation produces a strictly positive predictor coefficient for a nonempty observation history.
 Mathematical meaning: Positive correlation produces a strictly positive predictor coefficient for a nonempty observation history.
 Exact checked proposition: forall r c, 1 <= r -> 0 < c -> 0 < sensitivity_beta r c.
 Premises and side conditions: Exactly the positivity, correlation range and
 nonzero denominator assumptions written in the declaration; no hidden
 Gaussian, empirical IQ, or measure-theoretic hypotheses are supplied.
 Proof/definition method: Apply standard real-division positivity and the prior exact gap identities.
 Library reuse: Stdlib.Reals, Lra, Psatz, Field and
 SequentialReport.sequential_d / existing checked regression identities.
 Boundary: Kernel verification checks deterministic real algebra only; it
 does not construct a Gaussian distribution or certified normal tail.
 *)
Theorem sensitivity_beta_strict_positive :
  forall r c, 1 <= r -> 0 < c -> 0 < sensitivity_beta r c.
Proof.
  intros r c Hr Hc.
  unfold sensitivity_beta.
  apply Rdiv_lt_0_compat.
  - nra.
  - apply sequential_denominator_positive_nonnegative_correlation; lra.
Qed.

(**
 [sensitivity_beta_strict_below_one] (theorem) — Imperfect positive correlation makes the regression coefficient strictly less than one.
 Mathematical meaning: Imperfect positive correlation makes the regression coefficient strictly less than one.
 Exact checked proposition: forall r c, 1 <= r -> 0 <= c -> c < 1 -> sensitivity_beta r c < 1.
 Premises and side conditions: Exactly the positivity, correlation range and
 nonzero denominator assumptions written in the declaration; no hidden
 Gaussian, empirical IQ, or measure-theoretic hypotheses are supplied.
 Proof/definition method: Apply standard real-division positivity and the prior exact gap identities.
 Library reuse: Stdlib.Reals, Lra, Psatz, Field and
 SequentialReport.sequential_d / existing checked regression identities.
 Boundary: Kernel verification checks deterministic real algebra only; it
 does not construct a Gaussian distribution or certified normal tail.
 *)
Theorem sensitivity_beta_strict_below_one :
  forall r c, 1 <= r -> 0 <= c -> c < 1 -> sensitivity_beta r c < 1.
Proof.
  intros r c Hr Hc Hcu.
  assert (Hd : 0 < sequential_d r c)
    by (apply sequential_denominator_positive_nonnegative_correlation; lra).
  pose proof (sensitivity_beta_complement r c (Rgt_not_eq _ _ Hd)) as Hgap.
  assert (Hpos : 0 < (1-c)/sequential_d r c).
  { apply Rdiv_lt_0_compat; nra. }
  lra.
Qed.

(**
 [sensitivity_beta_excess_over_c] (theorem) — Pooling observations increases the prediction weight above raw correlation by a sharp nonnegative adjustment.
 Mathematical meaning: Pooling observations increases the prediction weight above raw correlation by a sharp nonnegative adjustment.
 Exact checked proposition: forall r c, sequential_d r c <> 0 -> sensitivity_beta r c - c = c*(r-1)*(1-c)/sequential_d r c.
 Premises and side conditions: Exactly the positivity, correlation range and
 nonzero denominator assumptions written in the declaration; no hidden
 Gaussian, empirical IQ, or measure-theoretic hypotheses are supplied.
 Proof/definition method: Normalize exact rational formulas with Stdlib.Field and algebraic side-condition checking.
 Library reuse: Stdlib.Reals, Lra, Psatz, Field and
 SequentialReport.sequential_d / existing checked regression identities.
 Boundary: Kernel verification checks deterministic real algebra only; it
 does not construct a Gaussian distribution or certified normal tail.
 *)
Theorem sensitivity_beta_excess_over_c :
  forall r c, sequential_d r c <> 0 -> sensitivity_beta r c - c = c*(r-1)*(1-c)/sequential_d r c.
Proof.
  intros r c Hd; unfold sensitivity_beta, sequential_d in *; field; nra.
Qed.

(**
 [sensitivity_beta_count_gap] (theorem) — The exact information-weight gain from adding observations factors into count increment, correlation and imperfection.
 Mathematical meaning: The exact information-weight gain from adding observations factors into count increment, correlation and imperfection.
 Exact checked proposition: forall r k c, sequential_d r c <> 0 -> sequential_d (r+k) c <> 0 -> sensitivity_beta (r+k) c - sensitivity_beta r c = k*c*(1-c)/(sequential_d r c*sequential_d (r+k) c).
 Premises and side conditions: Exactly the positivity, correlation range and
 nonzero denominator assumptions written in the declaration; no hidden
 Gaussian, empirical IQ, or measure-theoretic hypotheses are supplied.
 Proof/definition method: Normalize exact rational formulas with Stdlib.Field and algebraic side-condition checking.
 Library reuse: Stdlib.Reals, Lra, Psatz, Field and
 SequentialReport.sequential_d / existing checked regression identities.
 Boundary: Kernel verification checks deterministic real algebra only; it
 does not construct a Gaussian distribution or certified normal tail.
 *)
Theorem sensitivity_beta_count_gap :
  forall r k c, sequential_d r c <> 0 -> sequential_d (r+k) c <> 0 -> sensitivity_beta (r+k) c - sensitivity_beta r c = k*c*(1-c)/(sequential_d r c*sequential_d (r+k) c).
Proof.
  intros r k c Hr Hrk; unfold sensitivity_beta, sequential_d in *; field; nra.
Qed.

(**
 [sensitivity_beta_correlation_gap] (theorem) — The regression-weight response to a correlation increase has an exact rational gap with two denominators.
 Mathematical meaning: The regression-weight response to a correlation increase has an exact rational gap with two denominators.
 Exact checked proposition: forall r c1 c2, sequential_d r c1 <> 0 -> sequential_d r c2 <> 0 -> sensitivity_beta r c2 - sensitivity_beta r c1 = r*(c2-c1)/(sequential_d r c1*sequential_d r c2).
 Premises and side conditions: Exactly the positivity, correlation range and
 nonzero denominator assumptions written in the declaration; no hidden
 Gaussian, empirical IQ, or measure-theoretic hypotheses are supplied.
 Proof/definition method: Normalize exact rational formulas with Stdlib.Field and algebraic side-condition checking.
 Library reuse: Stdlib.Reals, Lra, Psatz, Field and
 SequentialReport.sequential_d / existing checked regression identities.
 Boundary: Kernel verification checks deterministic real algebra only; it
 does not construct a Gaussian distribution or certified normal tail.
 *)
Theorem sensitivity_beta_correlation_gap :
  forall r c1 c2, sequential_d r c1 <> 0 -> sequential_d r c2 <> 0 -> sensitivity_beta r c2 - sensitivity_beta r c1 = r*(c2-c1)/(sequential_d r c1*sequential_d r c2).
Proof.
  intros r c1 c2 H1 H2; unfold sensitivity_beta, sequential_d in *; field; nra.
Qed.

(**
 [sensitivity_beta_count_monotone] (theorem) — For nonnegative imperfect correlation, extending the observed history never decreases its fixed linear regression weight.
 Mathematical meaning: For nonnegative imperfect correlation, extending the observed history never decreases its fixed linear regression weight.
 Exact checked proposition: forall r k c, 1 <= r -> 0 <= k -> 0 <= c -> c <= 1 -> sensitivity_beta r c <= sensitivity_beta (r+k) c.
 Premises and side conditions: Exactly the positivity, correlation range and
 nonzero denominator assumptions written in the declaration; no hidden
 Gaussian, empirical IQ, or measure-theoretic hypotheses are supplied.
 Proof/definition method: Apply standard real-division positivity and the prior exact gap identities.
 Library reuse: Stdlib.Reals, Lra, Psatz, Field and
 SequentialReport.sequential_d / existing checked regression identities.
 Boundary: Kernel verification checks deterministic real algebra only; it
 does not construct a Gaussian distribution or certified normal tail.
 *)
Theorem sensitivity_beta_count_monotone :
  forall r k c, 1 <= r -> 0 <= k -> 0 <= c -> c <= 1 -> sensitivity_beta r c <= sensitivity_beta (r+k) c.
Proof.
  intros r k c Hr Hk Hc Hcu.
  assert (H1 : 0 < sequential_d r c)
    by (apply sequential_denominator_positive_nonnegative_correlation; lra).
  assert (H2 : 0 < sequential_d (r+k) c)
    by (apply sequential_denominator_positive_nonnegative_correlation; lra).
  pose proof (sensitivity_beta_count_gap r k c
    (Rgt_not_eq _ _ H1) (Rgt_not_eq _ _ H2)) as Hgap.
  assert (Hge : 0 <= k*c*(1-c)/(sequential_d r c*sequential_d (r+k) c)).
  { apply Rdiv_le_0_compat; nra. }
  lra.
Qed.

(**
 [sensitivity_beta_correlation_monotone] (theorem) — Increasing correlation on the admissible range cannot reduce a nonempty history's prediction coefficient.
 Mathematical meaning: Increasing correlation on the admissible range cannot reduce a nonempty history's prediction coefficient.
 Exact checked proposition: forall r c1 c2, 1 <= r -> 0 <= c1 -> c1 <= c2 -> sensitivity_beta r c1 <= sensitivity_beta r c2.
 Premises and side conditions: Exactly the positivity, correlation range and
 nonzero denominator assumptions written in the declaration; no hidden
 Gaussian, empirical IQ, or measure-theoretic hypotheses are supplied.
 Proof/definition method: Apply standard real-division positivity and the prior exact gap identities.
 Library reuse: Stdlib.Reals, Lra, Psatz, Field and
 SequentialReport.sequential_d / existing checked regression identities.
 Boundary: Kernel verification checks deterministic real algebra only; it
 does not construct a Gaussian distribution or certified normal tail.
 *)
Theorem sensitivity_beta_correlation_monotone :
  forall r c1 c2, 1 <= r -> 0 <= c1 -> c1 <= c2 -> sensitivity_beta r c1 <= sensitivity_beta r c2.
Proof.
  intros r c1 c2 Hr Hc1 Horder.
  assert (H1 : 0 < sequential_d r c1)
    by (apply sequential_denominator_positive_nonnegative_correlation; lra).
  assert (H2 : 0 < sequential_d r c2)
    by (apply sequential_denominator_positive_nonnegative_correlation; lra).
  pose proof (sensitivity_beta_correlation_gap r c1 c2
    (Rgt_not_eq _ _ H1) (Rgt_not_eq _ _ H2)) as Hgap.
  assert (Hge : 0 <= r*(c2-c1)/(sequential_d r c1*sequential_d r c2)).
  { apply Rdiv_le_0_compat; nra. }
  lra.
Qed.

