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
  { unfold Rdiv; apply Rmult_le_pos; [nra | apply Rlt_le, Rinv_0_lt_compat; nra]. }
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
  { unfold Rdiv; apply Rmult_le_pos; [nra | apply Rlt_le, Rinv_0_lt_compat; nra]. }
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
  { unfold Rdiv; apply Rmult_le_pos; [nra | apply Rlt_le, Rinv_0_lt_compat; nra]. }
  lra.
Qed.

(**
 [sensitivity_population_common_idiosyncratic] (theorem) — The population mean-score variance splits into common correlation and the independent residual averaged across n tests.
 Mathematical meaning: The population mean-score variance splits into common correlation and the independent residual averaged across n tests.
 Exact checked proposition: forall n c, n <> 0 -> sequential_population_variance n c = c + (1-c)/n.
 Premises and side conditions: Assumptions on positive sample sizes, admissible
 correlation or nonzero denominator appear explicitly in this declaration;
 no Gaussian regression, distributional independence or measured IQ inputs are assumed.
 Proof/definition method: Apply Stdlib.Field to exact rational formulas and discharge invertibility by the premises.
 Library reuse: Stdlib.Reals, Lra, Psatz, Field and the already checked
 SequentialReport regression denominator, means, and variance formulas.
 Boundary: The theorem is only exact real algebra for model-specified
 covariance expressions, not a stochastic conditional distribution proof.
 *)
Theorem sensitivity_population_common_idiosyncratic :
  forall n c, n <> 0 -> sequential_population_variance n c = c + (1-c)/n.
Proof.
  intros n c Hn; unfold sequential_population_variance, sequential_d; field; nra.
Qed.

(**
 [sensitivity_population_independent] (theorem) — The equal-weight average of uncorrelated unit-variance scores has variance exactly reciprocal battery size.
 Mathematical meaning: The equal-weight average of uncorrelated unit-variance scores has variance exactly reciprocal battery size.
 Exact checked proposition: forall n, sequential_population_variance n 0 = 1/n.
 Premises and side conditions: Assumptions on positive sample sizes, admissible
 correlation or nonzero denominator appear explicitly in this declaration;
 no Gaussian regression, distributional independence or measured IQ inputs are assumed.
 Proof/definition method: Reuse the maintained ring and nonlinear real arithmetic tactics on the report formulas.
 Library reuse: Stdlib.Reals, Lra, Psatz, Field and the already checked
 SequentialReport regression denominator, means, and variance formulas.
 Boundary: The theorem is only exact real algebra for model-specified
 covariance expressions, not a stochastic conditional distribution proof.
 *)
Theorem sensitivity_population_independent :
  forall n, sequential_population_variance n 0 = 1/n.
Proof.
  intros n; unfold sequential_population_variance, sequential_d; ring.
Qed.

(**
 [sensitivity_population_perfect] (theorem) — Perfectly correlated scores retain unit variance no matter how many are averaged, for nonzero count.
 Mathematical meaning: Perfectly correlated scores retain unit variance no matter how many are averaged, for nonzero count.
 Exact checked proposition: forall n, n <> 0 -> sequential_population_variance n 1 = 1.
 Premises and side conditions: Assumptions on positive sample sizes, admissible
 correlation or nonzero denominator appear explicitly in this declaration;
 no Gaussian regression, distributional independence or measured IQ inputs are assumed.
 Proof/definition method: Apply Stdlib.Field to exact rational formulas and discharge invertibility by the premises.
 Library reuse: Stdlib.Reals, Lra, Psatz, Field and the already checked
 SequentialReport regression denominator, means, and variance formulas.
 Boundary: The theorem is only exact real algebra for model-specified
 covariance expressions, not a stochastic conditional distribution proof.
 *)
Theorem sensitivity_population_perfect :
  forall n, n <> 0 -> sequential_population_variance n 1 = 1.
Proof.
  intros n Hn; unfold sequential_population_variance, sequential_d; field; nra.
Qed.

(**
 [sensitivity_population_at_least_correlation] (theorem) — With positive count and correlation at most one, population-average variance exceeds its common-factor floor.
 Mathematical meaning: With positive count and correlation at most one, population-average variance exceeds its common-factor floor.
 Exact checked proposition: forall n c, 0 < n -> c <= 1 -> c <= sequential_population_variance n c.
 Premises and side conditions: Assumptions on positive sample sizes, admissible
 correlation or nonzero denominator appear explicitly in this declaration;
 no Gaussian regression, distributional independence or measured IQ inputs are assumed.
 Proof/definition method: Reuse the preceding sharp fraction identity and Stdlib division-positivity rules.
 Library reuse: Stdlib.Reals, Lra, Psatz, Field and the already checked
 SequentialReport regression denominator, means, and variance formulas.
 Boundary: The theorem is only exact real algebra for model-specified
 covariance expressions, not a stochastic conditional distribution proof.
 *)
Theorem sensitivity_population_at_least_correlation :
  forall n c, 0 < n -> c <= 1 -> c <= sequential_population_variance n c.
Proof.
  intros n c Hn Hc.
  pose proof (sensitivity_population_common_idiosyncratic n c
    (Rgt_not_eq _ _ Hn)) as H.
  assert (Htail : 0 <= (1-c)/n) by (unfold Rdiv; apply Rmult_le_pos; [nra | apply Rlt_le, Rinv_0_lt_compat; nra]).
  lra.
Qed.

(**
 [sensitivity_population_unit_gap] (theorem) — The distance below unit variance equals the product of extra tests and imperfect correlation divided by count.
 Mathematical meaning: The distance below unit variance equals the product of extra tests and imperfect correlation divided by count.
 Exact checked proposition: forall n c, n <> 0 -> 1-sequential_population_variance n c = (n-1)*(1-c)/n.
 Premises and side conditions: Assumptions on positive sample sizes, admissible
 correlation or nonzero denominator appear explicitly in this declaration;
 no Gaussian regression, distributional independence or measured IQ inputs are assumed.
 Proof/definition method: Apply Stdlib.Field to exact rational formulas and discharge invertibility by the premises.
 Library reuse: Stdlib.Reals, Lra, Psatz, Field and the already checked
 SequentialReport regression denominator, means, and variance formulas.
 Boundary: The theorem is only exact real algebra for model-specified
 covariance expressions, not a stochastic conditional distribution proof.
 *)
Theorem sensitivity_population_unit_gap :
  forall n c, n <> 0 -> 1-sequential_population_variance n c = (n-1)*(1-c)/n.
Proof.
  intros n c Hn; unfold sequential_population_variance, sequential_d; field; nra.
Qed.

(**
 [sensitivity_population_bounded_by_one] (theorem) — Averaging at least one score with correlation at most one cannot have variance above one.
 Mathematical meaning: Averaging at least one score with correlation at most one cannot have variance above one.
 Exact checked proposition: forall n c, 1 <= n -> c <= 1 -> sequential_population_variance n c <= 1.
 Premises and side conditions: Assumptions on positive sample sizes, admissible
 correlation or nonzero denominator appear explicitly in this declaration;
 no Gaussian regression, distributional independence or measured IQ inputs are assumed.
 Proof/definition method: Reuse the preceding sharp fraction identity and Stdlib division-positivity rules.
 Library reuse: Stdlib.Reals, Lra, Psatz, Field and the already checked
 SequentialReport regression denominator, means, and variance formulas.
 Boundary: The theorem is only exact real algebra for model-specified
 covariance expressions, not a stochastic conditional distribution proof.
 *)
Theorem sensitivity_population_bounded_by_one :
  forall n c, 1 <= n -> c <= 1 -> sequential_population_variance n c <= 1.
Proof.
  intros n c Hn Hc.
  pose proof (sensitivity_population_unit_gap n c) as Hgap.
  assert (Hnz : n <> 0) by lra.
  specialize (Hgap Hnz).
  assert (Htail : 0 <= (n-1)*(1-c)/n)
    by (unfold Rdiv; apply Rmult_le_pos; [nra | apply Rlt_le, Rinv_0_lt_compat; nra]).
  lra.
Qed.

(**
 [sensitivity_population_correlation_gap] (theorem) — The exact change in population variance is proportional to correlation increment and off-diagonal test fraction.
 Mathematical meaning: The exact change in population variance is proportional to correlation increment and off-diagonal test fraction.
 Exact checked proposition: forall n c1 c2, n <> 0 -> sequential_population_variance n c2 - sequential_population_variance n c1 = (n-1)*(c2-c1)/n.
 Premises and side conditions: Assumptions on positive sample sizes, admissible
 correlation or nonzero denominator appear explicitly in this declaration;
 no Gaussian regression, distributional independence or measured IQ inputs are assumed.
 Proof/definition method: Apply Stdlib.Field to exact rational formulas and discharge invertibility by the premises.
 Library reuse: Stdlib.Reals, Lra, Psatz, Field and the already checked
 SequentialReport regression denominator, means, and variance formulas.
 Boundary: The theorem is only exact real algebra for model-specified
 covariance expressions, not a stochastic conditional distribution proof.
 *)
Theorem sensitivity_population_correlation_gap :
  forall n c1 c2, n <> 0 -> sequential_population_variance n c2 - sequential_population_variance n c1 = (n-1)*(c2-c1)/n.
Proof.
  intros n c1 c2 Hn; unfold sequential_population_variance, sequential_d; field; nra.
Qed.

(**
 [sensitivity_population_count_gap] (theorem) — Increasing battery size reduces population variance by a sharp residual term k(1-c)/(n(n+k)).
 Mathematical meaning: Increasing battery size reduces population variance by a sharp residual term k(1-c)/(n(n+k)).
 Exact checked proposition: forall n k c, n <> 0 -> n+k <> 0 -> sequential_population_variance n c - sequential_population_variance (n+k) c = k*(1-c)/(n*(n+k)).
 Premises and side conditions: Assumptions on positive sample sizes, admissible
 correlation or nonzero denominator appear explicitly in this declaration;
 no Gaussian regression, distributional independence or measured IQ inputs are assumed.
 Proof/definition method: Apply Stdlib.Field to exact rational formulas and discharge invertibility by the premises.
 Library reuse: Stdlib.Reals, Lra, Psatz, Field and the already checked
 SequentialReport regression denominator, means, and variance formulas.
 Boundary: The theorem is only exact real algebra for model-specified
 covariance expressions, not a stochastic conditional distribution proof.
 *)
Theorem sensitivity_population_count_gap :
  forall n k c, n <> 0 -> n+k <> 0 -> sequential_population_variance n c - sequential_population_variance (n+k) c = k*(1-c)/(n*(n+k)).
Proof.
  intros n k c Hn Hnk; unfold sequential_population_variance, sequential_d; field; nra.
Qed.

(**
 [sensitivity_population_count_monotone] (theorem) — At correlation at most one, enlarging a positive battery cannot increase equal-weight variance.
 Mathematical meaning: At correlation at most one, enlarging a positive battery cannot increase equal-weight variance.
 Exact checked proposition: forall n k c, 0 < n -> 0 <= k -> c <= 1 -> sequential_population_variance (n+k) c <= sequential_population_variance n c.
 Premises and side conditions: Assumptions on positive sample sizes, admissible
 correlation or nonzero denominator appear explicitly in this declaration;
 no Gaussian regression, distributional independence or measured IQ inputs are assumed.
 Proof/definition method: Reuse the preceding sharp fraction identity and Stdlib division-positivity rules.
 Library reuse: Stdlib.Reals, Lra, Psatz, Field and the already checked
 SequentialReport regression denominator, means, and variance formulas.
 Boundary: The theorem is only exact real algebra for model-specified
 covariance expressions, not a stochastic conditional distribution proof.
 *)
Theorem sensitivity_population_count_monotone :
  forall n k c, 0 < n -> 0 <= k -> c <= 1 -> sequential_population_variance (n+k) c <= sequential_population_variance n c.
Proof.
  intros n k c Hn Hk Hc.
  assert (Hnk : 0 < n+k) by lra.
  pose proof (sensitivity_population_count_gap n k c
    (Rgt_not_eq _ _ Hn) (Rgt_not_eq _ _ Hnk)) as Hgap.
  assert (Hge : 0 <= k*(1-c)/(n*(n+k)))
    by (unfold Rdiv; apply Rmult_le_pos; [nra | apply Rlt_le, Rinv_0_lt_compat; nra]).
  lra.
Qed.

(**
 [sensitivity_population_count_strict] (theorem) — With added scores and imperfect correlation, equal-weight population variance strictly decreases.
 Mathematical meaning: With added scores and imperfect correlation, equal-weight population variance strictly decreases.
 Exact checked proposition: forall n k c, 0 < n -> 0 < k -> c < 1 -> sequential_population_variance (n+k) c < sequential_population_variance n c.
 Premises and side conditions: Assumptions on positive sample sizes, admissible
 correlation or nonzero denominator appear explicitly in this declaration;
 no Gaussian regression, distributional independence or measured IQ inputs are assumed.
 Proof/definition method: Reuse the preceding sharp fraction identity and Stdlib division-positivity rules.
 Library reuse: Stdlib.Reals, Lra, Psatz, Field and the already checked
 SequentialReport regression denominator, means, and variance formulas.
 Boundary: The theorem is only exact real algebra for model-specified
 covariance expressions, not a stochastic conditional distribution proof.
 *)
Theorem sensitivity_population_count_strict :
  forall n k c, 0 < n -> 0 < k -> c < 1 -> sequential_population_variance (n+k) c < sequential_population_variance n c.
Proof.
  intros n k c Hn Hk Hc.
  assert (Hnk : 0 < n+k) by lra.
  pose proof (sensitivity_population_count_gap n k c
    (Rgt_not_eq _ _ Hn) (Rgt_not_eq _ _ Hnk)) as Hgap.
  assert (Hpos : 0 < k*(1-c)/(n*(n+k)))
    by (apply Rdiv_lt_0_compat; nra).
  lra.
Qed.

(**
 [sensitivity_population_correlation_monotone] (theorem) — For at least one test, raising correlation cannot lower the variance of the composite mean.
 Mathematical meaning: For at least one test, raising correlation cannot lower the variance of the composite mean.
 Exact checked proposition: forall n c1 c2, 1 <= n -> c1 <= c2 -> sequential_population_variance n c1 <= sequential_population_variance n c2.
 Premises and side conditions: Assumptions on positive sample sizes, admissible
 correlation or nonzero denominator appear explicitly in this declaration;
 no Gaussian regression, distributional independence or measured IQ inputs are assumed.
 Proof/definition method: Reuse the preceding sharp fraction identity and Stdlib division-positivity rules.
 Library reuse: Stdlib.Reals, Lra, Psatz, Field and the already checked
 SequentialReport regression denominator, means, and variance formulas.
 Boundary: The theorem is only exact real algebra for model-specified
 covariance expressions, not a stochastic conditional distribution proof.
 *)
Theorem sensitivity_population_correlation_monotone :
  forall n c1 c2, 1 <= n -> c1 <= c2 -> sequential_population_variance n c1 <= sequential_population_variance n c2.
Proof.
  intros n c1 c2 Hn Hc.
  pose proof (sensitivity_population_correlation_gap n c1 c2) as Hgap.
  assert (Hnz : n <> 0) by lra.
  specialize (Hgap Hnz).
  assert (Hge : 0 <= (n-1)*(c2-c1)/n)
    by (unfold Rdiv; apply Rmult_le_pos; [nra | apply Rlt_le, Rinv_0_lt_compat; nra]).
  lra.
Qed.

(**
 [sensitivity_population_correlation_strict] (theorem) — For at least two tests, strictly increased pair correlation strictly increases average-score variance.
 Mathematical meaning: For at least two tests, strictly increased pair correlation strictly increases average-score variance.
 Exact checked proposition: forall n c1 c2, 1 < n -> c1 < c2 -> sequential_population_variance n c1 < sequential_population_variance n c2.
 Premises and side conditions: Assumptions on positive sample sizes, admissible
 correlation or nonzero denominator appear explicitly in this declaration;
 no Gaussian regression, distributional independence or measured IQ inputs are assumed.
 Proof/definition method: Reuse the preceding sharp fraction identity and Stdlib division-positivity rules.
 Library reuse: Stdlib.Reals, Lra, Psatz, Field and the already checked
 SequentialReport regression denominator, means, and variance formulas.
 Boundary: The theorem is only exact real algebra for model-specified
 covariance expressions, not a stochastic conditional distribution proof.
 *)
Theorem sensitivity_population_correlation_strict :
  forall n c1 c2, 1 < n -> c1 < c2 -> sequential_population_variance n c1 < sequential_population_variance n c2.
Proof.
  intros n c1 c2 Hn Hc.
  pose proof (sensitivity_population_correlation_gap n c1 c2) as Hgap.
  assert (Hnz : n <> 0) by lra.
  specialize (Hgap Hnz).
  assert (Hpos : 0 < (n-1)*(c2-c1)/n)
    by (apply Rdiv_lt_0_compat; nra).
  lra.
Qed.

(**
 [sensitivity_conditional_no_future] (theorem) — With no predicted future observations the defined residual variance of the inclusive average vanishes.
 Mathematical meaning: With no predicted future observations the defined residual variance of the inclusive average vanishes.
 Exact checked proposition: forall r c, sequential_conditional_variance r 0 c = 0.
 Premises and side conditions: Assumptions on positive sample sizes, admissible
 correlation or nonzero denominator appear explicitly in this declaration;
 no Gaussian regression, distributional independence or measured IQ inputs are assumed.
 Proof/definition method: Reuse the maintained ring and nonlinear real arithmetic tactics on the report formulas.
 Library reuse: Stdlib.Reals, Lra, Psatz, Field and the already checked
 SequentialReport regression denominator, means, and variance formulas.
 Boundary: The theorem is only exact real algebra for model-specified
 covariance expressions, not a stochastic conditional distribution proof.
 *)
Theorem sensitivity_conditional_no_future :
  forall r c, sequential_conditional_variance r 0 c = 0.
Proof.
  intros r c; unfold sequential_conditional_variance; ring.
Qed.

(**
 [sensitivity_conditional_independent] (theorem) — At zero correlation the residual variance contributed by k future independent tests is k/(r+k)^2.
 Mathematical meaning: At zero correlation the residual variance contributed by k future independent tests is k/(r+k)^2.
 Exact checked proposition: forall r k, r+k <> 0 -> sequential_conditional_variance r k 0 = k/((r+k)*(r+k)).
 Premises and side conditions: Assumptions on positive sample sizes, admissible
 correlation or nonzero denominator appear explicitly in this declaration;
 no Gaussian regression, distributional independence or measured IQ inputs are assumed.
 Proof/definition method: Apply Stdlib.Field to exact rational formulas and discharge invertibility by the premises.
 Library reuse: Stdlib.Reals, Lra, Psatz, Field and the already checked
 SequentialReport regression denominator, means, and variance formulas.
 Boundary: The theorem is only exact real algebra for model-specified
 covariance expressions, not a stochastic conditional distribution proof.
 *)
Theorem sensitivity_conditional_independent :
  forall r k, r+k <> 0 -> sequential_conditional_variance r k 0 = k/((r+k)*(r+k)).
Proof.
  intros r k Hn; unfold sequential_conditional_variance, sequential_d; field; nra.
Qed.

(**
 [sensitivity_conditional_explained_gap] (theorem) — The variance explained by the initial r scores is exactly r d_total^2/(total^2 d_r).
 Mathematical meaning: The variance explained by the initial r scores is exactly r d_total^2/(total^2 d_r).
 Exact checked proposition: forall r k c, r+k <> 0 -> sequential_d r c <> 0 -> sequential_population_variance (r+k) c - sequential_conditional_variance r k c = r*(sequential_d (r+k) c)*(sequential_d (r+k) c)/((r+k)*(r+k)*sequential_d r c).
 Premises and side conditions: Assumptions on positive sample sizes, admissible
 correlation or nonzero denominator appear explicitly in this declaration;
 no Gaussian regression, distributional independence or measured IQ inputs are assumed.
 Proof/definition method: Apply Stdlib.Field to exact rational formulas and discharge invertibility by the premises.
 Library reuse: Stdlib.Reals, Lra, Psatz, Field and the already checked
 SequentialReport regression denominator, means, and variance formulas.
 Boundary: The theorem is only exact real algebra for model-specified
 covariance expressions, not a stochastic conditional distribution proof.
 *)
Theorem sensitivity_conditional_explained_gap :
  forall r k c, r+k <> 0 -> sequential_d r c <> 0 -> sequential_population_variance (r+k) c - sequential_conditional_variance r k c = r*(sequential_d (r+k) c)*(sequential_d (r+k) c)/((r+k)*(r+k)*sequential_d r c).
Proof.
  intros r k c Hn Hd; unfold sequential_population_variance, sequential_conditional_variance, sequential_d in *; field; nra.
Qed.

(**
 [sensitivity_conditional_fraction_of_population] (theorem) — The residual-to-population variance ratio is precisely the fraction of future uncorrelated variability.
 Mathematical meaning: The residual-to-population variance ratio is precisely the fraction of future uncorrelated variability.
 Exact checked proposition: forall r k c, r+k <> 0 -> sequential_d r c <> 0 -> sequential_d (r+k) c <> 0 -> sequential_conditional_variance r k c / sequential_population_variance (r+k) c = k*(1-c)/((r+k)*sequential_d r c).
 Premises and side conditions: Assumptions on positive sample sizes, admissible
 correlation or nonzero denominator appear explicitly in this declaration;
 no Gaussian regression, distributional independence or measured IQ inputs are assumed.
 Proof/definition method: Apply Stdlib.Field to exact rational formulas and discharge invertibility by the premises.
 Library reuse: Stdlib.Reals, Lra, Psatz, Field and the already checked
 SequentialReport regression denominator, means, and variance formulas.
 Boundary: The theorem is only exact real algebra for model-specified
 covariance expressions, not a stochastic conditional distribution proof.
 *)
Theorem sensitivity_conditional_fraction_of_population :
  forall r k c, r+k <> 0 -> sequential_d r c <> 0 -> sequential_d (r+k) c <> 0 -> sequential_conditional_variance r k c / sequential_population_variance (r+k) c = k*(1-c)/((r+k)*sequential_d r c).
Proof.
  intros r k c Hn Hd Htotal; unfold sequential_population_variance, sequential_conditional_variance, sequential_d in *; field; nra.
Qed.

(**
 [sensitivity_conditional_strict_positive] (theorem) — For genuinely future scores and imperfect nonnegative correlation, the finite residual-variance formula is strictly positive.
 Mathematical meaning: For genuinely future scores and imperfect nonnegative correlation, the finite residual-variance formula is strictly positive.
 Exact checked proposition: forall r k c, 1 <= r -> 0 < k -> 0 <= c -> c < 1 -> 0 < sequential_conditional_variance r k c.
 Premises and side conditions: Assumptions on positive sample sizes, admissible
 correlation or nonzero denominator appear explicitly in this declaration;
 no Gaussian regression, distributional independence or measured IQ inputs are assumed.
 Proof/definition method: Reuse the preceding sharp fraction identity and Stdlib division-positivity rules.
 Library reuse: Stdlib.Reals, Lra, Psatz, Field and the already checked
 SequentialReport regression denominator, means, and variance formulas.
 Boundary: The theorem is only exact real algebra for model-specified
 covariance expressions, not a stochastic conditional distribution proof.
 *)
Theorem sensitivity_conditional_strict_positive :
  forall r k c, 1 <= r -> 0 < k -> 0 <= c -> c < 1 -> 0 < sequential_conditional_variance r k c.
Proof.
  intros r k c Hr Hk Hc Hcu.
  assert (Hd : 0 < sequential_d r c)
    by (apply sequential_denominator_positive_nonnegative_correlation; lra).
  assert (Ht : 0 < sequential_d (r+k) c)
    by (apply sequential_denominator_positive_nonnegative_correlation; lra).
  unfold sequential_conditional_variance.
  apply Rdiv_lt_0_compat; nra.
Qed.

(**
 [sensitivity_conditional_explained_positive] (theorem) — A nonempty observed block under nonnegative correlation explains strictly positive mean-score variance, even at perfect correlation.
 Mathematical meaning: A nonempty observed block under nonnegative correlation explains strictly positive mean-score variance, even at perfect correlation.
 Exact checked proposition: forall r k c, 0 < r -> 0 <= k -> 0 <= c -> 0 < sequential_population_variance (r+k) c - sequential_conditional_variance r k c.
 Premises and side conditions: Assumptions on positive sample sizes, admissible
 correlation or nonzero denominator appear explicitly in this declaration;
 no Gaussian regression, distributional independence or measured IQ inputs are assumed.
 Proof/definition method: Reuse the preceding sharp fraction identity and Stdlib division-positivity rules.
 Library reuse: Stdlib.Reals, Lra, Psatz, Field and the already checked
 SequentialReport regression denominator, means, and variance formulas.
 Boundary: The theorem is only exact real algebra for model-specified
 covariance expressions, not a stochastic conditional distribution proof.
 *)
Theorem sensitivity_conditional_explained_positive :
  forall r k c, 0 < r -> 0 <= k -> 0 <= c -> 0 < sequential_population_variance (r+k) c - sequential_conditional_variance r k c.
Proof.
  intros r k c Hr Hk Hc.
  assert (Hn : 0 < r+k) by lra.
  assert (Hdr : 0 < sequential_d r c)
    by (apply sequential_denominator_positive_nonnegative_correlation; lra).
  assert (Hdt : 0 < sequential_d (r+k) c)
    by (apply sequential_denominator_positive_nonnegative_correlation; lra).
  rewrite sensitivity_conditional_explained_gap
    by (apply Rgt_not_eq; assumption).
  apply Rdiv_lt_0_compat; nra.
Qed.

(**
 [sensitivity_conditional_below_population] (theorem) — The algebraic residual risk cannot exceed the unconditional composite-score variance for a nonempty initial block.
 Mathematical meaning: The algebraic residual risk cannot exceed the unconditional composite-score variance for a nonempty initial block.
 Exact checked proposition: forall r k c, 1 <= r -> 0 <= k -> 0 <= c -> sequential_conditional_variance r k c <= sequential_population_variance (r+k) c.
 Premises and side conditions: Assumptions on positive sample sizes, admissible
 correlation or nonzero denominator appear explicitly in this declaration;
 no Gaussian regression, distributional independence or measured IQ inputs are assumed.
 Proof/definition method: Reuse the maintained ring and nonlinear real arithmetic tactics on the report formulas.
 Library reuse: Stdlib.Reals, Lra, Psatz, Field and the already checked
 SequentialReport regression denominator, means, and variance formulas.
 Boundary: The theorem is only exact real algebra for model-specified
 covariance expressions, not a stochastic conditional distribution proof.
 *)
Theorem sensitivity_conditional_below_population :
  forall r k c, 1 <= r -> 0 <= k -> 0 <= c -> sequential_conditional_variance r k c <= sequential_population_variance (r+k) c.
Proof.
  intros r k c Hr Hk Hc.
  pose proof (sensitivity_conditional_explained_positive r k c) as H.
  assert (Hrp : 0 < r) by lra.
  specialize (H Hrp Hk Hc); lra.
Qed.

(**
 [sensitivity_conditional_first_future] (theorem) — The first predicted score has a closed Schur residual variance with numerator (1-c)(1+rc).
 Mathematical meaning: The first predicted score has a closed Schur residual variance with numerator (1-c)(1+rc).
 Exact checked proposition: forall r c, r+1 <> 0 -> sequential_d r c <> 0 -> sequential_conditional_variance r 1 c = (1-c)*(1+r*c)/((r+1)*(r+1)*sequential_d r c).
 Premises and side conditions: Assumptions on positive sample sizes, admissible
 correlation or nonzero denominator appear explicitly in this declaration;
 no Gaussian regression, distributional independence or measured IQ inputs are assumed.
 Proof/definition method: Apply Stdlib.Field to exact rational formulas and discharge invertibility by the premises.
 Library reuse: Stdlib.Reals, Lra, Psatz, Field and the already checked
 SequentialReport regression denominator, means, and variance formulas.
 Boundary: The theorem is only exact real algebra for model-specified
 covariance expressions, not a stochastic conditional distribution proof.
 *)
Theorem sensitivity_conditional_first_future :
  forall r c, r+1 <> 0 -> sequential_d r c <> 0 -> sequential_conditional_variance r 1 c = (1-c)*(1+r*c)/((r+1)*(r+1)*sequential_d r c).
Proof.
  intros r c Hn Hd; unfold sequential_conditional_variance, sequential_d in *; field; nra.
Qed.

(**
 [sensitivity_mean_zero_score] (theorem) — A zero initial standardized score gives a zero inclusive predicted mean for any coefficients and counts.
 Mathematical meaning: A zero initial standardized score gives a zero inclusive predicted mean for any coefficients and counts.
 Exact checked proposition: forall r k c, sequential_inclusive_mean r k c 0 = 0.
 Premises and side conditions: Assumptions on positive sample sizes, admissible
 correlation or nonzero denominator appear explicitly in this declaration;
 no Gaussian regression, distributional independence or measured IQ inputs are assumed.
 Proof/definition method: Reuse the maintained ring and nonlinear real arithmetic tactics on the report formulas.
 Library reuse: Stdlib.Reals, Lra, Psatz, Field and the already checked
 SequentialReport regression denominator, means, and variance formulas.
 Boundary: The theorem is only exact real algebra for model-specified
 covariance expressions, not a stochastic conditional distribution proof.
 *)
Theorem sensitivity_mean_zero_score :
  forall r k c, sequential_inclusive_mean r k c 0 = 0.
Proof.
  intros r k c; unfold sequential_inclusive_mean, sequential_prediction; ring.
Qed.

(**
 [sensitivity_mean_no_future] (theorem) — Without later predicted scores, the inclusive average equals the original observed score.
 Mathematical meaning: Without later predicted scores, the inclusive average equals the original observed score.
 Exact checked proposition: forall r c a, r <> 0 -> sequential_inclusive_mean r 0 c a = a.
 Premises and side conditions: Assumptions on positive sample sizes, admissible
 correlation or nonzero denominator appear explicitly in this declaration;
 no Gaussian regression, distributional independence or measured IQ inputs are assumed.
 Proof/definition method: Apply Stdlib.Field to exact rational formulas and discharge invertibility by the premises.
 Library reuse: Stdlib.Reals, Lra, Psatz, Field and the already checked
 SequentialReport regression denominator, means, and variance formulas.
 Boundary: The theorem is only exact real algebra for model-specified
 covariance expressions, not a stochastic conditional distribution proof.
 *)
Theorem sensitivity_mean_no_future :
  forall r c a, r <> 0 -> sequential_inclusive_mean r 0 c a = a.
Proof.
  intros r c a Hr.
  unfold sequential_inclusive_mean.
  replace (0 * sequential_prediction r c a) with 0 by ring.
  field; nra.
Qed.

(**
 [sensitivity_mean_independent] (theorem) — When all scores are uncorrelated, future expected scores are zero and the inclusive average is diluted by r/(r+k).
 Mathematical meaning: When all scores are uncorrelated, future expected scores are zero and the inclusive average is diluted by r/(r+k).
 Exact checked proposition: forall r k a, r+k <> 0 -> sequential_inclusive_mean r k 0 a = r*a/(r+k).
 Premises and side conditions: Assumptions on positive sample sizes, admissible
 correlation or nonzero denominator appear explicitly in this declaration;
 no Gaussian regression, distributional independence or measured IQ inputs are assumed.
 Proof/definition method: Apply Stdlib.Field to exact rational formulas and discharge invertibility by the premises.
 Library reuse: Stdlib.Reals, Lra, Psatz, Field and the already checked
 SequentialReport regression denominator, means, and variance formulas.
 Boundary: The theorem is only exact real algebra for model-specified
 covariance expressions, not a stochastic conditional distribution proof.
 *)
Theorem sensitivity_mean_independent :
  forall r k a, r+k <> 0 -> sequential_inclusive_mean r k 0 a = r*a/(r+k).
Proof.
  intros r k a Hn; unfold sequential_inclusive_mean, sequential_prediction, sequential_d; field; nra.
Qed.

(**
 [sensitivity_mean_observed_gap] (theorem) — The exact shrinkage of the inclusive mean below a positive observed score is proportional to k(1-c).
 Mathematical meaning: The exact shrinkage of the inclusive mean below a positive observed score is proportional to k(1-c).
 Exact checked proposition: forall r k c a, r+k <> 0 -> sequential_d r c <> 0 -> a-sequential_inclusive_mean r k c a = k*(1-c)*a/((r+k)*sequential_d r c).
 Premises and side conditions: Assumptions on positive sample sizes, admissible
 correlation or nonzero denominator appear explicitly in this declaration;
 no Gaussian regression, distributional independence or measured IQ inputs are assumed.
 Proof/definition method: Apply Stdlib.Field to exact rational formulas and discharge invertibility by the premises.
 Library reuse: Stdlib.Reals, Lra, Psatz, Field and the already checked
 SequentialReport regression denominator, means, and variance formulas.
 Boundary: The theorem is only exact real algebra for model-specified
 covariance expressions, not a stochastic conditional distribution proof.
 *)
Theorem sensitivity_mean_observed_gap :
  forall r k c a, r+k <> 0 -> sequential_d r c <> 0 -> a-sequential_inclusive_mean r k c a = k*(1-c)*a/((r+k)*sequential_d r c).
Proof.
  intros r k c a Hn Hd; unfold sequential_inclusive_mean, sequential_prediction, sequential_d in *; field; nra.
Qed.

(**
 [sensitivity_mean_prediction_gap] (theorem) — The inclusive mean exceeds the common future prediction by the initial-score weight r(1-c).
 Mathematical meaning: The inclusive mean exceeds the common future prediction by the initial-score weight r(1-c).
 Exact checked proposition: forall r k c a, r+k <> 0 -> sequential_d r c <> 0 -> sequential_inclusive_mean r k c a - sequential_prediction r c a = r*(1-c)*a/((r+k)*sequential_d r c).
 Premises and side conditions: Assumptions on positive sample sizes, admissible
 correlation or nonzero denominator appear explicitly in this declaration;
 no Gaussian regression, distributional independence or measured IQ inputs are assumed.
 Proof/definition method: Apply Stdlib.Field to exact rational formulas and discharge invertibility by the premises.
 Library reuse: Stdlib.Reals, Lra, Psatz, Field and the already checked
 SequentialReport regression denominator, means, and variance formulas.
 Boundary: The theorem is only exact real algebra for model-specified
 covariance expressions, not a stochastic conditional distribution proof.
 *)
Theorem sensitivity_mean_prediction_gap :
  forall r k c a, r+k <> 0 -> sequential_d r c <> 0 -> sequential_inclusive_mean r k c a - sequential_prediction r c a = r*(1-c)*a/((r+k)*sequential_d r c).
Proof.
  intros r k c a Hn Hd; unfold sequential_inclusive_mean, sequential_prediction, sequential_d in *; field; nra.
Qed.

(**
 [sensitivity_mean_additive_in_score] (theorem) — A shift of two initial scores induces the sum of their separate inclusive predictions by exact linearity.
 Mathematical meaning: A shift of two initial scores induces the sum of their separate inclusive predictions by exact linearity.
 Exact checked proposition: forall r k c a b, sequential_inclusive_mean r k c (a+b) = sequential_inclusive_mean r k c a + sequential_inclusive_mean r k c b.
 Premises and side conditions: Assumptions on positive sample sizes, admissible
 correlation or nonzero denominator appear explicitly in this declaration;
 no Gaussian regression, distributional independence or measured IQ inputs are assumed.
 Proof/definition method: Reuse the preceding sharp fraction identity and Stdlib division-positivity rules.
 Library reuse: Stdlib.Reals, Lra, Psatz, Field and the already checked
 SequentialReport regression denominator, means, and variance formulas.
 Boundary: The theorem is only exact real algebra for model-specified
 covariance expressions, not a stochastic conditional distribution proof.
 *)
Theorem sensitivity_mean_additive_in_score :
  forall r k c a b, sequential_inclusive_mean r k c (a+b) = sequential_inclusive_mean r k c a + sequential_inclusive_mean r k c b.
Proof.
  intros r k c a b; unfold sequential_inclusive_mean, sequential_prediction, Rdiv; ring.
Qed.

(**
 [sensitivity_mean_homogeneous_in_score] (theorem) — Rescaling the observed standardized score commutes with the inclusive prediction and averaging operation.
 Mathematical meaning: Rescaling the observed standardized score commutes with the inclusive prediction and averaging operation.
 Exact checked proposition: forall r k c a t, sequential_inclusive_mean r k c (t*a) = t*sequential_inclusive_mean r k c a.
 Premises and side conditions: Assumptions on positive sample sizes, admissible
 correlation or nonzero denominator appear explicitly in this declaration;
 no Gaussian regression, distributional independence or measured IQ inputs are assumed.
 Proof/definition method: Reuse the preceding sharp fraction identity and Stdlib division-positivity rules.
 Library reuse: Stdlib.Reals, Lra, Psatz, Field and the already checked
 SequentialReport regression denominator, means, and variance formulas.
 Boundary: The theorem is only exact real algebra for model-specified
 covariance expressions, not a stochastic conditional distribution proof.
 *)
Theorem sensitivity_mean_homogeneous_in_score :
  forall r k c a t, sequential_inclusive_mean r k c (t*a) = t*sequential_inclusive_mean r k c a.
Proof.
  intros r k c a t; unfold sequential_inclusive_mean, sequential_prediction, Rdiv; ring.
Qed.

(**
 [sensitivity_mean_not_above_observation] (theorem) — For a positive observed score and admissible correlation, adding predicted observations cannot increase the inclusive mean above the observation.
 Mathematical meaning: For a positive observed score and admissible correlation, adding predicted observations cannot increase the inclusive mean above the observation.
 Exact checked proposition: forall r k c a, 1 <= r -> 0 <= k -> 0 <= c -> c <= 1 -> 0 <= a -> sequential_inclusive_mean r k c a <= a.
 Premises and side conditions: Assumptions on positive sample sizes, admissible
 correlation or nonzero denominator appear explicitly in this declaration;
 no Gaussian regression, distributional independence or measured IQ inputs are assumed.
 Proof/definition method: Reuse the preceding sharp fraction identity and Stdlib division-positivity rules.
 Library reuse: Stdlib.Reals, Lra, Psatz, Field and the already checked
 SequentialReport regression denominator, means, and variance formulas.
 Boundary: The theorem is only exact real algebra for model-specified
 covariance expressions, not a stochastic conditional distribution proof.
 *)
Theorem sensitivity_mean_not_above_observation :
  forall r k c a, 1 <= r -> 0 <= k -> 0 <= c -> c <= 1 -> 0 <= a -> sequential_inclusive_mean r k c a <= a.
Proof.
  intros r k c a Hr Hk Hc Hcu Ha.
  assert (Hn : 0 < r+k) by lra.
  assert (Hd : 0 < sequential_d r c)
    by (apply sequential_denominator_positive_nonnegative_correlation; lra).
  pose proof (sensitivity_mean_observed_gap r k c a
    (Rgt_not_eq _ _ Hn) (Rgt_not_eq _ _ Hd)) as Hgap.
  assert (Hge : 0 <= k*(1-c)*a/((r+k)*sequential_d r c))
    by (unfold Rdiv; apply Rmult_le_pos; [nra | apply Rlt_le, Rinv_0_lt_compat; nra]).
  lra.
Qed.

(**
 [sensitivity_mean_not_below_prediction] (theorem) — A nonnegative observed score makes the inclusive mean no smaller than any common linear prediction under admissible correlation.
 Mathematical meaning: A nonnegative observed score makes the inclusive mean no smaller than any common linear prediction under admissible correlation.
 Exact checked proposition: forall r k c a, 1 <= r -> 0 <= k -> 0 <= c -> c <= 1 -> 0 <= a -> sequential_prediction r c a <= sequential_inclusive_mean r k c a.
 Premises and side conditions: Assumptions on positive sample sizes, admissible
 correlation or nonzero denominator appear explicitly in this declaration;
 no Gaussian regression, distributional independence or measured IQ inputs are assumed.
 Proof/definition method: Reuse the preceding sharp fraction identity and Stdlib division-positivity rules.
 Library reuse: Stdlib.Reals, Lra, Psatz, Field and the already checked
 SequentialReport regression denominator, means, and variance formulas.
 Boundary: The theorem is only exact real algebra for model-specified
 covariance expressions, not a stochastic conditional distribution proof.
 *)
Theorem sensitivity_mean_not_below_prediction :
  forall r k c a, 1 <= r -> 0 <= k -> 0 <= c -> c <= 1 -> 0 <= a -> sequential_prediction r c a <= sequential_inclusive_mean r k c a.
Proof.
  intros r k c a Hr Hk Hc Hcu Ha.
  assert (Hn : 0 < r+k) by lra.
  assert (Hd : 0 < sequential_d r c)
    by (apply sequential_denominator_positive_nonnegative_correlation; lra).
  pose proof (sensitivity_mean_prediction_gap r k c a
    (Rgt_not_eq _ _ Hn) (Rgt_not_eq _ _ Hd)) as Hgap.
  assert (Hge : 0 <= r*(1-c)*a/((r+k)*sequential_d r c))
    by (unfold Rdiv; apply Rmult_le_pos; [nra | apply Rlt_le, Rinv_0_lt_compat; nra]).
  lra.
Qed.

(**
 [sensitivity_mean_correlation_gap] (theorem) — The increase in inclusive mean under a correlation increase has an exact rational derivative-free comparison.
 Mathematical meaning: The increase in inclusive mean under a correlation increase has an exact rational derivative-free comparison.
 Exact checked proposition: forall r k c1 c2 a, r+k <> 0 -> sequential_d r c1 <> 0 -> sequential_d r c2 <> 0 -> sequential_inclusive_mean r k c2 a - sequential_inclusive_mean r k c1 a = r*k*a*(c2-c1)/((r+k)*sequential_d r c1*sequential_d r c2).
 Premises and side conditions: Assumptions on positive sample sizes, admissible
 correlation or nonzero denominator appear explicitly in this declaration;
 no Gaussian regression, distributional independence or measured IQ inputs are assumed.
 Proof/definition method: Apply Stdlib.Field to exact rational formulas and discharge invertibility by the premises.
 Library reuse: Stdlib.Reals, Lra, Psatz, Field and the already checked
 SequentialReport regression denominator, means, and variance formulas.
 Boundary: The theorem is only exact real algebra for model-specified
 covariance expressions, not a stochastic conditional distribution proof.
 *)
Theorem sensitivity_mean_correlation_gap :
  forall r k c1 c2 a, r+k <> 0 -> sequential_d r c1 <> 0 -> sequential_d r c2 <> 0 -> sequential_inclusive_mean r k c2 a - sequential_inclusive_mean r k c1 a = r*k*a*(c2-c1)/((r+k)*sequential_d r c1*sequential_d r c2).
Proof.
  intros r k c1 c2 a Hn H1 H2; unfold sequential_inclusive_mean, sequential_prediction, sequential_d in *; field; nra.
Qed.

(**
 [sensitivity_mean_future_count_gap] (theorem) — Comparing different numbers of predicted future scores yields an exact decrease proportional to count increase and unpredictable variance.
 Mathematical meaning: Comparing different numbers of predicted future scores yields an exact decrease proportional to count increase and unpredictable variance.
 Exact checked proposition: forall r k1 k2 c a, sequential_d r c <> 0 -> r+k1 <> 0 -> r+k2 <> 0 -> sequential_inclusive_mean r k1 c a - sequential_inclusive_mean r k2 c a = r*(k2-k1)*(1-c)*a/(sequential_d r c*(r+k1)*(r+k2)).
 Premises and side conditions: Assumptions on positive sample sizes, admissible
 correlation or nonzero denominator appear explicitly in this declaration;
 no Gaussian regression, distributional independence or measured IQ inputs are assumed.
 Proof/definition method: Apply Stdlib.Field to exact rational formulas and discharge invertibility by the premises.
 Library reuse: Stdlib.Reals, Lra, Psatz, Field and the already checked
 SequentialReport regression denominator, means, and variance formulas.
 Boundary: The theorem is only exact real algebra for model-specified
 covariance expressions, not a stochastic conditional distribution proof.
 *)
Theorem sensitivity_mean_future_count_gap :
  forall r k1 k2 c a, sequential_d r c <> 0 -> r+k1 <> 0 -> r+k2 <> 0 -> sequential_inclusive_mean r k1 c a - sequential_inclusive_mean r k2 c a = r*(k2-k1)*(1-c)*a/(sequential_d r c*(r+k1)*(r+k2)).
Proof.
  intros r k1 k2 c a Hd H1 H2; unfold sequential_inclusive_mean, sequential_prediction, sequential_d in *; field; nra.
Qed.

