(** Module: ThreeTestSchur.v
 Purpose: Instantiate all trivariate Schur covariance conditions for the
 AB|C, AC|B and BC|A conditional pairings in multiple-test admissions.
 Mathematical representation: One six-entry symmetric trivariate covariance
 candidate is reused under three different choices of conditioning test.
 Exact residual Cauchy-Schwarz, singularity and determinant sign criteria
 are instantiated without creating an independent matrix or Gaussian law.
 Explicit hypotheses: The raw trivariate covariance coordinates are real;
 each sign equivalence requires strictly positive conditioning variance.
 Neither Gaussianity nor positive semidefiniteness is assumed implicitly.
 Library use: Canonical TrivariateSchur generic theorems, Rocq Stdlib.Reals.
 Limitations: The algebra is needed by trivariate conditional Gaussian
 interpretations but does not derive their probability distributions,
 independence or normal-tail integrals.
 Reproduction: scripts/compile_rocq.sh in Rocq 9.2, compiling
 TrivariateSchur before this Towers report-specific module.
 AI disclosure: AI-assisted code, comments, specializations and audit;
 formal validity depends on Rocq's kernel checking at the final SHA.
*)
From Stdlib Require Import Reals.
Require Import TrivariateSchur.
Open Scope R_scope.

(**
 [TripleCovariance] (definition) — A named six-coordinate trivariate covariance candidate for the three IQ-admissions tests.
 Mathematical meaning: A named six-coordinate trivariate covariance candidate for the three IQ-admissions tests. The result is used to audit conditional covariance or precision in a three-test score model.
 Exact declaration: Record TripleCovariance : Type := {
  covariance_var_A : R;
  covariance_var_B : R;
  covariance_var_C : R;
  covariance_AB : R;
  covariance_AC : R;
  covariance_BC : R
}.
 Premises and side conditions: All scalar quantities are real. Strict conditioning variance and any determinant, residual or nonzero assumptions are explicit in the statement; no positive semidefinite matrix is silently assumed.
 Proof/definition method: A transparent real polynomial without independent probability or matrix implementations.
 Library reuse: Rocq standard Reals, Lra, Psatz and Ring, rather than a custom algebra solver or a duplicate probability-sum implementation.
 Boundary: Exact 3x3 covariance-candidate algebra; no continuous Gaussian conditional law, normal tail or empirical psychometric assertion is proved here.
*)
Record TripleCovariance : Type := {
  covariance_var_A : R;
  covariance_var_B : R;
  covariance_var_C : R;
  covariance_AB : R;
  covariance_AC : R;
  covariance_BC : R
}.

(**
 [triple_AB_given_C_factor] (theorem) — The exact three-variable Schur determinant factorization. This is the AB conditioned on C instantiation using the named test covariance coordinates.
 Mathematical meaning: The exact three-variable Schur determinant factorization. This is the AB conditioned on C instantiation using the named test covariance coordinates. The result is used to audit conditional covariance or precision in a three-test score model.
 Exact checked proposition: forall m : TripleCovariance, ((tri_left(undefined)(covariance_var_A m)(undefined)(covariance_var_C m)(undefined)(covariance_AC m)) * (tri_right(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_BC m))) - ((tri_cross(undefined)(covariance_AB m)(undefined)(covariance_var_C m)(undefined)(covariance_AC m)(undefined)(covariance_BC m)) * (tri_cross(undefined)(covariance_AB m)(undefined)(covariance_var_C m)(undefined)(covariance_AC m)(undefined)(covariance_BC m))) = (covariance_var_C m) * (tri_determinant(undefined)(covariance_var_A m)(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)(undefined)(covariance_BC m)).
 Premises and side conditions: All scalar quantities are real. Strict conditioning variance and any determinant, residual or nonzero assumptions are explicit in the statement; no positive semidefinite matrix is silently assumed.
 Proof/definition method: Deduction from the exact trivariate Schur factorization using canonical real polynomial normalization, inequalities and elementary real algebra.
 Library reuse: Rocq standard Reals, Lra, Psatz and Ring, rather than a custom algebra solver or a duplicate probability-sum implementation.
 Boundary: Exact 3x3 covariance-candidate algebra; no continuous Gaussian conditional law, normal tail or empirical psychometric assertion is proved here.
*)
Theorem triple_AB_given_C_factor :
  forall m : TripleCovariance, ((tri_left(undefined)(covariance_var_A m)(undefined)(covariance_var_C m)(undefined)(covariance_AC m)) * (tri_right(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_BC m))) - ((tri_cross(undefined)(covariance_AB m)(undefined)(covariance_var_C m)(undefined)(covariance_AC m)(undefined)(covariance_BC m)) * (tri_cross(undefined)(covariance_AB m)(undefined)(covariance_var_C m)(undefined)(covariance_AC m)(undefined)(covariance_BC m))) = (covariance_var_C m) * (tri_determinant(undefined)(covariance_var_A m)(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)(undefined)(covariance_BC m)).
Proof.
  intro m.
  exact (trivariate_factor
    (covariance_var_A m) (covariance_var_B m) (covariance_var_C m) (covariance_AB m) (covariance_AC m) (covariance_BC m)).
Qed.

(**
 [triple_AB_given_C_balance] (theorem) — The residual product is the sum of squared conditional cross-covariance and the determinant contribution. This is the AB conditioned on C instantiation using the named test covariance coordinates.
 Mathematical meaning: The residual product is the sum of squared conditional cross-covariance and the determinant contribution. This is the AB conditioned on C instantiation using the named test covariance coordinates. The result is used to audit conditional covariance or precision in a three-test score model.
 Exact checked proposition: forall m : TripleCovariance, ((tri_left(undefined)(covariance_var_A m)(undefined)(covariance_var_C m)(undefined)(covariance_AC m)) * (tri_right(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_BC m))) = ((tri_cross(undefined)(covariance_AB m)(undefined)(covariance_var_C m)(undefined)(covariance_AC m)(undefined)(covariance_BC m)) * (tri_cross(undefined)(covariance_AB m)(undefined)(covariance_var_C m)(undefined)(covariance_AC m)(undefined)(covariance_BC m))) + (covariance_var_C m) * (tri_determinant(undefined)(covariance_var_A m)(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)(undefined)(covariance_BC m)).
 Premises and side conditions: All scalar quantities are real. Strict conditioning variance and any determinant, residual or nonzero assumptions are explicit in the statement; no positive semidefinite matrix is silently assumed.
 Proof/definition method: Deduction from the exact trivariate Schur factorization using canonical real polynomial normalization, inequalities and elementary real algebra.
 Library reuse: Rocq standard Reals, Lra, Psatz and Ring, rather than a custom algebra solver or a duplicate probability-sum implementation.
 Boundary: Exact 3x3 covariance-candidate algebra; no continuous Gaussian conditional law, normal tail or empirical psychometric assertion is proved here.
*)
Theorem triple_AB_given_C_balance :
  forall m : TripleCovariance, ((tri_left(undefined)(covariance_var_A m)(undefined)(covariance_var_C m)(undefined)(covariance_AC m)) * (tri_right(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_BC m))) = ((tri_cross(undefined)(covariance_AB m)(undefined)(covariance_var_C m)(undefined)(covariance_AC m)(undefined)(covariance_BC m)) * (tri_cross(undefined)(covariance_AB m)(undefined)(covariance_var_C m)(undefined)(covariance_AC m)(undefined)(covariance_BC m))) + (covariance_var_C m) * (tri_determinant(undefined)(covariance_var_A m)(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)(undefined)(covariance_BC m)).
Proof.
  intro m.
  exact (trivariate_balance
    (covariance_var_A m) (covariance_var_B m) (covariance_var_C m) (covariance_AB m) (covariance_AC m) (covariance_BC m)).
Qed.

(**
 [triple_AB_given_C_singular_implies_tight] (theorem) — A zero trivariate determinant gives exact saturation of the residual covariance inequality. This is the AB conditioned on C instantiation using the named test covariance coordinates.
 Mathematical meaning: A zero trivariate determinant gives exact saturation of the residual covariance inequality. This is the AB conditioned on C instantiation using the named test covariance coordinates. The result is used to audit conditional covariance or precision in a three-test score model.
 Exact checked proposition: forall m : TripleCovariance, (tri_determinant(undefined)(covariance_var_A m)(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)(undefined)(covariance_BC m)) = 0 -> ((tri_left(undefined)(covariance_var_A m)(undefined)(covariance_var_C m)(undefined)(covariance_AC m)) * (tri_right(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_BC m))) = ((tri_cross(undefined)(covariance_AB m)(undefined)(covariance_var_C m)(undefined)(covariance_AC m)(undefined)(covariance_BC m)) * (tri_cross(undefined)(covariance_AB m)(undefined)(covariance_var_C m)(undefined)(covariance_AC m)(undefined)(covariance_BC m))).
 Premises and side conditions: All scalar quantities are real. Strict conditioning variance and any determinant, residual or nonzero assumptions are explicit in the statement; no positive semidefinite matrix is silently assumed.
 Proof/definition method: Deduction from the exact trivariate Schur factorization using canonical real polynomial normalization, inequalities and elementary real algebra.
 Library reuse: Rocq standard Reals, Lra, Psatz and Ring, rather than a custom algebra solver or a duplicate probability-sum implementation.
 Boundary: Exact 3x3 covariance-candidate algebra; no continuous Gaussian conditional law, normal tail or empirical psychometric assertion is proved here.
*)
Theorem triple_AB_given_C_singular_implies_tight :
  forall m : TripleCovariance, (tri_determinant(undefined)(covariance_var_A m)(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)(undefined)(covariance_BC m)) = 0 -> ((tri_left(undefined)(covariance_var_A m)(undefined)(covariance_var_C m)(undefined)(covariance_AC m)) * (tri_right(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_BC m))) = ((tri_cross(undefined)(covariance_AB m)(undefined)(covariance_var_C m)(undefined)(covariance_AC m)(undefined)(covariance_BC m)) * (tri_cross(undefined)(covariance_AB m)(undefined)(covariance_var_C m)(undefined)(covariance_AC m)(undefined)(covariance_BC m))).
Proof.
  intro m.
  exact (trivariate_singular_implies_tight
    (covariance_var_A m) (covariance_var_B m) (covariance_var_C m) (covariance_AB m) (covariance_AC m) (covariance_BC m)).
Qed.

(**
 [triple_AB_given_C_tight_iff_singular] (theorem) — For positive conditioning variance, tightness is equivalent to a zero determinant. This is the AB conditioned on C instantiation using the named test covariance coordinates.
 Mathematical meaning: For positive conditioning variance, tightness is equivalent to a zero determinant. This is the AB conditioned on C instantiation using the named test covariance coordinates. The result is used to audit conditional covariance or precision in a three-test score model.
 Exact checked proposition: forall m : TripleCovariance, 0 < (covariance_var_C m) -> (((tri_left(undefined)(covariance_var_A m)(undefined)(covariance_var_C m)(undefined)(covariance_AC m)) * (tri_right(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_BC m))) = ((tri_cross(undefined)(covariance_AB m)(undefined)(covariance_var_C m)(undefined)(covariance_AC m)(undefined)(covariance_BC m)) * (tri_cross(undefined)(covariance_AB m)(undefined)(covariance_var_C m)(undefined)(covariance_AC m)(undefined)(covariance_BC m))) <-> (tri_determinant(undefined)(covariance_var_A m)(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)(undefined)(covariance_BC m)) = 0).
 Premises and side conditions: All scalar quantities are real. Strict conditioning variance and any determinant, residual or nonzero assumptions are explicit in the statement; no positive semidefinite matrix is silently assumed.
 Proof/definition method: Deduction from the exact trivariate Schur factorization using canonical real polynomial normalization, inequalities and elementary real algebra.
 Library reuse: Rocq standard Reals, Lra, Psatz and Ring, rather than a custom algebra solver or a duplicate probability-sum implementation.
 Boundary: Exact 3x3 covariance-candidate algebra; no continuous Gaussian conditional law, normal tail or empirical psychometric assertion is proved here.
*)
Theorem triple_AB_given_C_tight_iff_singular :
  forall m : TripleCovariance, 0 < (covariance_var_C m) -> (((tri_left(undefined)(covariance_var_A m)(undefined)(covariance_var_C m)(undefined)(covariance_AC m)) * (tri_right(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_BC m))) = ((tri_cross(undefined)(covariance_AB m)(undefined)(covariance_var_C m)(undefined)(covariance_AC m)(undefined)(covariance_BC m)) * (tri_cross(undefined)(covariance_AB m)(undefined)(covariance_var_C m)(undefined)(covariance_AC m)(undefined)(covariance_BC m))) <-> (tri_determinant(undefined)(covariance_var_A m)(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)(undefined)(covariance_BC m)) = 0).
Proof.
  intro m.
  exact (trivariate_tight_iff_singular
    (covariance_var_A m) (covariance_var_B m) (covariance_var_C m) (covariance_AB m) (covariance_AC m) (covariance_BC m)).
Qed.

(**
 [triple_AB_given_C_positive_iff_strict] (theorem) — Positive determinant is equivalent to a strict Schur Cauchy-Schwarz gap. This is the AB conditioned on C instantiation using the named test covariance coordinates.
 Mathematical meaning: Positive determinant is equivalent to a strict Schur Cauchy-Schwarz gap. This is the AB conditioned on C instantiation using the named test covariance coordinates. The result is used to audit conditional covariance or precision in a three-test score model.
 Exact checked proposition: forall m : TripleCovariance, 0 < (covariance_var_C m) -> (0 < (tri_determinant(undefined)(covariance_var_A m)(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)(undefined)(covariance_BC m)) <-> ((tri_cross(undefined)(covariance_AB m)(undefined)(covariance_var_C m)(undefined)(covariance_AC m)(undefined)(covariance_BC m)) * (tri_cross(undefined)(covariance_AB m)(undefined)(covariance_var_C m)(undefined)(covariance_AC m)(undefined)(covariance_BC m))) < ((tri_left(undefined)(covariance_var_A m)(undefined)(covariance_var_C m)(undefined)(covariance_AC m)) * (tri_right(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_BC m)))).
 Premises and side conditions: All scalar quantities are real. Strict conditioning variance and any determinant, residual or nonzero assumptions are explicit in the statement; no positive semidefinite matrix is silently assumed.
 Proof/definition method: Deduction from the exact trivariate Schur factorization using canonical real polynomial normalization, inequalities and elementary real algebra.
 Library reuse: Rocq standard Reals, Lra, Psatz and Ring, rather than a custom algebra solver or a duplicate probability-sum implementation.
 Boundary: Exact 3x3 covariance-candidate algebra; no continuous Gaussian conditional law, normal tail or empirical psychometric assertion is proved here.
*)
Theorem triple_AB_given_C_positive_iff_strict :
  forall m : TripleCovariance, 0 < (covariance_var_C m) -> (0 < (tri_determinant(undefined)(covariance_var_A m)(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)(undefined)(covariance_BC m)) <-> ((tri_cross(undefined)(covariance_AB m)(undefined)(covariance_var_C m)(undefined)(covariance_AC m)(undefined)(covariance_BC m)) * (tri_cross(undefined)(covariance_AB m)(undefined)(covariance_var_C m)(undefined)(covariance_AC m)(undefined)(covariance_BC m))) < ((tri_left(undefined)(covariance_var_A m)(undefined)(covariance_var_C m)(undefined)(covariance_AC m)) * (tri_right(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_BC m)))).
Proof.
  intro m.
  exact (trivariate_positive_iff_strict
    (covariance_var_A m) (covariance_var_B m) (covariance_var_C m) (covariance_AB m) (covariance_AC m) (covariance_BC m)).
Qed.

(**
 [triple_AB_given_C_negative_iff_reverse] (theorem) — Negative determinant is equivalent to strict reversal of the Schur inequality. This is the AB conditioned on C instantiation using the named test covariance coordinates.
 Mathematical meaning: Negative determinant is equivalent to strict reversal of the Schur inequality. This is the AB conditioned on C instantiation using the named test covariance coordinates. The result is used to audit conditional covariance or precision in a three-test score model.
 Exact checked proposition: forall m : TripleCovariance, 0 < (covariance_var_C m) -> ((tri_determinant(undefined)(covariance_var_A m)(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)(undefined)(covariance_BC m)) < 0 <-> ((tri_left(undefined)(covariance_var_A m)(undefined)(covariance_var_C m)(undefined)(covariance_AC m)) * (tri_right(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_BC m))) < ((tri_cross(undefined)(covariance_AB m)(undefined)(covariance_var_C m)(undefined)(covariance_AC m)(undefined)(covariance_BC m)) * (tri_cross(undefined)(covariance_AB m)(undefined)(covariance_var_C m)(undefined)(covariance_AC m)(undefined)(covariance_BC m)))).
 Premises and side conditions: All scalar quantities are real. Strict conditioning variance and any determinant, residual or nonzero assumptions are explicit in the statement; no positive semidefinite matrix is silently assumed.
 Proof/definition method: Deduction from the exact trivariate Schur factorization using canonical real polynomial normalization, inequalities and elementary real algebra.
 Library reuse: Rocq standard Reals, Lra, Psatz and Ring, rather than a custom algebra solver or a duplicate probability-sum implementation.
 Boundary: Exact 3x3 covariance-candidate algebra; no continuous Gaussian conditional law, normal tail or empirical psychometric assertion is proved here.
*)
Theorem triple_AB_given_C_negative_iff_reverse :
  forall m : TripleCovariance, 0 < (covariance_var_C m) -> ((tri_determinant(undefined)(covariance_var_A m)(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)(undefined)(covariance_BC m)) < 0 <-> ((tri_left(undefined)(covariance_var_A m)(undefined)(covariance_var_C m)(undefined)(covariance_AC m)) * (tri_right(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_BC m))) < ((tri_cross(undefined)(covariance_AB m)(undefined)(covariance_var_C m)(undefined)(covariance_AC m)(undefined)(covariance_BC m)) * (tri_cross(undefined)(covariance_AB m)(undefined)(covariance_var_C m)(undefined)(covariance_AC m)(undefined)(covariance_BC m)))).
Proof.
  intro m.
  exact (trivariate_negative_iff_reverse
    (covariance_var_A m) (covariance_var_B m) (covariance_var_C m) (covariance_AB m) (covariance_AC m) (covariance_BC m)).
Qed.

(**
 [triple_AB_given_C_nonnegative_iff_weak] (theorem) — Nonnegative determinant is equivalent to the weak Schur Cauchy-Schwarz inequality. This is the AB conditioned on C instantiation using the named test covariance coordinates.
 Mathematical meaning: Nonnegative determinant is equivalent to the weak Schur Cauchy-Schwarz inequality. This is the AB conditioned on C instantiation using the named test covariance coordinates. The result is used to audit conditional covariance or precision in a three-test score model.
 Exact checked proposition: forall m : TripleCovariance, 0 < (covariance_var_C m) -> (0 <= (tri_determinant(undefined)(covariance_var_A m)(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)(undefined)(covariance_BC m)) <-> ((tri_cross(undefined)(covariance_AB m)(undefined)(covariance_var_C m)(undefined)(covariance_AC m)(undefined)(covariance_BC m)) * (tri_cross(undefined)(covariance_AB m)(undefined)(covariance_var_C m)(undefined)(covariance_AC m)(undefined)(covariance_BC m))) <= ((tri_left(undefined)(covariance_var_A m)(undefined)(covariance_var_C m)(undefined)(covariance_AC m)) * (tri_right(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_BC m)))).
 Premises and side conditions: All scalar quantities are real. Strict conditioning variance and any determinant, residual or nonzero assumptions are explicit in the statement; no positive semidefinite matrix is silently assumed.
 Proof/definition method: Deduction from the exact trivariate Schur factorization using canonical real polynomial normalization, inequalities and elementary real algebra.
 Library reuse: Rocq standard Reals, Lra, Psatz and Ring, rather than a custom algebra solver or a duplicate probability-sum implementation.
 Boundary: Exact 3x3 covariance-candidate algebra; no continuous Gaussian conditional law, normal tail or empirical psychometric assertion is proved here.
*)
Theorem triple_AB_given_C_nonnegative_iff_weak :
  forall m : TripleCovariance, 0 < (covariance_var_C m) -> (0 <= (tri_determinant(undefined)(covariance_var_A m)(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)(undefined)(covariance_BC m)) <-> ((tri_cross(undefined)(covariance_AB m)(undefined)(covariance_var_C m)(undefined)(covariance_AC m)(undefined)(covariance_BC m)) * (tri_cross(undefined)(covariance_AB m)(undefined)(covariance_var_C m)(undefined)(covariance_AC m)(undefined)(covariance_BC m))) <= ((tri_left(undefined)(covariance_var_A m)(undefined)(covariance_var_C m)(undefined)(covariance_AC m)) * (tri_right(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_BC m)))).
Proof.
  intro m.
  exact (trivariate_nonnegative_iff_weak
    (covariance_var_A m) (covariance_var_B m) (covariance_var_C m) (covariance_AB m) (covariance_AC m) (covariance_BC m)).
Qed.

(**
 [triple_AB_given_C_nonpositive_iff_reverse_weak] (theorem) — Nonpositive determinant is equivalent to the reverse weak residual inequality. This is the AB conditioned on C instantiation using the named test covariance coordinates.
 Mathematical meaning: Nonpositive determinant is equivalent to the reverse weak residual inequality. This is the AB conditioned on C instantiation using the named test covariance coordinates. The result is used to audit conditional covariance or precision in a three-test score model.
 Exact checked proposition: forall m : TripleCovariance, 0 < (covariance_var_C m) -> ((tri_determinant(undefined)(covariance_var_A m)(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)(undefined)(covariance_BC m)) <= 0 <-> ((tri_left(undefined)(covariance_var_A m)(undefined)(covariance_var_C m)(undefined)(covariance_AC m)) * (tri_right(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_BC m))) <= ((tri_cross(undefined)(covariance_AB m)(undefined)(covariance_var_C m)(undefined)(covariance_AC m)(undefined)(covariance_BC m)) * (tri_cross(undefined)(covariance_AB m)(undefined)(covariance_var_C m)(undefined)(covariance_AC m)(undefined)(covariance_BC m)))).
 Premises and side conditions: All scalar quantities are real. Strict conditioning variance and any determinant, residual or nonzero assumptions are explicit in the statement; no positive semidefinite matrix is silently assumed.
 Proof/definition method: Deduction from the exact trivariate Schur factorization using canonical real polynomial normalization, inequalities and elementary real algebra.
 Library reuse: Rocq standard Reals, Lra, Psatz and Ring, rather than a custom algebra solver or a duplicate probability-sum implementation.
 Boundary: Exact 3x3 covariance-candidate algebra; no continuous Gaussian conditional law, normal tail or empirical psychometric assertion is proved here.
*)
Theorem triple_AB_given_C_nonpositive_iff_reverse_weak :
  forall m : TripleCovariance, 0 < (covariance_var_C m) -> ((tri_determinant(undefined)(covariance_var_A m)(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)(undefined)(covariance_BC m)) <= 0 <-> ((tri_left(undefined)(covariance_var_A m)(undefined)(covariance_var_C m)(undefined)(covariance_AC m)) * (tri_right(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_BC m))) <= ((tri_cross(undefined)(covariance_AB m)(undefined)(covariance_var_C m)(undefined)(covariance_AC m)(undefined)(covariance_BC m)) * (tri_cross(undefined)(covariance_AB m)(undefined)(covariance_var_C m)(undefined)(covariance_AC m)(undefined)(covariance_BC m)))).
Proof.
  intro m.
  exact (trivariate_nonpositive_iff_reverse_weak
    (covariance_var_A m) (covariance_var_B m) (covariance_var_C m) (covariance_AB m) (covariance_AC m) (covariance_BC m)).
Qed.

(**
 [triple_AB_given_C_strict_positive_bound] (theorem) — A positive determinant forces a strict conditional Cauchy-Schwarz bound. This is the AB conditioned on C instantiation using the named test covariance coordinates.
 Mathematical meaning: A positive determinant forces a strict conditional Cauchy-Schwarz bound. This is the AB conditioned on C instantiation using the named test covariance coordinates. The result is used to audit conditional covariance or precision in a three-test score model.
 Exact checked proposition: forall m : TripleCovariance, 0 < (covariance_var_C m) -> 0 < (tri_determinant(undefined)(covariance_var_A m)(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)(undefined)(covariance_BC m)) -> ((tri_cross(undefined)(covariance_AB m)(undefined)(covariance_var_C m)(undefined)(covariance_AC m)(undefined)(covariance_BC m)) * (tri_cross(undefined)(covariance_AB m)(undefined)(covariance_var_C m)(undefined)(covariance_AC m)(undefined)(covariance_BC m))) < ((tri_left(undefined)(covariance_var_A m)(undefined)(covariance_var_C m)(undefined)(covariance_AC m)) * (tri_right(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_BC m))).
 Premises and side conditions: All scalar quantities are real. Strict conditioning variance and any determinant, residual or nonzero assumptions are explicit in the statement; no positive semidefinite matrix is silently assumed.
 Proof/definition method: Deduction from the exact trivariate Schur factorization using canonical real polynomial normalization, inequalities and elementary real algebra.
 Library reuse: Rocq standard Reals, Lra, Psatz and Ring, rather than a custom algebra solver or a duplicate probability-sum implementation.
 Boundary: Exact 3x3 covariance-candidate algebra; no continuous Gaussian conditional law, normal tail or empirical psychometric assertion is proved here.
*)
Theorem triple_AB_given_C_strict_positive_bound :
  forall m : TripleCovariance, 0 < (covariance_var_C m) -> 0 < (tri_determinant(undefined)(covariance_var_A m)(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)(undefined)(covariance_BC m)) -> ((tri_cross(undefined)(covariance_AB m)(undefined)(covariance_var_C m)(undefined)(covariance_AC m)(undefined)(covariance_BC m)) * (tri_cross(undefined)(covariance_AB m)(undefined)(covariance_var_C m)(undefined)(covariance_AC m)(undefined)(covariance_BC m))) < ((tri_left(undefined)(covariance_var_A m)(undefined)(covariance_var_C m)(undefined)(covariance_AC m)) * (tri_right(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_BC m))).
Proof.
  intro m.
  exact (trivariate_strict_positive_bound
    (covariance_var_A m) (covariance_var_B m) (covariance_var_C m) (covariance_AB m) (covariance_AC m) (covariance_BC m)).
Qed.

(**
 [triple_AB_given_C_strict_negative_bound] (theorem) — A negative determinant forces a strict reverse conditional Cauchy-Schwarz bound. This is the AB conditioned on C instantiation using the named test covariance coordinates.
 Mathematical meaning: A negative determinant forces a strict reverse conditional Cauchy-Schwarz bound. This is the AB conditioned on C instantiation using the named test covariance coordinates. The result is used to audit conditional covariance or precision in a three-test score model.
 Exact checked proposition: forall m : TripleCovariance, 0 < (covariance_var_C m) -> (tri_determinant(undefined)(covariance_var_A m)(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)(undefined)(covariance_BC m)) < 0 -> ((tri_left(undefined)(covariance_var_A m)(undefined)(covariance_var_C m)(undefined)(covariance_AC m)) * (tri_right(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_BC m))) < ((tri_cross(undefined)(covariance_AB m)(undefined)(covariance_var_C m)(undefined)(covariance_AC m)(undefined)(covariance_BC m)) * (tri_cross(undefined)(covariance_AB m)(undefined)(covariance_var_C m)(undefined)(covariance_AC m)(undefined)(covariance_BC m))).
 Premises and side conditions: All scalar quantities are real. Strict conditioning variance and any determinant, residual or nonzero assumptions are explicit in the statement; no positive semidefinite matrix is silently assumed.
 Proof/definition method: Deduction from the exact trivariate Schur factorization using canonical real polynomial normalization, inequalities and elementary real algebra.
 Library reuse: Rocq standard Reals, Lra, Psatz and Ring, rather than a custom algebra solver or a duplicate probability-sum implementation.
 Boundary: Exact 3x3 covariance-candidate algebra; no continuous Gaussian conditional law, normal tail or empirical psychometric assertion is proved here.
*)
Theorem triple_AB_given_C_strict_negative_bound :
  forall m : TripleCovariance, 0 < (covariance_var_C m) -> (tri_determinant(undefined)(covariance_var_A m)(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)(undefined)(covariance_BC m)) < 0 -> ((tri_left(undefined)(covariance_var_A m)(undefined)(covariance_var_C m)(undefined)(covariance_AC m)) * (tri_right(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_BC m))) < ((tri_cross(undefined)(covariance_AB m)(undefined)(covariance_var_C m)(undefined)(covariance_AC m)(undefined)(covariance_BC m)) * (tri_cross(undefined)(covariance_AB m)(undefined)(covariance_var_C m)(undefined)(covariance_AC m)(undefined)(covariance_BC m))).
Proof.
  intro m.
  exact (trivariate_strict_negative_bound
    (covariance_var_A m) (covariance_var_B m) (covariance_var_C m) (covariance_AB m) (covariance_AC m) (covariance_BC m)).
Qed.

(**
 [triple_AB_given_C_weak_positive_bound] (theorem) — A nonnegative determinant bounds squared conditional covariance by the residual product. This is the AB conditioned on C instantiation using the named test covariance coordinates.
 Mathematical meaning: A nonnegative determinant bounds squared conditional covariance by the residual product. This is the AB conditioned on C instantiation using the named test covariance coordinates. The result is used to audit conditional covariance or precision in a three-test score model.
 Exact checked proposition: forall m : TripleCovariance, 0 < (covariance_var_C m) -> 0 <= (tri_determinant(undefined)(covariance_var_A m)(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)(undefined)(covariance_BC m)) -> ((tri_cross(undefined)(covariance_AB m)(undefined)(covariance_var_C m)(undefined)(covariance_AC m)(undefined)(covariance_BC m)) * (tri_cross(undefined)(covariance_AB m)(undefined)(covariance_var_C m)(undefined)(covariance_AC m)(undefined)(covariance_BC m))) <= ((tri_left(undefined)(covariance_var_A m)(undefined)(covariance_var_C m)(undefined)(covariance_AC m)) * (tri_right(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_BC m))).
 Premises and side conditions: All scalar quantities are real. Strict conditioning variance and any determinant, residual or nonzero assumptions are explicit in the statement; no positive semidefinite matrix is silently assumed.
 Proof/definition method: Deduction from the exact trivariate Schur factorization using canonical real polynomial normalization, inequalities and elementary real algebra.
 Library reuse: Rocq standard Reals, Lra, Psatz and Ring, rather than a custom algebra solver or a duplicate probability-sum implementation.
 Boundary: Exact 3x3 covariance-candidate algebra; no continuous Gaussian conditional law, normal tail or empirical psychometric assertion is proved here.
*)
Theorem triple_AB_given_C_weak_positive_bound :
  forall m : TripleCovariance, 0 < (covariance_var_C m) -> 0 <= (tri_determinant(undefined)(covariance_var_A m)(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)(undefined)(covariance_BC m)) -> ((tri_cross(undefined)(covariance_AB m)(undefined)(covariance_var_C m)(undefined)(covariance_AC m)(undefined)(covariance_BC m)) * (tri_cross(undefined)(covariance_AB m)(undefined)(covariance_var_C m)(undefined)(covariance_AC m)(undefined)(covariance_BC m))) <= ((tri_left(undefined)(covariance_var_A m)(undefined)(covariance_var_C m)(undefined)(covariance_AC m)) * (tri_right(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_BC m))).
Proof.
  intro m.
  exact (trivariate_weak_positive_bound
    (covariance_var_A m) (covariance_var_B m) (covariance_var_C m) (covariance_AB m) (covariance_AC m) (covariance_BC m)).
Qed.

(**
 [triple_AB_given_C_weak_negative_bound] (theorem) — A nonpositive determinant bounds the residual product by squared conditional covariance. This is the AB conditioned on C instantiation using the named test covariance coordinates.
 Mathematical meaning: A nonpositive determinant bounds the residual product by squared conditional covariance. This is the AB conditioned on C instantiation using the named test covariance coordinates. The result is used to audit conditional covariance or precision in a three-test score model.
 Exact checked proposition: forall m : TripleCovariance, 0 < (covariance_var_C m) -> (tri_determinant(undefined)(covariance_var_A m)(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)(undefined)(covariance_BC m)) <= 0 -> ((tri_left(undefined)(covariance_var_A m)(undefined)(covariance_var_C m)(undefined)(covariance_AC m)) * (tri_right(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_BC m))) <= ((tri_cross(undefined)(covariance_AB m)(undefined)(covariance_var_C m)(undefined)(covariance_AC m)(undefined)(covariance_BC m)) * (tri_cross(undefined)(covariance_AB m)(undefined)(covariance_var_C m)(undefined)(covariance_AC m)(undefined)(covariance_BC m))).
 Premises and side conditions: All scalar quantities are real. Strict conditioning variance and any determinant, residual or nonzero assumptions are explicit in the statement; no positive semidefinite matrix is silently assumed.
 Proof/definition method: Deduction from the exact trivariate Schur factorization using canonical real polynomial normalization, inequalities and elementary real algebra.
 Library reuse: Rocq standard Reals, Lra, Psatz and Ring, rather than a custom algebra solver or a duplicate probability-sum implementation.
 Boundary: Exact 3x3 covariance-candidate algebra; no continuous Gaussian conditional law, normal tail or empirical psychometric assertion is proved here.
*)
Theorem triple_AB_given_C_weak_negative_bound :
  forall m : TripleCovariance, 0 < (covariance_var_C m) -> (tri_determinant(undefined)(covariance_var_A m)(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)(undefined)(covariance_BC m)) <= 0 -> ((tri_left(undefined)(covariance_var_A m)(undefined)(covariance_var_C m)(undefined)(covariance_AC m)) * (tri_right(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_BC m))) <= ((tri_cross(undefined)(covariance_AB m)(undefined)(covariance_var_C m)(undefined)(covariance_AC m)(undefined)(covariance_BC m)) * (tri_cross(undefined)(covariance_AB m)(undefined)(covariance_var_C m)(undefined)(covariance_AC m)(undefined)(covariance_BC m))).
Proof.
  intro m.
  exact (trivariate_weak_negative_bound
    (covariance_var_A m) (covariance_var_B m) (covariance_var_C m) (covariance_AB m) (covariance_AC m) (covariance_BC m)).
Qed.

(**
 [triple_AB_given_C_zero_cross_factor] (theorem) — Conditional uncorrelatedness makes the residual product exactly the conditioning variance times the determinant. This is the AB conditioned on C instantiation using the named test covariance coordinates.
 Mathematical meaning: Conditional uncorrelatedness makes the residual product exactly the conditioning variance times the determinant. This is the AB conditioned on C instantiation using the named test covariance coordinates. The result is used to audit conditional covariance or precision in a three-test score model.
 Exact checked proposition: forall m : TripleCovariance, (tri_cross(undefined)(covariance_AB m)(undefined)(covariance_var_C m)(undefined)(covariance_AC m)(undefined)(covariance_BC m)) = 0 -> ((tri_left(undefined)(covariance_var_A m)(undefined)(covariance_var_C m)(undefined)(covariance_AC m)) * (tri_right(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_BC m))) = (covariance_var_C m) * (tri_determinant(undefined)(covariance_var_A m)(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)(undefined)(covariance_BC m)).
 Premises and side conditions: All scalar quantities are real. Strict conditioning variance and any determinant, residual or nonzero assumptions are explicit in the statement; no positive semidefinite matrix is silently assumed.
 Proof/definition method: Deduction from the exact trivariate Schur factorization using canonical real polynomial normalization, inequalities and elementary real algebra.
 Library reuse: Rocq standard Reals, Lra, Psatz and Ring, rather than a custom algebra solver or a duplicate probability-sum implementation.
 Boundary: Exact 3x3 covariance-candidate algebra; no continuous Gaussian conditional law, normal tail or empirical psychometric assertion is proved here.
*)
Theorem triple_AB_given_C_zero_cross_factor :
  forall m : TripleCovariance, (tri_cross(undefined)(covariance_AB m)(undefined)(covariance_var_C m)(undefined)(covariance_AC m)(undefined)(covariance_BC m)) = 0 -> ((tri_left(undefined)(covariance_var_A m)(undefined)(covariance_var_C m)(undefined)(covariance_AC m)) * (tri_right(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_BC m))) = (covariance_var_C m) * (tri_determinant(undefined)(covariance_var_A m)(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)(undefined)(covariance_BC m)).
Proof.
  intro m.
  exact (trivariate_zero_cross_factor
    (covariance_var_A m) (covariance_var_B m) (covariance_var_C m) (covariance_AB m) (covariance_AC m) (covariance_BC m)).
Qed.

(**
 [triple_AB_given_C_zero_cross_positive_product] (theorem) — Conditional uncorrelatedness and positive determinant imply a strictly positive residual product. This is the AB conditioned on C instantiation using the named test covariance coordinates.
 Mathematical meaning: Conditional uncorrelatedness and positive determinant imply a strictly positive residual product. This is the AB conditioned on C instantiation using the named test covariance coordinates. The result is used to audit conditional covariance or precision in a three-test score model.
 Exact checked proposition: forall m : TripleCovariance, 0 < (covariance_var_C m) -> (tri_cross(undefined)(covariance_AB m)(undefined)(covariance_var_C m)(undefined)(covariance_AC m)(undefined)(covariance_BC m)) = 0 -> 0 < (tri_determinant(undefined)(covariance_var_A m)(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)(undefined)(covariance_BC m)) -> 0 < ((tri_left(undefined)(covariance_var_A m)(undefined)(covariance_var_C m)(undefined)(covariance_AC m)) * (tri_right(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_BC m))).
 Premises and side conditions: All scalar quantities are real. Strict conditioning variance and any determinant, residual or nonzero assumptions are explicit in the statement; no positive semidefinite matrix is silently assumed.
 Proof/definition method: Deduction from the exact trivariate Schur factorization using canonical real polynomial normalization, inequalities and elementary real algebra.
 Library reuse: Rocq standard Reals, Lra, Psatz and Ring, rather than a custom algebra solver or a duplicate probability-sum implementation.
 Boundary: Exact 3x3 covariance-candidate algebra; no continuous Gaussian conditional law, normal tail or empirical psychometric assertion is proved here.
*)
Theorem triple_AB_given_C_zero_cross_positive_product :
  forall m : TripleCovariance, 0 < (covariance_var_C m) -> (tri_cross(undefined)(covariance_AB m)(undefined)(covariance_var_C m)(undefined)(covariance_AC m)(undefined)(covariance_BC m)) = 0 -> 0 < (tri_determinant(undefined)(covariance_var_A m)(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)(undefined)(covariance_BC m)) -> 0 < ((tri_left(undefined)(covariance_var_A m)(undefined)(covariance_var_C m)(undefined)(covariance_AC m)) * (tri_right(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_BC m))).
Proof.
  intro m.
  exact (trivariate_zero_cross_positive_product
    (covariance_var_A m) (covariance_var_B m) (covariance_var_C m) (covariance_AB m) (covariance_AC m) (covariance_BC m)).
Qed.

(**
 [triple_AB_given_C_zero_cross_singular_product] (theorem) — Conditional uncorrelatedness with singular determinant forces at least one residual factor to vanish. This is the AB conditioned on C instantiation using the named test covariance coordinates.
 Mathematical meaning: Conditional uncorrelatedness with singular determinant forces at least one residual factor to vanish. This is the AB conditioned on C instantiation using the named test covariance coordinates. The result is used to audit conditional covariance or precision in a three-test score model.
 Exact checked proposition: forall m : TripleCovariance, (tri_cross(undefined)(covariance_AB m)(undefined)(covariance_var_C m)(undefined)(covariance_AC m)(undefined)(covariance_BC m)) = 0 -> (tri_determinant(undefined)(covariance_var_A m)(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)(undefined)(covariance_BC m)) = 0 -> ((tri_left(undefined)(covariance_var_A m)(undefined)(covariance_var_C m)(undefined)(covariance_AC m)) * (tri_right(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_BC m))) = 0.
 Premises and side conditions: All scalar quantities are real. Strict conditioning variance and any determinant, residual or nonzero assumptions are explicit in the statement; no positive semidefinite matrix is silently assumed.
 Proof/definition method: Deduction from the exact trivariate Schur factorization using canonical real polynomial normalization, inequalities and elementary real algebra.
 Library reuse: Rocq standard Reals, Lra, Psatz and Ring, rather than a custom algebra solver or a duplicate probability-sum implementation.
 Boundary: Exact 3x3 covariance-candidate algebra; no continuous Gaussian conditional law, normal tail or empirical psychometric assertion is proved here.
*)
Theorem triple_AB_given_C_zero_cross_singular_product :
  forall m : TripleCovariance, (tri_cross(undefined)(covariance_AB m)(undefined)(covariance_var_C m)(undefined)(covariance_AC m)(undefined)(covariance_BC m)) = 0 -> (tri_determinant(undefined)(covariance_var_A m)(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)(undefined)(covariance_BC m)) = 0 -> ((tri_left(undefined)(covariance_var_A m)(undefined)(covariance_var_C m)(undefined)(covariance_AC m)) * (tri_right(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_BC m))) = 0.
Proof.
  intro m.
  exact (trivariate_zero_cross_singular_product
    (covariance_var_A m) (covariance_var_B m) (covariance_var_C m) (covariance_AB m) (covariance_AC m) (covariance_BC m)).
Qed.

(**
 [triple_AB_given_C_zero_left_determinant] (theorem) — Vanishing first residual gives an exact negative-square identity. This is the AB conditioned on C instantiation using the named test covariance coordinates.
 Mathematical meaning: Vanishing first residual gives an exact negative-square identity. This is the AB conditioned on C instantiation using the named test covariance coordinates. The result is used to audit conditional covariance or precision in a three-test score model.
 Exact checked proposition: forall m : TripleCovariance, (tri_left(undefined)(covariance_var_A m)(undefined)(covariance_var_C m)(undefined)(covariance_AC m)) = 0 -> (covariance_var_C m) * (tri_determinant(undefined)(covariance_var_A m)(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)(undefined)(covariance_BC m)) = - ((tri_cross(undefined)(covariance_AB m)(undefined)(covariance_var_C m)(undefined)(covariance_AC m)(undefined)(covariance_BC m)) * (tri_cross(undefined)(covariance_AB m)(undefined)(covariance_var_C m)(undefined)(covariance_AC m)(undefined)(covariance_BC m))).
 Premises and side conditions: All scalar quantities are real. Strict conditioning variance and any determinant, residual or nonzero assumptions are explicit in the statement; no positive semidefinite matrix is silently assumed.
 Proof/definition method: Deduction from the exact trivariate Schur factorization using canonical real polynomial normalization, inequalities and elementary real algebra.
 Library reuse: Rocq standard Reals, Lra, Psatz and Ring, rather than a custom algebra solver or a duplicate probability-sum implementation.
 Boundary: Exact 3x3 covariance-candidate algebra; no continuous Gaussian conditional law, normal tail or empirical psychometric assertion is proved here.
*)
Theorem triple_AB_given_C_zero_left_determinant :
  forall m : TripleCovariance, (tri_left(undefined)(covariance_var_A m)(undefined)(covariance_var_C m)(undefined)(covariance_AC m)) = 0 -> (covariance_var_C m) * (tri_determinant(undefined)(covariance_var_A m)(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)(undefined)(covariance_BC m)) = - ((tri_cross(undefined)(covariance_AB m)(undefined)(covariance_var_C m)(undefined)(covariance_AC m)(undefined)(covariance_BC m)) * (tri_cross(undefined)(covariance_AB m)(undefined)(covariance_var_C m)(undefined)(covariance_AC m)(undefined)(covariance_BC m))).
Proof.
  intro m.
  exact (trivariate_zero_left_determinant
    (covariance_var_A m) (covariance_var_B m) (covariance_var_C m) (covariance_AB m) (covariance_AC m) (covariance_BC m)).
Qed.

(**
 [triple_AB_given_C_zero_right_determinant] (theorem) — Vanishing second residual gives an exact negative-square identity. This is the AB conditioned on C instantiation using the named test covariance coordinates.
 Mathematical meaning: Vanishing second residual gives an exact negative-square identity. This is the AB conditioned on C instantiation using the named test covariance coordinates. The result is used to audit conditional covariance or precision in a three-test score model.
 Exact checked proposition: forall m : TripleCovariance, (tri_right(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_BC m)) = 0 -> (covariance_var_C m) * (tri_determinant(undefined)(covariance_var_A m)(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)(undefined)(covariance_BC m)) = - ((tri_cross(undefined)(covariance_AB m)(undefined)(covariance_var_C m)(undefined)(covariance_AC m)(undefined)(covariance_BC m)) * (tri_cross(undefined)(covariance_AB m)(undefined)(covariance_var_C m)(undefined)(covariance_AC m)(undefined)(covariance_BC m))).
 Premises and side conditions: All scalar quantities are real. Strict conditioning variance and any determinant, residual or nonzero assumptions are explicit in the statement; no positive semidefinite matrix is silently assumed.
 Proof/definition method: Deduction from the exact trivariate Schur factorization using canonical real polynomial normalization, inequalities and elementary real algebra.
 Library reuse: Rocq standard Reals, Lra, Psatz and Ring, rather than a custom algebra solver or a duplicate probability-sum implementation.
 Boundary: Exact 3x3 covariance-candidate algebra; no continuous Gaussian conditional law, normal tail or empirical psychometric assertion is proved here.
*)
Theorem triple_AB_given_C_zero_right_determinant :
  forall m : TripleCovariance, (tri_right(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_BC m)) = 0 -> (covariance_var_C m) * (tri_determinant(undefined)(covariance_var_A m)(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)(undefined)(covariance_BC m)) = - ((tri_cross(undefined)(covariance_AB m)(undefined)(covariance_var_C m)(undefined)(covariance_AC m)(undefined)(covariance_BC m)) * (tri_cross(undefined)(covariance_AB m)(undefined)(covariance_var_C m)(undefined)(covariance_AC m)(undefined)(covariance_BC m))).
Proof.
  intro m.
  exact (trivariate_zero_right_determinant
    (covariance_var_A m) (covariance_var_B m) (covariance_var_C m) (covariance_AB m) (covariance_AC m) (covariance_BC m)).
Qed.

(**
 [triple_AB_given_C_zero_left_cross_nonzero_negative] (theorem) — A zero first residual with nonzero conditional cross-covariance forces negative determinant. This is the AB conditioned on C instantiation using the named test covariance coordinates.
 Mathematical meaning: A zero first residual with nonzero conditional cross-covariance forces negative determinant. This is the AB conditioned on C instantiation using the named test covariance coordinates. The result is used to audit conditional covariance or precision in a three-test score model.
 Exact checked proposition: forall m : TripleCovariance, 0 < (covariance_var_C m) -> (tri_left(undefined)(covariance_var_A m)(undefined)(covariance_var_C m)(undefined)(covariance_AC m)) = 0 -> (tri_cross(undefined)(covariance_AB m)(undefined)(covariance_var_C m)(undefined)(covariance_AC m)(undefined)(covariance_BC m)) <> 0 -> (tri_determinant(undefined)(covariance_var_A m)(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)(undefined)(covariance_BC m)) < 0.
 Premises and side conditions: All scalar quantities are real. Strict conditioning variance and any determinant, residual or nonzero assumptions are explicit in the statement; no positive semidefinite matrix is silently assumed.
 Proof/definition method: Deduction from the exact trivariate Schur factorization using canonical real polynomial normalization, inequalities and elementary real algebra.
 Library reuse: Rocq standard Reals, Lra, Psatz and Ring, rather than a custom algebra solver or a duplicate probability-sum implementation.
 Boundary: Exact 3x3 covariance-candidate algebra; no continuous Gaussian conditional law, normal tail or empirical psychometric assertion is proved here.
*)
Theorem triple_AB_given_C_zero_left_cross_nonzero_negative :
  forall m : TripleCovariance, 0 < (covariance_var_C m) -> (tri_left(undefined)(covariance_var_A m)(undefined)(covariance_var_C m)(undefined)(covariance_AC m)) = 0 -> (tri_cross(undefined)(covariance_AB m)(undefined)(covariance_var_C m)(undefined)(covariance_AC m)(undefined)(covariance_BC m)) <> 0 -> (tri_determinant(undefined)(covariance_var_A m)(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)(undefined)(covariance_BC m)) < 0.
Proof.
  intro m.
  exact (trivariate_zero_left_cross_nonzero_negative
    (covariance_var_A m) (covariance_var_B m) (covariance_var_C m) (covariance_AB m) (covariance_AC m) (covariance_BC m)).
Qed.

(**
 [triple_AB_given_C_zero_right_cross_nonzero_negative] (theorem) — A zero second residual with nonzero conditional cross-covariance forces negative determinant. This is the AB conditioned on C instantiation using the named test covariance coordinates.
 Mathematical meaning: A zero second residual with nonzero conditional cross-covariance forces negative determinant. This is the AB conditioned on C instantiation using the named test covariance coordinates. The result is used to audit conditional covariance or precision in a three-test score model.
 Exact checked proposition: forall m : TripleCovariance, 0 < (covariance_var_C m) -> (tri_right(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_BC m)) = 0 -> (tri_cross(undefined)(covariance_AB m)(undefined)(covariance_var_C m)(undefined)(covariance_AC m)(undefined)(covariance_BC m)) <> 0 -> (tri_determinant(undefined)(covariance_var_A m)(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)(undefined)(covariance_BC m)) < 0.
 Premises and side conditions: All scalar quantities are real. Strict conditioning variance and any determinant, residual or nonzero assumptions are explicit in the statement; no positive semidefinite matrix is silently assumed.
 Proof/definition method: Deduction from the exact trivariate Schur factorization using canonical real polynomial normalization, inequalities and elementary real algebra.
 Library reuse: Rocq standard Reals, Lra, Psatz and Ring, rather than a custom algebra solver or a duplicate probability-sum implementation.
 Boundary: Exact 3x3 covariance-candidate algebra; no continuous Gaussian conditional law, normal tail or empirical psychometric assertion is proved here.
*)
Theorem triple_AB_given_C_zero_right_cross_nonzero_negative :
  forall m : TripleCovariance, 0 < (covariance_var_C m) -> (tri_right(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_BC m)) = 0 -> (tri_cross(undefined)(covariance_AB m)(undefined)(covariance_var_C m)(undefined)(covariance_AC m)(undefined)(covariance_BC m)) <> 0 -> (tri_determinant(undefined)(covariance_var_A m)(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)(undefined)(covariance_BC m)) < 0.
Proof.
  intro m.
  exact (trivariate_zero_right_cross_nonzero_negative
    (covariance_var_A m) (covariance_var_B m) (covariance_var_C m) (covariance_AB m) (covariance_AC m) (covariance_BC m)).
Qed.

(**
 [triple_AB_given_C_zero_left_psd_forces_zero_cross] (theorem) — Under a nonnegative determinant, zero first residual forces conditional uncorrelatedness. This is the AB conditioned on C instantiation using the named test covariance coordinates.
 Mathematical meaning: Under a nonnegative determinant, zero first residual forces conditional uncorrelatedness. This is the AB conditioned on C instantiation using the named test covariance coordinates. The result is used to audit conditional covariance or precision in a three-test score model.
 Exact checked proposition: forall m : TripleCovariance, 0 < (covariance_var_C m) -> 0 <= (tri_determinant(undefined)(covariance_var_A m)(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)(undefined)(covariance_BC m)) -> (tri_left(undefined)(covariance_var_A m)(undefined)(covariance_var_C m)(undefined)(covariance_AC m)) = 0 -> (tri_cross(undefined)(covariance_AB m)(undefined)(covariance_var_C m)(undefined)(covariance_AC m)(undefined)(covariance_BC m)) = 0.
 Premises and side conditions: All scalar quantities are real. Strict conditioning variance and any determinant, residual or nonzero assumptions are explicit in the statement; no positive semidefinite matrix is silently assumed.
 Proof/definition method: Deduction from the exact trivariate Schur factorization using canonical real polynomial normalization, inequalities and elementary real algebra.
 Library reuse: Rocq standard Reals, Lra, Psatz and Ring, rather than a custom algebra solver or a duplicate probability-sum implementation.
 Boundary: Exact 3x3 covariance-candidate algebra; no continuous Gaussian conditional law, normal tail or empirical psychometric assertion is proved here.
*)
Theorem triple_AB_given_C_zero_left_psd_forces_zero_cross :
  forall m : TripleCovariance, 0 < (covariance_var_C m) -> 0 <= (tri_determinant(undefined)(covariance_var_A m)(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)(undefined)(covariance_BC m)) -> (tri_left(undefined)(covariance_var_A m)(undefined)(covariance_var_C m)(undefined)(covariance_AC m)) = 0 -> (tri_cross(undefined)(covariance_AB m)(undefined)(covariance_var_C m)(undefined)(covariance_AC m)(undefined)(covariance_BC m)) = 0.
Proof.
  intro m.
  exact (trivariate_zero_left_psd_forces_zero_cross
    (covariance_var_A m) (covariance_var_B m) (covariance_var_C m) (covariance_AB m) (covariance_AC m) (covariance_BC m)).
Qed.

(**
 [triple_AB_given_C_zero_right_psd_forces_zero_cross] (theorem) — Under a nonnegative determinant, zero second residual forces conditional uncorrelatedness. This is the AB conditioned on C instantiation using the named test covariance coordinates.
 Mathematical meaning: Under a nonnegative determinant, zero second residual forces conditional uncorrelatedness. This is the AB conditioned on C instantiation using the named test covariance coordinates. The result is used to audit conditional covariance or precision in a three-test score model.
 Exact checked proposition: forall m : TripleCovariance, 0 < (covariance_var_C m) -> 0 <= (tri_determinant(undefined)(covariance_var_A m)(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)(undefined)(covariance_BC m)) -> (tri_right(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_BC m)) = 0 -> (tri_cross(undefined)(covariance_AB m)(undefined)(covariance_var_C m)(undefined)(covariance_AC m)(undefined)(covariance_BC m)) = 0.
 Premises and side conditions: All scalar quantities are real. Strict conditioning variance and any determinant, residual or nonzero assumptions are explicit in the statement; no positive semidefinite matrix is silently assumed.
 Proof/definition method: Deduction from the exact trivariate Schur factorization using canonical real polynomial normalization, inequalities and elementary real algebra.
 Library reuse: Rocq standard Reals, Lra, Psatz and Ring, rather than a custom algebra solver or a duplicate probability-sum implementation.
 Boundary: Exact 3x3 covariance-candidate algebra; no continuous Gaussian conditional law, normal tail or empirical psychometric assertion is proved here.
*)
Theorem triple_AB_given_C_zero_right_psd_forces_zero_cross :
  forall m : TripleCovariance, 0 < (covariance_var_C m) -> 0 <= (tri_determinant(undefined)(covariance_var_A m)(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)(undefined)(covariance_BC m)) -> (tri_right(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_BC m)) = 0 -> (tri_cross(undefined)(covariance_AB m)(undefined)(covariance_var_C m)(undefined)(covariance_AC m)(undefined)(covariance_BC m)) = 0.
Proof.
  intro m.
  exact (trivariate_zero_right_psd_forces_zero_cross
    (covariance_var_A m) (covariance_var_B m) (covariance_var_C m) (covariance_AB m) (covariance_AC m) (covariance_BC m)).
Qed.

(**
 [triple_AB_given_C_positive_det_left_forces_right] (theorem) — Positive determinant and positive first residual force a positive second residual. This is the AB conditioned on C instantiation using the named test covariance coordinates.
 Mathematical meaning: Positive determinant and positive first residual force a positive second residual. This is the AB conditioned on C instantiation using the named test covariance coordinates. The result is used to audit conditional covariance or precision in a three-test score model.
 Exact checked proposition: forall m : TripleCovariance, 0 < (covariance_var_C m) -> 0 < (tri_determinant(undefined)(covariance_var_A m)(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)(undefined)(covariance_BC m)) -> 0 < (tri_left(undefined)(covariance_var_A m)(undefined)(covariance_var_C m)(undefined)(covariance_AC m)) -> 0 < (tri_right(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_BC m)).
 Premises and side conditions: All scalar quantities are real. Strict conditioning variance and any determinant, residual or nonzero assumptions are explicit in the statement; no positive semidefinite matrix is silently assumed.
 Proof/definition method: Deduction from the exact trivariate Schur factorization using canonical real polynomial normalization, inequalities and elementary real algebra.
 Library reuse: Rocq standard Reals, Lra, Psatz and Ring, rather than a custom algebra solver or a duplicate probability-sum implementation.
 Boundary: Exact 3x3 covariance-candidate algebra; no continuous Gaussian conditional law, normal tail or empirical psychometric assertion is proved here.
*)
Theorem triple_AB_given_C_positive_det_left_forces_right :
  forall m : TripleCovariance, 0 < (covariance_var_C m) -> 0 < (tri_determinant(undefined)(covariance_var_A m)(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)(undefined)(covariance_BC m)) -> 0 < (tri_left(undefined)(covariance_var_A m)(undefined)(covariance_var_C m)(undefined)(covariance_AC m)) -> 0 < (tri_right(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_BC m)).
Proof.
  intro m.
  exact (trivariate_positive_det_left_forces_right
    (covariance_var_A m) (covariance_var_B m) (covariance_var_C m) (covariance_AB m) (covariance_AC m) (covariance_BC m)).
Qed.

(**
 [triple_AB_given_C_positive_det_right_forces_left] (theorem) — Positive determinant and positive second residual force a positive first residual. This is the AB conditioned on C instantiation using the named test covariance coordinates.
 Mathematical meaning: Positive determinant and positive second residual force a positive first residual. This is the AB conditioned on C instantiation using the named test covariance coordinates. The result is used to audit conditional covariance or precision in a three-test score model.
 Exact checked proposition: forall m : TripleCovariance, 0 < (covariance_var_C m) -> 0 < (tri_determinant(undefined)(covariance_var_A m)(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)(undefined)(covariance_BC m)) -> 0 < (tri_right(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_BC m)) -> 0 < (tri_left(undefined)(covariance_var_A m)(undefined)(covariance_var_C m)(undefined)(covariance_AC m)).
 Premises and side conditions: All scalar quantities are real. Strict conditioning variance and any determinant, residual or nonzero assumptions are explicit in the statement; no positive semidefinite matrix is silently assumed.
 Proof/definition method: Deduction from the exact trivariate Schur factorization using canonical real polynomial normalization, inequalities and elementary real algebra.
 Library reuse: Rocq standard Reals, Lra, Psatz and Ring, rather than a custom algebra solver or a duplicate probability-sum implementation.
 Boundary: Exact 3x3 covariance-candidate algebra; no continuous Gaussian conditional law, normal tail or empirical psychometric assertion is proved here.
*)
Theorem triple_AB_given_C_positive_det_right_forces_left :
  forall m : TripleCovariance, 0 < (covariance_var_C m) -> 0 < (tri_determinant(undefined)(covariance_var_A m)(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)(undefined)(covariance_BC m)) -> 0 < (tri_right(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_BC m)) -> 0 < (tri_left(undefined)(covariance_var_A m)(undefined)(covariance_var_C m)(undefined)(covariance_AC m)).
Proof.
  intro m.
  exact (trivariate_positive_det_right_forces_left
    (covariance_var_A m) (covariance_var_B m) (covariance_var_C m) (covariance_AB m) (covariance_AC m) (covariance_BC m)).
Qed.

(**
 [triple_AB_given_C_nonnegative_det_left_forces_right] (theorem) — A nonnegative determinant and strict first residual positivity force nonnegative second residual. This is the AB conditioned on C instantiation using the named test covariance coordinates.
 Mathematical meaning: A nonnegative determinant and strict first residual positivity force nonnegative second residual. This is the AB conditioned on C instantiation using the named test covariance coordinates. The result is used to audit conditional covariance or precision in a three-test score model.
 Exact checked proposition: forall m : TripleCovariance, 0 < (covariance_var_C m) -> 0 <= (tri_determinant(undefined)(covariance_var_A m)(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)(undefined)(covariance_BC m)) -> 0 < (tri_left(undefined)(covariance_var_A m)(undefined)(covariance_var_C m)(undefined)(covariance_AC m)) -> 0 <= (tri_right(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_BC m)).
 Premises and side conditions: All scalar quantities are real. Strict conditioning variance and any determinant, residual or nonzero assumptions are explicit in the statement; no positive semidefinite matrix is silently assumed.
 Proof/definition method: Deduction from the exact trivariate Schur factorization using canonical real polynomial normalization, inequalities and elementary real algebra.
 Library reuse: Rocq standard Reals, Lra, Psatz and Ring, rather than a custom algebra solver or a duplicate probability-sum implementation.
 Boundary: Exact 3x3 covariance-candidate algebra; no continuous Gaussian conditional law, normal tail or empirical psychometric assertion is proved here.
*)
Theorem triple_AB_given_C_nonnegative_det_left_forces_right :
  forall m : TripleCovariance, 0 < (covariance_var_C m) -> 0 <= (tri_determinant(undefined)(covariance_var_A m)(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)(undefined)(covariance_BC m)) -> 0 < (tri_left(undefined)(covariance_var_A m)(undefined)(covariance_var_C m)(undefined)(covariance_AC m)) -> 0 <= (tri_right(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_BC m)).
Proof.
  intro m.
  exact (trivariate_nonnegative_det_left_forces_right
    (covariance_var_A m) (covariance_var_B m) (covariance_var_C m) (covariance_AB m) (covariance_AC m) (covariance_BC m)).
Qed.

(**
 [triple_AB_given_C_nonnegative_det_right_forces_left] (theorem) — A nonnegative determinant and strict second residual positivity force nonnegative first residual. This is the AB conditioned on C instantiation using the named test covariance coordinates.
 Mathematical meaning: A nonnegative determinant and strict second residual positivity force nonnegative first residual. This is the AB conditioned on C instantiation using the named test covariance coordinates. The result is used to audit conditional covariance or precision in a three-test score model.
 Exact checked proposition: forall m : TripleCovariance, 0 < (covariance_var_C m) -> 0 <= (tri_determinant(undefined)(covariance_var_A m)(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)(undefined)(covariance_BC m)) -> 0 < (tri_right(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_BC m)) -> 0 <= (tri_left(undefined)(covariance_var_A m)(undefined)(covariance_var_C m)(undefined)(covariance_AC m)).
 Premises and side conditions: All scalar quantities are real. Strict conditioning variance and any determinant, residual or nonzero assumptions are explicit in the statement; no positive semidefinite matrix is silently assumed.
 Proof/definition method: Deduction from the exact trivariate Schur factorization using canonical real polynomial normalization, inequalities and elementary real algebra.
 Library reuse: Rocq standard Reals, Lra, Psatz and Ring, rather than a custom algebra solver or a duplicate probability-sum implementation.
 Boundary: Exact 3x3 covariance-candidate algebra; no continuous Gaussian conditional law, normal tail or empirical psychometric assertion is proved here.
*)
Theorem triple_AB_given_C_nonnegative_det_right_forces_left :
  forall m : TripleCovariance, 0 < (covariance_var_C m) -> 0 <= (tri_determinant(undefined)(covariance_var_A m)(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)(undefined)(covariance_BC m)) -> 0 < (tri_right(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_BC m)) -> 0 <= (tri_left(undefined)(covariance_var_A m)(undefined)(covariance_var_C m)(undefined)(covariance_AC m)).
Proof.
  intro m.
  exact (trivariate_nonnegative_det_right_forces_left
    (covariance_var_A m) (covariance_var_B m) (covariance_var_C m) (covariance_AB m) (covariance_AC m) (covariance_BC m)).
Qed.

(**
 [triple_AB_given_C_positive_det_positive_product] (theorem) — A strictly positive determinant forces both Schur residual factors to have a positive product. This is the AB conditioned on C instantiation using the named test covariance coordinates.
 Mathematical meaning: A strictly positive determinant forces both Schur residual factors to have a positive product. This is the AB conditioned on C instantiation using the named test covariance coordinates. The result is used to audit conditional covariance or precision in a three-test score model.
 Exact checked proposition: forall m : TripleCovariance, 0 < (covariance_var_C m) -> 0 < (tri_determinant(undefined)(covariance_var_A m)(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)(undefined)(covariance_BC m)) -> 0 < ((tri_left(undefined)(covariance_var_A m)(undefined)(covariance_var_C m)(undefined)(covariance_AC m)) * (tri_right(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_BC m))).
 Premises and side conditions: All scalar quantities are real. Strict conditioning variance and any determinant, residual or nonzero assumptions are explicit in the statement; no positive semidefinite matrix is silently assumed.
 Proof/definition method: Deduction from the exact trivariate Schur factorization using canonical real polynomial normalization, inequalities and elementary real algebra.
 Library reuse: Rocq standard Reals, Lra, Psatz and Ring, rather than a custom algebra solver or a duplicate probability-sum implementation.
 Boundary: Exact 3x3 covariance-candidate algebra; no continuous Gaussian conditional law, normal tail or empirical psychometric assertion is proved here.
*)
Theorem triple_AB_given_C_positive_det_positive_product :
  forall m : TripleCovariance, 0 < (covariance_var_C m) -> 0 < (tri_determinant(undefined)(covariance_var_A m)(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)(undefined)(covariance_BC m)) -> 0 < ((tri_left(undefined)(covariance_var_A m)(undefined)(covariance_var_C m)(undefined)(covariance_AC m)) * (tri_right(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_BC m))).
Proof.
  intro m.
  exact (trivariate_positive_det_positive_product
    (covariance_var_A m) (covariance_var_B m) (covariance_var_C m) (covariance_AB m) (covariance_AC m) (covariance_BC m)).
Qed.

(**
 [triple_AB_given_C_nonnegative_det_nonnegative_product] (theorem) — A nonnegative determinant forces the Schur residual product to be nonnegative. This is the AB conditioned on C instantiation using the named test covariance coordinates.
 Mathematical meaning: A nonnegative determinant forces the Schur residual product to be nonnegative. This is the AB conditioned on C instantiation using the named test covariance coordinates. The result is used to audit conditional covariance or precision in a three-test score model.
 Exact checked proposition: forall m : TripleCovariance, 0 < (covariance_var_C m) -> 0 <= (tri_determinant(undefined)(covariance_var_A m)(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)(undefined)(covariance_BC m)) -> 0 <= ((tri_left(undefined)(covariance_var_A m)(undefined)(covariance_var_C m)(undefined)(covariance_AC m)) * (tri_right(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_BC m))).
 Premises and side conditions: All scalar quantities are real. Strict conditioning variance and any determinant, residual or nonzero assumptions are explicit in the statement; no positive semidefinite matrix is silently assumed.
 Proof/definition method: Deduction from the exact trivariate Schur factorization using canonical real polynomial normalization, inequalities and elementary real algebra.
 Library reuse: Rocq standard Reals, Lra, Psatz and Ring, rather than a custom algebra solver or a duplicate probability-sum implementation.
 Boundary: Exact 3x3 covariance-candidate algebra; no continuous Gaussian conditional law, normal tail or empirical psychometric assertion is proved here.
*)
Theorem triple_AB_given_C_nonnegative_det_nonnegative_product :
  forall m : TripleCovariance, 0 < (covariance_var_C m) -> 0 <= (tri_determinant(undefined)(covariance_var_A m)(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)(undefined)(covariance_BC m)) -> 0 <= ((tri_left(undefined)(covariance_var_A m)(undefined)(covariance_var_C m)(undefined)(covariance_AC m)) * (tri_right(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_BC m))).
Proof.
  intro m.
  exact (trivariate_nonnegative_det_nonnegative_product
    (covariance_var_A m) (covariance_var_B m) (covariance_var_C m) (covariance_AB m) (covariance_AC m) (covariance_BC m)).
Qed.

(**
 [triple_AC_given_B_factor] (theorem) — The exact three-variable Schur determinant factorization. This is the AC conditioned on B instantiation using the named test covariance coordinates.
 Mathematical meaning: The exact three-variable Schur determinant factorization. This is the AC conditioned on B instantiation using the named test covariance coordinates. The result is used to audit conditional covariance or precision in a three-test score model.
 Exact checked proposition: forall m : TripleCovariance, ((tri_left(undefined)(covariance_var_A m)(undefined)(covariance_var_B m)(undefined)(covariance_AB m)) * (tri_right(undefined)(covariance_var_C m)(undefined)(covariance_var_B m)(undefined)(covariance_BC m))) - ((tri_cross(undefined)(covariance_AC m)(undefined)(covariance_var_B m)(undefined)(covariance_AB m)(undefined)(covariance_BC m)) * (tri_cross(undefined)(covariance_AC m)(undefined)(covariance_var_B m)(undefined)(covariance_AB m)(undefined)(covariance_BC m))) = (covariance_var_B m) * (tri_determinant(undefined)(covariance_var_A m)(undefined)(covariance_var_C m)(undefined)(covariance_var_B m)(undefined)(covariance_AC m)(undefined)(covariance_AB m)(undefined)(covariance_BC m)).
 Premises and side conditions: All scalar quantities are real. Strict conditioning variance and any determinant, residual or nonzero assumptions are explicit in the statement; no positive semidefinite matrix is silently assumed.
 Proof/definition method: Deduction from the exact trivariate Schur factorization using canonical real polynomial normalization, inequalities and elementary real algebra.
 Library reuse: Rocq standard Reals, Lra, Psatz and Ring, rather than a custom algebra solver or a duplicate probability-sum implementation.
 Boundary: Exact 3x3 covariance-candidate algebra; no continuous Gaussian conditional law, normal tail or empirical psychometric assertion is proved here.
*)
Theorem triple_AC_given_B_factor :
  forall m : TripleCovariance, ((tri_left(undefined)(covariance_var_A m)(undefined)(covariance_var_B m)(undefined)(covariance_AB m)) * (tri_right(undefined)(covariance_var_C m)(undefined)(covariance_var_B m)(undefined)(covariance_BC m))) - ((tri_cross(undefined)(covariance_AC m)(undefined)(covariance_var_B m)(undefined)(covariance_AB m)(undefined)(covariance_BC m)) * (tri_cross(undefined)(covariance_AC m)(undefined)(covariance_var_B m)(undefined)(covariance_AB m)(undefined)(covariance_BC m))) = (covariance_var_B m) * (tri_determinant(undefined)(covariance_var_A m)(undefined)(covariance_var_C m)(undefined)(covariance_var_B m)(undefined)(covariance_AC m)(undefined)(covariance_AB m)(undefined)(covariance_BC m)).
Proof.
  intro m.
  exact (trivariate_factor
    (covariance_var_A m) (covariance_var_C m) (covariance_var_B m) (covariance_AC m) (covariance_AB m) (covariance_BC m)).
Qed.

(**
 [triple_AC_given_B_balance] (theorem) — The residual product is the sum of squared conditional cross-covariance and the determinant contribution. This is the AC conditioned on B instantiation using the named test covariance coordinates.
 Mathematical meaning: The residual product is the sum of squared conditional cross-covariance and the determinant contribution. This is the AC conditioned on B instantiation using the named test covariance coordinates. The result is used to audit conditional covariance or precision in a three-test score model.
 Exact checked proposition: forall m : TripleCovariance, ((tri_left(undefined)(covariance_var_A m)(undefined)(covariance_var_B m)(undefined)(covariance_AB m)) * (tri_right(undefined)(covariance_var_C m)(undefined)(covariance_var_B m)(undefined)(covariance_BC m))) = ((tri_cross(undefined)(covariance_AC m)(undefined)(covariance_var_B m)(undefined)(covariance_AB m)(undefined)(covariance_BC m)) * (tri_cross(undefined)(covariance_AC m)(undefined)(covariance_var_B m)(undefined)(covariance_AB m)(undefined)(covariance_BC m))) + (covariance_var_B m) * (tri_determinant(undefined)(covariance_var_A m)(undefined)(covariance_var_C m)(undefined)(covariance_var_B m)(undefined)(covariance_AC m)(undefined)(covariance_AB m)(undefined)(covariance_BC m)).
 Premises and side conditions: All scalar quantities are real. Strict conditioning variance and any determinant, residual or nonzero assumptions are explicit in the statement; no positive semidefinite matrix is silently assumed.
 Proof/definition method: Deduction from the exact trivariate Schur factorization using canonical real polynomial normalization, inequalities and elementary real algebra.
 Library reuse: Rocq standard Reals, Lra, Psatz and Ring, rather than a custom algebra solver or a duplicate probability-sum implementation.
 Boundary: Exact 3x3 covariance-candidate algebra; no continuous Gaussian conditional law, normal tail or empirical psychometric assertion is proved here.
*)
Theorem triple_AC_given_B_balance :
  forall m : TripleCovariance, ((tri_left(undefined)(covariance_var_A m)(undefined)(covariance_var_B m)(undefined)(covariance_AB m)) * (tri_right(undefined)(covariance_var_C m)(undefined)(covariance_var_B m)(undefined)(covariance_BC m))) = ((tri_cross(undefined)(covariance_AC m)(undefined)(covariance_var_B m)(undefined)(covariance_AB m)(undefined)(covariance_BC m)) * (tri_cross(undefined)(covariance_AC m)(undefined)(covariance_var_B m)(undefined)(covariance_AB m)(undefined)(covariance_BC m))) + (covariance_var_B m) * (tri_determinant(undefined)(covariance_var_A m)(undefined)(covariance_var_C m)(undefined)(covariance_var_B m)(undefined)(covariance_AC m)(undefined)(covariance_AB m)(undefined)(covariance_BC m)).
Proof.
  intro m.
  exact (trivariate_balance
    (covariance_var_A m) (covariance_var_C m) (covariance_var_B m) (covariance_AC m) (covariance_AB m) (covariance_BC m)).
Qed.

(**
 [triple_AC_given_B_singular_implies_tight] (theorem) — A zero trivariate determinant gives exact saturation of the residual covariance inequality. This is the AC conditioned on B instantiation using the named test covariance coordinates.
 Mathematical meaning: A zero trivariate determinant gives exact saturation of the residual covariance inequality. This is the AC conditioned on B instantiation using the named test covariance coordinates. The result is used to audit conditional covariance or precision in a three-test score model.
 Exact checked proposition: forall m : TripleCovariance, (tri_determinant(undefined)(covariance_var_A m)(undefined)(covariance_var_C m)(undefined)(covariance_var_B m)(undefined)(covariance_AC m)(undefined)(covariance_AB m)(undefined)(covariance_BC m)) = 0 -> ((tri_left(undefined)(covariance_var_A m)(undefined)(covariance_var_B m)(undefined)(covariance_AB m)) * (tri_right(undefined)(covariance_var_C m)(undefined)(covariance_var_B m)(undefined)(covariance_BC m))) = ((tri_cross(undefined)(covariance_AC m)(undefined)(covariance_var_B m)(undefined)(covariance_AB m)(undefined)(covariance_BC m)) * (tri_cross(undefined)(covariance_AC m)(undefined)(covariance_var_B m)(undefined)(covariance_AB m)(undefined)(covariance_BC m))).
 Premises and side conditions: All scalar quantities are real. Strict conditioning variance and any determinant, residual or nonzero assumptions are explicit in the statement; no positive semidefinite matrix is silently assumed.
 Proof/definition method: Deduction from the exact trivariate Schur factorization using canonical real polynomial normalization, inequalities and elementary real algebra.
 Library reuse: Rocq standard Reals, Lra, Psatz and Ring, rather than a custom algebra solver or a duplicate probability-sum implementation.
 Boundary: Exact 3x3 covariance-candidate algebra; no continuous Gaussian conditional law, normal tail or empirical psychometric assertion is proved here.
*)
Theorem triple_AC_given_B_singular_implies_tight :
  forall m : TripleCovariance, (tri_determinant(undefined)(covariance_var_A m)(undefined)(covariance_var_C m)(undefined)(covariance_var_B m)(undefined)(covariance_AC m)(undefined)(covariance_AB m)(undefined)(covariance_BC m)) = 0 -> ((tri_left(undefined)(covariance_var_A m)(undefined)(covariance_var_B m)(undefined)(covariance_AB m)) * (tri_right(undefined)(covariance_var_C m)(undefined)(covariance_var_B m)(undefined)(covariance_BC m))) = ((tri_cross(undefined)(covariance_AC m)(undefined)(covariance_var_B m)(undefined)(covariance_AB m)(undefined)(covariance_BC m)) * (tri_cross(undefined)(covariance_AC m)(undefined)(covariance_var_B m)(undefined)(covariance_AB m)(undefined)(covariance_BC m))).
Proof.
  intro m.
  exact (trivariate_singular_implies_tight
    (covariance_var_A m) (covariance_var_C m) (covariance_var_B m) (covariance_AC m) (covariance_AB m) (covariance_BC m)).
Qed.

(**
 [triple_AC_given_B_tight_iff_singular] (theorem) — For positive conditioning variance, tightness is equivalent to a zero determinant. This is the AC conditioned on B instantiation using the named test covariance coordinates.
 Mathematical meaning: For positive conditioning variance, tightness is equivalent to a zero determinant. This is the AC conditioned on B instantiation using the named test covariance coordinates. The result is used to audit conditional covariance or precision in a three-test score model.
 Exact checked proposition: forall m : TripleCovariance, 0 < (covariance_var_B m) -> (((tri_left(undefined)(covariance_var_A m)(undefined)(covariance_var_B m)(undefined)(covariance_AB m)) * (tri_right(undefined)(covariance_var_C m)(undefined)(covariance_var_B m)(undefined)(covariance_BC m))) = ((tri_cross(undefined)(covariance_AC m)(undefined)(covariance_var_B m)(undefined)(covariance_AB m)(undefined)(covariance_BC m)) * (tri_cross(undefined)(covariance_AC m)(undefined)(covariance_var_B m)(undefined)(covariance_AB m)(undefined)(covariance_BC m))) <-> (tri_determinant(undefined)(covariance_var_A m)(undefined)(covariance_var_C m)(undefined)(covariance_var_B m)(undefined)(covariance_AC m)(undefined)(covariance_AB m)(undefined)(covariance_BC m)) = 0).
 Premises and side conditions: All scalar quantities are real. Strict conditioning variance and any determinant, residual or nonzero assumptions are explicit in the statement; no positive semidefinite matrix is silently assumed.
 Proof/definition method: Deduction from the exact trivariate Schur factorization using canonical real polynomial normalization, inequalities and elementary real algebra.
 Library reuse: Rocq standard Reals, Lra, Psatz and Ring, rather than a custom algebra solver or a duplicate probability-sum implementation.
 Boundary: Exact 3x3 covariance-candidate algebra; no continuous Gaussian conditional law, normal tail or empirical psychometric assertion is proved here.
*)
Theorem triple_AC_given_B_tight_iff_singular :
  forall m : TripleCovariance, 0 < (covariance_var_B m) -> (((tri_left(undefined)(covariance_var_A m)(undefined)(covariance_var_B m)(undefined)(covariance_AB m)) * (tri_right(undefined)(covariance_var_C m)(undefined)(covariance_var_B m)(undefined)(covariance_BC m))) = ((tri_cross(undefined)(covariance_AC m)(undefined)(covariance_var_B m)(undefined)(covariance_AB m)(undefined)(covariance_BC m)) * (tri_cross(undefined)(covariance_AC m)(undefined)(covariance_var_B m)(undefined)(covariance_AB m)(undefined)(covariance_BC m))) <-> (tri_determinant(undefined)(covariance_var_A m)(undefined)(covariance_var_C m)(undefined)(covariance_var_B m)(undefined)(covariance_AC m)(undefined)(covariance_AB m)(undefined)(covariance_BC m)) = 0).
Proof.
  intro m.
  exact (trivariate_tight_iff_singular
    (covariance_var_A m) (covariance_var_C m) (covariance_var_B m) (covariance_AC m) (covariance_AB m) (covariance_BC m)).
Qed.

(**
 [triple_AC_given_B_positive_iff_strict] (theorem) — Positive determinant is equivalent to a strict Schur Cauchy-Schwarz gap. This is the AC conditioned on B instantiation using the named test covariance coordinates.
 Mathematical meaning: Positive determinant is equivalent to a strict Schur Cauchy-Schwarz gap. This is the AC conditioned on B instantiation using the named test covariance coordinates. The result is used to audit conditional covariance or precision in a three-test score model.
 Exact checked proposition: forall m : TripleCovariance, 0 < (covariance_var_B m) -> (0 < (tri_determinant(undefined)(covariance_var_A m)(undefined)(covariance_var_C m)(undefined)(covariance_var_B m)(undefined)(covariance_AC m)(undefined)(covariance_AB m)(undefined)(covariance_BC m)) <-> ((tri_cross(undefined)(covariance_AC m)(undefined)(covariance_var_B m)(undefined)(covariance_AB m)(undefined)(covariance_BC m)) * (tri_cross(undefined)(covariance_AC m)(undefined)(covariance_var_B m)(undefined)(covariance_AB m)(undefined)(covariance_BC m))) < ((tri_left(undefined)(covariance_var_A m)(undefined)(covariance_var_B m)(undefined)(covariance_AB m)) * (tri_right(undefined)(covariance_var_C m)(undefined)(covariance_var_B m)(undefined)(covariance_BC m)))).
 Premises and side conditions: All scalar quantities are real. Strict conditioning variance and any determinant, residual or nonzero assumptions are explicit in the statement; no positive semidefinite matrix is silently assumed.
 Proof/definition method: Deduction from the exact trivariate Schur factorization using canonical real polynomial normalization, inequalities and elementary real algebra.
 Library reuse: Rocq standard Reals, Lra, Psatz and Ring, rather than a custom algebra solver or a duplicate probability-sum implementation.
 Boundary: Exact 3x3 covariance-candidate algebra; no continuous Gaussian conditional law, normal tail or empirical psychometric assertion is proved here.
*)
Theorem triple_AC_given_B_positive_iff_strict :
  forall m : TripleCovariance, 0 < (covariance_var_B m) -> (0 < (tri_determinant(undefined)(covariance_var_A m)(undefined)(covariance_var_C m)(undefined)(covariance_var_B m)(undefined)(covariance_AC m)(undefined)(covariance_AB m)(undefined)(covariance_BC m)) <-> ((tri_cross(undefined)(covariance_AC m)(undefined)(covariance_var_B m)(undefined)(covariance_AB m)(undefined)(covariance_BC m)) * (tri_cross(undefined)(covariance_AC m)(undefined)(covariance_var_B m)(undefined)(covariance_AB m)(undefined)(covariance_BC m))) < ((tri_left(undefined)(covariance_var_A m)(undefined)(covariance_var_B m)(undefined)(covariance_AB m)) * (tri_right(undefined)(covariance_var_C m)(undefined)(covariance_var_B m)(undefined)(covariance_BC m)))).
Proof.
  intro m.
  exact (trivariate_positive_iff_strict
    (covariance_var_A m) (covariance_var_C m) (covariance_var_B m) (covariance_AC m) (covariance_AB m) (covariance_BC m)).
Qed.

(**
 [triple_AC_given_B_negative_iff_reverse] (theorem) — Negative determinant is equivalent to strict reversal of the Schur inequality. This is the AC conditioned on B instantiation using the named test covariance coordinates.
 Mathematical meaning: Negative determinant is equivalent to strict reversal of the Schur inequality. This is the AC conditioned on B instantiation using the named test covariance coordinates. The result is used to audit conditional covariance or precision in a three-test score model.
 Exact checked proposition: forall m : TripleCovariance, 0 < (covariance_var_B m) -> ((tri_determinant(undefined)(covariance_var_A m)(undefined)(covariance_var_C m)(undefined)(covariance_var_B m)(undefined)(covariance_AC m)(undefined)(covariance_AB m)(undefined)(covariance_BC m)) < 0 <-> ((tri_left(undefined)(covariance_var_A m)(undefined)(covariance_var_B m)(undefined)(covariance_AB m)) * (tri_right(undefined)(covariance_var_C m)(undefined)(covariance_var_B m)(undefined)(covariance_BC m))) < ((tri_cross(undefined)(covariance_AC m)(undefined)(covariance_var_B m)(undefined)(covariance_AB m)(undefined)(covariance_BC m)) * (tri_cross(undefined)(covariance_AC m)(undefined)(covariance_var_B m)(undefined)(covariance_AB m)(undefined)(covariance_BC m)))).
 Premises and side conditions: All scalar quantities are real. Strict conditioning variance and any determinant, residual or nonzero assumptions are explicit in the statement; no positive semidefinite matrix is silently assumed.
 Proof/definition method: Deduction from the exact trivariate Schur factorization using canonical real polynomial normalization, inequalities and elementary real algebra.
 Library reuse: Rocq standard Reals, Lra, Psatz and Ring, rather than a custom algebra solver or a duplicate probability-sum implementation.
 Boundary: Exact 3x3 covariance-candidate algebra; no continuous Gaussian conditional law, normal tail or empirical psychometric assertion is proved here.
*)
Theorem triple_AC_given_B_negative_iff_reverse :
  forall m : TripleCovariance, 0 < (covariance_var_B m) -> ((tri_determinant(undefined)(covariance_var_A m)(undefined)(covariance_var_C m)(undefined)(covariance_var_B m)(undefined)(covariance_AC m)(undefined)(covariance_AB m)(undefined)(covariance_BC m)) < 0 <-> ((tri_left(undefined)(covariance_var_A m)(undefined)(covariance_var_B m)(undefined)(covariance_AB m)) * (tri_right(undefined)(covariance_var_C m)(undefined)(covariance_var_B m)(undefined)(covariance_BC m))) < ((tri_cross(undefined)(covariance_AC m)(undefined)(covariance_var_B m)(undefined)(covariance_AB m)(undefined)(covariance_BC m)) * (tri_cross(undefined)(covariance_AC m)(undefined)(covariance_var_B m)(undefined)(covariance_AB m)(undefined)(covariance_BC m)))).
Proof.
  intro m.
  exact (trivariate_negative_iff_reverse
    (covariance_var_A m) (covariance_var_C m) (covariance_var_B m) (covariance_AC m) (covariance_AB m) (covariance_BC m)).
Qed.

(**
 [triple_AC_given_B_nonnegative_iff_weak] (theorem) — Nonnegative determinant is equivalent to the weak Schur Cauchy-Schwarz inequality. This is the AC conditioned on B instantiation using the named test covariance coordinates.
 Mathematical meaning: Nonnegative determinant is equivalent to the weak Schur Cauchy-Schwarz inequality. This is the AC conditioned on B instantiation using the named test covariance coordinates. The result is used to audit conditional covariance or precision in a three-test score model.
 Exact checked proposition: forall m : TripleCovariance, 0 < (covariance_var_B m) -> (0 <= (tri_determinant(undefined)(covariance_var_A m)(undefined)(covariance_var_C m)(undefined)(covariance_var_B m)(undefined)(covariance_AC m)(undefined)(covariance_AB m)(undefined)(covariance_BC m)) <-> ((tri_cross(undefined)(covariance_AC m)(undefined)(covariance_var_B m)(undefined)(covariance_AB m)(undefined)(covariance_BC m)) * (tri_cross(undefined)(covariance_AC m)(undefined)(covariance_var_B m)(undefined)(covariance_AB m)(undefined)(covariance_BC m))) <= ((tri_left(undefined)(covariance_var_A m)(undefined)(covariance_var_B m)(undefined)(covariance_AB m)) * (tri_right(undefined)(covariance_var_C m)(undefined)(covariance_var_B m)(undefined)(covariance_BC m)))).
 Premises and side conditions: All scalar quantities are real. Strict conditioning variance and any determinant, residual or nonzero assumptions are explicit in the statement; no positive semidefinite matrix is silently assumed.
 Proof/definition method: Deduction from the exact trivariate Schur factorization using canonical real polynomial normalization, inequalities and elementary real algebra.
 Library reuse: Rocq standard Reals, Lra, Psatz and Ring, rather than a custom algebra solver or a duplicate probability-sum implementation.
 Boundary: Exact 3x3 covariance-candidate algebra; no continuous Gaussian conditional law, normal tail or empirical psychometric assertion is proved here.
*)
Theorem triple_AC_given_B_nonnegative_iff_weak :
  forall m : TripleCovariance, 0 < (covariance_var_B m) -> (0 <= (tri_determinant(undefined)(covariance_var_A m)(undefined)(covariance_var_C m)(undefined)(covariance_var_B m)(undefined)(covariance_AC m)(undefined)(covariance_AB m)(undefined)(covariance_BC m)) <-> ((tri_cross(undefined)(covariance_AC m)(undefined)(covariance_var_B m)(undefined)(covariance_AB m)(undefined)(covariance_BC m)) * (tri_cross(undefined)(covariance_AC m)(undefined)(covariance_var_B m)(undefined)(covariance_AB m)(undefined)(covariance_BC m))) <= ((tri_left(undefined)(covariance_var_A m)(undefined)(covariance_var_B m)(undefined)(covariance_AB m)) * (tri_right(undefined)(covariance_var_C m)(undefined)(covariance_var_B m)(undefined)(covariance_BC m)))).
Proof.
  intro m.
  exact (trivariate_nonnegative_iff_weak
    (covariance_var_A m) (covariance_var_C m) (covariance_var_B m) (covariance_AC m) (covariance_AB m) (covariance_BC m)).
Qed.

(**
 [triple_AC_given_B_nonpositive_iff_reverse_weak] (theorem) — Nonpositive determinant is equivalent to the reverse weak residual inequality. This is the AC conditioned on B instantiation using the named test covariance coordinates.
 Mathematical meaning: Nonpositive determinant is equivalent to the reverse weak residual inequality. This is the AC conditioned on B instantiation using the named test covariance coordinates. The result is used to audit conditional covariance or precision in a three-test score model.
 Exact checked proposition: forall m : TripleCovariance, 0 < (covariance_var_B m) -> ((tri_determinant(undefined)(covariance_var_A m)(undefined)(covariance_var_C m)(undefined)(covariance_var_B m)(undefined)(covariance_AC m)(undefined)(covariance_AB m)(undefined)(covariance_BC m)) <= 0 <-> ((tri_left(undefined)(covariance_var_A m)(undefined)(covariance_var_B m)(undefined)(covariance_AB m)) * (tri_right(undefined)(covariance_var_C m)(undefined)(covariance_var_B m)(undefined)(covariance_BC m))) <= ((tri_cross(undefined)(covariance_AC m)(undefined)(covariance_var_B m)(undefined)(covariance_AB m)(undefined)(covariance_BC m)) * (tri_cross(undefined)(covariance_AC m)(undefined)(covariance_var_B m)(undefined)(covariance_AB m)(undefined)(covariance_BC m)))).
 Premises and side conditions: All scalar quantities are real. Strict conditioning variance and any determinant, residual or nonzero assumptions are explicit in the statement; no positive semidefinite matrix is silently assumed.
 Proof/definition method: Deduction from the exact trivariate Schur factorization using canonical real polynomial normalization, inequalities and elementary real algebra.
 Library reuse: Rocq standard Reals, Lra, Psatz and Ring, rather than a custom algebra solver or a duplicate probability-sum implementation.
 Boundary: Exact 3x3 covariance-candidate algebra; no continuous Gaussian conditional law, normal tail or empirical psychometric assertion is proved here.
*)
Theorem triple_AC_given_B_nonpositive_iff_reverse_weak :
  forall m : TripleCovariance, 0 < (covariance_var_B m) -> ((tri_determinant(undefined)(covariance_var_A m)(undefined)(covariance_var_C m)(undefined)(covariance_var_B m)(undefined)(covariance_AC m)(undefined)(covariance_AB m)(undefined)(covariance_BC m)) <= 0 <-> ((tri_left(undefined)(covariance_var_A m)(undefined)(covariance_var_B m)(undefined)(covariance_AB m)) * (tri_right(undefined)(covariance_var_C m)(undefined)(covariance_var_B m)(undefined)(covariance_BC m))) <= ((tri_cross(undefined)(covariance_AC m)(undefined)(covariance_var_B m)(undefined)(covariance_AB m)(undefined)(covariance_BC m)) * (tri_cross(undefined)(covariance_AC m)(undefined)(covariance_var_B m)(undefined)(covariance_AB m)(undefined)(covariance_BC m)))).
Proof.
  intro m.
  exact (trivariate_nonpositive_iff_reverse_weak
    (covariance_var_A m) (covariance_var_C m) (covariance_var_B m) (covariance_AC m) (covariance_AB m) (covariance_BC m)).
Qed.

(**
 [triple_AC_given_B_strict_positive_bound] (theorem) — A positive determinant forces a strict conditional Cauchy-Schwarz bound. This is the AC conditioned on B instantiation using the named test covariance coordinates.
 Mathematical meaning: A positive determinant forces a strict conditional Cauchy-Schwarz bound. This is the AC conditioned on B instantiation using the named test covariance coordinates. The result is used to audit conditional covariance or precision in a three-test score model.
 Exact checked proposition: forall m : TripleCovariance, 0 < (covariance_var_B m) -> 0 < (tri_determinant(undefined)(covariance_var_A m)(undefined)(covariance_var_C m)(undefined)(covariance_var_B m)(undefined)(covariance_AC m)(undefined)(covariance_AB m)(undefined)(covariance_BC m)) -> ((tri_cross(undefined)(covariance_AC m)(undefined)(covariance_var_B m)(undefined)(covariance_AB m)(undefined)(covariance_BC m)) * (tri_cross(undefined)(covariance_AC m)(undefined)(covariance_var_B m)(undefined)(covariance_AB m)(undefined)(covariance_BC m))) < ((tri_left(undefined)(covariance_var_A m)(undefined)(covariance_var_B m)(undefined)(covariance_AB m)) * (tri_right(undefined)(covariance_var_C m)(undefined)(covariance_var_B m)(undefined)(covariance_BC m))).
 Premises and side conditions: All scalar quantities are real. Strict conditioning variance and any determinant, residual or nonzero assumptions are explicit in the statement; no positive semidefinite matrix is silently assumed.
 Proof/definition method: Deduction from the exact trivariate Schur factorization using canonical real polynomial normalization, inequalities and elementary real algebra.
 Library reuse: Rocq standard Reals, Lra, Psatz and Ring, rather than a custom algebra solver or a duplicate probability-sum implementation.
 Boundary: Exact 3x3 covariance-candidate algebra; no continuous Gaussian conditional law, normal tail or empirical psychometric assertion is proved here.
*)
Theorem triple_AC_given_B_strict_positive_bound :
  forall m : TripleCovariance, 0 < (covariance_var_B m) -> 0 < (tri_determinant(undefined)(covariance_var_A m)(undefined)(covariance_var_C m)(undefined)(covariance_var_B m)(undefined)(covariance_AC m)(undefined)(covariance_AB m)(undefined)(covariance_BC m)) -> ((tri_cross(undefined)(covariance_AC m)(undefined)(covariance_var_B m)(undefined)(covariance_AB m)(undefined)(covariance_BC m)) * (tri_cross(undefined)(covariance_AC m)(undefined)(covariance_var_B m)(undefined)(covariance_AB m)(undefined)(covariance_BC m))) < ((tri_left(undefined)(covariance_var_A m)(undefined)(covariance_var_B m)(undefined)(covariance_AB m)) * (tri_right(undefined)(covariance_var_C m)(undefined)(covariance_var_B m)(undefined)(covariance_BC m))).
Proof.
  intro m.
  exact (trivariate_strict_positive_bound
    (covariance_var_A m) (covariance_var_C m) (covariance_var_B m) (covariance_AC m) (covariance_AB m) (covariance_BC m)).
Qed.

(**
 [triple_AC_given_B_strict_negative_bound] (theorem) — A negative determinant forces a strict reverse conditional Cauchy-Schwarz bound. This is the AC conditioned on B instantiation using the named test covariance coordinates.
 Mathematical meaning: A negative determinant forces a strict reverse conditional Cauchy-Schwarz bound. This is the AC conditioned on B instantiation using the named test covariance coordinates. The result is used to audit conditional covariance or precision in a three-test score model.
 Exact checked proposition: forall m : TripleCovariance, 0 < (covariance_var_B m) -> (tri_determinant(undefined)(covariance_var_A m)(undefined)(covariance_var_C m)(undefined)(covariance_var_B m)(undefined)(covariance_AC m)(undefined)(covariance_AB m)(undefined)(covariance_BC m)) < 0 -> ((tri_left(undefined)(covariance_var_A m)(undefined)(covariance_var_B m)(undefined)(covariance_AB m)) * (tri_right(undefined)(covariance_var_C m)(undefined)(covariance_var_B m)(undefined)(covariance_BC m))) < ((tri_cross(undefined)(covariance_AC m)(undefined)(covariance_var_B m)(undefined)(covariance_AB m)(undefined)(covariance_BC m)) * (tri_cross(undefined)(covariance_AC m)(undefined)(covariance_var_B m)(undefined)(covariance_AB m)(undefined)(covariance_BC m))).
 Premises and side conditions: All scalar quantities are real. Strict conditioning variance and any determinant, residual or nonzero assumptions are explicit in the statement; no positive semidefinite matrix is silently assumed.
 Proof/definition method: Deduction from the exact trivariate Schur factorization using canonical real polynomial normalization, inequalities and elementary real algebra.
 Library reuse: Rocq standard Reals, Lra, Psatz and Ring, rather than a custom algebra solver or a duplicate probability-sum implementation.
 Boundary: Exact 3x3 covariance-candidate algebra; no continuous Gaussian conditional law, normal tail or empirical psychometric assertion is proved here.
*)
Theorem triple_AC_given_B_strict_negative_bound :
  forall m : TripleCovariance, 0 < (covariance_var_B m) -> (tri_determinant(undefined)(covariance_var_A m)(undefined)(covariance_var_C m)(undefined)(covariance_var_B m)(undefined)(covariance_AC m)(undefined)(covariance_AB m)(undefined)(covariance_BC m)) < 0 -> ((tri_left(undefined)(covariance_var_A m)(undefined)(covariance_var_B m)(undefined)(covariance_AB m)) * (tri_right(undefined)(covariance_var_C m)(undefined)(covariance_var_B m)(undefined)(covariance_BC m))) < ((tri_cross(undefined)(covariance_AC m)(undefined)(covariance_var_B m)(undefined)(covariance_AB m)(undefined)(covariance_BC m)) * (tri_cross(undefined)(covariance_AC m)(undefined)(covariance_var_B m)(undefined)(covariance_AB m)(undefined)(covariance_BC m))).
Proof.
  intro m.
  exact (trivariate_strict_negative_bound
    (covariance_var_A m) (covariance_var_C m) (covariance_var_B m) (covariance_AC m) (covariance_AB m) (covariance_BC m)).
Qed.

(**
 [triple_AC_given_B_weak_positive_bound] (theorem) — A nonnegative determinant bounds squared conditional covariance by the residual product. This is the AC conditioned on B instantiation using the named test covariance coordinates.
 Mathematical meaning: A nonnegative determinant bounds squared conditional covariance by the residual product. This is the AC conditioned on B instantiation using the named test covariance coordinates. The result is used to audit conditional covariance or precision in a three-test score model.
 Exact checked proposition: forall m : TripleCovariance, 0 < (covariance_var_B m) -> 0 <= (tri_determinant(undefined)(covariance_var_A m)(undefined)(covariance_var_C m)(undefined)(covariance_var_B m)(undefined)(covariance_AC m)(undefined)(covariance_AB m)(undefined)(covariance_BC m)) -> ((tri_cross(undefined)(covariance_AC m)(undefined)(covariance_var_B m)(undefined)(covariance_AB m)(undefined)(covariance_BC m)) * (tri_cross(undefined)(covariance_AC m)(undefined)(covariance_var_B m)(undefined)(covariance_AB m)(undefined)(covariance_BC m))) <= ((tri_left(undefined)(covariance_var_A m)(undefined)(covariance_var_B m)(undefined)(covariance_AB m)) * (tri_right(undefined)(covariance_var_C m)(undefined)(covariance_var_B m)(undefined)(covariance_BC m))).
 Premises and side conditions: All scalar quantities are real. Strict conditioning variance and any determinant, residual or nonzero assumptions are explicit in the statement; no positive semidefinite matrix is silently assumed.
 Proof/definition method: Deduction from the exact trivariate Schur factorization using canonical real polynomial normalization, inequalities and elementary real algebra.
 Library reuse: Rocq standard Reals, Lra, Psatz and Ring, rather than a custom algebra solver or a duplicate probability-sum implementation.
 Boundary: Exact 3x3 covariance-candidate algebra; no continuous Gaussian conditional law, normal tail or empirical psychometric assertion is proved here.
*)
Theorem triple_AC_given_B_weak_positive_bound :
  forall m : TripleCovariance, 0 < (covariance_var_B m) -> 0 <= (tri_determinant(undefined)(covariance_var_A m)(undefined)(covariance_var_C m)(undefined)(covariance_var_B m)(undefined)(covariance_AC m)(undefined)(covariance_AB m)(undefined)(covariance_BC m)) -> ((tri_cross(undefined)(covariance_AC m)(undefined)(covariance_var_B m)(undefined)(covariance_AB m)(undefined)(covariance_BC m)) * (tri_cross(undefined)(covariance_AC m)(undefined)(covariance_var_B m)(undefined)(covariance_AB m)(undefined)(covariance_BC m))) <= ((tri_left(undefined)(covariance_var_A m)(undefined)(covariance_var_B m)(undefined)(covariance_AB m)) * (tri_right(undefined)(covariance_var_C m)(undefined)(covariance_var_B m)(undefined)(covariance_BC m))).
Proof.
  intro m.
  exact (trivariate_weak_positive_bound
    (covariance_var_A m) (covariance_var_C m) (covariance_var_B m) (covariance_AC m) (covariance_AB m) (covariance_BC m)).
Qed.

(**
 [triple_AC_given_B_weak_negative_bound] (theorem) — A nonpositive determinant bounds the residual product by squared conditional covariance. This is the AC conditioned on B instantiation using the named test covariance coordinates.
 Mathematical meaning: A nonpositive determinant bounds the residual product by squared conditional covariance. This is the AC conditioned on B instantiation using the named test covariance coordinates. The result is used to audit conditional covariance or precision in a three-test score model.
 Exact checked proposition: forall m : TripleCovariance, 0 < (covariance_var_B m) -> (tri_determinant(undefined)(covariance_var_A m)(undefined)(covariance_var_C m)(undefined)(covariance_var_B m)(undefined)(covariance_AC m)(undefined)(covariance_AB m)(undefined)(covariance_BC m)) <= 0 -> ((tri_left(undefined)(covariance_var_A m)(undefined)(covariance_var_B m)(undefined)(covariance_AB m)) * (tri_right(undefined)(covariance_var_C m)(undefined)(covariance_var_B m)(undefined)(covariance_BC m))) <= ((tri_cross(undefined)(covariance_AC m)(undefined)(covariance_var_B m)(undefined)(covariance_AB m)(undefined)(covariance_BC m)) * (tri_cross(undefined)(covariance_AC m)(undefined)(covariance_var_B m)(undefined)(covariance_AB m)(undefined)(covariance_BC m))).
 Premises and side conditions: All scalar quantities are real. Strict conditioning variance and any determinant, residual or nonzero assumptions are explicit in the statement; no positive semidefinite matrix is silently assumed.
 Proof/definition method: Deduction from the exact trivariate Schur factorization using canonical real polynomial normalization, inequalities and elementary real algebra.
 Library reuse: Rocq standard Reals, Lra, Psatz and Ring, rather than a custom algebra solver or a duplicate probability-sum implementation.
 Boundary: Exact 3x3 covariance-candidate algebra; no continuous Gaussian conditional law, normal tail or empirical psychometric assertion is proved here.
*)
Theorem triple_AC_given_B_weak_negative_bound :
  forall m : TripleCovariance, 0 < (covariance_var_B m) -> (tri_determinant(undefined)(covariance_var_A m)(undefined)(covariance_var_C m)(undefined)(covariance_var_B m)(undefined)(covariance_AC m)(undefined)(covariance_AB m)(undefined)(covariance_BC m)) <= 0 -> ((tri_left(undefined)(covariance_var_A m)(undefined)(covariance_var_B m)(undefined)(covariance_AB m)) * (tri_right(undefined)(covariance_var_C m)(undefined)(covariance_var_B m)(undefined)(covariance_BC m))) <= ((tri_cross(undefined)(covariance_AC m)(undefined)(covariance_var_B m)(undefined)(covariance_AB m)(undefined)(covariance_BC m)) * (tri_cross(undefined)(covariance_AC m)(undefined)(covariance_var_B m)(undefined)(covariance_AB m)(undefined)(covariance_BC m))).
Proof.
  intro m.
  exact (trivariate_weak_negative_bound
    (covariance_var_A m) (covariance_var_C m) (covariance_var_B m) (covariance_AC m) (covariance_AB m) (covariance_BC m)).
Qed.

(**
 [triple_AC_given_B_zero_cross_factor] (theorem) — Conditional uncorrelatedness makes the residual product exactly the conditioning variance times the determinant. This is the AC conditioned on B instantiation using the named test covariance coordinates.
 Mathematical meaning: Conditional uncorrelatedness makes the residual product exactly the conditioning variance times the determinant. This is the AC conditioned on B instantiation using the named test covariance coordinates. The result is used to audit conditional covariance or precision in a three-test score model.
 Exact checked proposition: forall m : TripleCovariance, (tri_cross(undefined)(covariance_AC m)(undefined)(covariance_var_B m)(undefined)(covariance_AB m)(undefined)(covariance_BC m)) = 0 -> ((tri_left(undefined)(covariance_var_A m)(undefined)(covariance_var_B m)(undefined)(covariance_AB m)) * (tri_right(undefined)(covariance_var_C m)(undefined)(covariance_var_B m)(undefined)(covariance_BC m))) = (covariance_var_B m) * (tri_determinant(undefined)(covariance_var_A m)(undefined)(covariance_var_C m)(undefined)(covariance_var_B m)(undefined)(covariance_AC m)(undefined)(covariance_AB m)(undefined)(covariance_BC m)).
 Premises and side conditions: All scalar quantities are real. Strict conditioning variance and any determinant, residual or nonzero assumptions are explicit in the statement; no positive semidefinite matrix is silently assumed.
 Proof/definition method: Deduction from the exact trivariate Schur factorization using canonical real polynomial normalization, inequalities and elementary real algebra.
 Library reuse: Rocq standard Reals, Lra, Psatz and Ring, rather than a custom algebra solver or a duplicate probability-sum implementation.
 Boundary: Exact 3x3 covariance-candidate algebra; no continuous Gaussian conditional law, normal tail or empirical psychometric assertion is proved here.
*)
Theorem triple_AC_given_B_zero_cross_factor :
  forall m : TripleCovariance, (tri_cross(undefined)(covariance_AC m)(undefined)(covariance_var_B m)(undefined)(covariance_AB m)(undefined)(covariance_BC m)) = 0 -> ((tri_left(undefined)(covariance_var_A m)(undefined)(covariance_var_B m)(undefined)(covariance_AB m)) * (tri_right(undefined)(covariance_var_C m)(undefined)(covariance_var_B m)(undefined)(covariance_BC m))) = (covariance_var_B m) * (tri_determinant(undefined)(covariance_var_A m)(undefined)(covariance_var_C m)(undefined)(covariance_var_B m)(undefined)(covariance_AC m)(undefined)(covariance_AB m)(undefined)(covariance_BC m)).
Proof.
  intro m.
  exact (trivariate_zero_cross_factor
    (covariance_var_A m) (covariance_var_C m) (covariance_var_B m) (covariance_AC m) (covariance_AB m) (covariance_BC m)).
Qed.

(**
 [triple_AC_given_B_zero_cross_positive_product] (theorem) — Conditional uncorrelatedness and positive determinant imply a strictly positive residual product. This is the AC conditioned on B instantiation using the named test covariance coordinates.
 Mathematical meaning: Conditional uncorrelatedness and positive determinant imply a strictly positive residual product. This is the AC conditioned on B instantiation using the named test covariance coordinates. The result is used to audit conditional covariance or precision in a three-test score model.
 Exact checked proposition: forall m : TripleCovariance, 0 < (covariance_var_B m) -> (tri_cross(undefined)(covariance_AC m)(undefined)(covariance_var_B m)(undefined)(covariance_AB m)(undefined)(covariance_BC m)) = 0 -> 0 < (tri_determinant(undefined)(covariance_var_A m)(undefined)(covariance_var_C m)(undefined)(covariance_var_B m)(undefined)(covariance_AC m)(undefined)(covariance_AB m)(undefined)(covariance_BC m)) -> 0 < ((tri_left(undefined)(covariance_var_A m)(undefined)(covariance_var_B m)(undefined)(covariance_AB m)) * (tri_right(undefined)(covariance_var_C m)(undefined)(covariance_var_B m)(undefined)(covariance_BC m))).
 Premises and side conditions: All scalar quantities are real. Strict conditioning variance and any determinant, residual or nonzero assumptions are explicit in the statement; no positive semidefinite matrix is silently assumed.
 Proof/definition method: Deduction from the exact trivariate Schur factorization using canonical real polynomial normalization, inequalities and elementary real algebra.
 Library reuse: Rocq standard Reals, Lra, Psatz and Ring, rather than a custom algebra solver or a duplicate probability-sum implementation.
 Boundary: Exact 3x3 covariance-candidate algebra; no continuous Gaussian conditional law, normal tail or empirical psychometric assertion is proved here.
*)
Theorem triple_AC_given_B_zero_cross_positive_product :
  forall m : TripleCovariance, 0 < (covariance_var_B m) -> (tri_cross(undefined)(covariance_AC m)(undefined)(covariance_var_B m)(undefined)(covariance_AB m)(undefined)(covariance_BC m)) = 0 -> 0 < (tri_determinant(undefined)(covariance_var_A m)(undefined)(covariance_var_C m)(undefined)(covariance_var_B m)(undefined)(covariance_AC m)(undefined)(covariance_AB m)(undefined)(covariance_BC m)) -> 0 < ((tri_left(undefined)(covariance_var_A m)(undefined)(covariance_var_B m)(undefined)(covariance_AB m)) * (tri_right(undefined)(covariance_var_C m)(undefined)(covariance_var_B m)(undefined)(covariance_BC m))).
Proof.
  intro m.
  exact (trivariate_zero_cross_positive_product
    (covariance_var_A m) (covariance_var_C m) (covariance_var_B m) (covariance_AC m) (covariance_AB m) (covariance_BC m)).
Qed.

(**
 [triple_AC_given_B_zero_cross_singular_product] (theorem) — Conditional uncorrelatedness with singular determinant forces at least one residual factor to vanish. This is the AC conditioned on B instantiation using the named test covariance coordinates.
 Mathematical meaning: Conditional uncorrelatedness with singular determinant forces at least one residual factor to vanish. This is the AC conditioned on B instantiation using the named test covariance coordinates. The result is used to audit conditional covariance or precision in a three-test score model.
 Exact checked proposition: forall m : TripleCovariance, (tri_cross(undefined)(covariance_AC m)(undefined)(covariance_var_B m)(undefined)(covariance_AB m)(undefined)(covariance_BC m)) = 0 -> (tri_determinant(undefined)(covariance_var_A m)(undefined)(covariance_var_C m)(undefined)(covariance_var_B m)(undefined)(covariance_AC m)(undefined)(covariance_AB m)(undefined)(covariance_BC m)) = 0 -> ((tri_left(undefined)(covariance_var_A m)(undefined)(covariance_var_B m)(undefined)(covariance_AB m)) * (tri_right(undefined)(covariance_var_C m)(undefined)(covariance_var_B m)(undefined)(covariance_BC m))) = 0.
 Premises and side conditions: All scalar quantities are real. Strict conditioning variance and any determinant, residual or nonzero assumptions are explicit in the statement; no positive semidefinite matrix is silently assumed.
 Proof/definition method: Deduction from the exact trivariate Schur factorization using canonical real polynomial normalization, inequalities and elementary real algebra.
 Library reuse: Rocq standard Reals, Lra, Psatz and Ring, rather than a custom algebra solver or a duplicate probability-sum implementation.
 Boundary: Exact 3x3 covariance-candidate algebra; no continuous Gaussian conditional law, normal tail or empirical psychometric assertion is proved here.
*)
Theorem triple_AC_given_B_zero_cross_singular_product :
  forall m : TripleCovariance, (tri_cross(undefined)(covariance_AC m)(undefined)(covariance_var_B m)(undefined)(covariance_AB m)(undefined)(covariance_BC m)) = 0 -> (tri_determinant(undefined)(covariance_var_A m)(undefined)(covariance_var_C m)(undefined)(covariance_var_B m)(undefined)(covariance_AC m)(undefined)(covariance_AB m)(undefined)(covariance_BC m)) = 0 -> ((tri_left(undefined)(covariance_var_A m)(undefined)(covariance_var_B m)(undefined)(covariance_AB m)) * (tri_right(undefined)(covariance_var_C m)(undefined)(covariance_var_B m)(undefined)(covariance_BC m))) = 0.
Proof.
  intro m.
  exact (trivariate_zero_cross_singular_product
    (covariance_var_A m) (covariance_var_C m) (covariance_var_B m) (covariance_AC m) (covariance_AB m) (covariance_BC m)).
Qed.

(**
 [triple_AC_given_B_zero_left_determinant] (theorem) — Vanishing first residual gives an exact negative-square identity. This is the AC conditioned on B instantiation using the named test covariance coordinates.
 Mathematical meaning: Vanishing first residual gives an exact negative-square identity. This is the AC conditioned on B instantiation using the named test covariance coordinates. The result is used to audit conditional covariance or precision in a three-test score model.
 Exact checked proposition: forall m : TripleCovariance, (tri_left(undefined)(covariance_var_A m)(undefined)(covariance_var_B m)(undefined)(covariance_AB m)) = 0 -> (covariance_var_B m) * (tri_determinant(undefined)(covariance_var_A m)(undefined)(covariance_var_C m)(undefined)(covariance_var_B m)(undefined)(covariance_AC m)(undefined)(covariance_AB m)(undefined)(covariance_BC m)) = - ((tri_cross(undefined)(covariance_AC m)(undefined)(covariance_var_B m)(undefined)(covariance_AB m)(undefined)(covariance_BC m)) * (tri_cross(undefined)(covariance_AC m)(undefined)(covariance_var_B m)(undefined)(covariance_AB m)(undefined)(covariance_BC m))).
 Premises and side conditions: All scalar quantities are real. Strict conditioning variance and any determinant, residual or nonzero assumptions are explicit in the statement; no positive semidefinite matrix is silently assumed.
 Proof/definition method: Deduction from the exact trivariate Schur factorization using canonical real polynomial normalization, inequalities and elementary real algebra.
 Library reuse: Rocq standard Reals, Lra, Psatz and Ring, rather than a custom algebra solver or a duplicate probability-sum implementation.
 Boundary: Exact 3x3 covariance-candidate algebra; no continuous Gaussian conditional law, normal tail or empirical psychometric assertion is proved here.
*)
Theorem triple_AC_given_B_zero_left_determinant :
  forall m : TripleCovariance, (tri_left(undefined)(covariance_var_A m)(undefined)(covariance_var_B m)(undefined)(covariance_AB m)) = 0 -> (covariance_var_B m) * (tri_determinant(undefined)(covariance_var_A m)(undefined)(covariance_var_C m)(undefined)(covariance_var_B m)(undefined)(covariance_AC m)(undefined)(covariance_AB m)(undefined)(covariance_BC m)) = - ((tri_cross(undefined)(covariance_AC m)(undefined)(covariance_var_B m)(undefined)(covariance_AB m)(undefined)(covariance_BC m)) * (tri_cross(undefined)(covariance_AC m)(undefined)(covariance_var_B m)(undefined)(covariance_AB m)(undefined)(covariance_BC m))).
Proof.
  intro m.
  exact (trivariate_zero_left_determinant
    (covariance_var_A m) (covariance_var_C m) (covariance_var_B m) (covariance_AC m) (covariance_AB m) (covariance_BC m)).
Qed.

(**
 [triple_AC_given_B_zero_right_determinant] (theorem) — Vanishing second residual gives an exact negative-square identity. This is the AC conditioned on B instantiation using the named test covariance coordinates.
 Mathematical meaning: Vanishing second residual gives an exact negative-square identity. This is the AC conditioned on B instantiation using the named test covariance coordinates. The result is used to audit conditional covariance or precision in a three-test score model.
 Exact checked proposition: forall m : TripleCovariance, (tri_right(undefined)(covariance_var_C m)(undefined)(covariance_var_B m)(undefined)(covariance_BC m)) = 0 -> (covariance_var_B m) * (tri_determinant(undefined)(covariance_var_A m)(undefined)(covariance_var_C m)(undefined)(covariance_var_B m)(undefined)(covariance_AC m)(undefined)(covariance_AB m)(undefined)(covariance_BC m)) = - ((tri_cross(undefined)(covariance_AC m)(undefined)(covariance_var_B m)(undefined)(covariance_AB m)(undefined)(covariance_BC m)) * (tri_cross(undefined)(covariance_AC m)(undefined)(covariance_var_B m)(undefined)(covariance_AB m)(undefined)(covariance_BC m))).
 Premises and side conditions: All scalar quantities are real. Strict conditioning variance and any determinant, residual or nonzero assumptions are explicit in the statement; no positive semidefinite matrix is silently assumed.
 Proof/definition method: Deduction from the exact trivariate Schur factorization using canonical real polynomial normalization, inequalities and elementary real algebra.
 Library reuse: Rocq standard Reals, Lra, Psatz and Ring, rather than a custom algebra solver or a duplicate probability-sum implementation.
 Boundary: Exact 3x3 covariance-candidate algebra; no continuous Gaussian conditional law, normal tail or empirical psychometric assertion is proved here.
*)
Theorem triple_AC_given_B_zero_right_determinant :
  forall m : TripleCovariance, (tri_right(undefined)(covariance_var_C m)(undefined)(covariance_var_B m)(undefined)(covariance_BC m)) = 0 -> (covariance_var_B m) * (tri_determinant(undefined)(covariance_var_A m)(undefined)(covariance_var_C m)(undefined)(covariance_var_B m)(undefined)(covariance_AC m)(undefined)(covariance_AB m)(undefined)(covariance_BC m)) = - ((tri_cross(undefined)(covariance_AC m)(undefined)(covariance_var_B m)(undefined)(covariance_AB m)(undefined)(covariance_BC m)) * (tri_cross(undefined)(covariance_AC m)(undefined)(covariance_var_B m)(undefined)(covariance_AB m)(undefined)(covariance_BC m))).
Proof.
  intro m.
  exact (trivariate_zero_right_determinant
    (covariance_var_A m) (covariance_var_C m) (covariance_var_B m) (covariance_AC m) (covariance_AB m) (covariance_BC m)).
Qed.

(**
 [triple_AC_given_B_zero_left_cross_nonzero_negative] (theorem) — A zero first residual with nonzero conditional cross-covariance forces negative determinant. This is the AC conditioned on B instantiation using the named test covariance coordinates.
 Mathematical meaning: A zero first residual with nonzero conditional cross-covariance forces negative determinant. This is the AC conditioned on B instantiation using the named test covariance coordinates. The result is used to audit conditional covariance or precision in a three-test score model.
 Exact checked proposition: forall m : TripleCovariance, 0 < (covariance_var_B m) -> (tri_left(undefined)(covariance_var_A m)(undefined)(covariance_var_B m)(undefined)(covariance_AB m)) = 0 -> (tri_cross(undefined)(covariance_AC m)(undefined)(covariance_var_B m)(undefined)(covariance_AB m)(undefined)(covariance_BC m)) <> 0 -> (tri_determinant(undefined)(covariance_var_A m)(undefined)(covariance_var_C m)(undefined)(covariance_var_B m)(undefined)(covariance_AC m)(undefined)(covariance_AB m)(undefined)(covariance_BC m)) < 0.
 Premises and side conditions: All scalar quantities are real. Strict conditioning variance and any determinant, residual or nonzero assumptions are explicit in the statement; no positive semidefinite matrix is silently assumed.
 Proof/definition method: Deduction from the exact trivariate Schur factorization using canonical real polynomial normalization, inequalities and elementary real algebra.
 Library reuse: Rocq standard Reals, Lra, Psatz and Ring, rather than a custom algebra solver or a duplicate probability-sum implementation.
 Boundary: Exact 3x3 covariance-candidate algebra; no continuous Gaussian conditional law, normal tail or empirical psychometric assertion is proved here.
*)
Theorem triple_AC_given_B_zero_left_cross_nonzero_negative :
  forall m : TripleCovariance, 0 < (covariance_var_B m) -> (tri_left(undefined)(covariance_var_A m)(undefined)(covariance_var_B m)(undefined)(covariance_AB m)) = 0 -> (tri_cross(undefined)(covariance_AC m)(undefined)(covariance_var_B m)(undefined)(covariance_AB m)(undefined)(covariance_BC m)) <> 0 -> (tri_determinant(undefined)(covariance_var_A m)(undefined)(covariance_var_C m)(undefined)(covariance_var_B m)(undefined)(covariance_AC m)(undefined)(covariance_AB m)(undefined)(covariance_BC m)) < 0.
Proof.
  intro m.
  exact (trivariate_zero_left_cross_nonzero_negative
    (covariance_var_A m) (covariance_var_C m) (covariance_var_B m) (covariance_AC m) (covariance_AB m) (covariance_BC m)).
Qed.

(**
 [triple_AC_given_B_zero_right_cross_nonzero_negative] (theorem) — A zero second residual with nonzero conditional cross-covariance forces negative determinant. This is the AC conditioned on B instantiation using the named test covariance coordinates.
 Mathematical meaning: A zero second residual with nonzero conditional cross-covariance forces negative determinant. This is the AC conditioned on B instantiation using the named test covariance coordinates. The result is used to audit conditional covariance or precision in a three-test score model.
 Exact checked proposition: forall m : TripleCovariance, 0 < (covariance_var_B m) -> (tri_right(undefined)(covariance_var_C m)(undefined)(covariance_var_B m)(undefined)(covariance_BC m)) = 0 -> (tri_cross(undefined)(covariance_AC m)(undefined)(covariance_var_B m)(undefined)(covariance_AB m)(undefined)(covariance_BC m)) <> 0 -> (tri_determinant(undefined)(covariance_var_A m)(undefined)(covariance_var_C m)(undefined)(covariance_var_B m)(undefined)(covariance_AC m)(undefined)(covariance_AB m)(undefined)(covariance_BC m)) < 0.
 Premises and side conditions: All scalar quantities are real. Strict conditioning variance and any determinant, residual or nonzero assumptions are explicit in the statement; no positive semidefinite matrix is silently assumed.
 Proof/definition method: Deduction from the exact trivariate Schur factorization using canonical real polynomial normalization, inequalities and elementary real algebra.
 Library reuse: Rocq standard Reals, Lra, Psatz and Ring, rather than a custom algebra solver or a duplicate probability-sum implementation.
 Boundary: Exact 3x3 covariance-candidate algebra; no continuous Gaussian conditional law, normal tail or empirical psychometric assertion is proved here.
*)
Theorem triple_AC_given_B_zero_right_cross_nonzero_negative :
  forall m : TripleCovariance, 0 < (covariance_var_B m) -> (tri_right(undefined)(covariance_var_C m)(undefined)(covariance_var_B m)(undefined)(covariance_BC m)) = 0 -> (tri_cross(undefined)(covariance_AC m)(undefined)(covariance_var_B m)(undefined)(covariance_AB m)(undefined)(covariance_BC m)) <> 0 -> (tri_determinant(undefined)(covariance_var_A m)(undefined)(covariance_var_C m)(undefined)(covariance_var_B m)(undefined)(covariance_AC m)(undefined)(covariance_AB m)(undefined)(covariance_BC m)) < 0.
Proof.
  intro m.
  exact (trivariate_zero_right_cross_nonzero_negative
    (covariance_var_A m) (covariance_var_C m) (covariance_var_B m) (covariance_AC m) (covariance_AB m) (covariance_BC m)).
Qed.

(**
 [triple_AC_given_B_zero_left_psd_forces_zero_cross] (theorem) — Under a nonnegative determinant, zero first residual forces conditional uncorrelatedness. This is the AC conditioned on B instantiation using the named test covariance coordinates.
 Mathematical meaning: Under a nonnegative determinant, zero first residual forces conditional uncorrelatedness. This is the AC conditioned on B instantiation using the named test covariance coordinates. The result is used to audit conditional covariance or precision in a three-test score model.
 Exact checked proposition: forall m : TripleCovariance, 0 < (covariance_var_B m) -> 0 <= (tri_determinant(undefined)(covariance_var_A m)(undefined)(covariance_var_C m)(undefined)(covariance_var_B m)(undefined)(covariance_AC m)(undefined)(covariance_AB m)(undefined)(covariance_BC m)) -> (tri_left(undefined)(covariance_var_A m)(undefined)(covariance_var_B m)(undefined)(covariance_AB m)) = 0 -> (tri_cross(undefined)(covariance_AC m)(undefined)(covariance_var_B m)(undefined)(covariance_AB m)(undefined)(covariance_BC m)) = 0.
 Premises and side conditions: All scalar quantities are real. Strict conditioning variance and any determinant, residual or nonzero assumptions are explicit in the statement; no positive semidefinite matrix is silently assumed.
 Proof/definition method: Deduction from the exact trivariate Schur factorization using canonical real polynomial normalization, inequalities and elementary real algebra.
 Library reuse: Rocq standard Reals, Lra, Psatz and Ring, rather than a custom algebra solver or a duplicate probability-sum implementation.
 Boundary: Exact 3x3 covariance-candidate algebra; no continuous Gaussian conditional law, normal tail or empirical psychometric assertion is proved here.
*)
Theorem triple_AC_given_B_zero_left_psd_forces_zero_cross :
  forall m : TripleCovariance, 0 < (covariance_var_B m) -> 0 <= (tri_determinant(undefined)(covariance_var_A m)(undefined)(covariance_var_C m)(undefined)(covariance_var_B m)(undefined)(covariance_AC m)(undefined)(covariance_AB m)(undefined)(covariance_BC m)) -> (tri_left(undefined)(covariance_var_A m)(undefined)(covariance_var_B m)(undefined)(covariance_AB m)) = 0 -> (tri_cross(undefined)(covariance_AC m)(undefined)(covariance_var_B m)(undefined)(covariance_AB m)(undefined)(covariance_BC m)) = 0.
Proof.
  intro m.
  exact (trivariate_zero_left_psd_forces_zero_cross
    (covariance_var_A m) (covariance_var_C m) (covariance_var_B m) (covariance_AC m) (covariance_AB m) (covariance_BC m)).
Qed.

(**
 [triple_AC_given_B_zero_right_psd_forces_zero_cross] (theorem) — Under a nonnegative determinant, zero second residual forces conditional uncorrelatedness. This is the AC conditioned on B instantiation using the named test covariance coordinates.
 Mathematical meaning: Under a nonnegative determinant, zero second residual forces conditional uncorrelatedness. This is the AC conditioned on B instantiation using the named test covariance coordinates. The result is used to audit conditional covariance or precision in a three-test score model.
 Exact checked proposition: forall m : TripleCovariance, 0 < (covariance_var_B m) -> 0 <= (tri_determinant(undefined)(covariance_var_A m)(undefined)(covariance_var_C m)(undefined)(covariance_var_B m)(undefined)(covariance_AC m)(undefined)(covariance_AB m)(undefined)(covariance_BC m)) -> (tri_right(undefined)(covariance_var_C m)(undefined)(covariance_var_B m)(undefined)(covariance_BC m)) = 0 -> (tri_cross(undefined)(covariance_AC m)(undefined)(covariance_var_B m)(undefined)(covariance_AB m)(undefined)(covariance_BC m)) = 0.
 Premises and side conditions: All scalar quantities are real. Strict conditioning variance and any determinant, residual or nonzero assumptions are explicit in the statement; no positive semidefinite matrix is silently assumed.
 Proof/definition method: Deduction from the exact trivariate Schur factorization using canonical real polynomial normalization, inequalities and elementary real algebra.
 Library reuse: Rocq standard Reals, Lra, Psatz and Ring, rather than a custom algebra solver or a duplicate probability-sum implementation.
 Boundary: Exact 3x3 covariance-candidate algebra; no continuous Gaussian conditional law, normal tail or empirical psychometric assertion is proved here.
*)
Theorem triple_AC_given_B_zero_right_psd_forces_zero_cross :
  forall m : TripleCovariance, 0 < (covariance_var_B m) -> 0 <= (tri_determinant(undefined)(covariance_var_A m)(undefined)(covariance_var_C m)(undefined)(covariance_var_B m)(undefined)(covariance_AC m)(undefined)(covariance_AB m)(undefined)(covariance_BC m)) -> (tri_right(undefined)(covariance_var_C m)(undefined)(covariance_var_B m)(undefined)(covariance_BC m)) = 0 -> (tri_cross(undefined)(covariance_AC m)(undefined)(covariance_var_B m)(undefined)(covariance_AB m)(undefined)(covariance_BC m)) = 0.
Proof.
  intro m.
  exact (trivariate_zero_right_psd_forces_zero_cross
    (covariance_var_A m) (covariance_var_C m) (covariance_var_B m) (covariance_AC m) (covariance_AB m) (covariance_BC m)).
Qed.

(**
 [triple_AC_given_B_positive_det_left_forces_right] (theorem) — Positive determinant and positive first residual force a positive second residual. This is the AC conditioned on B instantiation using the named test covariance coordinates.
 Mathematical meaning: Positive determinant and positive first residual force a positive second residual. This is the AC conditioned on B instantiation using the named test covariance coordinates. The result is used to audit conditional covariance or precision in a three-test score model.
 Exact checked proposition: forall m : TripleCovariance, 0 < (covariance_var_B m) -> 0 < (tri_determinant(undefined)(covariance_var_A m)(undefined)(covariance_var_C m)(undefined)(covariance_var_B m)(undefined)(covariance_AC m)(undefined)(covariance_AB m)(undefined)(covariance_BC m)) -> 0 < (tri_left(undefined)(covariance_var_A m)(undefined)(covariance_var_B m)(undefined)(covariance_AB m)) -> 0 < (tri_right(undefined)(covariance_var_C m)(undefined)(covariance_var_B m)(undefined)(covariance_BC m)).
 Premises and side conditions: All scalar quantities are real. Strict conditioning variance and any determinant, residual or nonzero assumptions are explicit in the statement; no positive semidefinite matrix is silently assumed.
 Proof/definition method: Deduction from the exact trivariate Schur factorization using canonical real polynomial normalization, inequalities and elementary real algebra.
 Library reuse: Rocq standard Reals, Lra, Psatz and Ring, rather than a custom algebra solver or a duplicate probability-sum implementation.
 Boundary: Exact 3x3 covariance-candidate algebra; no continuous Gaussian conditional law, normal tail or empirical psychometric assertion is proved here.
*)
Theorem triple_AC_given_B_positive_det_left_forces_right :
  forall m : TripleCovariance, 0 < (covariance_var_B m) -> 0 < (tri_determinant(undefined)(covariance_var_A m)(undefined)(covariance_var_C m)(undefined)(covariance_var_B m)(undefined)(covariance_AC m)(undefined)(covariance_AB m)(undefined)(covariance_BC m)) -> 0 < (tri_left(undefined)(covariance_var_A m)(undefined)(covariance_var_B m)(undefined)(covariance_AB m)) -> 0 < (tri_right(undefined)(covariance_var_C m)(undefined)(covariance_var_B m)(undefined)(covariance_BC m)).
Proof.
  intro m.
  exact (trivariate_positive_det_left_forces_right
    (covariance_var_A m) (covariance_var_C m) (covariance_var_B m) (covariance_AC m) (covariance_AB m) (covariance_BC m)).
Qed.

(**
 [triple_AC_given_B_positive_det_right_forces_left] (theorem) — Positive determinant and positive second residual force a positive first residual. This is the AC conditioned on B instantiation using the named test covariance coordinates.
 Mathematical meaning: Positive determinant and positive second residual force a positive first residual. This is the AC conditioned on B instantiation using the named test covariance coordinates. The result is used to audit conditional covariance or precision in a three-test score model.
 Exact checked proposition: forall m : TripleCovariance, 0 < (covariance_var_B m) -> 0 < (tri_determinant(undefined)(covariance_var_A m)(undefined)(covariance_var_C m)(undefined)(covariance_var_B m)(undefined)(covariance_AC m)(undefined)(covariance_AB m)(undefined)(covariance_BC m)) -> 0 < (tri_right(undefined)(covariance_var_C m)(undefined)(covariance_var_B m)(undefined)(covariance_BC m)) -> 0 < (tri_left(undefined)(covariance_var_A m)(undefined)(covariance_var_B m)(undefined)(covariance_AB m)).
 Premises and side conditions: All scalar quantities are real. Strict conditioning variance and any determinant, residual or nonzero assumptions are explicit in the statement; no positive semidefinite matrix is silently assumed.
 Proof/definition method: Deduction from the exact trivariate Schur factorization using canonical real polynomial normalization, inequalities and elementary real algebra.
 Library reuse: Rocq standard Reals, Lra, Psatz and Ring, rather than a custom algebra solver or a duplicate probability-sum implementation.
 Boundary: Exact 3x3 covariance-candidate algebra; no continuous Gaussian conditional law, normal tail or empirical psychometric assertion is proved here.
*)
Theorem triple_AC_given_B_positive_det_right_forces_left :
  forall m : TripleCovariance, 0 < (covariance_var_B m) -> 0 < (tri_determinant(undefined)(covariance_var_A m)(undefined)(covariance_var_C m)(undefined)(covariance_var_B m)(undefined)(covariance_AC m)(undefined)(covariance_AB m)(undefined)(covariance_BC m)) -> 0 < (tri_right(undefined)(covariance_var_C m)(undefined)(covariance_var_B m)(undefined)(covariance_BC m)) -> 0 < (tri_left(undefined)(covariance_var_A m)(undefined)(covariance_var_B m)(undefined)(covariance_AB m)).
Proof.
  intro m.
  exact (trivariate_positive_det_right_forces_left
    (covariance_var_A m) (covariance_var_C m) (covariance_var_B m) (covariance_AC m) (covariance_AB m) (covariance_BC m)).
Qed.

(**
 [triple_AC_given_B_nonnegative_det_left_forces_right] (theorem) — A nonnegative determinant and strict first residual positivity force nonnegative second residual. This is the AC conditioned on B instantiation using the named test covariance coordinates.
 Mathematical meaning: A nonnegative determinant and strict first residual positivity force nonnegative second residual. This is the AC conditioned on B instantiation using the named test covariance coordinates. The result is used to audit conditional covariance or precision in a three-test score model.
 Exact checked proposition: forall m : TripleCovariance, 0 < (covariance_var_B m) -> 0 <= (tri_determinant(undefined)(covariance_var_A m)(undefined)(covariance_var_C m)(undefined)(covariance_var_B m)(undefined)(covariance_AC m)(undefined)(covariance_AB m)(undefined)(covariance_BC m)) -> 0 < (tri_left(undefined)(covariance_var_A m)(undefined)(covariance_var_B m)(undefined)(covariance_AB m)) -> 0 <= (tri_right(undefined)(covariance_var_C m)(undefined)(covariance_var_B m)(undefined)(covariance_BC m)).
 Premises and side conditions: All scalar quantities are real. Strict conditioning variance and any determinant, residual or nonzero assumptions are explicit in the statement; no positive semidefinite matrix is silently assumed.
 Proof/definition method: Deduction from the exact trivariate Schur factorization using canonical real polynomial normalization, inequalities and elementary real algebra.
 Library reuse: Rocq standard Reals, Lra, Psatz and Ring, rather than a custom algebra solver or a duplicate probability-sum implementation.
 Boundary: Exact 3x3 covariance-candidate algebra; no continuous Gaussian conditional law, normal tail or empirical psychometric assertion is proved here.
*)
Theorem triple_AC_given_B_nonnegative_det_left_forces_right :
  forall m : TripleCovariance, 0 < (covariance_var_B m) -> 0 <= (tri_determinant(undefined)(covariance_var_A m)(undefined)(covariance_var_C m)(undefined)(covariance_var_B m)(undefined)(covariance_AC m)(undefined)(covariance_AB m)(undefined)(covariance_BC m)) -> 0 < (tri_left(undefined)(covariance_var_A m)(undefined)(covariance_var_B m)(undefined)(covariance_AB m)) -> 0 <= (tri_right(undefined)(covariance_var_C m)(undefined)(covariance_var_B m)(undefined)(covariance_BC m)).
Proof.
  intro m.
  exact (trivariate_nonnegative_det_left_forces_right
    (covariance_var_A m) (covariance_var_C m) (covariance_var_B m) (covariance_AC m) (covariance_AB m) (covariance_BC m)).
Qed.

(**
 [triple_AC_given_B_nonnegative_det_right_forces_left] (theorem) — A nonnegative determinant and strict second residual positivity force nonnegative first residual. This is the AC conditioned on B instantiation using the named test covariance coordinates.
 Mathematical meaning: A nonnegative determinant and strict second residual positivity force nonnegative first residual. This is the AC conditioned on B instantiation using the named test covariance coordinates. The result is used to audit conditional covariance or precision in a three-test score model.
 Exact checked proposition: forall m : TripleCovariance, 0 < (covariance_var_B m) -> 0 <= (tri_determinant(undefined)(covariance_var_A m)(undefined)(covariance_var_C m)(undefined)(covariance_var_B m)(undefined)(covariance_AC m)(undefined)(covariance_AB m)(undefined)(covariance_BC m)) -> 0 < (tri_right(undefined)(covariance_var_C m)(undefined)(covariance_var_B m)(undefined)(covariance_BC m)) -> 0 <= (tri_left(undefined)(covariance_var_A m)(undefined)(covariance_var_B m)(undefined)(covariance_AB m)).
 Premises and side conditions: All scalar quantities are real. Strict conditioning variance and any determinant, residual or nonzero assumptions are explicit in the statement; no positive semidefinite matrix is silently assumed.
 Proof/definition method: Deduction from the exact trivariate Schur factorization using canonical real polynomial normalization, inequalities and elementary real algebra.
 Library reuse: Rocq standard Reals, Lra, Psatz and Ring, rather than a custom algebra solver or a duplicate probability-sum implementation.
 Boundary: Exact 3x3 covariance-candidate algebra; no continuous Gaussian conditional law, normal tail or empirical psychometric assertion is proved here.
*)
Theorem triple_AC_given_B_nonnegative_det_right_forces_left :
  forall m : TripleCovariance, 0 < (covariance_var_B m) -> 0 <= (tri_determinant(undefined)(covariance_var_A m)(undefined)(covariance_var_C m)(undefined)(covariance_var_B m)(undefined)(covariance_AC m)(undefined)(covariance_AB m)(undefined)(covariance_BC m)) -> 0 < (tri_right(undefined)(covariance_var_C m)(undefined)(covariance_var_B m)(undefined)(covariance_BC m)) -> 0 <= (tri_left(undefined)(covariance_var_A m)(undefined)(covariance_var_B m)(undefined)(covariance_AB m)).
Proof.
  intro m.
  exact (trivariate_nonnegative_det_right_forces_left
    (covariance_var_A m) (covariance_var_C m) (covariance_var_B m) (covariance_AC m) (covariance_AB m) (covariance_BC m)).
Qed.

(**
 [triple_AC_given_B_positive_det_positive_product] (theorem) — A strictly positive determinant forces both Schur residual factors to have a positive product. This is the AC conditioned on B instantiation using the named test covariance coordinates.
 Mathematical meaning: A strictly positive determinant forces both Schur residual factors to have a positive product. This is the AC conditioned on B instantiation using the named test covariance coordinates. The result is used to audit conditional covariance or precision in a three-test score model.
 Exact checked proposition: forall m : TripleCovariance, 0 < (covariance_var_B m) -> 0 < (tri_determinant(undefined)(covariance_var_A m)(undefined)(covariance_var_C m)(undefined)(covariance_var_B m)(undefined)(covariance_AC m)(undefined)(covariance_AB m)(undefined)(covariance_BC m)) -> 0 < ((tri_left(undefined)(covariance_var_A m)(undefined)(covariance_var_B m)(undefined)(covariance_AB m)) * (tri_right(undefined)(covariance_var_C m)(undefined)(covariance_var_B m)(undefined)(covariance_BC m))).
 Premises and side conditions: All scalar quantities are real. Strict conditioning variance and any determinant, residual or nonzero assumptions are explicit in the statement; no positive semidefinite matrix is silently assumed.
 Proof/definition method: Deduction from the exact trivariate Schur factorization using canonical real polynomial normalization, inequalities and elementary real algebra.
 Library reuse: Rocq standard Reals, Lra, Psatz and Ring, rather than a custom algebra solver or a duplicate probability-sum implementation.
 Boundary: Exact 3x3 covariance-candidate algebra; no continuous Gaussian conditional law, normal tail or empirical psychometric assertion is proved here.
*)
Theorem triple_AC_given_B_positive_det_positive_product :
  forall m : TripleCovariance, 0 < (covariance_var_B m) -> 0 < (tri_determinant(undefined)(covariance_var_A m)(undefined)(covariance_var_C m)(undefined)(covariance_var_B m)(undefined)(covariance_AC m)(undefined)(covariance_AB m)(undefined)(covariance_BC m)) -> 0 < ((tri_left(undefined)(covariance_var_A m)(undefined)(covariance_var_B m)(undefined)(covariance_AB m)) * (tri_right(undefined)(covariance_var_C m)(undefined)(covariance_var_B m)(undefined)(covariance_BC m))).
Proof.
  intro m.
  exact (trivariate_positive_det_positive_product
    (covariance_var_A m) (covariance_var_C m) (covariance_var_B m) (covariance_AC m) (covariance_AB m) (covariance_BC m)).
Qed.

(**
 [triple_AC_given_B_nonnegative_det_nonnegative_product] (theorem) — A nonnegative determinant forces the Schur residual product to be nonnegative. This is the AC conditioned on B instantiation using the named test covariance coordinates.
 Mathematical meaning: A nonnegative determinant forces the Schur residual product to be nonnegative. This is the AC conditioned on B instantiation using the named test covariance coordinates. The result is used to audit conditional covariance or precision in a three-test score model.
 Exact checked proposition: forall m : TripleCovariance, 0 < (covariance_var_B m) -> 0 <= (tri_determinant(undefined)(covariance_var_A m)(undefined)(covariance_var_C m)(undefined)(covariance_var_B m)(undefined)(covariance_AC m)(undefined)(covariance_AB m)(undefined)(covariance_BC m)) -> 0 <= ((tri_left(undefined)(covariance_var_A m)(undefined)(covariance_var_B m)(undefined)(covariance_AB m)) * (tri_right(undefined)(covariance_var_C m)(undefined)(covariance_var_B m)(undefined)(covariance_BC m))).
 Premises and side conditions: All scalar quantities are real. Strict conditioning variance and any determinant, residual or nonzero assumptions are explicit in the statement; no positive semidefinite matrix is silently assumed.
 Proof/definition method: Deduction from the exact trivariate Schur factorization using canonical real polynomial normalization, inequalities and elementary real algebra.
 Library reuse: Rocq standard Reals, Lra, Psatz and Ring, rather than a custom algebra solver or a duplicate probability-sum implementation.
 Boundary: Exact 3x3 covariance-candidate algebra; no continuous Gaussian conditional law, normal tail or empirical psychometric assertion is proved here.
*)
Theorem triple_AC_given_B_nonnegative_det_nonnegative_product :
  forall m : TripleCovariance, 0 < (covariance_var_B m) -> 0 <= (tri_determinant(undefined)(covariance_var_A m)(undefined)(covariance_var_C m)(undefined)(covariance_var_B m)(undefined)(covariance_AC m)(undefined)(covariance_AB m)(undefined)(covariance_BC m)) -> 0 <= ((tri_left(undefined)(covariance_var_A m)(undefined)(covariance_var_B m)(undefined)(covariance_AB m)) * (tri_right(undefined)(covariance_var_C m)(undefined)(covariance_var_B m)(undefined)(covariance_BC m))).
Proof.
  intro m.
  exact (trivariate_nonnegative_det_nonnegative_product
    (covariance_var_A m) (covariance_var_C m) (covariance_var_B m) (covariance_AC m) (covariance_AB m) (covariance_BC m)).
Qed.

(**
 [triple_BC_given_A_factor] (theorem) — The exact three-variable Schur determinant factorization. This is the BC conditioned on A instantiation using the named test covariance coordinates.
 Mathematical meaning: The exact three-variable Schur determinant factorization. This is the BC conditioned on A instantiation using the named test covariance coordinates. The result is used to audit conditional covariance or precision in a three-test score model.
 Exact checked proposition: forall m : TripleCovariance, ((tri_left(undefined)(covariance_var_B m)(undefined)(covariance_var_A m)(undefined)(covariance_AB m)) * (tri_right(undefined)(covariance_var_C m)(undefined)(covariance_var_A m)(undefined)(covariance_AC m))) - ((tri_cross(undefined)(covariance_BC m)(undefined)(covariance_var_A m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)) * (tri_cross(undefined)(covariance_BC m)(undefined)(covariance_var_A m)(undefined)(covariance_AB m)(undefined)(covariance_AC m))) = (covariance_var_A m) * (tri_determinant(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_var_A m)(undefined)(covariance_BC m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)).
 Premises and side conditions: All scalar quantities are real. Strict conditioning variance and any determinant, residual or nonzero assumptions are explicit in the statement; no positive semidefinite matrix is silently assumed.
 Proof/definition method: Deduction from the exact trivariate Schur factorization using canonical real polynomial normalization, inequalities and elementary real algebra.
 Library reuse: Rocq standard Reals, Lra, Psatz and Ring, rather than a custom algebra solver or a duplicate probability-sum implementation.
 Boundary: Exact 3x3 covariance-candidate algebra; no continuous Gaussian conditional law, normal tail or empirical psychometric assertion is proved here.
*)
Theorem triple_BC_given_A_factor :
  forall m : TripleCovariance, ((tri_left(undefined)(covariance_var_B m)(undefined)(covariance_var_A m)(undefined)(covariance_AB m)) * (tri_right(undefined)(covariance_var_C m)(undefined)(covariance_var_A m)(undefined)(covariance_AC m))) - ((tri_cross(undefined)(covariance_BC m)(undefined)(covariance_var_A m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)) * (tri_cross(undefined)(covariance_BC m)(undefined)(covariance_var_A m)(undefined)(covariance_AB m)(undefined)(covariance_AC m))) = (covariance_var_A m) * (tri_determinant(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_var_A m)(undefined)(covariance_BC m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)).
Proof.
  intro m.
  exact (trivariate_factor
    (covariance_var_B m) (covariance_var_C m) (covariance_var_A m) (covariance_BC m) (covariance_AB m) (covariance_AC m)).
Qed.

(**
 [triple_BC_given_A_balance] (theorem) — The residual product is the sum of squared conditional cross-covariance and the determinant contribution. This is the BC conditioned on A instantiation using the named test covariance coordinates.
 Mathematical meaning: The residual product is the sum of squared conditional cross-covariance and the determinant contribution. This is the BC conditioned on A instantiation using the named test covariance coordinates. The result is used to audit conditional covariance or precision in a three-test score model.
 Exact checked proposition: forall m : TripleCovariance, ((tri_left(undefined)(covariance_var_B m)(undefined)(covariance_var_A m)(undefined)(covariance_AB m)) * (tri_right(undefined)(covariance_var_C m)(undefined)(covariance_var_A m)(undefined)(covariance_AC m))) = ((tri_cross(undefined)(covariance_BC m)(undefined)(covariance_var_A m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)) * (tri_cross(undefined)(covariance_BC m)(undefined)(covariance_var_A m)(undefined)(covariance_AB m)(undefined)(covariance_AC m))) + (covariance_var_A m) * (tri_determinant(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_var_A m)(undefined)(covariance_BC m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)).
 Premises and side conditions: All scalar quantities are real. Strict conditioning variance and any determinant, residual or nonzero assumptions are explicit in the statement; no positive semidefinite matrix is silently assumed.
 Proof/definition method: Deduction from the exact trivariate Schur factorization using canonical real polynomial normalization, inequalities and elementary real algebra.
 Library reuse: Rocq standard Reals, Lra, Psatz and Ring, rather than a custom algebra solver or a duplicate probability-sum implementation.
 Boundary: Exact 3x3 covariance-candidate algebra; no continuous Gaussian conditional law, normal tail or empirical psychometric assertion is proved here.
*)
Theorem triple_BC_given_A_balance :
  forall m : TripleCovariance, ((tri_left(undefined)(covariance_var_B m)(undefined)(covariance_var_A m)(undefined)(covariance_AB m)) * (tri_right(undefined)(covariance_var_C m)(undefined)(covariance_var_A m)(undefined)(covariance_AC m))) = ((tri_cross(undefined)(covariance_BC m)(undefined)(covariance_var_A m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)) * (tri_cross(undefined)(covariance_BC m)(undefined)(covariance_var_A m)(undefined)(covariance_AB m)(undefined)(covariance_AC m))) + (covariance_var_A m) * (tri_determinant(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_var_A m)(undefined)(covariance_BC m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)).
Proof.
  intro m.
  exact (trivariate_balance
    (covariance_var_B m) (covariance_var_C m) (covariance_var_A m) (covariance_BC m) (covariance_AB m) (covariance_AC m)).
Qed.

(**
 [triple_BC_given_A_singular_implies_tight] (theorem) — A zero trivariate determinant gives exact saturation of the residual covariance inequality. This is the BC conditioned on A instantiation using the named test covariance coordinates.
 Mathematical meaning: A zero trivariate determinant gives exact saturation of the residual covariance inequality. This is the BC conditioned on A instantiation using the named test covariance coordinates. The result is used to audit conditional covariance or precision in a three-test score model.
 Exact checked proposition: forall m : TripleCovariance, (tri_determinant(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_var_A m)(undefined)(covariance_BC m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)) = 0 -> ((tri_left(undefined)(covariance_var_B m)(undefined)(covariance_var_A m)(undefined)(covariance_AB m)) * (tri_right(undefined)(covariance_var_C m)(undefined)(covariance_var_A m)(undefined)(covariance_AC m))) = ((tri_cross(undefined)(covariance_BC m)(undefined)(covariance_var_A m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)) * (tri_cross(undefined)(covariance_BC m)(undefined)(covariance_var_A m)(undefined)(covariance_AB m)(undefined)(covariance_AC m))).
 Premises and side conditions: All scalar quantities are real. Strict conditioning variance and any determinant, residual or nonzero assumptions are explicit in the statement; no positive semidefinite matrix is silently assumed.
 Proof/definition method: Deduction from the exact trivariate Schur factorization using canonical real polynomial normalization, inequalities and elementary real algebra.
 Library reuse: Rocq standard Reals, Lra, Psatz and Ring, rather than a custom algebra solver or a duplicate probability-sum implementation.
 Boundary: Exact 3x3 covariance-candidate algebra; no continuous Gaussian conditional law, normal tail or empirical psychometric assertion is proved here.
*)
Theorem triple_BC_given_A_singular_implies_tight :
  forall m : TripleCovariance, (tri_determinant(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_var_A m)(undefined)(covariance_BC m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)) = 0 -> ((tri_left(undefined)(covariance_var_B m)(undefined)(covariance_var_A m)(undefined)(covariance_AB m)) * (tri_right(undefined)(covariance_var_C m)(undefined)(covariance_var_A m)(undefined)(covariance_AC m))) = ((tri_cross(undefined)(covariance_BC m)(undefined)(covariance_var_A m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)) * (tri_cross(undefined)(covariance_BC m)(undefined)(covariance_var_A m)(undefined)(covariance_AB m)(undefined)(covariance_AC m))).
Proof.
  intro m.
  exact (trivariate_singular_implies_tight
    (covariance_var_B m) (covariance_var_C m) (covariance_var_A m) (covariance_BC m) (covariance_AB m) (covariance_AC m)).
Qed.

(**
 [triple_BC_given_A_tight_iff_singular] (theorem) — For positive conditioning variance, tightness is equivalent to a zero determinant. This is the BC conditioned on A instantiation using the named test covariance coordinates.
 Mathematical meaning: For positive conditioning variance, tightness is equivalent to a zero determinant. This is the BC conditioned on A instantiation using the named test covariance coordinates. The result is used to audit conditional covariance or precision in a three-test score model.
 Exact checked proposition: forall m : TripleCovariance, 0 < (covariance_var_A m) -> (((tri_left(undefined)(covariance_var_B m)(undefined)(covariance_var_A m)(undefined)(covariance_AB m)) * (tri_right(undefined)(covariance_var_C m)(undefined)(covariance_var_A m)(undefined)(covariance_AC m))) = ((tri_cross(undefined)(covariance_BC m)(undefined)(covariance_var_A m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)) * (tri_cross(undefined)(covariance_BC m)(undefined)(covariance_var_A m)(undefined)(covariance_AB m)(undefined)(covariance_AC m))) <-> (tri_determinant(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_var_A m)(undefined)(covariance_BC m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)) = 0).
 Premises and side conditions: All scalar quantities are real. Strict conditioning variance and any determinant, residual or nonzero assumptions are explicit in the statement; no positive semidefinite matrix is silently assumed.
 Proof/definition method: Deduction from the exact trivariate Schur factorization using canonical real polynomial normalization, inequalities and elementary real algebra.
 Library reuse: Rocq standard Reals, Lra, Psatz and Ring, rather than a custom algebra solver or a duplicate probability-sum implementation.
 Boundary: Exact 3x3 covariance-candidate algebra; no continuous Gaussian conditional law, normal tail or empirical psychometric assertion is proved here.
*)
Theorem triple_BC_given_A_tight_iff_singular :
  forall m : TripleCovariance, 0 < (covariance_var_A m) -> (((tri_left(undefined)(covariance_var_B m)(undefined)(covariance_var_A m)(undefined)(covariance_AB m)) * (tri_right(undefined)(covariance_var_C m)(undefined)(covariance_var_A m)(undefined)(covariance_AC m))) = ((tri_cross(undefined)(covariance_BC m)(undefined)(covariance_var_A m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)) * (tri_cross(undefined)(covariance_BC m)(undefined)(covariance_var_A m)(undefined)(covariance_AB m)(undefined)(covariance_AC m))) <-> (tri_determinant(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_var_A m)(undefined)(covariance_BC m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)) = 0).
Proof.
  intro m.
  exact (trivariate_tight_iff_singular
    (covariance_var_B m) (covariance_var_C m) (covariance_var_A m) (covariance_BC m) (covariance_AB m) (covariance_AC m)).
Qed.

(**
 [triple_BC_given_A_positive_iff_strict] (theorem) — Positive determinant is equivalent to a strict Schur Cauchy-Schwarz gap. This is the BC conditioned on A instantiation using the named test covariance coordinates.
 Mathematical meaning: Positive determinant is equivalent to a strict Schur Cauchy-Schwarz gap. This is the BC conditioned on A instantiation using the named test covariance coordinates. The result is used to audit conditional covariance or precision in a three-test score model.
 Exact checked proposition: forall m : TripleCovariance, 0 < (covariance_var_A m) -> (0 < (tri_determinant(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_var_A m)(undefined)(covariance_BC m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)) <-> ((tri_cross(undefined)(covariance_BC m)(undefined)(covariance_var_A m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)) * (tri_cross(undefined)(covariance_BC m)(undefined)(covariance_var_A m)(undefined)(covariance_AB m)(undefined)(covariance_AC m))) < ((tri_left(undefined)(covariance_var_B m)(undefined)(covariance_var_A m)(undefined)(covariance_AB m)) * (tri_right(undefined)(covariance_var_C m)(undefined)(covariance_var_A m)(undefined)(covariance_AC m)))).
 Premises and side conditions: All scalar quantities are real. Strict conditioning variance and any determinant, residual or nonzero assumptions are explicit in the statement; no positive semidefinite matrix is silently assumed.
 Proof/definition method: Deduction from the exact trivariate Schur factorization using canonical real polynomial normalization, inequalities and elementary real algebra.
 Library reuse: Rocq standard Reals, Lra, Psatz and Ring, rather than a custom algebra solver or a duplicate probability-sum implementation.
 Boundary: Exact 3x3 covariance-candidate algebra; no continuous Gaussian conditional law, normal tail or empirical psychometric assertion is proved here.
*)
Theorem triple_BC_given_A_positive_iff_strict :
  forall m : TripleCovariance, 0 < (covariance_var_A m) -> (0 < (tri_determinant(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_var_A m)(undefined)(covariance_BC m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)) <-> ((tri_cross(undefined)(covariance_BC m)(undefined)(covariance_var_A m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)) * (tri_cross(undefined)(covariance_BC m)(undefined)(covariance_var_A m)(undefined)(covariance_AB m)(undefined)(covariance_AC m))) < ((tri_left(undefined)(covariance_var_B m)(undefined)(covariance_var_A m)(undefined)(covariance_AB m)) * (tri_right(undefined)(covariance_var_C m)(undefined)(covariance_var_A m)(undefined)(covariance_AC m)))).
Proof.
  intro m.
  exact (trivariate_positive_iff_strict
    (covariance_var_B m) (covariance_var_C m) (covariance_var_A m) (covariance_BC m) (covariance_AB m) (covariance_AC m)).
Qed.

(**
 [triple_BC_given_A_negative_iff_reverse] (theorem) — Negative determinant is equivalent to strict reversal of the Schur inequality. This is the BC conditioned on A instantiation using the named test covariance coordinates.
 Mathematical meaning: Negative determinant is equivalent to strict reversal of the Schur inequality. This is the BC conditioned on A instantiation using the named test covariance coordinates. The result is used to audit conditional covariance or precision in a three-test score model.
 Exact checked proposition: forall m : TripleCovariance, 0 < (covariance_var_A m) -> ((tri_determinant(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_var_A m)(undefined)(covariance_BC m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)) < 0 <-> ((tri_left(undefined)(covariance_var_B m)(undefined)(covariance_var_A m)(undefined)(covariance_AB m)) * (tri_right(undefined)(covariance_var_C m)(undefined)(covariance_var_A m)(undefined)(covariance_AC m))) < ((tri_cross(undefined)(covariance_BC m)(undefined)(covariance_var_A m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)) * (tri_cross(undefined)(covariance_BC m)(undefined)(covariance_var_A m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)))).
 Premises and side conditions: All scalar quantities are real. Strict conditioning variance and any determinant, residual or nonzero assumptions are explicit in the statement; no positive semidefinite matrix is silently assumed.
 Proof/definition method: Deduction from the exact trivariate Schur factorization using canonical real polynomial normalization, inequalities and elementary real algebra.
 Library reuse: Rocq standard Reals, Lra, Psatz and Ring, rather than a custom algebra solver or a duplicate probability-sum implementation.
 Boundary: Exact 3x3 covariance-candidate algebra; no continuous Gaussian conditional law, normal tail or empirical psychometric assertion is proved here.
*)
Theorem triple_BC_given_A_negative_iff_reverse :
  forall m : TripleCovariance, 0 < (covariance_var_A m) -> ((tri_determinant(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_var_A m)(undefined)(covariance_BC m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)) < 0 <-> ((tri_left(undefined)(covariance_var_B m)(undefined)(covariance_var_A m)(undefined)(covariance_AB m)) * (tri_right(undefined)(covariance_var_C m)(undefined)(covariance_var_A m)(undefined)(covariance_AC m))) < ((tri_cross(undefined)(covariance_BC m)(undefined)(covariance_var_A m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)) * (tri_cross(undefined)(covariance_BC m)(undefined)(covariance_var_A m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)))).
Proof.
  intro m.
  exact (trivariate_negative_iff_reverse
    (covariance_var_B m) (covariance_var_C m) (covariance_var_A m) (covariance_BC m) (covariance_AB m) (covariance_AC m)).
Qed.

(**
 [triple_BC_given_A_nonnegative_iff_weak] (theorem) — Nonnegative determinant is equivalent to the weak Schur Cauchy-Schwarz inequality. This is the BC conditioned on A instantiation using the named test covariance coordinates.
 Mathematical meaning: Nonnegative determinant is equivalent to the weak Schur Cauchy-Schwarz inequality. This is the BC conditioned on A instantiation using the named test covariance coordinates. The result is used to audit conditional covariance or precision in a three-test score model.
 Exact checked proposition: forall m : TripleCovariance, 0 < (covariance_var_A m) -> (0 <= (tri_determinant(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_var_A m)(undefined)(covariance_BC m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)) <-> ((tri_cross(undefined)(covariance_BC m)(undefined)(covariance_var_A m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)) * (tri_cross(undefined)(covariance_BC m)(undefined)(covariance_var_A m)(undefined)(covariance_AB m)(undefined)(covariance_AC m))) <= ((tri_left(undefined)(covariance_var_B m)(undefined)(covariance_var_A m)(undefined)(covariance_AB m)) * (tri_right(undefined)(covariance_var_C m)(undefined)(covariance_var_A m)(undefined)(covariance_AC m)))).
 Premises and side conditions: All scalar quantities are real. Strict conditioning variance and any determinant, residual or nonzero assumptions are explicit in the statement; no positive semidefinite matrix is silently assumed.
 Proof/definition method: Deduction from the exact trivariate Schur factorization using canonical real polynomial normalization, inequalities and elementary real algebra.
 Library reuse: Rocq standard Reals, Lra, Psatz and Ring, rather than a custom algebra solver or a duplicate probability-sum implementation.
 Boundary: Exact 3x3 covariance-candidate algebra; no continuous Gaussian conditional law, normal tail or empirical psychometric assertion is proved here.
*)
Theorem triple_BC_given_A_nonnegative_iff_weak :
  forall m : TripleCovariance, 0 < (covariance_var_A m) -> (0 <= (tri_determinant(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_var_A m)(undefined)(covariance_BC m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)) <-> ((tri_cross(undefined)(covariance_BC m)(undefined)(covariance_var_A m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)) * (tri_cross(undefined)(covariance_BC m)(undefined)(covariance_var_A m)(undefined)(covariance_AB m)(undefined)(covariance_AC m))) <= ((tri_left(undefined)(covariance_var_B m)(undefined)(covariance_var_A m)(undefined)(covariance_AB m)) * (tri_right(undefined)(covariance_var_C m)(undefined)(covariance_var_A m)(undefined)(covariance_AC m)))).
Proof.
  intro m.
  exact (trivariate_nonnegative_iff_weak
    (covariance_var_B m) (covariance_var_C m) (covariance_var_A m) (covariance_BC m) (covariance_AB m) (covariance_AC m)).
Qed.

(**
 [triple_BC_given_A_nonpositive_iff_reverse_weak] (theorem) — Nonpositive determinant is equivalent to the reverse weak residual inequality. This is the BC conditioned on A instantiation using the named test covariance coordinates.
 Mathematical meaning: Nonpositive determinant is equivalent to the reverse weak residual inequality. This is the BC conditioned on A instantiation using the named test covariance coordinates. The result is used to audit conditional covariance or precision in a three-test score model.
 Exact checked proposition: forall m : TripleCovariance, 0 < (covariance_var_A m) -> ((tri_determinant(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_var_A m)(undefined)(covariance_BC m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)) <= 0 <-> ((tri_left(undefined)(covariance_var_B m)(undefined)(covariance_var_A m)(undefined)(covariance_AB m)) * (tri_right(undefined)(covariance_var_C m)(undefined)(covariance_var_A m)(undefined)(covariance_AC m))) <= ((tri_cross(undefined)(covariance_BC m)(undefined)(covariance_var_A m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)) * (tri_cross(undefined)(covariance_BC m)(undefined)(covariance_var_A m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)))).
 Premises and side conditions: All scalar quantities are real. Strict conditioning variance and any determinant, residual or nonzero assumptions are explicit in the statement; no positive semidefinite matrix is silently assumed.
 Proof/definition method: Deduction from the exact trivariate Schur factorization using canonical real polynomial normalization, inequalities and elementary real algebra.
 Library reuse: Rocq standard Reals, Lra, Psatz and Ring, rather than a custom algebra solver or a duplicate probability-sum implementation.
 Boundary: Exact 3x3 covariance-candidate algebra; no continuous Gaussian conditional law, normal tail or empirical psychometric assertion is proved here.
*)
Theorem triple_BC_given_A_nonpositive_iff_reverse_weak :
  forall m : TripleCovariance, 0 < (covariance_var_A m) -> ((tri_determinant(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_var_A m)(undefined)(covariance_BC m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)) <= 0 <-> ((tri_left(undefined)(covariance_var_B m)(undefined)(covariance_var_A m)(undefined)(covariance_AB m)) * (tri_right(undefined)(covariance_var_C m)(undefined)(covariance_var_A m)(undefined)(covariance_AC m))) <= ((tri_cross(undefined)(covariance_BC m)(undefined)(covariance_var_A m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)) * (tri_cross(undefined)(covariance_BC m)(undefined)(covariance_var_A m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)))).
Proof.
  intro m.
  exact (trivariate_nonpositive_iff_reverse_weak
    (covariance_var_B m) (covariance_var_C m) (covariance_var_A m) (covariance_BC m) (covariance_AB m) (covariance_AC m)).
Qed.

(**
 [triple_BC_given_A_strict_positive_bound] (theorem) — A positive determinant forces a strict conditional Cauchy-Schwarz bound. This is the BC conditioned on A instantiation using the named test covariance coordinates.
 Mathematical meaning: A positive determinant forces a strict conditional Cauchy-Schwarz bound. This is the BC conditioned on A instantiation using the named test covariance coordinates. The result is used to audit conditional covariance or precision in a three-test score model.
 Exact checked proposition: forall m : TripleCovariance, 0 < (covariance_var_A m) -> 0 < (tri_determinant(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_var_A m)(undefined)(covariance_BC m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)) -> ((tri_cross(undefined)(covariance_BC m)(undefined)(covariance_var_A m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)) * (tri_cross(undefined)(covariance_BC m)(undefined)(covariance_var_A m)(undefined)(covariance_AB m)(undefined)(covariance_AC m))) < ((tri_left(undefined)(covariance_var_B m)(undefined)(covariance_var_A m)(undefined)(covariance_AB m)) * (tri_right(undefined)(covariance_var_C m)(undefined)(covariance_var_A m)(undefined)(covariance_AC m))).
 Premises and side conditions: All scalar quantities are real. Strict conditioning variance and any determinant, residual or nonzero assumptions are explicit in the statement; no positive semidefinite matrix is silently assumed.
 Proof/definition method: Deduction from the exact trivariate Schur factorization using canonical real polynomial normalization, inequalities and elementary real algebra.
 Library reuse: Rocq standard Reals, Lra, Psatz and Ring, rather than a custom algebra solver or a duplicate probability-sum implementation.
 Boundary: Exact 3x3 covariance-candidate algebra; no continuous Gaussian conditional law, normal tail or empirical psychometric assertion is proved here.
*)
Theorem triple_BC_given_A_strict_positive_bound :
  forall m : TripleCovariance, 0 < (covariance_var_A m) -> 0 < (tri_determinant(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_var_A m)(undefined)(covariance_BC m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)) -> ((tri_cross(undefined)(covariance_BC m)(undefined)(covariance_var_A m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)) * (tri_cross(undefined)(covariance_BC m)(undefined)(covariance_var_A m)(undefined)(covariance_AB m)(undefined)(covariance_AC m))) < ((tri_left(undefined)(covariance_var_B m)(undefined)(covariance_var_A m)(undefined)(covariance_AB m)) * (tri_right(undefined)(covariance_var_C m)(undefined)(covariance_var_A m)(undefined)(covariance_AC m))).
Proof.
  intro m.
  exact (trivariate_strict_positive_bound
    (covariance_var_B m) (covariance_var_C m) (covariance_var_A m) (covariance_BC m) (covariance_AB m) (covariance_AC m)).
Qed.

(**
 [triple_BC_given_A_strict_negative_bound] (theorem) — A negative determinant forces a strict reverse conditional Cauchy-Schwarz bound. This is the BC conditioned on A instantiation using the named test covariance coordinates.
 Mathematical meaning: A negative determinant forces a strict reverse conditional Cauchy-Schwarz bound. This is the BC conditioned on A instantiation using the named test covariance coordinates. The result is used to audit conditional covariance or precision in a three-test score model.
 Exact checked proposition: forall m : TripleCovariance, 0 < (covariance_var_A m) -> (tri_determinant(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_var_A m)(undefined)(covariance_BC m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)) < 0 -> ((tri_left(undefined)(covariance_var_B m)(undefined)(covariance_var_A m)(undefined)(covariance_AB m)) * (tri_right(undefined)(covariance_var_C m)(undefined)(covariance_var_A m)(undefined)(covariance_AC m))) < ((tri_cross(undefined)(covariance_BC m)(undefined)(covariance_var_A m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)) * (tri_cross(undefined)(covariance_BC m)(undefined)(covariance_var_A m)(undefined)(covariance_AB m)(undefined)(covariance_AC m))).
 Premises and side conditions: All scalar quantities are real. Strict conditioning variance and any determinant, residual or nonzero assumptions are explicit in the statement; no positive semidefinite matrix is silently assumed.
 Proof/definition method: Deduction from the exact trivariate Schur factorization using canonical real polynomial normalization, inequalities and elementary real algebra.
 Library reuse: Rocq standard Reals, Lra, Psatz and Ring, rather than a custom algebra solver or a duplicate probability-sum implementation.
 Boundary: Exact 3x3 covariance-candidate algebra; no continuous Gaussian conditional law, normal tail or empirical psychometric assertion is proved here.
*)
Theorem triple_BC_given_A_strict_negative_bound :
  forall m : TripleCovariance, 0 < (covariance_var_A m) -> (tri_determinant(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_var_A m)(undefined)(covariance_BC m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)) < 0 -> ((tri_left(undefined)(covariance_var_B m)(undefined)(covariance_var_A m)(undefined)(covariance_AB m)) * (tri_right(undefined)(covariance_var_C m)(undefined)(covariance_var_A m)(undefined)(covariance_AC m))) < ((tri_cross(undefined)(covariance_BC m)(undefined)(covariance_var_A m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)) * (tri_cross(undefined)(covariance_BC m)(undefined)(covariance_var_A m)(undefined)(covariance_AB m)(undefined)(covariance_AC m))).
Proof.
  intro m.
  exact (trivariate_strict_negative_bound
    (covariance_var_B m) (covariance_var_C m) (covariance_var_A m) (covariance_BC m) (covariance_AB m) (covariance_AC m)).
Qed.

(**
 [triple_BC_given_A_weak_positive_bound] (theorem) — A nonnegative determinant bounds squared conditional covariance by the residual product. This is the BC conditioned on A instantiation using the named test covariance coordinates.
 Mathematical meaning: A nonnegative determinant bounds squared conditional covariance by the residual product. This is the BC conditioned on A instantiation using the named test covariance coordinates. The result is used to audit conditional covariance or precision in a three-test score model.
 Exact checked proposition: forall m : TripleCovariance, 0 < (covariance_var_A m) -> 0 <= (tri_determinant(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_var_A m)(undefined)(covariance_BC m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)) -> ((tri_cross(undefined)(covariance_BC m)(undefined)(covariance_var_A m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)) * (tri_cross(undefined)(covariance_BC m)(undefined)(covariance_var_A m)(undefined)(covariance_AB m)(undefined)(covariance_AC m))) <= ((tri_left(undefined)(covariance_var_B m)(undefined)(covariance_var_A m)(undefined)(covariance_AB m)) * (tri_right(undefined)(covariance_var_C m)(undefined)(covariance_var_A m)(undefined)(covariance_AC m))).
 Premises and side conditions: All scalar quantities are real. Strict conditioning variance and any determinant, residual or nonzero assumptions are explicit in the statement; no positive semidefinite matrix is silently assumed.
 Proof/definition method: Deduction from the exact trivariate Schur factorization using canonical real polynomial normalization, inequalities and elementary real algebra.
 Library reuse: Rocq standard Reals, Lra, Psatz and Ring, rather than a custom algebra solver or a duplicate probability-sum implementation.
 Boundary: Exact 3x3 covariance-candidate algebra; no continuous Gaussian conditional law, normal tail or empirical psychometric assertion is proved here.
*)
Theorem triple_BC_given_A_weak_positive_bound :
  forall m : TripleCovariance, 0 < (covariance_var_A m) -> 0 <= (tri_determinant(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_var_A m)(undefined)(covariance_BC m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)) -> ((tri_cross(undefined)(covariance_BC m)(undefined)(covariance_var_A m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)) * (tri_cross(undefined)(covariance_BC m)(undefined)(covariance_var_A m)(undefined)(covariance_AB m)(undefined)(covariance_AC m))) <= ((tri_left(undefined)(covariance_var_B m)(undefined)(covariance_var_A m)(undefined)(covariance_AB m)) * (tri_right(undefined)(covariance_var_C m)(undefined)(covariance_var_A m)(undefined)(covariance_AC m))).
Proof.
  intro m.
  exact (trivariate_weak_positive_bound
    (covariance_var_B m) (covariance_var_C m) (covariance_var_A m) (covariance_BC m) (covariance_AB m) (covariance_AC m)).
Qed.

(**
 [triple_BC_given_A_weak_negative_bound] (theorem) — A nonpositive determinant bounds the residual product by squared conditional covariance. This is the BC conditioned on A instantiation using the named test covariance coordinates.
 Mathematical meaning: A nonpositive determinant bounds the residual product by squared conditional covariance. This is the BC conditioned on A instantiation using the named test covariance coordinates. The result is used to audit conditional covariance or precision in a three-test score model.
 Exact checked proposition: forall m : TripleCovariance, 0 < (covariance_var_A m) -> (tri_determinant(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_var_A m)(undefined)(covariance_BC m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)) <= 0 -> ((tri_left(undefined)(covariance_var_B m)(undefined)(covariance_var_A m)(undefined)(covariance_AB m)) * (tri_right(undefined)(covariance_var_C m)(undefined)(covariance_var_A m)(undefined)(covariance_AC m))) <= ((tri_cross(undefined)(covariance_BC m)(undefined)(covariance_var_A m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)) * (tri_cross(undefined)(covariance_BC m)(undefined)(covariance_var_A m)(undefined)(covariance_AB m)(undefined)(covariance_AC m))).
 Premises and side conditions: All scalar quantities are real. Strict conditioning variance and any determinant, residual or nonzero assumptions are explicit in the statement; no positive semidefinite matrix is silently assumed.
 Proof/definition method: Deduction from the exact trivariate Schur factorization using canonical real polynomial normalization, inequalities and elementary real algebra.
 Library reuse: Rocq standard Reals, Lra, Psatz and Ring, rather than a custom algebra solver or a duplicate probability-sum implementation.
 Boundary: Exact 3x3 covariance-candidate algebra; no continuous Gaussian conditional law, normal tail or empirical psychometric assertion is proved here.
*)
Theorem triple_BC_given_A_weak_negative_bound :
  forall m : TripleCovariance, 0 < (covariance_var_A m) -> (tri_determinant(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_var_A m)(undefined)(covariance_BC m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)) <= 0 -> ((tri_left(undefined)(covariance_var_B m)(undefined)(covariance_var_A m)(undefined)(covariance_AB m)) * (tri_right(undefined)(covariance_var_C m)(undefined)(covariance_var_A m)(undefined)(covariance_AC m))) <= ((tri_cross(undefined)(covariance_BC m)(undefined)(covariance_var_A m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)) * (tri_cross(undefined)(covariance_BC m)(undefined)(covariance_var_A m)(undefined)(covariance_AB m)(undefined)(covariance_AC m))).
Proof.
  intro m.
  exact (trivariate_weak_negative_bound
    (covariance_var_B m) (covariance_var_C m) (covariance_var_A m) (covariance_BC m) (covariance_AB m) (covariance_AC m)).
Qed.

(**
 [triple_BC_given_A_zero_cross_factor] (theorem) — Conditional uncorrelatedness makes the residual product exactly the conditioning variance times the determinant. This is the BC conditioned on A instantiation using the named test covariance coordinates.
 Mathematical meaning: Conditional uncorrelatedness makes the residual product exactly the conditioning variance times the determinant. This is the BC conditioned on A instantiation using the named test covariance coordinates. The result is used to audit conditional covariance or precision in a three-test score model.
 Exact checked proposition: forall m : TripleCovariance, (tri_cross(undefined)(covariance_BC m)(undefined)(covariance_var_A m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)) = 0 -> ((tri_left(undefined)(covariance_var_B m)(undefined)(covariance_var_A m)(undefined)(covariance_AB m)) * (tri_right(undefined)(covariance_var_C m)(undefined)(covariance_var_A m)(undefined)(covariance_AC m))) = (covariance_var_A m) * (tri_determinant(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_var_A m)(undefined)(covariance_BC m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)).
 Premises and side conditions: All scalar quantities are real. Strict conditioning variance and any determinant, residual or nonzero assumptions are explicit in the statement; no positive semidefinite matrix is silently assumed.
 Proof/definition method: Deduction from the exact trivariate Schur factorization using canonical real polynomial normalization, inequalities and elementary real algebra.
 Library reuse: Rocq standard Reals, Lra, Psatz and Ring, rather than a custom algebra solver or a duplicate probability-sum implementation.
 Boundary: Exact 3x3 covariance-candidate algebra; no continuous Gaussian conditional law, normal tail or empirical psychometric assertion is proved here.
*)
Theorem triple_BC_given_A_zero_cross_factor :
  forall m : TripleCovariance, (tri_cross(undefined)(covariance_BC m)(undefined)(covariance_var_A m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)) = 0 -> ((tri_left(undefined)(covariance_var_B m)(undefined)(covariance_var_A m)(undefined)(covariance_AB m)) * (tri_right(undefined)(covariance_var_C m)(undefined)(covariance_var_A m)(undefined)(covariance_AC m))) = (covariance_var_A m) * (tri_determinant(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_var_A m)(undefined)(covariance_BC m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)).
Proof.
  intro m.
  exact (trivariate_zero_cross_factor
    (covariance_var_B m) (covariance_var_C m) (covariance_var_A m) (covariance_BC m) (covariance_AB m) (covariance_AC m)).
Qed.

(**
 [triple_BC_given_A_zero_cross_positive_product] (theorem) — Conditional uncorrelatedness and positive determinant imply a strictly positive residual product. This is the BC conditioned on A instantiation using the named test covariance coordinates.
 Mathematical meaning: Conditional uncorrelatedness and positive determinant imply a strictly positive residual product. This is the BC conditioned on A instantiation using the named test covariance coordinates. The result is used to audit conditional covariance or precision in a three-test score model.
 Exact checked proposition: forall m : TripleCovariance, 0 < (covariance_var_A m) -> (tri_cross(undefined)(covariance_BC m)(undefined)(covariance_var_A m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)) = 0 -> 0 < (tri_determinant(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_var_A m)(undefined)(covariance_BC m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)) -> 0 < ((tri_left(undefined)(covariance_var_B m)(undefined)(covariance_var_A m)(undefined)(covariance_AB m)) * (tri_right(undefined)(covariance_var_C m)(undefined)(covariance_var_A m)(undefined)(covariance_AC m))).
 Premises and side conditions: All scalar quantities are real. Strict conditioning variance and any determinant, residual or nonzero assumptions are explicit in the statement; no positive semidefinite matrix is silently assumed.
 Proof/definition method: Deduction from the exact trivariate Schur factorization using canonical real polynomial normalization, inequalities and elementary real algebra.
 Library reuse: Rocq standard Reals, Lra, Psatz and Ring, rather than a custom algebra solver or a duplicate probability-sum implementation.
 Boundary: Exact 3x3 covariance-candidate algebra; no continuous Gaussian conditional law, normal tail or empirical psychometric assertion is proved here.
*)
Theorem triple_BC_given_A_zero_cross_positive_product :
  forall m : TripleCovariance, 0 < (covariance_var_A m) -> (tri_cross(undefined)(covariance_BC m)(undefined)(covariance_var_A m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)) = 0 -> 0 < (tri_determinant(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_var_A m)(undefined)(covariance_BC m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)) -> 0 < ((tri_left(undefined)(covariance_var_B m)(undefined)(covariance_var_A m)(undefined)(covariance_AB m)) * (tri_right(undefined)(covariance_var_C m)(undefined)(covariance_var_A m)(undefined)(covariance_AC m))).
Proof.
  intro m.
  exact (trivariate_zero_cross_positive_product
    (covariance_var_B m) (covariance_var_C m) (covariance_var_A m) (covariance_BC m) (covariance_AB m) (covariance_AC m)).
Qed.

(**
 [triple_BC_given_A_zero_cross_singular_product] (theorem) — Conditional uncorrelatedness with singular determinant forces at least one residual factor to vanish. This is the BC conditioned on A instantiation using the named test covariance coordinates.
 Mathematical meaning: Conditional uncorrelatedness with singular determinant forces at least one residual factor to vanish. This is the BC conditioned on A instantiation using the named test covariance coordinates. The result is used to audit conditional covariance or precision in a three-test score model.
 Exact checked proposition: forall m : TripleCovariance, (tri_cross(undefined)(covariance_BC m)(undefined)(covariance_var_A m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)) = 0 -> (tri_determinant(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_var_A m)(undefined)(covariance_BC m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)) = 0 -> ((tri_left(undefined)(covariance_var_B m)(undefined)(covariance_var_A m)(undefined)(covariance_AB m)) * (tri_right(undefined)(covariance_var_C m)(undefined)(covariance_var_A m)(undefined)(covariance_AC m))) = 0.
 Premises and side conditions: All scalar quantities are real. Strict conditioning variance and any determinant, residual or nonzero assumptions are explicit in the statement; no positive semidefinite matrix is silently assumed.
 Proof/definition method: Deduction from the exact trivariate Schur factorization using canonical real polynomial normalization, inequalities and elementary real algebra.
 Library reuse: Rocq standard Reals, Lra, Psatz and Ring, rather than a custom algebra solver or a duplicate probability-sum implementation.
 Boundary: Exact 3x3 covariance-candidate algebra; no continuous Gaussian conditional law, normal tail or empirical psychometric assertion is proved here.
*)
Theorem triple_BC_given_A_zero_cross_singular_product :
  forall m : TripleCovariance, (tri_cross(undefined)(covariance_BC m)(undefined)(covariance_var_A m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)) = 0 -> (tri_determinant(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_var_A m)(undefined)(covariance_BC m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)) = 0 -> ((tri_left(undefined)(covariance_var_B m)(undefined)(covariance_var_A m)(undefined)(covariance_AB m)) * (tri_right(undefined)(covariance_var_C m)(undefined)(covariance_var_A m)(undefined)(covariance_AC m))) = 0.
Proof.
  intro m.
  exact (trivariate_zero_cross_singular_product
    (covariance_var_B m) (covariance_var_C m) (covariance_var_A m) (covariance_BC m) (covariance_AB m) (covariance_AC m)).
Qed.

(**
 [triple_BC_given_A_zero_left_determinant] (theorem) — Vanishing first residual gives an exact negative-square identity. This is the BC conditioned on A instantiation using the named test covariance coordinates.
 Mathematical meaning: Vanishing first residual gives an exact negative-square identity. This is the BC conditioned on A instantiation using the named test covariance coordinates. The result is used to audit conditional covariance or precision in a three-test score model.
 Exact checked proposition: forall m : TripleCovariance, (tri_left(undefined)(covariance_var_B m)(undefined)(covariance_var_A m)(undefined)(covariance_AB m)) = 0 -> (covariance_var_A m) * (tri_determinant(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_var_A m)(undefined)(covariance_BC m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)) = - ((tri_cross(undefined)(covariance_BC m)(undefined)(covariance_var_A m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)) * (tri_cross(undefined)(covariance_BC m)(undefined)(covariance_var_A m)(undefined)(covariance_AB m)(undefined)(covariance_AC m))).
 Premises and side conditions: All scalar quantities are real. Strict conditioning variance and any determinant, residual or nonzero assumptions are explicit in the statement; no positive semidefinite matrix is silently assumed.
 Proof/definition method: Deduction from the exact trivariate Schur factorization using canonical real polynomial normalization, inequalities and elementary real algebra.
 Library reuse: Rocq standard Reals, Lra, Psatz and Ring, rather than a custom algebra solver or a duplicate probability-sum implementation.
 Boundary: Exact 3x3 covariance-candidate algebra; no continuous Gaussian conditional law, normal tail or empirical psychometric assertion is proved here.
*)
Theorem triple_BC_given_A_zero_left_determinant :
  forall m : TripleCovariance, (tri_left(undefined)(covariance_var_B m)(undefined)(covariance_var_A m)(undefined)(covariance_AB m)) = 0 -> (covariance_var_A m) * (tri_determinant(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_var_A m)(undefined)(covariance_BC m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)) = - ((tri_cross(undefined)(covariance_BC m)(undefined)(covariance_var_A m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)) * (tri_cross(undefined)(covariance_BC m)(undefined)(covariance_var_A m)(undefined)(covariance_AB m)(undefined)(covariance_AC m))).
Proof.
  intro m.
  exact (trivariate_zero_left_determinant
    (covariance_var_B m) (covariance_var_C m) (covariance_var_A m) (covariance_BC m) (covariance_AB m) (covariance_AC m)).
Qed.

(**
 [triple_BC_given_A_zero_right_determinant] (theorem) — Vanishing second residual gives an exact negative-square identity. This is the BC conditioned on A instantiation using the named test covariance coordinates.
 Mathematical meaning: Vanishing second residual gives an exact negative-square identity. This is the BC conditioned on A instantiation using the named test covariance coordinates. The result is used to audit conditional covariance or precision in a three-test score model.
 Exact checked proposition: forall m : TripleCovariance, (tri_right(undefined)(covariance_var_C m)(undefined)(covariance_var_A m)(undefined)(covariance_AC m)) = 0 -> (covariance_var_A m) * (tri_determinant(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_var_A m)(undefined)(covariance_BC m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)) = - ((tri_cross(undefined)(covariance_BC m)(undefined)(covariance_var_A m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)) * (tri_cross(undefined)(covariance_BC m)(undefined)(covariance_var_A m)(undefined)(covariance_AB m)(undefined)(covariance_AC m))).
 Premises and side conditions: All scalar quantities are real. Strict conditioning variance and any determinant, residual or nonzero assumptions are explicit in the statement; no positive semidefinite matrix is silently assumed.
 Proof/definition method: Deduction from the exact trivariate Schur factorization using canonical real polynomial normalization, inequalities and elementary real algebra.
 Library reuse: Rocq standard Reals, Lra, Psatz and Ring, rather than a custom algebra solver or a duplicate probability-sum implementation.
 Boundary: Exact 3x3 covariance-candidate algebra; no continuous Gaussian conditional law, normal tail or empirical psychometric assertion is proved here.
*)
Theorem triple_BC_given_A_zero_right_determinant :
  forall m : TripleCovariance, (tri_right(undefined)(covariance_var_C m)(undefined)(covariance_var_A m)(undefined)(covariance_AC m)) = 0 -> (covariance_var_A m) * (tri_determinant(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_var_A m)(undefined)(covariance_BC m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)) = - ((tri_cross(undefined)(covariance_BC m)(undefined)(covariance_var_A m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)) * (tri_cross(undefined)(covariance_BC m)(undefined)(covariance_var_A m)(undefined)(covariance_AB m)(undefined)(covariance_AC m))).
Proof.
  intro m.
  exact (trivariate_zero_right_determinant
    (covariance_var_B m) (covariance_var_C m) (covariance_var_A m) (covariance_BC m) (covariance_AB m) (covariance_AC m)).
Qed.

(**
 [triple_BC_given_A_zero_left_cross_nonzero_negative] (theorem) — A zero first residual with nonzero conditional cross-covariance forces negative determinant. This is the BC conditioned on A instantiation using the named test covariance coordinates.
 Mathematical meaning: A zero first residual with nonzero conditional cross-covariance forces negative determinant. This is the BC conditioned on A instantiation using the named test covariance coordinates. The result is used to audit conditional covariance or precision in a three-test score model.
 Exact checked proposition: forall m : TripleCovariance, 0 < (covariance_var_A m) -> (tri_left(undefined)(covariance_var_B m)(undefined)(covariance_var_A m)(undefined)(covariance_AB m)) = 0 -> (tri_cross(undefined)(covariance_BC m)(undefined)(covariance_var_A m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)) <> 0 -> (tri_determinant(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_var_A m)(undefined)(covariance_BC m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)) < 0.
 Premises and side conditions: All scalar quantities are real. Strict conditioning variance and any determinant, residual or nonzero assumptions are explicit in the statement; no positive semidefinite matrix is silently assumed.
 Proof/definition method: Deduction from the exact trivariate Schur factorization using canonical real polynomial normalization, inequalities and elementary real algebra.
 Library reuse: Rocq standard Reals, Lra, Psatz and Ring, rather than a custom algebra solver or a duplicate probability-sum implementation.
 Boundary: Exact 3x3 covariance-candidate algebra; no continuous Gaussian conditional law, normal tail or empirical psychometric assertion is proved here.
*)
Theorem triple_BC_given_A_zero_left_cross_nonzero_negative :
  forall m : TripleCovariance, 0 < (covariance_var_A m) -> (tri_left(undefined)(covariance_var_B m)(undefined)(covariance_var_A m)(undefined)(covariance_AB m)) = 0 -> (tri_cross(undefined)(covariance_BC m)(undefined)(covariance_var_A m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)) <> 0 -> (tri_determinant(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_var_A m)(undefined)(covariance_BC m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)) < 0.
Proof.
  intro m.
  exact (trivariate_zero_left_cross_nonzero_negative
    (covariance_var_B m) (covariance_var_C m) (covariance_var_A m) (covariance_BC m) (covariance_AB m) (covariance_AC m)).
Qed.

(**
 [triple_BC_given_A_zero_right_cross_nonzero_negative] (theorem) — A zero second residual with nonzero conditional cross-covariance forces negative determinant. This is the BC conditioned on A instantiation using the named test covariance coordinates.
 Mathematical meaning: A zero second residual with nonzero conditional cross-covariance forces negative determinant. This is the BC conditioned on A instantiation using the named test covariance coordinates. The result is used to audit conditional covariance or precision in a three-test score model.
 Exact checked proposition: forall m : TripleCovariance, 0 < (covariance_var_A m) -> (tri_right(undefined)(covariance_var_C m)(undefined)(covariance_var_A m)(undefined)(covariance_AC m)) = 0 -> (tri_cross(undefined)(covariance_BC m)(undefined)(covariance_var_A m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)) <> 0 -> (tri_determinant(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_var_A m)(undefined)(covariance_BC m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)) < 0.
 Premises and side conditions: All scalar quantities are real. Strict conditioning variance and any determinant, residual or nonzero assumptions are explicit in the statement; no positive semidefinite matrix is silently assumed.
 Proof/definition method: Deduction from the exact trivariate Schur factorization using canonical real polynomial normalization, inequalities and elementary real algebra.
 Library reuse: Rocq standard Reals, Lra, Psatz and Ring, rather than a custom algebra solver or a duplicate probability-sum implementation.
 Boundary: Exact 3x3 covariance-candidate algebra; no continuous Gaussian conditional law, normal tail or empirical psychometric assertion is proved here.
*)
Theorem triple_BC_given_A_zero_right_cross_nonzero_negative :
  forall m : TripleCovariance, 0 < (covariance_var_A m) -> (tri_right(undefined)(covariance_var_C m)(undefined)(covariance_var_A m)(undefined)(covariance_AC m)) = 0 -> (tri_cross(undefined)(covariance_BC m)(undefined)(covariance_var_A m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)) <> 0 -> (tri_determinant(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_var_A m)(undefined)(covariance_BC m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)) < 0.
Proof.
  intro m.
  exact (trivariate_zero_right_cross_nonzero_negative
    (covariance_var_B m) (covariance_var_C m) (covariance_var_A m) (covariance_BC m) (covariance_AB m) (covariance_AC m)).
Qed.

(**
 [triple_BC_given_A_zero_left_psd_forces_zero_cross] (theorem) — Under a nonnegative determinant, zero first residual forces conditional uncorrelatedness. This is the BC conditioned on A instantiation using the named test covariance coordinates.
 Mathematical meaning: Under a nonnegative determinant, zero first residual forces conditional uncorrelatedness. This is the BC conditioned on A instantiation using the named test covariance coordinates. The result is used to audit conditional covariance or precision in a three-test score model.
 Exact checked proposition: forall m : TripleCovariance, 0 < (covariance_var_A m) -> 0 <= (tri_determinant(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_var_A m)(undefined)(covariance_BC m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)) -> (tri_left(undefined)(covariance_var_B m)(undefined)(covariance_var_A m)(undefined)(covariance_AB m)) = 0 -> (tri_cross(undefined)(covariance_BC m)(undefined)(covariance_var_A m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)) = 0.
 Premises and side conditions: All scalar quantities are real. Strict conditioning variance and any determinant, residual or nonzero assumptions are explicit in the statement; no positive semidefinite matrix is silently assumed.
 Proof/definition method: Deduction from the exact trivariate Schur factorization using canonical real polynomial normalization, inequalities and elementary real algebra.
 Library reuse: Rocq standard Reals, Lra, Psatz and Ring, rather than a custom algebra solver or a duplicate probability-sum implementation.
 Boundary: Exact 3x3 covariance-candidate algebra; no continuous Gaussian conditional law, normal tail or empirical psychometric assertion is proved here.
*)
Theorem triple_BC_given_A_zero_left_psd_forces_zero_cross :
  forall m : TripleCovariance, 0 < (covariance_var_A m) -> 0 <= (tri_determinant(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_var_A m)(undefined)(covariance_BC m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)) -> (tri_left(undefined)(covariance_var_B m)(undefined)(covariance_var_A m)(undefined)(covariance_AB m)) = 0 -> (tri_cross(undefined)(covariance_BC m)(undefined)(covariance_var_A m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)) = 0.
Proof.
  intro m.
  exact (trivariate_zero_left_psd_forces_zero_cross
    (covariance_var_B m) (covariance_var_C m) (covariance_var_A m) (covariance_BC m) (covariance_AB m) (covariance_AC m)).
Qed.

(**
 [triple_BC_given_A_zero_right_psd_forces_zero_cross] (theorem) — Under a nonnegative determinant, zero second residual forces conditional uncorrelatedness. This is the BC conditioned on A instantiation using the named test covariance coordinates.
 Mathematical meaning: Under a nonnegative determinant, zero second residual forces conditional uncorrelatedness. This is the BC conditioned on A instantiation using the named test covariance coordinates. The result is used to audit conditional covariance or precision in a three-test score model.
 Exact checked proposition: forall m : TripleCovariance, 0 < (covariance_var_A m) -> 0 <= (tri_determinant(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_var_A m)(undefined)(covariance_BC m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)) -> (tri_right(undefined)(covariance_var_C m)(undefined)(covariance_var_A m)(undefined)(covariance_AC m)) = 0 -> (tri_cross(undefined)(covariance_BC m)(undefined)(covariance_var_A m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)) = 0.
 Premises and side conditions: All scalar quantities are real. Strict conditioning variance and any determinant, residual or nonzero assumptions are explicit in the statement; no positive semidefinite matrix is silently assumed.
 Proof/definition method: Deduction from the exact trivariate Schur factorization using canonical real polynomial normalization, inequalities and elementary real algebra.
 Library reuse: Rocq standard Reals, Lra, Psatz and Ring, rather than a custom algebra solver or a duplicate probability-sum implementation.
 Boundary: Exact 3x3 covariance-candidate algebra; no continuous Gaussian conditional law, normal tail or empirical psychometric assertion is proved here.
*)
Theorem triple_BC_given_A_zero_right_psd_forces_zero_cross :
  forall m : TripleCovariance, 0 < (covariance_var_A m) -> 0 <= (tri_determinant(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_var_A m)(undefined)(covariance_BC m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)) -> (tri_right(undefined)(covariance_var_C m)(undefined)(covariance_var_A m)(undefined)(covariance_AC m)) = 0 -> (tri_cross(undefined)(covariance_BC m)(undefined)(covariance_var_A m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)) = 0.
Proof.
  intro m.
  exact (trivariate_zero_right_psd_forces_zero_cross
    (covariance_var_B m) (covariance_var_C m) (covariance_var_A m) (covariance_BC m) (covariance_AB m) (covariance_AC m)).
Qed.

(**
 [triple_BC_given_A_positive_det_left_forces_right] (theorem) — Positive determinant and positive first residual force a positive second residual. This is the BC conditioned on A instantiation using the named test covariance coordinates.
 Mathematical meaning: Positive determinant and positive first residual force a positive second residual. This is the BC conditioned on A instantiation using the named test covariance coordinates. The result is used to audit conditional covariance or precision in a three-test score model.
 Exact checked proposition: forall m : TripleCovariance, 0 < (covariance_var_A m) -> 0 < (tri_determinant(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_var_A m)(undefined)(covariance_BC m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)) -> 0 < (tri_left(undefined)(covariance_var_B m)(undefined)(covariance_var_A m)(undefined)(covariance_AB m)) -> 0 < (tri_right(undefined)(covariance_var_C m)(undefined)(covariance_var_A m)(undefined)(covariance_AC m)).
 Premises and side conditions: All scalar quantities are real. Strict conditioning variance and any determinant, residual or nonzero assumptions are explicit in the statement; no positive semidefinite matrix is silently assumed.
 Proof/definition method: Deduction from the exact trivariate Schur factorization using canonical real polynomial normalization, inequalities and elementary real algebra.
 Library reuse: Rocq standard Reals, Lra, Psatz and Ring, rather than a custom algebra solver or a duplicate probability-sum implementation.
 Boundary: Exact 3x3 covariance-candidate algebra; no continuous Gaussian conditional law, normal tail or empirical psychometric assertion is proved here.
*)
Theorem triple_BC_given_A_positive_det_left_forces_right :
  forall m : TripleCovariance, 0 < (covariance_var_A m) -> 0 < (tri_determinant(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_var_A m)(undefined)(covariance_BC m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)) -> 0 < (tri_left(undefined)(covariance_var_B m)(undefined)(covariance_var_A m)(undefined)(covariance_AB m)) -> 0 < (tri_right(undefined)(covariance_var_C m)(undefined)(covariance_var_A m)(undefined)(covariance_AC m)).
Proof.
  intro m.
  exact (trivariate_positive_det_left_forces_right
    (covariance_var_B m) (covariance_var_C m) (covariance_var_A m) (covariance_BC m) (covariance_AB m) (covariance_AC m)).
Qed.

(**
 [triple_BC_given_A_positive_det_right_forces_left] (theorem) — Positive determinant and positive second residual force a positive first residual. This is the BC conditioned on A instantiation using the named test covariance coordinates.
 Mathematical meaning: Positive determinant and positive second residual force a positive first residual. This is the BC conditioned on A instantiation using the named test covariance coordinates. The result is used to audit conditional covariance or precision in a three-test score model.
 Exact checked proposition: forall m : TripleCovariance, 0 < (covariance_var_A m) -> 0 < (tri_determinant(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_var_A m)(undefined)(covariance_BC m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)) -> 0 < (tri_right(undefined)(covariance_var_C m)(undefined)(covariance_var_A m)(undefined)(covariance_AC m)) -> 0 < (tri_left(undefined)(covariance_var_B m)(undefined)(covariance_var_A m)(undefined)(covariance_AB m)).
 Premises and side conditions: All scalar quantities are real. Strict conditioning variance and any determinant, residual or nonzero assumptions are explicit in the statement; no positive semidefinite matrix is silently assumed.
 Proof/definition method: Deduction from the exact trivariate Schur factorization using canonical real polynomial normalization, inequalities and elementary real algebra.
 Library reuse: Rocq standard Reals, Lra, Psatz and Ring, rather than a custom algebra solver or a duplicate probability-sum implementation.
 Boundary: Exact 3x3 covariance-candidate algebra; no continuous Gaussian conditional law, normal tail or empirical psychometric assertion is proved here.
*)
Theorem triple_BC_given_A_positive_det_right_forces_left :
  forall m : TripleCovariance, 0 < (covariance_var_A m) -> 0 < (tri_determinant(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_var_A m)(undefined)(covariance_BC m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)) -> 0 < (tri_right(undefined)(covariance_var_C m)(undefined)(covariance_var_A m)(undefined)(covariance_AC m)) -> 0 < (tri_left(undefined)(covariance_var_B m)(undefined)(covariance_var_A m)(undefined)(covariance_AB m)).
Proof.
  intro m.
  exact (trivariate_positive_det_right_forces_left
    (covariance_var_B m) (covariance_var_C m) (covariance_var_A m) (covariance_BC m) (covariance_AB m) (covariance_AC m)).
Qed.

(**
 [triple_BC_given_A_nonnegative_det_left_forces_right] (theorem) — A nonnegative determinant and strict first residual positivity force nonnegative second residual. This is the BC conditioned on A instantiation using the named test covariance coordinates.
 Mathematical meaning: A nonnegative determinant and strict first residual positivity force nonnegative second residual. This is the BC conditioned on A instantiation using the named test covariance coordinates. The result is used to audit conditional covariance or precision in a three-test score model.
 Exact checked proposition: forall m : TripleCovariance, 0 < (covariance_var_A m) -> 0 <= (tri_determinant(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_var_A m)(undefined)(covariance_BC m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)) -> 0 < (tri_left(undefined)(covariance_var_B m)(undefined)(covariance_var_A m)(undefined)(covariance_AB m)) -> 0 <= (tri_right(undefined)(covariance_var_C m)(undefined)(covariance_var_A m)(undefined)(covariance_AC m)).
 Premises and side conditions: All scalar quantities are real. Strict conditioning variance and any determinant, residual or nonzero assumptions are explicit in the statement; no positive semidefinite matrix is silently assumed.
 Proof/definition method: Deduction from the exact trivariate Schur factorization using canonical real polynomial normalization, inequalities and elementary real algebra.
 Library reuse: Rocq standard Reals, Lra, Psatz and Ring, rather than a custom algebra solver or a duplicate probability-sum implementation.
 Boundary: Exact 3x3 covariance-candidate algebra; no continuous Gaussian conditional law, normal tail or empirical psychometric assertion is proved here.
*)
Theorem triple_BC_given_A_nonnegative_det_left_forces_right :
  forall m : TripleCovariance, 0 < (covariance_var_A m) -> 0 <= (tri_determinant(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_var_A m)(undefined)(covariance_BC m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)) -> 0 < (tri_left(undefined)(covariance_var_B m)(undefined)(covariance_var_A m)(undefined)(covariance_AB m)) -> 0 <= (tri_right(undefined)(covariance_var_C m)(undefined)(covariance_var_A m)(undefined)(covariance_AC m)).
Proof.
  intro m.
  exact (trivariate_nonnegative_det_left_forces_right
    (covariance_var_B m) (covariance_var_C m) (covariance_var_A m) (covariance_BC m) (covariance_AB m) (covariance_AC m)).
Qed.

(**
 [triple_BC_given_A_nonnegative_det_right_forces_left] (theorem) — A nonnegative determinant and strict second residual positivity force nonnegative first residual. This is the BC conditioned on A instantiation using the named test covariance coordinates.
 Mathematical meaning: A nonnegative determinant and strict second residual positivity force nonnegative first residual. This is the BC conditioned on A instantiation using the named test covariance coordinates. The result is used to audit conditional covariance or precision in a three-test score model.
 Exact checked proposition: forall m : TripleCovariance, 0 < (covariance_var_A m) -> 0 <= (tri_determinant(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_var_A m)(undefined)(covariance_BC m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)) -> 0 < (tri_right(undefined)(covariance_var_C m)(undefined)(covariance_var_A m)(undefined)(covariance_AC m)) -> 0 <= (tri_left(undefined)(covariance_var_B m)(undefined)(covariance_var_A m)(undefined)(covariance_AB m)).
 Premises and side conditions: All scalar quantities are real. Strict conditioning variance and any determinant, residual or nonzero assumptions are explicit in the statement; no positive semidefinite matrix is silently assumed.
 Proof/definition method: Deduction from the exact trivariate Schur factorization using canonical real polynomial normalization, inequalities and elementary real algebra.
 Library reuse: Rocq standard Reals, Lra, Psatz and Ring, rather than a custom algebra solver or a duplicate probability-sum implementation.
 Boundary: Exact 3x3 covariance-candidate algebra; no continuous Gaussian conditional law, normal tail or empirical psychometric assertion is proved here.
*)
Theorem triple_BC_given_A_nonnegative_det_right_forces_left :
  forall m : TripleCovariance, 0 < (covariance_var_A m) -> 0 <= (tri_determinant(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_var_A m)(undefined)(covariance_BC m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)) -> 0 < (tri_right(undefined)(covariance_var_C m)(undefined)(covariance_var_A m)(undefined)(covariance_AC m)) -> 0 <= (tri_left(undefined)(covariance_var_B m)(undefined)(covariance_var_A m)(undefined)(covariance_AB m)).
Proof.
  intro m.
  exact (trivariate_nonnegative_det_right_forces_left
    (covariance_var_B m) (covariance_var_C m) (covariance_var_A m) (covariance_BC m) (covariance_AB m) (covariance_AC m)).
Qed.

(**
 [triple_BC_given_A_positive_det_positive_product] (theorem) — A strictly positive determinant forces both Schur residual factors to have a positive product. This is the BC conditioned on A instantiation using the named test covariance coordinates.
 Mathematical meaning: A strictly positive determinant forces both Schur residual factors to have a positive product. This is the BC conditioned on A instantiation using the named test covariance coordinates. The result is used to audit conditional covariance or precision in a three-test score model.
 Exact checked proposition: forall m : TripleCovariance, 0 < (covariance_var_A m) -> 0 < (tri_determinant(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_var_A m)(undefined)(covariance_BC m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)) -> 0 < ((tri_left(undefined)(covariance_var_B m)(undefined)(covariance_var_A m)(undefined)(covariance_AB m)) * (tri_right(undefined)(covariance_var_C m)(undefined)(covariance_var_A m)(undefined)(covariance_AC m))).
 Premises and side conditions: All scalar quantities are real. Strict conditioning variance and any determinant, residual or nonzero assumptions are explicit in the statement; no positive semidefinite matrix is silently assumed.
 Proof/definition method: Deduction from the exact trivariate Schur factorization using canonical real polynomial normalization, inequalities and elementary real algebra.
 Library reuse: Rocq standard Reals, Lra, Psatz and Ring, rather than a custom algebra solver or a duplicate probability-sum implementation.
 Boundary: Exact 3x3 covariance-candidate algebra; no continuous Gaussian conditional law, normal tail or empirical psychometric assertion is proved here.
*)
Theorem triple_BC_given_A_positive_det_positive_product :
  forall m : TripleCovariance, 0 < (covariance_var_A m) -> 0 < (tri_determinant(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_var_A m)(undefined)(covariance_BC m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)) -> 0 < ((tri_left(undefined)(covariance_var_B m)(undefined)(covariance_var_A m)(undefined)(covariance_AB m)) * (tri_right(undefined)(covariance_var_C m)(undefined)(covariance_var_A m)(undefined)(covariance_AC m))).
Proof.
  intro m.
  exact (trivariate_positive_det_positive_product
    (covariance_var_B m) (covariance_var_C m) (covariance_var_A m) (covariance_BC m) (covariance_AB m) (covariance_AC m)).
Qed.

(**
 [triple_BC_given_A_nonnegative_det_nonnegative_product] (theorem) — A nonnegative determinant forces the Schur residual product to be nonnegative. This is the BC conditioned on A instantiation using the named test covariance coordinates.
 Mathematical meaning: A nonnegative determinant forces the Schur residual product to be nonnegative. This is the BC conditioned on A instantiation using the named test covariance coordinates. The result is used to audit conditional covariance or precision in a three-test score model.
 Exact checked proposition: forall m : TripleCovariance, 0 < (covariance_var_A m) -> 0 <= (tri_determinant(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_var_A m)(undefined)(covariance_BC m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)) -> 0 <= ((tri_left(undefined)(covariance_var_B m)(undefined)(covariance_var_A m)(undefined)(covariance_AB m)) * (tri_right(undefined)(covariance_var_C m)(undefined)(covariance_var_A m)(undefined)(covariance_AC m))).
 Premises and side conditions: All scalar quantities are real. Strict conditioning variance and any determinant, residual or nonzero assumptions are explicit in the statement; no positive semidefinite matrix is silently assumed.
 Proof/definition method: Deduction from the exact trivariate Schur factorization using canonical real polynomial normalization, inequalities and elementary real algebra.
 Library reuse: Rocq standard Reals, Lra, Psatz and Ring, rather than a custom algebra solver or a duplicate probability-sum implementation.
 Boundary: Exact 3x3 covariance-candidate algebra; no continuous Gaussian conditional law, normal tail or empirical psychometric assertion is proved here.
*)
Theorem triple_BC_given_A_nonnegative_det_nonnegative_product :
  forall m : TripleCovariance, 0 < (covariance_var_A m) -> 0 <= (tri_determinant(undefined)(covariance_var_B m)(undefined)(covariance_var_C m)(undefined)(covariance_var_A m)(undefined)(covariance_BC m)(undefined)(covariance_AB m)(undefined)(covariance_AC m)) -> 0 <= ((tri_left(undefined)(covariance_var_B m)(undefined)(covariance_var_A m)(undefined)(covariance_AB m)) * (tri_right(undefined)(covariance_var_C m)(undefined)(covariance_var_A m)(undefined)(covariance_AC m))).
Proof.
  intro m.
  exact (trivariate_nonnegative_det_nonnegative_product
    (covariance_var_B m) (covariance_var_C m) (covariance_var_A m) (covariance_BC m) (covariance_AB m) (covariance_AC m)).
Qed.

