(** Module: Admissions.v
   Purpose: Two-event admissions model and checked four-cell algebra.
   Formalizes joint, exclusive, and complementary admissions-event probabilities, conditionals, independence criteria, and union bounds.
   Mathematical representation: The four nonnegative cells joint, only_A, only_B and neither sum to one; each reported probability is a derived function of those cells.
   Explicit hypotheses: Conditional probabilities require positive denominators; independence is never assumed unless encoded in a premise or explicit recurrence.
   Library use: Stdlib.Reals, Lra, Psatz and PeanoNat.
   Limitations: Results are exact finite event algebra, not Gaussian admission models or estimates from empirical samples.
   Proof documentation: Every public and helper declaration below has its
   own statement, hypothesis, proof-approach, and scope commentary.
   Reproduction: rocq compile Admissions.v (after imported local modules);
   see rocq/README.md and rocq/LIBRARY_AUDIT.md for dependency order,
   checked-claim mapping, and library audit. All results are Rocq-kernel
   checked; no unchecked evidence is created by comments.
 *)
(* Event algebra from analyses/towers-multiple-test-admissions/analysis.md.
   A finite, four-cell probability space makes the logical assumptions explicit:
   A and B partition into both, A-only, B-only, and neither.  No normal
   distribution, independence or unproved probability axioms are imported. *)
From Stdlib Require Import Reals Lra Psatz Arith.PeanoNat.
Open Scope R_scope.

(* Reuse Stdlib.Reals quotient, inverse, and product sign lemmas. *)

(**
   [TwoEventModel] (record).
   Meaning: Gives a precise computational or algebraic interpretation of the
   named construction or assertion.
   Formal construction: Type := { joint : R; only_A : R; only_B : R; neither :
   R; joint_nonnegative : 0 <= joint; only_A_nonnegative : 0 <= only_A;
   only_B_nonnegative : 0 <= only_B; neither_nonnegative : 0 <= neither;
   cells_sum_to_one : joint + only_A + only_B + neither = 1 }. Definition p_A
   (m : TwoEventModel) : R := joint m + only_A m. D...
   Hypotheses: Requires the normalized nonnegative four-cell record where shown
   in the statement; all other constraints remain explicit.
   Implementation: application of already-proved lemmas; notably
   Rplus_le_le_0_compat., joint_nonnegative., only_A_nonnegative..
   Library discipline: Stdlib.Reals, Lra, Psatz and PeanoNat.
   Scope: Results are exact finite event algebra, not Gaussian admission models
   or estimates from empirical samples.
 *)
Record TwoEventModel : Type := {
  joint : R;
  only_A : R;
  only_B : R;
  neither : R;
  joint_nonnegative : 0 <= joint;
  only_A_nonnegative : 0 <= only_A;
  only_B_nonnegative : 0 <= only_B;
  neither_nonnegative : 0 <= neither;
  cells_sum_to_one : joint + only_A + only_B + neither = 1
}.

(**
   [p_A] (definition).
   Meaning: Gives a precise computational or algebraic interpretation of the
   named construction or assertion.
   Formal construction: (m : TwoEventModel) : R := joint m + only_A m.
   Hypotheses: Requires the normalized nonnegative four-cell record where shown
   in the statement; all other constraints remain explicit.
   Implementation: application of already-proved lemmas; notably
   Rplus_le_le_0_compat., joint_nonnegative., only_A_nonnegative..
   Library discipline: Stdlib.Reals, Lra, Psatz and PeanoNat.
   Scope: Results are exact finite event algebra, not Gaussian admission models
   or estimates from empirical samples.
 *)
Definition p_A (m : TwoEventModel) : R := joint m + only_A m.
(**
   [p_B] (definition).
   Meaning: Gives a precise computational or algebraic interpretation of the
   named construction or assertion.
   Formal construction: (m : TwoEventModel) : R := joint m + only_B m.
   Hypotheses: Requires the normalized nonnegative four-cell record where shown
   in the statement; all other constraints remain explicit.
   Implementation: application of already-proved lemmas; notably
   Rplus_le_le_0_compat., joint_nonnegative., only_A_nonnegative..
   Library discipline: Stdlib.Reals, Lra, Psatz and PeanoNat.
   Scope: Results are exact finite event algebra, not Gaussian admission models
   or estimates from empirical samples.
 *)
Definition p_B (m : TwoEventModel) : R := joint m + only_B m.
(**
   [p_both] (definition).
   Meaning: Controls union/intersection mass for Boolean events through finite
   probability algebra.
   Formal construction: (m : TwoEventModel) : R := joint m.
   Hypotheses: Requires the normalized nonnegative four-cell record where shown
   in the statement; all other constraints remain explicit.
   Implementation: application of already-proved lemmas; notably
   Rplus_le_le_0_compat., joint_nonnegative., only_A_nonnegative..
   Library discipline: Stdlib.Reals, Lra, Psatz and PeanoNat.
   Scope: Results are exact finite event algebra, not Gaussian admission models
   or estimates from empirical samples.
 *)
Definition p_both (m : TwoEventModel) : R := joint m.
(**
   [p_either] (definition).
   Meaning: Controls union/intersection mass for Boolean events through finite
   probability algebra.
   Formal construction: (m : TwoEventModel) : R := joint m + only_A m + only_B
   m.
   Hypotheses: Requires the normalized nonnegative four-cell record where shown
   in the statement; all other constraints remain explicit.
   Implementation: application of already-proved lemmas; notably
   Rplus_le_le_0_compat., joint_nonnegative., only_A_nonnegative..
   Library discipline: Stdlib.Reals, Lra, Psatz and PeanoNat.
   Scope: Results are exact finite event algebra, not Gaussian admission models
   or estimates from empirical samples.
 *)
Definition p_either (m : TwoEventModel) : R :=
  joint m + only_A m + only_B m.
(**
   [p_exactly_one] (definition).
   Meaning: Gives a precise computational or algebraic interpretation of the
   named construction or assertion.
   Formal construction: (m : TwoEventModel) : R := only_A m + only_B m.
   Hypotheses: Requires the normalized nonnegative four-cell record where shown
   in the statement; all other constraints remain explicit.
   Implementation: application of already-proved lemmas; notably
   Rplus_le_le_0_compat., joint_nonnegative., only_A_nonnegative..
   Library discipline: Stdlib.Reals, Lra, Psatz and PeanoNat.
   Scope: Results are exact finite event algebra, not Gaussian admission models
   or estimates from empirical samples.
 *)
Definition p_exactly_one (m : TwoEventModel) : R :=
  only_A m + only_B m.

(**
   [conditional_B_given_A] (definition).
   Meaning: Makes an event-independence or conditional-probability relationship
   explicit, including necessary denominators.
   Formal construction: (m : TwoEventModel) : R := joint m / p_A m.
   Hypotheses: Requires the normalized nonnegative four-cell record where shown
   in the statement; all other constraints remain explicit.
   Implementation: application of already-proved lemmas; notably
   Rplus_le_le_0_compat., joint_nonnegative., only_A_nonnegative..
   Library discipline: Stdlib.Reals, Lra, Psatz and PeanoNat.
   Scope: Results are exact finite event algebra, not Gaussian admission models
   or estimates from empirical samples.
 *)
Definition conditional_B_given_A (m : TwoEventModel) : R :=
  joint m / p_A m.
(**
   [conditional_A_given_B] (definition).
   Meaning: Makes an event-independence or conditional-probability relationship
   explicit, including necessary denominators.
   Formal construction: (m : TwoEventModel) : R := joint m / p_B m.
   Hypotheses: Requires the normalized nonnegative four-cell record where shown
   in the statement; all other constraints remain explicit.
   Implementation: application of already-proved lemmas; notably
   Rplus_le_le_0_compat., joint_nonnegative., only_A_nonnegative..
   Library discipline: Stdlib.Reals, Lra, Psatz and PeanoNat.
   Scope: Results are exact finite event algebra, not Gaussian admission models
   or estimates from empirical samples.
 *)
Definition conditional_A_given_B (m : TwoEventModel) : R :=
  joint m / p_B m.
(**
   [conditional_both_given_either] (definition).
   Meaning: Makes an event-independence or conditional-probability relationship
   explicit, including necessary denominators.
   Formal construction: (m : TwoEventModel) : R := joint m / p_either m.
   Hypotheses: Requires the normalized nonnegative four-cell record where shown
   in the statement; all other constraints remain explicit.
   Implementation: application of already-proved lemmas; notably
   Rplus_le_le_0_compat., joint_nonnegative., only_A_nonnegative..
   Library discipline: Stdlib.Reals, Lra, Psatz and PeanoNat.
   Scope: Results are exact finite event algebra, not Gaussian admission models
   or estimates from empirical samples.
 *)
Definition conditional_both_given_either (m : TwoEventModel) : R :=
  joint m / p_either m.
(**
   [conditional_not_A_given_B] (definition).
   Meaning: Makes an event-independence or conditional-probability relationship
   explicit, including necessary denominators.
   Formal construction: (m : TwoEventModel) : R := only_B m / p_B m.
   Hypotheses: Requires the normalized nonnegative four-cell record where shown
   in the statement; all other constraints remain explicit.
   Implementation: application of already-proved lemmas; notably
   Rplus_le_le_0_compat., joint_nonnegative., only_A_nonnegative..
   Library discipline: Stdlib.Reals, Lra, Psatz and PeanoNat.
   Scope: Results are exact finite event algebra, not Gaussian admission models
   or estimates from empirical samples.
 *)
Definition conditional_not_A_given_B (m : TwoEventModel) : R :=
  only_B m / p_B m.

(**
   [first_marginal_nonnegative] (theorem).
   Meaning: Relates explicit finite outcomes and weights to the corresponding
   marginal or joint quantity.
   Formal conclusion: forall m, 0 <= p_A m.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: application of already-proved lemmas; notably
   Rplus_le_le_0_compat., joint_nonnegative., only_A_nonnegative..
   Library discipline: Stdlib.Reals, Lra, Psatz and PeanoNat.
   Scope: Results are exact finite event algebra, not Gaussian admission models
   or estimates from empirical samples.
 *)
Theorem first_marginal_nonnegative :
  forall m, 0 <= p_A m.
Proof.
  intro m; unfold p_A.
  apply Rplus_le_le_0_compat.
  - apply joint_nonnegative.
  - apply only_A_nonnegative.
Qed.

(**
   [second_marginal_nonnegative] (theorem).
   Meaning: Relates explicit finite outcomes and weights to the corresponding
   marginal or joint quantity.
   Formal conclusion: forall m, 0 <= p_B m.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: application of already-proved lemmas; notably
   Rplus_le_le_0_compat., joint_nonnegative., only_B_nonnegative..
   Library discipline: Stdlib.Reals, Lra, Psatz and PeanoNat.
   Scope: Results are exact finite event algebra, not Gaussian admission models
   or estimates from empirical samples.
 *)
Theorem second_marginal_nonnegative :
  forall m, 0 <= p_B m.
Proof.
  intro m; unfold p_B.
  apply Rplus_le_le_0_compat.
  - apply joint_nonnegative.
  - apply only_B_nonnegative.
Qed.

(**
   [union_nonnegative] (theorem).
   Meaning: Controls union/intersection mass for Boolean events through finite
   probability algebra.
   Formal conclusion: forall m, 0 <= p_either m.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: application of already-proved lemmas; notably p_either.,
   Rplus_le_le_0_compat., joint_nonnegative..
   Library discipline: Stdlib.Reals, Lra, Psatz and PeanoNat.
   Scope: Results are exact finite event algebra, not Gaussian admission models
   or estimates from empirical samples.
 *)
Theorem union_nonnegative :
  forall m, 0 <= p_either m.
Proof.
  intro m; unfold p_either.
  apply Rplus_le_le_0_compat.
  - apply Rplus_le_le_0_compat.
    + apply joint_nonnegative.
    + apply only_A_nonnegative.
  - apply only_B_nonnegative.
Qed.

(**
   [union_at_most_one] (theorem).
   Meaning: Controls union/intersection mass for Boolean events through finite
   probability algebra.
   Formal conclusion: forall m, p_either m <= 1.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: application of already-proved lemmas, Stdlib Lra linear
   arithmetic; notably p_either., cells_sum_to_one, neither_nonnegative.
   Library discipline: Stdlib.Reals, Lra, Psatz and PeanoNat.
   Scope: Results are exact finite event algebra, not Gaussian admission models
   or estimates from empirical samples.
 *)
Theorem union_at_most_one :
  forall m, p_either m <= 1.
Proof.
  intro m; unfold p_either.
  pose proof (cells_sum_to_one m).
  pose proof (neither_nonnegative m).
  lra.
Qed.

(**
   [both_at_most_first] (theorem).
   Meaning: Controls union/intersection mass for Boolean events through finite
   probability algebra.
   Formal conclusion: forall m, p_both m <= p_A m.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: application of already-proved lemmas, Stdlib Lra linear
   arithmetic; notably only_A_nonnegative.
   Library discipline: Stdlib.Reals, Lra, Psatz and PeanoNat.
   Scope: Results are exact finite event algebra, not Gaussian admission models
   or estimates from empirical samples.
 *)
Theorem both_at_most_first :
  forall m, p_both m <= p_A m.
Proof.
  intro m; unfold p_both, p_A.
  pose proof (only_A_nonnegative m); lra.
Qed.

(**
   [both_at_most_second] (theorem).
   Meaning: Controls union/intersection mass for Boolean events through finite
   probability algebra.
   Formal conclusion: forall m, p_both m <= p_B m.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: application of already-proved lemmas, Stdlib Lra linear
   arithmetic; notably only_B_nonnegative.
   Library discipline: Stdlib.Reals, Lra, Psatz and PeanoNat.
   Scope: Results are exact finite event algebra, not Gaussian admission models
   or estimates from empirical samples.
 *)
Theorem both_at_most_second :
  forall m, p_both m <= p_B m.
Proof.
  intro m; unfold p_both, p_B.
  pose proof (only_B_nonnegative m); lra.
Qed.

(**
   [union_at_least_first] (theorem).
   Meaning: Controls union/intersection mass for Boolean events through finite
   probability algebra.
   Formal conclusion: forall m, p_A m <= p_either m.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: application of already-proved lemmas, Stdlib Lra linear
   arithmetic; notably only_B_nonnegative.
   Library discipline: Stdlib.Reals, Lra, Psatz and PeanoNat.
   Scope: Results are exact finite event algebra, not Gaussian admission models
   or estimates from empirical samples.
 *)
Theorem union_at_least_first :
  forall m, p_A m <= p_either m.
Proof.
  intro m; unfold p_A, p_either.
  pose proof (only_B_nonnegative m); lra.
Qed.

(**
   [union_at_least_second] (theorem).
   Meaning: Controls union/intersection mass for Boolean events through finite
   probability algebra.
   Formal conclusion: forall m, p_B m <= p_either m.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: application of already-proved lemmas, Stdlib Lra linear
   arithmetic; notably only_A_nonnegative.
   Library discipline: Stdlib.Reals, Lra, Psatz and PeanoNat.
   Scope: Results are exact finite event algebra, not Gaussian admission models
   or estimates from empirical samples.
 *)
Theorem union_at_least_second :
  forall m, p_B m <= p_either m.
Proof.
  intro m; unfold p_B, p_either.
  pose proof (only_A_nonnegative m); lra.
Qed.

(* Inclusion-exclusion is exact for arbitrary dependence. *)
(**
   [inclusion_exclusion] (theorem).
   Meaning: Gives a precise computational or algebraic interpretation of the
   named construction or assertion.
   Formal conclusion: forall m, p_either m = p_A m + p_B m - p_both m.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: ring/field normalization; notably p_either.
   Library discipline: Stdlib.Reals, Lra, Psatz and PeanoNat.
   Scope: Results are exact finite event algebra, not Gaussian admission models
   or estimates from empirical samples.
 *)
Theorem inclusion_exclusion :
  forall m, p_either m = p_A m + p_B m - p_both m.
Proof.
  intro m; unfold p_either, p_A, p_B, p_both; ring.
Qed.

(**
   [union_bound] (theorem).
   Meaning: Controls union/intersection mass for Boolean events through finite
   probability algebra.
   Formal conclusion: forall m, p_either m <= p_A m + p_B m.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: equational rewriting, application of already-proved lemmas,
   Stdlib Lra linear arithmetic; notably inclusion_exclusion., p_both.,
   joint_nonnegative.
   Library discipline: Stdlib.Reals, Lra, Psatz and PeanoNat.
   Scope: Results are exact finite event algebra, not Gaussian admission models
   or estimates from empirical samples.
 *)
Theorem union_bound :
  forall m, p_either m <= p_A m + p_B m.
Proof.
  intro m.
  rewrite inclusion_exclusion.
  unfold p_both.
  pose proof (joint_nonnegative m); lra.
Qed.

(**
   [frechet_lower_bound] (theorem).
   Meaning: Controls union/intersection mass for Boolean events through finite
   probability algebra.
   Formal conclusion: forall m, p_A m + p_B m - 1 <= p_both m.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: application of already-proved lemmas, Stdlib Lra linear
   arithmetic; notably cells_sum_to_one, neither_nonnegative.
   Library discipline: Stdlib.Reals, Lra, Psatz and PeanoNat.
   Scope: Results are exact finite event algebra, not Gaussian admission models
   or estimates from empirical samples.
 *)
Theorem frechet_lower_bound :
  forall m, p_A m + p_B m - 1 <= p_both m.
Proof.
  intro m.
  unfold p_A, p_B, p_both.
  pose proof (cells_sum_to_one m).
  pose proof (neither_nonnegative m).
  lra.
Qed.

(**
   [overlap_nonnegative] (theorem).
   Meaning: Controls union/intersection mass for Boolean events through finite
   probability algebra.
   Formal conclusion: forall m, 0 <= p_both m.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: application of already-proved lemmas; notably p_both.,
   joint_nonnegative..
   Library discipline: Stdlib.Reals, Lra, Psatz and PeanoNat.
   Scope: Results are exact finite event algebra, not Gaussian admission models
   or estimates from empirical samples.
 *)
Theorem overlap_nonnegative :
  forall m, 0 <= p_both m.
Proof.
  intro m; unfold p_both.
  apply joint_nonnegative.
Qed.

(**
   [union_complement] (theorem).
   Meaning: Controls union/intersection mass for Boolean events through finite
   probability algebra.
   Formal conclusion: forall m, p_either m + neither m = 1.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: application of already-proved lemmas; notably p_either.,
   cells_sum_to_one.
   Library discipline: Stdlib.Reals, Lra, Psatz and PeanoNat.
   Scope: Results are exact finite event algebra, not Gaussian admission models
   or estimates from empirical samples.
 *)
Theorem union_complement :
  forall m, p_either m + neither m = 1.
Proof.
  intro m; unfold p_either.
  exact (cells_sum_to_one m).
Qed.

(**
   [exactly_one_formula] (theorem).
   Meaning: Gives a precise computational or algebraic interpretation of the
   named construction or assertion.
   Formal conclusion: forall m, p_exactly_one m = p_A m + p_B m - 2 * p_both m.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: ring/field normalization; notably p_exactly_one.
   Library discipline: Stdlib.Reals, Lra, Psatz and PeanoNat.
   Scope: Results are exact finite event algebra, not Gaussian admission models
   or estimates from empirical samples.
 *)
Theorem exactly_one_formula :
  forall m, p_exactly_one m = p_A m + p_B m - 2 * p_both m.
Proof.
  intro m.
  unfold p_exactly_one, p_A, p_B, p_both; ring.
Qed.

(**
   [exactly_one_vs_union] (theorem).
   Meaning: Controls union/intersection mass for Boolean events through finite
   probability algebra.
   Formal conclusion: forall m, p_either m = p_exactly_one m + p_both m.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: ring/field normalization; notably p_either.
   Library discipline: Stdlib.Reals, Lra, Psatz and PeanoNat.
   Scope: Results are exact finite event algebra, not Gaussian admission models
   or estimates from empirical samples.
 *)
Theorem exactly_one_vs_union :
  forall m, p_either m = p_exactly_one m + p_both m.
Proof.
  intro m; unfold p_either, p_exactly_one, p_both; ring.
Qed.

(**
   [equal_marginal_union] (theorem).
   Meaning: Controls union/intersection mass for Boolean events through finite
   probability algebra.
   Formal conclusion: p_either m = 2 * p - p_both m.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: equational rewriting, ring/field normalization; notably
   inclusion_exclusion.
   Library discipline: Stdlib.Reals, Lra, Psatz and PeanoNat.
   Scope: Results are exact finite event algebra, not Gaussian admission models
   or estimates from empirical samples.
 *)
Theorem equal_marginal_union :
  forall m p, p_A m = p -> p_B m = p ->
    p_either m = 2 * p - p_both m.
Proof.
  intros m p Ha Hb.
  rewrite inclusion_exclusion, Ha, Hb.
  ring.
Qed.

(**
   [equal_marginal_exactly_one] (theorem).
   Meaning: Relates explicit finite outcomes and weights to the corresponding
   marginal or joint quantity.
   Formal conclusion: p_exactly_one m = 2 * (p - p_both m).
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: equational rewriting, ring/field normalization; notably
   exactly_one_formula.
   Library discipline: Stdlib.Reals, Lra, Psatz and PeanoNat.
   Scope: Results are exact finite event algebra, not Gaussian admission models
   or estimates from empirical samples.
 *)
Theorem equal_marginal_exactly_one :
  forall m p, p_A m = p -> p_B m = p ->
    p_exactly_one m = 2 * (p - p_both m).
Proof.
  intros m p Ha Hb.
  rewrite exactly_one_formula, Ha, Hb.
  ring.
Qed.

(**
   [conditional_B_numerator] (theorem).
   Meaning: Makes an event-independence or conditional-probability relationship
   explicit, including necessary denominators.
   Formal conclusion: p_A m * conditional_B_given_A m = p_both m.
   Hypotheses: Requires explicit nonzero/strict-positive denominator or scale
   where shown in the statement; all other constraints remain explicit.
   Proof outline: Stdlib Lra linear arithmetic, ring/field normalization;
   notably conditional_B_given_A.
   Library discipline: Stdlib.Reals, Lra, Psatz and PeanoNat.
   Scope: Results are exact finite event algebra, not Gaussian admission models
   or estimates from empirical samples.
 *)
Theorem conditional_B_numerator :
  forall m, 0 < p_A m ->
    p_A m * conditional_B_given_A m = p_both m.
Proof.
  intros m Ha.
  unfold conditional_B_given_A, p_both.
  field; lra.
Qed.

(**
   [conditional_A_numerator] (theorem).
   Meaning: Makes an event-independence or conditional-probability relationship
   explicit, including necessary denominators.
   Formal conclusion: p_B m * conditional_A_given_B m = p_both m.
   Hypotheses: Requires explicit nonzero/strict-positive denominator or scale
   where shown in the statement; all other constraints remain explicit.
   Proof outline: Stdlib Lra linear arithmetic, ring/field normalization;
   notably conditional_A_given_B.
   Library discipline: Stdlib.Reals, Lra, Psatz and PeanoNat.
   Scope: Results are exact finite event algebra, not Gaussian admission models
   or estimates from empirical samples.
 *)
Theorem conditional_A_numerator :
  forall m, 0 < p_B m ->
    p_B m * conditional_A_given_B m = p_both m.
Proof.
  intros m Hb.
  unfold conditional_A_given_B, p_both.
  field; lra.
Qed.

(**
   [conditional_either_numerator] (theorem).
   Meaning: Makes an event-independence or conditional-probability relationship
   explicit, including necessary denominators.
   Formal conclusion: p_either m * conditional_both_given_either m = p_both m.
   Hypotheses: Requires explicit nonzero/strict-positive denominator or scale
   where shown in the statement; all other constraints remain explicit.
   Proof outline: Stdlib Lra linear arithmetic, ring/field normalization;
   notably conditional_both_given_either.
   Library discipline: Stdlib.Reals, Lra, Psatz and PeanoNat.
   Scope: Results are exact finite event algebra, not Gaussian admission models
   or estimates from empirical samples.
 *)
Theorem conditional_either_numerator :
  forall m, 0 < p_either m ->
    p_either m * conditional_both_given_either m = p_both m.
Proof.
  intros m Hu.
  unfold conditional_both_given_either, p_both.
  field; lra.
Qed.

(**
   [both_conditional_denominators_agree] (theorem).
   Meaning: Makes an event-independence or conditional-probability relationship
   explicit, including necessary denominators.
   Formal conclusion: p_A m * conditional_B_given_A m = p_B m *
   conditional_A_given_B m.
   Hypotheses: Requires explicit nonzero/strict-positive denominator or scale
   where shown in the statement; all other constraints remain explicit.
   Proof outline: equational rewriting, definitional computation; notably
   conditional_B_numerator, conditional_A_numerator.
   Library discipline: Stdlib.Reals, Lra, Psatz and PeanoNat.
   Scope: Results are exact finite event algebra, not Gaussian admission models
   or estimates from empirical samples.
 *)
Theorem both_conditional_denominators_agree :
  forall m, 0 < p_A m -> 0 < p_B m ->
    p_A m * conditional_B_given_A m =
    p_B m * conditional_A_given_B m.
Proof.
  intros m Ha Hb.
  rewrite (conditional_B_numerator m Ha).
  rewrite (conditional_A_numerator m Hb).
  reflexivity.
Qed.

(**
   [conditional_failure_complement] (theorem).
   Meaning: Makes an event-independence or conditional-probability relationship
   explicit, including necessary denominators.
   Formal conclusion: conditional_not_A_given_B m + conditional_A_given_B m =
   1.
   Hypotheses: Requires explicit nonzero/strict-positive denominator or scale
   where shown in the statement; all other constraints remain explicit.
   Proof outline: Stdlib Lra linear arithmetic, ring/field normalization;
   notably conditional_not_A_given_B.
   Library discipline: Stdlib.Reals, Lra, Psatz and PeanoNat.
   Scope: Results are exact finite event algebra, not Gaussian admission models
   or estimates from empirical samples.
 *)
Theorem conditional_failure_complement :
  forall m, 0 < p_B m ->
    conditional_not_A_given_B m +
      conditional_A_given_B m = 1.
Proof.
  intros m Hb.
  unfold conditional_not_A_given_B, conditional_A_given_B.
  unfold p_B in *.
  field; lra.
Qed.

(**
   [conditional_second_le_one] (theorem).
   Meaning: Makes an event-independence or conditional-probability relationship
   explicit, including necessary denominators.
   Formal conclusion: conditional_B_given_A m <= 1.
   Hypotheses: Requires explicit nonzero/strict-positive denominator or scale
   where shown in the statement; all other constraints remain explicit.
   Proof outline: application of already-proved lemmas, Stdlib Lra linear
   arithmetic, ring/field normalization; notably Rinv_0_lt_compat,
   conditional_B_given_A, Rmult_le_compat_r..
   Library discipline: Stdlib.Reals, Lra, Psatz and PeanoNat.
   Scope: Results are exact finite event algebra, not Gaussian admission models
   or estimates from empirical samples.
 *)
Theorem conditional_second_le_one :
  forall m, 0 < p_A m ->
    conditional_B_given_A m <= 1.
Proof.
  intros m Ha.
  assert (Hinv : 0 <= / p_A m).
  { left; apply Rinv_0_lt_compat; exact Ha. }
  unfold conditional_B_given_A, Rdiv.
  replace 1 with (p_A m * / p_A m) by (field; lra).
  apply Rmult_le_compat_r.
  - exact Hinv.
  - apply both_at_most_first.
Qed.

(**
   [conditional_first_le_one] (theorem).
   Meaning: Makes an event-independence or conditional-probability relationship
   explicit, including necessary denominators.
   Formal conclusion: conditional_A_given_B m <= 1.
   Hypotheses: Requires explicit nonzero/strict-positive denominator or scale
   where shown in the statement; all other constraints remain explicit.
   Proof outline: application of already-proved lemmas, Stdlib Lra linear
   arithmetic, ring/field normalization; notably Rinv_0_lt_compat,
   conditional_A_given_B, Rmult_le_compat_r..
   Library discipline: Stdlib.Reals, Lra, Psatz and PeanoNat.
   Scope: Results are exact finite event algebra, not Gaussian admission models
   or estimates from empirical samples.
 *)
Theorem conditional_first_le_one :
  forall m, 0 < p_B m ->
    conditional_A_given_B m <= 1.
Proof.
  intros m Hb.
  assert (Hinv : 0 <= / p_B m).
  { left; apply Rinv_0_lt_compat; exact Hb. }
  unfold conditional_A_given_B, Rdiv.
  replace 1 with (p_B m * / p_B m) by (field; lra).
  apply Rmult_le_compat_r.
  - exact Hinv.
  - apply both_at_most_second.
Qed.

(**
   [conditional_failure_nonnegative] (theorem).
   Meaning: Makes an event-independence or conditional-probability relationship
   explicit, including necessary denominators.
   Formal conclusion: 0 <= conditional_not_A_given_B m.
   Hypotheses: Requires explicit nonzero/strict-positive denominator or scale
   where shown in the statement; all other constraints remain explicit.
   Proof outline: application of already-proved lemmas; notably
   conditional_not_A_given_B, Rmult_le_pos., only_B_nonnegative..
   Library discipline: Stdlib.Reals, Lra, Psatz and PeanoNat.
   Scope: Results are exact finite event algebra, not Gaussian admission models
   or estimates from empirical samples.
 *)
Theorem conditional_failure_nonnegative :
  forall m, 0 < p_B m ->
    0 <= conditional_not_A_given_B m.
Proof.
  intros m Hb; unfold conditional_not_A_given_B, Rdiv.
  apply Rmult_le_pos.
  - apply only_B_nonnegative.
  - apply Rlt_le, Rinv_0_lt_compat; exact Hb.
Qed.

(**
   [binary_indicator_covariance_numerator] (theorem).
   Meaning: Establishes an exact covariance identity or bound for the specified
   finite score functions.
   Formal conclusion: forall m, p_both m - p_A m * p_B m = joint m * neither m
   - only_A m * only_B m.
   Hypotheses: Requires the normalized nonnegative four-cell record where shown
   in the statement; all other constraints remain explicit.
   Proof outline: equational rewriting, application of already-proved lemmas,
   Stdlib Lra linear arithmetic, ring/field normalization; notably
   cells_sum_to_one, Hneither..
   Library discipline: Stdlib.Reals, Lra, Psatz and PeanoNat.
   Scope: Results are exact finite event algebra, not Gaussian admission models
   or estimates from empirical samples.
 *)
Theorem binary_indicator_covariance_numerator :
  forall m,
    p_both m - p_A m * p_B m =
    joint m * neither m - only_A m * only_B m.
Proof.
  intro m.
  pose proof (cells_sum_to_one m) as Hsum.
  assert (Hneither :
    neither m = 1 - joint m - only_A m - only_B m) by lra.
  rewrite Hneither.
  unfold p_both, p_A, p_B.
  ring.
Qed.

(**
   [binary_independence_criterion] (theorem).
   Meaning: Makes an event-independence or conditional-probability relationship
   explicit, including necessary denominators.
   Formal conclusion: forall m, p_both m = p_A m * p_B m <-> joint m * neither
   m = only_A m * only_B m.
   Hypotheses: Requires the normalized nonnegative four-cell record where shown
   in the statement; all other constraints remain explicit.
   Proof outline: application of already-proved lemmas, Stdlib Lra linear
   arithmetic; notably binary_indicator_covariance_numerator.
   Library discipline: Stdlib.Reals, Lra, Psatz and PeanoNat.
   Scope: Results are exact finite event algebra, not Gaussian admission models
   or estimates from empirical samples.
 *)
Theorem binary_independence_criterion :
  forall m,
    p_both m = p_A m * p_B m <->
    joint m * neither m = only_A m * only_B m.
Proof.
  intro m.
  pose proof (binary_indicator_covariance_numerator m) as Hcov.
  split; intro Heq; lra.
Qed.

(* Exact incompatibility with the 2.11% union quoted in the old letter,
   assuming the specified 2% and 0.1% marginal frequencies. *)
(**
   [original_mixed_union_impossible] (theorem).
   Meaning: Controls union/intersection mass for Boolean events through finite
   probability algebra.
   Formal conclusion: p_either m <> 211 / 10000.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: equational rewriting, application of already-proved lemmas,
   Stdlib Lra linear arithmetic; notably union_bound.
   Library discipline: Stdlib.Reals, Lra, Psatz and PeanoNat.
   Scope: Results are exact finite event algebra, not Gaussian admission models
   or estimates from empirical samples.
 *)
Theorem original_mixed_union_impossible :
  forall m,
    p_A m = 2 / 100 ->
    p_B m = 1 / 1000 ->
    p_either m <> 211 / 10000.
Proof.
  intros m Ha Hb Hbad.
  pose proof (union_bound m) as Hbound.
  rewrite Ha, Hb, Hbad in Hbound.
  lra.
Qed.

(**
   [equal_marginal_overlap_from_union] (theorem).
   Meaning: Controls union/intersection mass for Boolean events through finite
   probability algebra.
   Formal conclusion: p_both m = 2 * p - u.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: equational rewriting, application of already-proved lemmas,
   Stdlib Lra linear arithmetic; notably inclusion_exclusion.
   Library discipline: Stdlib.Reals, Lra, Psatz and PeanoNat.
   Scope: Results are exact finite event algebra, not Gaussian admission models
   or estimates from empirical samples.
 *)
Theorem equal_marginal_overlap_from_union :
  forall m p u,
    p_A m = p ->
    p_B m = p ->
    p_either m = u ->
    p_both m = 2 * p - u.
Proof.
  intros m p u Ha Hb Hu.
  pose proof (inclusion_exclusion m) as H.
  rewrite Ha, Hb, Hu in H; lra.
Qed.

(* Independence recurrence: the assumption is encoded by the recurrence,
   rather than silently asserted for real test/retest data. *)
(* Stdlib Nat.iter encodes the independence recurrence without an extra
   recursive function. The closed form remains a theorem, not a definition. *)
(**
   [independent_union] (definition).
   Meaning: Makes an event-independence or conditional-probability relationship
   explicit, including necessary denominators.
   Formal construction: (p : R) (n : nat) : R := Nat.iter n (fun u => u + p - u
   * p) 0.
   Hypotheses: A definition; its parameters and fields appear in the signature,
   with no silent statistical assumptions.
   Implementation: structural induction on a finite list or natural index,
   equational rewriting, ring/field normalization; notably independent_union,
   Nat.iter_succ..
   Library discipline: Stdlib.Reals, Lra, Psatz and PeanoNat.
   Scope: Results are exact finite event algebra, not Gaussian admission models
   or estimates from empirical samples.
 *)
Definition independent_union (p : R) (n : nat) : R :=
  Nat.iter n (fun u => u + p - u * p) 0.

(**
   [independent_union_formula] (theorem).
   Meaning: Makes an event-independence or conditional-probability relationship
   explicit, including necessary denominators.
   Formal conclusion: forall p n, independent_union p n = 1 - (1 - p) ^ n.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: structural induction on a finite list or natural index,
   equational rewriting, ring/field normalization; notably independent_union,
   Nat.iter_succ..
   Library discipline: Stdlib.Reals, Lra, Psatz and PeanoNat.
   Scope: Results are exact finite event algebra, not Gaussian admission models
   or estimates from empirical samples.
 *)
Theorem independent_union_formula :
  forall p n, independent_union p n = 1 - (1 - p) ^ n.
Proof.
  intros p n; induction n as [| k IH].
  - unfold independent_union; simpl; ring.
  - unfold independent_union in *.
    rewrite Nat.iter_succ.
    rewrite IH; simpl; ring.
Qed.

(**
   [independent_union_one] (theorem).
   Meaning: Makes an event-independence or conditional-probability relationship
   explicit, including necessary denominators.
   Formal conclusion: forall p, independent_union p 1%nat = p.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: ring/field normalization; notably independent_union.
   Library discipline: Stdlib.Reals, Lra, Psatz and PeanoNat.
   Scope: Results are exact finite event algebra, not Gaussian admission models
   or estimates from empirical samples.
 *)
Theorem independent_union_one :
  forall p, independent_union p 1%nat = p.
Proof.
  intro p; unfold independent_union; simpl; ring.
Qed.

(**
   [independent_union_two] (theorem).
   Meaning: Makes an event-independence or conditional-probability relationship
   explicit, including necessary denominators.
   Formal conclusion: forall p, independent_union p 2%nat = 2 * p - p * p.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: ring/field normalization; notably independent_union.
   Library discipline: Stdlib.Reals, Lra, Psatz and PeanoNat.
   Scope: Results are exact finite event algebra, not Gaussian admission models
   or estimates from empirical samples.
 *)
Theorem independent_union_two :
  forall p, independent_union p 2%nat = 2 * p - p * p.
Proof.
  intro p; unfold independent_union; simpl; ring.
Qed.

(* Two explicit probability models with equal marginals but different overlap.
   Thus marginal pass rates alone cannot fix the OR eligibility fraction. *)
(**
   [identical_half_events] (definition).
   Meaning: Gives a precise computational or algebraic interpretation of the
   named construction or assertion.
   Formal construction: TwoEventModel.
   Hypotheses: Requires the normalized nonnegative four-cell record where shown
   in the statement; all other constraints remain explicit.
   Implementation: Stdlib Lra linear arithmetic.
   Library discipline: Stdlib.Reals, Lra, Psatz and PeanoNat.
   Scope: Results are exact finite event algebra, not Gaussian admission models
   or estimates from empirical samples.
 *)
Definition identical_half_events : TwoEventModel.
Proof.
  refine {| joint := 1/2; only_A := 0; only_B := 0;
            neither := 1/2 |}; lra.
Defined.

(**
   [independent_half_events] (definition).
   Meaning: Makes an event-independence or conditional-probability relationship
   explicit, including necessary denominators.
   Formal construction: TwoEventModel.
   Hypotheses: Requires the normalized nonnegative four-cell record where shown
   in the statement; all other constraints remain explicit.
   Implementation: Stdlib Lra linear arithmetic.
   Library discipline: Stdlib.Reals, Lra, Psatz and PeanoNat.
   Scope: Results are exact finite event algebra, not Gaussian admission models
   or estimates from empirical samples.
 *)
Definition independent_half_events : TwoEventModel.
Proof.
  refine {| joint := 1/4; only_A := 1/4; only_B := 1/4;
            neither := 1/4 |}; lra.
Defined.

(**
   [same_marginals_different_joint] (theorem).
   Meaning: Relates explicit finite outcomes and weights to the corresponding
   marginal or joint quantity.
   Formal conclusion: p_A identical_half_events = p_A independent_half_events
   /\ p_B identical_half_events = p_B independent_half_events /\ p_both
   identical_half_events <> p_both independent_half_events.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: Stdlib Lra linear arithmetic.
   Library discipline: Stdlib.Reals, Lra, Psatz and PeanoNat.
   Scope: Results are exact finite event algebra, not Gaussian admission models
   or estimates from empirical samples.
 *)
Theorem same_marginals_different_joint :
  p_A identical_half_events = p_A independent_half_events /\
  p_B identical_half_events = p_B independent_half_events /\
  p_both identical_half_events <> p_both independent_half_events.
Proof.
  unfold p_A, p_B, p_both,
    identical_half_events, independent_half_events.
  simpl; repeat split; lra.
Qed.

(**
   [same_marginals_different_union] (theorem).
   Meaning: Controls union/intersection mass for Boolean events through finite
   probability algebra.
   Formal conclusion: p_A identical_half_events = p_A independent_half_events
   /\ p_B identical_half_events = p_B independent_half_events /\ p_either
   identical_half_events <> p_either independent_half_events.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: Stdlib Lra linear arithmetic.
   Library discipline: Stdlib.Reals, Lra, Psatz and PeanoNat.
   Scope: Results are exact finite event algebra, not Gaussian admission models
   or estimates from empirical samples.
 *)
Theorem same_marginals_different_union :
  p_A identical_half_events = p_A independent_half_events /\
  p_B identical_half_events = p_B independent_half_events /\
  p_either identical_half_events <> p_either independent_half_events.
Proof.
  unfold p_A, p_B, p_either,
    identical_half_events, independent_half_events.
  simpl; repeat split; lra.
Qed.

(* The BASIC grid had 397 nodes on each axis. *)
(**
   [grid_node_count] (example).
   Meaning: Gives a precise computational or algebraic interpretation of the
   named construction or assertion.
   Formal conclusion: (397 * 397)%nat = 157609%nat.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: Stdlib Psatz nonlinear arithmetic, ring/field normalization,
   definitional computation.
   Library discipline: Stdlib.Reals, Lra, Psatz and PeanoNat.
   Scope: Results are exact finite event algebra, not Gaussian admission models
   or estimates from empirical samples.
 *)
Example grid_node_count :
  (397 * 397)%nat = 157609%nat.
Proof. reflexivity. Qed.

(**
   [grid_scale_factors_cancel] (theorem).
   Meaning: Justifies a score conversion or standardization formula by exact
   real arithmetic.
   Formal conclusion: (scale * numerator) / (scale * denominator) = numerator /
   denominator.
   Hypotheses: Requires explicit nonzero/strict-positive denominator or scale
   where shown in the statement; all other constraints remain explicit.
   Proof outline: Stdlib Psatz nonlinear arithmetic, ring/field normalization.
   Library discipline: Stdlib.Reals, Lra, Psatz and PeanoNat.
   Scope: Results are exact finite event algebra, not Gaussian admission models
   or estimates from empirical samples.
 *)
Theorem grid_scale_factors_cancel :
  forall scale numerator denominator,
    0 < scale -> 0 < denominator ->
    (scale * numerator) / (scale * denominator) =
      numerator / denominator.
Proof.
  intros scale numerator denominator Hs Hd; field; nra.
Qed.

(**
   [half_point_grid_midpoint_shift] (theorem).
   Meaning: Gives a precise computational or algebraic interpretation of the
   named construction or assertion.
   Formal conclusion: forall cutoff, cutoff - (1/2) / 2 = cutoff - 1/4.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: ring/field normalization.
   Library discipline: Stdlib.Reals, Lra, Psatz and PeanoNat.
   Scope: Results are exact finite event algebra, not Gaussian admission models
   or estimates from empirical samples.
 *)
Theorem half_point_grid_midpoint_shift :
  forall cutoff,
    cutoff - (1/2) / 2 = cutoff - 1/4.
Proof.
  intro cutoff; field.
Qed.

(* Numerical bivariate-normal integrals and their error bounds are NOT
   claimed as Rocq theorems here. *)


(* Further distribution-free consequences of admission through either test.
   All statements follow from the four nonnegative disjoint outcome cells;
   in particular, they do not depend on a bivariate-normal assumption. *)

(**
   [exactly_one_nonnegative] (theorem).
   Meaning: Gives a precise computational or algebraic interpretation of the
   named construction or assertion.
   Formal conclusion: forall m, 0 <= p_exactly_one m.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: application of already-proved lemmas, Stdlib Lra linear
   arithmetic; notably p_exactly_one., only_A_nonnegative, only_B_nonnegative.
   Library discipline: Stdlib.Reals, Lra, Psatz and PeanoNat.
   Scope: Results are exact finite event algebra, not Gaussian admission models
   or estimates from empirical samples.
 *)
Theorem exactly_one_nonnegative :
  forall m, 0 <= p_exactly_one m.
Proof.
  intros m.
  unfold p_exactly_one.
  pose proof (only_A_nonnegative m).
  pose proof (only_B_nonnegative m).
  lra.
Qed.

(**
   [exactly_one_at_most_either] (theorem).
   Meaning: Controls union/intersection mass for Boolean events through finite
   probability algebra.
   Formal conclusion: forall m, p_exactly_one m <= p_either m.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: application of already-proved lemmas, Stdlib Lra linear
   arithmetic; notably p_exactly_one, joint_nonnegative.
   Library discipline: Stdlib.Reals, Lra, Psatz and PeanoNat.
   Scope: Results are exact finite event algebra, not Gaussian admission models
   or estimates from empirical samples.
 *)
Theorem exactly_one_at_most_either :
  forall m, p_exactly_one m <= p_either m.
Proof.
  intros m.
  unfold p_exactly_one, p_either.
  pose proof (joint_nonnegative m).
  lra.
Qed.

(**
   [intersection_at_most_minimum_marginal] (theorem).
   Meaning: Controls union/intersection mass for Boolean events through finite
   probability algebra.
   Formal conclusion: forall m p, p_A m <= p -> p_B m <= p -> p_both m <= p.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: application of already-proved lemmas, Stdlib Lra linear
   arithmetic; notably both_at_most_first.
   Library discipline: Stdlib.Reals, Lra, Psatz and PeanoNat.
   Scope: Results are exact finite event algebra, not Gaussian admission models
   or estimates from empirical samples.
 *)
Theorem intersection_at_most_minimum_marginal :
  forall m p, p_A m <= p -> p_B m <= p -> p_both m <= p.
Proof.
  intros m p Ha Hb.
  pose proof (both_at_most_first m).
  lra.
Qed.

(**
   [union_equal_marginal_lower_bound] (theorem).
   Meaning: Controls union/intersection mass for Boolean events through finite
   probability algebra.
   Formal conclusion: forall m p, p_A m = p -> p_B m = p -> p <= p_either m.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: application of already-proved lemmas, Stdlib Lra linear
   arithmetic; notably union_at_least_first.
   Library discipline: Stdlib.Reals, Lra, Psatz and PeanoNat.
   Scope: Results are exact finite event algebra, not Gaussian admission models
   or estimates from empirical samples.
 *)
Theorem union_equal_marginal_lower_bound :
  forall m p, p_A m = p -> p_B m = p -> p <= p_either m.
Proof.
  intros m p Ha Hb.
  pose proof (union_at_least_first m).
  lra.
Qed.

(**
   [union_equal_marginal_upper_bound] (theorem).
   Meaning: Controls union/intersection mass for Boolean events through finite
   probability algebra.
   Formal conclusion: p_either m <= 2 * p.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: application of already-proved lemmas, Stdlib Lra linear
   arithmetic; notably union_bound.
   Library discipline: Stdlib.Reals, Lra, Psatz and PeanoNat.
   Scope: Results are exact finite event algebra, not Gaussian admission models
   or estimates from empirical samples.
 *)
Theorem union_equal_marginal_upper_bound :
  forall m p, p_A m = p -> p_B m = p -> p_either m <= 2 * p.
Proof.
  intros m p Ha Hb.
  pose proof (union_bound m).
  lra.
Qed.

(**
   [disjoint_events_union_is_sum] (theorem).
   Meaning: Controls union/intersection mass for Boolean events through finite
   probability algebra.
   Formal conclusion: p_either m = p_A m + p_B m.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: equational rewriting, ring/field normalization; notably
   inclusion_exclusion.
   Library discipline: Stdlib.Reals, Lra, Psatz and PeanoNat.
   Scope: Results are exact finite event algebra, not Gaussian admission models
   or estimates from empirical samples.
 *)
Theorem disjoint_events_union_is_sum :
  forall m, p_both m = 0 ->
    p_either m = p_A m + p_B m.
Proof.
  intros m Hj.
  rewrite inclusion_exclusion, Hj; ring.
Qed.

(**
   [independent_events_union_formula] (theorem).
   Meaning: Makes an event-independence or conditional-probability relationship
   explicit, including necessary denominators.
   Formal conclusion: p_either m = p_A m + p_B m - p_A m * p_B m.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: equational rewriting, definitional computation; notably
   inclusion_exclusion.
   Library discipline: Stdlib.Reals, Lra, Psatz and PeanoNat.
   Scope: Results are exact finite event algebra, not Gaussian admission models
   or estimates from empirical samples.
 *)
Theorem independent_events_union_formula :
  forall m, p_both m = p_A m * p_B m ->
    p_either m = p_A m + p_B m - p_A m * p_B m.
Proof.
  intros m Hj.
  rewrite inclusion_exclusion, Hj; reflexivity.
Qed.

(**
   [independent_equal_marginal_union] (theorem).
   Meaning: Makes an event-independence or conditional-probability relationship
   explicit, including necessary denominators.
   Formal conclusion: p_either m = 2 * p - p * p.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: equational rewriting, ring/field normalization; notably
   inclusion_exclusion.
   Library discipline: Stdlib.Reals, Lra, Psatz and PeanoNat.
   Scope: Results are exact finite event algebra, not Gaussian admission models
   or estimates from empirical samples.
 *)
Theorem independent_equal_marginal_union :
  forall m p,
    p_A m = p -> p_B m = p ->
    p_both m = p * p ->
    p_either m = 2 * p - p * p.
Proof.
  intros m p Ha Hb Hj.
  rewrite inclusion_exclusion, Ha, Hb, Hj; ring.
Qed.

(**
   [all_first_passers_also_second_union] (theorem).
   Meaning: Controls union/intersection mass for Boolean events through finite
   probability algebra.
   Formal conclusion: p_either m = p_B m.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: equational rewriting, application of already-proved lemmas,
   Stdlib Lra linear arithmetic; notably inclusion_exclusion.
   Library discipline: Stdlib.Reals, Lra, Psatz and PeanoNat.
   Scope: Results are exact finite event algebra, not Gaussian admission models
   or estimates from empirical samples.
 *)
Theorem all_first_passers_also_second_union :
  forall m, p_both m = p_A m -> p_either m = p_B m.
Proof.
  intros m Hj.
  pose proof (inclusion_exclusion m) as H.
  rewrite Hj in H; lra.
Qed.

(**
   [excess_marginal_mass_forces_overlap] (theorem).
   Meaning: Controls union/intersection mass for Boolean events through finite
   probability algebra.
   Formal conclusion: forall m, 1 < p_A m + p_B m -> 0 < p_both m.
   Hypotheses: Requires explicit nonzero/strict-positive denominator or scale
   where shown in the statement; all other constraints remain explicit.
   Proof outline: application of already-proved lemmas, Stdlib Lra linear
   arithmetic; notably frechet_lower_bound.
   Library discipline: Stdlib.Reals, Lra, Psatz and PeanoNat.
   Scope: Results are exact finite event algebra, not Gaussian admission models
   or estimates from empirical samples.
 *)
Theorem excess_marginal_mass_forces_overlap :
  forall m, 1 < p_A m + p_B m -> 0 < p_both m.
Proof.
  intros m Hsum.
  pose proof (frechet_lower_bound m).
  lra.
Qed.

(**
   [lower_bound_on_overlap_from_union] (theorem).
   Meaning: Controls union/intersection mass for Boolean events through finite
   probability algebra.
   Formal conclusion: p_both m = pA + pB - u.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: application of already-proved lemmas, Stdlib Lra linear
   arithmetic; notably inclusion_exclusion.
   Library discipline: Stdlib.Reals, Lra, Psatz and PeanoNat.
   Scope: Results are exact finite event algebra, not Gaussian admission models
   or estimates from empirical samples.
 *)
Theorem lower_bound_on_overlap_from_union :
  forall m pA pB u,
    p_A m = pA -> p_B m = pB -> p_either m = u ->
    p_both m = pA + pB - u.
Proof.
  intros m pA pB u Ha Hb Hu.
  pose proof (inclusion_exclusion m) as H.
  lra.
Qed.


(* Independence is an explicit hypothesis about event probabilities.
   These consequences are exact even though the source report's empirical
   admissions tests need not satisfy independence. *)

(**
   [independent_either_as_complement_product] (theorem).
   Meaning: Makes an event-independence or conditional-probability relationship
   explicit, including necessary denominators.
   Formal conclusion: p_either m = 1 - (1 - p_A m) * (1 - p_B m).
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: equational rewriting, ring/field normalization; notably
   independent_events_union_formula.
   Library discipline: Stdlib.Reals, Lra, Psatz and PeanoNat.
   Scope: Results are exact finite event algebra, not Gaussian admission models
   or estimates from empirical samples.
 *)
Theorem independent_either_as_complement_product :
  forall m,
    p_both m = p_A m * p_B m ->
    p_either m = 1 - (1 - p_A m) * (1 - p_B m).
Proof.
  intros m Hjoint.
  rewrite (independent_events_union_formula m Hjoint).
  ring.
Qed.

(**
   [independent_equal_marginals_as_complement_square] (theorem).
   Meaning: Makes an event-independence or conditional-probability relationship
   explicit, including necessary denominators.
   Formal conclusion: p_either m = 1 - (1 - p) * (1 - p).
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: equational rewriting, ring/field normalization; notably
   independent_equal_marginal_union.
   Library discipline: Stdlib.Reals, Lra, Psatz and PeanoNat.
   Scope: Results are exact finite event algebra, not Gaussian admission models
   or estimates from empirical samples.
 *)
Theorem independent_equal_marginals_as_complement_square :
  forall m p,
    p_A m = p -> p_B m = p ->
    p_both m = p * p ->
    p_either m = 1 - (1 - p) * (1 - p).
Proof.
  intros m p Ha Hb Hj.
  rewrite (independent_equal_marginal_union m p Ha Hb Hj).
  ring.
Qed.

(**
   [independent_conditional_B_equals_marginal] (theorem).
   Meaning: Makes an event-independence or conditional-probability relationship
   explicit, including necessary denominators.
   Formal conclusion: conditional_B_given_A m = p_B m.
   Hypotheses: Requires explicit nonzero/strict-positive denominator or scale
   where shown in the statement; all other constraints remain explicit.
   Proof outline: equational rewriting, Stdlib Lra linear arithmetic,
   ring/field normalization; notably conditional_B_given_A..
   Library discipline: Stdlib.Reals, Lra, Psatz and PeanoNat.
   Scope: Results are exact finite event algebra, not Gaussian admission models
   or estimates from empirical samples.
 *)
Theorem independent_conditional_B_equals_marginal :
  forall m,
    0 < p_A m ->
    p_both m = p_A m * p_B m ->
    conditional_B_given_A m = p_B m.
Proof.
  intros m Hpositive Hind.
  unfold p_both in Hind.
  unfold conditional_B_given_A.
  rewrite Hind.
  field; lra.
Qed.

(**
   [independent_conditional_A_equals_marginal] (theorem).
   Meaning: Makes an event-independence or conditional-probability relationship
   explicit, including necessary denominators.
   Formal conclusion: conditional_A_given_B m = p_A m.
   Hypotheses: Requires explicit nonzero/strict-positive denominator or scale
   where shown in the statement; all other constraints remain explicit.
   Proof outline: equational rewriting, Stdlib Lra linear arithmetic,
   ring/field normalization; notably conditional_A_given_B..
   Library discipline: Stdlib.Reals, Lra, Psatz and PeanoNat.
   Scope: Results are exact finite event algebra, not Gaussian admission models
   or estimates from empirical samples.
 *)
Theorem independent_conditional_A_equals_marginal :
  forall m,
    0 < p_B m ->
    p_both m = p_A m * p_B m ->
    conditional_A_given_B m = p_A m.
Proof.
  intros m Hpositive Hind.
  unfold p_both in Hind.
  unfold conditional_A_given_B.
  rewrite Hind.
  field; lra.
Qed.

(**
   [independent_exactly_one_formula] (theorem).
   Meaning: Makes an event-independence or conditional-probability relationship
   explicit, including necessary denominators.
   Formal conclusion: p_exactly_one m = p_A m * (1 - p_B m) + p_B m * (1 - p_A
   m).
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: equational rewriting, ring/field normalization; notably
   exactly_one_formula.
   Library discipline: Stdlib.Reals, Lra, Psatz and PeanoNat.
   Scope: Results are exact finite event algebra, not Gaussian admission models
   or estimates from empirical samples.
 *)
Theorem independent_exactly_one_formula :
  forall m,
    p_both m = p_A m * p_B m ->
    p_exactly_one m =
      p_A m * (1 - p_B m) + p_B m * (1 - p_A m).
Proof.
  intros m Hind.
  rewrite exactly_one_formula, Hind.
  ring.
Qed.

(**
   [disjointness_iff_union_is_sum] (theorem).
   Meaning: Controls union/intersection mass for Boolean events through finite
   probability algebra.
   Formal conclusion: forall m, p_both m = 0 <-> p_either m = p_A m + p_B m.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: application of already-proved lemmas, Stdlib Lra linear
   arithmetic; notably disjoint_events_union_is_sum., inclusion_exclusion.
   Library discipline: Stdlib.Reals, Lra, Psatz and PeanoNat.
   Scope: Results are exact finite event algebra, not Gaussian admission models
   or estimates from empirical samples.
 *)
Theorem disjointness_iff_union_is_sum :
  forall m,
    p_both m = 0 <->
    p_either m = p_A m + p_B m.
Proof.
  intros m; split.
  - apply disjoint_events_union_is_sum.
  - intro Heq.
    pose proof (inclusion_exclusion m).
    lra.
Qed.

(**
   [complete_coverage_iff_no_failures] (theorem).
   Meaning: Gives a precise computational or algebraic interpretation of the
   named construction or assertion.
   Formal conclusion: forall m, p_either m = 1 <-> neither m = 0.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: application of already-proved lemmas, Stdlib Lra linear
   arithmetic; notably union_complement.
   Library discipline: Stdlib.Reals, Lra, Psatz and PeanoNat.
   Scope: Results are exact finite event algebra, not Gaussian admission models
   or estimates from empirical samples.
 *)
Theorem complete_coverage_iff_no_failures :
  forall m,
    p_either m = 1 <-> neither m = 0.
Proof.
  intro m; split; intro H.
  - pose proof (union_complement m); lra.
  - pose proof (union_complement m); lra.
Qed.

(**
   [equal_marginals_overlap_lower_bound] (theorem).
   Meaning: Controls union/intersection mass for Boolean events through finite
   probability algebra.
   Formal conclusion: 2 * p - 1 <= p_both m.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: application of already-proved lemmas, Stdlib Lra linear
   arithmetic; notably frechet_lower_bound.
   Library discipline: Stdlib.Reals, Lra, Psatz and PeanoNat.
   Scope: Results are exact finite event algebra, not Gaussian admission models
   or estimates from empirical samples.
 *)
Theorem equal_marginals_overlap_lower_bound :
  forall m p,
    p_A m = p -> p_B m = p ->
    2 * p - 1 <= p_both m.
Proof.
  intros m p Ha Hb.
  pose proof (frechet_lower_bound m).
  lra.
Qed.

(**
   [zero_first_marginal_forces_zero_overlap] (theorem).
   Meaning: Controls union/intersection mass for Boolean events through finite
   probability algebra.
   Formal conclusion: forall m, p_A m = 0 -> p_both m = 0.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: application of already-proved lemmas, Stdlib Lra linear
   arithmetic; notably overlap_nonnegative, both_at_most_first.
   Library discipline: Stdlib.Reals, Lra, Psatz and PeanoNat.
   Scope: Results are exact finite event algebra, not Gaussian admission models
   or estimates from empirical samples.
 *)
Theorem zero_first_marginal_forces_zero_overlap :
  forall m,
    p_A m = 0 -> p_both m = 0.
Proof.
  intros m Ha.
  pose proof (overlap_nonnegative m).
  pose proof (both_at_most_first m).
  lra.
Qed.

(**
   [zero_second_marginal_forces_zero_overlap] (theorem).
   Meaning: Controls union/intersection mass for Boolean events through finite
   probability algebra.
   Formal conclusion: forall m, p_B m = 0 -> p_both m = 0.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: application of already-proved lemmas, Stdlib Lra linear
   arithmetic; notably overlap_nonnegative, both_at_most_second.
   Library discipline: Stdlib.Reals, Lra, Psatz and PeanoNat.
   Scope: Results are exact finite event algebra, not Gaussian admission models
   or estimates from empirical samples.
 *)
Theorem zero_second_marginal_forces_zero_overlap :
  forall m,
    p_B m = 0 -> p_both m = 0.
Proof.
  intros m Hb.
  pose proof (overlap_nonnegative m).
  pose proof (both_at_most_second m).
  lra.
Qed.



(* Complement the existing upper bounds on conditional admission rates.
   Stdlib real sign lemmas supply the quotient reasoning; the events'
   finite-cell nonnegativity is explicit in TwoEventModel. *)

(**
   [conditional_B_given_A_nonnegative] (theorem).
   Meaning: Makes an event-independence or conditional-probability relationship
   explicit, including necessary denominators.
   Formal conclusion: 0 <= conditional_B_given_A m.
   Hypotheses: Requires explicit nonzero/strict-positive denominator or scale
   where shown in the statement; all other constraints remain explicit.
   Proof outline: application of already-proved lemmas; notably
   conditional_B_given_A, Rmult_le_pos., overlap_nonnegative..
   Library discipline: Stdlib.Reals, Lra, Psatz and PeanoNat.
   Scope: Results are exact finite event algebra, not Gaussian admission models
   or estimates from empirical samples.
 *)
Theorem conditional_B_given_A_nonnegative :
  forall m, 0 < p_A m ->
    0 <= conditional_B_given_A m.
Proof.
  intros m Hpositive.
  unfold conditional_B_given_A, Rdiv.
  apply Rmult_le_pos.
  - apply overlap_nonnegative.
  - apply Rlt_le, Rinv_0_lt_compat; exact Hpositive.
Qed.

(**
   [conditional_A_given_B_nonnegative] (theorem).
   Meaning: Makes an event-independence or conditional-probability relationship
   explicit, including necessary denominators.
   Formal conclusion: 0 <= conditional_A_given_B m.
   Hypotheses: Requires explicit nonzero/strict-positive denominator or scale
   where shown in the statement; all other constraints remain explicit.
   Proof outline: application of already-proved lemmas; notably
   conditional_A_given_B, Rmult_le_pos., overlap_nonnegative..
   Library discipline: Stdlib.Reals, Lra, Psatz and PeanoNat.
   Scope: Results are exact finite event algebra, not Gaussian admission models
   or estimates from empirical samples.
 *)
Theorem conditional_A_given_B_nonnegative :
  forall m, 0 < p_B m ->
    0 <= conditional_A_given_B m.
Proof.
  intros m Hpositive.
  unfold conditional_A_given_B, Rdiv.
  apply Rmult_le_pos.
  - apply overlap_nonnegative.
  - apply Rlt_le, Rinv_0_lt_compat; exact Hpositive.
Qed.

(**
   [conditional_B_given_A_unit_interval] (theorem).
   Meaning: Makes an event-independence or conditional-probability relationship
   explicit, including necessary denominators.
   Formal conclusion: 0 <= conditional_B_given_A m /\ conditional_B_given_A m
   <= 1.
   Hypotheses: Requires explicit nonzero/strict-positive denominator or scale
   where shown in the statement; all other constraints remain explicit.
   Proof outline: application of already-proved lemmas; notably
   conditional_B_given_A_nonnegative, Hpositive., conditional_second_le_one.
   Library discipline: Stdlib.Reals, Lra, Psatz and PeanoNat.
   Scope: Results are exact finite event algebra, not Gaussian admission models
   or estimates from empirical samples.
 *)
Theorem conditional_B_given_A_unit_interval :
  forall m, 0 < p_A m ->
    0 <= conditional_B_given_A m /\
    conditional_B_given_A m <= 1.
Proof.
  intros m Hpositive.
  split.
  - apply conditional_B_given_A_nonnegative; exact Hpositive.
  - apply conditional_second_le_one; exact Hpositive.
Qed.

(**
   [conditional_A_given_B_unit_interval] (theorem).
   Meaning: Makes an event-independence or conditional-probability relationship
   explicit, including necessary denominators.
   Formal conclusion: 0 <= conditional_A_given_B m /\ conditional_A_given_B m
   <= 1.
   Hypotheses: Requires explicit nonzero/strict-positive denominator or scale
   where shown in the statement; all other constraints remain explicit.
   Proof outline: application of already-proved lemmas; notably
   conditional_A_given_B_nonnegative, Hpositive., conditional_first_le_one.
   Library discipline: Stdlib.Reals, Lra, Psatz and PeanoNat.
   Scope: Results are exact finite event algebra, not Gaussian admission models
   or estimates from empirical samples.
 *)
Theorem conditional_A_given_B_unit_interval :
  forall m, 0 < p_B m ->
    0 <= conditional_A_given_B m /\
    conditional_A_given_B m <= 1.
Proof.
  intros m Hpositive.
  split.
  - apply conditional_A_given_B_nonnegative; exact Hpositive.
  - apply conditional_first_le_one; exact Hpositive.
Qed.


(**
   [overlap_at_most_either] (theorem).
   Meaning: Controls union/intersection mass for Boolean events through finite
   probability algebra.
   Formal conclusion: forall m, p_both m <= p_either m.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: equational rewriting, application of already-proved lemmas,
   Stdlib Lra linear arithmetic; notably exactly_one_vs_union.,
   exactly_one_nonnegative.
   Library discipline: Stdlib.Reals, Lra, Psatz and PeanoNat.
   Scope: Results are exact finite event algebra, not Gaussian admission models
   or estimates from empirical samples.
 *)
Theorem overlap_at_most_either :
  forall m, p_both m <= p_either m.
Proof.
  intro m.
  rewrite exactly_one_vs_union.
  pose proof (exactly_one_nonnegative m).
  lra.
Qed.

(**
   [conditional_both_given_either_unit_interval] (theorem).
   Meaning: Makes an event-independence or conditional-probability relationship
   explicit, including necessary denominators.
   Formal conclusion: 0 <= conditional_both_given_either m /\
   conditional_both_given_either m <= 1.
   Hypotheses: Requires explicit nonzero/strict-positive denominator or scale
   where shown in the statement; all other constraints remain explicit.
   Proof outline: application of already-proved lemmas, Stdlib Lra linear
   arithmetic, ring/field normalization; notably Hpositive.,
   conditional_both_given_either, Rmult_le_pos..
   Library discipline: Stdlib.Reals, Lra, Psatz and PeanoNat.
   Scope: Results are exact finite event algebra, not Gaussian admission models
   or estimates from empirical samples.
 *)
Theorem conditional_both_given_either_unit_interval :
  forall m, 0 < p_either m ->
    0 <= conditional_both_given_either m /\
    conditional_both_given_either m <= 1.
Proof.
  intros m Hpositive.
  assert (Hinv : 0 <= / p_either m).
  { apply Rlt_le, Rinv_0_lt_compat; exact Hpositive. }
  unfold conditional_both_given_either, Rdiv.
  split.
  - apply Rmult_le_pos.
    + apply overlap_nonnegative.
    + exact Hinv.
  - replace 1 with (p_either m * / p_either m)
      by (field; lra).
    apply Rmult_le_compat_r.
    + exact Hinv.
    + apply overlap_at_most_either.
Qed.

(**
   [conditional_not_A_given_B_unit_interval] (theorem).
   Meaning: Makes an event-independence or conditional-probability relationship
   explicit, including necessary denominators.
   Formal conclusion: 0 <= conditional_not_A_given_B m /\
   conditional_not_A_given_B m <= 1.
   Hypotheses: Requires explicit nonzero/strict-positive denominator or scale
   where shown in the statement; all other constraints remain explicit.
   Proof outline: application of already-proved lemmas, Stdlib Lra linear
   arithmetic; notably conditional_failure_complement,
   conditional_A_given_B_nonnegative, conditional_failure_nonnegative.
   Library discipline: Stdlib.Reals, Lra, Psatz and PeanoNat.
   Scope: Results are exact finite event algebra, not Gaussian admission models
   or estimates from empirical samples.
 *)
Theorem conditional_not_A_given_B_unit_interval :
  forall m, 0 < p_B m ->
    0 <= conditional_not_A_given_B m /\
    conditional_not_A_given_B m <= 1.
Proof.
  intros m Hpositive.
  pose proof (conditional_failure_complement m Hpositive) as Hsum.
  pose proof (conditional_A_given_B_nonnegative m Hpositive) as Hother.
  split.
  - apply conditional_failure_nonnegative; exact Hpositive.
  - lra.
Qed.


(* Observing that a conditional rate equals its corresponding marginal is
   equivalent to the algebraic independence criterion, when the
   conditioning marginal is positive.  These converses reuse the proven
   conditional numerators rather than manipulate divisions again. *)

(**
   [independence_iff_conditional_B_equals_marginal] (theorem).
   Meaning: Makes an event-independence or conditional-probability relationship
   explicit, including necessary denominators.
   Formal conclusion: (p_both m = p_A m * p_B m <-> conditional_B_given_A m =
   p_B m).
   Hypotheses: Requires explicit nonzero/strict-positive denominator or scale
   where shown in the statement; all other constraints remain explicit.
   Proof outline: equational rewriting, application of already-proved lemmas;
   notably independent_conditional_B_equals_marginal, Hpositive.,
   conditional_B_numerator.
   Library discipline: Stdlib.Reals, Lra, Psatz and PeanoNat.
   Scope: Results are exact finite event algebra, not Gaussian admission models
   or estimates from empirical samples.
 *)
Theorem independence_iff_conditional_B_equals_marginal :
  forall m,
    0 < p_A m ->
    (p_both m = p_A m * p_B m <->
      conditional_B_given_A m = p_B m).
Proof.
  intros m Hpositive.
  split.
  - apply independent_conditional_B_equals_marginal; exact Hpositive.
  - intro Hconditional.
    pose proof (conditional_B_numerator m Hpositive) as Hnumerator.
    rewrite Hconditional in Hnumerator.
    symmetry; exact Hnumerator.
Qed.

(**
   [independence_iff_conditional_A_equals_marginal] (theorem).
   Meaning: Makes an event-independence or conditional-probability relationship
   explicit, including necessary denominators.
   Formal conclusion: (p_both m = p_A m * p_B m <-> conditional_A_given_B m =
   p_A m).
   Hypotheses: Requires explicit nonzero/strict-positive denominator or scale
   where shown in the statement; all other constraints remain explicit.
   Proof outline: equational rewriting, application of already-proved lemmas;
   notably independent_conditional_A_equals_marginal, Hpositive.,
   conditional_A_numerator.
   Library discipline: Stdlib.Reals, Lra, Psatz and PeanoNat.
   Scope: Results are exact finite event algebra, not Gaussian admission models
   or estimates from empirical samples.
 *)
Theorem independence_iff_conditional_A_equals_marginal :
  forall m,
    0 < p_B m ->
    (p_both m = p_A m * p_B m <->
      conditional_A_given_B m = p_A m).
Proof.
  intros m Hpositive.
  split.
  - apply independent_conditional_A_equals_marginal; exact Hpositive.
  - intro Hconditional.
    pose proof (conditional_A_numerator m Hpositive) as Hnumerator.
    rewrite Hconditional in Hnumerator.
    rewrite Rmult_comm in Hnumerator.
    symmetry; exact Hnumerator.
Qed.
