(** Module: FourCellBridge.v
   Purpose: Concrete Boolean-product realization of the four-cell admissions report.
   Connects the Towers joint/exclusive/neither admissions cells to a complete list of Boolean outcome pairs.
   Mathematical representation: The standard List.list_prod enumerates four (bool * bool) outcomes; the four weights are the explicit Admissions.TwoEventModel cell fields.
   Explicit hypotheses: The admissions record supplies nonnegative cells summing to one, and the probability/moment identities are derived through the finite bridges.
   Library use: Stdlib.List.list_prod, in_prod and length_prod, plus Admissions, FiniteUnion, FiniteMoments and FiniteBridge.
   Limitations: The model proves exact four-cell algebra; it does not introduce independent events or an estimated admission-rate distribution.
   Proof documentation: Every public and helper declaration below has its
   own statement, hypothesis, proof-approach, and scope commentary.
   Reproduction: rocq compile FourCellBridge.v (after imported local modules);
   see rocq/README.md and rocq/LIBRARY_AUDIT.md for dependency order,
   checked-claim mapping, and library audit. All results are Rocq-kernel
   checked; no unchecked evidence is created by comments.
 *)
(* A checked interpretation of the Towers four-cell admissions model as a
   standard finite Boolean product space. No new probability axioms,
   recursive event structure, or bespoke finite-sum implementation. *)
From Stdlib Require Import Reals Lra Psatz List Bool.
Require Import Admissions FiniteSum FiniteUnion FiniteMoments FiniteBridge.
Import ListNotations.
Open Scope R_scope.

(* The four outcomes are the complete Cartesian product of two Booleans. *)
(**
   [four_cell_samples] (definition).
   Meaning: Relates explicit finite outcomes and weights to the corresponding
   marginal or joint quantity.
   Formal construction: list (bool * bool) := list_prod [true; false] [true;
   false].
   Hypotheses: A definition; its parameters and fields appear in the signature,
   with no silent statistical assumptions.
   Implementation: application of already-proved lemmas, explicit case
   analysis; notably four_cell_samples., in_prod..
   Library discipline: Stdlib.List.list_prod, in_prod and length_prod, plus
   Admissions, FiniteUnion, FiniteMoments and FiniteBridge.
   Scope: The model proves exact four-cell algebra; it does not introduce
   independent events or an estimated admission-rate distribution.
 *)
Definition four_cell_samples : list (bool * bool) :=
  list_prod [true; false] [true; false].

(* Stdlib.List.in_prod and length_prod certify that the enumeration
   covers every Boolean pair and has the expected four outcomes. *)
(**
   [four_cell_samples_complete] (theorem).
   Meaning: Relates explicit finite outcomes and weights to the corresponding
   marginal or joint quantity.
   Formal conclusion: forall outcome : bool * bool, In outcome
   four_cell_samples.
   Hypotheses: Requires enumerated-list membership where shown in the
   statement; all other constraints remain explicit.
   Proof outline: application of already-proved lemmas, explicit case analysis;
   notably four_cell_samples., in_prod..
   Library discipline: Stdlib.List.list_prod, in_prod and length_prod, plus
   Admissions, FiniteUnion, FiniteMoments and FiniteBridge.
   Scope: The model proves exact four-cell algebra; it does not introduce
   independent events or an estimated admission-rate distribution.
 *)
Theorem four_cell_samples_complete :
  forall outcome : bool * bool, In outcome four_cell_samples.
Proof.
  intros [a b].
  unfold four_cell_samples.
  apply in_prod.
  - destruct a; simpl; auto.
  - destruct b; simpl; auto.
Qed.

(**
   [four_cell_samples_length] (theorem).
   Meaning: Proves a structural list identity using Rocq's standard list
   operations.
   Formal conclusion: length four_cell_samples = 4%nat.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: equational rewriting, definitional computation; notably
   four_cell_samples., length_prod..
   Library discipline: Stdlib.List.list_prod, in_prod and length_prod, plus
   Admissions, FiniteUnion, FiniteMoments and FiniteBridge.
   Scope: The model proves exact four-cell algebra; it does not introduce
   independent events or an estimated admission-rate distribution.
 *)
Theorem four_cell_samples_length :
  length four_cell_samples = 4%nat.
Proof.
  unfold four_cell_samples.
  rewrite length_prod.
  reflexivity.
Qed.

(**
   [four_cell_weight] (definition).
   Meaning: Relates explicit finite outcomes and weights to the corresponding
   marginal or joint quantity.
   Formal construction: (m : TwoEventModel) (outcome : bool * bool) : R :=
   match outcome with | (true, true) => joint m | (true, false) => only_A m |
   (false, true) => only_B m | (false, false) => neither m end.
   Hypotheses: A definition; its parameters and fields appear in the signature,
   with no silent statistical assumptions.
   Implementation: application of already-proved lemmas, explicit case
   analysis; notably joint_nonnegative., only_A_nonnegative.,
   only_B_nonnegative..
   Library discipline: Stdlib.List.list_prod, in_prod and length_prod, plus
   Admissions, FiniteUnion, FiniteMoments and FiniteBridge.
   Scope: The model proves exact four-cell algebra; it does not introduce
   independent events or an estimated admission-rate distribution.
 *)
Definition four_cell_weight (m : TwoEventModel)
    (outcome : bool * bool) : R :=
  match outcome with
  | (true, true) => joint m
  | (true, false) => only_A m
  | (false, true) => only_B m
  | (false, false) => neither m
  end.

(**
   [four_cell_A] (definition).
   Meaning: Relates explicit finite outcomes and weights to the corresponding
   marginal or joint quantity.
   Formal construction: (outcome : bool * bool) : bool := fst outcome.
   Hypotheses: A definition; its parameters and fields appear in the signature,
   with no silent statistical assumptions.
   Implementation: application of already-proved lemmas, explicit case
   analysis; notably joint_nonnegative., only_A_nonnegative.,
   only_B_nonnegative..
   Library discipline: Stdlib.List.list_prod, in_prod and length_prod, plus
   Admissions, FiniteUnion, FiniteMoments and FiniteBridge.
   Scope: The model proves exact four-cell algebra; it does not introduce
   independent events or an estimated admission-rate distribution.
 *)
Definition four_cell_A (outcome : bool * bool) : bool := fst outcome.
(**
   [four_cell_B] (definition).
   Meaning: Relates explicit finite outcomes and weights to the corresponding
   marginal or joint quantity.
   Formal construction: (outcome : bool * bool) : bool := snd outcome.
   Hypotheses: A definition; its parameters and fields appear in the signature,
   with no silent statistical assumptions.
   Implementation: application of already-proved lemmas, explicit case
   analysis; notably joint_nonnegative., only_A_nonnegative.,
   only_B_nonnegative..
   Library discipline: Stdlib.List.list_prod, in_prod and length_prod, plus
   Admissions, FiniteUnion, FiniteMoments and FiniteBridge.
   Scope: The model proves exact four-cell algebra; it does not introduce
   independent events or an estimated admission-rate distribution.
 *)
Definition four_cell_B (outcome : bool * bool) : bool := snd outcome.
(**
   [four_cell_exactly_one] (definition).
   Meaning: Relates explicit finite outcomes and weights to the corresponding
   marginal or joint quantity.
   Formal construction: (outcome : bool * bool) : bool := xorb (four_cell_A
   outcome) (four_cell_B outcome).
   Hypotheses: A definition; its parameters and fields appear in the signature,
   with no silent statistical assumptions.
   Implementation: application of already-proved lemmas, explicit case
   analysis; notably joint_nonnegative., only_A_nonnegative.,
   only_B_nonnegative..
   Library discipline: Stdlib.List.list_prod, in_prod and length_prod, plus
   Admissions, FiniteUnion, FiniteMoments and FiniteBridge.
   Scope: The model proves exact four-cell algebra; it does not introduce
   independent events or an estimated admission-rate distribution.
 *)
Definition four_cell_exactly_one (outcome : bool * bool) : bool :=
  xorb (four_cell_A outcome) (four_cell_B outcome).

(**
   [four_cell_weight_nonnegative] (theorem).
   Meaning: Relates explicit finite outcomes and weights to the corresponding
   marginal or joint quantity.
   Formal conclusion: forall m outcome, 0 <= four_cell_weight m outcome.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: application of already-proved lemmas, explicit case analysis;
   notably joint_nonnegative., only_A_nonnegative., only_B_nonnegative..
   Library discipline: Stdlib.List.list_prod, in_prod and length_prod, plus
   Admissions, FiniteUnion, FiniteMoments and FiniteBridge.
   Scope: The model proves exact four-cell algebra; it does not introduce
   independent events or an estimated admission-rate distribution.
 *)
Theorem four_cell_weight_nonnegative :
  forall m outcome, 0 <= four_cell_weight m outcome.
Proof.
  intros m [a b].
  destruct a, b; simpl.
  - apply joint_nonnegative.
  - apply only_A_nonnegative.
  - apply only_B_nonnegative.
  - apply neither_nonnegative.
Qed.

(**
   [four_cell_total_mass] (theorem).
   Meaning: Relates explicit finite outcomes and weights to the corresponding
   marginal or joint quantity.
   Formal conclusion: forall m, @FiniteMoments.total_mass (bool * bool)
   four_cell_samples (four_cell_weight m) = 1.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: application of already-proved lemmas, Stdlib Lra linear
   arithmetic; notably FiniteMoments.total_mass, cells_sum_to_one.
   Library discipline: Stdlib.List.list_prod, in_prod and length_prod, plus
   Admissions, FiniteUnion, FiniteMoments and FiniteBridge.
   Scope: The model proves exact four-cell algebra; it does not introduce
   independent events or an estimated admission-rate distribution.
 *)
Theorem four_cell_total_mass :
  forall m,
    @FiniteMoments.total_mass (bool * bool)
      four_cell_samples (four_cell_weight m) = 1.
Proof.
  intro m.
  unfold FiniteMoments.total_mass, FiniteMoments.sum_finite,
    FiniteSum.finite_sum, four_cell_samples, four_cell_weight.
  simpl.
  pose proof (cells_sum_to_one m).
  lra.
Qed.

(**
   [four_cell_first_marginal] (theorem).
   Meaning: Relates explicit finite outcomes and weights to the corresponding
   marginal or joint quantity.
   Formal conclusion: forall m, @FiniteUnion.finite_prob (bool * bool)
   (four_cell_weight m) four_cell_samples four_cell_A = p_A m.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: ring/field normalization; notably FiniteUnion.finite_prob.
   Library discipline: Stdlib.List.list_prod, in_prod and length_prod, plus
   Admissions, FiniteUnion, FiniteMoments and FiniteBridge.
   Scope: The model proves exact four-cell algebra; it does not introduce
   independent events or an estimated admission-rate distribution.
 *)
Theorem four_cell_first_marginal :
  forall m,
    @FiniteUnion.finite_prob (bool * bool)
      (four_cell_weight m) four_cell_samples four_cell_A = p_A m.
Proof.
  intro m.
  unfold FiniteUnion.finite_prob, FiniteUnion.finite_sum,
    FiniteSum.finite_sum, four_cell_samples, four_cell_weight,
    four_cell_A, FiniteUnion.indicator, p_A.
  simpl; ring.
Qed.

(**
   [four_cell_second_marginal] (theorem).
   Meaning: Relates explicit finite outcomes and weights to the corresponding
   marginal or joint quantity.
   Formal conclusion: forall m, @FiniteUnion.finite_prob (bool * bool)
   (four_cell_weight m) four_cell_samples four_cell_B = p_B m.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: ring/field normalization; notably FiniteUnion.finite_prob.
   Library discipline: Stdlib.List.list_prod, in_prod and length_prod, plus
   Admissions, FiniteUnion, FiniteMoments and FiniteBridge.
   Scope: The model proves exact four-cell algebra; it does not introduce
   independent events or an estimated admission-rate distribution.
 *)
Theorem four_cell_second_marginal :
  forall m,
    @FiniteUnion.finite_prob (bool * bool)
      (four_cell_weight m) four_cell_samples four_cell_B = p_B m.
Proof.
  intro m.
  unfold FiniteUnion.finite_prob, FiniteUnion.finite_sum,
    FiniteSum.finite_sum, four_cell_samples, four_cell_weight,
    four_cell_B, FiniteUnion.indicator, p_B.
  simpl; ring.
Qed.

(**
   [four_cell_intersection_mass] (theorem).
   Meaning: Controls union/intersection mass for Boolean events through finite
   probability algebra.
   Formal conclusion: forall m, @FiniteUnion.finite_prob (bool * bool)
   (four_cell_weight m) four_cell_samples (fun x => andb (four_cell_A x)
   (four_cell_B x)) = p_both m.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: ring/field normalization; notably FiniteUnion.finite_prob.
   Library discipline: Stdlib.List.list_prod, in_prod and length_prod, plus
   Admissions, FiniteUnion, FiniteMoments and FiniteBridge.
   Scope: The model proves exact four-cell algebra; it does not introduce
   independent events or an estimated admission-rate distribution.
 *)
Theorem four_cell_intersection_mass :
  forall m,
    @FiniteUnion.finite_prob (bool * bool)
      (four_cell_weight m) four_cell_samples
      (fun x => andb (four_cell_A x) (four_cell_B x)) = p_both m.
Proof.
  intro m.
  unfold FiniteUnion.finite_prob, FiniteUnion.finite_sum,
    FiniteSum.finite_sum, four_cell_samples, four_cell_weight,
    four_cell_A, four_cell_B, FiniteUnion.indicator, p_both.
  simpl; ring.
Qed.

(**
   [four_cell_union_mass] (theorem).
   Meaning: Controls union/intersection mass for Boolean events through finite
   probability algebra.
   Formal conclusion: forall m, @FiniteUnion.union_prob (bool * bool)
   (four_cell_weight m) four_cell_samples [four_cell_A; four_cell_B] = p_either
   m.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: ring/field normalization; notably FiniteUnion.union_prob.
   Library discipline: Stdlib.List.list_prod, in_prod and length_prod, plus
   Admissions, FiniteUnion, FiniteMoments and FiniteBridge.
   Scope: The model proves exact four-cell algebra; it does not introduce
   independent events or an estimated admission-rate distribution.
 *)
Theorem four_cell_union_mass :
  forall m,
    @FiniteUnion.union_prob (bool * bool)
      (four_cell_weight m) four_cell_samples
      [four_cell_A; four_cell_B] = p_either m.
Proof.
  intro m.
  unfold FiniteUnion.union_prob, FiniteUnion.any_event,
    FiniteUnion.finite_prob, FiniteUnion.finite_sum,
    FiniteSum.finite_sum, four_cell_samples, four_cell_weight,
    four_cell_A, four_cell_B, FiniteUnion.indicator, p_either.
  simpl; ring.
Qed.

(**
   [four_cell_exactly_one_mass] (theorem).
   Meaning: Relates explicit finite outcomes and weights to the corresponding
   marginal or joint quantity.
   Formal conclusion: forall m, @FiniteUnion.finite_prob (bool * bool)
   (four_cell_weight m) four_cell_samples four_cell_exactly_one = p_exactly_one
   m.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: ring/field normalization; notably FiniteUnion.finite_prob.
   Library discipline: Stdlib.List.list_prod, in_prod and length_prod, plus
   Admissions, FiniteUnion, FiniteMoments and FiniteBridge.
   Scope: The model proves exact four-cell algebra; it does not introduce
   independent events or an estimated admission-rate distribution.
 *)
Theorem four_cell_exactly_one_mass :
  forall m,
    @FiniteUnion.finite_prob (bool * bool)
      (four_cell_weight m) four_cell_samples four_cell_exactly_one =
    p_exactly_one m.
Proof.
  intro m.
  unfold FiniteUnion.finite_prob, FiniteUnion.finite_sum,
    FiniteSum.finite_sum, four_cell_samples, four_cell_weight,
    four_cell_exactly_one, four_cell_A, four_cell_B,
    FiniteUnion.indicator, p_exactly_one.
  simpl; ring.
Qed.

(* Reuse the existing generic event-to-moment bridge, rather than
   recalculating covariance in the specialized four-cell structure. *)
(**
   [four_cell_indicator_covariance] (theorem).
   Meaning: Establishes an exact covariance identity or bound for the specified
   finite score functions.
   Formal conclusion: forall m, @FiniteMoments.covariance (bool * bool)
   four_cell_samples (four_cell_weight m) (fun x => FiniteUnion.indicator
   (four_cell_A x)) (fun x => FiniteUnion.indicator (four_cell_B x)) = p_both m
   - p_A m * p_B m.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: equational rewriting, definitional computation; notably
   finite_event_indicator_covariance, four_cell_intersection_mass.
   Library discipline: Stdlib.List.list_prod, in_prod and length_prod, plus
   Admissions, FiniteUnion, FiniteMoments and FiniteBridge.
   Scope: The model proves exact four-cell algebra; it does not introduce
   independent events or an estimated admission-rate distribution.
 *)
Theorem four_cell_indicator_covariance :
  forall m,
    @FiniteMoments.covariance (bool * bool)
      four_cell_samples (four_cell_weight m)
      (fun x => FiniteUnion.indicator (four_cell_A x))
      (fun x => FiniteUnion.indicator (four_cell_B x)) =
    p_both m - p_A m * p_B m.
Proof.
  intro m.
  rewrite (finite_event_indicator_covariance
    (bool * bool) four_cell_samples
    (four_cell_weight m) four_cell_A four_cell_B).
  rewrite four_cell_intersection_mass, four_cell_first_marginal,
    four_cell_second_marginal.
  reflexivity.
Qed.

(**
   [four_cell_indicator_independence_criterion] (theorem).
   Meaning: Makes an event-independence or conditional-probability relationship
   explicit, including necessary denominators.
   Formal conclusion: forall m, @FiniteMoments.covariance (bool * bool)
   four_cell_samples (four_cell_weight m) (fun x => FiniteUnion.indicator
   (four_cell_A x)) (fun x => FiniteUnion.indicator (four_cell_B x)) = 0 <->
   joint m * neither m = only_A m * only_B m.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: equational rewriting, Stdlib Lra linear arithmetic; notably
   four_cell_indicator_covariance., binary_indicator_covariance_numerator..
   Library discipline: Stdlib.List.list_prod, in_prod and length_prod, plus
   Admissions, FiniteUnion, FiniteMoments and FiniteBridge.
   Scope: The model proves exact four-cell algebra; it does not introduce
   independent events or an estimated admission-rate distribution.
 *)
Theorem four_cell_indicator_independence_criterion :
  forall m,
    @FiniteMoments.covariance (bool * bool)
      four_cell_samples (four_cell_weight m)
      (fun x => FiniteUnion.indicator (four_cell_A x))
      (fun x => FiniteUnion.indicator (four_cell_B x)) = 0 <->
    joint m * neither m = only_A m * only_B m.
Proof.
  intro m.
  rewrite four_cell_indicator_covariance.
  rewrite binary_indicator_covariance_numerator.
  split; intro H; lra.
Qed.

(**
   [four_cell_first_indicator_variance] (theorem).
   Meaning: Establishes a finite-sample variance identity or bound, including
   all stated scaling assumptions.
   Formal conclusion: forall m, @FiniteMoments.variance (bool * bool)
   four_cell_samples (four_cell_weight m) (fun x => FiniteUnion.indicator
   (four_cell_A x)) = p_A m * (1 - p_A m).
   Hypotheses: Requires unit-variance or stated moment hypotheses where shown
   in the statement; all other constraints remain explicit.
   Proof outline: equational rewriting, definitional computation; notably
   finite_event_indicator_variance, four_cell_first_marginal..
   Library discipline: Stdlib.List.list_prod, in_prod and length_prod, plus
   Admissions, FiniteUnion, FiniteMoments and FiniteBridge.
   Scope: The model proves exact four-cell algebra; it does not introduce
   independent events or an estimated admission-rate distribution.
 *)
Theorem four_cell_first_indicator_variance :
  forall m,
    @FiniteMoments.variance (bool * bool)
      four_cell_samples (four_cell_weight m)
      (fun x => FiniteUnion.indicator (four_cell_A x)) =
      p_A m * (1 - p_A m).
Proof.
  intro m.
  rewrite (finite_event_indicator_variance
    (bool * bool) four_cell_samples (four_cell_weight m)
    four_cell_A).
  rewrite four_cell_first_marginal.
  reflexivity.
Qed.

(**
   [four_cell_second_indicator_variance] (theorem).
   Meaning: Establishes a finite-sample variance identity or bound, including
   all stated scaling assumptions.
   Formal conclusion: forall m, @FiniteMoments.variance (bool * bool)
   four_cell_samples (four_cell_weight m) (fun x => FiniteUnion.indicator
   (four_cell_B x)) = p_B m * (1 - p_B m).
   Hypotheses: Requires unit-variance or stated moment hypotheses where shown
   in the statement; all other constraints remain explicit.
   Proof outline: equational rewriting, definitional computation; notably
   finite_event_indicator_variance, four_cell_second_marginal..
   Library discipline: Stdlib.List.list_prod, in_prod and length_prod, plus
   Admissions, FiniteUnion, FiniteMoments and FiniteBridge.
   Scope: The model proves exact four-cell algebra; it does not introduce
   independent events or an estimated admission-rate distribution.
 *)
Theorem four_cell_second_indicator_variance :
  forall m,
    @FiniteMoments.variance (bool * bool)
      four_cell_samples (four_cell_weight m)
      (fun x => FiniteUnion.indicator (four_cell_B x)) =
      p_B m * (1 - p_B m).
Proof.
  intro m.
  rewrite (finite_event_indicator_variance
    (bool * bool) four_cell_samples (four_cell_weight m)
    four_cell_B).
  rewrite four_cell_second_marginal.
  reflexivity.
Qed.
