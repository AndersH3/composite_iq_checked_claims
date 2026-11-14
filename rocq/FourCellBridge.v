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
   [four_cell_samples] (definition) — Interpretation of the admissions four-cell
   record as a finite Boolean product.
   Mathematical meaning: Defines four cell samples using explicit Rocq operations, so
   later theorems can refer to one stable mathematical object.
   Exact declaration: Definition four_cell_samples : list (bool * bool) := list_prod
   [true; false] [true; false].
   Premises and side conditions: Only the declared parameters, data fields, and types
   constrain this construction; no extraneous postulates are introduced.
   Proof/definition method: Definitionally uses the shown expression/record
   constructor; proof obligations, if any, are attached to this declaration alone.
   Library reuse: Stdlib.List.list_prod/in_prod/length_prod and
   Admissions/FiniteUnion/FiniteMoments.
   Boundary: Exactly the four Boolean pairs and the record-defined cell weights; no
   Gaussian model or independence is assumed.
 *)
Definition four_cell_samples : list (bool * bool) :=
  list_prod [true; false] [true; false].

(* Stdlib.List.in_prod and length_prod certify that the enumeration
   covers every Boolean pair and has the expected four outcomes. *)
(**
   [four_cell_samples_complete] (theorem) — Interpretation of the admissions
   four-cell record as a finite Boolean product.
   Mathematical meaning: Relates finite outcome weights to the stated marginal,
   joint, or enumerated-event quantity.
   Exact checked proposition: Theorem four_cell_samples_complete : forall outcome :
   bool * bool, In outcome four_cell_samples.
   Premises and side conditions: The displayed hypotheses include sample or list
   membership. No further assumptions are implicit.
   Proof/definition method: Kernel proof uses case analysis, reuse of previously
   established lemmas, definitional reduction; references include four_cell_samples.,
   in_prod..
   Library reuse: Stdlib.List.list_prod/in_prod/length_prod and
   Admissions/FiniteUnion/FiniteMoments.
   Boundary: Exactly the four Boolean pairs and the record-defined cell weights; no
   Gaussian model or independence is assumed.
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
   [four_cell_samples_length] (theorem) — Interpretation of the admissions four-cell
   record as a finite Boolean product.
   Mathematical meaning: Proves a list-structural invariant without custom sorting or
   indexing.
   Exact checked proposition: Theorem four_cell_samples_length : length
   four_cell_samples = 4%nat.
   Premises and side conditions: All required premises are written in the signature.
   No independence or distributional assumption is silently supplied.
   Proof/definition method: Kernel proof uses rewriting of equalities, definitional
   reduction; references include four_cell_samples., length_prod..
   Library reuse: Stdlib.List.list_prod/in_prod/length_prod and
   Admissions/FiniteUnion/FiniteMoments.
   Boundary: Exactly the four Boolean pairs and the record-defined cell weights; no
   Gaussian model or independence is assumed.
 *)
Theorem four_cell_samples_length :
  length four_cell_samples = 4%nat.
Proof.
  unfold four_cell_samples.
  rewrite length_prod.
  reflexivity.
Qed.

(**
   [four_cell_weight] (definition) — Interpretation of the admissions four-cell
   record as a finite Boolean product.
   Mathematical meaning: Defines four cell weight using explicit Rocq operations, so
   later theorems can refer to one stable mathematical object.
   Exact declaration: Definition four_cell_weight (m : TwoEventModel) (outcome : bool
   * bool) : R := match outcome with | (true, true) => joint m | (true, false) =>
   only_A m | (false, true) => only_B m | (false, false) => neither m end.
   Premises and side conditions: Only the declared parameters, data fields, and types
   constrain this construction; no extraneous postulates are introduced.
   Proof/definition method: Definitionally uses the shown expression/record
   constructor; proof obligations, if any, are attached to this declaration alone.
   Library reuse: Stdlib.List.list_prod/in_prod/length_prod and
   Admissions/FiniteUnion/FiniteMoments.
   Boundary: Exactly the four Boolean pairs and the record-defined cell weights; no
   Gaussian model or independence is assumed.
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
   [four_cell_A] (definition) — Interpretation of the admissions four-cell record as
   a finite Boolean product.
   Mathematical meaning: Defines four cell A using explicit Rocq operations, so later
   theorems can refer to one stable mathematical object.
   Exact declaration: Definition four_cell_A (outcome : bool * bool) : bool := fst
   outcome.
   Premises and side conditions: Only the declared parameters, data fields, and types
   constrain this construction; no extraneous postulates are introduced.
   Proof/definition method: Definitionally uses the shown expression/record
   constructor; proof obligations, if any, are attached to this declaration alone.
   Library reuse: Stdlib.List.list_prod/in_prod/length_prod and
   Admissions/FiniteUnion/FiniteMoments.
   Boundary: Exactly the four Boolean pairs and the record-defined cell weights; no
   Gaussian model or independence is assumed.
 *)
Definition four_cell_A (outcome : bool * bool) : bool := fst outcome.
(**
   [four_cell_B] (definition) — Interpretation of the admissions four-cell record as
   a finite Boolean product.
   Mathematical meaning: Defines four cell B using explicit Rocq operations, so later
   theorems can refer to one stable mathematical object.
   Exact declaration: Definition four_cell_B (outcome : bool * bool) : bool := snd
   outcome.
   Premises and side conditions: Only the declared parameters, data fields, and types
   constrain this construction; no extraneous postulates are introduced.
   Proof/definition method: Definitionally uses the shown expression/record
   constructor; proof obligations, if any, are attached to this declaration alone.
   Library reuse: Stdlib.List.list_prod/in_prod/length_prod and
   Admissions/FiniteUnion/FiniteMoments.
   Boundary: Exactly the four Boolean pairs and the record-defined cell weights; no
   Gaussian model or independence is assumed.
 *)
Definition four_cell_B (outcome : bool * bool) : bool := snd outcome.
(**
   [four_cell_exactly_one] (definition) — Interpretation of the admissions four-cell
   record as a finite Boolean product.
   Mathematical meaning: Defines four cell exactly one using explicit Rocq
   operations, so later theorems can refer to one stable mathematical object.
   Exact declaration: Definition four_cell_exactly_one (outcome : bool * bool) : bool
   := xorb (four_cell_A outcome) (four_cell_B outcome).
   Premises and side conditions: Only the declared parameters, data fields, and types
   constrain this construction; no extraneous postulates are introduced.
   Proof/definition method: Definitionally uses the shown expression/record
   constructor; proof obligations, if any, are attached to this declaration alone.
   Library reuse: Stdlib.List.list_prod/in_prod/length_prod and
   Admissions/FiniteUnion/FiniteMoments.
   Boundary: Exactly the four Boolean pairs and the record-defined cell weights; no
   Gaussian model or independence is assumed.
 *)
Definition four_cell_exactly_one (outcome : bool * bool) : bool :=
  xorb (four_cell_A outcome) (four_cell_B outcome).

(**
   [four_cell_weight_nonnegative] (theorem) — Interpretation of the admissions
   four-cell record as a finite Boolean product.
   Mathematical meaning: Relates finite outcome weights to the stated marginal,
   joint, or enumerated-event quantity.
   Exact checked proposition: Theorem four_cell_weight_nonnegative : forall m
   outcome, 0 <= four_cell_weight m outcome.
   Premises and side conditions: The displayed hypotheses include explicit nonzero or
   strict-positive numerical conditions. No further assumptions are implicit.
   Proof/definition method: Kernel proof uses case analysis, reuse of previously
   established lemmas, definitional reduction; references include joint_nonnegative.,
   only_A_nonnegative., only_B_nonnegative..
   Library reuse: Stdlib.List.list_prod/in_prod/length_prod and
   Admissions/FiniteUnion/FiniteMoments.
   Boundary: Exactly the four Boolean pairs and the record-defined cell weights; no
   Gaussian model or independence is assumed.
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
   [four_cell_total_mass] (theorem) — Interpretation of the admissions four-cell
   record as a finite Boolean product.
   Mathematical meaning: Relates finite outcome weights to the stated marginal,
   joint, or enumerated-event quantity.
   Exact checked proposition: Theorem four_cell_total_mass : forall m,
   @FiniteMoments.total_mass (bool * bool) four_cell_samples (four_cell_weight m) =
   1.
   Premises and side conditions: All required premises are written in the signature.
   No independence or distributional assumption is silently supplied.
   Proof/definition method: Kernel proof uses reuse of previously established lemmas,
   linear real arithmetic (Lra), definitional reduction; references include
   FiniteMoments.total_mass, cells_sum_to_one.
   Library reuse: Stdlib.List.list_prod/in_prod/length_prod and
   Admissions/FiniteUnion/FiniteMoments.
   Boundary: Exactly the four Boolean pairs and the record-defined cell weights; no
   Gaussian model or independence is assumed.
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
   [four_cell_first_marginal] (theorem) — Interpretation of the admissions four-cell
   record as a finite Boolean product.
   Mathematical meaning: Relates finite outcome weights to the stated marginal,
   joint, or enumerated-event quantity.
   Exact checked proposition: Theorem four_cell_first_marginal : forall m,
   @FiniteUnion.finite_prob (bool * bool) (four_cell_weight m) four_cell_samples
   four_cell_A = p_A m.
   Premises and side conditions: All required premises are written in the signature.
   No independence or distributional assumption is silently supplied.
   Proof/definition method: Kernel proof uses ring/field normalization, definitional
   reduction; references include FiniteUnion.finite_prob.
   Library reuse: Stdlib.List.list_prod/in_prod/length_prod and
   Admissions/FiniteUnion/FiniteMoments.
   Boundary: Exactly the four Boolean pairs and the record-defined cell weights; no
   Gaussian model or independence is assumed.
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
   [four_cell_second_marginal] (theorem) — Interpretation of the admissions four-cell
   record as a finite Boolean product.
   Mathematical meaning: Relates finite outcome weights to the stated marginal,
   joint, or enumerated-event quantity.
   Exact checked proposition: Theorem four_cell_second_marginal : forall m,
   @FiniteUnion.finite_prob (bool * bool) (four_cell_weight m) four_cell_samples
   four_cell_B = p_B m.
   Premises and side conditions: All required premises are written in the signature.
   No independence or distributional assumption is silently supplied.
   Proof/definition method: Kernel proof uses ring/field normalization, definitional
   reduction; references include FiniteUnion.finite_prob.
   Library reuse: Stdlib.List.list_prod/in_prod/length_prod and
   Admissions/FiniteUnion/FiniteMoments.
   Boundary: Exactly the four Boolean pairs and the record-defined cell weights; no
   Gaussian model or independence is assumed.
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
   [four_cell_intersection_mass] (theorem) — Interpretation of the admissions
   four-cell record as a finite Boolean product.
   Mathematical meaning: Proves a Boolean-event union/intersection fact or a
   corresponding probability bound.
   Exact checked proposition: Theorem four_cell_intersection_mass : forall m,
   @FiniteUnion.finite_prob (bool * bool) (four_cell_weight m) four_cell_samples (fun
   x => andb (four_cell_A x) (four_cell_B x)) = p_both m.
   Premises and side conditions: All required premises are written in the signature.
   No independence or distributional assumption is silently supplied.
   Proof/definition method: Kernel proof uses ring/field normalization, definitional
   reduction; references include FiniteUnion.finite_prob.
   Library reuse: Stdlib.List.list_prod/in_prod/length_prod and
   Admissions/FiniteUnion/FiniteMoments.
   Boundary: Exactly the four Boolean pairs and the record-defined cell weights; no
   Gaussian model or independence is assumed.
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
   [four_cell_union_mass] (theorem) — Interpretation of the admissions four-cell
   record as a finite Boolean product.
   Mathematical meaning: Proves a Boolean-event union/intersection fact or a
   corresponding probability bound.
   Exact checked proposition: Theorem four_cell_union_mass : forall m,
   @FiniteUnion.union_prob (bool * bool) (four_cell_weight m) four_cell_samples
   [four_cell_A; four_cell_B] = p_either m.
   Premises and side conditions: All required premises are written in the signature.
   No independence or distributional assumption is silently supplied.
   Proof/definition method: Kernel proof uses ring/field normalization, definitional
   reduction; references include FiniteUnion.union_prob.
   Library reuse: Stdlib.List.list_prod/in_prod/length_prod and
   Admissions/FiniteUnion/FiniteMoments.
   Boundary: Exactly the four Boolean pairs and the record-defined cell weights; no
   Gaussian model or independence is assumed.
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
   [four_cell_exactly_one_mass] (theorem) — Interpretation of the admissions
   four-cell record as a finite Boolean product.
   Mathematical meaning: Relates finite outcome weights to the stated marginal,
   joint, or enumerated-event quantity.
   Exact checked proposition: Theorem four_cell_exactly_one_mass : forall m,
   @FiniteUnion.finite_prob (bool * bool) (four_cell_weight m) four_cell_samples
   four_cell_exactly_one = p_exactly_one m.
   Premises and side conditions: All required premises are written in the signature.
   No independence or distributional assumption is silently supplied.
   Proof/definition method: Kernel proof uses ring/field normalization, definitional
   reduction; references include FiniteUnion.finite_prob.
   Library reuse: Stdlib.List.list_prod/in_prod/length_prod and
   Admissions/FiniteUnion/FiniteMoments.
   Boundary: Exactly the four Boolean pairs and the record-defined cell weights; no
   Gaussian model or independence is assumed.
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
   [four_cell_indicator_covariance] (theorem) — Interpretation of the admissions
   four-cell record as a finite Boolean product.
   Mathematical meaning: Derives a covariance identity or inequality from finite
   weighted expectations.
   Exact checked proposition: Theorem four_cell_indicator_covariance : forall m,
   @FiniteMoments.covariance (bool * bool) four_cell_samples (four_cell_weight m)
   (fun x => FiniteUnion.indicator (four_cell_A x)) (fun x => FiniteUnion.indicator
   (four_cell_B x)) = p_both m - p_A m * p_B m.
   Premises and side conditions: All required premises are written in the signature.
   No independence or distributional assumption is silently supplied.
   Proof/definition method: Kernel proof uses rewriting of equalities, definitional
   reduction; references include finite_event_indicator_covariance,
   four_cell_intersection_mass.
   Library reuse: Stdlib.List.list_prod/in_prod/length_prod and
   Admissions/FiniteUnion/FiniteMoments.
   Boundary: Exactly the four Boolean pairs and the record-defined cell weights; no
   Gaussian model or independence is assumed.
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
   [four_cell_indicator_independence_criterion] (theorem) — Interpretation of the
   admissions four-cell record as a finite Boolean product.
   Mathematical meaning: Formalizes the indicated independence or conditional-mass
   relationship, including explicit side conditions.
   Exact checked proposition: Theorem four_cell_indicator_independence_criterion :
   forall m, @FiniteMoments.covariance (bool * bool) four_cell_samples
   (four_cell_weight m) (fun x => FiniteUnion.indicator (four_cell_A x)) (fun x =>
   FiniteUnion.indicator (four_cell_B x)) = 0 <-> joint m * neither m = only_A m *
   only_B m.
   Premises and side conditions: The displayed hypotheses include explicit nonzero or
   strict-positive numerical conditions. No further assumptions are implicit.
   Proof/definition method: Kernel proof uses rewriting of equalities, linear real
   arithmetic (Lra); references include four_cell_indicator_covariance.,
   binary_indicator_covariance_numerator..
   Library reuse: Stdlib.List.list_prod/in_prod/length_prod and
   Admissions/FiniteUnion/FiniteMoments.
   Boundary: Exactly the four Boolean pairs and the record-defined cell weights; no
   Gaussian model or independence is assumed.
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
   [four_cell_first_indicator_variance] (theorem) — Interpretation of the admissions
   four-cell record as a finite Boolean product.
   Mathematical meaning: Identifies the precise variance, scaling behavior, or
   variance bound for the stated score construction.
   Exact checked proposition: Theorem four_cell_first_indicator_variance : forall m,
   @FiniteMoments.variance (bool * bool) four_cell_samples (four_cell_weight m) (fun
   x => FiniteUnion.indicator (four_cell_A x)) = p_A m * (1 - p_A m).
   Premises and side conditions: All required premises are written in the signature.
   No independence or distributional assumption is silently supplied.
   Proof/definition method: Kernel proof uses rewriting of equalities, definitional
   reduction; references include finite_event_indicator_variance,
   four_cell_first_marginal..
   Library reuse: Stdlib.List.list_prod/in_prod/length_prod and
   Admissions/FiniteUnion/FiniteMoments.
   Boundary: Exactly the four Boolean pairs and the record-defined cell weights; no
   Gaussian model or independence is assumed.
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
   [four_cell_second_indicator_variance] (theorem) — Interpretation of the admissions
   four-cell record as a finite Boolean product.
   Mathematical meaning: Identifies the precise variance, scaling behavior, or
   variance bound for the stated score construction.
   Exact checked proposition: Theorem four_cell_second_indicator_variance : forall m,
   @FiniteMoments.variance (bool * bool) four_cell_samples (four_cell_weight m) (fun
   x => FiniteUnion.indicator (four_cell_B x)) = p_B m * (1 - p_B m).
   Premises and side conditions: All required premises are written in the signature.
   No independence or distributional assumption is silently supplied.
   Proof/definition method: Kernel proof uses rewriting of equalities, definitional
   reduction; references include finite_event_indicator_variance,
   four_cell_second_marginal..
   Library reuse: Stdlib.List.list_prod/in_prod/length_prod and
   Admissions/FiniteUnion/FiniteMoments.
   Boundary: Exactly the four Boolean pairs and the record-defined cell weights; no
   Gaussian model or independence is assumed.
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

(* The report's conditional ratios are interpreted using generic Boolean
   events; positive conditioning mass is explicit in each statement. *)

(**
   [four_cell_second_without_first_mass] (theorem) — Four-cell event and conditional probability bridge.
   Mathematical meaning: The B-only cell equals the mass of the Boolean event B and not A over the four explicitly enumerated outcomes.
   Exact checked proposition: For any TwoEventModel m, finite_prob weights samples (fun x => andb (negb (A x)) (B x)) = only_B m.
   Premises and side conditions: The record provides four nonnegative cells totaling one; no conditional denominator or independence assumption is needed.
   Proof/definition method: Expand the existing finite_prob/finite_sum folds and standard Boolean-product enumeration; simpl and ring close the exact identity.
   Library reuse: Stdlib.List.list_prod, Stdlib.Bool.andb/negb, FiniteUnion.finite_prob, FiniteSum.finite_sum, Stdlib.Reals ring.
   Boundary: A four-outcome probability identity, not an estimate of observed admission rates.
 *)
Theorem four_cell_second_without_first_mass :
  forall m,
    @FiniteUnion.finite_prob (bool * bool)
      (four_cell_weight m) four_cell_samples
      (fun x => andb (negb (four_cell_A x)) (four_cell_B x)) =
    only_B m.
Proof.
  intro m.
  unfold FiniteUnion.finite_prob, FiniteUnion.finite_sum,
    FiniteSum.finite_sum, four_cell_samples, four_cell_weight,
    four_cell_A, four_cell_B, FiniteUnion.indicator.
  simpl; ring.
Qed.

(**
   [four_cell_conditional_B_given_A] (theorem) — Four-cell event and conditional probability bridge.
   Mathematical meaning: The generic Boolean-event ratio P(A and B)/P(A) matches the report's B-given-A conditional.
   Exact checked proposition: For positive p_A m, intersection-event mass divided by A-event mass equals conditional_B_given_A m.
   Premises and side conditions: The strict-positive A-marginal premise ensures conditional probability is meaningful; normalization and nonnegativity are carried in TwoEventModel.
   Proof/definition method: Rewrite the numerator by four_cell_intersection_mass and the denominator by four_cell_first_marginal, then reduce the original conditional definition.
   Library reuse: Existing FourCellBridge marginal/intersection lemmas; Admissions.conditional_B_given_A; Stdlib.Reals division.
   Boundary: No statistical independence or empirical admissions rate is assumed.
 *)
Theorem four_cell_conditional_B_given_A :
  forall m,
    0 < p_A m ->
    @FiniteUnion.finite_prob (bool * bool)
      (four_cell_weight m) four_cell_samples
      (fun x => andb (four_cell_A x) (four_cell_B x)) /
    @FiniteUnion.finite_prob (bool * bool)
      (four_cell_weight m) four_cell_samples four_cell_A =
    conditional_B_given_A m.
Proof.
  intros m Hpositive.
  rewrite four_cell_intersection_mass.
  rewrite four_cell_first_marginal.
  unfold conditional_B_given_A, p_both.
  reflexivity.
Qed.

(**
   [four_cell_conditional_A_given_B] (theorem) — Four-cell event and conditional probability bridge.
   Mathematical meaning: The reverse Boolean conditional P(A and B)/P(B) matches the four-cell admissions expression.
   Exact checked proposition: For positive p_B m, intersection-event mass divided by B-event mass equals conditional_A_given_B m.
   Premises and side conditions: The strict-positive B marginal is explicit; normalized nonnegative cell weights are inherited from the record.
   Proof/definition method: Compose the established finite-event intersection and B-marginal bridges and unfold the report's existing conditional.
   Library reuse: four_cell_intersection_mass; four_cell_second_marginal; Admissions.conditional_A_given_B; Stdlib.Reals.
   Boundary: A finite exact correspondence; no independence or Gaussian distribution is implied.
 *)
Theorem four_cell_conditional_A_given_B :
  forall m,
    0 < p_B m ->
    @FiniteUnion.finite_prob (bool * bool)
      (four_cell_weight m) four_cell_samples
      (fun x => andb (four_cell_A x) (four_cell_B x)) /
    @FiniteUnion.finite_prob (bool * bool)
      (four_cell_weight m) four_cell_samples four_cell_B =
    conditional_A_given_B m.
Proof.
  intros m Hpositive.
  rewrite four_cell_intersection_mass.
  rewrite four_cell_second_marginal.
  unfold conditional_A_given_B, p_both.
  reflexivity.
Qed.

(**
   [four_cell_conditional_both_given_either] (theorem) — Four-cell event and conditional probability bridge.
   Mathematical meaning: The intersection mass divided by the union mass is the report's both-given-either conditional.
   Exact checked proposition: For positive p_either m, P(A and B)/P(A or B) as finite-event masses equals conditional_both_given_either m.
   Premises and side conditions: Positive union mass is required; neither equal marginals nor route independence is assumed.
   Proof/definition method: Rewrite using the established intersection mass and finite union-of-event-list lemmas, then unfold the admissions conditional.
   Library reuse: four_cell_intersection_mass; four_cell_union_mass; FiniteUnion.union_prob; Admissions.conditional_both_given_either.
   Boundary: The result concerns only the constructed normalized Boolean pair space.
 *)
Theorem four_cell_conditional_both_given_either :
  forall m,
    0 < p_either m ->
    @FiniteUnion.finite_prob (bool * bool)
      (four_cell_weight m) four_cell_samples
      (fun x => andb (four_cell_A x) (four_cell_B x)) /
    @FiniteUnion.union_prob (bool * bool)
      (four_cell_weight m) four_cell_samples [four_cell_A; four_cell_B] =
    conditional_both_given_either m.
Proof.
  intros m Hpositive.
  rewrite four_cell_intersection_mass.
  rewrite four_cell_union_mass.
  unfold conditional_both_given_either, p_both.
  reflexivity.
Qed.

(**
   [four_cell_conditional_not_A_given_B] (theorem) — Four-cell event and conditional probability bridge.
   Mathematical meaning: The Boolean B-and-not-A event mass divided by the B marginal equals the report's failure conditional.
   Exact checked proposition: For positive p_B m, P(not A and B)/P(B) as finite-event masses equals conditional_not_A_given_B m.
   Premises and side conditions: B must have positive mass to interpret the division conditionally; no independence is assumed.
   Proof/definition method: Reuse the new B-only finite mass identity and the established B-marginal bridge and unfold the original conditional definition.
   Library reuse: four_cell_second_without_first_mass; four_cell_second_marginal; Admissions.conditional_not_A_given_B; Stdlib.Bool.
   Boundary: The exact four-cell algebra does not characterize real admissions or cognitive-test correlations.
 *)
Theorem four_cell_conditional_not_A_given_B :
  forall m,
    0 < p_B m ->
    @FiniteUnion.finite_prob (bool * bool)
      (four_cell_weight m) four_cell_samples
      (fun x => andb (negb (four_cell_A x)) (four_cell_B x)) /
    @FiniteUnion.finite_prob (bool * bool)
      (four_cell_weight m) four_cell_samples four_cell_B =
    conditional_not_A_given_B m.
Proof.
  intros m Hpositive.
  rewrite four_cell_second_without_first_mass.
  rewrite four_cell_second_marginal.
  unfold conditional_not_A_given_B.
  reflexivity.
Qed.

(* Interpret established four-cell conditionals via the shared generic
   conditional event operator, rather than duplicating list algebra. *)
(**
   [four_cell_generic_conditional_B_given_A] (theorem) — Generic conditional probability of finite Boolean events.
   Mathematical meaning: The new general finite conditional-probability operator, specialized to B given A on the normalized Boolean pair space, equals the report-specific conditional_B_given_A expression.
   Exact checked proposition: forall m, 0 < p_A m -> finite_conditional_prob (four_cell_weight m) four_cell_samples four_cell_B four_cell_A = conditional_B_given_A m.
   Premises and side conditions: The first-event marginal is positive, and the FourCellModel record supplies normalized nonnegative cell weights.
   Proof/definition method: Unfold the generic conditional operator and delegate to four_cell_conditional_B_given_A, retaining its unchanged positive-denominator premise.
   Library reuse: FiniteUnion.finite_conditional_prob and four_cell_conditional_B_given_A; no separate finite sum or Boolean recursion.
   Boundary: The claim applies to the specified finite four-outcome model, not empirically observed independence.
 *)
Theorem four_cell_generic_conditional_B_given_A :
  forall m,
    0 < p_A m ->
    @FiniteUnion.finite_conditional_prob (bool * bool)
      (four_cell_weight m) four_cell_samples four_cell_B four_cell_A =
    conditional_B_given_A m.
Proof.
  intros m Hpositive.
  unfold FiniteUnion.finite_conditional_prob.
  apply four_cell_conditional_B_given_A; exact Hpositive.
Qed.

(**
   [four_cell_generic_conditional_A_given_B] (theorem) — Generic conditional probability of finite Boolean events.
   Mathematical meaning: The general finite conditional operator, specialized to A given B, agrees with the previously established four-cell admissions conditional ratio.
   Exact checked proposition: forall m, 0 < p_B m -> finite_conditional_prob (four_cell_weight m) four_cell_samples four_cell_A four_cell_B = conditional_A_given_B m.
   Premises and side conditions: The B-marginal must be strictly positive; four-cell normalization and nonnegativity remain in the record constraints.
   Proof/definition method: Unfold only the new generic operator and apply the existing four_cell_conditional_A_given_B bridge theorem.
   Library reuse: FiniteUnion.finite_conditional_prob and four_cell_conditional_A_given_B; existing checked Boolean-event and marginal results.
   Boundary: This is a finite semantic equivalence, not a derivation of Gaussian or observed admission rates.
 *)
Theorem four_cell_generic_conditional_A_given_B :
  forall m,
    0 < p_B m ->
    @FiniteUnion.finite_conditional_prob (bool * bool)
      (four_cell_weight m) four_cell_samples four_cell_A four_cell_B =
    conditional_A_given_B m.
Proof.
  intros m Hpositive.
  unfold FiniteUnion.finite_conditional_prob.
  apply four_cell_conditional_A_given_B; exact Hpositive.
Qed.

(* The final two report conditionals now reuse the generic quotient
   without duplicating finite-event summation or probability axioms. *)
(**
   [four_cell_generic_conditional_both_given_either] (theorem) — Generic-to-four-cell conditional interpretation.
   Mathematical meaning: The generic conditional mass of the intersection of two Boolean admissions events given their union is exactly the existing report-level both-given-either conditional probability.
   Exact checked proposition: For all m, 0 < p_either m implies finite_conditional_prob (four_cell_weight m) four_cell_samples (A and B) (A or B) = conditional_both_given_either m.
   Premises and side conditions: The union mass must be strictly positive. The FourCell model supplies four nonnegative normalized cell weights; no event independence or equal marginals are assumed.
   Proof/definition method: Unfold only the common conditional quotient, use finite_prob_event_ext_on_samples and Boolean pair case elimination for the absorbed intersection, rewrite the denominator by two_event_union_probability, and apply the earlier four-cell ratio theorem.
   Library reuse: FiniteUnion.finite_prob_event_ext_on_samples, FiniteUnion.two_event_union_probability, four_cell_conditional_both_given_either, Stdlib.Bool.andb/orb.
   Boundary: This is an exact four-outcome finite probability theorem, not a claimed real-world admission correlation or Gaussian result.
 *)
Theorem four_cell_generic_conditional_both_given_either :
  forall m,
    0 < p_either m ->
    @FiniteUnion.finite_conditional_prob (bool * bool)
      (four_cell_weight m) four_cell_samples
      (fun x => andb (four_cell_A x) (four_cell_B x))
      (fun x => orb (four_cell_A x) (four_cell_B x)) =
    conditional_both_given_either m.
Proof.
  intros m Hpositive.
  unfold FiniteUnion.finite_conditional_prob.
  rewrite (@FiniteUnion.finite_prob_event_ext_on_samples
    (bool * bool) (four_cell_weight m) four_cell_samples
    (fun x => andb (orb (four_cell_A x) (four_cell_B x))
      (andb (four_cell_A x) (four_cell_B x)))
    (fun x => andb (four_cell_A x) (four_cell_B x))).
  2: { intros [a b] _; destruct a, b; reflexivity. }
  rewrite <- (@FiniteUnion.two_event_union_probability
    (bool * bool) (four_cell_weight m) four_cell_samples
    four_cell_A four_cell_B).
  apply four_cell_conditional_both_given_either; exact Hpositive.
Qed.

(**
   [four_cell_generic_conditional_not_A_given_B] (theorem) — Generic-to-four-cell conditional interpretation.
   Mathematical meaning: Conditional mass of the complement of admission event A given B, expressed with the shared finite conditional operator, coincides with the original four-cell B-only conditional expression.
   Exact checked proposition: Every m with positive p_B m satisfies finite_conditional_prob (four_cell_weight m) four_cell_samples (not A) B = conditional_not_A_given_B m.
   Premises and side conditions: Strict positivity of B's marginal makes the ratio a meaningful conditional. The FourCellModel record retains normalized nonnegative cell weights, without assuming independent admissions routes.
   Proof/definition method: Expand the shared quotient, use sample-support probability extensionality and the standard Boolean conjunction commutativity lemma, then apply the existing four-cell B-only conditional bridge.
   Library reuse: Stdlib.Bool.andb_comm/negb, FiniteUnion.finite_prob_event_ext_on_samples, four_cell_conditional_not_A_given_B.
   Boundary: The equality covers the explicitly enumerated four Boolean outcomes, not an empirical population or general conditional distribution.
 *)
Theorem four_cell_generic_conditional_not_A_given_B :
  forall m,
    0 < p_B m ->
    @FiniteUnion.finite_conditional_prob (bool * bool)
      (four_cell_weight m) four_cell_samples
      (fun x => negb (four_cell_A x)) four_cell_B =
    conditional_not_A_given_B m.
Proof.
  intros m Hpositive.
  unfold FiniteUnion.finite_conditional_prob.
  rewrite (@FiniteUnion.finite_prob_event_ext_on_samples
    (bool * bool) (four_cell_weight m) four_cell_samples
    (fun x => andb (four_cell_B x) (negb (four_cell_A x)))
    (fun x => andb (negb (four_cell_A x)) (four_cell_B x))).
  2: { intros x _; apply andb_comm. }
  apply four_cell_conditional_not_A_given_B; exact Hpositive.
Qed.


(**
   [four_cell_generic_independence_iff_marginal_product] (theorem) — Generic conditional independence on the four-cell admissions model.
   Mathematical meaning: The normalized four-outcome Boolean product interpretation satisfies the generic finite conditional-independence predicate under certain-event conditioning exactly when its existing joint admission mass equals the product of the two marginal admission masses.
   Exact checked proposition: For any Admissions.TwoEventModel m, FiniteUnion.finite_conditional_independent (four_cell_weight m) four_cell_samples four_cell_A four_cell_B (fun _ => true) iff p_both m = p_A m * p_B m.
   Premises and side conditions: The model's four nonnegative cell weights summing to one are supplied by TwoEventModel and verified by four_cell_total_mass; no independence is assumed before the iff. All four listed Boolean pairs are retained.
   Proof/definition method: Translate the verified four-cell mass normalization definitionally to the common FiniteSum fold, apply the generic true-conditioning independence/product theorem, then rewrite the already verified joint and marginal masses.
   Library reuse: FiniteUnion.finite_conditional_independent_given_true_iff_marginal_product, four_cell_total_mass, four_cell_intersection_mass, four_cell_first_marginal and four_cell_second_marginal.
   Boundary: The bridge proves a structural equivalence within an exact four-cell report model, not an empirical claim of independent admissions or Gaussian cognition.
 *)
Theorem four_cell_generic_independence_iff_marginal_product :
  forall m,
    (@FiniteUnion.finite_conditional_independent (bool * bool)
      (four_cell_weight m) four_cell_samples
      four_cell_A four_cell_B (fun _ => true) <->
     p_both m = p_A m * p_B m).
Proof.
  intro m.
  assert (Hunit :
      @FiniteUnion.finite_sum (bool * bool)
        (four_cell_weight m) four_cell_samples = 1).
  { change (@FiniteMoments.total_mass (bool * bool)
      four_cell_samples (four_cell_weight m) = 1).
    apply four_cell_total_mass. }
  rewrite (@FiniteUnion.finite_conditional_independent_given_true_iff_marginal_product
    (bool * bool) (four_cell_weight m) four_cell_samples
    four_cell_A four_cell_B Hunit).
  rewrite (four_cell_intersection_mass m).
  rewrite (four_cell_first_marginal m).
  rewrite (four_cell_second_marginal m).
  reflexivity.
Qed.

(**
   [four_cell_generic_independence_iff_cross_product_cells] (theorem) — Exact four-cell conditional-independence criterion.
   Mathematical meaning: The generic finite conditional-independence predicate with true conditioning is equivalent to the determinant-like four-cell product equality joint * neither = only_A * only_B.
   Exact checked proposition: For every TwoEventModel m, finite_conditional_independent on the four_cell_samples and four_cell_weight m for events A and B given true iff joint m * neither m = only_A m * only_B m.
   Premises and side conditions: Cell nonnegativity and unit sum are inherited from TwoEventModel; independence is not assumed. A zero marginal is permitted because the conditioning event itself has unit mass.
   Proof/definition method: Rewrite with the new generic-to-marginal-product bridge, then apply the previously checked Admissions.binary_independence_criterion; no four-cell product algebra or list traversal is rederived.
   Library reuse: four_cell_generic_independence_iff_marginal_product and Admissions.binary_independence_criterion.
   Boundary: This criterion is exact for the specified four Boolean cells; it does not establish any observed admissions process or continuous random-variable conditional independence.
 *)
Theorem four_cell_generic_independence_iff_cross_product_cells :
  forall m,
    (@FiniteUnion.finite_conditional_independent (bool * bool)
      (four_cell_weight m) four_cell_samples
      four_cell_A four_cell_B (fun _ => true) <->
     joint m * neither m = only_A m * only_B m).
Proof.
  intro m.
  rewrite (four_cell_generic_independence_iff_marginal_product m).
  apply binary_independence_criterion.
Qed.


(**
   [four_cell_generic_independence_iff_zero_indicator_covariance] (theorem) — Verified four-cell independence as a zero-covariance predicate.
   Mathematical meaning: The generic finite conditional-independence statement for the admissions Boolean pair A,B given true is logically equivalent to zero covariance of their indicator score functions, computed using the existing four-cell weights.
   Exact checked proposition: For every Admissions.TwoEventModel m, FiniteUnion.finite_conditional_independent (four_cell_weight m) four_cell_samples four_cell_A four_cell_B (fun _ => true) iff FiniteMoments.covariance (indicator ∘ four_cell_A) (indicator ∘ four_cell_B) = 0 in the existing four-cell finite moment model.
   Premises and side conditions: The four-cell record supplies nonnegative cells and a unit total weight, already established by four_cell_total_mass. Independence itself is not assumed; four sample outcomes and all their weights are left intact.
   Proof/definition method: Convert the existing four-cell normalization identity definitionally to the common FiniteUnion finite sum, then instantiate the generic checked normalized independence/indicator covariance equivalence. No re-enumeration of Boolean pairs or algebraic recomputation of covariance is performed.
   Library reuse: four_cell_total_mass, FiniteBridge.finite_normalized_conditional_independence_iff_zero_indicator_covariance, FiniteUnion.finite_sum, FiniteMoments.total_mass and the shared FiniteSum implementation.
   Boundary: This identifies equivalent propositions within the finite four-cell model, not an empirical zero-correlation finding, a causal claim or a Gaussian independence assertion.
 *)
Theorem four_cell_generic_independence_iff_zero_indicator_covariance :
  forall m,
    (@FiniteUnion.finite_conditional_independent (bool * bool)
       (four_cell_weight m) four_cell_samples
       four_cell_A four_cell_B (fun _ => true) <->
     @FiniteMoments.covariance (bool * bool) four_cell_samples
       (four_cell_weight m)
       (fun x => FiniteUnion.indicator (four_cell_A x))
       (fun x => FiniteUnion.indicator (four_cell_B x)) = 0).
Proof.
  intro m.
  assert (Hunit :
    @FiniteUnion.finite_sum (bool * bool)
      (four_cell_weight m) four_cell_samples = 1).
  { change (@FiniteMoments.total_mass (bool * bool)
      four_cell_samples (four_cell_weight m) = 1).
    apply four_cell_total_mass. }
  apply (finite_normalized_conditional_independence_iff_zero_indicator_covariance
    (bool * bool) four_cell_samples (four_cell_weight m)
    four_cell_A four_cell_B Hunit).
Qed.
