(* A checked interpretation of the Towers four-cell admissions model as a
   standard finite Boolean product space. No new probability axioms,
   recursive event structure, or bespoke finite-sum implementation. *)
From Stdlib Require Import Reals Lra Psatz List Bool.
Require Import Admissions FiniteSum FiniteUnion FiniteMoments FiniteBridge.
Import ListNotations.
Open Scope R_scope.

(* The four outcomes are the complete Cartesian product of two Booleans. *)
Definition four_cell_samples : list (bool * bool) :=
  list_prod [true; false] [true; false].

Definition four_cell_weight (m : TwoEventModel)
    (outcome : bool * bool) : R :=
  match outcome with
  | (true, true) => joint m
  | (true, false) => only_A m
  | (false, true) => only_B m
  | (false, false) => neither m
  end.

Definition four_cell_A (outcome : bool * bool) : bool := fst outcome.
Definition four_cell_B (outcome : bool * bool) : bool := snd outcome.
Definition four_cell_exactly_one (outcome : bool * bool) : bool :=
  xorb (four_cell_A outcome) (four_cell_B outcome).

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
