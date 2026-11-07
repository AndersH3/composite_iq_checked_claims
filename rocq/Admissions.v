(* Event algebra from analyses/towers-multiple-test-admissions/analysis.md.
   A finite, four-cell probability space makes the logical assumptions explicit:
   A and B partition into both, A-only, B-only, and neither.  No normal
   distribution, independence or unproved probability axioms are imported. *)
From Stdlib Require Import Reals Lra Psatz Arith.PeanoNat.
Open Scope R_scope.

(* Reuse Stdlib.Reals quotient, inverse, and product sign lemmas. *)

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

Definition p_A (m : TwoEventModel) : R := joint m + only_A m.
Definition p_B (m : TwoEventModel) : R := joint m + only_B m.
Definition p_both (m : TwoEventModel) : R := joint m.
Definition p_either (m : TwoEventModel) : R :=
  joint m + only_A m + only_B m.
Definition p_exactly_one (m : TwoEventModel) : R :=
  only_A m + only_B m.

Definition conditional_B_given_A (m : TwoEventModel) : R :=
  joint m / p_A m.
Definition conditional_A_given_B (m : TwoEventModel) : R :=
  joint m / p_B m.
Definition conditional_both_given_either (m : TwoEventModel) : R :=
  joint m / p_either m.
Definition conditional_not_A_given_B (m : TwoEventModel) : R :=
  only_B m / p_B m.

Theorem first_marginal_nonnegative :
  forall m, 0 <= p_A m.
Proof.
  intro m; unfold p_A.
  apply Rplus_le_le_0_compat.
  - apply joint_nonnegative.
  - apply only_A_nonnegative.
Qed.

Theorem second_marginal_nonnegative :
  forall m, 0 <= p_B m.
Proof.
  intro m; unfold p_B.
  apply Rplus_le_le_0_compat.
  - apply joint_nonnegative.
  - apply only_B_nonnegative.
Qed.

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

Theorem union_at_most_one :
  forall m, p_either m <= 1.
Proof.
  intro m; unfold p_either.
  pose proof (cells_sum_to_one m).
  pose proof (neither_nonnegative m).
  lra.
Qed.

Theorem both_at_most_first :
  forall m, p_both m <= p_A m.
Proof.
  intro m; unfold p_both, p_A.
  pose proof (only_A_nonnegative m); lra.
Qed.

Theorem both_at_most_second :
  forall m, p_both m <= p_B m.
Proof.
  intro m; unfold p_both, p_B.
  pose proof (only_B_nonnegative m); lra.
Qed.

Theorem union_at_least_first :
  forall m, p_A m <= p_either m.
Proof.
  intro m; unfold p_A, p_either.
  pose proof (only_B_nonnegative m); lra.
Qed.

Theorem union_at_least_second :
  forall m, p_B m <= p_either m.
Proof.
  intro m; unfold p_B, p_either.
  pose proof (only_A_nonnegative m); lra.
Qed.

(* Inclusion-exclusion is exact for arbitrary dependence. *)
Theorem inclusion_exclusion :
  forall m, p_either m = p_A m + p_B m - p_both m.
Proof.
  intro m; unfold p_either, p_A, p_B, p_both; ring.
Qed.

Theorem union_bound :
  forall m, p_either m <= p_A m + p_B m.
Proof.
  intro m.
  rewrite inclusion_exclusion.
  unfold p_both.
  pose proof (joint_nonnegative m); lra.
Qed.

Theorem frechet_lower_bound :
  forall m, p_A m + p_B m - 1 <= p_both m.
Proof.
  intro m.
  unfold p_A, p_B, p_both.
  pose proof (cells_sum_to_one m).
  pose proof (neither_nonnegative m).
  lra.
Qed.

Theorem overlap_nonnegative :
  forall m, 0 <= p_both m.
Proof.
  intro m; unfold p_both.
  apply joint_nonnegative.
Qed.

Theorem union_complement :
  forall m, p_either m + neither m = 1.
Proof.
  intro m; unfold p_either.
  exact (cells_sum_to_one m).
Qed.

Theorem exactly_one_formula :
  forall m, p_exactly_one m = p_A m + p_B m - 2 * p_both m.
Proof.
  intro m.
  unfold p_exactly_one, p_A, p_B, p_both; ring.
Qed.

Theorem exactly_one_vs_union :
  forall m, p_either m = p_exactly_one m + p_both m.
Proof.
  intro m; unfold p_either, p_exactly_one, p_both; ring.
Qed.

Theorem equal_marginal_union :
  forall m p, p_A m = p -> p_B m = p ->
    p_either m = 2 * p - p_both m.
Proof.
  intros m p Ha Hb.
  rewrite inclusion_exclusion, Ha, Hb.
  ring.
Qed.

Theorem equal_marginal_exactly_one :
  forall m p, p_A m = p -> p_B m = p ->
    p_exactly_one m = 2 * (p - p_both m).
Proof.
  intros m p Ha Hb.
  rewrite exactly_one_formula, Ha, Hb.
  ring.
Qed.

Theorem conditional_B_numerator :
  forall m, 0 < p_A m ->
    p_A m * conditional_B_given_A m = p_both m.
Proof.
  intros m Ha.
  unfold conditional_B_given_A, p_both.
  field; lra.
Qed.

Theorem conditional_A_numerator :
  forall m, 0 < p_B m ->
    p_B m * conditional_A_given_B m = p_both m.
Proof.
  intros m Hb.
  unfold conditional_A_given_B, p_both.
  field; lra.
Qed.

Theorem conditional_either_numerator :
  forall m, 0 < p_either m ->
    p_either m * conditional_both_given_either m = p_both m.
Proof.
  intros m Hu.
  unfold conditional_both_given_either, p_both.
  field; lra.
Qed.

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

Theorem conditional_failure_nonnegative :
  forall m, 0 < p_B m ->
    0 <= conditional_not_A_given_B m.
Proof.
  intros m Hb; unfold conditional_not_A_given_B, Rdiv.
  apply Rmult_le_pos.
  - apply only_B_nonnegative.
  - apply Rlt_le, Rinv_0_lt_compat; exact Hb.
Qed.

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
Definition independent_union (p : R) (n : nat) : R :=
  Nat.iter n (fun u => u + p - u * p) 0.

Theorem independent_union_formula :
  forall p n, independent_union p n = 1 - (1 - p) ^ n.
Proof.
  intros p n; induction n as [| k IH].
  - unfold independent_union; simpl; ring.
  - unfold independent_union in *.
    rewrite Nat.iter_succ.
    rewrite IH; simpl; ring.
Qed.

Theorem independent_union_one :
  forall p, independent_union p 1%nat = p.
Proof.
  intro p; unfold independent_union; simpl; ring.
Qed.

Theorem independent_union_two :
  forall p, independent_union p 2%nat = 2 * p - p * p.
Proof.
  intro p; unfold independent_union; simpl; ring.
Qed.

(* Two explicit probability models with equal marginals but different overlap.
   Thus marginal pass rates alone cannot fix the OR eligibility fraction. *)
Definition identical_half_events : TwoEventModel.
Proof.
  refine {| joint := 1/2; only_A := 0; only_B := 0;
            neither := 1/2 |}; lra.
Defined.

Definition independent_half_events : TwoEventModel.
Proof.
  refine {| joint := 1/4; only_A := 1/4; only_B := 1/4;
            neither := 1/4 |}; lra.
Defined.

Theorem same_marginals_different_joint :
  p_A identical_half_events = p_A independent_half_events /\
  p_B identical_half_events = p_B independent_half_events /\
  p_both identical_half_events <> p_both independent_half_events.
Proof.
  unfold p_A, p_B, p_both,
    identical_half_events, independent_half_events.
  simpl; repeat split; lra.
Qed.

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
Example grid_node_count :
  (397 * 397)%nat = 157609%nat.
Proof. reflexivity. Qed.

Theorem grid_scale_factors_cancel :
  forall scale numerator denominator,
    0 < scale -> 0 < denominator ->
    (scale * numerator) / (scale * denominator) =
      numerator / denominator.
Proof.
  intros scale numerator denominator Hs Hd; field; nra.
Qed.

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

Theorem exactly_one_nonnegative :
  forall m, 0 <= p_exactly_one m.
Proof.
  intros m.
  unfold p_exactly_one.
  pose proof (only_A_nonnegative m).
  pose proof (only_B_nonnegative m).
  lra.
Qed.

Theorem exactly_one_at_most_either :
  forall m, p_exactly_one m <= p_either m.
Proof.
  intros m.
  unfold p_exactly_one, p_either.
  pose proof (joint_nonnegative m).
  lra.
Qed.

Theorem intersection_at_most_minimum_marginal :
  forall m p, p_A m <= p -> p_B m <= p -> p_both m <= p.
Proof.
  intros m p Ha Hb.
  pose proof (both_at_most_first m).
  lra.
Qed.

Theorem union_equal_marginal_lower_bound :
  forall m p, p_A m = p -> p_B m = p -> p <= p_either m.
Proof.
  intros m p Ha Hb.
  pose proof (union_at_least_first m).
  lra.
Qed.

Theorem union_equal_marginal_upper_bound :
  forall m p, p_A m = p -> p_B m = p -> p_either m <= 2 * p.
Proof.
  intros m p Ha Hb.
  pose proof (union_bound m).
  lra.
Qed.

Theorem disjoint_events_union_is_sum :
  forall m, p_both m = 0 ->
    p_either m = p_A m + p_B m.
Proof.
  intros m Hj.
  rewrite inclusion_exclusion, Hj; ring.
Qed.

Theorem independent_events_union_formula :
  forall m, p_both m = p_A m * p_B m ->
    p_either m = p_A m + p_B m - p_A m * p_B m.
Proof.
  intros m Hj.
  rewrite inclusion_exclusion, Hj; reflexivity.
Qed.

Theorem independent_equal_marginal_union :
  forall m p,
    p_A m = p -> p_B m = p ->
    p_both m = p * p ->
    p_either m = 2 * p - p * p.
Proof.
  intros m p Ha Hb Hj.
  rewrite inclusion_exclusion, Ha, Hb, Hj; ring.
Qed.

Theorem all_first_passers_also_second_union :
  forall m, p_both m = p_A m -> p_either m = p_B m.
Proof.
  intros m Hj.
  pose proof (inclusion_exclusion m) as H.
  rewrite Hj in H; lra.
Qed.

Theorem excess_marginal_mass_forces_overlap :
  forall m, 1 < p_A m + p_B m -> 0 < p_both m.
Proof.
  intros m Hsum.
  pose proof (frechet_lower_bound m).
  lra.
Qed.

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

Theorem independent_either_as_complement_product :
  forall m,
    p_both m = p_A m * p_B m ->
    p_either m = 1 - (1 - p_A m) * (1 - p_B m).
Proof.
  intros m Hjoint.
  rewrite (independent_events_union_formula m Hjoint).
  ring.
Qed.

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

Theorem complete_coverage_iff_no_failures :
  forall m,
    p_either m = 1 <-> neither m = 0.
Proof.
  intro m; split; intro H.
  - pose proof (union_complement m); lra.
  - pose proof (union_complement m); lra.
Qed.

Theorem equal_marginals_overlap_lower_bound :
  forall m p,
    p_A m = p -> p_B m = p ->
    2 * p - 1 <= p_both m.
Proof.
  intros m p Ha Hb.
  pose proof (frechet_lower_bound m).
  lra.
Qed.

Theorem zero_first_marginal_forces_zero_overlap :
  forall m,
    p_A m = 0 -> p_both m = 0.
Proof.
  intros m Ha.
  pose proof (overlap_nonnegative m).
  pose proof (both_at_most_first m).
  lra.
Qed.

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
