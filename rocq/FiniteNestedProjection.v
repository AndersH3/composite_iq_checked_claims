(** Module: FiniteNestedProjection.v
 Purpose: Kernel-check sequential/nested finite conditioning for two Boolean
 observations p then q, with complete four-cell moment conservation,
 pointwise conditional-expectation tower, projection idempotence,
 orthogonality to every four-cell measurable score, finite least-squares
 optimality and an exact two-stage law of total variance.
 Mathematical representation: Arbitrary real weights and scores on an
 explicit finite list of occurrences. The existing FiniteSum.finite_sum
 list fold and Stdlib.List.filter drive all aggregation. The existing
 FiniteTwoCellProjection.v supplies weighted moments, conditional means,
 two-cell projection orthogonality, risk and variance decomposition.
 All unnormalized moments count repeated sample occurrences.
 Explicit hypotheses: Every conditional cell mean under projection has nonzero
 mass; optimization/monotonicity requires positive observed cell mass.
 No nonnegative-weight hypothesis is concealed in an algebraic theorem;
 interpretations as probabilities require normalized nonnegative weights.
 Library use: Stdlib.List and Stdlib.Reals, the shared FiniteSum,
 and the maintained FiniteTwoCellProjection theorem API.
 Refactoring: The only general sum helper is a derived if-partition
 property proved with FiniteSum.finite_sum_filter and finite_sum_add.
 No new recursive fold or custom indicator implementation.
 Limitations: Finite Boolean partitions are not a general sigma-algebra,
 L1 conditional expectation, or Gaussian conditional distribution.
 None of the report's empirical IQ premises follows from these results.
 Reproduction: rocq compile FiniteNestedProjection.v after all listed
 dependencies, in the pinned Rocq 9.2 GitHub Actions build.
 AI disclosure: OpenAI's assistant authored the source and explanatory
 comments; only independent kernel checking validates theorem statements.
 *)
From Stdlib Require Import Reals Lra Psatz List Bool.
Require Import FiniteSum FiniteTwoCellProjection.
Import ListNotations.
Open Scope R_scope.

(**
 [refined_projection] (definition) — The conditional-score predictor obtained by first observing p and then q within the observed p-cell.
 Mathematical meaning: The conditional-score predictor obtained by first observing p and then q within the observed p-cell.
 Exact declaration: Definition refined_projection {A : Type} (xs : list A) (weight score : A -> R) (p q : A -> bool) (x : A) : R := if p x then finite_two_cell_prediction (filter p xs) weight score q x else finite_two_cell_prediction (filter (fun y => negb (p y)) xs) weight score q x.
 Premises and side conditions: All finite enumerated score and Boolean-event functions, conditional denominators and positivity conditions are explicit in the theorem. Signed weights are permitted for algebraic equalities; probability meanings need normalized nonnegative mass.
 Proof/definition method: Define the transparent two-stage observable score or risk as a composition of already checked two-cell operators.
 Library reuse: Stdlib.List.filter/filter_In, Stdlib.Reals/Field/Lra/Psatz/Ring, FiniteSum.finite_sum_* and previously checked FiniteTwoCellProjection results, with no duplicated recursive fold.
 Boundary: Deterministic finite joint Boolean observation and squared-error algebra; no general measure-theoretic L1 conditioning, Gaussian conditional laws or empirical IQ validation.
 *)
Definition refined_projection {A : Type}
 (xs : list A) (weight score : A -> R) (p q : A -> bool) (x : A) : R :=
 if p x then finite_two_cell_prediction (filter p xs) weight score q x
 else finite_two_cell_prediction (filter (fun y => negb (p y)) xs) weight score q x.

(**
 [refined_test_score] (definition) — An arbitrary real score measurable with respect to the four joint Boolean cells p and q.
 Mathematical meaning: An arbitrary real score measurable with respect to the four joint Boolean cells p and q.
 Exact declaration: Definition refined_test_score {A : Type} (p q : A -> bool) (a b c d : R) (x : A) : R := if p x then (if q x then a else b) else (if q x then c else d).
 Premises and side conditions: All finite enumerated score and Boolean-event functions, conditional denominators and positivity conditions are explicit in the theorem. Signed weights are permitted for algebraic equalities; probability meanings need normalized nonnegative mass.
 Proof/definition method: Define the transparent two-stage observable score or risk as a composition of already checked two-cell operators.
 Library reuse: Stdlib.List.filter/filter_In, Stdlib.Reals/Field/Lra/Psatz/Ring, FiniteSum.finite_sum_* and previously checked FiniteTwoCellProjection results, with no duplicated recursive fold.
 Boundary: Deterministic finite joint Boolean observation and squared-error algebra; no general measure-theoretic L1 conditioning, Gaussian conditional laws or empirical IQ validation.
 *)
Definition refined_test_score {A : Type}
 (p q : A -> bool) (a b c d : R) (x : A) : R :=
 if p x then (if q x then a else b) else (if q x then c else d).

(**
 [refined_candidate_risk] (definition) — The finite sum of the two internal two-cell squared-loss risks for four arbitrary predictions.
 Mathematical meaning: The finite sum of the two internal two-cell squared-loss risks for four arbitrary predictions.
 Exact declaration: Definition refined_candidate_risk {A : Type} (xs : list A) (weight score : A -> R) (p q : A -> bool) (a b c d : R) : R := finite_two_cell_risk (filter p xs) weight score q a b + finite_two_cell_risk (filter (fun x => negb (p x)) xs) weight score q c d.
 Premises and side conditions: All finite enumerated score and Boolean-event functions, conditional denominators and positivity conditions are explicit in the theorem. Signed weights are permitted for algebraic equalities; probability meanings need normalized nonnegative mass.
 Proof/definition method: Define the transparent two-stage observable score or risk as a composition of already checked two-cell operators.
 Library reuse: Stdlib.List.filter/filter_In, Stdlib.Reals/Field/Lra/Psatz/Ring, FiniteSum.finite_sum_* and previously checked FiniteTwoCellProjection results, with no duplicated recursive fold.
 Boundary: Deterministic finite joint Boolean observation and squared-error algebra; no general measure-theoretic L1 conditioning, Gaussian conditional laws or empirical IQ validation.
 *)
Definition refined_candidate_risk {A : Type}
 (xs : list A) (weight score : A -> R) (p q : A -> bool)
 (a b c d : R) : R :=
 finite_two_cell_risk (filter p xs) weight score q a b +
 finite_two_cell_risk (filter (fun x => negb (p x)) xs) weight score q c d.

(**
 [refined_optimal_risk] (definition) — The actual four-cell mean-square prediction risk at the four conditional cell means.
 Mathematical meaning: The actual four-cell mean-square prediction risk at the four conditional cell means.
 Exact declaration: Definition refined_optimal_risk {A : Type} (xs : list A) (weight score : A -> R) (p q : A -> bool) : R := refined_candidate_risk xs weight score p q (finite_true_mean (filter p xs) weight score q) (finite_false_mean (filter p xs) weight score q) (finite_true_mean (filter (fun x => negb (p x)) xs) weight score q) (finite_false_mean (filter (fun x => negb (p x)) xs) weight score q).
 Premises and side conditions: All finite enumerated score and Boolean-event functions, conditional denominators and positivity conditions are explicit in the theorem. Signed weights are permitted for algebraic equalities; probability meanings need normalized nonnegative mass.
 Proof/definition method: Define the transparent two-stage observable score or risk as a composition of already checked two-cell operators.
 Library reuse: Stdlib.List.filter/filter_In, Stdlib.Reals/Field/Lra/Psatz/Ring, FiniteSum.finite_sum_* and previously checked FiniteTwoCellProjection results, with no duplicated recursive fold.
 Boundary: Deterministic finite joint Boolean observation and squared-error algebra; no general measure-theoretic L1 conditioning, Gaussian conditional laws or empirical IQ validation.
 *)
Definition refined_optimal_risk {A : Type}
 (xs : list A) (weight score : A -> R) (p q : A -> bool) : R :=
 refined_candidate_risk xs weight score p q
    (finite_true_mean (filter p xs) weight score q)
    (finite_false_mean (filter p xs) weight score q)
    (finite_true_mean (filter (fun x => negb (p x)) xs) weight score q)
    (finite_false_mean (filter (fun x => negb (p x)) xs) weight score q).

(**
 [refined_between_loss] (definition) — The four nonnegative weighted squared changes of the refined cell means from their respective coarser p-cell means.
 Mathematical meaning: The four nonnegative weighted squared changes of the refined cell means from their respective coarser p-cell means.
 Exact declaration: Definition refined_between_loss {A : Type} (xs : list A) (weight score : A -> R) (p q : A -> bool) : R := finite_true_mass (filter p xs) weight q * (finite_true_mean (filter p xs) weight score q - finite_true_mean xs weight score p) * (finite_true_mean (filter p xs) weight score q - finite_true_mean xs weight score p) + finite_false_mass (filter p xs) weight q * (finite_false_mean (filter p xs) weight score q - finite_true_mean xs weight score p) * (finite_false_mean (filter p xs) weight score q - finite_true_mean xs weight score p) + finite_true_mass (filter (fun x => negb (p x)) xs) weight q * (finite_true_mean (filter (fun x => negb (p x)) xs) weight score q - finite_false_mean xs weight score p) * (finite_true_mean (filter (fun x => negb (p x)) xs) weight score q - finite_false_mean xs weight score p) + finite_false_mass (filter (fun x => negb (p x)) xs) weight q * (finite_false_mean (filter (fun x => negb (p x)) xs) weight score q - finite_false_mean xs weight score p) * (finite_false_mean (filter (fun x => negb (p x)) xs) weight score q - finite_false_mean xs weight score p).
 Premises and side conditions: All finite enumerated score and Boolean-event functions, conditional denominators and positivity conditions are explicit in the theorem. Signed weights are permitted for algebraic equalities; probability meanings need normalized nonnegative mass.
 Proof/definition method: Define the transparent two-stage observable score or risk as a composition of already checked two-cell operators.
 Library reuse: Stdlib.List.filter/filter_In, Stdlib.Reals/Field/Lra/Psatz/Ring, FiniteSum.finite_sum_* and previously checked FiniteTwoCellProjection results, with no duplicated recursive fold.
 Boundary: Deterministic finite joint Boolean observation and squared-error algebra; no general measure-theoretic L1 conditioning, Gaussian conditional laws or empirical IQ validation.
 *)
Definition refined_between_loss {A : Type}
 (xs : list A) (weight score : A -> R) (p q : A -> bool) : R :=
 finite_true_mass (filter p xs) weight q *
    (finite_true_mean (filter p xs) weight score q -
     finite_true_mean xs weight score p) *
    (finite_true_mean (filter p xs) weight score q -
     finite_true_mean xs weight score p) +
 finite_false_mass (filter p xs) weight q *
    (finite_false_mean (filter p xs) weight score q -
     finite_true_mean xs weight score p) *
    (finite_false_mean (filter p xs) weight score q -
     finite_true_mean xs weight score p) +
 finite_true_mass (filter (fun x => negb (p x)) xs) weight q *
    (finite_true_mean (filter (fun x => negb (p x)) xs) weight score q -
     finite_false_mean xs weight score p) *
    (finite_true_mean (filter (fun x => negb (p x)) xs) weight score q -
     finite_false_mean xs weight score p) +
 finite_false_mass (filter (fun x => negb (p x)) xs) weight q *
    (finite_false_mean (filter (fun x => negb (p x)) xs) weight score q -
     finite_false_mean xs weight score p) *
    (finite_false_mean (filter (fun x => negb (p x)) xs) weight score q -
     finite_false_mean xs weight score p).

(**
 [finite_sum_if_partition] (theorem) — A reusable generic if-then-else sum decomposition across a Boolean partition, with multiplicities and signed terms preserved.
 Mathematical meaning: A reusable generic if-then-else sum decomposition across a Boolean partition, with multiplicities and signed terms preserved.
 Exact checked proposition: forall (A : Type) (xs : list A) (p : A -> bool) (f g : A -> R), finite_sum (fun x => if p x then f x else g x) xs = finite_sum f (filter p xs) + finite_sum g (filter (fun x => negb (p x)) xs).
 Premises and side conditions: All finite enumerated score and Boolean-event functions, conditional denominators and positivity conditions are explicit in the theorem. Signed weights are permitted for algebraic equalities; probability meanings need normalized nonnegative mass.
 Proof/definition method: Derive the new reusable conditionally selected integrand law from FiniteSum.finite_sum_filter, finite_sum_add and extensionality.
 Library reuse: Stdlib.List.filter/filter_In, Stdlib.Reals/Field/Lra/Psatz/Ring, FiniteSum.finite_sum_* and previously checked FiniteTwoCellProjection results, with no duplicated recursive fold.
 Boundary: Deterministic finite joint Boolean observation and squared-error algebra; no general measure-theoretic L1 conditioning, Gaussian conditional laws or empirical IQ validation.
 *)
Theorem finite_sum_if_partition :
 forall (A : Type) (xs : list A) (p : A -> bool) (f g : A -> R),
 finite_sum (fun x => if p x then f x else g x) xs =
 finite_sum f (filter p xs) +
 finite_sum g (filter (fun x => negb (p x)) xs).
Proof.
 intros A xs p f g.
 rewrite !finite_sum_filter.
 rewrite <- finite_sum_add.
 apply finite_sum_ext; intro x.
 destruct (p x); simpl; ring.
Qed.

(**
 [weighted_score_if_partition] (theorem) — The weighted moment of a piecewise score is the sum of its moments on the two selected occurrence lists.
 Mathematical meaning: The weighted moment of a piecewise score is the sum of its moments on the two selected occurrence lists.
 Exact checked proposition: forall (A : Type) (xs : list A) (weight f g : A -> R) (p : A -> bool), finite_weighted_score xs weight (fun x => if p x then f x else g x) = finite_weighted_score (filter p xs) weight f + finite_weighted_score (filter (fun x => negb (p x)) xs) weight g.
 Premises and side conditions: All finite enumerated score and Boolean-event functions, conditional denominators and positivity conditions are explicit in the theorem. Signed weights are permitted for algebraic equalities; probability meanings need normalized nonnegative mass.
 Proof/definition method: Reuse the generic if-partition finite sum theorem and the existing weighted-score definition.
 Library reuse: Stdlib.List.filter/filter_In, Stdlib.Reals/Field/Lra/Psatz/Ring, FiniteSum.finite_sum_* and previously checked FiniteTwoCellProjection results, with no duplicated recursive fold.
 Boundary: Deterministic finite joint Boolean observation and squared-error algebra; no general measure-theoretic L1 conditioning, Gaussian conditional laws or empirical IQ validation.
 *)
Theorem weighted_score_if_partition :
 forall (A : Type) (xs : list A) (weight f g : A -> R) (p : A -> bool),
 finite_weighted_score xs weight (fun x => if p x then f x else g x) =
 finite_weighted_score (filter p xs) weight f +
 finite_weighted_score (filter (fun x => negb (p x)) xs) weight g.
Proof.
 intros A xs weight f g p.
 unfold finite_weighted_score.
 transitivity (finite_sum (fun x =>
   if p x then weight x*f x else weight x*g x) xs).
 { apply finite_sum_ext; intro x; destruct (p x); reflexivity. }
 apply finite_sum_if_partition.
Qed.

(**
 [weighted_score_if_true_restriction] (theorem) — The p-true selected sample ignores the unused false branch of any piecewise score.
 Mathematical meaning: The p-true selected sample ignores the unused false branch of any piecewise score.
 Exact checked proposition: forall (A : Type) (xs : list A) (weight f g : A -> R) (p : A -> bool), finite_weighted_score (filter p xs) weight (fun x => if p x then f x else g x) = finite_weighted_score (filter p xs) weight f.
 Premises and side conditions: All finite enumerated score and Boolean-event functions, conditional denominators and positivity conditions are explicit in the theorem. Signed weights are permitted for algebraic equalities; probability meanings need normalized nonnegative mass.
 Proof/definition method: Use Stdlib.List.filter_In and FiniteSum.finite_sum_ext_in on the true-cell support.
 Library reuse: Stdlib.List.filter/filter_In, Stdlib.Reals/Field/Lra/Psatz/Ring, FiniteSum.finite_sum_* and previously checked FiniteTwoCellProjection results, with no duplicated recursive fold.
 Boundary: Deterministic finite joint Boolean observation and squared-error algebra; no general measure-theoretic L1 conditioning, Gaussian conditional laws or empirical IQ validation.
 *)
Theorem weighted_score_if_true_restriction :
 forall (A : Type) (xs : list A) (weight f g : A -> R) (p : A -> bool),
 finite_weighted_score (filter p xs) weight (fun x => if p x then f x else g x) =
 finite_weighted_score (filter p xs) weight f.
Proof.
 intros A xs weight f g p.
 unfold finite_weighted_score.
 apply finite_sum_ext_in; intros x Hx.
 apply filter_In in Hx.
 destruct Hx as [_ Hp].
 rewrite Hp; reflexivity.
Qed.

(**
 [weighted_score_if_false_restriction] (theorem) — The p-false selected sample ignores the unused true branch of any piecewise score.
 Mathematical meaning: The p-false selected sample ignores the unused true branch of any piecewise score.
 Exact checked proposition: forall (A : Type) (xs : list A) (weight f g : A -> R) (p : A -> bool), finite_weighted_score (filter (fun x=>negb (p x)) xs) weight (fun x => if p x then f x else g x) = finite_weighted_score (filter (fun x=>negb (p x)) xs) weight g.
 Premises and side conditions: All finite enumerated score and Boolean-event functions, conditional denominators and positivity conditions are explicit in the theorem. Signed weights are permitted for algebraic equalities; probability meanings need normalized nonnegative mass.
 Proof/definition method: Use Stdlib.List.filter_In with the complementary event and generic finite-sum extensionality.
 Library reuse: Stdlib.List.filter/filter_In, Stdlib.Reals/Field/Lra/Psatz/Ring, FiniteSum.finite_sum_* and previously checked FiniteTwoCellProjection results, with no duplicated recursive fold.
 Boundary: Deterministic finite joint Boolean observation and squared-error algebra; no general measure-theoretic L1 conditioning, Gaussian conditional laws or empirical IQ validation.
 *)
Theorem weighted_score_if_false_restriction :
 forall (A : Type) (xs : list A) (weight f g : A -> R) (p : A -> bool),
 finite_weighted_score (filter (fun x=>negb (p x)) xs) weight
   (fun x => if p x then f x else g x) =
 finite_weighted_score (filter (fun x=>negb (p x)) xs) weight g.
Proof.
 intros A xs weight f g p.
 unfold finite_weighted_score.
 apply finite_sum_ext_in; intros x Hx.
 apply filter_In in Hx.
 destruct Hx as [_ Hp].
 destruct (p x); simpl in Hp; [discriminate|reflexivity].
Qed.

(**
 [two_cell_predictor_true_moment] (theorem) — On the selected p-true observations, the original two-cell conditional-mean predictor has exactly mean times cell mass.
 Mathematical meaning: On the selected p-true observations, the original two-cell conditional-mean predictor has exactly mean times cell mass.
 Exact checked proposition: forall (A : Type) (xs : list A) (weight score : A -> R) (p : A -> bool), finite_weighted_score (filter p xs) weight (finite_two_cell_prediction xs weight score p) = finite_true_mean xs weight score p * finite_true_mass xs weight p.
 Premises and side conditions: All finite enumerated score and Boolean-event functions, conditional denominators and positivity conditions are explicit in the theorem. Signed weights are permitted for algebraic equalities; probability meanings need normalized nonnegative mass.
 Proof/definition method: Show the predictor is a constant on its true support, then reuse finite_weighted_score_constant.
 Library reuse: Stdlib.List.filter/filter_In, Stdlib.Reals/Field/Lra/Psatz/Ring, FiniteSum.finite_sum_* and previously checked FiniteTwoCellProjection results, with no duplicated recursive fold.
 Boundary: Deterministic finite joint Boolean observation and squared-error algebra; no general measure-theoretic L1 conditioning, Gaussian conditional laws or empirical IQ validation.
 *)
Theorem two_cell_predictor_true_moment :
 forall (A : Type) (xs : list A) (weight score : A -> R) (p : A -> bool),
 finite_weighted_score (filter p xs) weight
   (finite_two_cell_prediction xs weight score p) =
 finite_true_mean xs weight score p * finite_true_mass xs weight p.
Proof.
 intros A xs weight score p.
 transitivity (finite_weighted_score (filter p xs) weight
   (fun _ => finite_true_mean xs weight score p)).
 { unfold finite_weighted_score.
   apply finite_sum_ext_in; intros x Hx.
   apply filter_In in Hx; destruct Hx as [_ Hp].
   unfold finite_two_cell_prediction; rewrite Hp; reflexivity. }
 rewrite finite_weighted_score_constant.
 reflexivity.
Qed.

(**
 [two_cell_predictor_false_moment] (theorem) — On the p-false observations, the two-cell conditional-mean predictor has mean times complementary cell mass.
 Mathematical meaning: On the p-false observations, the two-cell conditional-mean predictor has mean times complementary cell mass.
 Exact checked proposition: forall (A : Type) (xs : list A) (weight score : A -> R) (p : A -> bool), finite_weighted_score (filter (fun x=>negb (p x)) xs) weight (finite_two_cell_prediction xs weight score p) = finite_false_mean xs weight score p * finite_false_mass xs weight p.
 Premises and side conditions: All finite enumerated score and Boolean-event functions, conditional denominators and positivity conditions are explicit in the theorem. Signed weights are permitted for algebraic equalities; probability meanings need normalized nonnegative mass.
 Proof/definition method: Use the complementary filtered support and constant-score aggregation.
 Library reuse: Stdlib.List.filter/filter_In, Stdlib.Reals/Field/Lra/Psatz/Ring, FiniteSum.finite_sum_* and previously checked FiniteTwoCellProjection results, with no duplicated recursive fold.
 Boundary: Deterministic finite joint Boolean observation and squared-error algebra; no general measure-theoretic L1 conditioning, Gaussian conditional laws or empirical IQ validation.
 *)
Theorem two_cell_predictor_false_moment :
 forall (A : Type) (xs : list A) (weight score : A -> R) (p : A -> bool),
 finite_weighted_score (filter (fun x=>negb (p x)) xs) weight
   (finite_two_cell_prediction xs weight score p) =
 finite_false_mean xs weight score p * finite_false_mass xs weight p.
Proof.
 intros A xs weight score p.
 transitivity (finite_weighted_score (filter (fun x=>negb (p x)) xs)
   weight (fun _ => finite_false_mean xs weight score p)).
 { unfold finite_weighted_score.
   apply finite_sum_ext_in; intros x Hx.
   apply filter_In in Hx; destruct Hx as [_ Hp].
   unfold finite_two_cell_prediction.
   destruct (p x); simpl in Hp; [discriminate|reflexivity]. }
 rewrite finite_weighted_score_constant.
 reflexivity.
Qed.

(**
 [two_cell_predictor_true_mean_fixed] (theorem) — Reapplying conditional averaging to the original two-cell predictor preserves the original true-cell mean.
 Mathematical meaning: Reapplying conditional averaging to the original two-cell predictor preserves the original true-cell mean.
 Exact checked proposition: forall (A : Type) (xs : list A) (weight score : A -> R) (p : A -> bool), finite_true_mass xs weight p <> 0 -> finite_true_mean xs weight (finite_two_cell_prediction xs weight score p) p = finite_true_mean xs weight score p.
 Premises and side conditions: All finite enumerated score and Boolean-event functions, conditional denominators and positivity conditions are explicit in the theorem. Signed weights are permitted for algebraic equalities; probability meanings need normalized nonnegative mass.
 Proof/definition method: Establish the finite conditional projection fixed-point property through the positive-cell mass cancellation.
 Library reuse: Stdlib.List.filter/filter_In, Stdlib.Reals/Field/Lra/Psatz/Ring, FiniteSum.finite_sum_* and previously checked FiniteTwoCellProjection results, with no duplicated recursive fold.
 Boundary: Deterministic finite joint Boolean observation and squared-error algebra; no general measure-theoretic L1 conditioning, Gaussian conditional laws or empirical IQ validation.
 *)
Theorem two_cell_predictor_true_mean_fixed :
 forall (A : Type) (xs : list A) (weight score : A -> R) (p : A -> bool),
 finite_true_mass xs weight p <> 0 ->
 finite_true_mean xs weight
    (finite_two_cell_prediction xs weight score p) p =
 finite_true_mean xs weight score p.
Proof.
 intros A xs weight score p Hm.
 unfold finite_true_mean at 1.
 unfold finite_weighted_mean at 1.
 rewrite two_cell_predictor_true_moment.
 change ((finite_true_mean xs weight score p * finite_true_mass xs weight p) /
   finite_true_mass xs weight p = finite_true_mean xs weight score p).
 field; exact Hm.
Qed.

(**
 [two_cell_predictor_false_mean_fixed] (theorem) — Reapplying conditional averaging preserves the original complementary-cell mean.
 Mathematical meaning: Reapplying conditional averaging preserves the original complementary-cell mean.
 Exact checked proposition: forall (A : Type) (xs : list A) (weight score : A -> R) (p : A -> bool), finite_false_mass xs weight p <> 0 -> finite_false_mean xs weight (finite_two_cell_prediction xs weight score p) p = finite_false_mean xs weight score p.
 Premises and side conditions: All finite enumerated score and Boolean-event functions, conditional denominators and positivity conditions are explicit in the theorem. Signed weights are permitted for algebraic equalities; probability meanings need normalized nonnegative mass.
 Proof/definition method: Reuse the filtered constant-predictor moment and exact denominator cancellation.
 Library reuse: Stdlib.List.filter/filter_In, Stdlib.Reals/Field/Lra/Psatz/Ring, FiniteSum.finite_sum_* and previously checked FiniteTwoCellProjection results, with no duplicated recursive fold.
 Boundary: Deterministic finite joint Boolean observation and squared-error algebra; no general measure-theoretic L1 conditioning, Gaussian conditional laws or empirical IQ validation.
 *)
Theorem two_cell_predictor_false_mean_fixed :
 forall (A : Type) (xs : list A) (weight score : A -> R) (p : A -> bool),
 finite_false_mass xs weight p <> 0 ->
 finite_false_mean xs weight
    (finite_two_cell_prediction xs weight score p) p =
 finite_false_mean xs weight score p.
Proof.
 intros A xs weight score p Hm.
 unfold finite_false_mean at 1.
 unfold finite_weighted_mean at 1.
 rewrite two_cell_predictor_false_moment.
 change ((finite_false_mean xs weight score p * finite_false_mass xs weight p) /
   finite_false_mass xs weight p = finite_false_mean xs weight score p).
 field; exact Hm.
Qed.

(**
 [two_cell_projection_idempotent] (theorem) — Conditional projection onto the same two Boolean cells is idempotent at every outcome, not just on average.
 Mathematical meaning: Conditional projection onto the same two Boolean cells is idempotent at every outcome, not just on average.
 Exact checked proposition: forall (A : Type) (xs : list A) (weight score : A -> R) (p : A -> bool) (x : A), finite_true_mass xs weight p <> 0 -> finite_false_mass xs weight p <> 0 -> finite_two_cell_prediction xs weight (finite_two_cell_prediction xs weight score p) p x = finite_two_cell_prediction xs weight score p x.
 Premises and side conditions: All finite enumerated score and Boolean-event functions, conditional denominators and positivity conditions are explicit in the theorem. Signed weights are permitted for algebraic equalities; probability meanings need normalized nonnegative mass.
 Proof/definition method: Combine the two conditional mean fixed-point results into the projection idempotence law.
 Library reuse: Stdlib.List.filter/filter_In, Stdlib.Reals/Field/Lra/Psatz/Ring, FiniteSum.finite_sum_* and previously checked FiniteTwoCellProjection results, with no duplicated recursive fold.
 Boundary: Deterministic finite joint Boolean observation and squared-error algebra; no general measure-theoretic L1 conditioning, Gaussian conditional laws or empirical IQ validation.
 *)
Theorem two_cell_projection_idempotent :
 forall (A : Type) (xs : list A) (weight score : A -> R)
 (p : A -> bool) (x : A),
 finite_true_mass xs weight p <> 0 ->
 finite_false_mass xs weight p <> 0 ->
 finite_two_cell_prediction xs weight
    (finite_two_cell_prediction xs weight score p) p x =
 finite_two_cell_prediction xs weight score p x.
Proof.
 intros A xs weight score p x Ht Hf.
 change
 (if p x then finite_true_mean xs weight
      (finite_two_cell_prediction xs weight score p) p
  else finite_false_mean xs weight
      (finite_two_cell_prediction xs weight score p) p =
  if p x then finite_true_mean xs weight score p
  else finite_false_mean xs weight score p).
 destruct (p x).
 - apply two_cell_predictor_true_mean_fixed; exact Ht.
 - apply two_cell_predictor_false_mean_fixed; exact Hf.
Qed.

(**
 [nested_true_mass_partition] (theorem) — Partitioning the coarse true group by q recovers its full mass exactly.
 Mathematical meaning: Partitioning the coarse true group by q recovers its full mass exactly.
 Exact checked proposition: forall (A : Type) (xs : list A) (weight : A -> R) (p q : A -> bool), finite_true_mass (filter p xs) weight q + finite_false_mass (filter p xs) weight q = finite_true_mass xs weight p.
 Premises and side conditions: All finite enumerated score and Boolean-event functions, conditional denominators and positivity conditions are explicit in the theorem. Signed weights are permitted for algebraic equalities; probability meanings need normalized nonnegative mass.
 Proof/definition method: Specialize the already checked two-cell mass partition to the first selected subgroup.
 Library reuse: Stdlib.List.filter/filter_In, Stdlib.Reals/Field/Lra/Psatz/Ring, FiniteSum.finite_sum_* and previously checked FiniteTwoCellProjection results, with no duplicated recursive fold.
 Boundary: Deterministic finite joint Boolean observation and squared-error algebra; no general measure-theoretic L1 conditioning, Gaussian conditional laws or empirical IQ validation.
 *)
Theorem nested_true_mass_partition :
 forall (A : Type) (xs : list A) (weight : A -> R)
 (p q : A -> bool),
 finite_true_mass (filter p xs) weight q +
 finite_false_mass (filter p xs) weight q =
 finite_true_mass xs weight p.
Proof.
 intros A xs weight p q.
 exact (finite_two_cell_mass_partition A (filter p xs) weight q).
Qed.

(**
 [nested_false_mass_partition] (theorem) — Partitioning the coarse false group by q also recovers its full mass exactly.
 Mathematical meaning: Partitioning the coarse false group by q also recovers its full mass exactly.
 Exact checked proposition: forall (A : Type) (xs : list A) (weight : A -> R) (p q : A -> bool), finite_true_mass (filter (fun x=>negb(p x)) xs) weight q + finite_false_mass (filter (fun x=>negb(p x)) xs) weight q = finite_false_mass xs weight p.
 Premises and side conditions: All finite enumerated score and Boolean-event functions, conditional denominators and positivity conditions are explicit in the theorem. Signed weights are permitted for algebraic equalities; probability meanings need normalized nonnegative mass.
 Proof/definition method: Specialize maintained Boolean-partition mass conservation to the complementary first subgroup.
 Library reuse: Stdlib.List.filter/filter_In, Stdlib.Reals/Field/Lra/Psatz/Ring, FiniteSum.finite_sum_* and previously checked FiniteTwoCellProjection results, with no duplicated recursive fold.
 Boundary: Deterministic finite joint Boolean observation and squared-error algebra; no general measure-theoretic L1 conditioning, Gaussian conditional laws or empirical IQ validation.
 *)
Theorem nested_false_mass_partition :
 forall (A : Type) (xs : list A) (weight : A -> R)
 (p q : A -> bool),
 finite_true_mass (filter (fun x=>negb(p x)) xs) weight q +
 finite_false_mass (filter (fun x=>negb(p x)) xs) weight q =
 finite_false_mass xs weight p.
Proof.
 intros A xs weight p q.
 exact (finite_two_cell_mass_partition A
   (filter (fun x => negb(p x)) xs) weight q).
Qed.

(**
 [nested_four_cell_total_mass] (theorem) — All four joint observations have precisely the original total weighted sample mass.
 Mathematical meaning: All four joint observations have precisely the original total weighted sample mass.
 Exact checked proposition: forall (A : Type) (xs : list A) (weight : A -> R) (p q : A -> bool), (finite_true_mass (filter p xs) weight q + finite_false_mass (filter p xs) weight q) + (finite_true_mass (filter (fun x=>negb(p x)) xs) weight q + finite_false_mass (filter (fun x=>negb(p x)) xs) weight q) = finite_weight_mass xs weight.
 Premises and side conditions: All finite enumerated score and Boolean-event functions, conditional denominators and positivity conditions are explicit in the theorem. Signed weights are permitted for algebraic equalities; probability meanings need normalized nonnegative mass.
 Proof/definition method: Compose the two child partition equalities with the parent partition theorem.
 Library reuse: Stdlib.List.filter/filter_In, Stdlib.Reals/Field/Lra/Psatz/Ring, FiniteSum.finite_sum_* and previously checked FiniteTwoCellProjection results, with no duplicated recursive fold.
 Boundary: Deterministic finite joint Boolean observation and squared-error algebra; no general measure-theoretic L1 conditioning, Gaussian conditional laws or empirical IQ validation.
 *)
Theorem nested_four_cell_total_mass :
 forall (A : Type) (xs : list A) (weight : A -> R)
 (p q : A -> bool),
 (finite_true_mass (filter p xs) weight q +
  finite_false_mass (filter p xs) weight q) +
 (finite_true_mass (filter (fun x=>negb(p x)) xs) weight q +
  finite_false_mass (filter (fun x=>negb(p x)) xs) weight q) =
 finite_weight_mass xs weight.
Proof.
 intros A xs weight p q.
 rewrite nested_true_mass_partition, nested_false_mass_partition.
 apply finite_two_cell_mass_partition.
Qed.

(**
 [nested_four_cell_score_partition] (theorem) — The four joint score moments sum to the original weighted first moment without new list recursion.
 Mathematical meaning: The four joint score moments sum to the original weighted first moment without new list recursion.
 Exact checked proposition: forall (A : Type) (xs : list A) (weight score : A -> R) (p q : A -> bool), (finite_weighted_score (filter q (filter p xs)) weight score + finite_weighted_score (filter (fun x=>negb(q x)) (filter p xs)) weight score) + (finite_weighted_score (filter q (filter (fun x=>negb(p x)) xs)) weight score + finite_weighted_score (filter (fun x=>negb(q x)) (filter (fun x=>negb(p x)) xs)) weight score) = finite_weighted_score xs weight score.
 Premises and side conditions: All finite enumerated score and Boolean-event functions, conditional denominators and positivity conditions are explicit in the theorem. Signed weights are permitted for algebraic equalities; probability meanings need normalized nonnegative mass.
 Proof/definition method: Invoke three existing exact score-partition theorems rather than duplicating finite-list induction.
 Library reuse: Stdlib.List.filter/filter_In, Stdlib.Reals/Field/Lra/Psatz/Ring, FiniteSum.finite_sum_* and previously checked FiniteTwoCellProjection results, with no duplicated recursive fold.
 Boundary: Deterministic finite joint Boolean observation and squared-error algebra; no general measure-theoretic L1 conditioning, Gaussian conditional laws or empirical IQ validation.
 *)
Theorem nested_four_cell_score_partition :
 forall (A : Type) (xs : list A) (weight score : A -> R)
 (p q : A -> bool),
 (finite_weighted_score (filter q (filter p xs)) weight score +
  finite_weighted_score (filter (fun x=>negb(q x)) (filter p xs)) weight score) +
 (finite_weighted_score (filter q (filter (fun x=>negb(p x)) xs)) weight score +
  finite_weighted_score (filter (fun x=>negb(q x))
    (filter (fun x=>negb(p x)) xs)) weight score) =
 finite_weighted_score xs weight score.
Proof.
 intros A xs weight score p q.
 rewrite (finite_two_cell_score_partition A (filter p xs) weight score q).
 rewrite (finite_two_cell_score_partition A (filter (fun x=>negb(p x)) xs)
   weight score q).
 apply finite_two_cell_score_partition.
Qed.

(**
 [nested_four_cell_loss_partition] (theorem) — The four joint within-cell squared-loss sums add up to the original loss for any shared constant predictor.
 Mathematical meaning: The four joint within-cell squared-loss sums add up to the original loss for any shared constant predictor.
 Exact checked proposition: forall (A : Type) (xs : list A) (weight score : A -> R) (p q : A -> bool) (a : R), (finite_weighted_loss (filter q (filter p xs)) weight score a + finite_weighted_loss (filter (fun x=>negb(q x)) (filter p xs)) weight score a) + (finite_weighted_loss (filter q (filter (fun x=>negb(p x)) xs)) weight score a + finite_weighted_loss (filter (fun x=>negb(q x)) (filter (fun x=>negb(p x)) xs)) weight score a) = finite_weighted_loss xs weight score a.
 Premises and side conditions: All finite enumerated score and Boolean-event functions, conditional denominators and positivity conditions are explicit in the theorem. Signed weights are permitted for algebraic equalities; probability meanings need normalized nonnegative mass.
 Proof/definition method: Compose the two-stage finite_loss_partition theorem over all four intersection cells.
 Library reuse: Stdlib.List.filter/filter_In, Stdlib.Reals/Field/Lra/Psatz/Ring, FiniteSum.finite_sum_* and previously checked FiniteTwoCellProjection results, with no duplicated recursive fold.
 Boundary: Deterministic finite joint Boolean observation and squared-error algebra; no general measure-theoretic L1 conditioning, Gaussian conditional laws or empirical IQ validation.
 *)
Theorem nested_four_cell_loss_partition :
 forall (A : Type) (xs : list A) (weight score : A -> R)
 (p q : A -> bool) (a : R),
 (finite_weighted_loss (filter q (filter p xs)) weight score a +
  finite_weighted_loss (filter (fun x=>negb(q x)) (filter p xs)) weight score a) +
 (finite_weighted_loss (filter q (filter (fun x=>negb(p x)) xs)) weight score a +
  finite_weighted_loss (filter (fun x=>negb(q x))
    (filter (fun x=>negb(p x)) xs)) weight score a) =
 finite_weighted_loss xs weight score a.
Proof.
 intros A xs weight score p q a.
 rewrite (finite_two_cell_loss_partition A (filter p xs) weight score q a).
 rewrite (finite_two_cell_loss_partition A (filter (fun x=>negb(p x)) xs)
   weight score q a).
 apply finite_two_cell_loss_partition.
Qed.

(**
 [nested_true_projection_moment] (theorem) — Refined prediction has exactly the original weighted first moment within the coarse true observation cell.
 Mathematical meaning: Refined prediction has exactly the original weighted first moment within the coarse true observation cell.
 Exact checked proposition: forall (A : Type) (xs : list A) (weight score : A -> R) (p q : A -> bool), finite_true_mass (filter p xs) weight q <> 0 -> finite_false_mass (filter p xs) weight q <> 0 -> finite_weighted_score (filter p xs) weight (refined_projection xs weight score p q) = finite_weighted_score (filter p xs) weight score.
 Premises and side conditions: All finite enumerated score and Boolean-event functions, conditional denominators and positivity conditions are explicit in the theorem. Signed weights are permitted for algebraic equalities; probability meanings need normalized nonnegative mass.
 Proof/definition method: Restrict the refined predictor to the true coarse cell and apply the previously checked conditional-score tower.
 Library reuse: Stdlib.List.filter/filter_In, Stdlib.Reals/Field/Lra/Psatz/Ring, FiniteSum.finite_sum_* and previously checked FiniteTwoCellProjection results, with no duplicated recursive fold.
 Boundary: Deterministic finite joint Boolean observation and squared-error algebra; no general measure-theoretic L1 conditioning, Gaussian conditional laws or empirical IQ validation.
 *)
Theorem nested_true_projection_moment :
 forall (A : Type) (xs : list A) (weight score : A -> R)
 (p q : A -> bool),
 finite_true_mass (filter p xs) weight q <> 0 ->
 finite_false_mass (filter p xs) weight q <> 0 ->
 finite_weighted_score (filter p xs) weight
   (refined_projection xs weight score p q) =
 finite_weighted_score (filter p xs) weight score.
Proof.
 intros A xs weight score p q Htt Htf.
 transitivity (finite_weighted_score (filter p xs) weight
   (finite_two_cell_prediction (filter p xs) weight score q)).
 { unfold finite_weighted_score.
   apply finite_sum_ext_in; intros x Hx.
   apply filter_In in Hx; destruct Hx as [_ Hp].
   unfold refined_projection; rewrite Hp; reflexivity. }
 apply finite_two_cell_tower_expectation; assumption.
Qed.

(**
 [nested_false_projection_moment] (theorem) — Refined prediction has exactly the original weighted moment within the coarse false observation cell.
 Mathematical meaning: Refined prediction has exactly the original weighted moment within the coarse false observation cell.
 Exact checked proposition: forall (A : Type) (xs : list A) (weight score : A -> R) (p q : A -> bool), finite_true_mass (filter (fun x=>negb(p x)) xs) weight q <> 0 -> finite_false_mass (filter (fun x=>negb(p x)) xs) weight q <> 0 -> finite_weighted_score (filter (fun x=>negb(p x)) xs) weight (refined_projection xs weight score p q) = finite_weighted_score (filter (fun x=>negb(p x)) xs) weight score.
 Premises and side conditions: All finite enumerated score and Boolean-event functions, conditional denominators and positivity conditions are explicit in the theorem. Signed weights are permitted for algebraic equalities; probability meanings need normalized nonnegative mass.
 Proof/definition method: Restrict the refined predictor to the complementary coarse cell and reuse the prior two-cell tower.
 Library reuse: Stdlib.List.filter/filter_In, Stdlib.Reals/Field/Lra/Psatz/Ring, FiniteSum.finite_sum_* and previously checked FiniteTwoCellProjection results, with no duplicated recursive fold.
 Boundary: Deterministic finite joint Boolean observation and squared-error algebra; no general measure-theoretic L1 conditioning, Gaussian conditional laws or empirical IQ validation.
 *)
Theorem nested_false_projection_moment :
 forall (A : Type) (xs : list A) (weight score : A -> R)
 (p q : A -> bool),
 finite_true_mass (filter (fun x=>negb(p x)) xs) weight q <> 0 ->
 finite_false_mass (filter (fun x=>negb(p x)) xs) weight q <> 0 ->
 finite_weighted_score (filter (fun x=>negb(p x)) xs) weight
   (refined_projection xs weight score p q) =
 finite_weighted_score (filter (fun x=>negb(p x)) xs) weight score.
Proof.
 intros A xs weight score p q Hft Hff.
 transitivity (finite_weighted_score (filter (fun x=>negb(p x)) xs) weight
   (finite_two_cell_prediction (filter (fun x=>negb(p x)) xs)
      weight score q)).
 { unfold finite_weighted_score.
   apply finite_sum_ext_in; intros x Hx.
   apply filter_In in Hx; destruct Hx as [_ Hp].
   unfold refined_projection.
   destruct (p x); simpl in Hp; [discriminate|reflexivity]. }
 apply finite_two_cell_tower_expectation; assumption.
Qed.

(**
 [nested_projection_tower_expectation] (theorem) — The full four-cell conditional prediction has the same unnormalized expectation as the original finite score.
 Mathematical meaning: The full four-cell conditional prediction has the same unnormalized expectation as the original finite score.
 Exact checked proposition: forall (A : Type) (xs : list A) (weight score : A -> R) (p q : A -> bool), finite_true_mass (filter p xs) weight q <> 0 -> finite_false_mass (filter p xs) weight q <> 0 -> finite_true_mass (filter (fun x=>negb(p x)) xs) weight q <> 0 -> finite_false_mass (filter (fun x=>negb(p x)) xs) weight q <> 0 -> finite_weighted_score xs weight (refined_projection xs weight score p q) = finite_weighted_score xs weight score.
 Premises and side conditions: All finite enumerated score and Boolean-event functions, conditional denominators and positivity conditions are explicit in the theorem. Signed weights are permitted for algebraic equalities; probability meanings need normalized nonnegative mass.
 Proof/definition method: Compose conditional expectation towers within each parent cell using the shared piecewise weighted-score decomposition.
 Library reuse: Stdlib.List.filter/filter_In, Stdlib.Reals/Field/Lra/Psatz/Ring, FiniteSum.finite_sum_* and previously checked FiniteTwoCellProjection results, with no duplicated recursive fold.
 Boundary: Deterministic finite joint Boolean observation and squared-error algebra; no general measure-theoretic L1 conditioning, Gaussian conditional laws or empirical IQ validation.
 *)
Theorem nested_projection_tower_expectation :
 forall (A : Type) (xs : list A) (weight score : A -> R)
 (p q : A -> bool),
 finite_true_mass (filter p xs) weight q <> 0 ->
 finite_false_mass (filter p xs) weight q <> 0 ->
 finite_true_mass (filter (fun x=>negb(p x)) xs) weight q <> 0 ->
 finite_false_mass (filter (fun x=>negb(p x)) xs) weight q <> 0 ->
 finite_weighted_score xs weight
    (refined_projection xs weight score p q) =
 finite_weighted_score xs weight score.
Proof.
 intros A xs weight score p q Htt Htf Hft Hff.
 unfold refined_projection.
 rewrite weighted_score_if_partition.
 rewrite (finite_two_cell_tower_expectation A (filter p xs)
   weight score q Htt Htf).
 rewrite (finite_two_cell_tower_expectation A
   (filter (fun x=>negb(p x)) xs) weight score q Hft Hff).
 apply finite_two_cell_score_partition.
Qed.

(**
 [nested_projection_coarse_tower] (theorem) — Projecting the refined four-cell prediction back onto the coarse observation returns exactly the original coarse predictor, pointwise.
 Mathematical meaning: Projecting the refined four-cell prediction back onto the coarse observation returns exactly the original coarse predictor, pointwise.
 Exact checked proposition: forall (A : Type) (xs : list A) (weight score : A -> R) (p q : A -> bool) (x : A), finite_true_mass (filter p xs) weight q <> 0 -> finite_false_mass (filter p xs) weight q <> 0 -> finite_true_mass (filter (fun y=>negb(p y)) xs) weight q <> 0 -> finite_false_mass (filter (fun y=>negb(p y)) xs) weight q <> 0 -> finite_two_cell_prediction xs weight (refined_projection xs weight score p q) p x = finite_two_cell_prediction xs weight score p x.
 Premises and side conditions: All finite enumerated score and Boolean-event functions, conditional denominators and positivity conditions are explicit in the theorem. Signed weights are permitted for algebraic equalities; probability meanings need normalized nonnegative mass.
 Proof/definition method: Prove the finite conditional expectation tower as a pointwise identity of coarse projections, using child-moment preservation.
 Library reuse: Stdlib.List.filter/filter_In, Stdlib.Reals/Field/Lra/Psatz/Ring, FiniteSum.finite_sum_* and previously checked FiniteTwoCellProjection results, with no duplicated recursive fold.
 Boundary: Deterministic finite joint Boolean observation and squared-error algebra; no general measure-theoretic L1 conditioning, Gaussian conditional laws or empirical IQ validation.
 *)
Theorem nested_projection_coarse_tower :
 forall (A : Type) (xs : list A) (weight score : A -> R)
 (p q : A -> bool) (x : A),
 finite_true_mass (filter p xs) weight q <> 0 ->
 finite_false_mass (filter p xs) weight q <> 0 ->
 finite_true_mass (filter (fun y=>negb(p y)) xs) weight q <> 0 ->
 finite_false_mass (filter (fun y=>negb(p y)) xs) weight q <> 0 ->
 finite_two_cell_prediction xs weight
   (refined_projection xs weight score p q) p x =
 finite_two_cell_prediction xs weight score p x.
Proof.
 intros A xs weight score p q x Htt Htf Hft Hff.
 assert (Htrue : finite_true_mean xs weight
   (refined_projection xs weight score p q) p =
   finite_true_mean xs weight score p).
 { unfold finite_true_mean, finite_weighted_mean.
   rewrite (nested_true_projection_moment A xs weight score p q Htt Htf).
   reflexivity. }
 assert (Hfalse : finite_false_mean xs weight
   (refined_projection xs weight score p q) p =
   finite_false_mean xs weight score p).
 { unfold finite_false_mean, finite_weighted_mean.
   rewrite (nested_false_projection_moment A xs weight score p q Hft Hff).
   reflexivity. }
 change
   (if p x then finite_true_mean xs weight
       (refined_projection xs weight score p q) p
    else finite_false_mean xs weight
       (refined_projection xs weight score p q) p =
    if p x then finite_true_mean xs weight score p
    else finite_false_mean xs weight score p).
 destruct (p x); assumption.
Qed.

(**
 [nested_projection_residual_mean_zero] (theorem) — The real score minus the refined prediction has globally zero weighted expectation.
 Mathematical meaning: The real score minus the refined prediction has globally zero weighted expectation.
 Exact checked proposition: forall (A : Type) (xs : list A) (weight score : A -> R) (p q : A -> bool), finite_true_mass (filter p xs) weight q <> 0 -> finite_false_mass (filter p xs) weight q <> 0 -> finite_true_mass (filter (fun x=>negb(p x)) xs) weight q <> 0 -> finite_false_mass (filter (fun x=>negb(p x)) xs) weight q <> 0 -> finite_weighted_score xs weight (fun x => score x - refined_projection xs weight score p q x) = 0.
 Premises and side conditions: All finite enumerated score and Boolean-event functions, conditional denominators and positivity conditions are explicit in the theorem. Signed weights are permitted for algebraic equalities; probability meanings need normalized nonnegative mass.
 Proof/definition method: Use the finite-score difference law and new two-stage tower property.
 Library reuse: Stdlib.List.filter/filter_In, Stdlib.Reals/Field/Lra/Psatz/Ring, FiniteSum.finite_sum_* and previously checked FiniteTwoCellProjection results, with no duplicated recursive fold.
 Boundary: Deterministic finite joint Boolean observation and squared-error algebra; no general measure-theoretic L1 conditioning, Gaussian conditional laws or empirical IQ validation.
 *)
Theorem nested_projection_residual_mean_zero :
 forall (A : Type) (xs : list A) (weight score : A -> R)
 (p q : A -> bool),
 finite_true_mass (filter p xs) weight q <> 0 ->
 finite_false_mass (filter p xs) weight q <> 0 ->
 finite_true_mass (filter (fun x=>negb(p x)) xs) weight q <> 0 ->
 finite_false_mass (filter (fun x=>negb(p x)) xs) weight q <> 0 ->
 finite_weighted_score xs weight
   (fun x => score x - refined_projection xs weight score p q x) = 0.
Proof.
 intros A xs weight score p q Htt Htf Hft Hff.
 rewrite finite_weighted_score_sub.
 rewrite (nested_projection_tower_expectation A xs weight score p q
   Htt Htf Hft Hff).
 ring.
Qed.

(**
 [nested_projection_residual_orthogonal] (theorem) — The refined prediction residual is orthogonal to every measurable four-cell score, not merely to each event indicator.
 Mathematical meaning: The refined prediction residual is orthogonal to every measurable four-cell score, not merely to each event indicator.
 Exact checked proposition: forall (A : Type) (xs : list A) (weight score : A -> R) (p q : A -> bool) (a b c d : R), finite_true_mass (filter p xs) weight q <> 0 -> finite_false_mass (filter p xs) weight q <> 0 -> finite_true_mass (filter (fun x=>negb(p x)) xs) weight q <> 0 -> finite_false_mass (filter (fun x=>negb(p x)) xs) weight q <> 0 -> finite_weighted_score xs weight (fun x => (score x-refined_projection xs weight score p q x)* refined_test_score p q a b c d x) = 0.
 Premises and side conditions: All finite enumerated score and Boolean-event functions, conditional denominators and positivity conditions are explicit in the theorem. Signed weights are permitted for algebraic equalities; probability meanings need normalized nonnegative mass.
 Proof/definition method: Use the old unconditional two-cell residual orthogonality separately inside each parent cell.
 Library reuse: Stdlib.List.filter/filter_In, Stdlib.Reals/Field/Lra/Psatz/Ring, FiniteSum.finite_sum_* and previously checked FiniteTwoCellProjection results, with no duplicated recursive fold.
 Boundary: Deterministic finite joint Boolean observation and squared-error algebra; no general measure-theoretic L1 conditioning, Gaussian conditional laws or empirical IQ validation.
 *)
Theorem nested_projection_residual_orthogonal :
 forall (A : Type) (xs : list A) (weight score : A -> R)
 (p q : A -> bool) (a b c d : R),
 finite_true_mass (filter p xs) weight q <> 0 ->
 finite_false_mass (filter p xs) weight q <> 0 ->
 finite_true_mass (filter (fun x=>negb(p x)) xs) weight q <> 0 ->
 finite_false_mass (filter (fun x=>negb(p x)) xs) weight q <> 0 ->
 finite_weighted_score xs weight (fun x =>
    (score x-refined_projection xs weight score p q x)*
    refined_test_score p q a b c d x) = 0.
Proof.
 intros A xs weight score p q a b c d Htt Htf Hft Hff.
 transitivity
  (finite_weighted_score xs weight (fun x =>
    if p x then
      (score x-finite_two_cell_prediction (filter p xs)
        weight score q x)*(if q x then a else b)
    else
      (score x-finite_two_cell_prediction
        (filter (fun y=>negb(p y)) xs) weight score q x)*
        (if q x then c else d))).
 { unfold finite_weighted_score, refined_projection, refined_test_score.
   apply finite_sum_ext; intro x; destruct (p x); reflexivity. }
 rewrite weighted_score_if_partition.
 rewrite (finite_two_cell_residual_orthogonal A
   (filter p xs) weight score q a b Htt Htf).
 rewrite (finite_two_cell_residual_orthogonal A
   (filter (fun y=>negb(p y)) xs) weight score q c d Hft Hff).
 ring.
Qed.

(**
 [nested_candidate_risk_global] (theorem) — Four independently chosen cell constants have the exact literal global weighted squared-loss form.
 Mathematical meaning: Four independently chosen cell constants have the exact literal global weighted squared-loss form.
 Exact checked proposition: forall (A : Type) (xs : list A) (weight score : A -> R) (p q : A -> bool) (a b c d : R), refined_candidate_risk xs weight score p q a b c d = finite_sum (fun x => weight x*(score x-refined_test_score p q a b c d x)* (score x-refined_test_score p q a b c d x)) xs.
 Premises and side conditions: All finite enumerated score and Boolean-event functions, conditional denominators and positivity conditions are explicit in the theorem. Signed weights are permitted for algebraic equalities; probability meanings need normalized nonnegative mass.
 Proof/definition method: Reuse generic if-partition summation and the prior exact risk-as-global-dot-product theorem in each parent subgroup.
 Library reuse: Stdlib.List.filter/filter_In, Stdlib.Reals/Field/Lra/Psatz/Ring, FiniteSum.finite_sum_* and previously checked FiniteTwoCellProjection results, with no duplicated recursive fold.
 Boundary: Deterministic finite joint Boolean observation and squared-error algebra; no general measure-theoretic L1 conditioning, Gaussian conditional laws or empirical IQ validation.
 *)
Theorem nested_candidate_risk_global :
 forall (A : Type) (xs : list A) (weight score : A -> R)
 (p q : A -> bool) (a b c d : R),
 refined_candidate_risk xs weight score p q a b c d =
 finite_sum (fun x =>
   weight x*(score x-refined_test_score p q a b c d x)*
   (score x-refined_test_score p q a b c d x)) xs.
Proof.
 intros A xs weight score p q a b c d.
 unfold refined_candidate_risk.
 symmetry.
 transitivity (finite_sum (fun x =>
   if p x then
     weight x*(score x-(if q x then a else b))*
       (score x-(if q x then a else b))
   else
     weight x*(score x-(if q x then c else d))*
       (score x-(if q x then c else d))) xs).
 { apply finite_sum_ext; intro x.
   unfold refined_test_score; destruct (p x); reflexivity. }
 rewrite finite_sum_if_partition.
 rewrite <- (finite_two_cell_risk_global_representation A
   (filter p xs) weight score q a b).
 rewrite <- (finite_two_cell_risk_global_representation A
   (filter (fun x=>negb(p x)) xs) weight score q c d).
 reflexivity.
Qed.

(**
 [nested_optimal_risk_global] (theorem) — The refined four-cell conditional predictor's squared error equals its explicitly aggregated optimal cell risk.
 Mathematical meaning: The refined four-cell conditional predictor's squared error equals its explicitly aggregated optimal cell risk.
 Exact checked proposition: forall (A : Type) (xs : list A) (weight score : A -> R) (p q : A -> bool), refined_optimal_risk xs weight score p q = finite_sum (fun x => weight x*(score x-refined_projection xs weight score p q x)* (score x-refined_projection xs weight score p q x)) xs.
 Premises and side conditions: All finite enumerated score and Boolean-event functions, conditional denominators and positivity conditions are explicit in the theorem. Signed weights are permitted for algebraic equalities; probability meanings need normalized nonnegative mass.
 Proof/definition method: Specialize the exact four-constant risk equality to the four true conditional means, retaining the actual predictor function.
 Library reuse: Stdlib.List.filter/filter_In, Stdlib.Reals/Field/Lra/Psatz/Ring, FiniteSum.finite_sum_* and previously checked FiniteTwoCellProjection results, with no duplicated recursive fold.
 Boundary: Deterministic finite joint Boolean observation and squared-error algebra; no general measure-theoretic L1 conditioning, Gaussian conditional laws or empirical IQ validation.
 *)
Theorem nested_optimal_risk_global :
 forall (A : Type) (xs : list A) (weight score : A -> R)
 (p q : A -> bool),
 refined_optimal_risk xs weight score p q =
 finite_sum (fun x =>
   weight x*(score x-refined_projection xs weight score p q x)*
   (score x-refined_projection xs weight score p q x)) xs.
Proof.
 intros A xs weight score p q.
 unfold refined_optimal_risk.
 rewrite nested_candidate_risk_global.
 unfold refined_test_score, refined_projection, finite_two_cell_prediction.
 reflexivity.
Qed.

(**
 [nested_coarse_risk_as_candidate] (theorem) — The coarse two-cell prediction risk equals the four-cell candidate risk that reuses each coarse prediction in both of its q-subcells.
 Mathematical meaning: The coarse two-cell prediction risk equals the four-cell candidate risk that reuses each coarse prediction in both of its q-subcells.
 Exact checked proposition: forall (A : Type) (xs : list A) (weight score : A -> R) (p q : A -> bool), finite_two_cell_risk xs weight score p (finite_true_mean xs weight score p) (finite_false_mean xs weight score p) = refined_candidate_risk xs weight score p q (finite_true_mean xs weight score p) (finite_true_mean xs weight score p) (finite_false_mean xs weight score p) (finite_false_mean xs weight score p).
 Premises and side conditions: All finite enumerated score and Boolean-event functions, conditional denominators and positivity conditions are explicit in the theorem. Signed weights are permitted for algebraic equalities; probability meanings need normalized nonnegative mass.
 Proof/definition method: Replace the duplicated coarse coefficients with two applications of the generic two-cell loss partition.
 Library reuse: Stdlib.List.filter/filter_In, Stdlib.Reals/Field/Lra/Psatz/Ring, FiniteSum.finite_sum_* and previously checked FiniteTwoCellProjection results, with no duplicated recursive fold.
 Boundary: Deterministic finite joint Boolean observation and squared-error algebra; no general measure-theoretic L1 conditioning, Gaussian conditional laws or empirical IQ validation.
 *)
Theorem nested_coarse_risk_as_candidate :
 forall (A : Type) (xs : list A) (weight score : A -> R)
 (p q : A -> bool),
 finite_two_cell_risk xs weight score p
  (finite_true_mean xs weight score p)
  (finite_false_mean xs weight score p) =
 refined_candidate_risk xs weight score p q
  (finite_true_mean xs weight score p)
  (finite_true_mean xs weight score p)
  (finite_false_mean xs weight score p)
  (finite_false_mean xs weight score p).
Proof.
 intros A xs weight score p q.
 symmetry.
 unfold refined_candidate_risk, finite_two_cell_risk.
 rewrite (finite_two_cell_loss_partition A (filter p xs) weight score q
   (finite_true_mean xs weight score p)).
 rewrite (finite_two_cell_loss_partition A
   (filter (fun x=>negb(p x)) xs) weight score q
   (finite_false_mean xs weight score p)).
 reflexivity.
Qed.

(**
 [nested_optimal_risk_minimizer] (theorem) — When all four observed joint cells have positive mass, the refined predictor globally minimizes loss among every four-cell candidate.
 Mathematical meaning: When all four observed joint cells have positive mass, the refined predictor globally minimizes loss among every four-cell candidate.
 Exact checked proposition: forall (A : Type) (xs : list A) (weight score : A -> R) (p q : A -> bool) (a b c d : R), 0<finite_true_mass (filter p xs) weight q -> 0<finite_false_mass (filter p xs) weight q -> 0<finite_true_mass (filter (fun x=>negb(p x)) xs) weight q -> 0<finite_false_mass (filter (fun x=>negb(p x)) xs) weight q -> refined_optimal_risk xs weight score p q <= refined_candidate_risk xs weight score p q a b c d.
 Premises and side conditions: All finite enumerated score and Boolean-event functions, conditional denominators and positivity conditions are explicit in the theorem. Signed weights are permitted for algebraic equalities; probability meanings need normalized nonnegative mass.
 Proof/definition method: Lift the already kernel-checked two-cell least-squares minimizer to four arbitrary cell constants by additivity.
 Library reuse: Stdlib.List.filter/filter_In, Stdlib.Reals/Field/Lra/Psatz/Ring, FiniteSum.finite_sum_* and previously checked FiniteTwoCellProjection results, with no duplicated recursive fold.
 Boundary: Deterministic finite joint Boolean observation and squared-error algebra; no general measure-theoretic L1 conditioning, Gaussian conditional laws or empirical IQ validation.
 *)
Theorem nested_optimal_risk_minimizer :
 forall (A : Type) (xs : list A) (weight score : A -> R)
 (p q : A -> bool) (a b c d : R),
 0<finite_true_mass (filter p xs) weight q ->
 0<finite_false_mass (filter p xs) weight q ->
 0<finite_true_mass (filter (fun x=>negb(p x)) xs) weight q ->
 0<finite_false_mass (filter (fun x=>negb(p x)) xs) weight q ->
 refined_optimal_risk xs weight score p q <=
 refined_candidate_risk xs weight score p q a b c d.
Proof.
 intros A xs weight score p q a b c d Htt Htf Hft Hff.
 unfold refined_optimal_risk, refined_candidate_risk.
 pose proof (finite_two_cell_risk_optimal A (filter p xs)
   weight score q a b Htt Htf) as H1.
 pose proof (finite_two_cell_risk_optimal A
   (filter (fun x=>negb(p x)) xs) weight score q c d Hft Hff) as H2.
 lra.
Qed.

(**
 [weighted_squared_penalty_nonnegative] (theorem) — Nonnegative mass times the square of any prediction error is nonnegative, even for signed prediction errors.
 Mathematical meaning: Nonnegative mass times the square of any prediction error is nonnegative, even for signed prediction errors.
 Exact checked proposition: forall (mass err : R), 0<=mass -> 0<=mass*err*err.
 Premises and side conditions: All finite enumerated score and Boolean-event functions, conditional denominators and positivity conditions are explicit in the theorem. Signed weights are permitted for algebraic equalities; probability meanings need normalized nonnegative mass.
 Proof/definition method: Reuse Rocq's Rsqr nonnegativity and Rmult_le_pos rather than a custom nonlinear positivity argument.
 Library reuse: Stdlib.List.filter/filter_In, Stdlib.Reals/Field/Lra/Psatz/Ring, FiniteSum.finite_sum_* and previously checked FiniteTwoCellProjection results, with no duplicated recursive fold.
 Boundary: Deterministic finite joint Boolean observation and squared-error algebra; no general measure-theoretic L1 conditioning, Gaussian conditional laws or empirical IQ validation.
 *)
Theorem weighted_squared_penalty_nonnegative :
 forall (mass err : R), 0<=mass -> 0<=mass*err*err.
Proof.
 intros mass err Hm.
 replace (mass*err*err) with (mass*Rsqr err)
   by (unfold Rsqr; ring).
 apply Rmult_le_pos; [assumption|apply Rle_0_sqr].
Qed.

(**
 [nested_refinement_variance_decomposition] (theorem) — The exact reduction in mean-square risk from observing q after p equals four weighted squared shifts of the conditional means.
 Mathematical meaning: The exact reduction in mean-square risk from observing q after p equals four weighted squared shifts of the conditional means.
 Exact checked proposition: forall (A : Type) (xs : list A) (weight score : A -> R) (p q : A -> bool), finite_true_mass (filter p xs) weight q <> 0 -> finite_false_mass (filter p xs) weight q <> 0 -> finite_true_mass (filter (fun x=>negb(p x)) xs) weight q <> 0 -> finite_false_mass (filter (fun x=>negb(p x)) xs) weight q <> 0 -> finite_two_cell_risk xs weight score p (finite_true_mean xs weight score p) (finite_false_mean xs weight score p) = refined_optimal_risk xs weight score p q + refined_between_loss xs weight score p q.
 Premises and side conditions: All finite enumerated score and Boolean-event functions, conditional denominators and positivity conditions are explicit in the theorem. Signed weights are permitted for algebraic equalities; probability meanings need normalized nonnegative mass.
 Proof/definition method: Apply the existing two-cell total squared-risk decomposition separately to each parent cell; no new probability/measure primitives.
 Library reuse: Stdlib.List.filter/filter_In, Stdlib.Reals/Field/Lra/Psatz/Ring, FiniteSum.finite_sum_* and previously checked FiniteTwoCellProjection results, with no duplicated recursive fold.
 Boundary: Deterministic finite joint Boolean observation and squared-error algebra; no general measure-theoretic L1 conditioning, Gaussian conditional laws or empirical IQ validation.
 *)
Theorem nested_refinement_variance_decomposition :
 forall (A : Type) (xs : list A) (weight score : A -> R)
 (p q : A -> bool),
 finite_true_mass (filter p xs) weight q <> 0 ->
 finite_false_mass (filter p xs) weight q <> 0 ->
 finite_true_mass (filter (fun x=>negb(p x)) xs) weight q <> 0 ->
 finite_false_mass (filter (fun x=>negb(p x)) xs) weight q <> 0 ->
 finite_two_cell_risk xs weight score p
   (finite_true_mean xs weight score p)
   (finite_false_mean xs weight score p) =
 refined_optimal_risk xs weight score p q +
 refined_between_loss xs weight score p q.
Proof.
 intros A xs weight score p q Htt Htf Hft Hff.
 rewrite nested_coarse_risk_as_candidate.
 unfold refined_candidate_risk at 1.
 rewrite (finite_two_cell_risk_completed_square A
   (filter p xs) weight score q
   (finite_true_mean xs weight score p)
   (finite_true_mean xs weight score p) Htt Htf).
 rewrite (finite_two_cell_risk_completed_square A
   (filter (fun x=>negb(p x)) xs) weight score q
   (finite_false_mean xs weight score p)
   (finite_false_mean xs weight score p) Hft Hff).
 unfold refined_optimal_risk, refined_candidate_risk, refined_between_loss.
 ring.
Qed.

(**
 [nested_between_loss_nonnegative] (theorem) — Every newly explained component in the second-stage law of total variance is nonnegative whenever all four joint cell masses are nonnegative.
 Mathematical meaning: Every newly explained component in the second-stage law of total variance is nonnegative whenever all four joint cell masses are nonnegative.
 Exact checked proposition: forall (A : Type) (xs : list A) (weight score : A -> R) (p q : A -> bool), 0<=finite_true_mass (filter p xs) weight q -> 0<=finite_false_mass (filter p xs) weight q -> 0<=finite_true_mass (filter (fun x=>negb(p x)) xs) weight q -> 0<=finite_false_mass (filter (fun x=>negb(p x)) xs) weight q -> 0<=refined_between_loss xs weight score p q.
 Premises and side conditions: All finite enumerated score and Boolean-event functions, conditional denominators and positivity conditions are explicit in the theorem. Signed weights are permitted for algebraic equalities; probability meanings need normalized nonnegative mass.
 Proof/definition method: Use the single standard-library-based weighted squared penalty theorem four times, avoiding duplicated positivity tactics.
 Library reuse: Stdlib.List.filter/filter_In, Stdlib.Reals/Field/Lra/Psatz/Ring, FiniteSum.finite_sum_* and previously checked FiniteTwoCellProjection results, with no duplicated recursive fold.
 Boundary: Deterministic finite joint Boolean observation and squared-error algebra; no general measure-theoretic L1 conditioning, Gaussian conditional laws or empirical IQ validation.
 *)
Theorem nested_between_loss_nonnegative :
 forall (A : Type) (xs : list A) (weight score : A -> R)
 (p q : A -> bool),
 0<=finite_true_mass (filter p xs) weight q ->
 0<=finite_false_mass (filter p xs) weight q ->
 0<=finite_true_mass (filter (fun x=>negb(p x)) xs) weight q ->
 0<=finite_false_mass (filter (fun x=>negb(p x)) xs) weight q ->
 0<=refined_between_loss xs weight score p q.
Proof.
 intros A xs weight score p q Htt Htf Hft Hff.
 unfold refined_between_loss.
 pose proof (weighted_squared_penalty_nonnegative
  (finite_true_mass (filter p xs) weight q)
  (finite_true_mean (filter p xs) weight score q -
   finite_true_mean xs weight score p) Htt) as H1.
 pose proof (weighted_squared_penalty_nonnegative
  (finite_false_mass (filter p xs) weight q)
  (finite_false_mean (filter p xs) weight score q -
   finite_true_mean xs weight score p) Htf) as H2.
 pose proof (weighted_squared_penalty_nonnegative
  (finite_true_mass (filter (fun x=>negb(p x)) xs) weight q)
  (finite_true_mean (filter (fun x=>negb(p x)) xs) weight score q -
   finite_false_mean xs weight score p) Hft) as H3.
 pose proof (weighted_squared_penalty_nonnegative
  (finite_false_mass (filter (fun x=>negb(p x)) xs) weight q)
  (finite_false_mean (filter (fun x=>negb(p x)) xs) weight score q -
   finite_false_mean xs weight score p) Hff) as H4.
 lra.
Qed.

(**
 [nested_refinement_cannot_increase_risk] (theorem) — Observing q in addition to p cannot worsen the optimal finite squared prediction risk.
 Mathematical meaning: Observing q in addition to p cannot worsen the optimal finite squared prediction risk.
 Exact checked proposition: forall (A : Type) (xs : list A) (weight score : A -> R) (p q : A -> bool), 0<finite_true_mass (filter p xs) weight q -> 0<finite_false_mass (filter p xs) weight q -> 0<finite_true_mass (filter (fun x=>negb(p x)) xs) weight q -> 0<finite_false_mass (filter (fun x=>negb(p x)) xs) weight q -> refined_optimal_risk xs weight score p q <= finite_two_cell_risk xs weight score p (finite_true_mean xs weight score p) (finite_false_mean xs weight score p).
 Premises and side conditions: All finite enumerated score and Boolean-event functions, conditional denominators and positivity conditions are explicit in the theorem. Signed weights are permitted for algebraic equalities; probability meanings need normalized nonnegative mass.
 Proof/definition method: Combine the exact refinement variance identity with the checked positivity of four squared corrections.
 Library reuse: Stdlib.List.filter/filter_In, Stdlib.Reals/Field/Lra/Psatz/Ring, FiniteSum.finite_sum_* and previously checked FiniteTwoCellProjection results, with no duplicated recursive fold.
 Boundary: Deterministic finite joint Boolean observation and squared-error algebra; no general measure-theoretic L1 conditioning, Gaussian conditional laws or empirical IQ validation.
 *)
Theorem nested_refinement_cannot_increase_risk :
 forall (A : Type) (xs : list A) (weight score : A -> R)
 (p q : A -> bool),
 0<finite_true_mass (filter p xs) weight q ->
 0<finite_false_mass (filter p xs) weight q ->
 0<finite_true_mass (filter (fun x=>negb(p x)) xs) weight q ->
 0<finite_false_mass (filter (fun x=>negb(p x)) xs) weight q ->
 refined_optimal_risk xs weight score p q <=
 finite_two_cell_risk xs weight score p
  (finite_true_mean xs weight score p)
  (finite_false_mean xs weight score p).
Proof.
 intros A xs weight score p q Htt Htf Hft Hff.
 assert (Htt0 : finite_true_mass (filter p xs) weight q <> 0) by lra.
 assert (Htf0 : finite_false_mass (filter p xs) weight q <> 0) by lra.
 assert (Hft0 : finite_true_mass (filter (fun x=>negb(p x)) xs) weight q <> 0) by lra.
 assert (Hff0 : finite_false_mass (filter (fun x=>negb(p x)) xs) weight q <> 0) by lra.
 pose proof (nested_refinement_variance_decomposition A xs weight score p q
   Htt0 Htf0 Hft0 Hff0) as Hdecomp.
 pose proof (nested_between_loss_nonnegative A xs weight score p q
   (Rlt_le _ _ Htt) (Rlt_le _ _ Htf)
   (Rlt_le _ _ Hft) (Rlt_le _ _ Hff)) as Hpos.
 lra.
Qed.

(**
 [nested_full_law_total_variance] (theorem) — The total finite variance decomposes into refined within-cell risk, newly explained four-cell variance, and the previously explained coarse two-cell variance.
 Mathematical meaning: The total finite variance decomposes into refined within-cell risk, newly explained four-cell variance, and the previously explained coarse two-cell variance.
 Exact checked proposition: forall (A : Type) (xs : list A) (weight score : A -> R) (p q : A -> bool), 0<finite_true_mass (filter p xs) weight q -> 0<finite_false_mass (filter p xs) weight q -> 0<finite_true_mass (filter (fun x=>negb(p x)) xs) weight q -> 0<finite_false_mass (filter (fun x=>negb(p x)) xs) weight q -> finite_weighted_loss xs weight score (finite_weighted_mean xs weight score) = refined_optimal_risk xs weight score p q + refined_between_loss xs weight score p q + finite_true_mass xs weight p * (finite_true_mean xs weight score p - finite_weighted_mean xs weight score) * (finite_true_mean xs weight score p - finite_weighted_mean xs weight score) + finite_false_mass xs weight p * (finite_false_mean xs weight score p - finite_weighted_mean xs weight score) * (finite_false_mean xs weight score p - finite_weighted_mean xs weight score).
 Premises and side conditions: All finite enumerated score and Boolean-event functions, conditional denominators and positivity conditions are explicit in the theorem. Signed weights are permitted for algebraic equalities; probability meanings need normalized nonnegative mass.
 Proof/definition method: Compose the previous two-cell law of total variance with the exact nested variance identity, preserving each observed-cell mass premise.
 Library reuse: Stdlib.List.filter/filter_In, Stdlib.Reals/Field/Lra/Psatz/Ring, FiniteSum.finite_sum_* and previously checked FiniteTwoCellProjection results, with no duplicated recursive fold.
 Boundary: Deterministic finite joint Boolean observation and squared-error algebra; no general measure-theoretic L1 conditioning, Gaussian conditional laws or empirical IQ validation.
 *)
Theorem nested_full_law_total_variance :
 forall (A : Type) (xs : list A) (weight score : A -> R)
 (p q : A -> bool),
 0<finite_true_mass (filter p xs) weight q ->
 0<finite_false_mass (filter p xs) weight q ->
 0<finite_true_mass (filter (fun x=>negb(p x)) xs) weight q ->
 0<finite_false_mass (filter (fun x=>negb(p x)) xs) weight q ->
 finite_weighted_loss xs weight score
   (finite_weighted_mean xs weight score) =
 refined_optimal_risk xs weight score p q +
 refined_between_loss xs weight score p q +
 finite_true_mass xs weight p *
   (finite_true_mean xs weight score p -
    finite_weighted_mean xs weight score) *
   (finite_true_mean xs weight score p -
    finite_weighted_mean xs weight score) +
 finite_false_mass xs weight p *
   (finite_false_mean xs weight score p -
    finite_weighted_mean xs weight score) *
   (finite_false_mean xs weight score p -
    finite_weighted_mean xs weight score).
Proof.
 intros A xs weight score p q Htt Htf Hft Hff.
 assert (Ht : finite_true_mass xs weight p <> 0).
 { pose proof (nested_true_mass_partition A xs weight p q) as Hm.
   nra. }
 assert (Hf : finite_false_mass xs weight p <> 0).
 { pose proof (nested_false_mass_partition A xs weight p q) as Hm.
   nra. }
 rewrite (finite_two_cell_total_variance A xs weight score p Ht Hf).
 rewrite (nested_refinement_variance_decomposition A xs weight score p q)
   by lra.
 ring.
Qed.

