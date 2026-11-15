(** Module: FiniteConditionalCovariance.v
 Purpose: Formalize finite conditional covariance, the exact law of total
 covariance, affine and bilinear conditional-expectation properties,
 and covariance polarization required by the reports' thm:moments and
 thm:conditional. This extends the proven FiniteTwoCellProjection and
 FiniteNestedProjection modules without introducing new probability axioms.
 Mathematical representation: Explicit lists of outcome occurrences,
 real weight/score functions, and Boolean observations. Every expectation,
 cross-loss and covariance is defined with the project's existing
 finite_weighted_score and FiniteSum.finite_sum; multiplicities persist.
 Explicit hypotheses: Nonzero total/cell masses for weighted means and
 projections; positive masses for probability/order interpretations;
 purely algebraic statements may use arbitrary signed weights.
 Library use: Rocq Stdlib List, Bool, Reals, Lra, Psatz and Ring/Field;
 existing FiniteSum filter/linearity lemmas, FiniteTwoCellProjection
 mean normalization and loss identities, and FiniteNestedProjection
 weighted squared positivity.
 Limitations: These are finite unnormalized covariance numerators, not
 arbitrary L1 conditional expectations or Gaussian conditional laws.
 No empirical psychometric distribution or independence is established.
 Reproduction: rocq compile FiniteConditionalCovariance.v after
 FiniteSum.v, FiniteTwoCellProjection.v and FiniteNestedProjection.v
 in the pinned Rocq 9.2 CI kernel workflow.
 AI disclosure: OpenAI's assistant drafted source and explanations;
 independently executed Rocq kernel checking establishes any proof claim.
 *)
From Stdlib Require Import Reals Lra Psatz List Bool.
Require Import FiniteSum FiniteTwoCellProjection FiniteNestedProjection.
Import ListNotations.
Open Scope R_scope.

(**
 [finite_weighted_cross] (definition) — The unnormalized weighted cross-loss for two arbitrary scores and prediction constants.
 Mathematical meaning: The unnormalized weighted cross-loss for two arbitrary scores and prediction constants.
 Exact declaration: Definition finite_weighted_cross {A : Type} (xs : list A) (weight f g : A -> R) (a b : R) : R := finite_weighted_score xs weight (fun x => (f x-a)*(g x-b)).
 Premises and side conditions: Explicit finite outcome list, arbitrary real weights and scores; hypotheses for nonzero masses appear where needed. Probability interpretation additionally requires normalized nonnegative weights.
 Proof/definition method: Transparent composition of existing finite weighted-score and two-cell APIs; no custom fold.
 Library reuse: Stdlib.List.filter, Stdlib.Reals/Lra/Psatz/Field/Ring, FiniteSum generic identities, and existing FiniteTwoCellProjection and FiniteNestedProjection facts. No duplicate finite-list recursion.
 Boundary: Finite weighted moments and Boolean observation only; no general L1 measure-theoretic or Gaussian conditional law and no empirical IQ claims.
 *)
Definition finite_weighted_cross {A : Type}
  (xs : list A) (weight f g : A -> R) (a b : R) : R :=
  finite_weighted_score xs weight (fun x => (f x-a)*(g x-b)).

(**
 [finite_centered_cross] (definition) — The exact finite weighted centered covariance numerator, without dividing by total mass.
 Mathematical meaning: The exact finite weighted centered covariance numerator, without dividing by total mass.
 Exact declaration: Definition finite_centered_cross {A : Type} (xs : list A) (weight f g : A -> R) : R := finite_weighted_cross xs weight f g (finite_weighted_mean xs weight f) (finite_weighted_mean xs weight g).
 Premises and side conditions: Explicit finite outcome list, arbitrary real weights and scores; hypotheses for nonzero masses appear where needed. Probability interpretation additionally requires normalized nonnegative weights.
 Proof/definition method: Transparent composition of existing finite weighted-score and two-cell APIs; no custom fold.
 Library reuse: Stdlib.List.filter, Stdlib.Reals/Lra/Psatz/Field/Ring, FiniteSum generic identities, and existing FiniteTwoCellProjection and FiniteNestedProjection facts. No duplicate finite-list recursion.
 Boundary: Finite weighted moments and Boolean observation only; no general L1 measure-theoretic or Gaussian conditional law and no empirical IQ claims.
 *)
Definition finite_centered_cross {A : Type}
  (xs : list A) (weight f g : A -> R) : R :=
  finite_weighted_cross xs weight f g
    (finite_weighted_mean xs weight f)
    (finite_weighted_mean xs weight g).

(**
 [finite_two_cell_within_cross] (definition) — Sum of the two centered within-cell cross-moments using actual filtered sample lists.
 Mathematical meaning: Sum of the two centered within-cell cross-moments using actual filtered sample lists.
 Exact declaration: Definition finite_two_cell_within_cross {A : Type} (xs : list A) (weight f g : A -> R) (event : A -> bool) : R := finite_centered_cross (filter event xs) weight f g + finite_centered_cross (filter (fun x=>negb(event x)) xs) weight f g.
 Premises and side conditions: Explicit finite outcome list, arbitrary real weights and scores; hypotheses for nonzero masses appear where needed. Probability interpretation additionally requires normalized nonnegative weights.
 Proof/definition method: Transparent composition of existing finite weighted-score and two-cell APIs; no custom fold.
 Library reuse: Stdlib.List.filter, Stdlib.Reals/Lra/Psatz/Field/Ring, FiniteSum generic identities, and existing FiniteTwoCellProjection and FiniteNestedProjection facts. No duplicate finite-list recursion.
 Boundary: Finite weighted moments and Boolean observation only; no general L1 measure-theoretic or Gaussian conditional law and no empirical IQ claims.
 *)
Definition finite_two_cell_within_cross {A : Type}
 (xs : list A) (weight f g : A -> R) (event : A -> bool) : R :=
 finite_centered_cross (filter event xs) weight f g +
 finite_centered_cross (filter (fun x=>negb(event x)) xs) weight f g.

(**
 [finite_two_cell_between_cross] (definition) — Mass-weighted product of conditional mean shifts on both observation cells.
 Mathematical meaning: Mass-weighted product of conditional mean shifts on both observation cells.
 Exact declaration: Definition finite_two_cell_between_cross {A : Type} (xs : list A) (weight f g : A -> R) (event : A -> bool) : R := finite_true_mass xs weight event * (finite_true_mean xs weight f event-finite_weighted_mean xs weight f) * (finite_true_mean xs weight g event-finite_weighted_mean xs weight g) + finite_false_mass xs weight event * (finite_false_mean xs weight f event-finite_weighted_mean xs weight f) * (finite_false_mean xs weight g event-finite_weighted_mean xs weight g).
 Premises and side conditions: Explicit finite outcome list, arbitrary real weights and scores; hypotheses for nonzero masses appear where needed. Probability interpretation additionally requires normalized nonnegative weights.
 Proof/definition method: Transparent composition of existing finite weighted-score and two-cell APIs; no custom fold.
 Library reuse: Stdlib.List.filter, Stdlib.Reals/Lra/Psatz/Field/Ring, FiniteSum generic identities, and existing FiniteTwoCellProjection and FiniteNestedProjection facts. No duplicate finite-list recursion.
 Boundary: Finite weighted moments and Boolean observation only; no general L1 measure-theoretic or Gaussian conditional law and no empirical IQ claims.
 *)
Definition finite_two_cell_between_cross {A : Type}
 (xs : list A) (weight f g : A -> R) (event : A -> bool) : R :=
 finite_true_mass xs weight event *
   (finite_true_mean xs weight f event-finite_weighted_mean xs weight f) *
   (finite_true_mean xs weight g event-finite_weighted_mean xs weight g) +
 finite_false_mass xs weight event *
   (finite_false_mean xs weight f event-finite_weighted_mean xs weight f) *
   (finite_false_mean xs weight g event-finite_weighted_mean xs weight g).

(**
 [finite_weighted_score_add] (theorem) — The finite weighted expectation of any two scores is additive without normalization assumptions.
 Mathematical meaning: The finite weighted expectation of any two scores is additive without normalization assumptions.
 Exact checked proposition: forall (A : Type) (xs : list A) (weight f g : A -> R), finite_weighted_score xs weight (fun x=>f x+g x) = finite_weighted_score xs weight f+finite_weighted_score xs weight g.
 Premises and side conditions: Explicit finite outcome list, arbitrary real weights and scores; hypotheses for nonzero masses appear where needed. Probability interpretation additionally requires normalized nonnegative weights.
 Proof/definition method: Use existing finite-sum linearity, verified mean/projection lemmas, and Rocq real ring/field arithmetic with explicitly written assumptions.
 Library reuse: Stdlib.List.filter, Stdlib.Reals/Lra/Psatz/Field/Ring, FiniteSum generic identities, and existing FiniteTwoCellProjection and FiniteNestedProjection facts. No duplicate finite-list recursion.
 Boundary: Finite weighted moments and Boolean observation only; no general L1 measure-theoretic or Gaussian conditional law and no empirical IQ claims.
 *)
Theorem finite_weighted_score_add :
 forall (A : Type) (xs : list A) (weight f g : A -> R),
 finite_weighted_score xs weight (fun x=>f x+g x) =
 finite_weighted_score xs weight f+finite_weighted_score xs weight g.
Proof.
 intros A xs weight f g.
 unfold finite_weighted_score.
 transitivity (finite_sum (fun x=>weight x*f x+weight x*g x) xs).
 { apply finite_sum_ext; intro x; ring. }
 apply finite_sum_add.
Qed.

(**
 [finite_weighted_score_scale] (theorem) — The finite weighted expectation respects arbitrary real scalar multiplication, including negative scalars.
 Mathematical meaning: The finite weighted expectation respects arbitrary real scalar multiplication, including negative scalars.
 Exact checked proposition: forall (A : Type) (xs : list A) (weight f : A -> R) (a : R), finite_weighted_score xs weight (fun x=>a*f x) = a*finite_weighted_score xs weight f.
 Premises and side conditions: Explicit finite outcome list, arbitrary real weights and scores; hypotheses for nonzero masses appear where needed. Probability interpretation additionally requires normalized nonnegative weights.
 Proof/definition method: Use existing finite-sum linearity, verified mean/projection lemmas, and Rocq real ring/field arithmetic with explicitly written assumptions.
 Library reuse: Stdlib.List.filter, Stdlib.Reals/Lra/Psatz/Field/Ring, FiniteSum generic identities, and existing FiniteTwoCellProjection and FiniteNestedProjection facts. No duplicate finite-list recursion.
 Boundary: Finite weighted moments and Boolean observation only; no general L1 measure-theoretic or Gaussian conditional law and no empirical IQ claims.
 *)
Theorem finite_weighted_score_scale :
 forall (A : Type) (xs : list A) (weight f : A -> R) (a : R),
 finite_weighted_score xs weight (fun x=>a*f x) =
 a*finite_weighted_score xs weight f.
Proof.
 intros A xs weight f a.
 unfold finite_weighted_score.
 transitivity (finite_sum (fun x=>a*(weight x*f x)) xs).
 { apply finite_sum_ext; intro x; ring. }
 apply finite_sum_scale.
Qed.

(**
 [finite_weighted_mean_add] (theorem) — The finite weighted mean is a linear map in its score argument when the total mass is nonzero.
 Mathematical meaning: The finite weighted mean is a linear map in its score argument when the total mass is nonzero.
 Exact checked proposition: forall (A : Type) (xs : list A) (weight f g : A -> R), finite_weight_mass xs weight <> 0 -> finite_weighted_mean xs weight (fun x=>f x+g x) = finite_weighted_mean xs weight f+finite_weighted_mean xs weight g.
 Premises and side conditions: Explicit finite outcome list, arbitrary real weights and scores; hypotheses for nonzero masses appear where needed. Probability interpretation additionally requires normalized nonnegative weights.
 Proof/definition method: Use existing finite-sum linearity, verified mean/projection lemmas, and Rocq real ring/field arithmetic with explicitly written assumptions.
 Library reuse: Stdlib.List.filter, Stdlib.Reals/Lra/Psatz/Field/Ring, FiniteSum generic identities, and existing FiniteTwoCellProjection and FiniteNestedProjection facts. No duplicate finite-list recursion.
 Boundary: Finite weighted moments and Boolean observation only; no general L1 measure-theoretic or Gaussian conditional law and no empirical IQ claims.
 *)
Theorem finite_weighted_mean_add :
 forall (A : Type) (xs : list A) (weight f g : A -> R),
 finite_weight_mass xs weight <> 0 ->
 finite_weighted_mean xs weight (fun x=>f x+g x) =
 finite_weighted_mean xs weight f+finite_weighted_mean xs weight g.
Proof.
 intros A xs weight f g Hm.
 unfold finite_weighted_mean.
 rewrite finite_weighted_score_add.
 field; exact Hm.
Qed.

(**
 [finite_weighted_mean_scale] (theorem) — The finite weighted mean commutes with arbitrary real score scaling under nonzero total mass.
 Mathematical meaning: The finite weighted mean commutes with arbitrary real score scaling under nonzero total mass.
 Exact checked proposition: forall (A : Type) (xs : list A) (weight f : A -> R) (a : R), finite_weight_mass xs weight <> 0 -> finite_weighted_mean xs weight (fun x=>a*f x) = a*finite_weighted_mean xs weight f.
 Premises and side conditions: Explicit finite outcome list, arbitrary real weights and scores; hypotheses for nonzero masses appear where needed. Probability interpretation additionally requires normalized nonnegative weights.
 Proof/definition method: Use existing finite-sum linearity, verified mean/projection lemmas, and Rocq real ring/field arithmetic with explicitly written assumptions.
 Library reuse: Stdlib.List.filter, Stdlib.Reals/Lra/Psatz/Field/Ring, FiniteSum generic identities, and existing FiniteTwoCellProjection and FiniteNestedProjection facts. No duplicate finite-list recursion.
 Boundary: Finite weighted moments and Boolean observation only; no general L1 measure-theoretic or Gaussian conditional law and no empirical IQ claims.
 *)
Theorem finite_weighted_mean_scale :
 forall (A : Type) (xs : list A) (weight f : A -> R) (a : R),
 finite_weight_mass xs weight <> 0 ->
 finite_weighted_mean xs weight (fun x=>a*f x) =
 a*finite_weighted_mean xs weight f.
Proof.
 intros A xs weight f a Hm.
 unfold finite_weighted_mean.
 rewrite finite_weighted_score_scale.
 field; exact Hm.
Qed.

(**
 [finite_weighted_mean_affine] (theorem) — The weighted mean obeys the complete affine transformation law under nonzero total mass.
 Mathematical meaning: The weighted mean obeys the complete affine transformation law under nonzero total mass.
 Exact checked proposition: forall (A : Type) (xs : list A) (weight f : A -> R) (a b : R), finite_weight_mass xs weight <> 0 -> finite_weighted_mean xs weight (fun x=>a*f x+b) = a*finite_weighted_mean xs weight f+b.
 Premises and side conditions: Explicit finite outcome list, arbitrary real weights and scores; hypotheses for nonzero masses appear where needed. Probability interpretation additionally requires normalized nonnegative weights.
 Proof/definition method: Use existing finite-sum linearity, verified mean/projection lemmas, and Rocq real ring/field arithmetic with explicitly written assumptions.
 Library reuse: Stdlib.List.filter, Stdlib.Reals/Lra/Psatz/Field/Ring, FiniteSum generic identities, and existing FiniteTwoCellProjection and FiniteNestedProjection facts. No duplicate finite-list recursion.
 Boundary: Finite weighted moments and Boolean observation only; no general L1 measure-theoretic or Gaussian conditional law and no empirical IQ claims.
 *)
Theorem finite_weighted_mean_affine :
 forall (A : Type) (xs : list A) (weight f : A -> R) (a b : R),
 finite_weight_mass xs weight <> 0 ->
 finite_weighted_mean xs weight (fun x=>a*f x+b) =
 a*finite_weighted_mean xs weight f+b.
Proof.
 intros A xs weight f a b Hm.
 unfold finite_weighted_mean.
 rewrite finite_weighted_score_affine.
 field; exact Hm.
Qed.

(**
 [finite_weighted_mean_sub] (theorem) — Weighted conditional means preserve score differences under nonzero mass.
 Mathematical meaning: Weighted conditional means preserve score differences under nonzero mass.
 Exact checked proposition: forall (A : Type) (xs : list A) (weight f g : A -> R), finite_weight_mass xs weight <> 0 -> finite_weighted_mean xs weight (fun x=>f x-g x) = finite_weighted_mean xs weight f-finite_weighted_mean xs weight g.
 Premises and side conditions: Explicit finite outcome list, arbitrary real weights and scores; hypotheses for nonzero masses appear where needed. Probability interpretation additionally requires normalized nonnegative weights.
 Proof/definition method: Use existing finite-sum linearity, verified mean/projection lemmas, and Rocq real ring/field arithmetic with explicitly written assumptions.
 Library reuse: Stdlib.List.filter, Stdlib.Reals/Lra/Psatz/Field/Ring, FiniteSum generic identities, and existing FiniteTwoCellProjection and FiniteNestedProjection facts. No duplicate finite-list recursion.
 Boundary: Finite weighted moments and Boolean observation only; no general L1 measure-theoretic or Gaussian conditional law and no empirical IQ claims.
 *)
Theorem finite_weighted_mean_sub :
 forall (A : Type) (xs : list A) (weight f g : A -> R),
 finite_weight_mass xs weight <> 0 ->
 finite_weighted_mean xs weight (fun x=>f x-g x) =
 finite_weighted_mean xs weight f-finite_weighted_mean xs weight g.
Proof.
 intros A xs weight f g Hm.
 unfold finite_weighted_mean.
 rewrite finite_weighted_score_sub.
 field; exact Hm.
Qed.

(**
 [finite_weighted_mean_constant] (theorem) — Under nonzero total mass the weighted mean of a constant score is precisely that constant.
 Mathematical meaning: Under nonzero total mass the weighted mean of a constant score is precisely that constant.
 Exact checked proposition: forall (A : Type) (xs : list A) (weight : A -> R) (a : R), finite_weight_mass xs weight <> 0 -> finite_weighted_mean xs weight (fun _=>a) = a.
 Premises and side conditions: Explicit finite outcome list, arbitrary real weights and scores; hypotheses for nonzero masses appear where needed. Probability interpretation additionally requires normalized nonnegative weights.
 Proof/definition method: Use existing finite-sum linearity, verified mean/projection lemmas, and Rocq real ring/field arithmetic with explicitly written assumptions.
 Library reuse: Stdlib.List.filter, Stdlib.Reals/Lra/Psatz/Field/Ring, FiniteSum generic identities, and existing FiniteTwoCellProjection and FiniteNestedProjection facts. No duplicate finite-list recursion.
 Boundary: Finite weighted moments and Boolean observation only; no general L1 measure-theoretic or Gaussian conditional law and no empirical IQ claims.
 *)
Theorem finite_weighted_mean_constant :
 forall (A : Type) (xs : list A) (weight : A -> R) (a : R),
 finite_weight_mass xs weight <> 0 ->
 finite_weighted_mean xs weight (fun _=>a) = a.
Proof.
 intros A xs weight a Hm.
 unfold finite_weighted_mean.
 rewrite finite_weighted_score_constant.
 field; exact Hm.
Qed.

(**
 [finite_two_cell_projection_add] (theorem) — Conditional two-cell prediction is pointwise additive for arbitrary pairs of scores.
 Mathematical meaning: Conditional two-cell prediction is pointwise additive for arbitrary pairs of scores.
 Exact checked proposition: forall (A : Type) (xs : list A) (weight f g : A -> R) (event : A -> bool) (x : A), finite_true_mass xs weight event <> 0 -> finite_false_mass xs weight event <> 0 -> finite_two_cell_prediction xs weight (fun x=>f x+g x) event x = finite_two_cell_prediction xs weight f event x + finite_two_cell_prediction xs weight g event x.
 Premises and side conditions: Explicit finite outcome list, arbitrary real weights and scores; hypotheses for nonzero masses appear where needed. Probability interpretation additionally requires normalized nonnegative weights.
 Proof/definition method: Use existing finite-sum linearity, verified mean/projection lemmas, and Rocq real ring/field arithmetic with explicitly written assumptions.
 Library reuse: Stdlib.List.filter, Stdlib.Reals/Lra/Psatz/Field/Ring, FiniteSum generic identities, and existing FiniteTwoCellProjection and FiniteNestedProjection facts. No duplicate finite-list recursion.
 Boundary: Finite weighted moments and Boolean observation only; no general L1 measure-theoretic or Gaussian conditional law and no empirical IQ claims.
 *)
Theorem finite_two_cell_projection_add :
 forall (A : Type) (xs : list A) (weight f g : A -> R)
 (event : A -> bool) (x : A),
 finite_true_mass xs weight event <> 0 ->
 finite_false_mass xs weight event <> 0 ->
 finite_two_cell_prediction xs weight (fun x=>f x+g x) event x =
 finite_two_cell_prediction xs weight f event x +
 finite_two_cell_prediction xs weight g event x.
Proof.
 intros A xs weight f g event x Ht Hf.
 unfold finite_two_cell_prediction.
 destruct (event x).
 - unfold finite_true_mean.
   apply finite_weighted_mean_add; exact Ht.
 - unfold finite_false_mean.
   apply finite_weighted_mean_add; exact Hf.
Qed.

(**
 [finite_two_cell_projection_scale] (theorem) — Conditional two-cell prediction is pointwise homogeneous for every real multiplier.
 Mathematical meaning: Conditional two-cell prediction is pointwise homogeneous for every real multiplier.
 Exact checked proposition: forall (A : Type) (xs : list A) (weight f : A -> R) (event : A -> bool) (x : A) (a : R), finite_true_mass xs weight event <> 0 -> finite_false_mass xs weight event <> 0 -> finite_two_cell_prediction xs weight (fun x=>a*f x) event x = a*finite_two_cell_prediction xs weight f event x.
 Premises and side conditions: Explicit finite outcome list, arbitrary real weights and scores; hypotheses for nonzero masses appear where needed. Probability interpretation additionally requires normalized nonnegative weights.
 Proof/definition method: Use existing finite-sum linearity, verified mean/projection lemmas, and Rocq real ring/field arithmetic with explicitly written assumptions.
 Library reuse: Stdlib.List.filter, Stdlib.Reals/Lra/Psatz/Field/Ring, FiniteSum generic identities, and existing FiniteTwoCellProjection and FiniteNestedProjection facts. No duplicate finite-list recursion.
 Boundary: Finite weighted moments and Boolean observation only; no general L1 measure-theoretic or Gaussian conditional law and no empirical IQ claims.
 *)
Theorem finite_two_cell_projection_scale :
 forall (A : Type) (xs : list A) (weight f : A -> R)
 (event : A -> bool) (x : A) (a : R),
 finite_true_mass xs weight event <> 0 ->
 finite_false_mass xs weight event <> 0 ->
 finite_two_cell_prediction xs weight (fun x=>a*f x) event x =
 a*finite_two_cell_prediction xs weight f event x.
Proof.
 intros A xs weight f event x a Ht Hf.
 unfold finite_two_cell_prediction.
 destruct (event x).
 - unfold finite_true_mean.
   apply finite_weighted_mean_scale; exact Ht.
 - unfold finite_false_mean.
   apply finite_weighted_mean_scale; exact Hf.
Qed.

(**
 [finite_two_cell_projection_affine] (theorem) — Conditional two-cell prediction commutes with all affine rescalings, including IQ-score normalization.
 Mathematical meaning: Conditional two-cell prediction commutes with all affine rescalings, including IQ-score normalization.
 Exact checked proposition: forall (A : Type) (xs : list A) (weight f : A -> R) (event : A -> bool) (x : A) (a b : R), finite_true_mass xs weight event <> 0 -> finite_false_mass xs weight event <> 0 -> finite_two_cell_prediction xs weight (fun x=>a*f x+b) event x = a*finite_two_cell_prediction xs weight f event x+b.
 Premises and side conditions: Explicit finite outcome list, arbitrary real weights and scores; hypotheses for nonzero masses appear where needed. Probability interpretation additionally requires normalized nonnegative weights.
 Proof/definition method: Use existing finite-sum linearity, verified mean/projection lemmas, and Rocq real ring/field arithmetic with explicitly written assumptions.
 Library reuse: Stdlib.List.filter, Stdlib.Reals/Lra/Psatz/Field/Ring, FiniteSum generic identities, and existing FiniteTwoCellProjection and FiniteNestedProjection facts. No duplicate finite-list recursion.
 Boundary: Finite weighted moments and Boolean observation only; no general L1 measure-theoretic or Gaussian conditional law and no empirical IQ claims.
 *)
Theorem finite_two_cell_projection_affine :
 forall (A : Type) (xs : list A) (weight f : A -> R)
 (event : A -> bool) (x : A) (a b : R),
 finite_true_mass xs weight event <> 0 ->
 finite_false_mass xs weight event <> 0 ->
 finite_two_cell_prediction xs weight (fun x=>a*f x+b) event x =
 a*finite_two_cell_prediction xs weight f event x+b.
Proof.
 intros A xs weight f event x a b Ht Hf.
 unfold finite_two_cell_prediction.
 destruct (event x).
 - unfold finite_true_mean.
   apply finite_weighted_mean_affine; exact Ht.
 - unfold finite_false_mean.
   apply finite_weighted_mean_affine; exact Hf.
Qed.

(**
 [finite_two_cell_projection_sub] (theorem) — The actual finite conditional predictor of a difference is the difference of the two conditional predictors.
 Mathematical meaning: The actual finite conditional predictor of a difference is the difference of the two conditional predictors.
 Exact checked proposition: forall (A : Type) (xs : list A) (weight f g : A -> R) (event : A -> bool) (x : A), finite_true_mass xs weight event <> 0 -> finite_false_mass xs weight event <> 0 -> finite_two_cell_prediction xs weight (fun x=>f x-g x) event x = finite_two_cell_prediction xs weight f event x - finite_two_cell_prediction xs weight g event x.
 Premises and side conditions: Explicit finite outcome list, arbitrary real weights and scores; hypotheses for nonzero masses appear where needed. Probability interpretation additionally requires normalized nonnegative weights.
 Proof/definition method: Use existing finite-sum linearity, verified mean/projection lemmas, and Rocq real ring/field arithmetic with explicitly written assumptions.
 Library reuse: Stdlib.List.filter, Stdlib.Reals/Lra/Psatz/Field/Ring, FiniteSum generic identities, and existing FiniteTwoCellProjection and FiniteNestedProjection facts. No duplicate finite-list recursion.
 Boundary: Finite weighted moments and Boolean observation only; no general L1 measure-theoretic or Gaussian conditional law and no empirical IQ claims.
 *)
Theorem finite_two_cell_projection_sub :
 forall (A : Type) (xs : list A) (weight f g : A -> R)
 (event : A -> bool) (x : A),
 finite_true_mass xs weight event <> 0 ->
 finite_false_mass xs weight event <> 0 ->
 finite_two_cell_prediction xs weight (fun x=>f x-g x) event x =
 finite_two_cell_prediction xs weight f event x -
 finite_two_cell_prediction xs weight g event x.
Proof.
 intros A xs weight f g event x Ht Hf.
 unfold finite_two_cell_prediction.
 destruct (event x).
 - unfold finite_true_mean.
   apply finite_weighted_mean_sub; exact Ht.
 - unfold finite_false_mean.
   apply finite_weighted_mean_sub; exact Hf.
Qed.

(**
 [finite_weighted_cross_symmetry] (theorem) — The literal finite weighted cross-loss is symmetric when its score and prediction arguments are exchanged.
 Mathematical meaning: The literal finite weighted cross-loss is symmetric when its score and prediction arguments are exchanged.
 Exact checked proposition: forall (A : Type) (xs : list A) (weight f g : A -> R) (a b : R), finite_weighted_cross xs weight f g a b = finite_weighted_cross xs weight g f b a.
 Premises and side conditions: Explicit finite outcome list, arbitrary real weights and scores; hypotheses for nonzero masses appear where needed. Probability interpretation additionally requires normalized nonnegative weights.
 Proof/definition method: Use existing finite-sum linearity, verified mean/projection lemmas, and Rocq real ring/field arithmetic with explicitly written assumptions.
 Library reuse: Stdlib.List.filter, Stdlib.Reals/Lra/Psatz/Field/Ring, FiniteSum generic identities, and existing FiniteTwoCellProjection and FiniteNestedProjection facts. No duplicate finite-list recursion.
 Boundary: Finite weighted moments and Boolean observation only; no general L1 measure-theoretic or Gaussian conditional law and no empirical IQ claims.
 *)
Theorem finite_weighted_cross_symmetry :
 forall (A : Type) (xs : list A) (weight f g : A -> R) (a b : R),
 finite_weighted_cross xs weight f g a b =
 finite_weighted_cross xs weight g f b a.
Proof.
 intros A xs weight f g a b.
 unfold finite_weighted_cross, finite_weighted_score.
 apply finite_sum_ext; intro x; ring.
Qed.

(**
 [finite_weighted_cross_expansion] (theorem) — Cross-loss expands exactly into the raw second moment, two weighted first moments and the total mass.
 Mathematical meaning: Cross-loss expands exactly into the raw second moment, two weighted first moments and the total mass.
 Exact checked proposition: forall (A : Type) (xs : list A) (weight f g : A -> R) (a b : R), finite_weighted_cross xs weight f g a b = finite_weighted_score xs weight (fun x=>f x*g x) - a*finite_weighted_score xs weight g - b*finite_weighted_score xs weight f + a*b*finite_weight_mass xs weight.
 Premises and side conditions: Explicit finite outcome list, arbitrary real weights and scores; hypotheses for nonzero masses appear where needed. Probability interpretation additionally requires normalized nonnegative weights.
 Proof/definition method: Use existing finite-sum linearity, verified mean/projection lemmas, and Rocq real ring/field arithmetic with explicitly written assumptions.
 Library reuse: Stdlib.List.filter, Stdlib.Reals/Lra/Psatz/Field/Ring, FiniteSum generic identities, and existing FiniteTwoCellProjection and FiniteNestedProjection facts. No duplicate finite-list recursion.
 Boundary: Finite weighted moments and Boolean observation only; no general L1 measure-theoretic or Gaussian conditional law and no empirical IQ claims.
 *)
Theorem finite_weighted_cross_expansion :
 forall (A : Type) (xs : list A) (weight f g : A -> R) (a b : R),
 finite_weighted_cross xs weight f g a b =
 finite_weighted_score xs weight (fun x=>f x*g x) -
 a*finite_weighted_score xs weight g -
 b*finite_weighted_score xs weight f +
 a*b*finite_weight_mass xs weight.
Proof.
 intros A xs weight f g a b.
 unfold finite_weighted_cross, finite_weighted_score, finite_weight_mass.
 transitivity (finite_sum (fun x=>
  weight x*(f x*g x) + (-a)*(weight x*g x) +
  (-b)*(weight x*f x) + (a*b)*weight x) xs).
 { apply finite_sum_ext; intro x; ring. }
 repeat rewrite finite_sum_add.
 repeat rewrite finite_sum_scale.
 ring.
Qed.

(**
 [finite_centered_cross_formula] (theorem) — Centered covariance admits the exact common-mean reduction of raw cross moment minus mass times mean product.
 Mathematical meaning: Centered covariance admits the exact common-mean reduction of raw cross moment minus mass times mean product.
 Exact checked proposition: forall (A : Type) (xs : list A) (weight f g : A -> R), finite_weight_mass xs weight <> 0 -> finite_centered_cross xs weight f g = finite_weighted_score xs weight (fun x=>f x*g x) - finite_weight_mass xs weight* finite_weighted_mean xs weight f*finite_weighted_mean xs weight g.
 Premises and side conditions: Explicit finite outcome list, arbitrary real weights and scores; hypotheses for nonzero masses appear where needed. Probability interpretation additionally requires normalized nonnegative weights.
 Proof/definition method: Use existing finite-sum linearity, verified mean/projection lemmas, and Rocq real ring/field arithmetic with explicitly written assumptions.
 Library reuse: Stdlib.List.filter, Stdlib.Reals/Lra/Psatz/Field/Ring, FiniteSum generic identities, and existing FiniteTwoCellProjection and FiniteNestedProjection facts. No duplicate finite-list recursion.
 Boundary: Finite weighted moments and Boolean observation only; no general L1 measure-theoretic or Gaussian conditional law and no empirical IQ claims.
 *)
Theorem finite_centered_cross_formula :
 forall (A : Type) (xs : list A) (weight f g : A -> R),
 finite_weight_mass xs weight <> 0 ->
 finite_centered_cross xs weight f g =
 finite_weighted_score xs weight (fun x=>f x*g x) -
 finite_weight_mass xs weight*
 finite_weighted_mean xs weight f*finite_weighted_mean xs weight g.
Proof.
 intros A xs weight f g Hm.
 unfold finite_centered_cross.
 rewrite finite_weighted_cross_expansion.
 pose proof (finite_weighted_mean_mass_identity A xs weight f Hm) as Hf.
 pose proof (finite_weighted_mean_mass_identity A xs weight g Hm) as Hg.
 rewrite <- Hf, <- Hg.
 ring.
Qed.

(**
 [finite_weighted_cross_completed_shift] (theorem) — Any cross-prediction loss decomposes into the centered covariance plus the product of its two prediction shifts.
 Mathematical meaning: Any cross-prediction loss decomposes into the centered covariance plus the product of its two prediction shifts.
 Exact checked proposition: forall (A : Type) (xs : list A) (weight f g : A -> R) (a b : R), finite_weight_mass xs weight <> 0 -> finite_weighted_cross xs weight f g a b = finite_centered_cross xs weight f g + finite_weight_mass xs weight* (a-finite_weighted_mean xs weight f)* (b-finite_weighted_mean xs weight g).
 Premises and side conditions: Explicit finite outcome list, arbitrary real weights and scores; hypotheses for nonzero masses appear where needed. Probability interpretation additionally requires normalized nonnegative weights.
 Proof/definition method: Use existing finite-sum linearity, verified mean/projection lemmas, and Rocq real ring/field arithmetic with explicitly written assumptions.
 Library reuse: Stdlib.List.filter, Stdlib.Reals/Lra/Psatz/Field/Ring, FiniteSum generic identities, and existing FiniteTwoCellProjection and FiniteNestedProjection facts. No duplicate finite-list recursion.
 Boundary: Finite weighted moments and Boolean observation only; no general L1 measure-theoretic or Gaussian conditional law and no empirical IQ claims.
 *)
Theorem finite_weighted_cross_completed_shift :
 forall (A : Type) (xs : list A) (weight f g : A -> R) (a b : R),
 finite_weight_mass xs weight <> 0 ->
 finite_weighted_cross xs weight f g a b =
 finite_centered_cross xs weight f g +
 finite_weight_mass xs weight*
  (a-finite_weighted_mean xs weight f)*
  (b-finite_weighted_mean xs weight g).
Proof.
 intros A xs weight f g a b Hm.
 unfold finite_centered_cross.
 rewrite !finite_weighted_cross_expansion.
 pose proof (finite_weighted_mean_mass_identity A xs weight f Hm) as Hf.
 pose proof (finite_weighted_mean_mass_identity A xs weight g Hm) as Hg.
 rewrite <- Hf, <- Hg.
 ring.
Qed.

(**
 [finite_weighted_cross_same_is_loss] (theorem) — The cross-loss of a score with itself is definitionally its actual weighted squared prediction error.
 Mathematical meaning: The cross-loss of a score with itself is definitionally its actual weighted squared prediction error.
 Exact checked proposition: forall (A : Type) (xs : list A) (weight f : A -> R) (a : R), finite_weighted_cross xs weight f f a a = finite_weighted_loss xs weight f a.
 Premises and side conditions: Explicit finite outcome list, arbitrary real weights and scores; hypotheses for nonzero masses appear where needed. Probability interpretation additionally requires normalized nonnegative weights.
 Proof/definition method: Use existing finite-sum linearity, verified mean/projection lemmas, and Rocq real ring/field arithmetic with explicitly written assumptions.
 Library reuse: Stdlib.List.filter, Stdlib.Reals/Lra/Psatz/Field/Ring, FiniteSum generic identities, and existing FiniteTwoCellProjection and FiniteNestedProjection facts. No duplicate finite-list recursion.
 Boundary: Finite weighted moments and Boolean observation only; no general L1 measure-theoretic or Gaussian conditional law and no empirical IQ claims.
 *)
Theorem finite_weighted_cross_same_is_loss :
 forall (A : Type) (xs : list A) (weight f : A -> R) (a : R),
 finite_weighted_cross xs weight f f a a =
 finite_weighted_loss xs weight f a.
Proof.
 intros A xs weight f a.
 unfold finite_weighted_cross, finite_weighted_loss, finite_weighted_score.
 apply finite_sum_ext; intro x; ring.
Qed.

(**
 [finite_centered_cross_symmetric] (theorem) — The actual finite centered covariance numerator is symmetric in its two score functions.
 Mathematical meaning: The actual finite centered covariance numerator is symmetric in its two score functions.
 Exact checked proposition: forall (A : Type) (xs : list A) (weight f g : A -> R), finite_centered_cross xs weight f g = finite_centered_cross xs weight g f.
 Premises and side conditions: Explicit finite outcome list, arbitrary real weights and scores; hypotheses for nonzero masses appear where needed. Probability interpretation additionally requires normalized nonnegative weights.
 Proof/definition method: Use existing finite-sum linearity, verified mean/projection lemmas, and Rocq real ring/field arithmetic with explicitly written assumptions.
 Library reuse: Stdlib.List.filter, Stdlib.Reals/Lra/Psatz/Field/Ring, FiniteSum generic identities, and existing FiniteTwoCellProjection and FiniteNestedProjection facts. No duplicate finite-list recursion.
 Boundary: Finite weighted moments and Boolean observation only; no general L1 measure-theoretic or Gaussian conditional law and no empirical IQ claims.
 *)
Theorem finite_centered_cross_symmetric :
 forall (A : Type) (xs : list A) (weight f g : A -> R),
 finite_centered_cross xs weight f g = finite_centered_cross xs weight g f.
Proof.
 intros A xs weight f g.
 unfold finite_centered_cross.
 apply finite_weighted_cross_symmetry.
Qed.

(**
 [finite_centered_cross_variance] (theorem) — The centered covariance of any score with itself is its actual weighted variance numerator.
 Mathematical meaning: The centered covariance of any score with itself is its actual weighted variance numerator.
 Exact checked proposition: forall (A : Type) (xs : list A) (weight f : A -> R), finite_centered_cross xs weight f f = finite_weighted_loss xs weight f (finite_weighted_mean xs weight f).
 Premises and side conditions: Explicit finite outcome list, arbitrary real weights and scores; hypotheses for nonzero masses appear where needed. Probability interpretation additionally requires normalized nonnegative weights.
 Proof/definition method: Use existing finite-sum linearity, verified mean/projection lemmas, and Rocq real ring/field arithmetic with explicitly written assumptions.
 Library reuse: Stdlib.List.filter, Stdlib.Reals/Lra/Psatz/Field/Ring, FiniteSum generic identities, and existing FiniteTwoCellProjection and FiniteNestedProjection facts. No duplicate finite-list recursion.
 Boundary: Finite weighted moments and Boolean observation only; no general L1 measure-theoretic or Gaussian conditional law and no empirical IQ claims.
 *)
Theorem finite_centered_cross_variance :
 forall (A : Type) (xs : list A) (weight f : A -> R),
 finite_centered_cross xs weight f f =
 finite_weighted_loss xs weight f (finite_weighted_mean xs weight f).
Proof.
 intros A xs weight f.
 unfold finite_centered_cross.
 apply finite_weighted_cross_same_is_loss.
Qed.

(**
 [finite_weighted_loss_polarization] (theorem) — The exact finite quadratic-loss polarization identity recovers weighted covariance without requiring positive or normalized weights.
 Mathematical meaning: The exact finite quadratic-loss polarization identity recovers weighted covariance without requiring positive or normalized weights.
 Exact checked proposition: forall (A : Type) (xs : list A) (weight f g : A -> R) (a b : R), finite_weighted_loss xs weight (fun x=>f x+g x) (a+b) = finite_weighted_loss xs weight f a + 2*finite_weighted_cross xs weight f g a b + finite_weighted_loss xs weight g b.
 Premises and side conditions: Explicit finite outcome list, arbitrary real weights and scores; hypotheses for nonzero masses appear where needed. Probability interpretation additionally requires normalized nonnegative weights.
 Proof/definition method: Use existing finite-sum linearity, verified mean/projection lemmas, and Rocq real ring/field arithmetic with explicitly written assumptions.
 Library reuse: Stdlib.List.filter, Stdlib.Reals/Lra/Psatz/Field/Ring, FiniteSum generic identities, and existing FiniteTwoCellProjection and FiniteNestedProjection facts. No duplicate finite-list recursion.
 Boundary: Finite weighted moments and Boolean observation only; no general L1 measure-theoretic or Gaussian conditional law and no empirical IQ claims.
 *)
Theorem finite_weighted_loss_polarization :
 forall (A : Type) (xs : list A) (weight f g : A -> R) (a b : R),
 finite_weighted_loss xs weight (fun x=>f x+g x) (a+b) =
 finite_weighted_loss xs weight f a +
 2*finite_weighted_cross xs weight f g a b +
 finite_weighted_loss xs weight g b.
Proof.
 intros A xs weight f g a b.
 unfold finite_weighted_loss, finite_weighted_cross, finite_weighted_score.
 rewrite <- finite_sum_scale.
 rewrite <- finite_sum_add.
 rewrite <- finite_sum_add.
 apply finite_sum_ext; intro x; ring.
Qed.

(**
 [finite_centered_cross_polarization] (theorem) — Centered finite covariance is exactly half the gain in variance of a score sum over its two component variances.
 Mathematical meaning: Centered finite covariance is exactly half the gain in variance of a score sum over its two component variances.
 Exact checked proposition: forall (A : Type) (xs : list A) (weight f g : A -> R), finite_weight_mass xs weight <> 0 -> finite_weighted_loss xs weight (fun x=>f x+g x) (finite_weighted_mean xs weight (fun x=>f x+g x)) = finite_centered_cross xs weight f f + 2*finite_centered_cross xs weight f g + finite_centered_cross xs weight g g.
 Premises and side conditions: Explicit finite outcome list, arbitrary real weights and scores; hypotheses for nonzero masses appear where needed. Probability interpretation additionally requires normalized nonnegative weights.
 Proof/definition method: Use existing finite-sum linearity, verified mean/projection lemmas, and Rocq real ring/field arithmetic with explicitly written assumptions.
 Library reuse: Stdlib.List.filter, Stdlib.Reals/Lra/Psatz/Field/Ring, FiniteSum generic identities, and existing FiniteTwoCellProjection and FiniteNestedProjection facts. No duplicate finite-list recursion.
 Boundary: Finite weighted moments and Boolean observation only; no general L1 measure-theoretic or Gaussian conditional law and no empirical IQ claims.
 *)
Theorem finite_centered_cross_polarization :
 forall (A : Type) (xs : list A) (weight f g : A -> R),
 finite_weight_mass xs weight <> 0 ->
 finite_weighted_loss xs weight (fun x=>f x+g x)
   (finite_weighted_mean xs weight (fun x=>f x+g x)) =
 finite_centered_cross xs weight f f +
 2*finite_centered_cross xs weight f g +
 finite_centered_cross xs weight g g.
Proof.
 intros A xs weight f g Hm.
 rewrite finite_weighted_mean_add by exact Hm.
 rewrite finite_weighted_loss_polarization.
 rewrite <- (finite_centered_cross_variance A xs weight f).
 rewrite <- (finite_centered_cross_variance A xs weight g).
 reflexivity.
Qed.

(**
 [finite_centered_cross_scale_first] (theorem) — Centered finite covariance is homogeneous in its first score under nonzero total mass.
 Mathematical meaning: Centered finite covariance is homogeneous in its first score under nonzero total mass.
 Exact checked proposition: forall (A : Type) (xs : list A) (weight f g : A -> R) (a : R), finite_weight_mass xs weight <> 0 -> finite_centered_cross xs weight (fun x=>a*f x) g = a*finite_centered_cross xs weight f g.
 Premises and side conditions: Explicit finite outcome list, arbitrary real weights and scores; hypotheses for nonzero masses appear where needed. Probability interpretation additionally requires normalized nonnegative weights.
 Proof/definition method: Use existing finite-sum linearity, verified mean/projection lemmas, and Rocq real ring/field arithmetic with explicitly written assumptions.
 Library reuse: Stdlib.List.filter, Stdlib.Reals/Lra/Psatz/Field/Ring, FiniteSum generic identities, and existing FiniteTwoCellProjection and FiniteNestedProjection facts. No duplicate finite-list recursion.
 Boundary: Finite weighted moments and Boolean observation only; no general L1 measure-theoretic or Gaussian conditional law and no empirical IQ claims.
 *)
Theorem finite_centered_cross_scale_first :
 forall (A : Type) (xs : list A) (weight f g : A -> R) (a : R),
 finite_weight_mass xs weight <> 0 ->
 finite_centered_cross xs weight (fun x=>a*f x) g =
 a*finite_centered_cross xs weight f g.
Proof.
 intros A xs weight f g a Hm.
 unfold finite_centered_cross.
 rewrite finite_weighted_mean_scale by exact Hm.
 unfold finite_weighted_cross, finite_weighted_score.
 transitivity (finite_sum (fun x=>
  a*(weight x*(f x-finite_weighted_mean xs weight f)*
    (g x-finite_weighted_mean xs weight g))) xs).
 { apply finite_sum_ext; intro x; ring. }
 rewrite finite_sum_scale.
 f_equal.
 apply finite_sum_ext; intro x; ring.
Qed.

(**
 [finite_centered_cross_scale_second] (theorem) — Centered finite covariance is homogeneous in its second score under nonzero total mass.
 Mathematical meaning: Centered finite covariance is homogeneous in its second score under nonzero total mass.
 Exact checked proposition: forall (A : Type) (xs : list A) (weight f g : A -> R) (a : R), finite_weight_mass xs weight <> 0 -> finite_centered_cross xs weight f (fun x=>a*g x) = a*finite_centered_cross xs weight f g.
 Premises and side conditions: Explicit finite outcome list, arbitrary real weights and scores; hypotheses for nonzero masses appear where needed. Probability interpretation additionally requires normalized nonnegative weights.
 Proof/definition method: Use existing finite-sum linearity, verified mean/projection lemmas, and Rocq real ring/field arithmetic with explicitly written assumptions.
 Library reuse: Stdlib.List.filter, Stdlib.Reals/Lra/Psatz/Field/Ring, FiniteSum generic identities, and existing FiniteTwoCellProjection and FiniteNestedProjection facts. No duplicate finite-list recursion.
 Boundary: Finite weighted moments and Boolean observation only; no general L1 measure-theoretic or Gaussian conditional law and no empirical IQ claims.
 *)
Theorem finite_centered_cross_scale_second :
 forall (A : Type) (xs : list A) (weight f g : A -> R) (a : R),
 finite_weight_mass xs weight <> 0 ->
 finite_centered_cross xs weight f (fun x=>a*g x) =
 a*finite_centered_cross xs weight f g.
Proof.
 intros A xs weight f g a Hm.
 rewrite finite_centered_cross_symmetric.
 rewrite (finite_centered_cross_scale_first A xs weight g f a Hm).
 rewrite finite_centered_cross_symmetric.
 reflexivity.
Qed.

(**
 [finite_centered_cross_add_first] (theorem) — Centered finite covariance distributes over addition in its first score.
 Mathematical meaning: Centered finite covariance distributes over addition in its first score.
 Exact checked proposition: forall (A : Type) (xs : list A) (weight f g h : A -> R), finite_weight_mass xs weight <> 0 -> finite_centered_cross xs weight (fun x=>f x+g x) h = finite_centered_cross xs weight f h+finite_centered_cross xs weight g h.
 Premises and side conditions: Explicit finite outcome list, arbitrary real weights and scores; hypotheses for nonzero masses appear where needed. Probability interpretation additionally requires normalized nonnegative weights.
 Proof/definition method: Use existing finite-sum linearity, verified mean/projection lemmas, and Rocq real ring/field arithmetic with explicitly written assumptions.
 Library reuse: Stdlib.List.filter, Stdlib.Reals/Lra/Psatz/Field/Ring, FiniteSum generic identities, and existing FiniteTwoCellProjection and FiniteNestedProjection facts. No duplicate finite-list recursion.
 Boundary: Finite weighted moments and Boolean observation only; no general L1 measure-theoretic or Gaussian conditional law and no empirical IQ claims.
 *)
Theorem finite_centered_cross_add_first :
 forall (A : Type) (xs : list A) (weight f g h : A -> R),
 finite_weight_mass xs weight <> 0 ->
 finite_centered_cross xs weight (fun x=>f x+g x) h =
 finite_centered_cross xs weight f h+finite_centered_cross xs weight g h.
Proof.
 intros A xs weight f g h Hm.
 unfold finite_centered_cross.
 rewrite finite_weighted_mean_add by exact Hm.
 unfold finite_weighted_cross, finite_weighted_score.
 transitivity (finite_sum (fun x=>
  weight x*(f x-finite_weighted_mean xs weight f)*
    (h x-finite_weighted_mean xs weight h) +
  weight x*(g x-finite_weighted_mean xs weight g)*
    (h x-finite_weighted_mean xs weight h)) xs).
 { apply finite_sum_ext; intro x; ring. }
 rewrite finite_sum_add.
 f_equal.
 - apply finite_sum_ext; intro x; ring.
 - apply finite_sum_ext; intro x; ring.
Qed.

(**
 [finite_centered_cross_add_second] (theorem) — Centered finite covariance distributes over addition in its second score.
 Mathematical meaning: Centered finite covariance distributes over addition in its second score.
 Exact checked proposition: forall (A : Type) (xs : list A) (weight f g h : A -> R), finite_weight_mass xs weight <> 0 -> finite_centered_cross xs weight f (fun x=>g x+h x) = finite_centered_cross xs weight f g+finite_centered_cross xs weight f h.
 Premises and side conditions: Explicit finite outcome list, arbitrary real weights and scores; hypotheses for nonzero masses appear where needed. Probability interpretation additionally requires normalized nonnegative weights.
 Proof/definition method: Use existing finite-sum linearity, verified mean/projection lemmas, and Rocq real ring/field arithmetic with explicitly written assumptions.
 Library reuse: Stdlib.List.filter, Stdlib.Reals/Lra/Psatz/Field/Ring, FiniteSum generic identities, and existing FiniteTwoCellProjection and FiniteNestedProjection facts. No duplicate finite-list recursion.
 Boundary: Finite weighted moments and Boolean observation only; no general L1 measure-theoretic or Gaussian conditional law and no empirical IQ claims.
 *)
Theorem finite_centered_cross_add_second :
 forall (A : Type) (xs : list A) (weight f g h : A -> R),
 finite_weight_mass xs weight <> 0 ->
 finite_centered_cross xs weight f (fun x=>g x+h x) =
 finite_centered_cross xs weight f g+finite_centered_cross xs weight f h.
Proof.
 intros A xs weight f g h Hm.
 rewrite finite_centered_cross_symmetric.
 rewrite (finite_centered_cross_add_first A xs weight g h f Hm).
 rewrite (finite_centered_cross_symmetric A xs weight g f).
 rewrite (finite_centered_cross_symmetric A xs weight h f).
 reflexivity.
Qed.

(**
 [finite_weighted_cross_filter_partition] (theorem) — Every finite weighted cross-moment splits over an event and its Boolean complement with no distribution assumptions.
 Mathematical meaning: Every finite weighted cross-moment splits over an event and its Boolean complement with no distribution assumptions.
 Exact checked proposition: forall (A : Type) (xs : list A) (weight f g : A -> R) (event : A -> bool) (a b : R), finite_weighted_cross (filter event xs) weight f g a b + finite_weighted_cross (filter (fun x=>negb(event x)) xs) weight f g a b = finite_weighted_cross xs weight f g a b.
 Premises and side conditions: Explicit finite outcome list, arbitrary real weights and scores; hypotheses for nonzero masses appear where needed. Probability interpretation additionally requires normalized nonnegative weights.
 Proof/definition method: Use existing finite-sum linearity, verified mean/projection lemmas, and Rocq real ring/field arithmetic with explicitly written assumptions.
 Library reuse: Stdlib.List.filter, Stdlib.Reals/Lra/Psatz/Field/Ring, FiniteSum generic identities, and existing FiniteTwoCellProjection and FiniteNestedProjection facts. No duplicate finite-list recursion.
 Boundary: Finite weighted moments and Boolean observation only; no general L1 measure-theoretic or Gaussian conditional law and no empirical IQ claims.
 *)
Theorem finite_weighted_cross_filter_partition :
 forall (A : Type) (xs : list A) (weight f g : A -> R)
 (event : A -> bool) (a b : R),
 finite_weighted_cross (filter event xs) weight f g a b +
 finite_weighted_cross (filter (fun x=>negb(event x)) xs) weight f g a b =
 finite_weighted_cross xs weight f g a b.
Proof.
 intros A xs weight f g event a b.
 unfold finite_weighted_cross, finite_weighted_score.
 apply finite_sum_filter_partition.
Qed.

(**
 [finite_two_cell_within_cross_symmetric] (theorem) — The total within-group centered covariance is symmetric in the two scores.
 Mathematical meaning: The total within-group centered covariance is symmetric in the two scores.
 Exact checked proposition: forall (A : Type) (xs : list A) (weight f g : A -> R) (event : A -> bool), finite_two_cell_within_cross xs weight f g event = finite_two_cell_within_cross xs weight g f event.
 Premises and side conditions: Explicit finite outcome list, arbitrary real weights and scores; hypotheses for nonzero masses appear where needed. Probability interpretation additionally requires normalized nonnegative weights.
 Proof/definition method: Use existing finite-sum linearity, verified mean/projection lemmas, and Rocq real ring/field arithmetic with explicitly written assumptions.
 Library reuse: Stdlib.List.filter, Stdlib.Reals/Lra/Psatz/Field/Ring, FiniteSum generic identities, and existing FiniteTwoCellProjection and FiniteNestedProjection facts. No duplicate finite-list recursion.
 Boundary: Finite weighted moments and Boolean observation only; no general L1 measure-theoretic or Gaussian conditional law and no empirical IQ claims.
 *)
Theorem finite_two_cell_within_cross_symmetric :
 forall (A : Type) (xs : list A) (weight f g : A -> R) (event : A -> bool),
 finite_two_cell_within_cross xs weight f g event =
 finite_two_cell_within_cross xs weight g f event.
Proof.
 intros A xs weight f g event.
 unfold finite_two_cell_within_cross.
 rewrite (finite_centered_cross_symmetric A (filter event xs) weight f g).
 rewrite (finite_centered_cross_symmetric A
   (filter (fun x=>negb(event x)) xs) weight f g).
 reflexivity.
Qed.

(**
 [finite_two_cell_between_cross_symmetric] (theorem) — The between-group covariance product of conditional-mean shifts is symmetric in its two score arguments.
 Mathematical meaning: The between-group covariance product of conditional-mean shifts is symmetric in its two score arguments.
 Exact checked proposition: forall (A : Type) (xs : list A) (weight f g : A -> R) (event : A -> bool), finite_two_cell_between_cross xs weight f g event = finite_two_cell_between_cross xs weight g f event.
 Premises and side conditions: Explicit finite outcome list, arbitrary real weights and scores; hypotheses for nonzero masses appear where needed. Probability interpretation additionally requires normalized nonnegative weights.
 Proof/definition method: Use existing finite-sum linearity, verified mean/projection lemmas, and Rocq real ring/field arithmetic with explicitly written assumptions.
 Library reuse: Stdlib.List.filter, Stdlib.Reals/Lra/Psatz/Field/Ring, FiniteSum generic identities, and existing FiniteTwoCellProjection and FiniteNestedProjection facts. No duplicate finite-list recursion.
 Boundary: Finite weighted moments and Boolean observation only; no general L1 measure-theoretic or Gaussian conditional law and no empirical IQ claims.
 *)
Theorem finite_two_cell_between_cross_symmetric :
 forall (A : Type) (xs : list A) (weight f g : A -> R) (event : A -> bool),
 finite_two_cell_between_cross xs weight f g event =
 finite_two_cell_between_cross xs weight g f event.
Proof.
 intros A xs weight f g event.
 unfold finite_two_cell_between_cross.
 ring.
Qed.

(**
 [finite_two_cell_total_covariance] (theorem) — The exact finite law of total covariance decomposes total centered covariance into within-cell cross covariance and between-cell mean-shift covariance.
 Mathematical meaning: The exact finite law of total covariance decomposes total centered covariance into within-cell cross covariance and between-cell mean-shift covariance.
 Exact checked proposition: forall (A : Type) (xs : list A) (weight f g : A -> R) (event : A -> bool), finite_true_mass xs weight event <> 0 -> finite_false_mass xs weight event <> 0 -> finite_centered_cross xs weight f g = finite_two_cell_within_cross xs weight f g event + finite_two_cell_between_cross xs weight f g event.
 Premises and side conditions: Explicit finite outcome list, arbitrary real weights and scores; hypotheses for nonzero masses appear where needed. Probability interpretation additionally requires normalized nonnegative weights.
 Proof/definition method: Use existing finite-sum linearity, verified mean/projection lemmas, and Rocq real ring/field arithmetic with explicitly written assumptions.
 Library reuse: Stdlib.List.filter, Stdlib.Reals/Lra/Psatz/Field/Ring, FiniteSum generic identities, and existing FiniteTwoCellProjection and FiniteNestedProjection facts. No duplicate finite-list recursion.
 Boundary: Finite weighted moments and Boolean observation only; no general L1 measure-theoretic or Gaussian conditional law and no empirical IQ claims.
 *)
Theorem finite_two_cell_total_covariance :
 forall (A : Type) (xs : list A) (weight f g : A -> R)
 (event : A -> bool),
 finite_true_mass xs weight event <> 0 ->
 finite_false_mass xs weight event <> 0 ->
 finite_centered_cross xs weight f g =
 finite_two_cell_within_cross xs weight f g event +
 finite_two_cell_between_cross xs weight f g event.
Proof.
 intros A xs weight f g event Ht Hf.
 unfold finite_centered_cross at 1.
 rewrite <- (finite_weighted_cross_filter_partition A xs weight f g
   event (finite_weighted_mean xs weight f)
         (finite_weighted_mean xs weight g)).
 rewrite (finite_weighted_cross_completed_shift A
   (filter event xs) weight f g
   (finite_weighted_mean xs weight f)
   (finite_weighted_mean xs weight g) Ht).
 rewrite (finite_weighted_cross_completed_shift A
   (filter (fun x=>negb(event x)) xs) weight f g
   (finite_weighted_mean xs weight f)
   (finite_weighted_mean xs weight g) Hf).
 unfold finite_two_cell_within_cross, finite_two_cell_between_cross,
   finite_true_mass, finite_false_mass, finite_true_mean, finite_false_mean.
 ring.
Qed.

(**
 [finite_two_cell_total_covariance_variance_case] (theorem) — The covariance decomposition with equal scores reduces exactly to the previously kernel-checked finite law of total variance.
 Mathematical meaning: The covariance decomposition with equal scores reduces exactly to the previously kernel-checked finite law of total variance.
 Exact checked proposition: forall (A : Type) (xs : list A) (weight f : A -> R) (event : A -> bool), finite_true_mass xs weight event <> 0 -> finite_false_mass xs weight event <> 0 -> finite_weighted_loss xs weight f (finite_weighted_mean xs weight f) = finite_two_cell_within_cross xs weight f f event + finite_two_cell_between_cross xs weight f f event.
 Premises and side conditions: Explicit finite outcome list, arbitrary real weights and scores; hypotheses for nonzero masses appear where needed. Probability interpretation additionally requires normalized nonnegative weights.
 Proof/definition method: Use existing finite-sum linearity, verified mean/projection lemmas, and Rocq real ring/field arithmetic with explicitly written assumptions.
 Library reuse: Stdlib.List.filter, Stdlib.Reals/Lra/Psatz/Field/Ring, FiniteSum generic identities, and existing FiniteTwoCellProjection and FiniteNestedProjection facts. No duplicate finite-list recursion.
 Boundary: Finite weighted moments and Boolean observation only; no general L1 measure-theoretic or Gaussian conditional law and no empirical IQ claims.
 *)
Theorem finite_two_cell_total_covariance_variance_case :
 forall (A : Type) (xs : list A) (weight f : A -> R)
 (event : A -> bool),
 finite_true_mass xs weight event <> 0 ->
 finite_false_mass xs weight event <> 0 ->
 finite_weighted_loss xs weight f (finite_weighted_mean xs weight f) =
 finite_two_cell_within_cross xs weight f f event +
 finite_two_cell_between_cross xs weight f f event.
Proof.
 intros A xs weight f event Ht Hf.
 rewrite <- (finite_centered_cross_variance A xs weight f).
 apply finite_two_cell_total_covariance; assumption.
Qed.

(**
 [finite_conditional_pullout_two_cell] (theorem) — Finite pull-out: multiplying by an arbitrary observed two-cell function does not distinguish a score from its conditional predictor.
 Mathematical meaning: Finite pull-out: multiplying by an arbitrary observed two-cell function does not distinguish a score from its conditional predictor.
 Exact checked proposition: forall (A : Type) (xs : list A) (weight f : A -> R) (event : A -> bool) (a b : R), finite_true_mass xs weight event <> 0 -> finite_false_mass xs weight event <> 0 -> finite_weighted_score xs weight (fun x => f x*(if event x then a else b)) = finite_weighted_score xs weight (fun x => finite_two_cell_prediction xs weight f event x* (if event x then a else b)).
 Premises and side conditions: Explicit finite outcome list, arbitrary real weights and scores; hypotheses for nonzero masses appear where needed. Probability interpretation additionally requires normalized nonnegative weights.
 Proof/definition method: Use existing finite-sum linearity, verified mean/projection lemmas, and Rocq real ring/field arithmetic with explicitly written assumptions.
 Library reuse: Stdlib.List.filter, Stdlib.Reals/Lra/Psatz/Field/Ring, FiniteSum generic identities, and existing FiniteTwoCellProjection and FiniteNestedProjection facts. No duplicate finite-list recursion.
 Boundary: Finite weighted moments and Boolean observation only; no general L1 measure-theoretic or Gaussian conditional law and no empirical IQ claims.
 *)
Theorem finite_conditional_pullout_two_cell :
 forall (A : Type) (xs : list A) (weight f : A -> R)
 (event : A -> bool) (a b : R),
 finite_true_mass xs weight event <> 0 ->
 finite_false_mass xs weight event <> 0 ->
 finite_weighted_score xs weight (fun x =>
    f x*(if event x then a else b)) =
 finite_weighted_score xs weight (fun x =>
    finite_two_cell_prediction xs weight f event x*
    (if event x then a else b)).
Proof.
 intros A xs weight f event a b Ht Hf.
 pose proof (finite_two_cell_residual_orthogonal A xs weight f event a b Ht Hf)
   as Horth.
 transitivity (finite_weighted_score xs weight (fun x =>
    (f x-finite_two_cell_prediction xs weight f event x)*
    (if event x then a else b)) +
    finite_weighted_score xs weight (fun x =>
    finite_two_cell_prediction xs weight f event x*
    (if event x then a else b))).
 { rewrite <- finite_weighted_score_add.
   unfold finite_weighted_score.
   apply finite_sum_ext; intro x; ring. }
 rewrite Horth; ring.
Qed.

(**
 [finite_two_cell_between_cross_variance_nonnegative] (theorem) — The between-cell covariance term for equal scores is nonnegative whenever the two sample-cell masses are nonnegative.
 Mathematical meaning: The between-cell covariance term for equal scores is nonnegative whenever the two sample-cell masses are nonnegative.
 Exact checked proposition: forall (A : Type) (xs : list A) (weight f : A -> R) (event : A -> bool), 0<=finite_true_mass xs weight event -> 0<=finite_false_mass xs weight event -> 0<=finite_two_cell_between_cross xs weight f f event.
 Premises and side conditions: Explicit finite outcome list, arbitrary real weights and scores; hypotheses for nonzero masses appear where needed. Probability interpretation additionally requires normalized nonnegative weights.
 Proof/definition method: Use existing finite-sum linearity, verified mean/projection lemmas, and Rocq real ring/field arithmetic with explicitly written assumptions.
 Library reuse: Stdlib.List.filter, Stdlib.Reals/Lra/Psatz/Field/Ring, FiniteSum generic identities, and existing FiniteTwoCellProjection and FiniteNestedProjection facts. No duplicate finite-list recursion.
 Boundary: Finite weighted moments and Boolean observation only; no general L1 measure-theoretic or Gaussian conditional law and no empirical IQ claims.
 *)
Theorem finite_two_cell_between_cross_variance_nonnegative :
 forall (A : Type) (xs : list A) (weight f : A -> R)
 (event : A -> bool),
 0<=finite_true_mass xs weight event ->
 0<=finite_false_mass xs weight event ->
 0<=finite_two_cell_between_cross xs weight f f event.
Proof.
 intros A xs weight f event Ht Hf.
 unfold finite_two_cell_between_cross.
 pose proof (weighted_squared_penalty_nonnegative
   (finite_true_mass xs weight event)
   (finite_true_mean xs weight f event-finite_weighted_mean xs weight f) Ht) as H1.
 pose proof (weighted_squared_penalty_nonnegative
   (finite_false_mass xs weight event)
   (finite_false_mean xs weight f event-finite_weighted_mean xs weight f) Hf) as H2.
 lra.
Qed.


(* D031x — general finite covariance Cauchy–Schwarz and finite-score
   linear-regression infrastructure; no new integration recursion. *)

(**
 [finite_cross_scale_first] (theorem) — Weighted cross-moments are homogeneous in their first centered score.
 Mathematical meaning: Weighted cross-moments are homogeneous in their first centered score.
 Exact checked proposition: forall (A:Type) (xs:list A) (w f g:A->R) (a b k:R), finite_weighted_cross xs w (fun x=>k*f x) g (k*a) b=k*finite_weighted_cross xs w f g a b.
 Premises and side conditions: Nonzero total mass is required only when a weighted mean is transformed.
 Proof/definition method: Reuse existing FiniteSum and FiniteTwoCellProjection weighted summation, zero-support, mean, variance and polarization lemmas; isolate the real quadratic discriminant argument and avoid further list recursions. Proofs are written in Rocq Stdlib real arithmetic without admitted steps.
 Library reuse: Stdlib.Reals, Lra, Psatz, List, Bool; existing finite_sum_ext, finite_sum_nonnegative, finite_weighted_loss_nonnegative, centered covariance linearity, and real ring/field simplification.
 Boundary: Exact finite real-weighted sample and best-linear-prediction algebra only. No Gaussian conditional distribution, continuous normal-tail theorem, empirical IQ psychometric parameter, or normality premise has been established.
 *)
Theorem finite_cross_scale_first :
 forall (A:Type) (xs:list A) (w f g:A->R) (a b k:R), finite_weighted_cross xs w (fun x=>k*f x) g (k*a) b=k*finite_weighted_cross xs w f g a b.
Proof.
 intros A xs w f g a b k; unfold finite_weighted_cross,finite_weighted_score; rewrite <- finite_sum_scale; apply finite_sum_ext; intro x; ring.
Qed.

(**
 [finite_cross_scale_second] (theorem) — Weighted cross-moments are homogeneous in their second centered score.
 Mathematical meaning: Weighted cross-moments are homogeneous in their second centered score.
 Exact checked proposition: forall (A:Type) (xs:list A) (w f g:A->R) (a b k:R), finite_weighted_cross xs w f (fun x=>k*g x) a (k*b)=k*finite_weighted_cross xs w f g a b.
 Premises and side conditions: Nonzero total mass is required only when a weighted mean is transformed.
 Proof/definition method: Reuse existing FiniteSum and FiniteTwoCellProjection weighted summation, zero-support, mean, variance and polarization lemmas; isolate the real quadratic discriminant argument and avoid further list recursions. Proofs are written in Rocq Stdlib real arithmetic without admitted steps.
 Library reuse: Stdlib.Reals, Lra, Psatz, List, Bool; existing finite_sum_ext, finite_sum_nonnegative, finite_weighted_loss_nonnegative, centered covariance linearity, and real ring/field simplification.
 Boundary: Exact finite real-weighted sample and best-linear-prediction algebra only. No Gaussian conditional distribution, continuous normal-tail theorem, empirical IQ psychometric parameter, or normality premise has been established.
 *)
Theorem finite_cross_scale_second :
 forall (A:Type) (xs:list A) (w f g:A->R) (a b k:R), finite_weighted_cross xs w f (fun x=>k*g x) a (k*b)=k*finite_weighted_cross xs w f g a b.
Proof.
 intros A xs w f g a b k; rewrite finite_weighted_cross_symmetry; rewrite (finite_cross_scale_first A xs w g f b a k); rewrite finite_weighted_cross_symmetry; reflexivity.
Qed.

(**
 [finite_cross_shift_first] (theorem) — Matched translation of a first score and its reference leaves cross-moments unchanged.
 Mathematical meaning: Matched translation of a first score and its reference leaves cross-moments unchanged.
 Exact checked proposition: forall (A:Type) (xs:list A) (w f g:A->R) (a b d:R), finite_weighted_cross xs w (fun x=>f x+d) g (a+d) b=finite_weighted_cross xs w f g a b.
 Premises and side conditions: Nonzero total mass is required only when a weighted mean is transformed.
 Proof/definition method: Reuse existing FiniteSum and FiniteTwoCellProjection weighted summation, zero-support, mean, variance and polarization lemmas; isolate the real quadratic discriminant argument and avoid further list recursions. Proofs are written in Rocq Stdlib real arithmetic without admitted steps.
 Library reuse: Stdlib.Reals, Lra, Psatz, List, Bool; existing finite_sum_ext, finite_sum_nonnegative, finite_weighted_loss_nonnegative, centered covariance linearity, and real ring/field simplification.
 Boundary: Exact finite real-weighted sample and best-linear-prediction algebra only. No Gaussian conditional distribution, continuous normal-tail theorem, empirical IQ psychometric parameter, or normality premise has been established.
 *)
Theorem finite_cross_shift_first :
 forall (A:Type) (xs:list A) (w f g:A->R) (a b d:R), finite_weighted_cross xs w (fun x=>f x+d) g (a+d) b=finite_weighted_cross xs w f g a b.
Proof.
 intros A xs w f g a b d; unfold finite_weighted_cross,finite_weighted_score; apply finite_sum_ext; intro x; ring.
Qed.

(**
 [finite_cross_shift_second] (theorem) — Matched translation of a second score and its reference leaves cross-moments unchanged.
 Mathematical meaning: Matched translation of a second score and its reference leaves cross-moments unchanged.
 Exact checked proposition: forall (A:Type) (xs:list A) (w f g:A->R) (a b d:R), finite_weighted_cross xs w f (fun x=>g x+d) a (b+d)=finite_weighted_cross xs w f g a b.
 Premises and side conditions: Nonzero total mass is required only when a weighted mean is transformed.
 Proof/definition method: Reuse existing FiniteSum and FiniteTwoCellProjection weighted summation, zero-support, mean, variance and polarization lemmas; isolate the real quadratic discriminant argument and avoid further list recursions. Proofs are written in Rocq Stdlib real arithmetic without admitted steps.
 Library reuse: Stdlib.Reals, Lra, Psatz, List, Bool; existing finite_sum_ext, finite_sum_nonnegative, finite_weighted_loss_nonnegative, centered covariance linearity, and real ring/field simplification.
 Boundary: Exact finite real-weighted sample and best-linear-prediction algebra only. No Gaussian conditional distribution, continuous normal-tail theorem, empirical IQ psychometric parameter, or normality premise has been established.
 *)
Theorem finite_cross_shift_second :
 forall (A:Type) (xs:list A) (w f g:A->R) (a b d:R), finite_weighted_cross xs w f (fun x=>g x+d) a (b+d)=finite_weighted_cross xs w f g a b.
Proof.
 intros A xs w f g a b d; rewrite finite_weighted_cross_symmetry; rewrite finite_cross_shift_first; rewrite finite_weighted_cross_symmetry; reflexivity.
Qed.

(**
 [finite_cross_add_first] (theorem) — First-coordinate cross-moment additivity permits decomposition of composite test scores.
 Mathematical meaning: First-coordinate cross-moment additivity permits decomposition of composite test scores.
 Exact checked proposition: forall (A:Type) (xs:list A) (w f g h:A->R) (a b c:R), finite_weighted_cross xs w (fun x=>f x+g x) h (a+b) c=finite_weighted_cross xs w f h a c+finite_weighted_cross xs w g h b c.
 Premises and side conditions: Nonzero total mass is required only when a weighted mean is transformed.
 Proof/definition method: Reuse existing FiniteSum and FiniteTwoCellProjection weighted summation, zero-support, mean, variance and polarization lemmas; isolate the real quadratic discriminant argument and avoid further list recursions. Proofs are written in Rocq Stdlib real arithmetic without admitted steps.
 Library reuse: Stdlib.Reals, Lra, Psatz, List, Bool; existing finite_sum_ext, finite_sum_nonnegative, finite_weighted_loss_nonnegative, centered covariance linearity, and real ring/field simplification.
 Boundary: Exact finite real-weighted sample and best-linear-prediction algebra only. No Gaussian conditional distribution, continuous normal-tail theorem, empirical IQ psychometric parameter, or normality premise has been established.
 *)
Theorem finite_cross_add_first :
 forall (A:Type) (xs:list A) (w f g h:A->R) (a b c:R), finite_weighted_cross xs w (fun x=>f x+g x) h (a+b) c=finite_weighted_cross xs w f h a c+finite_weighted_cross xs w g h b c.
Proof.
 intros A xs w f g h a b c; unfold finite_weighted_cross; rewrite <- finite_weighted_score_add; unfold finite_weighted_score; apply finite_sum_ext; intro x; ring.
Qed.

(**
 [finite_cross_add_second] (theorem) — Second-coordinate cross-moment additivity permits decomposition of composite test scores.
 Mathematical meaning: Second-coordinate cross-moment additivity permits decomposition of composite test scores.
 Exact checked proposition: forall (A:Type) (xs:list A) (w f g h:A->R) (a b c:R), finite_weighted_cross xs w f (fun x=>g x+h x) a (b+c)=finite_weighted_cross xs w f g a b+finite_weighted_cross xs w f h a c.
 Premises and side conditions: Nonzero total mass is required only when a weighted mean is transformed.
 Proof/definition method: Reuse existing FiniteSum and FiniteTwoCellProjection weighted summation, zero-support, mean, variance and polarization lemmas; isolate the real quadratic discriminant argument and avoid further list recursions. Proofs are written in Rocq Stdlib real arithmetic without admitted steps.
 Library reuse: Stdlib.Reals, Lra, Psatz, List, Bool; existing finite_sum_ext, finite_sum_nonnegative, finite_weighted_loss_nonnegative, centered covariance linearity, and real ring/field simplification.
 Boundary: Exact finite real-weighted sample and best-linear-prediction algebra only. No Gaussian conditional distribution, continuous normal-tail theorem, empirical IQ psychometric parameter, or normality premise has been established.
 *)
Theorem finite_cross_add_second :
 forall (A:Type) (xs:list A) (w f g h:A->R) (a b c:R), finite_weighted_cross xs w f (fun x=>g x+h x) a (b+c)=finite_weighted_cross xs w f g a b+finite_weighted_cross xs w f h a c.
Proof.
 intros A xs w f g h a b c; rewrite finite_weighted_cross_symmetry; rewrite (finite_cross_add_first A xs w g h f b c a); rewrite (finite_weighted_cross_symmetry A xs w g f b a); rewrite (finite_weighted_cross_symmetry A xs w h f c a); reflexivity.
Qed.

(**
 [finite_cross_sub_first] (theorem) — Weighted cross-moments split over first-score differences, preserving reference differences.
 Mathematical meaning: Weighted cross-moments split over first-score differences, preserving reference differences.
 Exact checked proposition: forall (A:Type) (xs:list A) (w f g h:A->R) (a b c:R), finite_weighted_cross xs w (fun x=>f x-g x) h (a-b) c=finite_weighted_cross xs w f h a c-finite_weighted_cross xs w g h b c.
 Premises and side conditions: Nonzero total mass is required only when a weighted mean is transformed.
 Proof/definition method: Reuse existing FiniteSum and FiniteTwoCellProjection weighted summation, zero-support, mean, variance and polarization lemmas; isolate the real quadratic discriminant argument and avoid further list recursions. Proofs are written in Rocq Stdlib real arithmetic without admitted steps.
 Library reuse: Stdlib.Reals, Lra, Psatz, List, Bool; existing finite_sum_ext, finite_sum_nonnegative, finite_weighted_loss_nonnegative, centered covariance linearity, and real ring/field simplification.
 Boundary: Exact finite real-weighted sample and best-linear-prediction algebra only. No Gaussian conditional distribution, continuous normal-tail theorem, empirical IQ psychometric parameter, or normality premise has been established.
 *)
Theorem finite_cross_sub_first :
 forall (A:Type) (xs:list A) (w f g h:A->R) (a b c:R), finite_weighted_cross xs w (fun x=>f x-g x) h (a-b) c=finite_weighted_cross xs w f h a c-finite_weighted_cross xs w g h b c.
Proof.
 intros A xs w f g h a b c; unfold finite_weighted_cross; rewrite <- finite_weighted_score_sub; unfold finite_weighted_score; apply finite_sum_ext; intro x; ring.
Qed.

(**
 [finite_cross_sub_second] (theorem) — Weighted cross-moments split over second-score differences, preserving reference differences.
 Mathematical meaning: Weighted cross-moments split over second-score differences, preserving reference differences.
 Exact checked proposition: forall (A:Type) (xs:list A) (w f g h:A->R) (a b c:R), finite_weighted_cross xs w f (fun x=>g x-h x) a (b-c)=finite_weighted_cross xs w f g a b-finite_weighted_cross xs w f h a c.
 Premises and side conditions: Nonzero total mass is required only when a weighted mean is transformed.
 Proof/definition method: Reuse existing FiniteSum and FiniteTwoCellProjection weighted summation, zero-support, mean, variance and polarization lemmas; isolate the real quadratic discriminant argument and avoid further list recursions. Proofs are written in Rocq Stdlib real arithmetic without admitted steps.
 Library reuse: Stdlib.Reals, Lra, Psatz, List, Bool; existing finite_sum_ext, finite_sum_nonnegative, finite_weighted_loss_nonnegative, centered covariance linearity, and real ring/field simplification.
 Boundary: Exact finite real-weighted sample and best-linear-prediction algebra only. No Gaussian conditional distribution, continuous normal-tail theorem, empirical IQ psychometric parameter, or normality premise has been established.
 *)
Theorem finite_cross_sub_second :
 forall (A:Type) (xs:list A) (w f g h:A->R) (a b c:R), finite_weighted_cross xs w f (fun x=>g x-h x) a (b-c)=finite_weighted_cross xs w f g a b-finite_weighted_cross xs w f h a c.
Proof.
 intros A xs w f g h a b c; rewrite finite_weighted_cross_symmetry; rewrite (finite_cross_sub_first A xs w g h f b c a); rewrite (finite_weighted_cross_symmetry A xs w g f b a); rewrite (finite_weighted_cross_symmetry A xs w h f c a); reflexivity.
Qed.

(**
 [finite_loss_scale] (theorem) — Quadratic weighted prediction loss has degree-two homogeneity in score and reference.
 Mathematical meaning: Quadratic weighted prediction loss has degree-two homogeneity in score and reference.
 Exact checked proposition: forall (A:Type) (xs:list A) (w f:A->R) (a k:R), finite_weighted_loss xs w (fun x=>k*f x) (k*a)=k*k*finite_weighted_loss xs w f a.
 Premises and side conditions: Nonzero total mass is required only when a weighted mean is transformed.
 Proof/definition method: Reuse existing FiniteSum and FiniteTwoCellProjection weighted summation, zero-support, mean, variance and polarization lemmas; isolate the real quadratic discriminant argument and avoid further list recursions. Proofs are written in Rocq Stdlib real arithmetic without admitted steps.
 Library reuse: Stdlib.Reals, Lra, Psatz, List, Bool; existing finite_sum_ext, finite_sum_nonnegative, finite_weighted_loss_nonnegative, centered covariance linearity, and real ring/field simplification.
 Boundary: Exact finite real-weighted sample and best-linear-prediction algebra only. No Gaussian conditional distribution, continuous normal-tail theorem, empirical IQ psychometric parameter, or normality premise has been established.
 *)
Theorem finite_loss_scale :
 forall (A:Type) (xs:list A) (w f:A->R) (a k:R), finite_weighted_loss xs w (fun x=>k*f x) (k*a)=k*k*finite_weighted_loss xs w f a.
Proof.
 intros A xs w f a k; unfold finite_weighted_loss; rewrite <- finite_sum_scale; apply finite_sum_ext; intro x; ring.
Qed.

(**
 [finite_loss_cross_scaled_polarization] (theorem) — The exact quadratic expansion of scaled composite-score loss separates individual losses and covariance.
 Mathematical meaning: The exact quadratic expansion of scaled composite-score loss separates individual losses and covariance.
 Exact checked proposition: forall (A:Type) (xs:list A) (w f g:A->R) (a b t:R), finite_weighted_loss xs w (fun x=>f x+t*g x) (a+t*b)=finite_weighted_loss xs w f a+2*t*finite_weighted_cross xs w f g a b+t*t*finite_weighted_loss xs w g b.
 Premises and side conditions: Nonzero total mass is required only when a weighted mean is transformed.
 Proof/definition method: Reuse existing FiniteSum and FiniteTwoCellProjection weighted summation, zero-support, mean, variance and polarization lemmas; isolate the real quadratic discriminant argument and avoid further list recursions. Proofs are written in Rocq Stdlib real arithmetic without admitted steps.
 Library reuse: Stdlib.Reals, Lra, Psatz, List, Bool; existing finite_sum_ext, finite_sum_nonnegative, finite_weighted_loss_nonnegative, centered covariance linearity, and real ring/field simplification.
 Boundary: Exact finite real-weighted sample and best-linear-prediction algebra only. No Gaussian conditional distribution, continuous normal-tail theorem, empirical IQ psychometric parameter, or normality premise has been established.
 *)
Theorem finite_loss_cross_scaled_polarization :
 forall (A:Type) (xs:list A) (w f g:A->R) (a b t:R), finite_weighted_loss xs w (fun x=>f x+t*g x) (a+t*b)=finite_weighted_loss xs w f a+2*t*finite_weighted_cross xs w f g a b+t*t*finite_weighted_loss xs w g b.
Proof.
 intros A xs w f g a b t; rewrite finite_weighted_loss_polarization; rewrite (finite_cross_scale_second A xs w f g a b t); rewrite (finite_loss_scale A xs w g b t); ring.
Qed.

(**
 [finite_cross_quadratic_psd] (theorem) — Nonnegative sample weights make every centered linear-combination loss nonnegative.
 Mathematical meaning: Nonnegative sample weights make every centered linear-combination loss nonnegative.
 Exact checked proposition: forall (A:Type) (xs:list A) (w f g:A->R) (a b t:R), (forall x, In x xs -> 0<=w x) -> 0<=finite_weighted_loss xs w f a+2*t*finite_weighted_cross xs w f g a b+t*t*finite_weighted_loss xs w g b.
 Premises and side conditions: Every outcome weight is nonnegative, with no normalization assumption.
 Proof/definition method: Reuse existing FiniteSum and FiniteTwoCellProjection weighted summation, zero-support, mean, variance and polarization lemmas; isolate the real quadratic discriminant argument and avoid further list recursions. Proofs are written in Rocq Stdlib real arithmetic without admitted steps.
 Library reuse: Stdlib.Reals, Lra, Psatz, List, Bool; existing finite_sum_ext, finite_sum_nonnegative, finite_weighted_loss_nonnegative, centered covariance linearity, and real ring/field simplification.
 Boundary: Exact finite real-weighted sample and best-linear-prediction algebra only. No Gaussian conditional distribution, continuous normal-tail theorem, empirical IQ psychometric parameter, or normality premise has been established.
 *)
Theorem finite_cross_quadratic_psd :
 forall (A:Type) (xs:list A) (w f g:A->R) (a b t:R), (forall x, In x xs -> 0<=w x) -> 0<=finite_weighted_loss xs w f a+2*t*finite_weighted_cross xs w f g a b+t*t*finite_weighted_loss xs w g b.
Proof.
 intros A xs w f g a b t Hw; rewrite <- finite_loss_cross_scaled_polarization; apply finite_weighted_loss_nonnegative; exact Hw.
Qed.

(**
 [real_quadratic_psd_discriminant] (theorem) — A globally nonnegative quadratic must have nonpositive discriminant, yielding the real Gram determinant inequality.
 Mathematical meaning: A globally nonnegative quadratic must have nonpositive discriminant, yielding the real Gram determinant inequality.
 Exact checked proposition: forall a b c:R, 0<=b -> (forall t:R, 0<=a+2*t*c+t*t*b) -> c*c<=a*b.
 Premises and side conditions: Requires nonnegative quadratic leading coefficient and nonnegativity for every scalar.
 Proof/definition method: Reuse existing FiniteSum and FiniteTwoCellProjection weighted summation, zero-support, mean, variance and polarization lemmas; isolate the real quadratic discriminant argument and avoid further list recursions. Proofs are written in Rocq Stdlib real arithmetic without admitted steps.
 Library reuse: Stdlib.Reals, Lra, Psatz, List, Bool; existing finite_sum_ext, finite_sum_nonnegative, finite_weighted_loss_nonnegative, centered covariance linearity, and real ring/field simplification.
 Boundary: Exact finite real-weighted sample and best-linear-prediction algebra only. No Gaussian conditional distribution, continuous normal-tail theorem, empirical IQ psychometric parameter, or normality premise has been established.
 *)
Theorem real_quadratic_psd_discriminant :
 forall a b c:R, 0<=b -> (forall t:R, 0<=a+2*t*c+t*t*b) -> c*c<=a*b.
Proof.
 intros a b c Hb Hq; destruct (Req_EM_T b 0) as [Hz|Hz].
 - subst b; destruct (Req_EM_T c 0) as [Hc|Hc].
   + subst c; nra.
   + specialize (Hq (-(a+1)/(2*c))).
     assert (Heq:a+2*(-(a+1)/(2*c))*c+(-(a+1)/(2*c))*(-(a+1)/(2*c))*0=-1) by (field; nra).
     rewrite Heq in Hq; lra.
 - assert (Hbpos:0<b) by lra.
   specialize (Hq (-c/b)).
   assert (Heq:a+2*(-c/b)*c+(-c/b)*(-c/b)*b=(a*b-c*c)/b) by (field; lra).
   rewrite Heq in Hq; unfold Rdiv in Hq.
   assert (Hi:0< /b) by (apply Rinv_0_lt_compat; exact Hbpos).
   nra.
Qed.

(**
 [finite_cross_cauchy_schwarz] (theorem) — The finite weighted Cauchy–Schwarz inequality holds for arbitrarily centered scores with nonnegative weights.
 Mathematical meaning: The finite weighted Cauchy–Schwarz inequality holds for arbitrarily centered scores with nonnegative weights.
 Exact checked proposition: forall (A:Type) (xs:list A) (w f g:A->R) (a b:R), (forall x, In x xs -> 0<=w x) -> finite_weighted_cross xs w f g a b*finite_weighted_cross xs w f g a b<=finite_weighted_loss xs w f a*finite_weighted_loss xs w g b.
 Premises and side conditions: Requires nonnegative weight at each enumerated sample.
 Proof/definition method: Reuse existing FiniteSum and FiniteTwoCellProjection weighted summation, zero-support, mean, variance and polarization lemmas; isolate the real quadratic discriminant argument and avoid further list recursions. Proofs are written in Rocq Stdlib real arithmetic without admitted steps.
 Library reuse: Stdlib.Reals, Lra, Psatz, List, Bool; existing finite_sum_ext, finite_sum_nonnegative, finite_weighted_loss_nonnegative, centered covariance linearity, and real ring/field simplification.
 Boundary: Exact finite real-weighted sample and best-linear-prediction algebra only. No Gaussian conditional distribution, continuous normal-tail theorem, empirical IQ psychometric parameter, or normality premise has been established.
 *)
Theorem finite_cross_cauchy_schwarz :
 forall (A:Type) (xs:list A) (w f g:A->R) (a b:R), (forall x, In x xs -> 0<=w x) -> finite_weighted_cross xs w f g a b*finite_weighted_cross xs w f g a b<=finite_weighted_loss xs w f a*finite_weighted_loss xs w g b.
Proof.
 intros A xs w f g a b Hw; apply real_quadratic_psd_discriminant.
 - apply finite_weighted_loss_nonnegative; exact Hw.
 - intro t; apply finite_cross_quadratic_psd; exact Hw.
Qed.

(**
 [finite_centered_variance_nonnegative] (theorem) — Every centered finite variance is nonnegative under nonnegative sample weights.
 Mathematical meaning: Every centered finite variance is nonnegative under nonnegative sample weights.
 Exact checked proposition: forall (A:Type) (xs:list A) (w f:A->R), (forall x, In x xs -> 0<=w x) -> 0<=finite_centered_cross xs w f f.
 Premises and side conditions: Nonnegative finite weights.
 Proof/definition method: Reuse existing FiniteSum and FiniteTwoCellProjection weighted summation, zero-support, mean, variance and polarization lemmas; isolate the real quadratic discriminant argument and avoid further list recursions. Proofs are written in Rocq Stdlib real arithmetic without admitted steps.
 Library reuse: Stdlib.Reals, Lra, Psatz, List, Bool; existing finite_sum_ext, finite_sum_nonnegative, finite_weighted_loss_nonnegative, centered covariance linearity, and real ring/field simplification.
 Boundary: Exact finite real-weighted sample and best-linear-prediction algebra only. No Gaussian conditional distribution, continuous normal-tail theorem, empirical IQ psychometric parameter, or normality premise has been established.
 *)
Theorem finite_centered_variance_nonnegative :
 forall (A:Type) (xs:list A) (w f:A->R), (forall x, In x xs -> 0<=w x) -> 0<=finite_centered_cross xs w f f.
Proof.
 intros A xs w f Hw; rewrite finite_centered_cross_variance; apply finite_weighted_loss_nonnegative; exact Hw.
Qed.

(**
 [finite_centered_variance_zero_iff_supported_constant] (theorem) — Zero centered variance occurs exactly when the score is constant at its weighted mean on positive-weight outcomes.
 Mathematical meaning: Zero centered variance occurs exactly when the score is constant at its weighted mean on positive-weight outcomes.
 Exact checked proposition: forall (A:Type) (xs:list A) (w f:A->R), (forall x, In x xs -> 0<=w x) -> (finite_centered_cross xs w f f=0 <-> forall x, In x xs -> 0<w x -> f x=finite_weighted_mean xs w f).
 Premises and side conditions: Nonnegative weight throughout the enumerated sample.
 Proof/definition method: Reuse existing FiniteSum and FiniteTwoCellProjection weighted summation, zero-support, mean, variance and polarization lemmas; isolate the real quadratic discriminant argument and avoid further list recursions. Proofs are written in Rocq Stdlib real arithmetic without admitted steps.
 Library reuse: Stdlib.Reals, Lra, Psatz, List, Bool; existing finite_sum_ext, finite_sum_nonnegative, finite_weighted_loss_nonnegative, centered covariance linearity, and real ring/field simplification.
 Boundary: Exact finite real-weighted sample and best-linear-prediction algebra only. No Gaussian conditional distribution, continuous normal-tail theorem, empirical IQ psychometric parameter, or normality premise has been established.
 *)
Theorem finite_centered_variance_zero_iff_supported_constant :
 forall (A:Type) (xs:list A) (w f:A->R), (forall x, In x xs -> 0<=w x) -> (finite_centered_cross xs w f f=0 <-> forall x, In x xs -> 0<w x -> f x=finite_weighted_mean xs w f).
Proof.
 intros A xs w f Hw; rewrite finite_centered_cross_variance; apply finite_weighted_loss_zero_iff_supported_constant; exact Hw.
Qed.

(**
 [finite_centered_cauchy_schwarz] (theorem) — Centered finite sample covariance obeys Cauchy–Schwarz, establishing positive semidefiniteness of its Gram matrix.
 Mathematical meaning: Centered finite sample covariance obeys Cauchy–Schwarz, establishing positive semidefiniteness of its Gram matrix.
 Exact checked proposition: forall (A:Type) (xs:list A) (w f g:A->R), (forall x, In x xs -> 0<=w x) -> finite_centered_cross xs w f g*finite_centered_cross xs w f g<=finite_centered_cross xs w f f*finite_centered_cross xs w g g.
 Premises and side conditions: Nonnegative sample weights, without Gaussian assumptions.
 Proof/definition method: Reuse existing FiniteSum and FiniteTwoCellProjection weighted summation, zero-support, mean, variance and polarization lemmas; isolate the real quadratic discriminant argument and avoid further list recursions. Proofs are written in Rocq Stdlib real arithmetic without admitted steps.
 Library reuse: Stdlib.Reals, Lra, Psatz, List, Bool; existing finite_sum_ext, finite_sum_nonnegative, finite_weighted_loss_nonnegative, centered covariance linearity, and real ring/field simplification.
 Boundary: Exact finite real-weighted sample and best-linear-prediction algebra only. No Gaussian conditional distribution, continuous normal-tail theorem, empirical IQ psychometric parameter, or normality premise has been established.
 *)
Theorem finite_centered_cauchy_schwarz :
 forall (A:Type) (xs:list A) (w f g:A->R), (forall x, In x xs -> 0<=w x) -> finite_centered_cross xs w f g*finite_centered_cross xs w f g<=finite_centered_cross xs w f f*finite_centered_cross xs w g g.
Proof.
 intros A xs w f g Hw.
 unfold finite_centered_cross.
 rewrite (finite_weighted_cross_same_is_loss A xs w f
   (finite_weighted_mean xs w f)).
 rewrite (finite_weighted_cross_same_is_loss A xs w g
   (finite_weighted_mean xs w g)).
 apply finite_cross_cauchy_schwarz; exact Hw.
Qed.

(**
 [finite_centered_cov_zero_if_first_supported_constant] (theorem) — Any supportwise constant score has zero covariance with every finite score.
 Mathematical meaning: Any supportwise constant score has zero covariance with every finite score.
 Exact checked proposition: forall (A:Type) (xs:list A) (w f g:A->R), (forall x, In x xs -> 0<=w x) -> (forall x, In x xs -> 0<w x -> f x=finite_weighted_mean xs w f) -> finite_centered_cross xs w f g=0.
 Premises and side conditions: Nonnegative sample weights and constancy on their positive support.
 Proof/definition method: Reuse existing FiniteSum and FiniteTwoCellProjection weighted summation, zero-support, mean, variance and polarization lemmas; isolate the real quadratic discriminant argument and avoid further list recursions. Proofs are written in Rocq Stdlib real arithmetic without admitted steps.
 Library reuse: Stdlib.Reals, Lra, Psatz, List, Bool; existing finite_sum_ext, finite_sum_nonnegative, finite_weighted_loss_nonnegative, centered covariance linearity, and real ring/field simplification.
 Boundary: Exact finite real-weighted sample and best-linear-prediction algebra only. No Gaussian conditional distribution, continuous normal-tail theorem, empirical IQ psychometric parameter, or normality premise has been established.
 *)
Theorem finite_centered_cov_zero_if_first_supported_constant :
 forall (A:Type) (xs:list A) (w f g:A->R), (forall x, In x xs -> 0<=w x) -> (forall x, In x xs -> 0<w x -> f x=finite_weighted_mean xs w f) -> finite_centered_cross xs w f g=0.
Proof.
 intros A xs w f g Hw Hconst; pose proof ((proj2 (finite_centered_variance_zero_iff_supported_constant A xs w f Hw)) Hconst) as Hz; pose proof (finite_centered_cauchy_schwarz A xs w f g Hw) as Hcs; rewrite Hz in Hcs; nra.
Qed.

(**
 [finite_centered_cov_zero_if_second_supported_constant] (theorem) — Supportwise constancy of the second score forces zero covariance with every first score.
 Mathematical meaning: Supportwise constancy of the second score forces zero covariance with every first score.
 Exact checked proposition: forall (A:Type) (xs:list A) (w f g:A->R), (forall x, In x xs -> 0<=w x) -> (forall x, In x xs -> 0<w x -> g x=finite_weighted_mean xs w g) -> finite_centered_cross xs w f g=0.
 Premises and side conditions: Nonnegative sample weights and constancy on their positive support.
 Proof/definition method: Reuse existing FiniteSum and FiniteTwoCellProjection weighted summation, zero-support, mean, variance and polarization lemmas; isolate the real quadratic discriminant argument and avoid further list recursions. Proofs are written in Rocq Stdlib real arithmetic without admitted steps.
 Library reuse: Stdlib.Reals, Lra, Psatz, List, Bool; existing finite_sum_ext, finite_sum_nonnegative, finite_weighted_loss_nonnegative, centered covariance linearity, and real ring/field simplification.
 Boundary: Exact finite real-weighted sample and best-linear-prediction algebra only. No Gaussian conditional distribution, continuous normal-tail theorem, empirical IQ psychometric parameter, or normality premise has been established.
 *)
Theorem finite_centered_cov_zero_if_second_supported_constant :
 forall (A:Type) (xs:list A) (w f g:A->R), (forall x, In x xs -> 0<=w x) -> (forall x, In x xs -> 0<w x -> g x=finite_weighted_mean xs w g) -> finite_centered_cross xs w f g=0.
Proof.
 intros A xs w f g Hw Hg; rewrite finite_centered_cross_symmetric; apply finite_centered_cov_zero_if_first_supported_constant; assumption.
Qed.

(**
 [finite_centered_shift_first] (theorem) — Finite centered covariance is invariant under translating the first score.
 Mathematical meaning: Finite centered covariance is invariant under translating the first score.
 Exact checked proposition: forall (A:Type) (xs:list A) (w f g:A->R) (d:R), finite_weight_mass xs w<>0 -> finite_centered_cross xs w (fun x=>f x+d) g=finite_centered_cross xs w f g.
 Premises and side conditions: Nonzero total mass is required only when a weighted mean is transformed.
 Proof/definition method: Reuse existing FiniteSum and FiniteTwoCellProjection weighted summation, zero-support, mean, variance and polarization lemmas; isolate the real quadratic discriminant argument and avoid further list recursions. Proofs are written in Rocq Stdlib real arithmetic without admitted steps.
 Library reuse: Stdlib.Reals, Lra, Psatz, List, Bool; existing finite_sum_ext, finite_sum_nonnegative, finite_weighted_loss_nonnegative, centered covariance linearity, and real ring/field simplification.
 Boundary: Exact finite real-weighted sample and best-linear-prediction algebra only. No Gaussian conditional distribution, continuous normal-tail theorem, empirical IQ psychometric parameter, or normality premise has been established.
 *)
Theorem finite_centered_shift_first :
 forall (A:Type) (xs:list A) (w f g:A->R) (d:R), finite_weight_mass xs w<>0 -> finite_centered_cross xs w (fun x=>f x+d) g=finite_centered_cross xs w f g.
Proof.
 intros A xs w f g d Hm; unfold finite_centered_cross; replace (finite_weighted_mean xs w (fun x=>f x+d)) with (finite_weighted_mean xs w f+d).
 - apply finite_cross_shift_first.
 - rewrite (finite_weighted_mean_add A xs w f (fun _=>d) Hm).
   rewrite (finite_weighted_mean_constant A xs w d Hm).
   reflexivity.
Qed.

(**
 [finite_centered_shift_second] (theorem) — Finite centered covariance is invariant under translating the second score.
 Mathematical meaning: Finite centered covariance is invariant under translating the second score.
 Exact checked proposition: forall (A:Type) (xs:list A) (w f g:A->R) (d:R), finite_weight_mass xs w<>0 -> finite_centered_cross xs w f (fun x=>g x+d)=finite_centered_cross xs w f g.
 Premises and side conditions: Nonzero total mass is required only when a weighted mean is transformed.
 Proof/definition method: Reuse existing FiniteSum and FiniteTwoCellProjection weighted summation, zero-support, mean, variance and polarization lemmas; isolate the real quadratic discriminant argument and avoid further list recursions. Proofs are written in Rocq Stdlib real arithmetic without admitted steps.
 Library reuse: Stdlib.Reals, Lra, Psatz, List, Bool; existing finite_sum_ext, finite_sum_nonnegative, finite_weighted_loss_nonnegative, centered covariance linearity, and real ring/field simplification.
 Boundary: Exact finite real-weighted sample and best-linear-prediction algebra only. No Gaussian conditional distribution, continuous normal-tail theorem, empirical IQ psychometric parameter, or normality premise has been established.
 *)
Theorem finite_centered_shift_second :
 forall (A:Type) (xs:list A) (w f g:A->R) (d:R), finite_weight_mass xs w<>0 -> finite_centered_cross xs w f (fun x=>g x+d)=finite_centered_cross xs w f g.
Proof.
 intros A xs w f g d Hm; rewrite finite_centered_cross_symmetric; rewrite (finite_centered_shift_first A xs w g f d Hm); apply finite_centered_cross_symmetric.
Qed.

(**
 [finite_centered_affine_first] (theorem) — Affine calibration of a first score multiplies covariance by its slope but not its intercept.
 Mathematical meaning: Affine calibration of a first score multiplies covariance by its slope but not its intercept.
 Exact checked proposition: forall (A:Type) (xs:list A) (w f g:A->R) (a b:R), finite_weight_mass xs w<>0 -> finite_centered_cross xs w (fun x=>a*f x+b) g=a*finite_centered_cross xs w f g.
 Premises and side conditions: Nonzero total mass is required only when a weighted mean is transformed.
 Proof/definition method: Reuse existing FiniteSum and FiniteTwoCellProjection weighted summation, zero-support, mean, variance and polarization lemmas; isolate the real quadratic discriminant argument and avoid further list recursions. Proofs are written in Rocq Stdlib real arithmetic without admitted steps.
 Library reuse: Stdlib.Reals, Lra, Psatz, List, Bool; existing finite_sum_ext, finite_sum_nonnegative, finite_weighted_loss_nonnegative, centered covariance linearity, and real ring/field simplification.
 Boundary: Exact finite real-weighted sample and best-linear-prediction algebra only. No Gaussian conditional distribution, continuous normal-tail theorem, empirical IQ psychometric parameter, or normality premise has been established.
 *)
Theorem finite_centered_affine_first :
 forall (A:Type) (xs:list A) (w f g:A->R) (a b:R), finite_weight_mass xs w<>0 -> finite_centered_cross xs w (fun x=>a*f x+b) g=a*finite_centered_cross xs w f g.
Proof.
 intros A xs w f g a b Hm; rewrite (finite_centered_shift_first A xs w (fun x=>a*f x) g b Hm); apply finite_centered_cross_scale_first; exact Hm.
Qed.

(**
 [finite_centered_affine_second] (theorem) — Affine calibration of a second score multiplies covariance by its slope but not its intercept.
 Mathematical meaning: Affine calibration of a second score multiplies covariance by its slope but not its intercept.
 Exact checked proposition: forall (A:Type) (xs:list A) (w f g:A->R) (a b:R), finite_weight_mass xs w<>0 -> finite_centered_cross xs w f (fun x=>a*g x+b)=a*finite_centered_cross xs w f g.
 Premises and side conditions: Nonzero total mass is required only when a weighted mean is transformed.
 Proof/definition method: Reuse existing FiniteSum and FiniteTwoCellProjection weighted summation, zero-support, mean, variance and polarization lemmas; isolate the real quadratic discriminant argument and avoid further list recursions. Proofs are written in Rocq Stdlib real arithmetic without admitted steps.
 Library reuse: Stdlib.Reals, Lra, Psatz, List, Bool; existing finite_sum_ext, finite_sum_nonnegative, finite_weighted_loss_nonnegative, centered covariance linearity, and real ring/field simplification.
 Boundary: Exact finite real-weighted sample and best-linear-prediction algebra only. No Gaussian conditional distribution, continuous normal-tail theorem, empirical IQ psychometric parameter, or normality premise has been established.
 *)
Theorem finite_centered_affine_second :
 forall (A:Type) (xs:list A) (w f g:A->R) (a b:R), finite_weight_mass xs w<>0 -> finite_centered_cross xs w f (fun x=>a*g x+b)=a*finite_centered_cross xs w f g.
Proof.
 intros A xs w f g a b Hm; rewrite (finite_centered_shift_second A xs w f (fun x=>a*g x) b Hm); apply finite_centered_cross_scale_second; exact Hm.
Qed.

(**
 [finite_centered_affine_both] (theorem) — Two independently calibrated scores have covariance multiplied by the product of calibration slopes.
 Mathematical meaning: Two independently calibrated scores have covariance multiplied by the product of calibration slopes.
 Exact checked proposition: forall (A:Type) (xs:list A) (w f g:A->R) (a b c d:R), finite_weight_mass xs w<>0 -> finite_centered_cross xs w (fun x=>a*f x+b) (fun x=>c*g x+d)=a*c*finite_centered_cross xs w f g.
 Premises and side conditions: Nonzero total mass is required only when a weighted mean is transformed.
 Proof/definition method: Reuse existing FiniteSum and FiniteTwoCellProjection weighted summation, zero-support, mean, variance and polarization lemmas; isolate the real quadratic discriminant argument and avoid further list recursions. Proofs are written in Rocq Stdlib real arithmetic without admitted steps.
 Library reuse: Stdlib.Reals, Lra, Psatz, List, Bool; existing finite_sum_ext, finite_sum_nonnegative, finite_weighted_loss_nonnegative, centered covariance linearity, and real ring/field simplification.
 Boundary: Exact finite real-weighted sample and best-linear-prediction algebra only. No Gaussian conditional distribution, continuous normal-tail theorem, empirical IQ psychometric parameter, or normality premise has been established.
 *)
Theorem finite_centered_affine_both :
 forall (A:Type) (xs:list A) (w f g:A->R) (a b c d:R), finite_weight_mass xs w<>0 -> finite_centered_cross xs w (fun x=>a*f x+b) (fun x=>c*g x+d)=a*c*finite_centered_cross xs w f g.
Proof.
 intros A xs w f g a b c d Hm; rewrite (finite_centered_affine_first A xs w f (fun x=>c*g x+d) a b Hm); rewrite (finite_centered_affine_second A xs w f g c d Hm); ring.
Qed.

(**
 [finite_centered_sub_first] (theorem) — Centered covariance is subtractive in its first argument.
 Mathematical meaning: Centered covariance is subtractive in its first argument.
 Exact checked proposition: forall (A:Type) (xs:list A) (w f g h:A->R), finite_weight_mass xs w<>0 -> finite_centered_cross xs w (fun x=>f x-g x) h=finite_centered_cross xs w f h-finite_centered_cross xs w g h.
 Premises and side conditions: Nonzero total mass is required only when a weighted mean is transformed.
 Proof/definition method: Reuse existing FiniteSum and FiniteTwoCellProjection weighted summation, zero-support, mean, variance and polarization lemmas; isolate the real quadratic discriminant argument and avoid further list recursions. Proofs are written in Rocq Stdlib real arithmetic without admitted steps.
 Library reuse: Stdlib.Reals, Lra, Psatz, List, Bool; existing finite_sum_ext, finite_sum_nonnegative, finite_weighted_loss_nonnegative, centered covariance linearity, and real ring/field simplification.
 Boundary: Exact finite real-weighted sample and best-linear-prediction algebra only. No Gaussian conditional distribution, continuous normal-tail theorem, empirical IQ psychometric parameter, or normality premise has been established.
 *)
Theorem finite_centered_sub_first :
 forall (A:Type) (xs:list A) (w f g h:A->R), finite_weight_mass xs w<>0 -> finite_centered_cross xs w (fun x=>f x-g x) h=finite_centered_cross xs w f h-finite_centered_cross xs w g h.
Proof.
 intros A xs w f g h Hm; unfold finite_centered_cross; rewrite (finite_weighted_mean_sub A xs w f g Hm); apply finite_cross_sub_first.
Qed.

(**
 [finite_centered_sub_second] (theorem) — Centered covariance is subtractive in its second argument.
 Mathematical meaning: Centered covariance is subtractive in its second argument.
 Exact checked proposition: forall (A:Type) (xs:list A) (w f g h:A->R), finite_weight_mass xs w<>0 -> finite_centered_cross xs w f (fun x=>g x-h x)=finite_centered_cross xs w f g-finite_centered_cross xs w f h.
 Premises and side conditions: Nonzero total mass is required only when a weighted mean is transformed.
 Proof/definition method: Reuse existing FiniteSum and FiniteTwoCellProjection weighted summation, zero-support, mean, variance and polarization lemmas; isolate the real quadratic discriminant argument and avoid further list recursions. Proofs are written in Rocq Stdlib real arithmetic without admitted steps.
 Library reuse: Stdlib.Reals, Lra, Psatz, List, Bool; existing finite_sum_ext, finite_sum_nonnegative, finite_weighted_loss_nonnegative, centered covariance linearity, and real ring/field simplification.
 Boundary: Exact finite real-weighted sample and best-linear-prediction algebra only. No Gaussian conditional distribution, continuous normal-tail theorem, empirical IQ psychometric parameter, or normality premise has been established.
 *)
Theorem finite_centered_sub_second :
 forall (A:Type) (xs:list A) (w f g h:A->R), finite_weight_mass xs w<>0 -> finite_centered_cross xs w f (fun x=>g x-h x)=finite_centered_cross xs w f g-finite_centered_cross xs w f h.
Proof.
 intros A xs w f g h Hm; rewrite finite_centered_cross_symmetric; rewrite (finite_centered_sub_first A xs w g h f Hm); rewrite (finite_centered_cross_symmetric A xs w g f); rewrite (finite_centered_cross_symmetric A xs w h f); reflexivity.
Qed.

(**
 [finite_centered_four_term_expansion] (theorem) — Covariance of two sum scores expands into four pairwise covariances.
 Mathematical meaning: Covariance of two sum scores expands into four pairwise covariances.
 Exact checked proposition: forall (A:Type) (xs:list A) (w f g h k:A->R), finite_weight_mass xs w<>0 -> finite_centered_cross xs w (fun x=>f x+g x) (fun x=>h x+k x)=finite_centered_cross xs w f h+finite_centered_cross xs w f k+finite_centered_cross xs w g h+finite_centered_cross xs w g k.
 Premises and side conditions: Nonzero total mass is required only when a weighted mean is transformed.
 Proof/definition method: Reuse existing FiniteSum and FiniteTwoCellProjection weighted summation, zero-support, mean, variance and polarization lemmas; isolate the real quadratic discriminant argument and avoid further list recursions. Proofs are written in Rocq Stdlib real arithmetic without admitted steps.
 Library reuse: Stdlib.Reals, Lra, Psatz, List, Bool; existing finite_sum_ext, finite_sum_nonnegative, finite_weighted_loss_nonnegative, centered covariance linearity, and real ring/field simplification.
 Boundary: Exact finite real-weighted sample and best-linear-prediction algebra only. No Gaussian conditional distribution, continuous normal-tail theorem, empirical IQ psychometric parameter, or normality premise has been established.
 *)
Theorem finite_centered_four_term_expansion :
 forall (A:Type) (xs:list A) (w f g h k:A->R), finite_weight_mass xs w<>0 -> finite_centered_cross xs w (fun x=>f x+g x) (fun x=>h x+k x)=finite_centered_cross xs w f h+finite_centered_cross xs w f k+finite_centered_cross xs w g h+finite_centered_cross xs w g k.
Proof.
 intros A xs w f g h k Hm; rewrite (finite_centered_cross_add_first A xs w f g (fun x=>h x+k x) Hm); rewrite (finite_centered_cross_add_second A xs w f h k Hm); rewrite (finite_centered_cross_add_second A xs w g h k Hm); ring.
Qed.

(**
 [finite_centered_difference_variance] (theorem) — Variance of a score difference equals the sum of variances minus twice their covariance.
 Mathematical meaning: Variance of a score difference equals the sum of variances minus twice their covariance.
 Exact checked proposition: forall (A:Type) (xs:list A) (w f g:A->R), finite_weight_mass xs w<>0 -> finite_centered_cross xs w (fun x=>f x-g x) (fun x=>f x-g x)=finite_centered_cross xs w f f-2*finite_centered_cross xs w f g+finite_centered_cross xs w g g.
 Premises and side conditions: Nonzero total mass is required only when a weighted mean is transformed.
 Proof/definition method: Reuse existing FiniteSum and FiniteTwoCellProjection weighted summation, zero-support, mean, variance and polarization lemmas; isolate the real quadratic discriminant argument and avoid further list recursions. Proofs are written in Rocq Stdlib real arithmetic without admitted steps.
 Library reuse: Stdlib.Reals, Lra, Psatz, List, Bool; existing finite_sum_ext, finite_sum_nonnegative, finite_weighted_loss_nonnegative, centered covariance linearity, and real ring/field simplification.
 Boundary: Exact finite real-weighted sample and best-linear-prediction algebra only. No Gaussian conditional distribution, continuous normal-tail theorem, empirical IQ psychometric parameter, or normality premise has been established.
 *)
Theorem finite_centered_difference_variance :
 forall (A:Type) (xs:list A) (w f g:A->R), finite_weight_mass xs w<>0 -> finite_centered_cross xs w (fun x=>f x-g x) (fun x=>f x-g x)=finite_centered_cross xs w f f-2*finite_centered_cross xs w f g+finite_centered_cross xs w g g.
Proof.
 intros A xs w f g Hm; rewrite (finite_centered_sub_first A xs w f g (fun x=>f x-g x) Hm); rewrite (finite_centered_sub_second A xs w f f g Hm); rewrite (finite_centered_sub_second A xs w g f g Hm); rewrite (finite_centered_cross_symmetric A xs w g f); ring.
Qed.

(**
 [finite_centered_sum_variance] (theorem) — Variance of a sum of test scores equals individual variances plus twice their covariance.
 Mathematical meaning: Variance of a sum of test scores equals individual variances plus twice their covariance.
 Exact checked proposition: forall (A:Type) (xs:list A) (w f g:A->R), finite_weight_mass xs w<>0 -> finite_centered_cross xs w (fun x=>f x+g x) (fun x=>f x+g x)=finite_centered_cross xs w f f+2*finite_centered_cross xs w f g+finite_centered_cross xs w g g.
 Premises and side conditions: Nonzero total mass is required only when a weighted mean is transformed.
 Proof/definition method: Reuse existing FiniteSum and FiniteTwoCellProjection weighted summation, zero-support, mean, variance and polarization lemmas; isolate the real quadratic discriminant argument and avoid further list recursions. Proofs are written in Rocq Stdlib real arithmetic without admitted steps.
 Library reuse: Stdlib.Reals, Lra, Psatz, List, Bool; existing finite_sum_ext, finite_sum_nonnegative, finite_weighted_loss_nonnegative, centered covariance linearity, and real ring/field simplification.
 Boundary: Exact finite real-weighted sample and best-linear-prediction algebra only. No Gaussian conditional distribution, continuous normal-tail theorem, empirical IQ psychometric parameter, or normality premise has been established.
 *)
Theorem finite_centered_sum_variance :
 forall (A:Type) (xs:list A) (w f g:A->R), finite_weight_mass xs w<>0 -> finite_centered_cross xs w (fun x=>f x+g x) (fun x=>f x+g x)=finite_centered_cross xs w f f+2*finite_centered_cross xs w f g+finite_centered_cross xs w g g.
Proof.
 intros A xs w f g Hm; rewrite (finite_centered_four_term_expansion A xs w f g f g Hm); rewrite (finite_centered_cross_symmetric A xs w g f); ring.
Qed.

(**
 [finite_centered_variance_parallelogram] (theorem) — The covariance-induced variance obeys the parallelogram identity, certifying a quadratic inner-product structure.
 Mathematical meaning: The covariance-induced variance obeys the parallelogram identity, certifying a quadratic inner-product structure.
 Exact checked proposition: forall (A:Type) (xs:list A) (w f g:A->R), finite_weight_mass xs w<>0 -> finite_centered_cross xs w (fun x=>f x+g x) (fun x=>f x+g x)+finite_centered_cross xs w (fun x=>f x-g x) (fun x=>f x-g x)=2*finite_centered_cross xs w f f+2*finite_centered_cross xs w g g.
 Premises and side conditions: Nonzero total mass is required only when a weighted mean is transformed.
 Proof/definition method: Reuse existing FiniteSum and FiniteTwoCellProjection weighted summation, zero-support, mean, variance and polarization lemmas; isolate the real quadratic discriminant argument and avoid further list recursions. Proofs are written in Rocq Stdlib real arithmetic without admitted steps.
 Library reuse: Stdlib.Reals, Lra, Psatz, List, Bool; existing finite_sum_ext, finite_sum_nonnegative, finite_weighted_loss_nonnegative, centered covariance linearity, and real ring/field simplification.
 Boundary: Exact finite real-weighted sample and best-linear-prediction algebra only. No Gaussian conditional distribution, continuous normal-tail theorem, empirical IQ psychometric parameter, or normality premise has been established.
 *)
Theorem finite_centered_variance_parallelogram :
 forall (A:Type) (xs:list A) (w f g:A->R), finite_weight_mass xs w<>0 -> finite_centered_cross xs w (fun x=>f x+g x) (fun x=>f x+g x)+finite_centered_cross xs w (fun x=>f x-g x) (fun x=>f x-g x)=2*finite_centered_cross xs w f f+2*finite_centered_cross xs w g g.
Proof.
 intros A xs w f g Hm; rewrite finite_centered_sum_variance by exact Hm; rewrite finite_centered_difference_variance by exact Hm; ring.
Qed.

(**
 [finite_cov_slope] (definition) — Covariance-ratio coefficient of the best finite one-feature linear predictor.
 Mathematical meaning: Covariance-ratio coefficient of the best finite one-feature linear predictor.
 Exact definition: Definition finite_cov_slope {A:Type} (xs:list A) (w f g:A->R) : R := finite_centered_cross xs w f g / finite_centered_cross xs w g g.
 Premises and side conditions: Feature variance nonzero is assumed when division is statistically interpreted; division is total in Rocq's real numbers.
 Proof/definition method: Reuse existing FiniteSum and FiniteTwoCellProjection weighted summation, zero-support, mean, variance and polarization lemmas; isolate the real quadratic discriminant argument and avoid further list recursions. Proofs are written in Rocq Stdlib real arithmetic without admitted steps.
 Library reuse: Stdlib.Reals, Lra, Psatz, List, Bool; existing finite_sum_ext, finite_sum_nonnegative, finite_weighted_loss_nonnegative, centered covariance linearity, and real ring/field simplification.
 Boundary: Exact finite real-weighted sample and best-linear-prediction algebra only. No Gaussian conditional distribution, continuous normal-tail theorem, empirical IQ psychometric parameter, or normality premise has been established.
 *)
Definition finite_cov_slope {A:Type} (xs:list A) (w f g:A->R) : R := finite_centered_cross xs w f g / finite_centered_cross xs w g g.

(**
 [finite_cov_residual_variance] (definition) — Centered finite squared prediction residual for a specified feature slope.
 Mathematical meaning: Centered finite squared prediction residual for a specified feature slope.
 Exact definition: Definition finite_cov_residual_variance {A:Type} (xs:list A) (w f g:A->R) (b:R) : R := finite_centered_cross xs w (fun x=>f x-b*g x) (fun x=>f x-b*g x).
 Premises and side conditions: Feature variance nonzero is assumed when division is statistically interpreted; division is total in Rocq's real numbers.
 Proof/definition method: Reuse existing FiniteSum and FiniteTwoCellProjection weighted summation, zero-support, mean, variance and polarization lemmas; isolate the real quadratic discriminant argument and avoid further list recursions. Proofs are written in Rocq Stdlib real arithmetic without admitted steps.
 Library reuse: Stdlib.Reals, Lra, Psatz, List, Bool; existing finite_sum_ext, finite_sum_nonnegative, finite_weighted_loss_nonnegative, centered covariance linearity, and real ring/field simplification.
 Boundary: Exact finite real-weighted sample and best-linear-prediction algebra only. No Gaussian conditional distribution, continuous normal-tail theorem, empirical IQ psychometric parameter, or normality premise has been established.
 *)
Definition finite_cov_residual_variance {A:Type} (xs:list A) (w f g:A->R) (b:R) : R := finite_centered_cross xs w (fun x=>f x-b*g x) (fun x=>f x-b*g x).

(**
 [finite_cov_optimal_variance] (definition) — Schur residual variance from projecting a target onto one finite weighted feature.
 Mathematical meaning: Schur residual variance from projecting a target onto one finite weighted feature.
 Exact definition: Definition finite_cov_optimal_variance {A:Type} (xs:list A) (w f g:A->R) : R := finite_centered_cross xs w f f - finite_centered_cross xs w f g * finite_centered_cross xs w f g / finite_centered_cross xs w g g.
 Premises and side conditions: Feature variance nonzero is assumed when division is statistically interpreted; division is total in Rocq's real numbers.
 Proof/definition method: Reuse existing FiniteSum and FiniteTwoCellProjection weighted summation, zero-support, mean, variance and polarization lemmas; isolate the real quadratic discriminant argument and avoid further list recursions. Proofs are written in Rocq Stdlib real arithmetic without admitted steps.
 Library reuse: Stdlib.Reals, Lra, Psatz, List, Bool; existing finite_sum_ext, finite_sum_nonnegative, finite_weighted_loss_nonnegative, centered covariance linearity, and real ring/field simplification.
 Boundary: Exact finite real-weighted sample and best-linear-prediction algebra only. No Gaussian conditional distribution, continuous normal-tail theorem, empirical IQ psychometric parameter, or normality premise has been established.
 *)
Definition finite_cov_optimal_variance {A:Type} (xs:list A) (w f g:A->R) : R := finite_centered_cross xs w f f - finite_centered_cross xs w f g * finite_centered_cross xs w f g / finite_centered_cross xs w g g.


(* D031x: one-feature finite covariance regression, normal equations,
    explained variance, strict uniqueness and calibration invariants. *)

(**
 [finite_cov_slope_variance_identity] (theorem) — Finite regression slope solves covariance equals coefficient times feature variance.
 Mathematical meaning: Finite regression slope solves covariance equals coefficient times feature variance.
 Exact checked proposition: forall (A:Type) (xs:list A) (w f g:A->R), finite_centered_cross xs w g g<>0 -> finite_cov_slope xs w f g*finite_centered_cross xs w g g=finite_centered_cross xs w f g.
 Premises and side conditions: Feature centered variance nonzero.
 Proof/definition method: Reuse previously established exact finite centered covariance, weighted Cauchy–Schwarz, covariance bilinearity and the scalar normal equations. Reduce regression objective to its completed square and explicitly discharge positive denominators and risk bounds.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, real field/ring, finite-sum and covariance library lemmas, and no custom matrix inversion or new sample enumeration recursion.
 Boundary: Exact finite weighted covariance and best linear predictor identities only; no Gaussian conditional laws, numerical integration correctness, psychometric population evidence or normality of test scores is established.
 *)
Theorem finite_cov_slope_variance_identity :
 forall (A:Type) (xs:list A) (w f g:A->R), finite_centered_cross xs w g g<>0 -> finite_cov_slope xs w f g*finite_centered_cross xs w g g=finite_centered_cross xs w f g.
Proof.
 intros A xs w f g Hv; unfold finite_cov_slope; field; exact Hv.
Qed.

(**
 [finite_cov_slope_zero_iff] (theorem) — Regression slope vanishes exactly when target-feature centered covariance vanishes.
 Mathematical meaning: Regression slope vanishes exactly when target-feature centered covariance vanishes.
 Exact checked proposition: forall (A:Type) (xs:list A) (w f g:A->R), 0<finite_centered_cross xs w g g -> (finite_cov_slope xs w f g=0 <-> finite_centered_cross xs w f g=0).
 Premises and side conditions: Strictly positive feature variance.
 Proof/definition method: Reuse previously established exact finite centered covariance, weighted Cauchy–Schwarz, covariance bilinearity and the scalar normal equations. Reduce regression objective to its completed square and explicitly discharge positive denominators and risk bounds.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, real field/ring, finite-sum and covariance library lemmas, and no custom matrix inversion or new sample enumeration recursion.
 Boundary: Exact finite weighted covariance and best linear predictor identities only; no Gaussian conditional laws, numerical integration correctness, psychometric population evidence or normality of test scores is established.
 *)
Theorem finite_cov_slope_zero_iff :
 forall (A:Type) (xs:list A) (w f g:A->R), 0<finite_centered_cross xs w g g -> (finite_cov_slope xs w f g=0 <-> finite_centered_cross xs w f g=0).
Proof.
 intros A xs w f g Hv; unfold finite_cov_slope,Rdiv.
 assert (Hi:0< /finite_centered_cross xs w g g)
   by (apply Rinv_0_lt_compat; exact Hv).
 split; intro H; nra.
Qed.

(**
 [finite_cov_slope_positive_iff] (theorem) — Positive optimal finite slope is equivalent to positive target-feature covariance.
 Mathematical meaning: Positive optimal finite slope is equivalent to positive target-feature covariance.
 Exact checked proposition: forall (A:Type) (xs:list A) (w f g:A->R), 0<finite_centered_cross xs w g g -> (0<finite_cov_slope xs w f g <-> 0<finite_centered_cross xs w f g).
 Premises and side conditions: Strictly positive feature variance.
 Proof/definition method: Reuse previously established exact finite centered covariance, weighted Cauchy–Schwarz, covariance bilinearity and the scalar normal equations. Reduce regression objective to its completed square and explicitly discharge positive denominators and risk bounds.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, real field/ring, finite-sum and covariance library lemmas, and no custom matrix inversion or new sample enumeration recursion.
 Boundary: Exact finite weighted covariance and best linear predictor identities only; no Gaussian conditional laws, numerical integration correctness, psychometric population evidence or normality of test scores is established.
 *)
Theorem finite_cov_slope_positive_iff :
 forall (A:Type) (xs:list A) (w f g:A->R), 0<finite_centered_cross xs w g g -> (0<finite_cov_slope xs w f g <-> 0<finite_centered_cross xs w f g).
Proof.
 intros A xs w f g Hv; unfold finite_cov_slope,Rdiv.
 assert (Hi:0< /finite_centered_cross xs w g g)
   by (apply Rinv_0_lt_compat; exact Hv).
 split; intro H; nra.
Qed.

(**
 [finite_cov_slope_negative_iff] (theorem) — Negative optimal finite slope is equivalent to negative target-feature covariance.
 Mathematical meaning: Negative optimal finite slope is equivalent to negative target-feature covariance.
 Exact checked proposition: forall (A:Type) (xs:list A) (w f g:A->R), 0<finite_centered_cross xs w g g -> (finite_cov_slope xs w f g<0 <-> finite_centered_cross xs w f g<0).
 Premises and side conditions: Strictly positive feature variance.
 Proof/definition method: Reuse previously established exact finite centered covariance, weighted Cauchy–Schwarz, covariance bilinearity and the scalar normal equations. Reduce regression objective to its completed square and explicitly discharge positive denominators and risk bounds.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, real field/ring, finite-sum and covariance library lemmas, and no custom matrix inversion or new sample enumeration recursion.
 Boundary: Exact finite weighted covariance and best linear predictor identities only; no Gaussian conditional laws, numerical integration correctness, psychometric population evidence or normality of test scores is established.
 *)
Theorem finite_cov_slope_negative_iff :
 forall (A:Type) (xs:list A) (w f g:A->R), 0<finite_centered_cross xs w g g -> (finite_cov_slope xs w f g<0 <-> finite_centered_cross xs w f g<0).
Proof.
 intros A xs w f g Hv; unfold finite_cov_slope,Rdiv.
 assert (Hi:0< /finite_centered_cross xs w g g)
   by (apply Rinv_0_lt_compat; exact Hv).
 split; intro H; nra.
Qed.

(**
 [finite_cov_slope_target_scale] (theorem) — Scaling a target measurement rescales its optimal simple-regression coefficient.
 Mathematical meaning: Scaling a target measurement rescales its optimal simple-regression coefficient.
 Exact checked proposition: forall (A:Type) (xs:list A) (w f g:A->R) (k:R), finite_weight_mass xs w<>0 -> finite_cov_slope xs w (fun x=>k*f x) g=k*finite_cov_slope xs w f g.
 Premises and side conditions: Nonzero total weight mass is required for finite mean and covariance linearity.
 Proof/definition method: Reuse previously established exact finite centered covariance, weighted Cauchy–Schwarz, covariance bilinearity and the scalar normal equations. Reduce regression objective to its completed square and explicitly discharge positive denominators and risk bounds.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, real field/ring, finite-sum and covariance library lemmas, and no custom matrix inversion or new sample enumeration recursion.
 Boundary: Exact finite weighted covariance and best linear predictor identities only; no Gaussian conditional laws, numerical integration correctness, psychometric population evidence or normality of test scores is established.
 *)
Theorem finite_cov_slope_target_scale :
 forall (A:Type) (xs:list A) (w f g:A->R) (k:R), finite_weight_mass xs w<>0 -> finite_cov_slope xs w (fun x=>k*f x) g=k*finite_cov_slope xs w f g.
Proof.
 intros A xs w f g k Hm; unfold finite_cov_slope.
 rewrite (finite_centered_cross_scale_first A xs w f g k Hm).
 unfold Rdiv; ring.
Qed.

(**
 [finite_cov_slope_target_translation] (theorem) — Target-score additive calibration does not change the optimal feature regression slope.
 Mathematical meaning: Target-score additive calibration does not change the optimal feature regression slope.
 Exact checked proposition: forall (A:Type) (xs:list A) (w f g:A->R) (d:R), finite_weight_mass xs w<>0 -> finite_cov_slope xs w (fun x=>f x+d) g=finite_cov_slope xs w f g.
 Premises and side conditions: Nonzero total weight mass is required for finite mean and covariance linearity.
 Proof/definition method: Reuse previously established exact finite centered covariance, weighted Cauchy–Schwarz, covariance bilinearity and the scalar normal equations. Reduce regression objective to its completed square and explicitly discharge positive denominators and risk bounds.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, real field/ring, finite-sum and covariance library lemmas, and no custom matrix inversion or new sample enumeration recursion.
 Boundary: Exact finite weighted covariance and best linear predictor identities only; no Gaussian conditional laws, numerical integration correctness, psychometric population evidence or normality of test scores is established.
 *)
Theorem finite_cov_slope_target_translation :
 forall (A:Type) (xs:list A) (w f g:A->R) (d:R), finite_weight_mass xs w<>0 -> finite_cov_slope xs w (fun x=>f x+d) g=finite_cov_slope xs w f g.
Proof.
 intros A xs w f g d Hm; unfold finite_cov_slope.
 rewrite (finite_centered_shift_first A xs w f g d Hm); reflexivity.
Qed.

(**
 [finite_cov_slope_feature_translation] (theorem) — Feature-score additive calibration does not change the optimal regression slope.
 Mathematical meaning: Feature-score additive calibration does not change the optimal regression slope.
 Exact checked proposition: forall (A:Type) (xs:list A) (w f g:A->R) (d:R), finite_weight_mass xs w<>0 -> finite_cov_slope xs w f (fun x=>g x+d)=finite_cov_slope xs w f g.
 Premises and side conditions: Nonzero total weight mass is required for finite mean and covariance linearity.
 Proof/definition method: Reuse previously established exact finite centered covariance, weighted Cauchy–Schwarz, covariance bilinearity and the scalar normal equations. Reduce regression objective to its completed square and explicitly discharge positive denominators and risk bounds.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, real field/ring, finite-sum and covariance library lemmas, and no custom matrix inversion or new sample enumeration recursion.
 Boundary: Exact finite weighted covariance and best linear predictor identities only; no Gaussian conditional laws, numerical integration correctness, psychometric population evidence or normality of test scores is established.
 *)
Theorem finite_cov_slope_feature_translation :
 forall (A:Type) (xs:list A) (w f g:A->R) (d:R), finite_weight_mass xs w<>0 -> finite_cov_slope xs w f (fun x=>g x+d)=finite_cov_slope xs w f g.
Proof.
 intros A xs w f g d Hm; unfold finite_cov_slope.
 rewrite (finite_centered_shift_second A xs w f g d Hm).
 rewrite (finite_centered_shift_first A xs w g (fun x=>g x+d) d Hm).
 rewrite (finite_centered_shift_second A xs w g g d Hm).
 reflexivity.
Qed.

(**
 [finite_cov_slope_target_add_feature] (theorem) — Adding a known multiple of the feature to the target shifts the optimal slope by that multiple.
 Mathematical meaning: Adding a known multiple of the feature to the target shifts the optimal slope by that multiple.
 Exact checked proposition: forall (A:Type) (xs:list A) (w f g:A->R) (k:R), finite_weight_mass xs w<>0 -> finite_centered_cross xs w g g<>0 -> finite_cov_slope xs w (fun x=>f x+k*g x) g=finite_cov_slope xs w f g+k.
 Premises and side conditions: Nonzero total mass and invertible feature variance.
 Proof/definition method: Reuse previously established exact finite centered covariance, weighted Cauchy–Schwarz, covariance bilinearity and the scalar normal equations. Reduce regression objective to its completed square and explicitly discharge positive denominators and risk bounds.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, real field/ring, finite-sum and covariance library lemmas, and no custom matrix inversion or new sample enumeration recursion.
 Boundary: Exact finite weighted covariance and best linear predictor identities only; no Gaussian conditional laws, numerical integration correctness, psychometric population evidence or normality of test scores is established.
 *)
Theorem finite_cov_slope_target_add_feature :
 forall (A:Type) (xs:list A) (w f g:A->R) (k:R), finite_weight_mass xs w<>0 -> finite_centered_cross xs w g g<>0 -> finite_cov_slope xs w (fun x=>f x+k*g x) g=finite_cov_slope xs w f g+k.
Proof.
 intros A xs w f g k Hm Hv; unfold finite_cov_slope.
 rewrite (finite_centered_cross_add_first A xs w f (fun x=>k*g x) g Hm).
 rewrite (finite_centered_cross_scale_first A xs w g g k Hm).
 unfold Rdiv; field; exact Hv.
Qed.

(**
 [finite_cov_residual_variance_expansion] (theorem) — Centered residual variance is exactly a quadratic polynomial in the candidate linear-regression slope.
 Mathematical meaning: Centered residual variance is exactly a quadratic polynomial in the candidate linear-regression slope.
 Exact checked proposition: forall (A:Type) (xs:list A) (w f g:A->R) (b:R), finite_weight_mass xs w<>0 -> finite_cov_residual_variance xs w f g b=finite_centered_cross xs w f f-2*b*finite_centered_cross xs w f g+b*b*finite_centered_cross xs w g g.
 Premises and side conditions: Nonzero total weight mass is required for finite mean and covariance linearity.
 Proof/definition method: Reuse previously established exact finite centered covariance, weighted Cauchy–Schwarz, covariance bilinearity and the scalar normal equations. Reduce regression objective to its completed square and explicitly discharge positive denominators and risk bounds.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, real field/ring, finite-sum and covariance library lemmas, and no custom matrix inversion or new sample enumeration recursion.
 Boundary: Exact finite weighted covariance and best linear predictor identities only; no Gaussian conditional laws, numerical integration correctness, psychometric population evidence or normality of test scores is established.
 *)
Theorem finite_cov_residual_variance_expansion :
 forall (A:Type) (xs:list A) (w f g:A->R) (b:R), finite_weight_mass xs w<>0 -> finite_cov_residual_variance xs w f g b=finite_centered_cross xs w f f-2*b*finite_centered_cross xs w f g+b*b*finite_centered_cross xs w g g.
Proof.
 intros A xs w f g b Hm; unfold finite_cov_residual_variance.
 rewrite (finite_centered_difference_variance A xs w f (fun x=>b*g x) Hm).
 rewrite (finite_centered_cross_scale_second A xs w f g b Hm).
 rewrite (finite_centered_cross_scale_first A xs w g (fun x=>b*g x) b Hm).
 rewrite (finite_centered_cross_scale_second A xs w g g b Hm).
 ring.
Qed.

(**
 [finite_cov_residual_variance_nonnegative] (theorem) — Centered finite regression residual variance cannot be negative under nonnegative sample weights.
 Mathematical meaning: Centered finite regression residual variance cannot be negative under nonnegative sample weights.
 Exact checked proposition: forall (A:Type) (xs:list A) (w f g:A->R) (b:R), (forall x, In x xs -> 0<=w x) -> 0<=finite_cov_residual_variance xs w f g b.
 Premises and side conditions: Nonnegative weights on all enumerated outcomes.
 Proof/definition method: Reuse previously established exact finite centered covariance, weighted Cauchy–Schwarz, covariance bilinearity and the scalar normal equations. Reduce regression objective to its completed square and explicitly discharge positive denominators and risk bounds.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, real field/ring, finite-sum and covariance library lemmas, and no custom matrix inversion or new sample enumeration recursion.
 Boundary: Exact finite weighted covariance and best linear predictor identities only; no Gaussian conditional laws, numerical integration correctness, psychometric population evidence or normality of test scores is established.
 *)
Theorem finite_cov_residual_variance_nonnegative :
 forall (A:Type) (xs:list A) (w f g:A->R) (b:R), (forall x, In x xs -> 0<=w x) -> 0<=finite_cov_residual_variance xs w f g b.
Proof.
 intros A xs w f g b Hw; unfold finite_cov_residual_variance.
 apply finite_centered_variance_nonnegative; exact Hw.
Qed.

(**
 [finite_cov_residual_normal_equation] (theorem) — The optimally fitted residual is orthogonal to the feature, giving the finite normal equation.
 Mathematical meaning: The optimally fitted residual is orthogonal to the feature, giving the finite normal equation.
 Exact checked proposition: forall (A:Type) (xs:list A) (w f g:A->R), finite_weight_mass xs w<>0 -> finite_centered_cross xs w g g<>0 -> finite_centered_cross xs w (fun x=>f x-finite_cov_slope xs w f g*g x) g=0.
 Premises and side conditions: Nonzero total mass and invertible feature variance.
 Proof/definition method: Reuse previously established exact finite centered covariance, weighted Cauchy–Schwarz, covariance bilinearity and the scalar normal equations. Reduce regression objective to its completed square and explicitly discharge positive denominators and risk bounds.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, real field/ring, finite-sum and covariance library lemmas, and no custom matrix inversion or new sample enumeration recursion.
 Boundary: Exact finite weighted covariance and best linear predictor identities only; no Gaussian conditional laws, numerical integration correctness, psychometric population evidence or normality of test scores is established.
 *)
Theorem finite_cov_residual_normal_equation :
 forall (A:Type) (xs:list A) (w f g:A->R), finite_weight_mass xs w<>0 -> finite_centered_cross xs w g g<>0 -> finite_centered_cross xs w (fun x=>f x-finite_cov_slope xs w f g*g x) g=0.
Proof.
 intros A xs w f g Hm Hv.
 rewrite (finite_centered_sub_first A xs w f
   (fun x=>finite_cov_slope xs w f g*g x) g Hm).
 rewrite (finite_centered_cross_scale_first A xs w g g
   (finite_cov_slope xs w f g) Hm).
 pose proof (finite_cov_slope_variance_identity A xs w f g Hv) as He.
 lra.
Qed.

(**
 [finite_cov_residual_variance_at_slope] (theorem) — At the optimal slope, the finite residual variance is the Schur covariance ratio formula.
 Mathematical meaning: At the optimal slope, the finite residual variance is the Schur covariance ratio formula.
 Exact checked proposition: forall (A:Type) (xs:list A) (w f g:A->R), finite_weight_mass xs w<>0 -> finite_centered_cross xs w g g<>0 -> finite_cov_residual_variance xs w f g (finite_cov_slope xs w f g)=finite_cov_optimal_variance xs w f g.
 Premises and side conditions: Nonzero sample mass and invertible feature centered variance.
 Proof/definition method: Reuse previously established exact finite centered covariance, weighted Cauchy–Schwarz, covariance bilinearity and the scalar normal equations. Reduce regression objective to its completed square and explicitly discharge positive denominators and risk bounds.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, real field/ring, finite-sum and covariance library lemmas, and no custom matrix inversion or new sample enumeration recursion.
 Boundary: Exact finite weighted covariance and best linear predictor identities only; no Gaussian conditional laws, numerical integration correctness, psychometric population evidence or normality of test scores is established.
 *)
Theorem finite_cov_residual_variance_at_slope :
 forall (A:Type) (xs:list A) (w f g:A->R), finite_weight_mass xs w<>0 -> finite_centered_cross xs w g g<>0 -> finite_cov_residual_variance xs w f g (finite_cov_slope xs w f g)=finite_cov_optimal_variance xs w f g.
Proof.
 intros A xs w f g Hm Hv.
 rewrite (finite_cov_residual_variance_expansion A xs w f g
   (finite_cov_slope xs w f g) Hm).
 unfold finite_cov_optimal_variance,finite_cov_slope.
 field; exact Hv.
Qed.

(**
 [finite_cov_excess_risk_identity] (theorem) — The exact loss from any slope misspecification equals feature variance times squared distance to the optimal slope.
 Mathematical meaning: The exact loss from any slope misspecification equals feature variance times squared distance to the optimal slope.
 Exact checked proposition: forall (A:Type) (xs:list A) (w f g:A->R) (b:R), finite_weight_mass xs w<>0 -> finite_centered_cross xs w g g<>0 -> finite_cov_residual_variance xs w f g b=finite_cov_residual_variance xs w f g (finite_cov_slope xs w f g)+finite_centered_cross xs w g g*(b-finite_cov_slope xs w f g)*(b-finite_cov_slope xs w f g).
 Premises and side conditions: Nonzero mass and invertible feature variance.
 Proof/definition method: Reuse previously established exact finite centered covariance, weighted Cauchy–Schwarz, covariance bilinearity and the scalar normal equations. Reduce regression objective to its completed square and explicitly discharge positive denominators and risk bounds.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, real field/ring, finite-sum and covariance library lemmas, and no custom matrix inversion or new sample enumeration recursion.
 Boundary: Exact finite weighted covariance and best linear predictor identities only; no Gaussian conditional laws, numerical integration correctness, psychometric population evidence or normality of test scores is established.
 *)
Theorem finite_cov_excess_risk_identity :
 forall (A:Type) (xs:list A) (w f g:A->R) (b:R), finite_weight_mass xs w<>0 -> finite_centered_cross xs w g g<>0 -> finite_cov_residual_variance xs w f g b=finite_cov_residual_variance xs w f g (finite_cov_slope xs w f g)+finite_centered_cross xs w g g*(b-finite_cov_slope xs w f g)*(b-finite_cov_slope xs w f g).
Proof.
 intros A xs w f g b Hm Hv.
 rewrite (finite_cov_residual_variance_expansion A xs w f g b Hm).
 rewrite (finite_cov_residual_variance_expansion A xs w f g
   (finite_cov_slope xs w f g) Hm).
 pose proof (finite_cov_slope_variance_identity A xs w f g Hv) as He.
 rewrite <- He; ring.
Qed.

(**
 [finite_cov_slope_global_optimality] (theorem) — The covariance-ratio slope globally minimizes finite centered squared error among all linear slopes.
 Mathematical meaning: The covariance-ratio slope globally minimizes finite centered squared error among all linear slopes.
 Exact checked proposition: forall (A:Type) (xs:list A) (w f g:A->R) (b:R), finite_weight_mass xs w<>0 -> 0<finite_centered_cross xs w g g -> finite_cov_residual_variance xs w f g (finite_cov_slope xs w f g)<=finite_cov_residual_variance xs w f g b.
 Premises and side conditions: Strictly positive feature centered variance and nonzero mass.
 Proof/definition method: Reuse previously established exact finite centered covariance, weighted Cauchy–Schwarz, covariance bilinearity and the scalar normal equations. Reduce regression objective to its completed square and explicitly discharge positive denominators and risk bounds.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, real field/ring, finite-sum and covariance library lemmas, and no custom matrix inversion or new sample enumeration recursion.
 Boundary: Exact finite weighted covariance and best linear predictor identities only; no Gaussian conditional laws, numerical integration correctness, psychometric population evidence or normality of test scores is established.
 *)
Theorem finite_cov_slope_global_optimality :
 forall (A:Type) (xs:list A) (w f g:A->R) (b:R), finite_weight_mass xs w<>0 -> 0<finite_centered_cross xs w g g -> finite_cov_residual_variance xs w f g (finite_cov_slope xs w f g)<=finite_cov_residual_variance xs w f g b.
Proof.
 intros A xs w f g b Hm Hv.
 rewrite (finite_cov_excess_risk_identity A xs w f g b Hm ltac:(lra)).
 assert (Hs:0<=(b-finite_cov_slope xs w f g)*(b-finite_cov_slope xs w f g)).
 { change (0<=Rsqr(b-finite_cov_slope xs w f g)); apply Rle_0_sqr. }
 assert (Hp:0<=finite_centered_cross xs w g g*
  ((b-finite_cov_slope xs w f g)*(b-finite_cov_slope xs w f g))).
 { apply Rmult_le_pos; [lra|exact Hs]. }
 replace (finite_centered_cross xs w g g*(b-finite_cov_slope xs w f g)*
  (b-finite_cov_slope xs w f g))
 with (finite_centered_cross xs w g g*
  ((b-finite_cov_slope xs w f g)*(b-finite_cov_slope xs w f g))) by ring.
 lra.
Qed.

(**
 [finite_cov_slope_optimal_iff] (theorem) — When feature variance is positive, equality with optimal centered loss holds only for the unique covariance-ratio slope.
 Mathematical meaning: When feature variance is positive, equality with optimal centered loss holds only for the unique covariance-ratio slope.
 Exact checked proposition: forall (A:Type) (xs:list A) (w f g:A->R) (b:R), finite_weight_mass xs w<>0 -> 0<finite_centered_cross xs w g g -> (finite_cov_residual_variance xs w f g b=finite_cov_residual_variance xs w f g (finite_cov_slope xs w f g) <-> b=finite_cov_slope xs w f g).
 Premises and side conditions: Positive feature centered variance guarantees strict convexity and uniqueness.
 Proof/definition method: Reuse previously established exact finite centered covariance, weighted Cauchy–Schwarz, covariance bilinearity and the scalar normal equations. Reduce regression objective to its completed square and explicitly discharge positive denominators and risk bounds.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, real field/ring, finite-sum and covariance library lemmas, and no custom matrix inversion or new sample enumeration recursion.
 Boundary: Exact finite weighted covariance and best linear predictor identities only; no Gaussian conditional laws, numerical integration correctness, psychometric population evidence or normality of test scores is established.
 *)
Theorem finite_cov_slope_optimal_iff :
 forall (A:Type) (xs:list A) (w f g:A->R) (b:R), finite_weight_mass xs w<>0 -> 0<finite_centered_cross xs w g g -> (finite_cov_residual_variance xs w f g b=finite_cov_residual_variance xs w f g (finite_cov_slope xs w f g) <-> b=finite_cov_slope xs w f g).
Proof.
 intros A xs w f g b Hm Hv.
 rewrite (finite_cov_excess_risk_identity A xs w f g b Hm ltac:(lra)).
 split; intro H.
 - assert (Hprod:finite_centered_cross xs w g g*
    ((b-finite_cov_slope xs w f g)*(b-finite_cov_slope xs w f g))=0) by nra.
   apply Rmult_integral in Hprod.
   destruct Hprod as [Hbad|Hsq]; [lra|nra].
 - rewrite H; ring.
Qed.

(**
 [finite_cov_slope_strict_optimality] (theorem) — Any slope differing from the covariance-ratio coefficient has strictly larger finite prediction error.
 Mathematical meaning: Any slope differing from the covariance-ratio coefficient has strictly larger finite prediction error.
 Exact checked proposition: forall (A:Type) (xs:list A) (w f g:A->R) (b:R), finite_weight_mass xs w<>0 -> 0<finite_centered_cross xs w g g -> b<>finite_cov_slope xs w f g -> finite_cov_residual_variance xs w f g (finite_cov_slope xs w f g)<finite_cov_residual_variance xs w f g b.
 Premises and side conditions: Positive feature variance and a nonoptimal candidate slope.
 Proof/definition method: Reuse previously established exact finite centered covariance, weighted Cauchy–Schwarz, covariance bilinearity and the scalar normal equations. Reduce regression objective to its completed square and explicitly discharge positive denominators and risk bounds.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, real field/ring, finite-sum and covariance library lemmas, and no custom matrix inversion or new sample enumeration recursion.
 Boundary: Exact finite weighted covariance and best linear predictor identities only; no Gaussian conditional laws, numerical integration correctness, psychometric population evidence or normality of test scores is established.
 *)
Theorem finite_cov_slope_strict_optimality :
 forall (A:Type) (xs:list A) (w f g:A->R) (b:R), finite_weight_mass xs w<>0 -> 0<finite_centered_cross xs w g g -> b<>finite_cov_slope xs w f g -> finite_cov_residual_variance xs w f g (finite_cov_slope xs w f g)<finite_cov_residual_variance xs w f g b.
Proof.
 intros A xs w f g b Hm Hv Hneq.
 rewrite (finite_cov_excess_risk_identity A xs w f g b Hm ltac:(lra)).
 assert (Hs:0<(b-finite_cov_slope xs w f g)*(b-finite_cov_slope xs w f g)) by nra.
 assert (Hp:0<finite_centered_cross xs w g g*
  ((b-finite_cov_slope xs w f g)*(b-finite_cov_slope xs w f g))).
 { apply Rmult_lt_0_compat; [exact Hv|exact Hs]. }
 nra.
Qed.

(**
 [finite_cov_explained_variance_exact] (theorem) — Explained variance from one-feature least-squares projection equals target-feature covariance squared divided by feature variance.
 Mathematical meaning: Explained variance from one-feature least-squares projection equals target-feature covariance squared divided by feature variance.
 Exact checked proposition: forall (A:Type) (xs:list A) (w f g:A->R), finite_weight_mass xs w<>0 -> finite_centered_cross xs w g g<>0 -> finite_centered_cross xs w f f-finite_cov_residual_variance xs w f g (finite_cov_slope xs w f g)=finite_centered_cross xs w f g*finite_centered_cross xs w f g/finite_centered_cross xs w g g.
 Premises and side conditions: Feature variance nonzero and total weight mass nonzero.
 Proof/definition method: Reuse previously established exact finite centered covariance, weighted Cauchy–Schwarz, covariance bilinearity and the scalar normal equations. Reduce regression objective to its completed square and explicitly discharge positive denominators and risk bounds.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, real field/ring, finite-sum and covariance library lemmas, and no custom matrix inversion or new sample enumeration recursion.
 Boundary: Exact finite weighted covariance and best linear predictor identities only; no Gaussian conditional laws, numerical integration correctness, psychometric population evidence or normality of test scores is established.
 *)
Theorem finite_cov_explained_variance_exact :
 forall (A:Type) (xs:list A) (w f g:A->R), finite_weight_mass xs w<>0 -> finite_centered_cross xs w g g<>0 -> finite_centered_cross xs w f f-finite_cov_residual_variance xs w f g (finite_cov_slope xs w f g)=finite_centered_cross xs w f g*finite_centered_cross xs w f g/finite_centered_cross xs w g g.
Proof.
 intros A xs w f g Hm Hv.
 rewrite (finite_cov_residual_variance_at_slope A xs w f g Hm Hv).
 unfold finite_cov_optimal_variance; ring.
Qed.

(**
 [finite_cov_explained_variance_nonnegative] (theorem) — The optimum finite one-feature regression cannot increase centered residual variance over the intercept-only baseline.
 Mathematical meaning: The optimum finite one-feature regression cannot increase centered residual variance over the intercept-only baseline.
 Exact checked proposition: forall (A:Type) (xs:list A) (w f g:A->R), finite_weight_mass xs w<>0 -> 0<finite_centered_cross xs w g g -> finite_cov_residual_variance xs w f g (finite_cov_slope xs w f g)<=finite_centered_cross xs w f f.
 Premises and side conditions: Nonzero mass and strictly positive feature variance.
 Proof/definition method: Reuse previously established exact finite centered covariance, weighted Cauchy–Schwarz, covariance bilinearity and the scalar normal equations. Reduce regression objective to its completed square and explicitly discharge positive denominators and risk bounds.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, real field/ring, finite-sum and covariance library lemmas, and no custom matrix inversion or new sample enumeration recursion.
 Boundary: Exact finite weighted covariance and best linear predictor identities only; no Gaussian conditional laws, numerical integration correctness, psychometric population evidence or normality of test scores is established.
 *)
Theorem finite_cov_explained_variance_nonnegative :
 forall (A:Type) (xs:list A) (w f g:A->R), finite_weight_mass xs w<>0 -> 0<finite_centered_cross xs w g g -> finite_cov_residual_variance xs w f g (finite_cov_slope xs w f g)<=finite_centered_cross xs w f f.
Proof.
 intros A xs w f g Hm Hv.
 pose proof (finite_cov_slope_global_optimality A xs w f g 0 Hm Hv) as Hmin.
 assert (H0:finite_cov_residual_variance xs w f g 0=finite_centered_cross xs w f f).
 { rewrite (finite_cov_residual_variance_expansion A xs w f g 0 Hm); ring. }
 rewrite H0 in Hmin; exact Hmin.
Qed.

(**
 [finite_cov_explained_variance_zero_iff] (theorem) — The fitted feature explains zero centered variance exactly when its covariance with the target is zero.
 Mathematical meaning: The fitted feature explains zero centered variance exactly when its covariance with the target is zero.
 Exact checked proposition: forall (A:Type) (xs:list A) (w f g:A->R), finite_weight_mass xs w<>0 -> 0<finite_centered_cross xs w g g -> (finite_cov_residual_variance xs w f g (finite_cov_slope xs w f g)=finite_centered_cross xs w f f <-> finite_centered_cross xs w f g=0).
 Premises and side conditions: Strictly positive feature variance and nonzero mass.
 Proof/definition method: Reuse previously established exact finite centered covariance, weighted Cauchy–Schwarz, covariance bilinearity and the scalar normal equations. Reduce regression objective to its completed square and explicitly discharge positive denominators and risk bounds.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, real field/ring, finite-sum and covariance library lemmas, and no custom matrix inversion or new sample enumeration recursion.
 Boundary: Exact finite weighted covariance and best linear predictor identities only; no Gaussian conditional laws, numerical integration correctness, psychometric population evidence or normality of test scores is established.
 *)
Theorem finite_cov_explained_variance_zero_iff :
 forall (A:Type) (xs:list A) (w f g:A->R), finite_weight_mass xs w<>0 -> 0<finite_centered_cross xs w g g -> (finite_cov_residual_variance xs w f g (finite_cov_slope xs w f g)=finite_centered_cross xs w f f <-> finite_centered_cross xs w f g=0).
Proof.
 intros A xs w f g Hm Hv.
 rewrite (finite_cov_residual_variance_at_slope A xs w f g Hm ltac:(lra)).
 unfold finite_cov_optimal_variance,Rdiv.
 assert (Hi:0< /finite_centered_cross xs w g g)
   by (apply Rinv_0_lt_compat; exact Hv).
 split; intro H.
 - assert (Hprod:finite_centered_cross xs w f g*finite_centered_cross xs w f g*
    /finite_centered_cross xs w g g=0) by lra.
   apply Rmult_integral in Hprod.
   destruct Hprod as [Hs|Hinv].
   + apply Rmult_integral in Hs; tauto.
   + lra.
 - rewrite H; ring.
Qed.

(**
 [finite_cov_explained_variance_strict_iff] (theorem) — Optimized finite linear prediction strictly improves over the intercept-only baseline exactly when covariance is nonzero.
 Mathematical meaning: Optimized finite linear prediction strictly improves over the intercept-only baseline exactly when covariance is nonzero.
 Exact checked proposition: forall (A:Type) (xs:list A) (w f g:A->R), finite_weight_mass xs w<>0 -> 0<finite_centered_cross xs w g g -> (finite_cov_residual_variance xs w f g (finite_cov_slope xs w f g)<finite_centered_cross xs w f f <-> finite_centered_cross xs w f g<>0).
 Premises and side conditions: Strictly positive feature variance and nonzero mass.
 Proof/definition method: Reuse previously established exact finite centered covariance, weighted Cauchy–Schwarz, covariance bilinearity and the scalar normal equations. Reduce regression objective to its completed square and explicitly discharge positive denominators and risk bounds.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, real field/ring, finite-sum and covariance library lemmas, and no custom matrix inversion or new sample enumeration recursion.
 Boundary: Exact finite weighted covariance and best linear predictor identities only; no Gaussian conditional laws, numerical integration correctness, psychometric population evidence or normality of test scores is established.
 *)
Theorem finite_cov_explained_variance_strict_iff :
 forall (A:Type) (xs:list A) (w f g:A->R), finite_weight_mass xs w<>0 -> 0<finite_centered_cross xs w g g -> (finite_cov_residual_variance xs w f g (finite_cov_slope xs w f g)<finite_centered_cross xs w f f <-> finite_centered_cross xs w f g<>0).
Proof.
 intros A xs w f g Hm Hv.
 rewrite (finite_cov_residual_variance_at_slope A xs w f g Hm ltac:(lra)).
 unfold finite_cov_optimal_variance,Rdiv.
 assert (Hi:0< /finite_centered_cross xs w g g)
   by (apply Rinv_0_lt_compat; exact Hv).
 split; intro H.
 - intro Hz; rewrite Hz in H; nra.
 - assert (Hs:0<finite_centered_cross xs w f g*finite_centered_cross xs w f g) by nra.
   assert (Hp:0<(finite_centered_cross xs w f g*finite_centered_cross xs w f g)*
                   /finite_centered_cross xs w g g).
   { apply Rmult_lt_0_compat; assumption. }
   lra.
Qed.

(**
 [finite_cov_optimal_variance_nonnegative] (theorem) — The closed-form finite Schur residual variance is nonnegative under nonnegative sample weights.
 Mathematical meaning: The closed-form finite Schur residual variance is nonnegative under nonnegative sample weights.
 Exact checked proposition: forall (A:Type) (xs:list A) (w f g:A->R), finite_weight_mass xs w<>0 -> finite_centered_cross xs w g g<>0 -> (forall x, In x xs -> 0<=w x) -> 0<=finite_cov_optimal_variance xs w f g.
 Premises and side conditions: Nonnegative sample weights and nonzero total mass and feature centered variance.
 Proof/definition method: Reuse previously established exact finite centered covariance, weighted Cauchy–Schwarz, covariance bilinearity and the scalar normal equations. Reduce regression objective to its completed square and explicitly discharge positive denominators and risk bounds.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, real field/ring, finite-sum and covariance library lemmas, and no custom matrix inversion or new sample enumeration recursion.
 Boundary: Exact finite weighted covariance and best linear predictor identities only; no Gaussian conditional laws, numerical integration correctness, psychometric population evidence or normality of test scores is established.
 *)
Theorem finite_cov_optimal_variance_nonnegative :
 forall (A:Type) (xs:list A) (w f g:A->R), finite_weight_mass xs w<>0 -> finite_centered_cross xs w g g<>0 -> (forall x, In x xs -> 0<=w x) -> 0<=finite_cov_optimal_variance xs w f g.
Proof.
 intros A xs w f g Hm Hv Hw.
 rewrite <- (finite_cov_residual_variance_at_slope A xs w f g Hm Hv).
 apply finite_cov_residual_variance_nonnegative; exact Hw.
Qed.

(**
 [finite_cov_optimal_variance_interval] (theorem) — Finite optimized residual variance lies between zero and the original target variance.
 Mathematical meaning: Finite optimized residual variance lies between zero and the original target variance.
 Exact checked proposition: forall (A:Type) (xs:list A) (w f g:A->R), finite_weight_mass xs w<>0 -> 0<finite_centered_cross xs w g g -> (forall x, In x xs -> 0<=w x) -> 0<=finite_cov_optimal_variance xs w f g /\ finite_cov_optimal_variance xs w f g<=finite_centered_cross xs w f f.
 Premises and side conditions: Nonnegative weights, positive feature variance and nonzero total mass.
 Proof/definition method: Reuse previously established exact finite centered covariance, weighted Cauchy–Schwarz, covariance bilinearity and the scalar normal equations. Reduce regression objective to its completed square and explicitly discharge positive denominators and risk bounds.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, real field/ring, finite-sum and covariance library lemmas, and no custom matrix inversion or new sample enumeration recursion.
 Boundary: Exact finite weighted covariance and best linear predictor identities only; no Gaussian conditional laws, numerical integration correctness, psychometric population evidence or normality of test scores is established.
 *)
Theorem finite_cov_optimal_variance_interval :
 forall (A:Type) (xs:list A) (w f g:A->R), finite_weight_mass xs w<>0 -> 0<finite_centered_cross xs w g g -> (forall x, In x xs -> 0<=w x) -> 0<=finite_cov_optimal_variance xs w f g /\ finite_cov_optimal_variance xs w f g<=finite_centered_cross xs w f f.
Proof.
 intros A xs w f g Hm Hv Hw; split.
 - apply finite_cov_optimal_variance_nonnegative; try assumption; lra.
 - rewrite <- (finite_cov_residual_variance_at_slope A xs w f g Hm ltac:(lra)).
   apply finite_cov_explained_variance_nonnegative; assumption.
Qed.

(**
 [finite_cov_optimal_target_translation] (theorem) — The best attainable finite linear-regression variance is invariant under an additive target-score shift.
 Mathematical meaning: The best attainable finite linear-regression variance is invariant under an additive target-score shift.
 Exact checked proposition: forall (A:Type) (xs:list A) (w f g:A->R) (d:R), finite_weight_mass xs w<>0 -> finite_cov_optimal_variance xs w (fun x=>f x+d) g=finite_cov_optimal_variance xs w f g.
 Premises and side conditions: Nonzero total weight mass is required for finite mean and covariance linearity.
 Proof/definition method: Reuse previously established exact finite centered covariance, weighted Cauchy–Schwarz, covariance bilinearity and the scalar normal equations. Reduce regression objective to its completed square and explicitly discharge positive denominators and risk bounds.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, real field/ring, finite-sum and covariance library lemmas, and no custom matrix inversion or new sample enumeration recursion.
 Boundary: Exact finite weighted covariance and best linear predictor identities only; no Gaussian conditional laws, numerical integration correctness, psychometric population evidence or normality of test scores is established.
 *)
Theorem finite_cov_optimal_target_translation :
 forall (A:Type) (xs:list A) (w f g:A->R) (d:R), finite_weight_mass xs w<>0 -> finite_cov_optimal_variance xs w (fun x=>f x+d) g=finite_cov_optimal_variance xs w f g.
Proof.
 intros A xs w f g d Hm; unfold finite_cov_optimal_variance.
 rewrite (finite_centered_shift_first A xs w f (fun x=>f x+d) d Hm).
 rewrite (finite_centered_shift_second A xs w f f d Hm).
 rewrite (finite_centered_shift_first A xs w f g d Hm).
 reflexivity.
Qed.

(**
 [finite_cov_optimal_feature_translation] (theorem) — The best attainable finite linear-regression variance is invariant under an additive feature-score shift.
 Mathematical meaning: The best attainable finite linear-regression variance is invariant under an additive feature-score shift.
 Exact checked proposition: forall (A:Type) (xs:list A) (w f g:A->R) (d:R), finite_weight_mass xs w<>0 -> finite_cov_optimal_variance xs w f (fun x=>g x+d)=finite_cov_optimal_variance xs w f g.
 Premises and side conditions: Nonzero total weight mass is required for finite mean and covariance linearity.
 Proof/definition method: Reuse previously established exact finite centered covariance, weighted Cauchy–Schwarz, covariance bilinearity and the scalar normal equations. Reduce regression objective to its completed square and explicitly discharge positive denominators and risk bounds.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, real field/ring, finite-sum and covariance library lemmas, and no custom matrix inversion or new sample enumeration recursion.
 Boundary: Exact finite weighted covariance and best linear predictor identities only; no Gaussian conditional laws, numerical integration correctness, psychometric population evidence or normality of test scores is established.
 *)
Theorem finite_cov_optimal_feature_translation :
 forall (A:Type) (xs:list A) (w f g:A->R) (d:R), finite_weight_mass xs w<>0 -> finite_cov_optimal_variance xs w f (fun x=>g x+d)=finite_cov_optimal_variance xs w f g.
Proof.
 intros A xs w f g d Hm; unfold finite_cov_optimal_variance.
 rewrite (finite_centered_shift_second A xs w f g d Hm).
 rewrite (finite_centered_shift_first A xs w g (fun x=>g x+d) d Hm).
 rewrite (finite_centered_shift_second A xs w g g d Hm).
 reflexivity.
Qed.


(* D032x: exact equality and strictness cases for finite two-score
   covariance determinants and supported affine regression. *)

(**
 [finite_regression_residual_zero_iff_affine_support] (theorem) — Zero finite least-squares residual variance for a fixed slope is equivalent to an affine target-feature relation on every outcome with strictly positive weight.
 Mathematical meaning: Zero finite least-squares residual variance for a fixed slope is equivalent to an affine target-feature relation on every outcome with strictly positive weight.
 Exact checked proposition: forall (A:Type) (xs:list A) (w f g:A->R) (b:R), finite_weight_mass xs w<>0 -> (forall x, In x xs -> 0<=w x) -> (finite_cov_residual_variance xs w f g b=0 <-> forall x, In x xs -> 0<w x -> f x=b*g x+(finite_weighted_mean xs w f-b*finite_weighted_mean xs w g)).
 Premises and side conditions: Nonzero total sample weight; every listed weight nonnegative; support means strictly positive weight.
 Proof/definition method: Combine existing finite weighted Cauchy–Schwarz, zero-variance iff supported constancy, finite covariance-ratio least-squares optimality, algebraic determinant normal equations, and positivity of squared residuals. Reuse the Rocq library instead of defining an alternate finite enumerator or covariance structure.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, List, classical real equality, field/ring tactics, FiniteSum and FiniteConditionalCovariance previous kernel lemmas.
 Boundary: Exact finite weighted sample and best-linear projection algebra only; no continuous Gaussian conditional distributions, normal-tail integrals, empirical IQ score calibration, or test-population correlations are verified.
 *)
Theorem finite_regression_residual_zero_iff_affine_support :
 forall (A:Type) (xs:list A) (w f g:A->R) (b:R), finite_weight_mass xs w<>0 -> (forall x, In x xs -> 0<=w x) ->
 (finite_cov_residual_variance xs w f g b=0 <->
  forall x, In x xs -> 0<w x -> f x=b*g x+(finite_weighted_mean xs w f-b*finite_weighted_mean xs w g)).
Proof.
 intros A xs w f g b Hm Hw.
 unfold finite_cov_residual_variance.
 rewrite (finite_centered_variance_zero_iff_supported_constant
   A xs w (fun x=>f x-b*g x) Hw).
 rewrite (finite_weighted_mean_sub A xs w f (fun x=>b*g x) Hm).
 rewrite (finite_weighted_mean_scale A xs w g b Hm).
 split; intros H x Hin Hpos; specialize (H x Hin Hpos); lra.
Qed.

(**
 [finite_regression_optimal_zero_iff_affine_support] (theorem) — The optimal one-feature Schur residual vanishes exactly when target scores are affine in the feature on all positive-weight outcomes.
 Mathematical meaning: The optimal one-feature Schur residual vanishes exactly when target scores are affine in the feature on all positive-weight outcomes.
 Exact checked proposition: forall (A:Type) (xs:list A) (w f g:A->R), finite_weight_mass xs w<>0 -> 0<finite_centered_cross xs w g g -> (forall x, In x xs -> 0<=w x) -> (finite_cov_optimal_variance xs w f g=0 <-> forall x, In x xs -> 0<w x -> f x=finite_cov_slope xs w f g*g x+ (finite_weighted_mean xs w f- finite_cov_slope xs w f g*finite_weighted_mean xs w g)).
 Premises and side conditions: Nonzero mass, nonnegative outcome weights and positive finite feature variance.
 Proof/definition method: Combine existing finite weighted Cauchy–Schwarz, zero-variance iff supported constancy, finite covariance-ratio least-squares optimality, algebraic determinant normal equations, and positivity of squared residuals. Reuse the Rocq library instead of defining an alternate finite enumerator or covariance structure.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, List, classical real equality, field/ring tactics, FiniteSum and FiniteConditionalCovariance previous kernel lemmas.
 Boundary: Exact finite weighted sample and best-linear projection algebra only; no continuous Gaussian conditional distributions, normal-tail integrals, empirical IQ score calibration, or test-population correlations are verified.
 *)
Theorem finite_regression_optimal_zero_iff_affine_support :
 forall (A:Type) (xs:list A) (w f g:A->R), finite_weight_mass xs w<>0 -> 0<finite_centered_cross xs w g g ->
 (forall x, In x xs -> 0<=w x) ->
 (finite_cov_optimal_variance xs w f g=0 <->
  forall x, In x xs -> 0<w x ->
    f x=finite_cov_slope xs w f g*g x+
      (finite_weighted_mean xs w f-
       finite_cov_slope xs w f g*finite_weighted_mean xs w g)).
Proof.
 intros A xs w f g Hm Hv Hw.
 rewrite <- (finite_cov_residual_variance_at_slope A xs w f g Hm ltac:(lra)).
 apply finite_regression_residual_zero_iff_affine_support; assumption.
Qed.

(**
 [finite_regression_optimal_positive_iff_nonaffine] (theorem) — Best finite linear prediction has strictly positive residual exactly when some supported outcome violates its optimal affine prediction.
 Mathematical meaning: Best finite linear prediction has strictly positive residual exactly when some supported outcome violates its optimal affine prediction.
 Exact checked proposition: forall (A:Type) (xs:list A) (w f g:A->R), finite_weight_mass xs w<>0 -> 0<finite_centered_cross xs w g g -> (forall x, In x xs -> 0<=w x) -> (0<finite_cov_optimal_variance xs w f g <-> exists x, In x xs /\ 0<w x /\ f x<>finite_cov_slope xs w f g*g x+ (finite_weighted_mean xs w f- finite_cov_slope xs w f g*finite_weighted_mean xs w g)).
 Premises and side conditions: Positive feature variance, nonnegative weights, and a supported non-affine observation.
 Proof/definition method: Combine existing finite weighted Cauchy–Schwarz, zero-variance iff supported constancy, finite covariance-ratio least-squares optimality, algebraic determinant normal equations, and positivity of squared residuals. Reuse the Rocq library instead of defining an alternate finite enumerator or covariance structure.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, List, classical real equality, field/ring tactics, FiniteSum and FiniteConditionalCovariance previous kernel lemmas.
 Boundary: Exact finite weighted sample and best-linear projection algebra only; no continuous Gaussian conditional distributions, normal-tail integrals, empirical IQ score calibration, or test-population correlations are verified.
 *)
Theorem finite_regression_optimal_positive_iff_nonaffine :
 forall (A:Type) (xs:list A) (w f g:A->R), finite_weight_mass xs w<>0 -> 0<finite_centered_cross xs w g g ->
 (forall x, In x xs -> 0<=w x) ->
 (0<finite_cov_optimal_variance xs w f g <->
   exists x, In x xs /\ 0<w x /\
   f x<>finite_cov_slope xs w f g*g x+
    (finite_weighted_mean xs w f-
       finite_cov_slope xs w f g*finite_weighted_mean xs w g)).
Proof.
 intros A xs w f g Hm Hv Hw.
 pose proof (finite_cov_optimal_variance_nonnegative A xs w f g Hm ltac:(lra) Hw) as Hnon.
 pose proof (finite_regression_optimal_zero_iff_affine_support
   A xs w f g Hm Hv Hw) as Hzero.
 split.
 - intro Hpos.
   apply NNPP; intro Hnone.
   assert (Hall: forall x, In x xs -> 0<w x ->
     f x=finite_cov_slope xs w f g*g x+
    (finite_weighted_mean xs w f-
       finite_cov_slope xs w f g*finite_weighted_mean xs w g)).
   { intros x Hin Hwx.
     destruct (Req_EM_T (f x) (finite_cov_slope xs w f g*g x+
       (finite_weighted_mean xs w f-
        finite_cov_slope xs w f g*finite_weighted_mean xs w g))) as [Heq|Hneq].
     - exact Heq.
     - exfalso; apply Hnone; exists x; repeat split; assumption. }
   apply (proj2 Hzero) in Hall; lra.
 - intros [x [Hin [Hwx Hneq]]].
   destruct (Req_EM_T (finite_cov_optimal_variance xs w f g) 0) as [Hz|Hz].
   + apply (proj1 Hzero) in Hz; exfalso; apply Hneq; apply Hz; assumption.
   + lra.
Qed.

(**
 [finite_regression_det_residual_identity] (theorem) — The finite covariance Gram determinant equals feature variance multiplied by optimal regression residual variance.
 Mathematical meaning: The finite covariance Gram determinant equals feature variance multiplied by optimal regression residual variance.
 Exact checked proposition: forall (A:Type) (xs:list A) (w f g:A->R), finite_centered_cross xs w g g<>0 -> finite_centered_cross xs w g g*finite_cov_optimal_variance xs w f g= finite_centered_cross xs w f f*finite_centered_cross xs w g g- finite_centered_cross xs w f g*finite_centered_cross xs w f g.
 Premises and side conditions: Feature variance is nonzero; the identity is otherwise unnormalized real finite covariance algebra.
 Proof/definition method: Combine existing finite weighted Cauchy–Schwarz, zero-variance iff supported constancy, finite covariance-ratio least-squares optimality, algebraic determinant normal equations, and positivity of squared residuals. Reuse the Rocq library instead of defining an alternate finite enumerator or covariance structure.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, List, classical real equality, field/ring tactics, FiniteSum and FiniteConditionalCovariance previous kernel lemmas.
 Boundary: Exact finite weighted sample and best-linear projection algebra only; no continuous Gaussian conditional distributions, normal-tail integrals, empirical IQ score calibration, or test-population correlations are verified.
 *)
Theorem finite_regression_det_residual_identity :
 forall (A:Type) (xs:list A) (w f g:A->R), finite_centered_cross xs w g g<>0 ->
 finite_centered_cross xs w g g*finite_cov_optimal_variance xs w f g=
 finite_centered_cross xs w f f*finite_centered_cross xs w g g-
 finite_centered_cross xs w f g*finite_centered_cross xs w f g.
Proof.
 intros A xs w f g Hv.
 unfold finite_cov_optimal_variance; field; exact Hv.
Qed.

(**
 [finite_regression_det_zero_iff_exact] (theorem) — A vanishing two-score Gram determinant is equivalent to zero optimal one-feature Schur residual when the feature variance is positive.
 Mathematical meaning: A vanishing two-score Gram determinant is equivalent to zero optimal one-feature Schur residual when the feature variance is positive.
 Exact checked proposition: forall (A:Type) (xs:list A) (w f g:A->R), 0<finite_centered_cross xs w g g -> (finite_centered_cross xs w f f*finite_centered_cross xs w g g- finite_centered_cross xs w f g*finite_centered_cross xs w f g=0 <-> finite_cov_optimal_variance xs w f g=0).
 Premises and side conditions: Strictly positive feature centered variance.
 Proof/definition method: Combine existing finite weighted Cauchy–Schwarz, zero-variance iff supported constancy, finite covariance-ratio least-squares optimality, algebraic determinant normal equations, and positivity of squared residuals. Reuse the Rocq library instead of defining an alternate finite enumerator or covariance structure.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, List, classical real equality, field/ring tactics, FiniteSum and FiniteConditionalCovariance previous kernel lemmas.
 Boundary: Exact finite weighted sample and best-linear projection algebra only; no continuous Gaussian conditional distributions, normal-tail integrals, empirical IQ score calibration, or test-population correlations are verified.
 *)
Theorem finite_regression_det_zero_iff_exact :
 forall (A:Type) (xs:list A) (w f g:A->R), 0<finite_centered_cross xs w g g ->
 (finite_centered_cross xs w f f*finite_centered_cross xs w g g-
 finite_centered_cross xs w f g*finite_centered_cross xs w f g=0
  <-> finite_cov_optimal_variance xs w f g=0).
Proof.
 intros A xs w f g Hv.
 pose proof (finite_regression_det_residual_identity A xs w f g ltac:(lra)) as He.
 split; intro H; nra.
Qed.

(**
 [finite_regression_det_positive_iff_residual_positive] (theorem) — The finite covariance Gram determinant is strictly positive exactly when the best one-feature residual variance is strictly positive.
 Mathematical meaning: The finite covariance Gram determinant is strictly positive exactly when the best one-feature residual variance is strictly positive.
 Exact checked proposition: forall (A:Type) (xs:list A) (w f g:A->R), 0<finite_centered_cross xs w g g -> (0<finite_centered_cross xs w f f*finite_centered_cross xs w g g- finite_centered_cross xs w f g*finite_centered_cross xs w f g <-> 0<finite_cov_optimal_variance xs w f g).
 Premises and side conditions: Strictly positive feature variance.
 Proof/definition method: Combine existing finite weighted Cauchy–Schwarz, zero-variance iff supported constancy, finite covariance-ratio least-squares optimality, algebraic determinant normal equations, and positivity of squared residuals. Reuse the Rocq library instead of defining an alternate finite enumerator or covariance structure.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, List, classical real equality, field/ring tactics, FiniteSum and FiniteConditionalCovariance previous kernel lemmas.
 Boundary: Exact finite weighted sample and best-linear projection algebra only; no continuous Gaussian conditional distributions, normal-tail integrals, empirical IQ score calibration, or test-population correlations are verified.
 *)
Theorem finite_regression_det_positive_iff_residual_positive :
 forall (A:Type) (xs:list A) (w f g:A->R), 0<finite_centered_cross xs w g g ->
 (0<finite_centered_cross xs w f f*finite_centered_cross xs w g g-
 finite_centered_cross xs w f g*finite_centered_cross xs w f g
  <-> 0<finite_cov_optimal_variance xs w f g).
Proof.
 intros A xs w f g Hv.
 pose proof (finite_regression_det_residual_identity A xs w f g ltac:(lra)) as He.
 split; intro H; nra.
Qed.

(**
 [finite_regression_det_zero_iff_affine_support] (theorem) — A singular finite two-score covariance matrix means the target is exactly affine in the feature on every positive-weight outcome.
 Mathematical meaning: A singular finite two-score covariance matrix means the target is exactly affine in the feature on every positive-weight outcome.
 Exact checked proposition: forall (A:Type) (xs:list A) (w f g:A->R), finite_weight_mass xs w<>0 -> 0<finite_centered_cross xs w g g -> (forall x, In x xs -> 0<=w x) -> (finite_centered_cross xs w f f*finite_centered_cross xs w g g- finite_centered_cross xs w f g*finite_centered_cross xs w f g=0 <-> forall x, In x xs -> 0<w x -> f x=finite_cov_slope xs w f g*g x+ (finite_weighted_mean xs w f- finite_cov_slope xs w f g*finite_weighted_mean xs w g)).
 Premises and side conditions: Nonnegative weights, nonzero total mass and positive feature variance.
 Proof/definition method: Combine existing finite weighted Cauchy–Schwarz, zero-variance iff supported constancy, finite covariance-ratio least-squares optimality, algebraic determinant normal equations, and positivity of squared residuals. Reuse the Rocq library instead of defining an alternate finite enumerator or covariance structure.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, List, classical real equality, field/ring tactics, FiniteSum and FiniteConditionalCovariance previous kernel lemmas.
 Boundary: Exact finite weighted sample and best-linear projection algebra only; no continuous Gaussian conditional distributions, normal-tail integrals, empirical IQ score calibration, or test-population correlations are verified.
 *)
Theorem finite_regression_det_zero_iff_affine_support :
 forall (A:Type) (xs:list A) (w f g:A->R), finite_weight_mass xs w<>0 -> 0<finite_centered_cross xs w g g ->
 (forall x, In x xs -> 0<=w x) ->
 (finite_centered_cross xs w f f*finite_centered_cross xs w g g-
  finite_centered_cross xs w f g*finite_centered_cross xs w f g=0
  <-> forall x, In x xs -> 0<w x ->
   f x=finite_cov_slope xs w f g*g x+
     (finite_weighted_mean xs w f-
      finite_cov_slope xs w f g*finite_weighted_mean xs w g)).
Proof.
 intros A xs w f g Hm Hv Hw.
 rewrite (finite_regression_det_zero_iff_exact A xs w f g Hv).
 apply finite_regression_optimal_zero_iff_affine_support; assumption.
Qed.

(**
 [finite_regression_det_positive_iff_nonaffine] (theorem) — The determinant is strictly positive exactly when some supported data point violates the optimal affine feature predictor.
 Mathematical meaning: The determinant is strictly positive exactly when some supported data point violates the optimal affine feature predictor.
 Exact checked proposition: forall (A:Type) (xs:list A) (w f g:A->R), finite_weight_mass xs w<>0 -> 0<finite_centered_cross xs w g g -> (forall x, In x xs -> 0<=w x) -> (0<finite_centered_cross xs w f f*finite_centered_cross xs w g g- finite_centered_cross xs w f g*finite_centered_cross xs w f g <-> exists x, In x xs /\ 0<w x /\ f x<>finite_cov_slope xs w f g*g x+ (finite_weighted_mean xs w f- finite_cov_slope xs w f g*finite_weighted_mean xs w g)).
 Premises and side conditions: Nonnegative sample weights, nonzero mass, and strictly positive feature variance.
 Proof/definition method: Combine existing finite weighted Cauchy–Schwarz, zero-variance iff supported constancy, finite covariance-ratio least-squares optimality, algebraic determinant normal equations, and positivity of squared residuals. Reuse the Rocq library instead of defining an alternate finite enumerator or covariance structure.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, List, classical real equality, field/ring tactics, FiniteSum and FiniteConditionalCovariance previous kernel lemmas.
 Boundary: Exact finite weighted sample and best-linear projection algebra only; no continuous Gaussian conditional distributions, normal-tail integrals, empirical IQ score calibration, or test-population correlations are verified.
 *)
Theorem finite_regression_det_positive_iff_nonaffine :
 forall (A:Type) (xs:list A) (w f g:A->R), finite_weight_mass xs w<>0 -> 0<finite_centered_cross xs w g g ->
 (forall x, In x xs -> 0<=w x) ->
 (0<finite_centered_cross xs w f f*finite_centered_cross xs w g g-
  finite_centered_cross xs w f g*finite_centered_cross xs w f g
  <-> exists x, In x xs /\ 0<w x /\
  f x<>finite_cov_slope xs w f g*g x+
     (finite_weighted_mean xs w f-
      finite_cov_slope xs w f g*finite_weighted_mean xs w g)).
Proof.
 intros A xs w f g Hm Hv Hw.
 rewrite (finite_regression_det_positive_iff_residual_positive A xs w f g Hv).
 apply finite_regression_optimal_positive_iff_nonaffine; assumption.
Qed.

(**
 [finite_regression_det_nonnegative] (theorem) — Nonnegative finite weights force the two-score covariance Gram determinant to be nonnegative.
 Mathematical meaning: Nonnegative finite weights force the two-score covariance Gram determinant to be nonnegative.
 Exact checked proposition: forall (A:Type) (xs:list A) (w f g:A->R), (forall x, In x xs -> 0<=w x) -> 0<=finite_centered_cross xs w f f*finite_centered_cross xs w g g- finite_centered_cross xs w f g*finite_centered_cross xs w f g.
 Premises and side conditions: Nonnegative weights on every enumerated outcome, with no mass normalization.
 Proof/definition method: Combine existing finite weighted Cauchy–Schwarz, zero-variance iff supported constancy, finite covariance-ratio least-squares optimality, algebraic determinant normal equations, and positivity of squared residuals. Reuse the Rocq library instead of defining an alternate finite enumerator or covariance structure.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, List, classical real equality, field/ring tactics, FiniteSum and FiniteConditionalCovariance previous kernel lemmas.
 Boundary: Exact finite weighted sample and best-linear projection algebra only; no continuous Gaussian conditional distributions, normal-tail integrals, empirical IQ score calibration, or test-population correlations are verified.
 *)
Theorem finite_regression_det_nonnegative :
 forall (A:Type) (xs:list A) (w f g:A->R), (forall x, In x xs -> 0<=w x) ->
 0<=finite_centered_cross xs w f f*finite_centered_cross xs w g g-
 finite_centered_cross xs w f g*finite_centered_cross xs w f g.
Proof.
 intros A xs w f g Hw.
 pose proof (finite_centered_cauchy_schwarz A xs w f g Hw) as Hcs.
 lra.
Qed.

(**
 [finite_regression_target_variance_positive_if_cross] (theorem) — If finite target-feature covariance is nonzero, then target variance is strictly positive.
 Mathematical meaning: If finite target-feature covariance is nonzero, then target variance is strictly positive.
 Exact checked proposition: forall (A:Type) (xs:list A) (w f g:A->R), (forall x, In x xs -> 0<=w x) -> finite_centered_cross xs w f g<>0 -> 0<finite_centered_cross xs w f f.
 Premises and side conditions: All enumerated weights nonnegative and covariance nonzero.
 Proof/definition method: Combine existing finite weighted Cauchy–Schwarz, zero-variance iff supported constancy, finite covariance-ratio least-squares optimality, algebraic determinant normal equations, and positivity of squared residuals. Reuse the Rocq library instead of defining an alternate finite enumerator or covariance structure.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, List, classical real equality, field/ring tactics, FiniteSum and FiniteConditionalCovariance previous kernel lemmas.
 Boundary: Exact finite weighted sample and best-linear projection algebra only; no continuous Gaussian conditional distributions, normal-tail integrals, empirical IQ score calibration, or test-population correlations are verified.
 *)
Theorem finite_regression_target_variance_positive_if_cross :
 forall (A:Type) (xs:list A) (w f g:A->R), (forall x, In x xs -> 0<=w x) ->
 finite_centered_cross xs w f g<>0 ->
 0<finite_centered_cross xs w f f.
Proof.
 intros A xs w f g Hw Hnz.
 pose proof (finite_centered_cauchy_schwarz A xs w f g Hw) as Hcs.
 pose proof (finite_centered_variance_nonnegative A xs w f Hw) as Hf.
 pose proof (finite_centered_variance_nonnegative A xs w g Hw) as Hg.
 nra.
Qed.

(**
 [finite_regression_feature_variance_positive_if_cross] (theorem) — If covariance with the target is nonzero, the feature has strictly positive finite variance.
 Mathematical meaning: If covariance with the target is nonzero, the feature has strictly positive finite variance.
 Exact checked proposition: forall (A:Type) (xs:list A) (w f g:A->R), (forall x, In x xs -> 0<=w x) -> finite_centered_cross xs w f g<>0 -> 0<finite_centered_cross xs w g g.
 Premises and side conditions: All enumerated weights nonnegative and target-feature covariance nonzero.
 Proof/definition method: Combine existing finite weighted Cauchy–Schwarz, zero-variance iff supported constancy, finite covariance-ratio least-squares optimality, algebraic determinant normal equations, and positivity of squared residuals. Reuse the Rocq library instead of defining an alternate finite enumerator or covariance structure.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, List, classical real equality, field/ring tactics, FiniteSum and FiniteConditionalCovariance previous kernel lemmas.
 Boundary: Exact finite weighted sample and best-linear projection algebra only; no continuous Gaussian conditional distributions, normal-tail integrals, empirical IQ score calibration, or test-population correlations are verified.
 *)
Theorem finite_regression_feature_variance_positive_if_cross :
 forall (A:Type) (xs:list A) (w f g:A->R), (forall x, In x xs -> 0<=w x) ->
 finite_centered_cross xs w f g<>0 ->
 0<finite_centered_cross xs w g g.
Proof.
 intros A xs w f g Hw Hnz.
 pose proof (finite_centered_cauchy_schwarz A xs w f g Hw) as Hcs.
 pose proof (finite_centered_variance_nonnegative A xs w f Hw) as Hf.
 pose proof (finite_centered_variance_nonnegative A xs w g Hw) as Hg.
 nra.
Qed.

(**
 [finite_regression_exact_zero_if_affine_witness] (theorem) — Any explicit affine relation between a finite target and feature on positive-weight outcomes forces zero optimal regression risk.
 Mathematical meaning: Any explicit affine relation between a finite target and feature on positive-weight outcomes forces zero optimal regression risk.
 Exact checked proposition: forall (A:Type) (xs:list A) (w f g:A->R) (a b:R), finite_weight_mass xs w<>0 -> 0<finite_centered_cross xs w g g -> (forall x, In x xs -> 0<=w x) -> (forall x, In x xs -> 0<w x -> f x=a+b*g x) -> finite_cov_optimal_variance xs w f g=0.
 Premises and side conditions: Finite nonnegative sample weights, positive feature variance, and supportwise affine equality.
 Proof/definition method: Combine existing finite weighted Cauchy–Schwarz, zero-variance iff supported constancy, finite covariance-ratio least-squares optimality, algebraic determinant normal equations, and positivity of squared residuals. Reuse the Rocq library instead of defining an alternate finite enumerator or covariance structure.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, List, classical real equality, field/ring tactics, FiniteSum and FiniteConditionalCovariance previous kernel lemmas.
 Boundary: Exact finite weighted sample and best-linear projection algebra only; no continuous Gaussian conditional distributions, normal-tail integrals, empirical IQ score calibration, or test-population correlations are verified.
 *)
Theorem finite_regression_exact_zero_if_affine_witness :
 forall (A:Type) (xs:list A) (w f g:A->R) (a b:R), finite_weight_mass xs w<>0 ->
 0<finite_centered_cross xs w g g ->
 (forall x, In x xs -> 0<=w x) ->
 (forall x, In x xs -> 0<w x -> f x=a+b*g x) ->
 finite_cov_optimal_variance xs w f g=0.
Proof.
 intros A xs w f g a b Hm Hv Hw Haff.
 assert (Hvar:0<=finite_cov_residual_variance xs w f g b).
 { apply finite_cov_residual_variance_nonnegative; exact Hw. }
 assert (Hmean:finite_weighted_mean xs w f=a+b*finite_weighted_mean xs w g).
 { assert (Hscore:finite_weighted_score xs w f =
       finite_weighted_score xs w (fun x=>a+b*g x)).
   { unfold finite_weighted_score.
     apply finite_sum_ext_in; intros x Hin.
     destruct (Rlt_dec 0 (w x)) as [Hpos|Hnot].
     - rewrite (Haff x Hin Hpos); reflexivity.
     - assert (Hz:w x=0) by (pose proof (Hw x Hin); lra).
       rewrite Hz; ring. }
   unfold finite_weighted_mean.
   rewrite Hscore.
   rewrite (finite_weighted_score_affine A xs w g b a).
   pose proof (finite_weighted_mean_mass_identity A xs w g Hm) as He.
   unfold finite_weighted_mean in He.
   field_simplify; try assumption.
   nra. }
 assert (Hres:finite_cov_residual_variance xs w f g b=0).
 { apply (proj2 (finite_regression_residual_zero_iff_affine_support
       A xs w f g b Hm Hw)).
   intros x Hin Hpos; rewrite (Haff x Hin Hpos), Hmean; ring. }
 pose proof (finite_cov_slope_global_optimality A xs w f g b Hm Hv) as Hopt.
 assert (Hnon:0<=finite_cov_optimal_variance xs w f g)
   by (apply finite_cov_optimal_variance_nonnegative; try assumption; lra).
 rewrite <- (finite_cov_residual_variance_at_slope A xs w f g Hm ltac:(lra)) in Hnon.
 rewrite <- (finite_cov_residual_variance_at_slope A xs w f g Hm ltac:(lra)).
 lra.
Qed.

(**
 [finite_regression_det_swap] (theorem) — The finite two-score covariance Gram determinant is invariant under exchanging target and feature.
 Mathematical meaning: The finite two-score covariance Gram determinant is invariant under exchanging target and feature.
 Exact checked proposition: forall (A:Type) (xs:list A) (w f g:A->R), finite_centered_cross xs w f f*finite_centered_cross xs w g g- finite_centered_cross xs w f g*finite_centered_cross xs w f g= finite_centered_cross xs w g g*finite_centered_cross xs w f f- finite_centered_cross xs w g f*finite_centered_cross xs w g f.
 Premises and side conditions: No positivity or normalization condition is required for determinant symmetry.
 Proof/definition method: Combine existing finite weighted Cauchy–Schwarz, zero-variance iff supported constancy, finite covariance-ratio least-squares optimality, algebraic determinant normal equations, and positivity of squared residuals. Reuse the Rocq library instead of defining an alternate finite enumerator or covariance structure.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, List, classical real equality, field/ring tactics, FiniteSum and FiniteConditionalCovariance previous kernel lemmas.
 Boundary: Exact finite weighted sample and best-linear projection algebra only; no continuous Gaussian conditional distributions, normal-tail integrals, empirical IQ score calibration, or test-population correlations are verified.
 *)
Theorem finite_regression_det_swap :
 forall (A:Type) (xs:list A) (w f g:A->R),
 finite_centered_cross xs w f f*finite_centered_cross xs w g g-
 finite_centered_cross xs w f g*finite_centered_cross xs w f g=
 finite_centered_cross xs w g g*finite_centered_cross xs w f f-
 finite_centered_cross xs w g f*finite_centered_cross xs w g f.
Proof.
 intros A xs w f g.
 rewrite (finite_centered_cross_symmetric A xs w g f); ring.
Qed.

(**
 [finite_regression_slope_reciprocal_covariance] (theorem) — The cross-covariance normal equations for the two regression orientations identify their shared numerator.
 Mathematical meaning: The cross-covariance normal equations for the two regression orientations identify their shared numerator.
 Exact checked proposition: forall (A:Type) (xs:list A) (w f g:A->R), finite_centered_cross xs w f f<>0 -> finite_centered_cross xs w g g<>0 -> finite_cov_slope xs w f g*finite_centered_cross xs w g g= finite_cov_slope xs w g f*finite_centered_cross xs w f f.
 Premises and side conditions: Both target and feature variances nonzero.
 Proof/definition method: Combine existing finite weighted Cauchy–Schwarz, zero-variance iff supported constancy, finite covariance-ratio least-squares optimality, algebraic determinant normal equations, and positivity of squared residuals. Reuse the Rocq library instead of defining an alternate finite enumerator or covariance structure.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, List, classical real equality, field/ring tactics, FiniteSum and FiniteConditionalCovariance previous kernel lemmas.
 Boundary: Exact finite weighted sample and best-linear projection algebra only; no continuous Gaussian conditional distributions, normal-tail integrals, empirical IQ score calibration, or test-population correlations are verified.
 *)
Theorem finite_regression_slope_reciprocal_covariance :
 forall (A:Type) (xs:list A) (w f g:A->R), finite_centered_cross xs w f f<>0 ->
 finite_centered_cross xs w g g<>0 ->
 finite_cov_slope xs w f g*finite_centered_cross xs w g g=
 finite_cov_slope xs w g f*finite_centered_cross xs w f f.
Proof.
 intros A xs w f g Hf Hg.
 rewrite (finite_cov_slope_variance_identity A xs w f g Hg).
 rewrite (finite_cov_slope_variance_identity A xs w g f Hf).
 apply finite_centered_cross_symmetric.
Qed.

(**
 [finite_regression_slope_zero_both_orientations] (theorem) — For nondegenerate finite target and feature, either directional regression coefficient vanishes exactly when the other does.
 Mathematical meaning: For nondegenerate finite target and feature, either directional regression coefficient vanishes exactly when the other does.
 Exact checked proposition: forall (A:Type) (xs:list A) (w f g:A->R), 0<finite_centered_cross xs w f f -> 0<finite_centered_cross xs w g g -> (finite_cov_slope xs w f g=0 <-> finite_cov_slope xs w g f=0).
 Premises and side conditions: Both covariance diagonal variances strictly positive.
 Proof/definition method: Combine existing finite weighted Cauchy–Schwarz, zero-variance iff supported constancy, finite covariance-ratio least-squares optimality, algebraic determinant normal equations, and positivity of squared residuals. Reuse the Rocq library instead of defining an alternate finite enumerator or covariance structure.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, List, classical real equality, field/ring tactics, FiniteSum and FiniteConditionalCovariance previous kernel lemmas.
 Boundary: Exact finite weighted sample and best-linear projection algebra only; no continuous Gaussian conditional distributions, normal-tail integrals, empirical IQ score calibration, or test-population correlations are verified.
 *)
Theorem finite_regression_slope_zero_both_orientations :
 forall (A:Type) (xs:list A) (w f g:A->R), 0<finite_centered_cross xs w f f ->
 0<finite_centered_cross xs w g g ->
 (finite_cov_slope xs w f g=0 <-> finite_cov_slope xs w g f=0).
Proof.
 intros A xs w f g Hf Hg.
 rewrite (finite_cov_slope_zero_iff A xs w f g Hg).
 rewrite (finite_cov_slope_zero_iff A xs w g f Hf).
 rewrite (finite_centered_cross_symmetric A xs w g f).
 tauto.
Qed.

(**
 [finite_regression_slope_positive_both_orientations] (theorem) — For nondegenerate finite target and feature, the two directional regression coefficients share a positive sign.
 Mathematical meaning: For nondegenerate finite target and feature, the two directional regression coefficients share a positive sign.
 Exact checked proposition: forall (A:Type) (xs:list A) (w f g:A->R), 0<finite_centered_cross xs w f f -> 0<finite_centered_cross xs w g g -> (0<finite_cov_slope xs w f g <-> 0<finite_cov_slope xs w g f).
 Premises and side conditions: Both covariance diagonal variances strictly positive.
 Proof/definition method: Combine existing finite weighted Cauchy–Schwarz, zero-variance iff supported constancy, finite covariance-ratio least-squares optimality, algebraic determinant normal equations, and positivity of squared residuals. Reuse the Rocq library instead of defining an alternate finite enumerator or covariance structure.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, List, classical real equality, field/ring tactics, FiniteSum and FiniteConditionalCovariance previous kernel lemmas.
 Boundary: Exact finite weighted sample and best-linear projection algebra only; no continuous Gaussian conditional distributions, normal-tail integrals, empirical IQ score calibration, or test-population correlations are verified.
 *)
Theorem finite_regression_slope_positive_both_orientations :
 forall (A:Type) (xs:list A) (w f g:A->R), 0<finite_centered_cross xs w f f ->
 0<finite_centered_cross xs w g g ->
 (0<finite_cov_slope xs w f g <-> 0<finite_cov_slope xs w g f).
Proof.
 intros A xs w f g Hf Hg.
 rewrite (finite_cov_slope_positive_iff A xs w f g Hg).
 rewrite (finite_cov_slope_positive_iff A xs w g f Hf).
 rewrite (finite_centered_cross_symmetric A xs w g f).
 tauto.
Qed.

(**
 [finite_regression_slope_negative_both_orientations] (theorem) — For nondegenerate finite target and feature, the two directional regression coefficients share a negative sign.
 Mathematical meaning: For nondegenerate finite target and feature, the two directional regression coefficients share a negative sign.
 Exact checked proposition: forall (A:Type) (xs:list A) (w f g:A->R), 0<finite_centered_cross xs w f f -> 0<finite_centered_cross xs w g g -> (finite_cov_slope xs w f g<0 <-> finite_cov_slope xs w g f<0).
 Premises and side conditions: Both covariance diagonal variances strictly positive.
 Proof/definition method: Combine existing finite weighted Cauchy–Schwarz, zero-variance iff supported constancy, finite covariance-ratio least-squares optimality, algebraic determinant normal equations, and positivity of squared residuals. Reuse the Rocq library instead of defining an alternate finite enumerator or covariance structure.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, List, classical real equality, field/ring tactics, FiniteSum and FiniteConditionalCovariance previous kernel lemmas.
 Boundary: Exact finite weighted sample and best-linear projection algebra only; no continuous Gaussian conditional distributions, normal-tail integrals, empirical IQ score calibration, or test-population correlations are verified.
 *)
Theorem finite_regression_slope_negative_both_orientations :
 forall (A:Type) (xs:list A) (w f g:A->R), 0<finite_centered_cross xs w f f ->
 0<finite_centered_cross xs w g g ->
 (finite_cov_slope xs w f g<0 <-> finite_cov_slope xs w g f<0).
Proof.
 intros A xs w f g Hf Hg.
 rewrite (finite_cov_slope_negative_iff A xs w f g Hg).
 rewrite (finite_cov_slope_negative_iff A xs w g f Hf).
 rewrite (finite_centered_cross_symmetric A xs w g f).
 tauto.
Qed.

(**
 [finite_regression_slope_product_identity] (theorem) — The product of the two directional finite regression slopes equals squared covariance normalized by the product of the two variances.
 Mathematical meaning: The product of the two directional finite regression slopes equals squared covariance normalized by the product of the two variances.
 Exact checked proposition: forall (A:Type) (xs:list A) (w f g:A->R), finite_centered_cross xs w f f<>0 -> finite_centered_cross xs w g g<>0 -> finite_cov_slope xs w f g*finite_cov_slope xs w g f= (finite_centered_cross xs w f g*finite_centered_cross xs w f g)/ (finite_centered_cross xs w f f*finite_centered_cross xs w g g).
 Premises and side conditions: Both variances nonzero, permitting correlation-squared-like normalization.
 Proof/definition method: Combine existing finite weighted Cauchy–Schwarz, zero-variance iff supported constancy, finite covariance-ratio least-squares optimality, algebraic determinant normal equations, and positivity of squared residuals. Reuse the Rocq library instead of defining an alternate finite enumerator or covariance structure.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, List, classical real equality, field/ring tactics, FiniteSum and FiniteConditionalCovariance previous kernel lemmas.
 Boundary: Exact finite weighted sample and best-linear projection algebra only; no continuous Gaussian conditional distributions, normal-tail integrals, empirical IQ score calibration, or test-population correlations are verified.
 *)
Theorem finite_regression_slope_product_identity :
 forall (A:Type) (xs:list A) (w f g:A->R), finite_centered_cross xs w f f<>0 ->
 finite_centered_cross xs w g g<>0 ->
 finite_cov_slope xs w f g*finite_cov_slope xs w g f=
 (finite_centered_cross xs w f g*finite_centered_cross xs w f g)/
 (finite_centered_cross xs w f f*finite_centered_cross xs w g g).
Proof.
 intros A xs w f g Hf Hg.
 unfold finite_cov_slope.
 rewrite (finite_centered_cross_symmetric A xs w g f).
 unfold Rdiv; field; split; assumption.
Qed.

(**
 [finite_regression_slope_product_unit_interval] (theorem) — Directional regression slopes yield a normalized nonnegative covariance product bounded above by one.
 Mathematical meaning: Directional regression slopes yield a normalized nonnegative covariance product bounded above by one.
 Exact checked proposition: forall (A:Type) (xs:list A) (w f g:A->R), (forall x, In x xs -> 0<=w x) -> 0<finite_centered_cross xs w f f -> 0<finite_centered_cross xs w g g -> 0<=finite_cov_slope xs w f g*finite_cov_slope xs w g f /\ finite_cov_slope xs w f g*finite_cov_slope xs w g f<=1.
 Premises and side conditions: Nonnegative sample weights and strictly positive variances in both orientations.
 Proof/definition method: Combine existing finite weighted Cauchy–Schwarz, zero-variance iff supported constancy, finite covariance-ratio least-squares optimality, algebraic determinant normal equations, and positivity of squared residuals. Reuse the Rocq library instead of defining an alternate finite enumerator or covariance structure.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, List, classical real equality, field/ring tactics, FiniteSum and FiniteConditionalCovariance previous kernel lemmas.
 Boundary: Exact finite weighted sample and best-linear projection algebra only; no continuous Gaussian conditional distributions, normal-tail integrals, empirical IQ score calibration, or test-population correlations are verified.
 *)
Theorem finite_regression_slope_product_unit_interval :
 forall (A:Type) (xs:list A) (w f g:A->R), (forall x, In x xs -> 0<=w x) ->
 0<finite_centered_cross xs w f f ->
 0<finite_centered_cross xs w g g ->
 0<=finite_cov_slope xs w f g*finite_cov_slope xs w g f /\
 finite_cov_slope xs w f g*finite_cov_slope xs w g f<=1.
Proof.
 intros A xs w f g Hw Hf Hg.
 pose proof (finite_centered_cauchy_schwarz A xs w f g Hw) as Hcs.
 rewrite (finite_regression_slope_product_identity A xs w f g ltac:(lra) ltac:(lra)).
 unfold Rdiv.
 assert (Hd:0<finite_centered_cross xs w f f*finite_centered_cross xs w g g)
   by (apply Rmult_lt_0_compat; assumption).
 assert (Hi:0< /(finite_centered_cross xs w f f*finite_centered_cross xs w g g))
   by (apply Rinv_0_lt_compat; exact Hd).
 split.
 - assert (Hs:0<=finite_centered_cross xs w f g*finite_centered_cross xs w f g)
     by (change (0<=Rsqr (finite_centered_cross xs w f g)); apply Rle_0_sqr).
   apply Rmult_le_pos; [exact Hs|lra].
 - assert (Hineq:0<=(finite_centered_cross xs w f f*finite_centered_cross xs w g g-
          finite_centered_cross xs w f g*finite_centered_cross xs w f g)*
          /(finite_centered_cross xs w f f*finite_centered_cross xs w g g)).
   { apply Rmult_le_pos; [lra|lra]. }
   assert (Hone: (finite_centered_cross xs w f f*finite_centered_cross xs w g g)*
        /(finite_centered_cross xs w f f*finite_centered_cross xs w g g)=1).
   { field; lra. }
   nra.
Qed.

