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
 transitivity (finite_sum (fun x=>
   weight x*(f x-a)*(f x-a) +
   2*(weight x*(f x-a)*(g x-b)) +
   weight x*(g x-b)*(g x-b)) xs).
 { apply finite_sum_ext; intro x; ring. }
 repeat rewrite finite_sum_add.
 rewrite finite_sum_scale.
 ring.
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
 reflexivity.
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
 reflexivity.
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

