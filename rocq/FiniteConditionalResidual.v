(** Module: FiniteConditionalResidual.v
 Purpose: Kernel-checked finite regression interpretation of the Boolean
 conditional-expectation model used by the composite-score reports.
 Establishes residual/fitted covariance orthogonality, exact total
 covariance as fitted-plus-residual decomposition, the identification
 of the between/within covariance terms with fitted/residual covariance,
 nonnegative risk, information monotonicity and uniqueness of prediction.
 Mathematical representation: Lists of explicit outcome occurrences,
 arbitrary real-valued weights and score functions, event : A -> bool.
 The shared FiniteSum.finite_sum and existing conditional projection,
 mean and covariance definitions implement all moments, with repeated
 list occurrences preserved exactly.
 Explicit hypotheses: Positive masses of both observed cells for
 normalized means and covariance regression identities; nonnegative
 per-observation weights wherever nonnegativity is asserted. Purely
 algebraic finite-list equations permit arbitrary signed weights when
 their nonzero denominators are explicitly assumed.
 Library use: Rocq Stdlib.List, Bool, Reals, Lra, Psatz, Ring,
 FunctionalExtensionality and maintained FiniteSum, FiniteTwoCellProjection,
 FiniteNestedProjection and FiniteConditionalCovariance modules. No
 new recursive summation, probabilistic axiom, Gaussian normal law
 or duplicate finite mean/covariance primitive is introduced.
 Limitations: Finite observed Boolean partitions only; no general
 sigma-algebra conditional expectation, Gaussian conditional
 distribution or empirical IQ evidence is asserted by these proofs.
 Reproduction: In Rocq 9.2, compile FiniteConditionalResidual.v after
 the three finite projection/covariance dependencies and FiniteSum.v
 using the pinned GitHub Actions Rocq kernel workflow.
 AI disclosure: Source and mathematical commentary were AI-authored;
 formal truth of the propositions requires independent Rocq kernel CI.
 *)
From Stdlib Require Import Reals Lra Psatz List Bool FunctionalExtensionality.
Require Import FiniteSum FiniteTwoCellProjection FiniteNestedProjection
               FiniteConditionalCovariance.
Import ListNotations.
Open Scope R_scope.

(**
 [finite_two_cell_residual] (definition) — The actual finite conditional prediction error after observing the Boolean event.
 Mathematical meaning: The actual finite conditional prediction error after observing the Boolean event.
 Exact declaration: Definition finite_two_cell_residual {A : Type} (xs : list A) (weight score : A -> R) (event : A -> bool) (x : A) : R := score x - finite_two_cell_prediction xs weight score event x.
 Premises and side conditions: All needed nonzero or positive Boolean cell masses are explicit at use sites; nonnegative individual outcome weights are required for order conclusions. There is no hidden continuity, normality or independence assumption.
 Proof/definition method: Transparent composition of checked conditional-score and centered-cross operators.
 Library reuse: Stdlib.List/FunctionalExtensionality/Reals/Lra/Ring, FiniteSum's exact list sums, previously kernel-checked two-cell projection, nested projection, and conditional covariance theorems.
 Boundary: Explicit finite occurrence lists with real weights and deterministic event partitions only; no arbitrary L1 conditional expectation, Gaussian conditioning, or empirical IQ claim.
 *)
Definition finite_two_cell_residual {A : Type}
 (xs : list A) (weight score : A -> R) (event : A -> bool)
 (x : A) : R :=
 score x - finite_two_cell_prediction xs weight score event x.

(**
 [finite_fitted_cross] (definition) — The centered cross-covariance numerator of the two conditional mean predictors.
 Mathematical meaning: The centered cross-covariance numerator of the two conditional mean predictors.
 Exact declaration: Definition finite_fitted_cross {A : Type} (xs : list A) (weight f g : A -> R) (event : A -> bool) : R := finite_centered_cross xs weight (finite_two_cell_prediction xs weight f event) (finite_two_cell_prediction xs weight g event).
 Premises and side conditions: All needed nonzero or positive Boolean cell masses are explicit at use sites; nonnegative individual outcome weights are required for order conclusions. There is no hidden continuity, normality or independence assumption.
 Proof/definition method: Transparent composition of checked conditional-score and centered-cross operators.
 Library reuse: Stdlib.List/FunctionalExtensionality/Reals/Lra/Ring, FiniteSum's exact list sums, previously kernel-checked two-cell projection, nested projection, and conditional covariance theorems.
 Boundary: Explicit finite occurrence lists with real weights and deterministic event partitions only; no arbitrary L1 conditional expectation, Gaussian conditioning, or empirical IQ claim.
 *)
Definition finite_fitted_cross {A : Type}
 (xs : list A) (weight f g : A -> R) (event : A -> bool) : R :=
 finite_centered_cross xs weight
  (finite_two_cell_prediction xs weight f event)
  (finite_two_cell_prediction xs weight g event).

(**
 [finite_residual_cross] (definition) — The centered cross-covariance numerator of two finite conditional prediction residuals.
 Mathematical meaning: The centered cross-covariance numerator of two finite conditional prediction residuals.
 Exact declaration: Definition finite_residual_cross {A : Type} (xs : list A) (weight f g : A -> R) (event : A -> bool) : R := finite_centered_cross xs weight (finite_two_cell_residual xs weight f event) (finite_two_cell_residual xs weight g event).
 Premises and side conditions: All needed nonzero or positive Boolean cell masses are explicit at use sites; nonnegative individual outcome weights are required for order conclusions. There is no hidden continuity, normality or independence assumption.
 Proof/definition method: Transparent composition of checked conditional-score and centered-cross operators.
 Library reuse: Stdlib.List/FunctionalExtensionality/Reals/Lra/Ring, FiniteSum's exact list sums, previously kernel-checked two-cell projection, nested projection, and conditional covariance theorems.
 Boundary: Explicit finite occurrence lists with real weights and deterministic event partitions only; no arbitrary L1 conditional expectation, Gaussian conditioning, or empirical IQ claim.
 *)
Definition finite_residual_cross {A : Type}
 (xs : list A) (weight f g : A -> R) (event : A -> bool) : R :=
 finite_centered_cross xs weight
  (finite_two_cell_residual xs weight f event)
  (finite_two_cell_residual xs weight g event).

(**
 [finite_two_cell_total_mass_positive] (theorem) — Positive masses in the event and its complement imply positive total sample weight.
 Mathematical meaning: Positive masses in the event and its complement imply positive total sample weight.
 Exact checked proposition: forall (A : Type) (xs : list A) (weight : A -> R) (event : A -> bool), 0 < finite_true_mass xs weight event -> 0 < finite_false_mass xs weight event -> 0 < finite_weight_mass xs weight.
 Premises and side conditions: All needed nonzero or positive Boolean cell masses are explicit at use sites; nonnegative individual outcome weights are required for order conclusions. There is no hidden continuity, normality or independence assumption.
 Proof/definition method: Compose existing exact projection/finite covariance identities, with explicit pointwise or real-ring normalization instead of new fold proofs.
 Library reuse: Stdlib.List/FunctionalExtensionality/Reals/Lra/Ring, FiniteSum's exact list sums, previously kernel-checked two-cell projection, nested projection, and conditional covariance theorems.
 Boundary: Explicit finite occurrence lists with real weights and deterministic event partitions only; no arbitrary L1 conditional expectation, Gaussian conditioning, or empirical IQ claim.
 *)
Theorem finite_two_cell_total_mass_positive :
 forall (A : Type) (xs : list A) (weight : A -> R) (event : A -> bool),
 0 < finite_true_mass xs weight event ->
 0 < finite_false_mass xs weight event ->
 0 < finite_weight_mass xs weight.
Proof.
 intros A xs weight event Ht Hf.
 pose proof (finite_two_cell_mass_partition A xs weight event) as Hp.
 lra.
Qed.

(**
 [finite_two_cell_residual_score_zero] (theorem) — The fitted two-cell prediction has residuals with exactly zero unnormalized first moment.
 Mathematical meaning: The fitted two-cell prediction has residuals with exactly zero unnormalized first moment.
 Exact checked proposition: forall (A : Type) (xs : list A) (weight score : A -> R) (event : A -> bool), finite_true_mass xs weight event <> 0 -> finite_false_mass xs weight event <> 0 -> finite_weighted_score xs weight (finite_two_cell_residual xs weight score event) = 0.
 Premises and side conditions: All needed nonzero or positive Boolean cell masses are explicit at use sites; nonnegative individual outcome weights are required for order conclusions. There is no hidden continuity, normality or independence assumption.
 Proof/definition method: Compose existing exact projection/finite covariance identities, with explicit pointwise or real-ring normalization instead of new fold proofs.
 Library reuse: Stdlib.List/FunctionalExtensionality/Reals/Lra/Ring, FiniteSum's exact list sums, previously kernel-checked two-cell projection, nested projection, and conditional covariance theorems.
 Boundary: Explicit finite occurrence lists with real weights and deterministic event partitions only; no arbitrary L1 conditional expectation, Gaussian conditioning, or empirical IQ claim.
 *)
Theorem finite_two_cell_residual_score_zero :
 forall (A : Type) (xs : list A) (weight score : A -> R) (event : A -> bool),
 finite_true_mass xs weight event <> 0 ->
 finite_false_mass xs weight event <> 0 ->
 finite_weighted_score xs weight
  (finite_two_cell_residual xs weight score event) = 0.
Proof.
 intros A xs weight score event Ht Hf.
 unfold finite_two_cell_residual.
 apply finite_two_cell_residual_mean_zero; assumption.
Qed.

(**
 [finite_two_cell_residual_mean_zero_normalized] (theorem) — With positive cell masses, a finite conditional prediction residual has normalized weighted mean exactly zero.
 Mathematical meaning: With positive cell masses, a finite conditional prediction residual has normalized weighted mean exactly zero.
 Exact checked proposition: forall (A : Type) (xs : list A) (weight score : A -> R) (event : A -> bool), 0 < finite_true_mass xs weight event -> 0 < finite_false_mass xs weight event -> finite_weighted_mean xs weight (finite_two_cell_residual xs weight score event) = 0.
 Premises and side conditions: All needed nonzero or positive Boolean cell masses are explicit at use sites; nonnegative individual outcome weights are required for order conclusions. There is no hidden continuity, normality or independence assumption.
 Proof/definition method: Compose existing exact projection/finite covariance identities, with explicit pointwise or real-ring normalization instead of new fold proofs.
 Library reuse: Stdlib.List/FunctionalExtensionality/Reals/Lra/Ring, FiniteSum's exact list sums, previously kernel-checked two-cell projection, nested projection, and conditional covariance theorems.
 Boundary: Explicit finite occurrence lists with real weights and deterministic event partitions only; no arbitrary L1 conditional expectation, Gaussian conditioning, or empirical IQ claim.
 *)
Theorem finite_two_cell_residual_mean_zero_normalized :
 forall (A : Type) (xs : list A) (weight score : A -> R) (event : A -> bool),
 0 < finite_true_mass xs weight event ->
 0 < finite_false_mass xs weight event ->
 finite_weighted_mean xs weight
  (finite_two_cell_residual xs weight score event) = 0.
Proof.
 intros A xs weight score event Ht Hf.
 unfold finite_weighted_mean.
 rewrite (finite_two_cell_residual_score_zero A xs weight score event) by lra.
 field.
 apply Rgt_not_eq.
 apply finite_two_cell_total_mass_positive with (event:=event); assumption.
Qed.

(**
 [finite_two_cell_fitted_score_tower] (theorem) — The finite fitted score has exactly the same unnormalized first moment as its original response.
 Mathematical meaning: The finite fitted score has exactly the same unnormalized first moment as its original response.
 Exact checked proposition: forall (A : Type) (xs : list A) (weight score : A -> R) (event : A -> bool), finite_true_mass xs weight event <> 0 -> finite_false_mass xs weight event <> 0 -> finite_weighted_score xs weight (finite_two_cell_prediction xs weight score event) = finite_weighted_score xs weight score.
 Premises and side conditions: All needed nonzero or positive Boolean cell masses are explicit at use sites; nonnegative individual outcome weights are required for order conclusions. There is no hidden continuity, normality or independence assumption.
 Proof/definition method: Compose existing exact projection/finite covariance identities, with explicit pointwise or real-ring normalization instead of new fold proofs.
 Library reuse: Stdlib.List/FunctionalExtensionality/Reals/Lra/Ring, FiniteSum's exact list sums, previously kernel-checked two-cell projection, nested projection, and conditional covariance theorems.
 Boundary: Explicit finite occurrence lists with real weights and deterministic event partitions only; no arbitrary L1 conditional expectation, Gaussian conditioning, or empirical IQ claim.
 *)
Theorem finite_two_cell_fitted_score_tower :
 forall (A : Type) (xs : list A) (weight score : A -> R) (event : A -> bool),
 finite_true_mass xs weight event <> 0 ->
 finite_false_mass xs weight event <> 0 ->
 finite_weighted_score xs weight
  (finite_two_cell_prediction xs weight score event) =
 finite_weighted_score xs weight score.
Proof.
 intros A xs weight score event Ht Hf.
 apply finite_two_cell_tower_expectation; assumption.
Qed.

(**
 [finite_two_cell_fitted_mean_tower] (theorem) — The normalized mean of a two-cell fitted response equals the original global mean.
 Mathematical meaning: The normalized mean of a two-cell fitted response equals the original global mean.
 Exact checked proposition: forall (A : Type) (xs : list A) (weight score : A -> R) (event : A -> bool), 0 < finite_true_mass xs weight event -> 0 < finite_false_mass xs weight event -> finite_weighted_mean xs weight (finite_two_cell_prediction xs weight score event) = finite_weighted_mean xs weight score.
 Premises and side conditions: All needed nonzero or positive Boolean cell masses are explicit at use sites; nonnegative individual outcome weights are required for order conclusions. There is no hidden continuity, normality or independence assumption.
 Proof/definition method: Compose existing exact projection/finite covariance identities, with explicit pointwise or real-ring normalization instead of new fold proofs.
 Library reuse: Stdlib.List/FunctionalExtensionality/Reals/Lra/Ring, FiniteSum's exact list sums, previously kernel-checked two-cell projection, nested projection, and conditional covariance theorems.
 Boundary: Explicit finite occurrence lists with real weights and deterministic event partitions only; no arbitrary L1 conditional expectation, Gaussian conditioning, or empirical IQ claim.
 *)
Theorem finite_two_cell_fitted_mean_tower :
 forall (A : Type) (xs : list A) (weight score : A -> R) (event : A -> bool),
 0 < finite_true_mass xs weight event ->
 0 < finite_false_mass xs weight event ->
 finite_weighted_mean xs weight
  (finite_two_cell_prediction xs weight score event) =
 finite_weighted_mean xs weight score.
Proof.
 intros A xs weight score event Ht Hf.
 unfold finite_weighted_mean.
 rewrite finite_two_cell_fitted_score_tower by lra.
 reflexivity.
Qed.

(**
 [finite_two_cell_residual_orthogonal_indicator] (theorem) — The finite projection residual has zero weighted moment on the observed true-event cell.
 Mathematical meaning: The finite projection residual has zero weighted moment on the observed true-event cell.
 Exact checked proposition: forall (A : Type) (xs : list A) (weight score : A -> R) (event : A -> bool), finite_true_mass xs weight event <> 0 -> finite_false_mass xs weight event <> 0 -> finite_weighted_score xs weight (fun x => finite_two_cell_residual xs weight score event x * (if event x then 1 else 0))=0.
 Premises and side conditions: All needed nonzero or positive Boolean cell masses are explicit at use sites; nonnegative individual outcome weights are required for order conclusions. There is no hidden continuity, normality or independence assumption.
 Proof/definition method: Compose existing exact projection/finite covariance identities, with explicit pointwise or real-ring normalization instead of new fold proofs.
 Library reuse: Stdlib.List/FunctionalExtensionality/Reals/Lra/Ring, FiniteSum's exact list sums, previously kernel-checked two-cell projection, nested projection, and conditional covariance theorems.
 Boundary: Explicit finite occurrence lists with real weights and deterministic event partitions only; no arbitrary L1 conditional expectation, Gaussian conditioning, or empirical IQ claim.
 *)
Theorem finite_two_cell_residual_orthogonal_indicator :
 forall (A : Type) (xs : list A) (weight score : A -> R) (event : A -> bool),
 finite_true_mass xs weight event <> 0 ->
 finite_false_mass xs weight event <> 0 ->
 finite_weighted_score xs weight
  (fun x => finite_two_cell_residual xs weight score event x *
    (if event x then 1 else 0))=0.
Proof.
 intros A xs weight score event Ht Hf.
 unfold finite_two_cell_residual.
 apply finite_two_cell_residual_orthogonal; assumption.
Qed.

(**
 [finite_two_cell_residual_orthogonal_complement] (theorem) — The finite projection residual has zero weighted moment on the unobserved complementary cell.
 Mathematical meaning: The finite projection residual has zero weighted moment on the unobserved complementary cell.
 Exact checked proposition: forall (A : Type) (xs : list A) (weight score : A -> R) (event : A -> bool), finite_true_mass xs weight event <> 0 -> finite_false_mass xs weight event <> 0 -> finite_weighted_score xs weight (fun x => finite_two_cell_residual xs weight score event x * (if event x then 0 else 1))=0.
 Premises and side conditions: All needed nonzero or positive Boolean cell masses are explicit at use sites; nonnegative individual outcome weights are required for order conclusions. There is no hidden continuity, normality or independence assumption.
 Proof/definition method: Compose existing exact projection/finite covariance identities, with explicit pointwise or real-ring normalization instead of new fold proofs.
 Library reuse: Stdlib.List/FunctionalExtensionality/Reals/Lra/Ring, FiniteSum's exact list sums, previously kernel-checked two-cell projection, nested projection, and conditional covariance theorems.
 Boundary: Explicit finite occurrence lists with real weights and deterministic event partitions only; no arbitrary L1 conditional expectation, Gaussian conditioning, or empirical IQ claim.
 *)
Theorem finite_two_cell_residual_orthogonal_complement :
 forall (A : Type) (xs : list A) (weight score : A -> R) (event : A -> bool),
 finite_true_mass xs weight event <> 0 ->
 finite_false_mass xs weight event <> 0 ->
 finite_weighted_score xs weight
  (fun x => finite_two_cell_residual xs weight score event x *
    (if event x then 0 else 1))=0.
Proof.
 intros A xs weight score event Ht Hf.
 unfold finite_two_cell_residual.
 apply finite_two_cell_residual_orthogonal; assumption.
Qed.

(**
 [finite_two_cell_residual_orthogonal_observable] (theorem) — Every piecewise constant two-cell-observable real score is orthogonal to the conditional prediction residual.
 Mathematical meaning: Every piecewise constant two-cell-observable real score is orthogonal to the conditional prediction residual.
 Exact checked proposition: forall (A : Type) (xs : list A) (weight score : A -> R) (event : A -> bool) (a b : R), finite_true_mass xs weight event <> 0 -> finite_false_mass xs weight event <> 0 -> finite_weighted_score xs weight (fun x => finite_two_cell_residual xs weight score event x * (if event x then a else b))=0.
 Premises and side conditions: All needed nonzero or positive Boolean cell masses are explicit at use sites; nonnegative individual outcome weights are required for order conclusions. There is no hidden continuity, normality or independence assumption.
 Proof/definition method: Compose existing exact projection/finite covariance identities, with explicit pointwise or real-ring normalization instead of new fold proofs.
 Library reuse: Stdlib.List/FunctionalExtensionality/Reals/Lra/Ring, FiniteSum's exact list sums, previously kernel-checked two-cell projection, nested projection, and conditional covariance theorems.
 Boundary: Explicit finite occurrence lists with real weights and deterministic event partitions only; no arbitrary L1 conditional expectation, Gaussian conditioning, or empirical IQ claim.
 *)
Theorem finite_two_cell_residual_orthogonal_observable :
 forall (A : Type) (xs : list A) (weight score : A -> R)
 (event : A -> bool) (a b : R),
 finite_true_mass xs weight event <> 0 ->
 finite_false_mass xs weight event <> 0 ->
 finite_weighted_score xs weight
  (fun x => finite_two_cell_residual xs weight score event x *
     (if event x then a else b))=0.
Proof.
 intros A xs weight score event a b Ht Hf.
 unfold finite_two_cell_residual.
 apply finite_two_cell_residual_orthogonal; assumption.
Qed.

(**
 [finite_two_cell_residual_fitted_product_zero] (theorem) — The residual of f has exactly zero weighted raw cross-moment with the conditional fitted predictor of g.
 Mathematical meaning: The residual of f has exactly zero weighted raw cross-moment with the conditional fitted predictor of g.
 Exact checked proposition: forall (A : Type) (xs : list A) (weight f g : A -> R) (event : A -> bool), finite_true_mass xs weight event <> 0 -> finite_false_mass xs weight event <> 0 -> finite_weighted_score xs weight (fun x => finite_two_cell_residual xs weight f event x * finite_two_cell_prediction xs weight g event x)=0.
 Premises and side conditions: All needed nonzero or positive Boolean cell masses are explicit at use sites; nonnegative individual outcome weights are required for order conclusions. There is no hidden continuity, normality or independence assumption.
 Proof/definition method: Compose existing exact projection/finite covariance identities, with explicit pointwise or real-ring normalization instead of new fold proofs.
 Library reuse: Stdlib.List/FunctionalExtensionality/Reals/Lra/Ring, FiniteSum's exact list sums, previously kernel-checked two-cell projection, nested projection, and conditional covariance theorems.
 Boundary: Explicit finite occurrence lists with real weights and deterministic event partitions only; no arbitrary L1 conditional expectation, Gaussian conditioning, or empirical IQ claim.
 *)
Theorem finite_two_cell_residual_fitted_product_zero :
 forall (A : Type) (xs : list A) (weight f g : A -> R)
 (event : A -> bool),
 finite_true_mass xs weight event <> 0 ->
 finite_false_mass xs weight event <> 0 ->
 finite_weighted_score xs weight
  (fun x => finite_two_cell_residual xs weight f event x *
    finite_two_cell_prediction xs weight g event x)=0.
Proof.
 intros A xs weight f g event Ht Hf.
 change (finite_weighted_score xs weight (fun x =>
  finite_two_cell_residual xs weight f event x *
    (if event x then finite_true_mean xs weight g event
     else finite_false_mean xs weight g event))=0).
 apply finite_two_cell_residual_orthogonal_observable; assumption.
Qed.

(**
 [finite_two_cell_fitted_residual_product_zero] (theorem) — The conditional fitted predictor of f has zero weighted raw cross-moment with the residual of g.
 Mathematical meaning: The conditional fitted predictor of f has zero weighted raw cross-moment with the residual of g.
 Exact checked proposition: forall (A : Type) (xs : list A) (weight f g : A -> R) (event : A -> bool), finite_true_mass xs weight event <> 0 -> finite_false_mass xs weight event <> 0 -> finite_weighted_score xs weight (fun x => finite_two_cell_prediction xs weight f event x * finite_two_cell_residual xs weight g event x)=0.
 Premises and side conditions: All needed nonzero or positive Boolean cell masses are explicit at use sites; nonnegative individual outcome weights are required for order conclusions. There is no hidden continuity, normality or independence assumption.
 Proof/definition method: Compose existing exact projection/finite covariance identities, with explicit pointwise or real-ring normalization instead of new fold proofs.
 Library reuse: Stdlib.List/FunctionalExtensionality/Reals/Lra/Ring, FiniteSum's exact list sums, previously kernel-checked two-cell projection, nested projection, and conditional covariance theorems.
 Boundary: Explicit finite occurrence lists with real weights and deterministic event partitions only; no arbitrary L1 conditional expectation, Gaussian conditioning, or empirical IQ claim.
 *)
Theorem finite_two_cell_fitted_residual_product_zero :
 forall (A : Type) (xs : list A) (weight f g : A -> R)
 (event : A -> bool),
 finite_true_mass xs weight event <> 0 ->
 finite_false_mass xs weight event <> 0 ->
 finite_weighted_score xs weight
  (fun x => finite_two_cell_prediction xs weight f event x *
    finite_two_cell_residual xs weight g event x)=0.
Proof.
 intros A xs weight f g event Ht Hf.
 transitivity (finite_weighted_score xs weight
  (fun x => finite_two_cell_residual xs weight g event x *
    finite_two_cell_prediction xs weight f event x)).
 { unfold finite_weighted_score.
   apply finite_sum_ext; intros x; ring. }
 apply finite_two_cell_residual_fitted_product_zero; assumption.
Qed.

(**
 [finite_two_cell_residual_fitted_covariance_zero] (theorem) — The globally centered covariance between any two-cell residual and any fitted value is zero.
 Mathematical meaning: The globally centered covariance between any two-cell residual and any fitted value is zero.
 Exact checked proposition: forall (A : Type) (xs : list A) (weight f g : A -> R) (event : A -> bool), 0 < finite_true_mass xs weight event -> 0 < finite_false_mass xs weight event -> finite_centered_cross xs weight (finite_two_cell_residual xs weight f event) (finite_two_cell_prediction xs weight g event) = 0.
 Premises and side conditions: All needed nonzero or positive Boolean cell masses are explicit at use sites; nonnegative individual outcome weights are required for order conclusions. There is no hidden continuity, normality or independence assumption.
 Proof/definition method: Compose existing exact projection/finite covariance identities, with explicit pointwise or real-ring normalization instead of new fold proofs.
 Library reuse: Stdlib.List/FunctionalExtensionality/Reals/Lra/Ring, FiniteSum's exact list sums, previously kernel-checked two-cell projection, nested projection, and conditional covariance theorems.
 Boundary: Explicit finite occurrence lists with real weights and deterministic event partitions only; no arbitrary L1 conditional expectation, Gaussian conditioning, or empirical IQ claim.
 *)
Theorem finite_two_cell_residual_fitted_covariance_zero :
 forall (A : Type) (xs : list A) (weight f g : A -> R)
 (event : A -> bool),
 0 < finite_true_mass xs weight event ->
 0 < finite_false_mass xs weight event ->
 finite_centered_cross xs weight
   (finite_two_cell_residual xs weight f event)
   (finite_two_cell_prediction xs weight g event) = 0.
Proof.
 intros A xs weight f g event Ht Hf.
 assert (Hm : finite_weight_mass xs weight <> 0).
 { apply Rgt_not_eq.
   apply finite_two_cell_total_mass_positive with (event:=event); assumption. }
 rewrite finite_centered_cross_formula by exact Hm.
 rewrite finite_two_cell_residual_fitted_product_zero by lra.
 rewrite finite_two_cell_residual_mean_zero_normalized by assumption.
 ring.
Qed.

(**
 [finite_two_cell_fitted_residual_covariance_zero] (theorem) — The centered covariance between any two-cell fitted score and any other score's residual is zero.
 Mathematical meaning: The centered covariance between any two-cell fitted score and any other score's residual is zero.
 Exact checked proposition: forall (A : Type) (xs : list A) (weight f g : A -> R) (event : A -> bool), 0 < finite_true_mass xs weight event -> 0 < finite_false_mass xs weight event -> finite_centered_cross xs weight (finite_two_cell_prediction xs weight f event) (finite_two_cell_residual xs weight g event) = 0.
 Premises and side conditions: All needed nonzero or positive Boolean cell masses are explicit at use sites; nonnegative individual outcome weights are required for order conclusions. There is no hidden continuity, normality or independence assumption.
 Proof/definition method: Compose existing exact projection/finite covariance identities, with explicit pointwise or real-ring normalization instead of new fold proofs.
 Library reuse: Stdlib.List/FunctionalExtensionality/Reals/Lra/Ring, FiniteSum's exact list sums, previously kernel-checked two-cell projection, nested projection, and conditional covariance theorems.
 Boundary: Explicit finite occurrence lists with real weights and deterministic event partitions only; no arbitrary L1 conditional expectation, Gaussian conditioning, or empirical IQ claim.
 *)
Theorem finite_two_cell_fitted_residual_covariance_zero :
 forall (A : Type) (xs : list A) (weight f g : A -> R)
 (event : A -> bool),
 0 < finite_true_mass xs weight event ->
 0 < finite_false_mass xs weight event ->
 finite_centered_cross xs weight
   (finite_two_cell_prediction xs weight f event)
   (finite_two_cell_residual xs weight g event) = 0.
Proof.
 intros A xs weight f g event Ht Hf.
 rewrite finite_centered_cross_symmetric.
 apply finite_two_cell_residual_fitted_covariance_zero; assumption.
Qed.

(**
 [finite_centered_cross_pointwise_ext] (theorem) — Pointwise equal score functions have the same globally centered covariance, independent of finite-list multiplicity.
 Mathematical meaning: Pointwise equal score functions have the same globally centered covariance, independent of finite-list multiplicity.
 Exact checked proposition: forall (A : Type) (xs : list A) (weight f f' g g' : A -> R), (forall x, f x = f' x) -> (forall x, g x = g' x) -> finite_centered_cross xs weight f g = finite_centered_cross xs weight f' g'.
 Premises and side conditions: All needed nonzero or positive Boolean cell masses are explicit at use sites; nonnegative individual outcome weights are required for order conclusions. There is no hidden continuity, normality or independence assumption.
 Proof/definition method: Compose existing exact projection/finite covariance identities, with explicit pointwise or real-ring normalization instead of new fold proofs.
 Library reuse: Stdlib.List/FunctionalExtensionality/Reals/Lra/Ring, FiniteSum's exact list sums, previously kernel-checked two-cell projection, nested projection, and conditional covariance theorems.
 Boundary: Explicit finite occurrence lists with real weights and deterministic event partitions only; no arbitrary L1 conditional expectation, Gaussian conditioning, or empirical IQ claim.
 *)
Theorem finite_centered_cross_pointwise_ext :
 forall (A : Type) (xs : list A) (weight f f' g g' : A -> R),
 (forall x, f x = f' x) ->
 (forall x, g x = g' x) ->
 finite_centered_cross xs weight f g =
 finite_centered_cross xs weight f' g'.
Proof.
 intros A xs weight f f' g g' Hf Hg.
 assert (Ef : f = f').
 { apply functional_extensionality; exact Hf. }
 assert (Eg : g = g').
 { apply functional_extensionality; exact Hg. }
 rewrite Ef, Eg.
 reflexivity.
Qed.

(**
 [finite_two_cell_total_covariance_fitted_residual] (theorem) — The total centered covariance decomposes exactly into fitted-fitted and residual-residual covariance with no mixed terms.
 Mathematical meaning: The total centered covariance decomposes exactly into fitted-fitted and residual-residual covariance with no mixed terms.
 Exact checked proposition: forall (A : Type) (xs : list A) (weight f g : A -> R) (event : A -> bool), 0 < finite_true_mass xs weight event -> 0 < finite_false_mass xs weight event -> finite_centered_cross xs weight f g = finite_fitted_cross xs weight f g event + finite_residual_cross xs weight f g event.
 Premises and side conditions: All needed nonzero or positive Boolean cell masses are explicit at use sites; nonnegative individual outcome weights are required for order conclusions. There is no hidden continuity, normality or independence assumption.
 Proof/definition method: Compose existing exact projection/finite covariance identities, with explicit pointwise or real-ring normalization instead of new fold proofs.
 Library reuse: Stdlib.List/FunctionalExtensionality/Reals/Lra/Ring, FiniteSum's exact list sums, previously kernel-checked two-cell projection, nested projection, and conditional covariance theorems.
 Boundary: Explicit finite occurrence lists with real weights and deterministic event partitions only; no arbitrary L1 conditional expectation, Gaussian conditioning, or empirical IQ claim.
 *)
Theorem finite_two_cell_total_covariance_fitted_residual :
 forall (A : Type) (xs : list A) (weight f g : A -> R)
 (event : A -> bool),
 0 < finite_true_mass xs weight event ->
 0 < finite_false_mass xs weight event ->
 finite_centered_cross xs weight f g =
 finite_fitted_cross xs weight f g event +
 finite_residual_cross xs weight f g event.
Proof.
 intros A xs weight f g event Ht Hf.
 assert (Hm : finite_weight_mass xs weight <> 0).
 { apply Rgt_not_eq.
   apply finite_two_cell_total_mass_positive with (event:=event); assumption. }
 transitivity (finite_centered_cross xs weight
   (fun x => finite_two_cell_prediction xs weight f event x +
     finite_two_cell_residual xs weight f event x)
   (fun x => finite_two_cell_prediction xs weight g event x +
     finite_two_cell_residual xs weight g event x)).
 { apply finite_centered_cross_pointwise_ext; intro x;
     unfold finite_two_cell_residual; ring. }
 rewrite (finite_centered_cross_add_first A xs weight
   (finite_two_cell_prediction xs weight f event)
   (finite_two_cell_residual xs weight f event)
   (fun x => finite_two_cell_prediction xs weight g event x +
     finite_two_cell_residual xs weight g event x) Hm).
 rewrite (finite_centered_cross_add_second A xs weight
   (finite_two_cell_prediction xs weight f event)
   (finite_two_cell_prediction xs weight g event)
   (finite_two_cell_residual xs weight g event) Hm).
 rewrite (finite_centered_cross_add_second A xs weight
   (finite_two_cell_residual xs weight f event)
   (finite_two_cell_prediction xs weight g event)
   (finite_two_cell_residual xs weight g event) Hm).
 rewrite (finite_two_cell_fitted_residual_covariance_zero
   A xs weight f g event Ht Hf).
 rewrite (finite_two_cell_residual_fitted_covariance_zero
   A xs weight f g event Ht Hf).
 unfold finite_fitted_cross, finite_residual_cross.
 ring.
Qed.

(**
 [finite_two_cell_fitted_covariance_symmetric] (theorem) — Swapping responses preserves the fitted conditional covariance term.
 Mathematical meaning: Swapping responses preserves the fitted conditional covariance term.
 Exact checked proposition: forall (A : Type) (xs : list A) (weight f g : A -> R) (event : A -> bool), finite_fitted_cross xs weight f g event = finite_fitted_cross xs weight g f event.
 Premises and side conditions: All needed nonzero or positive Boolean cell masses are explicit at use sites; nonnegative individual outcome weights are required for order conclusions. There is no hidden continuity, normality or independence assumption.
 Proof/definition method: Compose existing exact projection/finite covariance identities, with explicit pointwise or real-ring normalization instead of new fold proofs.
 Library reuse: Stdlib.List/FunctionalExtensionality/Reals/Lra/Ring, FiniteSum's exact list sums, previously kernel-checked two-cell projection, nested projection, and conditional covariance theorems.
 Boundary: Explicit finite occurrence lists with real weights and deterministic event partitions only; no arbitrary L1 conditional expectation, Gaussian conditioning, or empirical IQ claim.
 *)
Theorem finite_two_cell_fitted_covariance_symmetric :
 forall (A : Type) (xs : list A) (weight f g : A -> R)
 (event : A -> bool),
 finite_fitted_cross xs weight f g event =
 finite_fitted_cross xs weight g f event.
Proof.
 intros A xs weight f g event.
 unfold finite_fitted_cross.
 apply finite_centered_cross_symmetric.
Qed.

(**
 [finite_two_cell_residual_covariance_symmetric] (theorem) — Swapping responses preserves the residual conditional covariance term.
 Mathematical meaning: Swapping responses preserves the residual conditional covariance term.
 Exact checked proposition: forall (A : Type) (xs : list A) (weight f g : A -> R) (event : A -> bool), finite_residual_cross xs weight f g event = finite_residual_cross xs weight g f event.
 Premises and side conditions: All needed nonzero or positive Boolean cell masses are explicit at use sites; nonnegative individual outcome weights are required for order conclusions. There is no hidden continuity, normality or independence assumption.
 Proof/definition method: Compose existing exact projection/finite covariance identities, with explicit pointwise or real-ring normalization instead of new fold proofs.
 Library reuse: Stdlib.List/FunctionalExtensionality/Reals/Lra/Ring, FiniteSum's exact list sums, previously kernel-checked two-cell projection, nested projection, and conditional covariance theorems.
 Boundary: Explicit finite occurrence lists with real weights and deterministic event partitions only; no arbitrary L1 conditional expectation, Gaussian conditioning, or empirical IQ claim.
 *)
Theorem finite_two_cell_residual_covariance_symmetric :
 forall (A : Type) (xs : list A) (weight f g : A -> R)
 (event : A -> bool),
 finite_residual_cross xs weight f g event =
 finite_residual_cross xs weight g f event.
Proof.
 intros A xs weight f g event.
 unfold finite_residual_cross.
 apply finite_centered_cross_symmetric.
Qed.

(**
 [finite_two_cell_fitted_variance_nonnegative] (theorem) — The actual fitted-score centered squared loss is nonnegative for nonnegative weights.
 Mathematical meaning: The actual fitted-score centered squared loss is nonnegative for nonnegative weights.
 Exact checked proposition: forall (A : Type) (xs : list A) (weight f : A -> R) (event : A -> bool), (forall x, In x xs -> 0 <= weight x) -> 0 <= finite_fitted_cross xs weight f f event.
 Premises and side conditions: All needed nonzero or positive Boolean cell masses are explicit at use sites; nonnegative individual outcome weights are required for order conclusions. There is no hidden continuity, normality or independence assumption.
 Proof/definition method: Compose existing exact projection/finite covariance identities, with explicit pointwise or real-ring normalization instead of new fold proofs.
 Library reuse: Stdlib.List/FunctionalExtensionality/Reals/Lra/Ring, FiniteSum's exact list sums, previously kernel-checked two-cell projection, nested projection, and conditional covariance theorems.
 Boundary: Explicit finite occurrence lists with real weights and deterministic event partitions only; no arbitrary L1 conditional expectation, Gaussian conditioning, or empirical IQ claim.
 *)
Theorem finite_two_cell_fitted_variance_nonnegative :
 forall (A : Type) (xs : list A) (weight f : A -> R)
 (event : A -> bool),
 (forall x, In x xs -> 0 <= weight x) ->
 0 <= finite_fitted_cross xs weight f f event.
Proof.
 intros A xs weight f event Hweight.
 unfold finite_fitted_cross.
 rewrite finite_centered_cross_variance.
 apply finite_weighted_loss_nonnegative; assumption.
Qed.

(**
 [finite_two_cell_residual_variance_nonnegative] (theorem) — The actual conditional residual centered squared loss is nonnegative for nonnegative weights.
 Mathematical meaning: The actual conditional residual centered squared loss is nonnegative for nonnegative weights.
 Exact checked proposition: forall (A : Type) (xs : list A) (weight f : A -> R) (event : A -> bool), (forall x, In x xs -> 0 <= weight x) -> 0 <= finite_residual_cross xs weight f f event.
 Premises and side conditions: All needed nonzero or positive Boolean cell masses are explicit at use sites; nonnegative individual outcome weights are required for order conclusions. There is no hidden continuity, normality or independence assumption.
 Proof/definition method: Compose existing exact projection/finite covariance identities, with explicit pointwise or real-ring normalization instead of new fold proofs.
 Library reuse: Stdlib.List/FunctionalExtensionality/Reals/Lra/Ring, FiniteSum's exact list sums, previously kernel-checked two-cell projection, nested projection, and conditional covariance theorems.
 Boundary: Explicit finite occurrence lists with real weights and deterministic event partitions only; no arbitrary L1 conditional expectation, Gaussian conditioning, or empirical IQ claim.
 *)
Theorem finite_two_cell_residual_variance_nonnegative :
 forall (A : Type) (xs : list A) (weight f : A -> R)
 (event : A -> bool),
 (forall x, In x xs -> 0 <= weight x) ->
 0 <= finite_residual_cross xs weight f f event.
Proof.
 intros A xs weight f event Hweight.
 unfold finite_residual_cross.
 rewrite finite_centered_cross_variance.
 apply finite_weighted_loss_nonnegative; assumption.
Qed.

(**
 [finite_two_cell_total_variance_fitted_residual] (theorem) — The finite global variance is exactly the sum of fitted-score variance and residual variance.
 Mathematical meaning: The finite global variance is exactly the sum of fitted-score variance and residual variance.
 Exact checked proposition: forall (A : Type) (xs : list A) (weight f : A -> R) (event : A -> bool), 0 < finite_true_mass xs weight event -> 0 < finite_false_mass xs weight event -> finite_centered_cross xs weight f f = finite_fitted_cross xs weight f f event + finite_residual_cross xs weight f f event.
 Premises and side conditions: All needed nonzero or positive Boolean cell masses are explicit at use sites; nonnegative individual outcome weights are required for order conclusions. There is no hidden continuity, normality or independence assumption.
 Proof/definition method: Compose existing exact projection/finite covariance identities, with explicit pointwise or real-ring normalization instead of new fold proofs.
 Library reuse: Stdlib.List/FunctionalExtensionality/Reals/Lra/Ring, FiniteSum's exact list sums, previously kernel-checked two-cell projection, nested projection, and conditional covariance theorems.
 Boundary: Explicit finite occurrence lists with real weights and deterministic event partitions only; no arbitrary L1 conditional expectation, Gaussian conditioning, or empirical IQ claim.
 *)
Theorem finite_two_cell_total_variance_fitted_residual :
 forall (A : Type) (xs : list A) (weight f : A -> R)
 (event : A -> bool),
 0 < finite_true_mass xs weight event ->
 0 < finite_false_mass xs weight event ->
 finite_centered_cross xs weight f f =
 finite_fitted_cross xs weight f f event +
 finite_residual_cross xs weight f f event.
Proof.
 intros A xs weight f event Ht Hf.
 apply finite_two_cell_total_covariance_fitted_residual; assumption.
Qed.

(**
 [finite_two_cell_residual_variance_le_total] (theorem) — Nonnegative sample weights imply conditional residual variance is bounded above by original variance.
 Mathematical meaning: Nonnegative sample weights imply conditional residual variance is bounded above by original variance.
 Exact checked proposition: forall (A : Type) (xs : list A) (weight f : A -> R) (event : A -> bool), 0 < finite_true_mass xs weight event -> 0 < finite_false_mass xs weight event -> (forall x, In x xs -> 0 <= weight x) -> finite_residual_cross xs weight f f event <= finite_centered_cross xs weight f f.
 Premises and side conditions: All needed nonzero or positive Boolean cell masses are explicit at use sites; nonnegative individual outcome weights are required for order conclusions. There is no hidden continuity, normality or independence assumption.
 Proof/definition method: Compose existing exact projection/finite covariance identities, with explicit pointwise or real-ring normalization instead of new fold proofs.
 Library reuse: Stdlib.List/FunctionalExtensionality/Reals/Lra/Ring, FiniteSum's exact list sums, previously kernel-checked two-cell projection, nested projection, and conditional covariance theorems.
 Boundary: Explicit finite occurrence lists with real weights and deterministic event partitions only; no arbitrary L1 conditional expectation, Gaussian conditioning, or empirical IQ claim.
 *)
Theorem finite_two_cell_residual_variance_le_total :
 forall (A : Type) (xs : list A) (weight f : A -> R)
 (event : A -> bool),
 0 < finite_true_mass xs weight event ->
 0 < finite_false_mass xs weight event ->
 (forall x, In x xs -> 0 <= weight x) ->
 finite_residual_cross xs weight f f event <=
 finite_centered_cross xs weight f f.
Proof.
 intros A xs weight f event Ht Hf Hw.
 pose proof (finite_two_cell_total_variance_fitted_residual
  A xs weight f event Ht Hf) as Heq.
 pose proof (finite_two_cell_fitted_variance_nonnegative
  A xs weight f event Hw) as Hpos.
 lra.
Qed.

(**
 [finite_two_cell_fitted_variance_le_total] (theorem) — Nonnegative sample weights imply that fitted-score variance cannot exceed the original score variance.
 Mathematical meaning: Nonnegative sample weights imply that fitted-score variance cannot exceed the original score variance.
 Exact checked proposition: forall (A : Type) (xs : list A) (weight f : A -> R) (event : A -> bool), 0 < finite_true_mass xs weight event -> 0 < finite_false_mass xs weight event -> (forall x, In x xs -> 0 <= weight x) -> finite_fitted_cross xs weight f f event <= finite_centered_cross xs weight f f.
 Premises and side conditions: All needed nonzero or positive Boolean cell masses are explicit at use sites; nonnegative individual outcome weights are required for order conclusions. There is no hidden continuity, normality or independence assumption.
 Proof/definition method: Compose existing exact projection/finite covariance identities, with explicit pointwise or real-ring normalization instead of new fold proofs.
 Library reuse: Stdlib.List/FunctionalExtensionality/Reals/Lra/Ring, FiniteSum's exact list sums, previously kernel-checked two-cell projection, nested projection, and conditional covariance theorems.
 Boundary: Explicit finite occurrence lists with real weights and deterministic event partitions only; no arbitrary L1 conditional expectation, Gaussian conditioning, or empirical IQ claim.
 *)
Theorem finite_two_cell_fitted_variance_le_total :
 forall (A : Type) (xs : list A) (weight f : A -> R)
 (event : A -> bool),
 0 < finite_true_mass xs weight event ->
 0 < finite_false_mass xs weight event ->
 (forall x, In x xs -> 0 <= weight x) ->
 finite_fitted_cross xs weight f f event <=
 finite_centered_cross xs weight f f.
Proof.
 intros A xs weight f event Ht Hf Hw.
 pose proof (finite_two_cell_total_variance_fitted_residual
  A xs weight f event Ht Hf) as Heq.
 pose proof (finite_two_cell_residual_variance_nonnegative
  A xs weight f event Hw) as Hpos.
 lra.
Qed.

(**
 [finite_centered_cross_constant_on_support] (theorem) — If a score is constant at every enumerated outcome then its centered covariance with any other score vanishes.
 Mathematical meaning: If a score is constant at every enumerated outcome then its centered covariance with any other score vanishes.
 Exact checked proposition: forall (A : Type) (xs : list A) (weight f g : A -> R) (a : R), finite_weight_mass xs weight <> 0 -> (forall x, In x xs -> f x = a) -> finite_centered_cross xs weight f g = 0.
 Premises and side conditions: All needed nonzero or positive Boolean cell masses are explicit at use sites; nonnegative individual outcome weights are required for order conclusions. There is no hidden continuity, normality or independence assumption.
 Proof/definition method: Compose existing exact projection/finite covariance identities, with explicit pointwise or real-ring normalization instead of new fold proofs.
 Library reuse: Stdlib.List/FunctionalExtensionality/Reals/Lra/Ring, FiniteSum's exact list sums, previously kernel-checked two-cell projection, nested projection, and conditional covariance theorems.
 Boundary: Explicit finite occurrence lists with real weights and deterministic event partitions only; no arbitrary L1 conditional expectation, Gaussian conditioning, or empirical IQ claim.
 *)
Theorem finite_centered_cross_constant_on_support :
 forall (A : Type) (xs : list A) (weight f g : A -> R) (a : R),
 finite_weight_mass xs weight <> 0 ->
 (forall x, In x xs -> f x = a) ->
 finite_centered_cross xs weight f g = 0.
Proof.
 intros A xs weight f g a Hm Hconst.
 assert (Hmean : finite_weighted_mean xs weight f = a).
 { unfold finite_weighted_mean.
   replace (finite_weighted_score xs weight f)
    with (finite_weighted_score xs weight (fun _=>a)).
   2:{ unfold finite_weighted_score.
       apply finite_sum_ext_in; intros x Hx.
       rewrite (Hconst x Hx); reflexivity. }
   rewrite finite_weighted_score_constant.
   field; exact Hm. }
 unfold finite_centered_cross, finite_weighted_cross, finite_weighted_score.
 rewrite Hmean.
 transitivity (finite_sum (fun _=>0) xs).
 { apply finite_sum_ext_in; intros x Hx.
   rewrite (Hconst x Hx); ring. }
 apply finite_sum_zero.
Qed.

(**
 [finite_two_cell_fitted_within_covariance_zero] (theorem) — Both conditional fitted scores are constant inside each Boolean cell, so their within-cell covariance vanishes.
 Mathematical meaning: Both conditional fitted scores are constant inside each Boolean cell, so their within-cell covariance vanishes.
 Exact checked proposition: forall (A : Type) (xs : list A) (weight f g : A -> R) (event : A -> bool), finite_true_mass xs weight event <> 0 -> finite_false_mass xs weight event <> 0 -> finite_two_cell_within_cross xs weight (finite_two_cell_prediction xs weight f event) (finite_two_cell_prediction xs weight g event) event = 0.
 Premises and side conditions: All needed nonzero or positive Boolean cell masses are explicit at use sites; nonnegative individual outcome weights are required for order conclusions. There is no hidden continuity, normality or independence assumption.
 Proof/definition method: Compose existing exact projection/finite covariance identities, with explicit pointwise or real-ring normalization instead of new fold proofs.
 Library reuse: Stdlib.List/FunctionalExtensionality/Reals/Lra/Ring, FiniteSum's exact list sums, previously kernel-checked two-cell projection, nested projection, and conditional covariance theorems.
 Boundary: Explicit finite occurrence lists with real weights and deterministic event partitions only; no arbitrary L1 conditional expectation, Gaussian conditioning, or empirical IQ claim.
 *)
Theorem finite_two_cell_fitted_within_covariance_zero :
 forall (A : Type) (xs : list A) (weight f g : A -> R)
 (event : A -> bool),
 finite_true_mass xs weight event <> 0 ->
 finite_false_mass xs weight event <> 0 ->
 finite_two_cell_within_cross xs weight
   (finite_two_cell_prediction xs weight f event)
   (finite_two_cell_prediction xs weight g event) event = 0.
Proof.
 intros A xs weight f g event Ht Hf.
 unfold finite_two_cell_within_cross.
 rewrite (finite_centered_cross_constant_on_support A
  (filter event xs) weight
  (finite_two_cell_prediction xs weight f event)
  (finite_two_cell_prediction xs weight g event)
  (finite_true_mean xs weight f event) Ht).
 2:{ intros x Hx; apply filter_In in Hx; destruct Hx as [_ Hx].
     unfold finite_two_cell_prediction; rewrite Hx; reflexivity. }
 rewrite (finite_centered_cross_constant_on_support A
  (filter (fun x=>negb(event x)) xs) weight
  (finite_two_cell_prediction xs weight f event)
  (finite_two_cell_prediction xs weight g event)
  (finite_false_mean xs weight f event) Hf).
 2:{ intros x Hx; apply filter_In in Hx; destruct Hx as [_ Hx].
     unfold finite_two_cell_prediction.
     destruct (event x); simpl in Hx; [discriminate|reflexivity]. }
 ring.
Qed.

(**
 [finite_two_cell_fitted_between_covariance_fixed] (theorem) — Conditioning already-fitted scores a second time preserves their full between-cell covariance numerator.
 Mathematical meaning: Conditioning already-fitted scores a second time preserves their full between-cell covariance numerator.
 Exact checked proposition: forall (A : Type) (xs : list A) (weight f g : A -> R) (event : A -> bool), 0 < finite_true_mass xs weight event -> 0 < finite_false_mass xs weight event -> finite_two_cell_between_cross xs weight (finite_two_cell_prediction xs weight f event) (finite_two_cell_prediction xs weight g event) event = finite_two_cell_between_cross xs weight f g event.
 Premises and side conditions: All needed nonzero or positive Boolean cell masses are explicit at use sites; nonnegative individual outcome weights are required for order conclusions. There is no hidden continuity, normality or independence assumption.
 Proof/definition method: Compose existing exact projection/finite covariance identities, with explicit pointwise or real-ring normalization instead of new fold proofs.
 Library reuse: Stdlib.List/FunctionalExtensionality/Reals/Lra/Ring, FiniteSum's exact list sums, previously kernel-checked two-cell projection, nested projection, and conditional covariance theorems.
 Boundary: Explicit finite occurrence lists with real weights and deterministic event partitions only; no arbitrary L1 conditional expectation, Gaussian conditioning, or empirical IQ claim.
 *)
Theorem finite_two_cell_fitted_between_covariance_fixed :
 forall (A : Type) (xs : list A) (weight f g : A -> R)
 (event : A -> bool),
 0 < finite_true_mass xs weight event ->
 0 < finite_false_mass xs weight event ->
 finite_two_cell_between_cross xs weight
   (finite_two_cell_prediction xs weight f event)
   (finite_two_cell_prediction xs weight g event) event =
 finite_two_cell_between_cross xs weight f g event.
Proof.
 intros A xs weight f g event Ht Hf.
 unfold finite_two_cell_between_cross.
 rewrite (two_cell_predictor_true_mean_fixed A xs weight f event) by lra.
 rewrite (two_cell_predictor_false_mean_fixed A xs weight f event) by lra.
 rewrite (two_cell_predictor_true_mean_fixed A xs weight g event) by lra.
 rewrite (two_cell_predictor_false_mean_fixed A xs weight g event) by lra.
 rewrite (finite_two_cell_fitted_mean_tower A xs weight f event Ht Hf).
 rewrite (finite_two_cell_fitted_mean_tower A xs weight g event Ht Hf).
 reflexivity.
Qed.

(**
 [finite_two_cell_fitted_covariance_is_between] (theorem) — The covariance of conditional mean predictors equals the between-cell term in the finite law of total covariance.
 Mathematical meaning: The covariance of conditional mean predictors equals the between-cell term in the finite law of total covariance.
 Exact checked proposition: forall (A : Type) (xs : list A) (weight f g : A -> R) (event : A -> bool), 0 < finite_true_mass xs weight event -> 0 < finite_false_mass xs weight event -> finite_fitted_cross xs weight f g event = finite_two_cell_between_cross xs weight f g event.
 Premises and side conditions: All needed nonzero or positive Boolean cell masses are explicit at use sites; nonnegative individual outcome weights are required for order conclusions. There is no hidden continuity, normality or independence assumption.
 Proof/definition method: Compose existing exact projection/finite covariance identities, with explicit pointwise or real-ring normalization instead of new fold proofs.
 Library reuse: Stdlib.List/FunctionalExtensionality/Reals/Lra/Ring, FiniteSum's exact list sums, previously kernel-checked two-cell projection, nested projection, and conditional covariance theorems.
 Boundary: Explicit finite occurrence lists with real weights and deterministic event partitions only; no arbitrary L1 conditional expectation, Gaussian conditioning, or empirical IQ claim.
 *)
Theorem finite_two_cell_fitted_covariance_is_between :
 forall (A : Type) (xs : list A) (weight f g : A -> R)
 (event : A -> bool),
 0 < finite_true_mass xs weight event ->
 0 < finite_false_mass xs weight event ->
 finite_fitted_cross xs weight f g event =
 finite_two_cell_between_cross xs weight f g event.
Proof.
 intros A xs weight f g event Ht Hf.
 unfold finite_fitted_cross.
 rewrite (finite_two_cell_total_covariance A xs weight
  (finite_two_cell_prediction xs weight f event)
  (finite_two_cell_prediction xs weight g event) event) by lra.
 rewrite (finite_two_cell_fitted_within_covariance_zero A xs weight f g event) by lra.
 rewrite (finite_two_cell_fitted_between_covariance_fixed A xs weight f g event Ht Hf).
 ring.
Qed.

(**
 [finite_two_cell_residual_covariance_is_within] (theorem) — The covariance of conditional residuals equals the sum of within-cell conditional covariance terms.
 Mathematical meaning: The covariance of conditional residuals equals the sum of within-cell conditional covariance terms.
 Exact checked proposition: forall (A : Type) (xs : list A) (weight f g : A -> R) (event : A -> bool), 0 < finite_true_mass xs weight event -> 0 < finite_false_mass xs weight event -> finite_residual_cross xs weight f g event = finite_two_cell_within_cross xs weight f g event.
 Premises and side conditions: All needed nonzero or positive Boolean cell masses are explicit at use sites; nonnegative individual outcome weights are required for order conclusions. There is no hidden continuity, normality or independence assumption.
 Proof/definition method: Compose existing exact projection/finite covariance identities, with explicit pointwise or real-ring normalization instead of new fold proofs.
 Library reuse: Stdlib.List/FunctionalExtensionality/Reals/Lra/Ring, FiniteSum's exact list sums, previously kernel-checked two-cell projection, nested projection, and conditional covariance theorems.
 Boundary: Explicit finite occurrence lists with real weights and deterministic event partitions only; no arbitrary L1 conditional expectation, Gaussian conditioning, or empirical IQ claim.
 *)
Theorem finite_two_cell_residual_covariance_is_within :
 forall (A : Type) (xs : list A) (weight f g : A -> R)
 (event : A -> bool),
 0 < finite_true_mass xs weight event ->
 0 < finite_false_mass xs weight event ->
 finite_residual_cross xs weight f g event =
 finite_two_cell_within_cross xs weight f g event.
Proof.
 intros A xs weight f g event Ht Hf.
 pose proof (finite_two_cell_total_covariance_fitted_residual A xs weight f g event Ht Hf) as Hreg.
 pose proof (finite_two_cell_total_covariance A xs weight f g event) as Htotal.
 specialize (Htotal ltac:(lra) ltac:(lra)).
 pose proof (finite_two_cell_fitted_covariance_is_between A xs weight f g event Ht Hf) as Hfit.
 lra.
Qed.

(**
 [finite_two_cell_original_fitted_covariance] (theorem) — The covariance of an original response with another score's fitted value equals the covariance of their fitted values.
 Mathematical meaning: The covariance of an original response with another score's fitted value equals the covariance of their fitted values.
 Exact checked proposition: forall (A : Type) (xs : list A) (weight f g : A -> R) (event : A -> bool), 0 < finite_true_mass xs weight event -> 0 < finite_false_mass xs weight event -> finite_centered_cross xs weight f (finite_two_cell_prediction xs weight g event) = finite_fitted_cross xs weight f g event.
 Premises and side conditions: All needed nonzero or positive Boolean cell masses are explicit at use sites; nonnegative individual outcome weights are required for order conclusions. There is no hidden continuity, normality or independence assumption.
 Proof/definition method: Compose existing exact projection/finite covariance identities, with explicit pointwise or real-ring normalization instead of new fold proofs.
 Library reuse: Stdlib.List/FunctionalExtensionality/Reals/Lra/Ring, FiniteSum's exact list sums, previously kernel-checked two-cell projection, nested projection, and conditional covariance theorems.
 Boundary: Explicit finite occurrence lists with real weights and deterministic event partitions only; no arbitrary L1 conditional expectation, Gaussian conditioning, or empirical IQ claim.
 *)
Theorem finite_two_cell_original_fitted_covariance :
 forall (A : Type) (xs : list A) (weight f g : A -> R)
 (event : A -> bool),
 0 < finite_true_mass xs weight event ->
 0 < finite_false_mass xs weight event ->
 finite_centered_cross xs weight f
   (finite_two_cell_prediction xs weight g event) =
 finite_fitted_cross xs weight f g event.
Proof.
 intros A xs weight f g event Ht Hf.
 assert (Hm : finite_weight_mass xs weight <> 0).
 { apply Rgt_not_eq.
   apply finite_two_cell_total_mass_positive with (event:=event); assumption. }
 transitivity (finite_centered_cross xs weight
   (fun x=>finite_two_cell_prediction xs weight f event x+
     finite_two_cell_residual xs weight f event x)
   (finite_two_cell_prediction xs weight g event)).
 { apply finite_centered_cross_pointwise_ext.
   - intro x; unfold finite_two_cell_residual; ring.
   - intro x; reflexivity. }
 rewrite (finite_centered_cross_add_first A xs weight
   (finite_two_cell_prediction xs weight f event)
   (finite_two_cell_residual xs weight f event)
   (finite_two_cell_prediction xs weight g event) Hm).
 rewrite (finite_two_cell_residual_fitted_covariance_zero A xs weight f g event Ht Hf).
 unfold finite_fitted_cross.
 ring.
Qed.

(**
 [finite_two_cell_original_residual_covariance] (theorem) — The covariance of an original response with another score's residual equals the covariance of their residuals.
 Mathematical meaning: The covariance of an original response with another score's residual equals the covariance of their residuals.
 Exact checked proposition: forall (A : Type) (xs : list A) (weight f g : A -> R) (event : A -> bool), 0 < finite_true_mass xs weight event -> 0 < finite_false_mass xs weight event -> finite_centered_cross xs weight f (finite_two_cell_residual xs weight g event) = finite_residual_cross xs weight f g event.
 Premises and side conditions: All needed nonzero or positive Boolean cell masses are explicit at use sites; nonnegative individual outcome weights are required for order conclusions. There is no hidden continuity, normality or independence assumption.
 Proof/definition method: Compose existing exact projection/finite covariance identities, with explicit pointwise or real-ring normalization instead of new fold proofs.
 Library reuse: Stdlib.List/FunctionalExtensionality/Reals/Lra/Ring, FiniteSum's exact list sums, previously kernel-checked two-cell projection, nested projection, and conditional covariance theorems.
 Boundary: Explicit finite occurrence lists with real weights and deterministic event partitions only; no arbitrary L1 conditional expectation, Gaussian conditioning, or empirical IQ claim.
 *)
Theorem finite_two_cell_original_residual_covariance :
 forall (A : Type) (xs : list A) (weight f g : A -> R)
 (event : A -> bool),
 0 < finite_true_mass xs weight event ->
 0 < finite_false_mass xs weight event ->
 finite_centered_cross xs weight f
   (finite_two_cell_residual xs weight g event) =
 finite_residual_cross xs weight f g event.
Proof.
 intros A xs weight f g event Ht Hf.
 assert (Hm : finite_weight_mass xs weight <> 0).
 { apply Rgt_not_eq.
   apply finite_two_cell_total_mass_positive with (event:=event); assumption. }
 transitivity (finite_centered_cross xs weight
   (fun x=>finite_two_cell_prediction xs weight f event x+
     finite_two_cell_residual xs weight f event x)
   (finite_two_cell_residual xs weight g event)).
 { apply finite_centered_cross_pointwise_ext.
   - intro x; unfold finite_two_cell_residual; ring.
   - intro x; reflexivity. }
 rewrite (finite_centered_cross_add_first A xs weight
   (finite_two_cell_prediction xs weight f event)
   (finite_two_cell_residual xs weight f event)
   (finite_two_cell_residual xs weight g event) Hm).
 rewrite (finite_two_cell_fitted_residual_covariance_zero A xs weight f g event Ht Hf).
 unfold finite_residual_cross.
 ring.
Qed.

(**
 [finite_two_cell_residual_risk_global] (theorem) — The global finite squared prediction error of the conditional-mean predictor equals the established within-cell risk.
 Mathematical meaning: The global finite squared prediction error of the conditional-mean predictor equals the established within-cell risk.
 Exact checked proposition: forall (A : Type) (xs : list A) (weight score : A -> R) (event : A -> bool), finite_weighted_score xs weight (fun x => finite_two_cell_residual xs weight score event x * finite_two_cell_residual xs weight score event x) = finite_two_cell_risk xs weight score event (finite_true_mean xs weight score event) (finite_false_mean xs weight score event).
 Premises and side conditions: All needed nonzero or positive Boolean cell masses are explicit at use sites; nonnegative individual outcome weights are required for order conclusions. There is no hidden continuity, normality or independence assumption.
 Proof/definition method: Compose existing exact projection/finite covariance identities, with explicit pointwise or real-ring normalization instead of new fold proofs.
 Library reuse: Stdlib.List/FunctionalExtensionality/Reals/Lra/Ring, FiniteSum's exact list sums, previously kernel-checked two-cell projection, nested projection, and conditional covariance theorems.
 Boundary: Explicit finite occurrence lists with real weights and deterministic event partitions only; no arbitrary L1 conditional expectation, Gaussian conditioning, or empirical IQ claim.
 *)
Theorem finite_two_cell_residual_risk_global :
 forall (A : Type) (xs : list A) (weight score : A -> R)
 (event : A -> bool),
 finite_weighted_score xs weight
   (fun x => finite_two_cell_residual xs weight score event x *
     finite_two_cell_residual xs weight score event x) =
 finite_two_cell_risk xs weight score event
   (finite_true_mean xs weight score event)
   (finite_false_mean xs weight score event).
Proof.
 intros A xs weight score event.
 symmetry.
 rewrite finite_two_cell_risk_global_representation.
 unfold finite_weighted_score, finite_two_cell_residual, finite_two_cell_prediction.
 reflexivity.
Qed.

(**
 [finite_two_cell_risk_unique_minimizer] (theorem) — Strictly positive cell masses give uniqueness of the pair of least-squares conditional predictions.
 Mathematical meaning: Strictly positive cell masses give uniqueness of the pair of least-squares conditional predictions.
 Exact checked proposition: forall (A : Type) (xs : list A) (weight score : A -> R) (event : A -> bool) (a b : R), 0 < finite_true_mass xs weight event -> 0 < finite_false_mass xs weight event -> finite_two_cell_risk xs weight score event a b = finite_two_cell_risk xs weight score event (finite_true_mean xs weight score event) (finite_false_mean xs weight score event) -> a = finite_true_mean xs weight score event /\ b = finite_false_mean xs weight score event.
 Premises and side conditions: All needed nonzero or positive Boolean cell masses are explicit at use sites; nonnegative individual outcome weights are required for order conclusions. There is no hidden continuity, normality or independence assumption.
 Proof/definition method: Compose existing exact projection/finite covariance identities, with explicit pointwise or real-ring normalization instead of new fold proofs.
 Library reuse: Stdlib.List/FunctionalExtensionality/Reals/Lra/Ring, FiniteSum's exact list sums, previously kernel-checked two-cell projection, nested projection, and conditional covariance theorems.
 Boundary: Explicit finite occurrence lists with real weights and deterministic event partitions only; no arbitrary L1 conditional expectation, Gaussian conditioning, or empirical IQ claim.
 *)
Theorem finite_two_cell_risk_unique_minimizer :
 forall (A : Type) (xs : list A) (weight score : A -> R)
 (event : A -> bool) (a b : R),
 0 < finite_true_mass xs weight event ->
 0 < finite_false_mass xs weight event ->
 finite_two_cell_risk xs weight score event a b =
 finite_two_cell_risk xs weight score event
   (finite_true_mean xs weight score event)
   (finite_false_mean xs weight score event) ->
 a = finite_true_mean xs weight score event /\
 b = finite_false_mean xs weight score event.
Proof.
 intros A xs weight score event a b Ht Hf Hrisk.
 unfold finite_two_cell_risk in Hrisk.
 assert (Hlo1 : finite_weighted_loss (filter event xs) weight score
    (finite_true_mean xs weight score event) <=
    finite_weighted_loss (filter event xs) weight score a).
 { apply finite_weighted_loss_minimizer; exact Ht. }
 assert (Hlo2 : finite_weighted_loss (filter (fun x=>negb(event x)) xs) weight score
    (finite_false_mean xs weight score event) <=
    finite_weighted_loss (filter (fun x=>negb(event x)) xs) weight score b).
 { apply finite_weighted_loss_minimizer; exact Hf. }
 assert (Heq1 : finite_weighted_loss (filter event xs) weight score a =
    finite_weighted_loss (filter event xs) weight score
    (finite_true_mean xs weight score event)) by lra.
 assert (Heq2 : finite_weighted_loss (filter (fun x=>negb(event x)) xs) weight score b =
    finite_weighted_loss (filter (fun x=>negb(event x)) xs) weight score
    (finite_false_mean xs weight score event)) by lra.
 split.
 - unfold finite_true_mean in *.
   apply (finite_weighted_loss_unique_minimizer A
     (filter event xs) weight score a Ht); exact Heq1.
 - unfold finite_false_mean in *.
   apply (finite_weighted_loss_unique_minimizer A
     (filter (fun x=>negb(event x)) xs) weight score b Hf); exact Heq2.
Qed.

