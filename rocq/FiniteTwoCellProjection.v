(** Module: FiniteTwoCellProjection.v
 Purpose: Formalize a nontrivial finite-outcome conditional-expectation
 projection for a Boolean observed partition: tower, residual
 orthogonality, best measurable squared-error prediction, and
 the law of total variance. These directly correspond to the finite
 counterpart of claims identified in the report theorem inventory.
 Mathematical representation: An arbitrary type A, a finite list of
 outcome occurrences, a real weight function, and a Boolean observation
 event. All real aggregations use FiniteSum.finite_sum; stdlib filter
 creates the two disjoint occurrence multisets. No new summation fold,
 sigma-algebra data type, or probability-measure axioms are introduced.
 Explicit hypotheses: Nonzero observed-cell masses for conditional
 means; positive cell masses for least-squares optimality; nonnegative
 weights for nonnegative-risk and zero-support conclusions. Algebraic
 identities may apply even to signed weights.
 Library use: Rocq 9.2 Stdlib Reals, Lra, Psatz, Field, List, Bool;
 maintained FiniteSum.finite_sum_filter_partition, finite_sum_ext,
 finite_sum_add, finite_sum_scale, finite_sum_nonnegative_zero_iff
 and Rle_0_sqr, Rmult_integral.
 Limitations: This establishes conditioning only for an explicitly
 enumerated finite sample and one Boolean observation partition.
 It does NOT establish general L1 conditional expectation, countable
 additivity, Gaussian conditional laws or empirical IQ calibration.
 Reproduction: rocq compile FiniteTwoCellProjection.v after FiniteSum.v
 and standard repository prerequisites under pinned Rocq 9.2.
 AI disclosure: OpenAI assisted with all formal source and comments.
 The kernel and CI, not these comments, verify completed proof terms.
 *)
From Stdlib Require Import Reals Lra Psatz List Bool.
Require Import FiniteSum.
Import ListNotations.
Open Scope R_scope.

(**
 [finite_weight_mass] (definition) — The total mass of the finite weighted sample, reusing the shared finite sum.
 Mathematical meaning: The total mass of the finite weighted sample, reusing the shared finite sum.
 Exact declaration: Definition finite_weight_mass {A : Type} (samples : list A) (weight : A -> R) : R := finite_sum weight samples.
 Premises and side conditions: Finite outcome occurrences, Boolean-cell selection, and real score weights are explicit. A nonzero cell mass is required where a conditional mean divides, and positivity is required only for order/optimality conclusions.
 Proof/definition method: Transparent wrapper around Rocq's existing finite sum and Stdlib.List.filter; no new primitive.
 Library reuse: Stdlib.List.filter/filter_In, Stdlib.Reals/Lra/Psatz/Field/Ring, FiniteSum.finite_sum/finite_sum_filter_partition and existing nonnegative-zero-support and scaling lemmas. No duplicated finite-sum recursion.
 Boundary: Deterministic finite weighted projection and variance algebra only; continuous Gaussian conditioning, measurable conditional expectation and empirical modeling are not proved.
 *)
Definition finite_weight_mass {A : Type} (samples : list A) (weight : A -> R) : R := finite_sum weight samples.

(**
 [finite_weighted_score] (definition) — The finite unnormalized score moment defined with the existing shared list sum.
 Mathematical meaning: The finite unnormalized score moment defined with the existing shared list sum.
 Exact declaration: Definition finite_weighted_score {A : Type} (samples : list A) (weight score : A -> R) : R := finite_sum (fun x => weight x*score x) samples.
 Premises and side conditions: Finite outcome occurrences, Boolean-cell selection, and real score weights are explicit. A nonzero cell mass is required where a conditional mean divides, and positivity is required only for order/optimality conclusions.
 Proof/definition method: Transparent wrapper around Rocq's existing finite sum and Stdlib.List.filter; no new primitive.
 Library reuse: Stdlib.List.filter/filter_In, Stdlib.Reals/Lra/Psatz/Field/Ring, FiniteSum.finite_sum/finite_sum_filter_partition and existing nonnegative-zero-support and scaling lemmas. No duplicated finite-sum recursion.
 Boundary: Deterministic finite weighted projection and variance algebra only; continuous Gaussian conditioning, measurable conditional expectation and empirical modeling are not proved.
 *)
Definition finite_weighted_score {A : Type} (samples : list A) (weight score : A -> R) : R := finite_sum (fun x => weight x*score x) samples.

(**
 [finite_weighted_loss] (definition) — Weighted squared loss of a constant prediction on a finite weighted sample.
 Mathematical meaning: Weighted squared loss of a constant prediction on a finite weighted sample.
 Exact declaration: Definition finite_weighted_loss {A : Type} (samples : list A) (weight score : A -> R) (a : R) : R := finite_sum (fun x => weight x*(score x-a)*(score x-a)) samples.
 Premises and side conditions: Finite outcome occurrences, Boolean-cell selection, and real score weights are explicit. A nonzero cell mass is required where a conditional mean divides, and positivity is required only for order/optimality conclusions.
 Proof/definition method: Transparent wrapper around Rocq's existing finite sum and Stdlib.List.filter; no new primitive.
 Library reuse: Stdlib.List.filter/filter_In, Stdlib.Reals/Lra/Psatz/Field/Ring, FiniteSum.finite_sum/finite_sum_filter_partition and existing nonnegative-zero-support and scaling lemmas. No duplicated finite-sum recursion.
 Boundary: Deterministic finite weighted projection and variance algebra only; continuous Gaussian conditioning, measurable conditional expectation and empirical modeling are not proved.
 *)
Definition finite_weighted_loss {A : Type} (samples : list A) (weight score : A -> R) (a : R) : R := finite_sum (fun x => weight x*(score x-a)*(score x-a)) samples.

(**
 [finite_weighted_mean] (definition) — The finite weighted conditional mean, with nonzero total mass imposed at use sites.
 Mathematical meaning: The finite weighted conditional mean, with nonzero total mass imposed at use sites.
 Exact declaration: Definition finite_weighted_mean {A : Type} (samples : list A) (weight score : A -> R) : R := finite_weighted_score samples weight score / finite_weight_mass samples weight.
 Premises and side conditions: Finite outcome occurrences, Boolean-cell selection, and real score weights are explicit. A nonzero cell mass is required where a conditional mean divides, and positivity is required only for order/optimality conclusions.
 Proof/definition method: Transparent wrapper around Rocq's existing finite sum and Stdlib.List.filter; no new primitive.
 Library reuse: Stdlib.List.filter/filter_In, Stdlib.Reals/Lra/Psatz/Field/Ring, FiniteSum.finite_sum/finite_sum_filter_partition and existing nonnegative-zero-support and scaling lemmas. No duplicated finite-sum recursion.
 Boundary: Deterministic finite weighted projection and variance algebra only; continuous Gaussian conditioning, measurable conditional expectation and empirical modeling are not proved.
 *)
Definition finite_weighted_mean {A : Type} (samples : list A) (weight score : A -> R) : R := finite_weighted_score samples weight score / finite_weight_mass samples weight.

(**
 [finite_true_mass] (definition) — Total mass of the observations selected by a Boolean event.
 Mathematical meaning: Total mass of the observations selected by a Boolean event.
 Exact declaration: Definition finite_true_mass {A : Type} (samples : list A) (weight : A -> R) (event : A -> bool) : R := finite_weight_mass (filter event samples) weight.
 Premises and side conditions: Finite outcome occurrences, Boolean-cell selection, and real score weights are explicit. A nonzero cell mass is required where a conditional mean divides, and positivity is required only for order/optimality conclusions.
 Proof/definition method: Transparent wrapper around Rocq's existing finite sum and Stdlib.List.filter; no new primitive.
 Library reuse: Stdlib.List.filter/filter_In, Stdlib.Reals/Lra/Psatz/Field/Ring, FiniteSum.finite_sum/finite_sum_filter_partition and existing nonnegative-zero-support and scaling lemmas. No duplicated finite-sum recursion.
 Boundary: Deterministic finite weighted projection and variance algebra only; continuous Gaussian conditioning, measurable conditional expectation and empirical modeling are not proved.
 *)
Definition finite_true_mass {A : Type} (samples : list A) (weight : A -> R) (event : A -> bool) : R := finite_weight_mass (filter event samples) weight.

(**
 [finite_false_mass] (definition) — Total mass of the complementary observed event.
 Mathematical meaning: Total mass of the complementary observed event.
 Exact declaration: Definition finite_false_mass {A : Type} (samples : list A) (weight : A -> R) (event : A -> bool) : R := finite_weight_mass (filter (fun x => negb (event x)) samples) weight.
 Premises and side conditions: Finite outcome occurrences, Boolean-cell selection, and real score weights are explicit. A nonzero cell mass is required where a conditional mean divides, and positivity is required only for order/optimality conclusions.
 Proof/definition method: Transparent wrapper around Rocq's existing finite sum and Stdlib.List.filter; no new primitive.
 Library reuse: Stdlib.List.filter/filter_In, Stdlib.Reals/Lra/Psatz/Field/Ring, FiniteSum.finite_sum/finite_sum_filter_partition and existing nonnegative-zero-support and scaling lemmas. No duplicated finite-sum recursion.
 Boundary: Deterministic finite weighted projection and variance algebra only; continuous Gaussian conditioning, measurable conditional expectation and empirical modeling are not proved.
 *)
Definition finite_false_mass {A : Type} (samples : list A) (weight : A -> R) (event : A -> bool) : R := finite_weight_mass (filter (fun x => negb (event x)) samples) weight.

(**
 [finite_true_mean] (definition) — The conditional mean on the observed event's positive-mass cell.
 Mathematical meaning: The conditional mean on the observed event's positive-mass cell.
 Exact declaration: Definition finite_true_mean {A : Type} (samples : list A) (weight score : A -> R) (event : A -> bool) : R := finite_weighted_mean (filter event samples) weight score.
 Premises and side conditions: Finite outcome occurrences, Boolean-cell selection, and real score weights are explicit. A nonzero cell mass is required where a conditional mean divides, and positivity is required only for order/optimality conclusions.
 Proof/definition method: Transparent wrapper around Rocq's existing finite sum and Stdlib.List.filter; no new primitive.
 Library reuse: Stdlib.List.filter/filter_In, Stdlib.Reals/Lra/Psatz/Field/Ring, FiniteSum.finite_sum/finite_sum_filter_partition and existing nonnegative-zero-support and scaling lemmas. No duplicated finite-sum recursion.
 Boundary: Deterministic finite weighted projection and variance algebra only; continuous Gaussian conditioning, measurable conditional expectation and empirical modeling are not proved.
 *)
Definition finite_true_mean {A : Type} (samples : list A) (weight score : A -> R) (event : A -> bool) : R := finite_weighted_mean (filter event samples) weight score.

(**
 [finite_false_mean] (definition) — The conditional mean on the complementary positive-mass cell.
 Mathematical meaning: The conditional mean on the complementary positive-mass cell.
 Exact declaration: Definition finite_false_mean {A : Type} (samples : list A) (weight score : A -> R) (event : A -> bool) : R := finite_weighted_mean (filter (fun x => negb (event x)) samples) weight score.
 Premises and side conditions: Finite outcome occurrences, Boolean-cell selection, and real score weights are explicit. A nonzero cell mass is required where a conditional mean divides, and positivity is required only for order/optimality conclusions.
 Proof/definition method: Transparent wrapper around Rocq's existing finite sum and Stdlib.List.filter; no new primitive.
 Library reuse: Stdlib.List.filter/filter_In, Stdlib.Reals/Lra/Psatz/Field/Ring, FiniteSum.finite_sum/finite_sum_filter_partition and existing nonnegative-zero-support and scaling lemmas. No duplicated finite-sum recursion.
 Boundary: Deterministic finite weighted projection and variance algebra only; continuous Gaussian conditioning, measurable conditional expectation and empirical modeling are not proved.
 *)
Definition finite_false_mean {A : Type} (samples : list A) (weight score : A -> R) (event : A -> bool) : R := finite_weighted_mean (filter (fun x => negb (event x)) samples) weight score.

(**
 [finite_two_cell_prediction] (definition) — The finite conditional-score predictor measurable with respect to the observed Boolean cell.
 Mathematical meaning: The finite conditional-score predictor measurable with respect to the observed Boolean cell.
 Exact declaration: Definition finite_two_cell_prediction {A : Type} (samples : list A) (weight score : A -> R) (event : A -> bool) (x : A) : R := if event x then finite_true_mean samples weight score event else finite_false_mean samples weight score event.
 Premises and side conditions: Finite outcome occurrences, Boolean-cell selection, and real score weights are explicit. A nonzero cell mass is required where a conditional mean divides, and positivity is required only for order/optimality conclusions.
 Proof/definition method: Transparent wrapper around Rocq's existing finite sum and Stdlib.List.filter; no new primitive.
 Library reuse: Stdlib.List.filter/filter_In, Stdlib.Reals/Lra/Psatz/Field/Ring, FiniteSum.finite_sum/finite_sum_filter_partition and existing nonnegative-zero-support and scaling lemmas. No duplicated finite-sum recursion.
 Boundary: Deterministic finite weighted projection and variance algebra only; continuous Gaussian conditioning, measurable conditional expectation and empirical modeling are not proved.
 *)
Definition finite_two_cell_prediction {A : Type} (samples : list A) (weight score : A -> R) (event : A -> bool) (x : A) : R := if event x then finite_true_mean samples weight score event else finite_false_mean samples weight score event.

(**
 [finite_two_cell_risk] (definition) — Unnormalized quadratic risk of an arbitrary event-measurable two-constant predictor.
 Mathematical meaning: Unnormalized quadratic risk of an arbitrary event-measurable two-constant predictor.
 Exact declaration: Definition finite_two_cell_risk {A : Type} (samples : list A) (weight score : A -> R) (event : A -> bool) (a b : R) : R := finite_weighted_loss (filter event samples) weight score a + finite_weighted_loss (filter (fun x => negb (event x)) samples) weight score b.
 Premises and side conditions: Finite outcome occurrences, Boolean-cell selection, and real score weights are explicit. A nonzero cell mass is required where a conditional mean divides, and positivity is required only for order/optimality conclusions.
 Proof/definition method: Transparent wrapper around Rocq's existing finite sum and Stdlib.List.filter; no new primitive.
 Library reuse: Stdlib.List.filter/filter_In, Stdlib.Reals/Lra/Psatz/Field/Ring, FiniteSum.finite_sum/finite_sum_filter_partition and existing nonnegative-zero-support and scaling lemmas. No duplicated finite-sum recursion.
 Boundary: Deterministic finite weighted projection and variance algebra only; continuous Gaussian conditioning, measurable conditional expectation and empirical modeling are not proved.
 *)
Definition finite_two_cell_risk {A : Type} (samples : list A) (weight score : A -> R) (event : A -> bool) (a b : R) : R := finite_weighted_loss (filter event samples) weight score a + finite_weighted_loss (filter (fun x => negb (event x)) samples) weight score b.

(**
 [finite_weighted_score_sub] (theorem) — Weighted expectation of a score difference is exactly the difference of the two weighted expectations.
 Mathematical meaning: Weighted expectation of a score difference is exactly the difference of the two weighted expectations.
 Exact checked proposition: forall (A : Type) (samples : list A) (weight f g : A -> R), finite_weighted_score samples weight (fun x => f x-g x) = finite_weighted_score samples weight f - finite_weighted_score samples weight g.
 Premises and side conditions: Finite outcome occurrences, Boolean-cell selection, and real score weights are explicit. A nonzero cell mass is required where a conditional mean divides, and positivity is required only for order/optimality conclusions.
 Proof/definition method: Use FiniteSum.finite_sum_ext and finite_sum_sub directly, without list recursion.
 Library reuse: Stdlib.List.filter/filter_In, Stdlib.Reals/Lra/Psatz/Field/Ring, FiniteSum.finite_sum/finite_sum_filter_partition and existing nonnegative-zero-support and scaling lemmas. No duplicated finite-sum recursion.
 Boundary: Deterministic finite weighted projection and variance algebra only; continuous Gaussian conditioning, measurable conditional expectation and empirical modeling are not proved.
 *)
Theorem finite_weighted_score_sub :
 forall (A : Type) (samples : list A) (weight f g : A -> R),
 finite_weighted_score samples weight (fun x => f x-g x) =
 finite_weighted_score samples weight f - finite_weighted_score samples weight g.
Proof.
 intros A samples weight f g.
 unfold finite_weighted_score.
 transitivity (finite_sum (fun x => weight x*f x-weight x*g x) samples).
 { apply finite_sum_ext; intro x; ring. }
 rewrite finite_sum_sub; reflexivity.
Qed.

(**
 [finite_weighted_score_affine] (theorem) — An arbitrary affine score transform has weighted moment a*S+b*M, even for signed weights.
 Mathematical meaning: An arbitrary affine score transform has weighted moment a*S+b*M, even for signed weights.
 Exact checked proposition: forall (A : Type) (samples : list A) (weight f : A -> R) (a b : R), finite_weighted_score samples weight (fun x => a*f x+b) = a*finite_weighted_score samples weight f+b*finite_weight_mass samples weight.
 Premises and side conditions: Finite outcome occurrences, Boolean-cell selection, and real score weights are explicit. A nonzero cell mass is required where a conditional mean divides, and positivity is required only for order/optimality conclusions.
 Proof/definition method: Delegate all affine aggregation to shared finite_sum_add and finite_sum_scale.
 Library reuse: Stdlib.List.filter/filter_In, Stdlib.Reals/Lra/Psatz/Field/Ring, FiniteSum.finite_sum/finite_sum_filter_partition and existing nonnegative-zero-support and scaling lemmas. No duplicated finite-sum recursion.
 Boundary: Deterministic finite weighted projection and variance algebra only; continuous Gaussian conditioning, measurable conditional expectation and empirical modeling are not proved.
 *)
Theorem finite_weighted_score_affine :
 forall (A : Type) (samples : list A) (weight f : A -> R) (a b : R),
 finite_weighted_score samples weight (fun x => a*f x+b) =
 a*finite_weighted_score samples weight f+b*finite_weight_mass samples weight.
Proof.
 intros A samples weight f a b.
 unfold finite_weighted_score, finite_weight_mass.
 transitivity (finite_sum (fun x => a*(weight x*f x)+b*weight x) samples).
 { apply finite_sum_ext; intro x; ring. }
 rewrite finite_sum_add, !finite_sum_scale; ring.
Qed.

(**
 [finite_weighted_score_constant] (theorem) — A constant finite score has expectation equal to that constant times the true total mass.
 Mathematical meaning: A constant finite score has expectation equal to that constant times the true total mass.
 Exact checked proposition: forall (A : Type) (samples : list A) (weight : A -> R) (a : R), finite_weighted_score samples weight (fun _ => a) = a*finite_weight_mass samples weight.
 Premises and side conditions: Finite outcome occurrences, Boolean-cell selection, and real score weights are explicit. A nonzero cell mass is required where a conditional mean divides, and positivity is required only for order/optimality conclusions.
 Proof/definition method: Use finite_sum_ext and finite_sum_scale for the constant score.
 Library reuse: Stdlib.List.filter/filter_In, Stdlib.Reals/Lra/Psatz/Field/Ring, FiniteSum.finite_sum/finite_sum_filter_partition and existing nonnegative-zero-support and scaling lemmas. No duplicated finite-sum recursion.
 Boundary: Deterministic finite weighted projection and variance algebra only; continuous Gaussian conditioning, measurable conditional expectation and empirical modeling are not proved.
 *)
Theorem finite_weighted_score_constant :
 forall (A : Type) (samples : list A) (weight : A -> R) (a : R),
 finite_weighted_score samples weight (fun _ => a) =
 a*finite_weight_mass samples weight.
Proof.
 intros A samples weight a.
 unfold finite_weighted_score, finite_weight_mass.
 transitivity (finite_sum (fun x => a*weight x) samples).
 { apply finite_sum_ext; intro x; ring. }
 apply finite_sum_scale.
Qed.

(**
 [finite_weighted_loss_expansion] (theorem) — The exact quadratic loss equals the second weighted moment minus twice prediction times first moment plus a² times mass.
 Mathematical meaning: The exact quadratic loss equals the second weighted moment minus twice prediction times first moment plus a² times mass.
 Exact checked proposition: forall (A : Type) (samples : list A) (weight score : A -> R) (a : R), finite_weighted_loss samples weight score a = finite_weighted_score samples weight (fun x => score x*score x) - 2*a*finite_weighted_score samples weight score + a*a*finite_weight_mass samples weight.
 Premises and side conditions: Finite outcome occurrences, Boolean-cell selection, and real score weights are explicit. A nonzero cell mass is required where a conditional mean divides, and positivity is required only for order/optimality conclusions.
 Proof/definition method: Use pointwise ring normalization and FiniteSum addition/scaling; no new quadratic fold.
 Library reuse: Stdlib.List.filter/filter_In, Stdlib.Reals/Lra/Psatz/Field/Ring, FiniteSum.finite_sum/finite_sum_filter_partition and existing nonnegative-zero-support and scaling lemmas. No duplicated finite-sum recursion.
 Boundary: Deterministic finite weighted projection and variance algebra only; continuous Gaussian conditioning, measurable conditional expectation and empirical modeling are not proved.
 *)
Theorem finite_weighted_loss_expansion :
 forall (A : Type) (samples : list A) (weight score : A -> R) (a : R),
 finite_weighted_loss samples weight score a =
 finite_weighted_score samples weight (fun x => score x*score x) -
 2*a*finite_weighted_score samples weight score +
 a*a*finite_weight_mass samples weight.
Proof.
 intros A samples weight score a.
 unfold finite_weighted_loss, finite_weighted_score, finite_weight_mass.
 transitivity (finite_sum (fun x =>
    weight x*(score x*score x)+
    ((-2*a)*(weight x*score x)+(a*a)*weight x)) samples).
 { apply finite_sum_ext; intro x; ring. }
 rewrite !finite_sum_add, !finite_sum_scale; ring.
Qed.

(**
 [finite_weighted_mean_mass_identity] (theorem) — Multiplication of a finite weighted mean by the nonzero total mass recovers its exact first moment.
 Mathematical meaning: Multiplication of a finite weighted mean by the nonzero total mass recovers its exact first moment.
 Exact checked proposition: forall (A : Type) (samples : list A) (weight score : A -> R), finite_weight_mass samples weight<>0 -> finite_weight_mass samples weight*finite_weighted_mean samples weight score = finite_weighted_score samples weight score.
 Premises and side conditions: Finite outcome occurrences, Boolean-cell selection, and real score weights are explicit. A nonzero cell mass is required where a conditional mean divides, and positivity is required only for order/optimality conclusions.
 Proof/definition method: Cancel only an explicitly nonzero denominator with Stdlib.Field.
 Library reuse: Stdlib.List.filter/filter_In, Stdlib.Reals/Lra/Psatz/Field/Ring, FiniteSum.finite_sum/finite_sum_filter_partition and existing nonnegative-zero-support and scaling lemmas. No duplicated finite-sum recursion.
 Boundary: Deterministic finite weighted projection and variance algebra only; continuous Gaussian conditioning, measurable conditional expectation and empirical modeling are not proved.
 *)
Theorem finite_weighted_mean_mass_identity :
 forall (A : Type) (samples : list A) (weight score : A -> R),
 finite_weight_mass samples weight<>0 ->
 finite_weight_mass samples weight*finite_weighted_mean samples weight score =
 finite_weighted_score samples weight score.
Proof.
 intros A samples weight score Hmass.
 unfold finite_weighted_mean; field; exact Hmass.
Qed.

(**
 [finite_weighted_centered_score_zero] (theorem) — On any nonzero-mass finite sample, the score residual centered at the weighted mean has exactly zero weighted expectation.
 Mathematical meaning: On any nonzero-mass finite sample, the score residual centered at the weighted mean has exactly zero weighted expectation.
 Exact checked proposition: forall (A : Type) (samples : list A) (weight score : A -> R), finite_weight_mass samples weight<>0 -> finite_weighted_score samples weight (fun x => score x-finite_weighted_mean samples weight score)=0.
 Premises and side conditions: Finite outcome occurrences, Boolean-cell selection, and real score weights are explicit. A nonzero cell mass is required where a conditional mean divides, and positivity is required only for order/optimality conclusions.
 Proof/definition method: Combine existing score-subtraction, constant-score and mean-mass identities.
 Library reuse: Stdlib.List.filter/filter_In, Stdlib.Reals/Lra/Psatz/Field/Ring, FiniteSum.finite_sum/finite_sum_filter_partition and existing nonnegative-zero-support and scaling lemmas. No duplicated finite-sum recursion.
 Boundary: Deterministic finite weighted projection and variance algebra only; continuous Gaussian conditioning, measurable conditional expectation and empirical modeling are not proved.
 *)
Theorem finite_weighted_centered_score_zero :
 forall (A : Type) (samples : list A) (weight score : A -> R),
 finite_weight_mass samples weight<>0 ->
 finite_weighted_score samples weight
   (fun x => score x-finite_weighted_mean samples weight score)=0.
Proof.
 intros A samples weight score Hmass.
 rewrite finite_weighted_score_sub.
 rewrite finite_weighted_score_constant.
 pose proof (finite_weighted_mean_mass_identity A samples weight score Hmass) as Hidentity.
 lra.
Qed.

(**
 [finite_weighted_loss_completed_square] (theorem) — Every finite constant-prediction squared loss equals optimal mean-centered loss plus mass times squared deviation from the mean.
 Mathematical meaning: Every finite constant-prediction squared loss equals optimal mean-centered loss plus mass times squared deviation from the mean.
 Exact checked proposition: forall (A : Type) (samples : list A) (weight score : A -> R) (a : R), finite_weight_mass samples weight<>0 -> finite_weighted_loss samples weight score a = finite_weighted_loss samples weight score (finite_weighted_mean samples weight score) + finite_weight_mass samples weight* (a-finite_weighted_mean samples weight score)* (a-finite_weighted_mean samples weight score).
 Premises and side conditions: Finite outcome occurrences, Boolean-cell selection, and real score weights are explicit. A nonzero cell mass is required where a conditional mean divides, and positivity is required only for order/optimality conclusions.
 Proof/definition method: Complete the square algebraically using the verified mean normal equation.
 Library reuse: Stdlib.List.filter/filter_In, Stdlib.Reals/Lra/Psatz/Field/Ring, FiniteSum.finite_sum/finite_sum_filter_partition and existing nonnegative-zero-support and scaling lemmas. No duplicated finite-sum recursion.
 Boundary: Deterministic finite weighted projection and variance algebra only; continuous Gaussian conditioning, measurable conditional expectation and empirical modeling are not proved.
 *)
Theorem finite_weighted_loss_completed_square :
 forall (A : Type) (samples : list A) (weight score : A -> R) (a : R),
 finite_weight_mass samples weight<>0 ->
 finite_weighted_loss samples weight score a =
 finite_weighted_loss samples weight score (finite_weighted_mean samples weight score) +
 finite_weight_mass samples weight*
   (a-finite_weighted_mean samples weight score)*
   (a-finite_weighted_mean samples weight score).
Proof.
 intros A samples weight score a Hmass.
 rewrite !finite_weighted_loss_expansion.
 pose proof (finite_weighted_mean_mass_identity A samples weight score Hmass) as Hidentity.
 nra.
Qed.

(**
 [finite_weighted_loss_nonnegative] (theorem) — Finite weighted squared prediction error is nonnegative whenever every enumerated sample weight is nonnegative.
 Mathematical meaning: Finite weighted squared prediction error is nonnegative whenever every enumerated sample weight is nonnegative.
 Exact checked proposition: forall (A : Type) (samples : list A) (weight score : A -> R) (a : R), (forall x, In x samples -> 0<=weight x) -> 0<=finite_weighted_loss samples weight score a.
 Premises and side conditions: Finite outcome occurrences, Boolean-cell selection, and real score weights are explicit. A nonzero cell mass is required where a conditional mean divides, and positivity is required only for order/optimality conclusions.
 Proof/definition method: Use shared finite_sum_nonnegative and Stdlib.Rle_0_sqr/Rmult_le_pos.
 Library reuse: Stdlib.List.filter/filter_In, Stdlib.Reals/Lra/Psatz/Field/Ring, FiniteSum.finite_sum/finite_sum_filter_partition and existing nonnegative-zero-support and scaling lemmas. No duplicated finite-sum recursion.
 Boundary: Deterministic finite weighted projection and variance algebra only; continuous Gaussian conditioning, measurable conditional expectation and empirical modeling are not proved.
 *)
Theorem finite_weighted_loss_nonnegative :
 forall (A : Type) (samples : list A) (weight score : A -> R) (a : R),
 (forall x, In x samples -> 0<=weight x) ->
 0<=finite_weighted_loss samples weight score a.
Proof.
 intros A samples weight score a Hw.
 unfold finite_weighted_loss.
 apply finite_sum_nonnegative.
 intros x Hin.
 replace (weight x*(score x-a)*(score x-a))
   with (weight x*((score x-a)*(score x-a))) by ring.
 apply Rmult_le_pos.
 - apply Hw; exact Hin.
 - change (0<=Rsqr (score x-a)); apply Rle_0_sqr.
Qed.

(**
 [finite_weighted_loss_minimizer] (theorem) — For positive finite total mass, the true weighted mean minimizes all constant-prediction squared errors.
 Mathematical meaning: For positive finite total mass, the true weighted mean minimizes all constant-prediction squared errors.
 Exact checked proposition: forall (A : Type) (samples : list A) (weight score : A -> R) (a : R), 0<finite_weight_mass samples weight -> finite_weighted_loss samples weight score (finite_weighted_mean samples weight score) <= finite_weighted_loss samples weight score a.
 Premises and side conditions: Finite outcome occurrences, Boolean-cell selection, and real score weights are explicit. A nonzero cell mass is required where a conditional mean divides, and positivity is required only for order/optimality conclusions.
 Proof/definition method: Reuse completed-square equality and Stdlib square/nonnegative-product lemmas.
 Library reuse: Stdlib.List.filter/filter_In, Stdlib.Reals/Lra/Psatz/Field/Ring, FiniteSum.finite_sum/finite_sum_filter_partition and existing nonnegative-zero-support and scaling lemmas. No duplicated finite-sum recursion.
 Boundary: Deterministic finite weighted projection and variance algebra only; continuous Gaussian conditioning, measurable conditional expectation and empirical modeling are not proved.
 *)
Theorem finite_weighted_loss_minimizer :
 forall (A : Type) (samples : list A) (weight score : A -> R) (a : R),
 0<finite_weight_mass samples weight ->
 finite_weighted_loss samples weight score (finite_weighted_mean samples weight score) <=
 finite_weighted_loss samples weight score a.
Proof.
 intros A samples weight score a Hmass.
 rewrite (finite_weighted_loss_completed_square A samples weight score a) by lra.
 assert (Hs : 0<=Rsqr (a-finite_weighted_mean samples weight score))
   by apply Rle_0_sqr.
 unfold Rsqr in Hs.
 assert (Hpen : 0<=finite_weight_mass samples weight*
    ((a-finite_weighted_mean samples weight score)*
     (a-finite_weighted_mean samples weight score))).
 { apply Rmult_le_pos; [lra|exact Hs]. }
 replace (finite_weight_mass samples weight*
    (a-finite_weighted_mean samples weight score)*
    (a-finite_weighted_mean samples weight score))
   with (finite_weight_mass samples weight*
    ((a-finite_weighted_mean samples weight score)*
     (a-finite_weighted_mean samples weight score))) by ring.
 lra.
Qed.

(**
 [finite_weighted_loss_unique_minimizer] (theorem) — With strictly positive mass, no constant other than the exact weighted mean attains the minimum squared error.
 Mathematical meaning: With strictly positive mass, no constant other than the exact weighted mean attains the minimum squared error.
 Exact checked proposition: forall (A : Type) (samples : list A) (weight score : A -> R) (a : R), 0<finite_weight_mass samples weight -> finite_weighted_loss samples weight score a = finite_weighted_loss samples weight score (finite_weighted_mean samples weight score) -> a=finite_weighted_mean samples weight score.
 Premises and side conditions: Finite outcome occurrences, Boolean-cell selection, and real score weights are explicit. A nonzero cell mass is required where a conditional mean divides, and positivity is required only for order/optimality conclusions.
 Proof/definition method: Reuse square completion, Rmult_integral and positive-mass cancellation to prove uniqueness.
 Library reuse: Stdlib.List.filter/filter_In, Stdlib.Reals/Lra/Psatz/Field/Ring, FiniteSum.finite_sum/finite_sum_filter_partition and existing nonnegative-zero-support and scaling lemmas. No duplicated finite-sum recursion.
 Boundary: Deterministic finite weighted projection and variance algebra only; continuous Gaussian conditioning, measurable conditional expectation and empirical modeling are not proved.
 *)
Theorem finite_weighted_loss_unique_minimizer :
 forall (A : Type) (samples : list A) (weight score : A -> R) (a : R),
 0<finite_weight_mass samples weight ->
 finite_weighted_loss samples weight score a =
 finite_weighted_loss samples weight score (finite_weighted_mean samples weight score) ->
 a=finite_weighted_mean samples weight score.
Proof.
 intros A samples weight score a Hmass Heq.
 rewrite finite_weighted_loss_completed_square in Heq by lra.
 assert (Hsq :
    (a-finite_weighted_mean samples weight score)*
    (a-finite_weighted_mean samples weight score)=0).
 { assert (Hprod : finite_weight_mass samples weight*
     ((a-finite_weighted_mean samples weight score)*
      (a-finite_weighted_mean samples weight score))=0) by nra.
   apply Rmult_integral in Hprod.
   destruct Hprod as [Hz|Hz]; [lra|exact Hz]. }
 nra.
Qed.

(**
 [finite_weighted_loss_zero_iff_supported_constant] (theorem) — With nonnegative weights, vanishing squared error is equivalent to the score being constant at every strictly positive-weight sample occurrence.
 Mathematical meaning: With nonnegative weights, vanishing squared error is equivalent to the score being constant at every strictly positive-weight sample occurrence.
 Exact checked proposition: forall (A : Type) (samples : list A) (weight score : A -> R) (a : R), (forall x, In x samples -> 0<=weight x) -> (finite_weighted_loss samples weight score a=0 <-> forall x, In x samples -> 0<weight x -> score x=a).
 Premises and side conditions: Finite outcome occurrences, Boolean-cell selection, and real score weights are explicit. A nonzero cell mass is required where a conditional mean divides, and positivity is required only for order/optimality conclusions.
 Proof/definition method: Specialize FiniteSum's exact nonnegative-zero-support theorem and Stdlib.Rmult_integral.
 Library reuse: Stdlib.List.filter/filter_In, Stdlib.Reals/Lra/Psatz/Field/Ring, FiniteSum.finite_sum/finite_sum_filter_partition and existing nonnegative-zero-support and scaling lemmas. No duplicated finite-sum recursion.
 Boundary: Deterministic finite weighted projection and variance algebra only; continuous Gaussian conditioning, measurable conditional expectation and empirical modeling are not proved.
 *)
Theorem finite_weighted_loss_zero_iff_supported_constant :
 forall (A : Type) (samples : list A) (weight score : A -> R) (a : R),
 (forall x, In x samples -> 0<=weight x) ->
 (finite_weighted_loss samples weight score a=0 <->
   forall x, In x samples -> 0<weight x -> score x=a).
Proof.
 intros A samples weight score a Hw.
 assert (Hiff : finite_weighted_loss samples weight score a=0 <->
   forall x, In x samples -> weight x*(score x-a)*(score x-a)=0).
 { unfold finite_weighted_loss.
   apply finite_sum_nonnegative_zero_iff.
   intros x Hin.
   replace (weight x*(score x-a)*(score x-a))
     with (weight x*((score x-a)*(score x-a))) by ring.
   apply Rmult_le_pos.
   - apply Hw; exact Hin.
   - change (0<=Rsqr (score x-a)); apply Rle_0_sqr. }
 split.
 - intros Hz x Hin Hpos.
   pose proof ((proj1 Hiff) Hz x Hin) as Hprod.
   replace (weight x*(score x-a)*(score x-a))
     with (weight x*((score x-a)*(score x-a))) in Hprod by ring.
   apply Rmult_integral in Hprod.
   destruct Hprod as [Hbad|Hsq]; [lra|nra].
 - intros Hconst.
   apply (proj2 Hiff).
   intros x Hin.
   destruct (Rlt_dec 0 (weight x)) as [Hpos|Hnon].
   + rewrite (Hconst x Hin Hpos); ring.
   + assert (H0 : weight x=0) by (pose proof (Hw x Hin); lra).
     rewrite H0; ring.
Qed.

(**
 [finite_two_cell_mass_partition] (theorem) — The mass of two Boolean observation cells sums to the original total mass, even for signed weights.
 Mathematical meaning: The mass of two Boolean observation cells sums to the original total mass, even for signed weights.
 Exact checked proposition: forall (A : Type) (samples : list A) (weight : A -> R) (event : A -> bool), finite_true_mass samples weight event + finite_false_mass samples weight event = finite_weight_mass samples weight.
 Premises and side conditions: Finite outcome occurrences, Boolean-cell selection, and real score weights are explicit. A nonzero cell mass is required where a conditional mean divides, and positivity is required only for order/optimality conclusions.
 Proof/definition method: Reuse general finite_sum_filter_partition and Stdlib.List.filter.
 Library reuse: Stdlib.List.filter/filter_In, Stdlib.Reals/Lra/Psatz/Field/Ring, FiniteSum.finite_sum/finite_sum_filter_partition and existing nonnegative-zero-support and scaling lemmas. No duplicated finite-sum recursion.
 Boundary: Deterministic finite weighted projection and variance algebra only; continuous Gaussian conditioning, measurable conditional expectation and empirical modeling are not proved.
 *)
Theorem finite_two_cell_mass_partition :
 forall (A : Type) (samples : list A) (weight : A -> R) (event : A -> bool),
 finite_true_mass samples weight event + finite_false_mass samples weight event =
 finite_weight_mass samples weight.
Proof.
 intros A samples weight event.
 unfold finite_true_mass, finite_false_mass, finite_weight_mass.
 apply finite_sum_filter_partition.
Qed.

(**
 [finite_two_cell_score_partition] (theorem) — The original weighted first score moment decomposes exactly into observed and complementary cells.
 Mathematical meaning: The original weighted first score moment decomposes exactly into observed and complementary cells.
 Exact checked proposition: forall (A : Type) (samples : list A) (weight score : A -> R) (event : A -> bool), finite_weighted_score (filter event samples) weight score + finite_weighted_score (filter (fun x=>negb(event x)) samples) weight score = finite_weighted_score samples weight score.
 Premises and side conditions: Finite outcome occurrences, Boolean-cell selection, and real score weights are explicit. A nonzero cell mass is required where a conditional mean divides, and positivity is required only for order/optimality conclusions.
 Proof/definition method: Apply the generic partition theorem to the existing weighted first-moment integrand.
 Library reuse: Stdlib.List.filter/filter_In, Stdlib.Reals/Lra/Psatz/Field/Ring, FiniteSum.finite_sum/finite_sum_filter_partition and existing nonnegative-zero-support and scaling lemmas. No duplicated finite-sum recursion.
 Boundary: Deterministic finite weighted projection and variance algebra only; continuous Gaussian conditioning, measurable conditional expectation and empirical modeling are not proved.
 *)
Theorem finite_two_cell_score_partition :
 forall (A : Type) (samples : list A) (weight score : A -> R) (event : A -> bool),
 finite_weighted_score (filter event samples) weight score +
 finite_weighted_score (filter (fun x=>negb(event x)) samples) weight score =
 finite_weighted_score samples weight score.
Proof.
 intros A samples weight score event.
 unfold finite_weighted_score.
 apply finite_sum_filter_partition.
Qed.

(**
 [finite_two_cell_second_partition] (theorem) — The exact weighted second score moment splits over the two observed outcome cells.
 Mathematical meaning: The exact weighted second score moment splits over the two observed outcome cells.
 Exact checked proposition: forall (A : Type) (samples : list A) (weight score : A -> R) (event : A -> bool), finite_weighted_score (filter event samples) weight (fun x=>score x*score x) + finite_weighted_score (filter (fun x=>negb(event x)) samples) weight (fun x=>score x*score x) = finite_weighted_score samples weight (fun x=>score x*score x).
 Premises and side conditions: Finite outcome occurrences, Boolean-cell selection, and real score weights are explicit. A nonzero cell mass is required where a conditional mean divides, and positivity is required only for order/optimality conclusions.
 Proof/definition method: Apply shared finite_sum_filter_partition to the square-score integrand.
 Library reuse: Stdlib.List.filter/filter_In, Stdlib.Reals/Lra/Psatz/Field/Ring, FiniteSum.finite_sum/finite_sum_filter_partition and existing nonnegative-zero-support and scaling lemmas. No duplicated finite-sum recursion.
 Boundary: Deterministic finite weighted projection and variance algebra only; continuous Gaussian conditioning, measurable conditional expectation and empirical modeling are not proved.
 *)
Theorem finite_two_cell_second_partition :
 forall (A : Type) (samples : list A) (weight score : A -> R) (event : A -> bool),
 finite_weighted_score (filter event samples) weight
     (fun x=>score x*score x) +
 finite_weighted_score (filter (fun x=>negb(event x)) samples) weight
     (fun x=>score x*score x) =
 finite_weighted_score samples weight (fun x=>score x*score x).
Proof.
 intros A samples weight score event.
 unfold finite_weighted_score.
 apply finite_sum_filter_partition.
Qed.

(**
 [finite_two_cell_loss_partition] (theorem) — For any common predictor constant the total weighted squared error is exactly the sum of the two disjoint cell losses.
 Mathematical meaning: For any common predictor constant the total weighted squared error is exactly the sum of the two disjoint cell losses.
 Exact checked proposition: forall (A : Type) (samples : list A) (weight score : A -> R) (event : A -> bool) (a : R), finite_weighted_loss (filter event samples) weight score a + finite_weighted_loss (filter (fun x=>negb(event x)) samples) weight score a = finite_weighted_loss samples weight score a.
 Premises and side conditions: Finite outcome occurrences, Boolean-cell selection, and real score weights are explicit. A nonzero cell mass is required where a conditional mean divides, and positivity is required only for order/optimality conclusions.
 Proof/definition method: Reuse the general filter partition result, with no new quadratic list induction.
 Library reuse: Stdlib.List.filter/filter_In, Stdlib.Reals/Lra/Psatz/Field/Ring, FiniteSum.finite_sum/finite_sum_filter_partition and existing nonnegative-zero-support and scaling lemmas. No duplicated finite-sum recursion.
 Boundary: Deterministic finite weighted projection and variance algebra only; continuous Gaussian conditioning, measurable conditional expectation and empirical modeling are not proved.
 *)
Theorem finite_two_cell_loss_partition :
 forall (A : Type) (samples : list A) (weight score : A -> R)
 (event : A -> bool) (a : R),
 finite_weighted_loss (filter event samples) weight score a +
 finite_weighted_loss (filter (fun x=>negb(event x)) samples) weight score a =
 finite_weighted_loss samples weight score a.
Proof.
 intros A samples weight score event a.
 unfold finite_weighted_loss.
 apply finite_sum_filter_partition.
Qed.

(**
 [finite_two_cell_piecewise_constant_expectation] (theorem) — A two-cell constant predictor's weighted expectation is a times the selected mass plus b times complementary mass.
 Mathematical meaning: A two-cell constant predictor's weighted expectation is a times the selected mass plus b times complementary mass.
 Exact checked proposition: forall (A : Type) (samples : list A) (weight : A -> R) (event : A -> bool) (a b : R), finite_weighted_score samples weight (fun x=>if event x then a else b) = a*finite_true_mass samples weight event + b*finite_false_mass samples weight event.
 Premises and side conditions: Finite outcome occurrences, Boolean-cell selection, and real score weights are explicit. A nonzero cell mass is required where a conditional mean divides, and positivity is required only for order/optimality conclusions.
 Proof/definition method: Represent the predictor as two filtered sums and reuse finite_sum_filter/add/scale.
 Library reuse: Stdlib.List.filter/filter_In, Stdlib.Reals/Lra/Psatz/Field/Ring, FiniteSum.finite_sum/finite_sum_filter_partition and existing nonnegative-zero-support and scaling lemmas. No duplicated finite-sum recursion.
 Boundary: Deterministic finite weighted projection and variance algebra only; continuous Gaussian conditioning, measurable conditional expectation and empirical modeling are not proved.
 *)
Theorem finite_two_cell_piecewise_constant_expectation :
 forall (A : Type) (samples : list A) (weight : A -> R)
 (event : A -> bool) (a b : R),
 finite_weighted_score samples weight (fun x=>if event x then a else b) =
 a*finite_true_mass samples weight event +
 b*finite_false_mass samples weight event.
Proof.
 intros A samples weight event a b.
 unfold finite_weighted_score, finite_true_mass, finite_false_mass, finite_weight_mass.
 transitivity (finite_sum (fun x =>
    (if event x then a*weight x else 0) +
    (if negb(event x) then b*weight x else 0)) samples).
 { apply finite_sum_ext; intro x; destruct (event x); simpl; ring. }
 rewrite finite_sum_add.
 rewrite <- (finite_sum_filter samples event (fun x=>a*weight x)).
 rewrite <- (finite_sum_filter samples (fun x=>negb(event x)) (fun x=>b*weight x)).
 rewrite !finite_sum_scale; ring.
Qed.

(**
 [finite_two_cell_piecewise_score_expectation] (theorem) — The weighted expectation of a score multiplied by an arbitrary event-measurable two-constant function splits into exact cell score moments.
 Mathematical meaning: The weighted expectation of a score multiplied by an arbitrary event-measurable two-constant function splits into exact cell score moments.
 Exact checked proposition: forall (A : Type) (samples : list A) (weight score : A -> R) (event : A -> bool) (a b : R), finite_weighted_score samples weight (fun x=>score x*(if event x then a else b)) = a*finite_weighted_score (filter event samples) weight score+ b*finite_weighted_score (filter (fun x=>negb(event x)) samples) weight score.
 Premises and side conditions: Finite outcome occurrences, Boolean-cell selection, and real score weights are explicit. A nonzero cell mass is required where a conditional mean divides, and positivity is required only for order/optimality conclusions.
 Proof/definition method: Use Stdlib.Bool and the maintained filtered finite-sum linearity.
 Library reuse: Stdlib.List.filter/filter_In, Stdlib.Reals/Lra/Psatz/Field/Ring, FiniteSum.finite_sum/finite_sum_filter_partition and existing nonnegative-zero-support and scaling lemmas. No duplicated finite-sum recursion.
 Boundary: Deterministic finite weighted projection and variance algebra only; continuous Gaussian conditioning, measurable conditional expectation and empirical modeling are not proved.
 *)
Theorem finite_two_cell_piecewise_score_expectation :
 forall (A : Type) (samples : list A) (weight score : A -> R)
 (event : A -> bool) (a b : R),
 finite_weighted_score samples weight
    (fun x=>score x*(if event x then a else b)) =
 a*finite_weighted_score (filter event samples) weight score+
 b*finite_weighted_score (filter (fun x=>negb(event x)) samples) weight score.
Proof.
 intros A samples weight score event a b.
 unfold finite_weighted_score.
 transitivity (finite_sum (fun x =>
    (if event x then a*(weight x*score x) else 0) +
    (if negb(event x) then b*(weight x*score x) else 0)) samples).
 { apply finite_sum_ext; intro x; destruct (event x); simpl; ring. }
 rewrite finite_sum_add.
 rewrite <- (finite_sum_filter samples event (fun x=>a*(weight x*score x))).
 rewrite <- (finite_sum_filter samples (fun x=>negb(event x))
    (fun x=>b*(weight x*score x))).
 rewrite !finite_sum_scale; ring.
Qed.

(**
 [finite_two_cell_tower_expectation] (theorem) — The weighted expectation of the concrete two-cell conditional mean equals the original score expectation.
 Mathematical meaning: The weighted expectation of the concrete two-cell conditional mean equals the original score expectation.
 Exact checked proposition: forall (A : Type) (samples : list A) (weight score : A -> R) (event : A -> bool), finite_true_mass samples weight event<>0 -> finite_false_mass samples weight event<>0 -> finite_weighted_score samples weight (finite_two_cell_prediction samples weight score event) = finite_weighted_score samples weight score.
 Premises and side conditions: Finite outcome occurrences, Boolean-cell selection, and real score weights are explicit. A nonzero cell mass is required where a conditional mean divides, and positivity is required only for order/optimality conclusions.
 Proof/definition method: Combine the exact two-cell constant expectation with both weighted-mean mass identities and the partitioned score.
 Library reuse: Stdlib.List.filter/filter_In, Stdlib.Reals/Lra/Psatz/Field/Ring, FiniteSum.finite_sum/finite_sum_filter_partition and existing nonnegative-zero-support and scaling lemmas. No duplicated finite-sum recursion.
 Boundary: Deterministic finite weighted projection and variance algebra only; continuous Gaussian conditioning, measurable conditional expectation and empirical modeling are not proved.
 *)
Theorem finite_two_cell_tower_expectation :
 forall (A : Type) (samples : list A) (weight score : A -> R)
 (event : A -> bool),
 finite_true_mass samples weight event<>0 ->
 finite_false_mass samples weight event<>0 ->
 finite_weighted_score samples weight
    (finite_two_cell_prediction samples weight score event) =
 finite_weighted_score samples weight score.
Proof.
 intros A samples weight score event Htrue Hfalse.
 unfold finite_two_cell_prediction.
 rewrite finite_two_cell_piecewise_constant_expectation.
 pose proof (finite_weighted_mean_mass_identity A (filter event samples)
   weight score Htrue) as Ht.
 pose proof (finite_weighted_mean_mass_identity A
   (filter (fun x=>negb(event x)) samples) weight score Hfalse) as Hf.
 unfold finite_true_mean, finite_false_mean, finite_true_mass, finite_false_mass.
 rewrite <- (finite_two_cell_score_partition A samples weight score event).
 nra.
Qed.

(**
 [finite_two_cell_residual_mean_zero] (theorem) — The prediction residual of the finite two-cell conditional mean has global weighted expectation exactly zero.
 Mathematical meaning: The prediction residual of the finite two-cell conditional mean has global weighted expectation exactly zero.
 Exact checked proposition: forall (A : Type) (samples : list A) (weight score : A -> R) (event : A -> bool), finite_true_mass samples weight event<>0 -> finite_false_mass samples weight event<>0 -> finite_weighted_score samples weight (fun x=>score x-finite_two_cell_prediction samples weight score event x)=0.
 Premises and side conditions: Finite outcome occurrences, Boolean-cell selection, and real score weights are explicit. A nonzero cell mass is required where a conditional mean divides, and positivity is required only for order/optimality conclusions.
 Proof/definition method: Apply the existing weighted-score subtraction and two-cell tower equality.
 Library reuse: Stdlib.List.filter/filter_In, Stdlib.Reals/Lra/Psatz/Field/Ring, FiniteSum.finite_sum/finite_sum_filter_partition and existing nonnegative-zero-support and scaling lemmas. No duplicated finite-sum recursion.
 Boundary: Deterministic finite weighted projection and variance algebra only; continuous Gaussian conditioning, measurable conditional expectation and empirical modeling are not proved.
 *)
Theorem finite_two_cell_residual_mean_zero :
 forall (A : Type) (samples : list A) (weight score : A -> R)
 (event : A -> bool),
 finite_true_mass samples weight event<>0 ->
 finite_false_mass samples weight event<>0 ->
 finite_weighted_score samples weight
   (fun x=>score x-finite_two_cell_prediction samples weight score event x)=0.
Proof.
 intros A samples weight score event Ht Hf.
 rewrite finite_weighted_score_sub.
 rewrite finite_two_cell_tower_expectation by assumption.
 ring.
Qed.

(**
 [finite_two_cell_residual_orthogonal] (theorem) — The finite conditional prediction error is orthogonal to every function constant on each observation cell.
 Mathematical meaning: The finite conditional prediction error is orthogonal to every function constant on each observation cell.
 Exact checked proposition: forall (A : Type) (samples : list A) (weight score : A -> R) (event : A -> bool) (a b : R), finite_true_mass samples weight event<>0 -> finite_false_mass samples weight event<>0 -> finite_weighted_score samples weight (fun x=>(score x-finite_two_cell_prediction samples weight score event x)* (if event x then a else b))=0.
 Premises and side conditions: Finite outcome occurrences, Boolean-cell selection, and real score weights are explicit. A nonzero cell mass is required where a conditional mean divides, and positivity is required only for order/optimality conclusions.
 Proof/definition method: Derive projection orthogonality to every two-cell measurable score using the previously checked piecewise first moments and exact mean normal equations.
 Library reuse: Stdlib.List.filter/filter_In, Stdlib.Reals/Lra/Psatz/Field/Ring, FiniteSum.finite_sum/finite_sum_filter_partition and existing nonnegative-zero-support and scaling lemmas. No duplicated finite-sum recursion.
 Boundary: Deterministic finite weighted projection and variance algebra only; continuous Gaussian conditioning, measurable conditional expectation and empirical modeling are not proved.
 *)
Theorem finite_two_cell_residual_orthogonal :
 forall (A : Type) (samples : list A) (weight score : A -> R)
 (event : A -> bool) (a b : R),
 finite_true_mass samples weight event<>0 ->
 finite_false_mass samples weight event<>0 ->
 finite_weighted_score samples weight
  (fun x=>(score x-finite_two_cell_prediction samples weight score event x)*
    (if event x then a else b))=0.
Proof.
 intros A samples weight score event a b Ht Hf.
 transitivity (
   finite_weighted_score samples weight
     (fun x=>score x*(if event x then a else b)) -
   finite_weighted_score samples weight
     (fun x=>finite_two_cell_prediction samples weight score event x*
       (if event x then a else b))).
 { rewrite <- finite_weighted_score_sub.
   unfold finite_weighted_score.
   apply finite_sum_ext; intro x; ring. }
 rewrite finite_two_cell_piecewise_score_expectation.
 assert (Heq :
  finite_weighted_score samples weight
     (fun x=>finite_two_cell_prediction samples weight score event x*
       (if event x then a else b)) =
  finite_weighted_score samples weight
     (fun x=>if event x
       then finite_true_mean samples weight score event*a
       else finite_false_mean samples weight score event*b)).
 { unfold finite_weighted_score, finite_two_cell_prediction.
   apply finite_sum_ext; intro x; destruct (event x); ring. }
 rewrite Heq.
 rewrite finite_two_cell_piecewise_constant_expectation.
 pose proof (finite_weighted_mean_mass_identity A (filter event samples)
   weight score Ht) as Htrue.
 pose proof (finite_weighted_mean_mass_identity A
   (filter (fun x=>negb(event x)) samples) weight score Hf) as Hfalse.
 unfold finite_true_mean, finite_false_mean, finite_true_mass, finite_false_mass.
 nra.
Qed.

(**
 [finite_two_cell_risk_global_representation] (theorem) — The sum of the cellwise squared errors equals the weighted squared error of the actual event-measurable prediction over the original sample.
 Mathematical meaning: The sum of the cellwise squared errors equals the weighted squared error of the actual event-measurable prediction over the original sample.
 Exact checked proposition: forall (A : Type) (samples : list A) (weight score : A -> R) (event : A -> bool) (a b : R), finite_two_cell_risk samples weight score event a b = finite_sum (fun x=>weight x* (score x-(if event x then a else b))* (score x-(if event x then a else b))) samples.
 Premises and side conditions: Finite outcome occurrences, Boolean-cell selection, and real score weights are explicit. A nonzero cell mass is required where a conditional mean divides, and positivity is required only for order/optimality conclusions.
 Proof/definition method: Use finite_sum_filter_partition and Stdlib.List.filter_In to identify actual global prediction risk without new summation.
 Library reuse: Stdlib.List.filter/filter_In, Stdlib.Reals/Lra/Psatz/Field/Ring, FiniteSum.finite_sum/finite_sum_filter_partition and existing nonnegative-zero-support and scaling lemmas. No duplicated finite-sum recursion.
 Boundary: Deterministic finite weighted projection and variance algebra only; continuous Gaussian conditioning, measurable conditional expectation and empirical modeling are not proved.
 *)
Theorem finite_two_cell_risk_global_representation :
 forall (A : Type) (samples : list A) (weight score : A -> R)
 (event : A -> bool) (a b : R),
 finite_two_cell_risk samples weight score event a b =
 finite_sum (fun x=>weight x*
    (score x-(if event x then a else b))*
    (score x-(if event x then a else b))) samples.
Proof.
 intros A samples weight score event a b.
 unfold finite_two_cell_risk, finite_weighted_loss.
 symmetry.
 rewrite <- (finite_sum_filter_partition samples event
   (fun x=>weight x*(score x-(if event x then a else b))*
     (score x-(if event x then a else b)))).
 f_equal.
 - apply finite_sum_ext_in; intros x Hin.
   apply filter_In in Hin.
   destruct Hin as [_ Htrue].
   rewrite Htrue; reflexivity.
 - apply finite_sum_ext_in; intros x Hin.
   apply filter_In in Hin.
   destruct Hin as [_ Hfalse].
   destruct (event x) eqn:Hx; simpl in Hfalse; [discriminate|reflexivity].
Qed.

(**
 [finite_two_cell_risk_completed_square] (theorem) — Every two-constant prediction risk is optimal two-cell risk plus one positive quadratic penalty per observed cell.
 Mathematical meaning: Every two-constant prediction risk is optimal two-cell risk plus one positive quadratic penalty per observed cell.
 Exact checked proposition: forall (A : Type) (samples : list A) (weight score : A -> R) (event : A -> bool) (a b : R), finite_true_mass samples weight event<>0 -> finite_false_mass samples weight event<>0 -> finite_two_cell_risk samples weight score event a b = finite_two_cell_risk samples weight score event (finite_true_mean samples weight score event) (finite_false_mean samples weight score event) + finite_true_mass samples weight event* (a-finite_true_mean samples weight score event)* (a-finite_true_mean samples weight score event) + finite_false_mass samples weight event* (b-finite_false_mean samples weight score event)* (b-finite_false_mean samples weight score event).
 Premises and side conditions: Finite outcome occurrences, Boolean-cell selection, and real score weights are explicit. A nonzero cell mass is required where a conditional mean divides, and positivity is required only for order/optimality conclusions.
 Proof/definition method: Apply the generic finite weighted loss square-completion independently on each selected sample group.
 Library reuse: Stdlib.List.filter/filter_In, Stdlib.Reals/Lra/Psatz/Field/Ring, FiniteSum.finite_sum/finite_sum_filter_partition and existing nonnegative-zero-support and scaling lemmas. No duplicated finite-sum recursion.
 Boundary: Deterministic finite weighted projection and variance algebra only; continuous Gaussian conditioning, measurable conditional expectation and empirical modeling are not proved.
 *)
Theorem finite_two_cell_risk_completed_square :
 forall (A : Type) (samples : list A) (weight score : A -> R)
 (event : A -> bool) (a b : R),
 finite_true_mass samples weight event<>0 ->
 finite_false_mass samples weight event<>0 ->
 finite_two_cell_risk samples weight score event a b =
 finite_two_cell_risk samples weight score event
    (finite_true_mean samples weight score event)
    (finite_false_mean samples weight score event) +
 finite_true_mass samples weight event*
    (a-finite_true_mean samples weight score event)*
    (a-finite_true_mean samples weight score event) +
 finite_false_mass samples weight event*
    (b-finite_false_mean samples weight score event)*
    (b-finite_false_mean samples weight score event).
Proof.
 intros A samples weight score event a b Ht Hf.
 unfold finite_two_cell_risk.
 rewrite (finite_weighted_loss_completed_square A (filter event samples)
   weight score a Ht).
 rewrite (finite_weighted_loss_completed_square A
   (filter (fun x=>negb(event x)) samples) weight score b Hf).
 unfold finite_true_mass, finite_false_mass, finite_true_mean, finite_false_mean.
 ring.
Qed.

(**
 [finite_two_cell_risk_optimal] (theorem) — For strictly positive cell masses, the actual conditional means globally minimize squared loss among every two-cell measurable predictor.
 Mathematical meaning: For strictly positive cell masses, the actual conditional means globally minimize squared loss among every two-cell measurable predictor.
 Exact checked proposition: forall (A : Type) (samples : list A) (weight score : A -> R) (event : A -> bool) (a b : R), 0<finite_true_mass samples weight event -> 0<finite_false_mass samples weight event -> finite_two_cell_risk samples weight score event (finite_true_mean samples weight score event) (finite_false_mean samples weight score event) <= finite_two_cell_risk samples weight score event a b.
 Premises and side conditions: Finite outcome occurrences, Boolean-cell selection, and real score weights are explicit. A nonzero cell mass is required where a conditional mean divides, and positivity is required only for order/optimality conclusions.
 Proof/definition method: Use exact risk completion and standard real-square/product nonnegativity for both cells.
 Library reuse: Stdlib.List.filter/filter_In, Stdlib.Reals/Lra/Psatz/Field/Ring, FiniteSum.finite_sum/finite_sum_filter_partition and existing nonnegative-zero-support and scaling lemmas. No duplicated finite-sum recursion.
 Boundary: Deterministic finite weighted projection and variance algebra only; continuous Gaussian conditioning, measurable conditional expectation and empirical modeling are not proved.
 *)
Theorem finite_two_cell_risk_optimal :
 forall (A : Type) (samples : list A) (weight score : A -> R)
 (event : A -> bool) (a b : R),
 0<finite_true_mass samples weight event ->
 0<finite_false_mass samples weight event ->
 finite_two_cell_risk samples weight score event
    (finite_true_mean samples weight score event)
    (finite_false_mean samples weight score event) <=
 finite_two_cell_risk samples weight score event a b.
Proof.
 intros A samples weight score event a b Ht Hf.
 rewrite (finite_two_cell_risk_completed_square A samples weight score event a b) by lra.
 assert (Hs1 : 0<=Rsqr(a-finite_true_mean samples weight score event))
   by apply Rle_0_sqr.
 assert (Hs2 : 0<=Rsqr(b-finite_false_mean samples weight score event))
   by apply Rle_0_sqr.
 unfold Rsqr in Hs1, Hs2.
 assert (Hp1 : 0<=finite_true_mass samples weight event*
   ((a-finite_true_mean samples weight score event)*
    (a-finite_true_mean samples weight score event))).
 { apply Rmult_le_pos; [lra|exact Hs1]. }
 assert (Hp2 : 0<=finite_false_mass samples weight event*
   ((b-finite_false_mean samples weight score event)*
    (b-finite_false_mean samples weight score event))).
 { apply Rmult_le_pos; [lra|exact Hs2]. }
 replace (finite_true_mass samples weight event*
   (a-finite_true_mean samples weight score event)*
   (a-finite_true_mean samples weight score event))
 with (finite_true_mass samples weight event*
   ((a-finite_true_mean samples weight score event)*
    (a-finite_true_mean samples weight score event))) by ring.
 replace (finite_false_mass samples weight event*
   (b-finite_false_mean samples weight score event)*
   (b-finite_false_mean samples weight score event))
 with (finite_false_mass samples weight event*
   ((b-finite_false_mean samples weight score event)*
    (b-finite_false_mean samples weight score event))) by ring.
 lra.
Qed.

(**
 [finite_two_cell_total_variance] (theorem) — Finite law of total variance: global mean-centered squared error equals within-cell conditional-mean risk plus the between-cell mean energy.
 Mathematical meaning: Finite law of total variance: global mean-centered squared error equals within-cell conditional-mean risk plus the between-cell mean energy.
 Exact checked proposition: forall (A : Type) (samples : list A) (weight score : A -> R) (event : A -> bool), finite_true_mass samples weight event<>0 -> finite_false_mass samples weight event<>0 -> finite_weighted_loss samples weight score (finite_weighted_mean samples weight score) = finite_two_cell_risk samples weight score event (finite_true_mean samples weight score event) (finite_false_mean samples weight score event) + finite_true_mass samples weight event* (finite_true_mean samples weight score event- finite_weighted_mean samples weight score)* (finite_true_mean samples weight score event- finite_weighted_mean samples weight score) + finite_false_mass samples weight event* (finite_false_mean samples weight score event- finite_weighted_mean samples weight score)* (finite_false_mean samples weight score event- finite_weighted_mean samples weight score).
 Premises and side conditions: Finite outcome occurrences, Boolean-cell selection, and real score weights are explicit. A nonzero cell mass is required where a conditional mean divides, and positivity is required only for order/optimality conclusions.
 Proof/definition method: Derive law of total variance directly from FiniteSum partition plus two exact mean-square decompositions.
 Library reuse: Stdlib.List.filter/filter_In, Stdlib.Reals/Lra/Psatz/Field/Ring, FiniteSum.finite_sum/finite_sum_filter_partition and existing nonnegative-zero-support and scaling lemmas. No duplicated finite-sum recursion.
 Boundary: Deterministic finite weighted projection and variance algebra only; continuous Gaussian conditioning, measurable conditional expectation and empirical modeling are not proved.
 *)
Theorem finite_two_cell_total_variance :
 forall (A : Type) (samples : list A) (weight score : A -> R)
 (event : A -> bool),
 finite_true_mass samples weight event<>0 ->
 finite_false_mass samples weight event<>0 ->
 finite_weighted_loss samples weight score
    (finite_weighted_mean samples weight score) =
 finite_two_cell_risk samples weight score event
    (finite_true_mean samples weight score event)
    (finite_false_mean samples weight score event) +
 finite_true_mass samples weight event*
   (finite_true_mean samples weight score event-
     finite_weighted_mean samples weight score)*
   (finite_true_mean samples weight score event-
     finite_weighted_mean samples weight score) +
 finite_false_mass samples weight event*
   (finite_false_mean samples weight score event-
     finite_weighted_mean samples weight score)*
   (finite_false_mean samples weight score event-
     finite_weighted_mean samples weight score).
Proof.
 intros A samples weight score event Ht Hf.
 rewrite <- (finite_two_cell_loss_partition A samples weight score event
   (finite_weighted_mean samples weight score)).
 rewrite (finite_weighted_loss_completed_square A (filter event samples)
   weight score (finite_weighted_mean samples weight score) Ht).
 rewrite (finite_weighted_loss_completed_square A
   (filter (fun x=>negb(event x)) samples)
   weight score (finite_weighted_mean samples weight score) Hf).
 unfold finite_two_cell_risk, finite_true_mass, finite_false_mass,
   finite_true_mean, finite_false_mean.
 ring.
Qed.

(**
 [finite_two_cell_between_variance_nonnegative] (theorem) — The between-cell contribution to the finite total-variance decomposition is nonnegative when both cell masses are nonnegative.
 Mathematical meaning: The between-cell contribution to the finite total-variance decomposition is nonnegative when both cell masses are nonnegative.
 Exact checked proposition: forall (A : Type) (samples : list A) (weight score : A -> R) (event : A -> bool), 0<=finite_true_mass samples weight event -> 0<=finite_false_mass samples weight event -> 0<=finite_true_mass samples weight event* (finite_true_mean samples weight score event- finite_weighted_mean samples weight score)* (finite_true_mean samples weight score event- finite_weighted_mean samples weight score) + finite_false_mass samples weight event* (finite_false_mean samples weight score event- finite_weighted_mean samples weight score)* (finite_false_mean samples weight score event- finite_weighted_mean samples weight score).
 Premises and side conditions: Finite outcome occurrences, Boolean-cell selection, and real score weights are explicit. A nonzero cell mass is required where a conditional mean divides, and positivity is required only for order/optimality conclusions.
 Proof/definition method: Prove nonnegative between-group variance using standard square and nonnegative product theorems.
 Library reuse: Stdlib.List.filter/filter_In, Stdlib.Reals/Lra/Psatz/Field/Ring, FiniteSum.finite_sum/finite_sum_filter_partition and existing nonnegative-zero-support and scaling lemmas. No duplicated finite-sum recursion.
 Boundary: Deterministic finite weighted projection and variance algebra only; continuous Gaussian conditioning, measurable conditional expectation and empirical modeling are not proved.
 *)
Theorem finite_two_cell_between_variance_nonnegative :
 forall (A : Type) (samples : list A) (weight score : A -> R)
 (event : A -> bool),
 0<=finite_true_mass samples weight event ->
 0<=finite_false_mass samples weight event ->
 0<=finite_true_mass samples weight event*
   (finite_true_mean samples weight score event-
     finite_weighted_mean samples weight score)*
   (finite_true_mean samples weight score event-
     finite_weighted_mean samples weight score) +
 finite_false_mass samples weight event*
   (finite_false_mean samples weight score event-
     finite_weighted_mean samples weight score)*
   (finite_false_mean samples weight score event-
     finite_weighted_mean samples weight score).
Proof.
 intros A samples weight score event Ht Hf.
 assert (Hs1 : 0<=Rsqr(finite_true_mean samples weight score event-
   finite_weighted_mean samples weight score)) by apply Rle_0_sqr.
 assert (Hs2 : 0<=Rsqr(finite_false_mean samples weight score event-
   finite_weighted_mean samples weight score)) by apply Rle_0_sqr.
 unfold Rsqr in Hs1, Hs2.
 assert (Hp1 : 0<=finite_true_mass samples weight event*
   ((finite_true_mean samples weight score event-
     finite_weighted_mean samples weight score)*
    (finite_true_mean samples weight score event-
     finite_weighted_mean samples weight score))).
 { apply Rmult_le_pos; assumption. }
 assert (Hp2 : 0<=finite_false_mass samples weight event*
   ((finite_false_mean samples weight score event-
     finite_weighted_mean samples weight score)*
    (finite_false_mean samples weight score event-
     finite_weighted_mean samples weight score))).
 { apply Rmult_le_pos; assumption. }
 replace (finite_true_mass samples weight event*
   (finite_true_mean samples weight score event-
    finite_weighted_mean samples weight score)*
   (finite_true_mean samples weight score event-
    finite_weighted_mean samples weight score))
 with (finite_true_mass samples weight event*
   ((finite_true_mean samples weight score event-
     finite_weighted_mean samples weight score)*
    (finite_true_mean samples weight score event-
     finite_weighted_mean samples weight score))) by ring.
 replace (finite_false_mass samples weight event*
   (finite_false_mean samples weight score event-
    finite_weighted_mean samples weight score)*
   (finite_false_mean samples weight score event-
    finite_weighted_mean samples weight score))
 with (finite_false_mass samples weight event*
   ((finite_false_mean samples weight score event-
     finite_weighted_mean samples weight score)*
    (finite_false_mean samples weight score event-
     finite_weighted_mean samples weight score))) by ring.
 lra.
Qed.

(**
 [finite_two_cell_variance_reduction] (theorem) — Conditional averaging over an actual finite Boolean observation cannot increase squared prediction error relative to the unconditional weighted mean.
 Mathematical meaning: Conditional averaging over an actual finite Boolean observation cannot increase squared prediction error relative to the unconditional weighted mean.
 Exact checked proposition: forall (A : Type) (samples : list A) (weight score : A -> R) (event : A -> bool), 0<finite_true_mass samples weight event -> 0<finite_false_mass samples weight event -> finite_two_cell_risk samples weight score event (finite_true_mean samples weight score event) (finite_false_mean samples weight score event) <= finite_weighted_loss samples weight score (finite_weighted_mean samples weight score).
 Premises and side conditions: Finite outcome occurrences, Boolean-cell selection, and real score weights are explicit. A nonzero cell mass is required where a conditional mean divides, and positivity is required only for order/optimality conclusions.
 Proof/definition method: Combine the exact finite law of total variance with nonnegative between-cell energy.
 Library reuse: Stdlib.List.filter/filter_In, Stdlib.Reals/Lra/Psatz/Field/Ring, FiniteSum.finite_sum/finite_sum_filter_partition and existing nonnegative-zero-support and scaling lemmas. No duplicated finite-sum recursion.
 Boundary: Deterministic finite weighted projection and variance algebra only; continuous Gaussian conditioning, measurable conditional expectation and empirical modeling are not proved.
 *)
Theorem finite_two_cell_variance_reduction :
 forall (A : Type) (samples : list A) (weight score : A -> R)
 (event : A -> bool),
 0<finite_true_mass samples weight event ->
 0<finite_false_mass samples weight event ->
 finite_two_cell_risk samples weight score event
    (finite_true_mean samples weight score event)
    (finite_false_mean samples weight score event) <=
 finite_weighted_loss samples weight score
    (finite_weighted_mean samples weight score).
Proof.
 intros A samples weight score event Ht Hf.
 rewrite finite_two_cell_total_variance by lra.
 pose proof (finite_two_cell_between_variance_nonnegative A
   samples weight score event (Rlt_le _ _ Ht) (Rlt_le _ _ Hf)) as Hbetween.
 lra.
Qed.

