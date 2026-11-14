(** Module: EquicorrelationInverseVectors.v
 Purpose: Prove fully concrete finite-list matrix inverse composition and
 quadratic precision, and complete least-squares regression plus Schur-block
 algebra for the sequential conditional-means report.
 Mathematical representation: All vectors are Stdlib.list R and aggregate
 through the maintained FiniteSum.finite_sum operator. Equicorrelation and
 Schur actions are list maps using previously certified scalar entries.
 Regression risk is the exact second-moment polynomial implied by the
 specified equicorrelation covariance structure, not an unproved
 conditional expectation of a random Gaussian score.
 Explicit hypotheses: All required eigenvalue nonzero/positivity premises,
 positive observation count, correlation restrictions and nonempty vector
 premises appear on their respective theorems.
 Library use: Stdlib.List.map/map_map/map_repeat/Forall, Reals, Lra, Psatz,
 Field, Ring, FiniteSum, SequentialReport, EquicorrelationSpectral, and
 EquicorrelationVectors. No new list recursion, matrix postulate or axiom.
 Limitations: Kernel-checked deterministic finite real vector algebra;
 no Gaussian law, independent normal blocks, regular conditional
 distribution, numerical normal quantile or empirical IQ validation.
 Reproduction: after the existing dependency order, run
 rocq compile EquicorrelationInverseVectors.v with pinned Rocq 9.2.
 AI disclosure: This module was produced with AI assistance; the Rocq
 kernel, not source commentary, decides whether each proof is valid.
 *)
From Stdlib Require Import Reals Lra Psatz List.
Require Import FiniteSum SequentialReport EquicorrelationSpectral EquicorrelationVectors.
Import ListNotations.
Open Scope R_scope.

(**
 [vector_equicorrelation_inverse] (definition) — The componentwise inverse action using the same true vector length and full coordinate total.
 Mathematical meaning: The componentwise inverse action using the same true vector length and full coordinate total.
 Exact declaration: Definition vector_equicorrelation_inverse (c : R) (ys : list R) : list R := map (fun y => equicorr_inverse_entry (INR(length ys)) c y (vector_real_sum ys)) ys.
 Premises and side conditions: True finite-list dimensions and coordinate totals are used throughout; all inverse eigenvalues, positivity and admissible correlation conditions are explicit in the theorem statement when needed.
 Proof/definition method: Define a transparent concrete finite-list wrapper for an existing checked algebraic or finite-sum primitive.
 Library reuse: Stdlib.List, Reals, Lra, Psatz, Field/Ring, and the maintained FiniteSum, SequentialReport, EquicorrelationSpectral and EquicorrelationVectors theorems.
 Boundary: Deterministic rank-one real vector and Schur quadratic algebra; no inference of Gaussian conditional laws, normal quantiles or empirical composite-score accuracy.
 *)
Definition vector_equicorrelation_inverse (c : R) (ys : list R) : list R := map (fun y => equicorr_inverse_entry (INR(length ys)) c y (vector_real_sum ys)) ys.

(**
 [vector_inverse_quadratic] (definition) — The actual coordinate pairing y transpose times the inverse rank-one action on y.
 Mathematical meaning: The actual coordinate pairing y transpose times the inverse rank-one action on y.
 Exact declaration: Definition vector_inverse_quadratic (c : R) (ys : list R) : R := finite_sum (fun y => y*equicorr_inverse_entry (INR(length ys)) c y (vector_real_sum ys)) ys.
 Premises and side conditions: True finite-list dimensions and coordinate totals are used throughout; all inverse eigenvalues, positivity and admissible correlation conditions are explicit in the theorem statement when needed.
 Proof/definition method: Define a transparent concrete finite-list wrapper for an existing checked algebraic or finite-sum primitive.
 Library reuse: Stdlib.List, Reals, Lra, Psatz, Field/Ring, and the maintained FiniteSum, SequentialReport, EquicorrelationSpectral and EquicorrelationVectors theorems.
 Boundary: Deterministic rank-one real vector and Schur quadratic algebra; no inference of Gaussian conditional laws, normal quantiles or empirical composite-score accuracy.
 *)
Definition vector_inverse_quadratic (c : R) (ys : list R) : R := finite_sum (fun y => y*equicorr_inverse_entry (INR(length ys)) c y (vector_real_sum ys)) ys.

(**
 [vector_schur_action] (definition) — Full coordinate action of the exchangeable Schur residual block on a finite future vector.
 Mathematical meaning: Full coordinate action of the exchangeable Schur residual block on a finite future vector.
 Exact declaration: Definition vector_schur_action (r c : R) (ys : list R) : list R := map (fun y => (1-c)*y + equicorr_schur_cross r c * vector_real_sum ys) ys.
 Premises and side conditions: True finite-list dimensions and coordinate totals are used throughout; all inverse eigenvalues, positivity and admissible correlation conditions are explicit in the theorem statement when needed.
 Proof/definition method: Define a transparent concrete finite-list wrapper for an existing checked algebraic or finite-sum primitive.
 Library reuse: Stdlib.List, Reals, Lra, Psatz, Field/Ring, and the maintained FiniteSum, SequentialReport, EquicorrelationSpectral and EquicorrelationVectors theorems.
 Boundary: Deterministic rank-one real vector and Schur quadratic algebra; no inference of Gaussian conditional laws, normal quantiles or empirical composite-score accuracy.
 *)
Definition vector_schur_action (r c : R) (ys : list R) : list R := map (fun y => (1-c)*y + equicorr_schur_cross r c * vector_real_sum ys) ys.

(**
 [equicorr_regression_coefficient] (definition) — The equal-weight linear predictor coefficient for every observed coordinate.
 Mathematical meaning: The equal-weight linear predictor coefficient for every observed coordinate.
 Exact declaration: Definition equicorr_regression_coefficient (r c : R) : R := c/sequential_d r c.
 Premises and side conditions: True finite-list dimensions and coordinate totals are used throughout; all inverse eigenvalues, positivity and admissible correlation conditions are explicit in the theorem statement when needed.
 Proof/definition method: Define a transparent concrete finite-list wrapper for an existing checked algebraic or finite-sum primitive.
 Library reuse: Stdlib.List, Reals, Lra, Psatz, Field/Ring, and the maintained FiniteSum, SequentialReport, EquicorrelationSpectral and EquicorrelationVectors theorems.
 Boundary: Deterministic rank-one real vector and Schur quadratic algebra; no inference of Gaussian conditional laws, normal quantiles or empirical composite-score accuracy.
 *)
Definition equicorr_regression_coefficient (r c : R) : R := c/sequential_d r c.

(**
 [equicorr_regression_risk] (definition) — The variance-model mean squared prediction error for a future unit-variance score and equal weighting of r observed scores.
 Mathematical meaning: The variance-model mean squared prediction error for a future unit-variance score and equal weighting of r observed scores.
 Exact declaration: Definition equicorr_regression_risk (r c b : R) : R := 1-2*r*c*b + r*sequential_d r c*b*b.
 Premises and side conditions: True finite-list dimensions and coordinate totals are used throughout; all inverse eigenvalues, positivity and admissible correlation conditions are explicit in the theorem statement when needed.
 Proof/definition method: Define a transparent concrete finite-list wrapper for an existing checked algebraic or finite-sum primitive.
 Library reuse: Stdlib.List, Reals, Lra, Psatz, Field/Ring, and the maintained FiniteSum, SequentialReport, EquicorrelationSpectral and EquicorrelationVectors theorems.
 Boundary: Deterministic rank-one real vector and Schur quadratic algebra; no inference of Gaussian conditional laws, normal quantiles or empirical composite-score accuracy.
 *)
Definition equicorr_regression_risk (r c b : R) : R := 1-2*r*c*b + r*sequential_d r c*b*b.

(**
 [equicorr_regression_cross] (definition) — The covariance-model residual cross coefficient against an observed score.
 Mathematical meaning: The covariance-model residual cross coefficient against an observed score.
 Exact declaration: Definition equicorr_regression_cross (r c b : R) : R := c-sequential_d r c*b.
 Premises and side conditions: True finite-list dimensions and coordinate totals are used throughout; all inverse eigenvalues, positivity and admissible correlation conditions are explicit in the theorem statement when needed.
 Proof/definition method: Define a transparent concrete finite-list wrapper for an existing checked algebraic or finite-sum primitive.
 Library reuse: Stdlib.List, Reals, Lra, Psatz, Field/Ring, and the maintained FiniteSum, SequentialReport, EquicorrelationSpectral and EquicorrelationVectors theorems.
 Boundary: Deterministic rank-one real vector and Schur quadratic algebra; no inference of Gaussian conditional laws, normal quantiles or empirical composite-score accuracy.
 *)
Definition equicorr_regression_cross (r c b : R) : R := c-sequential_d r c*b.

(**
 [vector_equicorrelation_inverse_length] (theorem) — The inverse matrix action preserves the true number of coordinates.
 Mathematical meaning: The inverse matrix action preserves the true number of coordinates.
 Exact checked proposition: forall c : R, forall ys : list R, length (vector_equicorrelation_inverse c ys) = length ys.
 Premises and side conditions: True finite-list dimensions and coordinate totals are used throughout; all inverse eigenvalues, positivity and admissible correlation conditions are explicit in the theorem statement when needed.
 Proof/definition method: Use Stdlib.List.map_length directly.
 Library reuse: Stdlib.List, Reals, Lra, Psatz, Field/Ring, and the maintained FiniteSum, SequentialReport, EquicorrelationSpectral and EquicorrelationVectors theorems.
 Boundary: Deterministic rank-one real vector and Schur quadratic algebra; no inference of Gaussian conditional laws, normal quantiles or empirical composite-score accuracy.
 *)
Theorem vector_equicorrelation_inverse_length :
 forall c : R, forall ys : list R, length (vector_equicorrelation_inverse c ys) = length ys.
Proof.
 intros c ys; unfold vector_equicorrelation_inverse; apply map_length.
Qed.

(**
 [vector_equicorrelation_action_length] (theorem) — The original equicorrelation matrix action preserves the true number of coordinates.
 Mathematical meaning: The original equicorrelation matrix action preserves the true number of coordinates.
 Exact checked proposition: forall c : R, forall xs : list R, length (vector_equicorrelation_action c xs) = length xs.
 Premises and side conditions: True finite-list dimensions and coordinate totals are used throughout; all inverse eigenvalues, positivity and admissible correlation conditions are explicit in the theorem statement when needed.
 Proof/definition method: Reuse Stdlib.List.map_length rather than an index-level matrix proof.
 Library reuse: Stdlib.List, Reals, Lra, Psatz, Field/Ring, and the maintained FiniteSum, SequentialReport, EquicorrelationSpectral and EquicorrelationVectors theorems.
 Boundary: Deterministic rank-one real vector and Schur quadratic algebra; no inference of Gaussian conditional laws, normal quantiles or empirical composite-score accuracy.
 *)
Theorem vector_equicorrelation_action_length :
 forall c : R, forall xs : list R, length (vector_equicorrelation_action c xs) = length xs.
Proof.
 intros c xs; unfold vector_equicorrelation_action; apply map_length.
Qed.

(**
 [vector_equicorrelation_inverse_affine] (theorem) — The full list inverse has a coordinatewise affine representation with the exact inverse eigenvalue denominators.
 Mathematical meaning: The full list inverse has a coordinatewise affine representation with the exact inverse eigenvalue denominators.
 Exact checked proposition: forall c : R, forall ys : list R, 1-c<>0 -> sequential_d (INR(length ys)) c<>0 -> vector_equicorrelation_inverse c ys = map (fun y => /(1-c)*y - c*vector_real_sum ys / (sequential_d (INR(length ys)) c*(1-c))) ys.
 Premises and side conditions: True finite-list dimensions and coordinate totals are used throughout; all inverse eigenvalues, positivity and admissible correlation conditions are explicit in the theorem statement when needed.
 Proof/definition method: Normalize the maintained inverse coordinate formula pointwise with Stdlib.Field and map_ext_in.
 Library reuse: Stdlib.List, Reals, Lra, Psatz, Field/Ring, and the maintained FiniteSum, SequentialReport, EquicorrelationSpectral and EquicorrelationVectors theorems.
 Boundary: Deterministic rank-one real vector and Schur quadratic algebra; no inference of Gaussian conditional laws, normal quantiles or empirical composite-score accuracy.
 *)
Theorem vector_equicorrelation_inverse_affine :
 forall c : R, forall ys : list R,
 1-c<>0 -> sequential_d (INR(length ys)) c<>0 ->
 vector_equicorrelation_inverse c ys =
 map (fun y => /(1-c)*y + (-c*vector_real_sum ys /
       (sequential_d (INR(length ys)) c*(1-c)))) ys.
Proof.
 intros c ys Hc Hd.
 unfold vector_equicorrelation_inverse.
 apply map_ext_in; intros y _.
 unfold equicorr_inverse_entry; field; split; assumption.
Qed.

(**
 [vector_equicorrelation_inverse_sum] (theorem) — Summing the true inverse-vector coordinates yields the exact total divided by the common-mode eigenvalue.
 Mathematical meaning: Summing the true inverse-vector coordinates yields the exact total divided by the common-mode eigenvalue.
 Exact checked proposition: forall c : R, forall ys : list R, 1-c<>0 -> sequential_d (INR(length ys)) c<>0 -> vector_real_sum (vector_equicorrelation_inverse c ys) = vector_real_sum ys/sequential_d (INR(length ys)) c.
 Premises and side conditions: True finite-list dimensions and coordinate totals are used throughout; all inverse eigenvalues, positivity and admissible correlation conditions are explicit in the theorem statement when needed.
 Proof/definition method: Use the established finite-vector affine-sum theorem and scalar field normalization.
 Library reuse: Stdlib.List, Reals, Lra, Psatz, Field/Ring, and the maintained FiniteSum, SequentialReport, EquicorrelationSpectral and EquicorrelationVectors theorems.
 Boundary: Deterministic rank-one real vector and Schur quadratic algebra; no inference of Gaussian conditional laws, normal quantiles or empirical composite-score accuracy.
 *)
Theorem vector_equicorrelation_inverse_sum :
 forall c : R, forall ys : list R,
 1-c<>0 -> sequential_d (INR(length ys)) c<>0 ->
 vector_real_sum (vector_equicorrelation_inverse c ys) =
 vector_real_sum ys/sequential_d (INR(length ys)) c.
Proof.
 intros c ys Hc Hd.
 rewrite vector_equicorrelation_inverse_affine by assumption.
 rewrite vector_real_sum_affine.
 unfold sequential_d in *; field; nra.
Qed.

(**
 [vector_equicorrelation_inverse_left] (theorem) — The inverse list map is a true left inverse of the full equicorrelation matrix-vector action.
 Mathematical meaning: The inverse list map is a true left inverse of the full equicorrelation matrix-vector action.
 Exact checked proposition: forall c : R, forall xs : list R, 1-c<>0 -> sequential_d (INR(length xs)) c<>0 -> vector_equicorrelation_inverse c (vector_equicorrelation_action c xs) = xs.
 Premises and side conditions: True finite-list dimensions and coordinate totals are used throughout; all inverse eigenvalues, positivity and admissible correlation conditions are explicit in the theorem statement when needed.
 Proof/definition method: Lift the already checked coordinate inverse to list equality using the exact action sum and Stdlib.map_map/map_id.
 Library reuse: Stdlib.List, Reals, Lra, Psatz, Field/Ring, and the maintained FiniteSum, SequentialReport, EquicorrelationSpectral and EquicorrelationVectors theorems.
 Boundary: Deterministic rank-one real vector and Schur quadratic algebra; no inference of Gaussian conditional laws, normal quantiles or empirical composite-score accuracy.
 *)
Theorem vector_equicorrelation_inverse_left :
 forall c : R, forall xs : list R,
 1-c<>0 -> sequential_d (INR(length xs)) c<>0 ->
 vector_equicorrelation_inverse c (vector_equicorrelation_action c xs) = xs.
Proof.
 intros c xs Hc Hd.
 unfold vector_equicorrelation_inverse.
 rewrite vector_equicorrelation_action_length.
 rewrite vector_equicorrelation_action_sum.
 unfold vector_equicorrelation_action.
 rewrite map_map.
 transitivity (map (fun x : R => x) xs).
 - apply map_ext_in; intros x _; simpl.
   apply equicorr_inverse_left_action; assumption.
 - now rewrite map_id.
Qed.

(**
 [vector_equicorrelation_inverse_right] (theorem) — The inverse list map is a true right inverse of the full equicorrelation matrix-vector action.
 Mathematical meaning: The inverse list map is a true right inverse of the full equicorrelation matrix-vector action.
 Exact checked proposition: forall c : R, forall ys : list R, 1-c<>0 -> sequential_d (INR(length ys)) c<>0 -> vector_equicorrelation_action c (vector_equicorrelation_inverse c ys) = ys.
 Premises and side conditions: True finite-list dimensions and coordinate totals are used throughout; all inverse eigenvalues, positivity and admissible correlation conditions are explicit in the theorem statement when needed.
 Proof/definition method: Lift the scalar right-inverse theorem through Stdlib.map_map and the exact inverse-vector coordinate sum.
 Library reuse: Stdlib.List, Reals, Lra, Psatz, Field/Ring, and the maintained FiniteSum, SequentialReport, EquicorrelationSpectral and EquicorrelationVectors theorems.
 Boundary: Deterministic rank-one real vector and Schur quadratic algebra; no inference of Gaussian conditional laws, normal quantiles or empirical composite-score accuracy.
 *)
Theorem vector_equicorrelation_inverse_right :
 forall c : R, forall ys : list R,
 1-c<>0 -> sequential_d (INR(length ys)) c<>0 ->
 vector_equicorrelation_action c (vector_equicorrelation_inverse c ys) = ys.
Proof.
 intros c ys Hc Hd.
 unfold vector_equicorrelation_action.
 rewrite vector_equicorrelation_inverse_sum by assumption.
 unfold vector_equicorrelation_inverse.
 rewrite map_map.
 transitivity (map (fun y : R => y) ys).
 - apply map_ext_in; intros y _; simpl.
   apply equicorr_inverse_right_action; assumption.
 - now rewrite map_id.
Qed.

(**
 [vector_equicorrelation_inverse_contrast] (theorem) — On the entire zero-sum contrast subspace, the inverse list action is pure scaling by 1/(1-c).
 Mathematical meaning: On the entire zero-sum contrast subspace, the inverse list action is pure scaling by 1/(1-c).
 Exact checked proposition: forall c : R, forall ys : list R, 1-c<>0 -> vector_real_sum ys=0 -> vector_equicorrelation_inverse c ys = map (fun y => y/(1-c)) ys.
 Premises and side conditions: True finite-list dimensions and coordinate totals are used throughout; all inverse eigenvalues, positivity and admissible correlation conditions are explicit in the theorem statement when needed.
 Proof/definition method: Reuse the established inverse contrast-direction theorem and Stdlib.map extensionality.
 Library reuse: Stdlib.List, Reals, Lra, Psatz, Field/Ring, and the maintained FiniteSum, SequentialReport, EquicorrelationSpectral and EquicorrelationVectors theorems.
 Boundary: Deterministic rank-one real vector and Schur quadratic algebra; no inference of Gaussian conditional laws, normal quantiles or empirical composite-score accuracy.
 *)
Theorem vector_equicorrelation_inverse_contrast :
 forall c : R, forall ys : list R,
 1-c<>0 -> vector_real_sum ys=0 ->
 vector_equicorrelation_inverse c ys =
 map (fun y => y/(1-c)) ys.
Proof.
 intros c ys Hc Hsum.
 unfold vector_equicorrelation_inverse.
 rewrite Hsum.
 apply map_ext_in; intros y _.
 apply equicorr_inverse_contrast_direction; exact Hc.
Qed.

(**
 [vector_equicorrelation_inverse_constant] (theorem) — The all-ones eigenspace is inverted with eigenvalue 1/d_n, including exact multiplicity and empty-list behavior.
 Mathematical meaning: The all-ones eigenspace is inverted with eigenvalue 1/d_n, including exact multiplicity and empty-list behavior.
 Exact checked proposition: forall n : nat, forall c a : R, 1-c<>0 -> sequential_d (INR n) c<>0 -> vector_equicorrelation_inverse c (repeat a n) = repeat (a/sequential_d (INR n) c) n.
 Premises and side conditions: True finite-list dimensions and coordinate totals are used throughout; all inverse eigenvalues, positivity and admissible correlation conditions are explicit in the theorem statement when needed.
 Proof/definition method: Reuse the maintained constant-vector sum theorem, Stdlib.repeat_length/map_repeat, and scalar inverse algebra.
 Library reuse: Stdlib.List, Reals, Lra, Psatz, Field/Ring, and the maintained FiniteSum, SequentialReport, EquicorrelationSpectral and EquicorrelationVectors theorems.
 Boundary: Deterministic rank-one real vector and Schur quadratic algebra; no inference of Gaussian conditional laws, normal quantiles or empirical composite-score accuracy.
 *)
Theorem vector_equicorrelation_inverse_constant :
 forall n : nat, forall c a : R,
 1-c<>0 -> sequential_d (INR n) c<>0 ->
 vector_equicorrelation_inverse c (repeat a n) =
 repeat (a/sequential_d (INR n) c) n.
Proof.
 intros n c a Hc Hd.
 unfold vector_equicorrelation_inverse.
 rewrite repeat_length, vector_real_sum_repeat, map_repeat.
 f_equal.
 unfold equicorr_inverse_entry, sequential_d in *; field; nra.
Qed.

(**
 [vector_inverse_quadratic_formula] (theorem) — The coordinate pairing with the exact inverse matrix is (E-c S²/d_n)/(1-c), proving the actual inverse quadratic representation.
 Mathematical meaning: The coordinate pairing with the exact inverse matrix is (E-c S²/d_n)/(1-c), proving the actual inverse quadratic representation.
 Exact checked proposition: forall c : R, forall ys : list R, 1-c<>0 -> sequential_d (INR(length ys)) c<>0 -> vector_inverse_quadratic c ys = (vector_square_energy ys - c*vector_real_sum ys*vector_real_sum ys/sequential_d (INR(length ys)) c)/(1-c).
 Premises and side conditions: True finite-list dimensions and coordinate totals are used throughout; all inverse eigenvalues, positivity and admissible correlation conditions are explicit in the theorem statement when needed.
 Proof/definition method: Expand the literal inverse-coordinate dot product using FiniteSum extensionality, additivity, scaling and Stdlib.Field.
 Library reuse: Stdlib.List, Reals, Lra, Psatz, Field/Ring, and the maintained FiniteSum, SequentialReport, EquicorrelationSpectral and EquicorrelationVectors theorems.
 Boundary: Deterministic rank-one real vector and Schur quadratic algebra; no inference of Gaussian conditional laws, normal quantiles or empirical composite-score accuracy.
 *)
Theorem vector_inverse_quadratic_formula :
 forall c : R, forall ys : list R,
 1-c<>0 -> sequential_d (INR(length ys)) c<>0 ->
 vector_inverse_quadratic c ys =
 (vector_square_energy ys -
   c*vector_real_sum ys*vector_real_sum ys/sequential_d (INR(length ys)) c)/(1-c).
Proof.
 intros c ys Hc Hd.
 unfold vector_inverse_quadratic.
 transitivity (finite_sum (fun y =>
   (/(1-c))*(y*y) +
   (-c*vector_real_sum ys /
      (sequential_d (INR(length ys)) c*(1-c)))*y) ys).
 { apply finite_sum_ext; intro y.
   unfold equicorr_inverse_entry; field; split; assumption. }
 rewrite finite_sum_add, finite_sum_scale, finite_sum_scale.
 unfold vector_square_energy, vector_real_sum.
 field; split; assumption.
Qed.

(**
 [vector_inverse_quadratic_contrast] (theorem) — For zero-sum actual vectors the inverse quadratic form is E/(1-c), exactly the reciprocal contrast eigenvalue.
 Mathematical meaning: For zero-sum actual vectors the inverse quadratic form is E/(1-c), exactly the reciprocal contrast eigenvalue.
 Exact checked proposition: forall c : R, forall ys : list R, 1-c<>0 -> sequential_d (INR(length ys)) c<>0 -> vector_real_sum ys=0 -> vector_inverse_quadratic c ys = vector_square_energy ys/(1-c).
 Premises and side conditions: True finite-list dimensions and coordinate totals are used throughout; all inverse eigenvalues, positivity and admissible correlation conditions are explicit in the theorem statement when needed.
 Proof/definition method: Specialize the exact inverse quadratic formula to a zero-sum coordinate vector.
 Library reuse: Stdlib.List, Reals, Lra, Psatz, Field/Ring, and the maintained FiniteSum, SequentialReport, EquicorrelationSpectral and EquicorrelationVectors theorems.
 Boundary: Deterministic rank-one real vector and Schur quadratic algebra; no inference of Gaussian conditional laws, normal quantiles or empirical composite-score accuracy.
 *)
Theorem vector_inverse_quadratic_contrast :
 forall c : R, forall ys : list R,
 1-c<>0 -> sequential_d (INR(length ys)) c<>0 ->
 vector_real_sum ys=0 ->
 vector_inverse_quadratic c ys = vector_square_energy ys/(1-c).
Proof.
 intros c ys Hc Hd Hz.
 rewrite vector_inverse_quadratic_formula by assumption.
 rewrite Hz; unfold Rdiv; ring.
Qed.

(**
 [vector_inverse_quadratic_common] (theorem) — For constant score vectors the inverse quadratic energy is n a² / d_n.
 Mathematical meaning: For constant score vectors the inverse quadratic energy is n a² / d_n.
 Exact checked proposition: forall n : nat, forall c a : R, 1-c<>0 -> sequential_d (INR n) c<>0 -> vector_inverse_quadratic c (repeat a n) = INR n*a*a/sequential_d (INR n) c.
 Premises and side conditions: True finite-list dimensions and coordinate totals are used throughout; all inverse eigenvalues, positivity and admissible correlation conditions are explicit in the theorem statement when needed.
 Proof/definition method: Insert the constant-vector norm and sum closed forms into the verified inverse quadratic expression.
 Library reuse: Stdlib.List, Reals, Lra, Psatz, Field/Ring, and the maintained FiniteSum, SequentialReport, EquicorrelationSpectral and EquicorrelationVectors theorems.
 Boundary: Deterministic rank-one real vector and Schur quadratic algebra; no inference of Gaussian conditional laws, normal quantiles or empirical composite-score accuracy.
 *)
Theorem vector_inverse_quadratic_common :
 forall n : nat, forall c a : R,
 1-c<>0 -> sequential_d (INR n) c<>0 ->
 vector_inverse_quadratic c (repeat a n) =
 INR n*a*a/sequential_d (INR n) c.
Proof.
 intros n c a Hc Hd.
 rewrite vector_inverse_quadratic_formula.
 2:{ exact Hc. }
 2:{ rewrite repeat_length; exact Hd. }
 rewrite repeat_length, vector_square_energy_repeat, vector_real_sum_repeat.
 unfold sequential_d in *; field; nra.
Qed.

(**
 [vector_inverse_quadratic_action_pullback] (theorem) — The exact inverse quadratic of Cx equals the original equicorrelation Gram energy x transpose Cx.
 Mathematical meaning: The exact inverse quadratic of Cx equals the original equicorrelation Gram energy x transpose Cx.
 Exact checked proposition: forall c : R, forall xs : list R, 1-c<>0 -> sequential_d (INR(length xs)) c<>0 -> vector_inverse_quadratic c (vector_equicorrelation_action c xs) = vector_equicorrelation_form c xs.
 Premises and side conditions: True finite-list dimensions and coordinate totals are used throughout; all inverse eigenvalues, positivity and admissible correlation conditions are explicit in the theorem statement when needed.
 Proof/definition method: Use the full finite matrix-vector pairing, exact action-sum identity, and previously checked scalar left-inverse theorem.
 Library reuse: Stdlib.List, Reals, Lra, Psatz, Field/Ring, and the maintained FiniteSum, SequentialReport, EquicorrelationSpectral and EquicorrelationVectors theorems.
 Boundary: Deterministic rank-one real vector and Schur quadratic algebra; no inference of Gaussian conditional laws, normal quantiles or empirical composite-score accuracy.
 *)
Theorem vector_inverse_quadratic_action_pullback :
 forall c : R, forall xs : list R,
 1-c<>0 -> sequential_d (INR(length xs)) c<>0 ->
 vector_inverse_quadratic c (vector_equicorrelation_action c xs) =
 vector_equicorrelation_form c xs.
Proof.
 intros c xs Hc Hd.
 unfold vector_inverse_quadratic.
 rewrite vector_equicorrelation_action_length.
 rewrite vector_equicorrelation_action_sum.
 unfold vector_equicorrelation_action at 1.
 rewrite finite_sum_map.
 transitivity (finite_sum
   (fun x => x*equicorr_action c x (vector_real_sum xs)) xs).
 { apply finite_sum_ext; intro x.
   rewrite equicorr_inverse_left_action by assumption; ring. }
 apply vector_equicorrelation_dot_action_identity.
Qed.

(**
 [vector_inverse_quadratic_centered] (theorem) — The full inverse quadratic splits into positive contrast and common eigenspace contributions using the actual vector mean.
 Mathematical meaning: The full inverse quadratic splits into positive contrast and common eigenspace contributions using the actual vector mean.
 Exact checked proposition: forall c : R, forall ys : list R, ys<>nil -> 1-c<>0 -> sequential_d (INR(length ys)) c<>0 -> vector_inverse_quadratic c ys = (vector_square_energy ys - vector_real_sum ys*vector_real_sum ys/INR(length ys))/(1-c) + (vector_real_sum ys*vector_real_sum ys/INR(length ys))/ sequential_d (INR(length ys)) c.
 Premises and side conditions: True finite-list dimensions and coordinate totals are used throughout; all inverse eigenvalues, positivity and admissible correlation conditions are explicit in the theorem statement when needed.
 Proof/definition method: Algebraically diagonalize the true inverse quadratic into mean and contrast modes via the finite-vector length.
 Library reuse: Stdlib.List, Reals, Lra, Psatz, Field/Ring, and the maintained FiniteSum, SequentialReport, EquicorrelationSpectral and EquicorrelationVectors theorems.
 Boundary: Deterministic rank-one real vector and Schur quadratic algebra; no inference of Gaussian conditional laws, normal quantiles or empirical composite-score accuracy.
 *)
Theorem vector_inverse_quadratic_centered :
 forall c : R, forall ys : list R, ys<>nil ->
 1-c<>0 -> sequential_d (INR(length ys)) c<>0 ->
 vector_inverse_quadratic c ys =
 (vector_square_energy ys -
   vector_real_sum ys*vector_real_sum ys/INR(length ys))/(1-c) +
 (vector_real_sum ys*vector_real_sum ys/INR(length ys))/
   sequential_d (INR(length ys)) c.
Proof.
 intros c [|y ys] Hnon Hc Hd.
 - contradiction.
 - rewrite vector_inverse_quadratic_formula by assumption.
   assert (Hlen : INR(length (y::ys))<>0).
   { pose proof (vector_nat_to_real_successor_positive (length ys)).
     simpl; lra. }
   unfold sequential_d in *; field; nra.
Qed.

(**
 [equicorr_regression_risk_completed_square] (theorem) — The least-squares error for equal-weight score prediction is its optimal residual variance plus a nonnegative quadratic coefficient penalty.
 Mathematical meaning: The least-squares error for equal-weight score prediction is its optimal residual variance plus a nonnegative quadratic coefficient penalty.
 Exact checked proposition: forall r c b : R, sequential_d r c<>0 -> equicorr_regression_risk r c b = equicorr_schur_diagonal r c + r*sequential_d r c*(b-equicorr_regression_coefficient r c)* (b-equicorr_regression_coefficient r c).
 Premises and side conditions: True finite-list dimensions and coordinate totals are used throughout; all inverse eigenvalues, positivity and admissible correlation conditions are explicit in the theorem statement when needed.
 Proof/definition method: Complete the square with the existing Schur residual variance and exact denominator.
 Library reuse: Stdlib.List, Reals, Lra, Psatz, Field/Ring, and the maintained FiniteSum, SequentialReport, EquicorrelationSpectral and EquicorrelationVectors theorems.
 Boundary: Deterministic rank-one real vector and Schur quadratic algebra; no inference of Gaussian conditional laws, normal quantiles or empirical composite-score accuracy.
 *)
Theorem equicorr_regression_risk_completed_square :
 forall r c b : R, sequential_d r c<>0 ->
 equicorr_regression_risk r c b =
 equicorr_schur_diagonal r c +
 r*sequential_d r c*(b-equicorr_regression_coefficient r c)*
   (b-equicorr_regression_coefficient r c).
Proof.
 intros r c b Hd.
 unfold equicorr_regression_risk, equicorr_schur_diagonal,
   equicorr_regression_coefficient.
 field; exact Hd.
Qed.

(**
 [equicorr_regression_risk_at_optimum] (theorem) — The checked best equal-weight linear prediction coefficient achieves exactly the Schur diagonal residual variance.
 Mathematical meaning: The checked best equal-weight linear prediction coefficient achieves exactly the Schur diagonal residual variance.
 Exact checked proposition: forall r c : R, sequential_d r c<>0 -> equicorr_regression_risk r c (equicorr_regression_coefficient r c) = equicorr_schur_diagonal r c.
 Premises and side conditions: True finite-list dimensions and coordinate totals are used throughout; all inverse eigenvalues, positivity and admissible correlation conditions are explicit in the theorem statement when needed.
 Proof/definition method: Reuse the exact completed-square identity and the vanishing optimal coefficient difference.
 Library reuse: Stdlib.List, Reals, Lra, Psatz, Field/Ring, and the maintained FiniteSum, SequentialReport, EquicorrelationSpectral and EquicorrelationVectors theorems.
 Boundary: Deterministic rank-one real vector and Schur quadratic algebra; no inference of Gaussian conditional laws, normal quantiles or empirical composite-score accuracy.
 *)
Theorem equicorr_regression_risk_at_optimum :
 forall r c : R, sequential_d r c<>0 ->
 equicorr_regression_risk r c (equicorr_regression_coefficient r c) =
 equicorr_schur_diagonal r c.
Proof.
 intros r c Hd.
 rewrite equicorr_regression_risk_completed_square by exact Hd.
 ring.
Qed.

(**
 [equicorr_regression_risk_minimizer] (theorem) — For positive observed dimension and positive common eigenvalue, no other equal-weight linear predictor has smaller quadratic risk.
 Mathematical meaning: For positive observed dimension and positive common eigenvalue, no other equal-weight linear predictor has smaller quadratic risk.
 Exact checked proposition: forall r c b : R, 0<=r -> 0<sequential_d r c -> equicorr_schur_diagonal r c <= equicorr_regression_risk r c b.
 Premises and side conditions: True finite-list dimensions and coordinate totals are used throughout; all inverse eigenvalues, positivity and admissible correlation conditions are explicit in the theorem statement when needed.
 Proof/definition method: Combine the standard nonnegative-square theorem with the completed-square identity.
 Library reuse: Stdlib.List, Reals, Lra, Psatz, Field/Ring, and the maintained FiniteSum, SequentialReport, EquicorrelationSpectral and EquicorrelationVectors theorems.
 Boundary: Deterministic rank-one real vector and Schur quadratic algebra; no inference of Gaussian conditional laws, normal quantiles or empirical composite-score accuracy.
 *)
Theorem equicorr_regression_risk_minimizer :
 forall r c b : R, 0<=r -> 0<sequential_d r c ->
 equicorr_schur_diagonal r c <= equicorr_regression_risk r c b.
Proof.
 intros r c b Hr Hd.
 rewrite equicorr_regression_risk_completed_square by lra.
 assert (Hs : 0 <= Rsqr (b-equicorr_regression_coefficient r c)) by apply Rle_0_sqr.
 unfold Rsqr in Hs.
 nra.
Qed.

(**
 [equicorr_regression_risk_unique_optimum] (theorem) — For strictly positive block size and common eigenvalue, only the common inverse-regression coefficient attains the minimum quadratic risk.
 Mathematical meaning: For strictly positive block size and common eigenvalue, only the common inverse-regression coefficient attains the minimum quadratic risk.
 Exact checked proposition: forall r c b : R, 0<r -> 0<sequential_d r c -> equicorr_regression_risk r c b = equicorr_schur_diagonal r c -> b=equicorr_regression_coefficient r c.
 Premises and side conditions: True finite-list dimensions and coordinate totals are used throughout; all inverse eigenvalues, positivity and admissible correlation conditions are explicit in the theorem statement when needed.
 Proof/definition method: Use exact square completion plus strict positivity of both multiplicative risk factors.
 Library reuse: Stdlib.List, Reals, Lra, Psatz, Field/Ring, and the maintained FiniteSum, SequentialReport, EquicorrelationSpectral and EquicorrelationVectors theorems.
 Boundary: Deterministic rank-one real vector and Schur quadratic algebra; no inference of Gaussian conditional laws, normal quantiles or empirical composite-score accuracy.
 *)
Theorem equicorr_regression_risk_unique_optimum :
 forall r c b : R, 0<r -> 0<sequential_d r c ->
 equicorr_regression_risk r c b = equicorr_schur_diagonal r c ->
 b=equicorr_regression_coefficient r c.
Proof.
 intros r c b Hr Hd Heq.
 rewrite equicorr_regression_risk_completed_square in Heq by lra.
 assert (Hrs : 0 < r*sequential_d r c) by nra.
 assert (Hs : (b-equicorr_regression_coefficient r c)*
   (b-equicorr_regression_coefficient r c) = 0) by nra.
 nra.
Qed.

(**
 [equicorr_regression_cross_at_optimum] (theorem) — At the inverse-covariance coefficient every observed coordinate is algebraically uncorrelated with the prediction residual.
 Mathematical meaning: At the inverse-covariance coefficient every observed coordinate is algebraically uncorrelated with the prediction residual.
 Exact checked proposition: forall r c : R, sequential_d r c<>0 -> equicorr_regression_cross r c (equicorr_regression_coefficient r c)=0.
 Premises and side conditions: True finite-list dimensions and coordinate totals are used throughout; all inverse eigenvalues, positivity and admissible correlation conditions are explicit in the theorem statement when needed.
 Proof/definition method: Show normal-equation orthogonality by scalar denominator cancellation.
 Library reuse: Stdlib.List, Reals, Lra, Psatz, Field/Ring, and the maintained FiniteSum, SequentialReport, EquicorrelationSpectral and EquicorrelationVectors theorems.
 Boundary: Deterministic rank-one real vector and Schur quadratic algebra; no inference of Gaussian conditional laws, normal quantiles or empirical composite-score accuracy.
 *)
Theorem equicorr_regression_cross_at_optimum :
 forall r c : R, sequential_d r c<>0 ->
 equicorr_regression_cross r c (equicorr_regression_coefficient r c)=0.
Proof.
 intros r c Hd.
 unfold equicorr_regression_cross, equicorr_regression_coefficient.
 field; exact Hd.
Qed.

(**
 [equicorr_regression_cross_factorization] (theorem) — The prediction residual cross-covariance equals d_r times the deviation from the unique optimum.
 Mathematical meaning: The prediction residual cross-covariance equals d_r times the deviation from the unique optimum.
 Exact checked proposition: forall r c b : R, sequential_d r c<>0 -> equicorr_regression_cross r c b = sequential_d r c*(equicorr_regression_coefficient r c-b).
 Premises and side conditions: True finite-list dimensions and coordinate totals are used throughout; all inverse eigenvalues, positivity and admissible correlation conditions are explicit in the theorem statement when needed.
 Proof/definition method: Factor the exact common eigenvalue from the regression normal-equation residual.
 Library reuse: Stdlib.List, Reals, Lra, Psatz, Field/Ring, and the maintained FiniteSum, SequentialReport, EquicorrelationSpectral and EquicorrelationVectors theorems.
 Boundary: Deterministic rank-one real vector and Schur quadratic algebra; no inference of Gaussian conditional laws, normal quantiles or empirical composite-score accuracy.
 *)
Theorem equicorr_regression_cross_factorization :
 forall r c b : R, sequential_d r c<>0 ->
 equicorr_regression_cross r c b =
 sequential_d r c*(equicorr_regression_coefficient r c-b).
Proof.
 intros r c b Hd.
 unfold equicorr_regression_cross, equicorr_regression_coefficient.
 field; exact Hd.
Qed.

(**
 [equicorr_regression_optimal_risk_nonnegative] (theorem) — For nonnegative correlations below one and at least one observed score, optimal linear-prediction risk is strictly positive.
 Mathematical meaning: For nonnegative correlations below one and at least one observed score, optimal linear-prediction risk is strictly positive.
 Exact checked proposition: forall r c : R, 1<=r -> 0<=c -> c<1 -> 0<equicorr_regression_risk r c (equicorr_regression_coefficient r c).
 Premises and side conditions: True finite-list dimensions and coordinate totals are used throughout; all inverse eigenvalues, positivity and admissible correlation conditions are explicit in the theorem statement when needed.
 Proof/definition method: Reuse the sequential residual variance factorization and positivity of the common denominator.
 Library reuse: Stdlib.List, Reals, Lra, Psatz, Field/Ring, and the maintained FiniteSum, SequentialReport, EquicorrelationSpectral and EquicorrelationVectors theorems.
 Boundary: Deterministic rank-one real vector and Schur quadratic algebra; no inference of Gaussian conditional laws, normal quantiles or empirical composite-score accuracy.
 *)
Theorem equicorr_regression_optimal_risk_nonnegative :
 forall r c : R, 1<=r -> 0<=c -> c<1 ->
 0<equicorr_regression_risk r c (equicorr_regression_coefficient r c).
Proof.
 intros r c Hr Hc Hu.
 assert (Hd : 0<sequential_d r c).
 { apply sequential_denominator_positive_nonnegative_correlation; assumption. }
 rewrite equicorr_regression_risk_at_optimum by lra.
 unfold equicorr_schur_diagonal.
 rewrite sequential_residual_variance_identity by lra.
 apply Rdiv_lt_0_compat; nra.
Qed.

(**
 [vector_schur_action_length] (theorem) — The concrete Schur residual matrix action preserves the number of future score coordinates.
 Mathematical meaning: The concrete Schur residual matrix action preserves the number of future score coordinates.
 Exact checked proposition: forall r c : R, forall ys : list R, length (vector_schur_action r c ys)=length ys.
 Premises and side conditions: True finite-list dimensions and coordinate totals are used throughout; all inverse eigenvalues, positivity and admissible correlation conditions are explicit in the theorem statement when needed.
 Proof/definition method: Reuse Stdlib.List.map_length.
 Library reuse: Stdlib.List, Reals, Lra, Psatz, Field/Ring, and the maintained FiniteSum, SequentialReport, EquicorrelationSpectral and EquicorrelationVectors theorems.
 Boundary: Deterministic rank-one real vector and Schur quadratic algebra; no inference of Gaussian conditional laws, normal quantiles or empirical composite-score accuracy.
 *)
Theorem vector_schur_action_length :
 forall r c : R, forall ys : list R,
 length (vector_schur_action r c ys)=length ys.
Proof.
 intros r c ys; unfold vector_schur_action; apply map_length.
Qed.

(**
 [vector_schur_action_sum] (theorem) — The sum of an actual Schur-block action equals its common-mode eigenvalue times the original coordinate sum.
 Mathematical meaning: The sum of an actual Schur-block action equals its common-mode eigenvalue times the original coordinate sum.
 Exact checked proposition: forall r c : R, forall ys : list R, vector_real_sum (vector_schur_action r c ys) = ((1-c)+INR(length ys)*equicorr_schur_cross r c)*vector_real_sum ys.
 Premises and side conditions: True finite-list dimensions and coordinate totals are used throughout; all inverse eigenvalues, positivity and admissible correlation conditions are explicit in the theorem statement when needed.
 Proof/definition method: Apply existing FiniteSum addition, scaling and constant-sum laws to the explicit Schur matrix action.
 Library reuse: Stdlib.List, Reals, Lra, Psatz, Field/Ring, and the maintained FiniteSum, SequentialReport, EquicorrelationSpectral and EquicorrelationVectors theorems.
 Boundary: Deterministic rank-one real vector and Schur quadratic algebra; no inference of Gaussian conditional laws, normal quantiles or empirical composite-score accuracy.
 *)
Theorem vector_schur_action_sum :
 forall r c : R, forall ys : list R,
 vector_real_sum (vector_schur_action r c ys) =
 ((1-c)+INR(length ys)*equicorr_schur_cross r c)*vector_real_sum ys.
Proof.
 intros r c ys.
 unfold vector_schur_action.
 unfold vector_real_sum at 1.
 rewrite finite_sum_map.
 rewrite finite_sum_add, finite_sum_scale, finite_sum_const.
 unfold vector_real_sum; ring.
Qed.

(**
 [vector_schur_action_contrast] (theorem) — The Schur residual action preserves every zero-sum contrast direction with eigenvalue 1-c.
 Mathematical meaning: The Schur residual action preserves every zero-sum contrast direction with eigenvalue 1-c.
 Exact checked proposition: forall r c : R, forall ys : list R, vector_real_sum ys=0 -> vector_schur_action r c ys = map (fun y => (1-c)*y) ys.
 Premises and side conditions: True finite-list dimensions and coordinate totals are used throughout; all inverse eigenvalues, positivity and admissible correlation conditions are explicit in the theorem statement when needed.
 Proof/definition method: Use the same Stdlib.map_ext_in characterization as the maintained equicorrelation contrast proof.
 Library reuse: Stdlib.List, Reals, Lra, Psatz, Field/Ring, and the maintained FiniteSum, SequentialReport, EquicorrelationSpectral and EquicorrelationVectors theorems.
 Boundary: Deterministic rank-one real vector and Schur quadratic algebra; no inference of Gaussian conditional laws, normal quantiles or empirical composite-score accuracy.
 *)
Theorem vector_schur_action_contrast :
 forall r c : R, forall ys : list R, vector_real_sum ys=0 ->
 vector_schur_action r c ys = map (fun y => (1-c)*y) ys.
Proof.
 intros r c ys Hs.
 unfold vector_schur_action.
 rewrite Hs; apply map_ext_in; intros y _; ring.
Qed.

(**
 [vector_schur_action_constant] (theorem) — The Schur residual has explicit common-mode eigenvalue 1-c+m*cross for every constant m-score future vector.
 Mathematical meaning: The Schur residual has explicit common-mode eigenvalue 1-c+m*cross for every constant m-score future vector.
 Exact checked proposition: forall n : nat, forall r c a : R, vector_schur_action r c (repeat a n) = repeat (((1-c)+INR n*equicorr_schur_cross r c)*a) n.
 Premises and side conditions: True finite-list dimensions and coordinate totals are used throughout; all inverse eigenvalues, positivity and admissible correlation conditions are explicit in the theorem statement when needed.
 Proof/definition method: Reuse Stdlib.repeat/map_repeat and the previously established finite constant-vector sum.
 Library reuse: Stdlib.List, Reals, Lra, Psatz, Field/Ring, and the maintained FiniteSum, SequentialReport, EquicorrelationSpectral and EquicorrelationVectors theorems.
 Boundary: Deterministic rank-one real vector and Schur quadratic algebra; no inference of Gaussian conditional laws, normal quantiles or empirical composite-score accuracy.
 *)
Theorem vector_schur_action_constant :
 forall n : nat, forall r c a : R,
 vector_schur_action r c (repeat a n) =
 repeat (((1-c)+INR n*equicorr_schur_cross r c)*a) n.
Proof.
 intros n r c a.
 unfold vector_schur_action.
 rewrite vector_real_sum_repeat, map_repeat.
 f_equal; ring.
Qed.

(**
 [vector_schur_action_quadratic] (theorem) — The actual coordinate dot-product against the Schur residual action equals the previously checked Schur quadratic form.
 Mathematical meaning: The actual coordinate dot-product against the Schur residual action equals the previously checked Schur quadratic form.
 Exact checked proposition: forall r c : R, forall ys : list R, finite_sum (fun y => y*((1-c)*y+ equicorr_schur_cross r c*vector_real_sum ys)) ys = vector_schur_form r c ys.
 Premises and side conditions: True finite-list dimensions and coordinate totals are used throughout; all inverse eigenvalues, positivity and admissible correlation conditions are explicit in the theorem statement when needed.
 Proof/definition method: Expand the literal finite-sum dot-product with shared linearity and the maintained Schur contrast gap theorem.
 Library reuse: Stdlib.List, Reals, Lra, Psatz, Field/Ring, and the maintained FiniteSum, SequentialReport, EquicorrelationSpectral and EquicorrelationVectors theorems.
 Boundary: Deterministic rank-one real vector and Schur quadratic algebra; no inference of Gaussian conditional laws, normal quantiles or empirical composite-score accuracy.
 *)
Theorem vector_schur_action_quadratic :
 forall r c : R, forall ys : list R,
 finite_sum (fun y => y*((1-c)*y+
     equicorr_schur_cross r c*vector_real_sum ys)) ys =
 vector_schur_form r c ys.
Proof.
 intros r c ys.
 transitivity (finite_sum (fun y =>
     (1-c)*(y*y) + (equicorr_schur_cross r c*vector_real_sum ys)*y) ys).
 { apply finite_sum_ext; intro y; ring. }
 rewrite finite_sum_add, finite_sum_scale, finite_sum_scale.
 unfold vector_schur_form, equicorr_schur_energy,
   vector_square_energy, vector_real_sum.
 rewrite equicorr_schur_diagonal_contrast_gap.
 ring.
Qed.

(**
 [vector_schur_action_positive_pairing] (theorem) — The Schur action defines a positive semidefinite concrete quadratic pairing in the admissible nonnegative-correlation regime.
 Mathematical meaning: The Schur action defines a positive semidefinite concrete quadratic pairing in the admissible nonnegative-correlation regime.
 Exact checked proposition: forall r c : R, forall ys : list R, 1<=r -> 0<=c -> c<=1 -> 0<=finite_sum (fun y => y*((1-c)*y+ equicorr_schur_cross r c*vector_real_sum ys)) ys.
 Premises and side conditions: True finite-list dimensions and coordinate totals are used throughout; all inverse eigenvalues, positivity and admissible correlation conditions are explicit in the theorem statement when needed.
 Proof/definition method: Delegate positivity to the already checked finite-vector Schur PSD theorem after proving the explicit dot-action equality.
 Library reuse: Stdlib.List, Reals, Lra, Psatz, Field/Ring, and the maintained FiniteSum, SequentialReport, EquicorrelationSpectral and EquicorrelationVectors theorems.
 Boundary: Deterministic rank-one real vector and Schur quadratic algebra; no inference of Gaussian conditional laws, normal quantiles or empirical composite-score accuracy.
 *)
Theorem vector_schur_action_positive_pairing :
 forall r c : R, forall ys : list R,
 1<=r -> 0<=c -> c<=1 ->
 0<=finite_sum (fun y => y*((1-c)*y+
     equicorr_schur_cross r c*vector_real_sum ys)) ys.
Proof.
 intros r c ys Hr Hc Hu.
 rewrite vector_schur_action_quadratic.
 apply vector_schur_psd; assumption.
Qed.

