(** Module: EquicorrelationVectors.v
   Purpose: Close the report's missing bridge from abstract equicorrelation
   energy/sum criteria to concrete finite vectors of standardized scores.
   Mathematical representation: Stdlib.list R stores the coordinates.
   All coordinate aggregation uses FiniteSum.finite_sum, not bespoke folds.
   The rank-one Gram form, Schur block and scalar covariance action reuse
   EquicorrelationSpectral definitions. Natural numbers encode true lengths.
   Explicit hypotheses: Correlation, dimension, nonempty vector and
   positive squared energy premises are attached to each theorem. The
   exact fixed-dimension domain criterion is proved for n >= 2.
   Library use: Stdlib.Reals, List.repeat/map/Forall, Lra, Psatz, Field,
   Ring; FiniteSum positive/zero/affine sum laws and maintained
   EquicorrelationSpectral results. No new axioms or spectral package.
   Limitations: Finite real-vector matrix algebra only; Gaussian
   realization, conditional distributions, regular conditional laws,
   empirical IQ validity, and normal-integral accuracy remain separate.
   Reproduction: rocq compile FiniteSum.v; rocq compile Hoeflin.v;
   rocq compile SequentialReport.v; rocq compile
   EquicorrelationSpectral.v; rocq compile EquicorrelationVectors.v;
   after the established dependency compilation under Rocq 9.2.
 *)
From Stdlib Require Import Reals Lra Psatz List.
Require Import FiniteSum SequentialReport EquicorrelationSpectral.
Import ListNotations.
Open Scope R_scope.

(**
 [vector_real_sum] (definition) — Sum of the coordinates of an arbitrary finite real list.
 Mathematical meaning: Sum of the coordinates of an arbitrary finite real list.
 Exact declaration: Definition vector_real_sum (xs : list R) : R := finite_sum (fun x => x) xs.
 Premises and side conditions: Nonempty length, positivity, coordinate membership, and nonzero eigenvalue assumptions are explicit where required. Lists are finite, not statistical populations.
 Proof/definition method: Transparent wrapper around the maintained library-backed finite sum or rank-one algebra.
 Library reuse: Stdlib.List, Reals, Lra, Psatz, Ring and Field; FiniteSum shared lemmas and EquicorrelationSpectral identities, without custom summation or matrix recursion.
 Boundary: Only deterministic finite-dimensional real algebra is proved. No Gaussian realization, probabilistic conditional expectation or model calibration follows.
 *)
Definition vector_real_sum (xs : list R) : R := finite_sum (fun x => x) xs.

(**
 [vector_square_energy] (definition) — The diagonal squared Euclidean norm, using the shared finite sum.
 Mathematical meaning: The diagonal squared Euclidean norm, using the shared finite sum.
 Exact declaration: Definition vector_square_energy (xs : list R) : R := finite_sum (fun x => x*x) xs.
 Premises and side conditions: Nonempty length, positivity, coordinate membership, and nonzero eigenvalue assumptions are explicit where required. Lists are finite, not statistical populations.
 Proof/definition method: Transparent wrapper around the maintained library-backed finite sum or rank-one algebra.
 Library reuse: Stdlib.List, Reals, Lra, Psatz, Ring and Field; FiniteSum shared lemmas and EquicorrelationSpectral identities, without custom summation or matrix recursion.
 Boundary: Only deterministic finite-dimensional real algebra is proved. No Gaussian realization, probabilistic conditional expectation or model calibration follows.
 *)
Definition vector_square_energy (xs : list R) : R := finite_sum (fun x => x*x) xs.

(**
 [vector_center_energy] (definition) — Squared deviations of real coordinates around a supplied center.
 Mathematical meaning: Squared deviations of real coordinates around a supplied center.
 Exact declaration: Definition vector_center_energy (xs : list R) (a : R) : R := finite_sum (fun x => (x-a)*(x-a)) xs.
 Premises and side conditions: Nonempty length, positivity, coordinate membership, and nonzero eigenvalue assumptions are explicit where required. Lists are finite, not statistical populations.
 Proof/definition method: Transparent wrapper around the maintained library-backed finite sum or rank-one algebra.
 Library reuse: Stdlib.List, Reals, Lra, Psatz, Ring and Field; FiniteSum shared lemmas and EquicorrelationSpectral identities, without custom summation or matrix recursion.
 Boundary: Only deterministic finite-dimensional real algebra is proved. No Gaussian realization, probabilistic conditional expectation or model calibration follows.
 *)
Definition vector_center_energy (xs : list R) (a : R) : R := finite_sum (fun x => (x-a)*(x-a)) xs.

(**
 [vector_equicorrelation_form] (definition) — Explicit quadratic form of the equicorrelation matrix evaluated on an actual real score list.
 Mathematical meaning: Explicit quadratic form of the equicorrelation matrix evaluated on an actual real score list.
 Exact declaration: Definition vector_equicorrelation_form (c : R) (xs : list R) : R := equicorr_energy c (vector_square_energy xs) (vector_real_sum xs).
 Premises and side conditions: Nonempty length, positivity, coordinate membership, and nonzero eigenvalue assumptions are explicit where required. Lists are finite, not statistical populations.
 Proof/definition method: Transparent wrapper around the maintained library-backed finite sum or rank-one algebra.
 Library reuse: Stdlib.List, Reals, Lra, Psatz, Ring and Field; FiniteSum shared lemmas and EquicorrelationSpectral identities, without custom summation or matrix recursion.
 Boundary: Only deterministic finite-dimensional real algebra is proved. No Gaussian realization, probabilistic conditional expectation or model calibration follows.
 *)
Definition vector_equicorrelation_form (c : R) (xs : list R) : R := equicorr_energy c (vector_square_energy xs) (vector_real_sum xs).

(**
 [vector_schur_form] (definition) — Schur residual quadratic form evaluated on an actual future-score list.
 Mathematical meaning: Schur residual quadratic form evaluated on an actual future-score list.
 Exact declaration: Definition vector_schur_form (r c : R) (xs : list R) : R := equicorr_schur_energy r c (vector_square_energy xs) (vector_real_sum xs).
 Premises and side conditions: Nonempty length, positivity, coordinate membership, and nonzero eigenvalue assumptions are explicit where required. Lists are finite, not statistical populations.
 Proof/definition method: Transparent wrapper around the maintained library-backed finite sum or rank-one algebra.
 Library reuse: Stdlib.List, Reals, Lra, Psatz, Ring and Field; FiniteSum shared lemmas and EquicorrelationSpectral identities, without custom summation or matrix recursion.
 Boundary: Only deterministic finite-dimensional real algebra is proved. No Gaussian realization, probabilistic conditional expectation or model calibration follows.
 *)
Definition vector_schur_form (r c : R) (xs : list R) : R := equicorr_schur_energy r c (vector_square_energy xs) (vector_real_sum xs).

(**
 [vector_equicorrelation_action] (definition) — List-map representation of multiplying by an equicorrelation matrix without custom index recursion.
 Mathematical meaning: List-map representation of multiplying by an equicorrelation matrix without custom index recursion.
 Exact declaration: Definition vector_equicorrelation_action (c : R) (xs : list R) : list R := map (fun x => equicorr_action c x (vector_real_sum xs)) xs.
 Premises and side conditions: Nonempty length, positivity, coordinate membership, and nonzero eigenvalue assumptions are explicit where required. Lists are finite, not statistical populations.
 Proof/definition method: Transparent wrapper around the maintained library-backed finite sum or rank-one algebra.
 Library reuse: Stdlib.List, Reals, Lra, Psatz, Ring and Field; FiniteSum shared lemmas and EquicorrelationSpectral identities, without custom summation or matrix recursion.
 Boundary: Only deterministic finite-dimensional real algebra is proved. No Gaussian realization, probabilistic conditional expectation or model calibration follows.
 *)
Definition vector_equicorrelation_action (c : R) (xs : list R) : list R := map (fun x => equicorr_action c x (vector_real_sum xs)) xs.

(**
 [vector_nat_to_real_nonnegative] (theorem) — Natural-number dimension is nonnegative under the standard real embedding.
 Mathematical meaning: Natural-number dimension is nonnegative under the standard real embedding.
 Exact checked proposition: forall n : nat, 0 <= INR n.
 Premises and side conditions: Nonempty length, positivity, coordinate membership, and nonzero eigenvalue assumptions are explicit where required. Lists are finite, not statistical populations.
 Proof/definition method: Use Stdlib's S_INR, natural induction and Lra.
 Library reuse: Stdlib.List, Reals, Lra, Psatz, Ring and Field; FiniteSum shared lemmas and EquicorrelationSpectral identities, without custom summation or matrix recursion.
 Boundary: Only deterministic finite-dimensional real algebra is proved. No Gaussian realization, probabilistic conditional expectation or model calibration follows.
 *)
Theorem vector_nat_to_real_nonnegative :
  forall n : nat, 0 <= INR n.
Proof.
 intros n; induction n as [|n IH]; [simpl; lra | rewrite S_INR; lra].
Qed.

(**
 [vector_nat_to_real_successor_positive] (theorem) — A nonempty real vector has strictly positive embedded dimension.
 Mathematical meaning: A nonempty real vector has strictly positive embedded dimension.
 Exact checked proposition: forall n : nat, 0 < INR (S n).
 Premises and side conditions: Nonempty length, positivity, coordinate membership, and nonzero eigenvalue assumptions are explicit where required. Lists are finite, not statistical populations.
 Proof/definition method: Reuse the embedding monotonicity established above.
 Library reuse: Stdlib.List, Reals, Lra, Psatz, Ring and Field; FiniteSum shared lemmas and EquicorrelationSpectral identities, without custom summation or matrix recursion.
 Boundary: Only deterministic finite-dimensional real algebra is proved. No Gaussian realization, probabilistic conditional expectation or model calibration follows.
 *)
Theorem vector_nat_to_real_successor_positive :
  forall n : nat, 0 < INR (S n).
Proof.
 intro n; rewrite S_INR; pose proof (vector_nat_to_real_nonnegative n); lra.
Qed.

(**
 [vector_real_sum_append] (theorem) — Coordinate summation respects concatenation without a bespoke fold.
 Mathematical meaning: Coordinate summation respects concatenation without a bespoke fold.
 Exact checked proposition: forall xs ys : list R, vector_real_sum (xs ++ ys) = vector_real_sum xs + vector_real_sum ys.
 Premises and side conditions: Nonempty length, positivity, coordinate membership, and nonzero eigenvalue assumptions are explicit where required. Lists are finite, not statistical populations.
 Proof/definition method: Directly reuse the existing finite_sum_app law.
 Library reuse: Stdlib.List, Reals, Lra, Psatz, Ring and Field; FiniteSum shared lemmas and EquicorrelationSpectral identities, without custom summation or matrix recursion.
 Boundary: Only deterministic finite-dimensional real algebra is proved. No Gaussian realization, probabilistic conditional expectation or model calibration follows.
 *)
Theorem vector_real_sum_append :
  forall xs ys : list R, vector_real_sum (xs ++ ys) = vector_real_sum xs + vector_real_sum ys.
Proof.
 intros xs ys; unfold vector_real_sum; apply finite_sum_app.
Qed.

(**
 [vector_square_energy_append] (theorem) — Squared Euclidean energy is additive across concatenated score lists.
 Mathematical meaning: Squared Euclidean energy is additive across concatenated score lists.
 Exact checked proposition: forall xs ys : list R, vector_square_energy (xs ++ ys) = vector_square_energy xs + vector_square_energy ys.
 Premises and side conditions: Nonempty length, positivity, coordinate membership, and nonzero eigenvalue assumptions are explicit where required. Lists are finite, not statistical populations.
 Proof/definition method: Instantiate the shared finite_sum_app law with the square integrand.
 Library reuse: Stdlib.List, Reals, Lra, Psatz, Ring and Field; FiniteSum shared lemmas and EquicorrelationSpectral identities, without custom summation or matrix recursion.
 Boundary: Only deterministic finite-dimensional real algebra is proved. No Gaussian realization, probabilistic conditional expectation or model calibration follows.
 *)
Theorem vector_square_energy_append :
  forall xs ys : list R, vector_square_energy (xs ++ ys) = vector_square_energy xs + vector_square_energy ys.
Proof.
 intros xs ys; unfold vector_square_energy; apply finite_sum_app.
Qed.

(**
 [vector_real_sum_scale] (theorem) — Scaling a finite score vector scales its coordinate sum exactly.
 Mathematical meaning: Scaling a finite score vector scales its coordinate sum exactly.
 Exact checked proposition: forall xs : list R, forall a : R, vector_real_sum (map (fun x => a*x) xs) = a*vector_real_sum xs.
 Premises and side conditions: Nonempty length, positivity, coordinate membership, and nonzero eigenvalue assumptions are explicit where required. Lists are finite, not statistical populations.
 Proof/definition method: Compose Stdlib.List.map with finite_sum_map and finite_sum_scale.
 Library reuse: Stdlib.List, Reals, Lra, Psatz, Ring and Field; FiniteSum shared lemmas and EquicorrelationSpectral identities, without custom summation or matrix recursion.
 Boundary: Only deterministic finite-dimensional real algebra is proved. No Gaussian realization, probabilistic conditional expectation or model calibration follows.
 *)
Theorem vector_real_sum_scale :
  forall xs : list R, forall a : R, vector_real_sum (map (fun x => a*x) xs) = a*vector_real_sum xs.
Proof.
 intros xs a; unfold vector_real_sum; rewrite finite_sum_map, finite_sum_scale; reflexivity.
Qed.

(**
 [vector_square_energy_scale] (theorem) — Scaling every coordinate by a multiplies squared energy by a².
 Mathematical meaning: Scaling every coordinate by a multiplies squared energy by a².
 Exact checked proposition: forall xs : list R, forall a : R, vector_square_energy (map (fun x => a*x) xs) = a*a*vector_square_energy xs.
 Premises and side conditions: Nonempty length, positivity, coordinate membership, and nonzero eigenvalue assumptions are explicit where required. Lists are finite, not statistical populations.
 Proof/definition method: Use finite_sum_map, finite_sum_ext and finite_sum_scale; no new induction.
 Library reuse: Stdlib.List, Reals, Lra, Psatz, Ring and Field; FiniteSum shared lemmas and EquicorrelationSpectral identities, without custom summation or matrix recursion.
 Boundary: Only deterministic finite-dimensional real algebra is proved. No Gaussian realization, probabilistic conditional expectation or model calibration follows.
 *)
Theorem vector_square_energy_scale :
  forall xs : list R, forall a : R, vector_square_energy (map (fun x => a*x) xs) = a*a*vector_square_energy xs.
Proof.
 intros xs a; unfold vector_square_energy.
 rewrite finite_sum_map.
 transitivity (finite_sum (fun x => (a*a)*(x*x)) xs).
 { apply finite_sum_ext; intro x; ring. }
 rewrite finite_sum_scale; reflexivity.
Qed.

(**
 [vector_real_sum_repeat] (theorem) — An n-dimensional constant vector has coordinate sum n*a.
 Mathematical meaning: An n-dimensional constant vector has coordinate sum n*a.
 Exact checked proposition: forall n : nat, forall a : R, vector_real_sum (repeat a n) = INR n*a.
 Premises and side conditions: Nonempty length, positivity, coordinate membership, and nonzero eigenvalue assumptions are explicit where required. Lists are finite, not statistical populations.
 Proof/definition method: Induct over Stdlib.List.repeat and use S_INR.
 Library reuse: Stdlib.List, Reals, Lra, Psatz, Ring and Field; FiniteSum shared lemmas and EquicorrelationSpectral identities, without custom summation or matrix recursion.
 Boundary: Only deterministic finite-dimensional real algebra is proved. No Gaussian realization, probabilistic conditional expectation or model calibration follows.
 *)
Theorem vector_real_sum_repeat :
  forall n : nat, forall a : R, vector_real_sum (repeat a n) = INR n*a.
Proof.
 induction n as [|n IH]; intro a.
 - unfold vector_real_sum, finite_sum; simpl; ring.
 - change (a+vector_real_sum (repeat a n) = INR (S n)*a).
   rewrite IH, S_INR; ring.
Qed.

(**
 [vector_square_energy_repeat] (theorem) — A constant vector has squared energy n*a².
 Mathematical meaning: A constant vector has squared energy n*a².
 Exact checked proposition: forall n : nat, forall a : R, vector_square_energy (repeat a n) = INR n*a*a.
 Premises and side conditions: Nonempty length, positivity, coordinate membership, and nonzero eigenvalue assumptions are explicit where required. Lists are finite, not statistical populations.
 Proof/definition method: Use the standard repeat recursion only for this base conversion law.
 Library reuse: Stdlib.List, Reals, Lra, Psatz, Ring and Field; FiniteSum shared lemmas and EquicorrelationSpectral identities, without custom summation or matrix recursion.
 Boundary: Only deterministic finite-dimensional real algebra is proved. No Gaussian realization, probabilistic conditional expectation or model calibration follows.
 *)
Theorem vector_square_energy_repeat :
  forall n : nat, forall a : R, vector_square_energy (repeat a n) = INR n*a*a.
Proof.
 induction n as [|n IH]; intro a.
 - unfold vector_square_energy, finite_sum; simpl; ring.
 - change (a*a+vector_square_energy (repeat a n) = INR (S n)*a*a).
   rewrite IH, S_INR; ring.
Qed.

(**
 [vector_real_sum_affine] (theorem) — A common affine transformation of all coordinates changes the aggregate sum by a*sum + n*b.
 Mathematical meaning: A common affine transformation of all coordinates changes the aggregate sum by a*sum + n*b.
 Exact checked proposition: forall xs : list R, forall a b : R, vector_real_sum (map (fun x => a*x+b) xs) = a*vector_real_sum xs + INR (length xs)*b.
 Premises and side conditions: Nonempty length, positivity, coordinate membership, and nonzero eigenvalue assumptions are explicit where required. Lists are finite, not statistical populations.
 Proof/definition method: Reuse finite-sum linearity and the Stdlib constant sum.
 Library reuse: Stdlib.List, Reals, Lra, Psatz, Ring and Field; FiniteSum shared lemmas and EquicorrelationSpectral identities, without custom summation or matrix recursion.
 Boundary: Only deterministic finite-dimensional real algebra is proved. No Gaussian realization, probabilistic conditional expectation or model calibration follows.
 *)
Theorem vector_real_sum_affine :
  forall xs : list R, forall a b : R,
 vector_real_sum (map (fun x => a*x+b) xs) =
 a*vector_real_sum xs + INR (length xs)*b.
Proof.
 intros xs a b.
 unfold vector_real_sum at 1.
 rewrite finite_sum_map.
 change (finite_sum (fun x => a*x+b) xs =
   a*vector_real_sum xs + INR (length xs)*b).
 rewrite finite_sum_add, finite_sum_scale, finite_sum_const.
 reflexivity.
Qed.

(**
 [vector_center_energy_expansion] (theorem) — The centered sum of squares equals energy minus twice the center-weighted total plus n times center squared.
 Mathematical meaning: The centered sum of squares equals energy minus twice the center-weighted total plus n times center squared.
 Exact checked proposition: forall xs : list R, forall a : R, vector_center_energy xs a = vector_square_energy xs - 2*a*vector_real_sum xs + INR(length xs)*a*a.
 Premises and side conditions: Nonempty length, positivity, coordinate membership, and nonzero eigenvalue assumptions are explicit where required. Lists are finite, not statistical populations.
 Proof/definition method: Factor the polynomial pointwise, then use existing finite-sum linearity, scaling, and constants.
 Library reuse: Stdlib.List, Reals, Lra, Psatz, Ring and Field; FiniteSum shared lemmas and EquicorrelationSpectral identities, without custom summation or matrix recursion.
 Boundary: Only deterministic finite-dimensional real algebra is proved. No Gaussian realization, probabilistic conditional expectation or model calibration follows.
 *)
Theorem vector_center_energy_expansion :
  forall xs : list R, forall a : R,
 vector_center_energy xs a = vector_square_energy xs -
 2*a*vector_real_sum xs + INR(length xs)*a*a.
Proof.
 intros xs a.
 unfold vector_center_energy.
 transitivity (finite_sum (fun x => x*x + ((-2*a)*x + a*a)) xs).
 { apply finite_sum_ext; intro x; ring. }
 rewrite finite_sum_add, finite_sum_add.
 rewrite finite_sum_scale, finite_sum_const.
 unfold vector_square_energy, vector_real_sum.
 ring.
Qed.

(**
 [vector_center_energy_nonnegative] (theorem) — Every finite centered real-vector squared energy is nonnegative.
 Mathematical meaning: Every finite centered real-vector squared energy is nonnegative.
 Exact checked proposition: forall xs : list R, forall a : R, 0 <= vector_center_energy xs a.
 Premises and side conditions: Nonempty length, positivity, coordinate membership, and nonzero eigenvalue assumptions are explicit where required. Lists are finite, not statistical populations.
 Proof/definition method: Apply existing finite_sum_nonnegative to a pointwise real square.
 Library reuse: Stdlib.List, Reals, Lra, Psatz, Ring and Field; FiniteSum shared lemmas and EquicorrelationSpectral identities, without custom summation or matrix recursion.
 Boundary: Only deterministic finite-dimensional real algebra is proved. No Gaussian realization, probabilistic conditional expectation or model calibration follows.
 *)
Theorem vector_center_energy_nonnegative :
  forall xs : list R, forall a : R, 0 <= vector_center_energy xs a.
Proof.
 intros xs a; unfold vector_center_energy.
 apply finite_sum_nonnegative; intros x _.
 change (0 <= Rsqr (x-a)); apply Rle_0_sqr.
Qed.

(**
 [vector_square_energy_nonnegative] (theorem) — The squared energy of any finite real score vector is nonnegative.
 Mathematical meaning: The squared energy of any finite real score vector is nonnegative.
 Exact checked proposition: forall xs : list R, 0 <= vector_square_energy xs.
 Premises and side conditions: Nonempty length, positivity, coordinate membership, and nonzero eigenvalue assumptions are explicit where required. Lists are finite, not statistical populations.
 Proof/definition method: Reuse finite_sum_nonnegative with the squared-score integrand.
 Library reuse: Stdlib.List, Reals, Lra, Psatz, Ring and Field; FiniteSum shared lemmas and EquicorrelationSpectral identities, without custom summation or matrix recursion.
 Boundary: Only deterministic finite-dimensional real algebra is proved. No Gaussian realization, probabilistic conditional expectation or model calibration follows.
 *)
Theorem vector_square_energy_nonnegative :
  forall xs : list R, 0 <= vector_square_energy xs.
Proof.
 intro xs; unfold vector_square_energy.
 apply finite_sum_nonnegative; intros x _.
 change (0 <= Rsqr x); apply Rle_0_sqr.
Qed.

(**
 [vector_center_zero_iff_constant] (theorem) — Centered squared energy vanishes exactly when every vector component equals the supplied center.
 Mathematical meaning: Centered squared energy vanishes exactly when every vector component equals the supplied center.
 Exact checked proposition: forall xs : list R, forall a : R, vector_center_energy xs a = 0 <-> Forall (fun x => x=a) xs.
 Premises and side conditions: Nonempty length, positivity, coordinate membership, and nonzero eigenvalue assumptions are explicit where required. Lists are finite, not statistical populations.
 Proof/definition method: Specialize the existing exact nonnegative-zero-support characterization.
 Library reuse: Stdlib.List, Reals, Lra, Psatz, Ring and Field; FiniteSum shared lemmas and EquicorrelationSpectral identities, without custom summation or matrix recursion.
 Boundary: Only deterministic finite-dimensional real algebra is proved. No Gaussian realization, probabilistic conditional expectation or model calibration follows.
 *)
Theorem vector_center_zero_iff_constant :
  forall xs : list R, forall a : R,
 vector_center_energy xs a = 0 <-> Forall (fun x => x=a) xs.
Proof.
 intros xs a.
 assert (Hiff : vector_center_energy xs a = 0 <->
   forall x, In x xs -> (x-a)*(x-a)=0).
 { unfold vector_center_energy.
   apply finite_sum_nonnegative_zero_iff; intros x _.
   change (0 <= Rsqr (x-a)); apply Rle_0_sqr. }
 destruct Hiff as [Hforward Hbackward]; split.
 - intro H; apply Forall_forall; intros x Hin.
   pose proof (Hforward H x Hin); nra.
 - intro H.
   apply Hbackward; intros x Hin.
   pose proof ((proj1 (@Forall_forall R (fun y => y=a) xs)) H x Hin) as Heq.
   rewrite Heq; ring.
Qed.

(**
 [vector_energy_zero_iff_zero_components] (theorem) — The norm-square is zero precisely for an all-zero vector, even when entries repeat.
 Mathematical meaning: The norm-square is zero precisely for an all-zero vector, even when entries repeat.
 Exact checked proposition: forall xs : list R, vector_square_energy xs = 0 <-> Forall (fun x => x=0) xs.
 Premises and side conditions: Nonempty length, positivity, coordinate membership, and nonzero eigenvalue assumptions are explicit where required. Lists are finite, not statistical populations.
 Proof/definition method: Instantiate finite_sum_nonnegative_zero_iff rather than reprove list induction.
 Library reuse: Stdlib.List, Reals, Lra, Psatz, Ring and Field; FiniteSum shared lemmas and EquicorrelationSpectral identities, without custom summation or matrix recursion.
 Boundary: Only deterministic finite-dimensional real algebra is proved. No Gaussian realization, probabilistic conditional expectation or model calibration follows.
 *)
Theorem vector_energy_zero_iff_zero_components :
  forall xs : list R, vector_square_energy xs = 0 <-> Forall (fun x => x=0) xs.
Proof.
 intro xs.
 assert (Hiff : vector_square_energy xs = 0 <->
   forall x, In x xs -> x*x=0).
 { unfold vector_square_energy.
   apply finite_sum_nonnegative_zero_iff; intros x _; nra. }
 destruct Hiff as [Hforward Hbackward]; split.
 - intro H; apply Forall_forall; intros x Hin.
   pose proof (Hforward H x Hin); nra.
 - intro H.
   apply Hbackward; intros x Hin.
   pose proof ((proj1 (@Forall_forall R (fun y => y=0) xs)) H x Hin) as Heq.
   rewrite Heq; ring.
Qed.

(**
 [vector_energy_positive_iff_nonzero_component] (theorem) — Strictly positive vector squared energy is equivalent to an actual nonzero coordinate witness.
 Mathematical meaning: Strictly positive vector squared energy is equivalent to an actual nonzero coordinate witness.
 Exact checked proposition: forall xs : list R, 0 < vector_square_energy xs <-> exists x, In x xs /\ x<>0.
 Premises and side conditions: Nonempty length, positivity, coordinate membership, and nonzero eigenvalue assumptions are explicit where required. Lists are finite, not statistical populations.
 Proof/definition method: Reuse the existing strict-positive finite-sum member criterion.
 Library reuse: Stdlib.List, Reals, Lra, Psatz, Ring and Field; FiniteSum shared lemmas and EquicorrelationSpectral identities, without custom summation or matrix recursion.
 Boundary: Only deterministic finite-dimensional real algebra is proved. No Gaussian realization, probabilistic conditional expectation or model calibration follows.
 *)
Theorem vector_energy_positive_iff_nonzero_component :
  forall xs : list R,
 0 < vector_square_energy xs <->
 exists x, In x xs /\ x<>0.
Proof.
 intro xs.
 assert (Hiff : 0 < vector_square_energy xs <->
   exists x, In x xs /\ 0 < x*x).
 { unfold vector_square_energy.
   apply finite_sum_positive_iff_positive_member; intros x _.
   change (0 <= Rsqr x); apply Rle_0_sqr. }
 destruct Hiff as [Hforward Hbackward]; split.
 - intro H; destruct (Hforward H) as [x [Hin Hp]].
   exists x; split; [exact Hin | nra].
 - intros [x [Hin Hnz]].
   apply Hbackward; exists x; split; [exact Hin | nra].
Qed.

(**
 [vector_center_energy_mean_identity] (theorem) — For every nonempty finite vector, centered energy at its mean is energy minus squared total divided by its dimension.
 Mathematical meaning: For every nonempty finite vector, centered energy at its mean is energy minus squared total divided by its dimension.
 Exact checked proposition: forall xs : list R, xs<>nil -> vector_center_energy xs (vector_real_sum xs/INR(length xs)) = vector_square_energy xs - vector_real_sum xs*vector_real_sum xs/INR(length xs).
 Premises and side conditions: Nonempty length, positivity, coordinate membership, and nonzero eigenvalue assumptions are explicit where required. Lists are finite, not statistical populations.
 Proof/definition method: Use the exact expansion, the nonempty-list dimension lemma and Stdlib.Field.
 Library reuse: Stdlib.List, Reals, Lra, Psatz, Ring and Field; FiniteSum shared lemmas and EquicorrelationSpectral identities, without custom summation or matrix recursion.
 Boundary: Only deterministic finite-dimensional real algebra is proved. No Gaussian realization, probabilistic conditional expectation or model calibration follows.
 *)
Theorem vector_center_energy_mean_identity :
  forall xs : list R, xs<>nil ->
 vector_center_energy xs (vector_real_sum xs/INR(length xs)) =
 vector_square_energy xs -
 vector_real_sum xs*vector_real_sum xs/INR(length xs).
Proof.
 intros xs Hxs.
 assert (Hdim : 0 < INR(length xs)).
 { destruct xs as [|x rest]; [contradiction|simpl; apply vector_nat_to_real_successor_positive]. }
 rewrite vector_center_energy_expansion.
 field; lra.
Qed.

(**
 [vector_cauchy_schwarz_against_ones] (theorem) — Finite-vector Cauchy–Schwarz: the squared coordinate sum does not exceed dimension times squared Euclidean energy.
 Mathematical meaning: Finite-vector Cauchy–Schwarz: the squared coordinate sum does not exceed dimension times squared Euclidean energy.
 Exact checked proposition: forall xs : list R, vector_real_sum xs*vector_real_sum xs <= INR(length xs)*vector_square_energy xs.
 Premises and side conditions: Nonempty length, positivity, coordinate membership, and nonzero eigenvalue assumptions are explicit where required. Lists are finite, not statistical populations.
 Proof/definition method: Derive finite Cauchy–Schwarz from the exact centered sum-of-squares identity and nonnegativity.
 Library reuse: Stdlib.List, Reals, Lra, Psatz, Ring and Field; FiniteSum shared lemmas and EquicorrelationSpectral identities, without custom summation or matrix recursion.
 Boundary: Only deterministic finite-dimensional real algebra is proved. No Gaussian realization, probabilistic conditional expectation or model calibration follows.
 *)
Theorem vector_cauchy_schwarz_against_ones :
  forall xs : list R,
 vector_real_sum xs*vector_real_sum xs <=
 INR(length xs)*vector_square_energy xs.
Proof.
 intros [|x xs].
 - unfold vector_real_sum, vector_square_energy, finite_sum; simpl; nra.
 - assert (Hdim : 0 < INR(length (x::xs))).
   { simpl; apply vector_nat_to_real_successor_positive. }
   pose proof (vector_center_energy_nonnegative (x::xs)
     (vector_real_sum (x::xs)/INR(length (x::xs)))) as H.
   rewrite (vector_center_energy_mean_identity (x::xs)) in H by discriminate.
   assert (Hscaled : 0 <= INR(length (x::xs)) *
      (vector_square_energy (x::xs) -
       vector_real_sum (x::xs)*vector_real_sum (x::xs)/INR(length (x::xs)))).
   { apply Rmult_le_pos; lra. }
   replace (INR(length (x::xs)) *
      (vector_square_energy (x::xs) -
       vector_real_sum (x::xs)*vector_real_sum (x::xs)/INR(length (x::xs))))
     with (INR(length (x::xs))*vector_square_energy (x::xs) -
       vector_real_sum (x::xs)*vector_real_sum (x::xs)) in Hscaled
     by (field; lra).
   lra.
Qed.

(**
 [vector_cauchy_feasibility] (theorem) — Every nonempty concrete real score vector satisfies the feasibility inequality assumed in EquicorrelationSpectral.
 Mathematical meaning: Every nonempty concrete real score vector satisfies the feasibility inequality assumed in EquicorrelationSpectral.
 Exact checked proposition: forall xs : list R, xs<>nil -> 0 <= vector_square_energy xs - vector_real_sum xs*vector_real_sum xs/INR(length xs).
 Premises and side conditions: Nonempty length, positivity, coordinate membership, and nonzero eigenvalue assumptions are explicit where required. Lists are finite, not statistical populations.
 Proof/definition method: Turn the checked Cauchy–Schwarz inequality into the earlier feasible-summary premise.
 Library reuse: Stdlib.List, Reals, Lra, Psatz, Ring and Field; FiniteSum shared lemmas and EquicorrelationSpectral identities, without custom summation or matrix recursion.
 Boundary: Only deterministic finite-dimensional real algebra is proved. No Gaussian realization, probabilistic conditional expectation or model calibration follows.
 *)
Theorem vector_cauchy_feasibility :
  forall xs : list R, xs<>nil ->
 0 <= vector_square_energy xs -
 vector_real_sum xs*vector_real_sum xs/INR(length xs).
Proof.
 intros xs Hxs.
 assert (Hdim : 0 < INR(length xs)).
 { destruct xs as [|x rest]; [contradiction|simpl; apply vector_nat_to_real_successor_positive]. }
 pose proof (vector_cauchy_schwarz_against_ones xs) as Hcs.
 replace (vector_square_energy xs -
   vector_real_sum xs*vector_real_sum xs/INR(length xs))
 with ((INR(length xs)*vector_square_energy xs -
  vector_real_sum xs*vector_real_sum xs)/INR(length xs))
 by (field; lra).
 unfold Rdiv; apply Rmult_le_pos; [lra|].
 left; apply Rinv_0_lt_compat; lra.
Qed.

(**
 [vector_equicorrelation_centered_decomposition] (theorem) — Every nonempty concrete vector admits the exact common/contrast eigenspace decomposition of its equicorrelation form.
 Mathematical meaning: Every nonempty concrete vector admits the exact common/contrast eigenspace decomposition of its equicorrelation form.
 Exact checked proposition: forall xs : list R, forall c : R, xs<>nil -> vector_equicorrelation_form c xs = (1-c)*(vector_square_energy xs - vector_real_sum xs*vector_real_sum xs/INR(length xs)) + sequential_d (INR(length xs)) c * (vector_real_sum xs*vector_real_sum xs/INR(length xs)).
 Premises and side conditions: Nonempty length, positivity, coordinate membership, and nonzero eigenvalue assumptions are explicit where required. Lists are finite, not statistical populations.
 Proof/definition method: Apply the existing rank-one eigenspace decomposition to genuine finite-vector energy and sum.
 Library reuse: Stdlib.List, Reals, Lra, Psatz, Ring and Field; FiniteSum shared lemmas and EquicorrelationSpectral identities, without custom summation or matrix recursion.
 Boundary: Only deterministic finite-dimensional real algebra is proved. No Gaussian realization, probabilistic conditional expectation or model calibration follows.
 *)
Theorem vector_equicorrelation_centered_decomposition :
  forall xs : list R, forall c : R, xs<>nil ->
 vector_equicorrelation_form c xs =
 (1-c)*(vector_square_energy xs -
   vector_real_sum xs*vector_real_sum xs/INR(length xs)) +
 sequential_d (INR(length xs)) c *
 (vector_real_sum xs*vector_real_sum xs/INR(length xs)).
Proof.
 intros xs c Hxs.
 assert (Hdim : INR(length xs)<>0).
 { destruct xs as [|x rest]; [contradiction|simpl].
   pose proof (vector_nat_to_real_successor_positive (length rest)); lra. }
 unfold vector_equicorrelation_form.
 apply equicorr_centered_energy_decomposition; exact Hdim.
Qed.

(**
 [vector_equicorrelation_psd] (theorem) — Nonnegative contrast and common-mode eigenvalues imply positive semidefiniteness for every concrete real vector.
 Mathematical meaning: Nonnegative contrast and common-mode eigenvalues imply positive semidefiniteness for every concrete real vector.
 Exact checked proposition: forall xs : list R, forall c : R, c<=1 -> 0<=sequential_d (INR(length xs)) c -> 0<=vector_equicorrelation_form c xs.
 Premises and side conditions: Nonempty length, positivity, coordinate membership, and nonzero eigenvalue assumptions are explicit where required. Lists are finite, not statistical populations.
 Proof/definition method: Reuse the prior PSD theorem and the newly verified vector feasibility bridge.
 Library reuse: Stdlib.List, Reals, Lra, Psatz, Ring and Field; FiniteSum shared lemmas and EquicorrelationSpectral identities, without custom summation or matrix recursion.
 Boundary: Only deterministic finite-dimensional real algebra is proved. No Gaussian realization, probabilistic conditional expectation or model calibration follows.
 *)
Theorem vector_equicorrelation_psd :
  forall xs : list R, forall c : R,
 c<=1 -> 0<=sequential_d (INR(length xs)) c ->
 0<=vector_equicorrelation_form c xs.
Proof.
 intros [|x xs] c Hc Hd.
 - unfold vector_equicorrelation_form, vector_square_energy, vector_real_sum, equicorr_energy, finite_sum; simpl; nra.
 - unfold vector_equicorrelation_form.
   apply (equicorr_psd_on_feasible_summaries
     (INR(length (x::xs))) c
     (vector_square_energy (x::xs)) (vector_real_sum (x::xs))).
   + simpl; apply vector_nat_to_real_successor_positive.
   + exact Hc.
   + exact Hd.
   + apply vector_cauchy_feasibility; discriminate.
Qed.

(**
 [vector_equicorrelation_pd] (theorem) — Both eigenvalues strictly positive imply strictly positive quadratic form for every nonzero concrete vector.
 Mathematical meaning: Both eigenvalues strictly positive imply strictly positive quadratic form for every nonzero concrete vector.
 Exact checked proposition: forall xs : list R, forall c : R, c<1 -> 0<sequential_d (INR(length xs)) c -> 0<vector_square_energy xs -> 0<vector_equicorrelation_form c xs.
 Premises and side conditions: Nonempty length, positivity, coordinate membership, and nonzero eigenvalue assumptions are explicit where required. Lists are finite, not statistical populations.
 Proof/definition method: Reuse the previous strict PD theorem, finite-vector feasibility, and positive norm-square.
 Library reuse: Stdlib.List, Reals, Lra, Psatz, Ring and Field; FiniteSum shared lemmas and EquicorrelationSpectral identities, without custom summation or matrix recursion.
 Boundary: Only deterministic finite-dimensional real algebra is proved. No Gaussian realization, probabilistic conditional expectation or model calibration follows.
 *)
Theorem vector_equicorrelation_pd :
  forall xs : list R, forall c : R,
 c<1 -> 0<sequential_d (INR(length xs)) c ->
 0<vector_square_energy xs ->
 0<vector_equicorrelation_form c xs.
Proof.
 intros [|x xs] c Hc Hd He.
 - unfold vector_square_energy, finite_sum in He; simpl in He; lra.
 - unfold vector_equicorrelation_form.
   apply (equicorr_pd_on_nonzero_feasible_summaries
     (INR(length (x::xs))) c
     (vector_square_energy (x::xs)) (vector_real_sum (x::xs))).
   + simpl; apply vector_nat_to_real_successor_positive.
   + exact Hc.
   + exact Hd.
   + exact He.
   + apply vector_cauchy_feasibility; discriminate.
Qed.

(**
 [vector_equicorrelation_common_mode_witness] (theorem) — The constant-one vector realizes the common-mode eigenvalue exactly in any positive dimension.
 Mathematical meaning: The constant-one vector realizes the common-mode eigenvalue exactly in any positive dimension.
 Exact checked proposition: forall n : nat, forall c : R, vector_equicorrelation_form c (repeat 1 (S n)) = INR(S n)*sequential_d (INR(S n)) c.
 Premises and side conditions: Nonempty length, positivity, coordinate membership, and nonzero eigenvalue assumptions are explicit where required. Lists are finite, not statistical populations.
 Proof/definition method: Use both constant-vector finite-sum laws and the existing common-eigenvalue formula.
 Library reuse: Stdlib.List, Reals, Lra, Psatz, Ring and Field; FiniteSum shared lemmas and EquicorrelationSpectral identities, without custom summation or matrix recursion.
 Boundary: Only deterministic finite-dimensional real algebra is proved. No Gaussian realization, probabilistic conditional expectation or model calibration follows.
 *)
Theorem vector_equicorrelation_common_mode_witness :
  forall n : nat, forall c : R,
 vector_equicorrelation_form c (repeat 1 (S n)) =
 INR(S n)*sequential_d (INR(S n)) c.
Proof.
 intros n c; unfold vector_equicorrelation_form.
 rewrite vector_square_energy_repeat, vector_real_sum_repeat.
 replace (INR (S n)*1*1) with (INR (S n)) by ring.
 replace (INR (S n)*1) with (INR (S n)) by ring.
 unfold equicorr_energy, sequential_d; ring.
Qed.

(**
 [vector_equicorrelation_contrast_witness] (theorem) — For every dimension at least two, the padded [1,-1] contrast realizes the 1-c eigenvalue and has energy two.
 Mathematical meaning: For every dimension at least two, the padded [1,-1] contrast realizes the 1-c eigenvalue and has energy two.
 Exact checked proposition: forall k : nat, forall c : R, vector_equicorrelation_form c (1::(-1)::repeat 0 k) = 2*(1-c).
 Premises and side conditions: Nonempty length, positivity, coordinate membership, and nonzero eigenvalue assumptions are explicit where required. Lists are finite, not statistical populations.
 Proof/definition method: Construct the exact two-coordinate contrast using Stdlib.repeat for zero padding.
 Library reuse: Stdlib.List, Reals, Lra, Psatz, Ring and Field; FiniteSum shared lemmas and EquicorrelationSpectral identities, without custom summation or matrix recursion.
 Boundary: Only deterministic finite-dimensional real algebra is proved. No Gaussian realization, probabilistic conditional expectation or model calibration follows.
 *)
Theorem vector_equicorrelation_contrast_witness :
  forall k : nat, forall c : R,
 vector_equicorrelation_form c (1::(-1)::repeat 0 k) = 2*(1-c).
Proof.
 intros k c; unfold vector_equicorrelation_form.
 assert (Hs : vector_real_sum (1::(-1)::repeat 0 k) = 0).
 { change (1 + ((-1) + vector_real_sum (repeat 0 k)) = 0).
   rewrite vector_real_sum_repeat; ring. }
 assert (He : vector_square_energy (1::(-1)::repeat 0 k) = 2).
 { change (1*1 + ((-1)*(-1) + vector_square_energy (repeat 0 k)) = 2).
   rewrite vector_square_energy_repeat; ring. }
 rewrite Hs, He; unfold equicorr_energy; ring.
Qed.

(**
 [vector_equicorrelation_psd_necessary] (theorem) — PSD on all concrete vectors of a fixed dimension at least two forces both rank-one eigenvalues to be nonnegative.
 Mathematical meaning: PSD on all concrete vectors of a fixed dimension at least two forces both rank-one eigenvalues to be nonnegative.
 Exact checked proposition: forall k : nat, forall c : R, (forall xs : list R, length xs=S(S k) -> 0<=vector_equicorrelation_form c xs) -> c<=1 /\ 0<=sequential_d (INR(S(S k))) c.
 Premises and side conditions: Nonempty length, positivity, coordinate membership, and nonzero eigenvalue assumptions are explicit where required. Lists are finite, not statistical populations.
 Proof/definition method: Show necessity by explicit nonzero contrast and common-mode finite-list witnesses.
 Library reuse: Stdlib.List, Reals, Lra, Psatz, Ring and Field; FiniteSum shared lemmas and EquicorrelationSpectral identities, without custom summation or matrix recursion.
 Boundary: Only deterministic finite-dimensional real algebra is proved. No Gaussian realization, probabilistic conditional expectation or model calibration follows.
 *)
Theorem vector_equicorrelation_psd_necessary :
  forall k : nat, forall c : R,
 (forall xs : list R, length xs=S(S k) -> 0<=vector_equicorrelation_form c xs) ->
 c<=1 /\ 0<=sequential_d (INR(S(S k))) c.
Proof.
 intros k c H; split.
 - pose proof (H (1::(-1)::repeat 0 k)) as Hcontrast.
   assert (Hlen : length (1::(-1)::repeat 0 k)=S(S k)).
   { simpl; rewrite repeat_length; reflexivity. }
   specialize (Hcontrast Hlen).
   rewrite vector_equicorrelation_contrast_witness in Hcontrast; lra.
 - pose proof (H (repeat 1 (S(S k)))) as Hcommon.
   assert (Hlen : length (repeat 1 (S(S k)))=S(S k)).
   { apply repeat_length. }
   specialize (Hcommon Hlen).
   rewrite vector_equicorrelation_common_mode_witness in Hcommon.
   pose proof (vector_nat_to_real_successor_positive (S k)) as Hdim.
   nra.
Qed.

(**
 [vector_equicorrelation_psd_iff] (theorem) — Complete PSD criterion for actual n-dimensional real score lists, not merely abstract feasible summaries.
 Mathematical meaning: Complete PSD criterion for actual n-dimensional real score lists, not merely abstract feasible summaries.
 Exact checked proposition: forall k : nat, forall c : R, (forall xs : list R, length xs=S(S k) -> 0<=vector_equicorrelation_form c xs) <-> (c<=1 /\ 0<=sequential_d (INR(S(S k))) c).
 Premises and side conditions: Nonempty length, positivity, coordinate membership, and nonzero eigenvalue assumptions are explicit where required. Lists are finite, not statistical populations.
 Proof/definition method: Combine universal finite-vector positivity with the common/contrast necessity witnesses.
 Library reuse: Stdlib.List, Reals, Lra, Psatz, Ring and Field; FiniteSum shared lemmas and EquicorrelationSpectral identities, without custom summation or matrix recursion.
 Boundary: Only deterministic finite-dimensional real algebra is proved. No Gaussian realization, probabilistic conditional expectation or model calibration follows.
 *)
Theorem vector_equicorrelation_psd_iff :
  forall k : nat, forall c : R,
 (forall xs : list R, length xs=S(S k) -> 0<=vector_equicorrelation_form c xs)
 <-> (c<=1 /\ 0<=sequential_d (INR(S(S k))) c).
Proof.
 intros k c; split.
 - apply vector_equicorrelation_psd_necessary.
 - intros [Hc Hd] xs Hlen.
   apply vector_equicorrelation_psd; [exact Hc|].
   rewrite Hlen; exact Hd.
Qed.

(**
 [vector_equicorrelation_pd_necessary] (theorem) — Positive definiteness on every nonzero vector of a fixed dimension at least two forces strictly positive common and contrast eigenvalues.
 Mathematical meaning: Positive definiteness on every nonzero vector of a fixed dimension at least two forces strictly positive common and contrast eigenvalues.
 Exact checked proposition: forall k : nat, forall c : R, (forall xs : list R, length xs=S(S k) -> 0<vector_square_energy xs -> 0<vector_equicorrelation_form c xs) -> c<1 /\ 0<sequential_d (INR(S(S k))) c.
 Premises and side conditions: Nonempty length, positivity, coordinate membership, and nonzero eigenvalue assumptions are explicit where required. Lists are finite, not statistical populations.
 Proof/definition method: Derive strict eigenvalue necessity from finite real witnesses carrying positive squared energy.
 Library reuse: Stdlib.List, Reals, Lra, Psatz, Ring and Field; FiniteSum shared lemmas and EquicorrelationSpectral identities, without custom summation or matrix recursion.
 Boundary: Only deterministic finite-dimensional real algebra is proved. No Gaussian realization, probabilistic conditional expectation or model calibration follows.
 *)
Theorem vector_equicorrelation_pd_necessary :
  forall k : nat, forall c : R,
 (forall xs : list R, length xs=S(S k) ->
 0<vector_square_energy xs -> 0<vector_equicorrelation_form c xs) ->
 c<1 /\ 0<sequential_d (INR(S(S k))) c.
Proof.
 intros k c H; split.
 - assert (Hlen : length (1::(-1)::repeat 0 k)=S(S k)).
   { simpl; rewrite repeat_length; reflexivity. }
   assert (He : 0<vector_square_energy (1::(-1)::repeat 0 k)).
   { change (0 < 1*1 + ((-1)*(-1) + vector_square_energy (repeat 0 k))).
     rewrite vector_square_energy_repeat; nra. }
   pose proof (H (1::(-1)::repeat 0 k) Hlen He) as Hw.
   rewrite vector_equicorrelation_contrast_witness in Hw; lra.
 - assert (Hlen : length (repeat 1 (S(S k)))=S(S k)).
   { apply repeat_length. }
   assert (He : 0<vector_square_energy (repeat 1 (S(S k)))).
   { rewrite vector_square_energy_repeat.
     pose proof (vector_nat_to_real_successor_positive (S k)); nra. }
   pose proof (H (repeat 1 (S(S k))) Hlen He) as Hw.
   rewrite vector_equicorrelation_common_mode_witness in Hw.
   pose proof (vector_nat_to_real_successor_positive (S k)); nra.
Qed.

(**
 [vector_equicorrelation_pd_iff] (theorem) — Complete positive-definiteness criterion for actual finite real vectors of any fixed dimension at least two.
 Mathematical meaning: Complete positive-definiteness criterion for actual finite real vectors of any fixed dimension at least two.
 Exact checked proposition: forall k : nat, forall c : R, (forall xs : list R, length xs=S(S k) -> 0<vector_square_energy xs -> 0<vector_equicorrelation_form c xs) <-> (c<1 /\ 0<sequential_d (INR(S(S k))) c).
 Premises and side conditions: Nonempty length, positivity, coordinate membership, and nonzero eigenvalue assumptions are explicit where required. Lists are finite, not statistical populations.
 Proof/definition method: Compose strict-positive finite-vector sufficiency and both eigenmode witness necessities.
 Library reuse: Stdlib.List, Reals, Lra, Psatz, Ring and Field; FiniteSum shared lemmas and EquicorrelationSpectral identities, without custom summation or matrix recursion.
 Boundary: Only deterministic finite-dimensional real algebra is proved. No Gaussian realization, probabilistic conditional expectation or model calibration follows.
 *)
Theorem vector_equicorrelation_pd_iff :
  forall k : nat, forall c : R,
 (forall xs : list R, length xs=S(S k) ->
 0<vector_square_energy xs -> 0<vector_equicorrelation_form c xs)
 <-> (c<1 /\ 0<sequential_d (INR(S(S k))) c).
Proof.
 intros k c; split.
 - apply vector_equicorrelation_pd_necessary.
 - intros [Hc Hd] xs Hlen He.
   apply vector_equicorrelation_pd; [exact Hc| |exact He].
   rewrite Hlen; exact Hd.
Qed.

(**
 [vector_schur_psd] (theorem) — The conditioned Schur residual block is positive semidefinite on every actual finite future-score vector when 0<=c<=1.
 Mathematical meaning: The conditioned Schur residual block is positive semidefinite on every actual finite future-score vector when 0<=c<=1.
 Exact checked proposition: forall r c : R, forall xs : list R, 1<=r -> 0<=c -> c<=1 -> 0<=vector_schur_form r c xs.
 Premises and side conditions: Nonempty length, positivity, coordinate membership, and nonzero eigenvalue assumptions are explicit where required. Lists are finite, not statistical populations.
 Proof/definition method: Reuse the checked Schur PSD theorem and the shared finite-sum square nonnegativity.
 Library reuse: Stdlib.List, Reals, Lra, Psatz, Ring and Field; FiniteSum shared lemmas and EquicorrelationSpectral identities, without custom summation or matrix recursion.
 Boundary: Only deterministic finite-dimensional real algebra is proved. No Gaussian realization, probabilistic conditional expectation or model calibration follows.
 *)
Theorem vector_schur_psd :
  forall r c : R, forall xs : list R,
 1<=r -> 0<=c -> c<=1 -> 0<=vector_schur_form r c xs.
Proof.
 intros r c xs Hr Hc Hu; unfold vector_schur_form.
 apply equicorr_schur_psd_nonnegative_correlation; try assumption.
 apply vector_square_energy_nonnegative.
Qed.

(**
 [vector_schur_pd] (theorem) — For 0<=c<1 the Schur residual form is strictly positive for every nonzero future-score vector.
 Mathematical meaning: For 0<=c<1 the Schur residual form is strictly positive for every nonzero future-score vector.
 Exact checked proposition: forall r c : R, forall xs : list R, 1<=r -> 0<=c -> c<1 -> 0<vector_square_energy xs -> 0<vector_schur_form r c xs.
 Premises and side conditions: Nonempty length, positivity, coordinate membership, and nonzero eigenvalue assumptions are explicit where required. Lists are finite, not statistical populations.
 Proof/definition method: Reuse strict Schur positivity on squared energy and the maintained report denominator.
 Library reuse: Stdlib.List, Reals, Lra, Psatz, Ring and Field; FiniteSum shared lemmas and EquicorrelationSpectral identities, without custom summation or matrix recursion.
 Boundary: Only deterministic finite-dimensional real algebra is proved. No Gaussian realization, probabilistic conditional expectation or model calibration follows.
 *)
Theorem vector_schur_pd :
  forall r c : R, forall xs : list R,
 1<=r -> 0<=c -> c<1 -> 0<vector_square_energy xs ->
 0<vector_schur_form r c xs.
Proof.
 intros r c xs Hr Hc Hu He; unfold vector_schur_form.
 apply equicorr_schur_pd_nonnegative_correlation; assumption.
Qed.

(**
 [vector_equicorrelation_action_sum] (theorem) — The coordinate sum of an actual rank-one covariance matrix-vector product is the common eigenvalue times its original sum.
 Mathematical meaning: The coordinate sum of an actual rank-one covariance matrix-vector product is the common eigenvalue times its original sum.
 Exact checked proposition: forall c : R, forall xs : list R, vector_real_sum (vector_equicorrelation_action c xs) = sequential_d (INR(length xs)) c * vector_real_sum xs.
 Premises and side conditions: Nonempty length, positivity, coordinate membership, and nonzero eigenvalue assumptions are explicit where required. Lists are finite, not statistical populations.
 Proof/definition method: Use Stdlib.map plus finite_sum linearity to derive the actual matrix-vector sum eigenidentity.
 Library reuse: Stdlib.List, Reals, Lra, Psatz, Ring and Field; FiniteSum shared lemmas and EquicorrelationSpectral identities, without custom summation or matrix recursion.
 Boundary: Only deterministic finite-dimensional real algebra is proved. No Gaussian realization, probabilistic conditional expectation or model calibration follows.
 *)
Theorem vector_equicorrelation_action_sum :
  forall c : R, forall xs : list R,
 vector_real_sum (vector_equicorrelation_action c xs) =
 sequential_d (INR(length xs)) c * vector_real_sum xs.
Proof.
 intros c xs.
 unfold vector_equicorrelation_action.
 unfold vector_real_sum at 1.
 rewrite finite_sum_map.
 change (finite_sum (fun x => equicorr_action c x (vector_real_sum xs)) xs
   = sequential_d (INR(length xs)) c * vector_real_sum xs).
 unfold equicorr_action.
 rewrite finite_sum_add, finite_sum_scale, finite_sum_const.
 unfold sequential_d; ring.
Qed.

(**
 [vector_equicorrelation_action_repeat] (theorem) — Multiplying a constant finite score vector by the rank-one equicorrelation matrix produces a constant vector scaled by its common eigenvalue.
 Mathematical meaning: Multiplying a constant finite score vector by the rank-one equicorrelation matrix produces a constant vector scaled by its common eigenvalue.
 Exact checked proposition: forall n : nat, forall c a : R, vector_equicorrelation_action c (repeat a n) = repeat (sequential_d (INR n) c*a) n.
 Premises and side conditions: Nonempty length, positivity, coordinate membership, and nonzero eigenvalue assumptions are explicit where required. Lists are finite, not statistical populations.
 Proof/definition method: Reuse Stdlib.List.map_repeat and the constant-sum law rather than implementing matrix rows.
 Library reuse: Stdlib.List, Reals, Lra, Psatz, Ring and Field; FiniteSum shared lemmas and EquicorrelationSpectral identities, without custom summation or matrix recursion.
 Boundary: Only deterministic finite-dimensional real algebra is proved. No Gaussian realization, probabilistic conditional expectation or model calibration follows.
 *)
Theorem vector_equicorrelation_action_repeat :
  forall n : nat, forall c a : R,
 vector_equicorrelation_action c (repeat a n) =
 repeat (sequential_d (INR n) c*a) n.
Proof.
 intros n c a.
 unfold vector_equicorrelation_action.
 rewrite vector_real_sum_repeat.
 rewrite map_repeat.
 f_equal.
 unfold equicorr_action, sequential_d; ring.
Qed.

