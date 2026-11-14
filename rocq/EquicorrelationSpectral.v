(** Module: EquicorrelationSpectral.v
   Purpose: Prove the equicorrelation Gram-form domain, the two invariant
   scalar directions, inverse linear action and residual Schur algebra
   required by the sequential conditional-means report.
   Mathematical representation: A quadratic form is specified by squared
   coordinate energy E and coordinate sum S, with feasibility E >= S^2/n.
   The inverse acts on an individual coordinate and its full sum; the Schur
   form is parameterized by a previously observed block size r.
   Explicit hypotheses: Nonzero inverse denominators, positive nominal
   block sizes, energy feasibility and admissible correlations are stated
   on individual results. Real n is an algebraic generalization of integer
   battery size; feasibility is an explicit premise, not a proved
   vector-valued Cauchy-Schwarz theorem.
   Library use: Rocq Stdlib.Reals, Lra, Psatz, Field and Ring; reuse
   SequentialReport.sequential_d, its positivity theorem and Schur
   identities instead of introducing matrix arithmetic or sum recursions.
   Limitations: This module proves exact algebra and the PSD/PD criterion
   over abstract feasible energy summaries, not Gaussian realization,
   Gaussian conditioning, continuous probability measures or numerical
   quantiles. No claim of a Rocq spectral theorem for general matrices.
   Reproduction: rocq compile SequentialReport.v &&
   rocq compile EquicorrelationSpectral.v under pinned Rocq 9.2; consult
   REPORT_THEOREM_INVENTORY.md and PROOF_REFACTOR_REGISTER.md.
 *)
From Stdlib Require Import Reals Lra Psatz.
Require Import SequentialReport.
Open Scope R_scope.

(**
 [equicorr_energy] (definition) — Quadratic form of the rank-one equicorrelation model in aggregate squared energy and coordinate sum.
 Mathematical meaning: Quadratic form of the rank-one equicorrelation model in aggregate squared energy and coordinate sum.
 Exact definition: Transparent algebraic object defined below.
 Premises and side conditions: All division, strict positivity, correlation-domain and energy-feasibility assumptions appear explicitly in the declaration; none is inferred from a Gaussian model.
 Proof/definition method: Define only the precise rank-one algebraic representation; do not postulate a stochastic matrix.
 Library reuse: Stdlib.Reals, Stdlib.Field/Ring/Lra/Psatz, SequentialReport.sequential_d and previously proved report identities where appropriate; no new list, matrix or summation recursion.
 Boundary: Kernel-checkable deterministic real algebra about quadratic forms and inverse actions; no construction of Gaussian conditional laws or certified normal integrals.
 *)
Definition equicorr_energy (c energy total : R) : R := (1-c)*energy + c*total*total.

(**
 [equicorr_action] (definition) — Matrix-vector action on one coordinate, given its vector's coordinate sum.
 Mathematical meaning: Matrix-vector action on one coordinate, given its vector's coordinate sum.
 Exact definition: Transparent algebraic object defined below.
 Premises and side conditions: All division, strict positivity, correlation-domain and energy-feasibility assumptions appear explicitly in the declaration; none is inferred from a Gaussian model.
 Proof/definition method: Define only the precise rank-one algebraic representation; do not postulate a stochastic matrix.
 Library reuse: Stdlib.Reals, Stdlib.Field/Ring/Lra/Psatz, SequentialReport.sequential_d and previously proved report identities where appropriate; no new list, matrix or summation recursion.
 Boundary: Kernel-checkable deterministic real algebra about quadratic forms and inverse actions; no construction of Gaussian conditional laws or certified normal integrals.
 *)
Definition equicorr_action (c x total : R) : R := (1-c)*x + c*total.

(**
 [equicorr_inverse_entry] (definition) — Inverse rank-one action on one coordinate with the total output sum supplied.
 Mathematical meaning: Inverse rank-one action on one coordinate with the total output sum supplied.
 Exact definition: Transparent algebraic object defined below.
 Premises and side conditions: All division, strict positivity, correlation-domain and energy-feasibility assumptions appear explicitly in the declaration; none is inferred from a Gaussian model.
 Proof/definition method: Define only the precise rank-one algebraic representation; do not postulate a stochastic matrix.
 Library reuse: Stdlib.Reals, Stdlib.Field/Ring/Lra/Psatz, SequentialReport.sequential_d and previously proved report identities where appropriate; no new list, matrix or summation recursion.
 Boundary: Kernel-checkable deterministic real algebra about quadratic forms and inverse actions; no construction of Gaussian conditional laws or certified normal integrals.
 *)
Definition equicorr_inverse_entry (n c y total : R) : R := (y - c*total/sequential_d n c)/(1-c).

(**
 [equicorr_schur_diagonal] (definition) — Algebraic diagonal of the rank-one Schur residual after r observations.
 Mathematical meaning: Algebraic diagonal of the rank-one Schur residual after r observations.
 Exact definition: Transparent algebraic object defined below.
 Premises and side conditions: All division, strict positivity, correlation-domain and energy-feasibility assumptions appear explicitly in the declaration; none is inferred from a Gaussian model.
 Proof/definition method: Define only the precise rank-one algebraic representation; do not postulate a stochastic matrix.
 Library reuse: Stdlib.Reals, Stdlib.Field/Ring/Lra/Psatz, SequentialReport.sequential_d and previously proved report identities where appropriate; no new list, matrix or summation recursion.
 Boundary: Kernel-checkable deterministic real algebra about quadratic forms and inverse actions; no construction of Gaussian conditional laws or certified normal integrals.
 *)
Definition equicorr_schur_diagonal (r c : R) : R := 1-r*c*c/sequential_d r c.

(**
 [equicorr_schur_cross] (definition) — Algebraic off-diagonal of the rank-one Schur residual after r observations.
 Mathematical meaning: Algebraic off-diagonal of the rank-one Schur residual after r observations.
 Exact definition: Transparent algebraic object defined below.
 Premises and side conditions: All division, strict positivity, correlation-domain and energy-feasibility assumptions appear explicitly in the declaration; none is inferred from a Gaussian model.
 Proof/definition method: Define only the precise rank-one algebraic representation; do not postulate a stochastic matrix.
 Library reuse: Stdlib.Reals, Stdlib.Field/Ring/Lra/Psatz, SequentialReport.sequential_d and previously proved report identities where appropriate; no new list, matrix or summation recursion.
 Boundary: Kernel-checkable deterministic real algebra about quadratic forms and inverse actions; no construction of Gaussian conditional laws or certified normal integrals.
 *)
Definition equicorr_schur_cross (r c : R) : R := c-r*c*c/sequential_d r c.

(**
 [equicorr_schur_energy] (definition) — Quadratic form of the exchangeable Schur block in energy/sum coordinates.
 Mathematical meaning: Quadratic form of the exchangeable Schur block in energy/sum coordinates.
 Exact definition: Transparent algebraic object defined below.
 Premises and side conditions: All division, strict positivity, correlation-domain and energy-feasibility assumptions appear explicitly in the declaration; none is inferred from a Gaussian model.
 Proof/definition method: Define only the precise rank-one algebraic representation; do not postulate a stochastic matrix.
 Library reuse: Stdlib.Reals, Stdlib.Field/Ring/Lra/Psatz, SequentialReport.sequential_d and previously proved report identities where appropriate; no new list, matrix or summation recursion.
 Boundary: Kernel-checkable deterministic real algebra about quadratic forms and inverse actions; no construction of Gaussian conditional laws or certified normal integrals.
 *)
Definition equicorr_schur_energy (r c energy total : R) : R := (equicorr_schur_diagonal r c-equicorr_schur_cross r c)*energy + equicorr_schur_cross r c*total*total.

(**
 [equicorr_common_direction_eigenvalue] (theorem) — The all-ones direction has eigenvalue d_n(c); its energy is n times the squared common coordinate.
 Mathematical meaning: The all-ones direction has eigenvalue d_n(c); its energy is n times the squared common coordinate.
 Exact checked proposition: The following declaration establishes the stated identity, inequality, or equivalence for all quantified real parameters.
 Premises and side conditions: All division, strict positivity, correlation-domain and energy-feasibility assumptions appear explicitly in the declaration; none is inferred from a Gaussian model.
 Proof/definition method: Expand the constant-direction Gram form and collect the d_n coefficient.
 Library reuse: Stdlib.Reals, Stdlib.Field/Ring/Lra/Psatz, SequentialReport.sequential_d and previously proved report identities where appropriate; no new list, matrix or summation recursion.
 Boundary: Kernel-checkable deterministic real algebra about quadratic forms and inverse actions; no construction of Gaussian conditional laws or certified normal integrals.
 *)
Theorem equicorr_common_direction_eigenvalue :
  forall n c x, equicorr_energy c (n*x*x) (n*x) = n*sequential_d n c*x*x.
Proof.
  intros n c x; unfold equicorr_energy, sequential_d; ring.
Qed.

(**
 [equicorr_contrast_direction_eigenvalue] (theorem) — All zero-sum contrast directions have eigenvalue 1-c in the aggregate Gram form.
 Mathematical meaning: All zero-sum contrast directions have eigenvalue 1-c in the aggregate Gram form.
 Exact checked proposition: The following declaration establishes the stated identity, inequality, or equivalence for all quantified real parameters.
 Premises and side conditions: All division, strict positivity, correlation-domain and energy-feasibility assumptions appear explicitly in the declaration; none is inferred from a Gaussian model.
 Proof/definition method: Cancel the rank-one term when the coordinate sum vanishes.
 Library reuse: Stdlib.Reals, Stdlib.Field/Ring/Lra/Psatz, SequentialReport.sequential_d and previously proved report identities where appropriate; no new list, matrix or summation recursion.
 Boundary: Kernel-checkable deterministic real algebra about quadratic forms and inverse actions; no construction of Gaussian conditional laws or certified normal integrals.
 *)
Theorem equicorr_contrast_direction_eigenvalue :
  forall c energy, equicorr_energy c energy 0 = (1-c)*energy.
Proof.
  intros c energy; unfold equicorr_energy; ring.
Qed.

(**
 [equicorr_centered_energy_decomposition] (theorem) — The energy splits into orthogonal contrast and constant-direction contributions with eigenvalues 1-c and d_n.
 Mathematical meaning: The energy splits into orthogonal contrast and constant-direction contributions with eigenvalues 1-c and d_n.
 Exact checked proposition: The following declaration establishes the stated identity, inequality, or equivalence for all quantified real parameters.
 Premises and side conditions: All division, strict positivity, correlation-domain and energy-feasibility assumptions appear explicitly in the declaration; none is inferred from a Gaussian model.
 Proof/definition method: Apply Stdlib.Field to the exact constant/contrast decomposition.
 Library reuse: Stdlib.Reals, Stdlib.Field/Ring/Lra/Psatz, SequentialReport.sequential_d and previously proved report identities where appropriate; no new list, matrix or summation recursion.
 Boundary: Kernel-checkable deterministic real algebra about quadratic forms and inverse actions; no construction of Gaussian conditional laws or certified normal integrals.
 *)
Theorem equicorr_centered_energy_decomposition :
  forall n c energy total, n <> 0 ->
  equicorr_energy c energy total =
  (1-c)*(energy-total*total/n) +
  sequential_d n c*(total*total/n).
Proof.
  intros n c energy total Hn; unfold equicorr_energy, sequential_d; field; exact Hn.
Qed.

(**
 [equicorr_psd_on_feasible_summaries] (theorem) — Both eigenvalues nonnegative imply a nonnegative quadratic form for every energy satisfying the Cauchy feasibility bound.
 Mathematical meaning: Both eigenvalues nonnegative imply a nonnegative quadratic form for every energy satisfying the Cauchy feasibility bound.
 Exact checked proposition: The following declaration establishes the stated identity, inequality, or equivalence for all quantified real parameters.
 Premises and side conditions: All division, strict positivity, correlation-domain and energy-feasibility assumptions appear explicitly in the declaration; none is inferred from a Gaussian model.
 Proof/definition method: Use the checked eigenvalue decomposition and positivity of squared-energy components.
 Library reuse: Stdlib.Reals, Stdlib.Field/Ring/Lra/Psatz, SequentialReport.sequential_d and previously proved report identities where appropriate; no new list, matrix or summation recursion.
 Boundary: Kernel-checkable deterministic real algebra about quadratic forms and inverse actions; no construction of Gaussian conditional laws or certified normal integrals.
 *)
Theorem equicorr_psd_on_feasible_summaries :
  forall n c energy total, 0<n -> c<=1 -> 0<=sequential_d n c ->
  0<=energy-total*total/n -> 0<=equicorr_energy c energy total.
Proof.
  intros n c energy total Hn Hc Hd Hfeas.
  rewrite (equicorr_centered_energy_decomposition n c energy total) by lra.
  assert (Ht : 0 <= total*total/n).
  { unfold Rdiv; apply Rmult_le_pos; [nra | left; apply Rinv_0_lt_compat; lra]. }
  nra.
Qed.

(**
 [equicorr_pd_on_nonzero_feasible_summaries] (theorem) — Strict positivity of both eigenvalues gives positive energy for every nonzero feasible vector summary.
 Mathematical meaning: Strict positivity of both eigenvalues gives positive energy for every nonzero feasible vector summary.
 Exact checked proposition: The following declaration establishes the stated identity, inequality, or equivalence for all quantified real parameters.
 Premises and side conditions: All division, strict positivity, correlation-domain and energy-feasibility assumptions appear explicitly in the declaration; none is inferred from a Gaussian model.
 Proof/definition method: Use strict positive eigenvalues, positive total energy, and nonnegative centered energy.
 Library reuse: Stdlib.Reals, Stdlib.Field/Ring/Lra/Psatz, SequentialReport.sequential_d and previously proved report identities where appropriate; no new list, matrix or summation recursion.
 Boundary: Kernel-checkable deterministic real algebra about quadratic forms and inverse actions; no construction of Gaussian conditional laws or certified normal integrals.
 *)
Theorem equicorr_pd_on_nonzero_feasible_summaries :
  forall n c energy total, 0<n -> c<1 -> 0<sequential_d n c ->
  0<energy -> 0<=energy-total*total/n ->
  0<equicorr_energy c energy total.
Proof.
  intros n c energy total Hn Hc Hd He Hfeas.
  rewrite (equicorr_centered_energy_decomposition n c energy total) by lra.
  assert (Ht : 0 <= total*total/n).
  { unfold Rdiv; apply Rmult_le_pos; [nra | left; apply Rinv_0_lt_compat; lra]. }
  assert (Hcontrast : 0 <= (1-c)*(energy-total*total/n)).
  { apply Rmult_le_pos; lra. }
  assert (Hcommon : 0 <= sequential_d n c*(total*total/n)).
  { apply Rmult_le_pos; lra. }
  destruct (Rlt_dec 0 (energy-total*total/n)) as [Hu | Hu].
  - assert (Hpos : 0 < (1-c)*(energy-total*total/n)).
    { apply Rmult_lt_0_compat; lra. }
    lra.
  - assert (Htot : 0 < total*total/n) by lra.
    assert (Hpos : 0 < sequential_d n c*(total*total/n)).
    { apply Rmult_lt_0_compat; lra. }
    lra.
Qed.

(**
 [equicorr_negative_common_direction_witness] (theorem) — A negative common-direction eigenvalue yields an explicit negative-energy witness of the Gram form.
 Mathematical meaning: A negative common-direction eigenvalue yields an explicit negative-energy witness of the Gram form.
 Exact checked proposition: The following declaration establishes the stated identity, inequality, or equivalence for all quantified real parameters.
 Premises and side conditions: All division, strict positivity, correlation-domain and energy-feasibility assumptions appear explicitly in the declaration; none is inferred from a Gaussian model.
 Proof/definition method: Evaluate the common-mode quadratic form at the vector summary E=S=n.
 Library reuse: Stdlib.Reals, Stdlib.Field/Ring/Lra/Psatz, SequentialReport.sequential_d and previously proved report identities where appropriate; no new list, matrix or summation recursion.
 Boundary: Kernel-checkable deterministic real algebra about quadratic forms and inverse actions; no construction of Gaussian conditional laws or certified normal integrals.
 *)
Theorem equicorr_negative_common_direction_witness :
  forall n c, 0<n -> sequential_d n c<0 ->
  equicorr_energy c n n<0.
Proof.
  intros n c Hn Hd.
  replace (equicorr_energy c n n) with (n*sequential_d n c)
    by (unfold equicorr_energy, sequential_d; ring).
  nra.
Qed.

(**
 [equicorr_negative_contrast_direction_witness] (theorem) — Correlation greater than one yields a negative zero-sum contrast witness.
 Mathematical meaning: Correlation greater than one yields a negative zero-sum contrast witness.
 Exact checked proposition: The following declaration establishes the stated identity, inequality, or equivalence for all quantified real parameters.
 Premises and side conditions: All division, strict positivity, correlation-domain and energy-feasibility assumptions appear explicitly in the declaration; none is inferred from a Gaussian model.
 Proof/definition method: Evaluate the contrast energy at E=1 and S=0.
 Library reuse: Stdlib.Reals, Stdlib.Field/Ring/Lra/Psatz, SequentialReport.sequential_d and previously proved report identities where appropriate; no new list, matrix or summation recursion.
 Boundary: Kernel-checkable deterministic real algebra about quadratic forms and inverse actions; no construction of Gaussian conditional laws or certified normal integrals.
 *)
Theorem equicorr_negative_contrast_direction_witness :
  forall c, 1<c -> equicorr_energy c 1 0<0.
Proof.
  intros c Hc; unfold equicorr_energy; nra.
Qed.

(**
 [equicorr_psd_iff_eigenvalue_conditions] (theorem) — The abstract feasible-energy PSD property is equivalent to nonnegative contrast and common-mode eigenvalues.
 Mathematical meaning: The abstract feasible-energy PSD property is equivalent to nonnegative contrast and common-mode eigenvalues.
 Exact checked proposition: The following declaration establishes the stated identity, inequality, or equivalence for all quantified real parameters.
 Premises and side conditions: All division, strict positivity, correlation-domain and energy-feasibility assumptions appear explicitly in the declaration; none is inferred from a Gaussian model.
 Proof/definition method: Prove necessity by contrast/common-mode witnesses and sufficiency by decomposition.
 Library reuse: Stdlib.Reals, Stdlib.Field/Ring/Lra/Psatz, SequentialReport.sequential_d and previously proved report identities where appropriate; no new list, matrix or summation recursion.
 Boundary: Kernel-checkable deterministic real algebra about quadratic forms and inverse actions; no construction of Gaussian conditional laws or certified normal integrals.
 *)
Theorem equicorr_psd_iff_eigenvalue_conditions :
  forall n c, 0<n ->
  (forall energy total, 0<=energy-total*total/n ->
     0<=equicorr_energy c energy total)
  <-> (c<=1 /\ 0<=sequential_d n c).
Proof.
  intros n c Hn; split.
  - intros H; split.
    + assert (Hf : 0 <= 1-0*0/n) by nra.
      specialize (H 1 0 Hf).
      unfold equicorr_energy in H; nra.
    + assert (Hf : 0 <= n-n*n/n).
      { replace (n*n/n) with n by (field; lra); lra. }
      specialize (H n n Hf).
      replace (equicorr_energy c n n) with (n*sequential_d n c) in H
        by (unfold equicorr_energy, sequential_d; ring).
      nra.
  - intros [Hc Hd] energy total Hf.
    eapply equicorr_psd_on_feasible_summaries; eauto.
Qed.

(**
 [equicorr_pd_iff_strict_eigenvalue_conditions] (theorem) — The abstract feasible-energy positive-definiteness property is equivalent to strictly positive eigenvalues.
 Mathematical meaning: The abstract feasible-energy positive-definiteness property is equivalent to strictly positive eigenvalues.
 Exact checked proposition: The following declaration establishes the stated identity, inequality, or equivalence for all quantified real parameters.
 Premises and side conditions: All division, strict positivity, correlation-domain and energy-feasibility assumptions appear explicitly in the declaration; none is inferred from a Gaussian model.
 Proof/definition method: Use two exact eigenmode witnesses and the strict sum-of-nonnegative-components theorem.
 Library reuse: Stdlib.Reals, Stdlib.Field/Ring/Lra/Psatz, SequentialReport.sequential_d and previously proved report identities where appropriate; no new list, matrix or summation recursion.
 Boundary: Kernel-checkable deterministic real algebra about quadratic forms and inverse actions; no construction of Gaussian conditional laws or certified normal integrals.
 *)
Theorem equicorr_pd_iff_strict_eigenvalue_conditions :
  forall n c, 0<n ->
  (forall energy total, 0<energy -> 0<=energy-total*total/n ->
     0<equicorr_energy c energy total)
  <-> (c<1 /\ 0<sequential_d n c).
Proof.
  intros n c Hn; split.
  - intros H; split.
    + assert (Hf : 0 <= 1-0*0/n) by nra.
      specialize (H 1 0 ltac:(lra) Hf).
      unfold equicorr_energy in H; nra.
    + assert (Hf : 0 <= n-n*n/n).
      { replace (n*n/n) with n by (field; lra); lra. }
      specialize (H n n Hn Hf).
      replace (equicorr_energy c n n) with (n*sequential_d n c) in H
        by (unfold equicorr_energy, sequential_d; ring).
      nra.
  - intros [Hc Hd] energy total He Hf.
    eapply equicorr_pd_on_nonzero_feasible_summaries; eauto.
Qed.

(**
 [equicorr_admissible_interval] (theorem) — For n>1, the common eigenvalue constraint exactly gives the lower equicorrelation bound -1/(n-1).
 Mathematical meaning: For n>1, the common eigenvalue constraint exactly gives the lower equicorrelation bound -1/(n-1).
 Exact checked proposition: The following declaration establishes the stated identity, inequality, or equivalence for all quantified real parameters.
 Premises and side conditions: All division, strict positivity, correlation-domain and energy-feasibility assumptions appear explicitly in the declaration; none is inferred from a Gaussian model.
 Proof/definition method: Clear the positive factor n-1 using exact field identity and nonlinear real arithmetic.
 Library reuse: Stdlib.Reals, Stdlib.Field/Ring/Lra/Psatz, SequentialReport.sequential_d and previously proved report identities where appropriate; no new list, matrix or summation recursion.
 Boundary: Kernel-checkable deterministic real algebra about quadratic forms and inverse actions; no construction of Gaussian conditional laws or certified normal integrals.
 *)
Theorem equicorr_admissible_interval :
  forall n c, 1<n ->
  (c<=1 /\ 0<=sequential_d n c) <->
  (-1/(n-1)<=c /\ c<=1).
Proof.
  intros n c Hn.
  assert (Hnonzero : n-1<>0) by lra.
  assert (Hfactor : (n-1)*(-1/(n-1)) = -1).
  { field; exact Hnonzero. }
  unfold sequential_d; split; intros [Hc Hd]; split; nra.
Qed.

(**
 [equicorr_inverse_left_action] (theorem) — The proposed inverse undoes the rank-one equicorrelation action on each coordinate when the input and output sums agree.
 Mathematical meaning: The proposed inverse undoes the rank-one equicorrelation action on each coordinate when the input and output sums agree.
 Exact checked proposition: The following declaration establishes the stated identity, inequality, or equivalence for all quantified real parameters.
 Premises and side conditions: All division, strict positivity, correlation-domain and energy-feasibility assumptions appear explicitly in the declaration; none is inferred from a Gaussian model.
 Proof/definition method: Apply the two eigen-denominator identities and Field to cancel the inverse action.
 Library reuse: Stdlib.Reals, Stdlib.Field/Ring/Lra/Psatz, SequentialReport.sequential_d and previously proved report identities where appropriate; no new list, matrix or summation recursion.
 Boundary: Kernel-checkable deterministic real algebra about quadratic forms and inverse actions; no construction of Gaussian conditional laws or certified normal integrals.
 *)
Theorem equicorr_inverse_left_action :
  forall n c x total, 1-c<>0 -> sequential_d n c<>0 ->
  equicorr_inverse_entry n c (equicorr_action c x total)
    (sequential_d n c*total) = x.
Proof.
  intros n c x total Hc Hd.
  unfold equicorr_inverse_entry, equicorr_action; field; nra.
Qed.

(**
 [equicorr_inverse_right_action] (theorem) — Applying the rank-one action to the explicit inverse coordinate recovers each original coordinate.
 Mathematical meaning: Applying the rank-one action to the explicit inverse coordinate recovers each original coordinate.
 Exact checked proposition: The following declaration establishes the stated identity, inequality, or equivalence for all quantified real parameters.
 Premises and side conditions: All division, strict positivity, correlation-domain and energy-feasibility assumptions appear explicitly in the declaration; none is inferred from a Gaussian model.
 Proof/definition method: Check the other inverse identity by field cancellation with nonzero eigenvalues.
 Library reuse: Stdlib.Reals, Stdlib.Field/Ring/Lra/Psatz, SequentialReport.sequential_d and previously proved report identities where appropriate; no new list, matrix or summation recursion.
 Boundary: Kernel-checkable deterministic real algebra about quadratic forms and inverse actions; no construction of Gaussian conditional laws or certified normal integrals.
 *)
Theorem equicorr_inverse_right_action :
  forall n c y total, 1-c<>0 -> sequential_d n c<>0 ->
  equicorr_action c (equicorr_inverse_entry n c y total)
    (total/sequential_d n c) = y.
Proof.
  intros n c y total Hc Hd.
  unfold equicorr_action, equicorr_inverse_entry, sequential_d in *; field; nra.
Qed.

(**
 [equicorr_inverse_total_identity] (theorem) — Summing the inverse-coordinate formula symbolically recovers total/d_n, the correct inverse output sum.
 Mathematical meaning: Summing the inverse-coordinate formula symbolically recovers total/d_n, the correct inverse output sum.
 Exact checked proposition: The following declaration establishes the stated identity, inequality, or equivalence for all quantified real parameters.
 Premises and side conditions: All division, strict positivity, correlation-domain and energy-feasibility assumptions appear explicitly in the declaration; none is inferred from a Gaussian model.
 Proof/definition method: Use the identity d_n-n*c=1-c to check inverse sum preservation.
 Library reuse: Stdlib.Reals, Stdlib.Field/Ring/Lra/Psatz, SequentialReport.sequential_d and previously proved report identities where appropriate; no new list, matrix or summation recursion.
 Boundary: Kernel-checkable deterministic real algebra about quadratic forms and inverse actions; no construction of Gaussian conditional laws or certified normal integrals.
 *)
Theorem equicorr_inverse_total_identity :
  forall n c total, 1-c<>0 -> sequential_d n c<>0 ->
  (total-n*c*total/sequential_d n c)/(1-c) =
  total/sequential_d n c.
Proof.
  intros n c total Hc Hd; unfold sequential_d in *; field; nra.
Qed.

(**
 [equicorr_inverse_additive] (theorem) — The equicorrelation inverse acts linearly on pairs of coordinates and their totals.
 Mathematical meaning: The equicorrelation inverse acts linearly on pairs of coordinates and their totals.
 Exact checked proposition: The following declaration establishes the stated identity, inequality, or equivalence for all quantified real parameters.
 Premises and side conditions: All division, strict positivity, correlation-domain and energy-feasibility assumptions appear explicitly in the declaration; none is inferred from a Gaussian model.
 Proof/definition method: Distribute the same two inverse eigen-denominators across coordinate and total sums.
 Library reuse: Stdlib.Reals, Stdlib.Field/Ring/Lra/Psatz, SequentialReport.sequential_d and previously proved report identities where appropriate; no new list, matrix or summation recursion.
 Boundary: Kernel-checkable deterministic real algebra about quadratic forms and inverse actions; no construction of Gaussian conditional laws or certified normal integrals.
 *)
Theorem equicorr_inverse_additive :
  forall n c y1 y2 total1 total2, 1-c<>0 -> sequential_d n c<>0 ->
  equicorr_inverse_entry n c (y1+y2) (total1+total2) =
  equicorr_inverse_entry n c y1 total1 +
  equicorr_inverse_entry n c y2 total2.
Proof.
  intros n c y1 y2 total1 total2 Hc Hd.
  unfold equicorr_inverse_entry; field; nra.
Qed.

(**
 [equicorr_inverse_homogeneous] (theorem) — The equicorrelation inverse commutes with scaling of the input vector and its sum.
 Mathematical meaning: The equicorrelation inverse commutes with scaling of the input vector and its sum.
 Exact checked proposition: The following declaration establishes the stated identity, inequality, or equivalence for all quantified real parameters.
 Premises and side conditions: All division, strict positivity, correlation-domain and energy-feasibility assumptions appear explicitly in the declaration; none is inferred from a Gaussian model.
 Proof/definition method: Use bilinearity and field normalization instead of a bespoke linear-map library.
 Library reuse: Stdlib.Reals, Stdlib.Field/Ring/Lra/Psatz, SequentialReport.sequential_d and previously proved report identities where appropriate; no new list, matrix or summation recursion.
 Boundary: Kernel-checkable deterministic real algebra about quadratic forms and inverse actions; no construction of Gaussian conditional laws or certified normal integrals.
 *)
Theorem equicorr_inverse_homogeneous :
  forall n c a y total, 1-c<>0 -> sequential_d n c<>0 ->
  equicorr_inverse_entry n c (a*y) (a*total) =
  a*equicorr_inverse_entry n c y total.
Proof.
  intros n c a y total Hc Hd;
  unfold equicorr_inverse_entry; field; nra.
Qed.

(**
 [equicorr_inverse_contrast_direction] (theorem) — For a zero-sum vector the inverse is pure contrast scaling by 1/(1-c).
 Mathematical meaning: For a zero-sum vector the inverse is pure contrast scaling by 1/(1-c).
 Exact checked proposition: The following declaration establishes the stated identity, inequality, or equivalence for all quantified real parameters.
 Premises and side conditions: All division, strict positivity, correlation-domain and energy-feasibility assumptions appear explicitly in the declaration; none is inferred from a Gaussian model.
 Proof/definition method: Set the input total to zero and cancel the absent rank-one inverse component.
 Library reuse: Stdlib.Reals, Stdlib.Field/Ring/Lra/Psatz, SequentialReport.sequential_d and previously proved report identities where appropriate; no new list, matrix or summation recursion.
 Boundary: Kernel-checkable deterministic real algebra about quadratic forms and inverse actions; no construction of Gaussian conditional laws or certified normal integrals.
 *)
Theorem equicorr_inverse_contrast_direction :
  forall n c y, 1-c<>0 ->
  equicorr_inverse_entry n c y 0 = y/(1-c).
Proof.
  intros n c y Hc; unfold equicorr_inverse_entry; field; nra.
Qed.

(**
 [equicorr_schur_diagonal_contrast_gap] (theorem) — Conditioning preserves the contrast eigenvalue 1-c; diagonal minus cross-residual covariance is unchanged.
 Mathematical meaning: Conditioning preserves the contrast eigenvalue 1-c; diagonal minus cross-residual covariance is unchanged.
 Exact checked proposition: The following declaration establishes the stated identity, inequality, or equivalence for all quantified real parameters.
 Premises and side conditions: All division, strict positivity, correlation-domain and energy-feasibility assumptions appear explicitly in the declaration; none is inferred from a Gaussian model.
 Proof/definition method: Cancel the same Schur rank-one correction in diagonal and off-diagonal entries.
 Library reuse: Stdlib.Reals, Stdlib.Field/Ring/Lra/Psatz, SequentialReport.sequential_d and previously proved report identities where appropriate; no new list, matrix or summation recursion.
 Boundary: Kernel-checkable deterministic real algebra about quadratic forms and inverse actions; no construction of Gaussian conditional laws or certified normal integrals.
 *)
Theorem equicorr_schur_diagonal_contrast_gap :
  forall r c, equicorr_schur_diagonal r c -
  equicorr_schur_cross r c = 1-c.
Proof.
  intros r c; unfold equicorr_schur_diagonal, equicorr_schur_cross; ring.
Qed.

(**
 [equicorr_schur_energy_factorization] (theorem) — The Schur quadratic form factors into contrast energy and the exact c(1-c)/d_r common-mode correction.
 Mathematical meaning: The Schur quadratic form factors into contrast energy and the exact c(1-c)/d_r common-mode correction.
 Exact checked proposition: The following declaration establishes the stated identity, inequality, or equivalence for all quantified real parameters.
 Premises and side conditions: All division, strict positivity, correlation-domain and energy-feasibility assumptions appear explicitly in the declaration; none is inferred from a Gaussian model.
 Proof/definition method: Reuse both previously proved residual-covariance simplification and contrast gap.
 Library reuse: Stdlib.Reals, Stdlib.Field/Ring/Lra/Psatz, SequentialReport.sequential_d and previously proved report identities where appropriate; no new list, matrix or summation recursion.
 Boundary: Kernel-checkable deterministic real algebra about quadratic forms and inverse actions; no construction of Gaussian conditional laws or certified normal integrals.
 *)
Theorem equicorr_schur_energy_factorization :
  forall r c energy total, sequential_d r c<>0 ->
  equicorr_schur_energy r c energy total =
  (1-c)*energy + c*(1-c)/sequential_d r c*total*total.
Proof.
  intros r c energy total Hd.
  unfold equicorr_schur_energy.
  rewrite equicorr_schur_diagonal_contrast_gap.
  unfold equicorr_schur_cross.
  rewrite sequential_residual_covariance_identity by exact Hd.
  ring.
Qed.

(**
 [equicorr_schur_psd_nonnegative_correlation] (theorem) — Every Schur energy is nonnegative for 0<=c<=1, at least one initial score, and nonnegative squared-energy data.
 Mathematical meaning: Every Schur energy is nonnegative for 0<=c<=1, at least one initial score, and nonnegative squared-energy data.
 Exact checked proposition: The following declaration establishes the stated identity, inequality, or equivalence for all quantified real parameters.
 Premises and side conditions: All division, strict positivity, correlation-domain and energy-feasibility assumptions appear explicitly in the declaration; none is inferred from a Gaussian model.
 Proof/definition method: Apply the shared denominator positivity theorem and factorization to show Schur PSD.
 Library reuse: Stdlib.Reals, Stdlib.Field/Ring/Lra/Psatz, SequentialReport.sequential_d and previously proved report identities where appropriate; no new list, matrix or summation recursion.
 Boundary: Kernel-checkable deterministic real algebra about quadratic forms and inverse actions; no construction of Gaussian conditional laws or certified normal integrals.
 *)
Theorem equicorr_schur_psd_nonnegative_correlation :
  forall r c energy total, 1<=r -> 0<=c -> c<=1 -> 0<=energy ->
  0<=equicorr_schur_energy r c energy total.
Proof.
  intros r c energy total Hr Hc Hu He.
  assert (Hd : 0<sequential_d r c).
  { apply sequential_denominator_positive_nonnegative_correlation; assumption. }
  rewrite equicorr_schur_energy_factorization by lra.
  assert (Hcoef : 0<=c*(1-c)/sequential_d r c).
  { unfold Rdiv; apply Rmult_le_pos; [nra | left; apply Rinv_0_lt_compat; lra]. }
  nra.
Qed.

(**
 [equicorr_schur_pd_nonnegative_correlation] (theorem) — If 0<=c<1 and squared energy is positive, the Schur quadratic form is strictly positive.
 Mathematical meaning: If 0<=c<1 and squared energy is positive, the Schur quadratic form is strictly positive.
 Exact checked proposition: The following declaration establishes the stated identity, inequality, or equivalence for all quantified real parameters.
 Premises and side conditions: All division, strict positivity, correlation-domain and energy-feasibility assumptions appear explicitly in the declaration; none is inferred from a Gaussian model.
 Proof/definition method: Derive strict residual energy from the positive contrast term and the nonnegative rank-one term.
 Library reuse: Stdlib.Reals, Stdlib.Field/Ring/Lra/Psatz, SequentialReport.sequential_d and previously proved report identities where appropriate; no new list, matrix or summation recursion.
 Boundary: Kernel-checkable deterministic real algebra about quadratic forms and inverse actions; no construction of Gaussian conditional laws or certified normal integrals.
 *)
Theorem equicorr_schur_pd_nonnegative_correlation :
  forall r c energy total, 1<=r -> 0<=c -> c<1 -> 0<energy ->
  0<equicorr_schur_energy r c energy total.
Proof.
  intros r c energy total Hr Hc Hu He.
  assert (Hd : 0<sequential_d r c).
  { apply sequential_denominator_positive_nonnegative_correlation; assumption. }
  rewrite equicorr_schur_energy_factorization by lra.
  assert (Hcoef : 0<=c*(1-c)/sequential_d r c).
  { unfold Rdiv; apply Rmult_le_pos; [nra | left; apply Rinv_0_lt_compat; lra]. }
  nra.
Qed.

(**
 [equicorr_schur_common_mode_formula] (theorem) — For k identical future coordinates, Schur energy is k(1-c)d_(r+k)/d_r times their squared common score.
 Mathematical meaning: For k identical future coordinates, Schur energy is k(1-c)d_(r+k)/d_r times their squared common score.
 Exact checked proposition: The following declaration establishes the stated identity, inequality, or equivalence for all quantified real parameters.
 Premises and side conditions: All division, strict positivity, correlation-domain and energy-feasibility assumptions appear explicitly in the declaration; none is inferred from a Gaussian model.
 Proof/definition method: Factor the symmetric future block's common-mode residual eigenvalue exactly.
 Library reuse: Stdlib.Reals, Stdlib.Field/Ring/Lra/Psatz, SequentialReport.sequential_d and previously proved report identities where appropriate; no new list, matrix or summation recursion.
 Boundary: Kernel-checkable deterministic real algebra about quadratic forms and inverse actions; no construction of Gaussian conditional laws or certified normal integrals.
 *)
Theorem equicorr_schur_common_mode_formula :
  forall r k c x, sequential_d r c<>0 ->
  equicorr_schur_energy r c (k*x*x) (k*x) =
  k*(1-c)*sequential_d (r+k) c/sequential_d r c*x*x.
Proof.
  intros r k c x Hd.
  rewrite equicorr_schur_energy_factorization by exact Hd.
  unfold sequential_d in *; field; nra.
Qed.

(**
 [equicorr_schur_contrast_formula] (theorem) — After conditioning, any zero-sum future contrast retains energy coefficient 1-c.
 Mathematical meaning: After conditioning, any zero-sum future contrast retains energy coefficient 1-c.
 Exact checked proposition: The following declaration establishes the stated identity, inequality, or equivalence for all quantified real parameters.
 Premises and side conditions: All division, strict positivity, correlation-domain and energy-feasibility assumptions appear explicitly in the declaration; none is inferred from a Gaussian model.
 Proof/definition method: Use the factored residual Gram form and cancel the total-sum term.
 Library reuse: Stdlib.Reals, Stdlib.Field/Ring/Lra/Psatz, SequentialReport.sequential_d and previously proved report identities where appropriate; no new list, matrix or summation recursion.
 Boundary: Kernel-checkable deterministic real algebra about quadratic forms and inverse actions; no construction of Gaussian conditional laws or certified normal integrals.
 *)
Theorem equicorr_schur_contrast_formula :
  forall r c energy, sequential_d r c<>0 ->
  equicorr_schur_energy r c energy 0 = (1-c)*energy.
Proof.
  intros r c energy Hd.
  rewrite equicorr_schur_energy_factorization by exact Hd; ring.
Qed.

(**
 [equicorr_schur_variance_reduction] (theorem) — For nonnegative correlation, conditioning reduces the unconditioned diagonal variance by a nonnegative r*c²/d_r term.
 Mathematical meaning: For nonnegative correlation, conditioning reduces the unconditioned diagonal variance by a nonnegative r*c²/d_r term.
 Exact checked proposition: The following declaration establishes the stated identity, inequality, or equivalence for all quantified real parameters.
 Premises and side conditions: All division, strict positivity, correlation-domain and energy-feasibility assumptions appear explicitly in the declaration; none is inferred from a Gaussian model.
 Proof/definition method: Show conditioning cannot increase a diagonal variance when the Schur correction is nonnegative.
 Library reuse: Stdlib.Reals, Stdlib.Field/Ring/Lra/Psatz, SequentialReport.sequential_d and previously proved report identities where appropriate; no new list, matrix or summation recursion.
 Boundary: Kernel-checkable deterministic real algebra about quadratic forms and inverse actions; no construction of Gaussian conditional laws or certified normal integrals.
 *)
Theorem equicorr_schur_variance_reduction :
  forall r c, 1<=r -> 0<=c ->
  0<=1-equicorr_schur_diagonal r c.
Proof.
  intros r c Hr Hc.
  assert (Hd : 0<sequential_d r c).
  { apply sequential_denominator_positive_nonnegative_correlation; assumption. }
  unfold equicorr_schur_diagonal.
  assert (Hcorr : 0<=r*c*c/sequential_d r c).
  { unfold Rdiv; apply Rmult_le_pos; [nra | left; apply Rinv_0_lt_compat; lra]. }
  lra.
Qed.

