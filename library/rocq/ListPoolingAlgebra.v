(** Module: ListPoolingAlgebra.v
 Purpose: Establish exact, arbitrary-list weighted sample pooling and centered
 sums of squares for the six Hoeflin/Ferguson, Towers and Sequential reports.
 Mathematical representation: Reuse FiniteSum.finite_sum over a list of
 arbitrary group identifiers and functions for group mass and group mean.
 Explicit hypotheses: Nonnegative weights, positive total mass and nonzero
 denominators are stated in the precise propositions needing them.
 Library use: Stdlib Reals, List, Sorting.Permutation, Lra, Psatz, Ring,
 Field and the shared canonical FiniteSum and PooledMomentsAlgebra modules.
 Limitations: The statements are deterministic weighted-moment identities;
 they do not imply independent sampling, Gaussian/chi-square laws,
 Monte Carlo accuracy or finite-sample coverage probabilities.
 Reproduction: Canonical scripts/compile_rocq.sh; Rocq Prover 9.2 CI.
 AI disclosure: Proof design, source comments and refactoring were
 assisted by OpenAI ChatGPT. Kernel compilation is the proof criterion.
*)
From Stdlib Require Import Reals Lra Psatz Ring Field List Sorting.Permutation.
Require Import FiniteSum PooledMomentsAlgebra SamplingPrecision.
Import ListNotations.
Open Scope R_scope.

(** [batch_mass] (definition).
 Mathematical meaning: The weighted number of observations across arbitrary many batches.
 Exact declaration: Definition batch_mass {A:Type} (w:A->R) (xs:list A):R := finite_sum w xs.
 Premises and side conditions: All positivity, membership, and nonzero denominator hypotheses needed by this exact statement are explicit. A group is a deterministic identifier, not an independently generated random sample.
 Proof/definition method: Rewrite into the canonical finite_sum and use its previously certified fold, permutation, linearity and order results, or standard real ring and field tactics.
 Library reuse: Rocq Stdlib Reals/List/Ring/Field/Lra/Psatz and the single shared FiniteSum; no custom recursive summation, new probability axioms, or duplicate sample pooling implementation.
 Boundary: Report G12 arbitrary-list deterministic pooling only. No Gaussian sample distribution, chi-square pivot, binomial independence, statistical confidence coverage, or empirical IQ model is inferred.
*)

Definition batch_mass {A:Type} (w:A->R) (xs:list A):R := finite_sum w xs.

(** [batch_total] (definition).
 Mathematical meaning: The weighted first raw moment (weighted sum of group centers).
 Exact declaration: Definition batch_total {A:Type} (w v:A->R) (xs:list A):R := finite_sum (fun x => w x * v x) xs.
 Premises and side conditions: All positivity, membership, and nonzero denominator hypotheses needed by this exact statement are explicit. A group is a deterministic identifier, not an independently generated random sample.
 Proof/definition method: Rewrite into the canonical finite_sum and use its previously certified fold, permutation, linearity and order results, or standard real ring and field tactics.
 Library reuse: Rocq Stdlib Reals/List/Ring/Field/Lra/Psatz and the single shared FiniteSum; no custom recursive summation, new probability axioms, or duplicate sample pooling implementation.
 Boundary: Report G12 arbitrary-list deterministic pooling only. No Gaussian sample distribution, chi-square pivot, binomial independence, statistical confidence coverage, or empirical IQ model is inferred.
*)

Definition batch_total {A:Type} (w v:A->R) (xs:list A):R := finite_sum (fun x => w x * v x) xs.

(** [batch_second] (definition).
 Mathematical meaning: The weighted second raw moment for arbitrary batches.
 Exact declaration: Definition batch_second {A:Type} (w v:A->R) (xs:list A):R := finite_sum (fun x => w x * v x * v x) xs.
 Premises and side conditions: All positivity, membership, and nonzero denominator hypotheses needed by this exact statement are explicit. A group is a deterministic identifier, not an independently generated random sample.
 Proof/definition method: Rewrite into the canonical finite_sum and use its previously certified fold, permutation, linearity and order results, or standard real ring and field tactics.
 Library reuse: Rocq Stdlib Reals/List/Ring/Field/Lra/Psatz and the single shared FiniteSum; no custom recursive summation, new probability axioms, or duplicate sample pooling implementation.
 Boundary: Report G12 arbitrary-list deterministic pooling only. No Gaussian sample distribution, chi-square pivot, binomial independence, statistical confidence coverage, or empirical IQ model is inferred.
*)

Definition batch_second {A:Type} (w v:A->R) (xs:list A):R := finite_sum (fun x => w x * v x * v x) xs.

(** [batch_mean] (definition).
 Mathematical meaning: The total weighted mean (valid as a statistical mean for positive mass).
 Exact declaration: Definition batch_mean {A:Type} (w v:A->R) (xs:list A):R := batch_total w v xs / batch_mass w xs.
 Premises and side conditions: All positivity, membership, and nonzero denominator hypotheses needed by this exact statement are explicit. A group is a deterministic identifier, not an independently generated random sample.
 Proof/definition method: Rewrite into the canonical finite_sum and use its previously certified fold, permutation, linearity and order results, or standard real ring and field tactics.
 Library reuse: Rocq Stdlib Reals/List/Ring/Field/Lra/Psatz and the single shared FiniteSum; no custom recursive summation, new probability axioms, or duplicate sample pooling implementation.
 Boundary: Report G12 arbitrary-list deterministic pooling only. No Gaussian sample distribution, chi-square pivot, binomial independence, statistical confidence coverage, or empirical IQ model is inferred.
*)

Definition batch_mean {A:Type} (w v:A->R) (xs:list A):R := batch_total w v xs / batch_mass w xs.

(** [batch_centered] (definition).
 Mathematical meaning: Between-group corrected sum of squares about an arbitrary reference center.
 Exact declaration: Definition batch_centered {A:Type} (w v:A->R) (c:R) (xs:list A):R := finite_sum (fun x => w x * (v x - c) * (v x - c)) xs.
 Premises and side conditions: All positivity, membership, and nonzero denominator hypotheses needed by this exact statement are explicit. A group is a deterministic identifier, not an independently generated random sample.
 Proof/definition method: Rewrite into the canonical finite_sum and use its previously certified fold, permutation, linearity and order results, or standard real ring and field tactics.
 Library reuse: Rocq Stdlib Reals/List/Ring/Field/Lra/Psatz and the single shared FiniteSum; no custom recursive summation, new probability axioms, or duplicate sample pooling implementation.
 Boundary: Report G12 arbitrary-list deterministic pooling only. No Gaussian sample distribution, chi-square pivot, binomial independence, statistical confidence coverage, or empirical IQ model is inferred.
*)

Definition batch_centered {A:Type} (w v:A->R) (c:R) (xs:list A):R := finite_sum (fun x => w x * (v x - c) * (v x - c)) xs.

(** [batch_total_ss] (definition).
 Mathematical meaning: Total corrected sum of squares with supplied within-group residual sums.
 Exact declaration: Definition batch_total_ss {A:Type} (w v u:A->R) (xs:list A):R := finite_sum u xs + batch_centered w v (batch_mean w v xs) xs.
 Premises and side conditions: All positivity, membership, and nonzero denominator hypotheses needed by this exact statement are explicit. A group is a deterministic identifier, not an independently generated random sample.
 Proof/definition method: Rewrite into the canonical finite_sum and use its previously certified fold, permutation, linearity and order results, or standard real ring and field tactics.
 Library reuse: Rocq Stdlib Reals/List/Ring/Field/Lra/Psatz and the single shared FiniteSum; no custom recursive summation, new probability axioms, or duplicate sample pooling implementation.
 Boundary: Report G12 arbitrary-list deterministic pooling only. No Gaussian sample distribution, chi-square pivot, binomial independence, statistical confidence coverage, or empirical IQ model is inferred.
*)

Definition batch_total_ss {A:Type} (w v u:A->R) (xs:list A):R := finite_sum u xs + batch_centered w v (batch_mean w v xs) xs.
(** [batch_mass_app] (theorem).
 Mathematical meaning: Additivity of pooled exposure across any two list partitions.
 Exact proposition: forall (A:Type) (w:A->R) (xs ys:list A), batch_mass w (xs++ys)=batch_mass w xs+batch_mass w ys.
 Premises and side conditions: All positivity, membership, and nonzero denominator hypotheses needed by this exact statement are explicit. A group is a deterministic identifier, not an independently generated random sample.
 Proof/definition method: Rewrite into the canonical finite_sum and use its previously certified fold, permutation, linearity and order results, or standard real ring and field tactics.
 Library reuse: Rocq Stdlib Reals/List/Ring/Field/Lra/Psatz and the single shared FiniteSum; no custom recursive summation, new probability axioms, or duplicate sample pooling implementation.
 Boundary: Report G12 arbitrary-list deterministic pooling only. No Gaussian sample distribution, chi-square pivot, binomial independence, statistical confidence coverage, or empirical IQ model is inferred.
*)
Theorem batch_mass_app :
  forall (A:Type) (w:A->R) (xs ys:list A), batch_mass w (xs++ys)=batch_mass w xs+batch_mass w ys.
Proof.
  intros A w xs ys; unfold batch_mass; apply finite_sum_app.
Qed.

(** [batch_total_app] (theorem).
 Mathematical meaning: Additivity of the weighted first moment across partitions.
 Exact proposition: forall (A:Type) (w v:A->R) (xs ys:list A), batch_total w v (xs++ys)=batch_total w v xs+batch_total w v ys.
 Premises and side conditions: All positivity, membership, and nonzero denominator hypotheses needed by this exact statement are explicit. A group is a deterministic identifier, not an independently generated random sample.
 Proof/definition method: Rewrite into the canonical finite_sum and use its previously certified fold, permutation, linearity and order results, or standard real ring and field tactics.
 Library reuse: Rocq Stdlib Reals/List/Ring/Field/Lra/Psatz and the single shared FiniteSum; no custom recursive summation, new probability axioms, or duplicate sample pooling implementation.
 Boundary: Report G12 arbitrary-list deterministic pooling only. No Gaussian sample distribution, chi-square pivot, binomial independence, statistical confidence coverage, or empirical IQ model is inferred.
*)
Theorem batch_total_app :
  forall (A:Type) (w v:A->R) (xs ys:list A), batch_total w v (xs++ys)=batch_total w v xs+batch_total w v ys.
Proof.
  intros A w v xs ys; unfold batch_total; apply finite_sum_app.
Qed.

(** [batch_second_app] (theorem).
 Mathematical meaning: Additivity of the weighted second moment across partitions.
 Exact proposition: forall (A:Type) (w v:A->R) (xs ys:list A), batch_second w v (xs++ys)=batch_second w v xs+batch_second w v ys.
 Premises and side conditions: All positivity, membership, and nonzero denominator hypotheses needed by this exact statement are explicit. A group is a deterministic identifier, not an independently generated random sample.
 Proof/definition method: Rewrite into the canonical finite_sum and use its previously certified fold, permutation, linearity and order results, or standard real ring and field tactics.
 Library reuse: Rocq Stdlib Reals/List/Ring/Field/Lra/Psatz and the single shared FiniteSum; no custom recursive summation, new probability axioms, or duplicate sample pooling implementation.
 Boundary: Report G12 arbitrary-list deterministic pooling only. No Gaussian sample distribution, chi-square pivot, binomial independence, statistical confidence coverage, or empirical IQ model is inferred.
*)
Theorem batch_second_app :
  forall (A:Type) (w v:A->R) (xs ys:list A), batch_second w v (xs++ys)=batch_second w v xs+batch_second w v ys.
Proof.
  intros A w v xs ys; unfold batch_second; apply finite_sum_app.
Qed.

(** [batch_centered_app] (theorem).
 Mathematical meaning: The same reference-centered between-group dispersion adds over partitions.
 Exact proposition: forall (A:Type) (w v:A->R) (c:R) (xs ys:list A), batch_centered w v c (xs++ys)=batch_centered w v c xs+batch_centered w v c ys.
 Premises and side conditions: All positivity, membership, and nonzero denominator hypotheses needed by this exact statement are explicit. A group is a deterministic identifier, not an independently generated random sample.
 Proof/definition method: Rewrite into the canonical finite_sum and use its previously certified fold, permutation, linearity and order results, or standard real ring and field tactics.
 Library reuse: Rocq Stdlib Reals/List/Ring/Field/Lra/Psatz and the single shared FiniteSum; no custom recursive summation, new probability axioms, or duplicate sample pooling implementation.
 Boundary: Report G12 arbitrary-list deterministic pooling only. No Gaussian sample distribution, chi-square pivot, binomial independence, statistical confidence coverage, or empirical IQ model is inferred.
*)
Theorem batch_centered_app :
  forall (A:Type) (w v:A->R) (c:R) (xs ys:list A), batch_centered w v c (xs++ys)=batch_centered w v c xs+batch_centered w v c ys.
Proof.
  intros A w v c xs ys; unfold batch_centered; apply finite_sum_app.
Qed.

(** [batch_mass_permutation] (theorem).
 Mathematical meaning: Pooled exposure is invariant under arbitrary batch reordering.
 Exact proposition: forall (A:Type) (w:A->R) (xs ys:list A), Permutation xs ys -> batch_mass w xs=batch_mass w ys.
 Premises and side conditions: All positivity, membership, and nonzero denominator hypotheses needed by this exact statement are explicit. A group is a deterministic identifier, not an independently generated random sample.
 Proof/definition method: Rewrite into the canonical finite_sum and use its previously certified fold, permutation, linearity and order results, or standard real ring and field tactics.
 Library reuse: Rocq Stdlib Reals/List/Ring/Field/Lra/Psatz and the single shared FiniteSum; no custom recursive summation, new probability axioms, or duplicate sample pooling implementation.
 Boundary: Report G12 arbitrary-list deterministic pooling only. No Gaussian sample distribution, chi-square pivot, binomial independence, statistical confidence coverage, or empirical IQ model is inferred.
*)
Theorem batch_mass_permutation :
  forall (A:Type) (w:A->R) (xs ys:list A), Permutation xs ys -> batch_mass w xs=batch_mass w ys.
Proof.
  intros A w xs ys H; unfold batch_mass; now apply finite_sum_permutation.
Qed.

(** [batch_total_permutation] (theorem).
 Mathematical meaning: Weighted first moment is invariant under arbitrary batch reordering.
 Exact proposition: forall (A:Type) (w v:A->R) (xs ys:list A), Permutation xs ys -> batch_total w v xs=batch_total w v ys.
 Premises and side conditions: All positivity, membership, and nonzero denominator hypotheses needed by this exact statement are explicit. A group is a deterministic identifier, not an independently generated random sample.
 Proof/definition method: Rewrite into the canonical finite_sum and use its previously certified fold, permutation, linearity and order results, or standard real ring and field tactics.
 Library reuse: Rocq Stdlib Reals/List/Ring/Field/Lra/Psatz and the single shared FiniteSum; no custom recursive summation, new probability axioms, or duplicate sample pooling implementation.
 Boundary: Report G12 arbitrary-list deterministic pooling only. No Gaussian sample distribution, chi-square pivot, binomial independence, statistical confidence coverage, or empirical IQ model is inferred.
*)
Theorem batch_total_permutation :
  forall (A:Type) (w v:A->R) (xs ys:list A), Permutation xs ys -> batch_total w v xs=batch_total w v ys.
Proof.
  intros A w v xs ys H; unfold batch_total; now apply finite_sum_permutation.
Qed.

(** [batch_second_permutation] (theorem).
 Mathematical meaning: Weighted second moment is invariant under arbitrary batch reordering.
 Exact proposition: forall (A:Type) (w v:A->R) (xs ys:list A), Permutation xs ys -> batch_second w v xs=batch_second w v ys.
 Premises and side conditions: All positivity, membership, and nonzero denominator hypotheses needed by this exact statement are explicit. A group is a deterministic identifier, not an independently generated random sample.
 Proof/definition method: Rewrite into the canonical finite_sum and use its previously certified fold, permutation, linearity and order results, or standard real ring and field tactics.
 Library reuse: Rocq Stdlib Reals/List/Ring/Field/Lra/Psatz and the single shared FiniteSum; no custom recursive summation, new probability axioms, or duplicate sample pooling implementation.
 Boundary: Report G12 arbitrary-list deterministic pooling only. No Gaussian sample distribution, chi-square pivot, binomial independence, statistical confidence coverage, or empirical IQ model is inferred.
*)
Theorem batch_second_permutation :
  forall (A:Type) (w v:A->R) (xs ys:list A), Permutation xs ys -> batch_second w v xs=batch_second w v ys.
Proof.
  intros A w v xs ys H; unfold batch_second; now apply finite_sum_permutation.
Qed.

(** [batch_mean_permutation] (theorem).
 Mathematical meaning: A non-normalized denominator does not break exact permutation invariance of the weighted mean.
 Exact proposition: forall (A:Type) (w v:A->R) (xs ys:list A), Permutation xs ys -> batch_mean w v xs=batch_mean w v ys.
 Premises and side conditions: All positivity, membership, and nonzero denominator hypotheses needed by this exact statement are explicit. A group is a deterministic identifier, not an independently generated random sample.
 Proof/definition method: Rewrite into the canonical finite_sum and use its previously certified fold, permutation, linearity and order results, or standard real ring and field tactics.
 Library reuse: Rocq Stdlib Reals/List/Ring/Field/Lra/Psatz and the single shared FiniteSum; no custom recursive summation, new probability axioms, or duplicate sample pooling implementation.
 Boundary: Report G12 arbitrary-list deterministic pooling only. No Gaussian sample distribution, chi-square pivot, binomial independence, statistical confidence coverage, or empirical IQ model is inferred.
*)
Theorem batch_mean_permutation :
  forall (A:Type) (w v:A->R) (xs ys:list A), Permutation xs ys -> batch_mean w v xs=batch_mean w v ys.
Proof.
  intros A w v xs ys H; unfold batch_mean; now rewrite (batch_total_permutation A w v xs ys H), (batch_mass_permutation A w xs ys H).
Qed.

(** [batch_centered_permutation] (theorem).
 Mathematical meaning: Between-group corrected sums are unaffected by ordering.
 Exact proposition: forall (A:Type) (w v:A->R) (c:R) (xs ys:list A), Permutation xs ys -> batch_centered w v c xs=batch_centered w v c ys.
 Premises and side conditions: All positivity, membership, and nonzero denominator hypotheses needed by this exact statement are explicit. A group is a deterministic identifier, not an independently generated random sample.
 Proof/definition method: Rewrite into the canonical finite_sum and use its previously certified fold, permutation, linearity and order results, or standard real ring and field tactics.
 Library reuse: Rocq Stdlib Reals/List/Ring/Field/Lra/Psatz and the single shared FiniteSum; no custom recursive summation, new probability axioms, or duplicate sample pooling implementation.
 Boundary: Report G12 arbitrary-list deterministic pooling only. No Gaussian sample distribution, chi-square pivot, binomial independence, statistical confidence coverage, or empirical IQ model is inferred.
*)
Theorem batch_centered_permutation :
  forall (A:Type) (w v:A->R) (c:R) (xs ys:list A), Permutation xs ys -> batch_centered w v c xs=batch_centered w v c ys.
Proof.
  intros A w v c xs ys H; unfold batch_centered; now apply finite_sum_permutation.
Qed.

(** [batch_total_ss_permutation] (theorem).
 Mathematical meaning: The complete within/between corrected-sum-of-squares pooling is order invariant.
 Exact proposition: forall (A:Type) (w v u:A->R) (xs ys:list A), Permutation xs ys -> batch_total_ss w v u xs=batch_total_ss w v u ys.
 Premises and side conditions: All positivity, membership, and nonzero denominator hypotheses needed by this exact statement are explicit. A group is a deterministic identifier, not an independently generated random sample.
 Proof/definition method: Rewrite into the canonical finite_sum and use its previously certified fold, permutation, linearity and order results, or standard real ring and field tactics.
 Library reuse: Rocq Stdlib Reals/List/Ring/Field/Lra/Psatz and the single shared FiniteSum; no custom recursive summation, new probability axioms, or duplicate sample pooling implementation.
 Boundary: Report G12 arbitrary-list deterministic pooling only. No Gaussian sample distribution, chi-square pivot, binomial independence, statistical confidence coverage, or empirical IQ model is inferred.
*)
Theorem batch_total_ss_permutation :
  forall (A:Type) (w v u:A->R) (xs ys:list A), Permutation xs ys -> batch_total_ss w v u xs=batch_total_ss w v u ys.
Proof.
  intros A w v u xs ys H; unfold batch_total_ss; rewrite (finite_sum_permutation xs ys u H), (batch_mean_permutation A w v xs ys H); now rewrite (batch_centered_permutation A w v (batch_mean w v ys) xs ys H).
Qed.

(** [batch_mass_nonnegative] (theorem).
 Mathematical meaning: Nonnegative batch weights have nonnegative aggregate exposure.
 Exact proposition: forall (A:Type) (w:A->R) (xs:list A), (forall x, In x xs -> 0<=w x) -> 0<=batch_mass w xs.
 Premises and side conditions: All positivity, membership, and nonzero denominator hypotheses needed by this exact statement are explicit. A group is a deterministic identifier, not an independently generated random sample.
 Proof/definition method: Rewrite into the canonical finite_sum and use its previously certified fold, permutation, linearity and order results, or standard real ring and field tactics.
 Library reuse: Rocq Stdlib Reals/List/Ring/Field/Lra/Psatz and the single shared FiniteSum; no custom recursive summation, new probability axioms, or duplicate sample pooling implementation.
 Boundary: Report G12 arbitrary-list deterministic pooling only. No Gaussian sample distribution, chi-square pivot, binomial independence, statistical confidence coverage, or empirical IQ model is inferred.
*)
Theorem batch_mass_nonnegative :
  forall (A:Type) (w:A->R) (xs:list A), (forall x, In x xs -> 0<=w x) -> 0<=batch_mass w xs.
Proof.
  intros A w xs Hw; unfold batch_mass; now apply finite_sum_nonnegative.
Qed.

(** [batch_mass_positive_member] (theorem).
 Mathematical meaning: A positive member weight and nonnegative others yield strictly positive total exposure.
 Exact proposition: forall (A:Type) (w:A->R) (xs:list A) (x:A), (forall y, In y xs -> 0<=w y) -> In x xs -> 0<w x -> 0<batch_mass w xs.
 Premises and side conditions: All positivity, membership, and nonzero denominator hypotheses needed by this exact statement are explicit. A group is a deterministic identifier, not an independently generated random sample.
 Proof/definition method: Rewrite into the canonical finite_sum and use its previously certified fold, permutation, linearity and order results, or standard real ring and field tactics.
 Library reuse: Rocq Stdlib Reals/List/Ring/Field/Lra/Psatz and the single shared FiniteSum; no custom recursive summation, new probability axioms, or duplicate sample pooling implementation.
 Boundary: Report G12 arbitrary-list deterministic pooling only. No Gaussian sample distribution, chi-square pivot, binomial independence, statistical confidence coverage, or empirical IQ model is inferred.
*)
Theorem batch_mass_positive_member :
  forall (A:Type) (w:A->R) (xs:list A) (x:A), (forall y, In y xs -> 0<=w y) -> In x xs -> 0<w x -> 0<batch_mass w xs.
Proof.
  intros A w xs x Hnon Hin Hp; unfold batch_mass; now apply (finite_sum_positive_of_positive_member xs w x Hnon Hin Hp).
Qed.

(** [batch_total_add_values] (theorem).
 Mathematical meaning: The weighted first moment is additive in the observed group means.
 Exact proposition: forall (A:Type) (w v z:A->R) (xs:list A), batch_total w (fun x => v x+z x) xs = batch_total w v xs+batch_total w z xs.
 Premises and side conditions: All positivity, membership, and nonzero denominator hypotheses needed by this exact statement are explicit. A group is a deterministic identifier, not an independently generated random sample.
 Proof/definition method: Rewrite into the canonical finite_sum and use its previously certified fold, permutation, linearity and order results, or standard real ring and field tactics.
 Library reuse: Rocq Stdlib Reals/List/Ring/Field/Lra/Psatz and the single shared FiniteSum; no custom recursive summation, new probability axioms, or duplicate sample pooling implementation.
 Boundary: Report G12 arbitrary-list deterministic pooling only. No Gaussian sample distribution, chi-square pivot, binomial independence, statistical confidence coverage, or empirical IQ model is inferred.
*)
Theorem batch_total_add_values :
  forall (A:Type) (w v z:A->R) (xs:list A), batch_total w (fun x => v x+z x) xs = batch_total w v xs+batch_total w z xs.
Proof.
  intros A w v z xs; unfold batch_total; transitivity (finite_sum (fun x => w x*v x+w x*z x) xs); [apply finite_sum_ext; intro x; ring|rewrite finite_sum_add; reflexivity].
Qed.

(** [batch_total_scale_values] (theorem).
 Mathematical meaning: Scaling all reported group means scales the weighted first moment.
 Exact proposition: forall (A:Type) (w v:A->R) (xs:list A) (t:R), batch_total w (fun x => t*v x) xs=t*batch_total w v xs.
 Premises and side conditions: All positivity, membership, and nonzero denominator hypotheses needed by this exact statement are explicit. A group is a deterministic identifier, not an independently generated random sample.
 Proof/definition method: Rewrite into the canonical finite_sum and use its previously certified fold, permutation, linearity and order results, or standard real ring and field tactics.
 Library reuse: Rocq Stdlib Reals/List/Ring/Field/Lra/Psatz and the single shared FiniteSum; no custom recursive summation, new probability axioms, or duplicate sample pooling implementation.
 Boundary: Report G12 arbitrary-list deterministic pooling only. No Gaussian sample distribution, chi-square pivot, binomial independence, statistical confidence coverage, or empirical IQ model is inferred.
*)
Theorem batch_total_scale_values :
  forall (A:Type) (w v:A->R) (xs:list A) (t:R), batch_total w (fun x => t*v x) xs=t*batch_total w v xs.
Proof.
  intros A w v xs t; unfold batch_total; transitivity (finite_sum (fun x => t*(w x*v x)) xs); [apply finite_sum_ext; intro x; ring|rewrite finite_sum_scale; reflexivity].
Qed.

(** [batch_total_scale_weights] (theorem).
 Mathematical meaning: Rescaling every sample weight scales the first raw moment.
 Exact proposition: forall (A:Type) (w v:A->R) (xs:list A) (t:R), batch_total (fun x => t*w x) v xs=t*batch_total w v xs.
 Premises and side conditions: All positivity, membership, and nonzero denominator hypotheses needed by this exact statement are explicit. A group is a deterministic identifier, not an independently generated random sample.
 Proof/definition method: Rewrite into the canonical finite_sum and use its previously certified fold, permutation, linearity and order results, or standard real ring and field tactics.
 Library reuse: Rocq Stdlib Reals/List/Ring/Field/Lra/Psatz and the single shared FiniteSum; no custom recursive summation, new probability axioms, or duplicate sample pooling implementation.
 Boundary: Report G12 arbitrary-list deterministic pooling only. No Gaussian sample distribution, chi-square pivot, binomial independence, statistical confidence coverage, or empirical IQ model is inferred.
*)
Theorem batch_total_scale_weights :
  forall (A:Type) (w v:A->R) (xs:list A) (t:R), batch_total (fun x => t*w x) v xs=t*batch_total w v xs.
Proof.
  intros A w v xs t; unfold batch_total; transitivity (finite_sum (fun x => t*(w x*v x)) xs); [apply finite_sum_ext; intro x; ring|rewrite finite_sum_scale; reflexivity].
Qed.

(** [batch_mass_scale_weights] (theorem).
 Mathematical meaning: A uniform rescaling of group size scales total exposure.
 Exact proposition: forall (A:Type) (w:A->R) (xs:list A) (t:R), batch_mass (fun x => t*w x) xs=t*batch_mass w xs.
 Premises and side conditions: All positivity, membership, and nonzero denominator hypotheses needed by this exact statement are explicit. A group is a deterministic identifier, not an independently generated random sample.
 Proof/definition method: Rewrite into the canonical finite_sum and use its previously certified fold, permutation, linearity and order results, or standard real ring and field tactics.
 Library reuse: Rocq Stdlib Reals/List/Ring/Field/Lra/Psatz and the single shared FiniteSum; no custom recursive summation, new probability axioms, or duplicate sample pooling implementation.
 Boundary: Report G12 arbitrary-list deterministic pooling only. No Gaussian sample distribution, chi-square pivot, binomial independence, statistical confidence coverage, or empirical IQ model is inferred.
*)
Theorem batch_mass_scale_weights :
  forall (A:Type) (w:A->R) (xs:list A) (t:R), batch_mass (fun x => t*w x) xs=t*batch_mass w xs.
Proof.
  intros A w xs t; unfold batch_mass; apply finite_sum_scale.
Qed.

(** [batch_total_translate_values] (theorem).
 Mathematical meaning: A common score shift changes the weighted sum by shift times total exposure.
 Exact proposition: forall (A:Type) (w v:A->R) (xs:list A) (c:R), batch_total w (fun x => v x+c) xs = batch_total w v xs+c*batch_mass w xs.
 Premises and side conditions: All positivity, membership, and nonzero denominator hypotheses needed by this exact statement are explicit. A group is a deterministic identifier, not an independently generated random sample.
 Proof/definition method: Rewrite into the canonical finite_sum and use its previously certified fold, permutation, linearity and order results, or standard real ring and field tactics.
 Library reuse: Rocq Stdlib Reals/List/Ring/Field/Lra/Psatz and the single shared FiniteSum; no custom recursive summation, new probability axioms, or duplicate sample pooling implementation.
 Boundary: Report G12 arbitrary-list deterministic pooling only. No Gaussian sample distribution, chi-square pivot, binomial independence, statistical confidence coverage, or empirical IQ model is inferred.
*)
Theorem batch_total_translate_values :
  forall (A:Type) (w v:A->R) (xs:list A) (c:R), batch_total w (fun x => v x+c) xs = batch_total w v xs+c*batch_mass w xs.
Proof.
  intros A w v xs c; unfold batch_total,batch_mass; transitivity (finite_sum (fun x => w x*v x+c*w x) xs); [apply finite_sum_ext; intro x; ring|rewrite finite_sum_add, finite_sum_scale; ring].
Qed.

(** [batch_second_nonnegative] (theorem).
 Mathematical meaning: Nonnegative sample weights give a nonnegative second raw moment.
 Exact proposition: forall (A:Type) (w v:A->R) (xs:list A), (forall x, In x xs -> 0<=w x) -> 0<=batch_second w v xs.
 Premises and side conditions: All positivity, membership, and nonzero denominator hypotheses needed by this exact statement are explicit. A group is a deterministic identifier, not an independently generated random sample.
 Proof/definition method: Rewrite into the canonical finite_sum and use its previously certified fold, permutation, linearity and order results, or standard real ring and field tactics.
 Library reuse: Rocq Stdlib Reals/List/Ring/Field/Lra/Psatz and the single shared FiniteSum; no custom recursive summation, new probability axioms, or duplicate sample pooling implementation.
 Boundary: Report G12 arbitrary-list deterministic pooling only. No Gaussian sample distribution, chi-square pivot, binomial independence, statistical confidence coverage, or empirical IQ model is inferred.
*)
Theorem batch_second_nonnegative :
  forall (A:Type) (w v:A->R) (xs:list A), (forall x, In x xs -> 0<=w x) -> 0<=batch_second w v xs.
Proof.
  intros A w v xs Hw; unfold batch_second; apply finite_sum_nonnegative; intros x Hin; replace (w x*v x*v x) with (w x*(v x*v x)) by ring; apply Rmult_le_pos; [apply Hw; exact Hin|pose proof (Rle_0_sqr (v x)) as H; unfold Rsqr in H; exact H].
Qed.

(** [batch_centered_nonnegative] (theorem).
 Mathematical meaning: Any reference-centered corrected sum is nonnegative under nonnegative group sizes.
 Exact proposition: forall (A:Type) (w v:A->R) (c:R) (xs:list A), (forall x, In x xs -> 0<=w x) -> 0<=batch_centered w v c xs.
 Premises and side conditions: All positivity, membership, and nonzero denominator hypotheses needed by this exact statement are explicit. A group is a deterministic identifier, not an independently generated random sample.
 Proof/definition method: Rewrite into the canonical finite_sum and use its previously certified fold, permutation, linearity and order results, or standard real ring and field tactics.
 Library reuse: Rocq Stdlib Reals/List/Ring/Field/Lra/Psatz and the single shared FiniteSum; no custom recursive summation, new probability axioms, or duplicate sample pooling implementation.
 Boundary: Report G12 arbitrary-list deterministic pooling only. No Gaussian sample distribution, chi-square pivot, binomial independence, statistical confidence coverage, or empirical IQ model is inferred.
*)
Theorem batch_centered_nonnegative :
  forall (A:Type) (w v:A->R) (c:R) (xs:list A), (forall x, In x xs -> 0<=w x) -> 0<=batch_centered w v c xs.
Proof.
  intros A w v c xs Hw; unfold batch_centered; apply finite_sum_nonnegative; intros x Hin; replace (w x*(v x-c)*(v x-c)) with (w x*((v x-c)*(v x-c))) by ring; apply Rmult_le_pos; [apply Hw; exact Hin|pose proof (Rle_0_sqr (v x-c)) as H; unfold Rsqr in H; exact H].
Qed.

(** [batch_total_ss_nonnegative] (theorem).
 Mathematical meaning: Nonnegative within-group and between-group dispersions yield nonnegative overall corrected sum of squares.
 Exact proposition: forall (A:Type) (w v u:A->R) (xs:list A), (forall x, In x xs -> 0<=w x) -> (forall x, In x xs -> 0<=u x) -> 0<=batch_total_ss w v u xs.
 Premises and side conditions: All positivity, membership, and nonzero denominator hypotheses needed by this exact statement are explicit. A group is a deterministic identifier, not an independently generated random sample.
 Proof/definition method: Rewrite into the canonical finite_sum and use its previously certified fold, permutation, linearity and order results, or standard real ring and field tactics.
 Library reuse: Rocq Stdlib Reals/List/Ring/Field/Lra/Psatz and the single shared FiniteSum; no custom recursive summation, new probability axioms, or duplicate sample pooling implementation.
 Boundary: Report G12 arbitrary-list deterministic pooling only. No Gaussian sample distribution, chi-square pivot, binomial independence, statistical confidence coverage, or empirical IQ model is inferred.
*)
Theorem batch_total_ss_nonnegative :
  forall (A:Type) (w v u:A->R) (xs:list A), (forall x, In x xs -> 0<=w x) -> (forall x, In x xs -> 0<=u x) -> 0<=batch_total_ss w v u xs.
Proof.
  intros A w v u xs Hw Hu; unfold batch_total_ss; pose proof (finite_sum_nonnegative xs u Hu) as Hwithin; pose proof (batch_centered_nonnegative A w v (batch_mean w v xs) xs Hw) as Hbetween; lra.
Qed.

(** [batch_mean_translation] (theorem).
 Mathematical meaning: A common score translation translates the general weighted mean when total exposure is nonzero.
 Exact proposition: forall (A:Type) (w v:A->R) (xs:list A) (c:R), batch_mass w xs<>0 -> batch_mean w (fun x => v x+c) xs=batch_mean w v xs+c.
 Premises and side conditions: All positivity, membership, and nonzero denominator hypotheses needed by this exact statement are explicit. A group is a deterministic identifier, not an independently generated random sample.
 Proof/definition method: Rewrite into the canonical finite_sum and use its previously certified fold, permutation, linearity and order results, or standard real ring and field tactics.
 Library reuse: Rocq Stdlib Reals/List/Ring/Field/Lra/Psatz and the single shared FiniteSum; no custom recursive summation, new probability axioms, or duplicate sample pooling implementation.
 Boundary: Report G12 arbitrary-list deterministic pooling only. No Gaussian sample distribution, chi-square pivot, binomial independence, statistical confidence coverage, or empirical IQ model is inferred.
*)
Theorem batch_mean_translation :
  forall (A:Type) (w v:A->R) (xs:list A) (c:R), batch_mass w xs<>0 -> batch_mean w (fun x => v x+c) xs=batch_mean w v xs+c.
Proof.
  intros A w v xs c H; unfold batch_mean; rewrite batch_total_translate_values; field; exact H.
Qed.

(** [batch_mean_scale] (theorem).
 Mathematical meaning: Scaling all group centers scales their pooled mean when total exposure is nonzero.
 Exact proposition: forall (A:Type) (w v:A->R) (xs:list A) (t:R), batch_mass w xs<>0 -> batch_mean w (fun x => t*v x) xs=t*batch_mean w v xs.
 Premises and side conditions: All positivity, membership, and nonzero denominator hypotheses needed by this exact statement are explicit. A group is a deterministic identifier, not an independently generated random sample.
 Proof/definition method: Rewrite into the canonical finite_sum and use its previously certified fold, permutation, linearity and order results, or standard real ring and field tactics.
 Library reuse: Rocq Stdlib Reals/List/Ring/Field/Lra/Psatz and the single shared FiniteSum; no custom recursive summation, new probability axioms, or duplicate sample pooling implementation.
 Boundary: Report G12 arbitrary-list deterministic pooling only. No Gaussian sample distribution, chi-square pivot, binomial independence, statistical confidence coverage, or empirical IQ model is inferred.
*)
Theorem batch_mean_scale :
  forall (A:Type) (w v:A->R) (xs:list A) (t:R), batch_mass w xs<>0 -> batch_mean w (fun x => t*v x) xs=t*batch_mean w v xs.
Proof.
  intros A w v xs t H; unfold batch_mean; rewrite batch_total_scale_values; field; exact H.
Qed.

(** [batch_mean_rescale_weights] (theorem).
 Mathematical meaning: Multiplying all group sizes by a nonzero factor does not change the mean.
 Exact proposition: forall (A:Type) (w v:A->R) (xs:list A) (t:R), batch_mass w xs<>0 -> t<>0 -> batch_mean (fun x => t*w x) v xs=batch_mean w v xs.
 Premises and side conditions: All positivity, membership, and nonzero denominator hypotheses needed by this exact statement are explicit. A group is a deterministic identifier, not an independently generated random sample.
 Proof/definition method: Rewrite into the canonical finite_sum and use its previously certified fold, permutation, linearity and order results, or standard real ring and field tactics.
 Library reuse: Rocq Stdlib Reals/List/Ring/Field/Lra/Psatz and the single shared FiniteSum; no custom recursive summation, new probability axioms, or duplicate sample pooling implementation.
 Boundary: Report G12 arbitrary-list deterministic pooling only. No Gaussian sample distribution, chi-square pivot, binomial independence, statistical confidence coverage, or empirical IQ model is inferred.
*)
Theorem batch_mean_rescale_weights :
  forall (A:Type) (w v:A->R) (xs:list A) (t:R), batch_mass w xs<>0 -> t<>0 -> batch_mean (fun x => t*w x) v xs=batch_mean w v xs.
Proof.
  intros A w v xs t Hm Ht; unfold batch_mean; rewrite batch_total_scale_weights, batch_mass_scale_weights; field; nra.
Qed.

(** [batch_cross] (definition).
 Mathematical meaning: The mixed second raw moment or weighted inner product of two batch-level attributes.
 Exact declaration: Definition batch_cross {A:Type} (w v z:A->R) (xs:list A):R := finite_sum (fun x => w x*v x*z x) xs.
 Premises and side conditions: All positivity, membership and denominator conditions needed for the stated assertion are written explicitly. Group identifiers and observations are deterministic data, not asserted independent random samples.
 Proof/definition method: Reduce to FiniteSum's certified additive and scalar identities or use standard real arithmetic; reuse earlier bridge lemmas wherever possible.
 Library reuse: Rocq Stdlib List/Reals/Ring/Field/Lra/Psatz, canonical FiniteSum and prior ListPoolingAlgebra lemmas, not a second recursive aggregator.
 Boundary: This is a reusable deterministic finite-sample algebraic fact for report G12. The statement alone does not certify a Gaussian/chi-square or independent binomial distribution, IQ-model validity, or confidence coverage.
*)

Definition batch_cross {A:Type} (w v z:A->R) (xs:list A):R := finite_sum (fun x => w x*v x*z x) xs.

(** [batch_cross_app] (theorem).
 Mathematical meaning: The weighted mixed moment is additive over disjoint list concatenation.
 Exact proposition: forall (A:Type) (w v z:A->R) (xs ys:list A), batch_cross w v z (xs++ys)=batch_cross w v z xs+batch_cross w v z ys.
 Premises and side conditions: All positivity, membership and denominator conditions needed for the stated assertion are written explicitly. Group identifiers and observations are deterministic data, not asserted independent random samples.
 Proof/definition method: Reduce to FiniteSum's certified additive and scalar identities or use standard real arithmetic; reuse earlier bridge lemmas wherever possible.
 Library reuse: Rocq Stdlib List/Reals/Ring/Field/Lra/Psatz, canonical FiniteSum and prior ListPoolingAlgebra lemmas, not a second recursive aggregator.
 Boundary: This is a reusable deterministic finite-sample algebraic fact for report G12. The statement alone does not certify a Gaussian/chi-square or independent binomial distribution, IQ-model validity, or confidence coverage.
*)
Theorem batch_cross_app :
  forall (A:Type) (w v z:A->R) (xs ys:list A), batch_cross w v z (xs++ys)=batch_cross w v z xs+batch_cross w v z ys.
Proof.
  intros A w v z xs ys; unfold batch_cross; apply finite_sum_app.
Qed.

(** [batch_cross_permutation] (theorem).
 Mathematical meaning: Mixed raw moments remain unchanged after any permutation of the batch ordering.
 Exact proposition: forall (A:Type) (w v z:A->R) (xs ys:list A), Permutation xs ys -> batch_cross w v z xs=batch_cross w v z ys.
 Premises and side conditions: All positivity, membership and denominator conditions needed for the stated assertion are written explicitly. Group identifiers and observations are deterministic data, not asserted independent random samples.
 Proof/definition method: Reduce to FiniteSum's certified additive and scalar identities or use standard real arithmetic; reuse earlier bridge lemmas wherever possible.
 Library reuse: Rocq Stdlib List/Reals/Ring/Field/Lra/Psatz, canonical FiniteSum and prior ListPoolingAlgebra lemmas, not a second recursive aggregator.
 Boundary: This is a reusable deterministic finite-sample algebraic fact for report G12. The statement alone does not certify a Gaussian/chi-square or independent binomial distribution, IQ-model validity, or confidence coverage.
*)
Theorem batch_cross_permutation :
  forall (A:Type) (w v z:A->R) (xs ys:list A), Permutation xs ys -> batch_cross w v z xs=batch_cross w v z ys.
Proof.
  intros A w v z xs ys Hp; unfold batch_cross; now apply finite_sum_permutation.
Qed.

(** [batch_cross_symmetry] (theorem).
 Mathematical meaning: The weighted inner product is symmetric in the two batch-level attributes.
 Exact proposition: forall (A:Type) (w v z:A->R) (xs:list A), batch_cross w v z xs=batch_cross w z v xs.
 Premises and side conditions: All positivity, membership and denominator conditions needed for the stated assertion are written explicitly. Group identifiers and observations are deterministic data, not asserted independent random samples.
 Proof/definition method: Reduce to FiniteSum's certified additive and scalar identities or use standard real arithmetic; reuse earlier bridge lemmas wherever possible.
 Library reuse: Rocq Stdlib List/Reals/Ring/Field/Lra/Psatz, canonical FiniteSum and prior ListPoolingAlgebra lemmas, not a second recursive aggregator.
 Boundary: This is a reusable deterministic finite-sample algebraic fact for report G12. The statement alone does not certify a Gaussian/chi-square or independent binomial distribution, IQ-model validity, or confidence coverage.
*)
Theorem batch_cross_symmetry :
  forall (A:Type) (w v z:A->R) (xs:list A), batch_cross w v z xs=batch_cross w z v xs.
Proof.
  intros A w v z xs; unfold batch_cross; apply finite_sum_ext; intro x; ring.
Qed.

(** [batch_cross_add_left] (theorem).
 Mathematical meaning: The weighted mixed moment is linear in its first variable.
 Exact proposition: forall (A:Type) (w v z u:A->R) (xs:list A), batch_cross w (fun x=>v x+z x) u xs=batch_cross w v u xs+batch_cross w z u xs.
 Premises and side conditions: All positivity, membership and denominator conditions needed for the stated assertion are written explicitly. Group identifiers and observations are deterministic data, not asserted independent random samples.
 Proof/definition method: Reduce to FiniteSum's certified additive and scalar identities or use standard real arithmetic; reuse earlier bridge lemmas wherever possible.
 Library reuse: Rocq Stdlib List/Reals/Ring/Field/Lra/Psatz, canonical FiniteSum and prior ListPoolingAlgebra lemmas, not a second recursive aggregator.
 Boundary: This is a reusable deterministic finite-sample algebraic fact for report G12. The statement alone does not certify a Gaussian/chi-square or independent binomial distribution, IQ-model validity, or confidence coverage.
*)
Theorem batch_cross_add_left :
  forall (A:Type) (w v z u:A->R) (xs:list A), batch_cross w (fun x=>v x+z x) u xs=batch_cross w v u xs+batch_cross w z u xs.
Proof.
  intros A w v z u xs; unfold batch_cross; transitivity (finite_sum (fun x => w x*v x*u x+w x*z x*u x) xs); [apply finite_sum_ext; intro x; ring|rewrite finite_sum_add; reflexivity].
Qed.

(** [batch_cross_scale_left] (theorem).
 Mathematical meaning: Scaling the left attribute scales the complete mixed moment.
 Exact proposition: forall (A:Type) (w v z:A->R) (xs:list A) (t:R), batch_cross w (fun x=>t*v x) z xs=t*batch_cross w v z xs.
 Premises and side conditions: All positivity, membership and denominator conditions needed for the stated assertion are written explicitly. Group identifiers and observations are deterministic data, not asserted independent random samples.
 Proof/definition method: Reduce to FiniteSum's certified additive and scalar identities or use standard real arithmetic; reuse earlier bridge lemmas wherever possible.
 Library reuse: Rocq Stdlib List/Reals/Ring/Field/Lra/Psatz, canonical FiniteSum and prior ListPoolingAlgebra lemmas, not a second recursive aggregator.
 Boundary: This is a reusable deterministic finite-sample algebraic fact for report G12. The statement alone does not certify a Gaussian/chi-square or independent binomial distribution, IQ-model validity, or confidence coverage.
*)
Theorem batch_cross_scale_left :
  forall (A:Type) (w v z:A->R) (xs:list A) (t:R), batch_cross w (fun x=>t*v x) z xs=t*batch_cross w v z xs.
Proof.
  intros A w v z xs t; unfold batch_cross; transitivity (finite_sum (fun x => t*(w x*v x*z x)) xs); [apply finite_sum_ext; intro x; ring|rewrite finite_sum_scale; reflexivity].
Qed.

(** [batch_cross_nonnegative] (theorem).
 Mathematical meaning: If weights and both attributes are nonnegative, their weighted mixed moment is nonnegative.
 Exact proposition: forall (A:Type) (w v z:A->R) (xs:list A), (forall x, In x xs -> 0<=w x) -> (forall x, In x xs -> 0<=v x) -> (forall x, In x xs -> 0<=z x) -> 0<=batch_cross w v z xs.
 Premises and side conditions: All positivity, membership and denominator conditions needed for the stated assertion are written explicitly. Group identifiers and observations are deterministic data, not asserted independent random samples.
 Proof/definition method: Reduce to FiniteSum's certified additive and scalar identities or use standard real arithmetic; reuse earlier bridge lemmas wherever possible.
 Library reuse: Rocq Stdlib List/Reals/Ring/Field/Lra/Psatz, canonical FiniteSum and prior ListPoolingAlgebra lemmas, not a second recursive aggregator.
 Boundary: This is a reusable deterministic finite-sample algebraic fact for report G12. The statement alone does not certify a Gaussian/chi-square or independent binomial distribution, IQ-model validity, or confidence coverage.
*)
Theorem batch_cross_nonnegative :
  forall (A:Type) (w v z:A->R) (xs:list A), (forall x, In x xs -> 0<=w x) -> (forall x, In x xs -> 0<=v x) -> (forall x, In x xs -> 0<=z x) -> 0<=batch_cross w v z xs.
Proof.
  intros A w v z xs Hw Hv Hz; unfold batch_cross; apply finite_sum_nonnegative; intros x Hin; apply Rmult_le_pos; [apply Rmult_le_pos; [apply Hw|apply Hv]; exact Hin|apply Hz; exact Hin].
Qed.

(** [batch_cross_self_second] (theorem).
 Mathematical meaning: A weighted raw second moment is exactly the mixed moment of an attribute with itself.
 Exact proposition: forall (A:Type) (w v:A->R) (xs:list A), batch_second w v xs=batch_cross w v v xs.
 Premises and side conditions: All positivity, membership and denominator conditions needed for the stated assertion are written explicitly. Group identifiers and observations are deterministic data, not asserted independent random samples.
 Proof/definition method: Reduce to FiniteSum's certified additive and scalar identities or use standard real arithmetic; reuse earlier bridge lemmas wherever possible.
 Library reuse: Rocq Stdlib List/Reals/Ring/Field/Lra/Psatz, canonical FiniteSum and prior ListPoolingAlgebra lemmas, not a second recursive aggregator.
 Boundary: This is a reusable deterministic finite-sample algebraic fact for report G12. The statement alone does not certify a Gaussian/chi-square or independent binomial distribution, IQ-model validity, or confidence coverage.
*)
Theorem batch_cross_self_second :
  forall (A:Type) (w v:A->R) (xs:list A), batch_second w v xs=batch_cross w v v xs.
Proof.
  intros A w v xs; reflexivity.
Qed.

(** [batch_cross_scale_weights] (theorem).
 Mathematical meaning: Uniformly scaling sample weights scales the mixed raw moment.
 Exact proposition: forall (A:Type) (w v z:A->R) (xs:list A) (t:R), batch_cross (fun x=>t*w x) v z xs=t*batch_cross w v z xs.
 Premises and side conditions: All positivity, membership and denominator conditions needed for the stated assertion are written explicitly. Group identifiers and observations are deterministic data, not asserted independent random samples.
 Proof/definition method: Reduce to FiniteSum's certified additive and scalar identities or use standard real arithmetic; reuse earlier bridge lemmas wherever possible.
 Library reuse: Rocq Stdlib List/Reals/Ring/Field/Lra/Psatz, canonical FiniteSum and prior ListPoolingAlgebra lemmas, not a second recursive aggregator.
 Boundary: This is a reusable deterministic finite-sample algebraic fact for report G12. The statement alone does not certify a Gaussian/chi-square or independent binomial distribution, IQ-model validity, or confidence coverage.
*)
Theorem batch_cross_scale_weights :
  forall (A:Type) (w v z:A->R) (xs:list A) (t:R), batch_cross (fun x=>t*w x) v z xs=t*batch_cross w v z xs.
Proof.
  intros A w v z xs t; unfold batch_cross; transitivity (finite_sum (fun x => t*(w x*v x*z x)) xs); [apply finite_sum_ext; intro x; ring|rewrite finite_sum_scale; reflexivity].
Qed.

(** [batch_second_sum_square] (theorem).
 Mathematical meaning: Polarization: the second moment of a sum is the two second moments plus twice their mixed moment.
 Exact proposition: forall (A:Type) (w v z:A->R) (xs:list A), batch_second w (fun x=>v x+z x) xs=batch_second w v xs+2*batch_cross w v z xs+batch_second w z xs.
 Premises and side conditions: All positivity, membership and denominator conditions needed for the stated assertion are written explicitly. Group identifiers and observations are deterministic data, not asserted independent random samples.
 Proof/definition method: Reduce to FiniteSum's certified additive and scalar identities or use standard real arithmetic; reuse earlier bridge lemmas wherever possible.
 Library reuse: Rocq Stdlib List/Reals/Ring/Field/Lra/Psatz, canonical FiniteSum and prior ListPoolingAlgebra lemmas, not a second recursive aggregator.
 Boundary: This is a reusable deterministic finite-sample algebraic fact for report G12. The statement alone does not certify a Gaussian/chi-square or independent binomial distribution, IQ-model validity, or confidence coverage.
*)
Theorem batch_second_sum_square :
  forall (A:Type) (w v z:A->R) (xs:list A), batch_second w (fun x=>v x+z x) xs=batch_second w v xs+2*batch_cross w v z xs+batch_second w z xs.
Proof.
  intros A w v z xs; unfold batch_second,batch_cross; transitivity (finite_sum (fun x => (w x*v x*v x+2*(w x*v x*z x))+w x*z x*z x) xs); [apply finite_sum_ext; intro x; ring|rewrite !finite_sum_add, finite_sum_scale; ring].
Qed.

(** [batch_total_constant] (theorem).
 Mathematical meaning: Every batch receiving a common value has weighted sum equal to that value times total exposure.
 Exact proposition: forall (A:Type) (w:A->R) (xs:list A) (c:R), batch_total w (fun _=>c) xs=c*batch_mass w xs.
 Premises and side conditions: All positivity, membership and denominator conditions needed for the stated assertion are written explicitly. Group identifiers and observations are deterministic data, not asserted independent random samples.
 Proof/definition method: Reduce to FiniteSum's certified additive and scalar identities or use standard real arithmetic; reuse earlier bridge lemmas wherever possible.
 Library reuse: Rocq Stdlib List/Reals/Ring/Field/Lra/Psatz, canonical FiniteSum and prior ListPoolingAlgebra lemmas, not a second recursive aggregator.
 Boundary: This is a reusable deterministic finite-sample algebraic fact for report G12. The statement alone does not certify a Gaussian/chi-square or independent binomial distribution, IQ-model validity, or confidence coverage.
*)
Theorem batch_total_constant :
  forall (A:Type) (w:A->R) (xs:list A) (c:R), batch_total w (fun _=>c) xs=c*batch_mass w xs.
Proof.
  intros A w xs c; unfold batch_total,batch_mass; transitivity (finite_sum (fun x=>c*w x) xs); [apply finite_sum_ext; intro x; ring|rewrite finite_sum_scale; reflexivity].
Qed.

(** [batch_mean_constant] (theorem).
 Mathematical meaning: The weighted mean of a common constant is that constant when total mass is nonzero.
 Exact proposition: forall (A:Type) (w:A->R) (xs:list A) (c:R), batch_mass w xs<>0 -> batch_mean w (fun _=>c) xs=c.
 Premises and side conditions: All positivity, membership and denominator conditions needed for the stated assertion are written explicitly. Group identifiers and observations are deterministic data, not asserted independent random samples.
 Proof/definition method: Reduce to FiniteSum's certified additive and scalar identities or use standard real arithmetic; reuse earlier bridge lemmas wherever possible.
 Library reuse: Rocq Stdlib List/Reals/Ring/Field/Lra/Psatz, canonical FiniteSum and prior ListPoolingAlgebra lemmas, not a second recursive aggregator.
 Boundary: This is a reusable deterministic finite-sample algebraic fact for report G12. The statement alone does not certify a Gaussian/chi-square or independent binomial distribution, IQ-model validity, or confidence coverage.
*)
Theorem batch_mean_constant :
  forall (A:Type) (w:A->R) (xs:list A) (c:R), batch_mass w xs<>0 -> batch_mean w (fun _=>c) xs=c.
Proof.
  intros A w xs c H; unfold batch_mean; rewrite batch_total_constant; field; exact H.
Qed.

(** [batch_mean_total_identity] (theorem).
 Mathematical meaning: Total weighted first moment equals pooled mean multiplied by total mass when mass is nonzero.
 Exact proposition: forall (A:Type) (w v:A->R) (xs:list A), batch_mass w xs<>0 -> batch_total w v xs=batch_mean w v xs*batch_mass w xs.
 Premises and side conditions: All positivity, membership and denominator conditions needed for the stated assertion are written explicitly. Group identifiers and observations are deterministic data, not asserted independent random samples.
 Proof/definition method: Reduce to FiniteSum's certified additive and scalar identities or use standard real arithmetic; reuse earlier bridge lemmas wherever possible.
 Library reuse: Rocq Stdlib List/Reals/Ring/Field/Lra/Psatz, canonical FiniteSum and prior ListPoolingAlgebra lemmas, not a second recursive aggregator.
 Boundary: This is a reusable deterministic finite-sample algebraic fact for report G12. The statement alone does not certify a Gaussian/chi-square or independent binomial distribution, IQ-model validity, or confidence coverage.
*)
Theorem batch_mean_total_identity :
  forall (A:Type) (w v:A->R) (xs:list A), batch_mass w xs<>0 -> batch_total w v xs=batch_mean w v xs*batch_mass w xs.
Proof.
  intros A w v xs H; unfold batch_mean; field; exact H.
Qed.

(** [batch_mean_zero_iff_total_zero] (theorem).
 Mathematical meaning: With positive or negative nonzero mass, the weighted mean vanishes iff the first raw weighted moment vanishes.
 Exact proposition: forall (A:Type) (w v:A->R) (xs:list A), batch_mass w xs<>0 -> (batch_mean w v xs=0 <-> batch_total w v xs=0).
 Premises and side conditions: All positivity, membership and denominator conditions needed for the stated assertion are written explicitly. Group identifiers and observations are deterministic data, not asserted independent random samples.
 Proof/definition method: Reduce to FiniteSum's certified additive and scalar identities or use standard real arithmetic; reuse earlier bridge lemmas wherever possible.
 Library reuse: Rocq Stdlib List/Reals/Ring/Field/Lra/Psatz, canonical FiniteSum and prior ListPoolingAlgebra lemmas, not a second recursive aggregator.
 Boundary: This is a reusable deterministic finite-sample algebraic fact for report G12. The statement alone does not certify a Gaussian/chi-square or independent binomial distribution, IQ-model validity, or confidence coverage.
*)
Theorem batch_mean_zero_iff_total_zero :
  forall (A:Type) (w v:A->R) (xs:list A), batch_mass w xs<>0 -> (batch_mean w v xs=0 <-> batch_total w v xs=0).
Proof.
  intros A w v xs Hm; split; intro H; [pose proof (batch_mean_total_identity A w v xs Hm) as E; rewrite H in E; nra|unfold batch_mean; rewrite H; field; exact Hm].
Qed.

(** [batch_centered_expand] (theorem).
 Mathematical meaning: Arbitrary-list weighted ANOVA expands around any reference into the first and second raw moments.
 Exact proposition: forall (A:Type) (w v:A->R) (xs:list A) (c:R), batch_centered w v c xs=batch_second w v xs-2*c*batch_total w v xs+c*c*batch_mass w xs.
 Premises and side conditions: All positivity, membership and denominator conditions needed for the stated assertion are written explicitly. Group identifiers and observations are deterministic data, not asserted independent random samples.
 Proof/definition method: Reduce to FiniteSum's certified additive and scalar identities or use standard real arithmetic; reuse earlier bridge lemmas wherever possible.
 Library reuse: Rocq Stdlib List/Reals/Ring/Field/Lra/Psatz, canonical FiniteSum and prior ListPoolingAlgebra lemmas, not a second recursive aggregator.
 Boundary: This is a reusable deterministic finite-sample algebraic fact for report G12. The statement alone does not certify a Gaussian/chi-square or independent binomial distribution, IQ-model validity, or confidence coverage.
*)
Theorem batch_centered_expand :
  forall (A:Type) (w v:A->R) (xs:list A) (c:R), batch_centered w v c xs=batch_second w v xs-2*c*batch_total w v xs+c*c*batch_mass w xs.
Proof.
  intros A w v xs c; unfold batch_centered,batch_second,batch_total,batch_mass; transitivity (finite_sum (fun x => (w x*v x*v x-(2*c)*(w x*v x))+(c*c)*w x) xs); [apply finite_sum_ext; intro x; ring|rewrite finite_sum_add, finite_sum_sub, !finite_sum_scale; ring].
Qed.

(** [batch_centered_at_mean_closed] (theorem).
 Mathematical meaning: The exact corrected sum about the weighted mean is second raw moment minus squared first moment divided by mass.
 Exact proposition: forall (A:Type) (w v:A->R) (xs:list A), batch_mass w xs<>0 -> batch_centered w v (batch_mean w v xs) xs=batch_second w v xs-(batch_total w v xs*batch_total w v xs)/batch_mass w xs.
 Premises and side conditions: All positivity, membership and denominator conditions needed for the stated assertion are written explicitly. Group identifiers and observations are deterministic data, not asserted independent random samples.
 Proof/definition method: Reduce to FiniteSum's certified additive and scalar identities or use standard real arithmetic; reuse earlier bridge lemmas wherever possible.
 Library reuse: Rocq Stdlib List/Reals/Ring/Field/Lra/Psatz, canonical FiniteSum and prior ListPoolingAlgebra lemmas, not a second recursive aggregator.
 Boundary: This is a reusable deterministic finite-sample algebraic fact for report G12. The statement alone does not certify a Gaussian/chi-square or independent binomial distribution, IQ-model validity, or confidence coverage.
*)
Theorem batch_centered_at_mean_closed :
  forall (A:Type) (w v:A->R) (xs:list A), batch_mass w xs<>0 -> batch_centered w v (batch_mean w v xs) xs=batch_second w v xs-(batch_total w v xs*batch_total w v xs)/batch_mass w xs.
Proof.
  intros A w v xs H; rewrite batch_centered_expand; unfold batch_mean; field; exact H.
Qed.

(** [batch_centered_mean_correction] (theorem).
 Mathematical meaning: The reference-center dispersion differs from the optimized mean-centered dispersion by mass times the squared center discrepancy.
 Exact proposition: forall (A:Type) (w v:A->R) (xs:list A) (c:R), batch_mass w xs<>0 -> batch_centered w v c xs=batch_centered w v (batch_mean w v xs) xs+batch_mass w xs*(batch_mean w v xs-c)*(batch_mean w v xs-c).
 Premises and side conditions: All positivity, membership and denominator conditions needed for the stated assertion are written explicitly. Group identifiers and observations are deterministic data, not asserted independent random samples.
 Proof/definition method: Reduce to FiniteSum's certified additive and scalar identities or use standard real arithmetic; reuse earlier bridge lemmas wherever possible.
 Library reuse: Rocq Stdlib List/Reals/Ring/Field/Lra/Psatz, canonical FiniteSum and prior ListPoolingAlgebra lemmas, not a second recursive aggregator.
 Boundary: This is a reusable deterministic finite-sample algebraic fact for report G12. The statement alone does not certify a Gaussian/chi-square or independent binomial distribution, IQ-model validity, or confidence coverage.
*)
Theorem batch_centered_mean_correction :
  forall (A:Type) (w v:A->R) (xs:list A) (c:R), batch_mass w xs<>0 -> batch_centered w v c xs=batch_centered w v (batch_mean w v xs) xs+batch_mass w xs*(batch_mean w v xs-c)*(batch_mean w v xs-c).
Proof.
  intros A w v xs c H; rewrite !batch_centered_expand; pose proof (batch_mean_total_identity A w v xs H) as E; rewrite E; ring.
Qed.

(** [batch_centered_minimal] (theorem).
 Mathematical meaning: Under nonnegative weights and positive mass, weighted sample mean minimizes corrected sum of squares.
 Exact proposition: forall (A:Type) (w v:A->R) (xs:list A) (c:R), 0<batch_mass w xs -> batch_centered w v (batch_mean w v xs) xs<=batch_centered w v c xs.
 Premises and side conditions: All positivity, membership and denominator conditions needed for the stated assertion are written explicitly. Group identifiers and observations are deterministic data, not asserted independent random samples.
 Proof/definition method: Reduce to FiniteSum's certified additive and scalar identities or use standard real arithmetic; reuse earlier bridge lemmas wherever possible.
 Library reuse: Rocq Stdlib List/Reals/Ring/Field/Lra/Psatz, canonical FiniteSum and prior ListPoolingAlgebra lemmas, not a second recursive aggregator.
 Boundary: This is a reusable deterministic finite-sample algebraic fact for report G12. The statement alone does not certify a Gaussian/chi-square or independent binomial distribution, IQ-model validity, or confidence coverage.
*)
Theorem batch_centered_minimal :
  forall (A:Type) (w v:A->R) (xs:list A) (c:R), 0<batch_mass w xs -> batch_centered w v (batch_mean w v xs) xs<=batch_centered w v c xs.
Proof.
  intros A w v xs c H; rewrite (batch_centered_mean_correction A w v xs c) by lra; assert (Hs:0<=(batch_mean w v xs-c)*(batch_mean w v xs-c)) by (pose proof (Rle_0_sqr (batch_mean w v xs-c)) as E; unfold Rsqr in E; exact E); nra.
Qed.

(** [batch_centered_constant_zero] (theorem).
 Mathematical meaning: Every batch equal to a common reference produces zero between-batch corrected dispersion.
 Exact proposition: forall (A:Type) (w:A->R) (xs:list A) (c:R), batch_centered w (fun _=>c) c xs=0.
 Premises and side conditions: All positivity, membership and denominator conditions needed for the stated assertion are written explicitly. Group identifiers and observations are deterministic data, not asserted independent random samples.
 Proof/definition method: Reduce to FiniteSum's certified additive and scalar identities or use standard real arithmetic; reuse earlier bridge lemmas wherever possible.
 Library reuse: Rocq Stdlib List/Reals/Ring/Field/Lra/Psatz, canonical FiniteSum and prior ListPoolingAlgebra lemmas, not a second recursive aggregator.
 Boundary: This is a reusable deterministic finite-sample algebraic fact for report G12. The statement alone does not certify a Gaussian/chi-square or independent binomial distribution, IQ-model validity, or confidence coverage.
*)
Theorem batch_centered_constant_zero :
  forall (A:Type) (w:A->R) (xs:list A) (c:R), batch_centered w (fun _=>c) c xs=0.
Proof.
  intros A w xs c; unfold batch_centered; transitivity (finite_sum (fun _=>0) xs); [apply finite_sum_ext; intro x; ring|apply finite_sum_zero].
Qed.

(** [batch_centered_translation] (theorem).
 Mathematical meaning: Translating all group means and the reference by the same amount preserves between-group dispersion.
 Exact proposition: forall (A:Type) (w v:A->R) (xs:list A) (c t:R), batch_centered w (fun x=>v x+t) (c+t) xs=batch_centered w v c xs.
 Premises and side conditions: All positivity, membership and denominator conditions needed for the stated assertion are written explicitly. Group identifiers and observations are deterministic data, not asserted independent random samples.
 Proof/definition method: Reduce to FiniteSum's certified additive and scalar identities or use standard real arithmetic; reuse earlier bridge lemmas wherever possible.
 Library reuse: Rocq Stdlib List/Reals/Ring/Field/Lra/Psatz, canonical FiniteSum and prior ListPoolingAlgebra lemmas, not a second recursive aggregator.
 Boundary: This is a reusable deterministic finite-sample algebraic fact for report G12. The statement alone does not certify a Gaussian/chi-square or independent binomial distribution, IQ-model validity, or confidence coverage.
*)
Theorem batch_centered_translation :
  forall (A:Type) (w v:A->R) (xs:list A) (c t:R), batch_centered w (fun x=>v x+t) (c+t) xs=batch_centered w v c xs.
Proof.
  intros A w v xs c t; unfold batch_centered; apply finite_sum_ext; intro x; ring.
Qed.

(** [batch_centered_scale_values] (theorem).
 Mathematical meaning: Rescaling both group means and reference scales corrected dispersion by the square of the factor.
 Exact proposition: forall (A:Type) (w v:A->R) (xs:list A) (c t:R), batch_centered w (fun x=>t*v x) (t*c) xs=t*t*batch_centered w v c xs.
 Premises and side conditions: All positivity, membership and denominator conditions needed for the stated assertion are written explicitly. Group identifiers and observations are deterministic data, not asserted independent random samples.
 Proof/definition method: Reduce to FiniteSum's certified additive and scalar identities or use standard real arithmetic; reuse earlier bridge lemmas wherever possible.
 Library reuse: Rocq Stdlib List/Reals/Ring/Field/Lra/Psatz, canonical FiniteSum and prior ListPoolingAlgebra lemmas, not a second recursive aggregator.
 Boundary: This is a reusable deterministic finite-sample algebraic fact for report G12. The statement alone does not certify a Gaussian/chi-square or independent binomial distribution, IQ-model validity, or confidence coverage.
*)
Theorem batch_centered_scale_values :
  forall (A:Type) (w v:A->R) (xs:list A) (c t:R), batch_centered w (fun x=>t*v x) (t*c) xs=t*t*batch_centered w v c xs.
Proof.
  intros A w v xs c t; unfold batch_centered; transitivity (finite_sum (fun x => (t*t)*(w x*(v x-c)*(v x-c))) xs); [apply finite_sum_ext; intro x; ring|rewrite finite_sum_scale; ring].
Qed.

(** [batch_centered_scale_weights] (theorem).
 Mathematical meaning: A uniform sample-size rescaling scales corrected between-batch dispersion linearly.
 Exact proposition: forall (A:Type) (w v:A->R) (xs:list A) (c t:R), batch_centered (fun x=>t*w x) v c xs=t*batch_centered w v c xs.
 Premises and side conditions: All positivity, membership and denominator conditions needed for the stated assertion are written explicitly. Group identifiers and observations are deterministic data, not asserted independent random samples.
 Proof/definition method: Reduce to FiniteSum's certified additive and scalar identities or use standard real arithmetic; reuse earlier bridge lemmas wherever possible.
 Library reuse: Rocq Stdlib List/Reals/Ring/Field/Lra/Psatz, canonical FiniteSum and prior ListPoolingAlgebra lemmas, not a second recursive aggregator.
 Boundary: This is a reusable deterministic finite-sample algebraic fact for report G12. The statement alone does not certify a Gaussian/chi-square or independent binomial distribution, IQ-model validity, or confidence coverage.
*)
Theorem batch_centered_scale_weights :
  forall (A:Type) (w v:A->R) (xs:list A) (c t:R), batch_centered (fun x=>t*w x) v c xs=t*batch_centered w v c xs.
Proof.
  intros A w v xs c t; unfold batch_centered; transitivity (finite_sum (fun x=>t*(w x*(v x-c)*(v x-c))) xs); [apply finite_sum_ext; intro x; ring|rewrite finite_sum_scale; reflexivity].
Qed.

(** [batch_total_ss_translation] (theorem).
 Mathematical meaning: Translation of every group center preserves the total corrected sum, including within-batch sums.
 Exact proposition: forall (A:Type) (w v u:A->R) (xs:list A) (t:R), batch_mass w xs<>0 -> batch_total_ss w (fun x=>v x+t) u xs=batch_total_ss w v u xs.
 Premises and side conditions: All positivity, membership and denominator conditions needed for the stated assertion are written explicitly. Group identifiers and observations are deterministic data, not asserted independent random samples.
 Proof/definition method: Reduce to FiniteSum's certified additive and scalar identities or use standard real arithmetic; reuse earlier bridge lemmas wherever possible.
 Library reuse: Rocq Stdlib List/Reals/Ring/Field/Lra/Psatz, canonical FiniteSum and prior ListPoolingAlgebra lemmas, not a second recursive aggregator.
 Boundary: This is a reusable deterministic finite-sample algebraic fact for report G12. The statement alone does not certify a Gaussian/chi-square or independent binomial distribution, IQ-model validity, or confidence coverage.
*)
Theorem batch_total_ss_translation :
  forall (A:Type) (w v u:A->R) (xs:list A) (t:R), batch_mass w xs<>0 -> batch_total_ss w (fun x=>v x+t) u xs=batch_total_ss w v u xs.
Proof.
  intros A w v u xs t H; unfold batch_total_ss; rewrite batch_mean_translation by assumption; rewrite batch_centered_translation; reflexivity.
Qed.

(** [batch_total_ss_scale] (theorem).
 Mathematical meaning: Rescaling group values and their within-batch quadratic sums has the expected quadratic effect on total corrected SS.
 Exact proposition: forall (A:Type) (w v u:A->R) (xs:list A) (t:R), batch_mass w xs<>0 -> batch_total_ss w (fun x=>t*v x) (fun x=>(t*t)*u x) xs=t*t*batch_total_ss w v u xs.
 Premises and side conditions: All positivity, membership and denominator conditions needed for the stated assertion are written explicitly. Group identifiers and observations are deterministic data, not asserted independent random samples.
 Proof/definition method: Reduce to FiniteSum's certified additive and scalar identities or use standard real arithmetic; reuse earlier bridge lemmas wherever possible.
 Library reuse: Rocq Stdlib List/Reals/Ring/Field/Lra/Psatz, canonical FiniteSum and prior ListPoolingAlgebra lemmas, not a second recursive aggregator.
 Boundary: This is a reusable deterministic finite-sample algebraic fact for report G12. The statement alone does not certify a Gaussian/chi-square or independent binomial distribution, IQ-model validity, or confidence coverage.
*)
Theorem batch_total_ss_scale :
  forall (A:Type) (w v u:A->R) (xs:list A) (t:R), batch_mass w xs<>0 -> batch_total_ss w (fun x=>t*v x) (fun x=>(t*t)*u x) xs=t*t*batch_total_ss w v u xs.
Proof.
  intros A w v u xs t H; unfold batch_total_ss; rewrite batch_mean_scale by assumption; rewrite batch_centered_scale_values; rewrite finite_sum_scale; ring.
Qed.

(** [batch_pairwise] (definition).
 Mathematical meaning: Twice-counted sample-size-weighted pairwise squared differences among all batch centers.
 Exact declaration: Definition batch_pairwise {A:Type} (w v:A->R) (xs:list A):R := finite_sum (fun i => finite_sum (fun j => w i*w j*(v i-v j)*(v i-v j)) xs) xs.
 Premises and side conditions: Finite input lists and all positive mass, sign, and sample-size hypotheses are stated where required. Observations and weights are numerical data rather than random variables.
 Proof/definition method: Compose the canonical FiniteSum algebra, the already established weighted moment identities and ordinary Rocq real field/ring/order lemmas.
 Library reuse: Rocq Stdlib Reals, List, Sorting.Permutation, Ring, Field, Lra, Psatz and canonical FiniteSum/PooledMomentsAlgebra; no recursive duplicate integrator or hidden statistical assumptions.
 Boundary: Deterministic arbitrary-list pooling supports report sm:pooling (G12), but does not by itself prove the report's independent-binomial summation, a chi-square pivot, Gaussianity or coverage.
*)
Definition batch_pairwise {A:Type} (w v:A->R) (xs:list A):R := finite_sum (fun i => finite_sum (fun j => w i*w j*(v i-v j)*(v i-v j)) xs) xs.

(** [batch_unbiased_variance] (definition).
 Mathematical meaning: Deterministic unbiased-style pooled variance quotient when aggregate sample count exceeds one.
 Exact declaration: Definition batch_unbiased_variance {A:Type} (w v u:A->R) (xs:list A):R := batch_total_ss w v u xs / (batch_mass w xs-1).
 Premises and side conditions: Finite input lists and all positive mass, sign, and sample-size hypotheses are stated where required. Observations and weights are numerical data rather than random variables.
 Proof/definition method: Compose the canonical FiniteSum algebra, the already established weighted moment identities and ordinary Rocq real field/ring/order lemmas.
 Library reuse: Rocq Stdlib Reals, List, Sorting.Permutation, Ring, Field, Lra, Psatz and canonical FiniteSum/PooledMomentsAlgebra; no recursive duplicate integrator or hidden statistical assumptions.
 Boundary: Deterministic arbitrary-list pooling supports report sm:pooling (G12), but does not by itself prove the report's independent-binomial summation, a chi-square pivot, Gaussianity or coverage.
*)
Definition batch_unbiased_variance {A:Type} (w v u:A->R) (xs:list A):R := batch_total_ss w v u xs / (batch_mass w xs-1).

(** [batch_mass_rev] (theorem).
 Mathematical meaning: Reversing the order of arbitrary batches preserves total mass.
 Exact proposition: forall (A:Type) (w:A->R) (xs:list A), batch_mass w (rev xs)=batch_mass w xs.
 Premises and side conditions: Finite input lists and all positive mass, sign, and sample-size hypotheses are stated where required. Observations and weights are numerical data rather than random variables.
 Proof/definition method: Compose the canonical FiniteSum algebra, the already established weighted moment identities and ordinary Rocq real field/ring/order lemmas.
 Library reuse: Rocq Stdlib Reals, List, Sorting.Permutation, Ring, Field, Lra, Psatz and canonical FiniteSum/PooledMomentsAlgebra; no recursive duplicate integrator or hidden statistical assumptions.
 Boundary: Deterministic arbitrary-list pooling supports report sm:pooling (G12), but does not by itself prove the report's independent-binomial summation, a chi-square pivot, Gaussianity or coverage.
*)
Theorem batch_mass_rev :
  forall (A:Type) (w:A->R) (xs:list A), batch_mass w (rev xs)=batch_mass w xs.
Proof.
  intros A w xs; unfold batch_mass; apply finite_sum_rev.
Qed.

(** [batch_total_rev] (theorem).
 Mathematical meaning: Reversing batches preserves their weighted first moment.
 Exact proposition: forall (A:Type) (w v:A->R) (xs:list A), batch_total w v (rev xs)=batch_total w v xs.
 Premises and side conditions: Finite input lists and all positive mass, sign, and sample-size hypotheses are stated where required. Observations and weights are numerical data rather than random variables.
 Proof/definition method: Compose the canonical FiniteSum algebra, the already established weighted moment identities and ordinary Rocq real field/ring/order lemmas.
 Library reuse: Rocq Stdlib Reals, List, Sorting.Permutation, Ring, Field, Lra, Psatz and canonical FiniteSum/PooledMomentsAlgebra; no recursive duplicate integrator or hidden statistical assumptions.
 Boundary: Deterministic arbitrary-list pooling supports report sm:pooling (G12), but does not by itself prove the report's independent-binomial summation, a chi-square pivot, Gaussianity or coverage.
*)
Theorem batch_total_rev :
  forall (A:Type) (w v:A->R) (xs:list A), batch_total w v (rev xs)=batch_total w v xs.
Proof.
  intros A w v xs; unfold batch_total; apply finite_sum_rev.
Qed.

(** [batch_second_rev] (theorem).
 Mathematical meaning: Reversing batches preserves weighted second raw moments.
 Exact proposition: forall (A:Type) (w v:A->R) (xs:list A), batch_second w v (rev xs)=batch_second w v xs.
 Premises and side conditions: Finite input lists and all positive mass, sign, and sample-size hypotheses are stated where required. Observations and weights are numerical data rather than random variables.
 Proof/definition method: Compose the canonical FiniteSum algebra, the already established weighted moment identities and ordinary Rocq real field/ring/order lemmas.
 Library reuse: Rocq Stdlib Reals, List, Sorting.Permutation, Ring, Field, Lra, Psatz and canonical FiniteSum/PooledMomentsAlgebra; no recursive duplicate integrator or hidden statistical assumptions.
 Boundary: Deterministic arbitrary-list pooling supports report sm:pooling (G12), but does not by itself prove the report's independent-binomial summation, a chi-square pivot, Gaussianity or coverage.
*)
Theorem batch_second_rev :
  forall (A:Type) (w v:A->R) (xs:list A), batch_second w v (rev xs)=batch_second w v xs.
Proof.
  intros A w v xs; unfold batch_second; apply finite_sum_rev.
Qed.

(** [batch_centered_rev] (theorem).
 Mathematical meaning: Reversing batches preserves arbitrary-reference corrected sums of squares.
 Exact proposition: forall (A:Type) (w v:A->R) (c:R) (xs:list A), batch_centered w v c (rev xs)=batch_centered w v c xs.
 Premises and side conditions: Finite input lists and all positive mass, sign, and sample-size hypotheses are stated where required. Observations and weights are numerical data rather than random variables.
 Proof/definition method: Compose the canonical FiniteSum algebra, the already established weighted moment identities and ordinary Rocq real field/ring/order lemmas.
 Library reuse: Rocq Stdlib Reals, List, Sorting.Permutation, Ring, Field, Lra, Psatz and canonical FiniteSum/PooledMomentsAlgebra; no recursive duplicate integrator or hidden statistical assumptions.
 Boundary: Deterministic arbitrary-list pooling supports report sm:pooling (G12), but does not by itself prove the report's independent-binomial summation, a chi-square pivot, Gaussianity or coverage.
*)
Theorem batch_centered_rev :
  forall (A:Type) (w v:A->R) (c:R) (xs:list A), batch_centered w v c (rev xs)=batch_centered w v c xs.
Proof.
  intros A w v c xs; unfold batch_centered; apply finite_sum_rev.
Qed.

(** [batch_mean_rev] (theorem).
 Mathematical meaning: The weighted mean is invariant under reversing a finite list.
 Exact proposition: forall (A:Type) (w v:A->R) (xs:list A), batch_mean w v (rev xs)=batch_mean w v xs.
 Premises and side conditions: Finite input lists and all positive mass, sign, and sample-size hypotheses are stated where required. Observations and weights are numerical data rather than random variables.
 Proof/definition method: Compose the canonical FiniteSum algebra, the already established weighted moment identities and ordinary Rocq real field/ring/order lemmas.
 Library reuse: Rocq Stdlib Reals, List, Sorting.Permutation, Ring, Field, Lra, Psatz and canonical FiniteSum/PooledMomentsAlgebra; no recursive duplicate integrator or hidden statistical assumptions.
 Boundary: Deterministic arbitrary-list pooling supports report sm:pooling (G12), but does not by itself prove the report's independent-binomial summation, a chi-square pivot, Gaussianity or coverage.
*)
Theorem batch_mean_rev :
  forall (A:Type) (w v:A->R) (xs:list A), batch_mean w v (rev xs)=batch_mean w v xs.
Proof.
  intros A w v xs; unfold batch_mean; now rewrite batch_total_rev,batch_mass_rev.
Qed.

(** [batch_mass_zero_characterization] (theorem).
 Mathematical meaning: A finite sum of nonnegative weights is zero precisely when every enumerated weight is zero.
 Exact proposition: forall (A:Type) (w:A->R) (xs:list A), (forall x, In x xs -> 0<=w x) -> (batch_mass w xs=0 <-> forall x, In x xs -> w x=0).
 Premises and side conditions: Finite input lists and all positive mass, sign, and sample-size hypotheses are stated where required. Observations and weights are numerical data rather than random variables.
 Proof/definition method: Compose the canonical FiniteSum algebra, the already established weighted moment identities and ordinary Rocq real field/ring/order lemmas.
 Library reuse: Rocq Stdlib Reals, List, Sorting.Permutation, Ring, Field, Lra, Psatz and canonical FiniteSum/PooledMomentsAlgebra; no recursive duplicate integrator or hidden statistical assumptions.
 Boundary: Deterministic arbitrary-list pooling supports report sm:pooling (G12), but does not by itself prove the report's independent-binomial summation, a chi-square pivot, Gaussianity or coverage.
*)
Theorem batch_mass_zero_characterization :
  forall (A:Type) (w:A->R) (xs:list A), (forall x, In x xs -> 0<=w x) -> (batch_mass w xs=0 <-> forall x, In x xs -> w x=0).
Proof.
  intros A w xs Hw; unfold batch_mass; now apply finite_sum_nonnegative_zero_iff.
Qed.

(** [batch_mass_constant_weights] (theorem).
 Mathematical meaning: Constant batch weights result in the exact list-length scaling of mass.
 Exact proposition: forall (A:Type) (xs:list A) (c:R), batch_mass (fun _=>c) xs=INR (length xs)*c.
 Premises and side conditions: Finite input lists and all positive mass, sign, and sample-size hypotheses are stated where required. Observations and weights are numerical data rather than random variables.
 Proof/definition method: Compose the canonical FiniteSum algebra, the already established weighted moment identities and ordinary Rocq real field/ring/order lemmas.
 Library reuse: Rocq Stdlib Reals, List, Sorting.Permutation, Ring, Field, Lra, Psatz and canonical FiniteSum/PooledMomentsAlgebra; no recursive duplicate integrator or hidden statistical assumptions.
 Boundary: Deterministic arbitrary-list pooling supports report sm:pooling (G12), but does not by itself prove the report's independent-binomial summation, a chi-square pivot, Gaussianity or coverage.
*)
Theorem batch_mass_constant_weights :
  forall (A:Type) (xs:list A) (c:R), batch_mass (fun _=>c) xs=INR (length xs)*c.
Proof.
  intros A xs c; unfold batch_mass; apply finite_sum_const.
Qed.

(** [batch_total_nonnegative] (theorem).
 Mathematical meaning: Weights and group values that are each nonnegative yield a nonnegative pooled first moment.
 Exact proposition: forall (A:Type) (w v:A->R) (xs:list A), (forall x, In x xs -> 0<=w x) -> (forall x, In x xs -> 0<=v x) -> 0<=batch_total w v xs.
 Premises and side conditions: Finite input lists and all positive mass, sign, and sample-size hypotheses are stated where required. Observations and weights are numerical data rather than random variables.
 Proof/definition method: Compose the canonical FiniteSum algebra, the already established weighted moment identities and ordinary Rocq real field/ring/order lemmas.
 Library reuse: Rocq Stdlib Reals, List, Sorting.Permutation, Ring, Field, Lra, Psatz and canonical FiniteSum/PooledMomentsAlgebra; no recursive duplicate integrator or hidden statistical assumptions.
 Boundary: Deterministic arbitrary-list pooling supports report sm:pooling (G12), but does not by itself prove the report's independent-binomial summation, a chi-square pivot, Gaussianity or coverage.
*)
Theorem batch_total_nonnegative :
  forall (A:Type) (w v:A->R) (xs:list A), (forall x, In x xs -> 0<=w x) -> (forall x, In x xs -> 0<=v x) -> 0<=batch_total w v xs.
Proof.
  intros A w v xs Hw Hv; unfold batch_total; apply finite_sum_nonnegative; intros x Hin; apply Rmult_le_pos; [apply Hw|apply Hv]; exact Hin.
Qed.

(** [batch_total_monotone_values] (theorem).
 Mathematical meaning: With nonnegative sample weights, increasing every group value cannot decrease its weighted total.
 Exact proposition: forall (A:Type) (w v z:A->R) (xs:list A), (forall x, In x xs -> 0<=w x) -> (forall x, In x xs -> v x<=z x) -> batch_total w v xs<=batch_total w z xs.
 Premises and side conditions: Finite input lists and all positive mass, sign, and sample-size hypotheses are stated where required. Observations and weights are numerical data rather than random variables.
 Proof/definition method: Compose the canonical FiniteSum algebra, the already established weighted moment identities and ordinary Rocq real field/ring/order lemmas.
 Library reuse: Rocq Stdlib Reals, List, Sorting.Permutation, Ring, Field, Lra, Psatz and canonical FiniteSum/PooledMomentsAlgebra; no recursive duplicate integrator or hidden statistical assumptions.
 Boundary: Deterministic arbitrary-list pooling supports report sm:pooling (G12), but does not by itself prove the report's independent-binomial summation, a chi-square pivot, Gaussianity or coverage.
*)
Theorem batch_total_monotone_values :
  forall (A:Type) (w v z:A->R) (xs:list A), (forall x, In x xs -> 0<=w x) -> (forall x, In x xs -> v x<=z x) -> batch_total w v xs<=batch_total w z xs.
Proof.
  intros A w v z xs Hw Hle; unfold batch_total; apply finite_sum_monotone; intros x Hin; pose proof (Hw x Hin) as Hwx; pose proof (Hle x Hin) as Hx; nra.
Qed.

(** [batch_mean_monotone_values] (theorem).
 Mathematical meaning: The pooled mean is monotone in the group observations when total sample exposure is positive.
 Exact proposition: forall (A:Type) (w v z:A->R) (xs:list A), 0<batch_mass w xs -> (forall x, In x xs -> 0<=w x) -> (forall x, In x xs -> v x<=z x) -> batch_mean w v xs<=batch_mean w z xs.
 Premises and side conditions: Finite input lists and all positive mass, sign, and sample-size hypotheses are stated where required. Observations and weights are numerical data rather than random variables.
 Proof/definition method: Compose the canonical FiniteSum algebra, the already established weighted moment identities and ordinary Rocq real field/ring/order lemmas.
 Library reuse: Rocq Stdlib Reals, List, Sorting.Permutation, Ring, Field, Lra, Psatz and canonical FiniteSum/PooledMomentsAlgebra; no recursive duplicate integrator or hidden statistical assumptions.
 Boundary: Deterministic arbitrary-list pooling supports report sm:pooling (G12), but does not by itself prove the report's independent-binomial summation, a chi-square pivot, Gaussianity or coverage.
*)
Theorem batch_mean_monotone_values :
  forall (A:Type) (w v z:A->R) (xs:list A), 0<batch_mass w xs -> (forall x, In x xs -> 0<=w x) -> (forall x, In x xs -> v x<=z x) -> batch_mean w v xs<=batch_mean w z xs.
Proof.
  intros A w v z xs Hm Hw Hle; pose proof (batch_total_monotone_values A w v z xs Hw Hle) as Ht; rewrite (batch_mean_total_identity A w v xs) in Ht by lra; rewrite (batch_mean_total_identity A w z xs) in Ht by lra; nra.
Qed.

(** [batch_mean_lower_bound] (theorem).
 Mathematical meaning: A sample-size-weighted average cannot fall below a lower bound satisfied by every batch value.
 Exact proposition: forall (A:Type) (w v:A->R) (xs:list A) (a:R), 0<batch_mass w xs -> (forall x, In x xs -> 0<=w x) -> (forall x, In x xs -> a<=v x) -> a<=batch_mean w v xs.
 Premises and side conditions: Finite input lists and all positive mass, sign, and sample-size hypotheses are stated where required. Observations and weights are numerical data rather than random variables.
 Proof/definition method: Compose the canonical FiniteSum algebra, the already established weighted moment identities and ordinary Rocq real field/ring/order lemmas.
 Library reuse: Rocq Stdlib Reals, List, Sorting.Permutation, Ring, Field, Lra, Psatz and canonical FiniteSum/PooledMomentsAlgebra; no recursive duplicate integrator or hidden statistical assumptions.
 Boundary: Deterministic arbitrary-list pooling supports report sm:pooling (G12), but does not by itself prove the report's independent-binomial summation, a chi-square pivot, Gaussianity or coverage.
*)
Theorem batch_mean_lower_bound :
  forall (A:Type) (w v:A->R) (xs:list A) (a:R), 0<batch_mass w xs -> (forall x, In x xs -> 0<=w x) -> (forall x, In x xs -> a<=v x) -> a<=batch_mean w v xs.
Proof.
  intros A w v xs a Hm Hw Hlo; pose proof (batch_mean_monotone_values A w (fun _=>a) v xs Hm Hw Hlo) as H; rewrite (batch_mean_constant A w xs a) in H by lra; exact H.
Qed.

(** [batch_mean_upper_bound] (theorem).
 Mathematical meaning: A weighted mean cannot exceed a common upper bound on its sample groups.
 Exact proposition: forall (A:Type) (w v:A->R) (xs:list A) (b:R), 0<batch_mass w xs -> (forall x, In x xs -> 0<=w x) -> (forall x, In x xs -> v x<=b) -> batch_mean w v xs<=b.
 Premises and side conditions: Finite input lists and all positive mass, sign, and sample-size hypotheses are stated where required. Observations and weights are numerical data rather than random variables.
 Proof/definition method: Compose the canonical FiniteSum algebra, the already established weighted moment identities and ordinary Rocq real field/ring/order lemmas.
 Library reuse: Rocq Stdlib Reals, List, Sorting.Permutation, Ring, Field, Lra, Psatz and canonical FiniteSum/PooledMomentsAlgebra; no recursive duplicate integrator or hidden statistical assumptions.
 Boundary: Deterministic arbitrary-list pooling supports report sm:pooling (G12), but does not by itself prove the report's independent-binomial summation, a chi-square pivot, Gaussianity or coverage.
*)
Theorem batch_mean_upper_bound :
  forall (A:Type) (w v:A->R) (xs:list A) (b:R), 0<batch_mass w xs -> (forall x, In x xs -> 0<=w x) -> (forall x, In x xs -> v x<=b) -> batch_mean w v xs<=b.
Proof.
  intros A w v xs b Hm Hw Hup; pose proof (batch_mean_monotone_values A w v (fun _=>b) xs Hm Hw Hup) as H; rewrite (batch_mean_constant A w xs b) in H by lra; exact H.
Qed.

(** [batch_mean_interval] (theorem).
 Mathematical meaning: If every group value belongs to an interval, the weighted mean belongs to that interval.
 Exact proposition: forall (A:Type) (w v:A->R) (xs:list A) (a b:R), 0<batch_mass w xs -> (forall x, In x xs -> 0<=w x) -> (forall x, In x xs -> a<=v x<=b) -> a<=batch_mean w v xs<=b.
 Premises and side conditions: Finite input lists and all positive mass, sign, and sample-size hypotheses are stated where required. Observations and weights are numerical data rather than random variables.
 Proof/definition method: Compose the canonical FiniteSum algebra, the already established weighted moment identities and ordinary Rocq real field/ring/order lemmas.
 Library reuse: Rocq Stdlib Reals, List, Sorting.Permutation, Ring, Field, Lra, Psatz and canonical FiniteSum/PooledMomentsAlgebra; no recursive duplicate integrator or hidden statistical assumptions.
 Boundary: Deterministic arbitrary-list pooling supports report sm:pooling (G12), but does not by itself prove the report's independent-binomial summation, a chi-square pivot, Gaussianity or coverage.
*)
Theorem batch_mean_interval :
  forall (A:Type) (w v:A->R) (xs:list A) (a b:R), 0<batch_mass w xs -> (forall x, In x xs -> 0<=w x) -> (forall x, In x xs -> a<=v x<=b) -> a<=batch_mean w v xs<=b.
Proof.
  intros A w v xs a b Hm Hw Hr; split; [apply batch_mean_lower_bound with (a:=a); try assumption; intros x Hin; apply (Hr x Hin)|apply batch_mean_upper_bound with (b:=b); try assumption; intros x Hin; apply (Hr x Hin)].
Qed.

(** [batch_pairwise_nonnegative] (theorem).
 Mathematical meaning: Every weighted pairwise contrast-squared term is nonnegative when the group weights are nonnegative.
 Exact proposition: forall (A:Type) (w v:A->R) (xs:list A), (forall x, In x xs -> 0<=w x) -> 0<=batch_pairwise w v xs.
 Premises and side conditions: Finite input lists and all positive mass, sign, and sample-size hypotheses are stated where required. Observations and weights are numerical data rather than random variables.
 Proof/definition method: Compose the canonical FiniteSum algebra, the already established weighted moment identities and ordinary Rocq real field/ring/order lemmas.
 Library reuse: Rocq Stdlib Reals, List, Sorting.Permutation, Ring, Field, Lra, Psatz and canonical FiniteSum/PooledMomentsAlgebra; no recursive duplicate integrator or hidden statistical assumptions.
 Boundary: Deterministic arbitrary-list pooling supports report sm:pooling (G12), but does not by itself prove the report's independent-binomial summation, a chi-square pivot, Gaussianity or coverage.
*)
Theorem batch_pairwise_nonnegative :
  forall (A:Type) (w v:A->R) (xs:list A), (forall x, In x xs -> 0<=w x) -> 0<=batch_pairwise w v xs.
Proof.
  intros A w v xs Hw; unfold batch_pairwise; apply finite_sum_nonnegative; intros i Hi; apply finite_sum_nonnegative; intros j Hj; replace (w i*w j*(v i-v j)*(v i-v j)) with ((w i*w j)*((v i-v j)*(v i-v j))) by ring; apply Rmult_le_pos; [apply Rmult_le_pos; [apply Hw; exact Hi|apply Hw; exact Hj]|pose proof (Rle_0_sqr (v i-v j)) as E; unfold Rsqr in E; exact E].
Qed.

(** [batch_pairwise_closed] (theorem).
 Mathematical meaning: The all-pairs weighted squared-difference statistic equals twice mass times second moment minus twice squared first moment.
 Exact proposition: forall (A:Type) (w v:A->R) (xs:list A), batch_pairwise w v xs=2*(batch_mass w xs*batch_second w v xs-batch_total w v xs*batch_total w v xs).
 Premises and side conditions: Finite input lists and all positive mass, sign, and sample-size hypotheses are stated where required. Observations and weights are numerical data rather than random variables.
 Proof/definition method: Compose the canonical FiniteSum algebra, the already established weighted moment identities and ordinary Rocq real field/ring/order lemmas.
 Library reuse: Rocq Stdlib Reals, List, Sorting.Permutation, Ring, Field, Lra, Psatz and canonical FiniteSum/PooledMomentsAlgebra; no recursive duplicate integrator or hidden statistical assumptions.
 Boundary: Deterministic arbitrary-list pooling supports report sm:pooling (G12), but does not by itself prove the report's independent-binomial summation, a chi-square pivot, Gaussianity or coverage.
*)
Theorem batch_pairwise_closed :
  forall (A:Type) (w v:A->R) (xs:list A), batch_pairwise w v xs=2*(batch_mass w xs*batch_second w v xs-batch_total w v xs*batch_total w v xs).
Proof.
  intros A w v xs; unfold batch_pairwise; transitivity (finite_sum (fun i=>w i*batch_centered w v (v i) xs) xs). { apply finite_sum_ext; intro i; unfold batch_centered; transitivity (finite_sum (fun j=>w i*(w j*(v j-v i)*(v j-v i))) xs); [apply finite_sum_ext; intro j; ring|rewrite finite_sum_scale; reflexivity]. } transitivity (finite_sum (fun i=>(batch_second w v xs*w i-(2*batch_total w v xs)*(w i*v i))+batch_mass w xs*(w i*v i*v i)) xs). { apply finite_sum_ext; intro i; rewrite batch_centered_expand; ring. } rewrite finite_sum_add, finite_sum_sub, !finite_sum_scale; unfold batch_mass,batch_second,batch_total; ring.
Qed.

(** [batch_pairwise_mean_bridge] (theorem).
 Mathematical meaning: For nonzero total mass, twice mass times mean-centered dispersion exactly equals the weighted all-pairs squared discrepancy.
 Exact proposition: forall (A:Type) (w v:A->R) (xs:list A), batch_mass w xs<>0 -> batch_pairwise w v xs=2*batch_mass w xs*batch_centered w v (batch_mean w v xs) xs.
 Premises and side conditions: Finite input lists and all positive mass, sign, and sample-size hypotheses are stated where required. Observations and weights are numerical data rather than random variables.
 Proof/definition method: Compose the canonical FiniteSum algebra, the already established weighted moment identities and ordinary Rocq real field/ring/order lemmas.
 Library reuse: Rocq Stdlib Reals, List, Sorting.Permutation, Ring, Field, Lra, Psatz and canonical FiniteSum/PooledMomentsAlgebra; no recursive duplicate integrator or hidden statistical assumptions.
 Boundary: Deterministic arbitrary-list pooling supports report sm:pooling (G12), but does not by itself prove the report's independent-binomial summation, a chi-square pivot, Gaussianity or coverage.
*)
Theorem batch_pairwise_mean_bridge :
  forall (A:Type) (w v:A->R) (xs:list A), batch_mass w xs<>0 -> batch_pairwise w v xs=2*batch_mass w xs*batch_centered w v (batch_mean w v xs) xs.
Proof.
  intros A w v xs H; rewrite batch_pairwise_closed, batch_centered_at_mean_closed by assumption; field; exact H.
Qed.

(** [batch_mean_append_two_groups] (theorem).
 Mathematical meaning: The mean over any concatenation is exactly the earlier two-group pooled mean computed from both list summaries.
 Exact proposition: forall (A:Type) (w v:A->R) (xs ys:list A), 0<batch_mass w xs -> 0<batch_mass w ys -> batch_mean w v (xs++ys)=pooled_mean (batch_mass w xs) (batch_mass w ys) (batch_mean w v xs) (batch_mean w v ys).
 Premises and side conditions: Finite input lists and all positive mass, sign, and sample-size hypotheses are stated where required. Observations and weights are numerical data rather than random variables.
 Proof/definition method: Compose the canonical FiniteSum algebra, the already established weighted moment identities and ordinary Rocq real field/ring/order lemmas.
 Library reuse: Rocq Stdlib Reals, List, Sorting.Permutation, Ring, Field, Lra, Psatz and canonical FiniteSum/PooledMomentsAlgebra; no recursive duplicate integrator or hidden statistical assumptions.
 Boundary: Deterministic arbitrary-list pooling supports report sm:pooling (G12), but does not by itself prove the report's independent-binomial summation, a chi-square pivot, Gaussianity or coverage.
*)
Theorem batch_mean_append_two_groups :
  forall (A:Type) (w v:A->R) (xs ys:list A), 0<batch_mass w xs -> 0<batch_mass w ys -> batch_mean w v (xs++ys)=pooled_mean (batch_mass w xs) (batch_mass w ys) (batch_mean w v xs) (batch_mean w v ys).
Proof.
  intros A w v xs ys Hx Hy; unfold batch_mean,pooled_mean,pooled_mass; rewrite batch_total_app,batch_mass_app; field; lra.
Qed.

(** [batch_centered_append_anova] (theorem).
 Mathematical meaning: Exact arbitrary-list two-block ANOVA: the pooled between-batch sum equals both sublist dispersions plus the between-sublist correction.
 Exact proposition: forall (A:Type) (w v:A->R) (xs ys:list A), 0<batch_mass w xs -> 0<batch_mass w ys -> batch_centered w v (batch_mean w v (xs++ys)) (xs++ys)=batch_centered w v (batch_mean w v xs) xs+batch_centered w v (batch_mean w v ys) ys+pooled_between (batch_mass w xs) (batch_mass w ys) (batch_mean w v xs) (batch_mean w v ys).
 Premises and side conditions: Finite input lists and all positive mass, sign, and sample-size hypotheses are stated where required. Observations and weights are numerical data rather than random variables.
 Proof/definition method: Compose the canonical FiniteSum algebra, the already established weighted moment identities and ordinary Rocq real field/ring/order lemmas.
 Library reuse: Rocq Stdlib Reals, List, Sorting.Permutation, Ring, Field, Lra, Psatz and canonical FiniteSum/PooledMomentsAlgebra; no recursive duplicate integrator or hidden statistical assumptions.
 Boundary: Deterministic arbitrary-list pooling supports report sm:pooling (G12), but does not by itself prove the report's independent-binomial summation, a chi-square pivot, Gaussianity or coverage.
*)
Theorem batch_centered_append_anova :
  forall (A:Type) (w v:A->R) (xs ys:list A), 0<batch_mass w xs -> 0<batch_mass w ys -> batch_centered w v (batch_mean w v (xs++ys)) (xs++ys)=batch_centered w v (batch_mean w v xs) xs+batch_centered w v (batch_mean w v ys) ys+pooled_between (batch_mass w xs) (batch_mass w ys) (batch_mean w v xs) (batch_mean w v ys).
Proof.
  intros A w v xs ys Hx Hy; rewrite batch_centered_app; rewrite (batch_centered_mean_correction A w v xs (batch_mean w v (xs++ys))) by lra; rewrite (batch_centered_mean_correction A w v ys (batch_mean w v (xs++ys))) by lra; rewrite (batch_mean_append_two_groups A w v xs ys Hx Hy); unfold pooled_between,pooled_mean,pooled_mass; field; lra.
Qed.

(** [batch_total_ss_append_anova] (theorem).
 Mathematical meaning: Exact arbitrary-list pooling of within-plus-between corrected sums matches the two-group ANOVA correction.
 Exact proposition: forall (A:Type) (w v u:A->R) (xs ys:list A), 0<batch_mass w xs -> 0<batch_mass w ys -> batch_total_ss w v u (xs++ys)=batch_total_ss w v u xs+batch_total_ss w v u ys+pooled_between (batch_mass w xs) (batch_mass w ys) (batch_mean w v xs) (batch_mean w v ys).
 Premises and side conditions: Finite input lists and all positive mass, sign, and sample-size hypotheses are stated where required. Observations and weights are numerical data rather than random variables.
 Proof/definition method: Compose the canonical FiniteSum algebra, the already established weighted moment identities and ordinary Rocq real field/ring/order lemmas.
 Library reuse: Rocq Stdlib Reals, List, Sorting.Permutation, Ring, Field, Lra, Psatz and canonical FiniteSum/PooledMomentsAlgebra; no recursive duplicate integrator or hidden statistical assumptions.
 Boundary: Deterministic arbitrary-list pooling supports report sm:pooling (G12), but does not by itself prove the report's independent-binomial summation, a chi-square pivot, Gaussianity or coverage.
*)
Theorem batch_total_ss_append_anova :
  forall (A:Type) (w v u:A->R) (xs ys:list A), 0<batch_mass w xs -> 0<batch_mass w ys -> batch_total_ss w v u (xs++ys)=batch_total_ss w v u xs+batch_total_ss w v u ys+pooled_between (batch_mass w xs) (batch_mass w ys) (batch_mean w v xs) (batch_mean w v ys).
Proof.
  intros A w v u xs ys Hx Hy; unfold batch_total_ss; rewrite finite_sum_app; rewrite (batch_centered_append_anova A w v xs ys Hx Hy); ring.
Qed.

(** [batch_total_ss_within_lower] (theorem).
 Mathematical meaning: For nonnegative sample weights, total corrected sum of squares dominates all supplied within-group sums.
 Exact proposition: forall (A:Type) (w v u:A->R) (xs:list A), (forall x, In x xs -> 0<=w x) -> finite_sum u xs<=batch_total_ss w v u xs.
 Premises and side conditions: Finite input lists and all positive mass, sign, and sample-size hypotheses are stated where required. Observations and weights are numerical data rather than random variables.
 Proof/definition method: Compose the canonical FiniteSum algebra, the already established weighted moment identities and ordinary Rocq real field/ring/order lemmas.
 Library reuse: Rocq Stdlib Reals, List, Sorting.Permutation, Ring, Field, Lra, Psatz and canonical FiniteSum/PooledMomentsAlgebra; no recursive duplicate integrator or hidden statistical assumptions.
 Boundary: Deterministic arbitrary-list pooling supports report sm:pooling (G12), but does not by itself prove the report's independent-binomial summation, a chi-square pivot, Gaussianity or coverage.
*)
Theorem batch_total_ss_within_lower :
  forall (A:Type) (w v u:A->R) (xs:list A), (forall x, In x xs -> 0<=w x) -> finite_sum u xs<=batch_total_ss w v u xs.
Proof.
  intros A w v u xs Hw; unfold batch_total_ss; pose proof (batch_centered_nonnegative A w v (batch_mean w v xs) xs Hw); lra.
Qed.

(** [batch_unbiased_variance_nonnegative] (theorem).
 Mathematical meaning: Positive degrees of freedom and nonnegative within/between components imply nonnegative unbiased-style pooled variance.
 Exact proposition: forall (A:Type) (w v u:A->R) (xs:list A), 1<batch_mass w xs -> (forall x, In x xs -> 0<=w x) -> (forall x, In x xs -> 0<=u x) -> 0<=batch_unbiased_variance w v u xs.
 Premises and side conditions: Finite input lists and all positive mass, sign, and sample-size hypotheses are stated where required. Observations and weights are numerical data rather than random variables.
 Proof/definition method: Compose the canonical FiniteSum algebra, the already established weighted moment identities and ordinary Rocq real field/ring/order lemmas.
 Library reuse: Rocq Stdlib Reals, List, Sorting.Permutation, Ring, Field, Lra, Psatz and canonical FiniteSum/PooledMomentsAlgebra; no recursive duplicate integrator or hidden statistical assumptions.
 Boundary: Deterministic arbitrary-list pooling supports report sm:pooling (G12), but does not by itself prove the report's independent-binomial summation, a chi-square pivot, Gaussianity or coverage.
*)
Theorem batch_unbiased_variance_nonnegative :
  forall (A:Type) (w v u:A->R) (xs:list A), 1<batch_mass w xs -> (forall x, In x xs -> 0<=w x) -> (forall x, In x xs -> 0<=u x) -> 0<=batch_unbiased_variance w v u xs.
Proof.
  intros A w v u xs Hm Hw Hu; unfold batch_unbiased_variance,Rdiv; apply Rmult_le_pos; [apply batch_total_ss_nonnegative; assumption|apply Rlt_le, Rinv_0_lt_compat; lra].
Qed.

(** [batch_unbiased_variance_translation] (theorem).
 Mathematical meaning: Translating every group center leaves pooled unbiased-style sample variance unchanged.
 Exact proposition: forall (A:Type) (w v u:A->R) (xs:list A) (t:R), batch_mass w xs<>0 -> batch_unbiased_variance w (fun x=>v x+t) u xs=batch_unbiased_variance w v u xs.
 Premises and side conditions: Finite input lists and all positive mass, sign, and sample-size hypotheses are stated where required. Observations and weights are numerical data rather than random variables.
 Proof/definition method: Compose the canonical FiniteSum algebra, the already established weighted moment identities and ordinary Rocq real field/ring/order lemmas.
 Library reuse: Rocq Stdlib Reals, List, Sorting.Permutation, Ring, Field, Lra, Psatz and canonical FiniteSum/PooledMomentsAlgebra; no recursive duplicate integrator or hidden statistical assumptions.
 Boundary: Deterministic arbitrary-list pooling supports report sm:pooling (G12), but does not by itself prove the report's independent-binomial summation, a chi-square pivot, Gaussianity or coverage.
*)
Theorem batch_unbiased_variance_translation :
  forall (A:Type) (w v u:A->R) (xs:list A) (t:R), batch_mass w xs<>0 -> batch_unbiased_variance w (fun x=>v x+t) u xs=batch_unbiased_variance w v u xs.
Proof.
  intros A w v u xs t H; unfold batch_unbiased_variance; rewrite batch_total_ss_translation by assumption; reflexivity.
Qed.

(** [batch_unbiased_variance_scale] (theorem).
 Mathematical meaning: Rescaling all observations by a factor scales the pooled unbiased-style variance quadratically.
 Exact proposition: forall (A:Type) (w v u:A->R) (xs:list A) (t:R), batch_mass w xs<>0 -> batch_unbiased_variance w (fun x=>t*v x) (fun x=>(t*t)*u x) xs=t*t*batch_unbiased_variance w v u xs.
 Premises and side conditions: Finite input lists and all positive mass, sign, and sample-size hypotheses are stated where required. Observations and weights are numerical data rather than random variables.
 Proof/definition method: Compose the canonical FiniteSum algebra, the already established weighted moment identities and ordinary Rocq real field/ring/order lemmas.
 Library reuse: Rocq Stdlib Reals, List, Sorting.Permutation, Ring, Field, Lra, Psatz and canonical FiniteSum/PooledMomentsAlgebra; no recursive duplicate integrator or hidden statistical assumptions.
 Boundary: Deterministic arbitrary-list pooling supports report sm:pooling (G12), but does not by itself prove the report's independent-binomial summation, a chi-square pivot, Gaussianity or coverage.
*)
Theorem batch_unbiased_variance_scale :
  forall (A:Type) (w v u:A->R) (xs:list A) (t:R), batch_mass w xs<>0 -> batch_unbiased_variance w (fun x=>t*v x) (fun x=>(t*t)*u x) xs=t*t*batch_unbiased_variance w v u xs.
Proof.
  intros A w v u xs t H; unfold batch_unbiased_variance; rewrite batch_total_ss_scale by assumption; unfold Rdiv; ring.
Qed.

(** [batch_second_mean_lower_bound] (theorem).
 Mathematical meaning: For nonnegative weights and positive total exposure, weighted second moment bounds mass times squared pooled mean.
 Exact proposition: forall (A:Type) (w v:A->R) (xs:list A), 0<batch_mass w xs -> (forall x, In x xs -> 0<=w x) -> batch_mass w xs*batch_mean w v xs*batch_mean w v xs<=batch_second w v xs.
 Premises and side conditions: Finite input lists and all positive mass, sign, and sample-size hypotheses are stated where required. Observations and weights are numerical data rather than random variables.
 Proof/definition method: Compose the canonical FiniteSum algebra, the already established weighted moment identities and ordinary Rocq real field/ring/order lemmas.
 Library reuse: Rocq Stdlib Reals, List, Sorting.Permutation, Ring, Field, Lra, Psatz and canonical FiniteSum/PooledMomentsAlgebra; no recursive duplicate integrator or hidden statistical assumptions.
 Boundary: Deterministic arbitrary-list pooling supports report sm:pooling (G12), but does not by itself prove the report's independent-binomial summation, a chi-square pivot, Gaussianity or coverage.
*)
Theorem batch_second_mean_lower_bound :
  forall (A:Type) (w v:A->R) (xs:list A), 0<batch_mass w xs -> (forall x, In x xs -> 0<=w x) -> batch_mass w xs*batch_mean w v xs*batch_mean w v xs<=batch_second w v xs.
Proof.
  intros A w v xs Hm Hw; pose proof (batch_centered_nonnegative A w v (batch_mean w v xs) xs Hw) as E; rewrite batch_centered_expand in E; rewrite (batch_mean_total_identity A w v xs) in E by lra; nra.
Qed.

(** [batch_failure] (definition).
 Mathematical meaning: Ideal failure count target obtained by summing the cohort-wise complements of success probabilities.
 Exact declaration: Definition batch_failure {A:Type} (w p:A->R) (xs:list A):R := batch_total w (fun x=>1-p x) xs.
 Premises and side conditions: Every member-weight, parameter-domain or nonzero-denominator requirement is explicit. Statements concern ideal, input-supplied Bernoulli moment targets, not a derived independent-trial probability model.
 Proof/definition method: Use the canonical SamplingPrecision variance factor and finite_sum linearity, positive-term arguments, exact weighted ANOVA and Rocq field/ring normalization.
 Library reuse: Rocq Stdlib List/Reals/Lra/Psatz/Ring/Field and existing FiniteSum, SamplingPrecision, ListPoolingAlgebra; no duplicated scalar Bernoulli implementation or random-count generator.
 Boundary: Supports the heterogeneous-rate algebra of reports sm:binomial/sm:rare and Towers admissions. No binomial PMF, independent trials, conditional-count law, chi-square pivot, or confidence coverage is proved.
*)
Definition batch_failure {A:Type} (w p:A->R) (xs:list A):R := batch_total w (fun x=>1-p x) xs.

(** [batch_bernoulli_variance] (definition).
 Mathematical meaning: Ideal heterogeneous Bernoulli count variance target, reusing SamplingPrecision rather than redefining p(1-p).
 Exact declaration: Definition batch_bernoulli_variance {A:Type} (w p:A->R) (xs:list A):R := finite_sum (fun x => w x*sampling_bernoulli_variance (p x)) xs.
 Premises and side conditions: Every member-weight, parameter-domain or nonzero-denominator requirement is explicit. Statements concern ideal, input-supplied Bernoulli moment targets, not a derived independent-trial probability model.
 Proof/definition method: Use the canonical SamplingPrecision variance factor and finite_sum linearity, positive-term arguments, exact weighted ANOVA and Rocq field/ring normalization.
 Library reuse: Rocq Stdlib List/Reals/Lra/Psatz/Ring/Field and existing FiniteSum, SamplingPrecision, ListPoolingAlgebra; no duplicated scalar Bernoulli implementation or random-count generator.
 Boundary: Supports the heterogeneous-rate algebra of reports sm:binomial/sm:rare and Towers admissions. No binomial PMF, independent trials, conditional-count law, chi-square pivot, or confidence coverage is proved.
*)
Definition batch_bernoulli_variance {A:Type} (w p:A->R) (xs:list A):R := finite_sum (fun x => w x*sampling_bernoulli_variance (p x)) xs.

(** [batch_failure_app] (theorem).
 Mathematical meaning: Ideal expected failure counts add exactly when two arbitrary cohort lists are joined.
 Exact proposition: forall (A:Type) (w p:A->R) (xs ys:list A), batch_failure w p (xs++ys)=batch_failure w p xs+batch_failure w p ys.
 Premises and side conditions: Every member-weight, parameter-domain or nonzero-denominator requirement is explicit. Statements concern ideal, input-supplied Bernoulli moment targets, not a derived independent-trial probability model.
 Proof/definition method: Use the canonical SamplingPrecision variance factor and finite_sum linearity, positive-term arguments, exact weighted ANOVA and Rocq field/ring normalization.
 Library reuse: Rocq Stdlib List/Reals/Lra/Psatz/Ring/Field and existing FiniteSum, SamplingPrecision, ListPoolingAlgebra; no duplicated scalar Bernoulli implementation or random-count generator.
 Boundary: Supports the heterogeneous-rate algebra of reports sm:binomial/sm:rare and Towers admissions. No binomial PMF, independent trials, conditional-count law, chi-square pivot, or confidence coverage is proved.
*)
Theorem batch_failure_app :
  forall (A:Type) (w p:A->R) (xs ys:list A), batch_failure w p (xs++ys)=batch_failure w p xs+batch_failure w p ys.
Proof.
  intros A w p xs ys; unfold batch_failure; apply batch_total_app.
Qed.

(** [batch_failure_permutation] (theorem).
 Mathematical meaning: Ideal failure counts do not depend on the order of cohorts.
 Exact proposition: forall (A:Type) (w p:A->R) (xs ys:list A), Permutation xs ys -> batch_failure w p xs=batch_failure w p ys.
 Premises and side conditions: Every member-weight, parameter-domain or nonzero-denominator requirement is explicit. Statements concern ideal, input-supplied Bernoulli moment targets, not a derived independent-trial probability model.
 Proof/definition method: Use the canonical SamplingPrecision variance factor and finite_sum linearity, positive-term arguments, exact weighted ANOVA and Rocq field/ring normalization.
 Library reuse: Rocq Stdlib List/Reals/Lra/Psatz/Ring/Field and existing FiniteSum, SamplingPrecision, ListPoolingAlgebra; no duplicated scalar Bernoulli implementation or random-count generator.
 Boundary: Supports the heterogeneous-rate algebra of reports sm:binomial/sm:rare and Towers admissions. No binomial PMF, independent trials, conditional-count law, chi-square pivot, or confidence coverage is proved.
*)
Theorem batch_failure_permutation :
  forall (A:Type) (w p:A->R) (xs ys:list A), Permutation xs ys -> batch_failure w p xs=batch_failure w p ys.
Proof.
  intros A w p xs ys Hp; unfold batch_failure; now apply batch_total_permutation.
Qed.

(** [batch_success_failure_total] (theorem).
 Mathematical meaning: Across arbitrarily many cohorts, ideal successes plus failures equal total cohort exposure.
 Exact proposition: forall (A:Type) (w p:A->R) (xs:list A), batch_total w p xs+batch_failure w p xs=batch_mass w xs.
 Premises and side conditions: Every member-weight, parameter-domain or nonzero-denominator requirement is explicit. Statements concern ideal, input-supplied Bernoulli moment targets, not a derived independent-trial probability model.
 Proof/definition method: Use the canonical SamplingPrecision variance factor and finite_sum linearity, positive-term arguments, exact weighted ANOVA and Rocq field/ring normalization.
 Library reuse: Rocq Stdlib List/Reals/Lra/Psatz/Ring/Field and existing FiniteSum, SamplingPrecision, ListPoolingAlgebra; no duplicated scalar Bernoulli implementation or random-count generator.
 Boundary: Supports the heterogeneous-rate algebra of reports sm:binomial/sm:rare and Towers admissions. No binomial PMF, independent trials, conditional-count law, chi-square pivot, or confidence coverage is proved.
*)
Theorem batch_success_failure_total :
  forall (A:Type) (w p:A->R) (xs:list A), batch_total w p xs+batch_failure w p xs=batch_mass w xs.
Proof.
  intros A w p xs; unfold batch_failure; rewrite <- batch_total_add_values; transitivity (batch_total w (fun _=>1) xs); [unfold batch_total; apply finite_sum_ext; intro x; ring|rewrite batch_total_constant; ring].
Qed.

(** [batch_failure_mass_minus_success] (theorem).
 Mathematical meaning: Ideal failures equal exposure minus ideal successes without restrictions on cohort rates.
 Exact proposition: forall (A:Type) (w p:A->R) (xs:list A), batch_failure w p xs=batch_mass w xs-batch_total w p xs.
 Premises and side conditions: Every member-weight, parameter-domain or nonzero-denominator requirement is explicit. Statements concern ideal, input-supplied Bernoulli moment targets, not a derived independent-trial probability model.
 Proof/definition method: Use the canonical SamplingPrecision variance factor and finite_sum linearity, positive-term arguments, exact weighted ANOVA and Rocq field/ring normalization.
 Library reuse: Rocq Stdlib List/Reals/Lra/Psatz/Ring/Field and existing FiniteSum, SamplingPrecision, ListPoolingAlgebra; no duplicated scalar Bernoulli implementation or random-count generator.
 Boundary: Supports the heterogeneous-rate algebra of reports sm:binomial/sm:rare and Towers admissions. No binomial PMF, independent trials, conditional-count law, chi-square pivot, or confidence coverage is proved.
*)
Theorem batch_failure_mass_minus_success :
  forall (A:Type) (w p:A->R) (xs:list A), batch_failure w p xs=batch_mass w xs-batch_total w p xs.
Proof.
  intros A w p xs; pose proof (batch_success_failure_total A w p xs); lra.
Qed.

(** [batch_failure_nonnegative] (theorem).
 Mathematical meaning: Admissible probabilities and nonnegative cohort weights imply nonnegative expected failures.
 Exact proposition: forall (A:Type) (w p:A->R) (xs:list A), (forall x, In x xs -> 0<=w x) -> (forall x, In x xs -> p x<=1) -> 0<=batch_failure w p xs.
 Premises and side conditions: Every member-weight, parameter-domain or nonzero-denominator requirement is explicit. Statements concern ideal, input-supplied Bernoulli moment targets, not a derived independent-trial probability model.
 Proof/definition method: Use the canonical SamplingPrecision variance factor and finite_sum linearity, positive-term arguments, exact weighted ANOVA and Rocq field/ring normalization.
 Library reuse: Rocq Stdlib List/Reals/Lra/Psatz/Ring/Field and existing FiniteSum, SamplingPrecision, ListPoolingAlgebra; no duplicated scalar Bernoulli implementation or random-count generator.
 Boundary: Supports the heterogeneous-rate algebra of reports sm:binomial/sm:rare and Towers admissions. No binomial PMF, independent trials, conditional-count law, chi-square pivot, or confidence coverage is proved.
*)
Theorem batch_failure_nonnegative :
  forall (A:Type) (w p:A->R) (xs:list A), (forall x, In x xs -> 0<=w x) -> (forall x, In x xs -> p x<=1) -> 0<=batch_failure w p xs.
Proof.
  intros A w p xs Hw Hp; unfold batch_failure; apply batch_total_nonnegative; [exact Hw|intros x Hin; specialize (Hp x Hin); lra].
Qed.

(** [batch_success_nonnegative] (theorem).
 Mathematical meaning: Admissible nonnegative rates and exposure weights imply nonnegative ideal expected success count.
 Exact proposition: forall (A:Type) (w p:A->R) (xs:list A), (forall x, In x xs -> 0<=w x) -> (forall x, In x xs -> 0<=p x) -> 0<=batch_total w p xs.
 Premises and side conditions: Every member-weight, parameter-domain or nonzero-denominator requirement is explicit. Statements concern ideal, input-supplied Bernoulli moment targets, not a derived independent-trial probability model.
 Proof/definition method: Use the canonical SamplingPrecision variance factor and finite_sum linearity, positive-term arguments, exact weighted ANOVA and Rocq field/ring normalization.
 Library reuse: Rocq Stdlib List/Reals/Lra/Psatz/Ring/Field and existing FiniteSum, SamplingPrecision, ListPoolingAlgebra; no duplicated scalar Bernoulli implementation or random-count generator.
 Boundary: Supports the heterogeneous-rate algebra of reports sm:binomial/sm:rare and Towers admissions. No binomial PMF, independent trials, conditional-count law, chi-square pivot, or confidence coverage is proved.
*)
Theorem batch_success_nonnegative :
  forall (A:Type) (w p:A->R) (xs:list A), (forall x, In x xs -> 0<=w x) -> (forall x, In x xs -> 0<=p x) -> 0<=batch_total w p xs.
Proof.
  intros A w p xs Hw Hp; now apply batch_total_nonnegative.
Qed.

(** [batch_bernoulli_variance_app] (theorem).
 Mathematical meaning: Heterogeneous ideal Bernoulli count-variance contributions add over concatenated independent-model cohort summaries.
 Exact proposition: forall (A:Type) (w p:A->R) (xs ys:list A), batch_bernoulli_variance w p (xs++ys)=batch_bernoulli_variance w p xs+batch_bernoulli_variance w p ys.
 Premises and side conditions: Every member-weight, parameter-domain or nonzero-denominator requirement is explicit. Statements concern ideal, input-supplied Bernoulli moment targets, not a derived independent-trial probability model.
 Proof/definition method: Use the canonical SamplingPrecision variance factor and finite_sum linearity, positive-term arguments, exact weighted ANOVA and Rocq field/ring normalization.
 Library reuse: Rocq Stdlib List/Reals/Lra/Psatz/Ring/Field and existing FiniteSum, SamplingPrecision, ListPoolingAlgebra; no duplicated scalar Bernoulli implementation or random-count generator.
 Boundary: Supports the heterogeneous-rate algebra of reports sm:binomial/sm:rare and Towers admissions. No binomial PMF, independent trials, conditional-count law, chi-square pivot, or confidence coverage is proved.
*)
Theorem batch_bernoulli_variance_app :
  forall (A:Type) (w p:A->R) (xs ys:list A), batch_bernoulli_variance w p (xs++ys)=batch_bernoulli_variance w p xs+batch_bernoulli_variance w p ys.
Proof.
  intros A w p xs ys; unfold batch_bernoulli_variance; apply finite_sum_app.
Qed.

(** [batch_bernoulli_variance_permutation] (theorem).
 Mathematical meaning: Cohort ordering cannot change the ideal heterogeneous Bernoulli variance target.
 Exact proposition: forall (A:Type) (w p:A->R) (xs ys:list A), Permutation xs ys -> batch_bernoulli_variance w p xs=batch_bernoulli_variance w p ys.
 Premises and side conditions: Every member-weight, parameter-domain or nonzero-denominator requirement is explicit. Statements concern ideal, input-supplied Bernoulli moment targets, not a derived independent-trial probability model.
 Proof/definition method: Use the canonical SamplingPrecision variance factor and finite_sum linearity, positive-term arguments, exact weighted ANOVA and Rocq field/ring normalization.
 Library reuse: Rocq Stdlib List/Reals/Lra/Psatz/Ring/Field and existing FiniteSum, SamplingPrecision, ListPoolingAlgebra; no duplicated scalar Bernoulli implementation or random-count generator.
 Boundary: Supports the heterogeneous-rate algebra of reports sm:binomial/sm:rare and Towers admissions. No binomial PMF, independent trials, conditional-count law, chi-square pivot, or confidence coverage is proved.
*)
Theorem batch_bernoulli_variance_permutation :
  forall (A:Type) (w p:A->R) (xs ys:list A), Permutation xs ys -> batch_bernoulli_variance w p xs=batch_bernoulli_variance w p ys.
Proof.
  intros A w p xs ys Hp; unfold batch_bernoulli_variance; now apply finite_sum_permutation.
Qed.

(** [batch_bernoulli_variance_scale_weights] (theorem).
 Mathematical meaning: Uniform exposure scaling scales the ideal count variance linearly.
 Exact proposition: forall (A:Type) (w p:A->R) (xs:list A) (t:R), batch_bernoulli_variance (fun x=>t*w x) p xs=t*batch_bernoulli_variance w p xs.
 Premises and side conditions: Every member-weight, parameter-domain or nonzero-denominator requirement is explicit. Statements concern ideal, input-supplied Bernoulli moment targets, not a derived independent-trial probability model.
 Proof/definition method: Use the canonical SamplingPrecision variance factor and finite_sum linearity, positive-term arguments, exact weighted ANOVA and Rocq field/ring normalization.
 Library reuse: Rocq Stdlib List/Reals/Lra/Psatz/Ring/Field and existing FiniteSum, SamplingPrecision, ListPoolingAlgebra; no duplicated scalar Bernoulli implementation or random-count generator.
 Boundary: Supports the heterogeneous-rate algebra of reports sm:binomial/sm:rare and Towers admissions. No binomial PMF, independent trials, conditional-count law, chi-square pivot, or confidence coverage is proved.
*)
Theorem batch_bernoulli_variance_scale_weights :
  forall (A:Type) (w p:A->R) (xs:list A) (t:R), batch_bernoulli_variance (fun x=>t*w x) p xs=t*batch_bernoulli_variance w p xs.
Proof.
  intros A w p xs t; unfold batch_bernoulli_variance; transitivity (finite_sum (fun x=>t*(w x*sampling_bernoulli_variance (p x))) xs); [apply finite_sum_ext; intro x; ring|rewrite finite_sum_scale; reflexivity].
Qed.

(** [batch_bernoulli_variance_complement] (theorem).
 Mathematical meaning: Exchanging successes and failures in every cohort leaves ideal Bernoulli count variance unchanged.
 Exact proposition: forall (A:Type) (w p:A->R) (xs:list A), batch_bernoulli_variance w (fun x=>1-p x) xs=batch_bernoulli_variance w p xs.
 Premises and side conditions: Every member-weight, parameter-domain or nonzero-denominator requirement is explicit. Statements concern ideal, input-supplied Bernoulli moment targets, not a derived independent-trial probability model.
 Proof/definition method: Use the canonical SamplingPrecision variance factor and finite_sum linearity, positive-term arguments, exact weighted ANOVA and Rocq field/ring normalization.
 Library reuse: Rocq Stdlib List/Reals/Lra/Psatz/Ring/Field and existing FiniteSum, SamplingPrecision, ListPoolingAlgebra; no duplicated scalar Bernoulli implementation or random-count generator.
 Boundary: Supports the heterogeneous-rate algebra of reports sm:binomial/sm:rare and Towers admissions. No binomial PMF, independent trials, conditional-count law, chi-square pivot, or confidence coverage is proved.
*)
Theorem batch_bernoulli_variance_complement :
  forall (A:Type) (w p:A->R) (xs:list A), batch_bernoulli_variance w (fun x=>1-p x) xs=batch_bernoulli_variance w p xs.
Proof.
  intros A w p xs; unfold batch_bernoulli_variance; apply finite_sum_ext; intro x; rewrite sampling_variance_complement; reflexivity.
Qed.

(** [batch_bernoulli_variance_as_moments] (theorem).
 Mathematical meaning: Ideal heterogeneous Bernoulli variance equals weighted first raw moment minus weighted second raw moment.
 Exact proposition: forall (A:Type) (w p:A->R) (xs:list A), batch_bernoulli_variance w p xs=batch_total w p xs-batch_second w p xs.
 Premises and side conditions: Every member-weight, parameter-domain or nonzero-denominator requirement is explicit. Statements concern ideal, input-supplied Bernoulli moment targets, not a derived independent-trial probability model.
 Proof/definition method: Use the canonical SamplingPrecision variance factor and finite_sum linearity, positive-term arguments, exact weighted ANOVA and Rocq field/ring normalization.
 Library reuse: Rocq Stdlib List/Reals/Lra/Psatz/Ring/Field and existing FiniteSum, SamplingPrecision, ListPoolingAlgebra; no duplicated scalar Bernoulli implementation or random-count generator.
 Boundary: Supports the heterogeneous-rate algebra of reports sm:binomial/sm:rare and Towers admissions. No binomial PMF, independent trials, conditional-count law, chi-square pivot, or confidence coverage is proved.
*)
Theorem batch_bernoulli_variance_as_moments :
  forall (A:Type) (w p:A->R) (xs:list A), batch_bernoulli_variance w p xs=batch_total w p xs-batch_second w p xs.
Proof.
  intros A w p xs; unfold batch_bernoulli_variance,batch_total,batch_second; transitivity (finite_sum (fun x=>w x*p x-w x*p x*p x) xs); [apply finite_sum_ext; intro x; unfold sampling_bernoulli_variance; ring|rewrite finite_sum_sub; reflexivity].
Qed.

(** [batch_bernoulli_variance_nonnegative] (theorem).
 Mathematical meaning: Every admissible heterogeneous Bernoulli rate and nonnegative weight contributes a nonnegative ideal variance.
 Exact proposition: forall (A:Type) (w p:A->R) (xs:list A), (forall x, In x xs -> 0<=w x) -> (forall x, In x xs -> 0<=p x<=1) -> 0<=batch_bernoulli_variance w p xs.
 Premises and side conditions: Every member-weight, parameter-domain or nonzero-denominator requirement is explicit. Statements concern ideal, input-supplied Bernoulli moment targets, not a derived independent-trial probability model.
 Proof/definition method: Use the canonical SamplingPrecision variance factor and finite_sum linearity, positive-term arguments, exact weighted ANOVA and Rocq field/ring normalization.
 Library reuse: Rocq Stdlib List/Reals/Lra/Psatz/Ring/Field and existing FiniteSum, SamplingPrecision, ListPoolingAlgebra; no duplicated scalar Bernoulli implementation or random-count generator.
 Boundary: Supports the heterogeneous-rate algebra of reports sm:binomial/sm:rare and Towers admissions. No binomial PMF, independent trials, conditional-count law, chi-square pivot, or confidence coverage is proved.
*)
Theorem batch_bernoulli_variance_nonnegative :
  forall (A:Type) (w p:A->R) (xs:list A), (forall x, In x xs -> 0<=w x) -> (forall x, In x xs -> 0<=p x<=1) -> 0<=batch_bernoulli_variance w p xs.
Proof.
  intros A w p xs Hw Hp; unfold batch_bernoulli_variance; apply finite_sum_nonnegative; intros x Hin; apply Rmult_le_pos; [apply Hw; exact Hin|apply sampling_variance_nonnegative; [apply (Hp x Hin)|apply (Hp x Hin)]].
Qed.

(** [batch_bernoulli_deficit_square] (theorem).
 Mathematical meaning: The gap between total exposure and four times ideal Bernoulli variance is a sum of weighted squared rate imbalances.
 Exact proposition: forall (A:Type) (w p:A->R) (xs:list A), batch_mass w xs-4*batch_bernoulli_variance w p xs=finite_sum (fun x=>w x*(2*p x-1)*(2*p x-1)) xs.
 Premises and side conditions: Every member-weight, parameter-domain or nonzero-denominator requirement is explicit. Statements concern ideal, input-supplied Bernoulli moment targets, not a derived independent-trial probability model.
 Proof/definition method: Use the canonical SamplingPrecision variance factor and finite_sum linearity, positive-term arguments, exact weighted ANOVA and Rocq field/ring normalization.
 Library reuse: Rocq Stdlib List/Reals/Lra/Psatz/Ring/Field and existing FiniteSum, SamplingPrecision, ListPoolingAlgebra; no duplicated scalar Bernoulli implementation or random-count generator.
 Boundary: Supports the heterogeneous-rate algebra of reports sm:binomial/sm:rare and Towers admissions. No binomial PMF, independent trials, conditional-count law, chi-square pivot, or confidence coverage is proved.
*)
Theorem batch_bernoulli_deficit_square :
  forall (A:Type) (w p:A->R) (xs:list A), batch_mass w xs-4*batch_bernoulli_variance w p xs=finite_sum (fun x=>w x*(2*p x-1)*(2*p x-1)) xs.
Proof.
  intros A w p xs; unfold batch_mass,batch_bernoulli_variance; rewrite <- (finite_sum_scale xs 4 (fun x=>w x*sampling_bernoulli_variance (p x))); rewrite <- (finite_sum_sub xs w (fun x=>4*(w x*sampling_bernoulli_variance (p x)))); apply finite_sum_ext; intro x; unfold sampling_bernoulli_variance; ring.
Qed.

(** [batch_bernoulli_variance_sharp_quarter] (theorem).
 Mathematical meaning: The total ideal Bernoulli count variance is at most one quarter of nonnegative total sample exposure, even with heterogeneous rates.
 Exact proposition: forall (A:Type) (w p:A->R) (xs:list A), (forall x, In x xs -> 0<=w x) -> 4*batch_bernoulli_variance w p xs<=batch_mass w xs.
 Premises and side conditions: Every member-weight, parameter-domain or nonzero-denominator requirement is explicit. Statements concern ideal, input-supplied Bernoulli moment targets, not a derived independent-trial probability model.
 Proof/definition method: Use the canonical SamplingPrecision variance factor and finite_sum linearity, positive-term arguments, exact weighted ANOVA and Rocq field/ring normalization.
 Library reuse: Rocq Stdlib List/Reals/Lra/Psatz/Ring/Field and existing FiniteSum, SamplingPrecision, ListPoolingAlgebra; no duplicated scalar Bernoulli implementation or random-count generator.
 Boundary: Supports the heterogeneous-rate algebra of reports sm:binomial/sm:rare and Towers admissions. No binomial PMF, independent trials, conditional-count law, chi-square pivot, or confidence coverage is proved.
*)
Theorem batch_bernoulli_variance_sharp_quarter :
  forall (A:Type) (w p:A->R) (xs:list A), (forall x, In x xs -> 0<=w x) -> 4*batch_bernoulli_variance w p xs<=batch_mass w xs.
Proof.
  intros A w p xs Hw; assert (H:0<=batch_mass w xs-4*batch_bernoulli_variance w p xs). { rewrite batch_bernoulli_deficit_square; apply finite_sum_nonnegative; intros x Hin; replace (w x*(2*p x-1)*(2*p x-1)) with (w x*((2*p x-1)*(2*p x-1))) by ring; apply Rmult_le_pos; [apply Hw; exact Hin|pose proof (Rle_0_sqr (2*p x-1)) as E; unfold Rsqr in E; exact E]. } lra.
Qed.

(** [batch_bernoulli_variance_max_attained] (theorem).
 Mathematical meaning: Every cohort rate at one half attains the sharp aggregate one-quarter Bernoulli count variance bound.
 Exact proposition: forall (A:Type) (w p:A->R) (xs:list A), (forall x, In x xs -> p x=1/2) -> 4*batch_bernoulli_variance w p xs=batch_mass w xs.
 Premises and side conditions: Every member-weight, parameter-domain or nonzero-denominator requirement is explicit. Statements concern ideal, input-supplied Bernoulli moment targets, not a derived independent-trial probability model.
 Proof/definition method: Use the canonical SamplingPrecision variance factor and finite_sum linearity, positive-term arguments, exact weighted ANOVA and Rocq field/ring normalization.
 Library reuse: Rocq Stdlib List/Reals/Lra/Psatz/Ring/Field and existing FiniteSum, SamplingPrecision, ListPoolingAlgebra; no duplicated scalar Bernoulli implementation or random-count generator.
 Boundary: Supports the heterogeneous-rate algebra of reports sm:binomial/sm:rare and Towers admissions. No binomial PMF, independent trials, conditional-count law, chi-square pivot, or confidence coverage is proved.
*)
Theorem batch_bernoulli_variance_max_attained :
  forall (A:Type) (w p:A->R) (xs:list A), (forall x, In x xs -> p x=1/2) -> 4*batch_bernoulli_variance w p xs=batch_mass w xs.
Proof.
  intros A w p xs Hp; assert (Hz:batch_mass w xs-4*batch_bernoulli_variance w p xs=0). { rewrite batch_bernoulli_deficit_square; rewrite (finite_sum_ext_in xs (fun x=>w x*(2*p x-1)*(2*p x-1)) (fun _=>0)); [apply finite_sum_zero|intros x Hin; rewrite (Hp x Hin); field; lra]. } lra.
Qed.

(** [batch_bernoulli_variance_le_success] (theorem).
 Mathematical meaning: With nonnegative group weights, ideal Bernoulli count variance never exceeds ideal success count.
 Exact proposition: forall (A:Type) (w p:A->R) (xs:list A), (forall x, In x xs -> 0<=w x) -> batch_bernoulli_variance w p xs<=batch_total w p xs.
 Premises and side conditions: Every member-weight, parameter-domain or nonzero-denominator requirement is explicit. Statements concern ideal, input-supplied Bernoulli moment targets, not a derived independent-trial probability model.
 Proof/definition method: Use the canonical SamplingPrecision variance factor and finite_sum linearity, positive-term arguments, exact weighted ANOVA and Rocq field/ring normalization.
 Library reuse: Rocq Stdlib List/Reals/Lra/Psatz/Ring/Field and existing FiniteSum, SamplingPrecision, ListPoolingAlgebra; no duplicated scalar Bernoulli implementation or random-count generator.
 Boundary: Supports the heterogeneous-rate algebra of reports sm:binomial/sm:rare and Towers admissions. No binomial PMF, independent trials, conditional-count law, chi-square pivot, or confidence coverage is proved.
*)
Theorem batch_bernoulli_variance_le_success :
  forall (A:Type) (w p:A->R) (xs:list A), (forall x, In x xs -> 0<=w x) -> batch_bernoulli_variance w p xs<=batch_total w p xs.
Proof.
  intros A w p xs Hw; rewrite batch_bernoulli_variance_as_moments; pose proof (batch_second_nonnegative A w p xs Hw) as H; lra.
Qed.

(** [batch_bernoulli_variance_le_failure] (theorem).
 Mathematical meaning: With nonnegative weights, ideal Bernoulli variance never exceeds expected failure count.
 Exact proposition: forall (A:Type) (w p:A->R) (xs:list A), (forall x, In x xs -> 0<=w x) -> batch_bernoulli_variance w p xs<=batch_failure w p xs.
 Premises and side conditions: Every member-weight, parameter-domain or nonzero-denominator requirement is explicit. Statements concern ideal, input-supplied Bernoulli moment targets, not a derived independent-trial probability model.
 Proof/definition method: Use the canonical SamplingPrecision variance factor and finite_sum linearity, positive-term arguments, exact weighted ANOVA and Rocq field/ring normalization.
 Library reuse: Rocq Stdlib List/Reals/Lra/Psatz/Ring/Field and existing FiniteSum, SamplingPrecision, ListPoolingAlgebra; no duplicated scalar Bernoulli implementation or random-count generator.
 Boundary: Supports the heterogeneous-rate algebra of reports sm:binomial/sm:rare and Towers admissions. No binomial PMF, independent trials, conditional-count law, chi-square pivot, or confidence coverage is proved.
*)
Theorem batch_bernoulli_variance_le_failure :
  forall (A:Type) (w p:A->R) (xs:list A), (forall x, In x xs -> 0<=w x) -> batch_bernoulli_variance w p xs<=batch_failure w p xs.
Proof.
  intros A w p xs Hw; rewrite <- (batch_bernoulli_variance_complement A w p xs); unfold batch_failure; apply batch_bernoulli_variance_le_success; exact Hw.
Qed.

(** [batch_bernoulli_variance_pooled_decomposition] (theorem).
 Mathematical meaning: Heterogeneous Bernoulli variance plus between-cohort rate dispersion equals the homogeneous-matched-rate variance target.
 Exact proposition: forall (A:Type) (w p:A->R) (xs:list A), 0<batch_mass w xs -> batch_mass w xs*sampling_bernoulli_variance (batch_mean w p xs)=batch_bernoulli_variance w p xs+batch_centered w p (batch_mean w p xs) xs.
 Premises and side conditions: Every member-weight, parameter-domain or nonzero-denominator requirement is explicit. Statements concern ideal, input-supplied Bernoulli moment targets, not a derived independent-trial probability model.
 Proof/definition method: Use the canonical SamplingPrecision variance factor and finite_sum linearity, positive-term arguments, exact weighted ANOVA and Rocq field/ring normalization.
 Library reuse: Rocq Stdlib List/Reals/Lra/Psatz/Ring/Field and existing FiniteSum, SamplingPrecision, ListPoolingAlgebra; no duplicated scalar Bernoulli implementation or random-count generator.
 Boundary: Supports the heterogeneous-rate algebra of reports sm:binomial/sm:rare and Towers admissions. No binomial PMF, independent trials, conditional-count law, chi-square pivot, or confidence coverage is proved.
*)
Theorem batch_bernoulli_variance_pooled_decomposition :
  forall (A:Type) (w p:A->R) (xs:list A), 0<batch_mass w xs -> batch_mass w xs*sampling_bernoulli_variance (batch_mean w p xs)=batch_bernoulli_variance w p xs+batch_centered w p (batch_mean w p xs) xs.
Proof.
  intros A w p xs Hm; rewrite batch_bernoulli_variance_as_moments; rewrite batch_centered_at_mean_closed by lra; rewrite (batch_mean_total_identity A w p xs) by lra; unfold sampling_bernoulli_variance; field; lra.
Qed.

(** [batch_bernoulli_variance_le_homogeneous] (theorem).
 Mathematical meaning: For nonnegative weights, heterogeneity cannot increase ideal Bernoulli variance beyond the rate-matched homogeneous benchmark.
 Exact proposition: forall (A:Type) (w p:A->R) (xs:list A), 0<batch_mass w xs -> (forall x, In x xs -> 0<=w x) -> batch_bernoulli_variance w p xs<=batch_mass w xs*sampling_bernoulli_variance (batch_mean w p xs).
 Premises and side conditions: Every member-weight, parameter-domain or nonzero-denominator requirement is explicit. Statements concern ideal, input-supplied Bernoulli moment targets, not a derived independent-trial probability model.
 Proof/definition method: Use the canonical SamplingPrecision variance factor and finite_sum linearity, positive-term arguments, exact weighted ANOVA and Rocq field/ring normalization.
 Library reuse: Rocq Stdlib List/Reals/Lra/Psatz/Ring/Field and existing FiniteSum, SamplingPrecision, ListPoolingAlgebra; no duplicated scalar Bernoulli implementation or random-count generator.
 Boundary: Supports the heterogeneous-rate algebra of reports sm:binomial/sm:rare and Towers admissions. No binomial PMF, independent trials, conditional-count law, chi-square pivot, or confidence coverage is proved.
*)
Theorem batch_bernoulli_variance_le_homogeneous :
  forall (A:Type) (w p:A->R) (xs:list A), 0<batch_mass w xs -> (forall x, In x xs -> 0<=w x) -> batch_bernoulli_variance w p xs<=batch_mass w xs*sampling_bernoulli_variance (batch_mean w p xs).
Proof.
  intros A w p xs Hm Hw; pose proof (batch_bernoulli_variance_pooled_decomposition A w p xs Hm) as H; pose proof (batch_centered_nonnegative A w p (batch_mean w p xs) xs Hw) as Hc; lra.
Qed.

(** [batch_bernoulli_variance_homogeneous] (theorem).
 Mathematical meaning: Constant cohort event rates yield total ideal Bernoulli count variance equal to mass times the common Bernoulli variance.
 Exact proposition: forall (A:Type) (w:A->R) (xs:list A) (p:R), batch_bernoulli_variance w (fun _=>p) xs=batch_mass w xs*sampling_bernoulli_variance p.
 Premises and side conditions: Every member-weight, parameter-domain or nonzero-denominator requirement is explicit. Statements concern ideal, input-supplied Bernoulli moment targets, not a derived independent-trial probability model.
 Proof/definition method: Use the canonical SamplingPrecision variance factor and finite_sum linearity, positive-term arguments, exact weighted ANOVA and Rocq field/ring normalization.
 Library reuse: Rocq Stdlib List/Reals/Lra/Psatz/Ring/Field and existing FiniteSum, SamplingPrecision, ListPoolingAlgebra; no duplicated scalar Bernoulli implementation or random-count generator.
 Boundary: Supports the heterogeneous-rate algebra of reports sm:binomial/sm:rare and Towers admissions. No binomial PMF, independent trials, conditional-count law, chi-square pivot, or confidence coverage is proved.
*)
Theorem batch_bernoulli_variance_homogeneous :
  forall (A:Type) (w:A->R) (xs:list A) (p:R), batch_bernoulli_variance w (fun _=>p) xs=batch_mass w xs*sampling_bernoulli_variance p.
Proof.
  intros A w xs p; unfold batch_bernoulli_variance,batch_mass; transitivity (finite_sum (fun x=>sampling_bernoulli_variance p*w x) xs); [apply finite_sum_ext; intro x; ring|rewrite finite_sum_scale; ring].
Qed.

(** [batch_bernoulli_variance_zero_probability] (theorem).
 Mathematical meaning: When every cohort has zero success probability, the ideal count variance vanishes.
 Exact proposition: forall (A:Type) (w:A->R) (xs:list A), batch_bernoulli_variance w (fun _=>0) xs=0.
 Premises and side conditions: Every member-weight, parameter-domain or nonzero-denominator requirement is explicit. Statements concern ideal, input-supplied Bernoulli moment targets, not a derived independent-trial probability model.
 Proof/definition method: Use the canonical SamplingPrecision variance factor and finite_sum linearity, positive-term arguments, exact weighted ANOVA and Rocq field/ring normalization.
 Library reuse: Rocq Stdlib List/Reals/Lra/Psatz/Ring/Field and existing FiniteSum, SamplingPrecision, ListPoolingAlgebra; no duplicated scalar Bernoulli implementation or random-count generator.
 Boundary: Supports the heterogeneous-rate algebra of reports sm:binomial/sm:rare and Towers admissions. No binomial PMF, independent trials, conditional-count law, chi-square pivot, or confidence coverage is proved.
*)
Theorem batch_bernoulli_variance_zero_probability :
  forall (A:Type) (w:A->R) (xs:list A), batch_bernoulli_variance w (fun _=>0) xs=0.
Proof.
  intros A w xs; rewrite batch_bernoulli_variance_homogeneous; unfold sampling_bernoulli_variance; ring.
Qed.

(** [batch_bernoulli_variance_certain_probability] (theorem).
 Mathematical meaning: When every cohort has certain success, the ideal count variance vanishes.
 Exact proposition: forall (A:Type) (w:A->R) (xs:list A), batch_bernoulli_variance w (fun _=>1) xs=0.
 Premises and side conditions: Every member-weight, parameter-domain or nonzero-denominator requirement is explicit. Statements concern ideal, input-supplied Bernoulli moment targets, not a derived independent-trial probability model.
 Proof/definition method: Use the canonical SamplingPrecision variance factor and finite_sum linearity, positive-term arguments, exact weighted ANOVA and Rocq field/ring normalization.
 Library reuse: Rocq Stdlib List/Reals/Lra/Psatz/Ring/Field and existing FiniteSum, SamplingPrecision, ListPoolingAlgebra; no duplicated scalar Bernoulli implementation or random-count generator.
 Boundary: Supports the heterogeneous-rate algebra of reports sm:binomial/sm:rare and Towers admissions. No binomial PMF, independent trials, conditional-count law, chi-square pivot, or confidence coverage is proved.
*)
Theorem batch_bernoulli_variance_certain_probability :
  forall (A:Type) (w:A->R) (xs:list A), batch_bernoulli_variance w (fun _=>1) xs=0.
Proof.
  intros A w xs; rewrite batch_bernoulli_variance_homogeneous; unfold sampling_bernoulli_variance; ring.
Qed.

(** [batch_expected_success_complement] (theorem).
 Mathematical meaning: The expected successes of complement events equal the expected failures of the original events.
 Exact proposition: forall (A:Type) (w p:A->R) (xs:list A), batch_total w (fun x=>1-p x) xs=batch_failure w p xs.
 Premises and side conditions: Every member-weight, parameter-domain or nonzero-denominator requirement is explicit. Statements concern ideal, input-supplied Bernoulli moment targets, not a derived independent-trial probability model.
 Proof/definition method: Use the canonical SamplingPrecision variance factor and finite_sum linearity, positive-term arguments, exact weighted ANOVA and Rocq field/ring normalization.
 Library reuse: Rocq Stdlib List/Reals/Lra/Psatz/Ring/Field and existing FiniteSum, SamplingPrecision, ListPoolingAlgebra; no duplicated scalar Bernoulli implementation or random-count generator.
 Boundary: Supports the heterogeneous-rate algebra of reports sm:binomial/sm:rare and Towers admissions. No binomial PMF, independent trials, conditional-count law, chi-square pivot, or confidence coverage is proved.
*)
Theorem batch_expected_success_complement :
  forall (A:Type) (w p:A->R) (xs:list A), batch_total w (fun x=>1-p x) xs=batch_failure w p xs.
Proof.
  intros A w p xs; reflexivity.
Qed.

(** [batch_failure_double_complement] (theorem).
 Mathematical meaning: Complementing an already complemented success rate restores the original success count.
 Exact proposition: forall (A:Type) (w p:A->R) (xs:list A), batch_failure w (fun x=>1-p x) xs=batch_total w p xs.
 Premises and side conditions: Every member-weight, parameter-domain or nonzero-denominator requirement is explicit. Statements concern ideal, input-supplied Bernoulli moment targets, not a derived independent-trial probability model.
 Proof/definition method: Use the canonical SamplingPrecision variance factor and finite_sum linearity, positive-term arguments, exact weighted ANOVA and Rocq field/ring normalization.
 Library reuse: Rocq Stdlib List/Reals/Lra/Psatz/Ring/Field and existing FiniteSum, SamplingPrecision, ListPoolingAlgebra; no duplicated scalar Bernoulli implementation or random-count generator.
 Boundary: Supports the heterogeneous-rate algebra of reports sm:binomial/sm:rare and Towers admissions. No binomial PMF, independent trials, conditional-count law, chi-square pivot, or confidence coverage is proved.
*)
Theorem batch_failure_double_complement :
  forall (A:Type) (w p:A->R) (xs:list A), batch_failure w (fun x=>1-p x) xs=batch_total w p xs.
Proof.
  intros A w p xs; unfold batch_failure,batch_total; apply finite_sum_ext; intro x; ring.
Qed.

(** [batch_centered_total] (definition).
 Mathematical meaning: Weighted signed deviation from an arbitrary reference center.
 Exact declaration: Definition batch_centered_total {A:Type} (w v:A->R) (c:R) (xs:list A):R := finite_sum (fun x => w x*(v x-c)) xs.
 Premises and side conditions: The stated finite-list, real-number, positivity and denominator hypotheses are explicit. An observation is not thereby assumed to have any particular probability distribution.
 Proof/definition method: Rewrite into the canonical FiniteSum fold, use earlier list-pooling facts and Rocq Stdlib real arithmetic; ensure all cross-term cancellations are proved rather than asserted.
 Library reuse: Stdlib Reals/List/Permutation/Ring/Field/Lra/Psatz, FiniteSum and canonical prior ListPoolingAlgebra definitions; never introduce a parallel summation or random-sampling engine.
 Boundary: Deterministic G12 finite-sample aggregation and covariance algebra only; no Gaussian independence, chi-square law, finite-sample statistical coverage, or empirical IQ model is proved.
*)
Definition batch_centered_total {A:Type} (w v:A->R) (c:R) (xs:list A):R := finite_sum (fun x => w x*(v x-c)) xs.

(** [batch_centered_cross] (definition).
 Mathematical meaning: Cross-product of two centered group attributes, weighted over arbitrary group lists.
 Exact declaration: Definition batch_centered_cross {A:Type} (w v z:A->R) (c d:R) (xs:list A):R := finite_sum (fun x => w x*(v x-c)*(z x-d)) xs.
 Premises and side conditions: The stated finite-list, real-number, positivity and denominator hypotheses are explicit. An observation is not thereby assumed to have any particular probability distribution.
 Proof/definition method: Rewrite into the canonical FiniteSum fold, use earlier list-pooling facts and Rocq Stdlib real arithmetic; ensure all cross-term cancellations are proved rather than asserted.
 Library reuse: Stdlib Reals/List/Permutation/Ring/Field/Lra/Psatz, FiniteSum and canonical prior ListPoolingAlgebra definitions; never introduce a parallel summation or random-sampling engine.
 Boundary: Deterministic G12 finite-sample aggregation and covariance algebra only; no Gaussian independence, chi-square law, finite-sample statistical coverage, or empirical IQ model is proved.
*)
Definition batch_centered_cross {A:Type} (w v z:A->R) (c d:R) (xs:list A):R := finite_sum (fun x => w x*(v x-c)*(z x-d)) xs.

(** [batch_cov_numer] (definition).
 Mathematical meaning: Centered cross-product sum at both weighted sample means.
 Exact declaration: Definition batch_cov_numer {A:Type} (w v z:A->R) (xs:list A):R := batch_centered_cross w v z (batch_mean w v xs) (batch_mean w z xs) xs.
 Premises and side conditions: The stated finite-list, real-number, positivity and denominator hypotheses are explicit. An observation is not thereby assumed to have any particular probability distribution.
 Proof/definition method: Rewrite into the canonical FiniteSum fold, use earlier list-pooling facts and Rocq Stdlib real arithmetic; ensure all cross-term cancellations are proved rather than asserted.
 Library reuse: Stdlib Reals/List/Permutation/Ring/Field/Lra/Psatz, FiniteSum and canonical prior ListPoolingAlgebra definitions; never introduce a parallel summation or random-sampling engine.
 Boundary: Deterministic G12 finite-sample aggregation and covariance algebra only; no Gaussian independence, chi-square law, finite-sample statistical coverage, or empirical IQ model is proved.
*)
Definition batch_cov_numer {A:Type} (w v z:A->R) (xs:list A):R := batch_centered_cross w v z (batch_mean w v xs) (batch_mean w z xs) xs.

(** [batch_variance] (definition).
 Mathematical meaning: Population-style normalized corrected-sum-of-squares of deterministic batch centers.
 Exact declaration: Definition batch_variance {A:Type} (w v:A->R) (xs:list A):R := batch_centered w v (batch_mean w v xs) xs / batch_mass w xs.
 Premises and side conditions: The stated finite-list, real-number, positivity and denominator hypotheses are explicit. An observation is not thereby assumed to have any particular probability distribution.
 Proof/definition method: Rewrite into the canonical FiniteSum fold, use earlier list-pooling facts and Rocq Stdlib real arithmetic; ensure all cross-term cancellations are proved rather than asserted.
 Library reuse: Stdlib Reals/List/Permutation/Ring/Field/Lra/Psatz, FiniteSum and canonical prior ListPoolingAlgebra definitions; never introduce a parallel summation or random-sampling engine.
 Boundary: Deterministic G12 finite-sample aggregation and covariance algebra only; no Gaussian independence, chi-square law, finite-sample statistical coverage, or empirical IQ model is proved.
*)
Definition batch_variance {A:Type} (w v:A->R) (xs:list A):R := batch_centered w v (batch_mean w v xs) xs / batch_mass w xs.

(** [batch_covariance] (definition).
 Mathematical meaning: Normalized batch cross-product centered at both weighted sample means.
 Exact declaration: Definition batch_covariance {A:Type} (w v z:A->R) (xs:list A):R := batch_cov_numer w v z xs / batch_mass w xs.
 Premises and side conditions: The stated finite-list, real-number, positivity and denominator hypotheses are explicit. An observation is not thereby assumed to have any particular probability distribution.
 Proof/definition method: Rewrite into the canonical FiniteSum fold, use earlier list-pooling facts and Rocq Stdlib real arithmetic; ensure all cross-term cancellations are proved rather than asserted.
 Library reuse: Stdlib Reals/List/Permutation/Ring/Field/Lra/Psatz, FiniteSum and canonical prior ListPoolingAlgebra definitions; never introduce a parallel summation or random-sampling engine.
 Boundary: Deterministic G12 finite-sample aggregation and covariance algebra only; no Gaussian independence, chi-square law, finite-sample statistical coverage, or empirical IQ model is proved.
*)
Definition batch_covariance {A:Type} (w v z:A->R) (xs:list A):R := batch_cov_numer w v z xs / batch_mass w xs.

(** [batch_centered_total_app] (theorem).
 Mathematical meaning: Signed deviations add over arbitrary concatenated batch partitions.
 Exact proposition: forall (A:Type) (w v:A->R) (c:R) (xs ys:list A), batch_centered_total w v c (xs++ys)=batch_centered_total w v c xs+batch_centered_total w v c ys.
 Premises and side conditions: The stated finite-list, real-number, positivity and denominator hypotheses are explicit. An observation is not thereby assumed to have any particular probability distribution.
 Proof/definition method: Rewrite into the canonical FiniteSum fold, use earlier list-pooling facts and Rocq Stdlib real arithmetic; ensure all cross-term cancellations are proved rather than asserted.
 Library reuse: Stdlib Reals/List/Permutation/Ring/Field/Lra/Psatz, FiniteSum and canonical prior ListPoolingAlgebra definitions; never introduce a parallel summation or random-sampling engine.
 Boundary: Deterministic G12 finite-sample aggregation and covariance algebra only; no Gaussian independence, chi-square law, finite-sample statistical coverage, or empirical IQ model is proved.
*)
Theorem batch_centered_total_app :
  forall (A:Type) (w v:A->R) (c:R) (xs ys:list A), batch_centered_total w v c (xs++ys)=batch_centered_total w v c xs+batch_centered_total w v c ys.
Proof.
  intros A w v c xs ys; unfold batch_centered_total; apply finite_sum_app.
Qed.

(** [batch_centered_total_permutation] (theorem).
 Mathematical meaning: Reordering groups leaves the signed aggregate deviation unchanged.
 Exact proposition: forall (A:Type) (w v:A->R) (c:R) (xs ys:list A), Permutation xs ys -> batch_centered_total w v c xs=batch_centered_total w v c ys.
 Premises and side conditions: The stated finite-list, real-number, positivity and denominator hypotheses are explicit. An observation is not thereby assumed to have any particular probability distribution.
 Proof/definition method: Rewrite into the canonical FiniteSum fold, use earlier list-pooling facts and Rocq Stdlib real arithmetic; ensure all cross-term cancellations are proved rather than asserted.
 Library reuse: Stdlib Reals/List/Permutation/Ring/Field/Lra/Psatz, FiniteSum and canonical prior ListPoolingAlgebra definitions; never introduce a parallel summation or random-sampling engine.
 Boundary: Deterministic G12 finite-sample aggregation and covariance algebra only; no Gaussian independence, chi-square law, finite-sample statistical coverage, or empirical IQ model is proved.
*)
Theorem batch_centered_total_permutation :
  forall (A:Type) (w v:A->R) (c:R) (xs ys:list A), Permutation xs ys -> batch_centered_total w v c xs=batch_centered_total w v c ys.
Proof.
  intros A w v c xs ys H; unfold batch_centered_total; now apply finite_sum_permutation.
Qed.

(** [batch_centered_total_expand] (theorem).
 Mathematical meaning: The signed deviation equals the raw weighted moment minus center times mass.
 Exact proposition: forall (A:Type) (w v:A->R) (c:R) (xs:list A), batch_centered_total w v c xs=batch_total w v xs-c*batch_mass w xs.
 Premises and side conditions: The stated finite-list, real-number, positivity and denominator hypotheses are explicit. An observation is not thereby assumed to have any particular probability distribution.
 Proof/definition method: Rewrite into the canonical FiniteSum fold, use earlier list-pooling facts and Rocq Stdlib real arithmetic; ensure all cross-term cancellations are proved rather than asserted.
 Library reuse: Stdlib Reals/List/Permutation/Ring/Field/Lra/Psatz, FiniteSum and canonical prior ListPoolingAlgebra definitions; never introduce a parallel summation or random-sampling engine.
 Boundary: Deterministic G12 finite-sample aggregation and covariance algebra only; no Gaussian independence, chi-square law, finite-sample statistical coverage, or empirical IQ model is proved.
*)
Theorem batch_centered_total_expand :
  forall (A:Type) (w v:A->R) (c:R) (xs:list A), batch_centered_total w v c xs=batch_total w v xs-c*batch_mass w xs.
Proof.
  intros A w v c xs; unfold batch_centered_total,batch_total,batch_mass; transitivity (finite_sum (fun x=>w x*v x-c*w x) xs); [apply finite_sum_ext; intro x; ring|rewrite finite_sum_sub,finite_sum_scale; ring].
Qed.

(** [batch_centered_total_mean_zero] (theorem).
 Mathematical meaning: The signed weighted residuals cancel exactly at the weighted mean.
 Exact proposition: forall (A:Type) (w v:A->R) (xs:list A), batch_mass w xs<>0 -> batch_centered_total w v (batch_mean w v xs) xs=0.
 Premises and side conditions: The stated finite-list, real-number, positivity and denominator hypotheses are explicit. An observation is not thereby assumed to have any particular probability distribution.
 Proof/definition method: Rewrite into the canonical FiniteSum fold, use earlier list-pooling facts and Rocq Stdlib real arithmetic; ensure all cross-term cancellations are proved rather than asserted.
 Library reuse: Stdlib Reals/List/Permutation/Ring/Field/Lra/Psatz, FiniteSum and canonical prior ListPoolingAlgebra definitions; never introduce a parallel summation or random-sampling engine.
 Boundary: Deterministic G12 finite-sample aggregation and covariance algebra only; no Gaussian independence, chi-square law, finite-sample statistical coverage, or empirical IQ model is proved.
*)
Theorem batch_centered_total_mean_zero :
  forall (A:Type) (w v:A->R) (xs:list A), batch_mass w xs<>0 -> batch_centered_total w v (batch_mean w v xs) xs=0.
Proof.
  intros A w v xs H; rewrite batch_centered_total_expand; pose proof (batch_mean_total_identity A w v xs H) as E; rewrite E; ring.
Qed.

(** [batch_centered_total_add] (theorem).
 Mathematical meaning: Signed deviations are additive in two group-center attributes.
 Exact proposition: forall (A:Type) (w v z:A->R) (c d:R) (xs:list A), batch_centered_total w (fun x=>v x+z x) (c+d) xs=batch_centered_total w v c xs+batch_centered_total w z d xs.
 Premises and side conditions: The stated finite-list, real-number, positivity and denominator hypotheses are explicit. An observation is not thereby assumed to have any particular probability distribution.
 Proof/definition method: Rewrite into the canonical FiniteSum fold, use earlier list-pooling facts and Rocq Stdlib real arithmetic; ensure all cross-term cancellations are proved rather than asserted.
 Library reuse: Stdlib Reals/List/Permutation/Ring/Field/Lra/Psatz, FiniteSum and canonical prior ListPoolingAlgebra definitions; never introduce a parallel summation or random-sampling engine.
 Boundary: Deterministic G12 finite-sample aggregation and covariance algebra only; no Gaussian independence, chi-square law, finite-sample statistical coverage, or empirical IQ model is proved.
*)
Theorem batch_centered_total_add :
  forall (A:Type) (w v z:A->R) (c d:R) (xs:list A), batch_centered_total w (fun x=>v x+z x) (c+d) xs=batch_centered_total w v c xs+batch_centered_total w z d xs.
Proof.
  intros A w v z c d xs; rewrite !batch_centered_total_expand, batch_total_add_values; ring.
Qed.

(** [batch_centered_total_scale] (theorem).
 Mathematical meaning: A common scale for group centers and reference scales signed residuals linearly.
 Exact proposition: forall (A:Type) (w v:A->R) (c t:R) (xs:list A), batch_centered_total w (fun x=>t*v x) (t*c) xs=t*batch_centered_total w v c xs.
 Premises and side conditions: The stated finite-list, real-number, positivity and denominator hypotheses are explicit. An observation is not thereby assumed to have any particular probability distribution.
 Proof/definition method: Rewrite into the canonical FiniteSum fold, use earlier list-pooling facts and Rocq Stdlib real arithmetic; ensure all cross-term cancellations are proved rather than asserted.
 Library reuse: Stdlib Reals/List/Permutation/Ring/Field/Lra/Psatz, FiniteSum and canonical prior ListPoolingAlgebra definitions; never introduce a parallel summation or random-sampling engine.
 Boundary: Deterministic G12 finite-sample aggregation and covariance algebra only; no Gaussian independence, chi-square law, finite-sample statistical coverage, or empirical IQ model is proved.
*)
Theorem batch_centered_total_scale :
  forall (A:Type) (w v:A->R) (c t:R) (xs:list A), batch_centered_total w (fun x=>t*v x) (t*c) xs=t*batch_centered_total w v c xs.
Proof.
  intros A w v c t xs; rewrite !batch_centered_total_expand, batch_total_scale_values; ring.
Qed.

(** [batch_centered_total_translate] (theorem).
 Mathematical meaning: Translating every observation and center identically does not change signed residuals.
 Exact proposition: forall (A:Type) (w v:A->R) (c t:R) (xs:list A), batch_centered_total w (fun x=>v x+t) (c+t) xs=batch_centered_total w v c xs.
 Premises and side conditions: The stated finite-list, real-number, positivity and denominator hypotheses are explicit. An observation is not thereby assumed to have any particular probability distribution.
 Proof/definition method: Rewrite into the canonical FiniteSum fold, use earlier list-pooling facts and Rocq Stdlib real arithmetic; ensure all cross-term cancellations are proved rather than asserted.
 Library reuse: Stdlib Reals/List/Permutation/Ring/Field/Lra/Psatz, FiniteSum and canonical prior ListPoolingAlgebra definitions; never introduce a parallel summation or random-sampling engine.
 Boundary: Deterministic G12 finite-sample aggregation and covariance algebra only; no Gaussian independence, chi-square law, finite-sample statistical coverage, or empirical IQ model is proved.
*)
Theorem batch_centered_total_translate :
  forall (A:Type) (w v:A->R) (c t:R) (xs:list A), batch_centered_total w (fun x=>v x+t) (c+t) xs=batch_centered_total w v c xs.
Proof.
  intros A w v c t xs; unfold batch_centered_total; apply finite_sum_ext; intro x; ring.
Qed.

(** [batch_centered_total_shift_center] (theorem).
 Mathematical meaning: Changing reference center modifies signed deviation by the total mass times that center shift.
 Exact proposition: forall (A:Type) (w v:A->R) (c d:R) (xs:list A), batch_centered_total w v c xs-batch_centered_total w v d xs=(d-c)*batch_mass w xs.
 Premises and side conditions: The stated finite-list, real-number, positivity and denominator hypotheses are explicit. An observation is not thereby assumed to have any particular probability distribution.
 Proof/definition method: Rewrite into the canonical FiniteSum fold, use earlier list-pooling facts and Rocq Stdlib real arithmetic; ensure all cross-term cancellations are proved rather than asserted.
 Library reuse: Stdlib Reals/List/Permutation/Ring/Field/Lra/Psatz, FiniteSum and canonical prior ListPoolingAlgebra definitions; never introduce a parallel summation or random-sampling engine.
 Boundary: Deterministic G12 finite-sample aggregation and covariance algebra only; no Gaussian independence, chi-square law, finite-sample statistical coverage, or empirical IQ model is proved.
*)
Theorem batch_centered_total_shift_center :
  forall (A:Type) (w v:A->R) (c d:R) (xs:list A), batch_centered_total w v c xs-batch_centered_total w v d xs=(d-c)*batch_mass w xs.
Proof.
  intros A w v c d xs; rewrite !batch_centered_total_expand; ring.
Qed.

(** [batch_centered_cross_app] (theorem).
 Mathematical meaning: Reference-centered cross-product sums add over any group partition.
 Exact proposition: forall (A:Type) (w v z:A->R) (c d:R) (xs ys:list A), batch_centered_cross w v z c d (xs++ys)=batch_centered_cross w v z c d xs+batch_centered_cross w v z c d ys.
 Premises and side conditions: The stated finite-list, real-number, positivity and denominator hypotheses are explicit. An observation is not thereby assumed to have any particular probability distribution.
 Proof/definition method: Rewrite into the canonical FiniteSum fold, use earlier list-pooling facts and Rocq Stdlib real arithmetic; ensure all cross-term cancellations are proved rather than asserted.
 Library reuse: Stdlib Reals/List/Permutation/Ring/Field/Lra/Psatz, FiniteSum and canonical prior ListPoolingAlgebra definitions; never introduce a parallel summation or random-sampling engine.
 Boundary: Deterministic G12 finite-sample aggregation and covariance algebra only; no Gaussian independence, chi-square law, finite-sample statistical coverage, or empirical IQ model is proved.
*)
Theorem batch_centered_cross_app :
  forall (A:Type) (w v z:A->R) (c d:R) (xs ys:list A), batch_centered_cross w v z c d (xs++ys)=batch_centered_cross w v z c d xs+batch_centered_cross w v z c d ys.
Proof.
  intros A w v z c d xs ys; unfold batch_centered_cross; apply finite_sum_app.
Qed.

(** [batch_centered_cross_permutation] (theorem).
 Mathematical meaning: Reordering arbitrary group IDs does not alter weighted cross-product dispersion.
 Exact proposition: forall (A:Type) (w v z:A->R) (c d:R) (xs ys:list A), Permutation xs ys -> batch_centered_cross w v z c d xs=batch_centered_cross w v z c d ys.
 Premises and side conditions: The stated finite-list, real-number, positivity and denominator hypotheses are explicit. An observation is not thereby assumed to have any particular probability distribution.
 Proof/definition method: Rewrite into the canonical FiniteSum fold, use earlier list-pooling facts and Rocq Stdlib real arithmetic; ensure all cross-term cancellations are proved rather than asserted.
 Library reuse: Stdlib Reals/List/Permutation/Ring/Field/Lra/Psatz, FiniteSum and canonical prior ListPoolingAlgebra definitions; never introduce a parallel summation or random-sampling engine.
 Boundary: Deterministic G12 finite-sample aggregation and covariance algebra only; no Gaussian independence, chi-square law, finite-sample statistical coverage, or empirical IQ model is proved.
*)
Theorem batch_centered_cross_permutation :
  forall (A:Type) (w v z:A->R) (c d:R) (xs ys:list A), Permutation xs ys -> batch_centered_cross w v z c d xs=batch_centered_cross w v z c d ys.
Proof.
  intros A w v z c d xs ys H; unfold batch_centered_cross; now apply finite_sum_permutation.
Qed.

(** [batch_centered_cross_symmetry] (theorem).
 Mathematical meaning: The centered weighted cross-product is symmetric in attributes and their reference centers.
 Exact proposition: forall (A:Type) (w v z:A->R) (c d:R) (xs:list A), batch_centered_cross w v z c d xs=batch_centered_cross w z v d c xs.
 Premises and side conditions: The stated finite-list, real-number, positivity and denominator hypotheses are explicit. An observation is not thereby assumed to have any particular probability distribution.
 Proof/definition method: Rewrite into the canonical FiniteSum fold, use earlier list-pooling facts and Rocq Stdlib real arithmetic; ensure all cross-term cancellations are proved rather than asserted.
 Library reuse: Stdlib Reals/List/Permutation/Ring/Field/Lra/Psatz, FiniteSum and canonical prior ListPoolingAlgebra definitions; never introduce a parallel summation or random-sampling engine.
 Boundary: Deterministic G12 finite-sample aggregation and covariance algebra only; no Gaussian independence, chi-square law, finite-sample statistical coverage, or empirical IQ model is proved.
*)
Theorem batch_centered_cross_symmetry :
  forall (A:Type) (w v z:A->R) (c d:R) (xs:list A), batch_centered_cross w v z c d xs=batch_centered_cross w z v d c xs.
Proof.
  intros A w v z c d xs; unfold batch_centered_cross; apply finite_sum_ext; intro x; ring.
Qed.

(** [batch_centered_cross_self] (theorem).
 Mathematical meaning: The centered weighted second moment equals the centered cross-product of a value with itself.
 Exact proposition: forall (A:Type) (w v:A->R) (c:R) (xs:list A), batch_centered w v c xs=batch_centered_cross w v v c c xs.
 Premises and side conditions: The stated finite-list, real-number, positivity and denominator hypotheses are explicit. An observation is not thereby assumed to have any particular probability distribution.
 Proof/definition method: Rewrite into the canonical FiniteSum fold, use earlier list-pooling facts and Rocq Stdlib real arithmetic; ensure all cross-term cancellations are proved rather than asserted.
 Library reuse: Stdlib Reals/List/Permutation/Ring/Field/Lra/Psatz, FiniteSum and canonical prior ListPoolingAlgebra definitions; never introduce a parallel summation or random-sampling engine.
 Boundary: Deterministic G12 finite-sample aggregation and covariance algebra only; no Gaussian independence, chi-square law, finite-sample statistical coverage, or empirical IQ model is proved.
*)
Theorem batch_centered_cross_self :
  forall (A:Type) (w v:A->R) (c:R) (xs:list A), batch_centered w v c xs=batch_centered_cross w v v c c xs.
Proof.
  intros A w v c xs; reflexivity.
Qed.

(** [batch_centered_cross_expand] (theorem).
 Mathematical meaning: The general weighted cross-product expands into raw mixed moment, weighted first moments and a constant mass term.
 Exact proposition: forall (A:Type) (w v z:A->R) (c d:R) (xs:list A), batch_centered_cross w v z c d xs=batch_cross w v z xs-c*batch_total w z xs-d*batch_total w v xs+c*d*batch_mass w xs.
 Premises and side conditions: The stated finite-list, real-number, positivity and denominator hypotheses are explicit. An observation is not thereby assumed to have any particular probability distribution.
 Proof/definition method: Rewrite into the canonical FiniteSum fold, use earlier list-pooling facts and Rocq Stdlib real arithmetic; ensure all cross-term cancellations are proved rather than asserted.
 Library reuse: Stdlib Reals/List/Permutation/Ring/Field/Lra/Psatz, FiniteSum and canonical prior ListPoolingAlgebra definitions; never introduce a parallel summation or random-sampling engine.
 Boundary: Deterministic G12 finite-sample aggregation and covariance algebra only; no Gaussian independence, chi-square law, finite-sample statistical coverage, or empirical IQ model is proved.
*)
Theorem batch_centered_cross_expand :
  forall (A:Type) (w v z:A->R) (c d:R) (xs:list A), batch_centered_cross w v z c d xs=batch_cross w v z xs-c*batch_total w z xs-d*batch_total w v xs+c*d*batch_mass w xs.
Proof.
  intros A w v z c d xs; unfold batch_centered_cross,batch_cross,batch_total,batch_mass; transitivity (finite_sum (fun x => (w x*v x*z x-c*(w x*z x))-(d*(w x*v x)-c*d*w x)) xs); [apply finite_sum_ext; intro x; ring|rewrite !finite_sum_sub, !finite_sum_scale; ring].
Qed.

(** [batch_cov_numer_closed] (theorem).
 Mathematical meaning: The centered covariance numerator is mixed raw moment minus the product of weighted first moments divided by mass.
 Exact proposition: forall (A:Type) (w v z:A->R) (xs:list A), batch_mass w xs<>0 -> batch_cov_numer w v z xs=batch_cross w v z xs-(batch_total w v xs*batch_total w z xs)/batch_mass w xs.
 Premises and side conditions: The stated finite-list, real-number, positivity and denominator hypotheses are explicit. An observation is not thereby assumed to have any particular probability distribution.
 Proof/definition method: Rewrite into the canonical FiniteSum fold, use earlier list-pooling facts and Rocq Stdlib real arithmetic; ensure all cross-term cancellations are proved rather than asserted.
 Library reuse: Stdlib Reals/List/Permutation/Ring/Field/Lra/Psatz, FiniteSum and canonical prior ListPoolingAlgebra definitions; never introduce a parallel summation or random-sampling engine.
 Boundary: Deterministic G12 finite-sample aggregation and covariance algebra only; no Gaussian independence, chi-square law, finite-sample statistical coverage, or empirical IQ model is proved.
*)
Theorem batch_cov_numer_closed :
  forall (A:Type) (w v z:A->R) (xs:list A), batch_mass w xs<>0 -> batch_cov_numer w v z xs=batch_cross w v z xs-(batch_total w v xs*batch_total w z xs)/batch_mass w xs.
Proof.
  intros A w v z xs H; unfold batch_cov_numer; rewrite batch_centered_cross_expand; unfold batch_mean; field; exact H.
Qed.

(** [batch_cov_numer_symmetry] (theorem).
 Mathematical meaning: Arbitrary-list covariance numerator is symmetric under swapping variables.
 Exact proposition: forall (A:Type) (w v z:A->R) (xs:list A), batch_cov_numer w v z xs=batch_cov_numer w z v xs.
 Premises and side conditions: The stated finite-list, real-number, positivity and denominator hypotheses are explicit. An observation is not thereby assumed to have any particular probability distribution.
 Proof/definition method: Rewrite into the canonical FiniteSum fold, use earlier list-pooling facts and Rocq Stdlib real arithmetic; ensure all cross-term cancellations are proved rather than asserted.
 Library reuse: Stdlib Reals/List/Permutation/Ring/Field/Lra/Psatz, FiniteSum and canonical prior ListPoolingAlgebra definitions; never introduce a parallel summation or random-sampling engine.
 Boundary: Deterministic G12 finite-sample aggregation and covariance algebra only; no Gaussian independence, chi-square law, finite-sample statistical coverage, or empirical IQ model is proved.
*)
Theorem batch_cov_numer_symmetry :
  forall (A:Type) (w v z:A->R) (xs:list A), batch_cov_numer w v z xs=batch_cov_numer w z v xs.
Proof.
  intros A w v z xs; unfold batch_cov_numer; apply batch_centered_cross_symmetry.
Qed.

(** [batch_cov_numer_self] (theorem).
 Mathematical meaning: The covariance numerator on an attribute with itself equals its corrected sum of squares.
 Exact proposition: forall (A:Type) (w v:A->R) (xs:list A), batch_cov_numer w v v xs=batch_centered w v (batch_mean w v xs) xs.
 Premises and side conditions: The stated finite-list, real-number, positivity and denominator hypotheses are explicit. An observation is not thereby assumed to have any particular probability distribution.
 Proof/definition method: Rewrite into the canonical FiniteSum fold, use earlier list-pooling facts and Rocq Stdlib real arithmetic; ensure all cross-term cancellations are proved rather than asserted.
 Library reuse: Stdlib Reals/List/Permutation/Ring/Field/Lra/Psatz, FiniteSum and canonical prior ListPoolingAlgebra definitions; never introduce a parallel summation or random-sampling engine.
 Boundary: Deterministic G12 finite-sample aggregation and covariance algebra only; no Gaussian independence, chi-square law, finite-sample statistical coverage, or empirical IQ model is proved.
*)
Theorem batch_cov_numer_self :
  forall (A:Type) (w v:A->R) (xs:list A), batch_cov_numer w v v xs=batch_centered w v (batch_mean w v xs) xs.
Proof.
  intros A w v xs; unfold batch_cov_numer; symmetry; apply batch_centered_cross_self.
Qed.

(** [batch_cov_numer_nonnegative_self] (theorem).
 Mathematical meaning: Every attribute has nonnegative weighted covariance numerator for nonnegative group sizes.
 Exact proposition: forall (A:Type) (w v:A->R) (xs:list A), (forall x, In x xs -> 0<=w x) -> 0<=batch_cov_numer w v v xs.
 Premises and side conditions: The stated finite-list, real-number, positivity and denominator hypotheses are explicit. An observation is not thereby assumed to have any particular probability distribution.
 Proof/definition method: Rewrite into the canonical FiniteSum fold, use earlier list-pooling facts and Rocq Stdlib real arithmetic; ensure all cross-term cancellations are proved rather than asserted.
 Library reuse: Stdlib Reals/List/Permutation/Ring/Field/Lra/Psatz, FiniteSum and canonical prior ListPoolingAlgebra definitions; never introduce a parallel summation or random-sampling engine.
 Boundary: Deterministic G12 finite-sample aggregation and covariance algebra only; no Gaussian independence, chi-square law, finite-sample statistical coverage, or empirical IQ model is proved.
*)
Theorem batch_cov_numer_nonnegative_self :
  forall (A:Type) (w v:A->R) (xs:list A), (forall x, In x xs -> 0<=w x) -> 0<=batch_cov_numer w v v xs.
Proof.
  intros A w v xs Hw; rewrite batch_cov_numer_self; apply batch_centered_nonnegative; exact Hw.
Qed.

(** [batch_covariance_symmetry] (theorem).
 Mathematical meaning: Normalized covariance is exactly symmetric for any real group weights.
 Exact proposition: forall (A:Type) (w v z:A->R) (xs:list A), batch_covariance w v z xs=batch_covariance w z v xs.
 Premises and side conditions: The stated finite-list, real-number, positivity and denominator hypotheses are explicit. An observation is not thereby assumed to have any particular probability distribution.
 Proof/definition method: Rewrite into the canonical FiniteSum fold, use earlier list-pooling facts and Rocq Stdlib real arithmetic; ensure all cross-term cancellations are proved rather than asserted.
 Library reuse: Stdlib Reals/List/Permutation/Ring/Field/Lra/Psatz, FiniteSum and canonical prior ListPoolingAlgebra definitions; never introduce a parallel summation or random-sampling engine.
 Boundary: Deterministic G12 finite-sample aggregation and covariance algebra only; no Gaussian independence, chi-square law, finite-sample statistical coverage, or empirical IQ model is proved.
*)
Theorem batch_covariance_symmetry :
  forall (A:Type) (w v z:A->R) (xs:list A), batch_covariance w v z xs=batch_covariance w z v xs.
Proof.
  intros A w v z xs; unfold batch_covariance; now rewrite batch_cov_numer_symmetry.
Qed.

(** [batch_covariance_self_variance] (theorem).
 Mathematical meaning: Diagonal normalized covariance equals normalized corrected variance.
 Exact proposition: forall (A:Type) (w v:A->R) (xs:list A), batch_covariance w v v xs=batch_variance w v xs.
 Premises and side conditions: The stated finite-list, real-number, positivity and denominator hypotheses are explicit. An observation is not thereby assumed to have any particular probability distribution.
 Proof/definition method: Rewrite into the canonical FiniteSum fold, use earlier list-pooling facts and Rocq Stdlib real arithmetic; ensure all cross-term cancellations are proved rather than asserted.
 Library reuse: Stdlib Reals/List/Permutation/Ring/Field/Lra/Psatz, FiniteSum and canonical prior ListPoolingAlgebra definitions; never introduce a parallel summation or random-sampling engine.
 Boundary: Deterministic G12 finite-sample aggregation and covariance algebra only; no Gaussian independence, chi-square law, finite-sample statistical coverage, or empirical IQ model is proved.
*)
Theorem batch_covariance_self_variance :
  forall (A:Type) (w v:A->R) (xs:list A), batch_covariance w v v xs=batch_variance w v xs.
Proof.
  intros A w v xs; unfold batch_covariance,batch_variance; now rewrite batch_cov_numer_self.
Qed.

(** [batch_variance_nonnegative] (theorem).
 Mathematical meaning: Under positive total mass and nonnegative weights, normalized corrected variance is nonnegative.
 Exact proposition: forall (A:Type) (w v:A->R) (xs:list A), (forall x, In x xs -> 0<=w x) -> 0<batch_mass w xs -> 0<=batch_variance w v xs.
 Premises and side conditions: The stated finite-list, real-number, positivity and denominator hypotheses are explicit. An observation is not thereby assumed to have any particular probability distribution.
 Proof/definition method: Rewrite into the canonical FiniteSum fold, use earlier list-pooling facts and Rocq Stdlib real arithmetic; ensure all cross-term cancellations are proved rather than asserted.
 Library reuse: Stdlib Reals/List/Permutation/Ring/Field/Lra/Psatz, FiniteSum and canonical prior ListPoolingAlgebra definitions; never introduce a parallel summation or random-sampling engine.
 Boundary: Deterministic G12 finite-sample aggregation and covariance algebra only; no Gaussian independence, chi-square law, finite-sample statistical coverage, or empirical IQ model is proved.
*)
Theorem batch_variance_nonnegative :
  forall (A:Type) (w v:A->R) (xs:list A), (forall x, In x xs -> 0<=w x) -> 0<batch_mass w xs -> 0<=batch_variance w v xs.
Proof.
  intros A w v xs Hw Hm; unfold batch_variance,Rdiv; apply Rmult_le_pos; [apply batch_centered_nonnegative; exact Hw|left; apply Rinv_0_lt_compat; exact Hm].
Qed.

(** [batch_variance_constant_zero] (theorem).
 Mathematical meaning: The variance of identical group means is zero, provided total group mass is nonzero.
 Exact proposition: forall (A:Type) (w:A->R) (c:R) (xs:list A), batch_mass w xs<>0 -> batch_variance w (fun _=>c) xs=0.
 Premises and side conditions: The stated finite-list, real-number, positivity and denominator hypotheses are explicit. An observation is not thereby assumed to have any particular probability distribution.
 Proof/definition method: Rewrite into the canonical FiniteSum fold, use earlier list-pooling facts and Rocq Stdlib real arithmetic; ensure all cross-term cancellations are proved rather than asserted.
 Library reuse: Stdlib Reals/List/Permutation/Ring/Field/Lra/Psatz, FiniteSum and canonical prior ListPoolingAlgebra definitions; never introduce a parallel summation or random-sampling engine.
 Boundary: Deterministic G12 finite-sample aggregation and covariance algebra only; no Gaussian independence, chi-square law, finite-sample statistical coverage, or empirical IQ model is proved.
*)
Theorem batch_variance_constant_zero :
  forall (A:Type) (w:A->R) (c:R) (xs:list A), batch_mass w xs<>0 -> batch_variance w (fun _=>c) xs=0.
Proof.
  intros A w c xs H; unfold batch_variance; rewrite (batch_mean_constant A w xs c H); rewrite batch_centered_constant_zero; unfold Rdiv; rewrite Rmult_0_l; reflexivity.
Qed.

(** [batch_variance_translation] (theorem).
 Mathematical meaning: A common score translation does not change the weighted batch-level variance.
 Exact proposition: forall (A:Type) (w v:A->R) (t:R) (xs:list A), batch_mass w xs<>0 -> batch_variance w (fun x=>v x+t) xs=batch_variance w v xs.
 Premises and side conditions: The stated finite-list, real-number, positivity and denominator hypotheses are explicit. An observation is not thereby assumed to have any particular probability distribution.
 Proof/definition method: Rewrite into the canonical FiniteSum fold, use earlier list-pooling facts and Rocq Stdlib real arithmetic; ensure all cross-term cancellations are proved rather than asserted.
 Library reuse: Stdlib Reals/List/Permutation/Ring/Field/Lra/Psatz, FiniteSum and canonical prior ListPoolingAlgebra definitions; never introduce a parallel summation or random-sampling engine.
 Boundary: Deterministic G12 finite-sample aggregation and covariance algebra only; no Gaussian independence, chi-square law, finite-sample statistical coverage, or empirical IQ model is proved.
*)
Theorem batch_variance_translation :
  forall (A:Type) (w v:A->R) (t:R) (xs:list A), batch_mass w xs<>0 -> batch_variance w (fun x=>v x+t) xs=batch_variance w v xs.
Proof.
  intros A w v t xs H; unfold batch_variance; rewrite batch_mean_translation by assumption; rewrite batch_centered_translation; reflexivity.
Qed.

(** [batch_variance_scale] (theorem).
 Mathematical meaning: Scaling every score by a real factor scales the normalized variance by the factor squared.
 Exact proposition: forall (A:Type) (w v:A->R) (t:R) (xs:list A), batch_mass w xs<>0 -> batch_variance w (fun x=>t*v x) xs=t*t*batch_variance w v xs.
 Premises and side conditions: The stated finite-list, real-number, positivity and denominator hypotheses are explicit. An observation is not thereby assumed to have any particular probability distribution.
 Proof/definition method: Rewrite into the canonical FiniteSum fold, use earlier list-pooling facts and Rocq Stdlib real arithmetic; ensure all cross-term cancellations are proved rather than asserted.
 Library reuse: Stdlib Reals/List/Permutation/Ring/Field/Lra/Psatz, FiniteSum and canonical prior ListPoolingAlgebra definitions; never introduce a parallel summation or random-sampling engine.
 Boundary: Deterministic G12 finite-sample aggregation and covariance algebra only; no Gaussian independence, chi-square law, finite-sample statistical coverage, or empirical IQ model is proved.
*)
Theorem batch_variance_scale :
  forall (A:Type) (w v:A->R) (t:R) (xs:list A), batch_mass w xs<>0 -> batch_variance w (fun x=>t*v x) xs=t*t*batch_variance w v xs.
Proof.
  intros A w v t xs H; unfold batch_variance; rewrite batch_mean_scale by assumption; rewrite batch_centered_scale_values; unfold Rdiv; ring.
Qed.

(** [batch_covariance_closed] (theorem).
 Mathematical meaning: Normalized covariance is the raw mixed moment divided by mass minus the product of raw first moments divided by squared mass.
 Exact proposition: forall (A:Type) (w v z:A->R) (xs:list A), batch_mass w xs<>0 -> batch_covariance w v z xs=batch_cross w v z xs/batch_mass w xs-(batch_total w v xs*batch_total w z xs)/(batch_mass w xs*batch_mass w xs).
 Premises and side conditions: The stated finite-list, real-number, positivity and denominator hypotheses are explicit. An observation is not thereby assumed to have any particular probability distribution.
 Proof/definition method: Rewrite into the canonical FiniteSum fold, use earlier list-pooling facts and Rocq Stdlib real arithmetic; ensure all cross-term cancellations are proved rather than asserted.
 Library reuse: Stdlib Reals/List/Permutation/Ring/Field/Lra/Psatz, FiniteSum and canonical prior ListPoolingAlgebra definitions; never introduce a parallel summation or random-sampling engine.
 Boundary: Deterministic G12 finite-sample aggregation and covariance algebra only; no Gaussian independence, chi-square law, finite-sample statistical coverage, or empirical IQ model is proved.
*)
Theorem batch_covariance_closed :
  forall (A:Type) (w v z:A->R) (xs:list A), batch_mass w xs<>0 -> batch_covariance w v z xs=batch_cross w v z xs/batch_mass w xs-(batch_total w v xs*batch_total w z xs)/(batch_mass w xs*batch_mass w xs).
Proof.
  intros A w v z xs H; unfold batch_covariance; rewrite batch_cov_numer_closed by exact H; field; exact H.
Qed.

(** [batch_covariance_constant_zero] (theorem).
 Mathematical meaning: A constant first attribute has zero covariance with any second attribute, given nonzero total weight.
 Exact proposition: forall (A:Type) (w z:A->R) (c:R) (xs:list A), batch_mass w xs<>0 -> batch_covariance w (fun _=>c) z xs=0.
 Premises and side conditions: The stated finite-list, real-number, positivity and denominator hypotheses are explicit. An observation is not thereby assumed to have any particular probability distribution.
 Proof/definition method: Rewrite into the canonical FiniteSum fold, use earlier list-pooling facts and Rocq Stdlib real arithmetic; ensure all cross-term cancellations are proved rather than asserted.
 Library reuse: Stdlib Reals/List/Permutation/Ring/Field/Lra/Psatz, FiniteSum and canonical prior ListPoolingAlgebra definitions; never introduce a parallel summation or random-sampling engine.
 Boundary: Deterministic G12 finite-sample aggregation and covariance algebra only; no Gaussian independence, chi-square law, finite-sample statistical coverage, or empirical IQ model is proved.
*)
Theorem batch_covariance_constant_zero :
  forall (A:Type) (w z:A->R) (c:R) (xs:list A), batch_mass w xs<>0 -> batch_covariance w (fun _=>c) z xs=0.
Proof.
  intros A w z c xs H; unfold batch_covariance,batch_cov_numer,batch_centered_cross; rewrite (batch_mean_constant A w xs c H); transitivity (finite_sum (fun _=>0) xs/batch_mass w xs); [f_equal; apply finite_sum_ext; intro x; ring|rewrite finite_sum_zero; unfold Rdiv; ring].
Qed.

(** [batch_covariance_constant_zero_right] (theorem).
 Mathematical meaning: A constant second attribute has zero covariance with any first attribute, given nonzero total weight.
 Exact proposition: forall (A:Type) (w v:A->R) (c:R) (xs:list A), batch_mass w xs<>0 -> batch_covariance w v (fun _=>c) xs=0.
 Premises and side conditions: The stated finite-list, real-number, positivity and denominator hypotheses are explicit. An observation is not thereby assumed to have any particular probability distribution.
 Proof/definition method: Rewrite into the canonical FiniteSum fold, use earlier list-pooling facts and Rocq Stdlib real arithmetic; ensure all cross-term cancellations are proved rather than asserted.
 Library reuse: Stdlib Reals/List/Permutation/Ring/Field/Lra/Psatz, FiniteSum and canonical prior ListPoolingAlgebra definitions; never introduce a parallel summation or random-sampling engine.
 Boundary: Deterministic G12 finite-sample aggregation and covariance algebra only; no Gaussian independence, chi-square law, finite-sample statistical coverage, or empirical IQ model is proved.
*)
Theorem batch_covariance_constant_zero_right :
  forall (A:Type) (w v:A->R) (c:R) (xs:list A), batch_mass w xs<>0 -> batch_covariance w v (fun _=>c) xs=0.
Proof.
  intros A w v c xs H; rewrite batch_covariance_symmetry; apply batch_covariance_constant_zero; exact H.
Qed.

(** [batch_mean_complement] (theorem).
 Mathematical meaning: The weighted mean success rate and the weighted mean failure rate sum to one for nonzero total mass.
 Exact proposition: forall (A:Type) (w p:A->R) (xs:list A), batch_mass w xs<>0 -> batch_mean w (fun x=>1-p x) xs=1-batch_mean w p xs.
 Premises and side conditions: All restrictions on list support, nonnegative/strictly positive weights, variance-rate domains and denominators are explicit. A deterministic ideal moment identity does not certify independence.
 Proof/definition method: Reuse the checked finite-sum zero and positivity criteria, earlier generic moment/variance decompositions, and standard Rocq real polynomial normalization rather than restating lengthy arithmetic proofs.
 Library reuse: Rocq Stdlib Reals/List/Ring/Lra/Psatz/Field, canonical FiniteSum, SamplingPrecision and prior ListPoolingAlgebra results, including ANOVA and the sharp Bernoulli deficit identity.
 Boundary: These are algebraic G08/G12/G13 and Towers event-rate diagnostics; Gaussian law, chi-square pivot, binomial PMF, independent experimental observations, exact coverage and IQ-model calibration remain outside the claims.
*)
Theorem batch_mean_complement :
  forall (A:Type) (w p:A->R) (xs:list A), batch_mass w xs<>0 -> batch_mean w (fun x=>1-p x) xs=1-batch_mean w p xs.
Proof.
  intros A w p xs Hm; unfold batch_mean; change (batch_failure w p xs/batch_mass w xs=1-batch_total w p xs/batch_mass w xs); rewrite batch_failure_mass_minus_success; field; exact Hm.
Qed.

(** [batch_mean_probability_interval] (theorem).
 Mathematical meaning: For admissible cohort probabilities and nonnegative weights the overall pooled event fraction remains in the unit interval.
 Exact proposition: forall (A:Type) (w p:A->R) (xs:list A), 0<batch_mass w xs -> (forall x, In x xs -> 0<=w x) -> (forall x, In x xs -> 0<=p x<=1) -> 0<=batch_mean w p xs<=1.
 Premises and side conditions: All restrictions on list support, nonnegative/strictly positive weights, variance-rate domains and denominators are explicit. A deterministic ideal moment identity does not certify independence.
 Proof/definition method: Reuse the checked finite-sum zero and positivity criteria, earlier generic moment/variance decompositions, and standard Rocq real polynomial normalization rather than restating lengthy arithmetic proofs.
 Library reuse: Rocq Stdlib Reals/List/Ring/Lra/Psatz/Field, canonical FiniteSum, SamplingPrecision and prior ListPoolingAlgebra results, including ANOVA and the sharp Bernoulli deficit identity.
 Boundary: These are algebraic G08/G12/G13 and Towers event-rate diagnostics; Gaussian law, chi-square pivot, binomial PMF, independent experimental observations, exact coverage and IQ-model calibration remain outside the claims.
*)
Theorem batch_mean_probability_interval :
  forall (A:Type) (w p:A->R) (xs:list A), 0<batch_mass w xs -> (forall x, In x xs -> 0<=w x) -> (forall x, In x xs -> 0<=p x<=1) -> 0<=batch_mean w p xs<=1.
Proof.
  intros A w p xs Hm Hw Hp; apply (batch_mean_interval A w p xs 0 1 Hm Hw); exact Hp.
Qed.

(** [batch_success_le_exposure] (theorem).
 Mathematical meaning: If every cohort success rate is at most one, ideal expected successes cannot exceed total nonnegative exposure.
 Exact proposition: forall (A:Type) (w p:A->R) (xs:list A), (forall x, In x xs -> 0<=w x) -> (forall x, In x xs -> p x<=1) -> batch_total w p xs<=batch_mass w xs.
 Premises and side conditions: All restrictions on list support, nonnegative/strictly positive weights, variance-rate domains and denominators are explicit. A deterministic ideal moment identity does not certify independence.
 Proof/definition method: Reuse the checked finite-sum zero and positivity criteria, earlier generic moment/variance decompositions, and standard Rocq real polynomial normalization rather than restating lengthy arithmetic proofs.
 Library reuse: Rocq Stdlib Reals/List/Ring/Lra/Psatz/Field, canonical FiniteSum, SamplingPrecision and prior ListPoolingAlgebra results, including ANOVA and the sharp Bernoulli deficit identity.
 Boundary: These are algebraic G08/G12/G13 and Towers event-rate diagnostics; Gaussian law, chi-square pivot, binomial PMF, independent experimental observations, exact coverage and IQ-model calibration remain outside the claims.
*)
Theorem batch_success_le_exposure :
  forall (A:Type) (w p:A->R) (xs:list A), (forall x, In x xs -> 0<=w x) -> (forall x, In x xs -> p x<=1) -> batch_total w p xs<=batch_mass w xs.
Proof.
  intros A w p xs Hw Hp; pose proof (batch_failure_nonnegative A w p xs Hw Hp) as Hf; pose proof (batch_success_failure_total A w p xs) as H; lra.
Qed.

(** [batch_failure_le_exposure] (theorem).
 Mathematical meaning: Nonnegative event probabilities imply expected failures do not exceed total exposure.
 Exact proposition: forall (A:Type) (w p:A->R) (xs:list A), (forall x, In x xs -> 0<=w x) -> (forall x, In x xs -> 0<=p x) -> batch_failure w p xs<=batch_mass w xs.
 Premises and side conditions: All restrictions on list support, nonnegative/strictly positive weights, variance-rate domains and denominators are explicit. A deterministic ideal moment identity does not certify independence.
 Proof/definition method: Reuse the checked finite-sum zero and positivity criteria, earlier generic moment/variance decompositions, and standard Rocq real polynomial normalization rather than restating lengthy arithmetic proofs.
 Library reuse: Rocq Stdlib Reals/List/Ring/Lra/Psatz/Field, canonical FiniteSum, SamplingPrecision and prior ListPoolingAlgebra results, including ANOVA and the sharp Bernoulli deficit identity.
 Boundary: These are algebraic G08/G12/G13 and Towers event-rate diagnostics; Gaussian law, chi-square pivot, binomial PMF, independent experimental observations, exact coverage and IQ-model calibration remain outside the claims.
*)
Theorem batch_failure_le_exposure :
  forall (A:Type) (w p:A->R) (xs:list A), (forall x, In x xs -> 0<=w x) -> (forall x, In x xs -> 0<=p x) -> batch_failure w p xs<=batch_mass w xs.
Proof.
  intros A w p xs Hw Hp; pose proof (batch_success_nonnegative A w p xs Hw Hp) as Hs; pose proof (batch_success_failure_total A w p xs) as H; lra.
Qed.

(** [batch_variance_le_both_counts] (theorem).
 Mathematical meaning: Ideal Bernoulli variance is bounded by both complementary expected event counts.
 Exact proposition: forall (A:Type) (w p:A->R) (xs:list A), (forall x, In x xs -> 0<=w x) -> batch_bernoulli_variance w p xs<=batch_total w p xs /\ batch_bernoulli_variance w p xs<=batch_failure w p xs.
 Premises and side conditions: All restrictions on list support, nonnegative/strictly positive weights, variance-rate domains and denominators are explicit. A deterministic ideal moment identity does not certify independence.
 Proof/definition method: Reuse the checked finite-sum zero and positivity criteria, earlier generic moment/variance decompositions, and standard Rocq real polynomial normalization rather than restating lengthy arithmetic proofs.
 Library reuse: Rocq Stdlib Reals/List/Ring/Lra/Psatz/Field, canonical FiniteSum, SamplingPrecision and prior ListPoolingAlgebra results, including ANOVA and the sharp Bernoulli deficit identity.
 Boundary: These are algebraic G08/G12/G13 and Towers event-rate diagnostics; Gaussian law, chi-square pivot, binomial PMF, independent experimental observations, exact coverage and IQ-model calibration remain outside the claims.
*)
Theorem batch_variance_le_both_counts :
  forall (A:Type) (w p:A->R) (xs:list A), (forall x, In x xs -> 0<=w x) -> batch_bernoulli_variance w p xs<=batch_total w p xs /\ batch_bernoulli_variance w p xs<=batch_failure w p xs.
Proof.
  intros A w p xs Hw; split; [apply batch_bernoulli_variance_le_success|apply batch_bernoulli_variance_le_failure]; exact Hw.
Qed.

(** [batch_variance_le_total_exposure] (theorem).
 Mathematical meaning: The sharp one-quarter bound entails an absolute upper bound by sample exposure for nonnegative weights.
 Exact proposition: forall (A:Type) (w p:A->R) (xs:list A), (forall x, In x xs -> 0<=w x) -> batch_bernoulli_variance w p xs<=batch_mass w xs.
 Premises and side conditions: All restrictions on list support, nonnegative/strictly positive weights, variance-rate domains and denominators are explicit. A deterministic ideal moment identity does not certify independence.
 Proof/definition method: Reuse the checked finite-sum zero and positivity criteria, earlier generic moment/variance decompositions, and standard Rocq real polynomial normalization rather than restating lengthy arithmetic proofs.
 Library reuse: Rocq Stdlib Reals/List/Ring/Lra/Psatz/Field, canonical FiniteSum, SamplingPrecision and prior ListPoolingAlgebra results, including ANOVA and the sharp Bernoulli deficit identity.
 Boundary: These are algebraic G08/G12/G13 and Towers event-rate diagnostics; Gaussian law, chi-square pivot, binomial PMF, independent experimental observations, exact coverage and IQ-model calibration remain outside the claims.
*)
Theorem batch_variance_le_total_exposure :
  forall (A:Type) (w p:A->R) (xs:list A), (forall x, In x xs -> 0<=w x) -> batch_bernoulli_variance w p xs<=batch_mass w xs.
Proof.
  intros A w p xs Hw; pose proof (batch_bernoulli_variance_sharp_quarter A w p xs Hw) as H; pose proof (batch_mass_nonnegative A w xs Hw) as Hm; lra.
Qed.

(** [batch_variance_zero_extreme_rates] (theorem).
 Mathematical meaning: Cohorts whose rates are all either zero or one contribute exactly zero ideal Bernoulli variance.
 Exact proposition: forall (A:Type) (w p:A->R) (xs:list A), (forall x, In x xs -> p x=0 \/ p x=1) -> batch_bernoulli_variance w p xs=0.
 Premises and side conditions: All restrictions on list support, nonnegative/strictly positive weights, variance-rate domains and denominators are explicit. A deterministic ideal moment identity does not certify independence.
 Proof/definition method: Reuse the checked finite-sum zero and positivity criteria, earlier generic moment/variance decompositions, and standard Rocq real polynomial normalization rather than restating lengthy arithmetic proofs.
 Library reuse: Rocq Stdlib Reals/List/Ring/Lra/Psatz/Field, canonical FiniteSum, SamplingPrecision and prior ListPoolingAlgebra results, including ANOVA and the sharp Bernoulli deficit identity.
 Boundary: These are algebraic G08/G12/G13 and Towers event-rate diagnostics; Gaussian law, chi-square pivot, binomial PMF, independent experimental observations, exact coverage and IQ-model calibration remain outside the claims.
*)
Theorem batch_variance_zero_extreme_rates :
  forall (A:Type) (w p:A->R) (xs:list A), (forall x, In x xs -> p x=0 \/ p x=1) -> batch_bernoulli_variance w p xs=0.
Proof.
  intros A w p xs Hp; unfold batch_bernoulli_variance; rewrite (finite_sum_ext_in xs (fun x=>w x*sampling_bernoulli_variance (p x)) (fun _=>0)); [apply finite_sum_zero|intros x Hin; destruct (Hp x Hin) as [H|H]; rewrite H; unfold sampling_bernoulli_variance; ring].
Qed.

(** [batch_variance_zero_member_extreme] (theorem).
 Mathematical meaning: A zero nonnegative aggregate Bernoulli variance forces each cohort with positive exposure to have a degenerate rate.
 Exact proposition: forall (A:Type) (w p:A->R) (xs:list A) (x:A), (forall y, In y xs -> 0<=w y) -> (forall y, In y xs -> 0<=p y<=1) -> batch_bernoulli_variance w p xs=0 -> In x xs -> 0<w x -> p x=0 \/ p x=1.
 Premises and side conditions: All restrictions on list support, nonnegative/strictly positive weights, variance-rate domains and denominators are explicit. A deterministic ideal moment identity does not certify independence.
 Proof/definition method: Reuse the checked finite-sum zero and positivity criteria, earlier generic moment/variance decompositions, and standard Rocq real polynomial normalization rather than restating lengthy arithmetic proofs.
 Library reuse: Rocq Stdlib Reals/List/Ring/Lra/Psatz/Field, canonical FiniteSum, SamplingPrecision and prior ListPoolingAlgebra results, including ANOVA and the sharp Bernoulli deficit identity.
 Boundary: These are algebraic G08/G12/G13 and Towers event-rate diagnostics; Gaussian law, chi-square pivot, binomial PMF, independent experimental observations, exact coverage and IQ-model calibration remain outside the claims.
*)
Theorem batch_variance_zero_member_extreme :
  forall (A:Type) (w p:A->R) (xs:list A) (x:A), (forall y, In y xs -> 0<=w y) -> (forall y, In y xs -> 0<=p y<=1) -> batch_bernoulli_variance w p xs=0 -> In x xs -> 0<w x -> p x=0 \/ p x=1.
Proof.
  intros A w p xs x Hw Hp Hz Hin Hwx; unfold batch_bernoulli_variance in Hz; assert (Hnon: forall y, In y xs -> 0<=w y*sampling_bernoulli_variance (p y)). { intros y Hy; apply Rmult_le_pos; [apply Hw; exact Hy|apply sampling_variance_nonnegative; [apply (Hp y Hy)|apply (Hp y Hy)]]. } pose proof (finite_sum_nonnegative_zero xs (fun y=>w y*sampling_bernoulli_variance (p y)) Hnon Hz x Hin) as Hterm; apply Rmult_integral in Hterm; destruct Hterm as [H0|H0]; [lra|apply (proj1 (sampling_variance_zero_iff_extreme (p x) (proj1 (Hp x Hin)) (proj2 (Hp x Hin)))); exact H0].
Qed.

(** [batch_variance_zero_iff_all_extreme] (theorem).
 Mathematical meaning: With strictly positive weights, aggregate ideal Bernoulli variance vanishes exactly when every listed rate is zero or one.
 Exact proposition: forall (A:Type) (w p:A->R) (xs:list A), (forall x, In x xs -> 0<w x) -> (forall x, In x xs -> 0<=p x<=1) -> (batch_bernoulli_variance w p xs=0 <-> forall x, In x xs -> p x=0 \/ p x=1).
 Premises and side conditions: All restrictions on list support, nonnegative/strictly positive weights, variance-rate domains and denominators are explicit. A deterministic ideal moment identity does not certify independence.
 Proof/definition method: Reuse the checked finite-sum zero and positivity criteria, earlier generic moment/variance decompositions, and standard Rocq real polynomial normalization rather than restating lengthy arithmetic proofs.
 Library reuse: Rocq Stdlib Reals/List/Ring/Lra/Psatz/Field, canonical FiniteSum, SamplingPrecision and prior ListPoolingAlgebra results, including ANOVA and the sharp Bernoulli deficit identity.
 Boundary: These are algebraic G08/G12/G13 and Towers event-rate diagnostics; Gaussian law, chi-square pivot, binomial PMF, independent experimental observations, exact coverage and IQ-model calibration remain outside the claims.
*)
Theorem batch_variance_zero_iff_all_extreme :
  forall (A:Type) (w p:A->R) (xs:list A), (forall x, In x xs -> 0<w x) -> (forall x, In x xs -> 0<=p x<=1) -> (batch_bernoulli_variance w p xs=0 <-> forall x, In x xs -> p x=0 \/ p x=1).
Proof.
  intros A w p xs Hw Hp; split; [intros Hz x Hin; apply (batch_variance_zero_member_extreme A w p xs x); [intros y Hy; specialize (Hw y Hy); lra|exact Hp|exact Hz|exact Hin|apply Hw; exact Hin]|apply batch_variance_zero_extreme_rates].
Qed.

(** [batch_variance_maximum_requires_half] (theorem).
 Mathematical meaning: Saturating the sharp aggregate variance bound forces every strictly positive weight cohort to have event rate one half.
 Exact proposition: forall (A:Type) (w p:A->R) (xs:list A), (forall x, In x xs -> 0<w x) -> 4*batch_bernoulli_variance w p xs=batch_mass w xs -> forall x, In x xs -> p x=1/2.
 Premises and side conditions: All restrictions on list support, nonnegative/strictly positive weights, variance-rate domains and denominators are explicit. A deterministic ideal moment identity does not certify independence.
 Proof/definition method: Reuse the checked finite-sum zero and positivity criteria, earlier generic moment/variance decompositions, and standard Rocq real polynomial normalization rather than restating lengthy arithmetic proofs.
 Library reuse: Rocq Stdlib Reals/List/Ring/Lra/Psatz/Field, canonical FiniteSum, SamplingPrecision and prior ListPoolingAlgebra results, including ANOVA and the sharp Bernoulli deficit identity.
 Boundary: These are algebraic G08/G12/G13 and Towers event-rate diagnostics; Gaussian law, chi-square pivot, binomial PMF, independent experimental observations, exact coverage and IQ-model calibration remain outside the claims.
*)
Theorem batch_variance_maximum_requires_half :
  forall (A:Type) (w p:A->R) (xs:list A), (forall x, In x xs -> 0<w x) -> 4*batch_bernoulli_variance w p xs=batch_mass w xs -> forall x, In x xs -> p x=1/2.
Proof.
  intros A w p xs Hw Hmax x Hin; assert (Hz:finite_sum (fun y=>w y*(2*p y-1)*(2*p y-1)) xs=0). { rewrite <- batch_bernoulli_deficit_square; lra. } assert (Hnon:forall y, In y xs -> 0<=w y*(2*p y-1)*(2*p y-1)). { intros y Hy; replace (w y*(2*p y-1)*(2*p y-1)) with (w y*((2*p y-1)*(2*p y-1))) by ring; apply Rmult_le_pos; [apply Rlt_le, Hw; exact Hy|pose proof (Rle_0_sqr (2*p y-1)) as E; unfold Rsqr in E; exact E]. } pose proof (finite_sum_nonnegative_zero xs (fun y=>w y*(2*p y-1)*(2*p y-1)) Hnon Hz x Hin) as Hterm; replace (w x*(2*p x-1)*(2*p x-1)) with (w x*((2*p x-1)*(2*p x-1))) in Hterm by ring; apply Rmult_integral in Hterm; destruct Hterm as [Hwz|Hsq]; [pose proof (Hw x Hin); lra|apply Rmult_integral in Hsq; destruct Hsq; lra].
Qed.

(** [batch_variance_maximum_iff_half] (theorem).
 Mathematical meaning: For strictly positive weights the ideal aggregate variance bound is saturated exactly by universally balanced cohort rates.
 Exact proposition: forall (A:Type) (w p:A->R) (xs:list A), (forall x, In x xs -> 0<w x) -> (4*batch_bernoulli_variance w p xs=batch_mass w xs <-> forall x, In x xs -> p x=1/2).
 Premises and side conditions: All restrictions on list support, nonnegative/strictly positive weights, variance-rate domains and denominators are explicit. A deterministic ideal moment identity does not certify independence.
 Proof/definition method: Reuse the checked finite-sum zero and positivity criteria, earlier generic moment/variance decompositions, and standard Rocq real polynomial normalization rather than restating lengthy arithmetic proofs.
 Library reuse: Rocq Stdlib Reals/List/Ring/Lra/Psatz/Field, canonical FiniteSum, SamplingPrecision and prior ListPoolingAlgebra results, including ANOVA and the sharp Bernoulli deficit identity.
 Boundary: These are algebraic G08/G12/G13 and Towers event-rate diagnostics; Gaussian law, chi-square pivot, binomial PMF, independent experimental observations, exact coverage and IQ-model calibration remain outside the claims.
*)
Theorem batch_variance_maximum_iff_half :
  forall (A:Type) (w p:A->R) (xs:list A), (forall x, In x xs -> 0<w x) -> (4*batch_bernoulli_variance w p xs=batch_mass w xs <-> forall x, In x xs -> p x=1/2).
Proof.
  intros A w p xs Hw; split; [apply batch_variance_maximum_requires_half; exact Hw|apply batch_bernoulli_variance_max_attained].
Qed.

(** [batch_centered_zero_if_constant] (theorem).
 Mathematical meaning: If every listed group center equals the reference, the weighted corrected sum of squares is zero.
 Exact proposition: forall (A:Type) (w v:A->R) (xs:list A) (c:R), (forall x, In x xs -> v x=c) -> batch_centered w v c xs=0.
 Premises and side conditions: All restrictions on list support, nonnegative/strictly positive weights, variance-rate domains and denominators are explicit. A deterministic ideal moment identity does not certify independence.
 Proof/definition method: Reuse the checked finite-sum zero and positivity criteria, earlier generic moment/variance decompositions, and standard Rocq real polynomial normalization rather than restating lengthy arithmetic proofs.
 Library reuse: Rocq Stdlib Reals/List/Ring/Lra/Psatz/Field, canonical FiniteSum, SamplingPrecision and prior ListPoolingAlgebra results, including ANOVA and the sharp Bernoulli deficit identity.
 Boundary: These are algebraic G08/G12/G13 and Towers event-rate diagnostics; Gaussian law, chi-square pivot, binomial PMF, independent experimental observations, exact coverage and IQ-model calibration remain outside the claims.
*)
Theorem batch_centered_zero_if_constant :
  forall (A:Type) (w v:A->R) (xs:list A) (c:R), (forall x, In x xs -> v x=c) -> batch_centered w v c xs=0.
Proof.
  intros A w v xs c Hv; unfold batch_centered; rewrite (finite_sum_ext_in xs (fun x=>w x*(v x-c)*(v x-c)) (fun _=>0)); [apply finite_sum_zero|intros x Hin; rewrite (Hv x Hin); ring].
Qed.

(** [batch_centered_zero_forces_constant] (theorem).
 Mathematical meaning: With strictly positive sample weights, zero corrected dispersion forces every batch mean to equal the chosen center.
 Exact proposition: forall (A:Type) (w v:A->R) (xs:list A) (c:R), (forall x, In x xs -> 0<w x) -> batch_centered w v c xs=0 -> forall x, In x xs -> v x=c.
 Premises and side conditions: All restrictions on list support, nonnegative/strictly positive weights, variance-rate domains and denominators are explicit. A deterministic ideal moment identity does not certify independence.
 Proof/definition method: Reuse the checked finite-sum zero and positivity criteria, earlier generic moment/variance decompositions, and standard Rocq real polynomial normalization rather than restating lengthy arithmetic proofs.
 Library reuse: Rocq Stdlib Reals/List/Ring/Lra/Psatz/Field, canonical FiniteSum, SamplingPrecision and prior ListPoolingAlgebra results, including ANOVA and the sharp Bernoulli deficit identity.
 Boundary: These are algebraic G08/G12/G13 and Towers event-rate diagnostics; Gaussian law, chi-square pivot, binomial PMF, independent experimental observations, exact coverage and IQ-model calibration remain outside the claims.
*)
Theorem batch_centered_zero_forces_constant :
  forall (A:Type) (w v:A->R) (xs:list A) (c:R), (forall x, In x xs -> 0<w x) -> batch_centered w v c xs=0 -> forall x, In x xs -> v x=c.
Proof.
  intros A w v xs c Hw Hz x Hin; unfold batch_centered in Hz; assert (Hnon:forall y, In y xs -> 0<=w y*(v y-c)*(v y-c)). { intros y Hy; replace (w y*(v y-c)*(v y-c)) with (w y*((v y-c)*(v y-c))) by ring; apply Rmult_le_pos; [apply Rlt_le, Hw; exact Hy|pose proof (Rle_0_sqr (v y-c)) as E; unfold Rsqr in E; exact E]. } pose proof (finite_sum_nonnegative_zero xs (fun y=>w y*(v y-c)*(v y-c)) Hnon Hz x Hin) as Hterm; replace (w x*(v x-c)*(v x-c)) with (w x*((v x-c)*(v x-c))) in Hterm by ring; apply Rmult_integral in Hterm; destruct Hterm as [Hwx|Hsq]; [pose proof (Hw x Hin); lra|apply Rmult_integral in Hsq; destruct Hsq; lra].
Qed.

(** [batch_centered_zero_iff_constant] (theorem).
 Mathematical meaning: Under strictly positive listed weights, zero weighted corrected dispersion is equivalent to all values being the same reference.
 Exact proposition: forall (A:Type) (w v:A->R) (xs:list A) (c:R), (forall x, In x xs -> 0<w x) -> (batch_centered w v c xs=0 <-> forall x, In x xs -> v x=c).
 Premises and side conditions: All restrictions on list support, nonnegative/strictly positive weights, variance-rate domains and denominators are explicit. A deterministic ideal moment identity does not certify independence.
 Proof/definition method: Reuse the checked finite-sum zero and positivity criteria, earlier generic moment/variance decompositions, and standard Rocq real polynomial normalization rather than restating lengthy arithmetic proofs.
 Library reuse: Rocq Stdlib Reals/List/Ring/Lra/Psatz/Field, canonical FiniteSum, SamplingPrecision and prior ListPoolingAlgebra results, including ANOVA and the sharp Bernoulli deficit identity.
 Boundary: These are algebraic G08/G12/G13 and Towers event-rate diagnostics; Gaussian law, chi-square pivot, binomial PMF, independent experimental observations, exact coverage and IQ-model calibration remain outside the claims.
*)
Theorem batch_centered_zero_iff_constant :
  forall (A:Type) (w v:A->R) (xs:list A) (c:R), (forall x, In x xs -> 0<w x) -> (batch_centered w v c xs=0 <-> forall x, In x xs -> v x=c).
Proof.
  intros A w v xs c Hw; split; [apply batch_centered_zero_forces_constant; exact Hw|apply batch_centered_zero_if_constant].
Qed.

(** [batch_variance_pooled_equality_iff_homogeneous] (theorem).
 Mathematical meaning: For positive weights, heterogeneous ideal count variance reaches the homogeneous matched-rate benchmark exactly for constant cohort rates.
 Exact proposition: forall (A:Type) (w p:A->R) (xs:list A), 0<batch_mass w xs -> (forall x, In x xs -> 0<w x) -> (batch_bernoulli_variance w p xs=batch_mass w xs*sampling_bernoulli_variance (batch_mean w p xs) <-> forall x, In x xs -> p x=batch_mean w p xs).
 Premises and side conditions: All restrictions on list support, nonnegative/strictly positive weights, variance-rate domains and denominators are explicit. A deterministic ideal moment identity does not certify independence.
 Proof/definition method: Reuse the checked finite-sum zero and positivity criteria, earlier generic moment/variance decompositions, and standard Rocq real polynomial normalization rather than restating lengthy arithmetic proofs.
 Library reuse: Rocq Stdlib Reals/List/Ring/Lra/Psatz/Field, canonical FiniteSum, SamplingPrecision and prior ListPoolingAlgebra results, including ANOVA and the sharp Bernoulli deficit identity.
 Boundary: These are algebraic G08/G12/G13 and Towers event-rate diagnostics; Gaussian law, chi-square pivot, binomial PMF, independent experimental observations, exact coverage and IQ-model calibration remain outside the claims.
*)
Theorem batch_variance_pooled_equality_iff_homogeneous :
  forall (A:Type) (w p:A->R) (xs:list A), 0<batch_mass w xs -> (forall x, In x xs -> 0<w x) -> (batch_bernoulli_variance w p xs=batch_mass w xs*sampling_bernoulli_variance (batch_mean w p xs) <-> forall x, In x xs -> p x=batch_mean w p xs).
Proof.
  intros A w p xs Hm Hw; pose proof (batch_bernoulli_variance_pooled_decomposition A w p xs Hm) as H; rewrite <- (batch_centered_zero_iff_constant A w p xs (batch_mean w p xs) Hw); split; intro He; lra.
Qed.

(** [batch_success_rate_difference] (theorem).
 Mathematical meaning: The change in ideal expected successes between two arbitrary rate vectors equals their weighted pointwise difference.
 Exact proposition: forall (A:Type) (w p q:A->R) (xs:list A), batch_total w q xs-batch_total w p xs=batch_total w (fun x=>q x-p x) xs.
 Premises and side conditions: All restrictions on list support, nonnegative/strictly positive weights, variance-rate domains and denominators are explicit. A deterministic ideal moment identity does not certify independence.
 Proof/definition method: Reuse the checked finite-sum zero and positivity criteria, earlier generic moment/variance decompositions, and standard Rocq real polynomial normalization rather than restating lengthy arithmetic proofs.
 Library reuse: Rocq Stdlib Reals/List/Ring/Lra/Psatz/Field, canonical FiniteSum, SamplingPrecision and prior ListPoolingAlgebra results, including ANOVA and the sharp Bernoulli deficit identity.
 Boundary: These are algebraic G08/G12/G13 and Towers event-rate diagnostics; Gaussian law, chi-square pivot, binomial PMF, independent experimental observations, exact coverage and IQ-model calibration remain outside the claims.
*)
Theorem batch_success_rate_difference :
  forall (A:Type) (w p q:A->R) (xs:list A), batch_total w q xs-batch_total w p xs=batch_total w (fun x=>q x-p x) xs.
Proof.
  intros A w p q xs; unfold batch_total; transitivity (finite_sum (fun x=>w x*q x-w x*p x) xs); [rewrite finite_sum_sub; reflexivity|apply finite_sum_ext; intro x; ring].
Qed.

(** [batch_failure_rate_difference] (theorem).
 Mathematical meaning: Changing cohort rates changes failures by the negative of the corresponding expected success-count change.
 Exact proposition: forall (A:Type) (w p q:A->R) (xs:list A), batch_failure w q xs-batch_failure w p xs=-(batch_total w q xs-batch_total w p xs).
 Premises and side conditions: All restrictions on list support, nonnegative/strictly positive weights, variance-rate domains and denominators are explicit. A deterministic ideal moment identity does not certify independence.
 Proof/definition method: Reuse the checked finite-sum zero and positivity criteria, earlier generic moment/variance decompositions, and standard Rocq real polynomial normalization rather than restating lengthy arithmetic proofs.
 Library reuse: Rocq Stdlib Reals/List/Ring/Lra/Psatz/Field, canonical FiniteSum, SamplingPrecision and prior ListPoolingAlgebra results, including ANOVA and the sharp Bernoulli deficit identity.
 Boundary: These are algebraic G08/G12/G13 and Towers event-rate diagnostics; Gaussian law, chi-square pivot, binomial PMF, independent experimental observations, exact coverage and IQ-model calibration remain outside the claims.
*)
Theorem batch_failure_rate_difference :
  forall (A:Type) (w p q:A->R) (xs:list A), batch_failure w q xs-batch_failure w p xs=-(batch_total w q xs-batch_total w p xs).
Proof.
  intros A w p q xs; rewrite !batch_failure_mass_minus_success; ring.
Qed.

(** [batch_variance_rate_difference] (theorem).
 Mathematical meaning: The ideal variance change factors exactly by the cohort rate difference and the complement of the sum of old and new rates.
 Exact proposition: forall (A:Type) (w p q:A->R) (xs:list A), batch_bernoulli_variance w q xs-batch_bernoulli_variance w p xs=finite_sum (fun x=>w x*(q x-p x)*(1-p x-q x)) xs.
 Premises and side conditions: All restrictions on list support, nonnegative/strictly positive weights, variance-rate domains and denominators are explicit. A deterministic ideal moment identity does not certify independence.
 Proof/definition method: Reuse the checked finite-sum zero and positivity criteria, earlier generic moment/variance decompositions, and standard Rocq real polynomial normalization rather than restating lengthy arithmetic proofs.
 Library reuse: Rocq Stdlib Reals/List/Ring/Lra/Psatz/Field, canonical FiniteSum, SamplingPrecision and prior ListPoolingAlgebra results, including ANOVA and the sharp Bernoulli deficit identity.
 Boundary: These are algebraic G08/G12/G13 and Towers event-rate diagnostics; Gaussian law, chi-square pivot, binomial PMF, independent experimental observations, exact coverage and IQ-model calibration remain outside the claims.
*)
Theorem batch_variance_rate_difference :
  forall (A:Type) (w p q:A->R) (xs:list A), batch_bernoulli_variance w q xs-batch_bernoulli_variance w p xs=finite_sum (fun x=>w x*(q x-p x)*(1-p x-q x)) xs.
Proof.
  intros A w p q xs; unfold batch_bernoulli_variance; transitivity (finite_sum (fun x=>w x*sampling_bernoulli_variance (q x)-w x*sampling_bernoulli_variance (p x)) xs); [rewrite finite_sum_sub; reflexivity|apply finite_sum_ext; intro x; unfold sampling_bernoulli_variance; ring].
Qed.

(** [batch_variance_rate_shift_uniform] (theorem).
 Mathematical meaning: A common rate increment changes ideal count variance by a linear mass term, a first-moment term, and a quadratic mass penalty.
 Exact proposition: forall (A:Type) (w p:A->R) (xs:list A) (c:R), batch_bernoulli_variance w (fun x=>p x+c) xs=batch_bernoulli_variance w p xs+c*batch_mass w xs-2*c*batch_total w p xs-c*c*batch_mass w xs.
 Premises and side conditions: All restrictions on list support, nonnegative/strictly positive weights, variance-rate domains and denominators are explicit. A deterministic ideal moment identity does not certify independence.
 Proof/definition method: Reuse the checked finite-sum zero and positivity criteria, earlier generic moment/variance decompositions, and standard Rocq real polynomial normalization rather than restating lengthy arithmetic proofs.
 Library reuse: Rocq Stdlib Reals/List/Ring/Lra/Psatz/Field, canonical FiniteSum, SamplingPrecision and prior ListPoolingAlgebra results, including ANOVA and the sharp Bernoulli deficit identity.
 Boundary: These are algebraic G08/G12/G13 and Towers event-rate diagnostics; Gaussian law, chi-square pivot, binomial PMF, independent experimental observations, exact coverage and IQ-model calibration remain outside the claims.
*)
Theorem batch_variance_rate_shift_uniform :
  forall (A:Type) (w p:A->R) (xs:list A) (c:R), batch_bernoulli_variance w (fun x=>p x+c) xs=batch_bernoulli_variance w p xs+c*batch_mass w xs-2*c*batch_total w p xs-c*c*batch_mass w xs.
Proof.
  intros A w p xs c; pose proof (batch_variance_rate_difference A w p (fun x=>p x+c) xs) as H; assert (E:finite_sum (fun x=>w x*((p x+c)-p x)*(1-p x-(p x+c))) xs=c*batch_mass w xs-2*c*batch_total w p xs-c*c*batch_mass w xs). { transitivity (finite_sum (fun x=>(c*w x-(2*c)*(w x*p x))-(c*c)*w x) xs); [apply finite_sum_ext; intro x; ring|rewrite !finite_sum_sub, !finite_sum_scale; unfold batch_mass,batch_total; ring]. } rewrite E in H; lra.
Qed.

(** [batch_variance_monotone_below_half] (theorem).
 Mathematical meaning: If all rates increase but remain at most one half, ideal Bernoulli variance cannot decrease.
 Exact proposition: forall (A:Type) (w p q:A->R) (xs:list A), (forall x, In x xs -> 0<=w x) -> (forall x, In x xs -> p x<=q x<=1/2) -> batch_bernoulli_variance w p xs<=batch_bernoulli_variance w q xs.
 Premises and side conditions: All restrictions on list support, nonnegative/strictly positive weights, variance-rate domains and denominators are explicit. A deterministic ideal moment identity does not certify independence.
 Proof/definition method: Reuse the checked finite-sum zero and positivity criteria, earlier generic moment/variance decompositions, and standard Rocq real polynomial normalization rather than restating lengthy arithmetic proofs.
 Library reuse: Rocq Stdlib Reals/List/Ring/Lra/Psatz/Field, canonical FiniteSum, SamplingPrecision and prior ListPoolingAlgebra results, including ANOVA and the sharp Bernoulli deficit identity.
 Boundary: These are algebraic G08/G12/G13 and Towers event-rate diagnostics; Gaussian law, chi-square pivot, binomial PMF, independent experimental observations, exact coverage and IQ-model calibration remain outside the claims.
*)
Theorem batch_variance_monotone_below_half :
  forall (A:Type) (w p q:A->R) (xs:list A), (forall x, In x xs -> 0<=w x) -> (forall x, In x xs -> p x<=q x<=1/2) -> batch_bernoulli_variance w p xs<=batch_bernoulli_variance w q xs.
Proof.
  intros A w p q xs Hw Hp; pose proof (batch_variance_rate_difference A w p q xs) as H; rewrite H; assert (Hnon:0<=finite_sum (fun x=>w x*(q x-p x)*(1-p x-q x)) xs). { apply finite_sum_nonnegative; intros x Hin; pose proof (Hw x Hin) as E; pose proof (Hp x Hin) as F; nra. } lra.
Qed.

(** [batch_variance_monotone_above_half] (theorem).
 Mathematical meaning: If all rates increase starting at one half, ideal Bernoulli variance cannot increase.
 Exact proposition: forall (A:Type) (w p q:A->R) (xs:list A), (forall x, In x xs -> 0<=w x) -> (forall x, In x xs -> 1/2<=p x<=q x) -> batch_bernoulli_variance w q xs<=batch_bernoulli_variance w p xs.
 Premises and side conditions: All restrictions on list support, nonnegative/strictly positive weights, variance-rate domains and denominators are explicit. A deterministic ideal moment identity does not certify independence.
 Proof/definition method: Reuse the checked finite-sum zero and positivity criteria, earlier generic moment/variance decompositions, and standard Rocq real polynomial normalization rather than restating lengthy arithmetic proofs.
 Library reuse: Rocq Stdlib Reals/List/Ring/Lra/Psatz/Field, canonical FiniteSum, SamplingPrecision and prior ListPoolingAlgebra results, including ANOVA and the sharp Bernoulli deficit identity.
 Boundary: These are algebraic G08/G12/G13 and Towers event-rate diagnostics; Gaussian law, chi-square pivot, binomial PMF, independent experimental observations, exact coverage and IQ-model calibration remain outside the claims.
*)
Theorem batch_variance_monotone_above_half :
  forall (A:Type) (w p q:A->R) (xs:list A), (forall x, In x xs -> 0<=w x) -> (forall x, In x xs -> 1/2<=p x<=q x) -> batch_bernoulli_variance w q xs<=batch_bernoulli_variance w p xs.
Proof.
  intros A w p q xs Hw Hp; pose proof (batch_variance_rate_difference A w p q xs) as H; rewrite H; assert (Hnon:finite_sum (fun x=>w x*(q x-p x)*(1-p x-q x)) xs<=0). { assert (E:0<=finite_sum (fun x=>- (w x*(q x-p x)*(1-p x-q x))) xs). { apply finite_sum_nonnegative; intros x Hin; pose proof (Hw x Hin) as W; pose proof (Hp x Hin) as P; nra. } rewrite finite_sum_neg in E; lra. } lra.
Qed.

(** [batch_success_strict_positive_member] (theorem).
 Mathematical meaning: A positive rate in one cohort with positive weight ensures a positive total ideal success count when other contributions are nonnegative.
 Exact proposition: forall (A:Type) (w p:A->R) (xs:list A) (x:A), (forall y, In y xs -> 0<=w y) -> (forall y, In y xs -> 0<=p y) -> In x xs -> 0<w x -> 0<p x -> 0<batch_total w p xs.
 Premises and side conditions: All restrictions on list support, nonnegative/strictly positive weights, variance-rate domains and denominators are explicit. A deterministic ideal moment identity does not certify independence.
 Proof/definition method: Reuse the checked finite-sum zero and positivity criteria, earlier generic moment/variance decompositions, and standard Rocq real polynomial normalization rather than restating lengthy arithmetic proofs.
 Library reuse: Rocq Stdlib Reals/List/Ring/Lra/Psatz/Field, canonical FiniteSum, SamplingPrecision and prior ListPoolingAlgebra results, including ANOVA and the sharp Bernoulli deficit identity.
 Boundary: These are algebraic G08/G12/G13 and Towers event-rate diagnostics; Gaussian law, chi-square pivot, binomial PMF, independent experimental observations, exact coverage and IQ-model calibration remain outside the claims.
*)
Theorem batch_success_strict_positive_member :
  forall (A:Type) (w p:A->R) (xs:list A) (x:A), (forall y, In y xs -> 0<=w y) -> (forall y, In y xs -> 0<=p y) -> In x xs -> 0<w x -> 0<p x -> 0<batch_total w p xs.
Proof.
  intros A w p xs x Hw Hp Hin Hwx Hpx; unfold batch_total; apply (finite_sum_positive_of_positive_member xs (fun y=>w y*p y) x); [intros y Hy; apply Rmult_le_pos; [apply Hw|apply Hp]; exact Hy|exact Hin|apply Rmult_lt_0_compat; assumption].
Qed.

(** [batch_variance_strict_positive_member] (theorem).
 Mathematical meaning: One positively weighted nondegenerate Bernoulli cohort makes the total ideal variance strictly positive when all other cohorts are admissible.
 Exact proposition: forall (A:Type) (w p:A->R) (xs:list A) (x:A), (forall y, In y xs -> 0<=w y) -> (forall y, In y xs -> 0<=p y<=1) -> In x xs -> 0<w x -> 0<p x<1 -> 0<batch_bernoulli_variance w p xs.
 Premises and side conditions: All restrictions on list support, nonnegative/strictly positive weights, variance-rate domains and denominators are explicit. A deterministic ideal moment identity does not certify independence.
 Proof/definition method: Reuse the checked finite-sum zero and positivity criteria, earlier generic moment/variance decompositions, and standard Rocq real polynomial normalization rather than restating lengthy arithmetic proofs.
 Library reuse: Rocq Stdlib Reals/List/Ring/Lra/Psatz/Field, canonical FiniteSum, SamplingPrecision and prior ListPoolingAlgebra results, including ANOVA and the sharp Bernoulli deficit identity.
 Boundary: These are algebraic G08/G12/G13 and Towers event-rate diagnostics; Gaussian law, chi-square pivot, binomial PMF, independent experimental observations, exact coverage and IQ-model calibration remain outside the claims.
*)
Theorem batch_variance_strict_positive_member :
  forall (A:Type) (w p:A->R) (xs:list A) (x:A), (forall y, In y xs -> 0<=w y) -> (forall y, In y xs -> 0<=p y<=1) -> In x xs -> 0<w x -> 0<p x<1 -> 0<batch_bernoulli_variance w p xs.
Proof.
  intros A w p xs x Hw Hp Hin Hwx Hpx; unfold batch_bernoulli_variance; apply (finite_sum_positive_of_positive_member xs (fun y=>w y*sampling_bernoulli_variance (p y)) x); [intros y Hy; apply Rmult_le_pos; [apply Hw; exact Hy|apply sampling_variance_nonnegative; [apply (Hp y Hy)|apply (Hp y Hy)]]|exact Hin|apply Rmult_lt_0_compat; [exact Hwx|apply sampling_variance_strictly_positive; [apply Hpx|apply Hpx]]].
Qed.

(** [batch_mass_member_bound] (theorem).
 Mathematical meaning: Every nonnegative individual group weight is at most the aggregate sample-size exposure.
 Exact proposition: forall (A:Type) (w:A->R) (xs:list A) (x:A), (forall y, In y xs -> 0<=w y) -> In x xs -> w x<=batch_mass w xs.
 Premises and side conditions: All restrictions on list support, nonnegative/strictly positive weights, variance-rate domains and denominators are explicit. A deterministic ideal moment identity does not certify independence.
 Proof/definition method: Reuse the checked finite-sum zero and positivity criteria, earlier generic moment/variance decompositions, and standard Rocq real polynomial normalization rather than restating lengthy arithmetic proofs.
 Library reuse: Rocq Stdlib Reals/List/Ring/Lra/Psatz/Field, canonical FiniteSum, SamplingPrecision and prior ListPoolingAlgebra results, including ANOVA and the sharp Bernoulli deficit identity.
 Boundary: These are algebraic G08/G12/G13 and Towers event-rate diagnostics; Gaussian law, chi-square pivot, binomial PMF, independent experimental observations, exact coverage and IQ-model calibration remain outside the claims.
*)
Theorem batch_mass_member_bound :
  forall (A:Type) (w:A->R) (xs:list A) (x:A), (forall y, In y xs -> 0<=w y) -> In x xs -> w x<=batch_mass w xs.
Proof.
  intros A w xs x Hw Hin; unfold batch_mass; apply (finite_sum_member_le xs w x Hw Hin).
Qed.

(** [batch_variance_zero_weights] (theorem).
 Mathematical meaning: All-zero exposure weights force the ideal cohort count variance to vanish even when nominal probabilities are arbitrary.
 Exact proposition: forall (A:Type) (w p:A->R) (xs:list A), (forall x, In x xs -> w x=0) -> batch_bernoulli_variance w p xs=0.
 Premises and side conditions: All restrictions on list support, nonnegative/strictly positive weights, variance-rate domains and denominators are explicit. A deterministic ideal moment identity does not certify independence.
 Proof/definition method: Reuse the checked finite-sum zero and positivity criteria, earlier generic moment/variance decompositions, and standard Rocq real polynomial normalization rather than restating lengthy arithmetic proofs.
 Library reuse: Rocq Stdlib Reals/List/Ring/Lra/Psatz/Field, canonical FiniteSum, SamplingPrecision and prior ListPoolingAlgebra results, including ANOVA and the sharp Bernoulli deficit identity.
 Boundary: These are algebraic G08/G12/G13 and Towers event-rate diagnostics; Gaussian law, chi-square pivot, binomial PMF, independent experimental observations, exact coverage and IQ-model calibration remain outside the claims.
*)
Theorem batch_variance_zero_weights :
  forall (A:Type) (w p:A->R) (xs:list A), (forall x, In x xs -> w x=0) -> batch_bernoulli_variance w p xs=0.
Proof.
  intros A w p xs Hw; unfold batch_bernoulli_variance; rewrite (finite_sum_ext_in xs (fun x=>w x*sampling_bernoulli_variance (p x)) (fun _=>0)); [apply finite_sum_zero|intros x Hin; rewrite (Hw x Hin); ring].
Qed.

(** [batch_centered_unique_minimizer] (theorem).
 Mathematical meaning: The weighted mean is the unique minimizer of reference-centered dispersion for positive total mass.
 Exact proposition: forall (A:Type) (w v:A->R) (xs:list A) (c:R), 0<batch_mass w xs -> batch_centered w v c xs=batch_centered w v (batch_mean w v xs) xs -> c=batch_mean w v xs.
 Premises and side conditions: All restrictions on list support, nonnegative/strictly positive weights, variance-rate domains and denominators are explicit. A deterministic ideal moment identity does not certify independence.
 Proof/definition method: Reuse the checked finite-sum zero and positivity criteria, earlier generic moment/variance decompositions, and standard Rocq real polynomial normalization rather than restating lengthy arithmetic proofs.
 Library reuse: Rocq Stdlib Reals/List/Ring/Lra/Psatz/Field, canonical FiniteSum, SamplingPrecision and prior ListPoolingAlgebra results, including ANOVA and the sharp Bernoulli deficit identity.
 Boundary: These are algebraic G08/G12/G13 and Towers event-rate diagnostics; Gaussian law, chi-square pivot, binomial PMF, independent experimental observations, exact coverage and IQ-model calibration remain outside the claims.
*)
Theorem batch_centered_unique_minimizer :
  forall (A:Type) (w v:A->R) (xs:list A) (c:R), 0<batch_mass w xs -> batch_centered w v c xs=batch_centered w v (batch_mean w v xs) xs -> c=batch_mean w v xs.
Proof.
  intros A w v xs c Hm Heq; rewrite (batch_centered_mean_correction A w v xs c) in Heq by lra; assert (Hz:(batch_mean w v xs-c)*(batch_mean w v xs-c)=0) by nra; apply Rmult_integral in Hz; destruct Hz; lra.
Qed.

(** [batch_centered_strictly_larger_off_mean] (theorem).
 Mathematical meaning: Any reference differing from the weighted mean has strictly larger corrected dispersion for positive total mass.
 Exact proposition: forall (A:Type) (w v:A->R) (xs:list A) (c:R), 0<batch_mass w xs -> c<>batch_mean w v xs -> batch_centered w v (batch_mean w v xs) xs<batch_centered w v c xs.
 Premises and side conditions: All restrictions on list support, nonnegative/strictly positive weights, variance-rate domains and denominators are explicit. A deterministic ideal moment identity does not certify independence.
 Proof/definition method: Reuse the checked finite-sum zero and positivity criteria, earlier generic moment/variance decompositions, and standard Rocq real polynomial normalization rather than restating lengthy arithmetic proofs.
 Library reuse: Rocq Stdlib Reals/List/Ring/Lra/Psatz/Field, canonical FiniteSum, SamplingPrecision and prior ListPoolingAlgebra results, including ANOVA and the sharp Bernoulli deficit identity.
 Boundary: These are algebraic G08/G12/G13 and Towers event-rate diagnostics; Gaussian law, chi-square pivot, binomial PMF, independent experimental observations, exact coverage and IQ-model calibration remain outside the claims.
*)
Theorem batch_centered_strictly_larger_off_mean :
  forall (A:Type) (w v:A->R) (xs:list A) (c:R), 0<batch_mass w xs -> c<>batch_mean w v xs -> batch_centered w v (batch_mean w v xs) xs<batch_centered w v c xs.
Proof.
  intros A w v xs c Hm Hne; rewrite (batch_centered_mean_correction A w v xs c) by lra; assert (Hs:0<(batch_mean w v xs-c)*(batch_mean w v xs-c)). { destruct (Rlt_dec (batch_mean w v xs) c); nra. } nra.
Qed.
