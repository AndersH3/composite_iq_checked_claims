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
Require Import FiniteSum PooledMomentsAlgebra.
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
