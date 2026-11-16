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
