(** Module: FiniteSum.v
   Purpose: Single shared implementation of finite real-valued sums.
   Supplies reusable algebraic and order properties of an explicitly enumerated sum, avoiding separate recursive summations in downstream modules.
   Mathematical representation: finite_sum f xs is fold_right Rplus 0 (map f xs), using Rocq standard list primitives and real addition.
   Explicit hypotheses: Functions and list entries are arbitrary; sign, support and permutation hypotheses are explicit in theorems that need them.
   Library use: Stdlib.List.map, fold_right, filter, map_ext_in, Sorting.Permutation, Reals and Lra.
   Limitations: This is a finite list fold rather than an axiomatized continuous integral or probability measure.
   Proof documentation: Every public and helper declaration below has its
   own statement, hypothesis, proof-approach, and scope commentary.
   Reproduction: rocq compile FiniteSum.v (after imported local modules);
   see rocq/README.md and rocq/LIBRARY_AUDIT.md for dependency order,
   checked-claim mapping, and library audit. All results are Rocq-kernel
   checked; no unchecked evidence is created by comments.
 *)
(* Shared finite real-valued integration over enumerated outcomes.
   This deliberately uses Stdlib.List.map/fold_right; it does not define
   another recursion, assume a measure axiom, or enforce normalization. *)
From Stdlib Require Import Reals Lra Psatz List Sorting.Permutation.
Import ListNotations.
Open Scope R_scope.

(**
   [finite_sum] (definition) — Shared real-valued list sums and their algebraic/order
   laws.
   Mathematical meaning: For each occurrence x in xs, evaluate the real integrand
   f x, then add those terms, with zero for an empty list. A repeated
   element contributes repeatedly; there is no deduplication, set
   construction or implicit statistical normalization.
   Exact declaration: Definition finite_sum {A : Type} (f : A -> R) (xs : list A) : R
   := fold_right Rplus 0 (map f xs).
   Premises and side conditions: The element type A is arbitrary, and f can
   return negative or positive reals. xs is a finite list, so no
   convergence, measure, probability-mass or positivity premise is
   needed. The order is computational; later Permutation lemmas
   establish order invariance of the resulting real sum.
   Proof/definition method: Definitionally maps f over xs using
   Stdlib.List.map and folds the resulting reals with Rplus and the
   neutral element 0 using Stdlib.List.fold_right. Subsequent
   algebraic laws are proved separately rather than assumed.
   Library reuse: Stdlib.List map, filter, fold_right, map_ext_in,
   Sorting.Permutation and Reals.
   Boundary: An arbitrary finite list and real integrand; this is not a continuous
   integral or axiomatic probability measure.
 *)
Definition finite_sum {A : Type} (f : A -> R) (xs : list A) : R :=
  fold_right Rplus 0 (map f xs).

(* Stdlib.List.map_ext_in only needs equality on the enumerated
   support; this is stronger than requiring a global function equality. *)
(**
   [finite_sum_ext_in] (lemma) — Shared real-valued list sums and their
   algebraic/order laws.
   Mathematical meaning: Derives a sum or expectation identity for the explicitly
   enumerated terms.
   Exact checked proposition: Lemma finite_sum_ext_in {A : Type} : forall (xs : list
   A) (f g : A -> R), (forall x, In x xs -> f x = g x) -> finite_sum f xs =
   finite_sum g xs.
   Premises and side conditions: The displayed hypotheses include sample or list
   membership. No further assumptions are implicit.
   Proof/definition method: Kernel proof uses reuse of previously established lemmas;
   references include finite_sum., map_ext_in.
   Library reuse: Stdlib.List map, filter, fold_right, map_ext_in,
   Sorting.Permutation and Reals.
   Boundary: An arbitrary finite list and real integrand; this is not a continuous
   integral or axiomatic probability measure.
 *)
Lemma finite_sum_ext_in {A : Type} :
  forall (xs : list A) (f g : A -> R),
    (forall x, In x xs -> f x = g x) ->
    finite_sum f xs = finite_sum g xs.
Proof.
  intros xs f g Heq.
  unfold finite_sum.
  f_equal.
  apply map_ext_in; exact Heq.
Qed.

(**
   [finite_sum_ext] (lemma) — Shared real-valued list sums and their algebraic/order
   laws.
   Mathematical meaning: Derives a sum or expectation identity for the explicitly
   enumerated terms.
   Exact checked proposition: Lemma finite_sum_ext {A : Type} : forall (xs : list A)
   (f g : A -> R), (forall x, f x = g x) -> finite_sum f xs = finite_sum g xs.
   Premises and side conditions: All required premises are written in the signature.
   No independence or distributional assumption is silently supplied.
   Proof/definition method: Kernel proof uses reuse of previously established lemmas;
   references include finite_sum_ext_in..
   Library reuse: Stdlib.List map, filter, fold_right, map_ext_in,
   Sorting.Permutation and Reals.
   Boundary: An arbitrary finite list and real integrand; this is not a continuous
   integral or axiomatic probability measure.
 *)
Lemma finite_sum_ext {A : Type} :
  forall (xs : list A) (f g : A -> R),
    (forall x, f x = g x) ->
    finite_sum f xs = finite_sum g xs.
Proof.
  intros xs f g Heq.
  apply finite_sum_ext_in.
  intros x _; apply Heq.
Qed.

(**
   [finite_sum_add] (lemma) — Shared real-valued list sums and their algebraic/order
   laws.
   Mathematical meaning: Derives a sum or expectation identity for the explicitly
   enumerated terms.
   Exact checked proposition: Lemma finite_sum_add {A : Type} : forall (xs : list A)
   (f g : A -> R), finite_sum (fun x => f x + g x) xs = finite_sum f xs + finite_sum
   g xs.
   Premises and side conditions: All required premises are written in the signature.
   No independence or distributional assumption is silently supplied.
   Proof/definition method: Kernel proof uses structural induction, rewriting of
   equalities, ring/field normalization, definitional reduction; references include
   finite_sum.
   Library reuse: Stdlib.List map, filter, fold_right, map_ext_in,
   Sorting.Permutation and Reals.
   Boundary: An arbitrary finite list and real integrand; this is not a continuous
   integral or axiomatic probability measure.
 *)
Lemma finite_sum_add {A : Type} :
  forall (xs : list A) (f g : A -> R),
    finite_sum (fun x => f x + g x) xs =
      finite_sum f xs + finite_sum g xs.
Proof.
  induction xs as [|x xs IH]; intros f g;
    unfold finite_sum in *; simpl.
  - ring.
  - rewrite IH; ring.
Qed.

(**
   [finite_sum_scale] (lemma) — Shared real-valued list sums and their
   algebraic/order laws.
   Mathematical meaning: Derives a sum or expectation identity for the explicitly
   enumerated terms.
   Exact checked proposition: Lemma finite_sum_scale {A : Type} : forall (xs : list
   A) (a : R) (f : A -> R), finite_sum (fun x => a * f x) xs = a * finite_sum f xs.
   Premises and side conditions: All required premises are written in the signature.
   No independence or distributional assumption is silently supplied.
   Proof/definition method: Kernel proof uses structural induction, rewriting of
   equalities, ring/field normalization, definitional reduction; references include
   finite_sum.
   Library reuse: Stdlib.List map, filter, fold_right, map_ext_in,
   Sorting.Permutation and Reals.
   Boundary: An arbitrary finite list and real integrand; this is not a continuous
   integral or axiomatic probability measure.
 *)
Lemma finite_sum_scale {A : Type} :
  forall (xs : list A) (a : R) (f : A -> R),
    finite_sum (fun x => a * f x) xs =
      a * finite_sum f xs.
Proof.
  induction xs as [|x xs IH]; intros a f;
    unfold finite_sum in *; simpl.
  - ring.
  - rewrite IH; ring.
Qed.

(**
   [finite_sum_nonnegative] (lemma) — Shared real-valued list sums and their
   algebraic/order laws.
   Mathematical meaning: Derives a sum or expectation identity for the explicitly
   enumerated terms.
   Exact checked proposition: Lemma finite_sum_nonnegative {A : Type} : forall (xs :
   list A) (f : A -> R), (forall x, In x xs -> 0 <= f x) -> 0 <= finite_sum f xs.
   Premises and side conditions: The displayed hypotheses include explicit nonzero or
   strict-positive numerical conditions; sample or list membership. No further
   assumptions are implicit.
   Proof/definition method: Kernel proof uses structural induction, reuse of
   previously established lemmas, linear real arithmetic (Lra), definitional
   reduction; references include finite_sum.
   Library reuse: Stdlib.List map, filter, fold_right, map_ext_in,
   Sorting.Permutation and Reals.
   Boundary: An arbitrary finite list and real integrand; this is not a continuous
   integral or axiomatic probability measure.
 *)
Lemma finite_sum_nonnegative {A : Type} :
  forall (xs : list A) (f : A -> R),
    (forall x, In x xs -> 0 <= f x) ->
    0 <= finite_sum f xs.
Proof.
  induction xs as [|x xs IH]; intros f Hf;
    unfold finite_sum in *; simpl.
  - lra.
  - assert (Hx : 0 <= f x) by (apply Hf; simpl; auto).
    assert (Htail : forall y, In y xs -> 0 <= f y).
    { intros y Hy; apply Hf; simpl; auto. }
    specialize (IH f Htail); lra.
Qed.

(* A nonnegative contribution is no larger than the whole sum.
   Unlike the report-specific union proof, the induction is generic. *)
(**
   [finite_sum_neg] (lemma) — Shared real-valued list sums and their algebraic/order
   laws.
   Mathematical meaning: Derives a sum or expectation identity for the explicitly
   enumerated terms.
   Exact checked proposition: Lemma finite_sum_neg {A : Type} : forall (xs : list A)
   (f : A -> R), finite_sum (fun x => - f x) xs = - finite_sum f xs.
   Premises and side conditions: All required premises are written in the signature.
   No independence or distributional assumption is silently supplied.
   Proof/definition method: Kernel proof uses rewriting of equalities, reuse of
   previously established lemmas, ring/field normalization; references include
   finite_sum_ext, finite_sum_scale.
   Library reuse: Stdlib.List map, filter, fold_right, map_ext_in,
   Sorting.Permutation and Reals.
   Boundary: An arbitrary finite list and real integrand; this is not a continuous
   integral or axiomatic probability measure.
 *)
Lemma finite_sum_neg {A : Type} :
  forall (xs : list A) (f : A -> R),
    finite_sum (fun x => - f x) xs = - finite_sum f xs.
Proof.
  intros xs f.
  transitivity (finite_sum (fun x => (-1) * f x) xs).
  - apply finite_sum_ext; intro x; ring.
  - rewrite finite_sum_scale; ring.
Qed.

(**
   [finite_sum_sub] (lemma) — Shared real-valued list sums and their algebraic/order
   laws.
   Mathematical meaning: Derives a sum or expectation identity for the explicitly
   enumerated terms.
   Exact checked proposition: Lemma finite_sum_sub {A : Type} : forall (xs : list A)
   (f g : A -> R), finite_sum (fun x => f x - g x) xs = finite_sum f xs - finite_sum
   g xs.
   Premises and side conditions: All required premises are written in the signature.
   No independence or distributional assumption is silently supplied.
   Proof/definition method: Kernel proof uses rewriting of equalities, reuse of
   previously established lemmas, ring/field normalization; references include
   finite_sum_ext, finite_sum_add.
   Library reuse: Stdlib.List map, filter, fold_right, map_ext_in,
   Sorting.Permutation and Reals.
   Boundary: An arbitrary finite list and real integrand; this is not a continuous
   integral or axiomatic probability measure.
 *)
Lemma finite_sum_sub {A : Type} :
  forall (xs : list A) (f g : A -> R),
    finite_sum (fun x => f x - g x) xs =
      finite_sum f xs - finite_sum g xs.
Proof.
  intros xs f g.
  transitivity (finite_sum (fun x => f x + - g x) xs).
  - apply finite_sum_ext; intro x; ring.
  - rewrite finite_sum_add, finite_sum_neg; ring.
Qed.

(**
   [finite_sum_member_le] (lemma) — Shared real-valued list sums and their
   algebraic/order laws.
   Mathematical meaning: Derives a sum or expectation identity for the explicitly
   enumerated terms.
   Exact checked proposition: Lemma finite_sum_member_le {A : Type} : forall (xs :
   list A) (f : A -> R) (x : A), (forall y, In y xs -> 0 <= f y) -> In x xs -> f x <=
   finite_sum f xs.
   Premises and side conditions: The displayed hypotheses include explicit nonzero or
   strict-positive numerical conditions; sample or list membership. No further
   assumptions are implicit.
   Proof/definition method: Kernel proof uses structural induction, case analysis,
   reuse of previously established lemmas, linear real arithmetic (Lra), definitional
   reduction; references include Hnonnegative, finite_sum_nonnegative, Htail..
   Library reuse: Stdlib.List map, filter, fold_right, map_ext_in,
   Sorting.Permutation and Reals.
   Boundary: An arbitrary finite list and real integrand; this is not a continuous
   integral or axiomatic probability measure.
 *)
Lemma finite_sum_member_le {A : Type} :
  forall (xs : list A) (f : A -> R) (x : A),
    (forall y, In y xs -> 0 <= f y) ->
    In x xs ->
    f x <= finite_sum f xs.
Proof.
  intros xs f x.
  induction xs as [|a xs IH]; intros Hnonnegative Hin.
  - contradiction.
  - assert (Ha : 0 <= f a).
    { apply Hnonnegative; simpl; auto. }
    assert (Htail : forall y, In y xs -> 0 <= f y).
    { intros y Hy; apply Hnonnegative; simpl; auto. }
    simpl in Hin.
    destruct Hin as [Heq | Hin].
    + subst a.
      assert (Hrest : 0 <= finite_sum f xs).
      { apply finite_sum_nonnegative; exact Htail. }
      change (f x <= f x + finite_sum f xs).
      lra.
    + specialize (IH Htail Hin).
      change (f x <= f a + finite_sum f xs).
      lra.
Qed.

(* Zero aggregate mass plus nonnegative contributions forces each
   supported contribution to vanish. Reuse the member bound. *)
(**
   [finite_sum_nonnegative_zero] (lemma) — Shared real-valued list sums and their
   algebraic/order laws.
   Mathematical meaning: Derives a sum or expectation identity for the explicitly
   enumerated terms.
   Exact checked proposition: Lemma finite_sum_nonnegative_zero {A : Type} : forall
   (xs : list A) (f : A -> R), (forall x, In x xs -> 0 <= f x) -> finite_sum f xs = 0
   -> forall x, In x xs -> f x = 0.
   Premises and side conditions: The displayed hypotheses include explicit nonzero or
   strict-positive numerical conditions; sample or list membership. No further
   assumptions are implicit.
   Proof/definition method: Kernel proof uses reuse of previously established lemmas,
   linear real arithmetic (Lra); references include Hnonnegative,
   finite_sum_member_le.
   Library reuse: Stdlib.List map, filter, fold_right, map_ext_in,
   Sorting.Permutation and Reals.
   Boundary: An arbitrary finite list and real integrand; this is not a continuous
   integral or axiomatic probability measure.
 *)
Lemma finite_sum_nonnegative_zero {A : Type} :
  forall (xs : list A) (f : A -> R),
    (forall x, In x xs -> 0 <= f x) ->
    finite_sum f xs = 0 ->
    forall x, In x xs -> f x = 0.
Proof.
  intros xs f Hnonnegative Hsum x Hin.
  pose proof (Hnonnegative x Hin) as Hlow.
  pose proof (finite_sum_member_le xs f x Hnonnegative Hin) as Hhigh.
  lra.
Qed.

(* A constant list sum is its length times the constant.
   This general list-fold identity replaces report-specific recursions. *)
(* Map composition and signed sums reuse Stdlib.List and existing
   finite-sum linearity instead of introducing new recursions. *)
(**
   [finite_sum_monotone] (lemma) — Shared real-valued list sums and their
   algebraic/order laws.
   Mathematical meaning: Derives a sum or expectation identity for the explicitly
   enumerated terms.
   Exact checked proposition: Lemma finite_sum_monotone {A : Type} : forall (xs :
   list A) (f g : A -> R), (forall x, In x xs -> f x <= g x) -> finite_sum f xs <=
   finite_sum g xs.
   Premises and side conditions: The displayed hypotheses include sample or list
   membership. No further assumptions are implicit.
   Proof/definition method: Establish nonnegativity of the pointwise difference
   using finite_sum_nonnegative; rewrite with finite_sum_sub and finish by Lra.
   Library reuse: Stdlib.List map, filter, fold_right, map_ext_in,
   Sorting.Permutation and Reals.
   Boundary: An arbitrary finite list and real integrand; this is not a continuous
   integral or axiomatic probability measure.
 *)
Lemma finite_sum_monotone {A : Type} :
  forall (xs : list A) (f g : A -> R),
    (forall x, In x xs -> f x <= g x) ->
    finite_sum f xs <= finite_sum g xs.
Proof.
  intros xs f g Hle.
  assert (Hnonnegative : 0 <= finite_sum (fun x => g x - f x) xs).
  { apply finite_sum_nonnegative.
    intros x Hin.
    specialize (Hle x Hin); lra. }
  rewrite finite_sum_sub in Hnonnegative.
  lra.
Qed.

(**
   [finite_sum_const] (lemma) — Shared real-valued list sums and their
   algebraic/order laws.
   Mathematical meaning: Derives a sum or expectation identity for the explicitly
   enumerated terms.
   Exact checked proposition: Lemma finite_sum_const {A : Type} : forall (xs : list
   A) (c : R), finite_sum (fun _ => c) xs = INR (length xs) * c.
   Premises and side conditions: All required premises are written in the signature.
   No independence or distributional assumption is silently supplied.
   Proof/definition method: Kernel proof uses structural induction, rewriting of
   equalities, ring/field normalization, definitional reduction; references include
   finite_sum.
   Library reuse: Stdlib.List map, filter, fold_right, map_ext_in,
   Sorting.Permutation and Reals.
   Boundary: An arbitrary finite list and real integrand; this is not a continuous
   integral or axiomatic probability measure.
 *)
Lemma finite_sum_const {A : Type} :
  forall (xs : list A) (c : R),
    finite_sum (fun _ => c) xs = INR (length xs) * c.
Proof.
  induction xs as [|x xs IH]; intro c.
  - unfold finite_sum; simpl; ring.
  - change (c + finite_sum (fun _ => c) xs = INR (S (length xs)) * c).
    rewrite IH, S_INR; ring.
Qed.

(**
   [finite_sum_zero] (lemma) — Shared real-valued list sums and their algebraic/order
   laws.
   Mathematical meaning: Derives a sum or expectation identity for the explicitly
   enumerated terms.
   Exact checked proposition: Lemma finite_sum_zero {A : Type} : forall (xs : list
   A), finite_sum (fun _ => 0) xs = 0.
   Premises and side conditions: All required premises are written in the signature.
   No independence or distributional assumption is silently supplied.
   Proof/definition method: Instantiate the shared finite_sum_const identity
   at zero; finish by Rocq's standard ring normalization, no list induction.
   Library reuse: Stdlib.List map, filter, fold_right, map_ext_in,
   Sorting.Permutation and Reals.
   Boundary: An arbitrary finite list and real integrand; this is not a continuous
   integral or axiomatic probability measure.
 *)
Lemma finite_sum_zero {A : Type} :
  forall (xs : list A),
    finite_sum (fun _ => 0) xs = 0.
Proof.
  intro xs.
  rewrite finite_sum_const.
  ring.
Qed.

(**
   [finite_sum_map] (lemma) — Shared real-valued list sums and their algebraic/order
   laws.
   Mathematical meaning: Derives a sum or expectation identity for the explicitly
   enumerated terms.
   Exact checked proposition: Lemma finite_sum_map {A B : Type} : forall (xs : list
   A) (g : A -> B) (f : B -> R), finite_sum f (map g xs) = finite_sum (fun x => f (g
   x)) xs.
   Premises and side conditions: All required premises are written in the signature.
   No independence or distributional assumption is silently supplied.
   Proof/definition method: Kernel proof uses rewriting of equalities, definitional
   reduction; references include finite_sum., map_map..
   Library reuse: Stdlib.List map, filter, fold_right, map_ext_in,
   Sorting.Permutation and Reals.
   Boundary: An arbitrary finite list and real integrand; this is not a continuous
   integral or axiomatic probability measure.
 *)
Lemma finite_sum_map {A B : Type} :
  forall (xs : list A) (g : A -> B) (f : B -> R),
    finite_sum f (map g xs) =
      finite_sum (fun x => f (g x)) xs.
Proof.
  intros xs g f.
  unfold finite_sum.
  rewrite map_map.
  reflexivity.
Qed.
 
(* The standard pairwise zip truncates only when input lengths differ.
   Here both lists are maps of the very same source list, so they have
   identical lengths and represent a per-element pair map. The single
   generic list-shape induction below replaces domain-specific matrix
   zip inductions, while the actual sum still uses Stdlib.List.map. *)
(**
   [finite_sum_zip_map] (lemma) — Shared real-valued list sums and their
   algebraic/order laws.
   Mathematical meaning: Combining two maps of one list is pointwise
   pairing, so a finite real sum over their zip is a mapped finite sum.
   Exact checked proposition: forall xs f g h, finite_sum h
   (combine (map f xs) (map g xs)) =
   finite_sum (fun x => h (f x, g x)) xs.
   Premises and side conditions: The two mapped lists share their source,
   hence have equal length; there is no probability or positivity premise.
   Proof/definition method: A single structural list induction identifies
   Stdlib.List.combine with pointwise pairing, followed by finite_sum_map.
   Library reuse: Stdlib.List.combine, Stdlib.List.map,
   FiniteSum.finite_sum_map, and definitional equality.
   Boundary: Only applies to equally aligned pairwise list maps;
   arbitrary differently sized zip inputs are excluded.
 *)
Lemma finite_sum_zip_map {A B C : Type} :
  forall (xs : list A) (f : A -> B) (g : A -> C) (h : B * C -> R),
    finite_sum h (combine (map f xs) (map g xs)) =
      finite_sum (fun x => h (f x, g x)) xs.
Proof.
  intros xs f g h.
  assert (Hcombine :
    combine (map f xs) (map g xs) =
      map (fun x => (f x, g x)) xs).
  { induction xs as [|x xs IH]; simpl.
    - reflexivity.
    - now rewrite IH. }
  rewrite Hcombine, finite_sum_map.
  reflexivity.
Qed.


(* Finite Fubini/interchange law for an explicit product of two
   lists, proved once using the existing sum-additivity laws.
   This introduces no new iterator, measure, or summation recursion. *)
(**
   [finite_sum_swap] (lemma) — Shared real-valued list sums and their algebraic/order
   laws.
   Mathematical meaning: Derives a sum or expectation identity for the explicitly
   enumerated terms.
   Exact checked proposition: Lemma finite_sum_swap {A B : Type} : forall (xs : list
   A) (ys : list B) (f : A -> B -> R), finite_sum (fun x => finite_sum (f x) ys) xs =
   finite_sum (fun y => finite_sum (fun x => f x y) xs) ys.
   Premises and side conditions: All required premises are written in the signature.
   No independence or distributional assumption is silently supplied.
   Proof/definition method: Kernel proof uses structural induction, rewriting of
   equalities, reuse of previously established lemmas, definitional reduction;
   references include finite_sum_zero., finite_sum_add..
   Library reuse: Stdlib.List map, filter, fold_right, map_ext_in,
   Sorting.Permutation and Reals.
   Boundary: An arbitrary finite list and real integrand; this is not a continuous
   integral or axiomatic probability measure.
 *)
Lemma finite_sum_swap {A B : Type} :
  forall (xs : list A) (ys : list B) (f : A -> B -> R),
    finite_sum (fun x => finite_sum (f x) ys) xs =
    finite_sum (fun y => finite_sum (fun x => f x y) xs) ys.
Proof.
  intros xs ys f.
  induction ys as [|y ys IH].
  - change (finite_sum (fun _ => 0) xs = 0).
    apply finite_sum_zero.
  - change
      (finite_sum
         (fun x => f x y + finite_sum (f x) ys) xs =
       finite_sum (fun x => f x y) xs +
         finite_sum (fun z => finite_sum (fun x => f x z) xs) ys).
    rewrite finite_sum_add.
    rewrite IH.
    reflexivity.
Qed.

(* Event restriction is Stdlib.List.filter, not a second event-specific
   summation.  This is a generic list-fold identity with no assumptions on
   the predicate or the (possibly signed) real-valued integrand. *)
(**
   [finite_sum_filter] (lemma) — Shared real-valued list sums and their
   algebraic/order laws.
   Mathematical meaning: Derives a sum or expectation identity for the explicitly
   enumerated terms.
   Exact checked proposition: Lemma finite_sum_filter {A : Type} : forall (xs : list
   A) (p : A -> bool) (f : A -> R), finite_sum f (filter p xs) = finite_sum (fun x =>
   if p x then f x else 0) xs.
   Premises and side conditions: All required premises are written in the signature.
   No independence or distributional assumption is silently supplied.
   Proof/definition method: Kernel proof uses structural induction, case analysis,
   rewriting of equalities, ring/field normalization, definitional reduction;
   references include finite_sum.
   Library reuse: Stdlib.List map, filter, fold_right, map_ext_in,
   Sorting.Permutation and Reals.
   Boundary: An arbitrary finite list and real integrand; this is not a continuous
   integral or axiomatic probability measure.
 *)
Lemma finite_sum_filter {A : Type} :
  forall (xs : list A) (p : A -> bool) (f : A -> R),
    finite_sum f (filter p xs) =
      finite_sum (fun x => if p x then f x else 0) xs.
Proof.
  intros xs p f.
  induction xs as [|x xs IH]; unfold finite_sum in *; simpl.
  - reflexivity.
  - destruct (p x); simpl; rewrite IH; ring.
Qed.

(* Boolean selection and its complement partition each index occurrence
   exactly once.  Reuse the existing generic filtered-sum and additive
   sum laws rather than inducting over the sample in each application. *)
(**
   [finite_sum_filter_partition] (lemma) — Shared finite real-valued sums
   and their behavior under Boolean partitions.
   Mathematical meaning: Filtering a finite list into accepted and
   rejected occurrences, then adding their weighted sums, recovers
   the original weighted sum exactly, including duplicate elements.
   Exact checked proposition: forall xs p f,
   finite_sum f (filter p xs) +
   finite_sum f (filter (fun x => negb (p x)) xs) =
   finite_sum f xs.
   Premises and side conditions: The finite list may repeat elements,
   the predicate is Boolean and the integrand takes arbitrary real
   values, including negatives. No sign or mass assumptions are needed.
   Proof/definition method: Rewrite both filtered sums with the
   previously checked finite_sum_filter, combine with finite_sum_add,
   and use finite_sum_ext with exhaustive Boolean reduction and ring.
   Library reuse: Stdlib.List.filter, Stdlib.Bool.negb,
   finite_sum_filter, finite_sum_add, finite_sum_ext, and Stdlib.Reals.
   Boundary: This establishes finite list-fold additivity, not
   countably additive or continuous probability-measure properties.
 *)
Lemma finite_sum_filter_partition {A : Type} :
  forall (xs : list A) (p : A -> bool) (f : A -> R),
    finite_sum f (filter p xs) +
    finite_sum f (filter (fun x => negb (p x)) xs) =
    finite_sum f xs.
Proof.
  intros xs p f.
  rewrite !finite_sum_filter.
  rewrite <- finite_sum_add.
  apply finite_sum_ext; intro x.
  destruct (p x); simpl; ring.
Qed.

(**
   [finite_sum_app] (lemma) — Shared real-valued list sums and their algebraic/order
   laws.
   Mathematical meaning: Derives a sum or expectation identity for the explicitly
   enumerated terms.
   Exact checked proposition: Lemma finite_sum_app {A : Type} : forall (f : A -> R)
   (xs ys : list A), finite_sum f (xs ++ ys) = finite_sum f xs + finite_sum f ys.
   Premises and side conditions: All required premises are written in the signature.
   No independence or distributional assumption is silently supplied.
   Proof/definition method: Kernel proof uses structural induction, rewriting of
   equalities, ring/field normalization, definitional reduction; references include
   finite_sum.
   Library reuse: Stdlib.List map, filter, fold_right, map_ext_in,
   Sorting.Permutation and Reals.
   Boundary: An arbitrary finite list and real integrand; this is not a continuous
   integral or axiomatic probability measure.
 *)
Lemma finite_sum_app {A : Type} :
  forall (f : A -> R) (xs ys : list A),
    finite_sum f (xs ++ ys) = finite_sum f xs + finite_sum f ys.
Proof.
  intros f xs; induction xs as [|x xs IH]; intro ys;
    unfold finite_sum in *; simpl.
  - ring.
  - rewrite IH; ring.
Qed.

(**
   [finite_sum_permutation] (lemma) — Shared real-valued list sums and their
   algebraic/order laws.
   Mathematical meaning: Derives a sum or expectation identity for the explicitly
   enumerated terms.
   Exact checked proposition: Lemma finite_sum_permutation {A : Type} : forall (xs ys
   : list A) (f : A -> R), Permutation xs ys -> finite_sum f xs = finite_sum f ys.
   Premises and side conditions: The displayed hypotheses include Stdlib permutation
   relation. No further assumptions are implicit.
   Proof/definition method: Kernel proof uses structural induction, rewriting of
   equalities, ring/field normalization, definitional reduction; references include
   finite_sum.
   Library reuse: Stdlib.List map, filter, fold_right, map_ext_in,
   Sorting.Permutation and Reals.
   Boundary: An arbitrary finite list and real integrand; this is not a continuous
   integral or axiomatic probability measure.
 *)
Lemma finite_sum_permutation {A : Type} :
  forall (xs ys : list A) (f : A -> R),
    Permutation xs ys ->
    finite_sum f xs = finite_sum f ys.
Proof.
  intros xs ys f Hperm.
  induction Hperm as
    [| x xs ys Hperm IH | x y xs | xs ys zs Hfirst IHfirst Hsecond IHsecond].
  - reflexivity.
  - change (f x + finite_sum f xs = f x + finite_sum f ys).
    rewrite IH; reflexivity.
  - unfold finite_sum; simpl; ring.
  - transitivity (finite_sum f ys); assumption.
Qed.

(* Reversal is a standard-library permutation, hence sum preserving. *)
(**
   [finite_sum_rev] (lemma) — Shared real-valued list sums and their algebraic/order
   laws.
   Mathematical meaning: Derives a sum or expectation identity for the explicitly
   enumerated terms.
   Exact checked proposition: Lemma finite_sum_rev {A : Type} : forall (xs : list A)
   (f : A -> R), finite_sum f (rev xs) = finite_sum f xs.
   Premises and side conditions: All required premises are written in the signature.
   No independence or distributional assumption is silently supplied.
   Proof/definition method: Kernel proof uses reuse of previously established lemmas;
   references include finite_sum_permutation., Permutation_sym.
   Library reuse: Stdlib.List map, filter, fold_right, map_ext_in,
   Sorting.Permutation and Reals.
   Boundary: An arbitrary finite list and real integrand; this is not a continuous
   integral or axiomatic probability measure.
 *)
Lemma finite_sum_rev {A : Type} :
  forall (xs : list A) (f : A -> R),
    finite_sum f (rev xs) = finite_sum f xs.
Proof.
  intros xs f.
  apply finite_sum_permutation.
  apply Permutation_sym, Permutation_rev.
Qed.

(**
   [finite_sum_nonnegative_zero_iff] (lemma) — Exact zero criterion for a
   nonnegative finite real sum.
   Mathematical meaning: A finite sum of nonnegative terms is zero exactly
   when every term at an enumerated sample position is zero.
   Exact checked proposition: Given nonnegative f on xs, finite_sum f xs = 0
   if and only if each x in xs satisfies f x = 0.
   Premises and side conditions: Nonnegativity is required only on the
   enumerated list, which may be empty or contain repeated elements; signed
   cancellation would invalidate the forward implication.
   Proof/definition method: Reuse the established zero-sum implication
   in one direction and support-restricted sum extensionality in the other.
   Library reuse: finite_sum_nonnegative_zero, finite_sum_ext_in,
   finite_sum_zero and Stdlib.List.In; no additional fold or induction.
   Boundary: This is a real-valued finite list identity, not a statement
   about continuous integration or strictly positive sampling weights.
 *)
Lemma finite_sum_nonnegative_zero_iff {A : Type} :
  forall (xs : list A) (f : A -> R),
    (forall x, In x xs -> 0 <= f x) ->
    (finite_sum f xs = 0 <->
       forall x, In x xs -> f x = 0).
Proof.
  intros xs f Hnonnegative.
  split.
  - apply finite_sum_nonnegative_zero; exact Hnonnegative.
  - intro Hzero.
    rewrite (finite_sum_ext_in xs f (fun _ => 0) Hzero).
    apply finite_sum_zero.
Qed.

(**
   [finite_sum_positive_of_positive_member] (lemma) — Strictly positive
   aggregate mass from one positive contribution.
   Mathematical meaning: A single strictly positive term prevents a
   finite sum of otherwise nonnegative terms from vanishing.
   Exact checked proposition: For x in xs, nonnegative f on xs and
   0 < f x imply 0 < finite_sum f xs.
   Premises and side conditions: The witness x must occur in the list;
   all other listed terms must be nonnegative, and duplicates are counted.
   Proof/definition method: Reuse the earlier
   finite_sum_member_le theorem, which directly bounds the weight
   of any enumerated member by the total nonnegative sum.
   Finish by linear real arithmetic. This removes the previous
   unnecessary real-order case split and zero-mass contradiction.
   Library reuse: finite_sum_member_le and Stdlib.Lra;
   no list recursion, extra decision procedure or new axiom.
   Boundary: No conclusion follows for signed sums where cancellation
   can occur, and the lemma says nothing about infinite sample spaces.
 *)
Lemma finite_sum_positive_of_positive_member {A : Type} :
  forall (xs : list A) (f : A -> R) (x : A),
    (forall y, In y xs -> 0 <= f y) ->
    In x xs ->
    0 < f x ->
    0 < finite_sum f xs.
Proof.
  intros xs f x Hnonnegative Hin Hpositive.
  pose proof (finite_sum_member_le xs f x Hnonnegative Hin).
  lra.
Qed.

(**
   [finite_sum_strict_monotone_at_member] (lemma) — Strict comparison
   of two finite sums from one strict pointwise comparison.
   Mathematical meaning: Pointwise domination of one score by another
   is strict at the sum level if at least one enumerated contribution
   is strictly dominated.
   Exact checked proposition: If f y <= g y for every y in xs, and
   x occurs in xs with f x < g x, then finite_sum f xs < finite_sum g xs.
   Premises and side conditions: The pointwise comparison is required
   at all list entries; no signs are required separately for f or g.
   Multiplicities in xs are preserved in both sums.
   Proof/definition method: Apply the preceding strictly-positive
   contribution lemma to the nonnegative difference g-f, then
   rewrite the difference sum using existing finite-sum linearity.
   Library reuse: finite_sum_positive_of_positive_member,
   finite_sum_sub, Stdlib.Reals and Stdlib.Lra, without a duplicate
   induction or a project-specific summation primitive.
   Boundary: This is a finite additive strict-order comparison;
   it does not prove monotonicity of a general nonlinear statistic.
 *)
Lemma finite_sum_strict_monotone_at_member {A : Type} :
  forall (xs : list A) (f g : A -> R) (x : A),
    (forall y, In y xs -> f y <= g y) ->
    In x xs ->
    f x < g x ->
    finite_sum f xs < finite_sum g xs.
Proof.
  intros xs f g x Hle Hin Hlt.
  assert (Hnonnegative :
      forall y, In y xs -> 0 <= g y - f y).
  { intros y Hy.
    specialize (Hle y Hy).
    lra. }
  pose proof (finite_sum_positive_of_positive_member xs
    (fun y => g y - f y) x Hnonnegative Hin) as Hdiff.
  assert (Hpositive : 0 < g x - f x) by lra.
  specialize (Hdiff Hpositive).
  rewrite finite_sum_sub in Hdiff.
  lra.
Qed.

(**
   [finite_sum_positive_iff_positive_member] (lemma) —
   Constructive positive-support characterization of a finite real sum.
   Mathematical meaning: A finite sum of nonnegative listed terms is
   strictly positive if and only if some enumerated term is strictly
   positive. The witness is an actual list member, not merely an
   abstract value of the summand function.
   Exact checked proposition: If f x >= 0 for each In x xs,
   then 0 < finite_sum f xs iff there exists x with In x xs
   and 0 < f x.
   Premises and side conditions: The list may be empty and may
   contain repeated elements. Nonnegativity is required only
   on enumerated entries; signed terms would admit cancellation.
   No decidable equality or total ordering on the element type
   A is required.
   Proof/definition method: The backwards implication delegates
   entirely to finite_sum_positive_of_positive_member. For the
   forwards implication, induct on the standard list, using the
   standard real-order decision Rlt_dec to select a positive head
   or show that its nonnegative value must be zero, after which
   the existing Stdlib.List.map/fold_right sum reduces to the tail.
   Library reuse: finite_sum_positive_of_positive_member,
   Stdlib.List.map/fold_right, Stdlib.Reals.Rlt_dec and Stdlib.Lra.
   Boundary: This is a finite list-support theorem, not
   countable additivity or a general measure-theoretic positivity law.
 *)
Lemma finite_sum_positive_iff_positive_member {A : Type} :
  forall (xs : list A) (f : A -> R),
    (forall x, In x xs -> 0 <= f x) ->
    (0 < finite_sum f xs <->
      exists x, In x xs /\ 0 < f x).
Proof.
  intros xs f.
  induction xs as [|a rest IH]; intros Hnonnegative.
  - split.
    + intro Hpositive.
      change (0 < 0) in Hpositive.
      lra.
    + intros [x [Hin _]].
      inversion Hin.
  - split.
    + intros Hpositive.
      destruct (Rlt_dec 0 (f a)) as [Ha | Hnot].
      * exists a; split.
        -- left; reflexivity.
        -- exact Ha.
      * assert (Hhead_nonnegative : 0 <= f a).
        { apply Hnonnegative; left; reflexivity. }
        assert (Hhead_zero : f a = 0) by lra.
        assert (Htail_positive : 0 < finite_sum f rest).
        { change (0 < f a + finite_sum f rest) in Hpositive.
          lra. }
        assert (Htail_nonnegative :
          forall y, In y rest -> 0 <= f y).
        { intros y Hy; apply Hnonnegative; right; exact Hy. }
        destruct ((proj1 (IH Htail_nonnegative)) Htail_positive)
          as [y [Hy Hfy]].
        exists y; split.
        -- right; exact Hy.
        -- exact Hfy.
    + intros [x [Hin Hpositive]].
      apply (finite_sum_positive_of_positive_member
        (a :: rest) f x Hnonnegative Hin Hpositive).
Qed.

(**
   [finite_sum_monotone_equality_iff_pointwise] (lemma) —
   Characterization of equality in finite-sum monotonicity.
   Mathematical meaning: When one real-valued summand is pointwise
   no larger than another on the enumerated support, equality of
   their two finite sums is equivalent to pointwise equality at
   every enumerated item, including repeated list entries.
   Exact checked proposition: If f x <= g x whenever In x xs,
   then finite_sum f xs = finite_sum g xs iff
   forall x, In x xs -> f x = g x.
   Premises and side conditions: The input type requires no
   decidable equality; empty and repeated lists are permitted.
   The pointwise comparison is essential: without it,
   signed differences might cancel even when sums agree.
   Proof/definition method: Apply the already checked zero-sum
   characterization to the nonnegative difference g-f and rewrite
   its finite sum using the generic subtraction law; Lra
   converts zero differences to equal pointwise values.
   Library reuse: finite_sum_nonnegative_zero_iff,
   finite_sum_sub, Stdlib.List.In and Stdlib.Lra.
   Boundary: This is an exact finite-list equivalence, not
   an almost-everywhere statement on a continuous measure.
 *)
Lemma finite_sum_monotone_equality_iff_pointwise {A : Type} :
  forall (xs : list A) (f g : A -> R),
    (forall x, In x xs -> f x <= g x) ->
    (finite_sum f xs = finite_sum g xs <->
      forall x, In x xs -> f x = g x).
Proof.
  intros xs f g Hle.
  assert (Hnonnegative :
      forall x, In x xs -> 0 <= g x - f x).
  { intros x Hx.
    specialize (Hle x Hx).
    lra. }
  split.
  - intro Hequal.
    assert (Hzero : finite_sum (fun x => g x - f x) xs = 0).
    { rewrite finite_sum_sub; lra. }
    pose proof
      ((proj1 (finite_sum_nonnegative_zero_iff
        xs (fun y => g y - f y) Hnonnegative)) Hzero)
      as Hzero_at_member.
    intros x Hx.
    specialize (Hzero_at_member x Hx).
    lra.
  - intro Hpointwise.
    assert (Hzero : finite_sum (fun x => g x - f x) xs = 0).
    { apply (proj2 (finite_sum_nonnegative_zero_iff
        xs (fun x => g x - f x) Hnonnegative)).
      intros x Hx.
      specialize (Hpointwise x Hx).
      lra. }
    rewrite finite_sum_sub in Hzero.
    lra.
Qed.

(**
   [finite_sum_strict_monotone_iff_strict_member] (lemma) —
   Constructive witness characterization of strict finite-sum order.
   Mathematical meaning: Under a pointwise non-strict comparison,
   strict inequality of total sums occurs exactly when at least
   one actual enumerated item has a strict comparison.
   Exact checked proposition: If f x <= g x on all In x xs,
   then finite_sum f xs < finite_sum g xs iff
   exists x, In x xs /\ f x < g x.
   Premises and side conditions: The list may be empty, can
   repeat items, and does not need decidable equality.
   The pointwise inequality rules out cancellation by
   negative contributions to the difference g-f.
   Proof/definition method: The forward implication converts
   the strict inequality to positivity of a nonnegative
   difference sum and invokes the previously established
   constructive positive-member iff. The reverse direction
   delegates to the checked strict-monotonicity-at-member lemma.
   Library reuse: finite_sum_positive_iff_positive_member,
   finite_sum_strict_monotone_at_member, finite_sum_sub,
   Stdlib.List.In and Stdlib.Lra.
   Boundary: Only finite enumerated sums are compared;
   no inference about continuous distributions is made.
 *)
Lemma finite_sum_strict_monotone_iff_strict_member {A : Type} :
  forall (xs : list A) (f g : A -> R),
    (forall x, In x xs -> f x <= g x) ->
    (finite_sum f xs < finite_sum g xs <->
      exists x, In x xs /\ f x < g x).
Proof.
  intros xs f g Hle.
  assert (Hnonnegative :
      forall x, In x xs -> 0 <= g x - f x).
  { intros x Hx.
    specialize (Hle x Hx).
    lra. }
  split.
  - intro Hstrict.
    assert (Hpositive : 0 < finite_sum (fun x => g x - f x) xs).
    { rewrite finite_sum_sub; lra. }
    pose proof
      ((proj1 (finite_sum_positive_iff_positive_member
        xs (fun y => g y - f y) Hnonnegative)) Hpositive)
      as Hpositive_at_member.
    destruct Hpositive_at_member as [x [Hx Hdiff]].
    exists x; split; [exact Hx | lra].
  - intros [x [Hx Hstrict]].
    exact (finite_sum_strict_monotone_at_member
      xs f g x Hle Hx Hstrict).
Qed.

(**
   [finite_sum_singleton_zero_iff] (lemma) — Zero sum on a singleton.
   Mathematical meaning: A list with one real summand has zero sum
   exactly when that summand is zero; cancellation is impossible.
   Exact checked proposition: If length xs = 1, finite_sum f xs = 0
   iff forall x, In x xs -> f x = 0.
   Premises and side conditions: Arbitrary element type, arbitrary
   real summand, no nonnegativity or normalization requirements.
   Proof/definition method: Analyze the ordinary list using its
   length-one constraint and discharge the real sum by linear
   arithmetic; avoid implementing another finite sum.
   Library reuse: Stdlib.List.In, length; Stdlib.Reals and Lra.
   Boundary: Finite one-element fold; no continuous integral claim.
 *)
Lemma finite_sum_singleton_zero_iff {A : Type} :
  forall (xs : list A) (f : A -> R),
    length xs = 1%nat ->
    (finite_sum f xs = 0 <-> forall x, In x xs -> f x = 0).
Proof.
  intros xs f Hlength.
  destruct xs as [| head [| next rest]].
  - discriminate Hlength.
  - unfold finite_sum; simpl.
    split.
    + intros Hsum x Hmember.
      destruct Hmember as [Heq | []].
      subst x.
      lra.
    + intro Hzero.
      specialize (Hzero head (or_introl eq_refl)).
      lra.
  - discriminate Hlength.
Qed.
 
(**
   [finite_sum_pair] (lemma) — Exact evaluation of a two-element
   list by the shared real finite sum.
   Mathematical meaning: An enumerated pair of samples contributes
   precisely the sum of its two real values, including duplicates.
   Exact checked proposition: finite_sum f [x; y] = f x + f y.
   Premises and side conditions: The element type and values are
   arbitrary; no sign, normalization or equality hypotheses.
   Proof/definition method: Unfold the existing list map/fold,
   simplify, and apply the maintained ring tactic.
   Library reuse: Stdlib.List.map/fold_right and Stdlib.Reals ring.
   Boundary: A finite two-occurrence computation, not a
   general continuous integral or covariance formula.
 *)
Lemma finite_sum_pair {A : Type} :
  forall (f : A -> R) x y,
    finite_sum f [x; y] = f x + f y.
Proof.
  intros f x y.
  unfold finite_sum.
  simpl.
  ring.
Qed.

(**
   [finite_sum_pair_zero_iff_opposite] (lemma) — Zero sum
   characterization for a pair of listed real scores.
   Mathematical meaning: Exactly two finite summands cancel iff
   their values are real additive inverses of one another.
   Exact checked proposition: finite_sum f [x; y] = 0 iff
   f x = - f y, whether or not x and y are distinct.
   Premises and side conditions: No nonnegative or positive
   score assumptions and no probability normalization.
   Proof/definition method: Apply finite_sum_pair then
   the standard real linear arithmetic tactic in both directions.
   Library reuse: finite_sum_pair and Stdlib.Lra.
   Boundary: This two-element cancellation criterion does
   not hold as stated for arbitrary-length signed lists.
 *)
Lemma finite_sum_pair_zero_iff_opposite {A : Type} :
  forall (f : A -> R) x y,
    (finite_sum f [x; y] = 0 <-> f x = - f y).
Proof.
  intros f x y.
  rewrite finite_sum_pair.
  split; intro H; lra.
Qed.
