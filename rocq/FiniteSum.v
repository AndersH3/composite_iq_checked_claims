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
