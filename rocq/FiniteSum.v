(* Shared finite real-valued integration over enumerated outcomes.
   This deliberately uses Stdlib.List.map/fold_right; it does not define
   another recursion, assume a measure axiom, or enforce normalization. *)
From Stdlib Require Import Reals Lra Psatz List Sorting.Permutation.
Import ListNotations.
Open Scope R_scope.

Definition finite_sum {A : Type} (f : A -> R) (xs : list A) : R :=
  fold_right Rplus 0 (map f xs).

(* Stdlib.List.map_ext_in only needs equality on the enumerated
   support; this is stronger than requiring a global function equality. *)
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

Lemma finite_sum_ext {A : Type} :
  forall (xs : list A) (f g : A -> R),
    (forall x, f x = g x) ->
    finite_sum f xs = finite_sum g xs.
Proof.
  intros xs f g Heq.
  apply finite_sum_ext_in.
  intros x _; apply Heq.
Qed.

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

Lemma finite_sum_monotone {A : Type} :
  forall (xs : list A) (f g : A -> R),
    (forall x, In x xs -> f x <= g x) ->
    finite_sum f xs <= finite_sum g xs.
Proof.
  induction xs as [|x xs IH]; intros f g Hle;
    unfold finite_sum in *; simpl.
  - lra.
  - assert (Hx : f x <= g x) by (apply Hle; simpl; auto).
    assert (Htail : forall y, In y xs -> f y <= g y).
    { intros y Hy; apply Hle; simpl; auto. }
    specialize (IH f g Htail); lra.
Qed.

Lemma finite_sum_zero {A : Type} :
  forall (xs : list A),
    finite_sum (fun _ => 0) xs = 0.
Proof.
  induction xs as [|x xs IH]; unfold finite_sum in *; simpl.
  - reflexivity.
  - rewrite IH; ring.
Qed.

(* Map composition and signed sums reuse Stdlib.List and existing
   finite-sum linearity instead of introducing new recursions. *)
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

Lemma finite_sum_neg {A : Type} :
  forall (xs : list A) (f : A -> R),
    finite_sum (fun x => - f x) xs = - finite_sum f xs.
Proof.
  intros xs f.
  transitivity (finite_sum (fun x => (-1) * f x) xs).
  - apply finite_sum_ext; intro x; ring.
  - rewrite finite_sum_scale; ring.
Qed.

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

(* Finite Fubini/interchange law for an explicit product of two
   lists, proved once using the existing sum-additivity laws.
   This introduces no new iterator, measure, or summation recursion. *)
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

Lemma finite_sum_app {A : Type} :
  forall (f : A -> R) (xs ys : list A),
    finite_sum f (xs ++ ys) = finite_sum f xs + finite_sum f ys.
Proof.
  intros f xs; induction xs as [|x xs IH]; intro ys;
    unfold finite_sum in *; simpl.
  - ring.
  - rewrite IH; ring.
Qed.

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
Lemma finite_sum_rev {A : Type} :
  forall (xs : list A) (f : A -> R),
    finite_sum f (rev xs) = finite_sum f xs.
Proof.
  intros xs f.
  apply finite_sum_permutation.
  apply Permutation_sym, Permutation_rev.
Qed.
