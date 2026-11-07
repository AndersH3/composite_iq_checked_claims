(* Shared finite real-valued integration over enumerated outcomes.
   This deliberately uses Stdlib.List.map/fold_right; it does not define
   another recursion, assume a measure axiom, or enforce normalization. *)
From Stdlib Require Import Reals Lra Psatz List Sorting.Permutation.
Import ListNotations.
Open Scope R_scope.

Definition finite_sum {A : Type} (f : A -> R) (xs : list A) : R :=
  fold_right Rplus 0 (map f xs).

Lemma finite_sum_ext {A : Type} :
  forall (xs : list A) (f g : A -> R),
    (forall x, f x = g x) ->
    finite_sum f xs = finite_sum g xs.
Proof.
  intros xs f g Heq.
  unfold finite_sum.
  f_equal.
  apply map_ext; exact Heq.
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
