(* Arbitrarily many admission routes on an explicit finite probability space.
   This formalizes the Towers report's distribution-free bound
      max_i P(A_i) <= P(union_i A_i) <= min(1, sum_i P(A_i)).
   Unlike an abstract measure axiom, finite probabilities are computed from
   nonnegative weights on concrete outcomes. *)
From Stdlib Require Import Reals Lra Psatz List Bool.
Import ListNotations.
Open Scope R_scope.

Section FiniteOutcomeSpace.
  Variable Outcome : Type.
  Definition Event := Outcome -> bool.

  Definition indicator (b : bool) : R := if b then 1 else 0.

  (* Stdlib.List.existsb is the finite Boolean OR over event membership;
     no project-specific Boolean recursion is required. *)
  Definition any_event (events : list Event) (x : Outcome) : bool :=
    existsb (fun e => e x) events.

  Fixpoint sum_event_indicators (events : list Event)
    (x : Outcome) : R :=
    match events with
    | [] => 0
    | e :: es => indicator (e x) + sum_event_indicators es x
    end.

  (* Finite integration uses standard List.fold_right/map, as in
     FiniteMoments; the sample list may contain repeated outcomes. *)
  Definition finite_sum (f : Outcome -> R) (xs : list Outcome) : R :=
    fold_right Rplus 0 (map f xs).

  Definition finite_prob (weights : Outcome -> R)
    (samples : list Outcome) (event : Event) : R :=
      finite_sum (fun x => weights x * indicator (event x)) samples.

  Fixpoint sum_marginal_probs
    (weights : Outcome -> R) (samples : list Outcome)
    (events : list Event) : R :=
    match events with
    | [] => 0
    | e :: es => finite_prob weights samples e +
                 sum_marginal_probs weights samples es
    end.

  Definition union_prob (weights : Outcome -> R)
    (samples : list Outcome) (events : list Event) : R :=
    finite_prob weights samples (any_event events).

  Lemma indicator_nonnegative :
    forall b, 0 <= indicator b.
  Proof.
    intros []; unfold indicator; lra.
  Qed.

  Lemma indicator_at_most_one :
    forall b, indicator b <= 1.
  Proof.
    intros []; unfold indicator; lra.
  Qed.

  Lemma sum_indicators_nonnegative :
    forall events x, 0 <= sum_event_indicators events x.
  Proof.
    intros events; induction events as [|e es IH]; intro x; simpl.
    - lra.
    - specialize (IH x).
      pose proof (indicator_nonnegative (e x)).
      lra.
  Qed.

  Lemma union_indicator_bound :
    forall events x,
      indicator (any_event events x) <= sum_event_indicators events x.
  Proof.
    intros events; induction events as [|e es IH]; intro x; simpl.
    - unfold indicator; lra.
    - destruct (e x) eqn:He; simpl.
      + pose proof (sum_indicators_nonnegative es x); lra.
      + specialize (IH x); lra.
  Qed.

  Lemma event_member_implies_union :
    forall events e x, In e events ->
      e x = true -> any_event events x = true.
  Proof.
    induction events as [|f fs IH]; intros e x Hin Htrue.
    - inversion Hin.
    - simpl in Hin.
      destruct Hin as [Heq | Hin].
      + subst f. simpl. rewrite Htrue. reflexivity.
      + simpl. specialize (IH e x Hin Htrue).
        rewrite IH. destruct (f x); reflexivity.
  Qed.

  Lemma indicator_implication_bound :
    forall b c,
      (b = true -> c = true) ->
      indicator b <= indicator c.
  Proof.
    intros [] [] H; unfold indicator; lra.
  Qed.

  Lemma finite_sum_monotone :
    forall xs f g,
      (forall x, In x xs -> f x <= g x) ->
      finite_sum f xs <= finite_sum g xs.
  Proof.
    induction xs as [|x xs IH]; intros f g Hle;
      unfold finite_sum in *; simpl.
    - lra.
    - assert (Hx : f x <= g x) by (apply Hle; simpl; auto).
      assert (Hxs : finite_sum f xs <= finite_sum g xs).
      { apply IH. intros y Hy. apply Hle. simpl; auto. }
      lra.
  Qed.

  Lemma finite_sum_extensional :
    forall xs f g, (forall x, f x = g x) ->
      finite_sum f xs = finite_sum g xs.
  Proof.
    induction xs as [|x xs IH]; intros f g Heq;
      unfold finite_sum in *; simpl.
    - reflexivity.
    - rewrite (Heq x), (IH f g Heq); reflexivity.
  Qed.

  Lemma finite_sum_addition :
    forall xs f g,
      finite_sum (fun x => f x + g x) xs =
        finite_sum f xs + finite_sum g xs.
  Proof.
    induction xs as [|x xs IH]; intros f g;
      unfold finite_sum in *; simpl.
    - ring.
    - rewrite IH; ring.
  Qed.

  Lemma interchange_finite_sums :
    forall weights samples events,
      finite_sum (fun x => weights x *
        sum_event_indicators events x) samples =
      sum_marginal_probs weights samples events.
  Proof.
    intros weights samples events.
    induction events as [|e es IH]; simpl.
    - induction samples as [|x xs IHxs];
        unfold finite_sum in *; simpl.
      + reflexivity.
      + rewrite IHxs; ring.
    - unfold finite_prob.
      rewrite <- IH.
      transitivity (finite_sum
        (fun x => weights x * indicator (e x) +
                  weights x * sum_event_indicators es x) samples).
      + apply finite_sum_extensional; intro x; simpl; ring.
      + rewrite finite_sum_addition; reflexivity.
  Qed.

  Theorem arbitrary_union_bound :
    forall weights samples events,
      (forall x, In x samples -> 0 <= weights x) ->
      union_prob weights samples events <=
        sum_marginal_probs weights samples events.
  Proof.
    intros weights samples events Hweights.
    unfold union_prob, finite_prob.
    rewrite <- interchange_finite_sums.
    apply finite_sum_monotone.
    intros x Hx.
    specialize (Hweights x Hx).
    pose proof (union_indicator_bound events x).
    nra.
  Qed.

  Theorem arbitrary_union_contains_every_member :
    forall weights samples events e,
      In e events ->
      (forall x, In x samples -> 0 <= weights x) ->
      finite_prob weights samples e <=
        union_prob weights samples events.
  Proof.
    intros weights samples events e Hin Hweights.
    unfold finite_prob, union_prob, finite_prob.
    apply finite_sum_monotone.
    intros x Hx.
    pose proof (Hweights x Hx) as Hw.
    assert (Himp :
      indicator (e x) <= indicator (any_event events x)).
    { apply indicator_implication_bound.
      intro He; eapply event_member_implies_union; eauto. }
    nra.
  Qed.

  Theorem arbitrary_union_at_most_total_mass :
    forall weights samples events,
      (forall x, In x samples -> 0 <= weights x) ->
      union_prob weights samples events <= finite_sum weights samples.
  Proof.
    intros weights samples events Hweights.
    unfold union_prob, finite_prob.
    apply finite_sum_monotone.
    intros x Hx.
    pose proof (Hweights x Hx).
    pose proof (indicator_at_most_one (any_event events x)).
    nra.
  Qed.

  Theorem normalized_arbitrary_union_at_most_one :
    forall weights samples events,
      (forall x, In x samples -> 0 <= weights x) ->
      finite_sum weights samples = 1 ->
      union_prob weights samples events <= 1.
  Proof.
    intros weights samples events Hweights Htotal.
    pose proof (arbitrary_union_at_most_total_mass
      weights samples events Hweights).
    lra.
  Qed.

  Theorem arbitrary_union_nonnegative :
    forall weights samples events,
      (forall x, In x samples -> 0 <= weights x) ->
      0 <= union_prob weights samples events.
  Proof.
    intros weights samples events Hweights.
    unfold union_prob, finite_prob.
    revert Hweights.
    induction samples as [|x xs IH]; intros Hweights;
      unfold finite_sum in *; simpl.
    - lra.
    - assert (Hw : 0 <= weights x)
        by (apply Hweights; simpl; auto).
      assert (Hind : 0 <= indicator (any_event events x))
        by apply indicator_nonnegative.
      assert (Htail : forall y, In y xs -> 0 <= weights y).
      { intros y Hy. apply Hweights. simpl; auto. }
      specialize (IH Htail).
      nra.
  Qed.

  Theorem empty_family_probability_zero :
    forall weights samples, union_prob weights samples [] = 0.
  Proof.
    intros weights samples.
    induction samples as [|x xs IH].
    - reflexivity.
    - change (weights x * 0 + union_prob weights xs [] = 0).
      rewrite IH; ring.
  Qed.

  Theorem singleton_family_probability :
    forall weights samples e,
      union_prob weights samples [e] =
        finite_prob weights samples e.
  Proof.
    intros weights samples e.
    unfold union_prob, finite_prob.
    apply finite_sum_extensional; intro x; simpl.
    destruct (e x); simpl; ring.
  Qed.

End FiniteOutcomeSpace.

(* The inequalities remain valid for a list with repeated sample points;
   normalized probabilities should be interpreted with the corresponding
   weighted-multiset convention. In applications with distinct outcomes,
   one normally uses a finite enumeration without duplicates. *)
