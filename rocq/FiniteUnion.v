(* Arbitrarily many admission routes on an explicit finite probability space.
   This formalizes the Towers report's distribution-free bound
      max_i P(A_i) <= P(union_i A_i) <= min(1, sum_i P(A_i)).
   Unlike an abstract measure axiom, finite probabilities are computed from
   nonnegative weights on concrete outcomes. *)
From Stdlib Require Import Reals Lra Psatz List Bool Sorting.Permutation.
Require Import FiniteSum.
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

  (* Count event indicators using the standard list fold. *)
  Definition sum_event_indicators (events : list Event)
    (x : Outcome) : R :=
    FiniteSum.finite_sum (fun e => indicator (e x)) events.

  (* Retain the original public name as a transparent wrapper around
     the same shared finite-sum implementation used in FiniteMoments. *)
  Definition finite_sum (f : Outcome -> R) (xs : list Outcome) : R :=
    FiniteSum.finite_sum f xs.

  Definition finite_prob (weights : Outcome -> R)
    (samples : list Outcome) (event : Event) : R :=
      finite_sum (fun x => weights x * indicator (event x)) samples.

  (* The same list fold computes the marginal union-bound total. *)
  Definition sum_marginal_probs
    (weights : Outcome -> R) (samples : list Outcome)
    (events : list Event) : R :=
    FiniteSum.finite_sum (finite_prob weights samples) events.

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
    intros events x.
    change (0 <= FiniteSum.finite_sum
      (fun e => indicator (e x)) events).
    apply FiniteSum.finite_sum_nonnegative.
    intros e Hin; apply indicator_nonnegative.
  Qed.

  Lemma union_indicator_bound :
    forall events x,
      indicator (any_event events x) <= sum_event_indicators events x.
  Proof.
    intros events x.
    unfold sum_event_indicators.
    destruct (any_event events x) eqn:Hunion; simpl.
    - (* Stdlib.List.existsb_exists gives an event in the union.
         The shared finite-sum member bound replaces this module's
         separate induction over every Boolean event. *)
      unfold any_event in Hunion.
      apply existsb_exists in Hunion.
      destruct Hunion as [e [Hin He]].
      pose proof (FiniteSum.finite_sum_member_le
        events (fun y => indicator (y x)) e
        (fun y _ => indicator_nonnegative (y x)) Hin) as Hbound.
      rewrite He in Hbound; simpl in Hbound.
      exact Hbound.
    - apply FiniteSum.finite_sum_nonnegative.
      intros e Hin; apply indicator_nonnegative.
  Qed.

  Lemma event_member_implies_union :
    forall events e x, In e events ->
      e x = true -> any_event events x = true.
  Proof.
    intros events e x Hin Htrue.
    unfold any_event.
    apply existsb_exists.
    exists e; split; assumption.
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
    intros xs f g Hle.
    apply FiniteSum.finite_sum_monotone; exact Hle.
  Qed.

  Lemma finite_sum_extensional :
    forall xs f g, (forall x, f x = g x) ->
      finite_sum f xs = finite_sum g xs.
  Proof.
    intros xs f g Heq.
    apply FiniteSum.finite_sum_ext; exact Heq.
  Qed.

  Lemma finite_sum_addition :
    forall xs f g,
      finite_sum (fun x => f x + g x) xs =
        finite_sum f xs + finite_sum g xs.
  Proof.
    intros xs f g.
    apply FiniteSum.finite_sum_add.
  Qed.

  Lemma interchange_finite_sums :
    forall weights samples events,
      finite_sum (fun x => weights x *
        sum_event_indicators events x) samples =
      sum_marginal_probs weights samples events.
  Proof.
    intros weights samples events.
    induction events as [|e es IH]; simpl.
    - change (finite_sum (fun x => weights x * 0) samples = 0).
      transitivity (finite_sum (fun _ => 0) samples).
      + apply finite_sum_extensional; intro x; ring.
      + apply FiniteSum.finite_sum_zero.
    - change
        (finite_sum (fun x =>
           weights x * (indicator (e x) + sum_event_indicators es x))
           samples =
         finite_prob weights samples e +
           sum_marginal_probs weights samples es).
      rewrite <- IH.
      unfold finite_prob.
      transitivity (finite_sum
        (fun x => weights x * indicator (e x) +
                  weights x * sum_event_indicators es x) samples).
      + apply finite_sum_extensional; intro x; ring.
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
    apply FiniteSum.finite_sum_nonnegative.
    intros x Hx.
    apply Rmult_le_pos.
    - apply Hweights; exact Hx.
    - apply indicator_nonnegative.
  Qed.

  (* Generic Boolean events are interpreted by the same finite fold.
     Probability mass is functorial in the sample list; no new
     traversal or duplicated arithmetic is introduced. *)
  Theorem finite_prob_true :
    forall weights samples,
      finite_prob weights samples (fun _ => true) =
        finite_sum weights samples.
  Proof.
    intros weights samples.
    unfold finite_prob.
    apply finite_sum_extensional; intro x; simpl; ring.
  Qed.

  Theorem finite_prob_false :
    forall weights samples,
      finite_prob weights samples (fun _ => false) = 0.
  Proof.
    intros weights samples.
    unfold finite_prob.
    transitivity (finite_sum (fun _ => 0) samples).
    - apply finite_sum_extensional; intro x; simpl; ring.
    - apply FiniteSum.finite_sum_zero.
  Qed.

  (* Zero event mass is exactly absence of positive weighted support.
     No assumption about globally distinct sample entries is needed. *)
  Theorem finite_prob_zero_iff_no_positive_mass_support :
    forall weights samples e,
      (forall x, In x samples -> 0 <= weights x) ->
      (finite_prob weights samples e = 0 <->
       forall x, In x samples -> e x = true -> weights x = 0).
  Proof.
    intros weights samples e Hw; split.
    - intros Hzero x Hin He.
      unfold finite_prob, finite_sum in Hzero.
      assert (Hnonnegative : forall y, In y samples ->
        0 <= weights y * indicator (e y)).
      { intros y Hy; apply Rmult_le_pos.
        - apply Hw; exact Hy.
        - apply indicator_nonnegative. }
      pose proof (FiniteSum.finite_sum_nonnegative_zero
        samples (fun y => weights y * indicator (e y))
        Hnonnegative Hzero x Hin) as Hterm.
      rewrite He in Hterm.
      unfold indicator in Hterm.
      nra.
    - intros Hsupport.
      unfold finite_prob, finite_sum.
      transitivity (FiniteSum.finite_sum (fun _ => 0) samples).
      + apply FiniteSum.finite_sum_ext_in.
        intros x Hin.
        destruct (e x) eqn:He; simpl.
        * rewrite (Hsupport x Hin He); ring.
        * ring.
      + apply FiniteSum.finite_sum_zero.
  Qed.

  Theorem finite_prob_positive_of_positive_support :
    forall weights samples e x,
      (forall y, In y samples -> 0 <= weights y) ->
      In x samples -> e x = true -> 0 < weights x ->
      0 < finite_prob weights samples e.
  Proof.
    intros weights samples e x Hw Hin He Hpositive.
    unfold finite_prob, finite_sum.
    assert (Hnonnegative : forall y, In y samples ->
      0 <= weights y * indicator (e y)).
    { intros y Hy; apply Rmult_le_pos.
      - apply Hw; exact Hy.
      - apply indicator_nonnegative. }
    pose proof (FiniteSum.finite_sum_member_le
      samples (fun y => weights y * indicator (e y))
      x Hnonnegative Hin) as Hbound.
    rewrite He in Hbound.
    unfold indicator in Hbound.
    nra.
  Qed.

  Theorem finite_prob_sample_append :
    forall weights left right e,
      finite_prob weights (left ++ right) e =
        finite_prob weights left e + finite_prob weights right e.
  Proof.
    intros weights left right e.
    unfold finite_prob, finite_sum.
    apply FiniteSum.finite_sum_app.
  Qed.

  Theorem finite_prob_sample_permutation :
    forall weights left right e,
      Permutation left right ->
      finite_prob weights left e = finite_prob weights right e.
  Proof.
    intros weights left right e Hperm.
    unfold finite_prob, finite_sum.
    apply FiniteSum.finite_sum_permutation; exact Hperm.
  Qed.

  Theorem union_prob_sample_permutation :
    forall weights left right events,
      Permutation left right ->
      union_prob weights left events = union_prob weights right events.
  Proof.
    intros weights left right events Hperm.
    unfold union_prob.
    apply finite_prob_sample_permutation; exact Hperm.
  Qed.

  Theorem sum_marginal_probs_event_permutation :
    forall weights samples left right,
      Permutation left right ->
      sum_marginal_probs weights samples left =
        sum_marginal_probs weights samples right.
  Proof.
    intros weights samples left right Hperm.
    unfold sum_marginal_probs.
    apply FiniteSum.finite_sum_permutation; exact Hperm.
  Qed.

  Theorem finite_prob_event_monotone :
    forall weights samples e f,
      (forall x, In x samples -> 0 <= weights x) ->
      (forall x, In x samples -> e x = true -> f x = true) ->
      finite_prob weights samples e <= finite_prob weights samples f.
  Proof.
    intros weights samples e f Hw Hsub.
    unfold finite_prob.
    apply finite_sum_monotone.
    intros x Hx.
    pose proof (Hw x Hx).
    pose proof (indicator_implication_bound
      (e x) (f x) (Hsub x Hx)).
    nra.
  Qed.

  Theorem normalized_finite_prob_unit_interval :
    forall weights samples e,
      (forall x, In x samples -> 0 <= weights x) ->
      finite_sum weights samples = 1 ->
      0 <= finite_prob weights samples e /\
        finite_prob weights samples e <= 1.
  Proof.
    intros weights samples e Hw Hmass.
    split.
    - unfold finite_prob.
      apply FiniteSum.finite_sum_nonnegative.
      intros x Hx.
      apply Rmult_le_pos.
      + apply Hw; exact Hx.
      + apply indicator_nonnegative.
    - unfold finite_prob.
      assert (Hle :
        finite_sum (fun x => weights x * indicator (e x)) samples <=
        finite_sum weights samples).
      { apply finite_sum_monotone.
        intros x Hx.
        pose proof (Hw x Hx).
        pose proof (indicator_at_most_one (e x)).
        nra. }
      lra.
  Qed.

  Theorem empty_family_probability_zero :
    forall weights samples, union_prob weights samples [] = 0.
  Proof.
    intros weights samples.
    change (finite_prob weights samples (fun _ => false) = 0).
    apply finite_prob_false.
  Qed.

  Theorem singleton_family_probability :
    forall weights samples e,
      union_prob weights samples [e] =
        finite_prob weights samples e.
  Proof.
    intros weights samples e.
    unfold union_prob, finite_prob.
    apply finite_sum_extensional; intro x.
    unfold any_event; simpl.
    rewrite orb_false_r.
    reflexivity.
  Qed.


  (* Event lists represent sets for union probability: only their membership
     matters.  Bool.existsb_exists and Sorting.Permutation.Permutation_in
     replace a custom induction over list permutations. *)

  Theorem union_prob_membership_extensional :
    forall weights samples left right,
      (forall e, In e left <-> In e right) ->
      union_prob weights samples left =
        union_prob weights samples right.
  Proof.
    intros weights samples left right Hmembers.
    unfold union_prob, finite_prob.
    apply finite_sum_extensional; intro x.
    assert (Hevents : any_event left x = any_event right x).
    { destruct (any_event left x) eqn:Hleft;
      destruct (any_event right x) eqn:Hright; try reflexivity.
      - unfold any_event in Hleft, Hright.
        apply existsb_exists in Hleft.
        destruct Hleft as [e [Hin He]].
        assert (Hyes : existsb (fun a => a x) right = true).
        { apply existsb_exists. exists e. split.
          - apply (proj1 (Hmembers e)); exact Hin.
          - exact He. }
        rewrite Hright in Hyes; discriminate.
      - unfold any_event in Hleft, Hright.
        apply existsb_exists in Hright.
        destruct Hright as [e [Hin He]].
        assert (Hyes : existsb (fun a => a x) left = true).
        { apply existsb_exists. exists e. split.
          - apply (proj2 (Hmembers e)); exact Hin.
          - exact He. }
        rewrite Hleft in Hyes; discriminate. }
    rewrite Hevents; reflexivity.
  Qed.

  Theorem union_prob_permutation_invariant :
    forall weights samples left right,
      Permutation left right ->
      union_prob weights samples left =
        union_prob weights samples right.
  Proof.
    intros weights samples left right Hperm.
    apply union_prob_membership_extensional.
    intro e; split; intro Hin.
    - eapply Permutation_in; eauto.
    - eapply Permutation_in.
      + apply Permutation_sym; exact Hperm.
      + exact Hin.
  Qed.

  Theorem union_prob_duplicate_route :
    forall weights samples e events,
      union_prob weights samples (e :: e :: events) =
        union_prob weights samples (e :: events).
  Proof.
    intros weights samples e events.
    apply union_prob_membership_extensional.
    intro a; simpl; tauto.
  Qed.


  (* Boolean complement and inclusion-exclusion are interpreted through
     Stdlib.Bool's negb/orb/andb, without a bespoke event-set datatype.
     These identities hold for arbitrary real weights; nonnegativity and
     normalization are required only for probability bounds. *)

  Lemma indicator_complement :
    forall b, indicator (negb b) + indicator b = 1.
  Proof.
    intros []; simpl; ring.
  Qed.

  Theorem finite_prob_complement :
    forall weights samples e,
      finite_prob weights samples (fun x => negb (e x)) +
        finite_prob weights samples e =
        finite_sum weights samples.
  Proof.
    intros weights samples e.
    unfold finite_prob.
    rewrite <- finite_sum_addition.
    apply finite_sum_extensional; intro x.
    rewrite <- Rmult_plus_distr_l.
    rewrite indicator_complement.
    ring.
  Qed.

  Theorem normalized_finite_prob_complement :
    forall weights samples e,
      finite_sum weights samples = 1 ->
      finite_prob weights samples (fun x => negb (e x)) =
        1 - finite_prob weights samples e.
  Proof.
    intros weights samples e Htotal.
    pose proof (finite_prob_complement weights samples e) as H.
    rewrite Htotal in H; lra.
  Qed.

  Lemma indicator_union_intersection :
    forall b c,
      indicator (orb b c) + indicator (andb b c) =
        indicator b + indicator c.
  Proof.
    intros [] []; simpl; ring.
  Qed.

  Theorem finite_prob_inclusion_exclusion :
    forall weights samples e f,
      finite_prob weights samples (fun x => orb (e x) (f x)) +
        finite_prob weights samples (fun x => andb (e x) (f x)) =
      finite_prob weights samples e + finite_prob weights samples f.
  Proof.
    intros weights samples e f.
    unfold finite_prob.
    rewrite <- !finite_sum_addition.
    apply finite_sum_extensional; intro x.
    rewrite <- !Rmult_plus_distr_l.
    rewrite indicator_union_intersection.
    ring.
  Qed.

  Theorem two_event_union_probability :
    forall weights samples e f,
      union_prob weights samples [e; f] =
        finite_prob weights samples (fun x => orb (e x) (f x)).
  Proof.
    intros weights samples e f.
    unfold union_prob, finite_prob.
    apply finite_sum_extensional; intro x.
    unfold any_event; simpl.
    rewrite orb_false_r.
    reflexivity.
  Qed.

  Theorem two_event_union_inclusion_exclusion :
    forall weights samples e f,
      union_prob weights samples [e; f] +
        finite_prob weights samples (fun x => andb (e x) (f x)) =
      finite_prob weights samples e + finite_prob weights samples f.
  Proof.
    intros weights samples e f.
    rewrite two_event_union_probability.
    apply finite_prob_inclusion_exclusion.
  Qed.


  (* Concatenating event families is covered by Stdlib.List.existsb_app;
     concatenating marginal sums uses map_app and fold_right_app. *)

  Lemma any_event_append :
    forall left right x,
      any_event (left ++ right) x =
        orb (any_event left x) (any_event right x).
  Proof.
    intros left right x.
    unfold any_event.
    rewrite existsb_app.
    reflexivity.
  Qed.

  Theorem union_prob_append :
    forall weights samples left right,
      union_prob weights samples (left ++ right) =
        finite_prob weights samples
          (fun x => orb (any_event left x) (any_event right x)).
  Proof.
    intros weights samples left right.
    unfold union_prob, finite_prob.
    apply finite_sum_extensional; intro x.
    rewrite any_event_append.
    reflexivity.
  Qed.

  Theorem sum_marginal_probs_append :
    forall weights samples left right,
      sum_marginal_probs weights samples (left ++ right) =
        sum_marginal_probs weights samples left +
        sum_marginal_probs weights samples right.
  Proof.
    intros weights samples left right.
    change (FiniteSum.finite_sum
              (finite_prob weights samples) (left ++ right) =
            FiniteSum.finite_sum (finite_prob weights samples) left +
            FiniteSum.finite_sum (finite_prob weights samples) right).
    apply FiniteSum.finite_sum_app.
  Qed.

End FiniteOutcomeSpace.

(* The inequalities remain valid for a list with repeated sample points;
   normalized probabilities should be interpreted with the corresponding
   weighted-multiset convention. In applications with distinct outcomes,
   one normally uses a finite enumeration without duplicates. *)
