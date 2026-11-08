(** Module: FiniteUnion.v
   Purpose: Distribution-free union probability for finitely many Boolean events.
   Defines event indicators, finite weighted masses, and Boolean unions, then proves monotonicity, inclusion-exclusion, Fréchet and union bounds.
   Mathematical representation: Outcomes are enumerated in a list; Boolean events are functions on outcomes and probability sums use FiniteSum.finite_sum.
   Explicit hypotheses: Bounds use nonnegative outcome weights; unit upper bounds additionally require mass normalization; raw identities need neither.
   Library use: Stdlib.List.existsb, filter, Bool, Sorting.Permutation and the shared FiniteSum lemmas.
   Limitations: Repeated sample entries contribute repeated weight; no measure axiom, independence or distributional model is imported.
   Proof documentation: Every public and helper declaration below has its
   own statement, hypothesis, proof-approach, and scope commentary.
   Reproduction: rocq compile FiniteUnion.v (after imported local modules);
   see rocq/README.md and rocq/LIBRARY_AUDIT.md for dependency order,
   checked-claim mapping, and library audit. All results are Rocq-kernel
   checked; no unchecked evidence is created by comments.
 *)
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
  (**
   [Event] (definition).
   Meaning: Gives a precise computational or algebraic interpretation of the
   named construction or assertion.
   Formal construction: = Outcome -> bool.
   Hypotheses: A definition; its parameters and fields appear in the signature,
   with no silent statistical assumptions.
   Implementation: Stdlib Lra linear arithmetic; notably indicator.
   Library discipline: Stdlib.List.existsb, filter, Bool, Sorting.Permutation
   and the shared FiniteSum lemmas.
   Scope: Repeated sample entries contribute repeated weight; no measure axiom,
   independence or distributional model is imported.
   *)
  Definition Event := Outcome -> bool.

  (**
   [indicator] (definition).
   Meaning: Gives a precise computational or algebraic interpretation of the
   named construction or assertion.
   Formal construction: (b : bool) : R := if b then 1 else 0.
   Hypotheses: A definition; its parameters and fields appear in the signature,
   with no silent statistical assumptions.
   Implementation: Stdlib Lra linear arithmetic; notably indicator.
   Library discipline: Stdlib.List.existsb, filter, Bool, Sorting.Permutation
   and the shared FiniteSum lemmas.
   Scope: Repeated sample entries contribute repeated weight; no measure axiom,
   independence or distributional model is imported.
   *)
  Definition indicator (b : bool) : R := if b then 1 else 0.

  (* Stdlib.List.existsb is the finite Boolean OR over event membership;
     no project-specific Boolean recursion is required. *)
  (**
   [any_event] (definition).
   Meaning: Gives a precise computational or algebraic interpretation of the
   named construction or assertion.
   Formal construction: (events : list Event) (x : Outcome) : bool := existsb
   (fun e => e x) events.
   Hypotheses: A definition; its parameters and fields appear in the signature,
   with no silent statistical assumptions.
   Implementation: Stdlib Lra linear arithmetic; notably indicator.
   Library discipline: Stdlib.List.existsb, filter, Bool, Sorting.Permutation
   and the shared FiniteSum lemmas.
   Scope: Repeated sample entries contribute repeated weight; no measure axiom,
   independence or distributional model is imported.
   *)
  Definition any_event (events : list Event) (x : Outcome) : bool :=
    existsb (fun e => e x) events.

  (* Count event indicators using the standard list fold. *)
  (**
   [sum_event_indicators] (definition).
   Meaning: Establishes finite-sum or finite-expectation algebra while
   retaining the original sum semantics.
   Formal construction: (events : list Event) (x : Outcome) : R :=
   FiniteSum.finite_sum (fun e => indicator (e x)) events.
   Hypotheses: A definition; its parameters and fields appear in the signature,
   with no silent statistical assumptions.
   Implementation: Stdlib Lra linear arithmetic; notably indicator.
   Library discipline: Stdlib.List.existsb, filter, Bool, Sorting.Permutation
   and the shared FiniteSum lemmas.
   Scope: Repeated sample entries contribute repeated weight; no measure axiom,
   independence or distributional model is imported.
   *)
  Definition sum_event_indicators (events : list Event)
    (x : Outcome) : R :=
    FiniteSum.finite_sum (fun e => indicator (e x)) events.

  (* Retain the original public name as a transparent wrapper around
     the same shared finite-sum implementation used in FiniteMoments. *)
  (**
   [finite_sum] (definition).
   Meaning: Establishes finite-sum or finite-expectation algebra while
   retaining the original sum semantics.
   Formal construction: R) (xs : list Outcome) : R := FiniteSum.finite_sum f
   xs.
   Hypotheses: A definition; its parameters and fields appear in the signature,
   with no silent statistical assumptions.
   Implementation: Stdlib Lra linear arithmetic; notably indicator.
   Library discipline: Stdlib.List.existsb, filter, Bool, Sorting.Permutation
   and the shared FiniteSum lemmas.
   Scope: Repeated sample entries contribute repeated weight; no measure axiom,
   independence or distributional model is imported.
   *)
  Definition finite_sum (f : Outcome -> R) (xs : list Outcome) : R :=
    FiniteSum.finite_sum f xs.

  (**
   [finite_prob] (definition).
   Meaning: Gives a precise computational or algebraic interpretation of the
   named construction or assertion.
   Formal construction: R) (samples : list Outcome) (event : Event) : R :=
   finite_sum (fun x => weights x * indicator (event x)) samples.
   Hypotheses: A definition; its parameters and fields appear in the signature,
   with no silent statistical assumptions.
   Implementation: Stdlib Lra linear arithmetic; notably indicator.
   Library discipline: Stdlib.List.existsb, filter, Bool, Sorting.Permutation
   and the shared FiniteSum lemmas.
   Scope: Repeated sample entries contribute repeated weight; no measure axiom,
   independence or distributional model is imported.
   *)
  Definition finite_prob (weights : Outcome -> R)
    (samples : list Outcome) (event : Event) : R :=
      finite_sum (fun x => weights x * indicator (event x)) samples.

  (* The same list fold computes the marginal union-bound total. *)
  (**
   [sum_marginal_probs] (definition).
   Meaning: Establishes finite-sum or finite-expectation algebra while
   retaining the original sum semantics.
   Formal construction: R) (samples : list Outcome) (events : list Event) : R
   := FiniteSum.finite_sum (finite_prob weights samples) events.
   Hypotheses: A definition; its parameters and fields appear in the signature,
   with no silent statistical assumptions.
   Implementation: Stdlib Lra linear arithmetic; notably indicator.
   Library discipline: Stdlib.List.existsb, filter, Bool, Sorting.Permutation
   and the shared FiniteSum lemmas.
   Scope: Repeated sample entries contribute repeated weight; no measure axiom,
   independence or distributional model is imported.
   *)
  Definition sum_marginal_probs
    (weights : Outcome -> R) (samples : list Outcome)
    (events : list Event) : R :=
    FiniteSum.finite_sum (finite_prob weights samples) events.

  (**
   [union_prob] (definition).
   Meaning: Controls union/intersection mass for Boolean events through finite
   probability algebra.
   Formal construction: R) (samples : list Outcome) (events : list Event) : R
   := finite_prob weights samples (any_event events).
   Hypotheses: A definition; its parameters and fields appear in the signature,
   with no silent statistical assumptions.
   Implementation: Stdlib Lra linear arithmetic; notably indicator.
   Library discipline: Stdlib.List.existsb, filter, Bool, Sorting.Permutation
   and the shared FiniteSum lemmas.
   Scope: Repeated sample entries contribute repeated weight; no measure axiom,
   independence or distributional model is imported.
   *)
  Definition union_prob (weights : Outcome -> R)
    (samples : list Outcome) (events : list Event) : R :=
    finite_prob weights samples (any_event events).

  (**
   [indicator_nonnegative] (lemma).
   Meaning: Gives a precise computational or algebraic interpretation of the
   named construction or assertion.
   Formal conclusion: forall b, 0 <= indicator b.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: Stdlib Lra linear arithmetic; notably indicator.
   Library discipline: Stdlib.List.existsb, filter, Bool, Sorting.Permutation
   and the shared FiniteSum lemmas.
   Scope: Repeated sample entries contribute repeated weight; no measure axiom,
   independence or distributional model is imported.
   *)
  Lemma indicator_nonnegative :
    forall b, 0 <= indicator b.
  Proof.
    intros []; unfold indicator; lra.
  Qed.

  (**
   [indicator_at_most_one] (lemma).
   Meaning: Gives a precise computational or algebraic interpretation of the
   named construction or assertion.
   Formal conclusion: forall b, indicator b <= 1.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: Stdlib Lra linear arithmetic; notably indicator.
   Library discipline: Stdlib.List.existsb, filter, Bool, Sorting.Permutation
   and the shared FiniteSum lemmas.
   Scope: Repeated sample entries contribute repeated weight; no measure axiom,
   independence or distributional model is imported.
   *)
  Lemma indicator_at_most_one :
    forall b, indicator b <= 1.
  Proof.
    intros []; unfold indicator; lra.
  Qed.

  (**
   [sum_indicators_nonnegative] (lemma).
   Meaning: Establishes finite-sum or finite-expectation algebra while
   retaining the original sum semantics.
   Formal conclusion: forall events x, 0 <= sum_event_indicators events x.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: application of already-proved lemmas; notably
   FiniteSum.finite_sum_nonnegative., indicator_nonnegative..
   Library discipline: Stdlib.List.existsb, filter, Bool, Sorting.Permutation
   and the shared FiniteSum lemmas.
   Scope: Repeated sample entries contribute repeated weight; no measure axiom,
   independence or distributional model is imported.
   *)
  Lemma sum_indicators_nonnegative :
    forall events x, 0 <= sum_event_indicators events x.
  Proof.
    intros events x.
    change (0 <= FiniteSum.finite_sum
      (fun e => indicator (e x)) events).
    apply FiniteSum.finite_sum_nonnegative.
    intros e Hin; apply indicator_nonnegative.
  Qed.

  (**
   [union_indicator_bound] (lemma).
   Meaning: Controls union/intersection mass for Boolean events through finite
   probability algebra.
   Formal conclusion: forall events x, indicator (any_event events x) <=
   sum_event_indicators events x.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: structural induction on a finite list or natural index,
   equational rewriting, application of already-proved lemmas, explicit case
   analysis; notably sum_event_indicators., any_event, existsb_exists.
   Library discipline: Stdlib.List.existsb, filter, Bool, Sorting.Permutation
   and the shared FiniteSum lemmas.
   Scope: Repeated sample entries contribute repeated weight; no measure axiom,
   independence or distributional model is imported.
   *)
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
      change (indicator (e x) <=
        FiniteSum.finite_sum (fun y => indicator (y x)) events)
        in Hbound.
      rewrite He in Hbound; simpl in Hbound.
      exact Hbound.
    - apply FiniteSum.finite_sum_nonnegative.
      intros e Hin; apply indicator_nonnegative.
  Qed.

  (**
   [event_member_implies_union] (lemma).
   Meaning: Controls union/intersection mass for Boolean events through finite
   probability algebra.
   Formal conclusion: any_event events x = true.
   Hypotheses: Requires enumerated-list membership where shown in the
   statement; all other constraints remain explicit.
   Proof outline: application of already-proved lemmas; notably any_event.,
   existsb_exists..
   Library discipline: Stdlib.List.existsb, filter, Bool, Sorting.Permutation
   and the shared FiniteSum lemmas.
   Scope: Repeated sample entries contribute repeated weight; no measure axiom,
   independence or distributional model is imported.
   *)
  Lemma event_member_implies_union :
    forall events e x, In e events ->
      e x = true -> any_event events x = true.
  Proof.
    intros events e x Hin Htrue.
    unfold any_event.
    apply existsb_exists.
    exists e; split; assumption.
  Qed.

  (**
   [indicator_implication_bound] (lemma).
   Meaning: Gives a precise computational or algebraic interpretation of the
   named construction or assertion.
   Formal conclusion: indicator b <= indicator c.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: Stdlib Lra linear arithmetic; notably indicator.
   Library discipline: Stdlib.List.existsb, filter, Bool, Sorting.Permutation
   and the shared FiniteSum lemmas.
   Scope: Repeated sample entries contribute repeated weight; no measure axiom,
   independence or distributional model is imported.
   *)
  Lemma indicator_implication_bound :
    forall b c,
      (b = true -> c = true) ->
      indicator b <= indicator c.
  Proof.
    intros [] [] H; unfold indicator; lra.
  Qed.

  (**
   [finite_sum_monotone] (lemma).
   Meaning: Establishes finite-sum or finite-expectation algebra while
   retaining the original sum semantics.
   Formal conclusion: finite_sum f xs <= finite_sum g xs.
   Hypotheses: Requires enumerated-list membership where shown in the
   statement; all other constraints remain explicit.
   Proof outline: application of already-proved lemmas; notably
   FiniteSum.finite_sum_monotone.
   Library discipline: Stdlib.List.existsb, filter, Bool, Sorting.Permutation
   and the shared FiniteSum lemmas.
   Scope: Repeated sample entries contribute repeated weight; no measure axiom,
   independence or distributional model is imported.
   *)
  Lemma finite_sum_monotone :
    forall xs f g,
      (forall x, In x xs -> f x <= g x) ->
      finite_sum f xs <= finite_sum g xs.
  Proof.
    intros xs f g Hle.
    apply FiniteSum.finite_sum_monotone; exact Hle.
  Qed.

  (**
   [finite_sum_extensional] (lemma).
   Meaning: Establishes finite-sum or finite-expectation algebra while
   retaining the original sum semantics.
   Formal conclusion: finite_sum f xs = finite_sum g xs.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: application of already-proved lemmas; notably
   FiniteSum.finite_sum_ext.
   Library discipline: Stdlib.List.existsb, filter, Bool, Sorting.Permutation
   and the shared FiniteSum lemmas.
   Scope: Repeated sample entries contribute repeated weight; no measure axiom,
   independence or distributional model is imported.
   *)
  Lemma finite_sum_extensional :
    forall xs f g, (forall x, f x = g x) ->
      finite_sum f xs = finite_sum g xs.
  Proof.
    intros xs f g Heq.
    apply FiniteSum.finite_sum_ext; exact Heq.
  Qed.

  (**
   [finite_sum_addition] (lemma).
   Meaning: Establishes finite-sum or finite-expectation algebra while
   retaining the original sum semantics.
   Formal conclusion: forall xs f g, finite_sum (fun x => f x + g x) xs =
   finite_sum f xs + finite_sum g xs.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: application of already-proved lemmas; notably
   FiniteSum.finite_sum_add..
   Library discipline: Stdlib.List.existsb, filter, Bool, Sorting.Permutation
   and the shared FiniteSum lemmas.
   Scope: Repeated sample entries contribute repeated weight; no measure axiom,
   independence or distributional model is imported.
   *)
  Lemma finite_sum_addition :
    forall xs f g,
      finite_sum (fun x => f x + g x) xs =
        finite_sum f xs + finite_sum g xs.
  Proof.
    intros xs f g.
    apply FiniteSum.finite_sum_add.
  Qed.

  (**
   [interchange_finite_sums] (lemma).
   Meaning: Establishes finite-sum or finite-expectation algebra while
   retaining the original sum semantics.
   Formal conclusion: forall weights samples events, finite_sum (fun x =>
   weights x * sum_event_indicators events x) samples = sum_marginal_probs
   weights samples events.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: application of already-proved lemmas; notably
   FiniteSum.finite_sum_ext, FiniteSum.finite_sum_scale.,
   FiniteSum.finite_sum_swap..
   Library discipline: Stdlib.List.existsb, filter, Bool, Sorting.Permutation
   and the shared FiniteSum lemmas.
   Scope: Repeated sample entries contribute repeated weight; no measure axiom,
   independence or distributional model is imported.
   *)
  Lemma interchange_finite_sums :
    forall weights samples events,
      finite_sum (fun x => weights x *
        sum_event_indicators events x) samples =
      sum_marginal_probs weights samples events.
  Proof.
    intros weights samples events.
    change
      (FiniteSum.finite_sum
        (fun x => weights x * FiniteSum.finite_sum
          (fun e => indicator (e x)) events) samples =
       FiniteSum.finite_sum
        (fun e => FiniteSum.finite_sum
          (fun x => weights x * indicator (e x)) samples) events).
    transitivity (FiniteSum.finite_sum
      (fun x => FiniteSum.finite_sum
        (fun e => weights x * indicator (e x)) events) samples).
    - apply FiniteSum.finite_sum_ext; intro x.
      symmetry; apply FiniteSum.finite_sum_scale.
    - apply FiniteSum.finite_sum_swap.
  Qed.

  (**
   [arbitrary_union_bound] (theorem).
   Meaning: Controls union/intersection mass for Boolean events through finite
   probability algebra.
   Formal conclusion: union_prob weights samples events <= sum_marginal_probs
   weights samples events.
   Hypotheses: Requires nonnegative outcome weights; enumerated-list membership
   where shown in the statement; all other constraints remain explicit.
   Proof outline: equational rewriting, application of already-proved lemmas,
   Stdlib Psatz nonlinear arithmetic; notably union_prob, finite_sum_monotone.,
   union_indicator_bound.
   Library discipline: Stdlib.List.existsb, filter, Bool, Sorting.Permutation
   and the shared FiniteSum lemmas.
   Scope: Repeated sample entries contribute repeated weight; no measure axiom,
   independence or distributional model is imported.
   *)
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

  (**
   [arbitrary_union_contains_every_member] (theorem).
   Meaning: Controls union/intersection mass for Boolean events through finite
   probability algebra.
   Formal conclusion: finite_prob weights samples e <= union_prob weights
   samples events.
   Hypotheses: Requires nonnegative outcome weights; enumerated-list membership
   where shown in the statement; all other constraints remain explicit.
   Proof outline: application of already-proved lemmas, Stdlib Psatz nonlinear
   arithmetic; notably finite_prob, finite_sum_monotone.,
   indicator_implication_bound..
   Library discipline: Stdlib.List.existsb, filter, Bool, Sorting.Permutation
   and the shared FiniteSum lemmas.
   Scope: Repeated sample entries contribute repeated weight; no measure axiom,
   independence or distributional model is imported.
   *)
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

  (**
   [arbitrary_union_at_most_total_mass] (theorem).
   Meaning: Controls union/intersection mass for Boolean events through finite
   probability algebra.
   Formal conclusion: union_prob weights samples events <= finite_sum weights
   samples.
   Hypotheses: Requires nonnegative outcome weights; enumerated-list membership
   where shown in the statement; all other constraints remain explicit.
   Proof outline: application of already-proved lemmas, Stdlib Psatz nonlinear
   arithmetic; notably union_prob, finite_sum_monotone., indicator_at_most_one.
   Library discipline: Stdlib.List.existsb, filter, Bool, Sorting.Permutation
   and the shared FiniteSum lemmas.
   Scope: Repeated sample entries contribute repeated weight; no measure axiom,
   independence or distributional model is imported.
   *)
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

  (**
   [normalized_arbitrary_union_at_most_one] (theorem).
   Meaning: Controls union/intersection mass for Boolean events through finite
   probability algebra.
   Formal conclusion: union_prob weights samples events <= 1.
   Hypotheses: Requires mass normalized to one; nonnegative outcome weights;
   enumerated-list membership where shown in the statement; all other
   constraints remain explicit.
   Proof outline: application of already-proved lemmas, Stdlib Lra linear
   arithmetic; notably arbitrary_union_at_most_total_mass.
   Library discipline: Stdlib.List.existsb, filter, Bool, Sorting.Permutation
   and the shared FiniteSum lemmas.
   Scope: Repeated sample entries contribute repeated weight; no measure axiom,
   independence or distributional model is imported.
   *)
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

  (**
   [arbitrary_union_nonnegative] (theorem).
   Meaning: Controls union/intersection mass for Boolean events through finite
   probability algebra.
   Formal conclusion: 0 <= union_prob weights samples events.
   Hypotheses: Requires nonnegative outcome weights; enumerated-list membership
   where shown in the statement; all other constraints remain explicit.
   Proof outline: application of already-proved lemmas; notably union_prob,
   FiniteSum.finite_sum_nonnegative., Rmult_le_pos..
   Library discipline: Stdlib.List.existsb, filter, Bool, Sorting.Permutation
   and the shared FiniteSum lemmas.
   Scope: Repeated sample entries contribute repeated weight; no measure axiom,
   independence or distributional model is imported.
   *)
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
  (**
   [finite_prob_true] (theorem).
   Meaning: Gives a precise computational or algebraic interpretation of the
   named construction or assertion.
   Formal conclusion: forall weights samples, finite_prob weights samples (fun
   _ => true) = finite_sum weights samples.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: application of already-proved lemmas, ring/field
   normalization; notably finite_prob., finite_sum_extensional.
   Library discipline: Stdlib.List.existsb, filter, Bool, Sorting.Permutation
   and the shared FiniteSum lemmas.
   Scope: Repeated sample entries contribute repeated weight; no measure axiom,
   independence or distributional model is imported.
   *)
  Theorem finite_prob_true :
    forall weights samples,
      finite_prob weights samples (fun _ => true) =
        finite_sum weights samples.
  Proof.
    intros weights samples.
    unfold finite_prob.
    apply finite_sum_extensional; intro x; simpl; ring.
  Qed.

  (**
   [finite_prob_false] (theorem).
   Meaning: Gives a precise computational or algebraic interpretation of the
   named construction or assertion.
   Formal conclusion: forall weights samples, finite_prob weights samples (fun
   _ => false) = 0.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: application of already-proved lemmas, ring/field
   normalization; notably finite_prob., finite_sum_extensional,
   FiniteSum.finite_sum_zero..
   Library discipline: Stdlib.List.existsb, filter, Bool, Sorting.Permutation
   and the shared FiniteSum lemmas.
   Scope: Repeated sample entries contribute repeated weight; no measure axiom,
   independence or distributional model is imported.
   *)
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
  (**
   [finite_prob_zero_iff_no_positive_mass_support] (theorem).
   Meaning: Gives a precise computational or algebraic interpretation of the
   named construction or assertion.
   Formal conclusion: forall weights samples e, (forall x, In x samples -> 0 <=
   weights x) -> (finite_prob weights samples e = 0 <-> forall x, In x samples
   -> e x = true -> weights x = 0).
   Hypotheses: Requires nonnegative outcome weights; enumerated-list membership
   where shown in the statement; all other constraints remain explicit.
   Proof outline: equational rewriting, application of already-proved lemmas,
   explicit case analysis, Stdlib Psatz nonlinear arithmetic, ring/field
   normalization; notably finite_prob, Rmult_le_pos., indicator_nonnegative..
   Library discipline: Stdlib.List.existsb, filter, Bool, Sorting.Permutation
   and the shared FiniteSum lemmas.
   Scope: Repeated sample entries contribute repeated weight; no measure axiom,
   independence or distributional model is imported.
   *)
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
      change (weights x * indicator (e x) = 0) in Hterm.
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

  (**
   [finite_prob_positive_of_positive_support] (theorem).
   Meaning: Gives a precise computational or algebraic interpretation of the
   named construction or assertion.
   Formal conclusion: 0 < finite_prob weights samples e.
   Hypotheses: Requires nonnegative outcome weights; explicit
   nonzero/strict-positive denominator or scale; enumerated-list membership
   where shown in the statement; all other constraints remain explicit.
   Proof outline: equational rewriting, application of already-proved lemmas,
   Stdlib Lra linear arithmetic; notably finite_prob, Rmult_le_pos.,
   indicator_nonnegative..
   Library discipline: Stdlib.List.existsb, filter, Bool, Sorting.Permutation
   and the shared FiniteSum lemmas.
   Scope: Repeated sample entries contribute repeated weight; no measure axiom,
   independence or distributional model is imported.
   *)
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
    change (weights x * indicator (e x) <=
      FiniteSum.finite_sum
        (fun y => weights y * indicator (e y)) samples)
      in Hbound.
    rewrite He in Hbound.
    simpl in Hbound.
    lra.
  Qed.

  (* A Boolean event restricts the sample list using the standard
     List.filter operation. This equivalence is valid for arbitrary real
     weights; normalization and positivity are not needed for equality. *)
  (**
   [finite_prob_as_filtered_mass] (theorem).
   Meaning: Gives a precise computational or algebraic interpretation of the
   named construction or assertion.
   Formal conclusion: forall weights samples e, finite_prob weights samples e =
   FiniteSum.finite_sum weights (filter e samples).
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: equational rewriting, application of already-proved lemmas,
   explicit case analysis, ring/field normalization; notably finite_prob,
   FiniteSum.finite_sum_filter., FiniteSum.finite_sum_ext.
   Library discipline: Stdlib.List.existsb, filter, Bool, Sorting.Permutation
   and the shared FiniteSum lemmas.
   Scope: Repeated sample entries contribute repeated weight; no measure axiom,
   independence or distributional model is imported.
   *)
  Theorem finite_prob_as_filtered_mass :
    forall weights samples e,
      finite_prob weights samples e =
        FiniteSum.finite_sum weights (filter e samples).
  Proof.
    intros weights samples e.
    unfold finite_prob, finite_sum.
    rewrite FiniteSum.finite_sum_filter.
    apply FiniteSum.finite_sum_ext; intro x.
    destruct (e x); unfold indicator; simpl; ring.
  Qed.

  (* Two event predicates only need to agree on enumerated outcomes.
     Their values outside the finite sample have no bearing on mass. *)
  (**
   [finite_prob_event_ext_on_samples] (theorem).
   Meaning: Relates explicit finite outcomes and weights to the corresponding
   marginal or joint quantity.
   Formal conclusion: finite_prob weights samples e = finite_prob weights
   samples f.
   Hypotheses: Requires enumerated-list membership where shown in the
   statement; all other constraints remain explicit.
   Proof outline: equational rewriting, application of already-proved lemmas,
   definitional computation; notably finite_prob, FiniteSum.finite_sum_ext_in..
   Library discipline: Stdlib.List.existsb, filter, Bool, Sorting.Permutation
   and the shared FiniteSum lemmas.
   Scope: Repeated sample entries contribute repeated weight; no measure axiom,
   independence or distributional model is imported.
   *)
  Theorem finite_prob_event_ext_on_samples :
    forall weights samples e f,
      (forall x, In x samples -> e x = f x) ->
      finite_prob weights samples e =
        finite_prob weights samples f.
  Proof.
    intros weights samples e f Heq.
    unfold finite_prob, finite_sum.
    apply FiniteSum.finite_sum_ext_in.
    intros x Hin.
    rewrite (Heq x Hin).
    reflexivity.
  Qed.

  (**
   [finite_prob_sample_append] (theorem).
   Meaning: Proves a structural list identity using Rocq's standard list
   operations.
   Formal conclusion: forall weights left right e, finite_prob weights (left ++
   right) e = finite_prob weights left e + finite_prob weights right e.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: application of already-proved lemmas; notably finite_prob,
   FiniteSum.finite_sum_app..
   Library discipline: Stdlib.List.existsb, filter, Bool, Sorting.Permutation
   and the shared FiniteSum lemmas.
   Scope: Repeated sample entries contribute repeated weight; no measure axiom,
   independence or distributional model is imported.
   *)
  Theorem finite_prob_sample_append :
    forall weights left right e,
      finite_prob weights (left ++ right) e =
        finite_prob weights left e + finite_prob weights right e.
  Proof.
    intros weights left right e.
    unfold finite_prob, finite_sum.
    apply FiniteSum.finite_sum_app.
  Qed.

  (**
   [finite_prob_sample_permutation] (theorem).
   Meaning: Proves a structural list identity using Rocq's standard list
   operations.
   Formal conclusion: finite_prob weights left e = finite_prob weights right e.
   Hypotheses: Requires Stdlib list-permutation premise where shown in the
   statement; all other constraints remain explicit.
   Proof outline: application of already-proved lemmas; notably finite_prob,
   FiniteSum.finite_sum_permutation.
   Library discipline: Stdlib.List.existsb, filter, Bool, Sorting.Permutation
   and the shared FiniteSum lemmas.
   Scope: Repeated sample entries contribute repeated weight; no measure axiom,
   independence or distributional model is imported.
   *)
  Theorem finite_prob_sample_permutation :
    forall weights left right e,
      Permutation left right ->
      finite_prob weights left e = finite_prob weights right e.
  Proof.
    intros weights left right e Hperm.
    unfold finite_prob, finite_sum.
    apply FiniteSum.finite_sum_permutation; exact Hperm.
  Qed.

  (**
   [union_prob_sample_permutation] (theorem).
   Meaning: Controls union/intersection mass for Boolean events through finite
   probability algebra.
   Formal conclusion: union_prob weights left events = union_prob weights right
   events.
   Hypotheses: Requires Stdlib list-permutation premise where shown in the
   statement; all other constraints remain explicit.
   Proof outline: application of already-proved lemmas; notably union_prob.,
   finite_prob_sample_permutation.
   Library discipline: Stdlib.List.existsb, filter, Bool, Sorting.Permutation
   and the shared FiniteSum lemmas.
   Scope: Repeated sample entries contribute repeated weight; no measure axiom,
   independence or distributional model is imported.
   *)
  Theorem union_prob_sample_permutation :
    forall weights left right events,
      Permutation left right ->
      union_prob weights left events = union_prob weights right events.
  Proof.
    intros weights left right events Hperm.
    unfold union_prob.
    apply finite_prob_sample_permutation; exact Hperm.
  Qed.

  (**
   [sum_marginal_probs_event_permutation] (theorem).
   Meaning: Establishes finite-sum or finite-expectation algebra while
   retaining the original sum semantics.
   Formal conclusion: sum_marginal_probs weights samples left =
   sum_marginal_probs weights samples right.
   Hypotheses: Requires Stdlib list-permutation premise where shown in the
   statement; all other constraints remain explicit.
   Proof outline: application of already-proved lemmas; notably
   sum_marginal_probs., FiniteSum.finite_sum_permutation.
   Library discipline: Stdlib.List.existsb, filter, Bool, Sorting.Permutation
   and the shared FiniteSum lemmas.
   Scope: Repeated sample entries contribute repeated weight; no measure axiom,
   independence or distributional model is imported.
   *)
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

  (**
   [finite_prob_event_monotone] (theorem).
   Meaning: Gives a precise computational or algebraic interpretation of the
   named construction or assertion.
   Formal conclusion: finite_prob weights samples e <= finite_prob weights
   samples f.
   Hypotheses: Requires nonnegative outcome weights; enumerated-list membership
   where shown in the statement; all other constraints remain explicit.
   Proof outline: application of already-proved lemmas, Stdlib Psatz nonlinear
   arithmetic; notably finite_prob., finite_sum_monotone.,
   indicator_implication_bound.
   Library discipline: Stdlib.List.existsb, filter, Bool, Sorting.Permutation
   and the shared FiniteSum lemmas.
   Scope: Repeated sample entries contribute repeated weight; no measure axiom,
   independence or distributional model is imported.
   *)
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

  (**
   [normalized_finite_prob_unit_interval] (theorem).
   Meaning: Gives a precise computational or algebraic interpretation of the
   named construction or assertion.
   Formal conclusion: 0 <= finite_prob weights samples e /\ finite_prob weights
   samples e <= 1.
   Hypotheses: Requires mass normalized to one; nonnegative outcome weights;
   enumerated-list membership where shown in the statement; all other
   constraints remain explicit.
   Proof outline: application of already-proved lemmas, Stdlib Lra linear
   arithmetic, Stdlib Psatz nonlinear arithmetic; notably finite_prob.,
   FiniteSum.finite_sum_nonnegative., Rmult_le_pos..
   Library discipline: Stdlib.List.existsb, filter, Bool, Sorting.Permutation
   and the shared FiniteSum lemmas.
   Scope: Repeated sample entries contribute repeated weight; no measure axiom,
   independence or distributional model is imported.
   *)
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

  (**
   [empty_family_probability_zero] (theorem).
   Meaning: Gives a precise computational or algebraic interpretation of the
   named construction or assertion.
   Formal conclusion: forall weights samples, union_prob weights samples [] =
   0.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: application of already-proved lemmas; notably
   finite_prob_false..
   Library discipline: Stdlib.List.existsb, filter, Bool, Sorting.Permutation
   and the shared FiniteSum lemmas.
   Scope: Repeated sample entries contribute repeated weight; no measure axiom,
   independence or distributional model is imported.
   *)
  Theorem empty_family_probability_zero :
    forall weights samples, union_prob weights samples [] = 0.
  Proof.
    intros weights samples.
    change (finite_prob weights samples (fun _ => false) = 0).
    apply finite_prob_false.
  Qed.

  (**
   [singleton_family_probability] (theorem).
   Meaning: Gives a precise computational or algebraic interpretation of the
   named construction or assertion.
   Formal conclusion: forall weights samples e, union_prob weights samples [e]
   = finite_prob weights samples e.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: equational rewriting, application of already-proved lemmas,
   definitional computation; notably union_prob, finite_sum_extensional,
   any_event.
   Library discipline: Stdlib.List.existsb, filter, Bool, Sorting.Permutation
   and the shared FiniteSum lemmas.
   Scope: Repeated sample entries contribute repeated weight; no measure axiom,
   independence or distributional model is imported.
   *)
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

  (**
   [union_prob_membership_extensional] (theorem).
   Meaning: Controls union/intersection mass for Boolean events through finite
   probability algebra.
   Formal conclusion: union_prob weights samples left = union_prob weights
   samples right.
   Hypotheses: Requires enumerated-list membership where shown in the
   statement; all other constraints remain explicit.
   Proof outline: equational rewriting, application of already-proved lemmas,
   explicit case analysis, definitional computation; notably union_prob,
   finite_sum_extensional, any_event.
   Library discipline: Stdlib.List.existsb, filter, Bool, Sorting.Permutation
   and the shared FiniteSum lemmas.
   Scope: Repeated sample entries contribute repeated weight; no measure axiom,
   independence or distributional model is imported.
   *)
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

  (**
   [union_prob_permutation_invariant] (theorem).
   Meaning: Controls union/intersection mass for Boolean events through finite
   probability algebra.
   Formal conclusion: union_prob weights samples left = union_prob weights
   samples right.
   Hypotheses: Requires Stdlib list-permutation premise where shown in the
   statement; all other constraints remain explicit.
   Proof outline: application of already-proved lemmas; notably
   union_prob_membership_extensional., Permutation_sym.
   Library discipline: Stdlib.List.existsb, filter, Bool, Sorting.Permutation
   and the shared FiniteSum lemmas.
   Scope: Repeated sample entries contribute repeated weight; no measure axiom,
   independence or distributional model is imported.
   *)
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

  (**
   [union_prob_duplicate_route] (theorem).
   Meaning: Controls union/intersection mass for Boolean events through finite
   probability algebra.
   Formal conclusion: forall weights samples e events, union_prob weights
   samples (e :: e :: events) = union_prob weights samples (e :: events).
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: application of already-proved lemmas; notably
   union_prob_membership_extensional..
   Library discipline: Stdlib.List.existsb, filter, Bool, Sorting.Permutation
   and the shared FiniteSum lemmas.
   Scope: Repeated sample entries contribute repeated weight; no measure axiom,
   independence or distributional model is imported.
   *)
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

  (**
   [indicator_complement] (lemma).
   Meaning: Gives a precise computational or algebraic interpretation of the
   named construction or assertion.
   Formal conclusion: forall b, indicator (negb b) + indicator b = 1.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: ring/field normalization.
   Library discipline: Stdlib.List.existsb, filter, Bool, Sorting.Permutation
   and the shared FiniteSum lemmas.
   Scope: Repeated sample entries contribute repeated weight; no measure axiom,
   independence or distributional model is imported.
   *)
  Lemma indicator_complement :
    forall b, indicator (negb b) + indicator b = 1.
  Proof.
    intros []; simpl; ring.
  Qed.

  (**
   [finite_prob_complement] (theorem).
   Meaning: Gives a precise computational or algebraic interpretation of the
   named construction or assertion.
   Formal conclusion: forall weights samples e, finite_prob weights samples
   (fun x => negb (e x)) + finite_prob weights samples e = finite_sum weights
   samples.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: equational rewriting, application of already-proved lemmas,
   ring/field normalization; notably finite_prob., finite_sum_extensional,
   indicator_complement..
   Library discipline: Stdlib.List.existsb, filter, Bool, Sorting.Permutation
   and the shared FiniteSum lemmas.
   Scope: Repeated sample entries contribute repeated weight; no measure axiom,
   independence or distributional model is imported.
   *)
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

  (**
   [normalized_finite_prob_complement] (theorem).
   Meaning: Gives a precise computational or algebraic interpretation of the
   named construction or assertion.
   Formal conclusion: finite_prob weights samples (fun x => negb (e x)) = 1 -
   finite_prob weights samples e.
   Hypotheses: Requires mass normalized to one where shown in the statement;
   all other constraints remain explicit.
   Proof outline: equational rewriting, application of already-proved lemmas,
   Stdlib Lra linear arithmetic; notably finite_prob_complement.
   Library discipline: Stdlib.List.existsb, filter, Bool, Sorting.Permutation
   and the shared FiniteSum lemmas.
   Scope: Repeated sample entries contribute repeated weight; no measure axiom,
   independence or distributional model is imported.
   *)
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

  (**
   [indicator_union_intersection] (lemma).
   Meaning: Controls union/intersection mass for Boolean events through finite
   probability algebra.
   Formal conclusion: forall b c, indicator (orb b c) + indicator (andb b c) =
   indicator b + indicator c.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: ring/field normalization.
   Library discipline: Stdlib.List.existsb, filter, Bool, Sorting.Permutation
   and the shared FiniteSum lemmas.
   Scope: Repeated sample entries contribute repeated weight; no measure axiom,
   independence or distributional model is imported.
   *)
  Lemma indicator_union_intersection :
    forall b c,
      indicator (orb b c) + indicator (andb b c) =
        indicator b + indicator c.
  Proof.
    intros [] []; simpl; ring.
  Qed.

  (**
   [finite_prob_inclusion_exclusion] (theorem).
   Meaning: Gives a precise computational or algebraic interpretation of the
   named construction or assertion.
   Formal conclusion: forall weights samples e f, finite_prob weights samples
   (fun x => orb (e x) (f x)) + finite_prob weights samples (fun x => andb (e
   x) (f x)) = finite_prob weights samples e + finite_prob weights samples f.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: equational rewriting, application of already-proved lemmas,
   ring/field normalization; notably finite_prob., finite_sum_extensional,
   indicator_union_intersection..
   Library discipline: Stdlib.List.existsb, filter, Bool, Sorting.Permutation
   and the shared FiniteSum lemmas.
   Scope: Repeated sample entries contribute repeated weight; no measure axiom,
   independence or distributional model is imported.
   *)
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

  (**
   [two_event_union_probability] (theorem).
   Meaning: Controls union/intersection mass for Boolean events through finite
   probability algebra.
   Formal conclusion: forall weights samples e f, union_prob weights samples
   [e; f] = finite_prob weights samples (fun x => orb (e x) (f x)).
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: equational rewriting, application of already-proved lemmas,
   definitional computation; notably union_prob, finite_sum_extensional,
   any_event.
   Library discipline: Stdlib.List.existsb, filter, Bool, Sorting.Permutation
   and the shared FiniteSum lemmas.
   Scope: Repeated sample entries contribute repeated weight; no measure axiom,
   independence or distributional model is imported.
   *)
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

  (**
   [two_event_union_inclusion_exclusion] (theorem).
   Meaning: Controls union/intersection mass for Boolean events through finite
   probability algebra.
   Formal conclusion: forall weights samples e f, union_prob weights samples
   [e; f] + finite_prob weights samples (fun x => andb (e x) (f x)) =
   finite_prob weights samples e + finite_prob weights samples f.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: equational rewriting, application of already-proved lemmas;
   notably two_event_union_probability., finite_prob_inclusion_exclusion..
   Library discipline: Stdlib.List.existsb, filter, Bool, Sorting.Permutation
   and the shared FiniteSum lemmas.
   Scope: Repeated sample entries contribute repeated weight; no measure axiom,
   independence or distributional model is imported.
   *)
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

  (**
   [any_event_append] (lemma).
   Meaning: Proves a structural list identity using Rocq's standard list
   operations.
   Formal conclusion: forall left right x, any_event (left ++ right) x = orb
   (any_event left x) (any_event right x).
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: equational rewriting, definitional computation; notably
   any_event., existsb_app..
   Library discipline: Stdlib.List.existsb, filter, Bool, Sorting.Permutation
   and the shared FiniteSum lemmas.
   Scope: Repeated sample entries contribute repeated weight; no measure axiom,
   independence or distributional model is imported.
   *)
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

  (**
   [union_prob_append] (theorem).
   Meaning: Controls union/intersection mass for Boolean events through finite
   probability algebra.
   Formal conclusion: forall weights samples left right, union_prob weights
   samples (left ++ right) = finite_prob weights samples (fun x => orb
   (any_event left x) (any_event right x)).
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: equational rewriting, application of already-proved lemmas,
   definitional computation; notably union_prob, finite_sum_extensional,
   any_event_append..
   Library discipline: Stdlib.List.existsb, filter, Bool, Sorting.Permutation
   and the shared FiniteSum lemmas.
   Scope: Repeated sample entries contribute repeated weight; no measure axiom,
   independence or distributional model is imported.
   *)
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

  (**
   [sum_marginal_probs_append] (theorem).
   Meaning: Establishes finite-sum or finite-expectation algebra while
   retaining the original sum semantics.
   Formal conclusion: forall weights samples left right, sum_marginal_probs
   weights samples (left ++ right) = sum_marginal_probs weights samples left +
   sum_marginal_probs weights samples right.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: application of already-proved lemmas; notably
   FiniteSum.finite_sum_app..
   Library discipline: Stdlib.List.existsb, filter, Bool, Sorting.Permutation
   and the shared FiniteSum lemmas.
   Scope: Repeated sample entries contribute repeated weight; no measure axiom,
   independence or distributional model is imported.
   *)
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

  (* Frechet bounds follow from the generic monotone event mass and
     inclusion-exclusion laws; the specialized four-cell calculation in
     Admissions need not be repeated here. *)
  (**
   [finite_intersection_at_most_first] (theorem).
   Meaning: Controls union/intersection mass for Boolean events through finite
   probability algebra.
   Formal conclusion: finite_prob weights samples (fun x => andb (e x) (f x))
   <= finite_prob weights samples e.
   Hypotheses: Requires nonnegative outcome weights; enumerated-list membership
   where shown in the statement; all other constraints remain explicit.
   Proof outline: application of already-proved lemmas; notably
   finite_prob_event_monotone., andb_true_iff.
   Library discipline: Stdlib.List.existsb, filter, Bool, Sorting.Permutation
   and the shared FiniteSum lemmas.
   Scope: Repeated sample entries contribute repeated weight; no measure axiom,
   independence or distributional model is imported.
   *)
  Theorem finite_intersection_at_most_first :
    forall weights samples e f,
      (forall x, In x samples -> 0 <= weights x) ->
      finite_prob weights samples
        (fun x => andb (e x) (f x)) <= finite_prob weights samples e.
  Proof.
    intros weights samples e f Hw.
    apply finite_prob_event_monotone.
    - exact Hw.
    - intros x Hx Hboth.
      apply andb_true_iff in Hboth.
      exact (proj1 Hboth).
  Qed.

  (**
   [finite_intersection_at_most_second] (theorem).
   Meaning: Controls union/intersection mass for Boolean events through finite
   probability algebra.
   Formal conclusion: finite_prob weights samples (fun x => andb (e x) (f x))
   <= finite_prob weights samples f.
   Hypotheses: Requires nonnegative outcome weights; enumerated-list membership
   where shown in the statement; all other constraints remain explicit.
   Proof outline: application of already-proved lemmas; notably
   finite_prob_event_monotone., andb_true_iff.
   Library discipline: Stdlib.List.existsb, filter, Bool, Sorting.Permutation
   and the shared FiniteSum lemmas.
   Scope: Repeated sample entries contribute repeated weight; no measure axiom,
   independence or distributional model is imported.
   *)
  Theorem finite_intersection_at_most_second :
    forall weights samples e f,
      (forall x, In x samples -> 0 <= weights x) ->
      finite_prob weights samples
        (fun x => andb (e x) (f x)) <= finite_prob weights samples f.
  Proof.
    intros weights samples e f Hw.
    apply finite_prob_event_monotone.
    - exact Hw.
    - intros x Hx Hboth.
      apply andb_true_iff in Hboth.
      exact (proj2 Hboth).
  Qed.

  (**
   [finite_frechet_lower_bound] (theorem).
   Meaning: Controls union/intersection mass for Boolean events through finite
   probability algebra.
   Formal conclusion: finite_prob weights samples e + finite_prob weights
   samples f - 1 <= finite_prob weights samples (fun x => andb (e x) (f x)).
   Hypotheses: Requires mass normalized to one; nonnegative outcome weights;
   enumerated-list membership where shown in the statement; all other
   constraints remain explicit.
   Proof outline: application of already-proved lemmas, Stdlib Lra linear
   arithmetic; notably finite_prob_inclusion_exclusion,
   normalized_finite_prob_unit_interval.
   Library discipline: Stdlib.List.existsb, filter, Bool, Sorting.Permutation
   and the shared FiniteSum lemmas.
   Scope: Repeated sample entries contribute repeated weight; no measure axiom,
   independence or distributional model is imported.
   *)
  Theorem finite_frechet_lower_bound :
    forall weights samples e f,
      (forall x, In x samples -> 0 <= weights x) ->
      finite_sum weights samples = 1 ->
      finite_prob weights samples e + finite_prob weights samples f - 1 <=
        finite_prob weights samples (fun x => andb (e x) (f x)).
  Proof.
    intros weights samples e f Hw Hmass.
    pose proof (finite_prob_inclusion_exclusion weights samples e f)
      as Hinclusion.
    pose proof (normalized_finite_prob_unit_interval
      weights samples (fun x => orb (e x) (f x)) Hw Hmass)
      as [_ Hunion].
    lra.
  Qed.

End FiniteOutcomeSpace.

(* The inequalities remain valid for a list with repeated sample points;
   normalized probabilities should be interpreted with the corresponding
   weighted-multiset convention. In applications with distinct outcomes,
   one normally uses a finite enumeration without duplicates. *)
