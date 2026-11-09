(** Module: FiniteUnion.v
   Purpose: Distribution-free union probability for finitely many Boolean events.
   Defines Boolean-event masses, unions and conditional ratios, then proves monotonicity, filtering, inclusion-exclusion, Fréchet and union bounds.
   Mathematical representation: Outcomes are enumerated in a list; Boolean events are functions on outcomes and probability sums use FiniteSum.finite_sum.
   Explicit hypotheses: Bounds use nonnegative outcome weights; unit upper bounds additionally require mass normalization; raw identities need neither.
   Library use: Stdlib.List.existsb, forallb, map, fold_right, filter, Bool, Sorting.Permutation and the shared FiniteSum lemmas.
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
   [Event] (definition) — Finite Boolean event mass and union/intersection
   inequalities.
   Mathematical meaning: An event is a total decidable predicate on an outcome:
   true means membership and false means nonmembership. No
   specialized event-set data structure is introduced.
   Exact declaration: Definition Event := Outcome -> bool.
   Premises and side conditions: The outcome type is arbitrary; this is a Boolean function,
   not a sigma-algebra, finite sample enumeration or normalized
   probability measure.
   Proof/definition method: The alias is Outcome -> bool. Union, intersection
   and event membership later use Rocq's standard Bool and List
   functions instead of custom event-set implementations.
   Library reuse: Stdlib.List (existsb/filter), Bool, Sorting.Permutation and
   FiniteSum.
   Boundary: Finite list semantics; duplicates contribute repeatedly. Probabilistic
   bounds need explicit nonnegative weights and possibly normalization.
   *)
  Definition Event := Outcome -> bool.

  (**
   [indicator] (definition) — Finite Boolean event mass and union/intersection
   inequalities.
   Mathematical meaning: The exact 0-1 real indicator associated with Boolean
   event membership; it turns Boolean predicates into terms in
   the shared real-valued finite-sum algebra.
   Exact declaration: Definition indicator (b : bool) : R := if b then 1 else 0.
   Premises and side conditions: No probability, weight sign or normalization hypothesis
   is required for this Boolean-to-real conversion.
   Proof/definition method: Uses if b then 1 else 0; positivity,
   complement and conjunction properties are proved separately
   with Bool case distinctions and Stdlib.Reals operations.
   Library reuse: Stdlib.List (existsb/filter), Bool, Sorting.Permutation and
   FiniteSum.
   Boundary: Finite list semantics; duplicates contribute repeatedly. Probabilistic
   bounds need explicit nonnegative weights and possibly normalization.
   *)
  Definition indicator (b : bool) : R := if b then 1 else 0.

  (* Stdlib.List.existsb is the finite Boolean OR over event membership;
     no project-specific Boolean recursion is required. *)
  (**
   [any_event] (definition) — Finite Boolean event mass and union/intersection
   inequalities.
   Mathematical meaning: The union predicate for a finite list of events,
   true if some listed event accepts the outcome. The empty
   list denotes the false event.
   Exact declaration: Definition any_event (events : list Event) (x : Outcome) : bool
   := existsb (fun e => e x) events.
   Premises and side conditions: Event-list entries may repeat; repetition does not change
   the union truth value, although it changes sums of marginal
   masses. No independence assumption is present.
   Proof/definition method: Stdlib.List.existsb applies each event to the
   same outcome, avoiding custom recursive event or set logic.
   Library reuse: Stdlib.List (existsb/filter), Bool, Sorting.Permutation and
   FiniteSum.
   Boundary: Finite list semantics; duplicates contribute repeatedly. Probabilistic
   bounds need explicit nonnegative weights and possibly normalization.
   *)
  Definition any_event (events : list Event) (x : Outcome) : bool :=
    existsb (fun e => e x) events.

  (* Count event indicators using the standard list fold. *)
  (**
   [sum_event_indicators] (definition) — Finite Boolean event mass and
   union/intersection inequalities.
   Mathematical meaning: Counts, as a real, how many listed events hold at
   an outcome. Overlap or duplicated events each contribute
   another indicator, so the result need not be at most one.
   Exact declaration: Definition sum_event_indicators (events : list Event) (x :
   Outcome) : R := FiniteSum.finite_sum (fun e => indicator (e x)) events.
   Premises and side conditions: Only finite event-list membership is needed. Events
   may overlap or be repeated; no normalized probability model
   is required for this counting expression.
   Proof/definition method: Reuses FiniteSum.finite_sum of the existing
   indicator functions, built from Stdlib.List.map/fold_right.
   Library reuse: Stdlib.List (existsb/filter), Bool, Sorting.Permutation and
   FiniteSum.
   Boundary: Finite list semantics; duplicates contribute repeatedly. Probabilistic
   bounds need explicit nonnegative weights and possibly normalization.
   *)
  Definition sum_event_indicators (events : list Event)
    (x : Outcome) : R :=
    FiniteSum.finite_sum (fun e => indicator (e x)) events.

  (* Retain the original public name as a transparent wrapper around
     the same shared finite-sum implementation used in FiniteMoments. *)
  (**
   [finite_sum] (definition) — Finite Boolean event mass and union/intersection
   inequalities.
   Mathematical meaning: An outcome-specialized alias of the generic
   finite_sum from FiniteSum.v, preserving multiplicities and
   real-valued integrands without another fold implementation.
   Exact declaration: Definition finite_sum (f : Outcome -> R) (xs : list Outcome) :
   R := FiniteSum.finite_sum f xs.
   Premises and side conditions: The sample list may repeat outcomes and the
   integrand can have any real sign. This is a list fold, not
   a probability construction in itself.
   Proof/definition method: Directly delegates to FiniteSum.finite_sum,
   which already has checked addition, scaling, extensionality
   and permutation theorems.
   Library reuse: Stdlib.List (existsb/filter), Bool, Sorting.Permutation and
   FiniteSum.
   Boundary: Finite list semantics; duplicates contribute repeatedly. Probabilistic
   bounds need explicit nonnegative weights and possibly normalization.
   *)
  Definition finite_sum (f : Outcome -> R) (xs : list Outcome) : R :=
    FiniteSum.finite_sum f xs.

  (**
   [finite_prob] (definition) — Finite Boolean event mass and union/intersection
   inequalities.
   Mathematical meaning: Computes the event's weighted mass as the sum of
   weights(x) times its Boolean 0-1 indicator over every sample
   list occurrence, retaining duplicate contributions.
   Exact declaration: Definition finite_prob (weights : Outcome -> R) (samples : list
   Outcome) (event : Event) : R := finite_sum (fun x => weights x * indicator (event
   x)) samples.
   Premises and side conditions: Arbitrary real weights are accepted syntactically.
   A genuine probability interpretation requires nonnegative
   sample weights and appropriate total-mass normalization;
   subsequent probability inequalities state those assumptions.
   Proof/definition method: Uses the shared finite_sum and indicator,
   not a separate probability recursion or an assumed measure.
   Library reuse: Stdlib.List (existsb/filter), Bool, Sorting.Permutation and
   FiniteSum.
   Boundary: Finite list semantics; duplicates contribute repeatedly. Probabilistic
   bounds need explicit nonnegative weights and possibly normalization.
   *)
  Definition finite_prob (weights : Outcome -> R)
    (samples : list Outcome) (event : Event) : R :=
      finite_sum (fun x => weights x * indicator (event x)) samples.

  (* The same list fold computes the marginal union-bound total. *)
  (**
   [sum_marginal_probs] (definition) — Finite Boolean event mass and
   union/intersection inequalities.
   Mathematical meaning: Adds event masses across the listed family,
   counting overlaps and duplicate event entries separately.
   Unlike union_prob, this quantity can exceed total mass.
   Exact declaration: Definition sum_marginal_probs (weights : Outcome -> R) (samples
   : list Outcome) (events : list Event) : R := FiniteSum.finite_sum (finite_prob
   weights samples) events.
   Premises and side conditions: Finite event families are allowed to overlap;
   neither disjointness nor independence, signs or total mass
   are assumed by the definition.
   Proof/definition method: Maps each event to its previously defined
   finite_prob and sums via FiniteSum.finite_sum.
   Library reuse: Stdlib.List (existsb/filter), Bool, Sorting.Permutation and
   FiniteSum.
   Boundary: Finite list semantics; duplicates contribute repeatedly. Probabilistic
   bounds need explicit nonnegative weights and possibly normalization.
   *)
  Definition sum_marginal_probs
    (weights : Outcome -> R) (samples : list Outcome)
    (events : list Event) : R :=
    FiniteSum.finite_sum (finite_prob weights samples) events.

  (**
   [union_prob] (definition) — Finite Boolean event mass and union/intersection
   inequalities.
   Mathematical meaning: Mass of the union of a finite event family:
   each outcome-list occurrence is included once when at least
   one event accepts it, regardless of how many events do.
   Exact declaration: Definition union_prob (weights : Outcome -> R) (samples : list
   Outcome) (events : list Event) : R := finite_prob weights samples (any_event
   events).
   Premises and side conditions: Outcome and event lists may include repeated elements.
   Nonnegative weights and normalized total mass must be
   stated separately for probability-specific bounds.
   Proof/definition method: Computes finite_prob with the any_event
   predicate built from Stdlib.List.existsb; no new event
   recursion or inclusion-exclusion formula is embedded.
   Library reuse: Stdlib.List (existsb/filter), Bool, Sorting.Permutation and
   FiniteSum.
   Boundary: Finite list semantics; duplicates contribute repeatedly. Probabilistic
   bounds need explicit nonnegative weights and possibly normalization.
   *)
  Definition union_prob (weights : Outcome -> R)
    (samples : list Outcome) (events : list Event) : R :=
    finite_prob weights samples (any_event events).

  (**
   [indicator_nonnegative] (lemma) — Finite Boolean event mass and union/intersection
   inequalities.
   Mathematical meaning: Expresses a checked identity or bound within the finite
   boolean event mass and union/intersection inequalities.
   Exact checked proposition: Lemma indicator_nonnegative : forall b, 0 <= indicator
   b.
   Premises and side conditions: The displayed hypotheses include explicit nonzero or
   strict-positive numerical conditions. No further assumptions are implicit.
   Proof/definition method: Kernel proof uses linear real arithmetic (Lra);
   references include indicator.
   Library reuse: Stdlib.List (existsb/filter), Bool, Sorting.Permutation and
   FiniteSum.
   Boundary: Finite list semantics; duplicates contribute repeatedly. Probabilistic
   bounds need explicit nonnegative weights and possibly normalization.
   *)
  Lemma indicator_nonnegative :
    forall b, 0 <= indicator b.
  Proof.
    intros []; unfold indicator; lra.
  Qed.

  (**
   [indicator_at_most_one] (lemma) — Finite Boolean event mass and union/intersection
   inequalities.
   Mathematical meaning: Expresses a checked identity or bound within the finite
   boolean event mass and union/intersection inequalities.
   Exact checked proposition: Lemma indicator_at_most_one : forall b, indicator b <=
   1.
   Premises and side conditions: All required premises are written in the signature.
   No independence or distributional assumption is silently supplied.
   Proof/definition method: Kernel proof uses linear real arithmetic (Lra);
   references include indicator.
   Library reuse: Stdlib.List (existsb/filter), Bool, Sorting.Permutation and
   FiniteSum.
   Boundary: Finite list semantics; duplicates contribute repeatedly. Probabilistic
   bounds need explicit nonnegative weights and possibly normalization.
   *)
  Lemma indicator_at_most_one :
    forall b, indicator b <= 1.
  Proof.
    intros []; unfold indicator; lra.
  Qed.

  (**
   [sum_indicators_nonnegative] (lemma) — Finite Boolean event mass and
   union/intersection inequalities.
   Mathematical meaning: Derives a sum or expectation identity for the explicitly
   enumerated terms.
   Exact checked proposition: Lemma sum_indicators_nonnegative : forall events x, 0
   <= sum_event_indicators events x.
   Premises and side conditions: The displayed hypotheses include explicit nonzero or
   strict-positive numerical conditions. No further assumptions are implicit.
   Proof/definition method: Kernel proof uses reuse of previously established lemmas;
   references include FiniteSum.finite_sum_nonnegative., indicator_nonnegative..
   Library reuse: Stdlib.List (existsb/filter), Bool, Sorting.Permutation and
   FiniteSum.
   Boundary: Finite list semantics; duplicates contribute repeatedly. Probabilistic
   bounds need explicit nonnegative weights and possibly normalization.
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
   [union_indicator_bound] (lemma) — Finite Boolean event mass and union/intersection
   inequalities.
   Mathematical meaning: Proves a Boolean-event union/intersection fact or a
   corresponding probability bound.
   Exact checked proposition: Lemma union_indicator_bound : forall events x,
   indicator (any_event events x) <= sum_event_indicators events x.
   Premises and side conditions: All required premises are written in the signature.
   No independence or distributional assumption is silently supplied.
   Proof/definition method: Kernel proof uses structural induction, case analysis,
   rewriting of equalities, reuse of previously established lemmas, definitional
   reduction; references include sum_event_indicators., any_event, existsb_exists.
   Library reuse: Stdlib.List (existsb/filter), Bool, Sorting.Permutation and
   FiniteSum.
   Boundary: Finite list semantics; duplicates contribute repeatedly. Probabilistic
   bounds need explicit nonnegative weights and possibly normalization.
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
   [event_member_implies_union] (lemma) — Finite Boolean event mass and
   union/intersection inequalities.
   Mathematical meaning: Proves a Boolean-event union/intersection fact or a
   corresponding probability bound.
   Exact checked proposition: Lemma event_member_implies_union : forall events e x,
   In e events -> e x = true -> any_event events x = true.
   Premises and side conditions: The displayed hypotheses include sample or list
   membership. No further assumptions are implicit.
   Proof/definition method: Kernel proof uses reuse of previously established lemmas;
   references include any_event., existsb_exists..
   Library reuse: Stdlib.List (existsb/filter), Bool, Sorting.Permutation and
   FiniteSum.
   Boundary: Finite list semantics; duplicates contribute repeatedly. Probabilistic
   bounds need explicit nonnegative weights and possibly normalization.
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
   [indicator_implication_bound] (lemma) — Finite Boolean event mass and
   union/intersection inequalities.
   Mathematical meaning: Expresses a checked identity or bound within the finite
   boolean event mass and union/intersection inequalities.
   Exact checked proposition: Lemma indicator_implication_bound : forall b c, (b =
   true -> c = true) -> indicator b <= indicator c.
   Premises and side conditions: All required premises are written in the signature.
   No independence or distributional assumption is silently supplied.
   Proof/definition method: Kernel proof uses linear real arithmetic (Lra);
   references include indicator.
   Library reuse: Stdlib.List (existsb/filter), Bool, Sorting.Permutation and
   FiniteSum.
   Boundary: Finite list semantics; duplicates contribute repeatedly. Probabilistic
   bounds need explicit nonnegative weights and possibly normalization.
   *)
  Lemma indicator_implication_bound :
    forall b c,
      (b = true -> c = true) ->
      indicator b <= indicator c.
  Proof.
    intros [] [] H; unfold indicator; lra.
  Qed.

  (**
   [finite_sum_monotone] (lemma) — Finite Boolean event mass and union/intersection
   inequalities.
   Mathematical meaning: Derives a sum or expectation identity for the explicitly
   enumerated terms.
   Exact checked proposition: Lemma finite_sum_monotone : forall xs f g, (forall x,
   In x xs -> f x <= g x) -> finite_sum f xs <= finite_sum g xs.
   Premises and side conditions: The displayed hypotheses include sample or list
   membership. No further assumptions are implicit.
   Proof/definition method: Kernel proof uses reuse of previously established lemmas;
   references include FiniteSum.finite_sum_monotone.
   Library reuse: Stdlib.List (existsb/filter), Bool, Sorting.Permutation and
   FiniteSum.
   Boundary: Finite list semantics; duplicates contribute repeatedly. Probabilistic
   bounds need explicit nonnegative weights and possibly normalization.
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
   [finite_sum_extensional] (lemma) — Finite Boolean event mass and
   union/intersection inequalities.
   Mathematical meaning: Derives a sum or expectation identity for the explicitly
   enumerated terms.
   Exact checked proposition: Lemma finite_sum_extensional : forall xs f g, (forall
   x, f x = g x) -> finite_sum f xs = finite_sum g xs.
   Premises and side conditions: All required premises are written in the signature.
   No independence or distributional assumption is silently supplied.
   Proof/definition method: Kernel proof uses reuse of previously established lemmas;
   references include FiniteSum.finite_sum_ext.
   Library reuse: Stdlib.List (existsb/filter), Bool, Sorting.Permutation and
   FiniteSum.
   Boundary: Finite list semantics; duplicates contribute repeatedly. Probabilistic
   bounds need explicit nonnegative weights and possibly normalization.
   *)
  Lemma finite_sum_extensional :
    forall xs f g, (forall x, f x = g x) ->
      finite_sum f xs = finite_sum g xs.
  Proof.
    intros xs f g Heq.
    apply FiniteSum.finite_sum_ext; exact Heq.
  Qed.

  (**
   [finite_sum_addition] (lemma) — Finite Boolean event mass and union/intersection
   inequalities.
   Mathematical meaning: Derives a sum or expectation identity for the explicitly
   enumerated terms.
   Exact checked proposition: Lemma finite_sum_addition : forall xs f g, finite_sum
   (fun x => f x + g x) xs = finite_sum f xs + finite_sum g xs.
   Premises and side conditions: All required premises are written in the signature.
   No independence or distributional assumption is silently supplied.
   Proof/definition method: Kernel proof uses reuse of previously established lemmas;
   references include FiniteSum.finite_sum_add..
   Library reuse: Stdlib.List (existsb/filter), Bool, Sorting.Permutation and
   FiniteSum.
   Boundary: Finite list semantics; duplicates contribute repeatedly. Probabilistic
   bounds need explicit nonnegative weights and possibly normalization.
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
   [interchange_finite_sums] (lemma) — Finite Boolean event mass and
   union/intersection inequalities.
   Mathematical meaning: Derives a sum or expectation identity for the explicitly
   enumerated terms.
   Exact checked proposition: Lemma interchange_finite_sums : forall weights samples
   events, finite_sum (fun x => weights x * sum_event_indicators events x) samples =
   sum_marginal_probs weights samples events.
   Premises and side conditions: All required premises are written in the signature.
   No independence or distributional assumption is silently supplied.
   Proof/definition method: Kernel proof uses rewriting of equalities, reuse of
   previously established lemmas; references include FiniteSum.finite_sum_ext,
   FiniteSum.finite_sum_scale., FiniteSum.finite_sum_swap..
   Library reuse: Stdlib.List (existsb/filter), Bool, Sorting.Permutation and
   FiniteSum.
   Boundary: Finite list semantics; duplicates contribute repeatedly. Probabilistic
   bounds need explicit nonnegative weights and possibly normalization.
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
   [arbitrary_union_bound] (theorem) — Finite Boolean event mass and
   union/intersection inequalities.
   Mathematical meaning: Proves a Boolean-event union/intersection fact or a
   corresponding probability bound.
   Exact checked proposition: Theorem arbitrary_union_bound : forall weights samples
   events, (forall x, In x samples -> 0 <= weights x) -> union_prob weights samples
   events <= sum_marginal_probs weights samples events.
   Premises and side conditions: The displayed hypotheses include nonnegative outcome
   weights; explicit nonzero or strict-positive numerical conditions; sample or list
   membership. No further assumptions are implicit.
   Proof/definition method: Kernel proof uses rewriting of equalities, reuse of
   previously established lemmas, polynomial real arithmetic (Psatz); references
   include union_prob, finite_sum_monotone., union_indicator_bound.
   Library reuse: Stdlib.List (existsb/filter), Bool, Sorting.Permutation and
   FiniteSum.
   Boundary: Finite list semantics; duplicates contribute repeatedly. Probabilistic
   bounds need explicit nonnegative weights and possibly normalization.
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
   [arbitrary_union_contains_every_member] (theorem) — Finite Boolean event mass and
   union/intersection inequalities.
   Mathematical meaning: Proves a Boolean-event union/intersection fact or a
   corresponding probability bound.
   Exact checked proposition: Theorem arbitrary_union_contains_every_member : forall
   weights samples events e, In e events -> (forall x, In x samples -> 0 <= weights
   x) -> finite_prob weights samples e <= union_prob weights samples events.
   Premises and side conditions: The displayed hypotheses include nonnegative outcome
   weights; explicit nonzero or strict-positive numerical conditions; sample or list
   membership. No further assumptions are implicit.
   Proof/definition method: Kernel proof uses reuse of previously established lemmas,
   polynomial real arithmetic (Psatz); references include finite_prob,
   finite_sum_monotone., Hweights.
   Library reuse: Stdlib.List (existsb/filter), Bool, Sorting.Permutation and
   FiniteSum.
   Boundary: Finite list semantics; duplicates contribute repeatedly. Probabilistic
   bounds need explicit nonnegative weights and possibly normalization.
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
   [arbitrary_union_at_most_total_mass] (theorem) — Finite Boolean event mass and
   union/intersection inequalities.
   Mathematical meaning: Proves a Boolean-event union/intersection fact or a
   corresponding probability bound.
   Exact checked proposition: Theorem arbitrary_union_at_most_total_mass : forall
   weights samples events, (forall x, In x samples -> 0 <= weights x) -> union_prob
   weights samples events <= finite_sum weights samples.
   Premises and side conditions: The displayed hypotheses include nonnegative outcome
   weights; explicit nonzero or strict-positive numerical conditions; sample or list
   membership. No further assumptions are implicit.
   Proof/definition method: Kernel proof uses reuse of previously established lemmas,
   polynomial real arithmetic (Psatz); references include union_prob,
   finite_sum_monotone., Hweights.
   Library reuse: Stdlib.List (existsb/filter), Bool, Sorting.Permutation and
   FiniteSum.
   Boundary: Finite list semantics; duplicates contribute repeatedly. Probabilistic
   bounds need explicit nonnegative weights and possibly normalization.
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
   [normalized_arbitrary_union_at_most_one] (theorem) — Finite Boolean event mass and
   union/intersection inequalities.
   Mathematical meaning: Proves a Boolean-event union/intersection fact or a
   corresponding probability bound.
   Exact checked proposition: Theorem normalized_arbitrary_union_at_most_one : forall
   weights samples events, (forall x, In x samples -> 0 <= weights x) -> finite_sum
   weights samples = 1 -> union_prob weights samples events <= 1.
   Premises and side conditions: The displayed hypotheses include unit total sample
   mass; nonnegative outcome weights; explicit nonzero or strict-positive numerical
   conditions; sample or list membership. No further assumptions are implicit.
   Proof/definition method: Kernel proof uses reuse of previously established lemmas,
   linear real arithmetic (Lra); references include
   arbitrary_union_at_most_total_mass.
   Library reuse: Stdlib.List (existsb/filter), Bool, Sorting.Permutation and
   FiniteSum.
   Boundary: Finite list semantics; duplicates contribute repeatedly. Probabilistic
   bounds need explicit nonnegative weights and possibly normalization.
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
   [arbitrary_union_nonnegative] (theorem) — Finite Boolean event mass and
   union/intersection inequalities.
   Mathematical meaning: Proves a Boolean-event union/intersection fact or a
   corresponding probability bound.
   Exact checked proposition: Theorem arbitrary_union_nonnegative : forall weights
   samples events, (forall x, In x samples -> 0 <= weights x) -> 0 <= union_prob
   weights samples events.
   Premises and side conditions: The displayed hypotheses include nonnegative outcome
   weights; explicit nonzero or strict-positive numerical conditions; sample or list
   membership. No further assumptions are implicit.
   Proof/definition method: Kernel proof uses reuse of previously established lemmas;
   references include union_prob, FiniteSum.finite_sum_nonnegative., Rmult_le_pos..
   Library reuse: Stdlib.List (existsb/filter), Bool, Sorting.Permutation and
   FiniteSum.
   Boundary: Finite list semantics; duplicates contribute repeatedly. Probabilistic
   bounds need explicit nonnegative weights and possibly normalization.
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
   [finite_prob_true] (theorem) — Finite Boolean event mass and union/intersection
   inequalities.
   Mathematical meaning: Expresses a checked identity or bound within the finite
   boolean event mass and union/intersection inequalities.
   Exact checked proposition: Theorem finite_prob_true : forall weights samples,
   finite_prob weights samples (fun _ => true) = finite_sum weights samples.
   Premises and side conditions: All required premises are written in the signature.
   No independence or distributional assumption is silently supplied.
   Proof/definition method: Kernel proof uses reuse of previously established lemmas,
   ring/field normalization, definitional reduction; references include finite_prob.,
   finite_sum_extensional.
   Library reuse: Stdlib.List (existsb/filter), Bool, Sorting.Permutation and
   FiniteSum.
   Boundary: Finite list semantics; duplicates contribute repeatedly. Probabilistic
   bounds need explicit nonnegative weights and possibly normalization.
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
   [finite_prob_false] (theorem) — Finite Boolean event mass and union/intersection
   inequalities.
   Mathematical meaning: Expresses a checked identity or bound within the finite
   boolean event mass and union/intersection inequalities.
   Exact checked proposition: Theorem finite_prob_false : forall weights samples,
   finite_prob weights samples (fun _ => false) = 0.
   Premises and side conditions: All required premises are written in the signature.
   No independence or distributional assumption is silently supplied.
   Proof/definition method: Kernel proof uses rewriting of equalities, reuse of
   previously established lemmas, ring/field normalization, definitional reduction;
   references include finite_prob., finite_sum_extensional,
   FiniteSum.finite_sum_zero..
   Library reuse: Stdlib.List (existsb/filter), Bool, Sorting.Permutation and
   FiniteSum.
   Boundary: Finite list semantics; duplicates contribute repeatedly. Probabilistic
   bounds need explicit nonnegative weights and possibly normalization.
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
   [finite_prob_zero_iff_no_positive_mass_support] (theorem) — Finite Boolean event
   mass and union/intersection inequalities.
   Mathematical meaning: Expresses a checked identity or bound within the finite
   boolean event mass and union/intersection inequalities.
   Exact checked proposition: Theorem finite_prob_zero_iff_no_positive_mass_support :
   forall weights samples e, (forall x, In x samples -> 0 <= weights x) ->
   (finite_prob weights samples e = 0 <-> forall x, In x samples -> e x = true ->
   weights x = 0).
   Premises and side conditions: The displayed hypotheses include nonnegative outcome
   weights; explicit nonzero or strict-positive numerical conditions; sample or list
   membership. No further assumptions are implicit.
   Proof/definition method: Kernel proof uses case analysis, rewriting of equalities,
   reuse of previously established lemmas, polynomial real arithmetic (Psatz),
   ring/field normalization, definitional reduction; references include finite_prob,
   Rmult_le_pos., indicator_nonnegative..
   Library reuse: Stdlib.List (existsb/filter), Bool, Sorting.Permutation and
   FiniteSum.
   Boundary: Finite list semantics; duplicates contribute repeatedly. Probabilistic
   bounds need explicit nonnegative weights and possibly normalization.
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
   [finite_prob_positive_of_positive_support] (theorem) — Finite Boolean event mass
   and union/intersection inequalities.
   Mathematical meaning: Expresses a checked identity or bound within the finite
   boolean event mass and union/intersection inequalities.
   Exact checked proposition: Theorem finite_prob_positive_of_positive_support :
   forall weights samples e x, (forall y, In y samples -> 0 <= weights y) -> In x
   samples -> e x = true -> 0 < weights x -> 0 < finite_prob weights samples e.
   Premises and side conditions: The displayed hypotheses include nonnegative outcome
   weights; explicit nonzero or strict-positive numerical conditions; sample or list
   membership. No further assumptions are implicit.
   Proof/definition method: Kernel proof uses rewriting of equalities, reuse of
   previously established lemmas, linear real arithmetic (Lra), definitional
   reduction; references include finite_prob, Rmult_le_pos., indicator_nonnegative..
   Library reuse: Stdlib.List (existsb/filter), Bool, Sorting.Permutation and
   FiniteSum.
   Boundary: Finite list semantics; duplicates contribute repeatedly. Probabilistic
   bounds need explicit nonnegative weights and possibly normalization.
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
   [finite_prob_as_filtered_mass] (theorem) — Finite Boolean event mass and
   union/intersection inequalities.
   Mathematical meaning: Expresses a checked identity or bound within the finite
   boolean event mass and union/intersection inequalities.
   Exact checked proposition: Theorem finite_prob_as_filtered_mass : forall weights
   samples e, finite_prob weights samples e = FiniteSum.finite_sum weights (filter e
   samples).
   Premises and side conditions: All required premises are written in the signature.
   No independence or distributional assumption is silently supplied.
   Proof/definition method: Kernel proof uses case analysis, rewriting of equalities,
   reuse of previously established lemmas, ring/field normalization, definitional
   reduction; references include finite_prob, FiniteSum.finite_sum_filter.,
   FiniteSum.finite_sum_ext.
   Library reuse: Stdlib.List (existsb/filter), Bool, Sorting.Permutation and
   FiniteSum.
   Boundary: Finite list semantics; duplicates contribute repeatedly. Probabilistic
   bounds need explicit nonnegative weights and possibly normalization.
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
   [finite_prob_event_ext_on_samples] (theorem) — Finite Boolean event mass and
   union/intersection inequalities.
   Mathematical meaning: Relates finite outcome weights to the stated marginal,
   joint, or enumerated-event quantity.
   Exact checked proposition: Theorem finite_prob_event_ext_on_samples : forall
   weights samples e f, (forall x, In x samples -> e x = f x) -> finite_prob weights
   samples e = finite_prob weights samples f.
   Premises and side conditions: The displayed hypotheses include sample or list
   membership. No further assumptions are implicit.
   Proof/definition method: Rewrite event probability as the sum of weights
   over a standard filtered sample, then use Stdlib.List.filter_ext_in.
   The premise only requires agreement on the enumerated sample.
   Library reuse: Stdlib.List (existsb/filter), Bool, Sorting.Permutation and
   FiniteSum.
   Boundary: Finite list semantics; duplicates contribute repeatedly. Probabilistic
   bounds need explicit nonnegative weights and possibly normalization.
   *)
  Theorem finite_prob_event_ext_on_samples :
    forall weights samples e f,
      (forall x, In x samples -> e x = f x) ->
      finite_prob weights samples e =
        finite_prob weights samples f.
  Proof.
    intros weights samples e f Heq.
    rewrite !finite_prob_as_filtered_mass.
    rewrite (filter_ext_in e f samples Heq).
    reflexivity.
  Qed.

  (* Restricting the outcomes by a Boolean predicate is exactly the
     same finite mass as intersecting the original event with it.
     Stdlib.List.filter performs the restriction; no custom selection
     recursion or normalization hypothesis is introduced. *)
  (**
   [finite_prob_on_filtered_samples] (theorem) — Finite Boolean-event mass.
   Mathematical meaning: The event mass computed from a filtered outcome
   list is the mass of the intersection with the filtering predicate on
   the original outcome list, including repeated outcomes with their
   original multiplicity.
   Exact checked proposition: forall weights samples p e,
   finite_prob weights (filter p samples) e =
   finite_prob weights samples (fun x => andb (p x) (e x)).
   Premises and side conditions: No positivity, independence or unit
   total mass is required; the identity holds for arbitrary real weights.
   Proof/definition method: Reuse the generic FiniteSum.finite_sum_filter
   theorem and finite_sum_ext; reduce the four Bool cases and normalize
   real arithmetic using the standard ring tactic.
   Library reuse: Stdlib.List.filter, Stdlib.Bool.andb,
   FiniteSum.finite_sum_filter, FiniteSum.finite_sum_ext, ring.
   Boundary: The equality is for explicitly enumerated finite samples;
   it makes no assertion about a continuous conditional distribution.
   *)
  Theorem finite_prob_on_filtered_samples :
    forall weights samples p e,
      finite_prob weights (filter p samples) e =
        finite_prob weights samples (fun x => andb (p x) (e x)).
  Proof.
    intros weights samples p e.
    unfold finite_prob, finite_sum.
    rewrite FiniteSum.finite_sum_filter.
    apply FiniteSum.finite_sum_ext; intro x.
    destruct (p x), (e x); unfold indicator; simpl; ring.
  Qed.

  (* Event families are represented by Stdlib.List.existsb; applying
     a filter to the outcome list restricts their union without any
     need to construct a bespoke intersection-of-events family. *)
  (**
   [union_prob_on_filtered_samples] (theorem) — Finite union mass.
   Mathematical meaning: Filtering outcomes before computing a finite
   event-family union equals intersecting the union indicator with
   the filter event in the original finite sample.
   Exact checked proposition: forall weights samples p events,
   union_prob weights (filter p samples) events =
   finite_prob weights samples
   (fun x => andb (p x) (any_event events x)).
   Premises and side conditions: Arbitrary finite event lists and real
   weights are supported, including duplicated outcomes; no independence
   or normalization assumption is needed for the algebraic equality.
   Proof/definition method: Unfold union_prob and apply the checked
   finite_prob_on_filtered_samples theorem directly.
   Library reuse: Stdlib.List.existsb and filter; the preceding
   finite_prob_on_filtered_samples correspondence.
   Boundary: This proves a finite counting/weighted-sum identity,
   not empirical admission probabilities or Gaussian assumptions.
   *)
  Theorem union_prob_on_filtered_samples :
    forall weights samples p events,
      union_prob weights (filter p samples) events =
        finite_prob weights samples
          (fun x => andb (p x) (any_event events x)).
  Proof.
    intros weights samples p events.
    unfold union_prob.
    apply finite_prob_on_filtered_samples.
  Qed.

  (* A Boolean predicate partitions the enumerated outcomes into
     selected and rejected lists. The equality is about weighted
     enumeration, not conditional probabilities or an assumed measure. *)
  (**
   [finite_prob_filtered_partition] (theorem) — Finite sample partition.
   Mathematical meaning: A finite event's mass splits additively into
   its contributions from outcomes satisfying a filter predicate and
   outcomes satisfying the Boolean complement, with multiplicities
   preserved by the standard filter operation.
   Exact checked proposition: forall weights samples p e,
   finite_prob weights (filter p samples) e +
   finite_prob weights (filter (fun x => negb (p x)) samples) e =
   finite_prob weights samples e.
   Premises and side conditions: Holds for any real weights, sample
   multiplicities and Boolean event predicates. No disjointness,
   nonnegativity, normality or probability normalization is assumed.
   Proof/definition method: Unfold the shared finite sum representation
   of event mass, then instantiate the fully generic and checked
   FiniteSum.finite_sum_filter_partition lemma. No local Boolean case
   analysis or event-specific recursion is necessary.
   Library reuse: Stdlib.List.filter, Stdlib.Bool.negb/andb,
   FiniteSum.finite_sum_filter_partition.
   Boundary: This is sample-list additivity; it does not assert
   conditional independence or probabilities over a continuum.
   *)
  Theorem finite_prob_filtered_partition :
    forall weights samples p e,
      finite_prob weights (filter p samples) e +
      finite_prob weights
        (filter (fun x => negb (p x)) samples) e =
      finite_prob weights samples e.
  Proof.
    intros weights samples p e.
    unfold finite_prob, finite_sum.
    apply FiniteSum.finite_sum_filter_partition.
  Qed.

  (* The same partition identity applies to a whole event family
     because union_prob is just finite_prob of Stdlib.List.existsb. *)
  (**
   [union_prob_filtered_partition] (theorem) — Finite union partition.
   Mathematical meaning: The weighted probability of a union of
   routes is additive across the selected and rejected portions of
   an enumerated sample, without requiring independence of the routes.
   Exact checked proposition: forall weights samples p events,
   union_prob weights (filter p samples) events +
   union_prob weights (filter (fun x => negb (p x)) samples) events =
   union_prob weights samples events.
   Premises and side conditions: Any finite family of Boolean events
   and arbitrary real weights; normalization and independence are not
   needed for this identity.
   Proof/definition method: Reduce union_prob to finite_prob of
   any_event, then invoke finite_prob_filtered_partition directly.
   Library reuse: Stdlib.List.existsb/filter, Stdlib.Bool.negb,
   finite_prob_filtered_partition.
   Boundary: A finite weighted-sample identity, not an empirical
   predictive-validity theorem.
   *)
  Theorem union_prob_filtered_partition :
    forall weights samples p events,
      union_prob weights (filter p samples) events +
      union_prob weights
        (filter (fun x => negb (p x)) samples) events =
      union_prob weights samples events.
  Proof.
    intros weights samples p events.
    unfold union_prob.
    apply finite_prob_filtered_partition.
  Qed.

  (**
   [finite_prob_sample_append] (theorem) — Finite Boolean event mass and
   union/intersection inequalities.
   Mathematical meaning: The weighted event mass is additive over a
   concatenation of two sample lists. The same outcome can occur
   in both inputs and contributes separately at both positions.
   Exact checked proposition: Theorem finite_prob_sample_append : forall weights left
   right e, finite_prob weights (left ++ right) e = finite_prob weights left e +
   finite_prob weights right e.
   Premises and side conditions: Arbitrary real weights and a Boolean event predicate.
   List concatenation changes enumeration multiplicities, not
   event membership. No independence, positivity, normalization
   or distinct-outcome premise is required.
   Proof/definition method: Unfold finite_prob and its shared finite_sum
   alias, then apply the already proved generic
   FiniteSum.finite_sum_app theorem, without a new induction.
   Library reuse: Stdlib.List.app, FiniteSum.finite_sum_app,
   finite_prob and the shared FiniteSum.finite_sum definition.
   Boundary: Exact additivity over concatenated lists; this
   does not assert disjointness of events or conventional
   additivity for arbitrary overlapping event sets.
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

  (* Appending sample lists is additive even for signed masses.
     Reuse the existing event-mass append law when the event is a
     union encoded by Stdlib.List.existsb; no event-specific fold. *)
  (**
   [union_prob_sample_append] (theorem) — Additivity over outcome lists.
   Mathematical meaning: For a fixed family of Boolean events,
   the union mass on concatenated outcome lists equals the sum
   of union masses on both lists. Duplicated outcome occurrences
   contribute once for each position, including across the join.
   Exact checked proposition: forall weights left right events,
   union_prob weights (left ++ right) events =
   union_prob weights left events + union_prob weights right events.
   Premises and side conditions: Works with arbitrary real weights,
   overlapping or repeated events, and duplicated outcomes. No
   independence, nonnegativity or mass normalization is assumed.
   Proof/definition method: Unfold the existing union_prob alias
   and apply finite_prob_sample_append directly; no new induction.
   Library reuse: Stdlib.List.app and existsb,
   finite_prob_sample_append and the existing union_prob definition.
   Boundary: Concatenation is a multiset/list operation rather than
   an assertion of disjoint measurable probability events.
   *)
  Theorem union_prob_sample_append :
    forall weights left right events,
      union_prob weights (left ++ right) events =
        union_prob weights left events +
        union_prob weights right events.
  Proof.
    intros weights left right events.
    unfold union_prob.
    apply finite_prob_sample_append.
  Qed.

  (* Filtering distributes over list concatenation by Stdlib.List;
     use the library law instead of proving another list recursion. *)
  (**
   [finite_prob_filtered_append] (theorem) — Event mass after filtering.
   Mathematical meaning: Filtering a concatenated outcome list and
   measuring a fixed event is additive across the two independently
   filtered input lists, preserving duplicate contributions.
   Exact checked proposition: forall weights left right p e,
   finite_prob weights (filter p (left ++ right)) e =
   finite_prob weights (filter p left) e +
   finite_prob weights (filter p right) e.
   Premises and side conditions: The filter p and event e are Boolean
   predicates. The real outcome weights are arbitrary; no positivity,
   normalization, event independence, or distinctness is assumed.
   Proof/definition method: Rewrite the sample using
   Stdlib.List.filter_app and invoke finite_prob_sample_append.
   Library reuse: Stdlib.List.filter_app, List.app,
   and the existing finite_prob_sample_append theorem.
   Boundary: This is exact finite sample-list algebra; it does not
   define conditional probabilities or continuous filtering.
   *)
  Theorem finite_prob_filtered_append :
    forall weights left right p e,
      finite_prob weights (filter p (left ++ right)) e =
        finite_prob weights (filter p left) e +
        finite_prob weights (filter p right) e.
  Proof.
    intros weights left right p e.
    rewrite filter_app.
    apply finite_prob_sample_append.
  Qed.

  (**
   [union_prob_filtered_append] (theorem) — Finite union sample additivity.
   Mathematical meaning: The union mass of any finite event family
   after filtering concatenated outcome lists is the sum of that
   union mass on each separately filtered list.
   Exact checked proposition: forall weights left right p events,
   union_prob weights (filter p (left ++ right)) events =
   union_prob weights (filter p left) events +
   union_prob weights (filter p right) events.
   Premises and side conditions: Any finite event family and sample
   lists are allowed, including duplicates. Sample weights can be
   negative, since the result is an algebraic equality rather than
   an inequality or a distributional interpretation.
   Proof/definition method: Apply Stdlib.List.filter_app to the
   concatenation, then reuse union_prob_sample_append directly.
   Library reuse: Stdlib.List.filter_app and the existing
   union_prob_sample_append finite-union law.
   Boundary: A finite enumeration identity; no assumption about
   empirical admission routes or probabilistic independence.
   *)
  Theorem union_prob_filtered_append :
    forall weights left right p events,
      union_prob weights (filter p (left ++ right)) events =
        union_prob weights (filter p left) events +
        union_prob weights (filter p right) events.
  Proof.
    intros weights left right p events.
    rewrite filter_app.
    apply union_prob_sample_append.
  Qed.

  (**
   [finite_prob_sample_permutation] (theorem) — Finite Boolean event mass and
   union/intersection inequalities.
   Mathematical meaning: Proves a list-structural invariant without custom sorting or
   indexing.
   Exact checked proposition: Theorem finite_prob_sample_permutation : forall weights
   left right e, Permutation left right -> finite_prob weights left e = finite_prob
   weights right e.
   Premises and side conditions: The displayed hypotheses include Stdlib permutation
   relation. No further assumptions are implicit.
   Proof/definition method: Kernel proof uses reuse of previously established lemmas;
   references include finite_prob, FiniteSum.finite_sum_permutation, Hperm..
   Library reuse: Stdlib.List (existsb/filter), Bool, Sorting.Permutation and
   FiniteSum.
   Boundary: Finite list semantics; duplicates contribute repeatedly. Probabilistic
   bounds need explicit nonnegative weights and possibly normalization.
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
   [union_prob_sample_permutation] (theorem) — Finite Boolean event mass and
   union/intersection inequalities.
   Mathematical meaning: Proves a Boolean-event union/intersection fact or a
   corresponding probability bound.
   Exact checked proposition: Theorem union_prob_sample_permutation : forall weights
   left right events, Permutation left right -> union_prob weights left events =
   union_prob weights right events.
   Premises and side conditions: The displayed hypotheses include Stdlib permutation
   relation. No further assumptions are implicit.
   Proof/definition method: Kernel proof uses reuse of previously established lemmas;
   references include union_prob., finite_prob_sample_permutation, Hperm..
   Library reuse: Stdlib.List (existsb/filter), Bool, Sorting.Permutation and
   FiniteSum.
   Boundary: Finite list semantics; duplicates contribute repeatedly. Probabilistic
   bounds need explicit nonnegative weights and possibly normalization.
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
   [sum_marginal_probs_event_permutation] (theorem) — Finite Boolean event mass and
   union/intersection inequalities.
   Mathematical meaning: Derives a sum or expectation identity for the explicitly
   enumerated terms.
   Exact checked proposition: Theorem sum_marginal_probs_event_permutation : forall
   weights samples left right, Permutation left right -> sum_marginal_probs weights
   samples left = sum_marginal_probs weights samples right.
   Premises and side conditions: The displayed hypotheses include Stdlib permutation
   relation. No further assumptions are implicit.
   Proof/definition method: Kernel proof uses reuse of previously established lemmas;
   references include sum_marginal_probs., FiniteSum.finite_sum_permutation, Hperm..
   Library reuse: Stdlib.List (existsb/filter), Bool, Sorting.Permutation and
   FiniteSum.
   Boundary: Finite list semantics; duplicates contribute repeatedly. Probabilistic
   bounds need explicit nonnegative weights and possibly normalization.
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
   [finite_prob_event_monotone] (theorem) — Finite Boolean event mass and
   union/intersection inequalities.
   Mathematical meaning: Expresses a checked identity or bound within the finite
   boolean event mass and union/intersection inequalities.
   Exact checked proposition: Theorem finite_prob_event_monotone : forall weights
   samples e f, (forall x, In x samples -> 0 <= weights x) -> (forall x, In x samples
   -> e x = true -> f x = true) -> finite_prob weights samples e <= finite_prob
   weights samples f.
   Premises and side conditions: The displayed hypotheses include nonnegative outcome
   weights; explicit nonzero or strict-positive numerical conditions; sample or list
   membership. No further assumptions are implicit.
   Proof/definition method: Kernel proof uses reuse of previously established lemmas,
   polynomial real arithmetic (Psatz); references include finite_prob.,
   finite_sum_monotone., indicator_implication_bound.
   Library reuse: Stdlib.List (existsb/filter), Bool, Sorting.Permutation and
   FiniteSum.
   Boundary: Finite list semantics; duplicates contribute repeatedly. Probabilistic
   bounds need explicit nonnegative weights and possibly normalization.
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

  (* Selecting a subset of sample positions cannot increase the
     weight of any fixed event when sample weights are nonnegative.
     This is a direct instance of event inclusion, not a new sum proof. *)
  (**
   [finite_prob_filtered_mass_le] (theorem) — Monotonicity under
   restriction of a finite list of outcomes.
   Mathematical meaning: The weighted mass assigned to an event on
   selected outcomes does not exceed its mass on all outcomes.
   Exact checked proposition: forall weights samples p e,
   (forall x, In x samples -> 0 <= weights x) ->
   finite_prob weights (filter p samples) e <=
   finite_prob weights samples e.
   Premises and side conditions: All weights at enumerated outcomes
   must be nonnegative. The list may contain duplicates; neither
   normalization nor event independence is required.
   Proof/definition method: Identify the filtered event with the
   conjunction using finite_prob_on_filtered_samples, then apply
   finite_prob_event_monotone and Bool.andb_true_iff.
   Library reuse: Stdlib.List.filter/In, Stdlib.Bool.andb_true_iff,
   finite_prob_on_filtered_samples and finite_prob_event_monotone.
   Boundary: Finite enumerated-outcome monotonicity only; no
   claim is made for signed weights or continuous measures.
   *)
  Theorem finite_prob_filtered_mass_le :
    forall weights samples p e,
      (forall x, In x samples -> 0 <= weights x) ->
      finite_prob weights (filter p samples) e <=
        finite_prob weights samples e.
  Proof.
    intros weights samples p e Hw.
    rewrite finite_prob_on_filtered_samples.
    apply finite_prob_event_monotone; [exact Hw|].
    intros x _ Hand.
    apply andb_true_iff in Hand.
    exact (proj2 Hand).
  Qed.

  (* The event-family version is an immediate specialization, since
     union_prob is the mass of Stdlib.List.existsb over the family. *)
  (**
   [union_prob_filtered_mass_le] (theorem) — Monotonicity for unions.
   Mathematical meaning: Restricting the sample cannot increase
   the weighted union mass of any finite family of Boolean events.
   Exact checked proposition: forall weights samples p events,
   (forall x, In x samples -> 0 <= weights x) ->
   union_prob weights (filter p samples) events <=
   union_prob weights samples events.
   Premises and side conditions: Weights are nonnegative at sample
   occurrences. No total-mass equality, independence or disjointness
   is assumed, and duplicates retain their original multiplicity.
   Proof/definition method: Unfold union_prob to expose the shared
   probability of any_event; directly invoke the already established
   finite_prob_filtered_mass_le result.
   Library reuse: Stdlib.List.existsb/filter, finite_prob_filtered_mass_le.
   Boundary: Finite event-family list semantics, not a statistical
   statement about actual test validity or conditional probabilities.
   *)
  Theorem union_prob_filtered_mass_le :
    forall weights samples p events,
      (forall x, In x samples -> 0 <= weights x) ->
      union_prob weights (filter p samples) events <=
        union_prob weights samples events.
  Proof.
    intros weights samples p events Hw.
    unfold union_prob.
    apply finite_prob_filtered_mass_le; exact Hw.
  Qed.

  (**
   [normalized_finite_prob_unit_interval] (theorem) — Finite Boolean event mass and
   union/intersection inequalities.
   Mathematical meaning: Expresses a checked identity or bound within the finite
   boolean event mass and union/intersection inequalities.
   Exact checked proposition: Theorem normalized_finite_prob_unit_interval : forall
   weights samples e, (forall x, In x samples -> 0 <= weights x) -> finite_sum
   weights samples = 1 -> 0 <= finite_prob weights samples e /\ finite_prob weights
   samples e <= 1.
   Premises and side conditions: The displayed hypotheses include unit total sample
   mass; nonnegative outcome weights; explicit nonzero or strict-positive numerical
   conditions; sample or list membership. No further assumptions are implicit.
   Proof/definition method: Kernel proof uses reuse of previously established lemmas,
   linear real arithmetic (Lra), polynomial real arithmetic (Psatz); references
   include finite_prob., FiniteSum.finite_sum_nonnegative., Rmult_le_pos..
   Library reuse: Stdlib.List (existsb/filter), Bool, Sorting.Permutation and
   FiniteSum.
   Boundary: Finite list semantics; duplicates contribute repeatedly. Probabilistic
   bounds need explicit nonnegative weights and possibly normalization.
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
   [empty_family_probability_zero] (theorem) — Finite Boolean event mass and
   union/intersection inequalities.
   Mathematical meaning: Expresses a checked identity or bound within the finite
   boolean event mass and union/intersection inequalities.
   Exact checked proposition: Theorem empty_family_probability_zero : forall weights
   samples, union_prob weights samples [] = 0.
   Premises and side conditions: All required premises are written in the signature.
   No independence or distributional assumption is silently supplied.
   Proof/definition method: Kernel proof uses reuse of previously established lemmas;
   references include finite_prob_false..
   Library reuse: Stdlib.List (existsb/filter), Bool, Sorting.Permutation and
   FiniteSum.
   Boundary: Finite list semantics; duplicates contribute repeatedly. Probabilistic
   bounds need explicit nonnegative weights and possibly normalization.
   *)
  Theorem empty_family_probability_zero :
    forall weights samples, union_prob weights samples [] = 0.
  Proof.
    intros weights samples.
    change (finite_prob weights samples (fun _ => false) = 0).
    apply finite_prob_false.
  Qed.

  (**
   [singleton_family_probability] (theorem) — Finite Boolean event mass and
   union/intersection inequalities.
   Mathematical meaning: Expresses a checked identity or bound within the finite
   boolean event mass and union/intersection inequalities.
   Exact checked proposition: Theorem singleton_family_probability : forall weights
   samples e, union_prob weights samples [e] = finite_prob weights samples e.
   Premises and side conditions: All required premises are written in the signature.
   No independence or distributional assumption is silently supplied.
   Proof/definition method: Kernel proof uses rewriting of equalities, reuse of
   previously established lemmas, definitional reduction; references include
   union_prob, finite_sum_extensional, any_event.
   Library reuse: Stdlib.List (existsb/filter), Bool, Sorting.Permutation and
   FiniteSum.
   Boundary: Finite list semantics; duplicates contribute repeatedly. Probabilistic
   bounds need explicit nonnegative weights and possibly normalization.
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
   [union_prob_membership_extensional] (theorem) — Finite Boolean event mass and
   union/intersection inequalities.
   Mathematical meaning: Proves a Boolean-event union/intersection fact or a
   corresponding probability bound.
   Exact checked proposition: Theorem union_prob_membership_extensional : forall
   weights samples left right, (forall e, In e left <-> In e right) -> union_prob
   weights samples left = union_prob weights samples right.
   Premises and side conditions: The displayed hypotheses include sample or list
   membership. No further assumptions are implicit.
   Proof/definition method: Kernel proof uses case analysis, rewriting of equalities,
   reuse of previously established lemmas, definitional reduction; references include
   union_prob, finite_sum_extensional, any_event.
   Library reuse: Stdlib.List (existsb/filter), Bool, Sorting.Permutation and
   FiniteSum.
   Boundary: Finite list semantics; duplicates contribute repeatedly. Probabilistic
   bounds need explicit nonnegative weights and possibly normalization.
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
   [union_prob_permutation_invariant] (theorem) — Finite Boolean event mass and
   union/intersection inequalities.
   Mathematical meaning: Proves a Boolean-event union/intersection fact or a
   corresponding probability bound.
   Exact checked proposition: Theorem union_prob_permutation_invariant : forall
   weights samples left right, Permutation left right -> union_prob weights samples
   left = union_prob weights samples right.
   Premises and side conditions: The displayed hypotheses include Stdlib permutation
   relation. No further assumptions are implicit.
   Proof/definition method: Kernel proof uses reuse of previously established lemmas;
   references include union_prob_membership_extensional., Permutation_in,
   Permutation_in..
   Library reuse: Stdlib.List (existsb/filter), Bool, Sorting.Permutation and
   FiniteSum.
   Boundary: Finite list semantics; duplicates contribute repeatedly. Probabilistic
   bounds need explicit nonnegative weights and possibly normalization.
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
   [union_prob_duplicate_route] (theorem) — Finite Boolean event mass and
   union/intersection inequalities.
   Mathematical meaning: Proves a Boolean-event union/intersection fact or a
   corresponding probability bound.
   Exact checked proposition: Theorem union_prob_duplicate_route : forall weights
   samples e events, union_prob weights samples (e :: e :: events) = union_prob
   weights samples (e :: events).
   Premises and side conditions: All required premises are written in the signature.
   No independence or distributional assumption is silently supplied.
   Proof/definition method: Kernel proof uses reuse of previously established lemmas,
   definitional reduction; references include union_prob_membership_extensional..
   Library reuse: Stdlib.List (existsb/filter), Bool, Sorting.Permutation and
   FiniteSum.
   Boundary: Finite list semantics; duplicates contribute repeatedly. Probabilistic
   bounds need explicit nonnegative weights and possibly normalization.
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
   [indicator_complement] (lemma) — Finite Boolean event mass and union/intersection
   inequalities.
   Mathematical meaning: Expresses a checked identity or bound within the finite
   boolean event mass and union/intersection inequalities.
   Exact checked proposition: Lemma indicator_complement : forall b, indicator (negb
   b) + indicator b = 1.
   Premises and side conditions: All required premises are written in the signature.
   No independence or distributional assumption is silently supplied.
   Proof/definition method: Kernel proof uses ring/field normalization, definitional
   reduction.
   Library reuse: Stdlib.List (existsb/filter), Bool, Sorting.Permutation and
   FiniteSum.
   Boundary: Finite list semantics; duplicates contribute repeatedly. Probabilistic
   bounds need explicit nonnegative weights and possibly normalization.
   *)
  Lemma indicator_complement :
    forall b, indicator (negb b) + indicator b = 1.
  Proof.
    intros []; simpl; ring.
  Qed.

  (**
   [finite_prob_complement] (theorem) — Finite Boolean event mass and
   union/intersection inequalities.
   Mathematical meaning: Expresses a checked identity or bound within the finite
   boolean event mass and union/intersection inequalities.
   Exact checked proposition: Theorem finite_prob_complement : forall weights samples
   e, finite_prob weights samples (fun x => negb (e x)) + finite_prob weights samples
   e = finite_sum weights samples.
   Premises and side conditions: All required premises are written in the signature.
   No independence or distributional assumption is silently supplied.
   Proof/definition method: Express event and complement masses
   through finite_prob_as_filtered_mass and use the checked generic
   FiniteSum.finite_sum_filter_partition identity, with Rplus_comm
   to align the order. No event-specific indicator arithmetic.
   Library reuse: Stdlib.List (existsb/filter), Bool, Sorting.Permutation and
   FiniteSum.
   Boundary: Finite list semantics; duplicates contribute repeatedly. Probabilistic
   bounds need explicit nonnegative weights and possibly normalization.
   *)
  Theorem finite_prob_complement :
    forall weights samples e,
      finite_prob weights samples (fun x => negb (e x)) +
        finite_prob weights samples e =
        finite_sum weights samples.
  Proof.
    intros weights samples e.
    rewrite !finite_prob_as_filtered_mass.
    rewrite Rplus_comm.
    apply FiniteSum.finite_sum_filter_partition.
  Qed.

  (**
   [normalized_finite_prob_complement] (theorem) — Finite Boolean event mass and
   union/intersection inequalities.
   Mathematical meaning: Expresses a checked identity or bound within the finite
   boolean event mass and union/intersection inequalities.
   Exact checked proposition: Theorem normalized_finite_prob_complement : forall
   weights samples e, finite_sum weights samples = 1 -> finite_prob weights samples
   (fun x => negb (e x)) = 1 - finite_prob weights samples e.
   Premises and side conditions: The displayed hypotheses include unit total sample
   mass. No further assumptions are implicit.
   Proof/definition method: Kernel proof uses rewriting of equalities, reuse of
   previously established lemmas, linear real arithmetic (Lra); references include
   finite_prob_complement, Htotal.
   Library reuse: Stdlib.List (existsb/filter), Bool, Sorting.Permutation and
   FiniteSum.
   Boundary: Finite list semantics; duplicates contribute repeatedly. Probabilistic
   bounds need explicit nonnegative weights and possibly normalization.
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
   [indicator_union_intersection] (lemma) — Finite Boolean event mass and
   union/intersection inequalities.
   Mathematical meaning: Proves a Boolean-event union/intersection fact or a
   corresponding probability bound.
   Exact checked proposition: Lemma indicator_union_intersection : forall b c,
   indicator (orb b c) + indicator (andb b c) = indicator b + indicator c.
   Premises and side conditions: All required premises are written in the signature.
   No independence or distributional assumption is silently supplied.
   Proof/definition method: Kernel proof uses ring/field normalization, definitional
   reduction.
   Library reuse: Stdlib.List (existsb/filter), Bool, Sorting.Permutation and
   FiniteSum.
   Boundary: Finite list semantics; duplicates contribute repeatedly. Probabilistic
   bounds need explicit nonnegative weights and possibly normalization.
   *)
  Lemma indicator_union_intersection :
    forall b c,
      indicator (orb b c) + indicator (andb b c) =
        indicator b + indicator c.
  Proof.
    intros [] []; simpl; ring.
  Qed.

  (**
   [finite_prob_inclusion_exclusion] (theorem) — Finite Boolean event mass and
   union/intersection inequalities.
   Mathematical meaning: Expresses a checked identity or bound within the finite
   boolean event mass and union/intersection inequalities.
   Exact checked proposition: Theorem finite_prob_inclusion_exclusion : forall
   weights samples e f, finite_prob weights samples (fun x => orb (e x) (f x)) +
   finite_prob weights samples (fun x => andb (e x) (f x)) = finite_prob weights
   samples e + finite_prob weights samples f.
   Premises and side conditions: All required premises are written in the signature.
   No independence or distributional assumption is silently supplied.
   Proof/definition method: Kernel proof uses rewriting of equalities, reuse of
   previously established lemmas, ring/field normalization; references include
   finite_prob., finite_sum_extensional, indicator_union_intersection..
   Library reuse: Stdlib.List (existsb/filter), Bool, Sorting.Permutation and
   FiniteSum.
   Boundary: Finite list semantics; duplicates contribute repeatedly. Probabilistic
   bounds need explicit nonnegative weights and possibly normalization.
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
   [two_event_union_probability] (theorem) — Finite Boolean event mass and
   union/intersection inequalities.
   Mathematical meaning: Proves a Boolean-event union/intersection fact or a
   corresponding probability bound.
   Exact checked proposition: Theorem two_event_union_probability : forall weights
   samples e f, union_prob weights samples [e; f] = finite_prob weights samples (fun
   x => orb (e x) (f x)).
   Premises and side conditions: All required premises are written in the signature.
   No independence or distributional assumption is silently supplied.
   Proof/definition method: Kernel proof uses rewriting of equalities, reuse of
   previously established lemmas, definitional reduction; references include
   union_prob, finite_sum_extensional, any_event.
   Library reuse: Stdlib.List (existsb/filter), Bool, Sorting.Permutation and
   FiniteSum.
   Boundary: Finite list semantics; duplicates contribute repeatedly. Probabilistic
   bounds need explicit nonnegative weights and possibly normalization.
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
   [two_event_union_inclusion_exclusion] (theorem) — Finite Boolean event mass and
   union/intersection inequalities.
   Mathematical meaning: Proves a Boolean-event union/intersection fact or a
   corresponding probability bound.
   Exact checked proposition: Theorem two_event_union_inclusion_exclusion : forall
   weights samples e f, union_prob weights samples [e; f] + finite_prob weights
   samples (fun x => andb (e x) (f x)) = finite_prob weights samples e + finite_prob
   weights samples f.
   Premises and side conditions: All required premises are written in the signature.
   No independence or distributional assumption is silently supplied.
   Proof/definition method: Kernel proof uses rewriting of equalities, reuse of
   previously established lemmas; references include two_event_union_probability.,
   finite_prob_inclusion_exclusion..
   Library reuse: Stdlib.List (existsb/filter), Bool, Sorting.Permutation and
   FiniteSum.
   Boundary: Finite list semantics; duplicates contribute repeatedly. Probabilistic
   bounds need explicit nonnegative weights and possibly normalization.
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
   [any_event_append] (lemma) — Finite Boolean event mass and union/intersection
   inequalities.
   Mathematical meaning: Proves a list-structural invariant without custom sorting or
   indexing.
   Exact checked proposition: Lemma any_event_append : forall left right x, any_event
   (left ++ right) x = orb (any_event left x) (any_event right x).
   Premises and side conditions: All required premises are written in the signature.
   No independence or distributional assumption is silently supplied.
   Proof/definition method: Kernel proof uses rewriting of equalities, definitional
   reduction; references include any_event., existsb_app..
   Library reuse: Stdlib.List (existsb/filter), Bool, Sorting.Permutation and
   FiniteSum.
   Boundary: Finite list semantics; duplicates contribute repeatedly. Probabilistic
   bounds need explicit nonnegative weights and possibly normalization.
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
   [union_prob_append] (theorem) — Finite Boolean event mass and union/intersection
   inequalities.
   Mathematical meaning: The union of two finite event families equals
   their Boolean OR at each outcome; this describes appending
   event lists, not appending sample lists.
   Exact checked proposition: Theorem union_prob_append : forall weights samples left
   right, union_prob weights samples (left ++ right) = finite_prob weights samples
   (fun x => orb (any_event left x) (any_event right x)).
   Premises and side conditions: Events are arbitrary Boolean predicates and
   may overlap or repeat. Sample weights can have any sign;
   the identity is Boolean/algebraic, not an independence
   or probability-normalization statement.
   Proof/definition method: Unfold union_prob to finite_prob, reuse the
   already checked finite_prob_event_ext_on_samples theorem,
   then apply any_event_append pointwise. This in turn relies
   on Stdlib.List.existsb_app, with no new finite sum proof.
   Library reuse: Stdlib.List.existsb_app, FiniteUnion.any_event,
   any_event_append and finite_prob_event_ext_on_samples.
   Boundary: Event-family union is idempotent under
   duplicate events but the sum of marginal probabilities is
   not; this identity concerns the union indicator, not the
   generally larger sum of overlapping marginal masses.
*)
  Theorem union_prob_append :
    forall weights samples left right,
      union_prob weights samples (left ++ right) =
        finite_prob weights samples
          (fun x => orb (any_event left x) (any_event right x)).
  Proof.
    intros weights samples left right.
    unfold union_prob.
    apply finite_prob_event_ext_on_samples.
    intros x _.
    apply any_event_append.
  Qed.

  (**
   [sum_marginal_probs_append] (theorem) — Finite Boolean event mass and
   union/intersection inequalities.
   Mathematical meaning: Derives a sum or expectation identity for the explicitly
   enumerated terms.
   Exact checked proposition: Theorem sum_marginal_probs_append : forall weights
   samples left right, sum_marginal_probs weights samples (left ++ right) =
   sum_marginal_probs weights samples left + sum_marginal_probs weights samples
   right.
   Premises and side conditions: All required premises are written in the signature.
   No independence or distributional assumption is silently supplied.
   Proof/definition method: Kernel proof uses reuse of previously established lemmas;
   references include FiniteSum.finite_sum_app..
   Library reuse: Stdlib.List (existsb/filter), Bool, Sorting.Permutation and
   FiniteSum.
   Boundary: Finite list semantics; duplicates contribute repeatedly. Probabilistic
   bounds need explicit nonnegative weights and possibly normalization.
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
   [finite_intersection_at_most_first] (theorem) — Finite Boolean event mass and
   union/intersection inequalities.
   Mathematical meaning: Proves a Boolean-event union/intersection fact or a
   corresponding probability bound.
   Exact checked proposition: Theorem finite_intersection_at_most_first : forall
   weights samples e f, (forall x, In x samples -> 0 <= weights x) -> finite_prob
   weights samples (fun x => andb (e x) (f x)) <= finite_prob weights samples e.
   Premises and side conditions: The displayed hypotheses include nonnegative outcome
   weights; explicit nonzero or strict-positive numerical conditions; sample or list
   membership. No further assumptions are implicit.
   Proof/definition method: Kernel proof uses reuse of previously established lemmas;
   references include finite_prob_event_monotone., andb_true_iff.
   Library reuse: Stdlib.List (existsb/filter), Bool, Sorting.Permutation and
   FiniteSum.
   Boundary: Finite list semantics; duplicates contribute repeatedly. Probabilistic
   bounds need explicit nonnegative weights and possibly normalization.
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
   [finite_intersection_at_most_second] (theorem) — Finite Boolean event mass and
   union/intersection inequalities.
   Mathematical meaning: Proves a Boolean-event union/intersection fact or a
   corresponding probability bound.
   Exact checked proposition: Theorem finite_intersection_at_most_second : forall
   weights samples e f, (forall x, In x samples -> 0 <= weights x) -> finite_prob
   weights samples (fun x => andb (e x) (f x)) <= finite_prob weights samples f.
   Premises and side conditions: The displayed hypotheses include nonnegative outcome
   weights; explicit nonzero or strict-positive numerical conditions; sample or list
   membership. No further assumptions are implicit.
   Proof/definition method: Kernel proof uses reuse of previously established lemmas;
   references include finite_prob_event_monotone., andb_true_iff.
   Library reuse: Stdlib.List (existsb/filter), Bool, Sorting.Permutation and
   FiniteSum.
   Boundary: Finite list semantics; duplicates contribute repeatedly. Probabilistic
   bounds need explicit nonnegative weights and possibly normalization.
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
   [finite_frechet_lower_bound] (theorem) — Finite Boolean event mass and
   union/intersection inequalities.
   Mathematical meaning: Proves a Boolean-event union/intersection fact or a
   corresponding probability bound.
   Exact checked proposition: Theorem finite_frechet_lower_bound : forall weights
   samples e f, (forall x, In x samples -> 0 <= weights x) -> finite_sum weights
   samples = 1 -> finite_prob weights samples e + finite_prob weights samples f - 1
   <= finite_prob weights samples (fun x => andb (e x) (f x)).
   Premises and side conditions: The displayed hypotheses include unit total sample
   mass; nonnegative outcome weights; explicit nonzero or strict-positive numerical
   conditions; sample or list membership. No further assumptions are implicit.
   Proof/definition method: Kernel proof uses reuse of previously established lemmas,
   linear real arithmetic (Lra); references include finite_prob_inclusion_exclusion,
   normalized_finite_prob_unit_interval.
   Library reuse: Stdlib.List (existsb/filter), Bool, Sorting.Permutation and
   FiniteSum.
   Boundary: Finite list semantics; duplicates contribute repeatedly. Probabilistic
   bounds need explicit nonnegative weights and possibly normalization.
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


  (* This is an interpretive quotient of already-defined Boolean-event
     masses, not a new probability measure or a recursive event type.
     At zero conditioning mass R division remains a total algebraic
     expression; theorems interpreting conditionals require positivity. *)
(**
   [finite_conditional_prob] (definition) — Generic conditional probability of finite Boolean events.
   Mathematical meaning: Defines the mass of an intersection of a given event and a target event divided by the mass of the conditioning event, using the existing finite Boolean indicator model.
   Exact declaration: Definition finite_conditional_prob weights samples event given := finite_prob weights samples (fun x => andb (given x) (event x)) / finite_prob weights samples given.
   Premises and side conditions: Arbitrary real weights and repeated sample elements are syntactically permitted; interpretation as a probability requires nonnegative normalized weights and strictly positive conditioning-event mass.
   Proof/definition method: Compose the already-defined finite_prob masses with Stdlib.Bool.andb and Reals division, preserving the exact original finite enumeration.
   Library reuse: FiniteUnion.finite_prob, Stdlib.Bool.andb, Stdlib.Reals.Rdiv and FiniteSum.finite_sum.
   Boundary: No continuous measure or new event algebra is provided; zero denominators are excluded from meaningful conditional interpretations.
 *)
  Definition finite_conditional_prob (weights : Outcome -> R)
      (samples : list Outcome) (event given : Event) : R :=
    finite_prob weights samples
      (fun x => andb (given x) (event x)) /
    finite_prob weights samples given.

(**
   [finite_conditional_prob_filtered] (theorem) — Generic conditional probability of finite Boolean events.
   Mathematical meaning: Conditional mass may be computed by filtering the sample with the conditioning event, then taking the event mass on that restricted list and dividing by the original conditioning mass.
   Exact checked proposition: For all weights, samples, event and given, finite_conditional_prob weights samples event given = finite_prob weights (filter given samples) event / finite_prob weights samples given.
   Premises and side conditions: No normalization, sign assumption or positive denominator is needed for the identity as a real expression; positive mass is needed for conditional-probability semantics.
   Proof/definition method: Unfold only the new quotient definition and rewrite by the pre-existing finite_prob_on_filtered_samples theorem, which uses Stdlib.List.filter.
   Library reuse: Stdlib.List.filter, finite_prob_on_filtered_samples, finite_prob and Stdlib.Reals division.
   Boundary: Duplicates retain their multiplicity; this is not a normalized distribution conditional on a measurable set in a continuous space.
 *)
  Theorem finite_conditional_prob_filtered :
    forall weights samples event given,
      finite_conditional_prob weights samples event given =
        finite_prob weights (filter given samples) event /
        finite_prob weights samples given.
  Proof.
    intros weights samples event given.
    unfold finite_conditional_prob.
    rewrite (finite_prob_on_filtered_samples weights samples given event).
    reflexivity.
  Qed.

(**
   [finite_conditional_prob_self] (theorem) — Generic conditional probability of finite Boolean events.
   Mathematical meaning: Any strictly positive finite conditioning event has conditional probability one given itself.
   Exact checked proposition: For all weights, samples, given, if 0 < finite_prob weights samples given then finite_conditional_prob weights samples given given = 1.
   Premises and side conditions: The conditioning mass is strictly positive, making division by itself valid. Probability normalization and weight signs are not required for this algebraic identity, but are needed for general probability semantics.
   Proof/definition method: Use finite_prob_event_ext_on_samples to identify the idempotent Boolean conjunction with the original event on the enumerated support, then apply the standard real-division self-identity.
   Library reuse: Stdlib.Bool.andb, finite_prob_event_ext_on_samples, Stdlib.Reals field tactic and Lra.
   Boundary: This does not prove that arbitrary signed finite weights define a valid probability distribution.
 *)
  Theorem finite_conditional_prob_self :
    forall weights samples given,
      0 < finite_prob weights samples given ->
      finite_conditional_prob weights samples given given = 1.
  Proof.
    intros weights samples given Hpositive.
    unfold finite_conditional_prob.
    assert (Hsame :
      finite_prob weights samples
        (fun x => andb (given x) (given x)) =
      finite_prob weights samples given).
    { apply finite_prob_event_ext_on_samples.
      intros x Hx.
      destruct (given x); reflexivity. }
    rewrite Hsame.
    field; lra.
  Qed.

  (**
   [finite_conditional_prob_unit_interval] (theorem) — Generic finite conditional probability.
   Mathematical meaning: With nonnegative sample weights and a strictly positive conditioning mass, the finite conditional event mass lies between zero and one; prior normalization of the finite sample is unnecessary.
   Exact checked proposition: For all weights samples event given, nonnegative sampled weights and strictly positive finite_prob weights samples given imply 0 <= finite_conditional_prob weights samples event given <= 1.
   Premises and side conditions: Every sampled weight must be nonnegative and the conditioning event must have positive mass. The total mass need not be one because both numerator and denominator share the same unnormalized weights.
   Proof/definition method: Use finite_prob_false and finite_prob_event_monotone to bound the intersection below by zero; reuse finite_intersection_at_most_first for the upper bound, and multiply by the nonnegative inverse using standard real-number lemmas.
   Library reuse: finite_prob_false, finite_prob_event_monotone, finite_intersection_at_most_first, Stdlib.Reals.Rinv_0_lt_compat/Rmult_le_compat_r, Lra.
   Boundary: This proves a finite weighted event inequality, not abstract conditional probability for signed weights or zero-mass conditioning sets.
   *)
  Theorem finite_conditional_prob_unit_interval :
    forall weights samples event given,
      (forall x, In x samples -> 0 <= weights x) ->
      0 < finite_prob weights samples given ->
      0 <= finite_conditional_prob weights samples event given /\
      finite_conditional_prob weights samples event given <= 1.
  Proof.
    intros weights samples event given Hw Hpositive.
    assert (Hlower :
      0 <= finite_prob weights samples
        (fun x => andb (given x) (event x))).
    { rewrite <- (finite_prob_false weights samples).
      apply finite_prob_event_monotone; [exact Hw|].
      intros x _ Hfalse; discriminate Hfalse. }
    pose proof (finite_intersection_at_most_first
      weights samples given event Hw) as Hupper.
    assert (Hinv : 0 <= / finite_prob weights samples given).
    { apply Rlt_le, Rinv_0_lt_compat; exact Hpositive. }
    unfold finite_conditional_prob, Rdiv.
    split.
    - apply Rmult_le_pos; assumption.
    - replace 1 with
        (finite_prob weights samples given *
          / finite_prob weights samples given)
        by (field; lra).
      apply Rmult_le_compat_r; assumption.
  Qed.

  (**
   [finite_conditional_prob_event_ext_on_conditioned_samples] (theorem) — Generic finite conditional-event laws.
   Mathematical meaning: Two target events have equal finite conditional mass whenever they agree on sampled outcomes where the conditioning event is true; they need not agree elsewhere, even inside the original sample.
   Exact checked proposition: For all weights samples event1 event2 given, agreement of event1 and event2 on every sampled x satisfying given x = true implies finite_conditional_prob weights samples event1 given = finite_conditional_prob weights samples event2 given.
   Premises and side conditions: Outcome weights may be signed and the sample may contain repetitions; no unit-mass or strictly positive conditioning requirement is needed for equality of the algebraic quotient expressions.
   Proof/definition method: Use the established finite_prob_event_ext_on_samples on the conjunction indicators and reduce the two standard Boolean cases for the conditioning event, with no list recursion.
   Library reuse: finite_prob_event_ext_on_samples, Stdlib.Bool.andb, Stdlib.List.In, Stdlib.Reals.
   Boundary: Support-sensitive extensionality is only over the enumerated conditioning sample, not a construction of a conditional measure on an arbitrary measurable space.
   *)
  Theorem finite_conditional_prob_event_ext_on_conditioned_samples :
    forall weights samples event1 event2 given,
      (forall x, In x samples -> given x = true ->
        event1 x = event2 x) ->
      finite_conditional_prob weights samples event1 given =
      finite_conditional_prob weights samples event2 given.
  Proof.
    intros weights samples event1 event2 given Hevents.
    unfold finite_conditional_prob.
    rewrite (finite_prob_event_ext_on_samples
      weights samples
      (fun x => andb (given x) (event1 x))
      (fun x => andb (given x) (event2 x))).
    - reflexivity.
    - intros x Hx.
      destruct (given x) eqn:Hgiven; simpl.
      + rewrite (Hevents x Hx Hgiven); reflexivity.
      + reflexivity.
  Qed.

  (**
   [finite_conditional_prob_event_ext_on_samples] (theorem) — Generic finite conditional probability.
   Mathematical meaning: Replacing a conditioned target event with another Boolean predicate that agrees on each enumerated sample occurrence does not affect the conditional quotient.
   Exact checked proposition: For all weights samples event1 event2 given, event1 and event2 agreeing on In x samples implies the two finite_conditional_prob values are equal.
   Premises and side conditions: Arbitrary real weights and duplicate outcomes are allowed; no sign, normalization or positive-conditioning hypothesis is necessary for this real expression equality.
   Proof/definition method: Delegate to the stronger finite_conditional_prob_event_ext_on_conditioned_samples theorem and weaken the target-agreement premise to the conditioning support, without repeating the original Boolean case proof.
   Library reuse: finite_conditional_prob_event_ext_on_conditioned_samples, finite_prob_event_ext_on_samples, Stdlib.List.In and Stdlib.Bool.andb.
   Boundary: Agreement is needed only on explicitly enumerated finite support; there is no claim about a general measurable event space.
   *)
  Theorem finite_conditional_prob_event_ext_on_samples :
    forall weights samples event1 event2 given,
      (forall x, In x samples -> event1 x = event2 x) ->
      finite_conditional_prob weights samples event1 given =
      finite_conditional_prob weights samples event2 given.
  Proof.
    intros weights samples event1 event2 given Hevents.
    apply finite_conditional_prob_event_ext_on_conditioned_samples.
    intros x Hx _.
    apply Hevents; exact Hx.
  Qed.

  (**
   [finite_conditional_prob_complement] (theorem) — Generic finite conditional probability.
   Mathematical meaning: An event and its complement partition the conditioning event, so their finite conditional probabilities sum to one when the conditioning event has positive mass.
   Exact checked proposition: forall weights samples event given, strictly positive finite_prob weights samples given implies finite_conditional_prob weights samples event given + finite_conditional_prob weights samples (fun x => negb (event x)) given = 1.
   Premises and side conditions: The conditioning mass must be strictly positive for the quotient identity. Neither weight nonnegativity nor unit total mass is required for this algebraic equality, but probability interpretation additionally requires nonnegative weights.
   Proof/definition method: Rewrite with the existing filtered-sample conditional equality, invoke finite_prob_complement for selected outcomes, and cancel the positive selected total mass using the standard real inverse-right identity Rinv_r.
   Library reuse: Stdlib.List.filter, Bool.negb, finite_conditional_prob_filtered, finite_prob_complement, finite_prob_as_filtered_mass, Stdlib.Reals.Rinv_r.
   Boundary: The identity is about finite weighted enumeration, not a construction of a regular conditional probability or empirical independence.
   *)
  Theorem finite_conditional_prob_complement :
    forall weights samples event given,
      0 < finite_prob weights samples given ->
      finite_conditional_prob weights samples event given +
      finite_conditional_prob weights samples
        (fun x => negb (event x)) given = 1.
  Proof.
    intros weights samples event given Hpositive.
    rewrite !finite_conditional_prob_filtered.
    pose proof (finite_prob_as_filtered_mass weights samples given)
      as Hfiltered.
    rewrite Hfiltered in Hpositive.
    rewrite Hfiltered.
    unfold Rdiv.
    rewrite <- Rmult_plus_distr_r.
    rewrite (Rplus_comm
      (finite_prob weights (filter given samples) event)
      (finite_prob weights (filter given samples)
        (fun x => negb (event x)))).
    rewrite finite_prob_complement.
    apply Rinv_r; lra.
  Qed.

  (**
   [finite_conditional_prob_monotone] (theorem) — Generic finite conditional-event laws.
   Mathematical meaning: For a fixed positive-mass conditioning event and nonnegative sampled weights, strengthening the target event by implication cannot decrease its conditional mass.
   Exact checked proposition: For all weights samples event1 event2 given, nonnegative sampled weights, positive mass of given and pointwise sampled event1 implies event2 entail finite_conditional_prob weights samples event1 given <= finite_conditional_prob weights samples event2 given.
   Premises and side conditions: Nonnegativity on every enumerated outcome and a positive conditioning marginal are explicit; sample normalization, event independence and distinct outcomes are not required.
   Proof/definition method: Apply the existing finite_prob_event_monotone to the two conjunction predicates via Stdlib.Bool.andb_true_iff, then multiply by the nonnegative inverse of the common conditioning mass.
   Library reuse: finite_prob_event_monotone, Stdlib.Bool.andb_true_iff, Stdlib.Reals.Rinv_0_lt_compat/Rmult_le_compat_r, Lra.
   Boundary: The result concerns exact finite weighted event mass and does not imply conditional probabilities for signed measures or a Gaussian model.
   *)
  Theorem finite_conditional_prob_monotone :
    forall weights samples event1 event2 given,
      (forall x, In x samples -> 0 <= weights x) ->
      0 < finite_prob weights samples given ->
      (forall x, In x samples -> event1 x = true ->
        event2 x = true) ->
      finite_conditional_prob weights samples event1 given <=
      finite_conditional_prob weights samples event2 given.
  Proof.
    intros weights samples event1 event2 given Hw Hpositive Hsubset.
    unfold finite_conditional_prob, Rdiv.
    apply Rmult_le_compat_r.
    - apply Rlt_le, Rinv_0_lt_compat; exact Hpositive.
    - apply finite_prob_event_monotone; [exact Hw|].
      intros x Hx Hboth.
      apply andb_true_iff in Hboth.
      apply andb_true_iff.
      destruct Hboth as [Hgiven Hfirst].
      split; [exact Hgiven|].
      apply Hsubset with (x := x); assumption.
  Qed.

  (**
   [finite_conditional_prob_true] (theorem) — Generic finite conditional-event laws.
   Mathematical meaning: When conditioning on a positive-mass event, the always-true event has conditional mass exactly one.
   Exact checked proposition: For all weights samples given, positive finite_prob weights samples given implies finite_conditional_prob weights samples (fun _ => true) given = 1.
   Premises and side conditions: Only strictly positive conditioning mass is needed for this algebraic identity; interpreting all conditional event values probabilistically separately requires nonnegative outcome weights.
   Proof/definition method: Use the stronger conditioned-support extensionality theorem to identify the always-true target with the conditioning event on accepted outcomes, then reuse finite_conditional_prob_self; no new division algebra is performed.
   Library reuse: finite_conditional_prob_event_ext_on_conditioned_samples, finite_conditional_prob_self and Stdlib.Bool.
   Boundary: The conclusion is an exact finite-event identity, not normalization of an entire continuous or empirical distribution.
   *)
  Theorem finite_conditional_prob_true :
    forall weights samples given,
      0 < finite_prob weights samples given ->
      finite_conditional_prob weights samples (fun _ => true) given = 1.
  Proof.
    intros weights samples given Hpositive.
    transitivity (finite_conditional_prob weights samples given given).
    - apply finite_conditional_prob_event_ext_on_conditioned_samples.
      intros x _ Hgiven.
      symmetry; exact Hgiven.
    - apply finite_conditional_prob_self; exact Hpositive.
  Qed.

  (**
   [finite_conditional_prob_conditioning_ext_on_samples] (theorem) — Generic finite conditional-event laws.
   Mathematical meaning: Changing the conditioning Boolean event outside the enumerated sample does not change either its finite mass or the numerator of a finite conditional probability.
   Exact checked proposition: For all weights samples event given1 given2, equality of the two conditioning predicates on every sampled outcome implies finite_conditional_prob weights samples event given1 = finite_conditional_prob weights samples event given2.
   Premises and side conditions: The weights are arbitrary real numbers and sample repetitions remain significant; the algebraic quotient identity needs no positivity or normalized-mass hypothesis.
   Proof/definition method: Unfold the generic quotient, then reuse finite_prob_event_ext_on_samples once on the numerators and once on the conditioning marginals; no new Boolean folding or list induction is used.
   Library reuse: finite_prob_event_ext_on_samples, Stdlib.Bool.andb, Stdlib.List.In and Stdlib.Reals division.
   Boundary: This is finite-support equality of expressions and does not establish uniqueness of conditional probability outside the sampled support.
   *)
  Theorem finite_conditional_prob_conditioning_ext_on_samples :
    forall weights samples event given1 given2,
      (forall x, In x samples -> given1 x = given2 x) ->
      finite_conditional_prob weights samples event given1 =
      finite_conditional_prob weights samples event given2.
  Proof.
    intros weights samples event given1 given2 Hevents.
    unfold finite_conditional_prob.
    rewrite (finite_prob_event_ext_on_samples
      weights samples
      (fun x => andb (given1 x) (event x))
      (fun x => andb (given2 x) (event x))).
    2: { intros x Hx; rewrite (Hevents x Hx); reflexivity. }
    rewrite (finite_prob_event_ext_on_samples
      weights samples given1 given2).
    - reflexivity.
    - exact Hevents.
  Qed.

  (**
   [finite_conditional_prob_false] (theorem) — Finite conditional-event probability algebra.
   Mathematical meaning: The impossible Boolean target event has zero conditional mass for any conditioning predicate, including the algebraic zero-mass case.
   Exact checked proposition: For all weights samples given, finite_conditional_prob weights samples (fun _ => false) given = 0.
   Premises and side conditions: This is an equality of real expressions and does not need a positive conditioning denominator or nonnegative weights. A probability interpretation of conditioning itself still requires positive marginal mass.
   Proof/definition method: Reduce the conjunction with the false target by finite_prob_event_ext_on_samples, reuse the existing finite_prob_false theorem, then simplify real multiplication by zero.
   Library reuse: finite_prob_event_ext_on_samples, finite_prob_false, Stdlib.Bool.andb, Stdlib.Reals field/ring algebra.
   Boundary: The theorem concerns the totalized real-division expression on finite weighted outcomes and makes no claim that zero-mass conditioning has probabilistic semantics.
   *)
  Theorem finite_conditional_prob_false :
    forall weights samples given,
      finite_conditional_prob weights samples (fun _ => false) given = 0.
  Proof.
    intros weights samples given.
    unfold finite_conditional_prob.
    rewrite (finite_prob_event_ext_on_samples
      weights samples
      (fun x => andb (given x) false)
      (fun _ => false)).
    2: { intros x _; destruct (given x); reflexivity. }
    rewrite finite_prob_false.
    unfold Rdiv; ring.
  Qed.

  (**
   [finite_conditional_prob_inclusion_exclusion] (theorem) — Finite conditional-event probability algebra.
   Mathematical meaning: For a fixed conditioning event, conditional mass satisfies the ordinary two-event inclusion–exclusion equality for arbitrary Boolean targets.
   Exact checked proposition: For all weights samples event1 event2 given, conditional(event1 OR event2|given) + conditional(event1 AND event2|given) = conditional(event1|given) + conditional(event2|given).
   Premises and side conditions: No normalization, weight-sign assumption, or conditioning-mass positivity is needed for this algebraic equality. The usual probability interpretation requires nonnegative weights and positive conditioning mass.
   Proof/definition method: Use finite_conditional_prob_filtered for all four terms, factor out their shared inverse conditioning marginal, and apply the pre-existing finite_prob_inclusion_exclusion theorem to Stdlib.List.filter given samples.
   Library reuse: finite_conditional_prob_filtered, finite_prob_inclusion_exclusion, Stdlib.List.filter, Stdlib.Bool.orb/andb, Stdlib.Reals.Rmult_plus_distr_r.
   Boundary: Only the explicitly enumerated finite sample is covered; the theorem does not introduce a new conditional-event summation or any abstract sigma algebra.
   *)
  Theorem finite_conditional_prob_inclusion_exclusion :
    forall weights samples event1 event2 given,
      finite_conditional_prob weights samples
        (fun x => orb (event1 x) (event2 x)) given +
      finite_conditional_prob weights samples
        (fun x => andb (event1 x) (event2 x)) given =
      finite_conditional_prob weights samples event1 given +
      finite_conditional_prob weights samples event2 given.
  Proof.
    intros weights samples event1 event2 given.
    rewrite !finite_conditional_prob_filtered.
    unfold Rdiv.
    rewrite <- !Rmult_plus_distr_r.
    rewrite finite_prob_inclusion_exclusion.
    reflexivity.
  Qed.

  (**
   [finite_conditional_prob_bayes_balance] (theorem) — Finite conditional-event probability algebra.
   Mathematical meaning: The intersection mass can be reconstructed in either direction: the conditional event mass times the corresponding conditioning marginal is invariant under swapping the two events.
   Exact checked proposition: For any weights samples event1 event2, positive masses of both events imply conditional(event1|event2) * finite_prob(event2) = conditional(event2|event1) * finite_prob(event1).
   Premises and side conditions: Both conditioning event marginals must be strictly positive for cancellation. The algebraic equality does not need unit total mass or independence, and nonnegative sampled weights are only needed to interpret every quantity as a probability.
   Proof/definition method: Use finite_prob_event_ext_on_samples and Stdlib.Bool.andb_comm to identify the two intersection numerators, then cancel positive denominators with the standard Reals field tactic.
   Library reuse: finite_prob_event_ext_on_samples, Stdlib.Bool.andb_comm, Stdlib.Reals field, Stdlib.Lra.
   Boundary: This is finite-event Bayes balance, not an assumption of independence or a certified continuous conditional-density formula.
   *)
  Theorem finite_conditional_prob_bayes_balance :
    forall weights samples event1 event2,
      0 < finite_prob weights samples event1 ->
      0 < finite_prob weights samples event2 ->
      finite_conditional_prob weights samples event1 event2 *
        finite_prob weights samples event2 =
      finite_conditional_prob weights samples event2 event1 *
        finite_prob weights samples event1.
  Proof.
    intros weights samples event1 event2 Hfirst Hsecond.
    unfold finite_conditional_prob.
    rewrite (finite_prob_event_ext_on_samples
      weights samples
      (fun x => andb (event2 x) (event1 x))
      (fun x => andb (event1 x) (event2 x))).
    2: { intros x _; apply andb_comm. }
    field; lra.
  Qed.

  (**
   [finite_conditional_prob_total_probability] (theorem) — Finite conditional-event probability algebra.
   Mathematical meaning: The unconditioned mass of a target event equals the sum of its conditional masses across a Boolean partition, each weighted by its conditioning-event mass.
   Exact checked proposition: For all weights samples event given with both given and its Boolean complement of strictly positive finite mass, finite_prob(event) equals conditional(event|given)*finite_prob(given) + conditional(event|not given)*finite_prob(not given).
   Premises and side conditions: Strict positivity is required for both conditional denominators; neither unit normalization of the original sample nor nonnegative individual weights is required for the displayed algebraic identity.
   Proof/definition method: Rewrite each quotient using finite_conditional_prob_filtered, use the already proven finite_prob_filtered_partition decomposition of the original event mass, and cancel the two strictly positive denominators with the standard Reals field tactic.
   Library reuse: finite_prob_filtered_partition, finite_conditional_prob_filtered, Stdlib.List.filter, Stdlib.Bool.negb, Stdlib.Reals field, Stdlib.Lra.
   Boundary: The identity refers to an explicit finite weighted sample and does not establish existence or uniqueness of general conditional distributions.
   *)
  Theorem finite_conditional_prob_total_probability :
    forall weights samples event given,
      0 < finite_prob weights samples given ->
      0 < finite_prob weights samples (fun x => negb (given x)) ->
      finite_prob weights samples event =
        finite_conditional_prob weights samples event given *
          finite_prob weights samples given +
        finite_conditional_prob weights samples event
          (fun x => negb (given x)) *
          finite_prob weights samples (fun x => negb (given x)).
  Proof.
    intros weights samples event given Hgiven Hnot.
    rewrite !finite_conditional_prob_filtered.
    rewrite <- (finite_prob_filtered_partition
      weights samples given event).
    field; lra.
  Qed.


  (**
   [finite_conditional_prob_chain_rule] (theorem) — Generic conditional Boolean-event algebra.
   Mathematical meaning: A finite conditional intersection factors into the probability of its first component given the conditioning event multiplied by the second component conditional on the first component and the conditioning event.
   Exact checked proposition: For all weights samples event1 event2 given, positive given mass and positive mass of given AND event1 imply conditional(event1 AND event2 | given) = conditional(event1 | given) * conditional(event2 | given AND event1).
   Premises and side conditions: Both the original conditioning event and its intersection with the first target event have strictly positive finite mass. Neither total-mass normalization nor individual nonnegative weights are needed for the equality as real algebra.
   Proof/definition method: Unfold the existing conditional quotient, use the pointwise standard Boolean conjunction associativity theorem to align intersection numerators, then apply Rocq's real-field normalization with explicit denominator positivity.
   Library reuse: Stdlib.Bool.andb_assoc, finite_prob_event_ext_on_samples, Stdlib.Reals field and Stdlib.Lra.
   Boundary: Finite enumerated mass with two explicit nonzero denominators only; no continuous disintegration or conditional independence is inferred.
   *)
  Theorem finite_conditional_prob_chain_rule :
    forall weights samples event1 event2 given,
      0 < finite_prob weights samples given ->
      0 < finite_prob weights samples
        (fun x => andb (given x) (event1 x)) ->
      finite_conditional_prob weights samples
        (fun x => andb (event1 x) (event2 x)) given =
      finite_conditional_prob weights samples event1 given *
      finite_conditional_prob weights samples event2
        (fun x => andb (given x) (event1 x)).
  Proof.
    intros weights samples event1 event2 given Hgiven Hcombined.
    unfold finite_conditional_prob.
    rewrite (finite_prob_event_ext_on_samples
      weights samples
      (fun x => andb (given x)
        (andb (event1 x) (event2 x)))
      (fun x => andb (andb (given x) (event1 x)) (event2 x))).
    2: { intros x _; apply andb_assoc. }
    field; lra.
  Qed.


  (**
   [finite_conditional_prob_intersection_symmetric] (theorem) — Order invariance of conditioned event intersection.
   Mathematical meaning: Exchanging the two target events does not change their conditional intersection mass. The conditioning event is unchanged, and the result is an equality of finite real-valued quotients.
   Exact checked proposition: For arbitrary weights, samples, Boolean events first and second and conditioning event given, conditional(first AND second | given) equals conditional(second AND first | given).
   Premises and side conditions: No positivity, normalization or nonnegative-weight premise is needed for this algebraic equality. If the conditioning mass vanishes, the quotient is Rocq's totalized real division and does not represent a probability.
   Proof/definition method: Apply the previously checked finite conditional-event extensionality theorem on the sample support, discharging its pointwise Boolean goal by the standard conjunction commutativity lemma.
   Library reuse: finite_conditional_prob_event_ext_on_samples and Stdlib.Bool.andb_comm; no new sample summation or case splitting is required.
   Boundary: Only finite sampled Boolean events are covered; this supplies no conditional-independence assertion on its own.
   *)
  Theorem finite_conditional_prob_intersection_symmetric :
    forall weights samples first second given,
      finite_conditional_prob weights samples
        (fun x => andb (first x) (second x)) given =
      finite_conditional_prob weights samples
        (fun x => andb (second x) (first x)) given.
  Proof.
    intros weights samples first second given.
    apply finite_conditional_prob_event_ext_on_samples.
    intros x _.
    apply andb_comm.
  Qed.

  (**
   [finite_conditional_independent] (definition) — Independence of two Boolean events relative to a finite conditioning event.
   Mathematical meaning: Conditional independence means that the joint conditional mass factors into the product of the two conditional marginals, with strictly positive conditioning mass required as part of the predicate rather than left implicit.
   Exact declaration: finite_conditional_independent weights samples first second given is the conjunction of 0 < finite_prob weights samples given and conditional(first AND second | given) = conditional(first | given) * conditional(second | given).
   Premises and side conditions: All finite weights are real and repeated samples are counted with multiplicity. Signed weights still satisfy algebraic expressions, but nonnegative weights are needed to interpret the predicate as probabilistic conditional independence. No unit-total-mass assumption is necessary.
   Proof/definition method: Reuse the existing generic finite_prob and finite_conditional_prob operations, and the standard Boolean conjunction, as a transparent proposition without another event representation or quotient implementation.
   Library reuse: finite_prob, finite_conditional_prob, Stdlib.Bool.andb and Stdlib.Reals; no custom probability or matrix library is introduced.
   Boundary: This is exact finite conditioned factorization, not causal independence, Gaussian conditional independence, or a continuous regular conditional law.
   *)
  Definition finite_conditional_independent
      (weights : Outcome -> R) (samples : list Outcome)
      (first second given : Event) : Prop :=
    0 < finite_prob weights samples given /\
    finite_conditional_prob weights samples
      (fun x => andb (first x) (second x)) given =
    finite_conditional_prob weights samples first given *
    finite_conditional_prob weights samples second given.

  (**
   [finite_conditional_independent_symmetric] (theorem) — Symmetry of conditional independence.
   Mathematical meaning: Factorization of the joint finite conditional event mass does not privilege the order of the two events; the same strictly positive conditioning mass is retained in both directions.
   Exact checked proposition: For any finite weights, sample list, first and second Boolean events and conditioning event, finite_conditional_independent first second given holds if and only if finite_conditional_independent second first given holds.
   Premises and side conditions: Positivity of the conditioning marginal is built into the two predicates. The proof is an algebraic equivalence and does not require normalization, individual weight nonnegativity, or distinct sample elements.
   Proof/definition method: Destructure the factorization and positivity conjuncts, use the previously established conditional-intersection symmetry in each direction and commute the real product on the right.
   Library reuse: finite_conditional_prob_intersection_symmetric, Stdlib.Reals.Rmult_comm and ordinary propositional conjunction introduction.
   Boundary: This establishes a structural law for the explicitly defined finite conditional factorization; it does not claim arbitrary random-variable conditional independence.
   *)
  Theorem finite_conditional_independent_symmetric :
    forall weights samples first second given,
      finite_conditional_independent weights samples first second given <->
      finite_conditional_independent weights samples second first given.
  Proof.
    intros weights samples first second given.
    unfold finite_conditional_independent.
    split.
    - intros [Hpositive Hfactor].
      split; [exact Hpositive |].
      rewrite <- (finite_conditional_prob_intersection_symmetric
        weights samples first second given).
      rewrite Rmult_comm.
      exact Hfactor.
    - intros [Hpositive Hfactor].
      split; [exact Hpositive |].
      rewrite (finite_conditional_prob_intersection_symmetric
        weights samples first second given).
      rewrite Rmult_comm.
      exact Hfactor.
  Qed.


  (**
   [finite_conditional_independent_event_ext_on_conditioned_samples] (theorem) — Conditional-support extensionality of the first independence target.
   Mathematical meaning: A conditional-independence assertion is unchanged when its first Boolean target is replaced by another predicate that agrees only on sampled outcomes satisfying the conditioning event. Outcomes outside the conditioning event do not contribute to any of its three conditional probabilities.
   Exact checked proposition: For arbitrary weights, samples, first, replacement, second and given, agreement of first and replacement at each sampled x with given x=true implies the biconditional between conditional independence of first,second and conditional independence of replacement,second given the same event.
   Premises and side conditions: Positivity of the conditioning mass is built into both independence predicates. No unit normalization, nonnegative-weight premise or distinctness of outcomes is needed for the formal algebra; interpreting conditional masses as probabilities additionally requires nonnegative weights.
   Proof/definition method: Unfold only the existing independence proposition; rewrite the conditional joint and the first conditional marginal by the already established target-event extensionality law on conditioned support, leaving the conditioning mass and second conditional marginal unchanged.
   Library reuse: finite_conditional_prob_event_ext_on_conditioned_samples and Stdlib.Bool.andb, without new finite sums, Boolean enumeration, quotient definitions or proof axioms.
   Boundary: This is equality on the selected finite support, not almost-everywhere equality in an abstract measure space; target replacement outside this support need not preserve unconditional event mass.
   *)
  Theorem finite_conditional_independent_event_ext_on_conditioned_samples :
    forall weights samples first replacement second given,
      (forall x, In x samples -> given x = true ->
        first x = replacement x) ->
      (finite_conditional_independent weights samples first second given <->
       finite_conditional_independent weights samples replacement second given).
  Proof.
    intros weights samples first replacement second given Hagree.
    unfold finite_conditional_independent.
    rewrite (finite_conditional_prob_event_ext_on_conditioned_samples
      weights samples
      (fun x => andb (first x) (second x))
      (fun x => andb (replacement x) (second x)) given).
    2: { intros x Hx Hg; rewrite (Hagree x Hx Hg); reflexivity. }
    rewrite (finite_conditional_prob_event_ext_on_conditioned_samples
      weights samples first replacement given Hagree).
    reflexivity.
  Qed.

  (**
   [finite_conditional_independent_event_ext_on_samples] (theorem) — Support extensionality of a conditional-independence target.
   Mathematical meaning: Modifying the first target event away from the enumerated sample does not alter its conditional independence from the second event, because both its conditional marginal and their conditional intersection are unchanged.
   Exact checked proposition: If first and replacement agree at every member of samples, then conditional independence of first and second given is logically equivalent to conditional independence of replacement and second given.
   Premises and side conditions: The finite sample may repeat outcomes; positivity of the given marginal is internal to the predicate, and no further normalization or sign premise is imposed for the real algebraic equivalence.
   Proof/definition method: Refactor to invoke the stronger conditioned-support independence extensionality theorem; ordinary sampled-support agreement immediately yields the conditioned-support agreement required by that existing theorem.
   Library reuse: finite_conditional_independent_event_ext_on_conditioned_samples and Stdlib.List.In; the proof no longer unfolds independence or duplicates conditional-mass algebra.
   Boundary: This concerns agreement on the actual finite sample, not almost-everywhere equality for an external probability measure.
   *)
  Theorem finite_conditional_independent_event_ext_on_samples :
    forall weights samples first replacement second given,
      (forall x, In x samples -> first x = replacement x) ->
      (finite_conditional_independent weights samples first second given <->
       finite_conditional_independent weights samples replacement second given).
  Proof.
    intros weights samples first replacement second given Hagree.
    apply finite_conditional_independent_event_ext_on_conditioned_samples.
    intros x Hx _.
    exact (Hagree x Hx).
  Qed.

  (**
   [finite_conditional_independent_conditioning_ext_on_samples] (theorem) — Support extensionality of the conditioning event.
   Mathematical meaning: Two conditioning predicates that agree on the finite list of sampled outcomes yield the same positivity premise and conditional factorization, hence exactly the same conditional-independence assertion.
   Exact checked proposition: If given1 and given2 agree at every sample occurrence, conditional independence of first and second given1 holds if and only if the corresponding conditional independence given2 holds.
   Premises and side conditions: The positive-conditioning condition is preserved by support equality. This is an exact finite quotient identity for arbitrary signed weights; probability semantics additionally require nonnegative sample weights.
   Proof/definition method: Unfold the independence predicate, rewrite the conditioning marginal with finite_prob_event_ext_on_samples and then rewrite the three conditional terms via the existing conditioning support-extensionality theorem.
   Library reuse: finite_prob_event_ext_on_samples and finite_conditional_prob_conditioning_ext_on_samples, plus Stdlib.List.In and Stdlib.Bool.andb.
   Boundary: The result is restricted to enumerated finite outcome lists and does not identify conditional measures outside their sampled support.
   *)
  Theorem finite_conditional_independent_conditioning_ext_on_samples :
    forall weights samples first second given1 given2,
      (forall x, In x samples -> given1 x = given2 x) ->
      (finite_conditional_independent weights samples first second given1 <->
       finite_conditional_independent weights samples first second given2).
  Proof.
    intros weights samples first second given1 given2 Hagree.
    unfold finite_conditional_independent.
    rewrite (finite_prob_event_ext_on_samples
      weights samples given1 given2 Hagree).
    rewrite (finite_conditional_prob_conditioning_ext_on_samples
      weights samples
      (fun x => andb (first x) (second x)) given1 given2 Hagree).
    rewrite (finite_conditional_prob_conditioning_ext_on_samples
      weights samples first given1 given2 Hagree).
    rewrite (finite_conditional_prob_conditioning_ext_on_samples
      weights samples second given1 given2 Hagree).
    reflexivity.
  Qed.



  (**
   [finite_conditional_independent_second_event_ext_on_conditioned_samples] (theorem) — Conditional-support extensionality of the second independence target.
   Mathematical meaning: Replacing the second independence target on outcomes outside a positive or zero-mass conditioning selector cannot change its conditional independence from the first event, provided the replacement agrees on every enumerated outcome where the conditioning predicate is true.
   Exact checked proposition: For any finite weighted samples, first, second, replacement and given, support agreement of second and replacement restricted to given=true implies conditional independence first,second given iff conditional independence first,replacement given.
   Premises and side conditions: The source and target independence predicates both require positive conditioning mass, but no additional positivity or total-mass normalization is imposed for the Boolean event equality; repeated samples are allowed.
   Proof/definition method: Rewrite both sides by the already checked symmetry biconditional, making the second targets into first targets, then delegate to finite_conditional_independent_event_ext_on_conditioned_samples without repeating conditional quotient calculations.
   Library reuse: finite_conditional_independent_symmetric, finite_conditional_independent_event_ext_on_conditioned_samples and Stdlib propositional iff rewriting.
   Boundary: Exact finite conditioning-support invariance only; it makes no claim about continuous conditional laws or unobserved outcomes in a different finite list.
   *)
  Theorem finite_conditional_independent_second_event_ext_on_conditioned_samples :
    forall weights samples first second replacement given,
      (forall x, In x samples -> given x = true ->
        second x = replacement x) ->
      (finite_conditional_independent weights samples first second given <->
       finite_conditional_independent weights samples first replacement given).
  Proof.
    intros weights samples first second replacement given Hagree.
    rewrite (finite_conditional_independent_symmetric
      weights samples first second given).
    rewrite (finite_conditional_independent_symmetric
      weights samples first replacement given).
    apply finite_conditional_independent_event_ext_on_conditioned_samples.
    exact Hagree.
  Qed.

  (**
   [finite_conditional_independent_second_event_ext_on_samples] (theorem) — Support extensionality of the second independence target.
   Mathematical meaning: Replacing the second target event by one agreeing at every enumerated sample preserves conditional independence with the first event. The property follows from symmetry instead of duplicating the first-event proof.
   Exact checked proposition: For every weights and samples and first, second, replacement and given Boolean events, agreement of second and replacement on every sampled outcome gives an iff between independence of first with second and first with replacement given the same conditioning predicate.
   Premises and side conditions: The conditioning mass is required to be positive by the definition of conditional independence. Signed weights and repeated samples do not obstruct this purely algebraic extensionality result, although nonnegative weights are needed for probabilistic interpretation.
   Proof/definition method: Rewrite both sides using the already checked symmetry equivalence, then apply first-event support extensionality. This avoids another conjunction case analysis and another finite-sum proof.
   Library reuse: finite_conditional_independent_symmetric and finite_conditional_independent_event_ext_on_samples, with no additional mathematical infrastructure.
   Boundary: Equality is only required on sampled outcomes; this does not establish measure-theoretic almost-everywhere independence.
   *)
  Theorem finite_conditional_independent_second_event_ext_on_samples :
    forall weights samples first second replacement given,
      (forall x, In x samples -> second x = replacement x) ->
      (finite_conditional_independent weights samples first second given <->
       finite_conditional_independent weights samples first replacement given).
  Proof.
    intros weights samples first second replacement given Hagree.
    rewrite (finite_conditional_independent_symmetric
      weights samples first second given).
    rewrite (finite_conditional_independent_symmetric
      weights samples first replacement given).
    apply finite_conditional_independent_event_ext_on_samples.
    exact Hagree.
  Qed.

  (**
   [finite_conditional_independent_sample_permutation] (theorem) — Permutation invariance of finite conditional independence.
   Mathematical meaning: Reordering the finite list of weighted outcomes cannot change the strictly positive conditioning mass or any of the three finite conditional event masses defining conditional independence.
   Exact checked proposition: For arbitrary weights, sample lists left and right, two target events and a conditioning event, Stdlib.Permutation left right implies conditional independence on left iff conditional independence on right.
   Premises and side conditions: The two lists contain the same occurrences including multiplicity; they need not be duplicate-free or normalized. The result is algebraic for signed weights, with conditional-probability semantics depending on the usual nonnegative-weight assumption.
   Proof/definition method: Unfold the independence and conditional quotient wrappers, rewrite the conditioning marginal and the three conditional intersection numerators with finite_prob_sample_permutation, then discharge both sides by reflexivity.
   Library reuse: finite_prob_sample_permutation and FiniteSum.finite_sum_permutation via Stdlib.Sorting.Permutation. No additional list induction, sum or probability construction is introduced.
   Boundary: A permutation only reorders the existing weighted multiset; it does not justify arbitrary reweighting or dropping sample occurrences.
   *)
  Theorem finite_conditional_independent_sample_permutation :
    forall weights left right first second given,
      Permutation left right ->
      (finite_conditional_independent weights left first second given <->
       finite_conditional_independent weights right first second given).
  Proof.
    intros weights left right first second given Hperm.
    unfold finite_conditional_independent, finite_conditional_prob.
    repeat rewrite (finite_prob_sample_permutation
      weights left right given Hperm).
    rewrite (finite_prob_sample_permutation weights left right
      (fun x => andb (given x) (andb (first x) (second x))) Hperm).
    rewrite (finite_prob_sample_permutation weights left right
      (fun x => andb (given x) (first x)) Hperm).
    rewrite (finite_prob_sample_permutation weights left right
      (fun x => andb (given x) (second x)) Hperm).
    reflexivity.
  Qed.


  (**
   [finite_conditional_prob_partition_by_event] (theorem) — Finite conditional event partition.
   Mathematical meaning: Every target event splits into disjoint parts according to whether another Boolean event holds; the two conditional masses sum to the original target's conditional mass.
   Exact checked proposition: For any finite weights, samples, target, partition and given, conditional(target AND partition | given) + conditional(target AND NOT partition | given) = conditional(target | given).
   Premises and side conditions: Neither normalization nor nonnegative weights nor positive conditioning mass is needed for this algebraic identity of real quotients. Probability semantics still require a positive conditioning marginal and nonnegative sampled weights.
   Proof/definition method: Specialize the previously checked conditional inclusion–exclusion theorem to the two partition components, show by exhaustive standard Boolean evaluation that their union is target and their intersection is false, beta-normalize the specialized event lambdas before rewriting, and use the existing conditional-false theorem.
   Library reuse: finite_conditional_prob_inclusion_exclusion, finite_conditional_prob_event_ext_on_samples, finite_conditional_prob_false, Stdlib.Bool.andb/orb/negb and Stdlib.Lra.
   Boundary: The result handles the exact enumerated weighted multiset; it does not construct conditional distributions on infinite sample spaces.
   *)
  Theorem finite_conditional_prob_partition_by_event :
    forall weights samples target partition given,
      finite_conditional_prob weights samples
        (fun x => andb (target x) (partition x)) given +
      finite_conditional_prob weights samples
        (fun x => andb (target x) (negb (partition x))) given =
      finite_conditional_prob weights samples target given.
  Proof.
    intros weights samples target partition given.
    pose proof (finite_conditional_prob_inclusion_exclusion
      weights samples
      (fun x => andb (target x) (partition x))
      (fun x => andb (target x) (negb (partition x)))
      given) as Hinclusion.
    assert (Hunion :
      finite_conditional_prob weights samples
        (fun x => orb
          (andb (target x) (partition x))
          (andb (target x) (negb (partition x)))) given =
      finite_conditional_prob weights samples target given).
    { apply finite_conditional_prob_event_ext_on_samples.
      intros x _.
      destruct (target x), (partition x); reflexivity. }
    assert (Hintersection :
      finite_conditional_prob weights samples
        (fun x => andb
          (andb (target x) (partition x))
          (andb (target x) (negb (partition x)))) given = 0).
    { rewrite (finite_conditional_prob_event_ext_on_samples
        weights samples
        (fun x => andb
          (andb (target x) (partition x))
          (andb (target x) (negb (partition x))))
        (fun _ => false) given).
      - apply finite_conditional_prob_false.
      - intros x _.
        destruct (target x), (partition x); reflexivity. }
    cbn beta in Hinclusion.
    rewrite Hunion, Hintersection in Hinclusion.
    lra.
  Qed.

  (**
   [finite_conditional_independent_complement_first] (theorem) — Conditional independence is closed under complementing the first target.
   Mathematical meaning: If two finite Boolean events are conditionally independent, replacing the first event by its Boolean complement preserves conditional independence with the same second event and conditioning event.
   Exact checked proposition: finite_conditional_independent first second given implies finite_conditional_independent (NOT first) second given for any weighted finite sample.
   Premises and side conditions: The given event's positive mass is part of the assumed independence predicate. The argument is algebraic for arbitrary real weights; interpreting independence probabilistically additionally requires nonnegative sample weights.
   Proof/definition method: Partition the second target into its intersections with first and NOT first, use the existing conditional complement identity and joint-event symmetry, then combine the supplied product factorization by nonlinear real polynomial arithmetic.
   Library reuse: finite_conditional_prob_partition_by_event, finite_conditional_prob_complement, finite_conditional_prob_intersection_symmetric, Stdlib.Psatz.nra.
   Boundary: This is Boolean-event complement closure for the specified finite weighted model, not conditional independence of arbitrary measurable random variables.
   *)
  Theorem finite_conditional_independent_complement_first :
    forall weights samples first second given,
      finite_conditional_independent weights samples first second given ->
      finite_conditional_independent weights samples
        (fun x => negb (first x)) second given.
  Proof.
    intros weights samples first second given Hindependent.
    unfold finite_conditional_independent in *.
    destruct Hindependent as [Hpositive Hfactor].
    split; [exact Hpositive |].
    pose proof (finite_conditional_prob_partition_by_event
      weights samples second first given) as Hpartition.
    pose proof (finite_conditional_prob_complement
      weights samples first given Hpositive) as Hcomplement.
    rewrite (finite_conditional_prob_intersection_symmetric
      weights samples (fun x => negb (first x)) second given).
    rewrite <- (finite_conditional_prob_intersection_symmetric
      weights samples first second given) in Hpartition.
    nra.
  Qed.

  (**
   [finite_conditional_independent_complement_second] (theorem) — Conditional independence is closed under complementing the second target.
   Mathematical meaning: Complementing the second Boolean target has the same independence-preserving property as complementing the first, without repeating the finite conditional partition arithmetic.
   Exact checked proposition: finite_conditional_independent first second given implies finite_conditional_independent first (NOT second) given, with all weights and the finite outcome list preserved.
   Premises and side conditions: Positive conditioning mass remains implicit in the source and destination predicates; individual weights may be signed for the algebraic implication, though nonnegative weights are needed for probability semantics.
   Proof/definition method: Swap targets by the already proved symmetry equivalence, apply the first-target complement theorem, and swap back. No new Boolean case split, sample induction or polynomial manipulation is introduced.
   Library reuse: finite_conditional_independent_symmetric and finite_conditional_independent_complement_first.
   Boundary: The result concerns finite conditional factorization only; it is not a Gaussian or continuous independence theorem.
   *)
  Theorem finite_conditional_independent_complement_second :
    forall weights samples first second given,
      finite_conditional_independent weights samples first second given ->
      finite_conditional_independent weights samples first
        (fun x => negb (second x)) given.
  Proof.
    intros weights samples first second given Hindependent.
    apply (proj2 (finite_conditional_independent_symmetric
      weights samples first (fun x => negb (second x)) given)).
    apply (finite_conditional_independent_complement_first
      weights samples second first given).
    apply (proj1 (finite_conditional_independent_symmetric
      weights samples first second given)).
    exact Hindependent.
  Qed.

  (**
   [finite_conditional_independent_complement_both] (theorem) — Closure under simultaneous complementation.
   Mathematical meaning: If a pair of events conditionally factorizes, then the pair of complementary events also conditionally factorizes under the same strictly positive conditioning event.
   Exact checked proposition: finite_conditional_independent first second given implies finite_conditional_independent (NOT first) (NOT second) given for arbitrary finite weights and samples.
   Premises and side conditions: The same positivity condition for the given event is preserved in all steps, and the weighted sample multiset is unchanged. No unconditional independence, normalization or distinct-outcome hypothesis is silently supplied.
   Proof/definition method: Compose the two one-sided conditional complement closure lemmas, applying each exactly once and leaving the already verified probability algebra untouched.
   Library reuse: finite_conditional_independent_complement_first and finite_conditional_independent_complement_second.
   Boundary: This is a discrete Boolean factorization law and does not automatically extend to arbitrary transformations of random variables.
   *)
  Theorem finite_conditional_independent_complement_both :
    forall weights samples first second given,
      finite_conditional_independent weights samples first second given ->
      finite_conditional_independent weights samples
        (fun x => negb (first x))
        (fun x => negb (second x)) given.
  Proof.
    intros weights samples first second given Hindependent.
    apply (finite_conditional_independent_complement_first
      weights samples first (fun x => negb (second x)) given).
    apply (finite_conditional_independent_complement_second
      weights samples first second given).
    exact Hindependent.
  Qed.


  (**
   [finite_conditional_prob_given_true_normalized] (theorem) — Conditional mass on the certain event.
   Mathematical meaning: When the total finite sample weight is exactly one, conditioning a target Boolean event on the universally true event leaves its finite mass unchanged.
   Exact checked proposition: For any real-valued weights, samples and target event, finite_sum weights samples=1 implies finite_conditional_prob weights samples event (fun _ => true)=finite_prob weights samples event.
   Premises and side conditions: Unit total mass is assumed explicitly. No nonnegative-weight premise is needed for the algebraic quotient identity, although such a premise is needed to interpret the finite weights as probabilities.
   Proof/definition method: Unfold the existing conditional quotient, simplify conjunction with the true predicate using checked event extensionality, use finite_prob_true for its denominator, and discharge division by the unit mass using the standard real field tactic.
   Library reuse: finite_prob_event_ext_on_samples, finite_prob_true, Stdlib.Bool.andb and the Stdlib.Reals field tactic. No new normalization routine or summation is defined.
   Boundary: This concerns a weighted finite outcome list and does not provide a general measure-theoretic conditioning operator.
   *)
  Theorem finite_conditional_prob_given_true_normalized :
    forall weights samples event,
      finite_sum weights samples = 1 ->
      finite_conditional_prob weights samples event (fun _ => true) =
      finite_prob weights samples event.
  Proof.
    intros weights samples event Hunit.
    unfold finite_conditional_prob.
    rewrite (finite_prob_event_ext_on_samples
      weights samples (fun x => andb true (event x)) event).
    2: { intros x _; reflexivity. }
    rewrite finite_prob_true.
    rewrite Hunit.
    field; lra.
  Qed.

  (**
   [finite_conditional_independent_given_true_iff_marginal_product] (theorem) — Normalized unconditional independence as conditional independence.
   Mathematical meaning: In an explicitly normalized finite sample, the generic conditional-independence predicate with universally true conditioning event coincides exactly with the classical joint-mass product identity for the two Boolean events.
   Exact checked proposition: For weights and samples with finite_sum weights samples=1, finite_conditional_independent weights samples first second (fun _ => true) iff finite_prob weights samples (fun x => andb (first x) (second x)) = finite_prob weights samples first * finite_prob weights samples second.
   Premises and side conditions: The mass-normalization hypothesis ensures strictly positive true-event conditioning mass. No marginal positivity, independence or individual nonnegative-weight assumption is silently added; nonnegative weights are needed for probability interpretation.
   Proof/definition method: Unfold the independence predicate, rewrite the true-event marginal to unit mass, and reuse finite_conditional_prob_given_true_normalized on the joint and both single-event target expressions before splitting the iff.
   Library reuse: finite_conditional_prob_given_true_normalized, finite_prob_true, Stdlib.Reals and Stdlib.Lra; there is no duplicate finite conditional quotient proof.
   Boundary: This is an equality of finite event masses and does not establish stochastic independence for empirical IQ tests or continuous distributions.
   *)
  Theorem finite_conditional_independent_given_true_iff_marginal_product :
    forall weights samples first second,
      finite_sum weights samples = 1 ->
      (finite_conditional_independent weights samples
         first second (fun _ => true) <->
       finite_prob weights samples
         (fun x => andb (first x) (second x)) =
       finite_prob weights samples first *
       finite_prob weights samples second).
  Proof.
    intros weights samples first second Hunit.
    unfold finite_conditional_independent.
    rewrite finite_prob_true.
    rewrite Hunit.
    rewrite (finite_conditional_prob_given_true_normalized
      weights samples
      (fun x => andb (first x) (second x)) Hunit).
    rewrite (finite_conditional_prob_given_true_normalized
      weights samples first Hunit).
    rewrite (finite_conditional_prob_given_true_normalized
      weights samples second Hunit).
    split.
    - intros [_ Hfactor].
      exact Hfactor.
    - intro Hfactor.
      split; [lra | exact Hfactor].
  Qed.


  (**
   [finite_conditional_independent_true_first] (theorem) — The certain Boolean event is conditionally independent of every event.
   Mathematical meaning: The always-true target contributes conditional mass one, and its intersection with an arbitrary target coincides with that target. Consequently the product factorization required by conditional independence holds identically.
   Exact checked proposition: For any finite real weights, samples, second target and given event, positive finite mass of given implies finite_conditional_independent weights samples (fun _ => true) second given.
   Premises and side conditions: Strict positivity of the conditioning mass is explicit; no unit normalization or weight-sign restriction is necessary for this algebraic statement. Repeated samples retain multiplicity.
   Proof/definition method: Reduce the intersection through the existing finite conditional target-event extensionality theorem, rewrite the certain-event conditional mass to one, and close the real product identity with the standard ring tactic.
   Library reuse: finite_conditional_prob_event_ext_on_samples, finite_conditional_prob_true and Stdlib.Reals ring; no new event sum, Boolean recursion or quotient is introduced.
   Boundary: This is exact factorization for the certain Boolean event, not evidence that two nontrivial admissions events are independent.
   *)
  Theorem finite_conditional_independent_true_first :
    forall weights samples second given,
      0 < finite_prob weights samples given ->
      finite_conditional_independent weights samples
        (fun _ => true) second given.
  Proof.
    intros weights samples second given Hgiven.
    unfold finite_conditional_independent.
    split; [exact Hgiven |].
    rewrite (finite_conditional_prob_event_ext_on_samples
      weights samples
      (fun x => andb true (second x)) second given).
    2: { intros x _; reflexivity. }
    rewrite (finite_conditional_prob_true weights samples given Hgiven).
    ring.
  Qed.

  (**
   [finite_conditional_independent_true_second] (theorem) — The certain event in the second target position.
   Mathematical meaning: A finite Boolean target remains conditionally independent of the always-true event, irrespective of which target appears first in the factorization equation.
   Exact checked proposition: For any finite real weights, samples, first target and given event with strictly positive conditioning mass, finite_conditional_independent weights samples first (fun _ => true) given.
   Premises and side conditions: The same strictly positive conditioning mass is assumed. Arbitrary signed weights are accepted for algebraic equality, but nonnegative weights are required for probability semantics.
   Proof/definition method: Reuse the previously proved target symmetry biconditional and finite_conditional_independent_true_first, with no further computation or Boolean case split.
   Library reuse: finite_conditional_independent_symmetric and finite_conditional_independent_true_first; no duplicated quotient or proof of certain-event mass.
   Boundary: Only exact finite conditional Boolean-event algebra is asserted.
   *)
  Theorem finite_conditional_independent_true_second :
    forall weights samples first given,
      0 < finite_prob weights samples given ->
      finite_conditional_independent weights samples
        first (fun _ => true) given.
  Proof.
    intros weights samples first given Hgiven.
    apply (proj2 (finite_conditional_independent_symmetric
      weights samples first (fun _ => true) given)).
    apply finite_conditional_independent_true_first.
    exact Hgiven.
  Qed.

  (**
   [finite_conditional_independent_false_first] (theorem) — The impossible Boolean event is conditionally independent of every event.
   Mathematical meaning: The always-false target has zero conditional mass and zero intersection with every second target, making the required conditional product factorization identically zero.
   Exact checked proposition: Given any weighted finite list and Boolean target second, positive mass of given implies finite_conditional_independent weights samples (fun _ => false) second given.
   Premises and side conditions: Positive conditioning mass is required by the independence predicate. The algebraic cancellation itself is valid for arbitrary weights, without normalization, distinct samples or nonnegative-weight assumptions.
   Proof/definition method: Use existing conditional target-event extensionality to replace the intersection with false, reuse the general conditional-false theorem on both the joint and first marginal, then normalize zero products by the Stdlib ring tactic.
   Library reuse: finite_conditional_prob_event_ext_on_samples, finite_conditional_prob_false, Stdlib.Bool.andb and Stdlib.Reals ring.
   Boundary: An impossible target is a degenerate example; no independence of nontrivial events is established.
   *)
  Theorem finite_conditional_independent_false_first :
    forall weights samples second given,
      0 < finite_prob weights samples given ->
      finite_conditional_independent weights samples
        (fun _ => false) second given.
  Proof.
    intros weights samples second given Hgiven.
    unfold finite_conditional_independent.
    split; [exact Hgiven |].
    rewrite (finite_conditional_prob_event_ext_on_samples
      weights samples
      (fun x => andb false (second x)) (fun _ => false) given).
    2: { intros x _; reflexivity. }
    rewrite (finite_conditional_prob_false weights samples given).
    ring.
  Qed.

  (**
   [finite_conditional_independent_false_second] (theorem) — The impossible event in the second target position.
   Mathematical meaning: Conditional independence of the impossible Boolean event with an arbitrary target remains valid after swapping the two event positions.
   Exact checked proposition: For all weights, sample lists, first targets and positive-mass conditioning events, finite_conditional_independent weights samples first (fun _ => false) given.
   Premises and side conditions: Only positive mass of the conditioning event is needed to satisfy the definition; arbitrary real weights and repeated sample occurrences are accepted algebraically.
   Proof/definition method: Apply the checked independence-symmetry biconditional to the existing impossible-first theorem, rather than repeating Boolean simplification or zero-product algebra.
   Library reuse: finite_conditional_independent_symmetric and finite_conditional_independent_false_first.
   Boundary: This verifies a degenerate finite-event independence property, not a statistical hypothesis about observed data.
   *)
  Theorem finite_conditional_independent_false_second :
    forall weights samples first given,
      0 < finite_prob weights samples given ->
      finite_conditional_independent weights samples
        first (fun _ => false) given.
  Proof.
    intros weights samples first given Hgiven.
    apply (proj2 (finite_conditional_independent_symmetric
      weights samples first (fun _ => false) given)).
    apply finite_conditional_independent_false_first.
    exact Hgiven.
  Qed.


  (**
   [finite_conditional_independent_iff_cross_product_mass] (theorem) — A denominator-free criterion for finite conditional independence.
   Mathematical meaning: For a strictly positive conditioning mass, the product factorization of conditional event probabilities is equivalent to a cross-product equality of four unnormalized finite event masses: the mass of G∩A∩B times the mass of G equals the product of the masses of G∩A and G∩B.
   Exact checked proposition: For arbitrary real weights, sample list, first, second and given Boolean events with finite_prob given positive, finite_conditional_independent first second given iff finite_prob(G AND (A AND B))*finite_prob(G)=finite_prob(G AND A)*finite_prob(G AND B).
   Premises and side conditions: The conditioning mass must be strictly positive to cancel denominators; total sample mass need not equal one. Individual weights may be signed for this exact real-algebra equivalence, but require nonnegativity for probabilistic meaning. Duplicate outcomes retain their contributions.
   Proof/definition method: Unfold the already defined conditional quotient and independence predicate, abbreviate the four event masses, and multiply or divide each side by the square of the positive conditioning mass. Use Stdlib.Reals field algebra to cancel the nonzero denominator rather than introducing a new conditional-probability operator.
   Library reuse: finite_prob, finite_conditional_prob, finite_conditional_independent, Stdlib.Bool.andb, Stdlib.Reals field and Stdlib.Lra; there is no new finite sum, enumeration or recursive event construction.
   Boundary: The result characterizes a single finite Boolean conditional-independence assertion; it does not prove Gaussian conditional independence, a causal relationship, or conditional random-variable disintegration.
   *)
  Theorem finite_conditional_independent_iff_cross_product_mass :
    forall weights samples first second given,
      0 < finite_prob weights samples given ->
      (finite_conditional_independent weights samples
         first second given <->
       finite_prob weights samples
         (fun x => andb (given x) (andb (first x) (second x))) *
         finite_prob weights samples given =
       finite_prob weights samples
         (fun x => andb (given x) (first x)) *
       finite_prob weights samples
         (fun x => andb (given x) (second x))).
  Proof.
    intros weights samples first second given Hgiven.
    unfold finite_conditional_independent, finite_conditional_prob.
    cbn beta.
    set (d := finite_prob weights samples given) in *.
    set (j := finite_prob weights samples
      (fun x => andb (given x) (andb (first x) (second x)))) in *.
    set (a := finite_prob weights samples
      (fun x => andb (given x) (first x))) in *.
    set (b := finite_prob weights samples
      (fun x => andb (given x) (second x))) in *.
    split.
    - intros [_ Hfactor].
      apply (f_equal (fun z : R => z * d * d)) in Hfactor.
      replace (j / d * d * d) with (j * d) in Hfactor
        by (field; lra).
      replace ((a / d * (b / d)) * d * d) with (a * b)
        in Hfactor by (field; lra).
      exact Hfactor.
    - intro Hcross.
      split; [exact Hgiven |].
      apply (f_equal (fun z : R => z / (d * d))) in Hcross.
      replace (j * d / (d * d)) with (j / d)
        in Hcross by (field; lra).
      replace (a * b / (d * d)) with (a / d * (b / d))
        in Hcross by (field; lra).
      exact Hcross.
  Qed.


  (**
   [finite_conditional_independent_conditioning_first] (theorem) — An event is conditionally independent of every event when conditioned on itself.
   Mathematical meaning: Inside the conditioning event G, the first target G is necessarily true, so G and an arbitrary second target factor conditionally when G has positive finite mass.
   Exact checked proposition: For any weights, samples, second Boolean event and conditioning Boolean event given of strictly positive finite mass, finite_conditional_independent weights samples given second given.
   Premises and side conditions: Positive mass of given is required. All other equalities are valid for arbitrary signed or repeated finite weights; nonnegative weights are additionally necessary for a probabilistic interpretation.
   Proof/definition method: Apply the checked conditional-event extensionality theorem on the selected conditioning support to identify G∩second with second; reuse finite_conditional_prob_self to give the first target unit conditional mass and finish with Stdlib's ring tactic.
   Library reuse: finite_conditional_prob_event_ext_on_conditioned_samples, finite_conditional_prob_self, Stdlib.Bool.andb and Stdlib.Reals ring.
   Boundary: This is a conditioning tautology, not a claim that the unconditioned events are independent or that an event is independent of its own complement.
   *)
  Theorem finite_conditional_independent_conditioning_first :
    forall weights samples second given,
      0 < finite_prob weights samples given ->
      finite_conditional_independent weights samples given second given.
  Proof.
    intros weights samples second given Hgiven.
    unfold finite_conditional_independent.
    split; [exact Hgiven |].
    rewrite (finite_conditional_prob_event_ext_on_conditioned_samples
      weights samples (fun x => andb (given x) (second x))
      second given).
    2: { intros x _ Hx; rewrite Hx; reflexivity. }
    rewrite (finite_conditional_prob_self weights samples given Hgiven).
    ring.
  Qed.

  (**
   [finite_conditional_independent_conditioning_second] (theorem) — Conditioning-event independence with the second target fixed to the conditioning event.
   Mathematical meaning: If one target is identical to the positive-mass conditioning event, it has conditional mass one, and the conditional independence factorization is valid in either target order.
   Exact checked proposition: For every weights and samples, first Boolean target and conditioning event given with positive finite mass, finite_conditional_independent weights samples first given given.
   Premises and side conditions: Only positive conditioning mass is required for the exact finite algebraic statement; the weights may be signed, and the same repeated sample occurrences are preserved.
   Proof/definition method: Project the already checked symmetry biconditional and invoke finite_conditional_independent_conditioning_first instead of duplicating conditional support extensionality or quotient calculations.
   Library reuse: finite_conditional_independent_symmetric and finite_conditional_independent_conditioning_first.
   Boundary: This is a finite Boolean conditioning identity, not general causal independence or a continuous conditional probability theorem.
   *)
  Theorem finite_conditional_independent_conditioning_second :
    forall weights samples first given,
      0 < finite_prob weights samples given ->
      finite_conditional_independent weights samples first given given.
  Proof.
    intros weights samples first given Hgiven.
    apply (proj2 (finite_conditional_independent_symmetric
      weights samples first given given)).
    apply finite_conditional_independent_conditioning_first.
    exact Hgiven.
  Qed.

  (**
   [finite_conditional_independent_union_formula] (theorem) — Conditional two-event union under independence.
   Mathematical meaning: If two finite Boolean targets are conditionally independent given G, their conditional union mass is the sum of their conditional marginals minus the product of those marginals, just as in the elementary independent-event formula.
   Exact checked proposition: finite_conditional_independent weights samples first second given implies finite_conditional_prob weights samples (fun x => orb (first x) (second x)) given = finite_conditional_prob first given + finite_conditional_prob second given - finite_conditional_prob first given * finite_conditional_prob second given.
   Premises and side conditions: Positive mass of G follows from the independence predicate. No total-mass normalization, target-marginal positivity or weight-sign condition is needed for the algebraic formula; interpreting it as probability requires nonnegative weights.
   Proof/definition method: Instantiate the previously checked conditional inclusion–exclusion theorem; rewrite its intersection term using the factored conditional mass in the independence predicate, then rearrange the resulting real equality with Stdlib.Lra.
   Library reuse: finite_conditional_prob_inclusion_exclusion, finite_conditional_independent, Stdlib.Bool.orb/andb, Stdlib.Lra. No new enumeration, inclusion–exclusion proof or independent-union recursion is introduced.
   Boundary: This is a two-target union formula under an explicit finite conditional-independence premise; it does not imply that arbitrary families of events are mutually independent.
   *)
  Theorem finite_conditional_independent_union_formula :
    forall weights samples first second given,
      finite_conditional_independent weights samples first second given ->
      finite_conditional_prob weights samples
        (fun x => orb (first x) (second x)) given =
      finite_conditional_prob weights samples first given +
      finite_conditional_prob weights samples second given -
      finite_conditional_prob weights samples first given *
      finite_conditional_prob weights samples second given.
  Proof.
    intros weights samples first second given Hindependent.
    destruct Hindependent as [_ Hfactor].
    pose proof (finite_conditional_prob_inclusion_exclusion
      weights samples first second given) as Hinclusion.
    rewrite Hfactor in Hinclusion.
    lra.
  Qed.


  (**
   [finite_conditional_three_event_product] (theorem) — A three-target conditional product rule under explicit independence premises.
   Mathematical meaning: A conditional joint mass of three Boolean events factors into the product of their three conditional marginals when A and B are conditionally independent given G and the conjunction A∩B is conditionally independent of C given that same G.
   Exact checked proposition: If finite_conditional_independent first second given and finite_conditional_independent (fun x => andb (first x) (second x)) third given, then finite_conditional_prob (fun x => andb (first x) (andb (second x) (third x))) given = finite_conditional_prob first given * finite_conditional_prob second given * finite_conditional_prob third given.
   Premises and side conditions: Both explicit conditional-independence predicates include positive conditioning mass. The second premise is independence of the combined first two targets from the third; merely assuming three pairwise independence statements would not suffice. Real signed weights support the algebra, while nonnegative weights are needed for the probability interpretation.
   Proof/definition method: Use the standard Boolean conjunction associativity lemma and the established conditional target extensionality theorem to regroup the triple intersection. Rewrite by the second factorization and then by the first, finishing with Stdlib's ring tactic.
   Library reuse: finite_conditional_prob_event_ext_on_samples, finite_conditional_independent, Stdlib.Bool.andb_assoc and Stdlib.Reals ring; no custom list recursion, multievent probability operator, conditional quotient or independence axiom is introduced.
   Boundary: This checks a finite three-target factorization under two specified independence hypotheses; it does not assert that pairwise independence implies mutual independence, nor does it construct an arbitrary-event joint distribution.
   *)
  Theorem finite_conditional_three_event_product :
    forall weights samples first second third given,
      finite_conditional_independent weights samples
        first second given ->
      finite_conditional_independent weights samples
        (fun x => andb (first x) (second x)) third given ->
      finite_conditional_prob weights samples
        (fun x => andb (first x) (andb (second x) (third x))) given =
      finite_conditional_prob weights samples first given *
      finite_conditional_prob weights samples second given *
      finite_conditional_prob weights samples third given.
  Proof.
    intros weights samples first second third given Hind12 Hindpair.
    destruct Hind12 as [_ H12].
    destruct Hindpair as [_ Hpair].
    rewrite (finite_conditional_prob_event_ext_on_samples
      weights samples
      (fun x => andb (first x) (andb (second x) (third x)))
      (fun x => andb (andb (first x) (second x)) (third x))
      given).
    2: { intros x _; apply andb_assoc. }
    rewrite Hpair.
    rewrite H12.
    ring.
  Qed.


  (**
   [finite_conditional_independent_conditioning_complement_first] (theorem) — The complement of a conditioning event is impossible inside that event.
   Mathematical meaning: When conditioning on G, the Boolean complement not-G is necessarily false, and therefore conditionally independent of any other target event in the first target position.
   Exact checked proposition: If finite_prob weights samples given > 0, then finite_conditional_independent weights samples (fun x => negb (given x)) second given holds for arbitrary finite weights and sample occurrences.
   Premises and side conditions: Strictly positive mass of G is necessary for the independence predicate. The support-equivalence proof needs neither normalized total mass nor nonnegative weights, although probabilistic interpretation does require them.
   Proof/definition method: Show that false and not-G coincide wherever G is true, transfer the already checked impossible-event independence assertion through conditioned-support extensionality, and reuse the established positivity premise.
   Library reuse: finite_conditional_independent_false_first, finite_conditional_independent_event_ext_on_conditioned_samples and Stdlib.Bool.negb; no new conditional probability or Boolean case enumeration is introduced.
   Boundary: This is a conditioning tautology and does not imply that a nontrivial event is independent of its complement without conditioning.
   *)
  Theorem finite_conditional_independent_conditioning_complement_first :
    forall weights samples second given,
      0 < finite_prob weights samples given ->
      finite_conditional_independent weights samples
        (fun x => negb (given x)) second given.
  Proof.
    intros weights samples second given Hgiven.
    assert (Hagree :
      forall x, In x samples -> given x = true ->
      false = negb (given x)).
    { intros x _ Hg; rewrite Hg; reflexivity. }
    apply (proj1 (finite_conditional_independent_event_ext_on_conditioned_samples
      weights samples (fun _ => false)
      (fun x => negb (given x)) second given Hagree)).
    apply finite_conditional_independent_false_first.
    exact Hgiven.
  Qed.

  (**
   [finite_conditional_independent_conditioning_complement_second] (theorem) — Complement-of-conditioning independence in the second target position.
   Mathematical meaning: Under positive-mass conditioning G, the complementary event not-G is impossible on every conditioned sample, so it is independent of an arbitrary first target as well.
   Exact checked proposition: For all finite weights, samples, first and given with strictly positive finite event mass of G, finite_conditional_independent weights samples first (fun x => negb (given x)) given.
   Premises and side conditions: Only the conditioning-event positive-mass guard is required algebraically; nonnegative normalized finite weights are relevant solely when interpreting expressions as genuine probabilities.
   Proof/definition method: Use independence symmetry to swap the target positions and invoke the checked complement-of-conditioning first-target theorem, avoiding a second conditional-support extensionality proof.
   Library reuse: finite_conditional_independent_symmetric and finite_conditional_independent_conditioning_complement_first.
   Boundary: This finite conditional tautology supplies no independence statement about G and not-G under unconditional sampling.
   *)
  Theorem finite_conditional_independent_conditioning_complement_second :
    forall weights samples first given,
      0 < finite_prob weights samples given ->
      finite_conditional_independent weights samples
        first (fun x => negb (given x)) given.
  Proof.
    intros weights samples first given Hgiven.
    apply (proj2 (finite_conditional_independent_symmetric
      weights samples first (fun x => negb (given x)) given)).
    apply finite_conditional_independent_conditioning_complement_first.
    exact Hgiven.
  Qed.


  (**
   [finite_conditional_prob_as_filtered_true] (theorem) — Conditioning an original finite list equals certain-event conditioning after filtering.
   Mathematical meaning: To condition on G, first select the sampled outcomes satisfying G with the standard List.filter operation and then condition the resulting weighted list on the universally true event. The resulting conditional event mass equals the original conditional mass, even without explicit renormalization.
   Exact checked proposition: For any real weights, finite samples and target and conditioning Boolean events, finite_conditional_prob weights samples event given = finite_conditional_prob weights (filter given samples) event (fun _ => true).
   Premises and side conditions: Neither positive conditioning mass nor normalized/nonnegative weights is needed for the exact quotient equality; both denominators coincide as finite real sums, including the zero case where Rocq's real division has its algebraic convention. Repeated sample occurrences are retained.
   Proof/definition method: Unfold only the existing quotient on both sides, simplify conjunction with true by finite support extensionality, replace the selected numerator using finite_prob_on_filtered_samples, and identify the denominator using finite_prob_true and finite_prob_as_filtered_mass.
   Library reuse: Stdlib.List.filter, finite_prob_event_ext_on_samples, finite_prob_on_filtered_samples, finite_prob_true and finite_prob_as_filtered_mass; no new conditional kernel or finite summation is defined.
   Boundary: This is finite-list conditioning; the formula does not assert measure-theoretic disintegration or give zero-denominator quotients their usual probabilistic interpretation.
   *)
  Theorem finite_conditional_prob_as_filtered_true :
    forall weights samples event given,
      finite_conditional_prob weights samples event given =
      finite_conditional_prob weights (filter given samples)
        event (fun _ => true).
  Proof.
    intros weights samples event given.
    unfold finite_conditional_prob.
    rewrite (finite_prob_event_ext_on_samples weights
      (filter given samples) (fun x => andb true (event x)) event).
    2: { intros x _; reflexivity. }
    rewrite (finite_prob_on_filtered_samples
      weights samples given event).
    rewrite (finite_prob_true weights (filter given samples)).
    rewrite (finite_prob_as_filtered_mass weights samples given).
    reflexivity.
  Qed.

  (**
   [finite_conditional_independent_iff_filtered_true] (theorem) — Conditional independence as ordinary certain-event independence on a restricted finite list.
   Mathematical meaning: Independence of A and B given selector G on the original list is equivalent to the same generic factorization assertion conditioned on true over the sublist selected by G. All conditional marginals and the strict positivity requirement are preserved.
   Exact checked proposition: For all finite weights, samples, first, second and given, finite_conditional_independent weights samples first second given iff finite_conditional_independent weights (filter given samples) first second (fun _ => true).
   Premises and side conditions: There is no extra positive-mass hypothesis because both independence predicates carry it; the equivalence includes failure of both predicates at zero conditioned mass. Arbitrary signed weights and repeated outcomes remain legal algebraically, with nonnegative weights needed for actual probability semantics.
   Proof/definition method: Unfold the existing conditional-independence predicate, rewrite the two conditioning masses using finite_prob_true and finite_prob_as_filtered_mass, then rewrite its joint and both marginal conditional quotients via finite_conditional_prob_as_filtered_true.
   Library reuse: finite_conditional_prob_as_filtered_true, finite_prob_true, finite_prob_as_filtered_mass and Stdlib.List.filter; no additional independence predicate or event-sum recursion is introduced.
   Boundary: This represents conditioning by a restricted explicit finite list, not conditioning on a sigma-algebra or asserting a normalized conditional measure when the selector has zero mass.
   *)
  Theorem finite_conditional_independent_iff_filtered_true :
    forall weights samples first second given,
      (finite_conditional_independent weights samples first second given <->
       finite_conditional_independent weights (filter given samples)
         first second (fun _ => true)).
  Proof.
    intros weights samples first second given.
    unfold finite_conditional_independent.
    rewrite (finite_prob_true weights (filter given samples)).
    rewrite (finite_prob_as_filtered_mass weights samples given).
    rewrite (finite_conditional_prob_as_filtered_true
      weights samples
      (fun x => andb (first x) (second x)) given).
    rewrite (finite_conditional_prob_as_filtered_true
      weights samples first given).
    rewrite (finite_conditional_prob_as_filtered_true
      weights samples second given).
    reflexivity.
  Qed.

  (**
   [finite_conditional_independent_iff_filtered_cross_product] (theorem) — A denominator-free independence criterion on the conditioning-selected sublist.
   Mathematical meaning: Under positive conditioning mass, A and B are conditionally independent on the original weighted list iff their conjunction mass on the list filtered by G, multiplied by the total weight of that filtered list, equals the product of the two filtered marginal masses.
   Exact checked proposition: Given 0 < finite_prob weights samples given, finite_conditional_independent weights samples first second given iff finite_prob weights (filter given samples) (A AND B) * FiniteSum.finite_sum weights (filter given samples) = finite_prob weights (filter given samples) first * finite_prob weights (filter given samples) second.
   Premises and side conditions: Strict positive conditioning mass is required to cancel conditional denominators. The full sample mass need not be normalized, and even signed finite weights satisfy the algebraic criterion; genuine probabilistic semantics require all sampled weights to be nonnegative.
   Proof/definition method: Reuse the checked conditional mass cross-product equivalence, then rewrite each of its three event intersections by finite_prob_on_filtered_samples and its remaining selector mass by finite_prob_as_filtered_mass.
   Library reuse: finite_conditional_independent_iff_cross_product_mass, finite_prob_on_filtered_samples, finite_prob_as_filtered_mass and Stdlib.List.filter. No new quotient algebra or finite-sum traversal appears.
   Boundary: A four-mass identity on an explicit finite selected list is not a proof of independence of real-valued random variables or of conditional independence after changing the weight model.
   *)
  Theorem finite_conditional_independent_iff_filtered_cross_product :
    forall weights samples first second given,
      0 < finite_prob weights samples given ->
      (finite_conditional_independent weights samples first second given <->
       finite_prob weights (filter given samples)
         (fun x => andb (first x) (second x)) *
         FiniteSum.finite_sum weights (filter given samples) =
       finite_prob weights (filter given samples) first *
       finite_prob weights (filter given samples) second).
  Proof.
    intros weights samples first second given Hpositive.
    rewrite (finite_conditional_independent_iff_cross_product_mass
      weights samples first second given Hpositive).
    rewrite <- (finite_prob_on_filtered_samples weights samples given
      (fun x => andb (first x) (second x))).
    rewrite (finite_prob_as_filtered_mass weights samples given).
    rewrite <- (finite_prob_on_filtered_samples weights samples given first).
    rewrite <- (finite_prob_on_filtered_samples weights samples given second).
    reflexivity.
  Qed.


  (**
   [all_events] (definition) — Finite intersection of a list of Boolean events by the standard List.forallb operator.
   Mathematical meaning: A sample outcome lies in the intersection of a list of event predicates exactly when every listed event returns true for that outcome. The intersection of the empty list is the universally true event, the correct multiplicative unit for a subsequent finite joint-probability product.
   Exact declaration: all_events events x := forallb (fun event => event x) events, with event lists and outcomes supplied through the enclosing FiniteOutcomeSpace section.
   Premises and side conditions: Events need not be distinct, weights do not enter the definition, and the empty event list is accepted. Duplicating an event in the list does not change the resulting Boolean intersection.
   Proof/definition method: Delegate Boolean universal quantification across an event list to Rocq Stdlib.List.forallb, rather than writing a project-specific recursive Boolean conjunction fold.
   Library reuse: Stdlib.List.forallb, Stdlib.Bool.andb and the existing Event alias; no custom all-events recursion or finite probability representation is introduced.
   Boundary: This is a decidable finite predicate over an arbitrary outcome type, not a sigma-algebra, random-variable product or automatically independent family of events.
   *)
  Definition all_events (events : list Event) : Event :=
    fun x => forallb (fun event => event x) events.

  (**
   [finite_conditional_prefix_independent] (definition) — Sufficient chain assumptions for a finite list of conditionally independent event factors.
   Mathematical meaning: Every listed event must be conditionally independent, given G, of the conjunction of all the events following it in the list. The empty list satisfies this structural conjunction of assumptions; the separate factorization theorem also requires a positive conditioning mass.
   Exact declaration: finite_conditional_prefix_independent weights samples [] given := True; on first::rest it means finite_conditional_independent weights samples first (all_events rest) given AND finite_conditional_prefix_independent weights samples rest given.
   Premises and side conditions: No pairwise-only independence assumption is substituted for the required independence of each first event from its entire remaining conjunction. The weights and sample list are retained identically at each tail and may have repeated outcomes.
   Proof/definition method: Inductively collect the explicit finite Boolean-factorization premises required for product decomposition; the underlying intersection is the maintained Stdlib.List.forallb operation, not a custom event fold.
   Library reuse: finite_conditional_independent, all_events and Stdlib.List plus ordinary propositional conjunction/True. Only the project-specific list of logical side conditions is recursively defined.
   Boundary: This predicate does not imply mutual independence under arbitrary conditioning sets, nor does pairwise independence alone establish it.
   *)
  Fixpoint finite_conditional_prefix_independent
      (weights : Outcome -> R) (samples : list Outcome)
      (events : list Event) (given : Event) : Prop :=
    match events with
    | [] => True
    | first :: rest =>
        finite_conditional_independent weights samples
          first (all_events rest) given /\
        finite_conditional_prefix_independent weights samples rest given
    end.

  (**
   [finite_conditional_all_events_append] (theorem) — Standard-library conjunction distributes over appending event lists.
   Mathematical meaning: The joint event represented by all_events on two concatenated lists is the conjunction of the joint event for the left list with that for the right list, so the two representations have exactly the same conditional mass.
   Exact checked proposition: For all weights, samples, left and right event lists and given, finite_conditional_prob weights samples (all_events (left ++ right)) given equals finite_conditional_prob weights samples (fun x => andb (all_events left x) (all_events right x)) given.
   Premises and side conditions: No positivity, normalization or weight-sign premise is needed for the exact extensional equality. Empty lists and repeated events or sampled outcomes are permitted without altering the Boolean semantics.
   Proof/definition method: Invoke the existing finite conditional event-extensionality theorem on each sampled outcome, then rewrite the concatenation with the standard Rocq List.forallb_app lemma.
   Library reuse: Stdlib.List.forallb_app, Stdlib.List.app, finite_conditional_prob_event_ext_on_samples and all_events; no new list induction or Boolean append identity is implemented.
   Boundary: Concatenated event intersections do not by themselves imply probabilistic independence or a product of marginal probabilities.
   *)
  Theorem finite_conditional_all_events_append :
    forall weights samples left right given,
      finite_conditional_prob weights samples
        (all_events (left ++ right)) given =
      finite_conditional_prob weights samples
        (fun x => andb (all_events left x) (all_events right x)) given.
  Proof.
    intros weights samples left right given.
    apply finite_conditional_prob_event_ext_on_samples.
    intros x _.
    unfold all_events.
    rewrite forallb_app.
    reflexivity.
  Qed.

  (**
   [finite_conditional_all_events_singleton] (theorem) — Single-event conjunction has the original conditional event mass.
   Mathematical meaning: Intersecting a singleton list of Boolean event predicates does not change the event itself, since forallb on a one-element list reduces to the predicate value AND the true unit.
   Exact checked proposition: For any weighted sample, event and given selector, finite_conditional_prob weights samples (all_events [event]) given = finite_conditional_prob weights samples event given.
   Premises and side conditions: The identity holds for arbitrary real weights, zero conditioning denominator, and repeated sample points because it is an equality of two syntactically extensional finite event quotients.
   Proof/definition method: Apply the established conditional probability target-event extensionality on the sample and reduce the standard list singleton conjunction definition by computation.
   Library reuse: all_events, Stdlib.List.forallb, finite_conditional_prob_event_ext_on_samples and Stdlib.Bool.
   Boundary: This is a finite Boolean conjunction normalization, not an independence assertion or a claim about the probability that some event actually occurs.
   *)
  Theorem finite_conditional_all_events_singleton :
    forall weights samples event given,
      finite_conditional_prob weights samples
        (all_events [event]) given =
      finite_conditional_prob weights samples event given.
  Proof.
    intros weights samples event given.
    apply finite_conditional_prob_event_ext_on_samples.
    intros x _.
    unfold all_events; simpl.
    destruct (event x); reflexivity.
  Qed.

  (**
   [finite_conditional_all_events_product] (theorem) — Conditional product formula for any finite event list under a checked sequence of factorization assumptions.
   Mathematical meaning: The conditional probability of the conjunction of n event predicates equals the product of their n conditional probabilities if each current event is independent of the conjunction of the remaining events given the same selector G. Empty products have value one, consistent with the positive-mass certain-event identity.
   Exact checked proposition: Given 0 < finite_prob weights samples given and finite_conditional_prefix_independent weights samples events given, finite_conditional_prob weights samples (all_events events) given = fold_right Rmult 1 (map (fun event => finite_conditional_prob weights samples event given) events).
   Premises and side conditions: The conditioning marginal is explicitly strictly positive. The stepwise premise is stronger than pairwise independence and is imposed on the whole remaining intersection; repeated target events are not assumed independent. Arbitrary real weights satisfy the algebraic implication, while nonnegative weights are needed for statistical probability semantics.
   Proof/definition method: Induct on the event list, using finite_conditional_prob_true as the empty-list base case, the first conjunct of finite_conditional_prefix_independent as the current two-event factorization, and the induction hypothesis on the remaining event list. Use only definitionally reduced forallb, map and fold_right, without a new probability fold.
   Library reuse: Stdlib.List.forallb, map, fold_right, finite_conditional_independent and finite_conditional_prob_true. Event intersection and multiplicative product use maintained library operators rather than newly implemented algorithms.
   Boundary: The theorem is a finite Boolean joint-probability factorization under explicit sufficient hypotheses; it does not derive mutual independence from pairwise independence or extend to Gaussian random variables.
   *)
  Theorem finite_conditional_all_events_product :
    forall weights samples events given,
      0 < finite_prob weights samples given ->
      finite_conditional_prefix_independent weights samples events given ->
      finite_conditional_prob weights samples (all_events events) given =
      fold_right Rmult 1
        (map (fun event =>
          finite_conditional_prob weights samples event given) events).
  Proof.
    intros weights samples events.
    induction events as [|first rest IH]; intros given Hpositive Hchain.
    - change (finite_conditional_prob weights samples
        (fun _ => true) given = 1).
      apply finite_conditional_prob_true.
      exact Hpositive.
    - simpl in Hchain.
      destruct Hchain as [Hfactor Hrest].
      change (finite_conditional_prob weights samples
        (fun x => andb (first x) (all_events rest x)) given =
        finite_conditional_prob weights samples first given *
        fold_right Rmult 1
          (map (fun event =>
            finite_conditional_prob weights samples event given) rest)).
      destruct Hfactor as [_ Hjoint].
      rewrite Hjoint.
      rewrite (IH given Hpositive Hrest).
      reflexivity.
  Qed.


  (**
   [finite_conditional_union_contains_member] (theorem) — Conditional union mass contains every constituent event mass.
   Mathematical meaning: Under nonnegative sampled weights and a strictly positive conditioning mass, the conditional probability of any finite union of Boolean targets is no smaller than the conditional probability of any event listed in that union.
   Exact checked proposition: For any weights, samples, events, member event and conditioning event G, In member events, nonnegative sampled weights and 0 < finite_prob weights samples G imply finite_conditional_prob weights samples member G <= finite_conditional_prob weights samples (any_event events) G.
   Premises and side conditions: The event must occur in the provided list, each sampled weight must be nonnegative, and conditioning mass must be positive; the total mass need not be one and duplicate event predicates are permitted.
   Proof/definition method: Apply the existing monotonicity theorem for finite conditional event masses and discharge its pointwise implication through the already checked event_member_implies_union theorem.
   Library reuse: finite_conditional_prob_monotone, event_member_implies_union, Stdlib.List.In and Stdlib.List.existsb; no union event recursion or conditional-probability arithmetic is repeated.
   Boundary: This is a distribution-free finite weighted list inequality, not evidence that listed admissions routes actually overlap or are mutually independent.
   *)
  Theorem finite_conditional_union_contains_member :
    forall weights samples events member given,
      In member events ->
      (forall x, In x samples -> 0 <= weights x) ->
      0 < finite_prob weights samples given ->
      finite_conditional_prob weights samples member given <=
      finite_conditional_prob weights samples (any_event events) given.
  Proof.
    intros weights samples events member given Hin Hweight Hgiven.
    apply (finite_conditional_prob_monotone weights samples
      member (any_event events) given Hweight Hgiven).
    intros x _ Hmember.
    apply (event_member_implies_union events member x Hin).
    exact Hmember.
  Qed.

  (**
   [finite_conditional_union_bound_filtered] (theorem) — The finite Boole union upper bound under conditioning.
   Mathematical meaning: The conditional mass of the union of an arbitrary finite event list is bounded by the sum of their masses on the sublist selected by G, divided by the positive mass of G. This is the classical union bound applied to a finite conditioned sample without renormalizing the weights.
   Exact checked proposition: For nonnegative sampled weights and 0 < finite_prob weights samples given, finite_conditional_prob weights samples (any_event events) given <= sum_marginal_probs weights (filter given samples) events / finite_prob weights samples given.
   Premises and side conditions: Every original sampled weight must be nonnegative (hence also every filtered sampled weight), and the finite mass of the conditioning event must be strictly positive. Neither total-mass normalization nor independence between events is assumed. Repeated outcomes retain multiplicity.
   Proof/definition method: Rewrite the existing conditional quotient with finite_conditional_prob_filtered, recognize its numerator as union_prob on the filtered sample, apply the pre-existing arbitrary_union_bound on that list, and multiply the inequality by the nonnegative reciprocal of the conditioning mass.
   Library reuse: finite_conditional_prob_filtered, arbitrary_union_bound, Stdlib.List.filter_In, Stdlib.Reals.Rinv_0_lt_compat and Rmult_le_compat_r. No new inclusion-exclusion enumeration, event-mass sum or independent-family axiom is introduced.
   Boundary: This is an upper bound for finitely many Boolean event targets under explicitly positive conditioning; it does not assert that the bound is tight or derive the continuous-measure version.
   *)
  Theorem finite_conditional_union_bound_filtered :
    forall weights samples events given,
      (forall x, In x samples -> 0 <= weights x) ->
      0 < finite_prob weights samples given ->
      finite_conditional_prob weights samples (any_event events) given <=
      sum_marginal_probs weights (filter given samples) events /
      finite_prob weights samples given.
  Proof.
    intros weights samples events given Hweight Hgiven.
    rewrite finite_conditional_prob_filtered.
    change (union_prob weights (filter given samples) events /
      finite_prob weights samples given <=
      sum_marginal_probs weights (filter given samples) events /
      finite_prob weights samples given).
    unfold Rdiv.
    apply Rmult_le_compat_r.
    - apply Rlt_le, Rinv_0_lt_compat; exact Hgiven.
    - apply arbitrary_union_bound.
      intros x Hx.
      apply Hweight.
      apply filter_In in Hx.
      tauto.
  Qed.

  (**
   [finite_conditional_all_events_at_most_member] (theorem) — Any finite intersection is conditionally bounded by each member.
   Mathematical meaning: An outcome that satisfies every Boolean event in a nonempty finite list satisfies each listed member in particular, so the conditional mass of their conjunction cannot exceed the conditional mass of a chosen member for nonnegative weights.
   Exact checked proposition: If member is in events, all sampled weights are nonnegative and finite_prob weights samples given is positive, finite_conditional_prob weights samples (all_events events) given <= finite_conditional_prob weights samples member given.
   Premises and side conditions: Membership in the event list, sampled nonnegative weights and strictly positive conditioning mass are all explicit. No independence, distinctness, or unit sample-mass assumption is imposed.
   Proof/definition method: Reduce the desired mass inequality to a pointwise Boolean inclusion using finite_conditional_prob_monotone, then invoke Stdlib.List.forallb_forall to extract a listed member's truth from the finite conjunction event.
   Library reuse: finite_conditional_prob_monotone, all_events, Stdlib.List.forallb_forall and Stdlib.List.In. No custom conjunction induction, finite sum, or probability measure is introduced.
   Boundary: This exact finite event intersection inequality is independent of the product-factorization results and does not imply that target events are stochastically independent.
   *)
  Theorem finite_conditional_all_events_at_most_member :
    forall weights samples events member given,
      In member events ->
      (forall x, In x samples -> 0 <= weights x) ->
      0 < finite_prob weights samples given ->
      finite_conditional_prob weights samples (all_events events) given <=
      finite_conditional_prob weights samples member given.
  Proof.
    intros weights samples events member given Hin Hweight Hgiven.
    apply (finite_conditional_prob_monotone weights samples
      (all_events events) member given Hweight Hgiven).
    intros x _ Hall.
    unfold all_events in Hall.
    pose proof (proj1
      (@forallb_forall Event (fun e => e x) events) Hall)
      as Hallmember.
    apply Hallmember.
    exact Hin.
  Qed.


  (**
   [finite_conditional_marginals_sum_filtered] (theorem) — Sum of conditional event marginals as one scaled finite sum on the conditioned sublist.
   Mathematical meaning: Summing the conditional probabilities of a finite event family equals the sum of each target's unnormalized event mass on the G-filtered sample divided by the common conditioning mass. In particular the identity holds for an empty event family and does not create a separate conditional-sum operator.
   Exact checked proposition: For arbitrary weights, samples, event lists and given, FiniteSum.finite_sum (fun e => finite_conditional_prob weights samples e given) events = sum_marginal_probs weights (filter given samples) events / finite_prob weights samples given.
   Premises and side conditions: No nonnegative-weight or positive denominator assumption is needed for the exact algebraic equality, even if the denominator is zero according to Rocq's total real division convention. Statistical interpretation of these values requires positive conditioning mass and nonnegative weights.
   Proof/definition method: Expand the already defined sum_marginal_probs and division, commute its scalar product, apply the previously checked FiniteSum.finite_sum_scale theorem backward, and identify the per-event integrands through finite_conditional_prob_filtered and Stdlib ring algebra.
   Library reuse: FiniteSum.finite_sum_scale, FiniteSum.finite_sum_ext, finite_conditional_prob_filtered, Stdlib.Reals.Rmult_comm and ring. No custom event-list folding, conditional quotient or new finite sum is implemented.
   Boundary: This identity is about sums of weighted finite Boolean-event masses and does not claim independence, mutual exclusivity or that the marginals sum to one.
   *)
  Theorem finite_conditional_marginals_sum_filtered :
    forall weights samples events given,
      FiniteSum.finite_sum
        (fun event => finite_conditional_prob weights samples event given)
        events =
      sum_marginal_probs weights (filter given samples) events /
      finite_prob weights samples given.
  Proof.
    intros weights samples events given.
    unfold sum_marginal_probs, Rdiv.
    rewrite (Rmult_comm
      (FiniteSum.finite_sum
        (finite_prob weights (filter given samples)) events)
      (/ finite_prob weights samples given)).
    rewrite <- (FiniteSum.finite_sum_scale events
      (/ finite_prob weights samples given)
      (finite_prob weights (filter given samples))).
    apply FiniteSum.finite_sum_ext.
    intro event.
    rewrite (finite_conditional_prob_filtered
      weights samples event given).
    unfold Rdiv.
    ring.
  Qed.

  (**
   [finite_conditional_union_bound] (theorem) — The finite conditional Boole union bound in marginal-sum form.
   Mathematical meaning: The conditional probability of the union of any finite Boolean event family is no greater than the sum of the conditional probabilities of its members, without any independence assumptions or restriction on overlap. It is the direct conditional generalization of the existing finite arbitrary-union bound.
   Exact checked proposition: For weights nonnegative on samples and strictly positive finite_prob weights samples given, finite_conditional_prob weights samples (any_event events) given <= FiniteSum.finite_sum (fun event => finite_conditional_prob weights samples event given) events.
   Premises and side conditions: Each originally sampled weight is nonnegative and the conditioning mass is strictly positive. The original full sample need not be normalized, event predicates may repeat, and no independent or mutually exclusive-event hypothesis is assumed.
   Proof/definition method: Rewrite the conditional marginal sum through finite_conditional_marginals_sum_filtered and apply the already checked finite_conditional_union_bound_filtered inequality, so all substantial union and quotient inequalities remain in reusable earlier lemmas.
   Library reuse: finite_conditional_marginals_sum_filtered, finite_conditional_union_bound_filtered, FiniteSum.finite_sum and Stdlib.List.filter.
   Boundary: The inequality is a finite distribution-free bound; it does not claim sharpness, equality in the presence of overlap, or extension to continuous probability without a measure-theory bridge.
   *)
  Theorem finite_conditional_union_bound :
    forall weights samples events given,
      (forall x, In x samples -> 0 <= weights x) ->
      0 < finite_prob weights samples given ->
      finite_conditional_prob weights samples (any_event events) given <=
      FiniteSum.finite_sum
        (fun event => finite_conditional_prob weights samples event given)
        events.
  Proof.
    intros weights samples events given Hweight Hgiven.
    rewrite (finite_conditional_marginals_sum_filtered
      weights samples events given).
    apply finite_conditional_union_bound_filtered; assumption.
  Qed.


  (**
   [finite_prob_scale_weights] (theorem) — Homogeneity of a finite Boolean event mass.
   Mathematical meaning: Multiplying every sampled real weight by the same scalar multiplies the finite mass of every Boolean event by that scalar. This is the linearity property needed to compare conditional probabilities before and after a common change of weight units.
   Exact checked proposition: For every real scalar scale, weights, sample list and Boolean event, finite_prob (fun x => scale * weights x) samples event = scale * finite_prob weights samples event.
   Premises and side conditions: No positivity, normalization, event independence or distinct-outcome assumption is needed for the algebraic identity. The finite sample list and all repeated entries remain unchanged.
   Proof/definition method: Unfold only the existing finite event mass and its shared finite_sum alias, rewrite the right-hand side with the existing finite_sum_scale lemma, and apply finite_sum_ext to match the two pointwise scalar products using the standard ring tactic.
   Library reuse: FiniteSum.finite_sum_scale, FiniteSum.finite_sum_ext and Stdlib.Reals ring. There is no new recursive weighted-sum algorithm.
   Boundary: Real scaling is not a claim that scaled signed weights remain probabilities; positive normalization and nonnegative weights have to be supplied when interpreting them statistically.
   *)
  Theorem finite_prob_scale_weights :
    forall scale weights samples event,
      finite_prob (fun x => scale * weights x) samples event =
      scale * finite_prob weights samples event.
  Proof.
    intros scale weights samples event.
    unfold finite_prob, finite_sum.
    rewrite <- (FiniteSum.finite_sum_scale samples scale
      (fun x => weights x * indicator (event x))).
    apply FiniteSum.finite_sum_ext.
    intro x; ring.
  Qed.

  (**
   [finite_conditional_prob_scale_weights] (theorem) — Invariance of finite conditional event mass under positive global reweighting.
   Mathematical meaning: Scaling all sample weights by one strictly positive common factor changes both the selected target mass and the conditioning mass by that same factor; consequently their ratio and the conditional probability of the target event stay unchanged.
   Exact checked proposition: For all real scale, weights, samples, target event and given event, 0 < scale and 0 < finite_prob weights samples given imply finite_conditional_prob (fun x => scale * weights x) samples event given = finite_conditional_prob weights samples event given.
   Premises and side conditions: Strict positivity of scale and of the original conditioning mass ensure both denominators are nonzero; unit total mass, independence, and nonnegative individual weights are not needed for the equality of real expressions.
   Proof/definition method: Unfold only the existing conditional quotient, rewrite both finite event masses through finite_prob_scale_weights, then cancel their common nonzero positive scaling factor with the standard real-field tactic and linear arithmetic.
   Library reuse: finite_prob_scale_weights, finite_conditional_prob, Stdlib.Reals field and Stdlib.Lra; no new probability operator or denominator calculation is introduced.
   Boundary: A common positive scalar does not change conditional ratios; this does not imply invariance under outcome-dependent weighting or selection-bias transformations.
   *)
  Theorem finite_conditional_prob_scale_weights :
    forall scale weights samples event given,
      0 < scale ->
      0 < finite_prob weights samples given ->
      finite_conditional_prob (fun x => scale * weights x)
        samples event given =
      finite_conditional_prob weights samples event given.
  Proof.
    intros scale weights samples event given Hscale Hgiven.
    unfold finite_conditional_prob.
    rewrite (finite_prob_scale_weights scale weights samples
      (fun x => andb (given x) (event x))).
    rewrite (finite_prob_scale_weights scale weights samples given).
    field; lra.
  Qed.

  (**
   [finite_conditional_independent_scale_weights] (theorem) — Positive rescaling invariance of a finite conditional-independence proposition.
   Mathematical meaning: Conditional factorization of the joint event mass is unaffected by changing all finite outcome weights by a common positive factor, because both the positive conditioning-mass guard and each conditional quotient represent the same proposition after rescaling.
   Exact checked proposition: For scale > 0 and any weights, samples and Boolean first, second and given, finite_conditional_independent (fun x => scale * weights x) samples first second given iff finite_conditional_independent weights samples first second given.
   Premises and side conditions: The scale must be strictly positive to preserve positive conditioning mass in both directions. No normalization or nonnegative individual-weight assumption is silently inserted; the latter is needed only for probability interpretation.
   Proof/definition method: Unfold the existing two-conjunct independence predicate, rewrite the scaled conditioning mass with finite_prob_scale_weights, extract positivity on either side by Stdlib nonlinear real arithmetic, and rewrite all three conditional terms through finite_conditional_prob_scale_weights with the recovered original conditioning-mass guard.
   Library reuse: finite_prob_scale_weights, finite_conditional_prob_scale_weights, Stdlib.Psatz.nra and ordinary propositional iff. No repeated Boolean conjunction proof or independent finite summation is introduced.
   Boundary: Uniform positive scaling leaves these finite ratios and factorization claims unchanged, whereas zero, negative or nonuniform scaling is not covered.
   *)
  Theorem finite_conditional_independent_scale_weights :
    forall scale weights samples first second given,
      0 < scale ->
      (finite_conditional_independent (fun x => scale * weights x)
         samples first second given <->
       finite_conditional_independent weights samples first second given).
  Proof.
    intros scale weights samples first second given Hscale.
    unfold finite_conditional_independent.
    rewrite (finite_prob_scale_weights scale weights samples given).
    assert (Hguard :
      0 < scale * finite_prob weights samples given <->
      0 < finite_prob weights samples given).
    { split; intro H; nra. }
    rewrite Hguard.
    split.
    - intros [Hgiven Hfactor].
      split; [exact Hgiven |].
      rewrite (finite_conditional_prob_scale_weights
        scale weights samples
        (fun x => andb (first x) (second x)) given Hscale Hgiven)
        in Hfactor.
      rewrite (finite_conditional_prob_scale_weights
        scale weights samples first given Hscale Hgiven)
        in Hfactor.
      rewrite (finite_conditional_prob_scale_weights
        scale weights samples second given Hscale Hgiven)
        in Hfactor.
      exact Hfactor.
    - intros [Hgiven Hfactor].
      split; [exact Hgiven |].
      rewrite (finite_conditional_prob_scale_weights
        scale weights samples
        (fun x => andb (first x) (second x)) given Hscale Hgiven).
      rewrite (finite_conditional_prob_scale_weights
        scale weights samples first given Hscale Hgiven).
      rewrite (finite_conditional_prob_scale_weights
        scale weights samples second given Hscale Hgiven).
      exact Hfactor.
  Qed.


  (**
   [all_events_membership_ext] (theorem) — Membership-extensionality of a finite Boolean conjunction.
   Mathematical meaning: The finite conjunction of Boolean event predicates depends only on which predicates are members of the supplied event list. Event order and repeated occurrences cannot change the outcome-by-outcome truth value when the two lists have exactly the same membership relation.
   Exact checked proposition: For any two lists left and right of Boolean events, if every event belongs to left iff it belongs to right, then all_events left x = all_events right x for every outcome x.
   Premises and side conditions: The outcome type and event-list lengths are arbitrary; lists need not be permutations and may contain duplicates. There is no finite probability or normalization hypothesis because the theorem is purely Boolean.
   Proof/definition method: Unfold all_events as Stdlib.List.forallb, use the standard forallb_forall equivalence in each direction to transport all true member predicates across equal membership sets, and rule out the only inconsistent Boolean case.
   Library reuse: Stdlib.List.forallb_forall, Stdlib.List.In and Stdlib.Bool; no project-specific recursion over Boolean event lists is introduced.
   Boundary: The theorem says nothing about the arithmetic sum of event marginals, which deliberately counts duplicate listed events separately; it concerns only their conjunction predicate.
   *)
  Theorem all_events_membership_ext :
    forall left right,
      (forall event, In event left <-> In event right) ->
      forall x, all_events left x = all_events right x.
  Proof.
    intros left right Hsame x.
    assert (Hlr :
      all_events left x = true -> all_events right x = true).
    { intro Hl.
      unfold all_events in *.
      apply (proj2 (@forallb_forall Event (fun e => e x) right)).
      intros e Hin.
      apply (proj1 (@forallb_forall Event (fun e => e x) left) Hl).
      apply (proj2 (Hsame e)).
      exact Hin. }
    assert (Hrl :
      all_events right x = true -> all_events left x = true).
    { intro Hr.
      unfold all_events in *.
      apply (proj2 (@forallb_forall Event (fun e => e x) left)).
      intros e Hin.
      apply (proj1 (@forallb_forall Event (fun e => e x) right) Hr).
      apply (proj1 (Hsame e)).
      exact Hin. }
    destruct (all_events left x) eqn:Hl;
      destruct (all_events right x) eqn:Hr; try reflexivity.
    - pose proof (Hlr Hl) as Hcontradiction.
      rewrite Hr in Hcontradiction.
      discriminate Hcontradiction.
    - pose proof (Hrl Hr) as Hcontradiction.
      rewrite Hl in Hcontradiction.
      discriminate Hcontradiction.
  Qed.

  (**
   [all_events_permutation] (theorem) — Finite Boolean conjunction is invariant under event-list permutation.
   Mathematical meaning: Reordering the finite list of Boolean event predicates does not affect their pointwise conjunction. This is a direct structural consequence of membership-extensionality, not an independent induction on event lists.
   Exact checked proposition: If Stdlib.Sorting.Permutation.Permutation left right, then all_events left x = all_events right x for every outcome x.
   Premises and side conditions: Both lists contain exactly the same event occurrences up to permutation and may be empty or contain repeated event predicates. No sampled weights, conditional denominator, or normalization is assumed.
   Proof/definition method: Reduce to all_events_membership_ext and use the standard Permutation_in lemma in both directions, applying Permutation_sym for the reverse membership implication.
   Library reuse: all_events_membership_ext, Stdlib.Sorting.Permutation.Permutation_in and Permutation_sym, and Stdlib.List.In; no bespoke permutation proof or finite Boolean fold is added.
   Boundary: Invariance of conjunction under reordering is not a claim that arbitrary event probabilities are independent or that probabilities factor.
   *)
  Theorem all_events_permutation :
    forall left right,
      Permutation left right ->
      forall x, all_events left x = all_events right x.
  Proof.
    intros left right Hperm.
    apply all_events_membership_ext.
    intro e; split; intro Hin.
    - eapply Permutation_in; [exact Hperm | exact Hin].
    - eapply Permutation_in;
        [apply Permutation_sym; exact Hperm | exact Hin].
  Qed.

  (**
   [finite_conditional_all_events_permutation] (theorem) — Finite conditional conjunction mass ignores event order.
   Mathematical meaning: When a list of Boolean targets is reordered, the conjunction event selected at each sample outcome is unchanged; therefore its conditional mass with respect to any conditioning event remains exactly the same.
   Exact checked proposition: For weights, sample list, Boolean event lists left and right and conditioning event given, Permutation left right implies finite_conditional_prob weights samples (all_events left) given = finite_conditional_prob weights samples (all_events right) given.
   Premises and side conditions: No positive conditioning mass or weight sign restriction is needed to preserve two equal real quotient expressions, including the formal zero-denominator case. Both lists may have duplicate events, and the sample may have repeated outcomes.
   Proof/definition method: Apply the previously checked finite conditional target-event extensionality theorem and discharge its pointwise equality with all_events_permutation, avoiding unfolding any event mass or conditional quotient.
   Library reuse: finite_conditional_prob_event_ext_on_samples and all_events_permutation, which itself reuses Stdlib.Sorting.Permutation.
   Boundary: This equality holds for one fixed conditioning event, not for arbitrary reorderings that change event predicates or sample outcome weights.
   *)
  Theorem finite_conditional_all_events_permutation :
    forall weights samples left right given,
      Permutation left right ->
      finite_conditional_prob weights samples
        (all_events left) given =
      finite_conditional_prob weights samples
        (all_events right) given.
  Proof.
    intros weights samples left right given Hperm.
    apply finite_conditional_prob_event_ext_on_samples.
    intros x _.
    apply all_events_permutation.
    exact Hperm.
  Qed.

  (**
   [finite_conditional_all_events_subset] (theorem) — Adding Boolean constraints cannot increase conditional intersection mass.
   Mathematical meaning: If every event in the shorter constraint list occurs somewhere in the longer list, then satisfying every event in the longer list implies satisfying every event in the shorter list; with nonnegative sampled weights this inclusion makes the longer intersection no more probable under the same positive-mass conditioning event.
   Exact checked proposition: For arbitrary event lists required and additional, if each member of required is also in additional, weights are nonnegative on samples, and finite_prob weights samples given > 0, then finite_conditional_prob weights samples (all_events additional) given <= finite_conditional_prob weights samples (all_events required) given.
   Premises and side conditions: Explicit sampled nonnegative weights and strictly positive conditioning mass are essential for the inequality. Event lists may be empty, have different lengths or duplicate predicates; no target independence or normalization is silently assumed.
   Proof/definition method: Apply the existing finite_conditional_prob_monotone inequality with the two conjunction predicates; obtain the pointwise inclusion by two invocations of the standard forallb_forall characterization, transporting the truth of each required event to the longer list using membership inclusion.
   Library reuse: finite_conditional_prob_monotone, all_events, Stdlib.List.forallb_forall and Stdlib.List.In. No new Boolean conjunction recursion or finite weighted sum is written.
   Boundary: This is monotonicity under *adding constraints*, not the marginal-sum union bound or an assertion of independence among additional events.
   *)
  Theorem finite_conditional_all_events_subset :
    forall weights samples required additional given,
      (forall event, In event required -> In event additional) ->
      (forall x, In x samples -> 0 <= weights x) ->
      0 < finite_prob weights samples given ->
      finite_conditional_prob weights samples
        (all_events additional) given <=
      finite_conditional_prob weights samples
        (all_events required) given.
  Proof.
    intros weights samples required additional given Hsubset Hw Hgiven.
    apply (finite_conditional_prob_monotone
      weights samples (all_events additional) (all_events required)
      given Hw Hgiven).
    intros x _ Hall.
    unfold all_events in *.
    apply (proj2 (@forallb_forall Event
      (fun event => event x) required)).
    intros event Hin.
    apply (proj1 (@forallb_forall Event
      (fun e => e x) additional) Hall).
    apply Hsubset; exact Hin.
  Qed.

End FiniteOutcomeSpace.

(* The inequalities remain valid for a list with repeated sample points;
   normalized probabilities should be interpreted with the corresponding
   weighted-multiset convention. In applications with distinct outcomes,
   one normally uses a finite enumeration without duplicates. *)
