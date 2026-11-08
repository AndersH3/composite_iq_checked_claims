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

End FiniteOutcomeSpace.

(* The inequalities remain valid for a list with repeated sample points;
   normalized probabilities should be interpreted with the corresponding
   weighted-multiset convention. In applications with distinct outcomes,
   one normally uses a finite enumeration without duplicates. *)
