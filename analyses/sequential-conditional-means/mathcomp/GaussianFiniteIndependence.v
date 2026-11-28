(** Module: GaussianFiniteIndependence.v
    Purpose: Derive the pairwise independence of distinct coordinates
    of the actual finite standard Gaussian history probability.
    Reuse the verified recursive head/tail rectangle and marginal laws,
    and the MathComp tuple and ordinal decomposition lemmas.
    No Gaussian independence premise is introduced. Pairwise independence
    is not a substitute for independence of arbitrary linear projections.
    Researcher/requester: Anders Hellström.
    AI disclosure: AI-assisted proof candidates; validation pending.
*)
From mathcomp Require Import boot order ssralg ssrnum.
From mathcomp Require Import boolp classical_sets functions reals ereal topology normedtype.
From mathcomp Require Import numfun measure lebesgue_integral
  lebesgue_stieltjes_measure lebesgue_measure measurable_realfun.
From mathcomp.analysis Require Import normal_distribution.
Require Import GaussianFiniteStandard.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section FiniteIndependence.
Context {R : realType}.
Import MeasurableR.
Local Open Scope ereal_scope.
Local Abbreviation G := (normal_prob (0%R : R) (1%R : R)).

(** Expose the successor-coordinate identity from the previously
    validated marginal proof as a reusable lemma for joint events. *)
Lemma gmc_history_tail_coordinate n (j : 'I_n)
    (t : n.+1.-tuple (measurableTypeR R)) :
  tnth t (lift ord0 j) = tnth [tuple of behead t] j.
Proof.
case: (tupleP t) => x s.
have Htail : [tuple of behead [tuple of x :: s]] = s.
{ apply/val_inj; reflexivity. }
by rewrite tnthS Htail.
Qed.

(** Coordinate cylinders are measurable for every ordinal index.
    This is the canonical library coordinate measurability result
    applied to a measurable scalar event. *)
Lemma gmc_history_coordinate_event_measurable n (i : 'I_n) (U : set R) :
  measurable U ->
  measurable [set t : n.-tuple (measurableTypeR R) | U (tnth t i)].
Proof.
move=> mU.
have H := (@measurable_tnth _ (measurableTypeR R) n i)
  measurableT U mU.
by rewrite setTI in H.
Qed.

(** The first coordinate and any tail coordinate have independent
    standard normal marginals, derived from the verified rectangle law. *)
Theorem gmc_standard_history_head_other n (j : 'I_n) (U V : set R) :
  measurable U -> measurable V ->
  gmc_standard_history n.+1
    [set t : n.+1.-tuple (measurableTypeR R) |
      U (tnth t ord0) /\ V (tnth t (lift ord0 j))] = G U * G V.
Proof.
move=> mU mV.
pose A := [set t : n.-tuple (measurableTypeR R) | V (tnth t j)].
have mA : measurable A.
{ exact: gmc_history_coordinate_event_measurable mV. }
have Hset :
    [set t : n.+1.-tuple (measurableTypeR R) |
      U (tnth t ord0) /\ V (tnth t (lift ord0 j))] =
    [set t : n.+1.-tuple (measurableTypeR R) |
      U (tnth t ord0) /\ A [tuple of behead t]].
{ apply/seteqP; split=> t.
  - change (U (tnth t ord0) /\ V (tnth t (lift ord0 j)) ->
      U (tnth t ord0) /\ V (tnth [tuple of behead t] j)).
    by rewrite gmc_history_tail_coordinate.
  - change (U (tnth t ord0) /\ V (tnth [tuple of behead t] j) ->
      U (tnth t ord0) /\ V (tnth t (lift ord0 j))).
    by rewrite gmc_history_tail_coordinate. }
rewrite Hset.
transitivity (G U * gmc_standard_history n A).
- exact: gmc_standard_history_rectangle mU mA.
- exact (f_equal (fun z : \bar R => G U * z)
    (@gmc_standard_history_coordinate R n j V mV)).
Qed.

(** If both selected coordinates lie in the tail, their joint
    event has exactly the probability of the corresponding smaller
    history event. No independence hypothesis is needed here. *)
Theorem gmc_standard_history_other_other n (i j : 'I_n)
    (U V : set R) :
  measurable U -> measurable V ->
  gmc_standard_history n.+1
    [set t : n.+1.-tuple (measurableTypeR R) |
      U (tnth t (lift ord0 i)) /\ V (tnth t (lift ord0 j))] =
  gmc_standard_history n
    [set t : n.-tuple (measurableTypeR R) |
      U (tnth t i) /\ V (tnth t j)].
Proof.
move=> mU mV.
pose A := [set t : n.-tuple (measurableTypeR R) |
  U (tnth t i) /\ V (tnth t j)].
have mA : measurable A.
{ apply: measurableI.
  - exact: gmc_history_coordinate_event_measurable mU.
  - exact: gmc_history_coordinate_event_measurable mV. }
have Hset :
    [set t : n.+1.-tuple (measurableTypeR R) |
      U (tnth t (lift ord0 i)) /\ V (tnth t (lift ord0 j))] =
    [set t : n.+1.-tuple (measurableTypeR R) |
      A [tuple of behead t]].
{ apply/seteqP; split=> t.
  - change (U (tnth t (lift ord0 i)) /\ V (tnth t (lift ord0 j)) ->
      U (tnth [tuple of behead t] i) /\ V (tnth [tuple of behead t] j)).
    by rewrite !gmc_history_tail_coordinate.
  - change (U (tnth [tuple of behead t] i) /\ V (tnth [tuple of behead t] j) ->
      U (tnth t (lift ord0 i)) /\ V (tnth t (lift ord0 j))).
    by rewrite !gmc_history_tail_coordinate. }
rewrite Hset.
exact: gmc_standard_history_tail mA.
Qed.

(** Any distinct pair of coordinates is independent in the exact
    Borel rectangle sense. Induct on the history dimension, separating
    the head/head (impossible), head/tail and tail/tail cases.
    Distinctness is essential: a coordinate is not independent of itself. *)
Theorem gmc_standard_history_pair_independent n (i j : 'I_n)
    (U V : set R) :
  i != j -> measurable U -> measurable V ->
  gmc_standard_history n
    [set t : n.-tuple (measurableTypeR R) |
      U (tnth t i) /\ V (tnth t j)] = G U * G V.
Proof.
elim: n => [|n IH] in i j *.
- have Hi : (i < 0)%N := ltn_ord i.
  by rewrite ltn0 in Hi.
- case: (unliftP ord0 i) => [i' ->|->];
    case: (unliftP ord0 j) => [j' ->|->].
  + move=> Hij mU mV.
    have Hneq : i' != j'.
    { apply/eqP => He; subst j'.
      by rewrite eqxx in Hij. }
    transitivity (gmc_standard_history n
      [set t : n.-tuple (measurableTypeR R) |
        U (tnth t i') /\ V (tnth t j')]).
    * exact: gmc_standard_history_other_other mU mV.
    * exact (IH i' j' Hneq mU mV).
  + move=> _ mU mV.
    have Hset :
        [set t : n.+1.-tuple (measurableTypeR R) |
          U (tnth t (lift ord0 i')) /\ V (tnth t ord0)] =
        [set t : n.+1.-tuple (measurableTypeR R) |
          V (tnth t ord0) /\ U (tnth t (lift ord0 i'))].
    { apply/seteqP; split=> t H; exact (conj (proj2 H) (proj1 H)). }
    rewrite Hset.
    transitivity (G V * G U).
    * exact: gmc_standard_history_head_other mV mU.
    * exact: muleC.
  + move=> _ mU mV.
    exact: gmc_standard_history_head_other mU mV.
  + by rewrite eqxx.
Qed.
End FiniteIndependence.
