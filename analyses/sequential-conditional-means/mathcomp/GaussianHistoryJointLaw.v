(** Module: GaussianHistoryJointLaw.v
    Purpose: Transport the independently verified generic product
    conditional-mean theorem to an arbitrary original probability
    space via the joint observation/residual pushforward law.
    This is a reusable measure-theoretic bridge for histories of
    arbitrary dimension, not a proof that a multivariate Gaussian
    has the required product law. The law equality is explicit.
    Reuse MathComp pushforward integration and GaussianProductHistory.
    Researcher/requester: Anders Hellström.
    AI disclosure: AI-assisted proof candidates; validation pending.
*)
From mathcomp Require Import boot order ssralg ssrnum.
From mathcomp Require Import boolp classical_sets functions reals ereal topology normedtype.
From mathcomp Require Import numfun measure lebesgue_integral
  lebesgue_stieltjes_measure lebesgue_measure measurable_realfun.
Require Import GaussianProductHistory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section HistoryJointLaw.
Context {dO dX dE : measure_display}.
Context {O : measurableType dO} {X : measurableType dX}
        {E : measurableType dE}.
Context {R : realType}.
Local Open Scope ereal_scope.
Variables (J : probability O R) (QX : probability X R)
          (QE : probability E R).
Variables (obs : O -> X) (err : O -> E).
Hypotheses (mobs : measurable_fun [set: O] obs)
           (merr : measurable_fun [set: O] err).
Local Abbreviation Pair := ((X * E)%type).
Local Abbreviation P := (QX \x QE).
Local Abbreviation phi := (fun w : O => (obs w, err w)).
Hypothesis Hlaw : forall A : set Pair, measurable A ->
  pushforward J phi A = P A.

(** The observation/residual pair map is measurable by the existing
    product measurability theorem. *)
Lemma gmc_history_pair_measurable :
  measurable_fun [set: O] phi.
Proof. exact: measurable_fun_pair mobs merr. Qed.

(** Nonnegative integral transport over every measurable event in
    the product space. No integrability premise is required. *)
Theorem gmc_history_nonnegative_transport (f : Pair -> \bar R)
    (A : set Pair) :
  measurable A -> measurable_fun [set: Pair] f ->
  (forall z : Pair, 0 <= f z) ->
  \int[P]_(z in A) f z =
    \int[J]_(w in phi @^-1` A) f (phi w).
Proof.
move=> mA mf f0.
have mphi : measurable_fun [set: O] phi.
{ exact: gmc_history_pair_measurable. }
have mfa : measurable_fun A f.
{ exact: measurable_funTS mf. }
transitivity (\int[pushforward J phi]_(z in A) f z).
- symmetry.
  apply: (eq_measure_integral P) => B mB _.
  exact: Hlaw.
- exact (@ge0_integral_pushforward _ _ O Pair R
    phi mphi J A f mA mfa (fun z _ => f0 z)).
Qed.

(** Integrability on the original space follows from integrability
    under the product law, by transporting the absolute value. *)
Theorem gmc_history_integrable_transport (f : Pair -> \bar R) :
  P.-integrable [set: Pair] f ->
  J.-integrable [set: O] (fun w => f (phi w)).
Proof.
move=> fi.
have /integrableP [mf Hfin] := fi.
have ma : measurable_fun [set: \bar R] (@abse R).
{ exact: abse_measurable. }
have maf : measurable_fun [set: Pair] (fun z => `|f z|).
{ exact: measurableT_comp ma mf. }
have af0 (z : Pair) : 0 <= `|f z|.
{ exact: abse_ge0. }
have H := @gmc_history_nonnegative_transport
  (fun z => `|f z|) setT measurableT maf af0.
rewrite preimage_setT in H.
apply/integrableP; split.
- exact: measurableT_comp mf gmc_history_pair_measurable.
- by rewrite -H.
Qed.

(** Signed integral transport over arbitrary measurable product
    events, with the original-space integrability premise derived
    from the verified product law rather than postulated. *)
Theorem gmc_history_signed_transport (f : Pair -> \bar R)
    (A : set Pair) :
  measurable A -> P.-integrable [set: Pair] f ->
  \int[P]_(z in A) f z =
    \int[J]_(w in phi @^-1` A) f (phi w).
Proof.
move=> mA fi.
have mphi : measurable_fun [set: O] phi.
{ exact: gmc_history_pair_measurable. }
have mf : measurable_fun [set: Pair] f.
{ exact: measurable_int fi. }
have mpre : measurable (phi @^-1` A).
{ rewrite -[X in measurable X]setTI.
  exact (mphi measurableT A mA). }
have intcomp : J.-integrable (phi @^-1` A) (f \o phi).
{ exact: (integrableS measurableT mpre (subsetT _)
    (@gmc_history_integrable_transport f fi)). }
transitivity (\int[pushforward J phi]_(z in A) f z).
- symmetry.
  apply: (eq_measure_integral P) => B mB _.
  exact: Hlaw.
- exact (@integral_pushforward _ _ O Pair R phi mphi
    J A f mf intcomp mA).
Qed.

(** The preimage of an observation cylinder under the joint map
    is exactly the corresponding event of the original observation. *)
Lemma gmc_history_observation_preimage (U : set X) :
  phi @^-1` (U `*` [set: E]) = obs @^-1` U.
Proof.
apply/seteqP; split.
- move=> w Hw.
  exact (proj1 Hw).
- move=> w Hw.
  exact (conj Hw I).
Qed.

(** Original-space integrability of the additive model follows by
    composing the generic product-integrability theorem and the
    verified-law transport. The two terms are extended real;
    applications to real Gaussian coordinates use EFin embeddings. *)
Theorem gmc_history_additive_integrable (m : X -> \bar R)
    (e : E -> \bar R) :
  QX.-integrable [set: X] m -> QE.-integrable [set: E] e ->
  J.-integrable [set: O] (fun w => m (obs w) + e (err w)).
Proof.
move=> mi ei.
have pi : P.-integrable [set: Pair] (fun z => m z.1 + e z.2).
{ exact (@gmc_product_additive_integrable _ _ X E R QX QE m e mi ei). }
exact (@gmc_history_integrable_transport (fun z => m z.1 + e z.2) pi).
Qed.

(** Integrability of the proposed original-space conditional mean
    is transferred from its observation marginal. *)
Theorem gmc_history_mean_integrable (m : X -> \bar R) :
  QX.-integrable [set: X] m ->
  J.-integrable [set: O] (fun w => m (obs w)).
Proof.
move=> mi.
have pi : P.-integrable [set: Pair] (fun z => m z.1).
{ exact (@gmc_product_fst_integrable _ _ X E R QX QE m mi). }
exact (@gmc_history_integrable_transport (fun z => m z.1) pi).
Qed.

(** A zero-mean integrable residual and the supplied product-law
    certificate imply the conditional-mean identity on every event
    of the original observation. Independence is a consequence
    of the law certificate, not a Gaussian theorem proved here. *)
Theorem gmc_history_conditional_mean_event (m : X -> \bar R)
    (e : E -> \bar R) (U : set X) :
  QX.-integrable [set: X] m -> QE.-integrable [set: E] e ->
  \int[QE]_y e y = 0 -> measurable U ->
  \int[J]_(w in obs @^-1` U) (m (obs w) + e (err w)) =
  \int[J]_(w in obs @^-1` U) m (obs w).
Proof.
move=> mi ei ez mU.
pose A : set Pair := U `*` [set: E].
have mA : measurable A.
{ exact: measurableX mU measurableT. }
have pi : P.-integrable [set: Pair] (fun z => m z.1 + e z.2).
{ exact (@gmc_product_additive_integrable _ _ X E R QX QE m e mi ei). }
have qi : P.-integrable [set: Pair] (fun z => m z.1).
{ exact (@gmc_product_fst_integrable _ _ X E R QX QE m mi). }
have Ha := @gmc_history_signed_transport (fun z => m z.1 + e z.2) A mA pi.
have Hm := @gmc_history_signed_transport (fun z => m z.1) A mA qi.
have Hpre : phi @^-1` A = obs @^-1` U.
{ exact: gmc_history_observation_preimage. }
rewrite Hpre in Ha Hm.
transitivity (\int[P]_(z in A) (m z.1 + e z.2)).
- symmetry; exact Ha.
- transitivity (\int[P]_(z in A) m z.1).
  + exact (@gmc_product_additive_mean_event _ _ X E R QX QE m e U mi ei ez mU).
  + exact Hm.
Qed.
End HistoryJointLaw.
