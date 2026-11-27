(** Module: GaussianObservationSigma.v
    Purpose: Package the actual conditioning sigma algebra using
    MathComp's existing preimage-generated measurable type, and
    prove conditional-mean measurability and uniqueness on that
    sigma algebra. The observation marginal is the verified
    Gaussian law, and every observation-measurable function has
    a Borel representative by the explicit section x |-> (x,0).
    Use the library's integral_ae_eq for uniqueness, rather than
    constructing a new conditional-expectation operator.
    Researcher/requester: Anders Hellström.
    AI disclosure: AI-assisted proof candidates; validation pending.
*)
From mathcomp Require Import boot order ssralg ssrnum.
From mathcomp Require Import boolp classical_sets functions reals ereal topology normedtype.
From mathcomp Require Import numfun measure lebesgue_integral
  lebesgue_stieltjes_measure lebesgue_measure measurable_realfun.
From mathcomp.analysis Require Import normal_distribution.
Require Import GaussianJointDensityMeasure GaussianResidualPushforward
  GaussianPosteriorKernel GaussianScalarConditionalMean.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section ObservationSigma.
Context {R : realType}.
Import MeasurableR.
Local Abbreviation BorelPair := ((measurableTypeR R * measurableTypeR R)%type).
Local Abbreviation obs := (fst : BorelPair -> measurableTypeR R).
Local Abbreviation ObsSpace := (g_sigma_algebra_preimageType obs).
Local Open Scope ereal_scope.

(** The canonical preimage-generated sigma algebra consists exactly
    of observation cylinders. This uses the existing library's
    measurable structure, not a new sigma-algebra construction. *)
Theorem gmc_observation_sigma_events (A : set BorelPair) :
  measurable (A : set ObsSpace) <->
  exists U : set R, measurable U /\ A = U `*` [set: R].
Proof.
change (g_sigma_algebra_preimage obs A <-> _).
split.
- move=> [U mU H].
  exists U; split=> //.
  symmetry.
  move: H.
  by rewrite setTI -setXT.
- move=> [U [mU HA]].
  exists U => //.
  by rewrite setTI -setXT HA.
Qed.

(** Every event in the conditioning sigma algebra is measurable
    in the full joint Borel sigma algebra. *)
Theorem gmc_observation_sigma_sub (A : set BorelPair) :
  measurable (A : set ObsSpace) -> measurable A.
Proof.
move/gmc_observation_sigma_events => [U [mU ->]].
exact: measurableX mU measurableT.
Qed.

(** A Borel scalar representative composed with the first projection
    is measurable on the actual conditioning sigma algebra. *)
Theorem gmc_observation_factor_measurable (f : R -> \bar R) :
  measurable_fun [set: R] f ->
  measurable_fun [set: ObsSpace] (fun z : ObsSpace => f z.1).
Proof.
move=> mf _ V mV.
apply/gmc_observation_sigma_events.
exists (f @^-1` V); split.
- have H := mf measurableT V mV.
  by rewrite setTI in H.
- apply/seteqP; split.
  + by move=> [x t] [_ H]; split.
  + by move=> [x t] [H _]; split.
Qed.

(** Conversely, an arbitrary extended-real observation-measurable
    function is constant along every latent fiber.  Use the
    measurable singleton containing its value at (x,0). *)
Theorem gmc_observation_fiber_constant (h : ObsSpace -> \bar R) :
  measurable_fun [set: ObsSpace] h ->
  forall x t : R, h (x,t) = h (x,0%R).
Proof.
move=> mh x t.
pose V := [set h (x,0%R)].
have mV : measurable V.
{ exact: emeasurable_set1. }
have H := mh measurableT V mV.
rewrite setTI in H.
move/gmc_observation_sigma_events: H => [U [mU HA]].
have H0 : (h @^-1` V) (x,0%R).
{ by []. }
rewrite HA in H0.
have Ht : (h @^-1` V) (x,t).
{ rewrite HA.
  exact (conj (proj1 H0) I). }
exact Ht.
Qed.

(** The Borel representative obtained from the section (x,0)
    is measurable. The preimage of every Borel value set is
    obtained by taking the section of an observation cylinder. *)
Theorem gmc_observation_factorization (h : ObsSpace -> \bar R) :
  measurable_fun [set: ObsSpace] h ->
  exists f : R -> \bar R, measurable_fun [set: R] f /\
    forall z : BorelPair, h z = f z.1.
Proof.
move=> mh.
exists (fun x : R => h (x,0%R)); split.
- move=> _ V mV.
  have H := mh measurableT V mV.
  rewrite setTI in H.
  move/gmc_observation_sigma_events: H => [U [mU HA]].
  have Heq : [set: R] `&` (fun x : R => h (x,0%R)) @^-1` V = U.
  { apply/seteqP; split.
    - move=> x [_ Hx].
      have H0 : (h @^-1` V) (x,0%R) := Hx.
      rewrite HA in H0.
      exact (proj1 H0).
    - move=> x Hx; split; first exact I.
      have H0 : (h @^-1` V) (x,0%R).
      { rewrite HA; exact (conj Hx I). }
      exact H0. }
  rewrite Heq.
  exact mU.
- move=> [x t].
  exact (@gmc_observation_fiber_constant h mh x t).
Qed.

Variables (m0 s0 s : R).
Hypotheses (Hs0 : s0 != 0%R) (Hs : s != 0%R).
Local Abbreviation J :=
  (@GaussianJointDensityMeasure_gmc_joint_mass__canonical__measure_function_Measure
    R m0 s0 s Hs).
Local Abbreviation QX := (normal_prob m0 (gmc_observation_scale s0 s)).
Local Abbreviation M := (fun x : R => (post_mean m0 s0 x s)%:E).

(** The posterior candidate is measurable in the actual generated
    observation sigma algebra, using the checked scalar affine
    measurability and the preceding generic factor lemma. *)
Theorem gmc_conditional_mean_sigma_measurable :
  measurable_fun [set: ObsSpace] (fun z : ObsSpace => M z.1).
Proof.
apply: gmc_observation_factor_measurable.
apply/measurable_EFinP.
exact: gmc_post_mean_measurable.
Qed.

(** The verified observation marginal identifies the pushforward
    measure on all Borel events, now expressed as a direct measure
    equality certificate for the integral transport proofs. *)
Theorem gmc_observation_pushforward_event (U : set R) :
  measurable U -> pushforward J obs U = QX U.
Proof.
move=> mU.
change (gmc_joint_mass m0 s0 s (obs @^-1` U) = QX U).
rewrite -setXT.
exact (@gmc_observation_marginal R m0 s0 s U Hs0 Hs mU).
Qed.

(** Integrals of nonnegative observation functions transfer from the
    actual marginal to the joint space, without integrability. *)
Theorem gmc_observation_nonnegative_integral (f : R -> \bar R)
    (U : set R) :
  measurable U -> measurable_fun [set: R] f ->
  (forall x : R, 0 <= f x) ->
  \int[QX]_(x in U) f x = \int[J]_(z in U `*` [set: R]) f z.1.
Proof.
move=> mU mf f0.
have mo : measurable_fun [set: BorelPair] obs.
{ exact: measurable_fst. }
have mfu : measurable_fun U f.
{ exact: measurable_funTS mf. }
transitivity (\int[pushforward J obs]_(x in U) f x).
- symmetry.
  apply: (eq_measure_integral QX) => A mA _.
  exact: gmc_observation_pushforward_event.
- have H := @ge0_integral_pushforward _ _ BorelPair (measurableTypeR R)
    R obs mo J U f mU mfu (fun x _ => f0 x).
  rewrite -setXT in H.
  exact H.
Qed.

(** Integrability under the joint measure of a Borel observation
    function implies integrability under its Gaussian marginal.
    Apply nonnegative transport to its absolute value. *)
Theorem gmc_observation_marginal_integrable (f : R -> \bar R) :
  measurable_fun [set: R] f ->
  J.-integrable [set: BorelPair] (fun z => f z.1) ->
  QX.-integrable [set: R] f.
Proof.
move=> mf fi.
have /integrableP [_ Hfin] := fi.
have ma : measurable_fun [set: \bar R] (@abse R).
{ exact: abse_measurable. }
have maf : measurable_fun [set: R] (fun x => `|f x|).
{ exact: measurableT_comp ma mf. }
have af0 (x : R) : 0 <= `|f x|.
{ exact: abse_ge0. }
have H := @gmc_observation_nonnegative_integral
  (fun x => `|f x|) setT measurableT maf af0.
rewrite setXTT in H.
apply/integrableP; split=> //.
by rewrite H.
Qed.

(** Signed observation integrals transport on arbitrary Borel events.
    Restrict the already integrable joint observation function
    before invoking the library's signed pushforward theorem. *)
Theorem gmc_observation_signed_integral (f : R -> \bar R)
    (U : set R) :
  measurable U -> measurable_fun [set: R] f ->
  J.-integrable [set: BorelPair] (fun z => f z.1) ->
  \int[QX]_(x in U) f x = \int[J]_(z in U `*` [set: R]) f z.1.
Proof.
move=> mU mf fi.
have mo : measurable_fun [set: BorelPair] obs.
{ exact: measurable_fst. }
have mA : measurable (U `*` [set: R]).
{ exact: measurableX mU measurableT. }
have intcomp : J.-integrable (obs @^-1` U) (f \o obs).
{ rewrite -setXT.
  exact: (integrableS measurableT mA (subsetT _) fi). }
transitivity (\int[pushforward J obs]_(x in U) f x).
- symmetry.
  apply: (eq_measure_integral QX) => A mA' _.
  exact: gmc_observation_pushforward_event.
- have H := @integral_pushforward _ _ BorelPair (measurableTypeR R)
    R obs mo J U f mf intcomp mU.
  rewrite -setXT in H.
  exact H.
Qed.

(** The conditional mean satisfies the defining identity on every
    event of the actual packaged conditioning sigma algebra. *)
Theorem gmc_conditional_mean_sigma_event (A : set BorelPair) :
  measurable (A : set ObsSpace) ->
  \int[J]_(z in A) z.2%:E = \int[J]_(z in A) M z.1.
Proof.
move/gmc_observation_sigma_events => [U [mU ->]].
exact (@gmc_joint_conditional_mean_event R m0 s0 s Hs0 Hs U mU).
Qed.

(** Almost-everywhere uniqueness on the original joint space.
    Any integrable candidate measurable in the conditioning sigma
    algebra and satisfying the same defining integral identity
    factors through the observation. Transport the equality of
    event integrals to the marginal; use integral_ae_eq there.
    Pull the resulting marginal null witness back by the observation
    map, whose pushforward measure has already been identified. *)
Theorem gmc_conditional_mean_unique (h : ObsSpace -> \bar R) :
  measurable_fun [set: ObsSpace] h ->
  J.-integrable [set: BorelPair] h ->
  (forall A : set BorelPair, measurable (A : set ObsSpace) ->
    \int[J]_(z in A) z.2%:E = \int[J]_(z in A) h z) ->
  ae_eq J [set: BorelPair] h (fun z => M z.1).
Proof.
move=> mh hi hE.
have [f [mf Hf]] := @gmc_observation_factorization h mh.
have Hfun : h = (fun z : BorelPair => f z.1).
{ apply/funext; exact Hf. }
rewrite Hfun in hi hE *.
have fi : QX.-integrable [set: R] f.
{ exact (@gmc_observation_marginal_integrable f mf hi). }
have mM : measurable_fun [set: R] M.
{ apply/measurable_EFinP; exact: gmc_post_mean_measurable. }
have Mi : J.-integrable [set: BorelPair] (fun z => M z.1).
{ exact (@gmc_joint_posterior_mean_integrable R m0 s0 s Hs0 Hs). }
have Hints (U : set R) : measurable U ->
    \int[QX]_(x in U) f x = \int[QX]_(x in U) M x.
{ move=> mU.
  have mA : measurable ((U `*` [set: R]) : set ObsSpace).
  { apply/gmc_observation_sigma_events.
    by exists U. }
  transitivity (\int[J]_(z in U `*` [set: R]) f z.1).
  - exact (@gmc_observation_signed_integral f U mU mf hi).
  - transitivity (\int[J]_(z in U `*` [set: R]) z.2%:E).
    + symmetry; exact (hE _ mA).
    + transitivity (\int[J]_(z in U `*` [set: R]) M z.1).
      * exact (@gmc_conditional_mean_sigma_event _ mA).
      * symmetry; exact (@gmc_observation_signed_integral M U mU mM Mi). }
have Hae : ae_eq QX [set: R] f M.
{ apply: (@integral_ae_eq _ (measurableTypeR R) R QX
    setT measurableT M f fi mM).
  move=> U _ mU.
  exact: Hints. }
move: Hae => [N [mN HN Hbad]].
exists (obs @^-1` N); split.
- rewrite -setXT.
  exact: measurableX mN measurableT.
- change (gmc_joint_mass m0 s0 s (obs @^-1` N) = 0).
  rewrite -setXT.
  transitivity (QX N).
  + exact (@gmc_observation_marginal R m0 s0 s N Hs0 Hs mN).
  + exact HN.
- move=> z Hz.
  change (N z.1).
  apply: Hbad.
  apply/not_implyP; split; first exact I.
  move=> He.
  apply: Hz.
  by move=> _.
Qed.
End ObservationSigma.
