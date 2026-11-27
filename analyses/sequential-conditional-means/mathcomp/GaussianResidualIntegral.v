(** Module: GaussianResidualIntegral.v
    Purpose: Transport nonnegative and signed integrals and absolute
    integrability from the verified observation/residual product law
    to the actual observation/latent joint measure. Establish the
    pointwise first moment of the actual Gaussian posterior kernel.
    These are bridges toward the defining event-integral conditional
    expectation identity; that identity is not assumed here.
    Reuse MathComp-Analysis pushforward integration and measure
    equality, and the independently verified Gaussian moment results.
    Researcher/requester: Anders Hellström.
    AI disclosure: AI-assisted proof candidates; validation pending.
*)
From mathcomp Require Import boot order ssralg ssrnum.
From mathcomp Require Import boolp classical_sets functions reals ereal topology normedtype.
From mathcomp Require Import numfun measure lebesgue_integral
  lebesgue_stieltjes_measure lebesgue_measure measurable_realfun.
From mathcomp.analysis Require Import normal_distribution.
Require Import GaussianJointDensityMeasure GaussianResidualPushforward
  GaussianPosteriorKernel GaussianLocationMean.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section ResidualIntegral.
Context {R : realType}.
Import MeasurableR.
Local Abbreviation BorelPair := ((measurableTypeR R * measurableTypeR R)%type).
Local Open Scope ereal_scope.
Variables (m0 s0 s : R).
Hypotheses (Hs0 : s0 != 0%R) (Hs : s != 0%R).

(* Keep the actual joint measure certificate explicit: the packed
   measure is constructed from the proved nonzero-scale measure laws.
   The product measure is the independently verified residual law. *)
Local Abbreviation J :=
  (@GaussianJointDensityMeasure_gmc_joint_mass__canonical__measure_function_Measure
    R m0 s0 s Hs).
Local Abbreviation P :=
  (normal_prob m0 (gmc_observation_scale s0 s) \x
   normal_prob 0%R (post_stddev s0 s)).
Local Abbreviation phi := (gmc_residual_map m0 s0 s).

(** Every nonnegative measurable function of the observation and
    residual has the same integral under the product law as its
    composition with the actual residual map under the joint law.
    This does not require integrability or assume independence. *)
Theorem gmc_residual_nonnegative_integral (f : BorelPair -> \bar R) :
  measurable_fun [set: BorelPair] f ->
  (forall z : BorelPair, 0 <= f z) ->
  \int[P]_z f z = \int[J]_z f (phi z).
Proof.
move=> mf f0.
have mp : measurable_fun [set: BorelPair] phi.
{ exact: gmc_residual_map_measurable. }
have preT : phi @^-1` [set: BorelPair] = [set: BorelPair].
{ exact: preimage_setT. }
transitivity (\int[pushforward J phi]_z f z).
- symmetry.
  apply: (eq_measure_integral P) => A mA _.
  exact (@gmc_residual_pushforward_product R m0 s0 s A Hs0 Hs mA).
- have H := @ge0_integral_pushforward _ _ BorelPair BorelPair
    R phi mp J setT f measurableT mf (fun z _ => f0 z).
  rewrite preT in H.
  exact: H.
Qed.

(** Absolute integrability transports from the residual product law
    to the original joint law, using the nonnegative theorem on the
    absolute value. In particular this supplies a signed integration
    premise rather than introducing a moment assumption on J. *)
Theorem gmc_residual_integrable (f : BorelPair -> \bar R) :
  P.-integrable [set: BorelPair] f ->
  J.-integrable [set: BorelPair] (fun z => f (phi z)).
Proof.
move=> fi.
have /integrableP [mf Hfin] := fi.
have mp : measurable_fun [set: BorelPair] phi.
{ exact: gmc_residual_map_measurable. }
have ma : measurable_fun [set: \bar R] (@abse R).
{ exact: abse_measurable. }
have maf : measurable_fun [set: BorelPair] (fun z => `|f z|).
{ exact: measurableT_comp ma mf. }
have af0 (z : BorelPair) : 0 <= `|f z|.
{ exact: abse_ge0. }
apply/integrableP; split.
- exact: measurableT_comp mf mp.
- have H := @gmc_residual_nonnegative_integral
    (fun z => `|f z|) maf af0.
  rewrite -H.
  exact: Hfin.
Qed.

(** Signed integral transport through the actual residual map.
    Integrability on the joint space follows from the preceding
    theorem, so the signed pushforward identity is legitimate. *)
Theorem gmc_residual_signed_integral (f : BorelPair -> \bar R) :
  P.-integrable [set: BorelPair] f ->
  \int[P]_z f z = \int[J]_z f (phi z).
Proof.
move=> fi.
have mp : measurable_fun [set: BorelPair] phi.
{ exact: gmc_residual_map_measurable. }
have mf : measurable_fun [set: BorelPair] f.
{ exact: measurable_int fi. }
have preT : phi @^-1` [set: BorelPair] = [set: BorelPair].
{ exact: preimage_setT. }
have intcomp : J.-integrable (phi @^-1` [set: BorelPair]) (f \o phi).
{ rewrite preT.
  exact (@gmc_residual_integrable f fi). }
transitivity (\int[pushforward J phi]_z f z).
- symmetry.
  apply: (eq_measure_integral P) => A mA _.
  exact (@gmc_residual_pushforward_product R m0 s0 s A Hs0 Hs mA).
- have H := @integral_pushforward _ _ BorelPair BorelPair
    R phi mp J setT f mf intcomp measurableT.
  rewrite preT in H.
  exact: H.
Qed.

(** The first absolute moment of every posterior normal probability
    measure is finite. Its scale is nonzero by the upstream positive
    posterior-scale theorem; no posterior moment premise is needed. *)
Theorem gmc_posterior_first_moment_integrable (x : R) :
  (normal_prob (post_mean m0 s0 x s) (post_stddev s0 s)).-integrable
    [set: R] (fun t : R => t%:E).
Proof.
have hp : (0 < post_stddev s0 s)%R.
{ exact: post_stddev_gt0 Hs0 Hs. }
have hn : post_stddev s0 s != 0%R.
{ by rewrite (gt_eqF hp). }
exact (@gmc_normal_first_moment_integrable R
  (post_mean m0 s0 x s) (post_stddev s0 s) hn).
Qed.

(** The posterior distribution's signed first moment is exactly its
    affine location at every observation, not only almost everywhere.
    The separately verified posterior rectangle identity identifies
    this normal law as the actual conditional event kernel. *)
Theorem gmc_posterior_first_moment (x : R) :
  \int[normal_prob (post_mean m0 s0 x s) (post_stddev s0 s)]_t t%:E =
    (post_mean m0 s0 x s)%:E.
Proof.
have hp : (0 < post_stddev s0 s)%R.
{ exact: post_stddev_gt0 Hs0 Hs. }
have hn : post_stddev s0 s != 0%R.
{ by rewrite (gt_eqF hp). }
exact (@gmc_normal_mean R (post_mean m0 s0 x s) (post_stddev s0 s) hn).
Qed.
End ResidualIntegral.
