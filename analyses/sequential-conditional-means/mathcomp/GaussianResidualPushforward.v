(** Module: GaussianResidualPushforward.v
    Purpose: Identify the residual law on the actual scalar Gaussian
    joint measure, rather than merely factor a density. Reuse the
    verified joint-measure Tonelli representation, original-coordinate
    rectangle theorem, and MathComp product-measure uniqueness.
    Coordinate order: (observation, latent) -> (observation, residual).
    Nonzero Gaussian scales are required; degenerate laws and the
    finite-dimensional Gaussian and FormalML bridges remain separate.
    Researcher/requester: Anders Hellström.
    AI disclosure: AI-assisted proof candidates; validation pending.
*)
From HB Require Import structures.
From mathcomp Require Import boot order ssralg ssrnum.
From mathcomp Require Import boolp classical_sets functions reals ereal topology normedtype.
From mathcomp Require Import numfun measure lebesgue_integral
  lebesgue_stieltjes_measure lebesgue_measure measurable_realfun.
From mathcomp.analysis Require Import normal_distribution.
Require Import GaussianResidualMeasure GaussianOriginalResidualMeasure
  GaussianJointDensityMeasure.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section ResidualPushforward.
Context {R : realType}.
Import MeasurableR.
Local Abbreviation mu := (@lebesgue_measure R).
Local Abbreviation BorelPair := ((measurableTypeR R * measurableTypeR R)%type).

(** The posterior center is an affine, hence Borel-measurable,
    function of the observation. The denominator is a fixed scalar;
    measurability itself does not require that scalar to be nonzero. *)
Lemma gmc_post_mean_measurable (m0 s0 s : R) :
  measurable_fun [set: R] (fun x : R => post_mean m0 s0 x s).
Proof.
rewrite /post_mean.
apply: measurable_funM.
- apply: measurable_funD.
  + exact: measurable_cst.
  + apply: measurable_funM.
    * exact: measurable_cst.
    * exact: measurable_id.
- exact: measurable_cst.
Qed.

(** Keep the observation and subtract its posterior center from
    the latent variable. This is a map of the actual Borel pair. *)
Definition gmc_residual_map (m0 s0 s : R) (z : R * R) : R * R :=
  (z.1, z.2 - post_mean m0 s0 z.1 s).

(** Joint Borel measurability of the observation/residual map follows
    from the measurable projections, affine center and subtraction. *)
Theorem gmc_residual_map_measurable (m0 s0 s : R) :
  measurable_fun [set: BorelPair] (gmc_residual_map m0 s0 s).
Proof.
rewrite /gmc_residual_map.
apply: measurable_fun_pair.
- exact: measurable_fst.
- apply: measurable_funB.
  + exact: measurable_snd.
  + apply: measurableT_comp.
    * exact: gmc_post_mean_measurable.
    * exact: measurable_fst.
Qed.

HB.instance Definition _ m0 s0 s :=
  isMeasurableFun.Build _ _ _ _ (gmc_residual_map m0 s0 s)
    (gmc_residual_map_measurable m0 s0 s).

(** A section of a residual rectangle preimage is exactly the
    scalar translated residual event if the observation lies in U,
    and is empty otherwise. This is a set identity, not a density
    or probability hypothesis. *)
Lemma gmc_residual_rectangle_section (m0 s0 s x : R) (U V : set R) :
  xsection (gmc_residual_map m0 s0 s @^-1` (U `*` V)) x =
  (if x \in U then
     gmc_translate (post_mean m0 s0 x s) @^-1` V
   else set0).
Proof.
case: ifPn => Hx.
- have ux : U x by move: Hx; rewrite inE.
  apply/seteqP; split => t.
  + move/xsectionP => Ht.
    change (U x /\ V (t - post_mean m0 s0 x s)) in Ht.
    exact (proj2 Ht).
  + move=> Ht; apply/xsectionP.
    change (U x /\ V (t - post_mean m0 s0 x s)).
    exact (conj ux Ht).
- have nx : ~ U x by move: Hx; rewrite notin_setE.
  apply/seteqP; split => t.
  + move/xsectionP => Ht.
    change (U x /\ V (t - post_mean m0 s0 x s)) in Ht.
    exact (nx (proj1 Ht)).
  + by move=> [].
Qed.

Local Open Scope ereal_scope.

(** The pushforward on every measurable residual rectangle factors
    into the two Gaussian marginal measures. The Tonelli theorem
    connects the actual joint event to the already verified original
    coordinate density integral. No independence is assumed. *)
Theorem gmc_residual_pushforward_rectangle
    (m0 s0 s : R) (U V : set R) :
  s0 != 0%R -> s != 0%R -> measurable U -> measurable V ->
  pushforward (gmc_joint_mass m0 s0 s) (gmc_residual_map m0 s0 s)
    (U `*` V) =
  normal_prob m0 (Num.sqrt (s0 ^+ 2 + s ^+ 2)) U *
  normal_prob 0%R (post_stddev s0 s) V.
Proof.
move=> Hs0 Hs mU mV.
pose A := gmc_residual_map m0 s0 s @^-1` (U `*` V).
have mUV : measurable (U `*` V).
{ exact: measurableX. }
have mA : measurable A.
{ rewrite /A -[X in measurable X]setTI.
  exact (@gmc_residual_map_measurable m0 s0 s
    measurableT (U `*` V) mUV). }
change (gmc_joint_mass m0 s0 s A = _).
etransitivity; last exact (@gmc_original_residual_rectangle R
  m0 s0 s U V Hs0 Hs mU mV).
rewrite (@gmc_joint_mass_sections R m0 s0 s A Hs mA).
rewrite [RHS]integral_mkcond.
apply: eq_integral => x _.
rewrite /A (@gmc_residual_rectangle_section m0 s0 s x U V) patchE.
case: ifPn => Hx.
- apply: eq_integral => t _.
  by rewrite /gmc_joint_density.
- exact: integral_set0.
Qed.

(** Normalization of the actual joint measure. The full residual
    rectangle has preimage equal to the whole pair space, and both
    Gaussian marginal measures have total mass one. *)
Theorem gmc_joint_probability_mass (m0 s0 s : R) :
  s0 != 0%R -> s != 0%R ->
  gmc_joint_mass m0 s0 s setT = 1.
Proof.
move=> Hs0 Hs.
have Hrect := @gmc_residual_pushforward_rectangle
  m0 s0 s [set: R] [set: R] Hs0 Hs measurableT measurableT.
rewrite setXTT /pushforward preimage_setT in Hrect.
by rewrite !probability_setT mule1 in Hrect.
Qed.

(** Every measurable event of the residual pair has the product
    Gaussian law, by uniqueness of the product measure. The measure
    certificate is explicitly instantiated at the nonzero scale
    rather than treating Gaussian independence as a premise. *)
Theorem gmc_residual_pushforward_product
    (m0 s0 s : R) (A : set BorelPair) :
  s0 != 0%R -> s != 0%R -> measurable A ->
  pushforward (gmc_joint_mass m0 s0 s) (gmc_residual_map m0 s0 s) A =
  (normal_prob m0 (Num.sqrt (s0 ^+ 2 + s ^+ 2)) \x
    normal_prob 0%R (post_stddev s0 s)) A.
Proof.
move=> Hs0 Hs mA.
pose J : {measure set BorelPair -> \bar R} :=
  @GaussianJointDensityMeasure_gmc_joint_mass__canonical__measure_function_Measure
    R m0 s0 s Hs.
pose P : {measure set BorelPair -> \bar R} :=
  pushforward J (gmc_residual_map m0 s0 s).
change (P A =
  (normal_prob m0 (Num.sqrt (s0 ^+ 2 + s ^+ 2)) \x
    normal_prob 0%R (post_stddev s0 s)) A).
symmetry.
apply: (@product_measure_unique _ _ (measurableTypeR R)
  (measurableTypeR R) R
  (normal_prob m0 (Num.sqrt (s0 ^+ 2 + s ^+ 2)))
  (normal_prob 0%R (post_stddev s0 s)) P).
- move=> U V mU mV.
  exact: (@gmc_residual_pushforward_rectangle m0 s0 s U V Hs0 Hs mU mV).
- exact: mA.
Qed.
End ResidualPushforward.
