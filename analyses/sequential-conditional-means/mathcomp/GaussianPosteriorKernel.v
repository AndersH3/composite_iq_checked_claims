(** Module: GaussianPosteriorKernel.v
    Purpose: Derive the scalar posterior probability kernel directly
    on the independently checked Gaussian joint density measure.
    Prove measurability, bounded integrability, the conditional event
    identity for all Borel rectangles, and the observation marginal.
    Reuse MathComp normal conjugacy, kernel measurability, Tonelli,
    and integration against a normal measure.
    The unbounded first moment and general Gaussian histories remain
    separate obligations; this is the conditional distribution step.
    Researcher/requester: Anders Hellström.
    AI disclosure: AI-assisted proof candidates; validation pending.
*)
From mathcomp Require Import boot order ssralg ssrnum.
From mathcomp Require Import boolp classical_sets functions reals ereal topology normedtype.
From mathcomp Require Import numfun measure lebesgue_integral
  lebesgue_stieltjes_measure lebesgue_measure measurable_realfun.
From mathcomp.analysis Require Import normal_distribution.
Require Import GaussianJointDensityMeasure GaussianResidualPushforward.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section PosteriorKernel.
Context {R : realType}.
Import MeasurableR.
Local Abbreviation mu := (@lebesgue_measure R).

(** The observation marginal scale is constant in the observation. *)
Definition gmc_observation_scale (s0 s : R) : R :=
  Num.sqrt (s0 ^+ 2 + s ^+ 2).

(** The posterior event probability at a given observation, expressed
    using the existing normal probability measure rather than a
    custom probability distribution. *)
Definition gmc_posterior_kernel (m0 s0 s x : R) (V : set R) : \bar R :=
  normal_prob (post_mean m0 s0 x s) (post_stddev s0 s) V.

Local Open Scope ereal_scope.

(** Measurability in the observed value for every Borel event. *)
Theorem gmc_posterior_kernel_measurable (m0 s0 s : R) (V : set R) :
  measurable V ->
  measurable_fun [set: R] (fun x : R => gmc_posterior_kernel m0 s0 s x V).
Proof.
move=> mV.
rewrite /gmc_posterior_kernel.
have mc : measurable_fun [set: R] (fun x : R => post_mean m0 s0 x s).
{ exact: gmc_post_mean_measurable. }
have mk : measurable_fun [set: R]
    (fun a : R => normal_prob a (post_stddev s0 s) V).
{ exact: measurable_normal_prob. }
exact (@measurableT_comp _ _ _ (measurableTypeR R) (measurableTypeR R) _
  (fun a : R => normal_prob a (post_stddev s0 s) V)
  setT (fun x : R => post_mean m0 s0 x s) mk mc).
Qed.

(** Every posterior event probability is integrable under the actual
    candidate observation Gaussian marginal, since it is measurable
    and lies in [0,1]. This uses the existing bounded-integrability
    theorem for finite measures, not a new convergence argument. *)
Theorem gmc_posterior_kernel_integrable (m0 s0 s : R) (U V : set R) :
  measurable U -> measurable V ->
  (normal_prob m0 (gmc_observation_scale s0 s)).-integrable U
    (fun x : R => gmc_posterior_kernel m0 s0 s x V).
Proof.
move=> mU mV.
have H : (normal_prob m0 (gmc_observation_scale s0 s)).-integrable
    [set: R] (fun x : R => gmc_posterior_kernel m0 s0 s x V).
{ apply: emeasurable_bounded_integrable.
  - move=> x; rewrite /gmc_posterior_kernel; exact: measure_ge0.
  - exists 1%R => x; rewrite /gmc_posterior_kernel; exact: probability_le1.
  - exact: gmc_posterior_kernel_measurable. }
exact: (integrableS measurableT mU (subsetT _) H).
Qed.

(** At a fixed observation, the unnormalized joint density mass on
    an arbitrary Borel latent event is the evidence density times
    the posterior event probability. Use normal_pdf_conjugate and
    the checked integral scaling pattern from the original residual
    theorem. No division by a possibly zero evidence is needed. *)
Theorem gmc_posterior_joint_slice (m0 s0 s x : R) (V : set R) :
  s0 != 0%R -> s != 0%R -> measurable V ->
  \int[mu]_(t in V) (gmc_joint_density m0 s0 s (x,t))%:E =
  (normal_pdf m0 (gmc_observation_scale s0 s) x)%:E *
  gmc_posterior_kernel m0 s0 s x V.
Proof.
move=> Hs0 Hs mV.
pose k := normal_pdf m0 (gmc_observation_scale s0 s) x.
pose f := fun t : R =>
  (normal_pdf (post_mean m0 s0 x s) (post_stddev s0 s) t)%:E.
transitivity (\int[mu]_(t in V) (k%:E * f t)).
- apply: eq_integral => t _.
  by rewrite /gmc_joint_density /k /gmc_observation_scale /f
    (@normal_pdf_conjugate R m0 s0 s x t Hs0 Hs) EFinM.
- have f0 : forall t : R, V t -> 0 <= f t.
  { by move=> t _; rewrite /f lee_fin; exact: normal_pdf_ge0. }
  have mf : measurable_fun V f.
  { rewrite /f.
    by apply/measurable_EFinP/measurable_funTS; exact: measurable_normal_pdf. }
  have k0 : (0 <= k)%R.
  { rewrite /k; exact: normal_pdf_ge0. }
  exact (@ge0_integralZl_EFin _ (measurableTypeR R) R
    mu V mV f f0 mf k k0).
Qed.

(** Conditional-distribution identity on every pair of Borel events:
    the actual joint mass equals integration of the posterior kernel
    over the observation event with respect to its Gaussian law.
    The right side is an integral against the normal measure itself,
    not merely an unnormalized density integral. *)
Theorem gmc_posterior_kernel_rectangle (m0 s0 s : R) (U V : set R) :
  s0 != 0%R -> s != 0%R -> measurable U -> measurable V ->
  gmc_joint_mass m0 s0 s (U `*` V) =
  \int[normal_prob m0 (gmc_observation_scale s0 s)]_(x in U)
    gmc_posterior_kernel m0 s0 s x V.
Proof.
move=> Hs0 Hs mU mV.
have mUV : measurable (U `*` V).
{ exact: measurableX. }
have Hker := @gmc_posterior_kernel_integrable m0 s0 s U V mU mV.
rewrite (@gmc_joint_mass_sections R m0 s0 s (U `*` V) Hs mUV).
rewrite (@integral_normal_prob R m0 (gmc_observation_scale s0 s)
  (fun x : R => gmc_posterior_kernel m0 s0 s x V) U mU Hker).
rewrite [RHS]integral_mkcond.
apply: eq_integral => x _.
rewrite patchE.
case: ifPn => Hx.
- rewrite (@in_xsectionX _ _ U V x Hx).
  rewrite muleC.
  exact: (@gmc_posterior_joint_slice m0 s0 s x V Hs0 Hs mV).
- rewrite (@notin_xsectionX _ _ U V x Hx).
  exact: integral_set0.
Qed.

(** Identify the observation marginal by setting the latent event to
    the entire real line. This supplies the actual marginal required
    by the conditional-distribution identity. *)
Theorem gmc_observation_marginal (m0 s0 s : R) (U : set R) :
  s0 != 0%R -> s != 0%R -> measurable U ->
  gmc_joint_mass m0 s0 s (U `*` [set: R]) =
  normal_prob m0 (gmc_observation_scale s0 s) U.
Proof.
move=> Hs0 Hs mU.
rewrite (@gmc_posterior_kernel_rectangle m0 s0 s U [set: R]
  Hs0 Hs mU measurableT).
transitivity (\int[normal_prob m0 (gmc_observation_scale s0 s)]_(x in U) 1).
- apply: eq_integral => x _.
  by rewrite /gmc_posterior_kernel probability_setT.
- by rewrite integral_cst// mul1e.
Qed.
End PosteriorKernel.
