(** Module: GaussianScalarConditionalMean.v
    Purpose: Establish the scalar Gaussian conditional expectation
    by the defining event-integral characterization on the actual
    observation/latent joint measure. Derive joint integrability
    and zero residual integrals from the checked residual product
    law and the reusable GaussianProductHistory integration lemmas,
    not from an independence or conditional expectation axiom.
    Researcher/requester: Anders Hellström.
    AI disclosure: AI-assisted proof candidates; validation pending.
*)
From mathcomp Require Import boot order ssralg ssrnum.
From mathcomp Require Import boolp classical_sets functions reals ereal topology normedtype.
From mathcomp Require Import numfun measure lebesgue_integral
  lebesgue_stieltjes_measure lebesgue_measure measurable_realfun.
From mathcomp.analysis Require Import normal_distribution.
Require Import GaussianJointDensityMeasure GaussianResidualPushforward
  GaussianPosteriorKernel GaussianFirstMoment GaussianSignedMean
  GaussianLocationMean GaussianResidualIntegral GaussianProductHistory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section ScalarConditionalMean.
Context {R : realType}.
Import MeasurableR.
Local Abbreviation BorelPair := ((measurableTypeR R * measurableTypeR R)%type).
Local Open Scope ereal_scope.
Variables (m0 s0 s : R).
Hypotheses (Hs0 : s0 != 0%R) (Hs : s != 0%R).

Local Abbreviation J :=
  (@GaussianJointDensityMeasure_gmc_joint_mass__canonical__measure_function_Measure
    R m0 s0 s Hs).
Local Abbreviation QX := (normal_prob m0 (gmc_observation_scale s0 s)).
Local Abbreviation QE := (normal_prob 0%R (post_stddev s0 s)).
Local Abbreviation P := (QX \x QE).
Local Abbreviation phi := (gmc_residual_map m0 s0 s).

(** Lifting an integrable observation function to the residual product
    space preserves integrability. Tonelli integrates its absolute
    value over the other probability coordinate, whose mass is one. *)
Theorem gmc_product_observation_integrable (f : R -> \bar R) :
  QX.-integrable [set: R] f ->
  P.-integrable [set: BorelPair] (fun z => f z.1).
Proof.
(* Specialize the independently verified heterogeneous product lemma.
   Preserve this declaration's public statement for existing clients. *)
move=> fi.
exact (@gmc_product_fst_integrable _ _ (measurableTypeR R)
  (measurableTypeR R) R QX QE f fi).
Qed.

(** The corresponding lift of an integrable residual function follows
    from the reverse-order Tonelli integrability characterization. *)
Theorem gmc_product_residual_integrable (f : R -> \bar R) :
  QE.-integrable [set: R] f ->
  P.-integrable [set: BorelPair] (fun z => f z.2).
Proof.
(* Specialize the independently verified heterogeneous product lemma.
   Preserve this declaration's public statement for existing clients. *)
move=> fi.
exact (@gmc_product_snd_integrable _ _ (measurableTypeR R)
  (measurableTypeR R) R QX QE f fi).
Qed.

(** The affine posterior center is integrable under the observation
    Gaussian marginal. Use the established normal first moment and
    generic finite-measure constant, scalar and sum integrability. *)
Theorem gmc_posterior_mean_marginal_integrable :
  QX.-integrable [set: R] (fun x : R => (post_mean m0 s0 x s)%:E).
Proof.
have hs0sq : (0 < s0 ^+ 2)%R.
{ by rewrite exprn_even_gt0. }
have hssq : (0 < s ^+ 2)%R.
{ by rewrite exprn_even_gt0. }
have hd : (0 < s0 ^+ 2 + s ^+ 2)%R.
{ exact: addr_gt0 hs0sq hssq. }
have ho : (0 < gmc_observation_scale s0 s)%R.
{ by rewrite /gmc_observation_scale sqrtr_gt0. }
have hn : gmc_observation_scale s0 s != 0%R.
{ by rewrite (gt_eqF ho). }
pose a := (s ^+ 2 * m0)%R.
pose b := (s0 ^+ 2)%R.
pose k := ((s0 ^+ 2 + s ^+ 2)^-1)%R.
pose id := fun x : R => x%:E.
pose c := fun _ : R => a%:E.
pose l := fun x : R => b%:E * id x.
have ii : QX.-integrable [set: R] id.
{ exact (@gmc_normal_first_moment_integrable R m0
    (gmc_observation_scale s0 s) hn). }
have ci : QX.-integrable [set: R] c.
{ exact (@finite_measure_integrable_cst _ (measurableTypeR R) R QX
    setT a measurableT). }
have li : QX.-integrable [set: R] l.
{ exact (@integrableZl _ (measurableTypeR R) R QX setT
    measurableT b id ii). }
have si : QX.-integrable [set: R] (c \+ l).
{ exact (@integrableD _ (measurableTypeR R) R QX setT
    measurableT c l ci li). }
pose h := fun x : R => k%:E * (c x + l x).
have hi : QX.-integrable [set: R] h.
{ exact (@integrableZl _ (measurableTypeR R) R QX setT
    measurableT k (c \+ l) si). }
have Heq : {in [set: R], h =1
    (fun x : R => (post_mean m0 s0 x s)%:E)}.
{ move=> x _.
  rewrite /h /c /l /id -EFinM -EFinD -EFinM /post_mean /k /a /b.
  congr (_%:E).
  exact: mulrC. }
exact (@eq_integrable _ (measurableTypeR R) R QX setT measurableT
  h (fun x : R => (post_mean m0 s0 x s)%:E) Heq hi).
Qed.

(** On the actual joint measure the residual is integrable. Its
    product-law version is the second coordinate of a centered
    nondegenerate Gaussian. Transport back via the checked map. *)
Theorem gmc_joint_residual_integrable :
  J.-integrable [set: BorelPair]
    (fun z => (z.2 - post_mean m0 s0 z.1 s)%:E).
Proof.
have hp : (0 < post_stddev s0 s)%R.
{ exact: post_stddev_gt0 Hs0 Hs. }
have hn : post_stddev s0 s != 0%R.
{ by rewrite (gt_eqF hp). }
have ri : QE.-integrable [set: R] (fun x : R => x%:E).
{ exact (@gmc_centered_normal_first_moment_integrable R
    (post_stddev s0 s) hn). }
have pi : P.-integrable [set: BorelPair] (fun z => z.2%:E).
{ exact (@gmc_product_residual_integrable (fun x : R => x%:E) ri). }
exact (@gmc_residual_integrable R m0 s0 s Hs0 Hs
  (fun z : BorelPair => z.2%:E) pi).
Qed.

(** The proposed conditional mean is integrable under the actual
    joint law because the residual map preserves the observation. *)
Theorem gmc_joint_posterior_mean_integrable :
  J.-integrable [set: BorelPair]
    (fun z => (post_mean m0 s0 z.1 s)%:E).
Proof.
have pi : P.-integrable [set: BorelPair]
    (fun z => (post_mean m0 s0 z.1 s)%:E).
{ exact (@gmc_product_observation_integrable
    (fun x : R => (post_mean m0 s0 x s)%:E)
    gmc_posterior_mean_marginal_integrable). }
exact (@gmc_residual_integrable R m0 s0 s Hs0 Hs
  (fun z : BorelPair => (post_mean m0 s0 z.1 s)%:E) pi).
Qed.

(** The actual latent coordinate is integrable by decomposition
    into the integrable residual and posterior mean. *)
Theorem gmc_joint_latent_integrable :
  J.-integrable [set: BorelPair] (fun z => z.2%:E).
Proof.
pose f := fun z : BorelPair => (z.2 - post_mean m0 s0 z.1 s)%:E.
pose g := fun z : BorelPair => (post_mean m0 s0 z.1 s)%:E.
have fi : J.-integrable [set: BorelPair] f.
{ exact: gmc_joint_residual_integrable. }
have gi : J.-integrable [set: BorelPair] g.
{ exact: gmc_joint_posterior_mean_integrable. }
have hi : J.-integrable [set: BorelPair] (f \+ g).
{ exact (@integrableD _ BorelPair R J setT measurableT f g fi gi). }
have Heq : {in [set: BorelPair], (f \+ g) =1 (fun z => z.2%:E)}.
{ move=> z _.
  by rewrite /f /g /= -EFinD subrK. }
exact (@eq_integrable _ BorelPair R J setT measurableT
  (f \+ g) (fun z => z.2%:E) Heq hi).
Qed.

(** The centered residual has zero signed integral on every Borel
    observation event. Restrict the product integrand to the
    observation cylinder, apply signed Fubini and the checked
    centered mean, then transport the restricted integrand to J.
    No independence or zero conditional mean is assumed. *)
Theorem gmc_joint_residual_event_zero (U : set R) :
  measurable U ->
  \int[J]_(z in U `*` [set: R])
      (z.2 - post_mean m0 s0 z.1 s)%:E = 0.
Proof.
move=> mU.
pose A : set BorelPair := U `*` [set: R].
pose f := fun z : BorelPair => z.2%:E.
pose g := fun z : BorelPair => (z.2 - post_mean m0 s0 z.1 s)%:E.
pose h := f \_ A.
have mA : measurable A.
{ exact: measurableX mU measurableT. }
have hp : (0 < post_stddev s0 s)%R.
{ exact: post_stddev_gt0 Hs0 Hs. }
have hn : post_stddev s0 s != 0%R.
{ by rewrite (gt_eqF hp). }
have ri : QE.-integrable [set: R] (fun x : R => x%:E).
{ exact (@gmc_centered_normal_first_moment_integrable R
    (post_stddev s0 s) hn). }
have pi : P.-integrable [set: BorelPair] f.
{ exact (@gmc_product_residual_integrable (fun x : R => x%:E) ri). }
have ai : P.-integrable A f.
{ exact: (integrableS measurableT mA (subsetT _) pi). }
have hi : P.-integrable [set: BorelPair] h.
{ exact ((proj1 (integrable_mkcond f mA)) ai). }
(* The generic zero-residual event theorem already proves the
   product-space Fubini argument. Only transport to J is specific
   to the constructed scalar Gaussian law. *)
have ez : \int[QE]_y y%:E = 0.
{ exact (@gmc_centered_normal_mean_zero R (post_stddev s0 s) hn). }
have Hzero : \int[P]_(z in A) f z = 0.
{ exact (@gmc_product_residual_zero_event _ _ (measurableTypeR R)
    (measurableTypeR R) R QX QE (fun y : R => y%:E) U ri ez mU). }
have Hprod : \int[P]_z h z = 0.
{ transitivity (\int[P]_(z in A) f z).
  - symmetry; exact (integral_mkcond A f).
  - exact Hzero. }
have Htr := @gmc_residual_signed_integral R m0 s0 s Hs0 Hs h hi.
transitivity (\int[J]_z h (phi z)).
- transitivity (\int[J]_z (g \_ A) z).
  + exact (integral_mkcond A g).
  + apply: eq_integral => z _.
    by rewrite /h /f /g /A /gmc_residual_map !patchE !in_setX !in_setT !andbT.
- transitivity (\int[P]_z h z).
  + symmetry; exact Htr.
  + exact Hprod.
Qed.

(** Equality of the actual latent and posterior-mean integrals on
    every observation cylinder. This is the defining integral
    identity of conditional expectation given the observation.
    Both integrands' global integrability has been proved above. *)
Theorem gmc_joint_conditional_mean_event (U : set R) :
  measurable U ->
  \int[J]_(z in U `*` [set: R]) z.2%:E =
  \int[J]_(z in U `*` [set: R]) (post_mean m0 s0 z.1 s)%:E.
Proof.
move=> mU.
pose A : set BorelPair := U `*` [set: R].
pose f := fun z : BorelPair => (z.2 - post_mean m0 s0 z.1 s)%:E.
pose g := fun z : BorelPair => (post_mean m0 s0 z.1 s)%:E.
have mA : measurable A.
{ exact: measurableX mU measurableT. }
have fi : J.-integrable A f.
{ exact: (integrableS measurableT mA (subsetT _) gmc_joint_residual_integrable). }
have gi : J.-integrable A g.
{ exact: (integrableS measurableT mA (subsetT _) gmc_joint_posterior_mean_integrable). }
transitivity (\int[J]_(z in A) (f z + g z)).
- apply: eq_integral => z _.
  by rewrite /f /g -EFinD subrK.
- transitivity ((\int[J]_(z in A) f z) + (\int[J]_(z in A) g z)).
  + exact (@integralD _ BorelPair R J A mA f g fi gi).
  + have Hzero : \int[J]_(z in A) f z = 0.
    { exact (@gmc_joint_residual_event_zero U mU). }
    transitivity (0 + (\int[J]_(z in A) g z)).
    * exact (f_equal (fun t : \bar R => t + (\int[J]_(z in A) g z)) Hzero).
    * exact: add0e.
Qed.

(** Observation measurability in factorized form: the posterior
    candidate has a Borel-measurable scalar representative and is
    its composition with the observation projection. Consequently
    every Borel preimage of the candidate is an observation event.
    The final event-integral identity applies to all such cylinders. *)
Theorem gmc_joint_conditional_mean_characterization :
  J.-integrable [set: BorelPair] (fun z => z.2%:E) /\
  J.-integrable [set: BorelPair]
    (fun z => (post_mean m0 s0 z.1 s)%:E) /\
  measurable_fun [set: R] (fun x : R => (post_mean m0 s0 x s)%:E) /\
  (forall U : set R, measurable U ->
    \int[J]_(z in U `*` [set: R]) z.2%:E =
    \int[J]_(z in U `*` [set: R]) (post_mean m0 s0 z.1 s)%:E).
Proof.
split; first exact: gmc_joint_latent_integrable.
split; first exact: gmc_joint_posterior_mean_integrable.
split.
- apply/measurable_EFinP.
  exact: gmc_post_mean_measurable.
- exact: gmc_joint_conditional_mean_event.
Qed.
End ScalarConditionalMean.
