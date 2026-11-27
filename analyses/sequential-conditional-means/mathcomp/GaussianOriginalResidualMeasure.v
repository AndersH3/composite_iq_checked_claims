(** Module: GaussianOriginalResidualMeasure.v
    Purpose: Establish scalar Gaussian residual rectangle factorization
    in the original latent/observation coordinates, not just at the
    translated density. Reuse the independently checked normal centering
    theorem and MathComp-Analysis normal_pdf_conjugate and integral laws.
    The inner integral restricts the latent variable by the actual
    residual event theta - post_mean(x) in V. The outer integral
    restricts the observation to U. The resulting iterated density mass
    factors for every pair of measurable events U and V.
    Boundary: identification of this iterated density mass with an
    explicitly constructed joint pushforward measure, multivariate
    Gaussian histories, moments and singular cases remain separate.
    Researcher/requester: Anders Hellström.
    AI disclosure: AI-assisted proof candidates; validation pending.
*)
From mathcomp Require Import boot order ssralg ssrnum.
From mathcomp Require Import classical_sets reals ereal topology normedtype.
From mathcomp Require Import measure lebesgue_integral lebesgue_stieltjes_measure
  lebesgue_measure measurable_realfun.
From mathcomp.analysis Require Import normal_distribution.
Require Import GaussianResidualMeasure.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section OriginalResidualLaws.
Context {R : realType}.
Import MeasurableR.
Local Abbreviation mu := lebesgue_measure.

(** At a fixed observation x, the unnormalized latent/observation
    density integrated over the actual residual preimage event factors
    into the observation density and the centered residual probability.
    No division by evidence or probabilistic independence is assumed. *)
Theorem gmc_original_residual_slice
    (m0 s0 s x : R) (V : set R) :
  s0 != 0 -> s != 0 -> measurable V ->
  (\int[mu]_(t in gmc_translate (post_mean m0 s0 x s) @^-1` V)
      (normal_pdf t s x * normal_pdf m0 s0 t)%:E =
   (normal_pdf m0 (Num.sqrt (s0 ^+ 2 + s ^+ 2)) x)%:E *
      normal_prob 0 (post_stddev s0 s) V)%E.
Proof.
move=> Hs0 Hs mV.
have mpre : measurable (gmc_translate (post_mean m0 s0 x s) @^-1` V).
  rewrite -[X in measurable X]setTI.
  exact: (@gmc_translation_measurable R (post_mean m0 s0 x s)
    measurableT V mV).
have Hpost : post_stddev s0 s != 0.
  by rewrite lt0r_neq0//; exact: post_stddev_gt0.
(* Isolate the existing conjugacy identity under the integral. *)
transitivity
  (\int[mu]_(t in gmc_translate (post_mean m0 s0 x s) @^-1` V)
    ((normal_pdf m0 (Num.sqrt (s0 ^+ 2 + s ^+ 2)) x)%:E *
     (normal_pdf (post_mean m0 s0 x s) (post_stddev s0 s) t)%:E))%E.
  apply: eq_integral => t _.
  by rewrite (@normal_pdf_conjugate R m0 s0 s x t Hs0 Hs) EFinM.
rewrite ge0_integralZl_EFin //=.
- (* The preimage map is real-valued, while the measure product is
     extended-real-valued. Use the already checked centering equality
     directly under multiplication; avoid reparsing real subtraction
     inside an enclosing ereal scope or unfolding the packed measure. *)
  exact (f_equal
    (fun p : \bar R =>
       ((normal_pdf m0 (Num.sqrt (s0 ^+ 2 + s ^+ 2)) x)%:E * p)%E)
    (@gmc_normal_centered_event R (post_mean m0 s0 x s)
       (post_stddev s0 s) V Hpost mV)).
- by move=> t _; rewrite lee_fin; exact: normal_pdf_ge0.
- by apply/measurable_EFinP/measurable_funTS; exact: measurable_normal_pdf.
- exact: normal_pdf_ge0.
Qed.

(** Integrating the slice over any measurable observation event U
    establishes the original-coordinate rectangle mass factorization.
    This is the measure-integral version of scalar residual independence;
    identifying the mass with a constructed joint law is still needed. *)
Theorem gmc_original_residual_rectangle
    (m0 s0 s : R) (U V : set R) :
  s0 != 0 -> s != 0 -> measurable U -> measurable V ->
  (\int[mu]_(x in U)
    \int[mu]_(t in gmc_translate (post_mean m0 s0 x s) @^-1` V)
      (normal_pdf t s x * normal_pdf m0 s0 t)%:E =
   normal_prob m0 (Num.sqrt (s0 ^+ 2 + s ^+ 2)) U *
   normal_prob 0 (post_stddev s0 s) V)%E.
Proof.
move=> Hs0 Hs mU mV.
transitivity
  (\int[mu]_(x in U)
    ((normal_pdf m0 (Num.sqrt (s0 ^+ 2 + s ^+ 2)) x)%:E *
     normal_prob 0 (post_stddev s0 s) V))%E.
  apply: eq_integral => x _.
  exact: (@gmc_original_residual_slice m0 s0 s x V Hs0 Hs mV).
rewrite /normal_prob ge0_integralZr //=.
- by apply/measurable_EFinP/measurable_funTS; exact: measurable_normal_pdf.
- by move=> x _; rewrite lee_fin; exact: normal_pdf_ge0.
- apply: integral_ge0 => e _.
  by rewrite lee_fin; exact: normal_pdf_ge0.
Qed.
End OriginalResidualLaws.
