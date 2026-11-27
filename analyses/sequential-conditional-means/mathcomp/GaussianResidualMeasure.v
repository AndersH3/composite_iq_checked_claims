(** Module: GaussianResidualMeasure.v
    Purpose: Extend scalar Gaussian conjugacy to measurable residual
    events and integrated observation/residual rectangles.
    Reuse MathComp-Analysis measure uniqueness, pushforward integration,
    normal conjugacy and nonnegative integral scaling.
    No FormalML Gaussian Fubini axiom is imported.
    Arbitrary multivariate Gaussian laws, the joint change of variables
    and the two-library representation bridge remain separate obligations.
    Researcher/requester: Anders Hellström.
    AI disclosure: AI-assisted proof candidates; kernel validation pending.
*)
From HB Require Import structures.
From mathcomp Require Import boot order ssralg ssrnum field_tactic.
From mathcomp Require Import classical_sets reals ereal topology normedtype.
From mathcomp Require Import measure lebesgue_integral lebesgue_stieltjes_measure
  lebesgue_measure measurable_realfun set_interval.
From mathcomp.analysis Require Import normal_distribution.
Require Import GaussianPosteriorMeasure.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section ResidualMeasureLaws.
Context {R : realType}.
Import MeasurableR.
Local Abbreviation mu := lebesgue_measure.

(** The real translation map is deliberately named so its measurable
    function certificate can be registered with Hierarchy Builder.
    This is an ordinary real subtraction, not a new measure axiom. *)
Definition gmc_translate (m t : R) : R := t - m.

(** Explicit Borel measurability of translation follows from the
    existing subtraction, identity and constant-function lemmas. *)
Lemma gmc_translation_measurable (m : R) :
  measurable_fun [set: R] (gmc_translate m).
Proof.
change (measurable_fun [set: R] (fun t : R => t - m)).
apply: measurable_funB.
- exact: measurable_id.
- exact: measurable_cst.
Qed.

(* Pack the named map, as in the upstream pushforward-integration
   construction, so measure uniqueness receives a genuine measure. *)
HB.instance Definition _ m :=
  isMeasurableFun.Build _ _ _ _ (gmc_translate m)
    (gmc_translation_measurable m).

(** Translation invariance on arbitrary measurable subsets of the real
    line. As in upstream lebesgue_measureN, use uniqueness of Lebesgue
    measure on generating half-open intervals. Translation by -m
    changes the endpoints by +m but preserves interval length. *)
Theorem gmc_lebesgue_translation (m : R) (V : set R) :
  measurable V ->
  pushforward mu (fun t : R => (t - m : measurableTypeR R)) V = mu V.
Proof.
move=> mV.
change (pushforward mu (gmc_translate m) V = mu V).
(* First discharge the target event's measurability and any remaining
   structure obligation. Destructure an ocitv witness only in the
   actual interval-comparison goal. *)
apply/esym/lebesgue_measure_unique.
all: try solve [exact: mV | exact: gmc_translation_measurable].
move=> X [[a b]] _ <-.
rewrite /pushforward /gmc_translate.
have Hpre :
    (fun t : R => t - m) @^-1`
      ([set` Interval (BRight a) (BRight b)] : set R) =
    [set` Interval (BRight (a + m)) (BRight (b + m))].
  apply/seteqP; split => t /=;
    by rewrite !in_itv /= ltrBrDr lerBlDr.
rewrite Hpre !lebesgue_measure_itv /= !lte_fin ltrD2r.
have Hlength : b + m - (a + m) = b - a by field.
by rewrite -!EFinB Hlength.
Qed.

(** Centering a normal law translates every measurable event, not just
    its density at a point. Apply pushforward integration and translation
    invariance. Zero scale is excluded because the upstream fallback
    is not a Dirac measure. *)
Theorem gmc_normal_centered_event (m s : R) (V : set R) :
  s != 0 -> measurable V ->
  normal_prob m s ((fun t : R => t - m) @^-1` V) =
  normal_prob 0 s V.
Proof.
move=> Hs mV.
change (normal_prob m s (gmc_translate m @^-1` V) = normal_prob 0 s V).
rewrite /normal_prob.
transitivity
  (\int[mu]_(t in gmc_translate m @^-1` V)
     ((normal_pdf 0 s (gmc_translate m t))%:E))%E.
  apply: eq_integral => t _.
  by rewrite !normal_pdfE// /normal_fun /gmc_translate subr0.
rewrite -ge0_integral_pushforward//=.
- apply: eq_measure_integral => A mA _.
  exact: gmc_lebesgue_translation.
- by apply/measurable_EFinP/measurable_funTS; exact: measurable_normal_pdf.
- by move=> t _; rewrite lee_fin; exact: normal_pdf_ge0.
Qed.

(** Integrate the observation/residual density in the translated
    coordinates over arbitrary measurable rectangles. The inner integral
    is the centered residual measure times the marginal density; the
    outer integral produces the product of the two probabilities.
    Identification with the pushforward of the original joint law
    still requires the joint change-of-variables argument. *)
Theorem gmc_transformed_residual_rectangle
    (m0 s0 s : R) (U V : set R) :
  s0 != 0 -> s != 0 -> measurable U -> measurable V ->
  (\int[mu]_(x in U) \int[mu]_(e in V)
      (normal_pdf (post_mean m0 s0 x s + e) s x *
       normal_pdf m0 s0 (post_mean m0 s0 x s + e))%:E =
   normal_prob m0 (Num.sqrt (s0 ^+ 2 + s ^+ 2)) U *
   normal_prob 0 (post_stddev s0 s) V)%E.
Proof.
move=> Hs0 Hs mU mV.
transitivity
  (\int[mu]_(x in U)
    ((normal_pdf m0 (Num.sqrt (s0 ^+ 2 + s ^+ 2)) x)%:E *
     normal_prob 0 (post_stddev s0 s) V))%E.
  apply: eq_integral => x _.
  under eq_integral do rewrite
    (@gmc_gaussian_observation_residual_density_factor R m0 s0 s x _ Hs0 Hs)
    EFinM.
  rewrite /normal_prob ge0_integralZl_EFin //=.
  - by move=> e _; rewrite lee_fin; exact: normal_pdf_ge0.
  - by apply/measurable_EFinP/measurable_funTS; exact: measurable_normal_pdf.
  - exact: normal_pdf_ge0.
rewrite /normal_prob ge0_integralZr //=.
- by apply/measurable_EFinP/measurable_funTS; exact: measurable_normal_pdf.
- by move=> x _; rewrite lee_fin; exact: normal_pdf_ge0.
- exact: measure_ge0.
Qed.
End ResidualMeasureLaws.
