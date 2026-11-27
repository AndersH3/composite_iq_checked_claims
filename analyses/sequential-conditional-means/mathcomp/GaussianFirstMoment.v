(** Module: GaussianFirstMoment.v
    Purpose: Establish first absolute moment integrability for a
    nondegenerate centered normal distribution, using an integrable
    wider Gaussian as a dominating density. Extend the normal
    change-of-measure formula to nonnegative measurable integrands
    without presupposing their integrability.
    Reuse MathComp-Analysis exponential estimates, Radon-Nikodym
    theory, and Lebesgue integral comparison.
    The centered signed mean and general affine moments follow later.
    Researcher/requester: Anders Hellström.
    AI disclosure: AI-assisted proof candidates; validation pending.
*)
From mathcomp Require Import boot order ssralg ssrnum field_tactic.
From mathcomp Require Import boolp classical_sets functions reals ereal topology normedtype.
From mathcomp Require Import exp numfun measure lebesgue_integral
  lebesgue_stieltjes_measure lebesgue_measure measurable_realfun.
From mathcomp Require Import radon_nikodym.
From mathcomp.analysis Require Import normal_distribution.
Require Import GaussianPosteriorKernel.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section FirstMoment.
Context {R : realType}.
Import MeasurableR.
Local Abbreviation mu := (@lebesgue_measure R).

(** A simple polynomial bound on absolute value. It avoids relying
    on a numerical or asymptotic approximation of a Gaussian tail. *)
Lemma gmc_abs_le_one_square (x : R) :
  `|x| <= 1 + x ^+ 2.
Proof.
have Hsq : `|x| ^+ 2 = x ^+ 2.
{ by rewrite -normrX ger0_norm ?sqr_ge0. }
have h01 : 0 <= (1 : R) := ler01.
case: (leP `|x| 1) => h.
- apply: (le_trans h).
  by rewrite -[LHS]addr0 lerD2l sqr_ge0.
- have h2 : `|x| <= `|x| ^+ 2.
  { rewrite expr2 -[LHS]mulr1.
    apply: ler_wpM2l; [exact: normr_ge0 | exact: ltW h]. }
  apply: (le_trans h2).
  by rewrite Hsq -[LHS]add0r lerD2r.
Qed.

(** An exponential majorant, valid at every real x for every
    positive scale q. The bound is deliberately conservative:
    abs(x) <= (1+q) exp(x^2/q). *)
Theorem gmc_abs_exp_bound (q x : R) :
  0 < q -> `|x| <= (1 + q) * expR (x ^+ 2 / q).
Proof.
move=> q0.
pose u := x ^+ 2 / q.
have u0 : 0 <= u.
{ by rewrite /u divr_ge0 ?sqr_ge0 ?ltW. }
have qu : q * u = x ^+ 2.
{ by rewrite /u mulrC divfK ?gt_eqF. }
have c1 : 1 <= 1 + q.
{ by rewrite -[LHS]addr0 lerD2l ltW. }
have cq : q <= 1 + q.
{ by rewrite -[LHS]add0r lerD2r ler01. }
have c0 : 0 <= 1 + q := le_trans ler01 c1.
apply: (le_trans (gmc_abs_le_one_square x)).
apply: (@le_trans _ _ ((1 + q) * (1 + u))).
- rewrite mulrDr mulr1 -qu.
  apply: lerD; first exact: c1.
  exact: ler_wpM2r u0 cq.
- apply: ler_wpM2l => //.
  exact: expR_ge1Dx.
Qed.

(** A Gaussian with twice the variance dominates the absolute first
    moment density of a centered Gaussian, up to a finite nonnegative
    real multiplier. This supplies a global integrable majorant,
    including the tails, not just a bounded-domain estimate. *)
Theorem gmc_centered_weighted_pdf_bound (s : R) :
  s != 0 ->
  exists w c : R, 0 <= c /\
    forall x : R, `|x| * normal_pdf 0 s x <= c * normal_pdf 0 w x.
Proof.
move=> Hs.
pose d := s ^+ 2 *+ 2.
pose q := d *+ 2.
pose w := Num.sqrt d.
have d0 : 0 < d.
{ by rewrite /d pmulrn_lgt0 ?exprn_even_gt0. }
have q0 : 0 < q.
{ by rewrite /q pmulrn_lgt0. }
have w0 : w != 0.
{ by rewrite /w lt0r_neq0 ?sqrtr_gt0. }
have wd : w ^+ 2 = d.
{ by rewrite /w sqr_sqrtr ?ltW. }
pose c := (1 + q) * normal_peak s / normal_peak w.
have c0 : 0 <= c.
{ by rewrite /c divr_ge0 ?mulr_ge0 ?addr_ge0 ?ler01 ?ltW ?normal_peak_ge0. }
exists w, c; split=> // x.
pose u := x ^+ 2 / q.
pose e := expR (- u).
have He : 0 <= e := expR_ge0 _.
have Hsfun : normal_fun 0 s x = e * e.
{ rewrite /normal_fun subr0 /e -expRD.
  congr expR.
  rewrite /u /q -mulr_natr -/d.
  field by rewrite ?gt_eqF. }
have Hwfun : normal_fun 0 w x = e.
{ by rewrite /normal_fun subr0 wd -/q /e /u mulNr. }
have Hbound : `|x| * e <= 1 + q.
{ have H := ler_wpM2r He (gmc_abs_exp_bound x q0).
  change (`|x| * e <= ((1 + q) * expR u) * e) in H.
  by move: H; rewrite /e -mulrA expRxMexpNx_1 mulr1. }
rewrite (normal_pdfE 0 Hs) (normal_pdfE 0 w0) /= Hsfun Hwfun.
have Hleft :
    `|x| * (normal_peak s * (e * e)) =
    (`|x| * e) * (normal_peak s * e).
{ ring. }
have Hright :
    c * (normal_peak w * e) = (1 + q) * (normal_peak s * e).
{ rewrite /c.
  field by rewrite gt_eqF ?normal_peak_gt0. }
rewrite Hleft Hright.
apply: ler_wpM2r Hbound.
by rewrite mulr_ge0 ?normal_peak_ge0.
Qed.

Local Open Scope ereal_scope.

(** The signed first-moment density is absolutely Lebesgue integrable.
    Compare its absolute value with the wider normalized density
    using the library's integrableZl and le_integrable theorems. *)
Theorem gmc_centered_weighted_pdf_integrable (s : R) :
  s != 0%R ->
  mu.-integrable [set: R] (fun x : R => (x * normal_pdf 0%R s x)%:E).
Proof.
move=> Hs.
have [w [c [c0 Hbound]]] := @gmc_centered_weighted_pdf_bound s Hs.
pose f := fun x : R => (x * normal_pdf 0%R s x)%:E.
pose g := fun x : R => c%:E * (normal_pdf 0%R w x)%:E.
have mf : measurable_fun [set: R] f.
{ rewrite /f; apply/measurable_EFinP.
  apply: measurable_funM; [exact: measurable_id | exact: measurable_normal_pdf]. }
have gi : mu.-integrable [set: R] g.
{ rewrite /g.
  apply: integrableZl.
  exact: integrable_normal_pdf. }
have fg x : [set: R] x -> `|f x| <= `|g x|.
{ move=> _; rewrite /f /g -EFinM !abse_EFin lee_fin.
  rewrite !normrM (ger0_norm c0) !ger0_norm ?normal_pdf_ge0.
  exact: Hbound. }
exact (@le_integrable _ (measurableTypeR R) R mu setT measurableT f g mf fg gi).
Qed.

(** Nonnegative change of measure for the normal law. Unlike the
    signed integral_normal_prob lemma this does not require a finite
    first moment in advance. Identify the existing sigma-finite
    Radon-Nikodym derivative with the normal density by its integrals
    over all measurable events, then apply the library formula. *)
Theorem gmc_normal_nonnegative_integral (m s : R) (f : R -> \bar R) :
  (forall x, 0 <= f x) -> measurable_fun [set: R] f ->
  \int[normal_prob m s]_x f x =
  \int[mu]_x (f x * (normal_pdf m s x)%:E).
Proof.
move=> f0 mf.
pose p := normal_prob m s.
pose g := Radon_Nikodym_SigmaFinite.f p mu.
pose h := fun x : R => (normal_pdf m s x)%:E.
have dom : p `<< mu.
{ exact: normal_prob_dominates. }
have gi : mu.-integrable [set: R] g.
{ exact: Radon_Nikodym_SigmaFinite.f_integrable. }
have mg : measurable_fun [set: R] g.
{ exact: measurable_int gi. }
have mh : measurable_fun [set: R] h.
{ rewrite /h; by apply/measurable_EFinP; exact: measurable_normal_pdf. }
have gh : ae_eq mu [set: R] g h.
{ apply: integral_ae_eq => //.
  move=> A _ mA.
  rewrite /g -(@Radon_Nikodym_SigmaFinite.f_integral
    _ (measurableTypeR R) R p mu dom A mA).
  by rewrite /p /normal_prob /h. }
etransitivity.
- symmetry.
  exact (@Radon_Nikodym_SigmaFinite.change_of_variables
    _ (measurableTypeR R) R p mu dom f setT f0 measurableT mf).
- apply: ae_eq_integral => //.
  + exact: emeasurable_funM mf mg.
  + exact: emeasurable_funM mf mh.
  + exact: ae_eqe_mul2l gh.
Qed.

(** First absolute moment under the actual centered Gaussian measure.
    The nonnegative change-of-measure identity permits proving
    integrability rather than assuming it as a side condition. *)
Theorem gmc_centered_normal_first_moment_integrable (s : R) :
  s != 0%R ->
  (normal_prob 0%R s).-integrable [set: R] (fun x : R => x%:E).
Proof.
move=> Hs.
have mi : measurable_fun [set: R] (fun x : R => x%:E).
{ by apply/measurable_EFinP; exact: measurable_id. }
have mw : measurable_fun [set: R] (fun x : R => `|x%:E|).
{ exact: measurableT_comp. }
have w0 x : 0 <= `|x%:E| by exact: abse_ge0.
have /integrableP [_ Hfin] := @gmc_centered_weighted_pdf_integrable s Hs.
apply/integrableP; split; first exact: mi.
rewrite (@gmc_normal_nonnegative_integral 0%R s
  (fun x : R => `|x%:E|) w0 mw).
have Heq :
    \int[mu]_x ( `|x%:E| * (normal_pdf 0%R s x)%:E) =
    \int[mu]_x `|(x * normal_pdf 0%R s x)%:E|.
{ apply: eq_integral => x _.
  rewrite EFinM abseM.
  by rewrite (gee0_abs _) ?lee_fin ?normal_pdf_ge0. }
by rewrite Heq.
Qed.
End FirstMoment.
