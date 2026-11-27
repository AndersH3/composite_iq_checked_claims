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
From mathcomp Require Import boot order ssralg ssrnum.
From mathcomp Require Import boolp classical_sets functions reals ereal topology normedtype.
(* sequences defines expR; exp develops its properties without reexporting it. *)
From mathcomp Require Import sequences.
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
(* Construct ordinary inequalities directly. The ssreflect [LHS]
   rewrite selector is for equalities, not these order goals. *)
case: (leP `|x| 1) => h.
- have h1 : (1 : R) + 0 <= 1 + x ^+ 2.
  { apply: lerD; [exact: lexx | exact: sqr_ge0]. }
  rewrite addr0 in h1.
  exact: (le_trans h h1).
- have hm : `|x| * 1 <= `|x| * `|x|.
  { apply: ler_wpM2l; [exact: normr_ge0 | exact: ltW h]. }
  rewrite mulr1 -expr2 Hsq in hm.
  have hp : 0 + x ^+ 2 <= 1 + x ^+ 2.
  { apply: lerD; [exact: ler01 | exact: lexx]. }
  rewrite add0r in hp.
  exact: (le_trans hm hp).
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
{ have H : (1 : R) + 0 <= 1 + q.
  { apply: lerD; [exact: lexx | exact: ltW q0]. }
  by rewrite addr0 in H. }
have cq : q <= 1 + q.
{ have H : 0 + q <= 1 + q.
  { apply: lerD; [exact: ler01 | exact: lexx]. }
  by rewrite add0r in H. }
have c0 : 0 <= 1 + q := le_trans ler01 c1.
(* Prove the multiplicative comparison before any rewriting involving
   x^2 or the quotient u.  Transport only the finished sum inequality
   through q*u = x^2; this avoids matching inside local definitions. *)
have hm : q * u <= (1 + q) * u.
{ apply: ler_wpM2r; [exact: u0 | exact: cq]. }
have hsum : 1 + q * u <= (1 + q) + (1 + q) * u.
{ apply: lerD; [exact: c1 | exact: hm]. }
have hpoly : 1 + x ^+ 2 <= (1 + q) * (1 + u).
{ rewrite mulrDr mulr1.
  rewrite qu in hsum.
  exact: hsum. }
have hexp : (1 + q) * (1 + u) <= (1 + q) * expR u.
{ apply: ler_wpM2l; [exact: c0 | exact: expR_ge1Dx]. }
exact: (le_trans (gmc_abs_le_one_square x) (le_trans hpoly hexp)).
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
(* The multiplier is a quotient of nonnegative real quantities.
   Supply the two denominator/numerator certificates directly using
   the library's positivity lemmas, rather than chaining conditional
   rewrites whose side goals may depend on rewrite ordering. *)
pose c := (1 + q) * normal_peak s / normal_peak w.
have hq : 0 <= 1 + q.
{ apply: addr_ge0; [exact: ler01 | exact: ltW q0]. }
have hps : 0 <= normal_peak s.
{ exact: normal_peak_ge0. }
have hpw : 0 <= normal_peak w.
{ exact: normal_peak_ge0. }
have hn : 0 <= (1 + q) * normal_peak s.
{ exact: mulr_ge0 hq hps. }
have c0 : 0 <= c.
{ rewrite /c.
  exact: divr_ge0 hn hpw. }
exists w, c; split=> // x.
pose u := x ^+ 2 / q.
pose e := expR (- u).
have He : 0 <= e := expR_ge0 _.
(* Establish the exponent identity in the real field before passing
   it through expR.  Since d and q are positive, cancellation by
   either denominator is justified by the existing library lemmas. *)
have hd : d != 0 := gt_eqF d0.
have hqn : q != 0 := gt_eqF q0.
have Hq : q = d + d.
{ by rewrite /q mulr2n. }
have Huq : u * q = x ^+ 2.
{ by rewrite /u (divfK hqn). }
have Hud : (u + u) * d = x ^+ 2.
{ rewrite mulrDl -mulrDr -Hq.
  exact: Huq. }
have Hu : u + u = x ^+ 2 / d.
{ apply: (mulIf hd).
  rewrite (divfK hd).
  exact: Hud. }
have Harg : - (x ^+ 2) / d = - u + - u.
{ by rewrite mulNr -opprD Hu. }
have Hsfun : normal_fun 0 s x = e * e.
{ by rewrite /normal_fun subr0 -/d /e -expRD Harg. }
have Hwfun : normal_fun 0 w x = e.
{ by rewrite /normal_fun subr0 wd -/q /e /u mulNr. }
have Hbound : `|x| * e <= 1 + q.
{ have H := ler_wpM2r He (@gmc_abs_exp_bound q x q0).
  change (`|x| * e <= ((1 + q) * expR u) * e) in H.
  by move: H; rewrite /e -mulrA expRxMexpNx_1 mulr1. }
rewrite (normal_pdfE 0 Hs) (normal_pdfE 0 w0) /= Hsfun Hwfun.
have Hleft :
    `|x| * (normal_peak s * (e * e)) =
    (`|x| * e) * (normal_peak s * e).
{ by rewrite (mulrCA (normal_peak s) e e) mulrA. }
have Hright :
    c * (normal_peak w * e) = (1 + q) * (normal_peak s * e).
{ (* Cancel the nonzero wider density peak without a field tactic. *)
  have hpwn : normal_peak w != 0.
  { exact: gt_eqF (normal_peak_gt0 w0). }
  have Hcancel : c * normal_peak w = (1 + q) * normal_peak s.
  { by rewrite /c (divfK hpwn). }
  by rewrite mulrA Hcancel -mulrA. }
rewrite Hleft Hright.
(* State the common nonnegative multiplier independently, so the
   monotonicity application cannot confuse its two premises. *)
have Hmult : 0 <= normal_peak s * e.
{ exact: mulr_ge0 hps He. }
apply: ler_wpM2r; [exact: Hmult | exact: Hbound].
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
  rewrite !normrM (ger0_norm c0)
    (ger0_norm (@normal_pdf_ge0 R 0%R s x))
    (ger0_norm (@normal_pdf_ge0 R 0%R w x)).
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
pose p : {finite_measure set R -> \bar R} := normal_prob m s.
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
have ma : measurable_fun [set: \bar R] (@abse R).
{ exact: abse_measurable. }
have mw : measurable_fun [set: R] (fun x : R => `|x%:E|).
{ exact: measurableT_comp ma mi. }
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
  have Hp : 0 <= (normal_pdf 0%R s x)%:E.
  { by rewrite lee_fin; exact: normal_pdf_ge0. }
  by rewrite (gee0_abs Hp). }
by rewrite Heq.
Qed.
End FirstMoment.
