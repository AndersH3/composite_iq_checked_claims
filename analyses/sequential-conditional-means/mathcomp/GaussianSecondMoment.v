(** Module: GaussianSecondMoment.v
    Purpose: Establish finite second moments of actual centered
    Gaussian measures and of every standard history coordinate.
    Reuse the verified first-moment density domination and integral
    transport theorems; no variance value is assumed.
    The zero-scale convention of MathComp normal_pdf is not the
    degenerate Gaussian law, so the dominating scale must be nonzero.
    Researcher/requester: Anders Hellström.
    AI disclosure: AI-assisted proof candidates; validation pending.
*)
(* Import the core interval predicate instance explicitly, as in
   MathComp-Analysis set_interval and normal_distribution. *)
From mathcomp Require Import boot order ssralg ssrnum interval.
From mathcomp Require Import boolp classical_sets set_interval functions reals ereal topology normedtype.
From mathcomp Require Import numfun measure lebesgue_integral
  lebesgue_stieltjes_measure lebesgue_measure measurable_realfun.
From mathcomp.analysis Require Import normal_distribution.
Require Import GaussianFirstMoment GaussianFiniteStandard GaussianFiniteAffine.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section SecondMoment.
Context {R : realType}.
Import MeasurableR.
Local Abbreviation mu := (@lebesgue_measure R).

(** The wider-density witness in the verified first-moment bound
    cannot have scale zero: at x=-1 the library's zero-scale
    indicator density vanishes, but a nondegenerate Gaussian
    density is strictly positive. This strengthens the existing
    certificate without duplicating its exponential estimates. *)
Lemma gmc_weighted_pdf_nonzero_witness (s : R) :
  s != 0 ->
  exists w c : R, w != 0 /\ 0 <= c /\
    forall x : R, `|x| * normal_pdf 0 s x <= c * normal_pdf 0 w x.
Proof.
move=> Hs.
have [w [c [c0 Hbound]]] := @gmc_centered_weighted_pdf_bound R s Hs.
have Hw : w != 0.
{ apply/eqP => Hw0; subst w.
  have Hlt : (-1 : R) < 0.
  { by rewrite oppr_lt0 ltr01. }
  (* Separate Boolean set membership from the real-valued
     indicator. Use the classical set lemma explicitly, rather than
     the overloaded inE multirule from the finite-set libraries. *)
  have Hout : ((-1 : R) \in (`[0, 1]%classic : set R)) = false.
  { (* First reduce the Boolean equality to negated membership,
       then use the Prop-valued classical membership equality. *)
    apply: negbTE.
    apply/negP.
    rewrite in_setE set_itvcc /=.
    by rewrite (lt_geF Hlt). }
  have Hz : normal_pdf 0 0 (-1 : R) = 0.
  { by rewrite /normal_pdf eqxx indicE Hout. }
  have Hp : 0 < normal_pdf 0 s (-1 : R).
  { rewrite /normal_pdf (negbTE Hs).
    exact: NormalPdf0.normal_pdf0_gt0 Hs. }
  have H := Hbound (-1 : R).
  rewrite Hz mulr0 normrN normr1 mul1r in H.
  by rewrite (lt_geF Hp) in H. }
exists w, c; split; first exact Hw.
split; [exact c0 | exact Hbound].
Qed.

Local Open Scope ereal_scope.

(** The square-weighted density is integrable by multiplying the
    verified absolute first-moment majorization by abs(x) and
    using the integrable first-moment density at the wider scale. *)
Theorem gmc_centered_square_pdf_integrable (s : R) :
  s != 0%R ->
  mu.-integrable [set: R]
    (fun x : R => ((x ^+ 2 * normal_pdf 0%R s x)%R)%:E).
Proof.
move=> Hs.
have [w [c [Hw [c0 Hbound]]]] := @gmc_weighted_pdf_nonzero_witness s Hs.
pose f := fun x : R => ((x ^+ 2 * normal_pdf 0%R s x)%R)%:E.
pose g := fun x : R => c%:E * ((x * normal_pdf 0%R w x)%R)%:E.
have mf : measurable_fun [set: R] f.
{ rewrite /f; apply/measurable_EFinP.
  apply: measurable_funM; last exact: measurable_normal_pdf.
  (* The library directly proves measurability of natural powers;
     no function-product rewrite or identity-map inference is needed. *)
  exact: exprn_measurable. }
have gi : mu.-integrable [set: R] g.
{ exact (@integrableZl _ (measurableTypeR R) R mu setT
    measurableT c (fun x : R => ((x * normal_pdf 0%R w x)%R)%:E)
    (@gmc_centered_weighted_pdf_integrable R w Hw)). }
have fg x : [set: R] x -> `|f x| <= `|g x|.
{ move=> _; rewrite /f /g -EFinM !abse_EFin lee_fin.
  rewrite !normrM (ger0_norm c0)
    (ger0_norm (@normal_pdf_ge0 R 0%R s x))
    (ger0_norm (@normal_pdf_ge0 R 0%R w x))
    (ger0_norm (sqr_ge0 x)).
  have H := Hbound x.
  have Hm : (`|x| * (`|x| * normal_pdf 0 s x) <=
      `|x| * (c * normal_pdf 0 w x))%R.
  { exact: ler_wpM2l (normr_ge0 x) H. }
  have Hsq : (`|x| * `|x| = x ^+ 2)%R.
  { by rewrite -expr2 -normrX ger0_norm ?sqr_ge0. }
  have Hl : (`|x| * (`|x| * normal_pdf 0 s x) =
      x ^+ 2 * normal_pdf 0 s x)%R.
  { by rewrite mulrA Hsq. }
  have Hr : (`|x| * (c * normal_pdf 0 w x) =
      c * (`|x| * normal_pdf 0 w x))%R.
  { exact: mulrCA. }
  by rewrite Hl Hr in Hm. }
exact (@le_integrable _ (measurableTypeR R) R mu setT
  measurableT f g mf fg gi).
Qed.

(** The actual centered Gaussian square is integrable: transport
    its nonnegative absolute integral through the verified density
    change of measure, rather than assuming a second moment. *)
Theorem gmc_centered_normal_second_moment_integrable (s : R) :
  s != 0%R ->
  (normal_prob 0%R s).-integrable [set: R]
    (fun x : R => ((x ^+ 2)%R)%:E).
Proof.
move=> Hs.
pose f := fun x : R => ((x ^+ 2)%R)%:E.
have mf : measurable_fun [set: R] f.
{ rewrite /f; apply/measurable_EFinP.
  (* The library directly proves measurability of natural powers;
     no function-product rewrite or identity-map inference is needed. *)
  exact: exprn_measurable. }
have f0 (x : R) : 0 <= f x.
{ by rewrite /f lee_fin sqr_ge0. }
have ma : measurable_fun [set: \bar R] (@abse R).
{ exact: abse_measurable. }
have maf : measurable_fun [set: R] (fun x : R => `|f x|).
{ exact: measurableT_comp ma mf. }
have /integrableP [_ Hfin] := @gmc_centered_square_pdf_integrable s Hs.
apply/integrableP; split; first exact: mf.
rewrite (@gmc_normal_nonnegative_integral R 0%R s
  (fun x : R => `|f x|) (fun x => abse_ge0 (f x)) maf).
have Heq :
    \int[mu]_x (`|f x| * (normal_pdf 0%R s x)%:E) =
    \int[mu]_x `|((x ^+ 2 * normal_pdf 0%R s x)%R)%:E|.
{ apply: eq_integral => x _.
  rewrite /f EFinM abseM.
  have Hp : 0 <= (normal_pdf 0%R s x)%:E.
  { by rewrite lee_fin; exact: normal_pdf_ge0. }
  by rewrite (gee0_abs Hp). }
by rewrite Heq.
Qed.

(** The scalar second-moment certificate transfers to every
    coordinate of the constructed finite standard probability. *)
Theorem gmc_standard_coordinate_second_moment n (i : 'I_n) :
  (@gmc_standard_history R n).-integrable
    [set: n.-tuple (measurableTypeR R)]
    (fun t => ((tnth t i ^+ 2)%R)%:E).
Proof.
apply: gmc_standard_coordinate_integrable.
apply: gmc_centered_normal_second_moment_integrable.
exact: oner_neq0.
Qed.
End SecondMoment.
