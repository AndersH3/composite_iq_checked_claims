(** Module: GaussianSignedMean.v
    Purpose: Establish the vanishing signed first moment of a centered
    nondegenerate Gaussian probability measure, after absolute
    integrability has been proved in GaussianFirstMoment.
    The reusable reflection and odd-integrand lemmas apply to
    Lebesgue integrable functions, not merely Gaussian densities.
    Reuse MathComp-Analysis Lebesgue reflection invariance, signed
    pushforward integration, and normal-density symmetry.
    Researcher/requester: Anders Hellström.
    AI disclosure: AI-assisted proof candidates; validation pending.
*)
From mathcomp Require Import boot order ssralg ssrnum.
From mathcomp Require Import boolp classical_sets functions reals ereal topology normedtype.
From mathcomp Require Import numfun measure lebesgue_integral
  lebesgue_stieltjes_measure lebesgue_measure measurable_realfun.
From mathcomp.analysis Require Import normal_distribution.
Require Import GaussianFirstMoment.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section SignedMean.
Context {R : realType}.
Import MeasurableR.
Local Abbreviation mu := (@lebesgue_measure R).

(** The reflection map on the real line is measurable by the
    existing measurable negation and identity lemmas. *)
Local Lemma reflection_measurable :
  measurable_fun [set: R] (fun x : R => - x).
Proof.
apply: measurable_funN.
exact: measurable_id.
Qed.

Local Open Scope ereal_scope.

(** Signed integral reflection on the whole real line.  In contrast
    to a formal substitution of an improper integral, the theorem
    explicitly requires integrability of the reflected function.
    The pushforward of Lebesgue measure is identified by the pinned
    library's lebesgue_measureN, on every measurable event. *)
Theorem gmc_lebesgue_signed_reflection (f : R -> \bar R) :
  measurable_fun [set: R] f ->
  mu.-integrable [set: R] (fun x : R => f (- x)%R) ->
  \int[mu]_x f x = \int[mu]_x f (- x)%R.
Proof.
move=> mf fi.
pose phi := (-%R : R -> measurableTypeR R).
have mphi : measurable_fun [set: R] phi.
{ exact: reflection_measurable. }
have preT : phi @^-1` [set: R] = [set: R].
{ exact: preimage_setT. }
have intcomp : mu.-integrable (phi @^-1` [set: R]) (f \o phi).
{ rewrite preT.
  exact: fi. }
transitivity (\int[pushforward mu phi]_x f x).
- symmetry.
  apply: (eq_measure_integral mu) => A mA _.
  exact: lebesgue_measureN.
- have H := @integral_pushforward _ _ (measurableTypeR R)
    (measurableTypeR R) R phi mphi mu setT f mf intcomp measurableT.
  rewrite preT in H.
  exact: H.
Qed.

(** A genuinely integrable odd function has zero signed Lebesgue
    integral.  Reflection is integrable by the pointwise oddness
    identity and integrableN.  Finiteness is essential: it excludes
    infinite cancellation and lets us reduce I = -I to a real
    additive equation. *)
Theorem gmc_lebesgue_odd_integral_zero (f : R -> \bar R) :
  mu.-integrable [set: R] f ->
  (forall x : R, f (- x)%R = - f x) ->
  \int[mu]_x f x = 0.
Proof.
move=> fi oddf.
have mf : measurable_fun [set: R] f.
{ exact: measurable_int fi. }
have ni : mu.-integrable [set: R] (-%E \o f).
{ apply: integrableN => //. }
have ri : mu.-integrable [set: R] (fun x : R => f (- x)%R).
{ apply: (eq_integrable _ ni).
  move=> x _ /=.
  symmetry.
  exact: oddf. }
pose I := \int[mu]_x f x.
have Hopp : I = - I.
{ rewrite /I.
  transitivity (\int[mu]_x f (- x)%R).
  - exact: gmc_lebesgue_signed_reflection mf ri.
  - transitivity (\int[mu]_x - f x).
    + apply: eq_integral => x _.
      exact: oddf.
    + apply: integralN.
      exact: integrable_add_def. }
have Hfin : I \is a fin_num.
{ rewrite /I.
  exact: integrable_fin_num. }
have Hrepr : (fine I)%:E = I := fineK Hfin.
have Hr : fine I = (- fine I)%R.
{ apply: EFin_inj.
  by rewrite EFinN Hrepr Hopp. }
have Hsum : (fine I + fine I = 0)%R.
{ transitivity (fine I + (- fine I))%R.
  - exact (f_equal (fun t : R => (fine I + t)%R) Hr).
  - exact: addrN. }
have Hz : fine I = 0%R.
{ apply/eqP.
  move/eqP: Hsum.
  by rewrite -mulr2n mulrn_eq0. }
change (I = 0).
by rewrite -Hrepr Hz.
Qed.

Local Close Scope ereal_scope.

(** The centered nondegenerate normal density is even.  Reuse the
    library's normal_funN identity rather than expand the Gaussian
    exponential or reprove the symmetry of squares. *)
Theorem gmc_centered_normal_pdf_even (s x : R) :
  s != 0 -> normal_pdf 0 s (- x) = normal_pdf 0 s x.
Proof.
move=> Hs.
rewrite !normal_pdfE// /=.
have H := @normal_funN R 0 s x.
rewrite oppr0 in H.
by rewrite H.
Qed.

Local Open Scope ereal_scope.

(** The first-moment density is odd and absolutely integrable.
    Apply the general odd-integrand theorem, whose finite signed
    integral conclusion does not rely on a principal value. *)
Theorem gmc_centered_weighted_pdf_integral_zero (s : R) :
  s != 0%R ->
  \int[mu]_x (x * normal_pdf 0%R s x)%:E = 0.
Proof.
move=> Hs.
apply: gmc_lebesgue_odd_integral_zero.
- exact: gmc_centered_weighted_pdf_integrable.
- move=> x.
  by rewrite (@gmc_centered_normal_pdf_even s x Hs) mulNr EFinN.
Qed.

(** The signed expectation of a centered nondegenerate normal
    probability law is zero.  The previously verified absolute
    integrability theorem supplies the hypothesis of the library
    signed change-of-measure theorem integral_normal_prob. *)
Theorem gmc_centered_normal_mean_zero (s : R) :
  s != 0%R ->
  \int[normal_prob 0%R s]_x x%:E = 0.
Proof.
move=> Hs.
have Habs := @gmc_centered_normal_first_moment_integrable R s Hs.
rewrite (@integral_normal_prob R 0%R s
  (fun x : R => x%:E) setT measurableT Habs).
transitivity (\int[mu]_x (x * normal_pdf 0%R s x)%:E).
- apply: eq_integral => x _.
  by rewrite EFinM.
- exact: gmc_centered_weighted_pdf_integral_zero.
Qed.
End SignedMean.
