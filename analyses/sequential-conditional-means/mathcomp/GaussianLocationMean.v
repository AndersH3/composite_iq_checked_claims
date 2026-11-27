(** Module: GaussianLocationMean.v
    Purpose: Transport integrals through the verified Gaussian
    centering map, and establish absolute integrability and the
    exact signed mean of any nondegenerate scalar normal law.
    Reuse MathComp-Analysis pushforward integration, finite measure
    integrability and linearity, together with the checked centered
    Gaussian moment and centering-event results.
    Researcher/requester: Anders Hellström.
    AI disclosure: AI-assisted proof candidates; validation pending.
*)
From mathcomp Require Import boot order ssralg ssrnum.
From mathcomp Require Import boolp classical_sets functions reals ereal topology normedtype.
From mathcomp Require Import numfun measure lebesgue_integral
  lebesgue_stieltjes_measure lebesgue_measure measurable_realfun.
From mathcomp.analysis Require Import normal_distribution.
Require Import GaussianResidualMeasure GaussianSignedMean.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section LocationMean.
Context {R : realType}.
Import MeasurableR.
Local Open Scope ereal_scope.

(** Nonnegative integrals transport from a centered normal law to
    the translated coordinate of a noncentered law. No integrability
    premise is required, so this result can establish integrability. *)
Theorem gmc_normal_centered_nonnegative_integral (m s : R)
    (f : R -> \bar R) :
  s != 0%R -> measurable_fun [set: R] f ->
  (forall x : R, 0 <= f x) ->
  \int[normal_prob 0%R s]_x f x =
  \int[normal_prob m s]_x f (gmc_translate m x).
Proof.
move=> Hs mf f0.
pose phi := @gmc_translate R m.
have mphi : measurable_fun [set: R] phi.
{ exact: gmc_translation_measurable. }
have preT : phi @^-1` [set: R] = [set: R].
{ exact: preimage_setT. }
transitivity (\int[pushforward (normal_prob m s) phi]_x f x).
- symmetry.
  apply: (eq_measure_integral (normal_prob 0%R s)) => A mA _.
  exact (@gmc_normal_centered_event R m s A Hs mA).
- have H := @ge0_integral_pushforward _ _ (measurableTypeR R)
    (measurableTypeR R) R phi mphi (normal_prob m s) setT f
    measurableT mf (fun x _ => f0 x).
  rewrite preT in H.
  exact: H.
Qed.

(** Integrability transfers through the same centering map. Apply
    the nonnegative integral identity to the absolute value, with
    measurability inherited from the original integrability proof. *)
Theorem gmc_normal_centered_integrable (m s : R)
    (f : R -> \bar R) :
  s != 0%R -> (normal_prob 0%R s).-integrable [set: R] f ->
  (normal_prob m s).-integrable [set: R]
    (fun x : R => f (gmc_translate m x)).
Proof.
move=> Hs fi.
have /integrableP [mf Hfin] := fi.
have mphi : measurable_fun [set: R] (gmc_translate m).
{ exact: gmc_translation_measurable. }
have ma : measurable_fun [set: \bar R] (@abse R).
{ exact: abse_measurable. }
have maf : measurable_fun [set: R] (fun x : R => `|f x|).
{ exact: measurableT_comp ma mf. }
have af0 (x : R) : 0 <= `|f x|.
{ exact: abse_ge0. }
apply/integrableP; split.
- exact: measurableT_comp mf mphi.
- have H := @gmc_normal_centered_nonnegative_integral
    m s (fun x : R => `|f x|) Hs maf af0.
  rewrite -H.
  exact: Hfin.
Qed.

(** Signed expectation also transports through centering. The
    preceding integrability transfer supplies the precise premise
    needed by signed pushforward integration. *)
Theorem gmc_normal_centered_signed_integral (m s : R)
    (f : R -> \bar R) :
  s != 0%R -> (normal_prob 0%R s).-integrable [set: R] f ->
  \int[normal_prob 0%R s]_x f x =
  \int[normal_prob m s]_x f (gmc_translate m x).
Proof.
move=> Hs fi.
pose phi := @gmc_translate R m.
have mphi : measurable_fun [set: R] phi.
{ exact: gmc_translation_measurable. }
have mf : measurable_fun [set: R] f.
{ exact: measurable_int fi. }
have preT : phi @^-1` [set: R] = [set: R].
{ exact: preimage_setT. }
have intcomp : (normal_prob m s).-integrable (phi @^-1` [set: R]) (f \o phi).
{ rewrite preT.
  exact (@gmc_normal_centered_integrable m s f Hs fi). }
transitivity (\int[pushforward (normal_prob m s) phi]_x f x).
- symmetry.
  apply: (eq_measure_integral (normal_prob 0%R s)) => A mA _.
  exact (@gmc_normal_centered_event R m s A Hs mA).
- have H := @integral_pushforward _ _ (measurableTypeR R)
    (measurableTypeR R) R phi mphi (normal_prob m s) setT f mf
    intcomp measurableT.
  rewrite preT in H.
  exact: H.
Qed.

(** The centered coordinate x-m is integrable under N(m,s^2),
    by transporting the independently checked centered first moment. *)
Theorem gmc_normal_centered_coordinate_integrable (m s : R) :
  s != 0%R -> (normal_prob m s).-integrable [set: R]
    (fun x : R => (x - m)%:E).
Proof.
move=> Hs.
exact (@gmc_normal_centered_integrable m s (fun x : R => x%:E)
  Hs (@gmc_centered_normal_first_moment_integrable R s Hs)).
Qed.

(** The centered coordinate has signed expectation zero under
    N(m,s^2). This uses the verified centered signed mean, not
    any assumption about the mean of the noncentered normal law. *)
Theorem gmc_normal_centered_coordinate_mean_zero (m s : R) :
  s != 0%R ->
  \int[normal_prob m s]_x (x - m)%:E = 0.
Proof.
move=> Hs.
have H := @gmc_normal_centered_signed_integral m s
  (fun x : R => x%:E) Hs
  (@gmc_centered_normal_first_moment_integrable R s Hs).
rewrite (@gmc_centered_normal_mean_zero R s Hs) in H.
symmetry.
exact H.
Qed.

(** The original coordinate is integrable: decompose x as
    (x-m)+m, where the second summand is integrable under every
    finite measure. Transport the exact sum using function equality. *)
Theorem gmc_normal_first_moment_integrable (m s : R) :
  s != 0%R ->
  (normal_prob m s).-integrable [set: R] (fun x : R => x%:E).
Proof.
move=> Hs.
pose p := normal_prob m s.
pose f := fun x : R => (x - m)%:E.
pose g := fun _ : R => m%:E.
have fi : p.-integrable [set: R] f.
{ exact (@gmc_normal_centered_coordinate_integrable m s Hs). }
have gi : p.-integrable [set: R] g.
{ exact (@finite_measure_integrable_cst _ (measurableTypeR R) R p
    setT m measurableT). }
have si : p.-integrable [set: R] (f \+ g).
{ exact (@integrableD _ (measurableTypeR R) R p setT measurableT f g fi gi). }
have Heq : {in [set: R], (f \+ g) =1 (fun x : R => x%:E)}.
{ move=> x _.
  by rewrite /f /g /= -EFinD subrK. }
exact (@eq_integrable _ (measurableTypeR R) R p setT measurableT
  (f \+ g) (fun x : R => x%:E) Heq si).
Qed.

(** The nondegenerate normal law has signed expectation m.
    The decomposition into a centered coordinate and a constant
    is justified by absolute integrability and signed linearity;
    the constant integrates to m since the law is normalized. *)
Theorem gmc_normal_mean (m s : R) :
  s != 0%R ->
  \int[normal_prob m s]_x x%:E = m%:E.
Proof.
move=> Hs.
pose p := normal_prob m s.
pose f := fun x : R => (x - m)%:E.
pose g := fun _ : R => m%:E.
have fi : p.-integrable [set: R] f.
{ exact (@gmc_normal_centered_coordinate_integrable m s Hs). }
have gi : p.-integrable [set: R] g.
{ exact (@finite_measure_integrable_cst _ (measurableTypeR R) R p
    setT m measurableT). }
transitivity (\int[p]_x (f x + g x)).
- apply: eq_integral => x _.
  by rewrite /f /g -EFinD subrK.
- rewrite (@integralD _ (measurableTypeR R) R p setT measurableT f g fi gi).
  have Hf : \int[p]_x f x = 0.
  { exact (@gmc_normal_centered_coordinate_mean_zero m s Hs). }
  have Hg : \int[p]_x g x = m%:E.
  { rewrite /g /p.
    rewrite (@integral_cst _ (measurableTypeR R) R (normal_prob m s)
      setT measurableT m%:E).
    by rewrite /normal_prob integral_normal_pdf mule1. }
  by rewrite Hf Hg add0e.
Qed.
End LocationMean.
