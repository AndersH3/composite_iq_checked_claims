(** Module: GaussianProductHistory.v
    Purpose: Generalize the verified scalar product-law integration
    arguments to arbitrary measurable observation and residual spaces.
    These lemmas serve finite-dimensional Gaussian histories without
    committing to one particular vector representation. The
    independent-product conditional-mean conclusion is conditional on
    the product law; the Gaussian factorization itself is a distinct
    obligation. Reuse MathComp-Analysis Tonelli, signed Fubini,
    restriction and integral linearity.
    Researcher/requester: Anders Hellström.
    AI disclosure: AI-assisted proof candidates; validation pending.
*)
From mathcomp Require Import boot order ssralg ssrnum.
From mathcomp Require Import boolp classical_sets functions reals ereal topology normedtype.
From mathcomp Require Import numfun measure lebesgue_integral
  lebesgue_stieltjes_measure lebesgue_measure measurable_realfun.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section ProductHistory.
Context {dX dY : measure_display}.
Context {X : measurableType dX} {Y : measurableType dY}.
Context {R : realType}.
Local Open Scope ereal_scope.
Variables (QX : probability X R) (QY : probability Y R).
Local Abbreviation Pair := ((X * Y)%type).
Local Abbreviation P := (QX \x QY).

(** Lift an integrable observation function to the product space,
    using Tonelli and the unit mass of the residual probability. *)
Theorem gmc_product_fst_integrable (f : X -> \bar R) :
  QX.-integrable [set: X] f ->
  P.-integrable [set: Pair] (fun z => f z.1).
Proof.
move=> fi.
have /integrableP [mf Hfin] := fi.
pose h := fun z : Pair => f z.1.
have mh : measurable_fun [set: Pair] h.
{ exact (@measurableT_comp _ _ _ Pair X _
    f setT (fst : Pair -> X) mf measurable_fst). }
have Hp : QY [set: Y] = 1.
{ exact: probability_setT. }
have Hinner (x : X) : \int[QY]_y `|h (x,y)| = `|f x|.
{ transitivity (`|f x| * QY [set: Y]).
  - exact (@integral_cst _ Y R QY setT measurableT (`|f x|)).
  - transitivity (`|f x| * 1).
    + exact (f_equal (fun z : \bar R => `|f x| * z) Hp).
    + exact: mule1. }
have Hwhole : \int[QX]_x \int[QY]_y `|h (x,y)| =
    \int[QX]_x `|f x|.
{ apply: eq_integral => x _.
  exact: Hinner. }
apply (proj2 (@integrable12ltyP _ _ X
  Y R QX QY h mh)).
by rewrite Hwhole.
Qed.

(** Lift an integrable residual function using reverse-order Tonelli. *)
Theorem gmc_product_snd_integrable (f : Y -> \bar R) :
  QY.-integrable [set: Y] f ->
  P.-integrable [set: Pair] (fun z => f z.2).
Proof.
move=> fi.
have /integrableP [mf Hfin] := fi.
pose h := fun z : Pair => f z.2.
have mh : measurable_fun [set: Pair] h.
{ exact (@measurableT_comp _ _ _ Pair Y _
    f setT (snd : Pair -> Y) mf measurable_snd). }
have Hp : QX [set: X] = 1.
{ exact: probability_setT. }
have Hinner (y : Y) : \int[QX]_x `|h (x,y)| = `|f y|.
{ transitivity (`|f y| * QX [set: X]).
  - exact (@integral_cst _ X R QX setT measurableT (`|f y|)).
  - transitivity (`|f y| * 1).
    + exact (f_equal (fun z : \bar R => `|f y| * z) Hp).
    + exact: mule1. }
have Hwhole : \int[QY]_y \int[QX]_x `|h (x,y)| =
    \int[QY]_y `|f y|.
{ apply: eq_integral => y _.
  exact: Hinner. }
apply (proj2 (@integrable21ltyP _ _ X
  Y R QX QY h mh)).
by rewrite Hwhole.
Qed.

(** A residual function with zero signed mean has zero integral
    over every observation cylinder. The function need not be a
    coordinate or a Gaussian. Integrability legitimizes Fubini. *)
Theorem gmc_product_residual_zero_event (e : Y -> \bar R) (U : set X) :
  QY.-integrable [set: Y] e ->
  \int[QY]_y e y = 0 ->
  measurable U ->
  \int[P]_(z in U `*` [set: Y]) e z.2 = 0.
Proof.
move=> ei ez mU.
pose A : set Pair := U `*` [set: Y].
pose f := fun z : Pair => e z.2.
pose h := f \_ A.
have mA : measurable A.
{ exact: measurableX mU measurableT. }
have pi : P.-integrable [set: Pair] f.
{ exact (@gmc_product_snd_integrable e ei). }
have ai : P.-integrable A f.
{ exact: (integrableS measurableT mA (subsetT _) pi). }
have hi : P.-integrable [set: Pair] h.
{ exact ((proj1 (integrable_mkcond f mA)) ai). }
have Hinner (x : X) : \int[QY]_y h (x,y) = 0.
{ case: (boolP (x \in U)) => Hx.
  - transitivity (\int[QY]_y e y).
    + apply: eq_integral => y _.
      by rewrite /h /f /A patchE in_setX in_setT andbT Hx.
    + exact ez.
  - transitivity (\int[QY]_y (0 : \bar R)).
    + apply: eq_integral => y _.
      by rewrite /h /f /A patchE in_setX in_setT andbT (negbTE Hx).
    + exact: integral0. }
transitivity (\int[P]_z h z).
- exact (integral_mkcond A f).
- transitivity (\int[QX]_x \int[QY]_y h (x,y)).
  + symmetry.
    exact (@integral12_prod_meas1 _ _ X Y R QX QY h hi).
  + transitivity (\int[QX]_x (0 : \bar R)).
    * apply: eq_integral => x _.
      exact: Hinner.
    * exact: integral0.
Qed.

(** Integrability of an additive model under the actual product
    measure follows from the two marginal integrability facts. *)
Theorem gmc_product_additive_integrable (m : X -> \bar R) (e : Y -> \bar R) :
  QX.-integrable [set: X] m -> QY.-integrable [set: Y] e ->
  P.-integrable [set: Pair] (fun z => m z.1 + e z.2).
Proof.
move=> mi ei.
pose f := fun z : Pair => m z.1.
pose g := fun z : Pair => e z.2.
have fi : P.-integrable [set: Pair] f.
{ exact (@gmc_product_fst_integrable m mi). }
have gi : P.-integrable [set: Pair] g.
{ exact (@gmc_product_snd_integrable e ei). }
exact (@integrableD _ Pair R P setT measurableT f g fi gi).
Qed.

(** For an integrable additive model with zero-mean residual, the
    observation term satisfies the defining integral identity on
    every observation event, without a normality hypothesis. *)
Theorem gmc_product_additive_mean_event (m : X -> \bar R)
    (e : Y -> \bar R) (U : set X) :
  QX.-integrable [set: X] m -> QY.-integrable [set: Y] e ->
  \int[QY]_y e y = 0 -> measurable U ->
  \int[P]_(z in U `*` [set: Y]) (m z.1 + e z.2) =
  \int[P]_(z in U `*` [set: Y]) m z.1.
Proof.
move=> mi ei ez mU.
pose A : set Pair := U `*` [set: Y].
pose f := fun z : Pair => m z.1.
pose g := fun z : Pair => e z.2.
have mA : measurable A.
{ exact: measurableX mU measurableT. }
have fi : P.-integrable [set: Pair] f.
{ exact (@gmc_product_fst_integrable m mi). }
have gi : P.-integrable [set: Pair] g.
{ exact (@gmc_product_snd_integrable e ei). }
have fai : P.-integrable A f.
{ exact: (integrableS measurableT mA (subsetT _) fi). }
have gai : P.-integrable A g.
{ exact: (integrableS measurableT mA (subsetT _) gi). }
have gz : \int[P]_(z in A) g z = 0.
{ exact (@gmc_product_residual_zero_event e U ei ez mU). }
transitivity ((\int[P]_(z in A) f z) + (\int[P]_(z in A) g z)).
- exact (@integralD _ Pair R P A mA f g fai gai).
- transitivity ((\int[P]_(z in A) f z) + 0).
  + exact (f_equal (fun v : \bar R => (\int[P]_(z in A) f z) + v) gz).
  + exact: adde0.
Qed.
End ProductHistory.
