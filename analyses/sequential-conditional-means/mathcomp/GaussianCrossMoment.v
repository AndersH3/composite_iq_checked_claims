(** Module: GaussianCrossMoment.v
    Purpose: Identify the joint law of distinct standard Gaussian
    coordinates on all measurable pair events, then integrate their
    product using Fubini and verified scalar first moments.
    Reuse MathComp product-measure uniqueness, pushforward measures,
    integral linearity, Fubini and existing original-space transport.
    This does not assume Gaussian residual independence or establish
    the diagonal unit-variance identity.
    Researcher/requester: Anders Hellström.
    AI disclosure: AI-assisted proof candidates; validation pending.
*)
From mathcomp Require Import boot order ssralg ssrnum.
From mathcomp Require Import boolp classical_sets functions reals ereal topology normedtype.
From mathcomp Require Import numfun measure lebesgue_integral
  lebesgue_stieltjes_measure lebesgue_measure measurable_realfun.
From mathcomp.analysis Require Import normal_distribution.
Require Import GaussianFiniteStandard GaussianFiniteIndependence
  GaussianFirstMoment GaussianSignedMean GaussianHistoryJointLaw.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section CrossMoment.
Context {R : realType}.
Import MeasurableR.
Local Open Scope ereal_scope.
Local Abbreviation B := (measurableTypeR R).
Local Abbreviation Pair := ((B * B)%type).
Local Abbreviation G := (normal_prob (0%R : R) (1%R : R)).
Local Abbreviation Q := (G \x G).
Local Abbreviation f := (fun x : R => x%:E).
Local Abbreviation h := (fun z : Pair => z.1%:E * z.2%:E).

(** The product of the two real coordinate embeddings is measurable
    by the library's measurable projections and multiplication. *)
Lemma gmc_standard_pair_product_measurable :
  measurable_fun [set: Pair] h.
Proof.
have mx : measurable_fun [set: Pair] (fun z : Pair => z.1%:E).
{ apply/measurable_EFinP; exact: measurable_fst. }
have my : measurable_fun [set: Pair] (fun z : Pair => z.2%:E).
{ apply/measurable_EFinP; exact: measurable_snd. }
exact: emeasurable_funM mx my.
Qed.

(** The product is absolutely integrable under the independent
    scalar product probability. Tonelli and scalar multiplication
    reduce the iterated absolute integral to a finite multiple of
    the already verified first absolute moment. *)
Theorem gmc_standard_pair_product_integrable :
  Q.-integrable [set: Pair] h.
Proof.
have Hs : (1%R : R) != 0%R.
{ exact: oner_neq0. }
have fi : G.-integrable [set: R] f.
{ exact (@gmc_centered_normal_first_moment_integrable R 1%R Hs). }
pose a := fun x : R => `|x%:E|.
have ai : G.-integrable [set: R] a.
{ exact: integrable_abse fi. }
pose C := \int[G]_y a y.
have Cf : C \is a fin_num.
{ exact: integrable_fin_num ai. }
have CK : (fine C)%:E = C.
{ exact: fineK Cf. }
have Hinner (x : R) : \int[G]_y `|h (x,y)| = a x * C.
{ (* Parenthesize the entire integrand: the integral binder must
     scope over the multiplication and its y-dependent factor. *)
  transitivity (\int[G]_y ((`|x|%R)%:E * a y)).
  - apply: eq_integral => y _.
    (* Expose the product without simplifying the extended-real
       multiplication of finite embeddings before applying abseM. *)
    change (`|x%:E * y%:E| = (`|x|%R)%:E * `|y%:E|).
    by rewrite abseM (abse_EFin x).
  - transitivity ((`|x|%R)%:E * C).
    + rewrite /C.
      exact: integralZl ai.
    + by rewrite /a abse_EFin. }
have Hwhole : \int[G]_x \int[G]_y `|h (x,y)| =
    \int[G]_x (a x * (fine C)%:E).
{ apply: eq_integral => x _.
  by rewrite Hinner CK. }
have si : G.-integrable [set: R]
    (fun x => a x * (fine C)%:E).
{ exact: integrableZr ai. }
apply (proj2 (@integrable12ltyP _ _ B B R G G h
  gmc_standard_pair_product_measurable)).
rewrite Hwhole.
exact: integrable_lty si.
Qed.

(** The independent scalar product has zero signed cross moment:
    integrate the second coordinate first, use its zero mean,
    then integrate the resulting constant zero. *)
Theorem gmc_standard_pair_product_mean_zero :
  \int[Q]_z h z = 0.
Proof.
have Hs : (1%R : R) != 0%R.
{ exact: oner_neq0. }
have fi : G.-integrable [set: R] f.
{ exact (@gmc_centered_normal_first_moment_integrable R 1%R Hs). }
have Hz : \int[G]_y f y = 0.
{ exact (@gmc_centered_normal_mean_zero R 1%R Hs). }
transitivity (\int[G]_x \int[G]_y h (x,y)).
- symmetry.
  exact (@integral12_prod_meas1 _ _ B B R G G h
    gmc_standard_pair_product_integrable).
- transitivity (\int[G]_x (0 : \bar R)).
  + apply: eq_integral => x _.
    transitivity (x%:E * (\int[G]_y f y)).
    * exact: integralZl fi.
    * by rewrite Hz mule0.
  + exact: integral0.
Qed.

Variable n : nat.
Local Abbreviation T := (n.-tuple B).
Local Abbreviation P := (@gmc_standard_history R n).
Variables i j : 'I_n.
Local Abbreviation u := (fun t : T => tnth t i).
Local Abbreviation v := (fun t : T => tnth t j).
Local Abbreviation phi := (fun t : T => (u t, v t)).

(** The selected pair is a measurable map of the entire standard
    history, including histories of arbitrary finite dimension. *)
Lemma gmc_standard_coordinate_pair_measurable :
  measurable_fun [set: T] phi.
Proof.
have mu : measurable_fun [set: T] u.
{ exact: measurable_tnth. }
have mv : measurable_fun [set: T] v.
{ exact: measurable_tnth. }
exact: measurable_fun_pair mu mv.
Qed.

(** Rectangle factorization of the selected distinct coordinates
    extends to every measurable pair event by the library's
    product-measure uniqueness theorem. The law is derived,
    rather than supplied as an independent hypothesis. *)
Theorem gmc_standard_coordinate_pair_law (A : set Pair) :
  i != j -> measurable A ->
  pushforward P phi A = Q A.
Proof.
move=> Hij mA.
pose Pc : {measure set Pair -> \bar R} := pushforward P phi.
pose M := Pc gmc_standard_coordinate_pair_measurable.
change (M A = Q A).
symmetry.
apply: (@product_measure_unique _ _ B B R G G M).
- move=> U V mU mV.
  change (P [set t : T | U (u t) /\ V (v t)] = G U * G V).
  exact (@gmc_standard_history_pair_independent R n i j U V Hij mU mV).
- exact mA.
Qed.

(** The original-space product is integrable, using the actual
    joint-law certificate and the general product transport theorem. *)
Theorem gmc_standard_coordinate_cross_integrable :
  i != j ->
  P.-integrable [set: T] (fun t => (u t)%:E * (v t)%:E).
Proof.
move=> Hij.
have mu : measurable_fun [set: T] u.
{ exact: measurable_tnth. }
have mv : measurable_fun [set: T] v.
{ exact: measurable_tnth. }
have Hlaw (A : set Pair) : measurable A -> pushforward P phi A = Q A.
{ exact: gmc_standard_coordinate_pair_law Hij. }
exact (@gmc_history_integrable_transport _ _ _ T B B R P G G
  u v mu mv Hlaw h gmc_standard_pair_product_integrable).
Qed.

(** Distinct coordinates have zero cross moment on the actual
    finite history law, obtained by signed joint-law transport.
    Combined with zero coordinate means, this is the off-diagonal
    covariance identity; it does not evaluate the diagonal. *)
Theorem gmc_standard_coordinate_cross_zero :
  i != j ->
  \int[P]_t ((u t)%:E * (v t)%:E) = 0.
Proof.
move=> Hij.
have mu : measurable_fun [set: T] u.
{ exact: measurable_tnth. }
have mv : measurable_fun [set: T] v.
{ exact: measurable_tnth. }
have Hlaw (A : set Pair) : measurable A -> pushforward P phi A = Q A.
{ exact: gmc_standard_coordinate_pair_law Hij. }
have H := @gmc_history_signed_transport _ _ _ T B B R P G G
  u v mu mv Hlaw h setT measurableT gmc_standard_pair_product_integrable.
rewrite preimage_setT in H.
rewrite -H.
exact: gmc_standard_pair_product_mean_zero.
Qed.
End CrossMoment.
