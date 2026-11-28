(** Module: GaussianFiniteAffine.v
    Purpose: Establish coordinate integral transport and construct
    arbitrary finite affine images of the verified standard Gaussian
    history law, including rectangular and singular coefficient arrays.
    The affine pushforward construction alone does not prove affine
    Gaussian marginal closure or covariance-based independence.
    Researcher/requester: Anders Hellström.
    AI disclosure: AI-assisted proof candidates; validation pending.
*)
From HB Require Import structures.
From mathcomp Require Import boot order ssralg ssrnum.
From mathcomp Require Import boolp classical_sets functions reals ereal topology normedtype.
From mathcomp Require Import numfun measure lebesgue_integral
  lebesgue_stieltjes_measure lebesgue_measure measurable_realfun.
From mathcomp.analysis Require Import normal_distribution random_variable.
Require Import GaussianFiniteStandard GaussianFirstMoment GaussianSignedMean.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section CoordinateMoments.
Context {R : realType}.
Import MeasurableR.
Local Open Scope ereal_scope.
Local Abbreviation G := (normal_prob (0%R : R) (1%R : R)).
Variable n : nat.
Local Abbreviation T := (n.-tuple (measurableTypeR R)).
Local Abbreviation P := (@gmc_standard_history R n).
Variable i : 'I_n.
Local Abbreviation coord := (fun t : T => tnth t i).

(** Nonnegative coordinate integrals are exactly the scalar normal
    integrals by the verified marginal law and pushforward formula. *)
Theorem gmc_standard_coordinate_nonnegative (f : R -> \bar R) :
  measurable_fun [set: R] f -> (forall x, 0 <= f x) ->
  \int[G]_x f x = \int[P]_t f (coord t).
Proof.
move=> mf f0.
have mc : measurable_fun [set: T] coord.
{ exact: measurable_tnth. }
transitivity (\int[pushforward P coord]_x f x).
- symmetry.
  apply: (eq_measure_integral G) => A mA _.
  exact (@gmc_standard_history_coordinate R n i A mA).
- have H := @ge0_integral_pushforward _ _ T (measurableTypeR R)
    R coord mc P setT f measurableT mf (fun x _ => f0 x).
  by rewrite preimage_setT in H.
Qed.

(** Integrability transfers from the marginal to the actual
    finite-dimensional probability space using absolute values. *)
Theorem gmc_standard_coordinate_integrable (f : R -> \bar R) :
  G.-integrable [set: R] f ->
  P.-integrable [set: T] (fun t => f (coord t)).
Proof.
move=> fi.
have /integrableP [mf Hfin] := fi.
have mc : measurable_fun [set: T] coord.
{ exact: measurable_tnth. }
have ma : measurable_fun [set: \bar R] (@abse R).
{ exact: abse_measurable. }
have maf : measurable_fun [set: R] (fun x => `|f x|).
{ exact: measurableT_comp ma mf. }
have af0 (x : R) : 0 <= `|f x|.
{ exact: abse_ge0. }
have H := @gmc_standard_coordinate_nonnegative
  (fun x => `|f x|) maf af0.
apply/integrableP; split.
- exact: measurableT_comp mf mc.
- by rewrite -H.
Qed.

(** Signed coordinate integration uses the preceding integrability
    certificate, not an unstated assumption of finite moments. *)
Theorem gmc_standard_coordinate_signed (f : R -> \bar R) :
  G.-integrable [set: R] f ->
  \int[G]_x f x = \int[P]_t f (coord t).
Proof.
move=> fi.
have mc : measurable_fun [set: T] coord.
{ exact: measurable_tnth. }
have mf : measurable_fun [set: R] f.
{ exact: measurable_int fi. }
have ci : P.-integrable (coord @^-1` [set: R]) (f \o coord).
{ rewrite preimage_setT.
  exact: gmc_standard_coordinate_integrable fi. }
transitivity (\int[pushforward P coord]_x f x).
- symmetry.
  apply: (eq_measure_integral G) => A mA _.
  exact (@gmc_standard_history_coordinate R n i A mA).
- have H := @integral_pushforward _ _ T (measurableTypeR R)
    R coord mc P setT f mf ci measurableT.
  by rewrite preimage_setT in H.
Qed.

(** Every standard coordinate has a finite first absolute moment,
    including when the ambient history dimension is arbitrary. *)
Theorem gmc_standard_coordinate_first_moment :
  P.-integrable [set: T] (fun t => (coord t)%:E).
Proof.
apply: gmc_standard_coordinate_integrable.
apply: gmc_centered_normal_first_moment_integrable.
exact: oner_neq0.
Qed.

(** Every standard coordinate has expectation zero. The expectation
    is taken with respect to the constructed tuple law itself. *)
Theorem gmc_standard_coordinate_mean_zero :
  \int[P]_t (coord t)%:E = 0.
Proof.
(* Explicit ring scope distinguishes the scalar standard deviation
   from the extended-real integral codomain. *)
have Hs : (1%R : R) != 0%R.
{ exact: oner_neq0. }
have H := @gmc_standard_coordinate_signed (fun x : R => x%:E)
  (@gmc_centered_normal_first_moment_integrable R 1%R Hs).
rewrite (@gmc_centered_normal_mean_zero R 1%R Hs) in H.
exact: esym H.
Qed.
End CoordinateMoments.

Section AffineLaw.
Context {R : realType}.
Import MeasurableR.
Variables n k : nat.
Local Abbreviation T := (n.-tuple (measurableTypeR R)).
Local Abbreviation S := (k.-tuple (measurableTypeR R)).

(** A row of the affine map is a real finite linear combination
    plus its location. Use the library's ordinal enumeration,
    with an empty sum of zero for dimension zero. *)
Definition gmc_affine_row (b : R) (a : 'I_n -> R) (t : T) : R :=
  b + \sum_(j <- enum 'I_n) a j * tnth t j.

(** A finite row is measurable by induction on the library big
    operator, using measurable addition, multiplication, constants,
    and the canonical tuple-coordinate projections. *)
Lemma gmc_affine_row_measurable (b : R) (a : 'I_n -> R) :
  measurable_fun [set: T] (gmc_affine_row b a).
Proof.
rewrite /gmc_affine_row.
apply: measurable_funD; first exact: measurable_cst.
have H (l : seq 'I_n) :
    measurable_fun [set: T] (fun t => \sum_(j <- l) a j * tnth t j).
{ elim: l => [|j l IH].
  - have -> : (fun t : T => \sum_(i <- [::]) a i * tnth t i) =
        (fun _ : T => 0%R).
    { apply/funext => t; by rewrite big_nil. }
    exact: measurable_cst.
  - have -> : (fun t : T => \sum_(i <- j :: l) a i * tnth t i) =
        (fun t : T => a j * tnth t j + \sum_(i <- l) a i * tnth t i).
    { apply/funext => t; by rewrite big_cons. }
    apply: measurable_funD => //.
    apply: measurable_funM; first exact: measurable_cst.
    exact: measurable_tnth. }
exact: H.
Qed.

(** Arbitrary rectangular affine maps, represented by coefficient
    rows and a location vector. No invertibility or rank assumption. *)
Definition gmc_affine_map (b : 'I_k -> R)
    (a : 'I_k -> 'I_n -> R) (t : T) : S :=
  [tuple gmc_affine_row (b i) (a i) t | i < k].

(** Measurability follows coordinatewise by the library's
    measurable_fun_tnthP equivalence for finite tuples. *)
Lemma gmc_affine_map_measurable (b : 'I_k -> R)
    (a : 'I_k -> 'I_n -> R) :
  measurable_fun [set: T] (gmc_affine_map b a).
Proof.
apply/measurable_fun_tnthP => i.
have -> : (fun t : T => tnth (gmc_affine_map b a t) i) =
    gmc_affine_row (b i) (a i).
{ apply/funext => t; by rewrite /gmc_affine_map tnth_mktuple. }
exact: gmc_affine_row_measurable.
Qed.

(* Register the measurable affine map to reuse the existing
   distribution probability instance for arbitrary rectangular maps. *)
HB.instance Definition _ b a :=
  @isMeasurableFun.Build _ _ _ _ (gmc_affine_map b a)
    (@gmc_affine_map_measurable b a).

(** Actual probability law of an affine image of the standard
    history. This construction also makes sense for a zero matrix
    or singular coefficients, without any density assertion. *)
Definition gmc_affine_history (b : 'I_k -> R)
    (a : 'I_k -> 'I_n -> R) : probability S R :=
  [the probability S R of distribution (@gmc_standard_history R n)
    [mfun of gmc_affine_map b a]].

Local Open Scope ereal_scope.

(** Normalization follows from the library distribution instance. *)
Theorem gmc_affine_history_normalized b a :
  gmc_affine_history b a [set: S] = 1.
Proof. exact: probability_setT. Qed.

(** The affine law is the actual pushforward on every event; this
    identity does not claim a multivariate density exists. *)
Theorem gmc_affine_history_event b a (A : set S) :
  gmc_affine_history b a A =
    (@gmc_standard_history R n) ((gmc_affine_map b a) @^-1` A).
Proof. reflexivity. Qed.
End AffineLaw.
