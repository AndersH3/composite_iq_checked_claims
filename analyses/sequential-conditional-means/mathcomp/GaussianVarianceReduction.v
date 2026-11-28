(** Module: GaussianVarianceReduction.v
    Purpose: Reduce the diagonal standard Gaussian moment to a
    single scalar integral, isolate the integrable density balance
    needed for its calculus proof, and unify all coordinate products.
    Reuses the verified finite coordinate marginal and cross-moment
    theorems and MathComp integral linearity and normalization.
    The exact scalar unit variance is not assumed or proved here.
    Researcher/requester: Anders Hellström.
    AI disclosure: AI-assisted proof candidates; validation pending.
*)
From mathcomp Require Import boot order ssralg ssrnum.
From mathcomp Require Import boolp classical_sets functions reals ereal topology normedtype.
From mathcomp Require Import numfun measure lebesgue_integral
  lebesgue_stieltjes_measure lebesgue_measure measurable_realfun.
From mathcomp.analysis Require Import normal_distribution.
Require Import GaussianFirstMoment GaussianFiniteStandard
  GaussianFiniteAffine GaussianSecondMoment GaussianCrossMoment.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section VarianceReduction.
Context {R : realType}.
Import MeasurableR.
Local Open Scope ereal_scope.
Local Abbreviation B := (measurableTypeR R).
Local Abbreviation mu := (@lebesgue_measure R).
Local Abbreviation G := (normal_prob (0%R : R) (1%R : R)).
Local Abbreviation p := (normal_pdf (0%R : R) (1%R : R)).
Local Abbreviation f := (fun x : R => ((x ^+ 2)%R)%:E).
Local Abbreviation d := (fun x : R => (p x)%:E).
Local Abbreviation w := (fun x : R => ((x ^+ 2 * p x)%R)%:E).

(** Define the scalar standard second moment using the actual
    Gaussian measure, with no numerical value in its definition. *)
Definition gmc_standard_variance_value : \bar R :=
  \int[G]_x f x.

(** This scalar moment is finite by the verified integrability
    theorem; no evaluation of the Gaussian integral is necessary. *)
Lemma gmc_standard_variance_finite :
  gmc_standard_variance_value \is a fin_num.
Proof.
have Hs : (1%R : R) != 0%R.
{ exact: oner_neq0. }
have Hi : G.-integrable [set: R] f.
{ exact (@gmc_centered_normal_second_moment_integrable R 1%R Hs). }
rewrite /gmc_standard_variance_value.
exact: integrable_fin_num Hi.
Qed.

(** The diagonal scalar moment equals its square-weighted density
    integral under Lebesgue measure, using the previously verified
    nonnegative change-of-measure theorem. *)
Theorem gmc_standard_variance_density :
  gmc_standard_variance_value = \int[mu]_x w x.
Proof.
have mf : measurable_fun [set: R] f.
{ apply/measurable_EFinP; exact: exprn_measurable. }
have f0 (x : R) : 0 <= f x.
{ by rewrite lee_fin sqr_ge0. }
rewrite /gmc_standard_variance_value.
rewrite (@gmc_normal_nonnegative_integral R 0%R 1%R f f0 mf).
apply: eq_integral => x _.
by rewrite -EFinM.
Qed.

(** The derivative candidate for x times the standard density,
    phi(x) - x^2 phi(x), is integrable on the whole real line.
    This is a signed density balance, not an improper-integral
    convergence assumption. *)
Theorem gmc_standard_density_balance_integrable :
  mu.-integrable [set: R]
    (fun x => ((p x - x ^+ 2 * p x)%R)%:E).
Proof.
have Hs : (1%R : R) != 0%R.
{ exact: oner_neq0. }
have di : mu.-integrable [set: R] d.
{ exact: integrable_normal_pdf. }
have wi : mu.-integrable [set: R] w.
{ exact (@gmc_centered_square_pdf_integrable R 1%R Hs). }
have E : (fun x : R => ((p x - x ^+ 2 * p x)%R)%:E) =
    (fun x : R => d x - w x).
{ apply/funext => x; by rewrite EFinB. }
rewrite E.
exact: integrableB di wi.
Qed.

(** Integrating the balance subtracts the scalar second moment
    from the normalized unit mass. It suffices to show this
    balance integrates to zero in a subsequent calculus proof. *)
Theorem gmc_standard_density_balance_integral :
  \int[mu]_x ((p x - x ^+ 2 * p x)%R)%:E =
    1 - gmc_standard_variance_value.
Proof.
have Hs : (1%R : R) != 0%R.
{ exact: oner_neq0. }
have di : mu.-integrable [set: R] d.
{ exact: integrable_normal_pdf. }
have wi : mu.-integrable [set: R] w.
{ exact (@gmc_centered_square_pdf_integrable R 1%R Hs). }
transitivity (\int[mu]_x (d x - w x)).
- apply: eq_integral => x _; by rewrite EFinB.
- rewrite (@integralB _ B R mu setT measurableT d w di wi).
  by rewrite integral_normal_pdf -gmc_standard_variance_density.
Qed.

Variable n : nat.
Local Abbreviation T := (n.-tuple B).
Local Abbreviation P := (@gmc_standard_history R n).

(** Every coordinate has the same actual scalar second moment
    irrespective of the ambient dimension or its ordinal index. *)
Theorem gmc_standard_coordinate_variance_value (i : 'I_n) :
  \int[P]_t ((tnth t i ^+ 2)%R)%:E = gmc_standard_variance_value.
Proof.
have Hs : (1%R : R) != 0%R.
{ exact: oner_neq0. }
have Hi : G.-integrable [set: R] f.
{ exact (@gmc_centered_normal_second_moment_integrable R 1%R Hs). }
rewrite /gmc_standard_variance_value.
symmetry.
exact (@gmc_standard_coordinate_signed R n i f Hi).
Qed.

(** Every coordinate product is integrable, including equal indices.
    The diagonal uses the verified square integrability, while
    distinct indices use the verified pair-law cross moment. *)
Theorem gmc_standard_all_coordinate_products_integrable (i j : 'I_n) :
  P.-integrable [set: T]
    (fun t => (tnth t i)%:E * (tnth t j)%:E).
Proof.
case Hij : (i == j).
- move/eqP: Hij => E; subst j.
  have Hfun : (fun t : T => (tnth t i)%:E * (tnth t i)%:E) =
      (fun t : T => ((tnth t i ^+ 2)%R)%:E).
  { apply/funext => t; by rewrite -EFinM expr2. }
  rewrite Hfun.
  exact (@gmc_standard_coordinate_second_moment R n i).
- have Hne : i != j by rewrite Hij.
  exact (@gmc_standard_coordinate_cross_integrable R n i j Hne).
Qed.

(** The complete coordinate moment matrix is a scalar multiple of
    the identity. Evaluation of that scalar is the sole remaining
    diagonal moment problem; no unit-variance premise is inserted. *)
Theorem gmc_standard_coordinate_product_value (i j : 'I_n) :
  \int[P]_t ((tnth t i)%:E * (tnth t j)%:E) =
    if i == j then gmc_standard_variance_value else 0.
Proof.
case Hij : (i == j).
- move/eqP: Hij => E; subst j.
  transitivity (\int[P]_t ((tnth t i ^+ 2)%R)%:E).
  + apply: eq_integral => t _; by rewrite -EFinM expr2.
  + exact: gmc_standard_coordinate_variance_value.
- have Hne : i != j by rewrite Hij.
  exact (@gmc_standard_coordinate_cross_zero R n i j Hne).
Qed.
End VarianceReduction.
