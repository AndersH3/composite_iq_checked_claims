(** Module: GaussianVarianceCalculus.v
    Purpose: Derive the standard normal density and its weighted
    primitive, then evaluate the signed density balance on finite
    intervals using the library's fundamental theorem of calculus.
    The limit at infinity and exact variance are separate obligations.
    Reuse MathComp derivative instances, continuity and FTC2.
    Researcher/requester: Anders Hellström.
    AI disclosure: AI-assisted proof candidates; validation pending.
*)
From mathcomp Require Import boot order ssralg ssrnum interval field_tactic.
From mathcomp Require Import boolp classical_sets set_interval functions
  reals ereal topology normedtype derive sequences exp real_interval.
(* MathComp Analysis defines expR in sequences, while exp supplies
   its derivative and continuity lemmas. Import both explicitly. *)
From mathcomp Require Import measure lebesgue_measure lebesgue_integral ftc.
From mathcomp.analysis Require Import normal_distribution.
Require Import GaussianVarianceReduction.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldNormedType.Exports.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section VarianceCalculus.
Context {R : realType}.
Import MeasurableR.
Local Abbreviation p := (normal_pdf (0 : R) (1 : R)).
Local Abbreviation k := (normal_peak (1 : R)).
Local Abbreviation q :=
  ((cst (- (2%:R : R)^-1)) * ((id : R -> R) ^+ 2))%R.
Local Abbreviation F := ((id : R -> R) * p)%R.
Local Abbreviation b := (fun x : R => p x - x ^+ 2 * p x).
Local Abbreviation mu := (@lebesgue_measure R).

(** Express the library density in pointwise function-ring form,
    so its derivative can be synthesized from existing instances.
    The scale is explicitly one, hence nonzero. *)
Lemma gmc_standard_density_expression :
  p = ((cst k) * (expR \o q))%R.
Proof.
have Hs : (1 : R) != 0 by exact: oner_neq0.
apply/funext => x.
rewrite (normal_pdfE 0 Hs) /normal_fun subr0 expr1n.
(* Natural scaling of the ring unit is definitionally the natural
   cast: (1 *+ 2) = 2%:R. Expose both scalar exponents explicitly,
   then use only the library's negation and commutativity laws. *)
change (k * expR (- x ^+ 2 / (2%:R : R)) =
        k * expR ((- (2%:R : R)^-1) * x ^+ 2)).
have Harg : - x ^+ 2 / (2%:R : R) =
    (- (2%:R : R)^-1) * x ^+ 2.
{ by rewrite !mulNr mulrC. }
by rewrite Harg.
Qed.

(** The exponent polynomial is differentiable with derivative -x.
    Use the existing multiplication, constant, identity and natural
    power instances rather than an independent difference quotient. *)
Lemma gmc_standard_exponent_derivative (x : R) :
  'D_1 q x = - x.
Proof.
rewrite derive_val.
change ((- (2%:R : R)^-1) * ((2%:R * x ^+ 1) * 1) +
    x ^+ 2 * 0 = - x).
rewrite expr1 mulr1 mulr0 addr0.
have H2 : (2%:R : R) != 0 by rewrite pnatr_eq0.
by rewrite mulNr mulrA (mulVf H2) mul1r.
Qed.

(** The density derivative is the negative coordinate times its
    density. The chain rule is the pinned library instance for
    exponential composition with the quadratic exponent. *)
Theorem gmc_standard_density_derivative (x : R) :
  is_derive x 1 p (- x * p x).
Proof.
have dq : derivable q x 1 by exact: ex_derive.
have dp : derivable p x 1.
{ rewrite gmc_standard_density_expression; exact: ex_derive. }
apply: DeriveDef; first exact dp.
rewrite gmc_standard_density_expression deriveM.
- exact: ex_derive.
- exact: ex_derive.
- rewrite derive_cst fctE mulr0 addr0.
  have Hc := @derive1_comp _ q (@expR R) x dq
    (derivable_expR (q x)).
  rewrite !derive1E (derive_val (is_derive_expR (q x)))
    gmc_standard_exponent_derivative in Hc.
  rewrite Hc fctE /=.
  by rewrite mulrA [LHS]mulrC.
Qed.

(** The product rule gives the exact density balance as the
    derivative of x times its density, the primitive for FTC2. *)
Theorem gmc_standard_weighted_density_derivative (x : R) :
  is_derive x 1 F (b x).
Proof.
have dp := gmc_standard_density_derivative x.
have dF : derivable F x 1.
{ apply: derivableM.
  - exact: derivable_id.
  - exact: (ex_derive dp). }
apply: DeriveDef; first exact dF.
rewrite deriveM; [exact: derivable_id | exact: (ex_derive dp) |].
rewrite (derive_val dp) derive_id.
change (x * (- x * p x) + p x * 1 = p x - x ^+ 2 * p x).
by rewrite mulr1 mulNr mulrN mulrA -expr2 addrC.
Qed.

(** The primitive is continuous on the full real line by its
    established differentiability, including both endpoints of
    any subsequent finite integration interval. *)
Lemma gmc_standard_weighted_density_continuous :
  continuous F.
Proof.
move=> x.
apply/differentiable_continuous/derivable1_diffP.
exact: (ex_derive (gmc_standard_weighted_density_derivative x)).
Qed.

(** Continuity of the density balance follows from the nonzero
    normal density continuity theorem and ordinary product rules. *)
Lemma gmc_standard_density_balance_continuous :
  continuous b.
Proof.
have cp : continuous p.
{ exact: continuous_normal_pdf oner_neq0. }
move=> x; apply: continuousB; first exact: cp.
apply: continuousM; last exact: cp.
exact: sqr_continuous.
Qed.

Local Open Scope ereal_scope.

(** The exact finite-interval density balance integral is a
    difference of the weighted density at the endpoints.
    No improper integral or boundary-limit hypothesis is used. *)
Theorem gmc_standard_density_balance_interval (a z : R) :
  (a < z)%R ->
  \int[mu]_(x in `[a, z]) (b x)%:E = (F z)%:E - (F a)%:E.
Proof.
move=> az.
apply: (@continuous_FTC2 R b F a z az).
- apply: continuous_subspaceW (subsetT _).
  exact/continuous_subspaceT/gmc_standard_density_balance_continuous.
- split => /=.
  + move=> x _.
    exact: (ex_derive (gmc_standard_weighted_density_derivative x)).
  + exact/cvg_at_right_filter/gmc_standard_weighted_density_continuous.
  + exact/cvg_at_left_filter/gmc_standard_weighted_density_continuous.
- move=> x _.
  rewrite derive1E.
  exact: (derive_val (gmc_standard_weighted_density_derivative x)).
Qed.
End VarianceCalculus.
