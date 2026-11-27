(** Module: GaussianJointDensityMeasure.v
    Purpose: Construct the scalar latent/observation joint measure
    from its nonnegative density on the product of real Borel spaces.
    Prove joint density measurability and the measurable-section
    representation using MathComp-Analysis's existing Tonelli theorem.
    The coordinate order is (observation, latent variable).
    The normalization, actual residual pushforward factorization and
    multivariate extension are subsequent obligations.
    Researcher/requester: Anders Hellström.
    AI disclosure: AI-assisted proof candidates; validation pending.
*)
From HB Require Import structures.
From mathcomp Require Import boot order ssralg ssrnum.
From mathcomp Require Import boolp classical_sets functions reals ereal topology normedtype.
From mathcomp Require Import sequences esum.
From mathcomp Require Import measure lebesgue_integral lebesgue_stieltjes_measure
  lebesgue_measure measurable_realfun.
From mathcomp.analysis Require Import normal_distribution.
Require Import GaussianOriginalResidualMeasure.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section JointDensity.
Context {R : realType}.
Import MeasurableR.
Local Abbreviation mu := (@lebesgue_measure R).
Local Abbreviation BorelPair := ((measurableTypeR R * measurableTypeR R)%type).

(** Joint likelihood times prior, in observation-first coordinates.
    Use the ordinary real density here, lifting only at integration. *)
Definition gmc_joint_density (m0 s0 s : R) (z : R * R) : R :=
  normal_pdf z.2 s z.1 * normal_pdf m0 s0 z.2.

(** Rewrite the varying-location likelihood as a fixed-location
    Gaussian composed with the difference of the two coordinates. *)
Lemma gmc_joint_likelihood_center (s : R) (z : R * R) :
  s != 0 -> normal_pdf z.2 s z.1 =
    normal_pdf 0 s (z.1 - z.2).
Proof.
move=> Hs.
by rewrite !normal_pdfE// /normal_fun subr0.
Qed.

(** Joint Borel measurability of the likelihood/prior density.
    Reuse measurable coordinate projections, subtraction, composition,
    multiplication, and the library's scalar normal density. *)
Theorem gmc_joint_density_measurable (m0 s0 s : R) :
  s != 0 -> measurable_fun [set: BorelPair] (gmc_joint_density m0 s0 s).
Proof.
move=> Hs.
have mdiff : measurable_fun [set: BorelPair]
    (fun z : R * R => z.1 - z.2).
  apply: measurable_funB.
  - exact: measurable_fst.
  - exact: measurable_snd.
have ml : measurable_fun [set: BorelPair]
    (fun z : R * R => normal_pdf 0 s (z.1 - z.2)).
  apply: measurableT_comp.
  - exact: measurable_normal_pdf.
  - exact: mdiff.
have mp : measurable_fun [set: BorelPair]
    (fun z : R * R => normal_pdf m0 s0 z.2).
  apply: measurableT_comp.
  - exact: measurable_normal_pdf.
  - exact: measurable_snd.
have Hd : gmc_joint_density m0 s0 s =
    (fun z : R * R => normal_pdf 0 s (z.1 - z.2) *
                                  normal_pdf m0 s0 z.2).
  apply/funext => z.
  by rewrite /gmc_joint_density (@gmc_joint_likelihood_center s z Hs).
rewrite Hd.
exact: measurable_funM ml mp.
Qed.

(** The joint density is pointwise nonnegative, including the
    upstream fallback density at zero scale. *)
Lemma gmc_joint_density_ge0 (m0 s0 s : R) (z : R * R) :
  0 <= gmc_joint_density m0 s0 s z.
Proof. by rewrite /gmc_joint_density mulr_ge0 ?normal_pdf_ge0. Qed.

(* All mass and integral operations below are extended-real operations.
   The observation scale remains an ordinary real: explicitly scope
   its zero literal with %R in every nonzero-scale hypothesis. *)
Local Open Scope ereal_scope.

(** Mass of a joint measurable event with respect to the product
    Lebesgue measure and the actual Gaussian density. *)
Definition gmc_joint_mass (m0 s0 s : R) (A : set BorelPair) : \bar R :=
  \int[(mu \x mu)]_(z in A) (gmc_joint_density m0 s0 s z)%:E.

(** The empty event has zero mass by the library's empty integral. *)
Lemma gmc_joint_mass0 (m0 s0 s : R) : gmc_joint_mass m0 s0 s set0 = 0.
Proof. by rewrite /gmc_joint_mass integral_set0. Qed.

(** Every event has nonnegative mass, without assuming integrability. *)
Lemma gmc_joint_mass_ge0 (m0 s0 s : R) (A : set BorelPair) :
  0 <= gmc_joint_mass m0 s0 s A.
Proof.
rewrite /gmc_joint_mass; apply: integral_ge0 => z _.
by rewrite lee_fin; exact: gmc_joint_density_ge0.
Qed.

(** Countable additivity follows from the existing nonnegative
    integral disjoint-union theorem. No probability axiom is added. *)
Theorem gmc_joint_mass_sigma_additive (m0 s0 s : R) :
  s != 0%R -> semi_sigma_additive (gmc_joint_mass m0 s0 s).
Proof.
move=> Hs F mF tF mUF.
have Hmf : measurable_fun [set: BorelPair]
    (fun z : R * R => (gmc_joint_density m0 s0 s z)%:E).
  by apply/measurable_EFinP; exact: gmc_joint_density_measurable.
have Hsum :
    gmc_joint_mass m0 s0 s (\bigcup_n F n) =
    \sum_(n <oo) gmc_joint_mass m0 s0 s (F n).
  rewrite /gmc_joint_mass.
  apply: ge0_integral_bigcup => //.
  - exact: measurable_funTS Hmf.
  - by move=> z _; rewrite lee_fin; exact: gmc_joint_density_ge0.
rewrite Hsum.
apply/cvg_closeP; split.
- apply: is_cvg_nneseries => n _ _.
  exact: gmc_joint_mass_ge0.
- by rewrite closeE.
Qed.

(** A genuine joint measure, constructed from the three proved
    measure laws. Nonzero observation scale certifies measurability. *)
HB.instance Definition _ m0 s0 s (Hs : s != 0%R) :=
  isMeasure.Build _ _ _ (gmc_joint_mass m0 s0 s)
    (gmc_joint_mass0 m0 s0 s) (gmc_joint_mass_ge0 m0 s0 s)
    (@gmc_joint_mass_sigma_additive m0 s0 s Hs).

(** Tonelli for the restricted joint density gives an iterated integral
    over the actual measurable sections of an arbitrary joint event.
    This connects the two-dimensional measure to the scalar slice
    results without assuming a Gaussian change-of-variables formula. *)
Theorem gmc_joint_mass_sections (m0 s0 s : R) (A : set BorelPair) :
  s != 0%R -> measurable A ->
  gmc_joint_mass m0 s0 s A =
  \int[mu]_x \int[mu]_(t in xsection A x)
    (gmc_joint_density m0 s0 s (x,t))%:E.
Proof.
move=> Hs mA.
pose f := fun z : R * R => (gmc_joint_density m0 s0 s z)%:E.
pose h := f \_ A.
have mf : measurable_fun [set: BorelPair] f.
  rewrite /f; by apply/measurable_EFinP; exact: gmc_joint_density_measurable.
have mh : measurable_fun [set: BorelPair] h.
  rewrite /h; apply/(measurable_restrictT f mA).1.
  exact: measurable_funTS mf.
have h0 z : 0 <= h z.
  rewrite /h; apply: erestrict_ge0 => t _.
  by rewrite /f lee_fin; exact: gmc_joint_density_ge0.
change (\int[(mu \x mu)]_(z in A) f z =
        \int[mu]_x \int[mu]_(t in xsection A x) f (x,t)).
rewrite (integral_mkcond A f).
transitivity (\int[mu]_x \int[mu]_t h (x,t)).
- exact (@fubini_tonelli1 _ _ (measurableTypeR R)
    (measurableTypeR R) R mu mu h mh h0).
- apply: eq_integral => x _.
  rewrite (integral_mkcond (xsection A x) (fun t => f (x,t))).
  apply: eq_integral => t _.
  by rewrite /h !patchE mem_xsection.
Qed.
End JointDensity.
