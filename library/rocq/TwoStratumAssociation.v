(** Module: TwoStratumAssociation.v
   Purpose: Derive an exact association decomposition into within-stratum
   and selection-between-strata terms, sharp sign rules and Simpson-reversal
   criteria usable in multiple-test admissions reports.
   Mathematical representation: Two four-cell contingency tables have raw
   concordant and discordant masses. The pooled determinant equals a
   within component and a product of two between-stratum marginal contrasts.
   Explicit hypotheses: Polynomial identities hold for arbitrary reals.
   Sign and conditional-rate lemmas demand positive stratum totals; strict
   association conclusions never presume independence or random selection.
   Library use: Rocq Stdlib.Reals, Lra, Psatz, Field, Ring, and ordinary
   canonical polynomial operators. No custom probability, list, or matrix
   implementation is introduced; report-specific interpretation reuses
   Admissions.TwoEventModel in its own specialized source module.
   Limitations: Finite two-by-two probability tables and exact algebra only;
   not a Gaussian conditional law, numerical tail, or empirical IQ inference.
   Reproduction: scripts/compile_rocq.sh with pinned Rocq Prover 9.2,
   before the Towers-specific ThreeTestSelectionDecomposition.v module.
   AI disclosure: The following source and explanatory proof comments were
   drafted with AI assistance. Formal validity requires pinned Rocq CI.
*)
From Stdlib Require Import Reals Lra Psatz.
Open Scope R_scope.

(**
 [mix_total_yes] (definition) — Joint probability mass of the first selection stratum, before normalization.
 Mathematical meaning: Joint probability mass of the first selection stratum, before normalization.
 Exact declaration: Definition mix_total_yes (j1 x1 y1 n1 j0 x0 y0 n0 : R) : R := j1+x1+y1+n1.
 Premises and side conditions: None for the algebraic real definition;
 sample normalization and positive conditioning mass are only imposed in
 later propositions that require their statistical interpretation.
 Proof/definition method: A transparent scalar polynomial; no recursive
 probability sum, synthetic distribution, covariance matrix, or axiom.
 Library reuse: Rocq Stdlib.Reals, Ring, Lra and Psatz; the standard
 commutative ring operations, rather than custom polynomial infrastructure.
 Boundary: Exact two-stratum finite contingency-table algebra and no
 Gaussian, continuous probability or psychometric calibration inference.
*)
Definition mix_total_yes (j1 x1 y1 n1 j0 x0 y0 n0 : R) : R := j1+x1+y1+n1.

(**
 [mix_total_no] (definition) — Joint probability mass of the complementary selection stratum, before normalization.
 Mathematical meaning: Joint probability mass of the complementary selection stratum, before normalization.
 Exact declaration: Definition mix_total_no (j1 x1 y1 n1 j0 x0 y0 n0 : R) : R := j0+x0+y0+n0.
 Premises and side conditions: None for the algebraic real definition;
 sample normalization and positive conditioning mass are only imposed in
 later propositions that require their statistical interpretation.
 Proof/definition method: A transparent scalar polynomial; no recursive
 probability sum, synthetic distribution, covariance matrix, or axiom.
 Library reuse: Rocq Stdlib.Reals, Ring, Lra and Psatz; the standard
 commutative ring operations, rather than custom polynomial infrastructure.
 Boundary: Exact two-stratum finite contingency-table algebra and no
 Gaussian, continuous probability or psychometric calibration inference.
*)
Definition mix_total_no (j1 x1 y1 n1 j0 x0 y0 n0 : R) : R := j0+x0+y0+n0.

(**
 [mix_local_assoc_yes] (definition) — Determinantal association (concordant less discordant product) in the first selection stratum.
 Mathematical meaning: Determinantal association (concordant less discordant product) in the first selection stratum.
 Exact declaration: Definition mix_local_assoc_yes (j1 x1 y1 n1 j0 x0 y0 n0 : R) : R := j1*n1-x1*y1.
 Premises and side conditions: None for the algebraic real definition;
 sample normalization and positive conditioning mass are only imposed in
 later propositions that require their statistical interpretation.
 Proof/definition method: A transparent scalar polynomial; no recursive
 probability sum, synthetic distribution, covariance matrix, or axiom.
 Library reuse: Rocq Stdlib.Reals, Ring, Lra and Psatz; the standard
 commutative ring operations, rather than custom polynomial infrastructure.
 Boundary: Exact two-stratum finite contingency-table algebra and no
 Gaussian, continuous probability or psychometric calibration inference.
*)
Definition mix_local_assoc_yes (j1 x1 y1 n1 j0 x0 y0 n0 : R) : R := j1*n1-x1*y1.

(**
 [mix_local_assoc_no] (definition) — Determinantal association in the complementary selection stratum.
 Mathematical meaning: Determinantal association in the complementary selection stratum.
 Exact declaration: Definition mix_local_assoc_no (j1 x1 y1 n1 j0 x0 y0 n0 : R) : R := j0*n0-x0*y0.
 Premises and side conditions: None for the algebraic real definition;
 sample normalization and positive conditioning mass are only imposed in
 later propositions that require their statistical interpretation.
 Proof/definition method: A transparent scalar polynomial; no recursive
 probability sum, synthetic distribution, covariance matrix, or axiom.
 Library reuse: Rocq Stdlib.Reals, Ring, Lra and Psatz; the standard
 commutative ring operations, rather than custom polynomial infrastructure.
 Boundary: Exact two-stratum finite contingency-table algebra and no
 Gaussian, continuous probability or psychometric calibration inference.
*)
Definition mix_local_assoc_no (j1 x1 y1 n1 j0 x0 y0 n0 : R) : R := j0*n0-x0*y0.

(**
 [mix_pooled_association] (definition) — Unnormalized two-test cross-product association after the selected subpopulations are combined.
 Mathematical meaning: Unnormalized two-test cross-product association after the selected subpopulations are combined.
 Exact declaration: Definition mix_pooled_association (j1 x1 y1 n1 j0 x0 y0 n0 : R) : R := (j1+j0)*(n1+n0)-(x1+x0)*(y1+y0).
 Premises and side conditions: None for the algebraic real definition;
 sample normalization and positive conditioning mass are only imposed in
 later propositions that require their statistical interpretation.
 Proof/definition method: A transparent scalar polynomial; no recursive
 probability sum, synthetic distribution, covariance matrix, or axiom.
 Library reuse: Rocq Stdlib.Reals, Ring, Lra and Psatz; the standard
 commutative ring operations, rather than custom polynomial infrastructure.
 Boundary: Exact two-stratum finite contingency-table algebra and no
 Gaussian, continuous probability or psychometric calibration inference.
*)
Definition mix_pooled_association (j1 x1 y1 n1 j0 x0 y0 n0 : R) : R := (j1+j0)*(n1+n0)-(x1+x0)*(y1+y0).

(**
 [mix_gap_first] (definition) — Selection contrast in the first marginal admission probability, scaled by both stratum masses.
 Mathematical meaning: Selection contrast in the first marginal admission probability, scaled by both stratum masses.
 Exact declaration: Definition mix_gap_first (j1 x1 y1 n1 j0 x0 y0 n0 : R) : R := (j1+x1)*(j0+x0+y0+n0)-(j0+x0)*(j1+x1+y1+n1).
 Premises and side conditions: None for the algebraic real definition;
 sample normalization and positive conditioning mass are only imposed in
 later propositions that require their statistical interpretation.
 Proof/definition method: A transparent scalar polynomial; no recursive
 probability sum, synthetic distribution, covariance matrix, or axiom.
 Library reuse: Rocq Stdlib.Reals, Ring, Lra and Psatz; the standard
 commutative ring operations, rather than custom polynomial infrastructure.
 Boundary: Exact two-stratum finite contingency-table algebra and no
 Gaussian, continuous probability or psychometric calibration inference.
*)
Definition mix_gap_first (j1 x1 y1 n1 j0 x0 y0 n0 : R) : R := (j1+x1)*(j0+x0+y0+n0)-(j0+x0)*(j1+x1+y1+n1).

(**
 [mix_gap_second] (definition) — Selection contrast in the second marginal admission probability, scaled by both stratum masses.
 Mathematical meaning: Selection contrast in the second marginal admission probability, scaled by both stratum masses.
 Exact declaration: Definition mix_gap_second (j1 x1 y1 n1 j0 x0 y0 n0 : R) : R := (j1+y1)*(j0+x0+y0+n0)-(j0+y0)*(j1+x1+y1+n1).
 Premises and side conditions: None for the algebraic real definition;
 sample normalization and positive conditioning mass are only imposed in
 later propositions that require their statistical interpretation.
 Proof/definition method: A transparent scalar polynomial; no recursive
 probability sum, synthetic distribution, covariance matrix, or axiom.
 Library reuse: Rocq Stdlib.Reals, Ring, Lra and Psatz; the standard
 commutative ring operations, rather than custom polynomial infrastructure.
 Boundary: Exact two-stratum finite contingency-table algebra and no
 Gaussian, continuous probability or psychometric calibration inference.
*)
Definition mix_gap_second (j1 x1 y1 n1 j0 x0 y0 n0 : R) : R := (j1+y1)*(j0+x0+y0+n0)-(j0+y0)*(j1+x1+y1+n1).

(**
 [mix_within] (definition) — Within-stratum association component weighted by the opposite stratum mass.
 Mathematical meaning: Within-stratum association component weighted by the opposite stratum mass.
 Exact declaration: Definition mix_within (j1 x1 y1 n1 j0 x0 y0 n0 : R) : R := (j0+x0+y0+n0)*(j1*n1-x1*y1)+(j1+x1+y1+n1)*(j0*n0-x0*y0).
 Premises and side conditions: None for the algebraic real definition;
 sample normalization and positive conditioning mass are only imposed in
 later propositions that require their statistical interpretation.
 Proof/definition method: A transparent scalar polynomial; no recursive
 probability sum, synthetic distribution, covariance matrix, or axiom.
 Library reuse: Rocq Stdlib.Reals, Ring, Lra and Psatz; the standard
 commutative ring operations, rather than custom polynomial infrastructure.
 Boundary: Exact two-stratum finite contingency-table algebra and no
 Gaussian, continuous probability or psychometric calibration inference.
*)
Definition mix_within (j1 x1 y1 n1 j0 x0 y0 n0 : R) : R := (j0+x0+y0+n0)*(j1*n1-x1*y1)+(j1+x1+y1+n1)*(j0*n0-x0*y0).

(**
 [mix_between] (definition) — Cross-stratum selection component: product of two signed conditional marginal contrasts.
 Mathematical meaning: Cross-stratum selection component: product of two signed conditional marginal contrasts.
 Exact declaration: Definition mix_between (j1 x1 y1 n1 j0 x0 y0 n0 : R) : R := ((j1+x1)*(j0+x0+y0+n0)-(j0+x0)*(j1+x1+y1+n1))*((j1+y1)*(j0+x0+y0+n0)-(j0+y0)*(j1+x1+y1+n1)).
 Premises and side conditions: None for the algebraic real definition;
 sample normalization and positive conditioning mass are only imposed in
 later propositions that require their statistical interpretation.
 Proof/definition method: A transparent scalar polynomial; no recursive
 probability sum, synthetic distribution, covariance matrix, or axiom.
 Library reuse: Rocq Stdlib.Reals, Ring, Lra and Psatz; the standard
 commutative ring operations, rather than custom polynomial infrastructure.
 Boundary: Exact two-stratum finite contingency-table algebra and no
 Gaussian, continuous probability or psychometric calibration inference.
*)
Definition mix_between (j1 x1 y1 n1 j0 x0 y0 n0 : R) : R := ((j1+x1)*(j0+x0+y0+n0)-(j0+x0)*(j1+x1+y1+n1))*((j1+y1)*(j0+x0+y0+n0)-(j0+y0)*(j1+x1+y1+n1)).

(**
 [mix_effect] (definition) — Combined adjusted within plus between-stratum association contribution.
 Mathematical meaning: Combined adjusted within plus between-stratum association contribution.
 Exact declaration: Definition mix_effect (j1 x1 y1 n1 j0 x0 y0 n0 : R) : R := ((j1+x1+y1+n1)+(j0+x0+y0+n0))*((j0+x0+y0+n0)*(j1*n1-x1*y1)+(j1+x1+y1+n1)*(j0*n0-x0*y0))+((j1+x1)*(j0+x0+y0+n0)-(j0+x0)*(j1+x1+y1+n1))*((j1+y1)*(j0+x0+y0+n0)-(j0+y0)*(j1+x1+y1+n1)).
 Premises and side conditions: None for the algebraic real definition;
 sample normalization and positive conditioning mass are only imposed in
 later propositions that require their statistical interpretation.
 Proof/definition method: A transparent scalar polynomial; no recursive
 probability sum, synthetic distribution, covariance matrix, or axiom.
 Library reuse: Rocq Stdlib.Reals, Ring, Lra and Psatz; the standard
 commutative ring operations, rather than custom polynomial infrastructure.
 Boundary: Exact two-stratum finite contingency-table algebra and no
 Gaussian, continuous probability or psychometric calibration inference.
*)
Definition mix_effect (j1 x1 y1 n1 j0 x0 y0 n0 : R) : R := ((j1+x1+y1+n1)+(j0+x0+y0+n0))*((j0+x0+y0+n0)*(j1*n1-x1*y1)+(j1+x1+y1+n1)*(j0*n0-x0*y0))+((j1+x1)*(j0+x0+y0+n0)-(j0+x0)*(j1+x1+y1+n1))*((j1+y1)*(j0+x0+y0+n0)-(j0+y0)*(j1+x1+y1+n1)).

(**
 [mix_stratified_association_identity] (theorem) — The pooled two-test determinant decomposes into a stratum-mass-weighted within-association term plus the product of the selection marginal contrasts.
 Mathematical meaning: The pooled two-test determinant decomposes into a stratum-mass-weighted within-association term plus the product of the selection marginal contrasts.
 Exact checked proposition: forall j1 x1 y1 n1 j0 x0 y0 n0 : R, mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0*mix_total_no j1 x1 y1 n1 j0 x0 y0 n0*mix_pooled_association j1 x1 y1 n1 j0 x0 y0 n0=(mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0+mix_total_no j1 x1 y1 n1 j0 x0 y0 n0)*mix_within j1 x1 y1 n1 j0 x0 y0 n0+mix_between j1 x1 y1 n1 j0 x0 y0 n0.
 Premises and side conditions: All eight real cell masses are explicit.
 Polynomial equalities have no sign hypotheses. Every conditional-rate
 identity or sign inference explicitly requires strictly positive stratum
 masses; additional inequalities state their own sign assumptions.
 Proof/definition method: Reuse previously checked decomposition identities and trusted standard real field/positivity tactics.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Field, Ring, and previous
 TwoStratumAssociation identities. These statements are pure real-polynomial
 consequences, not a second finite-event probability implementation.
 Boundary: Exact two-stratum admissions association and selection algebra,
 not Gaussian distributions, normal-tail integrals, or IQ population data.
*)
Theorem mix_stratified_association_identity :
  forall j1 x1 y1 n1 j0 x0 y0 n0 : R, mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0*mix_total_no j1 x1 y1 n1 j0 x0 y0 n0*mix_pooled_association j1 x1 y1 n1 j0 x0 y0 n0=(mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0+mix_total_no j1 x1 y1 n1 j0 x0 y0 n0)*mix_within j1 x1 y1 n1 j0 x0 y0 n0+mix_between j1 x1 y1 n1 j0 x0 y0 n0.
Proof.
  intros; unfold mix_total_yes, mix_total_no, mix_pooled_association, mix_within, mix_between; ring.
Qed.

(**
 [mix_pooled_invariant_under_strata_swap] (theorem) — The pooled association is invariant under swapping the selected and nonselected groups.
 Mathematical meaning: The pooled association is invariant under swapping the selected and nonselected groups.
 Exact checked proposition: forall j1 x1 y1 n1 j0 x0 y0 n0 : R, mix_pooled_association j1 x1 y1 n1 j0 x0 y0 n0=mix_pooled_association j0 x0 y0 n0 j1 x1 y1 n1.
 Premises and side conditions: All eight real cell masses are explicit.
 Polynomial equalities have no sign hypotheses. Every conditional-rate
 identity or sign inference explicitly requires strictly positive stratum
 masses; additional inequalities state their own sign assumptions.
 Proof/definition method: Reuse previously checked decomposition identities and trusted standard real field/positivity tactics.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Field, Ring, and previous
 TwoStratumAssociation identities. These statements are pure real-polynomial
 consequences, not a second finite-event probability implementation.
 Boundary: Exact two-stratum admissions association and selection algebra,
 not Gaussian distributions, normal-tail integrals, or IQ population data.
*)
Theorem mix_pooled_invariant_under_strata_swap :
  forall j1 x1 y1 n1 j0 x0 y0 n0 : R, mix_pooled_association j1 x1 y1 n1 j0 x0 y0 n0=mix_pooled_association j0 x0 y0 n0 j1 x1 y1 n1.
Proof.
  intros; unfold mix_pooled_association; ring.
Qed.

(**
 [mix_pooled_invariant_under_routes_swap] (theorem) — Swapping the first and second admissions routes preserves their pooled cross-product association.
 Mathematical meaning: Swapping the first and second admissions routes preserves their pooled cross-product association.
 Exact checked proposition: forall j1 x1 y1 n1 j0 x0 y0 n0 : R, mix_pooled_association j1 x1 y1 n1 j0 x0 y0 n0=mix_pooled_association j1 y1 x1 n1 j0 y0 x0 n0.
 Premises and side conditions: All eight real cell masses are explicit.
 Polynomial equalities have no sign hypotheses. Every conditional-rate
 identity or sign inference explicitly requires strictly positive stratum
 masses; additional inequalities state their own sign assumptions.
 Proof/definition method: Reuse previously checked decomposition identities and trusted standard real field/positivity tactics.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Field, Ring, and previous
 TwoStratumAssociation identities. These statements are pure real-polynomial
 consequences, not a second finite-event probability implementation.
 Boundary: Exact two-stratum admissions association and selection algebra,
 not Gaussian distributions, normal-tail integrals, or IQ population data.
*)
Theorem mix_pooled_invariant_under_routes_swap :
  forall j1 x1 y1 n1 j0 x0 y0 n0 : R, mix_pooled_association j1 x1 y1 n1 j0 x0 y0 n0=mix_pooled_association j1 y1 x1 n1 j0 y0 x0 n0.
Proof.
  intros; unfold mix_pooled_association; ring.
Qed.

(**
 [mix_first_gap_reverses_with_stratum_swap] (theorem) — Reversing the selected and nonselected group negates the signed first-route conditional marginal contrast.
 Mathematical meaning: Reversing the selected and nonselected group negates the signed first-route conditional marginal contrast.
 Exact checked proposition: forall j1 x1 y1 n1 j0 x0 y0 n0 : R, mix_gap_first j1 x1 y1 n1 j0 x0 y0 n0=-mix_gap_first j0 x0 y0 n0 j1 x1 y1 n1.
 Premises and side conditions: All eight real cell masses are explicit.
 Polynomial equalities have no sign hypotheses. Every conditional-rate
 identity or sign inference explicitly requires strictly positive stratum
 masses; additional inequalities state their own sign assumptions.
 Proof/definition method: Reuse previously checked decomposition identities and trusted standard real field/positivity tactics.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Field, Ring, and previous
 TwoStratumAssociation identities. These statements are pure real-polynomial
 consequences, not a second finite-event probability implementation.
 Boundary: Exact two-stratum admissions association and selection algebra,
 not Gaussian distributions, normal-tail integrals, or IQ population data.
*)
Theorem mix_first_gap_reverses_with_stratum_swap :
  forall j1 x1 y1 n1 j0 x0 y0 n0 : R, mix_gap_first j1 x1 y1 n1 j0 x0 y0 n0=-mix_gap_first j0 x0 y0 n0 j1 x1 y1 n1.
Proof.
  intros; unfold mix_gap_first; ring.
Qed.

(**
 [mix_second_gap_reverses_with_stratum_swap] (theorem) — Reversing selection groups negates the second-route conditional marginal contrast.
 Mathematical meaning: Reversing selection groups negates the second-route conditional marginal contrast.
 Exact checked proposition: forall j1 x1 y1 n1 j0 x0 y0 n0 : R, mix_gap_second j1 x1 y1 n1 j0 x0 y0 n0=-mix_gap_second j0 x0 y0 n0 j1 x1 y1 n1.
 Premises and side conditions: All eight real cell masses are explicit.
 Polynomial equalities have no sign hypotheses. Every conditional-rate
 identity or sign inference explicitly requires strictly positive stratum
 masses; additional inequalities state their own sign assumptions.
 Proof/definition method: Reuse previously checked decomposition identities and trusted standard real field/positivity tactics.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Field, Ring, and previous
 TwoStratumAssociation identities. These statements are pure real-polynomial
 consequences, not a second finite-event probability implementation.
 Boundary: Exact two-stratum admissions association and selection algebra,
 not Gaussian distributions, normal-tail integrals, or IQ population data.
*)
Theorem mix_second_gap_reverses_with_stratum_swap :
  forall j1 x1 y1 n1 j0 x0 y0 n0 : R, mix_gap_second j1 x1 y1 n1 j0 x0 y0 n0=-mix_gap_second j0 x0 y0 n0 j1 x1 y1 n1.
Proof.
  intros; unfold mix_gap_second; ring.
Qed.

(**
 [mix_within_invariant_under_strata_swap] (theorem) — The weighted within-stratum determinant component is symmetric under exchanging selection groups.
 Mathematical meaning: The weighted within-stratum determinant component is symmetric under exchanging selection groups.
 Exact checked proposition: forall j1 x1 y1 n1 j0 x0 y0 n0 : R, mix_within j1 x1 y1 n1 j0 x0 y0 n0=mix_within j0 x0 y0 n0 j1 x1 y1 n1.
 Premises and side conditions: All eight real cell masses are explicit.
 Polynomial equalities have no sign hypotheses. Every conditional-rate
 identity or sign inference explicitly requires strictly positive stratum
 masses; additional inequalities state their own sign assumptions.
 Proof/definition method: Reuse previously checked decomposition identities and trusted standard real field/positivity tactics.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Field, Ring, and previous
 TwoStratumAssociation identities. These statements are pure real-polynomial
 consequences, not a second finite-event probability implementation.
 Boundary: Exact two-stratum admissions association and selection algebra,
 not Gaussian distributions, normal-tail integrals, or IQ population data.
*)
Theorem mix_within_invariant_under_strata_swap :
  forall j1 x1 y1 n1 j0 x0 y0 n0 : R, mix_within j1 x1 y1 n1 j0 x0 y0 n0=mix_within j0 x0 y0 n0 j1 x1 y1 n1.
Proof.
  intros; unfold mix_within; ring.
Qed.

(**
 [mix_between_invariant_under_strata_swap] (theorem) — The selection-between-strata component is unaffected by changing the labels of the two strata.
 Mathematical meaning: The selection-between-strata component is unaffected by changing the labels of the two strata.
 Exact checked proposition: forall j1 x1 y1 n1 j0 x0 y0 n0 : R, mix_between j1 x1 y1 n1 j0 x0 y0 n0=mix_between j0 x0 y0 n0 j1 x1 y1 n1.
 Premises and side conditions: All eight real cell masses are explicit.
 Polynomial equalities have no sign hypotheses. Every conditional-rate
 identity or sign inference explicitly requires strictly positive stratum
 masses; additional inequalities state their own sign assumptions.
 Proof/definition method: Reuse previously checked decomposition identities and trusted standard real field/positivity tactics.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Field, Ring, and previous
 TwoStratumAssociation identities. These statements are pure real-polynomial
 consequences, not a second finite-event probability implementation.
 Boundary: Exact two-stratum admissions association and selection algebra,
 not Gaussian distributions, normal-tail integrals, or IQ population data.
*)
Theorem mix_between_invariant_under_strata_swap :
  forall j1 x1 y1 n1 j0 x0 y0 n0 : R, mix_between j1 x1 y1 n1 j0 x0 y0 n0=mix_between j0 x0 y0 n0 j1 x1 y1 n1.
Proof.
  intros; unfold mix_between; ring.
Qed.

(**
 [mix_first_gap_reduced] (theorem) — The first-route contrast cancels the common admitted–admitted product and depends only on first-row and opposite-row mass.
 Mathematical meaning: The first-route contrast cancels the common admitted–admitted product and depends only on first-row and opposite-row mass.
 Exact checked proposition: forall j1 x1 y1 n1 j0 x0 y0 n0 : R, mix_gap_first j1 x1 y1 n1 j0 x0 y0 n0=(j1+x1)*(y0+n0)-(j0+x0)*(y1+n1).
 Premises and side conditions: All eight real cell masses are explicit.
 Polynomial equalities have no sign hypotheses. Every conditional-rate
 identity or sign inference explicitly requires strictly positive stratum
 masses; additional inequalities state their own sign assumptions.
 Proof/definition method: Reuse previously checked decomposition identities and trusted standard real field/positivity tactics.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Field, Ring, and previous
 TwoStratumAssociation identities. These statements are pure real-polynomial
 consequences, not a second finite-event probability implementation.
 Boundary: Exact two-stratum admissions association and selection algebra,
 not Gaussian distributions, normal-tail integrals, or IQ population data.
*)
Theorem mix_first_gap_reduced :
  forall j1 x1 y1 n1 j0 x0 y0 n0 : R, mix_gap_first j1 x1 y1 n1 j0 x0 y0 n0=(j1+x1)*(y0+n0)-(j0+x0)*(y1+n1).
Proof.
  intros; unfold mix_gap_first; ring.
Qed.

(**
 [mix_second_gap_reduced] (theorem) — The second-route contrast equals a cross-product difference of its column marginal and complement.
 Mathematical meaning: The second-route contrast equals a cross-product difference of its column marginal and complement.
 Exact checked proposition: forall j1 x1 y1 n1 j0 x0 y0 n0 : R, mix_gap_second j1 x1 y1 n1 j0 x0 y0 n0=(j1+y1)*(x0+n0)-(j0+y0)*(x1+n1).
 Premises and side conditions: All eight real cell masses are explicit.
 Polynomial equalities have no sign hypotheses. Every conditional-rate
 identity or sign inference explicitly requires strictly positive stratum
 masses; additional inequalities state their own sign assumptions.
 Proof/definition method: Reuse previously checked decomposition identities and trusted standard real field/positivity tactics.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Field, Ring, and previous
 TwoStratumAssociation identities. These statements are pure real-polynomial
 consequences, not a second finite-event probability implementation.
 Boundary: Exact two-stratum admissions association and selection algebra,
 not Gaussian distributions, normal-tail integrals, or IQ population data.
*)
Theorem mix_second_gap_reduced :
  forall j1 x1 y1 n1 j0 x0 y0 n0 : R, mix_gap_second j1 x1 y1 n1 j0 x0 y0 n0=(j1+y1)*(x0+n0)-(j0+y0)*(x1+n1).
Proof.
  intros; unfold mix_gap_second; ring.
Qed.

(**
 [mix_pooled_cross_terms] (theorem) — The marginal two-by-two determinant decomposes into within-table determinants and two cross-stratum concordant–discordant interaction terms.
 Mathematical meaning: The marginal two-by-two determinant decomposes into within-table determinants and two cross-stratum concordant–discordant interaction terms.
 Exact checked proposition: forall j1 x1 y1 n1 j0 x0 y0 n0 : R, mix_pooled_association j1 x1 y1 n1 j0 x0 y0 n0=mix_local_assoc_yes j1 x1 y1 n1 j0 x0 y0 n0+mix_local_assoc_no j1 x1 y1 n1 j0 x0 y0 n0+j1*n0+j0*n1-x1*y0-x0*y1.
 Premises and side conditions: All eight real cell masses are explicit.
 Polynomial equalities have no sign hypotheses. Every conditional-rate
 identity or sign inference explicitly requires strictly positive stratum
 masses; additional inequalities state their own sign assumptions.
 Proof/definition method: Reuse previously checked decomposition identities and trusted standard real field/positivity tactics.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Field, Ring, and previous
 TwoStratumAssociation identities. These statements are pure real-polynomial
 consequences, not a second finite-event probability implementation.
 Boundary: Exact two-stratum admissions association and selection algebra,
 not Gaussian distributions, normal-tail integrals, or IQ population data.
*)
Theorem mix_pooled_cross_terms :
  forall j1 x1 y1 n1 j0 x0 y0 n0 : R, mix_pooled_association j1 x1 y1 n1 j0 x0 y0 n0=mix_local_assoc_yes j1 x1 y1 n1 j0 x0 y0 n0+mix_local_assoc_no j1 x1 y1 n1 j0 x0 y0 n0+j1*n0+j0*n1-x1*y0-x0*y1.
Proof.
  intros; unfold mix_pooled_association, mix_local_assoc_yes, mix_local_assoc_no; ring.
Qed.

(**
 [mix_pooled_joint_total] (theorem) — The pooled joint-admission atom equals the sum of the selected and nonselected joint atoms.
 Mathematical meaning: The pooled joint-admission atom equals the sum of the selected and nonselected joint atoms.
 Exact checked proposition: forall j1 x1 y1 n1 j0 x0 y0 n0 : R, (j1+j0) + (x1+x0)=(j1+x1)+(j0+x0).
 Premises and side conditions: All eight real cell masses are explicit.
 Polynomial equalities have no sign hypotheses. Every conditional-rate
 identity or sign inference explicitly requires strictly positive stratum
 masses; additional inequalities state their own sign assumptions.
 Proof/definition method: Use Rocq's canonical polynomial normalization and arithmetic tactics.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Field, Ring, and previous
 TwoStratumAssociation identities. These statements are pure real-polynomial
 consequences, not a second finite-event probability implementation.
 Boundary: Exact two-stratum admissions association and selection algebra,
 not Gaussian distributions, normal-tail integrals, or IQ population data.
*)
Theorem mix_pooled_joint_total :
  forall j1 x1 y1 n1 j0 x0 y0 n0 : R, (j1+j0) + (x1+x0)=(j1+x1)+(j0+x0).
Proof.
  intros; ring.
Qed.

(**
 [mix_pooled_second_total] (theorem) — The pooled second-route admission probability is the sum of the corresponding second-route selected masses.
 Mathematical meaning: The pooled second-route admission probability is the sum of the corresponding second-route selected masses.
 Exact checked proposition: forall j1 x1 y1 n1 j0 x0 y0 n0 : R, (j1+j0)+(y1+y0)=(j1+y1)+(j0+y0).
 Premises and side conditions: All eight real cell masses are explicit.
 Polynomial equalities have no sign hypotheses. Every conditional-rate
 identity or sign inference explicitly requires strictly positive stratum
 masses; additional inequalities state their own sign assumptions.
 Proof/definition method: Use Rocq's canonical polynomial normalization and arithmetic tactics.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Field, Ring, and previous
 TwoStratumAssociation identities. These statements are pure real-polynomial
 consequences, not a second finite-event probability implementation.
 Boundary: Exact two-stratum admissions association and selection algebra,
 not Gaussian distributions, normal-tail integrals, or IQ population data.
*)
Theorem mix_pooled_second_total :
  forall j1 x1 y1 n1 j0 x0 y0 n0 : R, (j1+j0)+(y1+y0)=(j1+y1)+(j0+y0).
Proof.
  intros; ring.
Qed.

(**
 [mix_total_partitions] (theorem) — Total mass of the two strata is the total of all four pooled two-route cells.
 Mathematical meaning: Total mass of the two strata is the total of all four pooled two-route cells.
 Exact checked proposition: forall j1 x1 y1 n1 j0 x0 y0 n0 : R, mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0+mix_total_no j1 x1 y1 n1 j0 x0 y0 n0=(j1+j0)+(x1+x0)+(y1+y0)+(n1+n0).
 Premises and side conditions: All eight real cell masses are explicit.
 Polynomial equalities have no sign hypotheses. Every conditional-rate
 identity or sign inference explicitly requires strictly positive stratum
 masses; additional inequalities state their own sign assumptions.
 Proof/definition method: Reuse previously checked decomposition identities and trusted standard real field/positivity tactics.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Field, Ring, and previous
 TwoStratumAssociation identities. These statements are pure real-polynomial
 consequences, not a second finite-event probability implementation.
 Boundary: Exact two-stratum admissions association and selection algebra,
 not Gaussian distributions, normal-tail integrals, or IQ population data.
*)
Theorem mix_total_partitions :
  forall j1 x1 y1 n1 j0 x0 y0 n0 : R, mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0+mix_total_no j1 x1 y1 n1 j0 x0 y0 n0=(j1+j0)+(x1+x0)+(y1+y0)+(n1+n0).
Proof.
  intros; unfold mix_total_yes, mix_total_no; ring.
Qed.

(**
 [mix_within_explicit] (theorem) — The two local odds determinants contribute to the adjusted within association with the other stratum's mass.
 Mathematical meaning: The two local odds determinants contribute to the adjusted within association with the other stratum's mass.
 Exact checked proposition: forall j1 x1 y1 n1 j0 x0 y0 n0 : R, mix_within j1 x1 y1 n1 j0 x0 y0 n0=mix_total_no j1 x1 y1 n1 j0 x0 y0 n0*mix_local_assoc_yes j1 x1 y1 n1 j0 x0 y0 n0+mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0*mix_local_assoc_no j1 x1 y1 n1 j0 x0 y0 n0.
 Premises and side conditions: All eight real cell masses are explicit.
 Polynomial equalities have no sign hypotheses. Every conditional-rate
 identity or sign inference explicitly requires strictly positive stratum
 masses; additional inequalities state their own sign assumptions.
 Proof/definition method: Reuse previously checked decomposition identities and trusted standard real field/positivity tactics.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Field, Ring, and previous
 TwoStratumAssociation identities. These statements are pure real-polynomial
 consequences, not a second finite-event probability implementation.
 Boundary: Exact two-stratum admissions association and selection algebra,
 not Gaussian distributions, normal-tail integrals, or IQ population data.
*)
Theorem mix_within_explicit :
  forall j1 x1 y1 n1 j0 x0 y0 n0 : R, mix_within j1 x1 y1 n1 j0 x0 y0 n0=mix_total_no j1 x1 y1 n1 j0 x0 y0 n0*mix_local_assoc_yes j1 x1 y1 n1 j0 x0 y0 n0+mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0*mix_local_assoc_no j1 x1 y1 n1 j0 x0 y0 n0.
Proof.
  intros; unfold mix_within, mix_total_yes, mix_total_no, mix_local_assoc_yes, mix_local_assoc_no; ring.
Qed.

(**
 [mix_between_explicit] (theorem) — The between-stratum association is exactly the product of the two signed route-specific selection gaps.
 Mathematical meaning: The between-stratum association is exactly the product of the two signed route-specific selection gaps.
 Exact checked proposition: forall j1 x1 y1 n1 j0 x0 y0 n0 : R, mix_between j1 x1 y1 n1 j0 x0 y0 n0=mix_gap_first j1 x1 y1 n1 j0 x0 y0 n0*mix_gap_second j1 x1 y1 n1 j0 x0 y0 n0.
 Premises and side conditions: All eight real cell masses are explicit.
 Polynomial equalities have no sign hypotheses. Every conditional-rate
 identity or sign inference explicitly requires strictly positive stratum
 masses; additional inequalities state their own sign assumptions.
 Proof/definition method: Reuse previously checked decomposition identities and trusted standard real field/positivity tactics.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Field, Ring, and previous
 TwoStratumAssociation identities. These statements are pure real-polynomial
 consequences, not a second finite-event probability implementation.
 Boundary: Exact two-stratum admissions association and selection algebra,
 not Gaussian distributions, normal-tail integrals, or IQ population data.
*)
Theorem mix_between_explicit :
  forall j1 x1 y1 n1 j0 x0 y0 n0 : R, mix_between j1 x1 y1 n1 j0 x0 y0 n0=mix_gap_first j1 x1 y1 n1 j0 x0 y0 n0*mix_gap_second j1 x1 y1 n1 j0 x0 y0 n0.
Proof.
  intros; unfold mix_between, mix_gap_first, mix_gap_second; ring.
Qed.

(**
 [mix_effect_explicit] (theorem) — The aggregate selection effect equals the sum of total-mass-weighted within association and between selection gap.
 Mathematical meaning: The aggregate selection effect equals the sum of total-mass-weighted within association and between selection gap.
 Exact checked proposition: forall j1 x1 y1 n1 j0 x0 y0 n0 : R, mix_effect j1 x1 y1 n1 j0 x0 y0 n0=(mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0+mix_total_no j1 x1 y1 n1 j0 x0 y0 n0)*mix_within j1 x1 y1 n1 j0 x0 y0 n0+mix_between j1 x1 y1 n1 j0 x0 y0 n0.
 Premises and side conditions: All eight real cell masses are explicit.
 Polynomial equalities have no sign hypotheses. Every conditional-rate
 identity or sign inference explicitly requires strictly positive stratum
 masses; additional inequalities state their own sign assumptions.
 Proof/definition method: Reuse previously checked decomposition identities and trusted standard real field/positivity tactics.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Field, Ring, and previous
 TwoStratumAssociation identities. These statements are pure real-polynomial
 consequences, not a second finite-event probability implementation.
 Boundary: Exact two-stratum admissions association and selection algebra,
 not Gaussian distributions, normal-tail integrals, or IQ population data.
*)
Theorem mix_effect_explicit :
  forall j1 x1 y1 n1 j0 x0 y0 n0 : R, mix_effect j1 x1 y1 n1 j0 x0 y0 n0=(mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0+mix_total_no j1 x1 y1 n1 j0 x0 y0 n0)*mix_within j1 x1 y1 n1 j0 x0 y0 n0+mix_between j1 x1 y1 n1 j0 x0 y0 n0.
Proof.
  intros; unfold mix_effect, mix_total_yes, mix_total_no, mix_within, mix_between; ring.
Qed.

(**
 [mix_effect_is_scaled_pooled] (theorem) — The aggregate adjusted selection effect equals pooled association times the product of stratum masses.
 Mathematical meaning: The aggregate adjusted selection effect equals pooled association times the product of stratum masses.
 Exact checked proposition: forall j1 x1 y1 n1 j0 x0 y0 n0 : R, mix_effect j1 x1 y1 n1 j0 x0 y0 n0=mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0*mix_total_no j1 x1 y1 n1 j0 x0 y0 n0*mix_pooled_association j1 x1 y1 n1 j0 x0 y0 n0.
 Premises and side conditions: All eight real cell masses are explicit.
 Polynomial equalities have no sign hypotheses. Every conditional-rate
 identity or sign inference explicitly requires strictly positive stratum
 masses; additional inequalities state their own sign assumptions.
 Proof/definition method: Reuse previously checked decomposition identities and trusted standard real field/positivity tactics.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Field, Ring, and previous
 TwoStratumAssociation identities. These statements are pure real-polynomial
 consequences, not a second finite-event probability implementation.
 Boundary: Exact two-stratum admissions association and selection algebra,
 not Gaussian distributions, normal-tail integrals, or IQ population data.
*)
Theorem mix_effect_is_scaled_pooled :
  forall j1 x1 y1 n1 j0 x0 y0 n0 : R, mix_effect j1 x1 y1 n1 j0 x0 y0 n0=mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0*mix_total_no j1 x1 y1 n1 j0 x0 y0 n0*mix_pooled_association j1 x1 y1 n1 j0 x0 y0 n0.
Proof.
  intros; rewrite mix_effect_explicit; symmetry; apply mix_stratified_association_identity.
Qed.

(**
 [mix_first_rate_gap_exact] (theorem) — The two selection-conditional first-route pass rates differ by the exact signed first marginal contrast divided by the product of stratum masses.
 Mathematical meaning: The two selection-conditional first-route pass rates differ by the exact signed first marginal contrast divided by the product of stratum masses.
 Exact checked proposition: forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0->0<mix_total_no j1 x1 y1 n1 j0 x0 y0 n0->(j1+x1)/mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0-(j0+x0)/mix_total_no j1 x1 y1 n1 j0 x0 y0 n0=mix_gap_first j1 x1 y1 n1 j0 x0 y0 n0/(mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0*mix_total_no j1 x1 y1 n1 j0 x0 y0 n0).
 Premises and side conditions: All eight real cell masses are explicit.
 Polynomial equalities have no sign hypotheses. Every conditional-rate
 identity or sign inference explicitly requires strictly positive stratum
 masses; additional inequalities state their own sign assumptions.
 Proof/definition method: Reuse previously checked decomposition identities and trusted standard real field/positivity tactics.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Field, Ring, and previous
 TwoStratumAssociation identities. These statements are pure real-polynomial
 consequences, not a second finite-event probability implementation.
 Boundary: Exact two-stratum admissions association and selection algebra,
 not Gaussian distributions, normal-tail integrals, or IQ population data.
*)
Theorem mix_first_rate_gap_exact :
  forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0->0<mix_total_no j1 x1 y1 n1 j0 x0 y0 n0->(j1+x1)/mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0-(j0+x0)/mix_total_no j1 x1 y1 n1 j0 x0 y0 n0=mix_gap_first j1 x1 y1 n1 j0 x0 y0 n0/(mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0*mix_total_no j1 x1 y1 n1 j0 x0 y0 n0).
Proof.
  intros j1 x1 y1 n1 j0 x0 y0 n0 HU HV; unfold mix_gap_first; field; nra.
Qed.

(**
 [mix_second_rate_gap_exact] (theorem) — The selected versus nonselected second-route success-rate difference equals its scaled marginal contrast divided by both positive stratum masses.
 Mathematical meaning: The selected versus nonselected second-route success-rate difference equals its scaled marginal contrast divided by both positive stratum masses.
 Exact checked proposition: forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0->0<mix_total_no j1 x1 y1 n1 j0 x0 y0 n0->(j1+y1)/mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0-(j0+y0)/mix_total_no j1 x1 y1 n1 j0 x0 y0 n0=mix_gap_second j1 x1 y1 n1 j0 x0 y0 n0/(mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0*mix_total_no j1 x1 y1 n1 j0 x0 y0 n0).
 Premises and side conditions: All eight real cell masses are explicit.
 Polynomial equalities have no sign hypotheses. Every conditional-rate
 identity or sign inference explicitly requires strictly positive stratum
 masses; additional inequalities state their own sign assumptions.
 Proof/definition method: Reuse previously checked decomposition identities and trusted standard real field/positivity tactics.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Field, Ring, and previous
 TwoStratumAssociation identities. These statements are pure real-polynomial
 consequences, not a second finite-event probability implementation.
 Boundary: Exact two-stratum admissions association and selection algebra,
 not Gaussian distributions, normal-tail integrals, or IQ population data.
*)
Theorem mix_second_rate_gap_exact :
  forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0->0<mix_total_no j1 x1 y1 n1 j0 x0 y0 n0->(j1+y1)/mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0-(j0+y0)/mix_total_no j1 x1 y1 n1 j0 x0 y0 n0=mix_gap_second j1 x1 y1 n1 j0 x0 y0 n0/(mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0*mix_total_no j1 x1 y1 n1 j0 x0 y0 n0).
Proof.
  intros j1 x1 y1 n1 j0 x0 y0 n0 HU HV; unfold mix_gap_second; field; nra.
Qed.

(**
 [mix_pooled_positive_iff_adjusted_positive] (theorem) — Marginal positive two-route association is exactly positivity of within-plus-selection association after multiplying by positive stratum masses.
 Mathematical meaning: Marginal positive two-route association is exactly positivity of within-plus-selection association after multiplying by positive stratum masses.
 Exact checked proposition: forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0->0<mix_total_no j1 x1 y1 n1 j0 x0 y0 n0-> (0<mix_pooled_association j1 x1 y1 n1 j0 x0 y0 n0<->0<(mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0+mix_total_no j1 x1 y1 n1 j0 x0 y0 n0)*mix_within j1 x1 y1 n1 j0 x0 y0 n0+mix_between j1 x1 y1 n1 j0 x0 y0 n0).
 Premises and side conditions: All eight real cell masses are explicit.
 Polynomial equalities have no sign hypotheses. Every conditional-rate
 identity or sign inference explicitly requires strictly positive stratum
 masses; additional inequalities state their own sign assumptions.
 Proof/definition method: Reuse previously checked decomposition identities and trusted standard real field/positivity tactics.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Field, Ring, and previous
 TwoStratumAssociation identities. These statements are pure real-polynomial
 consequences, not a second finite-event probability implementation.
 Boundary: Exact two-stratum admissions association and selection algebra,
 not Gaussian distributions, normal-tail integrals, or IQ population data.
*)
Theorem mix_pooled_positive_iff_adjusted_positive :
  forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0->0<mix_total_no j1 x1 y1 n1 j0 x0 y0 n0-> (0<mix_pooled_association j1 x1 y1 n1 j0 x0 y0 n0<->0<(mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0+mix_total_no j1 x1 y1 n1 j0 x0 y0 n0)*mix_within j1 x1 y1 n1 j0 x0 y0 n0+mix_between j1 x1 y1 n1 j0 x0 y0 n0).
Proof.
  intros j1 x1 y1 n1 j0 x0 y0 n0 HU HV.
  pose proof (mix_stratified_association_identity j1 x1 y1 n1 j0 x0 y0 n0) as Hid.
  assert (HP:0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0*mix_total_no j1 x1 y1 n1 j0 x0 y0 n0) by (apply Rmult_lt_0_compat; assumption).
  assert (HT:0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0+mix_total_no j1 x1 y1 n1 j0 x0 y0 n0) by lra.
  split; intro Hz; nra.
Qed.

(**
 [mix_pooled_negative_iff_adjusted_negative] (theorem) — Marginal negative two-route association is exactly negativity of within-plus-selection association.
 Mathematical meaning: Marginal negative two-route association is exactly negativity of within-plus-selection association.
 Exact checked proposition: forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0->0<mix_total_no j1 x1 y1 n1 j0 x0 y0 n0-> (mix_pooled_association j1 x1 y1 n1 j0 x0 y0 n0<0 <-> (mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0+mix_total_no j1 x1 y1 n1 j0 x0 y0 n0)*mix_within j1 x1 y1 n1 j0 x0 y0 n0+mix_between j1 x1 y1 n1 j0 x0 y0 n0<0).
 Premises and side conditions: All eight real cell masses are explicit.
 Polynomial equalities have no sign hypotheses. Every conditional-rate
 identity or sign inference explicitly requires strictly positive stratum
 masses; additional inequalities state their own sign assumptions.
 Proof/definition method: Reuse previously checked decomposition identities and trusted standard real field/positivity tactics.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Field, Ring, and previous
 TwoStratumAssociation identities. These statements are pure real-polynomial
 consequences, not a second finite-event probability implementation.
 Boundary: Exact two-stratum admissions association and selection algebra,
 not Gaussian distributions, normal-tail integrals, or IQ population data.
*)
Theorem mix_pooled_negative_iff_adjusted_negative :
  forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0->0<mix_total_no j1 x1 y1 n1 j0 x0 y0 n0-> (mix_pooled_association j1 x1 y1 n1 j0 x0 y0 n0<0 <-> (mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0+mix_total_no j1 x1 y1 n1 j0 x0 y0 n0)*mix_within j1 x1 y1 n1 j0 x0 y0 n0+mix_between j1 x1 y1 n1 j0 x0 y0 n0<0).
Proof.
  intros j1 x1 y1 n1 j0 x0 y0 n0 HU HV.
  pose proof (mix_stratified_association_identity j1 x1 y1 n1 j0 x0 y0 n0) as Hid.
  assert (HP:0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0*mix_total_no j1 x1 y1 n1 j0 x0 y0 n0) by (apply Rmult_lt_0_compat; assumption).
  assert (HT:0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0+mix_total_no j1 x1 y1 n1 j0 x0 y0 n0) by lra.
  split; intro Hz; nra.
Qed.

(**
 [mix_pooled_zero_iff_adjusted_zero] (theorem) — Pooled pairwise independence (zero determinant) is equivalent to complete cancellation of within and between selection components.
 Mathematical meaning: Pooled pairwise independence (zero determinant) is equivalent to complete cancellation of within and between selection components.
 Exact checked proposition: forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0->0<mix_total_no j1 x1 y1 n1 j0 x0 y0 n0-> (mix_pooled_association j1 x1 y1 n1 j0 x0 y0 n0=0 <-> (mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0+mix_total_no j1 x1 y1 n1 j0 x0 y0 n0)*mix_within j1 x1 y1 n1 j0 x0 y0 n0+mix_between j1 x1 y1 n1 j0 x0 y0 n0=0).
 Premises and side conditions: All eight real cell masses are explicit.
 Polynomial equalities have no sign hypotheses. Every conditional-rate
 identity or sign inference explicitly requires strictly positive stratum
 masses; additional inequalities state their own sign assumptions.
 Proof/definition method: Reuse previously checked decomposition identities and trusted standard real field/positivity tactics.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Field, Ring, and previous
 TwoStratumAssociation identities. These statements are pure real-polynomial
 consequences, not a second finite-event probability implementation.
 Boundary: Exact two-stratum admissions association and selection algebra,
 not Gaussian distributions, normal-tail integrals, or IQ population data.
*)
Theorem mix_pooled_zero_iff_adjusted_zero :
  forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0->0<mix_total_no j1 x1 y1 n1 j0 x0 y0 n0-> (mix_pooled_association j1 x1 y1 n1 j0 x0 y0 n0=0 <-> (mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0+mix_total_no j1 x1 y1 n1 j0 x0 y0 n0)*mix_within j1 x1 y1 n1 j0 x0 y0 n0+mix_between j1 x1 y1 n1 j0 x0 y0 n0=0).
Proof.
  intros j1 x1 y1 n1 j0 x0 y0 n0 HU HV.
  pose proof (mix_stratified_association_identity j1 x1 y1 n1 j0 x0 y0 n0) as Hid.
  assert (HP:0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0*mix_total_no j1 x1 y1 n1 j0 x0 y0 n0) by (apply Rmult_lt_0_compat; assumption).
  assert (HT:0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0+mix_total_no j1 x1 y1 n1 j0 x0 y0 n0) by lra.
  split; intro Hz; nra.
Qed.

(**
 [mix_pooled_nonnegative_iff_adjusted_nonnegative] (theorem) — Nonnegative marginal two-test dependence is equivalent to a nonnegative adjusted selection-effect numerator.
 Mathematical meaning: Nonnegative marginal two-test dependence is equivalent to a nonnegative adjusted selection-effect numerator.
 Exact checked proposition: forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0->0<mix_total_no j1 x1 y1 n1 j0 x0 y0 n0-> (0<=mix_pooled_association j1 x1 y1 n1 j0 x0 y0 n0<->0<=(mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0+mix_total_no j1 x1 y1 n1 j0 x0 y0 n0)*mix_within j1 x1 y1 n1 j0 x0 y0 n0+mix_between j1 x1 y1 n1 j0 x0 y0 n0).
 Premises and side conditions: All eight real cell masses are explicit.
 Polynomial equalities have no sign hypotheses. Every conditional-rate
 identity or sign inference explicitly requires strictly positive stratum
 masses; additional inequalities state their own sign assumptions.
 Proof/definition method: Reuse previously checked decomposition identities and trusted standard real field/positivity tactics.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Field, Ring, and previous
 TwoStratumAssociation identities. These statements are pure real-polynomial
 consequences, not a second finite-event probability implementation.
 Boundary: Exact two-stratum admissions association and selection algebra,
 not Gaussian distributions, normal-tail integrals, or IQ population data.
*)
Theorem mix_pooled_nonnegative_iff_adjusted_nonnegative :
  forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0->0<mix_total_no j1 x1 y1 n1 j0 x0 y0 n0-> (0<=mix_pooled_association j1 x1 y1 n1 j0 x0 y0 n0<->0<=(mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0+mix_total_no j1 x1 y1 n1 j0 x0 y0 n0)*mix_within j1 x1 y1 n1 j0 x0 y0 n0+mix_between j1 x1 y1 n1 j0 x0 y0 n0).
Proof.
  intros j1 x1 y1 n1 j0 x0 y0 n0 HU HV.
  pose proof (mix_stratified_association_identity j1 x1 y1 n1 j0 x0 y0 n0) as Hid.
  assert (HP:0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0*mix_total_no j1 x1 y1 n1 j0 x0 y0 n0) by (apply Rmult_lt_0_compat; assumption).
  assert (HT:0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0+mix_total_no j1 x1 y1 n1 j0 x0 y0 n0) by lra.
  split; intro Hz; nra.
Qed.

(**
 [mix_pooled_nonpositive_iff_adjusted_nonpositive] (theorem) — Nonpositive marginal dependence is equivalent to a nonpositive adjusted selection-effect numerator.
 Mathematical meaning: Nonpositive marginal dependence is equivalent to a nonpositive adjusted selection-effect numerator.
 Exact checked proposition: forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0->0<mix_total_no j1 x1 y1 n1 j0 x0 y0 n0-> (mix_pooled_association j1 x1 y1 n1 j0 x0 y0 n0<=0<->(mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0+mix_total_no j1 x1 y1 n1 j0 x0 y0 n0)*mix_within j1 x1 y1 n1 j0 x0 y0 n0+mix_between j1 x1 y1 n1 j0 x0 y0 n0<=0).
 Premises and side conditions: All eight real cell masses are explicit.
 Polynomial equalities have no sign hypotheses. Every conditional-rate
 identity or sign inference explicitly requires strictly positive stratum
 masses; additional inequalities state their own sign assumptions.
 Proof/definition method: Reuse previously checked decomposition identities and trusted standard real field/positivity tactics.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Field, Ring, and previous
 TwoStratumAssociation identities. These statements are pure real-polynomial
 consequences, not a second finite-event probability implementation.
 Boundary: Exact two-stratum admissions association and selection algebra,
 not Gaussian distributions, normal-tail integrals, or IQ population data.
*)
Theorem mix_pooled_nonpositive_iff_adjusted_nonpositive :
  forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0->0<mix_total_no j1 x1 y1 n1 j0 x0 y0 n0-> (mix_pooled_association j1 x1 y1 n1 j0 x0 y0 n0<=0<->(mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0+mix_total_no j1 x1 y1 n1 j0 x0 y0 n0)*mix_within j1 x1 y1 n1 j0 x0 y0 n0+mix_between j1 x1 y1 n1 j0 x0 y0 n0<=0).
Proof.
  intros j1 x1 y1 n1 j0 x0 y0 n0 HU HV.
  pose proof (mix_stratified_association_identity j1 x1 y1 n1 j0 x0 y0 n0) as Hid.
  assert (HP:0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0*mix_total_no j1 x1 y1 n1 j0 x0 y0 n0) by (apply Rmult_lt_0_compat; assumption).
  assert (HT:0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0+mix_total_no j1 x1 y1 n1 j0 x0 y0 n0) by lra.
  split; intro Hz; nra.
Qed.

(**
 [mix_within_nonnegative_from_local_nonnegative] (theorem) — If both strata have nonnegative two-route association, their positive-mass-weighted within component is nonnegative.
 Mathematical meaning: If both strata have nonnegative two-route association, their positive-mass-weighted within component is nonnegative.
 Exact checked proposition: forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0->0<mix_total_no j1 x1 y1 n1 j0 x0 y0 n0-> 0<=mix_local_assoc_yes j1 x1 y1 n1 j0 x0 y0 n0->0<=mix_local_assoc_no j1 x1 y1 n1 j0 x0 y0 n0->0<=mix_within j1 x1 y1 n1 j0 x0 y0 n0.
 Premises and side conditions: All eight real cell masses are explicit.
 Polynomial equalities have no sign hypotheses. Every conditional-rate
 identity or sign inference explicitly requires strictly positive stratum
 masses; additional inequalities state their own sign assumptions.
 Proof/definition method: Reuse previously checked decomposition identities and trusted standard real field/positivity tactics.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Field, Ring, and previous
 TwoStratumAssociation identities. These statements are pure real-polynomial
 consequences, not a second finite-event probability implementation.
 Boundary: Exact two-stratum admissions association and selection algebra,
 not Gaussian distributions, normal-tail integrals, or IQ population data.
*)
Theorem mix_within_nonnegative_from_local_nonnegative :
  forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0->0<mix_total_no j1 x1 y1 n1 j0 x0 y0 n0-> 0<=mix_local_assoc_yes j1 x1 y1 n1 j0 x0 y0 n0->0<=mix_local_assoc_no j1 x1 y1 n1 j0 x0 y0 n0->0<=mix_within j1 x1 y1 n1 j0 x0 y0 n0.
Proof.
  intros j1 x1 y1 n1 j0 x0 y0 n0 HU HV H1 H0.
  rewrite mix_within_explicit.
  nra.
Qed.

(**
 [mix_within_nonpositive_from_local_nonpositive] (theorem) — If both strata have nonpositive two-route association, their weighted within component is nonpositive.
 Mathematical meaning: If both strata have nonpositive two-route association, their weighted within component is nonpositive.
 Exact checked proposition: forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0->0<mix_total_no j1 x1 y1 n1 j0 x0 y0 n0-> mix_local_assoc_yes j1 x1 y1 n1 j0 x0 y0 n0<=0->mix_local_assoc_no j1 x1 y1 n1 j0 x0 y0 n0<=0->mix_within j1 x1 y1 n1 j0 x0 y0 n0<=0.
 Premises and side conditions: All eight real cell masses are explicit.
 Polynomial equalities have no sign hypotheses. Every conditional-rate
 identity or sign inference explicitly requires strictly positive stratum
 masses; additional inequalities state their own sign assumptions.
 Proof/definition method: Reuse previously checked decomposition identities and trusted standard real field/positivity tactics.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Field, Ring, and previous
 TwoStratumAssociation identities. These statements are pure real-polynomial
 consequences, not a second finite-event probability implementation.
 Boundary: Exact two-stratum admissions association and selection algebra,
 not Gaussian distributions, normal-tail integrals, or IQ population data.
*)
Theorem mix_within_nonpositive_from_local_nonpositive :
  forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0->0<mix_total_no j1 x1 y1 n1 j0 x0 y0 n0-> mix_local_assoc_yes j1 x1 y1 n1 j0 x0 y0 n0<=0->mix_local_assoc_no j1 x1 y1 n1 j0 x0 y0 n0<=0->mix_within j1 x1 y1 n1 j0 x0 y0 n0<=0.
Proof.
  intros j1 x1 y1 n1 j0 x0 y0 n0 HU HV H1 H0.
  rewrite mix_within_explicit.
  nra.
Qed.

(**
 [mix_within_positive_from_first_strict] (theorem) — Strict positive association in the first stratum and nonnegative association in the second makes the weighted within component strictly positive.
 Mathematical meaning: Strict positive association in the first stratum and nonnegative association in the second makes the weighted within component strictly positive.
 Exact checked proposition: forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0->0<mix_total_no j1 x1 y1 n1 j0 x0 y0 n0-> 0<mix_local_assoc_yes j1 x1 y1 n1 j0 x0 y0 n0->0<=mix_local_assoc_no j1 x1 y1 n1 j0 x0 y0 n0->0<mix_within j1 x1 y1 n1 j0 x0 y0 n0.
 Premises and side conditions: All eight real cell masses are explicit.
 Polynomial equalities have no sign hypotheses. Every conditional-rate
 identity or sign inference explicitly requires strictly positive stratum
 masses; additional inequalities state their own sign assumptions.
 Proof/definition method: Reuse previously checked decomposition identities and trusted standard real field/positivity tactics.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Field, Ring, and previous
 TwoStratumAssociation identities. These statements are pure real-polynomial
 consequences, not a second finite-event probability implementation.
 Boundary: Exact two-stratum admissions association and selection algebra,
 not Gaussian distributions, normal-tail integrals, or IQ population data.
*)
Theorem mix_within_positive_from_first_strict :
  forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0->0<mix_total_no j1 x1 y1 n1 j0 x0 y0 n0-> 0<mix_local_assoc_yes j1 x1 y1 n1 j0 x0 y0 n0->0<=mix_local_assoc_no j1 x1 y1 n1 j0 x0 y0 n0->0<mix_within j1 x1 y1 n1 j0 x0 y0 n0.
Proof.
  intros j1 x1 y1 n1 j0 x0 y0 n0 HU HV H1 H0.
  rewrite mix_within_explicit.
  nra.
Qed.

(**
 [mix_within_positive_from_second_strict] (theorem) — Strict positive association in the second stratum and nonnegative association in the first makes the weighted within component strictly positive.
 Mathematical meaning: Strict positive association in the second stratum and nonnegative association in the first makes the weighted within component strictly positive.
 Exact checked proposition: forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0->0<mix_total_no j1 x1 y1 n1 j0 x0 y0 n0-> 0<=mix_local_assoc_yes j1 x1 y1 n1 j0 x0 y0 n0->0<mix_local_assoc_no j1 x1 y1 n1 j0 x0 y0 n0->0<mix_within j1 x1 y1 n1 j0 x0 y0 n0.
 Premises and side conditions: All eight real cell masses are explicit.
 Polynomial equalities have no sign hypotheses. Every conditional-rate
 identity or sign inference explicitly requires strictly positive stratum
 masses; additional inequalities state their own sign assumptions.
 Proof/definition method: Reuse previously checked decomposition identities and trusted standard real field/positivity tactics.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Field, Ring, and previous
 TwoStratumAssociation identities. These statements are pure real-polynomial
 consequences, not a second finite-event probability implementation.
 Boundary: Exact two-stratum admissions association and selection algebra,
 not Gaussian distributions, normal-tail integrals, or IQ population data.
*)
Theorem mix_within_positive_from_second_strict :
  forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0->0<mix_total_no j1 x1 y1 n1 j0 x0 y0 n0-> 0<=mix_local_assoc_yes j1 x1 y1 n1 j0 x0 y0 n0->0<mix_local_assoc_no j1 x1 y1 n1 j0 x0 y0 n0->0<mix_within j1 x1 y1 n1 j0 x0 y0 n0.
Proof.
  intros j1 x1 y1 n1 j0 x0 y0 n0 HU HV H1 H0.
  rewrite mix_within_explicit.
  nra.
Qed.

(**
 [mix_within_negative_from_first_strict] (theorem) — Strict negative first-stratum association and nonpositive second-stratum association make the weighted within component negative.
 Mathematical meaning: Strict negative first-stratum association and nonpositive second-stratum association make the weighted within component negative.
 Exact checked proposition: forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0->0<mix_total_no j1 x1 y1 n1 j0 x0 y0 n0-> mix_local_assoc_yes j1 x1 y1 n1 j0 x0 y0 n0<0->mix_local_assoc_no j1 x1 y1 n1 j0 x0 y0 n0<=0->mix_within j1 x1 y1 n1 j0 x0 y0 n0<0.
 Premises and side conditions: All eight real cell masses are explicit.
 Polynomial equalities have no sign hypotheses. Every conditional-rate
 identity or sign inference explicitly requires strictly positive stratum
 masses; additional inequalities state their own sign assumptions.
 Proof/definition method: Reuse previously checked decomposition identities and trusted standard real field/positivity tactics.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Field, Ring, and previous
 TwoStratumAssociation identities. These statements are pure real-polynomial
 consequences, not a second finite-event probability implementation.
 Boundary: Exact two-stratum admissions association and selection algebra,
 not Gaussian distributions, normal-tail integrals, or IQ population data.
*)
Theorem mix_within_negative_from_first_strict :
  forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0->0<mix_total_no j1 x1 y1 n1 j0 x0 y0 n0-> mix_local_assoc_yes j1 x1 y1 n1 j0 x0 y0 n0<0->mix_local_assoc_no j1 x1 y1 n1 j0 x0 y0 n0<=0->mix_within j1 x1 y1 n1 j0 x0 y0 n0<0.
Proof.
  intros j1 x1 y1 n1 j0 x0 y0 n0 HU HV H1 H0.
  rewrite mix_within_explicit.
  nra.
Qed.

(**
 [mix_within_negative_from_second_strict] (theorem) — Strict negative second-stratum association and nonpositive first-stratum association make the weighted within component negative.
 Mathematical meaning: Strict negative second-stratum association and nonpositive first-stratum association make the weighted within component negative.
 Exact checked proposition: forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0->0<mix_total_no j1 x1 y1 n1 j0 x0 y0 n0-> mix_local_assoc_yes j1 x1 y1 n1 j0 x0 y0 n0<=0->mix_local_assoc_no j1 x1 y1 n1 j0 x0 y0 n0<0->mix_within j1 x1 y1 n1 j0 x0 y0 n0<0.
 Premises and side conditions: All eight real cell masses are explicit.
 Polynomial equalities have no sign hypotheses. Every conditional-rate
 identity or sign inference explicitly requires strictly positive stratum
 masses; additional inequalities state their own sign assumptions.
 Proof/definition method: Reuse previously checked decomposition identities and trusted standard real field/positivity tactics.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Field, Ring, and previous
 TwoStratumAssociation identities. These statements are pure real-polynomial
 consequences, not a second finite-event probability implementation.
 Boundary: Exact two-stratum admissions association and selection algebra,
 not Gaussian distributions, normal-tail integrals, or IQ population data.
*)
Theorem mix_within_negative_from_second_strict :
  forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0->0<mix_total_no j1 x1 y1 n1 j0 x0 y0 n0-> mix_local_assoc_yes j1 x1 y1 n1 j0 x0 y0 n0<=0->mix_local_assoc_no j1 x1 y1 n1 j0 x0 y0 n0<0->mix_within j1 x1 y1 n1 j0 x0 y0 n0<0.
Proof.
  intros j1 x1 y1 n1 j0 x0 y0 n0 HU HV H1 H0.
  rewrite mix_within_explicit.
  nra.
Qed.

(**
 [mix_between_nonnegative_both_gaps_positive] (theorem) — Same-direction nonnegative selection gaps cannot create a negative between-stratum association.
 Mathematical meaning: Same-direction nonnegative selection gaps cannot create a negative between-stratum association.
 Exact checked proposition: forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<=mix_gap_first j1 x1 y1 n1 j0 x0 y0 n0->0<=mix_gap_second j1 x1 y1 n1 j0 x0 y0 n0->0<=mix_between j1 x1 y1 n1 j0 x0 y0 n0.
 Premises and side conditions: All eight real cell masses are explicit.
 Polynomial equalities have no sign hypotheses. Every conditional-rate
 identity or sign inference explicitly requires strictly positive stratum
 masses; additional inequalities state their own sign assumptions.
 Proof/definition method: Reuse previously checked decomposition identities and trusted standard real field/positivity tactics.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Field, Ring, and previous
 TwoStratumAssociation identities. These statements are pure real-polynomial
 consequences, not a second finite-event probability implementation.
 Boundary: Exact two-stratum admissions association and selection algebra,
 not Gaussian distributions, normal-tail integrals, or IQ population data.
*)
Theorem mix_between_nonnegative_both_gaps_positive :
  forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<=mix_gap_first j1 x1 y1 n1 j0 x0 y0 n0->0<=mix_gap_second j1 x1 y1 n1 j0 x0 y0 n0->0<=mix_between j1 x1 y1 n1 j0 x0 y0 n0.
Proof.
  intros j1 x1 y1 n1 j0 x0 y0 n0 HA HB.
  rewrite mix_between_explicit; nra.
Qed.

(**
 [mix_between_nonnegative_both_gaps_negative] (theorem) — Same-direction nonpositive selection gaps cannot create a negative between-stratum association.
 Mathematical meaning: Same-direction nonpositive selection gaps cannot create a negative between-stratum association.
 Exact checked proposition: forall j1 x1 y1 n1 j0 x0 y0 n0 : R, mix_gap_first j1 x1 y1 n1 j0 x0 y0 n0<=0->mix_gap_second j1 x1 y1 n1 j0 x0 y0 n0<=0->0<=mix_between j1 x1 y1 n1 j0 x0 y0 n0.
 Premises and side conditions: All eight real cell masses are explicit.
 Polynomial equalities have no sign hypotheses. Every conditional-rate
 identity or sign inference explicitly requires strictly positive stratum
 masses; additional inequalities state their own sign assumptions.
 Proof/definition method: Reuse previously checked decomposition identities and trusted standard real field/positivity tactics.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Field, Ring, and previous
 TwoStratumAssociation identities. These statements are pure real-polynomial
 consequences, not a second finite-event probability implementation.
 Boundary: Exact two-stratum admissions association and selection algebra,
 not Gaussian distributions, normal-tail integrals, or IQ population data.
*)
Theorem mix_between_nonnegative_both_gaps_negative :
  forall j1 x1 y1 n1 j0 x0 y0 n0 : R, mix_gap_first j1 x1 y1 n1 j0 x0 y0 n0<=0->mix_gap_second j1 x1 y1 n1 j0 x0 y0 n0<=0->0<=mix_between j1 x1 y1 n1 j0 x0 y0 n0.
Proof.
  intros j1 x1 y1 n1 j0 x0 y0 n0 HA HB.
  rewrite mix_between_explicit; nra.
Qed.

(**
 [mix_between_nonpositive_first_positive_second_negative] (theorem) — Opposite weak selection contrasts (first up, second down) produce a nonpositive between component.
 Mathematical meaning: Opposite weak selection contrasts (first up, second down) produce a nonpositive between component.
 Exact checked proposition: forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<=mix_gap_first j1 x1 y1 n1 j0 x0 y0 n0->mix_gap_second j1 x1 y1 n1 j0 x0 y0 n0<=0->mix_between j1 x1 y1 n1 j0 x0 y0 n0<=0.
 Premises and side conditions: All eight real cell masses are explicit.
 Polynomial equalities have no sign hypotheses. Every conditional-rate
 identity or sign inference explicitly requires strictly positive stratum
 masses; additional inequalities state their own sign assumptions.
 Proof/definition method: Reuse previously checked decomposition identities and trusted standard real field/positivity tactics.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Field, Ring, and previous
 TwoStratumAssociation identities. These statements are pure real-polynomial
 consequences, not a second finite-event probability implementation.
 Boundary: Exact two-stratum admissions association and selection algebra,
 not Gaussian distributions, normal-tail integrals, or IQ population data.
*)
Theorem mix_between_nonpositive_first_positive_second_negative :
  forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<=mix_gap_first j1 x1 y1 n1 j0 x0 y0 n0->mix_gap_second j1 x1 y1 n1 j0 x0 y0 n0<=0->mix_between j1 x1 y1 n1 j0 x0 y0 n0<=0.
Proof.
  intros j1 x1 y1 n1 j0 x0 y0 n0 HA HB.
  rewrite mix_between_explicit; nra.
Qed.

(**
 [mix_between_nonpositive_first_negative_second_positive] (theorem) — Opposite weak selection contrasts (first down, second up) produce a nonpositive between component.
 Mathematical meaning: Opposite weak selection contrasts (first down, second up) produce a nonpositive between component.
 Exact checked proposition: forall j1 x1 y1 n1 j0 x0 y0 n0 : R, mix_gap_first j1 x1 y1 n1 j0 x0 y0 n0<=0->0<=mix_gap_second j1 x1 y1 n1 j0 x0 y0 n0->mix_between j1 x1 y1 n1 j0 x0 y0 n0<=0.
 Premises and side conditions: All eight real cell masses are explicit.
 Polynomial equalities have no sign hypotheses. Every conditional-rate
 identity or sign inference explicitly requires strictly positive stratum
 masses; additional inequalities state their own sign assumptions.
 Proof/definition method: Reuse previously checked decomposition identities and trusted standard real field/positivity tactics.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Field, Ring, and previous
 TwoStratumAssociation identities. These statements are pure real-polynomial
 consequences, not a second finite-event probability implementation.
 Boundary: Exact two-stratum admissions association and selection algebra,
 not Gaussian distributions, normal-tail integrals, or IQ population data.
*)
Theorem mix_between_nonpositive_first_negative_second_positive :
  forall j1 x1 y1 n1 j0 x0 y0 n0 : R, mix_gap_first j1 x1 y1 n1 j0 x0 y0 n0<=0->0<=mix_gap_second j1 x1 y1 n1 j0 x0 y0 n0->mix_between j1 x1 y1 n1 j0 x0 y0 n0<=0.
Proof.
  intros j1 x1 y1 n1 j0 x0 y0 n0 HA HB.
  rewrite mix_between_explicit; nra.
Qed.

(**
 [mix_between_positive_both_gaps_positive] (theorem) — Two strictly positive selection gaps induce strictly positive between-stratum dependence.
 Mathematical meaning: Two strictly positive selection gaps induce strictly positive between-stratum dependence.
 Exact checked proposition: forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<mix_gap_first j1 x1 y1 n1 j0 x0 y0 n0->0<mix_gap_second j1 x1 y1 n1 j0 x0 y0 n0->0<mix_between j1 x1 y1 n1 j0 x0 y0 n0.
 Premises and side conditions: All eight real cell masses are explicit.
 Polynomial equalities have no sign hypotheses. Every conditional-rate
 identity or sign inference explicitly requires strictly positive stratum
 masses; additional inequalities state their own sign assumptions.
 Proof/definition method: Reuse previously checked decomposition identities and trusted standard real field/positivity tactics.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Field, Ring, and previous
 TwoStratumAssociation identities. These statements are pure real-polynomial
 consequences, not a second finite-event probability implementation.
 Boundary: Exact two-stratum admissions association and selection algebra,
 not Gaussian distributions, normal-tail integrals, or IQ population data.
*)
Theorem mix_between_positive_both_gaps_positive :
  forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<mix_gap_first j1 x1 y1 n1 j0 x0 y0 n0->0<mix_gap_second j1 x1 y1 n1 j0 x0 y0 n0->0<mix_between j1 x1 y1 n1 j0 x0 y0 n0.
Proof.
  intros j1 x1 y1 n1 j0 x0 y0 n0 HA HB.
  rewrite mix_between_explicit; nra.
Qed.

(**
 [mix_between_positive_both_gaps_negative] (theorem) — Two strictly negative selection gaps induce strictly positive between-stratum dependence.
 Mathematical meaning: Two strictly negative selection gaps induce strictly positive between-stratum dependence.
 Exact checked proposition: forall j1 x1 y1 n1 j0 x0 y0 n0 : R, mix_gap_first j1 x1 y1 n1 j0 x0 y0 n0<0->mix_gap_second j1 x1 y1 n1 j0 x0 y0 n0<0->0<mix_between j1 x1 y1 n1 j0 x0 y0 n0.
 Premises and side conditions: All eight real cell masses are explicit.
 Polynomial equalities have no sign hypotheses. Every conditional-rate
 identity or sign inference explicitly requires strictly positive stratum
 masses; additional inequalities state their own sign assumptions.
 Proof/definition method: Reuse previously checked decomposition identities and trusted standard real field/positivity tactics.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Field, Ring, and previous
 TwoStratumAssociation identities. These statements are pure real-polynomial
 consequences, not a second finite-event probability implementation.
 Boundary: Exact two-stratum admissions association and selection algebra,
 not Gaussian distributions, normal-tail integrals, or IQ population data.
*)
Theorem mix_between_positive_both_gaps_negative :
  forall j1 x1 y1 n1 j0 x0 y0 n0 : R, mix_gap_first j1 x1 y1 n1 j0 x0 y0 n0<0->mix_gap_second j1 x1 y1 n1 j0 x0 y0 n0<0->0<mix_between j1 x1 y1 n1 j0 x0 y0 n0.
Proof.
  intros j1 x1 y1 n1 j0 x0 y0 n0 HA HB.
  rewrite mix_between_explicit; nra.
Qed.

(**
 [mix_between_negative_opposing_positive_negative] (theorem) — A positive first-route gap and negative second-route gap induce strictly negative between-stratum dependence.
 Mathematical meaning: A positive first-route gap and negative second-route gap induce strictly negative between-stratum dependence.
 Exact checked proposition: forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<mix_gap_first j1 x1 y1 n1 j0 x0 y0 n0->mix_gap_second j1 x1 y1 n1 j0 x0 y0 n0<0->mix_between j1 x1 y1 n1 j0 x0 y0 n0<0.
 Premises and side conditions: All eight real cell masses are explicit.
 Polynomial equalities have no sign hypotheses. Every conditional-rate
 identity or sign inference explicitly requires strictly positive stratum
 masses; additional inequalities state their own sign assumptions.
 Proof/definition method: Reuse previously checked decomposition identities and trusted standard real field/positivity tactics.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Field, Ring, and previous
 TwoStratumAssociation identities. These statements are pure real-polynomial
 consequences, not a second finite-event probability implementation.
 Boundary: Exact two-stratum admissions association and selection algebra,
 not Gaussian distributions, normal-tail integrals, or IQ population data.
*)
Theorem mix_between_negative_opposing_positive_negative :
  forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<mix_gap_first j1 x1 y1 n1 j0 x0 y0 n0->mix_gap_second j1 x1 y1 n1 j0 x0 y0 n0<0->mix_between j1 x1 y1 n1 j0 x0 y0 n0<0.
Proof.
  intros j1 x1 y1 n1 j0 x0 y0 n0 HA HB.
  rewrite mix_between_explicit; nra.
Qed.

(**
 [mix_between_negative_opposing_negative_positive] (theorem) — A negative first-route gap and positive second-route gap induce strictly negative between-stratum dependence.
 Mathematical meaning: A negative first-route gap and positive second-route gap induce strictly negative between-stratum dependence.
 Exact checked proposition: forall j1 x1 y1 n1 j0 x0 y0 n0 : R, mix_gap_first j1 x1 y1 n1 j0 x0 y0 n0<0->0<mix_gap_second j1 x1 y1 n1 j0 x0 y0 n0->mix_between j1 x1 y1 n1 j0 x0 y0 n0<0.
 Premises and side conditions: All eight real cell masses are explicit.
 Polynomial equalities have no sign hypotheses. Every conditional-rate
 identity or sign inference explicitly requires strictly positive stratum
 masses; additional inequalities state their own sign assumptions.
 Proof/definition method: Reuse previously checked decomposition identities and trusted standard real field/positivity tactics.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Field, Ring, and previous
 TwoStratumAssociation identities. These statements are pure real-polynomial
 consequences, not a second finite-event probability implementation.
 Boundary: Exact two-stratum admissions association and selection algebra,
 not Gaussian distributions, normal-tail integrals, or IQ population data.
*)
Theorem mix_between_negative_opposing_negative_positive :
  forall j1 x1 y1 n1 j0 x0 y0 n0 : R, mix_gap_first j1 x1 y1 n1 j0 x0 y0 n0<0->0<mix_gap_second j1 x1 y1 n1 j0 x0 y0 n0->mix_between j1 x1 y1 n1 j0 x0 y0 n0<0.
Proof.
  intros j1 x1 y1 n1 j0 x0 y0 n0 HA HB.
  rewrite mix_between_explicit; nra.
Qed.

(**
 [mix_between_zero_if_first_gap_zero] (theorem) — Equal first-route pass rates across strata eliminate the between-stratum association.
 Mathematical meaning: Equal first-route pass rates across strata eliminate the between-stratum association.
 Exact checked proposition: forall j1 x1 y1 n1 j0 x0 y0 n0 : R, mix_gap_first j1 x1 y1 n1 j0 x0 y0 n0=0->mix_between j1 x1 y1 n1 j0 x0 y0 n0=0.
 Premises and side conditions: All eight real cell masses are explicit.
 Polynomial equalities have no sign hypotheses. Every conditional-rate
 identity or sign inference explicitly requires strictly positive stratum
 masses; additional inequalities state their own sign assumptions.
 Proof/definition method: Reuse previously checked decomposition identities and trusted standard real field/positivity tactics.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Field, Ring, and previous
 TwoStratumAssociation identities. These statements are pure real-polynomial
 consequences, not a second finite-event probability implementation.
 Boundary: Exact two-stratum admissions association and selection algebra,
 not Gaussian distributions, normal-tail integrals, or IQ population data.
*)
Theorem mix_between_zero_if_first_gap_zero :
  forall j1 x1 y1 n1 j0 x0 y0 n0 : R, mix_gap_first j1 x1 y1 n1 j0 x0 y0 n0=0->mix_between j1 x1 y1 n1 j0 x0 y0 n0=0.
Proof.
  intros j1 x1 y1 n1 j0 x0 y0 n0 HA HB.
  rewrite mix_between_explicit; nra.
Qed.

(**
 [mix_between_zero_if_second_gap_zero] (theorem) — Equal second-route pass rates across strata eliminate the between-stratum association.
 Mathematical meaning: Equal second-route pass rates across strata eliminate the between-stratum association.
 Exact checked proposition: forall j1 x1 y1 n1 j0 x0 y0 n0 : R, mix_gap_second j1 x1 y1 n1 j0 x0 y0 n0=0->mix_between j1 x1 y1 n1 j0 x0 y0 n0=0.
 Premises and side conditions: All eight real cell masses are explicit.
 Polynomial equalities have no sign hypotheses. Every conditional-rate
 identity or sign inference explicitly requires strictly positive stratum
 masses; additional inequalities state their own sign assumptions.
 Proof/definition method: Reuse previously checked decomposition identities and trusted standard real field/positivity tactics.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Field, Ring, and previous
 TwoStratumAssociation identities. These statements are pure real-polynomial
 consequences, not a second finite-event probability implementation.
 Boundary: Exact two-stratum admissions association and selection algebra,
 not Gaussian distributions, normal-tail integrals, or IQ population data.
*)
Theorem mix_between_zero_if_second_gap_zero :
  forall j1 x1 y1 n1 j0 x0 y0 n0 : R, mix_gap_second j1 x1 y1 n1 j0 x0 y0 n0=0->mix_between j1 x1 y1 n1 j0 x0 y0 n0=0.
Proof.
  intros j1 x1 y1 n1 j0 x0 y0 n0 HA HB.
  rewrite mix_between_explicit; nra.
Qed.

(**
 [mix_pooled_positive_from_nonnegative_within_positive_between] (theorem) — Nonnegative within association and strictly positive selection effect make pooled dependence strictly positive.
 Mathematical meaning: Nonnegative within association and strictly positive selection effect make pooled dependence strictly positive.
 Exact checked proposition: forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0->0<mix_total_no j1 x1 y1 n1 j0 x0 y0 n0-> 0<=mix_within j1 x1 y1 n1 j0 x0 y0 n0->0<mix_between j1 x1 y1 n1 j0 x0 y0 n0->0<mix_pooled_association j1 x1 y1 n1 j0 x0 y0 n0.
 Premises and side conditions: All eight real cell masses are explicit.
 Polynomial equalities have no sign hypotheses. Every conditional-rate
 identity or sign inference explicitly requires strictly positive stratum
 masses; additional inequalities state their own sign assumptions.
 Proof/definition method: Reuse previously checked decomposition identities and trusted standard real field/positivity tactics.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Field, Ring, and previous
 TwoStratumAssociation identities. These statements are pure real-polynomial
 consequences, not a second finite-event probability implementation.
 Boundary: Exact two-stratum admissions association and selection algebra,
 not Gaussian distributions, normal-tail integrals, or IQ population data.
*)
Theorem mix_pooled_positive_from_nonnegative_within_positive_between :
  forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0->0<mix_total_no j1 x1 y1 n1 j0 x0 y0 n0-> 0<=mix_within j1 x1 y1 n1 j0 x0 y0 n0->0<mix_between j1 x1 y1 n1 j0 x0 y0 n0->0<mix_pooled_association j1 x1 y1 n1 j0 x0 y0 n0.
Proof.
  intros j1 x1 y1 n1 j0 x0 y0 n0 HU HV HW HE.
  apply (proj2 (mix_pooled_positive_iff_adjusted_positive j1 x1 y1 n1 j0 x0 y0 n0 HU HV)).
  assert (HT:0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0+mix_total_no j1 x1 y1 n1 j0 x0 y0 n0) by lra.
  nra.
Qed.

(**
 [mix_pooled_positive_from_positive_within_nonnegative_between] (theorem) — Positive within association and nonnegative selection effect ensure positive pooled association.
 Mathematical meaning: Positive within association and nonnegative selection effect ensure positive pooled association.
 Exact checked proposition: forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0->0<mix_total_no j1 x1 y1 n1 j0 x0 y0 n0-> 0<mix_within j1 x1 y1 n1 j0 x0 y0 n0->0<=mix_between j1 x1 y1 n1 j0 x0 y0 n0->0<mix_pooled_association j1 x1 y1 n1 j0 x0 y0 n0.
 Premises and side conditions: All eight real cell masses are explicit.
 Polynomial equalities have no sign hypotheses. Every conditional-rate
 identity or sign inference explicitly requires strictly positive stratum
 masses; additional inequalities state their own sign assumptions.
 Proof/definition method: Reuse previously checked decomposition identities and trusted standard real field/positivity tactics.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Field, Ring, and previous
 TwoStratumAssociation identities. These statements are pure real-polynomial
 consequences, not a second finite-event probability implementation.
 Boundary: Exact two-stratum admissions association and selection algebra,
 not Gaussian distributions, normal-tail integrals, or IQ population data.
*)
Theorem mix_pooled_positive_from_positive_within_nonnegative_between :
  forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0->0<mix_total_no j1 x1 y1 n1 j0 x0 y0 n0-> 0<mix_within j1 x1 y1 n1 j0 x0 y0 n0->0<=mix_between j1 x1 y1 n1 j0 x0 y0 n0->0<mix_pooled_association j1 x1 y1 n1 j0 x0 y0 n0.
Proof.
  intros j1 x1 y1 n1 j0 x0 y0 n0 HU HV HW HE.
  apply (proj2 (mix_pooled_positive_iff_adjusted_positive j1 x1 y1 n1 j0 x0 y0 n0 HU HV)).
  assert (HT:0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0+mix_total_no j1 x1 y1 n1 j0 x0 y0 n0) by lra.
  nra.
Qed.

(**
 [mix_pooled_negative_from_nonpositive_within_negative_between] (theorem) — Nonpositive within association plus negative selection effect guarantee negative pooled association.
 Mathematical meaning: Nonpositive within association plus negative selection effect guarantee negative pooled association.
 Exact checked proposition: forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0->0<mix_total_no j1 x1 y1 n1 j0 x0 y0 n0-> mix_within j1 x1 y1 n1 j0 x0 y0 n0<=0->mix_between j1 x1 y1 n1 j0 x0 y0 n0<0->mix_pooled_association j1 x1 y1 n1 j0 x0 y0 n0<0.
 Premises and side conditions: All eight real cell masses are explicit.
 Polynomial equalities have no sign hypotheses. Every conditional-rate
 identity or sign inference explicitly requires strictly positive stratum
 masses; additional inequalities state their own sign assumptions.
 Proof/definition method: Reuse previously checked decomposition identities and trusted standard real field/positivity tactics.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Field, Ring, and previous
 TwoStratumAssociation identities. These statements are pure real-polynomial
 consequences, not a second finite-event probability implementation.
 Boundary: Exact two-stratum admissions association and selection algebra,
 not Gaussian distributions, normal-tail integrals, or IQ population data.
*)
Theorem mix_pooled_negative_from_nonpositive_within_negative_between :
  forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0->0<mix_total_no j1 x1 y1 n1 j0 x0 y0 n0-> mix_within j1 x1 y1 n1 j0 x0 y0 n0<=0->mix_between j1 x1 y1 n1 j0 x0 y0 n0<0->mix_pooled_association j1 x1 y1 n1 j0 x0 y0 n0<0.
Proof.
  intros j1 x1 y1 n1 j0 x0 y0 n0 HU HV HW HE.
  apply (proj2 (mix_pooled_negative_iff_adjusted_negative j1 x1 y1 n1 j0 x0 y0 n0 HU HV)).
  assert (HT:0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0+mix_total_no j1 x1 y1 n1 j0 x0 y0 n0) by lra.
  nra.
Qed.

(**
 [mix_pooled_negative_from_negative_within_nonpositive_between] (theorem) — Strict negative within association and nonpositive between effect ensure negative pooled association.
 Mathematical meaning: Strict negative within association and nonpositive between effect ensure negative pooled association.
 Exact checked proposition: forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0->0<mix_total_no j1 x1 y1 n1 j0 x0 y0 n0-> mix_within j1 x1 y1 n1 j0 x0 y0 n0<0->mix_between j1 x1 y1 n1 j0 x0 y0 n0<=0->mix_pooled_association j1 x1 y1 n1 j0 x0 y0 n0<0.
 Premises and side conditions: All eight real cell masses are explicit.
 Polynomial equalities have no sign hypotheses. Every conditional-rate
 identity or sign inference explicitly requires strictly positive stratum
 masses; additional inequalities state their own sign assumptions.
 Proof/definition method: Reuse previously checked decomposition identities and trusted standard real field/positivity tactics.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Field, Ring, and previous
 TwoStratumAssociation identities. These statements are pure real-polynomial
 consequences, not a second finite-event probability implementation.
 Boundary: Exact two-stratum admissions association and selection algebra,
 not Gaussian distributions, normal-tail integrals, or IQ population data.
*)
Theorem mix_pooled_negative_from_negative_within_nonpositive_between :
  forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0->0<mix_total_no j1 x1 y1 n1 j0 x0 y0 n0-> mix_within j1 x1 y1 n1 j0 x0 y0 n0<0->mix_between j1 x1 y1 n1 j0 x0 y0 n0<=0->mix_pooled_association j1 x1 y1 n1 j0 x0 y0 n0<0.
Proof.
  intros j1 x1 y1 n1 j0 x0 y0 n0 HU HV HW HE.
  apply (proj2 (mix_pooled_negative_iff_adjusted_negative j1 x1 y1 n1 j0 x0 y0 n0 HU HV)).
  assert (HT:0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0+mix_total_no j1 x1 y1 n1 j0 x0 y0 n0) by lra.
  nra.
Qed.

